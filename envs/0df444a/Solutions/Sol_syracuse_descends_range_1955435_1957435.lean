-- Prove2me | solution 1 for syracuse_descends_range_1955435_1957435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:45.767866+00:00
-- url     : https://prove2.me/submissions/94c3618f-89d1-48f2-9c72-5892d1d834f0

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

theorem B2199865 : Blo 1955435 2199865 := bbase (se 2 (by rfl) ⟨824949, by rfl⟩ : syracuseStep 2199865 = 1649899) (by norm_num)
theorem B2933153 : Blo 1955435 2933153 := bstep (se 2 (by rfl) ⟨1099932, by rfl⟩ : syracuseStep 2933153 = 2199865) B2199865
theorem B1955435 : Blo 1955435 1955435 := bstep (se 1 (by rfl) ⟨1466576, by rfl⟩ : syracuseStep 1955435 = 2933153) B2933153
theorem B5568421 : Blo 1955435 5568421 := bbase (se 4 (by rfl) ⟨522039, by rfl⟩ : syracuseStep 5568421 = 1044079) (by norm_num)
theorem B7424561 : Blo 1955435 7424561 := bstep (se 2 (by rfl) ⟨2784210, by rfl⟩ : syracuseStep 7424561 = 5568421) B5568421
theorem B4949707 : Blo 1955435 4949707 := bstep (se 1 (by rfl) ⟨3712280, by rfl⟩ : syracuseStep 4949707 = 7424561) B7424561
theorem B6599609 : Blo 1955435 6599609 := bstep (se 2 (by rfl) ⟨2474853, by rfl⟩ : syracuseStep 6599609 = 4949707) B4949707
theorem B4399739 : Blo 1955435 4399739 := bstep (se 1 (by rfl) ⟨3299804, by rfl⟩ : syracuseStep 4399739 = 6599609) B6599609
theorem B2933159 : Blo 1955435 2933159 := bstep (se 1 (by rfl) ⟨2199869, by rfl⟩ : syracuseStep 2933159 = 4399739) B4399739
theorem B1955439 : Blo 1955435 1955439 := bstep (se 1 (by rfl) ⟨1466579, by rfl⟩ : syracuseStep 1955439 = 2933159) B2933159
theorem B2933165 : Blo 1955435 2933165 := bbase (se 3 (by rfl) ⟨549968, by rfl⟩ : syracuseStep 2933165 = 1099937) (by norm_num)
theorem B1955443 : Blo 1955435 1955443 := bstep (se 1 (by rfl) ⟨1466582, by rfl⟩ : syracuseStep 1955443 = 2933165) B2933165
theorem B4399757 : Blo 1955435 4399757 := bbase (se 3 (by rfl) ⟨824954, by rfl⟩ : syracuseStep 4399757 = 1649909) (by norm_num)
theorem B2933171 : Blo 1955435 2933171 := bstep (se 1 (by rfl) ⟨2199878, by rfl⟩ : syracuseStep 2933171 = 4399757) B4399757
theorem B1955447 : Blo 1955435 1955447 := bstep (se 1 (by rfl) ⟨1466585, by rfl⟩ : syracuseStep 1955447 = 2933171) B2933171
theorem B2474869 : Blo 1955435 2474869 := bbase (se 5 (by rfl) ⟨116009, by rfl⟩ : syracuseStep 2474869 = 232019) (by norm_num)
theorem B3299825 : Blo 1955435 3299825 := bstep (se 2 (by rfl) ⟨1237434, by rfl⟩ : syracuseStep 3299825 = 2474869) B2474869
theorem B2199883 : Blo 1955435 2199883 := bstep (se 1 (by rfl) ⟨1649912, by rfl⟩ : syracuseStep 2199883 = 3299825) B3299825
theorem B2933177 : Blo 1955435 2933177 := bstep (se 2 (by rfl) ⟨1099941, by rfl⟩ : syracuseStep 2933177 = 2199883) B2199883
theorem B1955451 : Blo 1955435 1955451 := bstep (se 1 (by rfl) ⟨1466588, by rfl⟩ : syracuseStep 1955451 = 2933177) B2933177
theorem B4459805 : Blo 1955435 4459805 := bbase (se 3 (by rfl) ⟨836213, by rfl⟩ : syracuseStep 4459805 = 1672427) (by norm_num)
theorem B2973203 : Blo 1955435 2973203 := bstep (se 1 (by rfl) ⟨2229902, by rfl⟩ : syracuseStep 2973203 = 4459805) B4459805
theorem B1982135 : Blo 1955435 1982135 := bstep (se 1 (by rfl) ⟨1486601, by rfl⟩ : syracuseStep 1982135 = 2973203) B2973203
theorem B5285693 : Blo 1955435 5285693 := bstep (se 3 (by rfl) ⟨991067, by rfl⟩ : syracuseStep 5285693 = 1982135) B1982135
theorem B14095181 : Blo 1955435 14095181 := bstep (se 3 (by rfl) ⟨2642846, by rfl⟩ : syracuseStep 14095181 = 5285693) B5285693
theorem B37587149 : Blo 1955435 37587149 := bstep (se 3 (by rfl) ⟨7047590, by rfl⟩ : syracuseStep 37587149 = 14095181) B14095181
theorem B25058099 : Blo 1955435 25058099 := bstep (se 1 (by rfl) ⟨18793574, by rfl⟩ : syracuseStep 25058099 = 37587149) B37587149
theorem B16705399 : Blo 1955435 16705399 := bstep (se 1 (by rfl) ⟨12529049, by rfl⟩ : syracuseStep 16705399 = 25058099) B25058099
theorem B22273865 : Blo 1955435 22273865 := bstep (se 2 (by rfl) ⟨8352699, by rfl⟩ : syracuseStep 22273865 = 16705399) B16705399
theorem B14849243 : Blo 1955435 14849243 := bstep (se 1 (by rfl) ⟨11136932, by rfl⟩ : syracuseStep 14849243 = 22273865) B22273865
theorem B9899495 : Blo 1955435 9899495 := bstep (se 1 (by rfl) ⟨7424621, by rfl⟩ : syracuseStep 9899495 = 14849243) B14849243
theorem B6599663 : Blo 1955435 6599663 := bstep (se 1 (by rfl) ⟨4949747, by rfl⟩ : syracuseStep 6599663 = 9899495) B9899495
theorem B4399775 : Blo 1955435 4399775 := bstep (se 1 (by rfl) ⟨3299831, by rfl⟩ : syracuseStep 4399775 = 6599663) B6599663
theorem B2933183 : Blo 1955435 2933183 := bstep (se 1 (by rfl) ⟨2199887, by rfl⟩ : syracuseStep 2933183 = 4399775) B4399775
theorem B1955455 : Blo 1955435 1955455 := bstep (se 1 (by rfl) ⟨1466591, by rfl⟩ : syracuseStep 1955455 = 2933183) B2933183
theorem B2933189 : Blo 1955435 2933189 := bbase (se 4 (by rfl) ⟨274986, by rfl⟩ : syracuseStep 2933189 = 549973) (by norm_num)
theorem B1955459 : Blo 1955435 1955459 := bstep (se 1 (by rfl) ⟨1466594, by rfl⟩ : syracuseStep 1955459 = 2933189) B2933189
theorem B3299845 : Blo 1955435 3299845 := bbase (se 4 (by rfl) ⟨309360, by rfl⟩ : syracuseStep 3299845 = 618721) (by norm_num)
theorem B4399793 : Blo 1955435 4399793 := bstep (se 2 (by rfl) ⟨1649922, by rfl⟩ : syracuseStep 4399793 = 3299845) B3299845
theorem B2933195 : Blo 1955435 2933195 := bstep (se 1 (by rfl) ⟨2199896, by rfl⟩ : syracuseStep 2933195 = 4399793) B4399793
theorem B1955463 : Blo 1955435 1955463 := bstep (se 1 (by rfl) ⟨1466597, by rfl⟩ : syracuseStep 1955463 = 2933195) B2933195
theorem B2199901 : Blo 1955435 2199901 := bbase (se 3 (by rfl) ⟨412481, by rfl⟩ : syracuseStep 2199901 = 824963) (by norm_num)
theorem B2933201 : Blo 1955435 2933201 := bstep (se 2 (by rfl) ⟨1099950, by rfl⟩ : syracuseStep 2933201 = 2199901) B2199901
theorem B1955467 : Blo 1955435 1955467 := bstep (se 1 (by rfl) ⟨1466600, by rfl⟩ : syracuseStep 1955467 = 2933201) B2933201
theorem B6599717 : Blo 1955435 6599717 := bbase (se 4 (by rfl) ⟨618723, by rfl⟩ : syracuseStep 6599717 = 1237447) (by norm_num)
theorem B4399811 : Blo 1955435 4399811 := bstep (se 1 (by rfl) ⟨3299858, by rfl⟩ : syracuseStep 4399811 = 6599717) B6599717
theorem B2933207 : Blo 1955435 2933207 := bstep (se 1 (by rfl) ⟨2199905, by rfl⟩ : syracuseStep 2933207 = 4399811) B4399811
theorem B1955471 : Blo 1955435 1955471 := bstep (se 1 (by rfl) ⟨1466603, by rfl⟩ : syracuseStep 1955471 = 2933207) B2933207
theorem B2933213 : Blo 1955435 2933213 := bbase (se 3 (by rfl) ⟨549977, by rfl⟩ : syracuseStep 2933213 = 1099955) (by norm_num)
theorem B1955475 : Blo 1955435 1955475 := bstep (se 1 (by rfl) ⟨1466606, by rfl⟩ : syracuseStep 1955475 = 2933213) B2933213
theorem B4399829 : Blo 1955435 4399829 := bbase (se 7 (by rfl) ⟨51560, by rfl⟩ : syracuseStep 4399829 = 103121) (by norm_num)
theorem B2933219 : Blo 1955435 2933219 := bstep (se 1 (by rfl) ⟨2199914, by rfl⟩ : syracuseStep 2933219 = 4399829) B4399829
theorem B1955479 : Blo 1955435 1955479 := bstep (se 1 (by rfl) ⟨1466609, by rfl⟩ : syracuseStep 1955479 = 2933219) B2933219
theorem B8352821 : Blo 1955435 8352821 := bbase (se 5 (by rfl) ⟨391538, by rfl⟩ : syracuseStep 8352821 = 783077) (by norm_num)
theorem B5568547 : Blo 1955435 5568547 := bstep (se 1 (by rfl) ⟨4176410, by rfl⟩ : syracuseStep 5568547 = 8352821) B8352821
theorem B7424729 : Blo 1955435 7424729 := bstep (se 2 (by rfl) ⟨2784273, by rfl⟩ : syracuseStep 7424729 = 5568547) B5568547
theorem B4949819 : Blo 1955435 4949819 := bstep (se 1 (by rfl) ⟨3712364, by rfl⟩ : syracuseStep 4949819 = 7424729) B7424729
theorem B3299879 : Blo 1955435 3299879 := bstep (se 1 (by rfl) ⟨2474909, by rfl⟩ : syracuseStep 3299879 = 4949819) B4949819
theorem B2199919 : Blo 1955435 2199919 := bstep (se 1 (by rfl) ⟨1649939, by rfl⟩ : syracuseStep 2199919 = 3299879) B3299879
theorem B2933225 : Blo 1955435 2933225 := bstep (se 2 (by rfl) ⟨1099959, by rfl⟩ : syracuseStep 2933225 = 2199919) B2199919
theorem B1955483 : Blo 1955435 1955483 := bstep (se 1 (by rfl) ⟨1466612, by rfl⟩ : syracuseStep 1955483 = 2933225) B2933225
theorem B15052085 : Blo 1955435 15052085 := bbase (se 5 (by rfl) ⟨705566, by rfl⟩ : syracuseStep 15052085 = 1411133) (by norm_num)
theorem B10034723 : Blo 1955435 10034723 := bstep (se 1 (by rfl) ⟨7526042, by rfl⟩ : syracuseStep 10034723 = 15052085) B15052085
theorem B26759261 : Blo 1955435 26759261 := bstep (se 3 (by rfl) ⟨5017361, by rfl⟩ : syracuseStep 26759261 = 10034723) B10034723
theorem B71358029 : Blo 1955435 71358029 := bstep (se 3 (by rfl) ⟨13379630, by rfl⟩ : syracuseStep 71358029 = 26759261) B26759261
theorem B47572019 : Blo 1955435 47572019 := bstep (se 1 (by rfl) ⟨35679014, by rfl⟩ : syracuseStep 47572019 = 71358029) B71358029
theorem B31714679 : Blo 1955435 31714679 := bstep (se 1 (by rfl) ⟨23786009, by rfl⟩ : syracuseStep 31714679 = 47572019) B47572019
theorem B21143119 : Blo 1955435 21143119 := bstep (se 1 (by rfl) ⟨15857339, by rfl⟩ : syracuseStep 21143119 = 31714679) B31714679
theorem B28190825 : Blo 1955435 28190825 := bstep (se 2 (by rfl) ⟨10571559, by rfl⟩ : syracuseStep 28190825 = 21143119) B21143119
theorem B18793883 : Blo 1955435 18793883 := bstep (se 1 (by rfl) ⟨14095412, by rfl⟩ : syracuseStep 18793883 = 28190825) B28190825
theorem B12529255 : Blo 1955435 12529255 := bstep (se 1 (by rfl) ⟨9396941, by rfl⟩ : syracuseStep 12529255 = 18793883) B18793883
theorem B16705673 : Blo 1955435 16705673 := bstep (se 2 (by rfl) ⟨6264627, by rfl⟩ : syracuseStep 16705673 = 12529255) B12529255
theorem B11137115 : Blo 1955435 11137115 := bstep (se 1 (by rfl) ⟨8352836, by rfl⟩ : syracuseStep 11137115 = 16705673) B16705673
theorem B7424743 : Blo 1955435 7424743 := bstep (se 1 (by rfl) ⟨5568557, by rfl⟩ : syracuseStep 7424743 = 11137115) B11137115
theorem B9899657 : Blo 1955435 9899657 := bstep (se 2 (by rfl) ⟨3712371, by rfl⟩ : syracuseStep 9899657 = 7424743) B7424743
theorem B6599771 : Blo 1955435 6599771 := bstep (se 1 (by rfl) ⟨4949828, by rfl⟩ : syracuseStep 6599771 = 9899657) B9899657
theorem B4399847 : Blo 1955435 4399847 := bstep (se 1 (by rfl) ⟨3299885, by rfl⟩ : syracuseStep 4399847 = 6599771) B6599771
theorem B2933231 : Blo 1955435 2933231 := bstep (se 1 (by rfl) ⟨2199923, by rfl⟩ : syracuseStep 2933231 = 4399847) B4399847
theorem B1955487 : Blo 1955435 1955487 := bstep (se 1 (by rfl) ⟨1466615, by rfl⟩ : syracuseStep 1955487 = 2933231) B2933231
theorem B2933237 : Blo 1955435 2933237 := bbase (se 5 (by rfl) ⟨137495, by rfl⟩ : syracuseStep 2933237 = 274991) (by norm_num)
theorem B1955491 : Blo 1955435 1955491 := bstep (se 1 (by rfl) ⟨1466618, by rfl⟩ : syracuseStep 1955491 = 2933237) B2933237
theorem B5568581 : Blo 1955435 5568581 := bbase (se 4 (by rfl) ⟨522054, by rfl⟩ : syracuseStep 5568581 = 1044109) (by norm_num)
theorem B3712387 : Blo 1955435 3712387 := bstep (se 1 (by rfl) ⟨2784290, by rfl⟩ : syracuseStep 3712387 = 5568581) B5568581
theorem B4949849 : Blo 1955435 4949849 := bstep (se 2 (by rfl) ⟨1856193, by rfl⟩ : syracuseStep 4949849 = 3712387) B3712387
theorem B3299899 : Blo 1955435 3299899 := bstep (se 1 (by rfl) ⟨2474924, by rfl⟩ : syracuseStep 3299899 = 4949849) B4949849
theorem B4399865 : Blo 1955435 4399865 := bstep (se 2 (by rfl) ⟨1649949, by rfl⟩ : syracuseStep 4399865 = 3299899) B3299899
theorem B2933243 : Blo 1955435 2933243 := bstep (se 1 (by rfl) ⟨2199932, by rfl⟩ : syracuseStep 2933243 = 4399865) B4399865
theorem B1955495 : Blo 1955435 1955495 := bstep (se 1 (by rfl) ⟨1466621, by rfl⟩ : syracuseStep 1955495 = 2933243) B2933243
theorem B2199937 : Blo 1955435 2199937 := bbase (se 2 (by rfl) ⟨824976, by rfl⟩ : syracuseStep 2199937 = 1649953) (by norm_num)
theorem B2933249 : Blo 1955435 2933249 := bstep (se 2 (by rfl) ⟨1099968, by rfl⟩ : syracuseStep 2933249 = 2199937) B2199937
theorem B1955499 : Blo 1955435 1955499 := bstep (se 1 (by rfl) ⟨1466624, by rfl⟩ : syracuseStep 1955499 = 2933249) B2933249
theorem B4949869 : Blo 1955435 4949869 := bbase (se 3 (by rfl) ⟨928100, by rfl⟩ : syracuseStep 4949869 = 1856201) (by norm_num)
theorem B6599825 : Blo 1955435 6599825 := bstep (se 2 (by rfl) ⟨2474934, by rfl⟩ : syracuseStep 6599825 = 4949869) B4949869
theorem B4399883 : Blo 1955435 4399883 := bstep (se 1 (by rfl) ⟨3299912, by rfl⟩ : syracuseStep 4399883 = 6599825) B6599825
theorem B2933255 : Blo 1955435 2933255 := bstep (se 1 (by rfl) ⟨2199941, by rfl⟩ : syracuseStep 2933255 = 4399883) B4399883
theorem B1955503 : Blo 1955435 1955503 := bstep (se 1 (by rfl) ⟨1466627, by rfl⟩ : syracuseStep 1955503 = 2933255) B2933255
theorem B2933261 : Blo 1955435 2933261 := bbase (se 3 (by rfl) ⟨549986, by rfl⟩ : syracuseStep 2933261 = 1099973) (by norm_num)
theorem B1955507 : Blo 1955435 1955507 := bstep (se 1 (by rfl) ⟨1466630, by rfl⟩ : syracuseStep 1955507 = 2933261) B2933261
theorem B4399901 : Blo 1955435 4399901 := bbase (se 3 (by rfl) ⟨824981, by rfl⟩ : syracuseStep 4399901 = 1649963) (by norm_num)
theorem B2933267 : Blo 1955435 2933267 := bstep (se 1 (by rfl) ⟨2199950, by rfl⟩ : syracuseStep 2933267 = 4399901) B4399901
theorem B1955511 : Blo 1955435 1955511 := bstep (se 1 (by rfl) ⟨1466633, by rfl⟩ : syracuseStep 1955511 = 2933267) B2933267
theorem B3299933 : Blo 1955435 3299933 := bbase (se 3 (by rfl) ⟨618737, by rfl⟩ : syracuseStep 3299933 = 1237475) (by norm_num)
theorem B2199955 : Blo 1955435 2199955 := bstep (se 1 (by rfl) ⟨1649966, by rfl⟩ : syracuseStep 2199955 = 3299933) B3299933
theorem B2933273 : Blo 1955435 2933273 := bstep (se 2 (by rfl) ⟨1099977, by rfl⟩ : syracuseStep 2933273 = 2199955) B2199955
theorem B1955515 : Blo 1955435 1955515 := bstep (se 1 (by rfl) ⟨1466636, by rfl⟩ : syracuseStep 1955515 = 2933273) B2933273
theorem B3132365 : Blo 1955435 3132365 := bbase (se 3 (by rfl) ⟨587318, by rfl⟩ : syracuseStep 3132365 = 1174637) (by norm_num)
theorem B8352973 : Blo 1955435 8352973 := bstep (se 3 (by rfl) ⟨1566182, by rfl⟩ : syracuseStep 8352973 = 3132365) B3132365
theorem B11137297 : Blo 1955435 11137297 := bstep (se 2 (by rfl) ⟨4176486, by rfl⟩ : syracuseStep 11137297 = 8352973) B8352973
theorem B14849729 : Blo 1955435 14849729 := bstep (se 2 (by rfl) ⟨5568648, by rfl⟩ : syracuseStep 14849729 = 11137297) B11137297
theorem B9899819 : Blo 1955435 9899819 := bstep (se 1 (by rfl) ⟨7424864, by rfl⟩ : syracuseStep 9899819 = 14849729) B14849729
theorem B6599879 : Blo 1955435 6599879 := bstep (se 1 (by rfl) ⟨4949909, by rfl⟩ : syracuseStep 6599879 = 9899819) B9899819
theorem B4399919 : Blo 1955435 4399919 := bstep (se 1 (by rfl) ⟨3299939, by rfl⟩ : syracuseStep 4399919 = 6599879) B6599879
theorem B2933279 : Blo 1955435 2933279 := bstep (se 1 (by rfl) ⟨2199959, by rfl⟩ : syracuseStep 2933279 = 4399919) B4399919
theorem B1955519 : Blo 1955435 1955519 := bstep (se 1 (by rfl) ⟨1466639, by rfl⟩ : syracuseStep 1955519 = 2933279) B2933279
theorem B2933285 : Blo 1955435 2933285 := bbase (se 4 (by rfl) ⟨274995, by rfl⟩ : syracuseStep 2933285 = 549991) (by norm_num)
theorem B1955523 : Blo 1955435 1955523 := bstep (se 1 (by rfl) ⟨1466642, by rfl⟩ : syracuseStep 1955523 = 2933285) B2933285
theorem B2474965 : Blo 1955435 2474965 := bbase (se 7 (by rfl) ⟨29003, by rfl⟩ : syracuseStep 2474965 = 58007) (by norm_num)
theorem B3299953 : Blo 1955435 3299953 := bstep (se 2 (by rfl) ⟨1237482, by rfl⟩ : syracuseStep 3299953 = 2474965) B2474965
theorem B4399937 : Blo 1955435 4399937 := bstep (se 2 (by rfl) ⟨1649976, by rfl⟩ : syracuseStep 4399937 = 3299953) B3299953
theorem B2933291 : Blo 1955435 2933291 := bstep (se 1 (by rfl) ⟨2199968, by rfl⟩ : syracuseStep 2933291 = 4399937) B4399937
theorem B1955527 : Blo 1955435 1955527 := bstep (se 1 (by rfl) ⟨1466645, by rfl⟩ : syracuseStep 1955527 = 2933291) B2933291
theorem B2199973 : Blo 1955435 2199973 := bbase (se 4 (by rfl) ⟨206247, by rfl⟩ : syracuseStep 2199973 = 412495) (by norm_num)
theorem B2933297 : Blo 1955435 2933297 := bstep (se 2 (by rfl) ⟨1099986, by rfl⟩ : syracuseStep 2933297 = 2199973) B2199973
theorem B1955531 : Blo 1955435 1955531 := bstep (se 1 (by rfl) ⟨1466648, by rfl⟩ : syracuseStep 1955531 = 2933297) B2933297
theorem B11893301 : Blo 1955435 11893301 := bbase (se 5 (by rfl) ⟨557498, by rfl⟩ : syracuseStep 11893301 = 1114997) (by norm_num)
theorem B7928867 : Blo 1955435 7928867 := bstep (se 1 (by rfl) ⟨5946650, by rfl⟩ : syracuseStep 7928867 = 11893301) B11893301
theorem B5285911 : Blo 1955435 5285911 := bstep (se 1 (by rfl) ⟨3964433, by rfl⟩ : syracuseStep 5285911 = 7928867) B7928867
theorem B7047881 : Blo 1955435 7047881 := bstep (se 2 (by rfl) ⟨2642955, by rfl⟩ : syracuseStep 7047881 = 5285911) B5285911
theorem B4698587 : Blo 1955435 4698587 := bstep (se 1 (by rfl) ⟨3523940, by rfl⟩ : syracuseStep 4698587 = 7047881) B7047881
theorem B12529565 : Blo 1955435 12529565 := bstep (se 3 (by rfl) ⟨2349293, by rfl⟩ : syracuseStep 12529565 = 4698587) B4698587
theorem B8353043 : Blo 1955435 8353043 := bstep (se 1 (by rfl) ⟨6264782, by rfl⟩ : syracuseStep 8353043 = 12529565) B12529565
theorem B5568695 : Blo 1955435 5568695 := bstep (se 1 (by rfl) ⟨4176521, by rfl⟩ : syracuseStep 5568695 = 8353043) B8353043
theorem B3712463 : Blo 1955435 3712463 := bstep (se 1 (by rfl) ⟨2784347, by rfl⟩ : syracuseStep 3712463 = 5568695) B5568695
theorem B2474975 : Blo 1955435 2474975 := bstep (se 1 (by rfl) ⟨1856231, by rfl⟩ : syracuseStep 2474975 = 3712463) B3712463
theorem B6599933 : Blo 1955435 6599933 := bstep (se 3 (by rfl) ⟨1237487, by rfl⟩ : syracuseStep 6599933 = 2474975) B2474975
theorem B4399955 : Blo 1955435 4399955 := bstep (se 1 (by rfl) ⟨3299966, by rfl⟩ : syracuseStep 4399955 = 6599933) B6599933
theorem B2933303 : Blo 1955435 2933303 := bstep (se 1 (by rfl) ⟨2199977, by rfl⟩ : syracuseStep 2933303 = 4399955) B4399955
theorem B1955535 : Blo 1955435 1955535 := bstep (se 1 (by rfl) ⟨1466651, by rfl⟩ : syracuseStep 1955535 = 2933303) B2933303
theorem B2933309 : Blo 1955435 2933309 := bbase (se 3 (by rfl) ⟨549995, by rfl⟩ : syracuseStep 2933309 = 1099991) (by norm_num)
theorem B1955539 : Blo 1955435 1955539 := bstep (se 1 (by rfl) ⟨1466654, by rfl⟩ : syracuseStep 1955539 = 2933309) B2933309
theorem B4399973 : Blo 1955435 4399973 := bbase (se 4 (by rfl) ⟨412497, by rfl⟩ : syracuseStep 4399973 = 824995) (by norm_num)
theorem B2933315 : Blo 1955435 2933315 := bstep (se 1 (by rfl) ⟨2199986, by rfl⟩ : syracuseStep 2933315 = 4399973) B4399973
theorem B1955543 : Blo 1955435 1955543 := bstep (se 1 (by rfl) ⟨1466657, by rfl⟩ : syracuseStep 1955543 = 2933315) B2933315
theorem B4949981 : Blo 1955435 4949981 := bbase (se 3 (by rfl) ⟨928121, by rfl⟩ : syracuseStep 4949981 = 1856243) (by norm_num)
theorem B3299987 : Blo 1955435 3299987 := bstep (se 1 (by rfl) ⟨2474990, by rfl⟩ : syracuseStep 3299987 = 4949981) B4949981
theorem B2199991 : Blo 1955435 2199991 := bstep (se 1 (by rfl) ⟨1649993, by rfl⟩ : syracuseStep 2199991 = 3299987) B3299987
theorem B2933321 : Blo 1955435 2933321 := bstep (se 2 (by rfl) ⟨1099995, by rfl⟩ : syracuseStep 2933321 = 2199991) B2199991
theorem B1955547 : Blo 1955435 1955547 := bstep (se 1 (by rfl) ⟨1466660, by rfl⟩ : syracuseStep 1955547 = 2933321) B2933321
theorem B3712493 : Blo 1955435 3712493 := bbase (se 3 (by rfl) ⟨696092, by rfl⟩ : syracuseStep 3712493 = 1392185) (by norm_num)
theorem B9899981 : Blo 1955435 9899981 := bstep (se 3 (by rfl) ⟨1856246, by rfl⟩ : syracuseStep 9899981 = 3712493) B3712493
theorem B6599987 : Blo 1955435 6599987 := bstep (se 1 (by rfl) ⟨4949990, by rfl⟩ : syracuseStep 6599987 = 9899981) B9899981
theorem B4399991 : Blo 1955435 4399991 := bstep (se 1 (by rfl) ⟨3299993, by rfl⟩ : syracuseStep 4399991 = 6599987) B6599987
theorem B2933327 : Blo 1955435 2933327 := bstep (se 1 (by rfl) ⟨2199995, by rfl⟩ : syracuseStep 2933327 = 4399991) B4399991
theorem B1955551 : Blo 1955435 1955551 := bstep (se 1 (by rfl) ⟨1466663, by rfl⟩ : syracuseStep 1955551 = 2933327) B2933327
theorem B2933333 : Blo 1955435 2933333 := bbase (se 8 (by rfl) ⟨17187, by rfl⟩ : syracuseStep 2933333 = 34375) (by norm_num)
theorem B1955555 : Blo 1955435 1955555 := bstep (se 1 (by rfl) ⟨1466666, by rfl⟩ : syracuseStep 1955555 = 2933333) B2933333
theorem B22578965 : Blo 1955435 22578965 := bbase (se 6 (by rfl) ⟨529194, by rfl⟩ : syracuseStep 22578965 = 1058389) (by norm_num)
theorem B15052643 : Blo 1955435 15052643 := bstep (se 1 (by rfl) ⟨11289482, by rfl⟩ : syracuseStep 15052643 = 22578965) B22578965
theorem B10035095 : Blo 1955435 10035095 := bstep (se 1 (by rfl) ⟨7526321, by rfl⟩ : syracuseStep 10035095 = 15052643) B15052643
theorem B26760253 : Blo 1955435 26760253 := bstep (se 3 (by rfl) ⟨5017547, by rfl⟩ : syracuseStep 26760253 = 10035095) B10035095
theorem B35680337 : Blo 1955435 35680337 := bstep (se 2 (by rfl) ⟨13380126, by rfl⟩ : syracuseStep 35680337 = 26760253) B26760253
theorem B23786891 : Blo 1955435 23786891 := bstep (se 1 (by rfl) ⟨17840168, by rfl⟩ : syracuseStep 23786891 = 35680337) B35680337
theorem B15857927 : Blo 1955435 15857927 := bstep (se 1 (by rfl) ⟨11893445, by rfl⟩ : syracuseStep 15857927 = 23786891) B23786891
theorem B10571951 : Blo 1955435 10571951 := bstep (se 1 (by rfl) ⟨7928963, by rfl⟩ : syracuseStep 10571951 = 15857927) B15857927
theorem B7047967 : Blo 1955435 7047967 := bstep (se 1 (by rfl) ⟨5285975, by rfl⟩ : syracuseStep 7047967 = 10571951) B10571951
theorem B9397289 : Blo 1955435 9397289 := bstep (se 2 (by rfl) ⟨3523983, by rfl⟩ : syracuseStep 9397289 = 7047967) B7047967
theorem B6264859 : Blo 1955435 6264859 := bstep (se 1 (by rfl) ⟨4698644, by rfl⟩ : syracuseStep 6264859 = 9397289) B9397289
theorem B8353145 : Blo 1955435 8353145 := bstep (se 2 (by rfl) ⟨3132429, by rfl⟩ : syracuseStep 8353145 = 6264859) B6264859
theorem B5568763 : Blo 1955435 5568763 := bstep (se 1 (by rfl) ⟨4176572, by rfl⟩ : syracuseStep 5568763 = 8353145) B8353145
theorem B7425017 : Blo 1955435 7425017 := bstep (se 2 (by rfl) ⟨2784381, by rfl⟩ : syracuseStep 7425017 = 5568763) B5568763
theorem B4950011 : Blo 1955435 4950011 := bstep (se 1 (by rfl) ⟨3712508, by rfl⟩ : syracuseStep 4950011 = 7425017) B7425017
theorem B3300007 : Blo 1955435 3300007 := bstep (se 1 (by rfl) ⟨2475005, by rfl⟩ : syracuseStep 3300007 = 4950011) B4950011
theorem B4400009 : Blo 1955435 4400009 := bstep (se 2 (by rfl) ⟨1650003, by rfl⟩ : syracuseStep 4400009 = 3300007) B3300007
theorem B2933339 : Blo 1955435 2933339 := bstep (se 1 (by rfl) ⟨2200004, by rfl⟩ : syracuseStep 2933339 = 4400009) B4400009
theorem B1955559 : Blo 1955435 1955559 := bstep (se 1 (by rfl) ⟨1466669, by rfl⟩ : syracuseStep 1955559 = 2933339) B2933339
theorem B2200009 : Blo 1955435 2200009 := bbase (se 2 (by rfl) ⟨825003, by rfl⟩ : syracuseStep 2200009 = 1650007) (by norm_num)
theorem B2933345 : Blo 1955435 2933345 := bstep (se 2 (by rfl) ⟨1100004, by rfl⟩ : syracuseStep 2933345 = 2200009) B2200009
theorem B1955563 : Blo 1955435 1955563 := bstep (se 1 (by rfl) ⟨1466672, by rfl⟩ : syracuseStep 1955563 = 2933345) B2933345
theorem B16706357 : Blo 1955435 16706357 := bbase (se 5 (by rfl) ⟨783110, by rfl⟩ : syracuseStep 16706357 = 1566221) (by norm_num)
theorem B11137571 : Blo 1955435 11137571 := bstep (se 1 (by rfl) ⟨8353178, by rfl⟩ : syracuseStep 11137571 = 16706357) B16706357
theorem B7425047 : Blo 1955435 7425047 := bstep (se 1 (by rfl) ⟨5568785, by rfl⟩ : syracuseStep 7425047 = 11137571) B11137571
theorem B4950031 : Blo 1955435 4950031 := bstep (se 1 (by rfl) ⟨3712523, by rfl⟩ : syracuseStep 4950031 = 7425047) B7425047
theorem B6600041 : Blo 1955435 6600041 := bstep (se 2 (by rfl) ⟨2475015, by rfl⟩ : syracuseStep 6600041 = 4950031) B4950031
theorem B4400027 : Blo 1955435 4400027 := bstep (se 1 (by rfl) ⟨3300020, by rfl⟩ : syracuseStep 4400027 = 6600041) B6600041
theorem B2933351 : Blo 1955435 2933351 := bstep (se 1 (by rfl) ⟨2200013, by rfl⟩ : syracuseStep 2933351 = 4400027) B4400027
theorem B1955567 : Blo 1955435 1955567 := bstep (se 1 (by rfl) ⟨1466675, by rfl⟩ : syracuseStep 1955567 = 2933351) B2933351
theorem B2933357 : Blo 1955435 2933357 := bbase (se 3 (by rfl) ⟨550004, by rfl⟩ : syracuseStep 2933357 = 1100009) (by norm_num)
theorem B1955571 : Blo 1955435 1955571 := bstep (se 1 (by rfl) ⟨1466678, by rfl⟩ : syracuseStep 1955571 = 2933357) B2933357
theorem B4400045 : Blo 1955435 4400045 := bbase (se 3 (by rfl) ⟨825008, by rfl⟩ : syracuseStep 4400045 = 1650017) (by norm_num)
theorem B2933363 : Blo 1955435 2933363 := bstep (se 1 (by rfl) ⟨2200022, by rfl⟩ : syracuseStep 2933363 = 4400045) B4400045
theorem B1955575 : Blo 1955435 1955575 := bstep (se 1 (by rfl) ⟨1466681, by rfl⟩ : syracuseStep 1955575 = 2933363) B2933363
theorem B5568821 : Blo 1955435 5568821 := bbase (se 5 (by rfl) ⟨261038, by rfl⟩ : syracuseStep 5568821 = 522077) (by norm_num)
theorem B3712547 : Blo 1955435 3712547 := bstep (se 1 (by rfl) ⟨2784410, by rfl⟩ : syracuseStep 3712547 = 5568821) B5568821
theorem B2475031 : Blo 1955435 2475031 := bstep (se 1 (by rfl) ⟨1856273, by rfl⟩ : syracuseStep 2475031 = 3712547) B3712547
theorem B3300041 : Blo 1955435 3300041 := bstep (se 2 (by rfl) ⟨1237515, by rfl⟩ : syracuseStep 3300041 = 2475031) B2475031
theorem B2200027 : Blo 1955435 2200027 := bstep (se 1 (by rfl) ⟨1650020, by rfl⟩ : syracuseStep 2200027 = 3300041) B3300041
theorem B2933369 : Blo 1955435 2933369 := bstep (se 2 (by rfl) ⟨1100013, by rfl⟩ : syracuseStep 2933369 = 2200027) B2200027
theorem B1955579 : Blo 1955435 1955579 := bstep (se 1 (by rfl) ⟨1466684, by rfl⟩ : syracuseStep 1955579 = 2933369) B2933369
theorem B2543033 : Blo 1955435 2543033 := bbase (se 2 (by rfl) ⟨953637, by rfl⟩ : syracuseStep 2543033 = 1907275) (by norm_num)
theorem B6781421 : Blo 1955435 6781421 := bstep (se 3 (by rfl) ⟨1271516, by rfl⟩ : syracuseStep 6781421 = 2543033) B2543033
theorem B4520947 : Blo 1955435 4520947 := bstep (se 1 (by rfl) ⟨3390710, by rfl⟩ : syracuseStep 4520947 = 6781421) B6781421
theorem B6027929 : Blo 1955435 6027929 := bstep (se 2 (by rfl) ⟨2260473, by rfl⟩ : syracuseStep 6027929 = 4520947) B4520947
theorem B4018619 : Blo 1955435 4018619 := bstep (se 1 (by rfl) ⟨3013964, by rfl⟩ : syracuseStep 4018619 = 6027929) B6027929
theorem B10716317 : Blo 1955435 10716317 := bstep (se 3 (by rfl) ⟨2009309, by rfl⟩ : syracuseStep 10716317 = 4018619) B4018619
theorem B7144211 : Blo 1955435 7144211 := bstep (se 1 (by rfl) ⟨5358158, by rfl⟩ : syracuseStep 7144211 = 10716317) B10716317
theorem B19051229 : Blo 1955435 19051229 := bstep (se 3 (by rfl) ⟨3572105, by rfl⟩ : syracuseStep 19051229 = 7144211) B7144211
theorem B12700819 : Blo 1955435 12700819 := bstep (se 1 (by rfl) ⟨9525614, by rfl⟩ : syracuseStep 12700819 = 19051229) B19051229
theorem B67737701 : Blo 1955435 67737701 := bstep (se 4 (by rfl) ⟨6350409, by rfl⟩ : syracuseStep 67737701 = 12700819) B12700819
theorem B45158467 : Blo 1955435 45158467 := bstep (se 1 (by rfl) ⟨33868850, by rfl⟩ : syracuseStep 45158467 = 67737701) B67737701
theorem B60211289 : Blo 1955435 60211289 := bstep (se 2 (by rfl) ⟨22579233, by rfl⟩ : syracuseStep 60211289 = 45158467) B45158467
theorem B40140859 : Blo 1955435 40140859 := bstep (se 1 (by rfl) ⟨30105644, by rfl⟩ : syracuseStep 40140859 = 60211289) B60211289
theorem B53521145 : Blo 1955435 53521145 := bstep (se 2 (by rfl) ⟨20070429, by rfl⟩ : syracuseStep 53521145 = 40140859) B40140859
theorem B35680763 : Blo 1955435 35680763 := bstep (se 1 (by rfl) ⟨26760572, by rfl⟩ : syracuseStep 35680763 = 53521145) B53521145
theorem B95148701 : Blo 1955435 95148701 := bstep (se 3 (by rfl) ⟨17840381, by rfl⟩ : syracuseStep 95148701 = 35680763) B35680763
theorem B63432467 : Blo 1955435 63432467 := bstep (se 1 (by rfl) ⟨47574350, by rfl⟩ : syracuseStep 63432467 = 95148701) B95148701
theorem B42288311 : Blo 1955435 42288311 := bstep (se 1 (by rfl) ⟨31716233, by rfl⟩ : syracuseStep 42288311 = 63432467) B63432467
theorem B28192207 : Blo 1955435 28192207 := bstep (se 1 (by rfl) ⟨21144155, by rfl⟩ : syracuseStep 28192207 = 42288311) B42288311
theorem B37589609 : Blo 1955435 37589609 := bstep (se 2 (by rfl) ⟨14096103, by rfl⟩ : syracuseStep 37589609 = 28192207) B28192207
theorem B25059739 : Blo 1955435 25059739 := bstep (se 1 (by rfl) ⟨18794804, by rfl⟩ : syracuseStep 25059739 = 37589609) B37589609
theorem B33412985 : Blo 1955435 33412985 := bstep (se 2 (by rfl) ⟨12529869, by rfl⟩ : syracuseStep 33412985 = 25059739) B25059739
theorem B22275323 : Blo 1955435 22275323 := bstep (se 1 (by rfl) ⟨16706492, by rfl⟩ : syracuseStep 22275323 = 33412985) B33412985
theorem B14850215 : Blo 1955435 14850215 := bstep (se 1 (by rfl) ⟨11137661, by rfl⟩ : syracuseStep 14850215 = 22275323) B22275323
theorem B9900143 : Blo 1955435 9900143 := bstep (se 1 (by rfl) ⟨7425107, by rfl⟩ : syracuseStep 9900143 = 14850215) B14850215
theorem B6600095 : Blo 1955435 6600095 := bstep (se 1 (by rfl) ⟨4950071, by rfl⟩ : syracuseStep 6600095 = 9900143) B9900143
theorem B4400063 : Blo 1955435 4400063 := bstep (se 1 (by rfl) ⟨3300047, by rfl⟩ : syracuseStep 4400063 = 6600095) B6600095
theorem B2933375 : Blo 1955435 2933375 := bstep (se 1 (by rfl) ⟨2200031, by rfl⟩ : syracuseStep 2933375 = 4400063) B4400063
theorem B1955583 : Blo 1955435 1955583 := bstep (se 1 (by rfl) ⟨1466687, by rfl⟩ : syracuseStep 1955583 = 2933375) B2933375
theorem B2933381 : Blo 1955435 2933381 := bbase (se 4 (by rfl) ⟨275004, by rfl⟩ : syracuseStep 2933381 = 550009) (by norm_num)
theorem B1955587 : Blo 1955435 1955587 := bstep (se 1 (by rfl) ⟨1466690, by rfl⟩ : syracuseStep 1955587 = 2933381) B2933381
theorem B3300061 : Blo 1955435 3300061 := bbase (se 3 (by rfl) ⟨618761, by rfl⟩ : syracuseStep 3300061 = 1237523) (by norm_num)
theorem B4400081 : Blo 1955435 4400081 := bstep (se 2 (by rfl) ⟨1650030, by rfl⟩ : syracuseStep 4400081 = 3300061) B3300061
theorem B2933387 : Blo 1955435 2933387 := bstep (se 1 (by rfl) ⟨2200040, by rfl⟩ : syracuseStep 2933387 = 4400081) B4400081
theorem B1955591 : Blo 1955435 1955591 := bstep (se 1 (by rfl) ⟨1466693, by rfl⟩ : syracuseStep 1955591 = 2933387) B2933387
theorem B2200045 : Blo 1955435 2200045 := bbase (se 3 (by rfl) ⟨412508, by rfl⟩ : syracuseStep 2200045 = 825017) (by norm_num)
theorem B2933393 : Blo 1955435 2933393 := bstep (se 2 (by rfl) ⟨1100022, by rfl⟩ : syracuseStep 2933393 = 2200045) B2200045
theorem B1955595 : Blo 1955435 1955595 := bstep (se 1 (by rfl) ⟨1466696, by rfl⟩ : syracuseStep 1955595 = 2933393) B2933393
theorem B6600149 : Blo 1955435 6600149 := bbase (se 7 (by rfl) ⟨77345, by rfl⟩ : syracuseStep 6600149 = 154691) (by norm_num)
theorem B4400099 : Blo 1955435 4400099 := bstep (se 1 (by rfl) ⟨3300074, by rfl⟩ : syracuseStep 4400099 = 6600149) B6600149
theorem B2933399 : Blo 1955435 2933399 := bstep (se 1 (by rfl) ⟨2200049, by rfl⟩ : syracuseStep 2933399 = 4400099) B4400099
theorem B1955599 : Blo 1955435 1955599 := bstep (se 1 (by rfl) ⟨1466699, by rfl⟩ : syracuseStep 1955599 = 2933399) B2933399
theorem B2933405 : Blo 1955435 2933405 := bbase (se 3 (by rfl) ⟨550013, by rfl⟩ : syracuseStep 2933405 = 1100027) (by norm_num)
theorem B1955603 : Blo 1955435 1955603 := bstep (se 1 (by rfl) ⟨1466702, by rfl⟩ : syracuseStep 1955603 = 2933405) B2933405
theorem B4400117 : Blo 1955435 4400117 := bbase (se 5 (by rfl) ⟨206255, by rfl⟩ : syracuseStep 4400117 = 412511) (by norm_num)
theorem B2933411 : Blo 1955435 2933411 := bstep (se 1 (by rfl) ⟨2200058, by rfl⟩ : syracuseStep 2933411 = 4400117) B4400117
theorem B1955607 : Blo 1955435 1955607 := bstep (se 1 (by rfl) ⟨1466705, by rfl⟩ : syracuseStep 1955607 = 2933411) B2933411
theorem B18084053 : Blo 1955435 18084053 := bbase (se 7 (by rfl) ⟨211922, by rfl⟩ : syracuseStep 18084053 = 423845) (by norm_num)
theorem B12056035 : Blo 1955435 12056035 := bstep (se 1 (by rfl) ⟨9042026, by rfl⟩ : syracuseStep 12056035 = 18084053) B18084053
theorem B16074713 : Blo 1955435 16074713 := bstep (se 2 (by rfl) ⟨6028017, by rfl⟩ : syracuseStep 16074713 = 12056035) B12056035
theorem B10716475 : Blo 1955435 10716475 := bstep (se 1 (by rfl) ⟨8037356, by rfl⟩ : syracuseStep 10716475 = 16074713) B16074713
theorem B14288633 : Blo 1955435 14288633 := bstep (se 2 (by rfl) ⟨5358237, by rfl⟩ : syracuseStep 14288633 = 10716475) B10716475
theorem B9525755 : Blo 1955435 9525755 := bstep (se 1 (by rfl) ⟨7144316, by rfl⟩ : syracuseStep 9525755 = 14288633) B14288633
theorem B6350503 : Blo 1955435 6350503 := bstep (se 1 (by rfl) ⟨4762877, by rfl⟩ : syracuseStep 6350503 = 9525755) B9525755
theorem B8467337 : Blo 1955435 8467337 := bstep (se 2 (by rfl) ⟨3175251, by rfl⟩ : syracuseStep 8467337 = 6350503) B6350503
theorem B5644891 : Blo 1955435 5644891 := bstep (se 1 (by rfl) ⟨4233668, by rfl⟩ : syracuseStep 5644891 = 8467337) B8467337
theorem B7526521 : Blo 1955435 7526521 := bstep (se 2 (by rfl) ⟨2822445, by rfl⟩ : syracuseStep 7526521 = 5644891) B5644891
theorem B10035361 : Blo 1955435 10035361 := bstep (se 2 (by rfl) ⟨3763260, by rfl⟩ : syracuseStep 10035361 = 7526521) B7526521
theorem B13380481 : Blo 1955435 13380481 := bstep (se 2 (by rfl) ⟨5017680, by rfl⟩ : syracuseStep 13380481 = 10035361) B10035361
theorem B17840641 : Blo 1955435 17840641 := bstep (se 2 (by rfl) ⟨6690240, by rfl⟩ : syracuseStep 17840641 = 13380481) B13380481
theorem B23787521 : Blo 1955435 23787521 := bstep (se 2 (by rfl) ⟨8920320, by rfl⟩ : syracuseStep 23787521 = 17840641) B17840641
theorem B15858347 : Blo 1955435 15858347 := bstep (se 1 (by rfl) ⟨11893760, by rfl⟩ : syracuseStep 15858347 = 23787521) B23787521
theorem B42288925 : Blo 1955435 42288925 := bstep (se 3 (by rfl) ⟨7929173, by rfl⟩ : syracuseStep 42288925 = 15858347) B15858347
theorem B56385233 : Blo 1955435 56385233 := bstep (se 2 (by rfl) ⟨21144462, by rfl⟩ : syracuseStep 56385233 = 42288925) B42288925
theorem B37590155 : Blo 1955435 37590155 := bstep (se 1 (by rfl) ⟨28192616, by rfl⟩ : syracuseStep 37590155 = 56385233) B56385233
theorem B25060103 : Blo 1955435 25060103 := bstep (se 1 (by rfl) ⟨18795077, by rfl⟩ : syracuseStep 25060103 = 37590155) B37590155
theorem B16706735 : Blo 1955435 16706735 := bstep (se 1 (by rfl) ⟨12530051, by rfl⟩ : syracuseStep 16706735 = 25060103) B25060103
theorem B11137823 : Blo 1955435 11137823 := bstep (se 1 (by rfl) ⟨8353367, by rfl⟩ : syracuseStep 11137823 = 16706735) B16706735
theorem B7425215 : Blo 1955435 7425215 := bstep (se 1 (by rfl) ⟨5568911, by rfl⟩ : syracuseStep 7425215 = 11137823) B11137823
theorem B4950143 : Blo 1955435 4950143 := bstep (se 1 (by rfl) ⟨3712607, by rfl⟩ : syracuseStep 4950143 = 7425215) B7425215
theorem B3300095 : Blo 1955435 3300095 := bstep (se 1 (by rfl) ⟨2475071, by rfl⟩ : syracuseStep 3300095 = 4950143) B4950143
theorem B2200063 : Blo 1955435 2200063 := bstep (se 1 (by rfl) ⟨1650047, by rfl⟩ : syracuseStep 2200063 = 3300095) B3300095
theorem B2933417 : Blo 1955435 2933417 := bstep (se 2 (by rfl) ⟨1100031, by rfl⟩ : syracuseStep 2933417 = 2200063) B2200063
theorem B1955611 : Blo 1955435 1955611 := bstep (se 1 (by rfl) ⟨1466708, by rfl⟩ : syracuseStep 1955611 = 2933417) B2933417
theorem B2784461 : Blo 1955435 2784461 := bbase (se 3 (by rfl) ⟨522086, by rfl⟩ : syracuseStep 2784461 = 1044173) (by norm_num)
theorem B7425229 : Blo 1955435 7425229 := bstep (se 3 (by rfl) ⟨1392230, by rfl⟩ : syracuseStep 7425229 = 2784461) B2784461
theorem B9900305 : Blo 1955435 9900305 := bstep (se 2 (by rfl) ⟨3712614, by rfl⟩ : syracuseStep 9900305 = 7425229) B7425229
theorem B6600203 : Blo 1955435 6600203 := bstep (se 1 (by rfl) ⟨4950152, by rfl⟩ : syracuseStep 6600203 = 9900305) B9900305
theorem B4400135 : Blo 1955435 4400135 := bstep (se 1 (by rfl) ⟨3300101, by rfl⟩ : syracuseStep 4400135 = 6600203) B6600203
theorem B2933423 : Blo 1955435 2933423 := bstep (se 1 (by rfl) ⟨2200067, by rfl⟩ : syracuseStep 2933423 = 4400135) B4400135
theorem B1955615 : Blo 1955435 1955615 := bstep (se 1 (by rfl) ⟨1466711, by rfl⟩ : syracuseStep 1955615 = 2933423) B2933423
theorem B2933429 : Blo 1955435 2933429 := bbase (se 5 (by rfl) ⟨137504, by rfl⟩ : syracuseStep 2933429 = 275009) (by norm_num)
theorem B1955619 : Blo 1955435 1955619 := bstep (se 1 (by rfl) ⟨1466714, by rfl⟩ : syracuseStep 1955619 = 2933429) B2933429
theorem B4950173 : Blo 1955435 4950173 := bbase (se 3 (by rfl) ⟨928157, by rfl⟩ : syracuseStep 4950173 = 1856315) (by norm_num)
theorem B3300115 : Blo 1955435 3300115 := bstep (se 1 (by rfl) ⟨2475086, by rfl⟩ : syracuseStep 3300115 = 4950173) B4950173
theorem B4400153 : Blo 1955435 4400153 := bstep (se 2 (by rfl) ⟨1650057, by rfl⟩ : syracuseStep 4400153 = 3300115) B3300115
theorem B2933435 : Blo 1955435 2933435 := bstep (se 1 (by rfl) ⟨2200076, by rfl⟩ : syracuseStep 2933435 = 4400153) B4400153
theorem B1955623 : Blo 1955435 1955623 := bstep (se 1 (by rfl) ⟨1466717, by rfl⟩ : syracuseStep 1955623 = 2933435) B2933435
theorem B2200081 : Blo 1955435 2200081 := bbase (se 2 (by rfl) ⟨825030, by rfl⟩ : syracuseStep 2200081 = 1650061) (by norm_num)
theorem B2933441 : Blo 1955435 2933441 := bstep (se 2 (by rfl) ⟨1100040, by rfl⟩ : syracuseStep 2933441 = 2200081) B2200081
theorem B1955627 : Blo 1955435 1955627 := bstep (se 1 (by rfl) ⟨1466720, by rfl⟩ : syracuseStep 1955627 = 2933441) B2933441
theorem B3712645 : Blo 1955435 3712645 := bbase (se 4 (by rfl) ⟨348060, by rfl⟩ : syracuseStep 3712645 = 696121) (by norm_num)
theorem B4950193 : Blo 1955435 4950193 := bstep (se 2 (by rfl) ⟨1856322, by rfl⟩ : syracuseStep 4950193 = 3712645) B3712645
theorem B6600257 : Blo 1955435 6600257 := bstep (se 2 (by rfl) ⟨2475096, by rfl⟩ : syracuseStep 6600257 = 4950193) B4950193
theorem B4400171 : Blo 1955435 4400171 := bstep (se 1 (by rfl) ⟨3300128, by rfl⟩ : syracuseStep 4400171 = 6600257) B6600257
theorem B2933447 : Blo 1955435 2933447 := bstep (se 1 (by rfl) ⟨2200085, by rfl⟩ : syracuseStep 2933447 = 4400171) B4400171
theorem B1955631 : Blo 1955435 1955631 := bstep (se 1 (by rfl) ⟨1466723, by rfl⟩ : syracuseStep 1955631 = 2933447) B2933447
theorem B2933453 : Blo 1955435 2933453 := bbase (se 3 (by rfl) ⟨550022, by rfl⟩ : syracuseStep 2933453 = 1100045) (by norm_num)
theorem B1955635 : Blo 1955435 1955635 := bstep (se 1 (by rfl) ⟨1466726, by rfl⟩ : syracuseStep 1955635 = 2933453) B2933453
theorem B4400189 : Blo 1955435 4400189 := bbase (se 3 (by rfl) ⟨825035, by rfl⟩ : syracuseStep 4400189 = 1650071) (by norm_num)
theorem B2933459 : Blo 1955435 2933459 := bstep (se 1 (by rfl) ⟨2200094, by rfl⟩ : syracuseStep 2933459 = 4400189) B4400189
theorem B1955639 : Blo 1955435 1955639 := bstep (se 1 (by rfl) ⟨1466729, by rfl⟩ : syracuseStep 1955639 = 2933459) B2933459
theorem B3300149 : Blo 1955435 3300149 := bbase (se 5 (by rfl) ⟨154694, by rfl⟩ : syracuseStep 3300149 = 309389) (by norm_num)
theorem B2200099 : Blo 1955435 2200099 := bstep (se 1 (by rfl) ⟨1650074, by rfl⟩ : syracuseStep 2200099 = 3300149) B3300149
theorem B2933465 : Blo 1955435 2933465 := bstep (se 2 (by rfl) ⟨1100049, by rfl⟩ : syracuseStep 2933465 = 2200099) B2200099
theorem B1955643 : Blo 1955435 1955643 := bstep (se 1 (by rfl) ⟨1466732, by rfl⟩ : syracuseStep 1955643 = 2933465) B2933465
theorem B5569013 : Blo 1955435 5569013 := bbase (se 5 (by rfl) ⟨261047, by rfl⟩ : syracuseStep 5569013 = 522095) (by norm_num)
theorem B14850701 : Blo 1955435 14850701 := bstep (se 3 (by rfl) ⟨2784506, by rfl⟩ : syracuseStep 14850701 = 5569013) B5569013
theorem B9900467 : Blo 1955435 9900467 := bstep (se 1 (by rfl) ⟨7425350, by rfl⟩ : syracuseStep 9900467 = 14850701) B14850701
theorem B6600311 : Blo 1955435 6600311 := bstep (se 1 (by rfl) ⟨4950233, by rfl⟩ : syracuseStep 6600311 = 9900467) B9900467
theorem B4400207 : Blo 1955435 4400207 := bstep (se 1 (by rfl) ⟨3300155, by rfl⟩ : syracuseStep 4400207 = 6600311) B6600311
theorem B2933471 : Blo 1955435 2933471 := bstep (se 1 (by rfl) ⟨2200103, by rfl⟩ : syracuseStep 2933471 = 4400207) B4400207
theorem B1955647 : Blo 1955435 1955647 := bstep (se 1 (by rfl) ⟨1466735, by rfl⟩ : syracuseStep 1955647 = 2933471) B2933471
theorem B2933477 : Blo 1955435 2933477 := bbase (se 4 (by rfl) ⟨275013, by rfl⟩ : syracuseStep 2933477 = 550027) (by norm_num)
theorem B1955651 : Blo 1955435 1955651 := bstep (se 1 (by rfl) ⟨1466738, by rfl⟩ : syracuseStep 1955651 = 2933477) B2933477
theorem B2088389 : Blo 1955435 2088389 := bbase (se 4 (by rfl) ⟨195786, by rfl⟩ : syracuseStep 2088389 = 391573) (by norm_num)
theorem B5569037 : Blo 1955435 5569037 := bstep (se 3 (by rfl) ⟨1044194, by rfl⟩ : syracuseStep 5569037 = 2088389) B2088389
theorem B3712691 : Blo 1955435 3712691 := bstep (se 1 (by rfl) ⟨2784518, by rfl⟩ : syracuseStep 3712691 = 5569037) B5569037
theorem B2475127 : Blo 1955435 2475127 := bstep (se 1 (by rfl) ⟨1856345, by rfl⟩ : syracuseStep 2475127 = 3712691) B3712691
theorem B3300169 : Blo 1955435 3300169 := bstep (se 2 (by rfl) ⟨1237563, by rfl⟩ : syracuseStep 3300169 = 2475127) B2475127
theorem B4400225 : Blo 1955435 4400225 := bstep (se 2 (by rfl) ⟨1650084, by rfl⟩ : syracuseStep 4400225 = 3300169) B3300169
theorem B2933483 : Blo 1955435 2933483 := bstep (se 1 (by rfl) ⟨2200112, by rfl⟩ : syracuseStep 2933483 = 4400225) B4400225
theorem B1955655 : Blo 1955435 1955655 := bstep (se 1 (by rfl) ⟨1466741, by rfl⟩ : syracuseStep 1955655 = 2933483) B2933483
theorem B2200117 : Blo 1955435 2200117 := bbase (se 5 (by rfl) ⟨103130, by rfl⟩ : syracuseStep 2200117 = 206261) (by norm_num)
theorem B2933489 : Blo 1955435 2933489 := bstep (se 2 (by rfl) ⟨1100058, by rfl⟩ : syracuseStep 2933489 = 2200117) B2200117
theorem B1955659 : Blo 1955435 1955659 := bstep (se 1 (by rfl) ⟨1466744, by rfl⟩ : syracuseStep 1955659 = 2933489) B2933489
theorem B2475137 : Blo 1955435 2475137 := bbase (se 2 (by rfl) ⟨928176, by rfl⟩ : syracuseStep 2475137 = 1856353) (by norm_num)
theorem B6600365 : Blo 1955435 6600365 := bstep (se 3 (by rfl) ⟨1237568, by rfl⟩ : syracuseStep 6600365 = 2475137) B2475137
theorem B4400243 : Blo 1955435 4400243 := bstep (se 1 (by rfl) ⟨3300182, by rfl⟩ : syracuseStep 4400243 = 6600365) B6600365
theorem B2933495 : Blo 1955435 2933495 := bstep (se 1 (by rfl) ⟨2200121, by rfl⟩ : syracuseStep 2933495 = 4400243) B4400243
theorem B1955663 : Blo 1955435 1955663 := bstep (se 1 (by rfl) ⟨1466747, by rfl⟩ : syracuseStep 1955663 = 2933495) B2933495
theorem B2933501 : Blo 1955435 2933501 := bbase (se 3 (by rfl) ⟨550031, by rfl⟩ : syracuseStep 2933501 = 1100063) (by norm_num)
theorem B1955667 : Blo 1955435 1955667 := bstep (se 1 (by rfl) ⟨1466750, by rfl⟩ : syracuseStep 1955667 = 2933501) B2933501
theorem B4400261 : Blo 1955435 4400261 := bbase (se 4 (by rfl) ⟨412524, by rfl⟩ : syracuseStep 4400261 = 825049) (by norm_num)
theorem B2933507 : Blo 1955435 2933507 := bstep (se 1 (by rfl) ⟨2200130, by rfl⟩ : syracuseStep 2933507 = 4400261) B4400261
theorem B1955671 : Blo 1955435 1955671 := bstep (se 1 (by rfl) ⟨1466753, by rfl⟩ : syracuseStep 1955671 = 2933507) B2933507
theorem B4176821 : Blo 1955435 4176821 := bbase (se 5 (by rfl) ⟨195788, by rfl⟩ : syracuseStep 4176821 = 391577) (by norm_num)
theorem B2784547 : Blo 1955435 2784547 := bstep (se 1 (by rfl) ⟨2088410, by rfl⟩ : syracuseStep 2784547 = 4176821) B4176821
theorem B3712729 : Blo 1955435 3712729 := bstep (se 2 (by rfl) ⟨1392273, by rfl⟩ : syracuseStep 3712729 = 2784547) B2784547
theorem B4950305 : Blo 1955435 4950305 := bstep (se 2 (by rfl) ⟨1856364, by rfl⟩ : syracuseStep 4950305 = 3712729) B3712729
theorem B3300203 : Blo 1955435 3300203 := bstep (se 1 (by rfl) ⟨2475152, by rfl⟩ : syracuseStep 3300203 = 4950305) B4950305
theorem B2200135 : Blo 1955435 2200135 := bstep (se 1 (by rfl) ⟨1650101, by rfl⟩ : syracuseStep 2200135 = 3300203) B3300203
theorem B2933513 : Blo 1955435 2933513 := bstep (se 2 (by rfl) ⟨1100067, by rfl⟩ : syracuseStep 2933513 = 2200135) B2200135
theorem B1955675 : Blo 1955435 1955675 := bstep (se 1 (by rfl) ⟨1466756, by rfl⟩ : syracuseStep 1955675 = 2933513) B2933513
theorem B9900629 : Blo 1955435 9900629 := bbase (se 8 (by rfl) ⟨58011, by rfl⟩ : syracuseStep 9900629 = 116023) (by norm_num)
theorem B6600419 : Blo 1955435 6600419 := bstep (se 1 (by rfl) ⟨4950314, by rfl⟩ : syracuseStep 6600419 = 9900629) B9900629
theorem B4400279 : Blo 1955435 4400279 := bstep (se 1 (by rfl) ⟨3300209, by rfl⟩ : syracuseStep 4400279 = 6600419) B6600419
theorem B2933519 : Blo 1955435 2933519 := bstep (se 1 (by rfl) ⟨2200139, by rfl⟩ : syracuseStep 2933519 = 4400279) B4400279
theorem B1955679 : Blo 1955435 1955679 := bstep (se 1 (by rfl) ⟨1466759, by rfl⟩ : syracuseStep 1955679 = 2933519) B2933519
theorem B2933525 : Blo 1955435 2933525 := bbase (se 6 (by rfl) ⟨68754, by rfl⟩ : syracuseStep 2933525 = 137509) (by norm_num)
theorem B1955683 : Blo 1955435 1955683 := bstep (se 1 (by rfl) ⟨1466762, by rfl⟩ : syracuseStep 1955683 = 2933525) B2933525
theorem B3390893 : Blo 1955435 3390893 := bbase (se 3 (by rfl) ⟨635792, by rfl⟩ : syracuseStep 3390893 = 1271585) (by norm_num)
theorem B2260595 : Blo 1955435 2260595 := bstep (se 1 (by rfl) ⟨1695446, by rfl⟩ : syracuseStep 2260595 = 3390893) B3390893
theorem B6028253 : Blo 1955435 6028253 := bstep (se 3 (by rfl) ⟨1130297, by rfl⟩ : syracuseStep 6028253 = 2260595) B2260595
theorem B4018835 : Blo 1955435 4018835 := bstep (se 1 (by rfl) ⟨3014126, by rfl⟩ : syracuseStep 4018835 = 6028253) B6028253
theorem B2679223 : Blo 1955435 2679223 := bstep (se 1 (by rfl) ⟨2009417, by rfl⟩ : syracuseStep 2679223 = 4018835) B4018835
theorem B3572297 : Blo 1955435 3572297 := bstep (se 2 (by rfl) ⟨1339611, by rfl⟩ : syracuseStep 3572297 = 2679223) B2679223
theorem B2381531 : Blo 1955435 2381531 := bstep (se 1 (by rfl) ⟨1786148, by rfl⟩ : syracuseStep 2381531 = 3572297) B3572297
theorem B25402997 : Blo 1955435 25402997 := bstep (se 5 (by rfl) ⟨1190765, by rfl⟩ : syracuseStep 25402997 = 2381531) B2381531
theorem B16935331 : Blo 1955435 16935331 := bstep (se 1 (by rfl) ⟨12701498, by rfl⟩ : syracuseStep 16935331 = 25402997) B25402997
theorem B22580441 : Blo 1955435 22580441 := bstep (se 2 (by rfl) ⟨8467665, by rfl⟩ : syracuseStep 22580441 = 16935331) B16935331
theorem B15053627 : Blo 1955435 15053627 := bstep (se 1 (by rfl) ⟨11290220, by rfl⟩ : syracuseStep 15053627 = 22580441) B22580441
theorem B10035751 : Blo 1955435 10035751 := bstep (se 1 (by rfl) ⟨7526813, by rfl⟩ : syracuseStep 10035751 = 15053627) B15053627
theorem B13381001 : Blo 1955435 13381001 := bstep (se 2 (by rfl) ⟨5017875, by rfl⟩ : syracuseStep 13381001 = 10035751) B10035751
theorem B8920667 : Blo 1955435 8920667 := bstep (se 1 (by rfl) ⟨6690500, by rfl⟩ : syracuseStep 8920667 = 13381001) B13381001
theorem B5947111 : Blo 1955435 5947111 := bstep (se 1 (by rfl) ⟨4460333, by rfl⟩ : syracuseStep 5947111 = 8920667) B8920667
theorem B31717925 : Blo 1955435 31717925 := bstep (se 4 (by rfl) ⟨2973555, by rfl⟩ : syracuseStep 31717925 = 5947111) B5947111
theorem B21145283 : Blo 1955435 21145283 := bstep (se 1 (by rfl) ⟨15858962, by rfl⟩ : syracuseStep 21145283 = 31717925) B31717925
theorem B14096855 : Blo 1955435 14096855 := bstep (se 1 (by rfl) ⟨10572641, by rfl⟩ : syracuseStep 14096855 = 21145283) B21145283
theorem B37591613 : Blo 1955435 37591613 := bstep (se 3 (by rfl) ⟨7048427, by rfl⟩ : syracuseStep 37591613 = 14096855) B14096855
theorem B25061075 : Blo 1955435 25061075 := bstep (se 1 (by rfl) ⟨18795806, by rfl⟩ : syracuseStep 25061075 = 37591613) B37591613
theorem B16707383 : Blo 1955435 16707383 := bstep (se 1 (by rfl) ⟨12530537, by rfl⟩ : syracuseStep 16707383 = 25061075) B25061075
theorem B11138255 : Blo 1955435 11138255 := bstep (se 1 (by rfl) ⟨8353691, by rfl⟩ : syracuseStep 11138255 = 16707383) B16707383
theorem B7425503 : Blo 1955435 7425503 := bstep (se 1 (by rfl) ⟨5569127, by rfl⟩ : syracuseStep 7425503 = 11138255) B11138255
theorem B4950335 : Blo 1955435 4950335 := bstep (se 1 (by rfl) ⟨3712751, by rfl⟩ : syracuseStep 4950335 = 7425503) B7425503
theorem B3300223 : Blo 1955435 3300223 := bstep (se 1 (by rfl) ⟨2475167, by rfl⟩ : syracuseStep 3300223 = 4950335) B4950335
theorem B4400297 : Blo 1955435 4400297 := bstep (se 2 (by rfl) ⟨1650111, by rfl⟩ : syracuseStep 4400297 = 3300223) B3300223
theorem B2933531 : Blo 1955435 2933531 := bstep (se 1 (by rfl) ⟨2200148, by rfl⟩ : syracuseStep 2933531 = 4400297) B4400297
theorem B1955687 : Blo 1955435 1955687 := bstep (se 1 (by rfl) ⟨1466765, by rfl⟩ : syracuseStep 1955687 = 2933531) B2933531
theorem B2200153 : Blo 1955435 2200153 := bbase (se 2 (by rfl) ⟨825057, by rfl⟩ : syracuseStep 2200153 = 1650115) (by norm_num)
theorem B2933537 : Blo 1955435 2933537 := bstep (se 2 (by rfl) ⟨1100076, by rfl⟩ : syracuseStep 2933537 = 2200153) B2200153
theorem B1955691 : Blo 1955435 1955691 := bstep (se 1 (by rfl) ⟨1466768, by rfl⟩ : syracuseStep 1955691 = 2933537) B2933537
theorem B5358469 : Blo 1955435 5358469 := bbase (se 4 (by rfl) ⟨502356, by rfl⟩ : syracuseStep 5358469 = 1004713) (by norm_num)
theorem B7144625 : Blo 1955435 7144625 := bstep (se 2 (by rfl) ⟨2679234, by rfl⟩ : syracuseStep 7144625 = 5358469) B5358469
theorem B19052333 : Blo 1955435 19052333 := bstep (se 3 (by rfl) ⟨3572312, by rfl⟩ : syracuseStep 19052333 = 7144625) B7144625
theorem B12701555 : Blo 1955435 12701555 := bstep (se 1 (by rfl) ⟨9526166, by rfl⟩ : syracuseStep 12701555 = 19052333) B19052333
theorem B8467703 : Blo 1955435 8467703 := bstep (se 1 (by rfl) ⟨6350777, by rfl⟩ : syracuseStep 8467703 = 12701555) B12701555
theorem B5645135 : Blo 1955435 5645135 := bstep (se 1 (by rfl) ⟨4233851, by rfl⟩ : syracuseStep 5645135 = 8467703) B8467703
theorem B3763423 : Blo 1955435 3763423 := bstep (se 1 (by rfl) ⟨2822567, by rfl⟩ : syracuseStep 3763423 = 5645135) B5645135
theorem B5017897 : Blo 1955435 5017897 := bstep (se 2 (by rfl) ⟨1881711, by rfl⟩ : syracuseStep 5017897 = 3763423) B3763423
theorem B6690529 : Blo 1955435 6690529 := bstep (se 2 (by rfl) ⟨2508948, by rfl⟩ : syracuseStep 6690529 = 5017897) B5017897
theorem B8920705 : Blo 1955435 8920705 := bstep (se 2 (by rfl) ⟨3345264, by rfl⟩ : syracuseStep 8920705 = 6690529) B6690529
theorem B11894273 : Blo 1955435 11894273 := bstep (se 2 (by rfl) ⟨4460352, by rfl⟩ : syracuseStep 11894273 = 8920705) B8920705
theorem B7929515 : Blo 1955435 7929515 := bstep (se 1 (by rfl) ⟨5947136, by rfl⟩ : syracuseStep 7929515 = 11894273) B11894273
theorem B21145373 : Blo 1955435 21145373 := bstep (se 3 (by rfl) ⟨3964757, by rfl⟩ : syracuseStep 21145373 = 7929515) B7929515
theorem B14096915 : Blo 1955435 14096915 := bstep (se 1 (by rfl) ⟨10572686, by rfl⟩ : syracuseStep 14096915 = 21145373) B21145373
theorem B9397943 : Blo 1955435 9397943 := bstep (se 1 (by rfl) ⟨7048457, by rfl⟩ : syracuseStep 9397943 = 14096915) B14096915
theorem B6265295 : Blo 1955435 6265295 := bstep (se 1 (by rfl) ⟨4698971, by rfl⟩ : syracuseStep 6265295 = 9397943) B9397943
theorem B4176863 : Blo 1955435 4176863 := bstep (se 1 (by rfl) ⟨3132647, by rfl⟩ : syracuseStep 4176863 = 6265295) B6265295
theorem B2784575 : Blo 1955435 2784575 := bstep (se 1 (by rfl) ⟨2088431, by rfl⟩ : syracuseStep 2784575 = 4176863) B4176863
theorem B7425533 : Blo 1955435 7425533 := bstep (se 3 (by rfl) ⟨1392287, by rfl⟩ : syracuseStep 7425533 = 2784575) B2784575
theorem B4950355 : Blo 1955435 4950355 := bstep (se 1 (by rfl) ⟨3712766, by rfl⟩ : syracuseStep 4950355 = 7425533) B7425533
theorem B6600473 : Blo 1955435 6600473 := bstep (se 2 (by rfl) ⟨2475177, by rfl⟩ : syracuseStep 6600473 = 4950355) B4950355
theorem B4400315 : Blo 1955435 4400315 := bstep (se 1 (by rfl) ⟨3300236, by rfl⟩ : syracuseStep 4400315 = 6600473) B6600473
theorem B2933543 : Blo 1955435 2933543 := bstep (se 1 (by rfl) ⟨2200157, by rfl⟩ : syracuseStep 2933543 = 4400315) B4400315
theorem B1955695 : Blo 1955435 1955695 := bstep (se 1 (by rfl) ⟨1466771, by rfl⟩ : syracuseStep 1955695 = 2933543) B2933543
theorem B2933549 : Blo 1955435 2933549 := bbase (se 3 (by rfl) ⟨550040, by rfl⟩ : syracuseStep 2933549 = 1100081) (by norm_num)
theorem B1955699 : Blo 1955435 1955699 := bstep (se 1 (by rfl) ⟨1466774, by rfl⟩ : syracuseStep 1955699 = 2933549) B2933549
theorem B4400333 : Blo 1955435 4400333 := bbase (se 3 (by rfl) ⟨825062, by rfl⟩ : syracuseStep 4400333 = 1650125) (by norm_num)
theorem B2933555 : Blo 1955435 2933555 := bstep (se 1 (by rfl) ⟨2200166, by rfl⟩ : syracuseStep 2933555 = 4400333) B4400333
theorem B1955703 : Blo 1955435 1955703 := bstep (se 1 (by rfl) ⟨1466777, by rfl⟩ : syracuseStep 1955703 = 2933555) B2933555
theorem B2475193 : Blo 1955435 2475193 := bbase (se 2 (by rfl) ⟨928197, by rfl⟩ : syracuseStep 2475193 = 1856395) (by norm_num)
theorem B3300257 : Blo 1955435 3300257 := bstep (se 2 (by rfl) ⟨1237596, by rfl⟩ : syracuseStep 3300257 = 2475193) B2475193
theorem B2200171 : Blo 1955435 2200171 := bstep (se 1 (by rfl) ⟨1650128, by rfl⟩ : syracuseStep 2200171 = 3300257) B3300257
theorem B2933561 : Blo 1955435 2933561 := bstep (se 2 (by rfl) ⟨1100085, by rfl⟩ : syracuseStep 2933561 = 2200171) B2200171
theorem B1955707 : Blo 1955435 1955707 := bstep (se 1 (by rfl) ⟨1466780, by rfl⟩ : syracuseStep 1955707 = 2933561) B2933561
theorem B3345293 : Blo 1955435 3345293 := bbase (se 3 (by rfl) ⟨627242, by rfl⟩ : syracuseStep 3345293 = 1254485) (by norm_num)
theorem B2230195 : Blo 1955435 2230195 := bstep (se 1 (by rfl) ⟨1672646, by rfl⟩ : syracuseStep 2230195 = 3345293) B3345293
theorem B2973593 : Blo 1955435 2973593 := bstep (se 2 (by rfl) ⟨1115097, by rfl⟩ : syracuseStep 2973593 = 2230195) B2230195
theorem B1982395 : Blo 1955435 1982395 := bstep (se 1 (by rfl) ⟨1486796, by rfl⟩ : syracuseStep 1982395 = 2973593) B2973593
theorem B2643193 : Blo 1955435 2643193 := bstep (se 2 (by rfl) ⟨991197, by rfl⟩ : syracuseStep 2643193 = 1982395) B1982395
theorem B3524257 : Blo 1955435 3524257 := bstep (se 2 (by rfl) ⟨1321596, by rfl⟩ : syracuseStep 3524257 = 2643193) B2643193
theorem B4699009 : Blo 1955435 4699009 := bstep (se 2 (by rfl) ⟨1762128, by rfl⟩ : syracuseStep 4699009 = 3524257) B3524257
theorem B6265345 : Blo 1955435 6265345 := bstep (se 2 (by rfl) ⟨2349504, by rfl⟩ : syracuseStep 6265345 = 4699009) B4699009
theorem B8353793 : Blo 1955435 8353793 := bstep (se 2 (by rfl) ⟨3132672, by rfl⟩ : syracuseStep 8353793 = 6265345) B6265345
theorem B22276781 : Blo 1955435 22276781 := bstep (se 3 (by rfl) ⟨4176896, by rfl⟩ : syracuseStep 22276781 = 8353793) B8353793
theorem B14851187 : Blo 1955435 14851187 := bstep (se 1 (by rfl) ⟨11138390, by rfl⟩ : syracuseStep 14851187 = 22276781) B22276781
theorem B9900791 : Blo 1955435 9900791 := bstep (se 1 (by rfl) ⟨7425593, by rfl⟩ : syracuseStep 9900791 = 14851187) B14851187
theorem B6600527 : Blo 1955435 6600527 := bstep (se 1 (by rfl) ⟨4950395, by rfl⟩ : syracuseStep 6600527 = 9900791) B9900791
theorem B4400351 : Blo 1955435 4400351 := bstep (se 1 (by rfl) ⟨3300263, by rfl⟩ : syracuseStep 4400351 = 6600527) B6600527
theorem B2933567 : Blo 1955435 2933567 := bstep (se 1 (by rfl) ⟨2200175, by rfl⟩ : syracuseStep 2933567 = 4400351) B4400351
theorem B1955711 : Blo 1955435 1955711 := bstep (se 1 (by rfl) ⟨1466783, by rfl⟩ : syracuseStep 1955711 = 2933567) B2933567
theorem B2933573 : Blo 1955435 2933573 := bbase (se 4 (by rfl) ⟨275022, by rfl⟩ : syracuseStep 2933573 = 550045) (by norm_num)
theorem B1955715 : Blo 1955435 1955715 := bstep (se 1 (by rfl) ⟨1466786, by rfl⟩ : syracuseStep 1955715 = 2933573) B2933573
theorem B3300277 : Blo 1955435 3300277 := bbase (se 5 (by rfl) ⟨154700, by rfl⟩ : syracuseStep 3300277 = 309401) (by norm_num)
theorem B4400369 : Blo 1955435 4400369 := bstep (se 2 (by rfl) ⟨1650138, by rfl⟩ : syracuseStep 4400369 = 3300277) B3300277
theorem B2933579 : Blo 1955435 2933579 := bstep (se 1 (by rfl) ⟨2200184, by rfl⟩ : syracuseStep 2933579 = 4400369) B4400369
theorem B1955719 : Blo 1955435 1955719 := bstep (se 1 (by rfl) ⟨1466789, by rfl⟩ : syracuseStep 1955719 = 2933579) B2933579
theorem B2200189 : Blo 1955435 2200189 := bbase (se 3 (by rfl) ⟨412535, by rfl⟩ : syracuseStep 2200189 = 825071) (by norm_num)
theorem B2933585 : Blo 1955435 2933585 := bstep (se 2 (by rfl) ⟨1100094, by rfl⟩ : syracuseStep 2933585 = 2200189) B2200189
theorem B1955723 : Blo 1955435 1955723 := bstep (se 1 (by rfl) ⟨1466792, by rfl⟩ : syracuseStep 1955723 = 2933585) B2933585
theorem B6600581 : Blo 1955435 6600581 := bbase (se 4 (by rfl) ⟨618804, by rfl⟩ : syracuseStep 6600581 = 1237609) (by norm_num)
theorem B4400387 : Blo 1955435 4400387 := bstep (se 1 (by rfl) ⟨3300290, by rfl⟩ : syracuseStep 4400387 = 6600581) B6600581
theorem B2933591 : Blo 1955435 2933591 := bstep (se 1 (by rfl) ⟨2200193, by rfl⟩ : syracuseStep 2933591 = 4400387) B4400387
theorem B1955727 : Blo 1955435 1955727 := bstep (se 1 (by rfl) ⟨1466795, by rfl⟩ : syracuseStep 1955727 = 2933591) B2933591
theorem B2933597 : Blo 1955435 2933597 := bbase (se 3 (by rfl) ⟨550049, by rfl⟩ : syracuseStep 2933597 = 1100099) (by norm_num)
theorem B1955731 : Blo 1955435 1955731 := bstep (se 1 (by rfl) ⟨1466798, by rfl⟩ : syracuseStep 1955731 = 2933597) B2933597
theorem B4400405 : Blo 1955435 4400405 := bbase (se 6 (by rfl) ⟨103134, by rfl⟩ : syracuseStep 4400405 = 206269) (by norm_num)
theorem B2933603 : Blo 1955435 2933603 := bstep (se 1 (by rfl) ⟨2200202, by rfl⟩ : syracuseStep 2933603 = 4400405) B4400405
theorem B1955735 : Blo 1955435 1955735 := bstep (se 1 (by rfl) ⟨1466801, by rfl⟩ : syracuseStep 1955735 = 2933603) B2933603
theorem B7425701 : Blo 1955435 7425701 := bbase (se 4 (by rfl) ⟨696159, by rfl⟩ : syracuseStep 7425701 = 1392319) (by norm_num)
theorem B4950467 : Blo 1955435 4950467 := bstep (se 1 (by rfl) ⟨3712850, by rfl⟩ : syracuseStep 4950467 = 7425701) B7425701
theorem B3300311 : Blo 1955435 3300311 := bstep (se 1 (by rfl) ⟨2475233, by rfl⟩ : syracuseStep 3300311 = 4950467) B4950467
theorem B2200207 : Blo 1955435 2200207 := bstep (se 1 (by rfl) ⟨1650155, by rfl⟩ : syracuseStep 2200207 = 3300311) B3300311
theorem B2933609 : Blo 1955435 2933609 := bstep (se 2 (by rfl) ⟨1100103, by rfl⟩ : syracuseStep 2933609 = 2200207) B2200207
theorem B1955739 : Blo 1955435 1955739 := bstep (se 1 (by rfl) ⟨1466804, by rfl⟩ : syracuseStep 1955739 = 2933609) B2933609
theorem B4176965 : Blo 1955435 4176965 := bbase (se 4 (by rfl) ⟨391590, by rfl⟩ : syracuseStep 4176965 = 783181) (by norm_num)
theorem B11138573 : Blo 1955435 11138573 := bstep (se 3 (by rfl) ⟨2088482, by rfl⟩ : syracuseStep 11138573 = 4176965) B4176965
theorem B7425715 : Blo 1955435 7425715 := bstep (se 1 (by rfl) ⟨5569286, by rfl⟩ : syracuseStep 7425715 = 11138573) B11138573
theorem B9900953 : Blo 1955435 9900953 := bstep (se 2 (by rfl) ⟨3712857, by rfl⟩ : syracuseStep 9900953 = 7425715) B7425715
theorem B6600635 : Blo 1955435 6600635 := bstep (se 1 (by rfl) ⟨4950476, by rfl⟩ : syracuseStep 6600635 = 9900953) B9900953
theorem B4400423 : Blo 1955435 4400423 := bstep (se 1 (by rfl) ⟨3300317, by rfl⟩ : syracuseStep 4400423 = 6600635) B6600635
theorem B2933615 : Blo 1955435 2933615 := bstep (se 1 (by rfl) ⟨2200211, by rfl⟩ : syracuseStep 2933615 = 4400423) B4400423
theorem B1955743 : Blo 1955435 1955743 := bstep (se 1 (by rfl) ⟨1466807, by rfl⟩ : syracuseStep 1955743 = 2933615) B2933615
theorem B2933621 : Blo 1955435 2933621 := bbase (se 5 (by rfl) ⟨137513, by rfl⟩ : syracuseStep 2933621 = 275027) (by norm_num)
theorem B1955747 : Blo 1955435 1955747 := bstep (se 1 (by rfl) ⟨1466810, by rfl⟩ : syracuseStep 1955747 = 2933621) B2933621
theorem B9398213 : Blo 1955435 9398213 := bbase (se 4 (by rfl) ⟨881082, by rfl⟩ : syracuseStep 9398213 = 1762165) (by norm_num)
theorem B6265475 : Blo 1955435 6265475 := bstep (se 1 (by rfl) ⟨4699106, by rfl⟩ : syracuseStep 6265475 = 9398213) B9398213
theorem B4176983 : Blo 1955435 4176983 := bstep (se 1 (by rfl) ⟨3132737, by rfl⟩ : syracuseStep 4176983 = 6265475) B6265475
theorem B2784655 : Blo 1955435 2784655 := bstep (se 1 (by rfl) ⟨2088491, by rfl⟩ : syracuseStep 2784655 = 4176983) B4176983
theorem B3712873 : Blo 1955435 3712873 := bstep (se 2 (by rfl) ⟨1392327, by rfl⟩ : syracuseStep 3712873 = 2784655) B2784655
theorem B4950497 : Blo 1955435 4950497 := bstep (se 2 (by rfl) ⟨1856436, by rfl⟩ : syracuseStep 4950497 = 3712873) B3712873
theorem B3300331 : Blo 1955435 3300331 := bstep (se 1 (by rfl) ⟨2475248, by rfl⟩ : syracuseStep 3300331 = 4950497) B4950497
theorem B4400441 : Blo 1955435 4400441 := bstep (se 2 (by rfl) ⟨1650165, by rfl⟩ : syracuseStep 4400441 = 3300331) B3300331
theorem B2933627 : Blo 1955435 2933627 := bstep (se 1 (by rfl) ⟨2200220, by rfl⟩ : syracuseStep 2933627 = 4400441) B4400441
theorem B1955751 : Blo 1955435 1955751 := bstep (se 1 (by rfl) ⟨1466813, by rfl⟩ : syracuseStep 1955751 = 2933627) B2933627
theorem B2200225 : Blo 1955435 2200225 := bbase (se 2 (by rfl) ⟨825084, by rfl⟩ : syracuseStep 2200225 = 1650169) (by norm_num)
theorem B2933633 : Blo 1955435 2933633 := bstep (se 2 (by rfl) ⟨1100112, by rfl⟩ : syracuseStep 2933633 = 2200225) B2200225
theorem B1955755 : Blo 1955435 1955755 := bstep (se 1 (by rfl) ⟨1466816, by rfl⟩ : syracuseStep 1955755 = 2933633) B2933633
theorem B4950517 : Blo 1955435 4950517 := bbase (se 5 (by rfl) ⟨232055, by rfl⟩ : syracuseStep 4950517 = 464111) (by norm_num)
theorem B6600689 : Blo 1955435 6600689 := bstep (se 2 (by rfl) ⟨2475258, by rfl⟩ : syracuseStep 6600689 = 4950517) B4950517
theorem B4400459 : Blo 1955435 4400459 := bstep (se 1 (by rfl) ⟨3300344, by rfl⟩ : syracuseStep 4400459 = 6600689) B6600689
theorem B2933639 : Blo 1955435 2933639 := bstep (se 1 (by rfl) ⟨2200229, by rfl⟩ : syracuseStep 2933639 = 4400459) B4400459
theorem B1955759 : Blo 1955435 1955759 := bstep (se 1 (by rfl) ⟨1466819, by rfl⟩ : syracuseStep 1955759 = 2933639) B2933639
theorem B2933645 : Blo 1955435 2933645 := bbase (se 3 (by rfl) ⟨550058, by rfl⟩ : syracuseStep 2933645 = 1100117) (by norm_num)
theorem B1955763 : Blo 1955435 1955763 := bstep (se 1 (by rfl) ⟨1466822, by rfl⟩ : syracuseStep 1955763 = 2933645) B2933645
theorem B4400477 : Blo 1955435 4400477 := bbase (se 3 (by rfl) ⟨825089, by rfl⟩ : syracuseStep 4400477 = 1650179) (by norm_num)
theorem B2933651 : Blo 1955435 2933651 := bstep (se 1 (by rfl) ⟨2200238, by rfl⟩ : syracuseStep 2933651 = 4400477) B4400477
theorem B1955767 : Blo 1955435 1955767 := bstep (se 1 (by rfl) ⟨1466825, by rfl⟩ : syracuseStep 1955767 = 2933651) B2933651
theorem B3300365 : Blo 1955435 3300365 := bbase (se 3 (by rfl) ⟨618818, by rfl⟩ : syracuseStep 3300365 = 1237637) (by norm_num)
theorem B2200243 : Blo 1955435 2200243 := bstep (se 1 (by rfl) ⟨1650182, by rfl⟩ : syracuseStep 2200243 = 3300365) B3300365
theorem B2933657 : Blo 1955435 2933657 := bstep (se 2 (by rfl) ⟨1100121, by rfl⟩ : syracuseStep 2933657 = 2200243) B2200243
theorem B1955771 : Blo 1955435 1955771 := bstep (se 1 (by rfl) ⟨1466828, by rfl⟩ : syracuseStep 1955771 = 2933657) B2933657
theorem B19576565 : Blo 1955435 19576565 := bbase (se 5 (by rfl) ⟨917651, by rfl⟩ : syracuseStep 19576565 = 1835303) (by norm_num)
theorem B13051043 : Blo 1955435 13051043 := bstep (se 1 (by rfl) ⟨9788282, by rfl⟩ : syracuseStep 13051043 = 19576565) B19576565
theorem B8700695 : Blo 1955435 8700695 := bstep (se 1 (by rfl) ⟨6525521, by rfl⟩ : syracuseStep 8700695 = 13051043) B13051043
theorem B5800463 : Blo 1955435 5800463 := bstep (se 1 (by rfl) ⟨4350347, by rfl⟩ : syracuseStep 5800463 = 8700695) B8700695
theorem B3866975 : Blo 1955435 3866975 := bstep (se 1 (by rfl) ⟨2900231, by rfl⟩ : syracuseStep 3866975 = 5800463) B5800463
theorem B2577983 : Blo 1955435 2577983 := bstep (se 1 (by rfl) ⟨1933487, by rfl⟩ : syracuseStep 2577983 = 3866975) B3866975
theorem B6874621 : Blo 1955435 6874621 := bstep (se 3 (by rfl) ⟨1288991, by rfl⟩ : syracuseStep 6874621 = 2577983) B2577983
theorem B36664645 : Blo 1955435 36664645 := bstep (se 4 (by rfl) ⟨3437310, by rfl⟩ : syracuseStep 36664645 = 6874621) B6874621
theorem B48886193 : Blo 1955435 48886193 := bstep (se 2 (by rfl) ⟨18332322, by rfl⟩ : syracuseStep 48886193 = 36664645) B36664645
theorem B32590795 : Blo 1955435 32590795 := bstep (se 1 (by rfl) ⟨24443096, by rfl⟩ : syracuseStep 32590795 = 48886193) B48886193
theorem B43454393 : Blo 1955435 43454393 := bstep (se 2 (by rfl) ⟨16295397, by rfl⟩ : syracuseStep 43454393 = 32590795) B32590795
theorem B28969595 : Blo 1955435 28969595 := bstep (se 1 (by rfl) ⟨21727196, by rfl⟩ : syracuseStep 28969595 = 43454393) B43454393
theorem B19313063 : Blo 1955435 19313063 := bstep (se 1 (by rfl) ⟨14484797, by rfl⟩ : syracuseStep 19313063 = 28969595) B28969595
theorem B12875375 : Blo 1955435 12875375 := bstep (se 1 (by rfl) ⟨9656531, by rfl⟩ : syracuseStep 12875375 = 19313063) B19313063
theorem B8583583 : Blo 1955435 8583583 := bstep (se 1 (by rfl) ⟨6437687, by rfl⟩ : syracuseStep 8583583 = 12875375) B12875375
theorem B11444777 : Blo 1955435 11444777 := bstep (se 2 (by rfl) ⟨4291791, by rfl⟩ : syracuseStep 11444777 = 8583583) B8583583
theorem B7629851 : Blo 1955435 7629851 := bstep (se 1 (by rfl) ⟨5722388, by rfl⟩ : syracuseStep 7629851 = 11444777) B11444777
theorem B5086567 : Blo 1955435 5086567 := bstep (se 1 (by rfl) ⟨3814925, by rfl⟩ : syracuseStep 5086567 = 7629851) B7629851
theorem B6782089 : Blo 1955435 6782089 := bstep (se 2 (by rfl) ⟨2543283, by rfl⟩ : syracuseStep 6782089 = 5086567) B5086567
theorem B9042785 : Blo 1955435 9042785 := bstep (se 2 (by rfl) ⟨3391044, by rfl⟩ : syracuseStep 9042785 = 6782089) B6782089
theorem B6028523 : Blo 1955435 6028523 := bstep (se 1 (by rfl) ⟨4521392, by rfl⟩ : syracuseStep 6028523 = 9042785) B9042785
theorem B4019015 : Blo 1955435 4019015 := bstep (se 1 (by rfl) ⟨3014261, by rfl⟩ : syracuseStep 4019015 = 6028523) B6028523
theorem B10717373 : Blo 1955435 10717373 := bstep (se 3 (by rfl) ⟨2009507, by rfl⟩ : syracuseStep 10717373 = 4019015) B4019015
theorem B28579661 : Blo 1955435 28579661 := bstep (se 3 (by rfl) ⟨5358686, by rfl⟩ : syracuseStep 28579661 = 10717373) B10717373
theorem B19053107 : Blo 1955435 19053107 := bstep (se 1 (by rfl) ⟨14289830, by rfl⟩ : syracuseStep 19053107 = 28579661) B28579661
theorem B12702071 : Blo 1955435 12702071 := bstep (se 1 (by rfl) ⟨9526553, by rfl⟩ : syracuseStep 12702071 = 19053107) B19053107
theorem B8468047 : Blo 1955435 8468047 := bstep (se 1 (by rfl) ⟨6351035, by rfl⟩ : syracuseStep 8468047 = 12702071) B12702071
theorem B45162917 : Blo 1955435 45162917 := bstep (se 4 (by rfl) ⟨4234023, by rfl⟩ : syracuseStep 45162917 = 8468047) B8468047
theorem B30108611 : Blo 1955435 30108611 := bstep (se 1 (by rfl) ⟨22581458, by rfl⟩ : syracuseStep 30108611 = 45162917) B45162917
theorem B20072407 : Blo 1955435 20072407 := bstep (se 1 (by rfl) ⟨15054305, by rfl⟩ : syracuseStep 20072407 = 30108611) B30108611
theorem B26763209 : Blo 1955435 26763209 := bstep (se 2 (by rfl) ⟨10036203, by rfl⟩ : syracuseStep 26763209 = 20072407) B20072407
theorem B17842139 : Blo 1955435 17842139 := bstep (se 1 (by rfl) ⟨13381604, by rfl⟩ : syracuseStep 17842139 = 26763209) B26763209
theorem B11894759 : Blo 1955435 11894759 := bstep (se 1 (by rfl) ⟨8921069, by rfl⟩ : syracuseStep 11894759 = 17842139) B17842139
theorem B7929839 : Blo 1955435 7929839 := bstep (se 1 (by rfl) ⟨5947379, by rfl⟩ : syracuseStep 7929839 = 11894759) B11894759
theorem B5286559 : Blo 1955435 5286559 := bstep (se 1 (by rfl) ⟨3964919, by rfl⟩ : syracuseStep 5286559 = 7929839) B7929839
theorem B7048745 : Blo 1955435 7048745 := bstep (se 2 (by rfl) ⟨2643279, by rfl⟩ : syracuseStep 7048745 = 5286559) B5286559
theorem B4699163 : Blo 1955435 4699163 := bstep (se 1 (by rfl) ⟨3524372, by rfl⟩ : syracuseStep 4699163 = 7048745) B7048745
theorem B3132775 : Blo 1955435 3132775 := bstep (se 1 (by rfl) ⟨2349581, by rfl⟩ : syracuseStep 3132775 = 4699163) B4699163
theorem B16708133 : Blo 1955435 16708133 := bstep (se 4 (by rfl) ⟨1566387, by rfl⟩ : syracuseStep 16708133 = 3132775) B3132775
theorem B11138755 : Blo 1955435 11138755 := bstep (se 1 (by rfl) ⟨8354066, by rfl⟩ : syracuseStep 11138755 = 16708133) B16708133
theorem B14851673 : Blo 1955435 14851673 := bstep (se 2 (by rfl) ⟨5569377, by rfl⟩ : syracuseStep 14851673 = 11138755) B11138755
theorem B9901115 : Blo 1955435 9901115 := bstep (se 1 (by rfl) ⟨7425836, by rfl⟩ : syracuseStep 9901115 = 14851673) B14851673
theorem B6600743 : Blo 1955435 6600743 := bstep (se 1 (by rfl) ⟨4950557, by rfl⟩ : syracuseStep 6600743 = 9901115) B9901115
theorem B4400495 : Blo 1955435 4400495 := bstep (se 1 (by rfl) ⟨3300371, by rfl⟩ : syracuseStep 4400495 = 6600743) B6600743
theorem B2933663 : Blo 1955435 2933663 := bstep (se 1 (by rfl) ⟨2200247, by rfl⟩ : syracuseStep 2933663 = 4400495) B4400495
theorem B1955775 : Blo 1955435 1955775 := bstep (se 1 (by rfl) ⟨1466831, by rfl⟩ : syracuseStep 1955775 = 2933663) B2933663
theorem B2933669 : Blo 1955435 2933669 := bbase (se 4 (by rfl) ⟨275031, by rfl⟩ : syracuseStep 2933669 = 550063) (by norm_num)
theorem B1955779 : Blo 1955435 1955779 := bstep (se 1 (by rfl) ⟨1466834, by rfl⟩ : syracuseStep 1955779 = 2933669) B2933669
theorem B2475289 : Blo 1955435 2475289 := bbase (se 2 (by rfl) ⟨928233, by rfl⟩ : syracuseStep 2475289 = 1856467) (by norm_num)
theorem B3300385 : Blo 1955435 3300385 := bstep (se 2 (by rfl) ⟨1237644, by rfl⟩ : syracuseStep 3300385 = 2475289) B2475289
theorem B4400513 : Blo 1955435 4400513 := bstep (se 2 (by rfl) ⟨1650192, by rfl⟩ : syracuseStep 4400513 = 3300385) B3300385
theorem B2933675 : Blo 1955435 2933675 := bstep (se 1 (by rfl) ⟨2200256, by rfl⟩ : syracuseStep 2933675 = 4400513) B4400513
theorem B1955783 : Blo 1955435 1955783 := bstep (se 1 (by rfl) ⟨1466837, by rfl⟩ : syracuseStep 1955783 = 2933675) B2933675
theorem B2200261 : Blo 1955435 2200261 := bbase (se 4 (by rfl) ⟨206274, by rfl⟩ : syracuseStep 2200261 = 412549) (by norm_num)
theorem B2933681 : Blo 1955435 2933681 := bstep (se 2 (by rfl) ⟨1100130, by rfl⟩ : syracuseStep 2933681 = 2200261) B2200261
theorem B1955787 : Blo 1955435 1955787 := bstep (se 1 (by rfl) ⟨1466840, by rfl⟩ : syracuseStep 1955787 = 2933681) B2933681
theorem B3712949 : Blo 1955435 3712949 := bbase (se 5 (by rfl) ⟨174044, by rfl⟩ : syracuseStep 3712949 = 348089) (by norm_num)
theorem B2475299 : Blo 1955435 2475299 := bstep (se 1 (by rfl) ⟨1856474, by rfl⟩ : syracuseStep 2475299 = 3712949) B3712949
theorem B6600797 : Blo 1955435 6600797 := bstep (se 3 (by rfl) ⟨1237649, by rfl⟩ : syracuseStep 6600797 = 2475299) B2475299
theorem B4400531 : Blo 1955435 4400531 := bstep (se 1 (by rfl) ⟨3300398, by rfl⟩ : syracuseStep 4400531 = 6600797) B6600797
theorem B2933687 : Blo 1955435 2933687 := bstep (se 1 (by rfl) ⟨2200265, by rfl⟩ : syracuseStep 2933687 = 4400531) B4400531
theorem B1955791 : Blo 1955435 1955791 := bstep (se 1 (by rfl) ⟨1466843, by rfl⟩ : syracuseStep 1955791 = 2933687) B2933687
theorem B2933693 : Blo 1955435 2933693 := bbase (se 3 (by rfl) ⟨550067, by rfl⟩ : syracuseStep 2933693 = 1100135) (by norm_num)
theorem B1955795 : Blo 1955435 1955795 := bstep (se 1 (by rfl) ⟨1466846, by rfl⟩ : syracuseStep 1955795 = 2933693) B2933693
theorem B4400549 : Blo 1955435 4400549 := bbase (se 4 (by rfl) ⟨412551, by rfl⟩ : syracuseStep 4400549 = 825103) (by norm_num)
theorem B2933699 : Blo 1955435 2933699 := bstep (se 1 (by rfl) ⟨2200274, by rfl⟩ : syracuseStep 2933699 = 4400549) B4400549
theorem B1955799 : Blo 1955435 1955799 := bstep (se 1 (by rfl) ⟨1466849, by rfl⟩ : syracuseStep 1955799 = 2933699) B2933699
theorem B4950629 : Blo 1955435 4950629 := bbase (se 4 (by rfl) ⟨464121, by rfl⟩ : syracuseStep 4950629 = 928243) (by norm_num)
theorem B3300419 : Blo 1955435 3300419 := bstep (se 1 (by rfl) ⟨2475314, by rfl⟩ : syracuseStep 3300419 = 4950629) B4950629
theorem B2200279 : Blo 1955435 2200279 := bstep (se 1 (by rfl) ⟨1650209, by rfl⟩ : syracuseStep 2200279 = 3300419) B3300419
theorem B2933705 : Blo 1955435 2933705 := bstep (se 2 (by rfl) ⟨1100139, by rfl⟩ : syracuseStep 2933705 = 2200279) B2200279
theorem B1955803 : Blo 1955435 1955803 := bstep (se 1 (by rfl) ⟨1466852, by rfl⟩ : syracuseStep 1955803 = 2933705) B2933705
theorem B2509093 : Blo 1955435 2509093 := bbase (se 4 (by rfl) ⟨235227, by rfl⟩ : syracuseStep 2509093 = 470455) (by norm_num)
theorem B3345457 : Blo 1955435 3345457 := bstep (se 2 (by rfl) ⟨1254546, by rfl⟩ : syracuseStep 3345457 = 2509093) B2509093
theorem B4460609 : Blo 1955435 4460609 := bstep (se 2 (by rfl) ⟨1672728, by rfl⟩ : syracuseStep 4460609 = 3345457) B3345457
theorem B11894957 : Blo 1955435 11894957 := bstep (se 3 (by rfl) ⟨2230304, by rfl⟩ : syracuseStep 11894957 = 4460609) B4460609
theorem B7929971 : Blo 1955435 7929971 := bstep (se 1 (by rfl) ⟨5947478, by rfl⟩ : syracuseStep 7929971 = 11894957) B11894957
theorem B5286647 : Blo 1955435 5286647 := bstep (se 1 (by rfl) ⟨3964985, by rfl⟩ : syracuseStep 5286647 = 7929971) B7929971
theorem B3524431 : Blo 1955435 3524431 := bstep (se 1 (by rfl) ⟨2643323, by rfl⟩ : syracuseStep 3524431 = 5286647) B5286647
theorem B4699241 : Blo 1955435 4699241 := bstep (se 2 (by rfl) ⟨1762215, by rfl⟩ : syracuseStep 4699241 = 3524431) B3524431
theorem B3132827 : Blo 1955435 3132827 := bstep (se 1 (by rfl) ⟨2349620, by rfl⟩ : syracuseStep 3132827 = 4699241) B4699241
theorem B2088551 : Blo 1955435 2088551 := bstep (se 1 (by rfl) ⟨1566413, by rfl⟩ : syracuseStep 2088551 = 3132827) B3132827
theorem B5569469 : Blo 1955435 5569469 := bstep (se 3 (by rfl) ⟨1044275, by rfl⟩ : syracuseStep 5569469 = 2088551) B2088551
theorem B3712979 : Blo 1955435 3712979 := bstep (se 1 (by rfl) ⟨2784734, by rfl⟩ : syracuseStep 3712979 = 5569469) B5569469
theorem B9901277 : Blo 1955435 9901277 := bstep (se 3 (by rfl) ⟨1856489, by rfl⟩ : syracuseStep 9901277 = 3712979) B3712979
theorem B6600851 : Blo 1955435 6600851 := bstep (se 1 (by rfl) ⟨4950638, by rfl⟩ : syracuseStep 6600851 = 9901277) B9901277
theorem B4400567 : Blo 1955435 4400567 := bstep (se 1 (by rfl) ⟨3300425, by rfl⟩ : syracuseStep 4400567 = 6600851) B6600851
theorem B2933711 : Blo 1955435 2933711 := bstep (se 1 (by rfl) ⟨2200283, by rfl⟩ : syracuseStep 2933711 = 4400567) B4400567
theorem B1955807 : Blo 1955435 1955807 := bstep (se 1 (by rfl) ⟨1466855, by rfl⟩ : syracuseStep 1955807 = 2933711) B2933711
theorem B2933717 : Blo 1955435 2933717 := bbase (se 7 (by rfl) ⟨34379, by rfl⟩ : syracuseStep 2933717 = 68759) (by norm_num)
theorem B1955811 : Blo 1955435 1955811 := bstep (se 1 (by rfl) ⟨1466858, by rfl⟩ : syracuseStep 1955811 = 2933717) B2933717
theorem B7425989 : Blo 1955435 7425989 := bbase (se 4 (by rfl) ⟨696186, by rfl⟩ : syracuseStep 7425989 = 1392373) (by norm_num)
theorem B4950659 : Blo 1955435 4950659 := bstep (se 1 (by rfl) ⟨3712994, by rfl⟩ : syracuseStep 4950659 = 7425989) B7425989
theorem B3300439 : Blo 1955435 3300439 := bstep (se 1 (by rfl) ⟨2475329, by rfl⟩ : syracuseStep 3300439 = 4950659) B4950659
theorem B4400585 : Blo 1955435 4400585 := bstep (se 2 (by rfl) ⟨1650219, by rfl⟩ : syracuseStep 4400585 = 3300439) B3300439
theorem B2933723 : Blo 1955435 2933723 := bstep (se 1 (by rfl) ⟨2200292, by rfl⟩ : syracuseStep 2933723 = 4400585) B4400585
theorem B1955815 : Blo 1955435 1955815 := bstep (se 1 (by rfl) ⟨1466861, by rfl⟩ : syracuseStep 1955815 = 2933723) B2933723
theorem B2200297 : Blo 1955435 2200297 := bbase (se 2 (by rfl) ⟨825111, by rfl⟩ : syracuseStep 2200297 = 1650223) (by norm_num)
theorem B2933729 : Blo 1955435 2933729 := bstep (se 2 (by rfl) ⟨1100148, by rfl⟩ : syracuseStep 2933729 = 2200297) B2200297
theorem B1955819 : Blo 1955435 1955819 := bstep (se 1 (by rfl) ⟨1466864, by rfl⟩ : syracuseStep 1955819 = 2933729) B2933729
theorem B11139029 : Blo 1955435 11139029 := bbase (se 7 (by rfl) ⟨130535, by rfl⟩ : syracuseStep 11139029 = 261071) (by norm_num)
theorem B7426019 : Blo 1955435 7426019 := bstep (se 1 (by rfl) ⟨5569514, by rfl⟩ : syracuseStep 7426019 = 11139029) B11139029
theorem B4950679 : Blo 1955435 4950679 := bstep (se 1 (by rfl) ⟨3713009, by rfl⟩ : syracuseStep 4950679 = 7426019) B7426019
theorem B6600905 : Blo 1955435 6600905 := bstep (se 2 (by rfl) ⟨2475339, by rfl⟩ : syracuseStep 6600905 = 4950679) B4950679
theorem B4400603 : Blo 1955435 4400603 := bstep (se 1 (by rfl) ⟨3300452, by rfl⟩ : syracuseStep 4400603 = 6600905) B6600905
theorem B2933735 : Blo 1955435 2933735 := bstep (se 1 (by rfl) ⟨2200301, by rfl⟩ : syracuseStep 2933735 = 4400603) B4400603
theorem B1955823 : Blo 1955435 1955823 := bstep (se 1 (by rfl) ⟨1466867, by rfl⟩ : syracuseStep 1955823 = 2933735) B2933735
theorem B2933741 : Blo 1955435 2933741 := bbase (se 3 (by rfl) ⟨550076, by rfl⟩ : syracuseStep 2933741 = 1100153) (by norm_num)
theorem B1955827 : Blo 1955435 1955827 := bstep (se 1 (by rfl) ⟨1466870, by rfl⟩ : syracuseStep 1955827 = 2933741) B2933741
theorem B4400621 : Blo 1955435 4400621 := bbase (se 3 (by rfl) ⟨825116, by rfl⟩ : syracuseStep 4400621 = 1650233) (by norm_num)
theorem B2933747 : Blo 1955435 2933747 := bstep (se 1 (by rfl) ⟨2200310, by rfl⟩ : syracuseStep 2933747 = 4400621) B4400621
theorem B1955831 : Blo 1955435 1955831 := bstep (se 1 (by rfl) ⟨1466873, by rfl⟩ : syracuseStep 1955831 = 2933747) B2933747
theorem B4699309 : Blo 1955435 4699309 := bbase (se 3 (by rfl) ⟨881120, by rfl⟩ : syracuseStep 4699309 = 1762241) (by norm_num)
theorem B6265745 : Blo 1955435 6265745 := bstep (se 2 (by rfl) ⟨2349654, by rfl⟩ : syracuseStep 6265745 = 4699309) B4699309
theorem B4177163 : Blo 1955435 4177163 := bstep (se 1 (by rfl) ⟨3132872, by rfl⟩ : syracuseStep 4177163 = 6265745) B6265745
theorem B2784775 : Blo 1955435 2784775 := bstep (se 1 (by rfl) ⟨2088581, by rfl⟩ : syracuseStep 2784775 = 4177163) B4177163
theorem B3713033 : Blo 1955435 3713033 := bstep (se 2 (by rfl) ⟨1392387, by rfl⟩ : syracuseStep 3713033 = 2784775) B2784775
theorem B2475355 : Blo 1955435 2475355 := bstep (se 1 (by rfl) ⟨1856516, by rfl⟩ : syracuseStep 2475355 = 3713033) B3713033
theorem B3300473 : Blo 1955435 3300473 := bstep (se 2 (by rfl) ⟨1237677, by rfl⟩ : syracuseStep 3300473 = 2475355) B2475355
theorem B2200315 : Blo 1955435 2200315 := bstep (se 1 (by rfl) ⟨1650236, by rfl⟩ : syracuseStep 2200315 = 3300473) B3300473
theorem B2933753 : Blo 1955435 2933753 := bstep (se 2 (by rfl) ⟨1100157, by rfl⟩ : syracuseStep 2933753 = 2200315) B2200315
theorem B1955835 : Blo 1955435 1955835 := bstep (se 1 (by rfl) ⟨1466876, by rfl⟩ : syracuseStep 1955835 = 2933753) B2933753
theorem B7527397 : Blo 1955435 7527397 := bbase (se 4 (by rfl) ⟨705693, by rfl⟩ : syracuseStep 7527397 = 1411387) (by norm_num)
theorem B10036529 : Blo 1955435 10036529 := bstep (se 2 (by rfl) ⟨3763698, by rfl⟩ : syracuseStep 10036529 = 7527397) B7527397
theorem B6691019 : Blo 1955435 6691019 := bstep (se 1 (by rfl) ⟨5018264, by rfl⟩ : syracuseStep 6691019 = 10036529) B10036529
theorem B17842717 : Blo 1955435 17842717 := bstep (se 3 (by rfl) ⟨3345509, by rfl⟩ : syracuseStep 17842717 = 6691019) B6691019
theorem B23790289 : Blo 1955435 23790289 := bstep (se 2 (by rfl) ⟨8921358, by rfl⟩ : syracuseStep 23790289 = 17842717) B17842717
theorem B31720385 : Blo 1955435 31720385 := bstep (se 2 (by rfl) ⟨11895144, by rfl⟩ : syracuseStep 31720385 = 23790289) B23790289
theorem B21146923 : Blo 1955435 21146923 := bstep (se 1 (by rfl) ⟨15860192, by rfl⟩ : syracuseStep 21146923 = 31720385) B31720385
theorem B112783589 : Blo 1955435 112783589 := bstep (se 4 (by rfl) ⟨10573461, by rfl⟩ : syracuseStep 112783589 = 21146923) B21146923
theorem B75189059 : Blo 1955435 75189059 := bstep (se 1 (by rfl) ⟨56391794, by rfl⟩ : syracuseStep 75189059 = 112783589) B112783589
theorem B50126039 : Blo 1955435 50126039 := bstep (se 1 (by rfl) ⟨37594529, by rfl⟩ : syracuseStep 50126039 = 75189059) B75189059
theorem B33417359 : Blo 1955435 33417359 := bstep (se 1 (by rfl) ⟨25063019, by rfl⟩ : syracuseStep 33417359 = 50126039) B50126039
theorem B22278239 : Blo 1955435 22278239 := bstep (se 1 (by rfl) ⟨16708679, by rfl⟩ : syracuseStep 22278239 = 33417359) B33417359
theorem B14852159 : Blo 1955435 14852159 := bstep (se 1 (by rfl) ⟨11139119, by rfl⟩ : syracuseStep 14852159 = 22278239) B22278239
theorem B9901439 : Blo 1955435 9901439 := bstep (se 1 (by rfl) ⟨7426079, by rfl⟩ : syracuseStep 9901439 = 14852159) B14852159
theorem B6600959 : Blo 1955435 6600959 := bstep (se 1 (by rfl) ⟨4950719, by rfl⟩ : syracuseStep 6600959 = 9901439) B9901439
theorem B4400639 : Blo 1955435 4400639 := bstep (se 1 (by rfl) ⟨3300479, by rfl⟩ : syracuseStep 4400639 = 6600959) B6600959
theorem B2933759 : Blo 1955435 2933759 := bstep (se 1 (by rfl) ⟨2200319, by rfl⟩ : syracuseStep 2933759 = 4400639) B4400639
theorem B1955839 : Blo 1955435 1955839 := bstep (se 1 (by rfl) ⟨1466879, by rfl⟩ : syracuseStep 1955839 = 2933759) B2933759
theorem B2933765 : Blo 1955435 2933765 := bbase (se 4 (by rfl) ⟨275040, by rfl⟩ : syracuseStep 2933765 = 550081) (by norm_num)
theorem B1955843 : Blo 1955435 1955843 := bstep (se 1 (by rfl) ⟨1466882, by rfl⟩ : syracuseStep 1955843 = 2933765) B2933765
theorem B3300493 : Blo 1955435 3300493 := bbase (se 3 (by rfl) ⟨618842, by rfl⟩ : syracuseStep 3300493 = 1237685) (by norm_num)
theorem B4400657 : Blo 1955435 4400657 := bstep (se 2 (by rfl) ⟨1650246, by rfl⟩ : syracuseStep 4400657 = 3300493) B3300493
theorem B2933771 : Blo 1955435 2933771 := bstep (se 1 (by rfl) ⟨2200328, by rfl⟩ : syracuseStep 2933771 = 4400657) B4400657
theorem B1955847 : Blo 1955435 1955847 := bstep (se 1 (by rfl) ⟨1466885, by rfl⟩ : syracuseStep 1955847 = 2933771) B2933771
theorem B2200333 : Blo 1955435 2200333 := bbase (se 3 (by rfl) ⟨412562, by rfl⟩ : syracuseStep 2200333 = 825125) (by norm_num)
theorem B2933777 : Blo 1955435 2933777 := bstep (se 2 (by rfl) ⟨1100166, by rfl⟩ : syracuseStep 2933777 = 2200333) B2200333
theorem B1955851 : Blo 1955435 1955851 := bstep (se 1 (by rfl) ⟨1466888, by rfl⟩ : syracuseStep 1955851 = 2933777) B2933777
theorem B6601013 : Blo 1955435 6601013 := bbase (se 5 (by rfl) ⟨309422, by rfl⟩ : syracuseStep 6601013 = 618845) (by norm_num)
theorem B4400675 : Blo 1955435 4400675 := bstep (se 1 (by rfl) ⟨3300506, by rfl⟩ : syracuseStep 4400675 = 6601013) B6601013
theorem B2933783 : Blo 1955435 2933783 := bstep (se 1 (by rfl) ⟨2200337, by rfl⟩ : syracuseStep 2933783 = 4400675) B4400675
theorem B1955855 : Blo 1955435 1955855 := bstep (se 1 (by rfl) ⟨1466891, by rfl⟩ : syracuseStep 1955855 = 2933783) B2933783
theorem B2933789 : Blo 1955435 2933789 := bbase (se 3 (by rfl) ⟨550085, by rfl⟩ : syracuseStep 2933789 = 1100171) (by norm_num)
theorem B1955859 : Blo 1955435 1955859 := bstep (se 1 (by rfl) ⟨1466894, by rfl⟩ : syracuseStep 1955859 = 2933789) B2933789
theorem B4400693 : Blo 1955435 4400693 := bbase (se 5 (by rfl) ⟨206282, by rfl⟩ : syracuseStep 4400693 = 412565) (by norm_num)
theorem B2933795 : Blo 1955435 2933795 := bstep (se 1 (by rfl) ⟨2200346, by rfl⟩ : syracuseStep 2933795 = 4400693) B4400693
theorem B1955863 : Blo 1955435 1955863 := bstep (se 1 (by rfl) ⟨1466897, by rfl⟩ : syracuseStep 1955863 = 2933795) B2933795
theorem B2230373 : Blo 1955435 2230373 := bbase (se 4 (by rfl) ⟨209097, by rfl⟩ : syracuseStep 2230373 = 418195) (by norm_num)
theorem B5947661 : Blo 1955435 5947661 := bstep (se 3 (by rfl) ⟨1115186, by rfl⟩ : syracuseStep 5947661 = 2230373) B2230373
theorem B3965107 : Blo 1955435 3965107 := bstep (se 1 (by rfl) ⟨2973830, by rfl⟩ : syracuseStep 3965107 = 5947661) B5947661
theorem B5286809 : Blo 1955435 5286809 := bstep (se 2 (by rfl) ⟨1982553, by rfl⟩ : syracuseStep 5286809 = 3965107) B3965107
theorem B3524539 : Blo 1955435 3524539 := bstep (se 1 (by rfl) ⟨2643404, by rfl⟩ : syracuseStep 3524539 = 5286809) B5286809
theorem B4699385 : Blo 1955435 4699385 := bstep (se 2 (by rfl) ⟨1762269, by rfl⟩ : syracuseStep 4699385 = 3524539) B3524539
theorem B3132923 : Blo 1955435 3132923 := bstep (se 1 (by rfl) ⟨2349692, by rfl⟩ : syracuseStep 3132923 = 4699385) B4699385
theorem B8354461 : Blo 1955435 8354461 := bstep (se 3 (by rfl) ⟨1566461, by rfl⟩ : syracuseStep 8354461 = 3132923) B3132923
theorem B11139281 : Blo 1955435 11139281 := bstep (se 2 (by rfl) ⟨4177230, by rfl⟩ : syracuseStep 11139281 = 8354461) B8354461
theorem B7426187 : Blo 1955435 7426187 := bstep (se 1 (by rfl) ⟨5569640, by rfl⟩ : syracuseStep 7426187 = 11139281) B11139281
theorem B4950791 : Blo 1955435 4950791 := bstep (se 1 (by rfl) ⟨3713093, by rfl⟩ : syracuseStep 4950791 = 7426187) B7426187
theorem B3300527 : Blo 1955435 3300527 := bstep (se 1 (by rfl) ⟨2475395, by rfl⟩ : syracuseStep 3300527 = 4950791) B4950791
theorem B2200351 : Blo 1955435 2200351 := bstep (se 1 (by rfl) ⟨1650263, by rfl⟩ : syracuseStep 2200351 = 3300527) B3300527
theorem B2933801 : Blo 1955435 2933801 := bstep (se 2 (by rfl) ⟨1100175, by rfl⟩ : syracuseStep 2933801 = 2200351) B2200351
theorem B1955867 : Blo 1955435 1955867 := bstep (se 1 (by rfl) ⟨1466900, by rfl⟩ : syracuseStep 1955867 = 2933801) B2933801
theorem B2349697 : Blo 1955435 2349697 := bbase (se 2 (by rfl) ⟨881136, by rfl⟩ : syracuseStep 2349697 = 1762273) (by norm_num)
theorem B3132929 : Blo 1955435 3132929 := bstep (se 2 (by rfl) ⟨1174848, by rfl⟩ : syracuseStep 3132929 = 2349697) B2349697
theorem B8354477 : Blo 1955435 8354477 := bstep (se 3 (by rfl) ⟨1566464, by rfl⟩ : syracuseStep 8354477 = 3132929) B3132929
theorem B5569651 : Blo 1955435 5569651 := bstep (se 1 (by rfl) ⟨4177238, by rfl⟩ : syracuseStep 5569651 = 8354477) B8354477
theorem B7426201 : Blo 1955435 7426201 := bstep (se 2 (by rfl) ⟨2784825, by rfl⟩ : syracuseStep 7426201 = 5569651) B5569651
theorem B9901601 : Blo 1955435 9901601 := bstep (se 2 (by rfl) ⟨3713100, by rfl⟩ : syracuseStep 9901601 = 7426201) B7426201
theorem B6601067 : Blo 1955435 6601067 := bstep (se 1 (by rfl) ⟨4950800, by rfl⟩ : syracuseStep 6601067 = 9901601) B9901601
theorem B4400711 : Blo 1955435 4400711 := bstep (se 1 (by rfl) ⟨3300533, by rfl⟩ : syracuseStep 4400711 = 6601067) B6601067
theorem B2933807 : Blo 1955435 2933807 := bstep (se 1 (by rfl) ⟨2200355, by rfl⟩ : syracuseStep 2933807 = 4400711) B4400711
theorem B1955871 : Blo 1955435 1955871 := bstep (se 1 (by rfl) ⟨1466903, by rfl⟩ : syracuseStep 1955871 = 2933807) B2933807
theorem B2933813 : Blo 1955435 2933813 := bbase (se 5 (by rfl) ⟨137522, by rfl⟩ : syracuseStep 2933813 = 275045) (by norm_num)
theorem B1955875 : Blo 1955435 1955875 := bstep (se 1 (by rfl) ⟨1466906, by rfl⟩ : syracuseStep 1955875 = 2933813) B2933813
theorem B4950821 : Blo 1955435 4950821 := bbase (se 4 (by rfl) ⟨464139, by rfl⟩ : syracuseStep 4950821 = 928279) (by norm_num)
theorem B3300547 : Blo 1955435 3300547 := bstep (se 1 (by rfl) ⟨2475410, by rfl⟩ : syracuseStep 3300547 = 4950821) B4950821
theorem B4400729 : Blo 1955435 4400729 := bstep (se 2 (by rfl) ⟨1650273, by rfl⟩ : syracuseStep 4400729 = 3300547) B3300547
theorem B2933819 : Blo 1955435 2933819 := bstep (se 1 (by rfl) ⟨2200364, by rfl⟩ : syracuseStep 2933819 = 4400729) B4400729
theorem B1955879 : Blo 1955435 1955879 := bstep (se 1 (by rfl) ⟨1466909, by rfl⟩ : syracuseStep 1955879 = 2933819) B2933819
theorem B2200369 : Blo 1955435 2200369 := bbase (se 2 (by rfl) ⟨825138, by rfl⟩ : syracuseStep 2200369 = 1650277) (by norm_num)
theorem B2933825 : Blo 1955435 2933825 := bstep (se 2 (by rfl) ⟨1100184, by rfl⟩ : syracuseStep 2933825 = 2200369) B2200369
theorem B1955883 : Blo 1955435 1955883 := bstep (se 1 (by rfl) ⟨1466912, by rfl⟩ : syracuseStep 1955883 = 2933825) B2933825
theorem B2822845 : Blo 1955435 2822845 := bbase (se 3 (by rfl) ⟨529283, by rfl⟩ : syracuseStep 2822845 = 1058567) (by norm_num)
theorem B3763793 : Blo 1955435 3763793 := bstep (se 2 (by rfl) ⟨1411422, by rfl⟩ : syracuseStep 3763793 = 2822845) B2822845
theorem B10036781 : Blo 1955435 10036781 := bstep (se 3 (by rfl) ⟨1881896, by rfl⟩ : syracuseStep 10036781 = 3763793) B3763793
theorem B6691187 : Blo 1955435 6691187 := bstep (se 1 (by rfl) ⟨5018390, by rfl⟩ : syracuseStep 6691187 = 10036781) B10036781
theorem B17843165 : Blo 1955435 17843165 := bstep (se 3 (by rfl) ⟨3345593, by rfl⟩ : syracuseStep 17843165 = 6691187) B6691187
theorem B11895443 : Blo 1955435 11895443 := bstep (se 1 (by rfl) ⟨8921582, by rfl⟩ : syracuseStep 11895443 = 17843165) B17843165
theorem B7930295 : Blo 1955435 7930295 := bstep (se 1 (by rfl) ⟨5947721, by rfl⟩ : syracuseStep 7930295 = 11895443) B11895443
theorem B5286863 : Blo 1955435 5286863 := bstep (se 1 (by rfl) ⟨3965147, by rfl⟩ : syracuseStep 5286863 = 7930295) B7930295
theorem B3524575 : Blo 1955435 3524575 := bstep (se 1 (by rfl) ⟨2643431, by rfl⟩ : syracuseStep 3524575 = 5286863) B5286863
theorem B4699433 : Blo 1955435 4699433 := bstep (se 2 (by rfl) ⟨1762287, by rfl⟩ : syracuseStep 4699433 = 3524575) B3524575
theorem B3132955 : Blo 1955435 3132955 := bstep (se 1 (by rfl) ⟨2349716, by rfl⟩ : syracuseStep 3132955 = 4699433) B4699433
theorem B4177273 : Blo 1955435 4177273 := bstep (se 2 (by rfl) ⟨1566477, by rfl⟩ : syracuseStep 4177273 = 3132955) B3132955
theorem B5569697 : Blo 1955435 5569697 := bstep (se 2 (by rfl) ⟨2088636, by rfl⟩ : syracuseStep 5569697 = 4177273) B4177273
theorem B3713131 : Blo 1955435 3713131 := bstep (se 1 (by rfl) ⟨2784848, by rfl⟩ : syracuseStep 3713131 = 5569697) B5569697
theorem B4950841 : Blo 1955435 4950841 := bstep (se 2 (by rfl) ⟨1856565, by rfl⟩ : syracuseStep 4950841 = 3713131) B3713131
theorem B6601121 : Blo 1955435 6601121 := bstep (se 2 (by rfl) ⟨2475420, by rfl⟩ : syracuseStep 6601121 = 4950841) B4950841
theorem B4400747 : Blo 1955435 4400747 := bstep (se 1 (by rfl) ⟨3300560, by rfl⟩ : syracuseStep 4400747 = 6601121) B6601121
theorem B2933831 : Blo 1955435 2933831 := bstep (se 1 (by rfl) ⟨2200373, by rfl⟩ : syracuseStep 2933831 = 4400747) B4400747
theorem B1955887 : Blo 1955435 1955887 := bstep (se 1 (by rfl) ⟨1466915, by rfl⟩ : syracuseStep 1955887 = 2933831) B2933831
theorem B2933837 : Blo 1955435 2933837 := bbase (se 3 (by rfl) ⟨550094, by rfl⟩ : syracuseStep 2933837 = 1100189) (by norm_num)
theorem B1955891 : Blo 1955435 1955891 := bstep (se 1 (by rfl) ⟨1466918, by rfl⟩ : syracuseStep 1955891 = 2933837) B2933837
theorem B4400765 : Blo 1955435 4400765 := bbase (se 3 (by rfl) ⟨825143, by rfl⟩ : syracuseStep 4400765 = 1650287) (by norm_num)
theorem B2933843 : Blo 1955435 2933843 := bstep (se 1 (by rfl) ⟨2200382, by rfl⟩ : syracuseStep 2933843 = 4400765) B4400765
theorem B1955895 : Blo 1955435 1955895 := bstep (se 1 (by rfl) ⟨1466921, by rfl⟩ : syracuseStep 1955895 = 2933843) B2933843
theorem B3300581 : Blo 1955435 3300581 := bbase (se 4 (by rfl) ⟨309429, by rfl⟩ : syracuseStep 3300581 = 618859) (by norm_num)
theorem B2200387 : Blo 1955435 2200387 := bstep (se 1 (by rfl) ⟨1650290, by rfl⟩ : syracuseStep 2200387 = 3300581) B3300581
theorem B2933849 : Blo 1955435 2933849 := bstep (se 2 (by rfl) ⟨1100193, by rfl⟩ : syracuseStep 2933849 = 2200387) B2200387
theorem B1955899 : Blo 1955435 1955899 := bstep (se 1 (by rfl) ⟨1466924, by rfl⟩ : syracuseStep 1955899 = 2933849) B2933849
theorem B5086901 : Blo 1955435 5086901 := bbase (se 5 (by rfl) ⟨238448, by rfl⟩ : syracuseStep 5086901 = 476897) (by norm_num)
theorem B13565069 : Blo 1955435 13565069 := bstep (se 3 (by rfl) ⟨2543450, by rfl⟩ : syracuseStep 13565069 = 5086901) B5086901
theorem B9043379 : Blo 1955435 9043379 := bstep (se 1 (by rfl) ⟨6782534, by rfl⟩ : syracuseStep 9043379 = 13565069) B13565069
theorem B6028919 : Blo 1955435 6028919 := bstep (se 1 (by rfl) ⟨4521689, by rfl⟩ : syracuseStep 6028919 = 9043379) B9043379
theorem B4019279 : Blo 1955435 4019279 := bstep (se 1 (by rfl) ⟨3014459, by rfl⟩ : syracuseStep 4019279 = 6028919) B6028919
theorem B10718077 : Blo 1955435 10718077 := bstep (se 3 (by rfl) ⟨2009639, by rfl⟩ : syracuseStep 10718077 = 4019279) B4019279
theorem B14290769 : Blo 1955435 14290769 := bstep (se 2 (by rfl) ⟨5359038, by rfl⟩ : syracuseStep 14290769 = 10718077) B10718077
theorem B38108717 : Blo 1955435 38108717 := bstep (se 3 (by rfl) ⟨7145384, by rfl⟩ : syracuseStep 38108717 = 14290769) B14290769
theorem B25405811 : Blo 1955435 25405811 := bstep (se 1 (by rfl) ⟨19054358, by rfl⟩ : syracuseStep 25405811 = 38108717) B38108717
theorem B16937207 : Blo 1955435 16937207 := bstep (se 1 (by rfl) ⟨12702905, by rfl⟩ : syracuseStep 16937207 = 25405811) B25405811
theorem B11291471 : Blo 1955435 11291471 := bstep (se 1 (by rfl) ⟨8468603, by rfl⟩ : syracuseStep 11291471 = 16937207) B16937207
theorem B7527647 : Blo 1955435 7527647 := bstep (se 1 (by rfl) ⟨5645735, by rfl⟩ : syracuseStep 7527647 = 11291471) B11291471
theorem B5018431 : Blo 1955435 5018431 := bstep (se 1 (by rfl) ⟨3763823, by rfl⟩ : syracuseStep 5018431 = 7527647) B7527647
theorem B6691241 : Blo 1955435 6691241 := bstep (se 2 (by rfl) ⟨2509215, by rfl⟩ : syracuseStep 6691241 = 5018431) B5018431
theorem B4460827 : Blo 1955435 4460827 := bstep (se 1 (by rfl) ⟨3345620, by rfl⟩ : syracuseStep 4460827 = 6691241) B6691241
theorem B5947769 : Blo 1955435 5947769 := bstep (se 2 (by rfl) ⟨2230413, by rfl⟩ : syracuseStep 5947769 = 4460827) B4460827
theorem B15860717 : Blo 1955435 15860717 := bstep (se 3 (by rfl) ⟨2973884, by rfl⟩ : syracuseStep 15860717 = 5947769) B5947769
theorem B10573811 : Blo 1955435 10573811 := bstep (se 1 (by rfl) ⟨7930358, by rfl⟩ : syracuseStep 10573811 = 15860717) B15860717
theorem B7049207 : Blo 1955435 7049207 := bstep (se 1 (by rfl) ⟨5286905, by rfl⟩ : syracuseStep 7049207 = 10573811) B10573811
theorem B4699471 : Blo 1955435 4699471 := bstep (se 1 (by rfl) ⟨3524603, by rfl⟩ : syracuseStep 4699471 = 7049207) B7049207
theorem B6265961 : Blo 1955435 6265961 := bstep (se 2 (by rfl) ⟨2349735, by rfl⟩ : syracuseStep 6265961 = 4699471) B4699471
theorem B4177307 : Blo 1955435 4177307 := bstep (se 1 (by rfl) ⟨3132980, by rfl⟩ : syracuseStep 4177307 = 6265961) B6265961
theorem B2784871 : Blo 1955435 2784871 := bstep (se 1 (by rfl) ⟨2088653, by rfl⟩ : syracuseStep 2784871 = 4177307) B4177307
theorem B14852645 : Blo 1955435 14852645 := bstep (se 4 (by rfl) ⟨1392435, by rfl⟩ : syracuseStep 14852645 = 2784871) B2784871
theorem B9901763 : Blo 1955435 9901763 := bstep (se 1 (by rfl) ⟨7426322, by rfl⟩ : syracuseStep 9901763 = 14852645) B14852645
theorem B6601175 : Blo 1955435 6601175 := bstep (se 1 (by rfl) ⟨4950881, by rfl⟩ : syracuseStep 6601175 = 9901763) B9901763
theorem B4400783 : Blo 1955435 4400783 := bstep (se 1 (by rfl) ⟨3300587, by rfl⟩ : syracuseStep 4400783 = 6601175) B6601175
theorem B2933855 : Blo 1955435 2933855 := bstep (se 1 (by rfl) ⟨2200391, by rfl⟩ : syracuseStep 2933855 = 4400783) B4400783
theorem B1955903 : Blo 1955435 1955903 := bstep (se 1 (by rfl) ⟨1466927, by rfl⟩ : syracuseStep 1955903 = 2933855) B2933855
theorem B2933861 : Blo 1955435 2933861 := bbase (se 4 (by rfl) ⟨275049, by rfl⟩ : syracuseStep 2933861 = 550099) (by norm_num)
theorem B1955907 : Blo 1955435 1955907 := bstep (se 1 (by rfl) ⟨1466930, by rfl⟩ : syracuseStep 1955907 = 2933861) B2933861
theorem B4177325 : Blo 1955435 4177325 := bbase (se 3 (by rfl) ⟨783248, by rfl⟩ : syracuseStep 4177325 = 1566497) (by norm_num)
theorem B2784883 : Blo 1955435 2784883 := bstep (se 1 (by rfl) ⟨2088662, by rfl⟩ : syracuseStep 2784883 = 4177325) B4177325
theorem B3713177 : Blo 1955435 3713177 := bstep (se 2 (by rfl) ⟨1392441, by rfl⟩ : syracuseStep 3713177 = 2784883) B2784883
theorem B2475451 : Blo 1955435 2475451 := bstep (se 1 (by rfl) ⟨1856588, by rfl⟩ : syracuseStep 2475451 = 3713177) B3713177
theorem B3300601 : Blo 1955435 3300601 := bstep (se 2 (by rfl) ⟨1237725, by rfl⟩ : syracuseStep 3300601 = 2475451) B2475451
theorem B4400801 : Blo 1955435 4400801 := bstep (se 2 (by rfl) ⟨1650300, by rfl⟩ : syracuseStep 4400801 = 3300601) B3300601
theorem B2933867 : Blo 1955435 2933867 := bstep (se 1 (by rfl) ⟨2200400, by rfl⟩ : syracuseStep 2933867 = 4400801) B4400801
theorem B1955911 : Blo 1955435 1955911 := bstep (se 1 (by rfl) ⟨1466933, by rfl⟩ : syracuseStep 1955911 = 2933867) B2933867
theorem B2200405 : Blo 1955435 2200405 := bbase (se 9 (by rfl) ⟨6446, by rfl⟩ : syracuseStep 2200405 = 12893) (by norm_num)
theorem B2933873 : Blo 1955435 2933873 := bstep (se 2 (by rfl) ⟨1100202, by rfl⟩ : syracuseStep 2933873 = 2200405) B2200405
theorem B1955915 : Blo 1955435 1955915 := bstep (se 1 (by rfl) ⟨1466936, by rfl⟩ : syracuseStep 1955915 = 2933873) B2933873
theorem B2475461 : Blo 1955435 2475461 := bbase (se 4 (by rfl) ⟨232074, by rfl⟩ : syracuseStep 2475461 = 464149) (by norm_num)
theorem B6601229 : Blo 1955435 6601229 := bstep (se 3 (by rfl) ⟨1237730, by rfl⟩ : syracuseStep 6601229 = 2475461) B2475461
theorem B4400819 : Blo 1955435 4400819 := bstep (se 1 (by rfl) ⟨3300614, by rfl⟩ : syracuseStep 4400819 = 6601229) B6601229
theorem B2933879 : Blo 1955435 2933879 := bstep (se 1 (by rfl) ⟨2200409, by rfl⟩ : syracuseStep 2933879 = 4400819) B4400819
theorem B1955919 : Blo 1955435 1955919 := bstep (se 1 (by rfl) ⟨1466939, by rfl⟩ : syracuseStep 1955919 = 2933879) B2933879
theorem B2933885 : Blo 1955435 2933885 := bbase (se 3 (by rfl) ⟨550103, by rfl⟩ : syracuseStep 2933885 = 1100207) (by norm_num)
theorem B1955923 : Blo 1955435 1955923 := bstep (se 1 (by rfl) ⟨1466942, by rfl⟩ : syracuseStep 1955923 = 2933885) B2933885
theorem B4400837 : Blo 1955435 4400837 := bbase (se 4 (by rfl) ⟨412578, by rfl⟩ : syracuseStep 4400837 = 825157) (by norm_num)
theorem B2933891 : Blo 1955435 2933891 := bstep (se 1 (by rfl) ⟨2200418, by rfl⟩ : syracuseStep 2933891 = 4400837) B4400837
theorem B1955927 : Blo 1955435 1955927 := bstep (se 1 (by rfl) ⟨1466945, by rfl⟩ : syracuseStep 1955927 = 2933891) B2933891
theorem B21147925 : Blo 1955435 21147925 := bbase (se 6 (by rfl) ⟨495654, by rfl⟩ : syracuseStep 21147925 = 991309) (by norm_num)
theorem B28197233 : Blo 1955435 28197233 := bstep (se 2 (by rfl) ⟨10573962, by rfl⟩ : syracuseStep 28197233 = 21147925) B21147925
theorem B18798155 : Blo 1955435 18798155 := bstep (se 1 (by rfl) ⟨14098616, by rfl⟩ : syracuseStep 18798155 = 28197233) B28197233
theorem B12532103 : Blo 1955435 12532103 := bstep (se 1 (by rfl) ⟨9399077, by rfl⟩ : syracuseStep 12532103 = 18798155) B18798155
theorem B8354735 : Blo 1955435 8354735 := bstep (se 1 (by rfl) ⟨6266051, by rfl⟩ : syracuseStep 8354735 = 12532103) B12532103
theorem B5569823 : Blo 1955435 5569823 := bstep (se 1 (by rfl) ⟨4177367, by rfl⟩ : syracuseStep 5569823 = 8354735) B8354735
theorem B3713215 : Blo 1955435 3713215 := bstep (se 1 (by rfl) ⟨2784911, by rfl⟩ : syracuseStep 3713215 = 5569823) B5569823
theorem B4950953 : Blo 1955435 4950953 := bstep (se 2 (by rfl) ⟨1856607, by rfl⟩ : syracuseStep 4950953 = 3713215) B3713215
theorem B3300635 : Blo 1955435 3300635 := bstep (se 1 (by rfl) ⟨2475476, by rfl⟩ : syracuseStep 3300635 = 4950953) B4950953
theorem B2200423 : Blo 1955435 2200423 := bstep (se 1 (by rfl) ⟨1650317, by rfl⟩ : syracuseStep 2200423 = 3300635) B3300635
theorem B2933897 : Blo 1955435 2933897 := bstep (se 2 (by rfl) ⟨1100211, by rfl⟩ : syracuseStep 2933897 = 2200423) B2200423
theorem B1955931 : Blo 1955435 1955931 := bstep (se 1 (by rfl) ⟨1466948, by rfl⟩ : syracuseStep 1955931 = 2933897) B2933897
theorem B9901925 : Blo 1955435 9901925 := bbase (se 4 (by rfl) ⟨928305, by rfl⟩ : syracuseStep 9901925 = 1856611) (by norm_num)
theorem B6601283 : Blo 1955435 6601283 := bstep (se 1 (by rfl) ⟨4950962, by rfl⟩ : syracuseStep 6601283 = 9901925) B9901925
theorem B4400855 : Blo 1955435 4400855 := bstep (se 1 (by rfl) ⟨3300641, by rfl⟩ : syracuseStep 4400855 = 6601283) B6601283
theorem B2933903 : Blo 1955435 2933903 := bstep (se 1 (by rfl) ⟨2200427, by rfl⟩ : syracuseStep 2933903 = 4400855) B4400855
theorem B1955935 : Blo 1955435 1955935 := bstep (se 1 (by rfl) ⟨1466951, by rfl⟩ : syracuseStep 1955935 = 2933903) B2933903
theorem B2933909 : Blo 1955435 2933909 := bbase (se 6 (by rfl) ⟨68763, by rfl⟩ : syracuseStep 2933909 = 137527) (by norm_num)
theorem B1955939 : Blo 1955435 1955939 := bstep (se 1 (by rfl) ⟨1466954, by rfl⟩ : syracuseStep 1955939 = 2933909) B2933909
theorem B3763901 : Blo 1955435 3763901 := bbase (se 3 (by rfl) ⟨705731, by rfl⟩ : syracuseStep 3763901 = 1411463) (by norm_num)
theorem B2509267 : Blo 1955435 2509267 := bstep (se 1 (by rfl) ⟨1881950, by rfl⟩ : syracuseStep 2509267 = 3763901) B3763901
theorem B3345689 : Blo 1955435 3345689 := bstep (se 2 (by rfl) ⟨1254633, by rfl⟩ : syracuseStep 3345689 = 2509267) B2509267
theorem B2230459 : Blo 1955435 2230459 := bstep (se 1 (by rfl) ⟨1672844, by rfl⟩ : syracuseStep 2230459 = 3345689) B3345689
theorem B11895781 : Blo 1955435 11895781 := bstep (se 4 (by rfl) ⟨1115229, by rfl⟩ : syracuseStep 11895781 = 2230459) B2230459
theorem B15861041 : Blo 1955435 15861041 := bstep (se 2 (by rfl) ⟨5947890, by rfl⟩ : syracuseStep 15861041 = 11895781) B11895781
theorem B10574027 : Blo 1955435 10574027 := bstep (se 1 (by rfl) ⟨7930520, by rfl⟩ : syracuseStep 10574027 = 15861041) B15861041
theorem B7049351 : Blo 1955435 7049351 := bstep (se 1 (by rfl) ⟨5287013, by rfl⟩ : syracuseStep 7049351 = 10574027) B10574027
theorem B4699567 : Blo 1955435 4699567 := bstep (se 1 (by rfl) ⟨3524675, by rfl⟩ : syracuseStep 4699567 = 7049351) B7049351
theorem B6266089 : Blo 1955435 6266089 := bstep (se 2 (by rfl) ⟨2349783, by rfl⟩ : syracuseStep 6266089 = 4699567) B4699567
theorem B8354785 : Blo 1955435 8354785 := bstep (se 2 (by rfl) ⟨3133044, by rfl⟩ : syracuseStep 8354785 = 6266089) B6266089
theorem B11139713 : Blo 1955435 11139713 := bstep (se 2 (by rfl) ⟨4177392, by rfl⟩ : syracuseStep 11139713 = 8354785) B8354785
theorem B7426475 : Blo 1955435 7426475 := bstep (se 1 (by rfl) ⟨5569856, by rfl⟩ : syracuseStep 7426475 = 11139713) B11139713
theorem B4950983 : Blo 1955435 4950983 := bstep (se 1 (by rfl) ⟨3713237, by rfl⟩ : syracuseStep 4950983 = 7426475) B7426475
theorem B3300655 : Blo 1955435 3300655 := bstep (se 1 (by rfl) ⟨2475491, by rfl⟩ : syracuseStep 3300655 = 4950983) B4950983
theorem B4400873 : Blo 1955435 4400873 := bstep (se 2 (by rfl) ⟨1650327, by rfl⟩ : syracuseStep 4400873 = 3300655) B3300655
theorem B2933915 : Blo 1955435 2933915 := bstep (se 1 (by rfl) ⟨2200436, by rfl⟩ : syracuseStep 2933915 = 4400873) B4400873
theorem B1955943 : Blo 1955435 1955943 := bstep (se 1 (by rfl) ⟨1466957, by rfl⟩ : syracuseStep 1955943 = 2933915) B2933915
theorem B2200441 : Blo 1955435 2200441 := bbase (se 2 (by rfl) ⟨825165, by rfl⟩ : syracuseStep 2200441 = 1650331) (by norm_num)
theorem B2933921 : Blo 1955435 2933921 := bstep (se 2 (by rfl) ⟨1100220, by rfl⟩ : syracuseStep 2933921 = 2200441) B2200441
theorem B1955947 : Blo 1955435 1955947 := bstep (se 1 (by rfl) ⟨1466960, by rfl⟩ : syracuseStep 1955947 = 2933921) B2933921
theorem B2349793 : Blo 1955435 2349793 := bbase (se 2 (by rfl) ⟨881172, by rfl⟩ : syracuseStep 2349793 = 1762345) (by norm_num)
theorem B12532229 : Blo 1955435 12532229 := bstep (se 4 (by rfl) ⟨1174896, by rfl⟩ : syracuseStep 12532229 = 2349793) B2349793
theorem B8354819 : Blo 1955435 8354819 := bstep (se 1 (by rfl) ⟨6266114, by rfl⟩ : syracuseStep 8354819 = 12532229) B12532229
theorem B5569879 : Blo 1955435 5569879 := bstep (se 1 (by rfl) ⟨4177409, by rfl⟩ : syracuseStep 5569879 = 8354819) B8354819
theorem B7426505 : Blo 1955435 7426505 := bstep (se 2 (by rfl) ⟨2784939, by rfl⟩ : syracuseStep 7426505 = 5569879) B5569879
theorem B4951003 : Blo 1955435 4951003 := bstep (se 1 (by rfl) ⟨3713252, by rfl⟩ : syracuseStep 4951003 = 7426505) B7426505
theorem B6601337 : Blo 1955435 6601337 := bstep (se 2 (by rfl) ⟨2475501, by rfl⟩ : syracuseStep 6601337 = 4951003) B4951003
theorem B4400891 : Blo 1955435 4400891 := bstep (se 1 (by rfl) ⟨3300668, by rfl⟩ : syracuseStep 4400891 = 6601337) B6601337
theorem B2933927 : Blo 1955435 2933927 := bstep (se 1 (by rfl) ⟨2200445, by rfl⟩ : syracuseStep 2933927 = 4400891) B4400891
theorem B1955951 : Blo 1955435 1955951 := bstep (se 1 (by rfl) ⟨1466963, by rfl⟩ : syracuseStep 1955951 = 2933927) B2933927
theorem B2933933 : Blo 1955435 2933933 := bbase (se 3 (by rfl) ⟨550112, by rfl⟩ : syracuseStep 2933933 = 1100225) (by norm_num)
theorem B1955955 : Blo 1955435 1955955 := bstep (se 1 (by rfl) ⟨1466966, by rfl⟩ : syracuseStep 1955955 = 2933933) B2933933
theorem B4400909 : Blo 1955435 4400909 := bbase (se 3 (by rfl) ⟨825170, by rfl⟩ : syracuseStep 4400909 = 1650341) (by norm_num)
theorem B2933939 : Blo 1955435 2933939 := bstep (se 1 (by rfl) ⟨2200454, by rfl⟩ : syracuseStep 2933939 = 4400909) B4400909
theorem B1955959 : Blo 1955435 1955959 := bstep (se 1 (by rfl) ⟨1466969, by rfl⟩ : syracuseStep 1955959 = 2933939) B2933939
theorem B2475517 : Blo 1955435 2475517 := bbase (se 3 (by rfl) ⟨464159, by rfl⟩ : syracuseStep 2475517 = 928319) (by norm_num)
theorem B3300689 : Blo 1955435 3300689 := bstep (se 2 (by rfl) ⟨1237758, by rfl⟩ : syracuseStep 3300689 = 2475517) B2475517
theorem B2200459 : Blo 1955435 2200459 := bstep (se 1 (by rfl) ⟨1650344, by rfl⟩ : syracuseStep 2200459 = 3300689) B3300689
theorem B2933945 : Blo 1955435 2933945 := bstep (se 2 (by rfl) ⟨1100229, by rfl⟩ : syracuseStep 2933945 = 2200459) B2200459
theorem B1955963 : Blo 1955435 1955963 := bstep (se 1 (by rfl) ⟨1466972, by rfl⟩ : syracuseStep 1955963 = 2933945) B2933945
theorem B6266165 : Blo 1955435 6266165 := bbase (se 5 (by rfl) ⟨293726, by rfl⟩ : syracuseStep 6266165 = 587453) (by norm_num)
theorem B16709773 : Blo 1955435 16709773 := bstep (se 3 (by rfl) ⟨3133082, by rfl⟩ : syracuseStep 16709773 = 6266165) B6266165
theorem B22279697 : Blo 1955435 22279697 := bstep (se 2 (by rfl) ⟨8354886, by rfl⟩ : syracuseStep 22279697 = 16709773) B16709773
theorem B14853131 : Blo 1955435 14853131 := bstep (se 1 (by rfl) ⟨11139848, by rfl⟩ : syracuseStep 14853131 = 22279697) B22279697
theorem B9902087 : Blo 1955435 9902087 := bstep (se 1 (by rfl) ⟨7426565, by rfl⟩ : syracuseStep 9902087 = 14853131) B14853131
theorem B6601391 : Blo 1955435 6601391 := bstep (se 1 (by rfl) ⟨4951043, by rfl⟩ : syracuseStep 6601391 = 9902087) B9902087
theorem B4400927 : Blo 1955435 4400927 := bstep (se 1 (by rfl) ⟨3300695, by rfl⟩ : syracuseStep 4400927 = 6601391) B6601391
theorem B2933951 : Blo 1955435 2933951 := bstep (se 1 (by rfl) ⟨2200463, by rfl⟩ : syracuseStep 2933951 = 4400927) B4400927
theorem B1955967 : Blo 1955435 1955967 := bstep (se 1 (by rfl) ⟨1466975, by rfl⟩ : syracuseStep 1955967 = 2933951) B2933951
theorem B2933957 : Blo 1955435 2933957 := bbase (se 4 (by rfl) ⟨275058, by rfl⟩ : syracuseStep 2933957 = 550117) (by norm_num)
theorem B1955971 : Blo 1955435 1955971 := bstep (se 1 (by rfl) ⟨1466978, by rfl⟩ : syracuseStep 1955971 = 2933957) B2933957
theorem B3300709 : Blo 1955435 3300709 := bbase (se 4 (by rfl) ⟨309441, by rfl⟩ : syracuseStep 3300709 = 618883) (by norm_num)
theorem B4400945 : Blo 1955435 4400945 := bstep (se 2 (by rfl) ⟨1650354, by rfl⟩ : syracuseStep 4400945 = 3300709) B3300709
theorem B2933963 : Blo 1955435 2933963 := bstep (se 1 (by rfl) ⟨2200472, by rfl⟩ : syracuseStep 2933963 = 4400945) B4400945
theorem B1955975 : Blo 1955435 1955975 := bstep (se 1 (by rfl) ⟨1466981, by rfl⟩ : syracuseStep 1955975 = 2933963) B2933963
theorem B2200477 : Blo 1955435 2200477 := bbase (se 3 (by rfl) ⟨412589, by rfl⟩ : syracuseStep 2200477 = 825179) (by norm_num)
theorem B2933969 : Blo 1955435 2933969 := bstep (se 2 (by rfl) ⟨1100238, by rfl⟩ : syracuseStep 2933969 = 2200477) B2200477
theorem B1955979 : Blo 1955435 1955979 := bstep (se 1 (by rfl) ⟨1466984, by rfl⟩ : syracuseStep 1955979 = 2933969) B2933969
theorem B6601445 : Blo 1955435 6601445 := bbase (se 4 (by rfl) ⟨618885, by rfl⟩ : syracuseStep 6601445 = 1237771) (by norm_num)
theorem B4400963 : Blo 1955435 4400963 := bstep (se 1 (by rfl) ⟨3300722, by rfl⟩ : syracuseStep 4400963 = 6601445) B6601445
theorem B2933975 : Blo 1955435 2933975 := bstep (se 1 (by rfl) ⟨2200481, by rfl⟩ : syracuseStep 2933975 = 4400963) B4400963
theorem B1955983 : Blo 1955435 1955983 := bstep (se 1 (by rfl) ⟨1466987, by rfl⟩ : syracuseStep 1955983 = 2933975) B2933975
theorem B2933981 : Blo 1955435 2933981 := bbase (se 3 (by rfl) ⟨550121, by rfl⟩ : syracuseStep 2933981 = 1100243) (by norm_num)
theorem B1955987 : Blo 1955435 1955987 := bstep (se 1 (by rfl) ⟨1466990, by rfl⟩ : syracuseStep 1955987 = 2933981) B2933981
theorem B4400981 : Blo 1955435 4400981 := bbase (se 9 (by rfl) ⟨12893, by rfl⟩ : syracuseStep 4400981 = 25787) (by norm_num)
theorem B2933987 : Blo 1955435 2933987 := bstep (se 1 (by rfl) ⟨2200490, by rfl⟩ : syracuseStep 2933987 = 4400981) B4400981
theorem B1955991 : Blo 1955435 1955991 := bstep (se 1 (by rfl) ⟨1466993, by rfl⟩ : syracuseStep 1955991 = 2933987) B2933987
theorem B5570005 : Blo 1955435 5570005 := bbase (se 7 (by rfl) ⟨65273, by rfl⟩ : syracuseStep 5570005 = 130547) (by norm_num)
theorem B7426673 : Blo 1955435 7426673 := bstep (se 2 (by rfl) ⟨2785002, by rfl⟩ : syracuseStep 7426673 = 5570005) B5570005
theorem B4951115 : Blo 1955435 4951115 := bstep (se 1 (by rfl) ⟨3713336, by rfl⟩ : syracuseStep 4951115 = 7426673) B7426673
theorem B3300743 : Blo 1955435 3300743 := bstep (se 1 (by rfl) ⟨2475557, by rfl⟩ : syracuseStep 3300743 = 4951115) B4951115
theorem B2200495 : Blo 1955435 2200495 := bstep (se 1 (by rfl) ⟨1650371, by rfl⟩ : syracuseStep 2200495 = 3300743) B3300743
theorem B2933993 : Blo 1955435 2933993 := bstep (se 2 (by rfl) ⟨1100247, by rfl⟩ : syracuseStep 2933993 = 2200495) B2200495
theorem B1955995 : Blo 1955435 1955995 := bstep (se 1 (by rfl) ⟨1466996, by rfl⟩ : syracuseStep 1955995 = 2933993) B2933993
theorem B2823005 : Blo 1955435 2823005 := bbase (se 3 (by rfl) ⟨529313, by rfl⟩ : syracuseStep 2823005 = 1058627) (by norm_num)
theorem B7528013 : Blo 1955435 7528013 := bstep (se 3 (by rfl) ⟨1411502, by rfl⟩ : syracuseStep 7528013 = 2823005) B2823005
theorem B5018675 : Blo 1955435 5018675 := bstep (se 1 (by rfl) ⟨3764006, by rfl⟩ : syracuseStep 5018675 = 7528013) B7528013
theorem B13383133 : Blo 1955435 13383133 := bstep (se 3 (by rfl) ⟨2509337, by rfl⟩ : syracuseStep 13383133 = 5018675) B5018675
theorem B71376709 : Blo 1955435 71376709 := bstep (se 4 (by rfl) ⟨6691566, by rfl⟩ : syracuseStep 71376709 = 13383133) B13383133
theorem B95168945 : Blo 1955435 95168945 := bstep (se 2 (by rfl) ⟨35688354, by rfl⟩ : syracuseStep 95168945 = 71376709) B71376709
theorem B63445963 : Blo 1955435 63445963 := bstep (se 1 (by rfl) ⟨47584472, by rfl⟩ : syracuseStep 63445963 = 95168945) B95168945
theorem B84594617 : Blo 1955435 84594617 := bstep (se 2 (by rfl) ⟨31722981, by rfl⟩ : syracuseStep 84594617 = 63445963) B63445963
theorem B56396411 : Blo 1955435 56396411 := bstep (se 1 (by rfl) ⟨42297308, by rfl⟩ : syracuseStep 56396411 = 84594617) B84594617
theorem B37597607 : Blo 1955435 37597607 := bstep (se 1 (by rfl) ⟨28198205, by rfl⟩ : syracuseStep 37597607 = 56396411) B56396411
theorem B25065071 : Blo 1955435 25065071 := bstep (se 1 (by rfl) ⟨18798803, by rfl⟩ : syracuseStep 25065071 = 37597607) B37597607
theorem B16710047 : Blo 1955435 16710047 := bstep (se 1 (by rfl) ⟨12532535, by rfl⟩ : syracuseStep 16710047 = 25065071) B25065071
theorem B11140031 : Blo 1955435 11140031 := bstep (se 1 (by rfl) ⟨8355023, by rfl⟩ : syracuseStep 11140031 = 16710047) B16710047
theorem B7426687 : Blo 1955435 7426687 := bstep (se 1 (by rfl) ⟨5570015, by rfl⟩ : syracuseStep 7426687 = 11140031) B11140031
theorem B9902249 : Blo 1955435 9902249 := bstep (se 2 (by rfl) ⟨3713343, by rfl⟩ : syracuseStep 9902249 = 7426687) B7426687
theorem B6601499 : Blo 1955435 6601499 := bstep (se 1 (by rfl) ⟨4951124, by rfl⟩ : syracuseStep 6601499 = 9902249) B9902249
theorem B4400999 : Blo 1955435 4400999 := bstep (se 1 (by rfl) ⟨3300749, by rfl⟩ : syracuseStep 4400999 = 6601499) B6601499
theorem B2933999 : Blo 1955435 2933999 := bstep (se 1 (by rfl) ⟨2200499, by rfl⟩ : syracuseStep 2933999 = 4400999) B4400999
theorem B1955999 : Blo 1955435 1955999 := bstep (se 1 (by rfl) ⟨1466999, by rfl⟩ : syracuseStep 1955999 = 2933999) B2933999
theorem B2934005 : Blo 1955435 2934005 := bbase (se 5 (by rfl) ⟨137531, by rfl⟩ : syracuseStep 2934005 = 275063) (by norm_num)
theorem B1956003 : Blo 1955435 1956003 := bstep (se 1 (by rfl) ⟨1467002, by rfl⟩ : syracuseStep 1956003 = 2934005) B2934005
theorem B5646037 : Blo 1955435 5646037 := bbase (se 7 (by rfl) ⟨66164, by rfl⟩ : syracuseStep 5646037 = 132329) (by norm_num)
theorem B7528049 : Blo 1955435 7528049 := bstep (se 2 (by rfl) ⟨2823018, by rfl⟩ : syracuseStep 7528049 = 5646037) B5646037
theorem B5018699 : Blo 1955435 5018699 := bstep (se 1 (by rfl) ⟨3764024, by rfl⟩ : syracuseStep 5018699 = 7528049) B7528049
theorem B3345799 : Blo 1955435 3345799 := bstep (se 1 (by rfl) ⟨2509349, by rfl⟩ : syracuseStep 3345799 = 5018699) B5018699
theorem B4461065 : Blo 1955435 4461065 := bstep (se 2 (by rfl) ⟨1672899, by rfl⟩ : syracuseStep 4461065 = 3345799) B3345799
theorem B2974043 : Blo 1955435 2974043 := bstep (se 1 (by rfl) ⟨2230532, by rfl⟩ : syracuseStep 2974043 = 4461065) B4461065
theorem B7930781 : Blo 1955435 7930781 := bstep (se 3 (by rfl) ⟨1487021, by rfl⟩ : syracuseStep 7930781 = 2974043) B2974043
theorem B5287187 : Blo 1955435 5287187 := bstep (se 1 (by rfl) ⟨3965390, by rfl⟩ : syracuseStep 5287187 = 7930781) B7930781
theorem B3524791 : Blo 1955435 3524791 := bstep (se 1 (by rfl) ⟨2643593, by rfl⟩ : syracuseStep 3524791 = 5287187) B5287187
theorem B4699721 : Blo 1955435 4699721 := bstep (se 2 (by rfl) ⟨1762395, by rfl⟩ : syracuseStep 4699721 = 3524791) B3524791
theorem B12532589 : Blo 1955435 12532589 := bstep (se 3 (by rfl) ⟨2349860, by rfl⟩ : syracuseStep 12532589 = 4699721) B4699721
theorem B8355059 : Blo 1955435 8355059 := bstep (se 1 (by rfl) ⟨6266294, by rfl⟩ : syracuseStep 8355059 = 12532589) B12532589
theorem B5570039 : Blo 1955435 5570039 := bstep (se 1 (by rfl) ⟨4177529, by rfl⟩ : syracuseStep 5570039 = 8355059) B8355059
theorem B3713359 : Blo 1955435 3713359 := bstep (se 1 (by rfl) ⟨2785019, by rfl⟩ : syracuseStep 3713359 = 5570039) B5570039
theorem B4951145 : Blo 1955435 4951145 := bstep (se 2 (by rfl) ⟨1856679, by rfl⟩ : syracuseStep 4951145 = 3713359) B3713359
theorem B3300763 : Blo 1955435 3300763 := bstep (se 1 (by rfl) ⟨2475572, by rfl⟩ : syracuseStep 3300763 = 4951145) B4951145
theorem B4401017 : Blo 1955435 4401017 := bstep (se 2 (by rfl) ⟨1650381, by rfl⟩ : syracuseStep 4401017 = 3300763) B3300763
theorem B2934011 : Blo 1955435 2934011 := bstep (se 1 (by rfl) ⟨2200508, by rfl⟩ : syracuseStep 2934011 = 4401017) B4401017
theorem B1956007 : Blo 1955435 1956007 := bstep (se 1 (by rfl) ⟨1467005, by rfl⟩ : syracuseStep 1956007 = 2934011) B2934011
theorem B2200513 : Blo 1955435 2200513 := bbase (se 2 (by rfl) ⟨825192, by rfl⟩ : syracuseStep 2200513 = 1650385) (by norm_num)
theorem B2934017 : Blo 1955435 2934017 := bstep (se 2 (by rfl) ⟨1100256, by rfl⟩ : syracuseStep 2934017 = 2200513) B2200513
theorem B1956011 : Blo 1955435 1956011 := bstep (se 1 (by rfl) ⟨1467008, by rfl⟩ : syracuseStep 1956011 = 2934017) B2934017
theorem B4951165 : Blo 1955435 4951165 := bbase (se 3 (by rfl) ⟨928343, by rfl⟩ : syracuseStep 4951165 = 1856687) (by norm_num)
theorem B6601553 : Blo 1955435 6601553 := bstep (se 2 (by rfl) ⟨2475582, by rfl⟩ : syracuseStep 6601553 = 4951165) B4951165
theorem B4401035 : Blo 1955435 4401035 := bstep (se 1 (by rfl) ⟨3300776, by rfl⟩ : syracuseStep 4401035 = 6601553) B6601553
theorem B2934023 : Blo 1955435 2934023 := bstep (se 1 (by rfl) ⟨2200517, by rfl⟩ : syracuseStep 2934023 = 4401035) B4401035
theorem B1956015 : Blo 1955435 1956015 := bstep (se 1 (by rfl) ⟨1467011, by rfl⟩ : syracuseStep 1956015 = 2934023) B2934023
theorem B2934029 : Blo 1955435 2934029 := bbase (se 3 (by rfl) ⟨550130, by rfl⟩ : syracuseStep 2934029 = 1100261) (by norm_num)
theorem B1956019 : Blo 1955435 1956019 := bstep (se 1 (by rfl) ⟨1467014, by rfl⟩ : syracuseStep 1956019 = 2934029) B2934029
theorem B4401053 : Blo 1955435 4401053 := bbase (se 3 (by rfl) ⟨825197, by rfl⟩ : syracuseStep 4401053 = 1650395) (by norm_num)
theorem B2934035 : Blo 1955435 2934035 := bstep (se 1 (by rfl) ⟨2200526, by rfl⟩ : syracuseStep 2934035 = 4401053) B4401053
theorem B1956023 : Blo 1955435 1956023 := bstep (se 1 (by rfl) ⟨1467017, by rfl⟩ : syracuseStep 1956023 = 2934035) B2934035
theorem B3300797 : Blo 1955435 3300797 := bbase (se 3 (by rfl) ⟨618899, by rfl⟩ : syracuseStep 3300797 = 1237799) (by norm_num)
theorem B2200531 : Blo 1955435 2200531 := bstep (se 1 (by rfl) ⟨1650398, by rfl⟩ : syracuseStep 2200531 = 3300797) B3300797
theorem B2934041 : Blo 1955435 2934041 := bstep (se 2 (by rfl) ⟨1100265, by rfl⟩ : syracuseStep 2934041 = 2200531) B2200531
theorem B1956027 : Blo 1955435 1956027 := bstep (se 1 (by rfl) ⟨1467020, by rfl⟩ : syracuseStep 1956027 = 2934041) B2934041
theorem B11140213 : Blo 1955435 11140213 := bbase (se 5 (by rfl) ⟨522197, by rfl⟩ : syracuseStep 11140213 = 1044395) (by norm_num)
theorem B14853617 : Blo 1955435 14853617 := bstep (se 2 (by rfl) ⟨5570106, by rfl⟩ : syracuseStep 14853617 = 11140213) B11140213
theorem B9902411 : Blo 1955435 9902411 := bstep (se 1 (by rfl) ⟨7426808, by rfl⟩ : syracuseStep 9902411 = 14853617) B14853617
theorem B6601607 : Blo 1955435 6601607 := bstep (se 1 (by rfl) ⟨4951205, by rfl⟩ : syracuseStep 6601607 = 9902411) B9902411
theorem B4401071 : Blo 1955435 4401071 := bstep (se 1 (by rfl) ⟨3300803, by rfl⟩ : syracuseStep 4401071 = 6601607) B6601607
theorem B2934047 : Blo 1955435 2934047 := bstep (se 1 (by rfl) ⟨2200535, by rfl⟩ : syracuseStep 2934047 = 4401071) B4401071
theorem B1956031 : Blo 1955435 1956031 := bstep (se 1 (by rfl) ⟨1467023, by rfl⟩ : syracuseStep 1956031 = 2934047) B2934047
theorem B2934053 : Blo 1955435 2934053 := bbase (se 4 (by rfl) ⟨275067, by rfl⟩ : syracuseStep 2934053 = 550135) (by norm_num)
theorem B1956035 : Blo 1955435 1956035 := bstep (se 1 (by rfl) ⟨1467026, by rfl⟩ : syracuseStep 1956035 = 2934053) B2934053
theorem B2475613 : Blo 1955435 2475613 := bbase (se 3 (by rfl) ⟨464177, by rfl⟩ : syracuseStep 2475613 = 928355) (by norm_num)
theorem B3300817 : Blo 1955435 3300817 := bstep (se 2 (by rfl) ⟨1237806, by rfl⟩ : syracuseStep 3300817 = 2475613) B2475613
theorem B4401089 : Blo 1955435 4401089 := bstep (se 2 (by rfl) ⟨1650408, by rfl⟩ : syracuseStep 4401089 = 3300817) B3300817
theorem B2934059 : Blo 1955435 2934059 := bstep (se 1 (by rfl) ⟨2200544, by rfl⟩ : syracuseStep 2934059 = 4401089) B4401089
theorem B1956039 : Blo 1955435 1956039 := bstep (se 1 (by rfl) ⟨1467029, by rfl⟩ : syracuseStep 1956039 = 2934059) B2934059
theorem B2200549 : Blo 1955435 2200549 := bbase (se 4 (by rfl) ⟨206301, by rfl⟩ : syracuseStep 2200549 = 412603) (by norm_num)
theorem B2934065 : Blo 1955435 2934065 := bstep (se 2 (by rfl) ⟨1100274, by rfl⟩ : syracuseStep 2934065 = 2200549) B2200549
theorem B1956043 : Blo 1955435 1956043 := bstep (se 1 (by rfl) ⟨1467032, by rfl⟩ : syracuseStep 1956043 = 2934065) B2934065
theorem B4234613 : Blo 1955435 4234613 := bbase (se 5 (by rfl) ⟨198497, by rfl⟩ : syracuseStep 4234613 = 396995) (by norm_num)
theorem B11292301 : Blo 1955435 11292301 := bstep (se 3 (by rfl) ⟨2117306, by rfl⟩ : syracuseStep 11292301 = 4234613) B4234613
theorem B60225605 : Blo 1955435 60225605 := bstep (se 4 (by rfl) ⟨5646150, by rfl⟩ : syracuseStep 60225605 = 11292301) B11292301
theorem B40150403 : Blo 1955435 40150403 := bstep (se 1 (by rfl) ⟨30112802, by rfl⟩ : syracuseStep 40150403 = 60225605) B60225605
theorem B26766935 : Blo 1955435 26766935 := bstep (se 1 (by rfl) ⟨20075201, by rfl⟩ : syracuseStep 26766935 = 40150403) B40150403
theorem B17844623 : Blo 1955435 17844623 := bstep (se 1 (by rfl) ⟨13383467, by rfl⟩ : syracuseStep 17844623 = 26766935) B26766935
theorem B11896415 : Blo 1955435 11896415 := bstep (se 1 (by rfl) ⟨8922311, by rfl⟩ : syracuseStep 11896415 = 17844623) B17844623
theorem B7930943 : Blo 1955435 7930943 := bstep (se 1 (by rfl) ⟨5948207, by rfl⟩ : syracuseStep 7930943 = 11896415) B11896415
theorem B5287295 : Blo 1955435 5287295 := bstep (se 1 (by rfl) ⟨3965471, by rfl⟩ : syracuseStep 5287295 = 7930943) B7930943
theorem B14099453 : Blo 1955435 14099453 := bstep (se 3 (by rfl) ⟨2643647, by rfl⟩ : syracuseStep 14099453 = 5287295) B5287295
theorem B9399635 : Blo 1955435 9399635 := bstep (se 1 (by rfl) ⟨7049726, by rfl⟩ : syracuseStep 9399635 = 14099453) B14099453
theorem B6266423 : Blo 1955435 6266423 := bstep (se 1 (by rfl) ⟨4699817, by rfl⟩ : syracuseStep 6266423 = 9399635) B9399635
theorem B4177615 : Blo 1955435 4177615 := bstep (se 1 (by rfl) ⟨3133211, by rfl⟩ : syracuseStep 4177615 = 6266423) B6266423
theorem B5570153 : Blo 1955435 5570153 := bstep (se 2 (by rfl) ⟨2088807, by rfl⟩ : syracuseStep 5570153 = 4177615) B4177615
theorem B3713435 : Blo 1955435 3713435 := bstep (se 1 (by rfl) ⟨2785076, by rfl⟩ : syracuseStep 3713435 = 5570153) B5570153
theorem B2475623 : Blo 1955435 2475623 := bstep (se 1 (by rfl) ⟨1856717, by rfl⟩ : syracuseStep 2475623 = 3713435) B3713435
theorem B6601661 : Blo 1955435 6601661 := bstep (se 3 (by rfl) ⟨1237811, by rfl⟩ : syracuseStep 6601661 = 2475623) B2475623
theorem B4401107 : Blo 1955435 4401107 := bstep (se 1 (by rfl) ⟨3300830, by rfl⟩ : syracuseStep 4401107 = 6601661) B6601661
theorem B2934071 : Blo 1955435 2934071 := bstep (se 1 (by rfl) ⟨2200553, by rfl⟩ : syracuseStep 2934071 = 4401107) B4401107
theorem B1956047 : Blo 1955435 1956047 := bstep (se 1 (by rfl) ⟨1467035, by rfl⟩ : syracuseStep 1956047 = 2934071) B2934071
theorem B2934077 : Blo 1955435 2934077 := bbase (se 3 (by rfl) ⟨550139, by rfl⟩ : syracuseStep 2934077 = 1100279) (by norm_num)
theorem B1956051 : Blo 1955435 1956051 := bstep (se 1 (by rfl) ⟨1467038, by rfl⟩ : syracuseStep 1956051 = 2934077) B2934077
theorem B4401125 : Blo 1955435 4401125 := bbase (se 4 (by rfl) ⟨412605, by rfl⟩ : syracuseStep 4401125 = 825211) (by norm_num)
theorem B2934083 : Blo 1955435 2934083 := bstep (se 1 (by rfl) ⟨2200562, by rfl⟩ : syracuseStep 2934083 = 4401125) B4401125
theorem B1956055 : Blo 1955435 1956055 := bstep (se 1 (by rfl) ⟨1467041, by rfl⟩ : syracuseStep 1956055 = 2934083) B2934083
theorem B4951277 : Blo 1955435 4951277 := bbase (se 3 (by rfl) ⟨928364, by rfl⟩ : syracuseStep 4951277 = 1856729) (by norm_num)
theorem B3300851 : Blo 1955435 3300851 := bstep (se 1 (by rfl) ⟨2475638, by rfl⟩ : syracuseStep 3300851 = 4951277) B4951277
theorem B2200567 : Blo 1955435 2200567 := bstep (se 1 (by rfl) ⟨1650425, by rfl⟩ : syracuseStep 2200567 = 3300851) B3300851
theorem B2934089 : Blo 1955435 2934089 := bstep (se 2 (by rfl) ⟨1100283, by rfl⟩ : syracuseStep 2934089 = 2200567) B2200567
theorem B1956059 : Blo 1955435 1956059 := bstep (se 1 (by rfl) ⟨1467044, by rfl⟩ : syracuseStep 1956059 = 2934089) B2934089
theorem B3133237 : Blo 1955435 3133237 := bbase (se 5 (by rfl) ⟨146870, by rfl⟩ : syracuseStep 3133237 = 293741) (by norm_num)
theorem B4177649 : Blo 1955435 4177649 := bstep (se 2 (by rfl) ⟨1566618, by rfl⟩ : syracuseStep 4177649 = 3133237) B3133237
theorem B2785099 : Blo 1955435 2785099 := bstep (se 1 (by rfl) ⟨2088824, by rfl⟩ : syracuseStep 2785099 = 4177649) B4177649
theorem B3713465 : Blo 1955435 3713465 := bstep (se 2 (by rfl) ⟨1392549, by rfl⟩ : syracuseStep 3713465 = 2785099) B2785099
theorem B9902573 : Blo 1955435 9902573 := bstep (se 3 (by rfl) ⟨1856732, by rfl⟩ : syracuseStep 9902573 = 3713465) B3713465
theorem B6601715 : Blo 1955435 6601715 := bstep (se 1 (by rfl) ⟨4951286, by rfl⟩ : syracuseStep 6601715 = 9902573) B9902573
theorem B4401143 : Blo 1955435 4401143 := bstep (se 1 (by rfl) ⟨3300857, by rfl⟩ : syracuseStep 4401143 = 6601715) B6601715
theorem B2934095 : Blo 1955435 2934095 := bstep (se 1 (by rfl) ⟨2200571, by rfl⟩ : syracuseStep 2934095 = 4401143) B4401143
theorem B1956063 : Blo 1955435 1956063 := bstep (se 1 (by rfl) ⟨1467047, by rfl⟩ : syracuseStep 1956063 = 2934095) B2934095
theorem B2934101 : Blo 1955435 2934101 := bbase (se 12 (by rfl) ⟨1074, by rfl⟩ : syracuseStep 2934101 = 2149) (by norm_num)
theorem B1956067 : Blo 1955435 1956067 := bstep (se 1 (by rfl) ⟨1467050, by rfl⟩ : syracuseStep 1956067 = 2934101) B2934101
theorem B2088833 : Blo 1955435 2088833 := bbase (se 2 (by rfl) ⟨783312, by rfl⟩ : syracuseStep 2088833 = 1566625) (by norm_num)
theorem B5570221 : Blo 1955435 5570221 := bstep (se 3 (by rfl) ⟨1044416, by rfl⟩ : syracuseStep 5570221 = 2088833) B2088833
theorem B7426961 : Blo 1955435 7426961 := bstep (se 2 (by rfl) ⟨2785110, by rfl⟩ : syracuseStep 7426961 = 5570221) B5570221
theorem B4951307 : Blo 1955435 4951307 := bstep (se 1 (by rfl) ⟨3713480, by rfl⟩ : syracuseStep 4951307 = 7426961) B7426961
theorem B3300871 : Blo 1955435 3300871 := bstep (se 1 (by rfl) ⟨2475653, by rfl⟩ : syracuseStep 3300871 = 4951307) B4951307
theorem B4401161 : Blo 1955435 4401161 := bstep (se 2 (by rfl) ⟨1650435, by rfl⟩ : syracuseStep 4401161 = 3300871) B3300871
theorem B2934107 : Blo 1955435 2934107 := bstep (se 1 (by rfl) ⟨2200580, by rfl⟩ : syracuseStep 2934107 = 4401161) B4401161
theorem B1956071 : Blo 1955435 1956071 := bstep (se 1 (by rfl) ⟨1467053, by rfl⟩ : syracuseStep 1956071 = 2934107) B2934107
theorem B2200585 : Blo 1955435 2200585 := bbase (se 2 (by rfl) ⟨825219, by rfl⟩ : syracuseStep 2200585 = 1650439) (by norm_num)
theorem B2934113 : Blo 1955435 2934113 := bstep (se 2 (by rfl) ⟨1100292, by rfl⟩ : syracuseStep 2934113 = 2200585) B2200585
theorem B1956075 : Blo 1955435 1956075 := bstep (se 1 (by rfl) ⟨1467056, by rfl⟩ : syracuseStep 1956075 = 2934113) B2934113
theorem B18799573 : Blo 1955435 18799573 := bbase (se 7 (by rfl) ⟨220307, by rfl⟩ : syracuseStep 18799573 = 440615) (by norm_num)
theorem B25066097 : Blo 1955435 25066097 := bstep (se 2 (by rfl) ⟨9399786, by rfl⟩ : syracuseStep 25066097 = 18799573) B18799573
theorem B16710731 : Blo 1955435 16710731 := bstep (se 1 (by rfl) ⟨12533048, by rfl⟩ : syracuseStep 16710731 = 25066097) B25066097
theorem B11140487 : Blo 1955435 11140487 := bstep (se 1 (by rfl) ⟨8355365, by rfl⟩ : syracuseStep 11140487 = 16710731) B16710731
theorem B7426991 : Blo 1955435 7426991 := bstep (se 1 (by rfl) ⟨5570243, by rfl⟩ : syracuseStep 7426991 = 11140487) B11140487
theorem B4951327 : Blo 1955435 4951327 := bstep (se 1 (by rfl) ⟨3713495, by rfl⟩ : syracuseStep 4951327 = 7426991) B7426991
theorem B6601769 : Blo 1955435 6601769 := bstep (se 2 (by rfl) ⟨2475663, by rfl⟩ : syracuseStep 6601769 = 4951327) B4951327
theorem B4401179 : Blo 1955435 4401179 := bstep (se 1 (by rfl) ⟨3300884, by rfl⟩ : syracuseStep 4401179 = 6601769) B6601769
theorem B2934119 : Blo 1955435 2934119 := bstep (se 1 (by rfl) ⟨2200589, by rfl⟩ : syracuseStep 2934119 = 4401179) B4401179
theorem B1956079 : Blo 1955435 1956079 := bstep (se 1 (by rfl) ⟨1467059, by rfl⟩ : syracuseStep 1956079 = 2934119) B2934119
theorem B2934125 : Blo 1955435 2934125 := bbase (se 3 (by rfl) ⟨550148, by rfl⟩ : syracuseStep 2934125 = 1100297) (by norm_num)
theorem B1956083 : Blo 1955435 1956083 := bstep (se 1 (by rfl) ⟨1467062, by rfl⟩ : syracuseStep 1956083 = 2934125) B2934125
theorem B4401197 : Blo 1955435 4401197 := bbase (se 3 (by rfl) ⟨825224, by rfl⟩ : syracuseStep 4401197 = 1650449) (by norm_num)
theorem B2934131 : Blo 1955435 2934131 := bstep (se 1 (by rfl) ⟨2200598, by rfl⟩ : syracuseStep 2934131 = 4401197) B4401197
theorem B1956087 : Blo 1955435 1956087 := bstep (se 1 (by rfl) ⟨1467065, by rfl⟩ : syracuseStep 1956087 = 2934131) B2934131
theorem B23793365 : Blo 1955435 23793365 := bbase (se 7 (by rfl) ⟨278828, by rfl⟩ : syracuseStep 23793365 = 557657) (by norm_num)
theorem B15862243 : Blo 1955435 15862243 := bstep (se 1 (by rfl) ⟨11896682, by rfl⟩ : syracuseStep 15862243 = 23793365) B23793365
theorem B21149657 : Blo 1955435 21149657 := bstep (se 2 (by rfl) ⟨7931121, by rfl⟩ : syracuseStep 21149657 = 15862243) B15862243
theorem B14099771 : Blo 1955435 14099771 := bstep (se 1 (by rfl) ⟨10574828, by rfl⟩ : syracuseStep 14099771 = 21149657) B21149657
theorem B9399847 : Blo 1955435 9399847 := bstep (se 1 (by rfl) ⟨7049885, by rfl⟩ : syracuseStep 9399847 = 14099771) B14099771
theorem B12533129 : Blo 1955435 12533129 := bstep (se 2 (by rfl) ⟨4699923, by rfl⟩ : syracuseStep 12533129 = 9399847) B9399847
theorem B8355419 : Blo 1955435 8355419 := bstep (se 1 (by rfl) ⟨6266564, by rfl⟩ : syracuseStep 8355419 = 12533129) B12533129
theorem B5570279 : Blo 1955435 5570279 := bstep (se 1 (by rfl) ⟨4177709, by rfl⟩ : syracuseStep 5570279 = 8355419) B8355419
theorem B3713519 : Blo 1955435 3713519 := bstep (se 1 (by rfl) ⟨2785139, by rfl⟩ : syracuseStep 3713519 = 5570279) B5570279
theorem B2475679 : Blo 1955435 2475679 := bstep (se 1 (by rfl) ⟨1856759, by rfl⟩ : syracuseStep 2475679 = 3713519) B3713519
theorem B3300905 : Blo 1955435 3300905 := bstep (se 2 (by rfl) ⟨1237839, by rfl⟩ : syracuseStep 3300905 = 2475679) B2475679
theorem B2200603 : Blo 1955435 2200603 := bstep (se 1 (by rfl) ⟨1650452, by rfl⟩ : syracuseStep 2200603 = 3300905) B3300905
theorem B2934137 : Blo 1955435 2934137 := bstep (se 2 (by rfl) ⟨1100301, by rfl⟩ : syracuseStep 2934137 = 2200603) B2200603
theorem B1956091 : Blo 1955435 1956091 := bstep (se 1 (by rfl) ⟨1467068, by rfl⟩ : syracuseStep 1956091 = 2934137) B2934137
theorem B4829053 : Blo 1955435 4829053 := bbase (se 3 (by rfl) ⟨905447, by rfl⟩ : syracuseStep 4829053 = 1810895) (by norm_num)
theorem B6438737 : Blo 1955435 6438737 := bstep (se 2 (by rfl) ⟨2414526, by rfl⟩ : syracuseStep 6438737 = 4829053) B4829053
theorem B17169965 : Blo 1955435 17169965 := bstep (se 3 (by rfl) ⟨3219368, by rfl⟩ : syracuseStep 17169965 = 6438737) B6438737
theorem B11446643 : Blo 1955435 11446643 := bstep (se 1 (by rfl) ⟨8584982, by rfl⟩ : syracuseStep 11446643 = 17169965) B17169965
theorem B30524381 : Blo 1955435 30524381 := bstep (se 3 (by rfl) ⟨5723321, by rfl⟩ : syracuseStep 30524381 = 11446643) B11446643
theorem B20349587 : Blo 1955435 20349587 := bstep (se 1 (by rfl) ⟨15262190, by rfl⟩ : syracuseStep 20349587 = 30524381) B30524381
theorem B54265565 : Blo 1955435 54265565 := bstep (se 3 (by rfl) ⟨10174793, by rfl⟩ : syracuseStep 54265565 = 20349587) B20349587
theorem B36177043 : Blo 1955435 36177043 := bstep (se 1 (by rfl) ⟨27132782, by rfl⟩ : syracuseStep 36177043 = 54265565) B54265565
theorem B48236057 : Blo 1955435 48236057 := bstep (se 2 (by rfl) ⟨18088521, by rfl⟩ : syracuseStep 48236057 = 36177043) B36177043
theorem B32157371 : Blo 1955435 32157371 := bstep (se 1 (by rfl) ⟨24118028, by rfl⟩ : syracuseStep 32157371 = 48236057) B48236057
theorem B85752989 : Blo 1955435 85752989 := bstep (se 3 (by rfl) ⟨16078685, by rfl⟩ : syracuseStep 85752989 = 32157371) B32157371
theorem B57168659 : Blo 1955435 57168659 := bstep (se 1 (by rfl) ⟨42876494, by rfl⟩ : syracuseStep 57168659 = 85752989) B85752989
theorem B38112439 : Blo 1955435 38112439 := bstep (se 1 (by rfl) ⟨28584329, by rfl⟩ : syracuseStep 38112439 = 57168659) B57168659
theorem B50816585 : Blo 1955435 50816585 := bstep (se 2 (by rfl) ⟨19056219, by rfl⟩ : syracuseStep 50816585 = 38112439) B38112439
theorem B135510893 : Blo 1955435 135510893 := bstep (se 3 (by rfl) ⟨25408292, by rfl⟩ : syracuseStep 135510893 = 50816585) B50816585
theorem B90340595 : Blo 1955435 90340595 := bstep (se 1 (by rfl) ⟨67755446, by rfl⟩ : syracuseStep 90340595 = 135510893) B135510893
theorem B60227063 : Blo 1955435 60227063 := bstep (se 1 (by rfl) ⟨45170297, by rfl⟩ : syracuseStep 60227063 = 90340595) B90340595
theorem B40151375 : Blo 1955435 40151375 := bstep (se 1 (by rfl) ⟨30113531, by rfl⟩ : syracuseStep 40151375 = 60227063) B60227063
theorem B26767583 : Blo 1955435 26767583 := bstep (se 1 (by rfl) ⟨20075687, by rfl⟩ : syracuseStep 26767583 = 40151375) B40151375
theorem B17845055 : Blo 1955435 17845055 := bstep (se 1 (by rfl) ⟨13383791, by rfl⟩ : syracuseStep 17845055 = 26767583) B26767583
theorem B11896703 : Blo 1955435 11896703 := bstep (se 1 (by rfl) ⟨8922527, by rfl⟩ : syracuseStep 11896703 = 17845055) B17845055
theorem B7931135 : Blo 1955435 7931135 := bstep (se 1 (by rfl) ⟨5948351, by rfl⟩ : syracuseStep 7931135 = 11896703) B11896703
theorem B21149693 : Blo 1955435 21149693 := bstep (se 3 (by rfl) ⟨3965567, by rfl⟩ : syracuseStep 21149693 = 7931135) B7931135
theorem B14099795 : Blo 1955435 14099795 := bstep (se 1 (by rfl) ⟨10574846, by rfl⟩ : syracuseStep 14099795 = 21149693) B21149693
theorem B9399863 : Blo 1955435 9399863 := bstep (se 1 (by rfl) ⟨7049897, by rfl⟩ : syracuseStep 9399863 = 14099795) B14099795
theorem B6266575 : Blo 1955435 6266575 := bstep (se 1 (by rfl) ⟨4699931, by rfl⟩ : syracuseStep 6266575 = 9399863) B9399863
theorem B33421733 : Blo 1955435 33421733 := bstep (se 4 (by rfl) ⟨3133287, by rfl⟩ : syracuseStep 33421733 = 6266575) B6266575
theorem B22281155 : Blo 1955435 22281155 := bstep (se 1 (by rfl) ⟨16710866, by rfl⟩ : syracuseStep 22281155 = 33421733) B33421733
theorem B14854103 : Blo 1955435 14854103 := bstep (se 1 (by rfl) ⟨11140577, by rfl⟩ : syracuseStep 14854103 = 22281155) B22281155
theorem B9902735 : Blo 1955435 9902735 := bstep (se 1 (by rfl) ⟨7427051, by rfl⟩ : syracuseStep 9902735 = 14854103) B14854103
theorem B6601823 : Blo 1955435 6601823 := bstep (se 1 (by rfl) ⟨4951367, by rfl⟩ : syracuseStep 6601823 = 9902735) B9902735
theorem B4401215 : Blo 1955435 4401215 := bstep (se 1 (by rfl) ⟨3300911, by rfl⟩ : syracuseStep 4401215 = 6601823) B6601823
theorem B2934143 : Blo 1955435 2934143 := bstep (se 1 (by rfl) ⟨2200607, by rfl⟩ : syracuseStep 2934143 = 4401215) B4401215
theorem B1956095 : Blo 1955435 1956095 := bstep (se 1 (by rfl) ⟨1467071, by rfl⟩ : syracuseStep 1956095 = 2934143) B2934143
theorem B2934149 : Blo 1955435 2934149 := bbase (se 4 (by rfl) ⟨275076, by rfl⟩ : syracuseStep 2934149 = 550153) (by norm_num)
theorem B1956099 : Blo 1955435 1956099 := bstep (se 1 (by rfl) ⟨1467074, by rfl⟩ : syracuseStep 1956099 = 2934149) B2934149
theorem B3300925 : Blo 1955435 3300925 := bbase (se 3 (by rfl) ⟨618923, by rfl⟩ : syracuseStep 3300925 = 1237847) (by norm_num)
theorem B4401233 : Blo 1955435 4401233 := bstep (se 2 (by rfl) ⟨1650462, by rfl⟩ : syracuseStep 4401233 = 3300925) B3300925
theorem B2934155 : Blo 1955435 2934155 := bstep (se 1 (by rfl) ⟨2200616, by rfl⟩ : syracuseStep 2934155 = 4401233) B4401233
theorem B1956103 : Blo 1955435 1956103 := bstep (se 1 (by rfl) ⟨1467077, by rfl⟩ : syracuseStep 1956103 = 2934155) B2934155
theorem B2200621 : Blo 1955435 2200621 := bbase (se 3 (by rfl) ⟨412616, by rfl⟩ : syracuseStep 2200621 = 825233) (by norm_num)
theorem B2934161 : Blo 1955435 2934161 := bstep (se 2 (by rfl) ⟨1100310, by rfl⟩ : syracuseStep 2934161 = 2200621) B2200621
theorem B1956107 : Blo 1955435 1956107 := bstep (se 1 (by rfl) ⟨1467080, by rfl⟩ : syracuseStep 1956107 = 2934161) B2934161
theorem B6601877 : Blo 1955435 6601877 := bbase (se 6 (by rfl) ⟨154731, by rfl⟩ : syracuseStep 6601877 = 309463) (by norm_num)
theorem B4401251 : Blo 1955435 4401251 := bstep (se 1 (by rfl) ⟨3300938, by rfl⟩ : syracuseStep 4401251 = 6601877) B6601877
theorem B2934167 : Blo 1955435 2934167 := bstep (se 1 (by rfl) ⟨2200625, by rfl⟩ : syracuseStep 2934167 = 4401251) B4401251
theorem B1956111 : Blo 1955435 1956111 := bstep (se 1 (by rfl) ⟨1467083, by rfl⟩ : syracuseStep 1956111 = 2934167) B2934167
theorem B2934173 : Blo 1955435 2934173 := bbase (se 3 (by rfl) ⟨550157, by rfl⟩ : syracuseStep 2934173 = 1100315) (by norm_num)
theorem B1956115 : Blo 1955435 1956115 := bstep (se 1 (by rfl) ⟨1467086, by rfl⟩ : syracuseStep 1956115 = 2934173) B2934173
theorem B4401269 : Blo 1955435 4401269 := bbase (se 5 (by rfl) ⟨206309, by rfl⟩ : syracuseStep 4401269 = 412619) (by norm_num)
theorem B2934179 : Blo 1955435 2934179 := bstep (se 1 (by rfl) ⟨2200634, by rfl⟩ : syracuseStep 2934179 = 4401269) B4401269
theorem B1956119 : Blo 1955435 1956119 := bstep (se 1 (by rfl) ⟨1467089, by rfl⟩ : syracuseStep 1956119 = 2934179) B2934179
theorem B3133333 : Blo 1955435 3133333 := bbase (se 6 (by rfl) ⟨73437, by rfl⟩ : syracuseStep 3133333 = 146875) (by norm_num)
theorem B16711109 : Blo 1955435 16711109 := bstep (se 4 (by rfl) ⟨1566666, by rfl⟩ : syracuseStep 16711109 = 3133333) B3133333
theorem B11140739 : Blo 1955435 11140739 := bstep (se 1 (by rfl) ⟨8355554, by rfl⟩ : syracuseStep 11140739 = 16711109) B16711109
theorem B7427159 : Blo 1955435 7427159 := bstep (se 1 (by rfl) ⟨5570369, by rfl⟩ : syracuseStep 7427159 = 11140739) B11140739
theorem B4951439 : Blo 1955435 4951439 := bstep (se 1 (by rfl) ⟨3713579, by rfl⟩ : syracuseStep 4951439 = 7427159) B7427159
theorem B3300959 : Blo 1955435 3300959 := bstep (se 1 (by rfl) ⟨2475719, by rfl⟩ : syracuseStep 3300959 = 4951439) B4951439
theorem B2200639 : Blo 1955435 2200639 := bstep (se 1 (by rfl) ⟨1650479, by rfl⟩ : syracuseStep 2200639 = 3300959) B3300959
theorem B2934185 : Blo 1955435 2934185 := bstep (se 2 (by rfl) ⟨1100319, by rfl⟩ : syracuseStep 2934185 = 2200639) B2200639
theorem B1956123 : Blo 1955435 1956123 := bstep (se 1 (by rfl) ⟨1467092, by rfl⟩ : syracuseStep 1956123 = 2934185) B2934185
theorem B7427173 : Blo 1955435 7427173 := bbase (se 4 (by rfl) ⟨696297, by rfl⟩ : syracuseStep 7427173 = 1392595) (by norm_num)
theorem B9902897 : Blo 1955435 9902897 := bstep (se 2 (by rfl) ⟨3713586, by rfl⟩ : syracuseStep 9902897 = 7427173) B7427173
theorem B6601931 : Blo 1955435 6601931 := bstep (se 1 (by rfl) ⟨4951448, by rfl⟩ : syracuseStep 6601931 = 9902897) B9902897
theorem B4401287 : Blo 1955435 4401287 := bstep (se 1 (by rfl) ⟨3300965, by rfl⟩ : syracuseStep 4401287 = 6601931) B6601931
theorem B2934191 : Blo 1955435 2934191 := bstep (se 1 (by rfl) ⟨2200643, by rfl⟩ : syracuseStep 2934191 = 4401287) B4401287
theorem B1956127 : Blo 1955435 1956127 := bstep (se 1 (by rfl) ⟨1467095, by rfl⟩ : syracuseStep 1956127 = 2934191) B2934191
theorem B2934197 : Blo 1955435 2934197 := bbase (se 5 (by rfl) ⟨137540, by rfl⟩ : syracuseStep 2934197 = 275081) (by norm_num)
theorem B1956131 : Blo 1955435 1956131 := bstep (se 1 (by rfl) ⟨1467098, by rfl⟩ : syracuseStep 1956131 = 2934197) B2934197
theorem B4951469 : Blo 1955435 4951469 := bbase (se 3 (by rfl) ⟨928400, by rfl⟩ : syracuseStep 4951469 = 1856801) (by norm_num)
theorem B3300979 : Blo 1955435 3300979 := bstep (se 1 (by rfl) ⟨2475734, by rfl⟩ : syracuseStep 3300979 = 4951469) B4951469
theorem B4401305 : Blo 1955435 4401305 := bstep (se 2 (by rfl) ⟨1650489, by rfl⟩ : syracuseStep 4401305 = 3300979) B3300979
theorem B2934203 : Blo 1955435 2934203 := bstep (se 1 (by rfl) ⟨2200652, by rfl⟩ : syracuseStep 2934203 = 4401305) B4401305
theorem B1956135 : Blo 1955435 1956135 := bstep (se 1 (by rfl) ⟨1467101, by rfl⟩ : syracuseStep 1956135 = 2934203) B2934203
theorem B2200657 : Blo 1955435 2200657 := bbase (se 2 (by rfl) ⟨825246, by rfl⟩ : syracuseStep 2200657 = 1650493) (by norm_num)
theorem B2934209 : Blo 1955435 2934209 := bstep (se 2 (by rfl) ⟨1100328, by rfl⟩ : syracuseStep 2934209 = 2200657) B2200657
theorem B1956139 : Blo 1955435 1956139 := bstep (se 1 (by rfl) ⟨1467104, by rfl⟩ : syracuseStep 1956139 = 2934209) B2934209
theorem B2785213 : Blo 1955435 2785213 := bbase (se 3 (by rfl) ⟨522227, by rfl⟩ : syracuseStep 2785213 = 1044455) (by norm_num)
theorem B3713617 : Blo 1955435 3713617 := bstep (se 2 (by rfl) ⟨1392606, by rfl⟩ : syracuseStep 3713617 = 2785213) B2785213
theorem B4951489 : Blo 1955435 4951489 := bstep (se 2 (by rfl) ⟨1856808, by rfl⟩ : syracuseStep 4951489 = 3713617) B3713617
theorem B6601985 : Blo 1955435 6601985 := bstep (se 2 (by rfl) ⟨2475744, by rfl⟩ : syracuseStep 6601985 = 4951489) B4951489
theorem B4401323 : Blo 1955435 4401323 := bstep (se 1 (by rfl) ⟨3300992, by rfl⟩ : syracuseStep 4401323 = 6601985) B6601985
theorem B2934215 : Blo 1955435 2934215 := bstep (se 1 (by rfl) ⟨2200661, by rfl⟩ : syracuseStep 2934215 = 4401323) B4401323
theorem B1956143 : Blo 1955435 1956143 := bstep (se 1 (by rfl) ⟨1467107, by rfl⟩ : syracuseStep 1956143 = 2934215) B2934215
theorem B2934221 : Blo 1955435 2934221 := bbase (se 3 (by rfl) ⟨550166, by rfl⟩ : syracuseStep 2934221 = 1100333) (by norm_num)
theorem B1956147 : Blo 1955435 1956147 := bstep (se 1 (by rfl) ⟨1467110, by rfl⟩ : syracuseStep 1956147 = 2934221) B2934221
theorem B4401341 : Blo 1955435 4401341 := bbase (se 3 (by rfl) ⟨825251, by rfl⟩ : syracuseStep 4401341 = 1650503) (by norm_num)
theorem B2934227 : Blo 1955435 2934227 := bstep (se 1 (by rfl) ⟨2200670, by rfl⟩ : syracuseStep 2934227 = 4401341) B4401341
theorem B1956151 : Blo 1955435 1956151 := bstep (se 1 (by rfl) ⟨1467113, by rfl⟩ : syracuseStep 1956151 = 2934227) B2934227
theorem B3301013 : Blo 1955435 3301013 := bbase (se 6 (by rfl) ⟨77367, by rfl⟩ : syracuseStep 3301013 = 154735) (by norm_num)
theorem B2200675 : Blo 1955435 2200675 := bstep (se 1 (by rfl) ⟨1650506, by rfl⟩ : syracuseStep 2200675 = 3301013) B3301013
theorem B2934233 : Blo 1955435 2934233 := bstep (se 2 (by rfl) ⟨1100337, by rfl⟩ : syracuseStep 2934233 = 2200675) B2200675
theorem B1956155 : Blo 1955435 1956155 := bstep (se 1 (by rfl) ⟨1467116, by rfl⟩ : syracuseStep 1956155 = 2934233) B2934233
theorem B2230705 : Blo 1955435 2230705 := bbase (se 2 (by rfl) ⟨836514, by rfl⟩ : syracuseStep 2230705 = 1673029) (by norm_num)
theorem B11897093 : Blo 1955435 11897093 := bstep (se 4 (by rfl) ⟨1115352, by rfl⟩ : syracuseStep 11897093 = 2230705) B2230705
theorem B7931395 : Blo 1955435 7931395 := bstep (se 1 (by rfl) ⟨5948546, by rfl⟩ : syracuseStep 7931395 = 11897093) B11897093
theorem B10575193 : Blo 1955435 10575193 := bstep (se 2 (by rfl) ⟨3965697, by rfl⟩ : syracuseStep 10575193 = 7931395) B7931395
theorem B14100257 : Blo 1955435 14100257 := bstep (se 2 (by rfl) ⟨5287596, by rfl⟩ : syracuseStep 14100257 = 10575193) B10575193
theorem B9400171 : Blo 1955435 9400171 := bstep (se 1 (by rfl) ⟨7050128, by rfl⟩ : syracuseStep 9400171 = 14100257) B14100257
theorem B12533561 : Blo 1955435 12533561 := bstep (se 2 (by rfl) ⟨4700085, by rfl⟩ : syracuseStep 12533561 = 9400171) B9400171
theorem B8355707 : Blo 1955435 8355707 := bstep (se 1 (by rfl) ⟨6266780, by rfl⟩ : syracuseStep 8355707 = 12533561) B12533561
theorem B5570471 : Blo 1955435 5570471 := bstep (se 1 (by rfl) ⟨4177853, by rfl⟩ : syracuseStep 5570471 = 8355707) B8355707
theorem B14854589 : Blo 1955435 14854589 := bstep (se 3 (by rfl) ⟨2785235, by rfl⟩ : syracuseStep 14854589 = 5570471) B5570471
theorem B9903059 : Blo 1955435 9903059 := bstep (se 1 (by rfl) ⟨7427294, by rfl⟩ : syracuseStep 9903059 = 14854589) B14854589
theorem B6602039 : Blo 1955435 6602039 := bstep (se 1 (by rfl) ⟨4951529, by rfl⟩ : syracuseStep 6602039 = 9903059) B9903059
theorem B4401359 : Blo 1955435 4401359 := bstep (se 1 (by rfl) ⟨3301019, by rfl⟩ : syracuseStep 4401359 = 6602039) B6602039
theorem B2934239 : Blo 1955435 2934239 := bstep (se 1 (by rfl) ⟨2200679, by rfl⟩ : syracuseStep 2934239 = 4401359) B4401359
theorem B1956159 : Blo 1955435 1956159 := bstep (se 1 (by rfl) ⟨1467119, by rfl⟩ : syracuseStep 1956159 = 2934239) B2934239
theorem B2934245 : Blo 1955435 2934245 := bbase (se 4 (by rfl) ⟨275085, by rfl⟩ : syracuseStep 2934245 = 550171) (by norm_num)
theorem B1956163 : Blo 1955435 1956163 := bstep (se 1 (by rfl) ⟨1467122, by rfl⟩ : syracuseStep 1956163 = 2934245) B2934245
theorem B9044597 : Blo 1955435 9044597 := bbase (se 5 (by rfl) ⟨423965, by rfl⟩ : syracuseStep 9044597 = 847931) (by norm_num)
theorem B6029731 : Blo 1955435 6029731 := bstep (se 1 (by rfl) ⟨4522298, by rfl⟩ : syracuseStep 6029731 = 9044597) B9044597
theorem B32158565 : Blo 1955435 32158565 := bstep (se 4 (by rfl) ⟨3014865, by rfl⟩ : syracuseStep 32158565 = 6029731) B6029731
theorem B21439043 : Blo 1955435 21439043 := bstep (se 1 (by rfl) ⟨16079282, by rfl⟩ : syracuseStep 21439043 = 32158565) B32158565
theorem B14292695 : Blo 1955435 14292695 := bstep (se 1 (by rfl) ⟨10719521, by rfl⟩ : syracuseStep 14292695 = 21439043) B21439043
theorem B9528463 : Blo 1955435 9528463 := bstep (se 1 (by rfl) ⟨7146347, by rfl⟩ : syracuseStep 9528463 = 14292695) B14292695
theorem B12704617 : Blo 1955435 12704617 := bstep (se 2 (by rfl) ⟨4764231, by rfl⟩ : syracuseStep 12704617 = 9528463) B9528463
theorem B16939489 : Blo 1955435 16939489 := bstep (se 2 (by rfl) ⟨6352308, by rfl⟩ : syracuseStep 16939489 = 12704617) B12704617
theorem B22585985 : Blo 1955435 22585985 := bstep (se 2 (by rfl) ⟨8469744, by rfl⟩ : syracuseStep 22585985 = 16939489) B16939489
theorem B15057323 : Blo 1955435 15057323 := bstep (se 1 (by rfl) ⟨11292992, by rfl⟩ : syracuseStep 15057323 = 22585985) B22585985
theorem B10038215 : Blo 1955435 10038215 := bstep (se 1 (by rfl) ⟨7528661, by rfl⟩ : syracuseStep 10038215 = 15057323) B15057323
theorem B26768573 : Blo 1955435 26768573 := bstep (se 3 (by rfl) ⟨5019107, by rfl⟩ : syracuseStep 26768573 = 10038215) B10038215
theorem B17845715 : Blo 1955435 17845715 := bstep (se 1 (by rfl) ⟨13384286, by rfl⟩ : syracuseStep 17845715 = 26768573) B26768573
theorem B47588573 : Blo 1955435 47588573 := bstep (se 3 (by rfl) ⟨8922857, by rfl⟩ : syracuseStep 47588573 = 17845715) B17845715
theorem B31725715 : Blo 1955435 31725715 := bstep (se 1 (by rfl) ⟨23794286, by rfl⟩ : syracuseStep 31725715 = 47588573) B47588573
theorem B42300953 : Blo 1955435 42300953 := bstep (se 2 (by rfl) ⟨15862857, by rfl⟩ : syracuseStep 42300953 = 31725715) B31725715
theorem B28200635 : Blo 1955435 28200635 := bstep (se 1 (by rfl) ⟨21150476, by rfl⟩ : syracuseStep 28200635 = 42300953) B42300953
theorem B18800423 : Blo 1955435 18800423 := bstep (se 1 (by rfl) ⟨14100317, by rfl⟩ : syracuseStep 18800423 = 28200635) B28200635
theorem B12533615 : Blo 1955435 12533615 := bstep (se 1 (by rfl) ⟨9400211, by rfl⟩ : syracuseStep 12533615 = 18800423) B18800423
theorem B8355743 : Blo 1955435 8355743 := bstep (se 1 (by rfl) ⟨6266807, by rfl⟩ : syracuseStep 8355743 = 12533615) B12533615
theorem B5570495 : Blo 1955435 5570495 := bstep (se 1 (by rfl) ⟨4177871, by rfl⟩ : syracuseStep 5570495 = 8355743) B8355743
theorem B3713663 : Blo 1955435 3713663 := bstep (se 1 (by rfl) ⟨2785247, by rfl⟩ : syracuseStep 3713663 = 5570495) B5570495
theorem B2475775 : Blo 1955435 2475775 := bstep (se 1 (by rfl) ⟨1856831, by rfl⟩ : syracuseStep 2475775 = 3713663) B3713663
theorem B3301033 : Blo 1955435 3301033 := bstep (se 2 (by rfl) ⟨1237887, by rfl⟩ : syracuseStep 3301033 = 2475775) B2475775
theorem B4401377 : Blo 1955435 4401377 := bstep (se 2 (by rfl) ⟨1650516, by rfl⟩ : syracuseStep 4401377 = 3301033) B3301033
theorem B2934251 : Blo 1955435 2934251 := bstep (se 1 (by rfl) ⟨2200688, by rfl⟩ : syracuseStep 2934251 = 4401377) B4401377
theorem B1956167 : Blo 1955435 1956167 := bstep (se 1 (by rfl) ⟨1467125, by rfl⟩ : syracuseStep 1956167 = 2934251) B2934251
theorem B2200693 : Blo 1955435 2200693 := bbase (se 5 (by rfl) ⟨103157, by rfl⟩ : syracuseStep 2200693 = 206315) (by norm_num)
theorem B2934257 : Blo 1955435 2934257 := bstep (se 2 (by rfl) ⟨1100346, by rfl⟩ : syracuseStep 2934257 = 2200693) B2200693
theorem B1956171 : Blo 1955435 1956171 := bstep (se 1 (by rfl) ⟨1467128, by rfl⟩ : syracuseStep 1956171 = 2934257) B2934257
theorem B2475785 : Blo 1955435 2475785 := bbase (se 2 (by rfl) ⟨928419, by rfl⟩ : syracuseStep 2475785 = 1856839) (by norm_num)
theorem B6602093 : Blo 1955435 6602093 := bstep (se 3 (by rfl) ⟨1237892, by rfl⟩ : syracuseStep 6602093 = 2475785) B2475785
theorem B4401395 : Blo 1955435 4401395 := bstep (se 1 (by rfl) ⟨3301046, by rfl⟩ : syracuseStep 4401395 = 6602093) B6602093
theorem B2934263 : Blo 1955435 2934263 := bstep (se 1 (by rfl) ⟨2200697, by rfl⟩ : syracuseStep 2934263 = 4401395) B4401395
theorem B1956175 : Blo 1955435 1956175 := bstep (se 1 (by rfl) ⟨1467131, by rfl⟩ : syracuseStep 1956175 = 2934263) B2934263
theorem B2934269 : Blo 1955435 2934269 := bbase (se 3 (by rfl) ⟨550175, by rfl⟩ : syracuseStep 2934269 = 1100351) (by norm_num)
theorem B1956179 : Blo 1955435 1956179 := bstep (se 1 (by rfl) ⟨1467134, by rfl⟩ : syracuseStep 1956179 = 2934269) B2934269
theorem B4401413 : Blo 1955435 4401413 := bbase (se 4 (by rfl) ⟨412632, by rfl⟩ : syracuseStep 4401413 = 825265) (by norm_num)
theorem B2934275 : Blo 1955435 2934275 := bstep (se 1 (by rfl) ⟨2200706, by rfl⟩ : syracuseStep 2934275 = 4401413) B4401413
theorem B1956183 : Blo 1955435 1956183 := bstep (se 1 (by rfl) ⟨1467137, by rfl⟩ : syracuseStep 1956183 = 2934275) B2934275
theorem B3713701 : Blo 1955435 3713701 := bbase (se 4 (by rfl) ⟨348159, by rfl⟩ : syracuseStep 3713701 = 696319) (by norm_num)
theorem B4951601 : Blo 1955435 4951601 := bstep (se 2 (by rfl) ⟨1856850, by rfl⟩ : syracuseStep 4951601 = 3713701) B3713701
theorem B3301067 : Blo 1955435 3301067 := bstep (se 1 (by rfl) ⟨2475800, by rfl⟩ : syracuseStep 3301067 = 4951601) B4951601
theorem B2200711 : Blo 1955435 2200711 := bstep (se 1 (by rfl) ⟨1650533, by rfl⟩ : syracuseStep 2200711 = 3301067) B3301067
theorem B2934281 : Blo 1955435 2934281 := bstep (se 2 (by rfl) ⟨1100355, by rfl⟩ : syracuseStep 2934281 = 2200711) B2200711
theorem B1956187 : Blo 1955435 1956187 := bstep (se 1 (by rfl) ⟨1467140, by rfl⟩ : syracuseStep 1956187 = 2934281) B2934281
theorem B9903221 : Blo 1955435 9903221 := bbase (se 5 (by rfl) ⟨464213, by rfl⟩ : syracuseStep 9903221 = 928427) (by norm_num)
theorem B6602147 : Blo 1955435 6602147 := bstep (se 1 (by rfl) ⟨4951610, by rfl⟩ : syracuseStep 6602147 = 9903221) B9903221
theorem B4401431 : Blo 1955435 4401431 := bstep (se 1 (by rfl) ⟨3301073, by rfl⟩ : syracuseStep 4401431 = 6602147) B6602147
theorem B2934287 : Blo 1955435 2934287 := bstep (se 1 (by rfl) ⟨2200715, by rfl⟩ : syracuseStep 2934287 = 4401431) B4401431
theorem B1956191 : Blo 1955435 1956191 := bstep (se 1 (by rfl) ⟨1467143, by rfl⟩ : syracuseStep 1956191 = 2934287) B2934287
theorem B2934293 : Blo 1955435 2934293 := bbase (se 6 (by rfl) ⟨68772, by rfl⟩ : syracuseStep 2934293 = 137545) (by norm_num)
theorem B1956195 : Blo 1955435 1956195 := bstep (se 1 (by rfl) ⟨1467146, by rfl⟩ : syracuseStep 1956195 = 2934293) B2934293
theorem B2643853 : Blo 1955435 2643853 := bbase (se 3 (by rfl) ⟨495722, by rfl⟩ : syracuseStep 2643853 = 991445) (by norm_num)
theorem B3525137 : Blo 1955435 3525137 := bstep (se 2 (by rfl) ⟨1321926, by rfl⟩ : syracuseStep 3525137 = 2643853) B2643853
theorem B2350091 : Blo 1955435 2350091 := bstep (se 1 (by rfl) ⟨1762568, by rfl⟩ : syracuseStep 2350091 = 3525137) B3525137
theorem B6266909 : Blo 1955435 6266909 := bstep (se 3 (by rfl) ⟨1175045, by rfl⟩ : syracuseStep 6266909 = 2350091) B2350091
theorem B16711757 : Blo 1955435 16711757 := bstep (se 3 (by rfl) ⟨3133454, by rfl⟩ : syracuseStep 16711757 = 6266909) B6266909
theorem B11141171 : Blo 1955435 11141171 := bstep (se 1 (by rfl) ⟨8355878, by rfl⟩ : syracuseStep 11141171 = 16711757) B16711757
theorem B7427447 : Blo 1955435 7427447 := bstep (se 1 (by rfl) ⟨5570585, by rfl⟩ : syracuseStep 7427447 = 11141171) B11141171
theorem B4951631 : Blo 1955435 4951631 := bstep (se 1 (by rfl) ⟨3713723, by rfl⟩ : syracuseStep 4951631 = 7427447) B7427447
theorem B3301087 : Blo 1955435 3301087 := bstep (se 1 (by rfl) ⟨2475815, by rfl⟩ : syracuseStep 3301087 = 4951631) B4951631
theorem B4401449 : Blo 1955435 4401449 := bstep (se 2 (by rfl) ⟨1650543, by rfl⟩ : syracuseStep 4401449 = 3301087) B3301087
theorem B2934299 : Blo 1955435 2934299 := bstep (se 1 (by rfl) ⟨2200724, by rfl⟩ : syracuseStep 2934299 = 4401449) B4401449
theorem B1956199 : Blo 1955435 1956199 := bstep (se 1 (by rfl) ⟨1467149, by rfl⟩ : syracuseStep 1956199 = 2934299) B2934299
theorem B2200729 : Blo 1955435 2200729 := bbase (se 2 (by rfl) ⟨825273, by rfl⟩ : syracuseStep 2200729 = 1650547) (by norm_num)
theorem B2934305 : Blo 1955435 2934305 := bstep (se 2 (by rfl) ⟨1100364, by rfl⟩ : syracuseStep 2934305 = 2200729) B2200729
theorem B1956203 : Blo 1955435 1956203 := bstep (se 1 (by rfl) ⟨1467152, by rfl⟩ : syracuseStep 1956203 = 2934305) B2934305
theorem B7427477 : Blo 1955435 7427477 := bbase (se 6 (by rfl) ⟨174081, by rfl⟩ : syracuseStep 7427477 = 348163) (by norm_num)
theorem B4951651 : Blo 1955435 4951651 := bstep (se 1 (by rfl) ⟨3713738, by rfl⟩ : syracuseStep 4951651 = 7427477) B7427477
theorem B6602201 : Blo 1955435 6602201 := bstep (se 2 (by rfl) ⟨2475825, by rfl⟩ : syracuseStep 6602201 = 4951651) B4951651
theorem B4401467 : Blo 1955435 4401467 := bstep (se 1 (by rfl) ⟨3301100, by rfl⟩ : syracuseStep 4401467 = 6602201) B6602201
theorem B2934311 : Blo 1955435 2934311 := bstep (se 1 (by rfl) ⟨2200733, by rfl⟩ : syracuseStep 2934311 = 4401467) B4401467
theorem B1956207 : Blo 1955435 1956207 := bstep (se 1 (by rfl) ⟨1467155, by rfl⟩ : syracuseStep 1956207 = 2934311) B2934311
theorem B2934317 : Blo 1955435 2934317 := bbase (se 3 (by rfl) ⟨550184, by rfl⟩ : syracuseStep 2934317 = 1100369) (by norm_num)
theorem B1956211 : Blo 1955435 1956211 := bstep (se 1 (by rfl) ⟨1467158, by rfl⟩ : syracuseStep 1956211 = 2934317) B2934317
theorem B4401485 : Blo 1955435 4401485 := bbase (se 3 (by rfl) ⟨825278, by rfl⟩ : syracuseStep 4401485 = 1650557) (by norm_num)
theorem B2934323 : Blo 1955435 2934323 := bstep (se 1 (by rfl) ⟨2200742, by rfl⟩ : syracuseStep 2934323 = 4401485) B4401485
theorem B1956215 : Blo 1955435 1956215 := bstep (se 1 (by rfl) ⟨1467161, by rfl⟩ : syracuseStep 1956215 = 2934323) B2934323
theorem B2475841 : Blo 1955435 2475841 := bbase (se 2 (by rfl) ⟨928440, by rfl⟩ : syracuseStep 2475841 = 1856881) (by norm_num)
theorem B3301121 : Blo 1955435 3301121 := bstep (se 2 (by rfl) ⟨1237920, by rfl⟩ : syracuseStep 3301121 = 2475841) B2475841
theorem B2200747 : Blo 1955435 2200747 := bstep (se 1 (by rfl) ⟨1650560, by rfl⟩ : syracuseStep 2200747 = 3301121) B3301121
theorem B2934329 : Blo 1955435 2934329 := bstep (se 2 (by rfl) ⟨1100373, by rfl⟩ : syracuseStep 2934329 = 2200747) B2200747
theorem B1956219 : Blo 1955435 1956219 := bstep (se 1 (by rfl) ⟨1467164, by rfl⟩ : syracuseStep 1956219 = 2934329) B2934329
theorem B3133493 : Blo 1955435 3133493 := bbase (se 5 (by rfl) ⟨146882, by rfl⟩ : syracuseStep 3133493 = 293765) (by norm_num)
theorem B2088995 : Blo 1955435 2088995 := bstep (se 1 (by rfl) ⟨1566746, by rfl⟩ : syracuseStep 2088995 = 3133493) B3133493
theorem B22282613 : Blo 1955435 22282613 := bstep (se 5 (by rfl) ⟨1044497, by rfl⟩ : syracuseStep 22282613 = 2088995) B2088995
theorem B14855075 : Blo 1955435 14855075 := bstep (se 1 (by rfl) ⟨11141306, by rfl⟩ : syracuseStep 14855075 = 22282613) B22282613
theorem B9903383 : Blo 1955435 9903383 := bstep (se 1 (by rfl) ⟨7427537, by rfl⟩ : syracuseStep 9903383 = 14855075) B14855075
theorem B6602255 : Blo 1955435 6602255 := bstep (se 1 (by rfl) ⟨4951691, by rfl⟩ : syracuseStep 6602255 = 9903383) B9903383
theorem B4401503 : Blo 1955435 4401503 := bstep (se 1 (by rfl) ⟨3301127, by rfl⟩ : syracuseStep 4401503 = 6602255) B6602255
theorem B2934335 : Blo 1955435 2934335 := bstep (se 1 (by rfl) ⟨2200751, by rfl⟩ : syracuseStep 2934335 = 4401503) B4401503
theorem B1956223 : Blo 1955435 1956223 := bstep (se 1 (by rfl) ⟨1467167, by rfl⟩ : syracuseStep 1956223 = 2934335) B2934335
theorem B2934341 : Blo 1955435 2934341 := bbase (se 4 (by rfl) ⟨275094, by rfl⟩ : syracuseStep 2934341 = 550189) (by norm_num)
theorem B1956227 : Blo 1955435 1956227 := bstep (se 1 (by rfl) ⟨1467170, by rfl⟩ : syracuseStep 1956227 = 2934341) B2934341
theorem B3301141 : Blo 1955435 3301141 := bbase (se 6 (by rfl) ⟨77370, by rfl⟩ : syracuseStep 3301141 = 154741) (by norm_num)
theorem B4401521 : Blo 1955435 4401521 := bstep (se 2 (by rfl) ⟨1650570, by rfl⟩ : syracuseStep 4401521 = 3301141) B3301141
theorem B2934347 : Blo 1955435 2934347 := bstep (se 1 (by rfl) ⟨2200760, by rfl⟩ : syracuseStep 2934347 = 4401521) B4401521
theorem B1956231 : Blo 1955435 1956231 := bstep (se 1 (by rfl) ⟨1467173, by rfl⟩ : syracuseStep 1956231 = 2934347) B2934347
theorem B2200765 : Blo 1955435 2200765 := bbase (se 3 (by rfl) ⟨412643, by rfl⟩ : syracuseStep 2200765 = 825287) (by norm_num)
theorem B2934353 : Blo 1955435 2934353 := bstep (se 2 (by rfl) ⟨1100382, by rfl⟩ : syracuseStep 2934353 = 2200765) B2200765
theorem B1956235 : Blo 1955435 1956235 := bstep (se 1 (by rfl) ⟨1467176, by rfl⟩ : syracuseStep 1956235 = 2934353) B2934353
theorem B6602309 : Blo 1955435 6602309 := bbase (se 4 (by rfl) ⟨618966, by rfl⟩ : syracuseStep 6602309 = 1237933) (by norm_num)
theorem B4401539 : Blo 1955435 4401539 := bstep (se 1 (by rfl) ⟨3301154, by rfl⟩ : syracuseStep 4401539 = 6602309) B6602309
theorem B2934359 : Blo 1955435 2934359 := bstep (se 1 (by rfl) ⟨2200769, by rfl⟩ : syracuseStep 2934359 = 4401539) B4401539
theorem B1956239 : Blo 1955435 1956239 := bstep (se 1 (by rfl) ⟨1467179, by rfl⟩ : syracuseStep 1956239 = 2934359) B2934359
theorem B2934365 : Blo 1955435 2934365 := bbase (se 3 (by rfl) ⟨550193, by rfl⟩ : syracuseStep 2934365 = 1100387) (by norm_num)
theorem B1956243 : Blo 1955435 1956243 := bstep (se 1 (by rfl) ⟨1467182, by rfl⟩ : syracuseStep 1956243 = 2934365) B2934365
theorem B4401557 : Blo 1955435 4401557 := bbase (se 6 (by rfl) ⟨103161, by rfl⟩ : syracuseStep 4401557 = 206323) (by norm_num)
theorem B2934371 : Blo 1955435 2934371 := bstep (se 1 (by rfl) ⟨2200778, by rfl⟩ : syracuseStep 2934371 = 4401557) B4401557
theorem B1956247 : Blo 1955435 1956247 := bstep (se 1 (by rfl) ⟨1467185, by rfl⟩ : syracuseStep 1956247 = 2934371) B2934371
theorem B6267077 : Blo 1955435 6267077 := bbase (se 4 (by rfl) ⟨587538, by rfl⟩ : syracuseStep 6267077 = 1175077) (by norm_num)
theorem B4178051 : Blo 1955435 4178051 := bstep (se 1 (by rfl) ⟨3133538, by rfl⟩ : syracuseStep 4178051 = 6267077) B6267077
theorem B2785367 : Blo 1955435 2785367 := bstep (se 1 (by rfl) ⟨2089025, by rfl⟩ : syracuseStep 2785367 = 4178051) B4178051
theorem B7427645 : Blo 1955435 7427645 := bstep (se 3 (by rfl) ⟨1392683, by rfl⟩ : syracuseStep 7427645 = 2785367) B2785367
theorem B4951763 : Blo 1955435 4951763 := bstep (se 1 (by rfl) ⟨3713822, by rfl⟩ : syracuseStep 4951763 = 7427645) B7427645
theorem B3301175 : Blo 1955435 3301175 := bstep (se 1 (by rfl) ⟨2475881, by rfl⟩ : syracuseStep 3301175 = 4951763) B4951763
theorem B2200783 : Blo 1955435 2200783 := bstep (se 1 (by rfl) ⟨1650587, by rfl⟩ : syracuseStep 2200783 = 3301175) B3301175
theorem B2934377 : Blo 1955435 2934377 := bstep (se 2 (by rfl) ⟨1100391, by rfl⟩ : syracuseStep 2934377 = 2200783) B2200783
theorem B1956251 : Blo 1955435 1956251 := bstep (se 1 (by rfl) ⟨1467188, by rfl⟩ : syracuseStep 1956251 = 2934377) B2934377
theorem B8356117 : Blo 1955435 8356117 := bbase (se 6 (by rfl) ⟨195846, by rfl⟩ : syracuseStep 8356117 = 391693) (by norm_num)
theorem B11141489 : Blo 1955435 11141489 := bstep (se 2 (by rfl) ⟨4178058, by rfl⟩ : syracuseStep 11141489 = 8356117) B8356117
theorem B7427659 : Blo 1955435 7427659 := bstep (se 1 (by rfl) ⟨5570744, by rfl⟩ : syracuseStep 7427659 = 11141489) B11141489
theorem B9903545 : Blo 1955435 9903545 := bstep (se 2 (by rfl) ⟨3713829, by rfl⟩ : syracuseStep 9903545 = 7427659) B7427659
theorem B6602363 : Blo 1955435 6602363 := bstep (se 1 (by rfl) ⟨4951772, by rfl⟩ : syracuseStep 6602363 = 9903545) B9903545
theorem B4401575 : Blo 1955435 4401575 := bstep (se 1 (by rfl) ⟨3301181, by rfl⟩ : syracuseStep 4401575 = 6602363) B6602363
theorem B2934383 : Blo 1955435 2934383 := bstep (se 1 (by rfl) ⟨2200787, by rfl⟩ : syracuseStep 2934383 = 4401575) B4401575
theorem B1956255 : Blo 1955435 1956255 := bstep (se 1 (by rfl) ⟨1467191, by rfl⟩ : syracuseStep 1956255 = 2934383) B2934383
theorem B2934389 : Blo 1955435 2934389 := bbase (se 5 (by rfl) ⟨137549, by rfl⟩ : syracuseStep 2934389 = 275099) (by norm_num)
theorem B1956259 : Blo 1955435 1956259 := bstep (se 1 (by rfl) ⟨1467194, by rfl⟩ : syracuseStep 1956259 = 2934389) B2934389
theorem B3713845 : Blo 1955435 3713845 := bbase (se 5 (by rfl) ⟨174086, by rfl⟩ : syracuseStep 3713845 = 348173) (by norm_num)
theorem B4951793 : Blo 1955435 4951793 := bstep (se 2 (by rfl) ⟨1856922, by rfl⟩ : syracuseStep 4951793 = 3713845) B3713845
theorem B3301195 : Blo 1955435 3301195 := bstep (se 1 (by rfl) ⟨2475896, by rfl⟩ : syracuseStep 3301195 = 4951793) B4951793
theorem B4401593 : Blo 1955435 4401593 := bstep (se 2 (by rfl) ⟨1650597, by rfl⟩ : syracuseStep 4401593 = 3301195) B3301195
theorem B2934395 : Blo 1955435 2934395 := bstep (se 1 (by rfl) ⟨2200796, by rfl⟩ : syracuseStep 2934395 = 4401593) B4401593
theorem B1956263 : Blo 1955435 1956263 := bstep (se 1 (by rfl) ⟨1467197, by rfl⟩ : syracuseStep 1956263 = 2934395) B2934395
theorem B2200801 : Blo 1955435 2200801 := bbase (se 2 (by rfl) ⟨825300, by rfl⟩ : syracuseStep 2200801 = 1650601) (by norm_num)
theorem B2934401 : Blo 1955435 2934401 := bstep (se 2 (by rfl) ⟨1100400, by rfl⟩ : syracuseStep 2934401 = 2200801) B2200801
theorem B1956267 : Blo 1955435 1956267 := bstep (se 1 (by rfl) ⟨1467200, by rfl⟩ : syracuseStep 1956267 = 2934401) B2934401
theorem B4951813 : Blo 1955435 4951813 := bbase (se 4 (by rfl) ⟨464232, by rfl⟩ : syracuseStep 4951813 = 928465) (by norm_num)
theorem B6602417 : Blo 1955435 6602417 := bstep (se 2 (by rfl) ⟨2475906, by rfl⟩ : syracuseStep 6602417 = 4951813) B4951813
theorem B4401611 : Blo 1955435 4401611 := bstep (se 1 (by rfl) ⟨3301208, by rfl⟩ : syracuseStep 4401611 = 6602417) B6602417
theorem B2934407 : Blo 1955435 2934407 := bstep (se 1 (by rfl) ⟨2200805, by rfl⟩ : syracuseStep 2934407 = 4401611) B4401611
theorem B1956271 : Blo 1955435 1956271 := bstep (se 1 (by rfl) ⟨1467203, by rfl⟩ : syracuseStep 1956271 = 2934407) B2934407
theorem B2934413 : Blo 1955435 2934413 := bbase (se 3 (by rfl) ⟨550202, by rfl⟩ : syracuseStep 2934413 = 1100405) (by norm_num)
theorem B1956275 : Blo 1955435 1956275 := bstep (se 1 (by rfl) ⟨1467206, by rfl⟩ : syracuseStep 1956275 = 2934413) B2934413
theorem B4401629 : Blo 1955435 4401629 := bbase (se 3 (by rfl) ⟨825305, by rfl⟩ : syracuseStep 4401629 = 1650611) (by norm_num)
theorem B2934419 : Blo 1955435 2934419 := bstep (se 1 (by rfl) ⟨2200814, by rfl⟩ : syracuseStep 2934419 = 4401629) B4401629
theorem B1956279 : Blo 1955435 1956279 := bstep (se 1 (by rfl) ⟨1467209, by rfl⟩ : syracuseStep 1956279 = 2934419) B2934419
theorem B3301229 : Blo 1955435 3301229 := bbase (se 3 (by rfl) ⟨618980, by rfl⟩ : syracuseStep 3301229 = 1237961) (by norm_num)
theorem B2200819 : Blo 1955435 2200819 := bstep (se 1 (by rfl) ⟨1650614, by rfl⟩ : syracuseStep 2200819 = 3301229) B3301229
theorem B2934425 : Blo 1955435 2934425 := bstep (se 2 (by rfl) ⟨1100409, by rfl⟩ : syracuseStep 2934425 = 2200819) B2200819
theorem B1956283 : Blo 1955435 1956283 := bstep (se 1 (by rfl) ⟨1467212, by rfl⟩ : syracuseStep 1956283 = 2934425) B2934425
theorem B3965957 : Blo 1955435 3965957 := bbase (se 4 (by rfl) ⟨371808, by rfl⟩ : syracuseStep 3965957 = 743617) (by norm_num)
theorem B2643971 : Blo 1955435 2643971 := bstep (se 1 (by rfl) ⟨1982978, by rfl⟩ : syracuseStep 2643971 = 3965957) B3965957
theorem B28202357 : Blo 1955435 28202357 := bstep (se 5 (by rfl) ⟨1321985, by rfl⟩ : syracuseStep 28202357 = 2643971) B2643971
theorem B18801571 : Blo 1955435 18801571 := bstep (se 1 (by rfl) ⟨14101178, by rfl⟩ : syracuseStep 18801571 = 28202357) B28202357
theorem B25068761 : Blo 1955435 25068761 := bstep (se 2 (by rfl) ⟨9400785, by rfl⟩ : syracuseStep 25068761 = 18801571) B18801571
theorem B16712507 : Blo 1955435 16712507 := bstep (se 1 (by rfl) ⟨12534380, by rfl⟩ : syracuseStep 16712507 = 25068761) B25068761
theorem B11141671 : Blo 1955435 11141671 := bstep (se 1 (by rfl) ⟨8356253, by rfl⟩ : syracuseStep 11141671 = 16712507) B16712507
theorem B14855561 : Blo 1955435 14855561 := bstep (se 2 (by rfl) ⟨5570835, by rfl⟩ : syracuseStep 14855561 = 11141671) B11141671
theorem B9903707 : Blo 1955435 9903707 := bstep (se 1 (by rfl) ⟨7427780, by rfl⟩ : syracuseStep 9903707 = 14855561) B14855561
theorem B6602471 : Blo 1955435 6602471 := bstep (se 1 (by rfl) ⟨4951853, by rfl⟩ : syracuseStep 6602471 = 9903707) B9903707
theorem B4401647 : Blo 1955435 4401647 := bstep (se 1 (by rfl) ⟨3301235, by rfl⟩ : syracuseStep 4401647 = 6602471) B6602471
theorem B2934431 : Blo 1955435 2934431 := bstep (se 1 (by rfl) ⟨2200823, by rfl⟩ : syracuseStep 2934431 = 4401647) B4401647
theorem B1956287 : Blo 1955435 1956287 := bstep (se 1 (by rfl) ⟨1467215, by rfl⟩ : syracuseStep 1956287 = 2934431) B2934431
theorem B2934437 : Blo 1955435 2934437 := bbase (se 4 (by rfl) ⟨275103, by rfl⟩ : syracuseStep 2934437 = 550207) (by norm_num)
theorem B1956291 : Blo 1955435 1956291 := bstep (se 1 (by rfl) ⟨1467218, by rfl⟩ : syracuseStep 1956291 = 2934437) B2934437
theorem B2475937 : Blo 1955435 2475937 := bbase (se 2 (by rfl) ⟨928476, by rfl⟩ : syracuseStep 2475937 = 1856953) (by norm_num)
theorem B3301249 : Blo 1955435 3301249 := bstep (se 2 (by rfl) ⟨1237968, by rfl⟩ : syracuseStep 3301249 = 2475937) B2475937
theorem B4401665 : Blo 1955435 4401665 := bstep (se 2 (by rfl) ⟨1650624, by rfl⟩ : syracuseStep 4401665 = 3301249) B3301249
theorem B2934443 : Blo 1955435 2934443 := bstep (se 1 (by rfl) ⟨2200832, by rfl⟩ : syracuseStep 2934443 = 4401665) B4401665
theorem B1956295 : Blo 1955435 1956295 := bstep (se 1 (by rfl) ⟨1467221, by rfl⟩ : syracuseStep 1956295 = 2934443) B2934443
theorem B2200837 : Blo 1955435 2200837 := bbase (se 4 (by rfl) ⟨206328, by rfl⟩ : syracuseStep 2200837 = 412657) (by norm_num)
theorem B2934449 : Blo 1955435 2934449 := bstep (se 2 (by rfl) ⟨1100418, by rfl⟩ : syracuseStep 2934449 = 2200837) B2200837
theorem B1956299 : Blo 1955435 1956299 := bstep (se 1 (by rfl) ⟨1467224, by rfl⟩ : syracuseStep 1956299 = 2934449) B2934449
theorem B2089081 : Blo 1955435 2089081 := bbase (se 2 (by rfl) ⟨783405, by rfl⟩ : syracuseStep 2089081 = 1566811) (by norm_num)
theorem B2785441 : Blo 1955435 2785441 := bstep (se 2 (by rfl) ⟨1044540, by rfl⟩ : syracuseStep 2785441 = 2089081) B2089081
theorem B3713921 : Blo 1955435 3713921 := bstep (se 2 (by rfl) ⟨1392720, by rfl⟩ : syracuseStep 3713921 = 2785441) B2785441
theorem B2475947 : Blo 1955435 2475947 := bstep (se 1 (by rfl) ⟨1856960, by rfl⟩ : syracuseStep 2475947 = 3713921) B3713921
theorem B6602525 : Blo 1955435 6602525 := bstep (se 3 (by rfl) ⟨1237973, by rfl⟩ : syracuseStep 6602525 = 2475947) B2475947
theorem B4401683 : Blo 1955435 4401683 := bstep (se 1 (by rfl) ⟨3301262, by rfl⟩ : syracuseStep 4401683 = 6602525) B6602525
theorem B2934455 : Blo 1955435 2934455 := bstep (se 1 (by rfl) ⟨2200841, by rfl⟩ : syracuseStep 2934455 = 4401683) B4401683
theorem B1956303 : Blo 1955435 1956303 := bstep (se 1 (by rfl) ⟨1467227, by rfl⟩ : syracuseStep 1956303 = 2934455) B2934455
theorem B2934461 : Blo 1955435 2934461 := bbase (se 3 (by rfl) ⟨550211, by rfl⟩ : syracuseStep 2934461 = 1100423) (by norm_num)
theorem B1956307 : Blo 1955435 1956307 := bstep (se 1 (by rfl) ⟨1467230, by rfl⟩ : syracuseStep 1956307 = 2934461) B2934461
theorem B4401701 : Blo 1955435 4401701 := bbase (se 4 (by rfl) ⟨412659, by rfl⟩ : syracuseStep 4401701 = 825319) (by norm_num)
theorem B2934467 : Blo 1955435 2934467 := bstep (se 1 (by rfl) ⟨2200850, by rfl⟩ : syracuseStep 2934467 = 4401701) B4401701
theorem B1956311 : Blo 1955435 1956311 := bstep (se 1 (by rfl) ⟨1467233, by rfl⟩ : syracuseStep 1956311 = 2934467) B2934467
theorem B4951925 : Blo 1955435 4951925 := bbase (se 5 (by rfl) ⟨232121, by rfl⟩ : syracuseStep 4951925 = 464243) (by norm_num)
theorem B3301283 : Blo 1955435 3301283 := bstep (se 1 (by rfl) ⟨2475962, by rfl⟩ : syracuseStep 3301283 = 4951925) B4951925
theorem B2200855 : Blo 1955435 2200855 := bstep (se 1 (by rfl) ⟨1650641, by rfl⟩ : syracuseStep 2200855 = 3301283) B3301283
theorem B2934473 : Blo 1955435 2934473 := bstep (se 2 (by rfl) ⟨1100427, by rfl⟩ : syracuseStep 2934473 = 2200855) B2200855
theorem B1956315 : Blo 1955435 1956315 := bstep (se 1 (by rfl) ⟨1467236, by rfl⟩ : syracuseStep 1956315 = 2934473) B2934473
theorem B2974517 : Blo 1955435 2974517 := bbase (se 5 (by rfl) ⟨139430, by rfl⟩ : syracuseStep 2974517 = 278861) (by norm_num)
theorem B1983011 : Blo 1955435 1983011 := bstep (se 1 (by rfl) ⟨1487258, by rfl⟩ : syracuseStep 1983011 = 2974517) B2974517
theorem B21152117 : Blo 1955435 21152117 := bstep (se 5 (by rfl) ⟨991505, by rfl⟩ : syracuseStep 21152117 = 1983011) B1983011
theorem B14101411 : Blo 1955435 14101411 := bstep (se 1 (by rfl) ⟨10576058, by rfl⟩ : syracuseStep 14101411 = 21152117) B21152117
theorem B18801881 : Blo 1955435 18801881 := bstep (se 2 (by rfl) ⟨7050705, by rfl⟩ : syracuseStep 18801881 = 14101411) B14101411
theorem B12534587 : Blo 1955435 12534587 := bstep (se 1 (by rfl) ⟨9400940, by rfl⟩ : syracuseStep 12534587 = 18801881) B18801881
theorem B8356391 : Blo 1955435 8356391 := bstep (se 1 (by rfl) ⟨6267293, by rfl⟩ : syracuseStep 8356391 = 12534587) B12534587
theorem B5570927 : Blo 1955435 5570927 := bstep (se 1 (by rfl) ⟨4178195, by rfl⟩ : syracuseStep 5570927 = 8356391) B8356391
theorem B3713951 : Blo 1955435 3713951 := bstep (se 1 (by rfl) ⟨2785463, by rfl⟩ : syracuseStep 3713951 = 5570927) B5570927
theorem B9903869 : Blo 1955435 9903869 := bstep (se 3 (by rfl) ⟨1856975, by rfl⟩ : syracuseStep 9903869 = 3713951) B3713951
theorem B6602579 : Blo 1955435 6602579 := bstep (se 1 (by rfl) ⟨4951934, by rfl⟩ : syracuseStep 6602579 = 9903869) B9903869
theorem B4401719 : Blo 1955435 4401719 := bstep (se 1 (by rfl) ⟨3301289, by rfl⟩ : syracuseStep 4401719 = 6602579) B6602579
theorem B2934479 : Blo 1955435 2934479 := bstep (se 1 (by rfl) ⟨2200859, by rfl⟩ : syracuseStep 2934479 = 4401719) B4401719
theorem B1956319 : Blo 1955435 1956319 := bstep (se 1 (by rfl) ⟨1467239, by rfl⟩ : syracuseStep 1956319 = 2934479) B2934479
theorem B2934485 : Blo 1955435 2934485 := bbase (se 7 (by rfl) ⟨34388, by rfl⟩ : syracuseStep 2934485 = 68777) (by norm_num)
theorem B1956323 : Blo 1955435 1956323 := bstep (se 1 (by rfl) ⟨1467242, by rfl⟩ : syracuseStep 1956323 = 2934485) B2934485
theorem B4178213 : Blo 1955435 4178213 := bbase (se 4 (by rfl) ⟨391707, by rfl⟩ : syracuseStep 4178213 = 783415) (by norm_num)
theorem B2785475 : Blo 1955435 2785475 := bstep (se 1 (by rfl) ⟨2089106, by rfl⟩ : syracuseStep 2785475 = 4178213) B4178213
theorem B7427933 : Blo 1955435 7427933 := bstep (se 3 (by rfl) ⟨1392737, by rfl⟩ : syracuseStep 7427933 = 2785475) B2785475
theorem B4951955 : Blo 1955435 4951955 := bstep (se 1 (by rfl) ⟨3713966, by rfl⟩ : syracuseStep 4951955 = 7427933) B7427933
theorem B3301303 : Blo 1955435 3301303 := bstep (se 1 (by rfl) ⟨2475977, by rfl⟩ : syracuseStep 3301303 = 4951955) B4951955
theorem B4401737 : Blo 1955435 4401737 := bstep (se 2 (by rfl) ⟨1650651, by rfl⟩ : syracuseStep 4401737 = 3301303) B3301303
theorem B2934491 : Blo 1955435 2934491 := bstep (se 1 (by rfl) ⟨2200868, by rfl⟩ : syracuseStep 2934491 = 4401737) B4401737
theorem B1956327 : Blo 1955435 1956327 := bstep (se 1 (by rfl) ⟨1467245, by rfl⟩ : syracuseStep 1956327 = 2934491) B2934491
theorem B2200873 : Blo 1955435 2200873 := bbase (se 2 (by rfl) ⟨825327, by rfl⟩ : syracuseStep 2200873 = 1650655) (by norm_num)
theorem B2934497 : Blo 1955435 2934497 := bstep (se 2 (by rfl) ⟨1100436, by rfl⟩ : syracuseStep 2934497 = 2200873) B2200873
theorem B1956331 : Blo 1955435 1956331 := bstep (se 1 (by rfl) ⟨1467248, by rfl⟩ : syracuseStep 1956331 = 2934497) B2934497
theorem B2974541 : Blo 1955435 2974541 := bbase (se 3 (by rfl) ⟨557726, by rfl⟩ : syracuseStep 2974541 = 1115453) (by norm_num)
theorem B7932109 : Blo 1955435 7932109 := bstep (se 3 (by rfl) ⟨1487270, by rfl⟩ : syracuseStep 7932109 = 2974541) B2974541
theorem B10576145 : Blo 1955435 10576145 := bstep (se 2 (by rfl) ⟨3966054, by rfl⟩ : syracuseStep 10576145 = 7932109) B7932109
theorem B7050763 : Blo 1955435 7050763 := bstep (se 1 (by rfl) ⟨5288072, by rfl⟩ : syracuseStep 7050763 = 10576145) B10576145
theorem B9401017 : Blo 1955435 9401017 := bstep (se 2 (by rfl) ⟨3525381, by rfl⟩ : syracuseStep 9401017 = 7050763) B7050763
theorem B12534689 : Blo 1955435 12534689 := bstep (se 2 (by rfl) ⟨4700508, by rfl⟩ : syracuseStep 12534689 = 9401017) B9401017
theorem B8356459 : Blo 1955435 8356459 := bstep (se 1 (by rfl) ⟨6267344, by rfl⟩ : syracuseStep 8356459 = 12534689) B12534689
theorem B11141945 : Blo 1955435 11141945 := bstep (se 2 (by rfl) ⟨4178229, by rfl⟩ : syracuseStep 11141945 = 8356459) B8356459
theorem B7427963 : Blo 1955435 7427963 := bstep (se 1 (by rfl) ⟨5570972, by rfl⟩ : syracuseStep 7427963 = 11141945) B11141945
theorem B4951975 : Blo 1955435 4951975 := bstep (se 1 (by rfl) ⟨3713981, by rfl⟩ : syracuseStep 4951975 = 7427963) B7427963
theorem B6602633 : Blo 1955435 6602633 := bstep (se 2 (by rfl) ⟨2475987, by rfl⟩ : syracuseStep 6602633 = 4951975) B4951975
theorem B4401755 : Blo 1955435 4401755 := bstep (se 1 (by rfl) ⟨3301316, by rfl⟩ : syracuseStep 4401755 = 6602633) B6602633
theorem B2934503 : Blo 1955435 2934503 := bstep (se 1 (by rfl) ⟨2200877, by rfl⟩ : syracuseStep 2934503 = 4401755) B4401755
theorem B1956335 : Blo 1955435 1956335 := bstep (se 1 (by rfl) ⟨1467251, by rfl⟩ : syracuseStep 1956335 = 2934503) B2934503
theorem B2934509 : Blo 1955435 2934509 := bbase (se 3 (by rfl) ⟨550220, by rfl⟩ : syracuseStep 2934509 = 1100441) (by norm_num)
theorem B1956339 : Blo 1955435 1956339 := bstep (se 1 (by rfl) ⟨1467254, by rfl⟩ : syracuseStep 1956339 = 2934509) B2934509
theorem B4401773 : Blo 1955435 4401773 := bbase (se 3 (by rfl) ⟨825332, by rfl⟩ : syracuseStep 4401773 = 1650665) (by norm_num)
theorem B2934515 : Blo 1955435 2934515 := bstep (se 1 (by rfl) ⟨2200886, by rfl⟩ : syracuseStep 2934515 = 4401773) B4401773
theorem B1956343 : Blo 1955435 1956343 := bstep (se 1 (by rfl) ⟨1467257, by rfl⟩ : syracuseStep 1956343 = 2934515) B2934515
theorem B3714005 : Blo 1955435 3714005 := bbase (se 7 (by rfl) ⟨43523, by rfl⟩ : syracuseStep 3714005 = 87047) (by norm_num)
theorem B2476003 : Blo 1955435 2476003 := bstep (se 1 (by rfl) ⟨1857002, by rfl⟩ : syracuseStep 2476003 = 3714005) B3714005
theorem B3301337 : Blo 1955435 3301337 := bstep (se 2 (by rfl) ⟨1238001, by rfl⟩ : syracuseStep 3301337 = 2476003) B2476003
theorem B2200891 : Blo 1955435 2200891 := bstep (se 1 (by rfl) ⟨1650668, by rfl⟩ : syracuseStep 2200891 = 3301337) B3301337
theorem B2934521 : Blo 1955435 2934521 := bstep (se 2 (by rfl) ⟨1100445, by rfl⟩ : syracuseStep 2934521 = 2200891) B2200891
theorem B1956347 : Blo 1955435 1956347 := bstep (se 1 (by rfl) ⟨1467260, by rfl⟩ : syracuseStep 1956347 = 2934521) B2934521
theorem B10039157 : Blo 1955435 10039157 := bbase (se 5 (by rfl) ⟨470585, by rfl⟩ : syracuseStep 10039157 = 941171) (by norm_num)
theorem B6692771 : Blo 1955435 6692771 := bstep (se 1 (by rfl) ⟨5019578, by rfl⟩ : syracuseStep 6692771 = 10039157) B10039157
theorem B4461847 : Blo 1955435 4461847 := bstep (se 1 (by rfl) ⟨3346385, by rfl⟩ : syracuseStep 4461847 = 6692771) B6692771
theorem B23796517 : Blo 1955435 23796517 := bstep (se 4 (by rfl) ⟨2230923, by rfl⟩ : syracuseStep 23796517 = 4461847) B4461847
theorem B31728689 : Blo 1955435 31728689 := bstep (se 2 (by rfl) ⟨11898258, by rfl⟩ : syracuseStep 31728689 = 23796517) B23796517
theorem B21152459 : Blo 1955435 21152459 := bstep (se 1 (by rfl) ⟨15864344, by rfl⟩ : syracuseStep 21152459 = 31728689) B31728689
theorem B56406557 : Blo 1955435 56406557 := bstep (se 3 (by rfl) ⟨10576229, by rfl⟩ : syracuseStep 56406557 = 21152459) B21152459
theorem B37604371 : Blo 1955435 37604371 := bstep (se 1 (by rfl) ⟨28203278, by rfl⟩ : syracuseStep 37604371 = 56406557) B56406557
theorem B50139161 : Blo 1955435 50139161 := bstep (se 2 (by rfl) ⟨18802185, by rfl⟩ : syracuseStep 50139161 = 37604371) B37604371
theorem B33426107 : Blo 1955435 33426107 := bstep (se 1 (by rfl) ⟨25069580, by rfl⟩ : syracuseStep 33426107 = 50139161) B50139161
theorem B22284071 : Blo 1955435 22284071 := bstep (se 1 (by rfl) ⟨16713053, by rfl⟩ : syracuseStep 22284071 = 33426107) B33426107
theorem B14856047 : Blo 1955435 14856047 := bstep (se 1 (by rfl) ⟨11142035, by rfl⟩ : syracuseStep 14856047 = 22284071) B22284071
theorem B9904031 : Blo 1955435 9904031 := bstep (se 1 (by rfl) ⟨7428023, by rfl⟩ : syracuseStep 9904031 = 14856047) B14856047
theorem B6602687 : Blo 1955435 6602687 := bstep (se 1 (by rfl) ⟨4952015, by rfl⟩ : syracuseStep 6602687 = 9904031) B9904031
theorem B4401791 : Blo 1955435 4401791 := bstep (se 1 (by rfl) ⟨3301343, by rfl⟩ : syracuseStep 4401791 = 6602687) B6602687
theorem B2934527 : Blo 1955435 2934527 := bstep (se 1 (by rfl) ⟨2200895, by rfl⟩ : syracuseStep 2934527 = 4401791) B4401791
theorem B1956351 : Blo 1955435 1956351 := bstep (se 1 (by rfl) ⟨1467263, by rfl⟩ : syracuseStep 1956351 = 2934527) B2934527
theorem B2934533 : Blo 1955435 2934533 := bbase (se 4 (by rfl) ⟨275112, by rfl⟩ : syracuseStep 2934533 = 550225) (by norm_num)
theorem B1956355 : Blo 1955435 1956355 := bstep (se 1 (by rfl) ⟨1467266, by rfl⟩ : syracuseStep 1956355 = 2934533) B2934533
theorem B3301357 : Blo 1955435 3301357 := bbase (se 3 (by rfl) ⟨619004, by rfl⟩ : syracuseStep 3301357 = 1238009) (by norm_num)
theorem B4401809 : Blo 1955435 4401809 := bstep (se 2 (by rfl) ⟨1650678, by rfl⟩ : syracuseStep 4401809 = 3301357) B3301357
theorem B2934539 : Blo 1955435 2934539 := bstep (se 1 (by rfl) ⟨2200904, by rfl⟩ : syracuseStep 2934539 = 4401809) B4401809
theorem B1956359 : Blo 1955435 1956359 := bstep (se 1 (by rfl) ⟨1467269, by rfl⟩ : syracuseStep 1956359 = 2934539) B2934539
theorem B2200909 : Blo 1955435 2200909 := bbase (se 3 (by rfl) ⟨412670, by rfl⟩ : syracuseStep 2200909 = 825341) (by norm_num)
theorem B2934545 : Blo 1955435 2934545 := bstep (se 2 (by rfl) ⟨1100454, by rfl⟩ : syracuseStep 2934545 = 2200909) B2200909
theorem B1956363 : Blo 1955435 1956363 := bstep (se 1 (by rfl) ⟨1467272, by rfl⟩ : syracuseStep 1956363 = 2934545) B2934545
theorem B6602741 : Blo 1955435 6602741 := bbase (se 5 (by rfl) ⟨309503, by rfl⟩ : syracuseStep 6602741 = 619007) (by norm_num)
theorem B4401827 : Blo 1955435 4401827 := bstep (se 1 (by rfl) ⟨3301370, by rfl⟩ : syracuseStep 4401827 = 6602741) B6602741
theorem B2934551 : Blo 1955435 2934551 := bstep (se 1 (by rfl) ⟨2200913, by rfl⟩ : syracuseStep 2934551 = 4401827) B4401827
theorem B1956367 : Blo 1955435 1956367 := bstep (se 1 (by rfl) ⟨1467275, by rfl⟩ : syracuseStep 1956367 = 2934551) B2934551
theorem B2934557 : Blo 1955435 2934557 := bbase (se 3 (by rfl) ⟨550229, by rfl⟩ : syracuseStep 2934557 = 1100459) (by norm_num)
theorem B1956371 : Blo 1955435 1956371 := bstep (se 1 (by rfl) ⟨1467278, by rfl⟩ : syracuseStep 1956371 = 2934557) B2934557
theorem B4401845 : Blo 1955435 4401845 := bbase (se 5 (by rfl) ⟨206336, by rfl⟩ : syracuseStep 4401845 = 412673) (by norm_num)
theorem B2934563 : Blo 1955435 2934563 := bstep (se 1 (by rfl) ⟨2200922, by rfl⟩ : syracuseStep 2934563 = 4401845) B4401845
theorem B1956375 : Blo 1955435 1956375 := bstep (se 1 (by rfl) ⟨1467281, by rfl⟩ : syracuseStep 1956375 = 2934563) B2934563
theorem B11142197 : Blo 1955435 11142197 := bbase (se 5 (by rfl) ⟨522290, by rfl⟩ : syracuseStep 11142197 = 1044581) (by norm_num)
theorem B7428131 : Blo 1955435 7428131 := bstep (se 1 (by rfl) ⟨5571098, by rfl⟩ : syracuseStep 7428131 = 11142197) B11142197
theorem B4952087 : Blo 1955435 4952087 := bstep (se 1 (by rfl) ⟨3714065, by rfl⟩ : syracuseStep 4952087 = 7428131) B7428131
theorem B3301391 : Blo 1955435 3301391 := bstep (se 1 (by rfl) ⟨2476043, by rfl⟩ : syracuseStep 3301391 = 4952087) B4952087
theorem B2200927 : Blo 1955435 2200927 := bstep (se 1 (by rfl) ⟨1650695, by rfl⟩ : syracuseStep 2200927 = 3301391) B3301391
theorem B2934569 : Blo 1955435 2934569 := bstep (se 2 (by rfl) ⟨1100463, by rfl⟩ : syracuseStep 2934569 = 2200927) B2200927
theorem B1956379 : Blo 1955435 1956379 := bstep (se 1 (by rfl) ⟨1467284, by rfl⟩ : syracuseStep 1956379 = 2934569) B2934569
theorem B5571109 : Blo 1955435 5571109 := bbase (se 4 (by rfl) ⟨522291, by rfl⟩ : syracuseStep 5571109 = 1044583) (by norm_num)
theorem B7428145 : Blo 1955435 7428145 := bstep (se 2 (by rfl) ⟨2785554, by rfl⟩ : syracuseStep 7428145 = 5571109) B5571109
theorem B9904193 : Blo 1955435 9904193 := bstep (se 2 (by rfl) ⟨3714072, by rfl⟩ : syracuseStep 9904193 = 7428145) B7428145
theorem B6602795 : Blo 1955435 6602795 := bstep (se 1 (by rfl) ⟨4952096, by rfl⟩ : syracuseStep 6602795 = 9904193) B9904193
theorem B4401863 : Blo 1955435 4401863 := bstep (se 1 (by rfl) ⟨3301397, by rfl⟩ : syracuseStep 4401863 = 6602795) B6602795
theorem B2934575 : Blo 1955435 2934575 := bstep (se 1 (by rfl) ⟨2200931, by rfl⟩ : syracuseStep 2934575 = 4401863) B4401863
theorem B1956383 : Blo 1955435 1956383 := bstep (se 1 (by rfl) ⟨1467287, by rfl⟩ : syracuseStep 1956383 = 2934575) B2934575
theorem B2934581 : Blo 1955435 2934581 := bbase (se 5 (by rfl) ⟨137558, by rfl⟩ : syracuseStep 2934581 = 275117) (by norm_num)
theorem B1956387 : Blo 1955435 1956387 := bstep (se 1 (by rfl) ⟨1467290, by rfl⟩ : syracuseStep 1956387 = 2934581) B2934581
theorem B4952117 : Blo 1955435 4952117 := bbase (se 5 (by rfl) ⟨232130, by rfl⟩ : syracuseStep 4952117 = 464261) (by norm_num)
theorem B3301411 : Blo 1955435 3301411 := bstep (se 1 (by rfl) ⟨2476058, by rfl⟩ : syracuseStep 3301411 = 4952117) B4952117
theorem B4401881 : Blo 1955435 4401881 := bstep (se 2 (by rfl) ⟨1650705, by rfl⟩ : syracuseStep 4401881 = 3301411) B3301411
theorem B2934587 : Blo 1955435 2934587 := bstep (se 1 (by rfl) ⟨2200940, by rfl⟩ : syracuseStep 2934587 = 4401881) B4401881
theorem B1956391 : Blo 1955435 1956391 := bstep (se 1 (by rfl) ⟨1467293, by rfl⟩ : syracuseStep 1956391 = 2934587) B2934587
theorem B2200945 : Blo 1955435 2200945 := bbase (se 2 (by rfl) ⟨825354, by rfl⟩ : syracuseStep 2200945 = 1650709) (by norm_num)
theorem B2934593 : Blo 1955435 2934593 := bstep (se 2 (by rfl) ⟨1100472, by rfl⟩ : syracuseStep 2934593 = 2200945) B2200945
theorem B1956395 : Blo 1955435 1956395 := bstep (se 1 (by rfl) ⟨1467296, by rfl⟩ : syracuseStep 1956395 = 2934593) B2934593
theorem B7529557 : Blo 1955435 7529557 := bbase (se 8 (by rfl) ⟨44118, by rfl⟩ : syracuseStep 7529557 = 88237) (by norm_num)
theorem B10039409 : Blo 1955435 10039409 := bstep (se 2 (by rfl) ⟨3764778, by rfl⟩ : syracuseStep 10039409 = 7529557) B7529557
theorem B6692939 : Blo 1955435 6692939 := bstep (se 1 (by rfl) ⟨5019704, by rfl⟩ : syracuseStep 6692939 = 10039409) B10039409
theorem B4461959 : Blo 1955435 4461959 := bstep (se 1 (by rfl) ⟨3346469, by rfl⟩ : syracuseStep 4461959 = 6692939) B6692939
theorem B2974639 : Blo 1955435 2974639 := bstep (se 1 (by rfl) ⟨2230979, by rfl⟩ : syracuseStep 2974639 = 4461959) B4461959
theorem B3966185 : Blo 1955435 3966185 := bstep (se 2 (by rfl) ⟨1487319, by rfl⟩ : syracuseStep 3966185 = 2974639) B2974639
theorem B10576493 : Blo 1955435 10576493 := bstep (se 3 (by rfl) ⟨1983092, by rfl⟩ : syracuseStep 10576493 = 3966185) B3966185
theorem B7050995 : Blo 1955435 7050995 := bstep (se 1 (by rfl) ⟨5288246, by rfl⟩ : syracuseStep 7050995 = 10576493) B10576493
theorem B4700663 : Blo 1955435 4700663 := bstep (se 1 (by rfl) ⟨3525497, by rfl⟩ : syracuseStep 4700663 = 7050995) B7050995
theorem B3133775 : Blo 1955435 3133775 := bstep (se 1 (by rfl) ⟨2350331, by rfl⟩ : syracuseStep 3133775 = 4700663) B4700663
theorem B8356733 : Blo 1955435 8356733 := bstep (se 3 (by rfl) ⟨1566887, by rfl⟩ : syracuseStep 8356733 = 3133775) B3133775
theorem B5571155 : Blo 1955435 5571155 := bstep (se 1 (by rfl) ⟨4178366, by rfl⟩ : syracuseStep 5571155 = 8356733) B8356733
theorem B3714103 : Blo 1955435 3714103 := bstep (se 1 (by rfl) ⟨2785577, by rfl⟩ : syracuseStep 3714103 = 5571155) B5571155
theorem B4952137 : Blo 1955435 4952137 := bstep (se 2 (by rfl) ⟨1857051, by rfl⟩ : syracuseStep 4952137 = 3714103) B3714103
theorem B6602849 : Blo 1955435 6602849 := bstep (se 2 (by rfl) ⟨2476068, by rfl⟩ : syracuseStep 6602849 = 4952137) B4952137
theorem B4401899 : Blo 1955435 4401899 := bstep (se 1 (by rfl) ⟨3301424, by rfl⟩ : syracuseStep 4401899 = 6602849) B6602849
theorem B2934599 : Blo 1955435 2934599 := bstep (se 1 (by rfl) ⟨2200949, by rfl⟩ : syracuseStep 2934599 = 4401899) B4401899
theorem B1956399 : Blo 1955435 1956399 := bstep (se 1 (by rfl) ⟨1467299, by rfl⟩ : syracuseStep 1956399 = 2934599) B2934599
theorem B2934605 : Blo 1955435 2934605 := bbase (se 3 (by rfl) ⟨550238, by rfl⟩ : syracuseStep 2934605 = 1100477) (by norm_num)
theorem B1956403 : Blo 1955435 1956403 := bstep (se 1 (by rfl) ⟨1467302, by rfl⟩ : syracuseStep 1956403 = 2934605) B2934605
theorem B4401917 : Blo 1955435 4401917 := bbase (se 3 (by rfl) ⟨825359, by rfl⟩ : syracuseStep 4401917 = 1650719) (by norm_num)
theorem B2934611 : Blo 1955435 2934611 := bstep (se 1 (by rfl) ⟨2200958, by rfl⟩ : syracuseStep 2934611 = 4401917) B4401917
theorem B1956407 : Blo 1955435 1956407 := bstep (se 1 (by rfl) ⟨1467305, by rfl⟩ : syracuseStep 1956407 = 2934611) B2934611
theorem B3301445 : Blo 1955435 3301445 := bbase (se 4 (by rfl) ⟨309510, by rfl⟩ : syracuseStep 3301445 = 619021) (by norm_num)
theorem B2200963 : Blo 1955435 2200963 := bstep (se 1 (by rfl) ⟨1650722, by rfl⟩ : syracuseStep 2200963 = 3301445) B3301445
theorem B2934617 : Blo 1955435 2934617 := bstep (se 2 (by rfl) ⟨1100481, by rfl⟩ : syracuseStep 2934617 = 2200963) B2200963
theorem B1956411 : Blo 1955435 1956411 := bstep (se 1 (by rfl) ⟨1467308, by rfl⟩ : syracuseStep 1956411 = 2934617) B2934617
theorem B14856533 : Blo 1955435 14856533 := bbase (se 10 (by rfl) ⟨21762, by rfl⟩ : syracuseStep 14856533 = 43525) (by norm_num)
theorem B9904355 : Blo 1955435 9904355 := bstep (se 1 (by rfl) ⟨7428266, by rfl⟩ : syracuseStep 9904355 = 14856533) B14856533
theorem B6602903 : Blo 1955435 6602903 := bstep (se 1 (by rfl) ⟨4952177, by rfl⟩ : syracuseStep 6602903 = 9904355) B9904355
theorem B4401935 : Blo 1955435 4401935 := bstep (se 1 (by rfl) ⟨3301451, by rfl⟩ : syracuseStep 4401935 = 6602903) B6602903
theorem B2934623 : Blo 1955435 2934623 := bstep (se 1 (by rfl) ⟨2200967, by rfl⟩ : syracuseStep 2934623 = 4401935) B4401935
theorem B1956415 : Blo 1955435 1956415 := bstep (se 1 (by rfl) ⟨1467311, by rfl⟩ : syracuseStep 1956415 = 2934623) B2934623
theorem B2934629 : Blo 1955435 2934629 := bbase (se 4 (by rfl) ⟨275121, by rfl⟩ : syracuseStep 2934629 = 550243) (by norm_num)
theorem B1956419 : Blo 1955435 1956419 := bstep (se 1 (by rfl) ⟨1467314, by rfl⟩ : syracuseStep 1956419 = 2934629) B2934629
theorem B3714149 : Blo 1955435 3714149 := bbase (se 4 (by rfl) ⟨348201, by rfl⟩ : syracuseStep 3714149 = 696403) (by norm_num)
theorem B2476099 : Blo 1955435 2476099 := bstep (se 1 (by rfl) ⟨1857074, by rfl⟩ : syracuseStep 2476099 = 3714149) B3714149
theorem B3301465 : Blo 1955435 3301465 := bstep (se 2 (by rfl) ⟨1238049, by rfl⟩ : syracuseStep 3301465 = 2476099) B2476099
theorem B4401953 : Blo 1955435 4401953 := bstep (se 2 (by rfl) ⟨1650732, by rfl⟩ : syracuseStep 4401953 = 3301465) B3301465
theorem B2934635 : Blo 1955435 2934635 := bstep (se 1 (by rfl) ⟨2200976, by rfl⟩ : syracuseStep 2934635 = 4401953) B4401953
theorem B1956423 : Blo 1955435 1956423 := bstep (se 1 (by rfl) ⟨1467317, by rfl⟩ : syracuseStep 1956423 = 2934635) B2934635
theorem B2200981 : Blo 1955435 2200981 := bbase (se 6 (by rfl) ⟨51585, by rfl⟩ : syracuseStep 2200981 = 103171) (by norm_num)
theorem B2934641 : Blo 1955435 2934641 := bstep (se 2 (by rfl) ⟨1100490, by rfl⟩ : syracuseStep 2934641 = 2200981) B2200981
theorem B1956427 : Blo 1955435 1956427 := bstep (se 1 (by rfl) ⟨1467320, by rfl⟩ : syracuseStep 1956427 = 2934641) B2934641
theorem B2476109 : Blo 1955435 2476109 := bbase (se 3 (by rfl) ⟨464270, by rfl⟩ : syracuseStep 2476109 = 928541) (by norm_num)
theorem B6602957 : Blo 1955435 6602957 := bstep (se 3 (by rfl) ⟨1238054, by rfl⟩ : syracuseStep 6602957 = 2476109) B2476109
theorem B4401971 : Blo 1955435 4401971 := bstep (se 1 (by rfl) ⟨3301478, by rfl⟩ : syracuseStep 4401971 = 6602957) B6602957
theorem B2934647 : Blo 1955435 2934647 := bstep (se 1 (by rfl) ⟨2200985, by rfl⟩ : syracuseStep 2934647 = 4401971) B4401971
theorem B1956431 : Blo 1955435 1956431 := bstep (se 1 (by rfl) ⟨1467323, by rfl⟩ : syracuseStep 1956431 = 2934647) B2934647
theorem B2934653 : Blo 1955435 2934653 := bbase (se 3 (by rfl) ⟨550247, by rfl⟩ : syracuseStep 2934653 = 1100495) (by norm_num)
theorem B1956435 : Blo 1955435 1956435 := bstep (se 1 (by rfl) ⟨1467326, by rfl⟩ : syracuseStep 1956435 = 2934653) B2934653
theorem B4401989 : Blo 1955435 4401989 := bbase (se 4 (by rfl) ⟨412686, by rfl⟩ : syracuseStep 4401989 = 825373) (by norm_num)
theorem B2934659 : Blo 1955435 2934659 := bstep (se 1 (by rfl) ⟨2200994, by rfl⟩ : syracuseStep 2934659 = 4401989) B4401989
theorem B1956439 : Blo 1955435 1956439 := bstep (se 1 (by rfl) ⟨1467329, by rfl⟩ : syracuseStep 1956439 = 2934659) B2934659
theorem B4178461 : Blo 1955435 4178461 := bbase (se 3 (by rfl) ⟨783461, by rfl⟩ : syracuseStep 4178461 = 1566923) (by norm_num)
theorem B5571281 : Blo 1955435 5571281 := bstep (se 2 (by rfl) ⟨2089230, by rfl⟩ : syracuseStep 5571281 = 4178461) B4178461
theorem B3714187 : Blo 1955435 3714187 := bstep (se 1 (by rfl) ⟨2785640, by rfl⟩ : syracuseStep 3714187 = 5571281) B5571281
theorem B4952249 : Blo 1955435 4952249 := bstep (se 2 (by rfl) ⟨1857093, by rfl⟩ : syracuseStep 4952249 = 3714187) B3714187
theorem B3301499 : Blo 1955435 3301499 := bstep (se 1 (by rfl) ⟨2476124, by rfl⟩ : syracuseStep 3301499 = 4952249) B4952249
theorem B2200999 : Blo 1955435 2200999 := bstep (se 1 (by rfl) ⟨1650749, by rfl⟩ : syracuseStep 2200999 = 3301499) B3301499
theorem B2934665 : Blo 1955435 2934665 := bstep (se 2 (by rfl) ⟨1100499, by rfl⟩ : syracuseStep 2934665 = 2200999) B2200999
theorem B1956443 : Blo 1955435 1956443 := bstep (se 1 (by rfl) ⟨1467332, by rfl⟩ : syracuseStep 1956443 = 2934665) B2934665
theorem B9904517 : Blo 1955435 9904517 := bbase (se 4 (by rfl) ⟨928548, by rfl⟩ : syracuseStep 9904517 = 1857097) (by norm_num)
theorem B6603011 : Blo 1955435 6603011 := bstep (se 1 (by rfl) ⟨4952258, by rfl⟩ : syracuseStep 6603011 = 9904517) B9904517
theorem B4402007 : Blo 1955435 4402007 := bstep (se 1 (by rfl) ⟨3301505, by rfl⟩ : syracuseStep 4402007 = 6603011) B6603011
theorem B2934671 : Blo 1955435 2934671 := bstep (se 1 (by rfl) ⟨2201003, by rfl⟩ : syracuseStep 2934671 = 4402007) B4402007
theorem B1956447 : Blo 1955435 1956447 := bstep (se 1 (by rfl) ⟨1467335, by rfl⟩ : syracuseStep 1956447 = 2934671) B2934671
theorem B2934677 : Blo 1955435 2934677 := bbase (se 6 (by rfl) ⟨68781, by rfl⟩ : syracuseStep 2934677 = 137563) (by norm_num)
theorem B1956451 : Blo 1955435 1956451 := bstep (se 1 (by rfl) ⟨1467338, by rfl⟩ : syracuseStep 1956451 = 2934677) B2934677
theorem B2117749 : Blo 1955435 2117749 := bbase (se 5 (by rfl) ⟨99269, by rfl⟩ : syracuseStep 2117749 = 198539) (by norm_num)
theorem B2823665 : Blo 1955435 2823665 := bstep (se 2 (by rfl) ⟨1058874, by rfl⟩ : syracuseStep 2823665 = 2117749) B2117749
theorem B7529773 : Blo 1955435 7529773 := bstep (se 3 (by rfl) ⟨1411832, by rfl⟩ : syracuseStep 7529773 = 2823665) B2823665
theorem B10039697 : Blo 1955435 10039697 := bstep (se 2 (by rfl) ⟨3764886, by rfl⟩ : syracuseStep 10039697 = 7529773) B7529773
theorem B6693131 : Blo 1955435 6693131 := bstep (se 1 (by rfl) ⟨5019848, by rfl⟩ : syracuseStep 6693131 = 10039697) B10039697
theorem B17848349 : Blo 1955435 17848349 := bstep (se 3 (by rfl) ⟨3346565, by rfl⟩ : syracuseStep 17848349 = 6693131) B6693131
theorem B11898899 : Blo 1955435 11898899 := bstep (se 1 (by rfl) ⟨8924174, by rfl⟩ : syracuseStep 11898899 = 17848349) B17848349
theorem B7932599 : Blo 1955435 7932599 := bstep (se 1 (by rfl) ⟨5949449, by rfl⟩ : syracuseStep 7932599 = 11898899) B11898899
theorem B5288399 : Blo 1955435 5288399 := bstep (se 1 (by rfl) ⟨3966299, by rfl⟩ : syracuseStep 5288399 = 7932599) B7932599
theorem B3525599 : Blo 1955435 3525599 := bstep (se 1 (by rfl) ⟨2644199, by rfl⟩ : syracuseStep 3525599 = 5288399) B5288399
theorem B2350399 : Blo 1955435 2350399 := bstep (se 1 (by rfl) ⟨1762799, by rfl⟩ : syracuseStep 2350399 = 3525599) B3525599
theorem B3133865 : Blo 1955435 3133865 := bstep (se 2 (by rfl) ⟨1175199, by rfl⟩ : syracuseStep 3133865 = 2350399) B2350399
theorem B2089243 : Blo 1955435 2089243 := bstep (se 1 (by rfl) ⟨1566932, by rfl⟩ : syracuseStep 2089243 = 3133865) B3133865
theorem B11142629 : Blo 1955435 11142629 := bstep (se 4 (by rfl) ⟨1044621, by rfl⟩ : syracuseStep 11142629 = 2089243) B2089243
theorem B7428419 : Blo 1955435 7428419 := bstep (se 1 (by rfl) ⟨5571314, by rfl⟩ : syracuseStep 7428419 = 11142629) B11142629
theorem B4952279 : Blo 1955435 4952279 := bstep (se 1 (by rfl) ⟨3714209, by rfl⟩ : syracuseStep 4952279 = 7428419) B7428419
theorem B3301519 : Blo 1955435 3301519 := bstep (se 1 (by rfl) ⟨2476139, by rfl⟩ : syracuseStep 3301519 = 4952279) B4952279
theorem B4402025 : Blo 1955435 4402025 := bstep (se 2 (by rfl) ⟨1650759, by rfl⟩ : syracuseStep 4402025 = 3301519) B3301519
theorem B2934683 : Blo 1955435 2934683 := bstep (se 1 (by rfl) ⟨2201012, by rfl⟩ : syracuseStep 2934683 = 4402025) B4402025
theorem B1956455 : Blo 1955435 1956455 := bstep (se 1 (by rfl) ⟨1467341, by rfl⟩ : syracuseStep 1956455 = 2934683) B2934683
theorem B2201017 : Blo 1955435 2201017 := bbase (se 2 (by rfl) ⟨825381, by rfl⟩ : syracuseStep 2201017 = 1650763) (by norm_num)
theorem B2934689 : Blo 1955435 2934689 := bstep (se 2 (by rfl) ⟨1100508, by rfl⟩ : syracuseStep 2934689 = 2201017) B2201017
theorem B1956459 : Blo 1955435 1956459 := bstep (se 1 (by rfl) ⟨1467344, by rfl⟩ : syracuseStep 1956459 = 2934689) B2934689
theorem B7932629 : Blo 1955435 7932629 := bbase (se 7 (by rfl) ⟨92960, by rfl⟩ : syracuseStep 7932629 = 185921) (by norm_num)
theorem B5288419 : Blo 1955435 5288419 := bstep (se 1 (by rfl) ⟨3966314, by rfl⟩ : syracuseStep 5288419 = 7932629) B7932629
theorem B7051225 : Blo 1955435 7051225 := bstep (se 2 (by rfl) ⟨2644209, by rfl⟩ : syracuseStep 7051225 = 5288419) B5288419
theorem B9401633 : Blo 1955435 9401633 := bstep (se 2 (by rfl) ⟨3525612, by rfl⟩ : syracuseStep 9401633 = 7051225) B7051225
theorem B6267755 : Blo 1955435 6267755 := bstep (se 1 (by rfl) ⟨4700816, by rfl⟩ : syracuseStep 6267755 = 9401633) B9401633
theorem B4178503 : Blo 1955435 4178503 := bstep (se 1 (by rfl) ⟨3133877, by rfl⟩ : syracuseStep 4178503 = 6267755) B6267755
theorem B5571337 : Blo 1955435 5571337 := bstep (se 2 (by rfl) ⟨2089251, by rfl⟩ : syracuseStep 5571337 = 4178503) B4178503
theorem B7428449 : Blo 1955435 7428449 := bstep (se 2 (by rfl) ⟨2785668, by rfl⟩ : syracuseStep 7428449 = 5571337) B5571337
theorem B4952299 : Blo 1955435 4952299 := bstep (se 1 (by rfl) ⟨3714224, by rfl⟩ : syracuseStep 4952299 = 7428449) B7428449
theorem B6603065 : Blo 1955435 6603065 := bstep (se 2 (by rfl) ⟨2476149, by rfl⟩ : syracuseStep 6603065 = 4952299) B4952299
theorem B4402043 : Blo 1955435 4402043 := bstep (se 1 (by rfl) ⟨3301532, by rfl⟩ : syracuseStep 4402043 = 6603065) B6603065
theorem B2934695 : Blo 1955435 2934695 := bstep (se 1 (by rfl) ⟨2201021, by rfl⟩ : syracuseStep 2934695 = 4402043) B4402043
theorem B1956463 : Blo 1955435 1956463 := bstep (se 1 (by rfl) ⟨1467347, by rfl⟩ : syracuseStep 1956463 = 2934695) B2934695
theorem B2934701 : Blo 1955435 2934701 := bbase (se 3 (by rfl) ⟨550256, by rfl⟩ : syracuseStep 2934701 = 1100513) (by norm_num)
theorem B1956467 : Blo 1955435 1956467 := bstep (se 1 (by rfl) ⟨1467350, by rfl⟩ : syracuseStep 1956467 = 2934701) B2934701
theorem B4402061 : Blo 1955435 4402061 := bbase (se 3 (by rfl) ⟨825386, by rfl⟩ : syracuseStep 4402061 = 1650773) (by norm_num)
theorem B2934707 : Blo 1955435 2934707 := bstep (se 1 (by rfl) ⟨2201030, by rfl⟩ : syracuseStep 2934707 = 4402061) B4402061
theorem B1956471 : Blo 1955435 1956471 := bstep (se 1 (by rfl) ⟨1467353, by rfl⟩ : syracuseStep 1956471 = 2934707) B2934707
theorem B2476165 : Blo 1955435 2476165 := bbase (se 4 (by rfl) ⟨232140, by rfl⟩ : syracuseStep 2476165 = 464281) (by norm_num)
theorem B3301553 : Blo 1955435 3301553 := bstep (se 2 (by rfl) ⟨1238082, by rfl⟩ : syracuseStep 3301553 = 2476165) B2476165
theorem B2201035 : Blo 1955435 2201035 := bstep (se 1 (by rfl) ⟨1650776, by rfl⟩ : syracuseStep 2201035 = 3301553) B3301553
theorem B2934713 : Blo 1955435 2934713 := bstep (se 2 (by rfl) ⟨1100517, by rfl⟩ : syracuseStep 2934713 = 2201035) B2201035
theorem B1956475 : Blo 1955435 1956475 := bstep (se 1 (by rfl) ⟨1467356, by rfl⟩ : syracuseStep 1956475 = 2934713) B2934713
theorem B4462141 : Blo 1955435 4462141 := bbase (se 3 (by rfl) ⟨836651, by rfl⟩ : syracuseStep 4462141 = 1673303) (by norm_num)
theorem B5949521 : Blo 1955435 5949521 := bstep (se 2 (by rfl) ⟨2231070, by rfl⟩ : syracuseStep 5949521 = 4462141) B4462141
theorem B3966347 : Blo 1955435 3966347 := bstep (se 1 (by rfl) ⟨2974760, by rfl⟩ : syracuseStep 3966347 = 5949521) B5949521
theorem B2644231 : Blo 1955435 2644231 := bstep (se 1 (by rfl) ⟨1983173, by rfl⟩ : syracuseStep 2644231 = 3966347) B3966347
theorem B3525641 : Blo 1955435 3525641 := bstep (se 2 (by rfl) ⟨1322115, by rfl⟩ : syracuseStep 3525641 = 2644231) B2644231
theorem B2350427 : Blo 1955435 2350427 := bstep (se 1 (by rfl) ⟨1762820, by rfl⟩ : syracuseStep 2350427 = 3525641) B3525641
theorem B25071221 : Blo 1955435 25071221 := bstep (se 5 (by rfl) ⟨1175213, by rfl⟩ : syracuseStep 25071221 = 2350427) B2350427
theorem B16714147 : Blo 1955435 16714147 := bstep (se 1 (by rfl) ⟨12535610, by rfl⟩ : syracuseStep 16714147 = 25071221) B25071221
theorem B22285529 : Blo 1955435 22285529 := bstep (se 2 (by rfl) ⟨8357073, by rfl⟩ : syracuseStep 22285529 = 16714147) B16714147
theorem B14857019 : Blo 1955435 14857019 := bstep (se 1 (by rfl) ⟨11142764, by rfl⟩ : syracuseStep 14857019 = 22285529) B22285529
theorem B9904679 : Blo 1955435 9904679 := bstep (se 1 (by rfl) ⟨7428509, by rfl⟩ : syracuseStep 9904679 = 14857019) B14857019
theorem B6603119 : Blo 1955435 6603119 := bstep (se 1 (by rfl) ⟨4952339, by rfl⟩ : syracuseStep 6603119 = 9904679) B9904679
theorem B4402079 : Blo 1955435 4402079 := bstep (se 1 (by rfl) ⟨3301559, by rfl⟩ : syracuseStep 4402079 = 6603119) B6603119
theorem B2934719 : Blo 1955435 2934719 := bstep (se 1 (by rfl) ⟨2201039, by rfl⟩ : syracuseStep 2934719 = 4402079) B4402079
theorem B1956479 : Blo 1955435 1956479 := bstep (se 1 (by rfl) ⟨1467359, by rfl⟩ : syracuseStep 1956479 = 2934719) B2934719
theorem B2934725 : Blo 1955435 2934725 := bbase (se 4 (by rfl) ⟨275130, by rfl⟩ : syracuseStep 2934725 = 550261) (by norm_num)
theorem B1956483 : Blo 1955435 1956483 := bstep (se 1 (by rfl) ⟨1467362, by rfl⟩ : syracuseStep 1956483 = 2934725) B2934725
theorem B3301573 : Blo 1955435 3301573 := bbase (se 4 (by rfl) ⟨309522, by rfl⟩ : syracuseStep 3301573 = 619045) (by norm_num)
theorem B4402097 : Blo 1955435 4402097 := bstep (se 2 (by rfl) ⟨1650786, by rfl⟩ : syracuseStep 4402097 = 3301573) B3301573
theorem B2934731 : Blo 1955435 2934731 := bstep (se 1 (by rfl) ⟨2201048, by rfl⟩ : syracuseStep 2934731 = 4402097) B4402097
theorem B1956487 : Blo 1955435 1956487 := bstep (se 1 (by rfl) ⟨1467365, by rfl⟩ : syracuseStep 1956487 = 2934731) B2934731
theorem B2201053 : Blo 1955435 2201053 := bbase (se 3 (by rfl) ⟨412697, by rfl⟩ : syracuseStep 2201053 = 825395) (by norm_num)
theorem B2934737 : Blo 1955435 2934737 := bstep (se 2 (by rfl) ⟨1100526, by rfl⟩ : syracuseStep 2934737 = 2201053) B2201053
theorem B1956491 : Blo 1955435 1956491 := bstep (se 1 (by rfl) ⟨1467368, by rfl⟩ : syracuseStep 1956491 = 2934737) B2934737
theorem B6603173 : Blo 1955435 6603173 := bbase (se 4 (by rfl) ⟨619047, by rfl⟩ : syracuseStep 6603173 = 1238095) (by norm_num)
theorem B4402115 : Blo 1955435 4402115 := bstep (se 1 (by rfl) ⟨3301586, by rfl⟩ : syracuseStep 4402115 = 6603173) B6603173
theorem B2934743 : Blo 1955435 2934743 := bstep (se 1 (by rfl) ⟨2201057, by rfl⟩ : syracuseStep 2934743 = 4402115) B4402115
theorem B1956495 : Blo 1955435 1956495 := bstep (se 1 (by rfl) ⟨1467371, by rfl⟩ : syracuseStep 1956495 = 2934743) B2934743
theorem B2934749 : Blo 1955435 2934749 := bbase (se 3 (by rfl) ⟨550265, by rfl⟩ : syracuseStep 2934749 = 1100531) (by norm_num)
theorem B1956499 : Blo 1955435 1956499 := bstep (se 1 (by rfl) ⟨1467374, by rfl⟩ : syracuseStep 1956499 = 2934749) B2934749
theorem B4402133 : Blo 1955435 4402133 := bbase (se 7 (by rfl) ⟨51587, by rfl⟩ : syracuseStep 4402133 = 103175) (by norm_num)
theorem B2934755 : Blo 1955435 2934755 := bstep (se 1 (by rfl) ⟨2201066, by rfl⟩ : syracuseStep 2934755 = 4402133) B4402133
theorem B1956503 : Blo 1955435 1956503 := bstep (se 1 (by rfl) ⟨1467377, by rfl⟩ : syracuseStep 1956503 = 2934755) B2934755
theorem B9401845 : Blo 1955435 9401845 := bbase (se 5 (by rfl) ⟨440711, by rfl⟩ : syracuseStep 9401845 = 881423) (by norm_num)
theorem B12535793 : Blo 1955435 12535793 := bstep (se 2 (by rfl) ⟨4700922, by rfl⟩ : syracuseStep 12535793 = 9401845) B9401845
theorem B8357195 : Blo 1955435 8357195 := bstep (se 1 (by rfl) ⟨6267896, by rfl⟩ : syracuseStep 8357195 = 12535793) B12535793
theorem B5571463 : Blo 1955435 5571463 := bstep (se 1 (by rfl) ⟨4178597, by rfl⟩ : syracuseStep 5571463 = 8357195) B8357195
theorem B7428617 : Blo 1955435 7428617 := bstep (se 2 (by rfl) ⟨2785731, by rfl⟩ : syracuseStep 7428617 = 5571463) B5571463
theorem B4952411 : Blo 1955435 4952411 := bstep (se 1 (by rfl) ⟨3714308, by rfl⟩ : syracuseStep 4952411 = 7428617) B7428617
theorem B3301607 : Blo 1955435 3301607 := bstep (se 1 (by rfl) ⟨2476205, by rfl⟩ : syracuseStep 3301607 = 4952411) B4952411
theorem B2201071 : Blo 1955435 2201071 := bstep (se 1 (by rfl) ⟨1650803, by rfl⟩ : syracuseStep 2201071 = 3301607) B3301607
theorem B2934761 : Blo 1955435 2934761 := bstep (se 2 (by rfl) ⟨1100535, by rfl⟩ : syracuseStep 2934761 = 2201071) B2201071
theorem B1956507 : Blo 1955435 1956507 := bstep (se 1 (by rfl) ⟨1467380, by rfl⟩ : syracuseStep 1956507 = 2934761) B2934761
theorem B16714421 : Blo 1955435 16714421 := bbase (se 5 (by rfl) ⟨783488, by rfl⟩ : syracuseStep 16714421 = 1566977) (by norm_num)
theorem B11142947 : Blo 1955435 11142947 := bstep (se 1 (by rfl) ⟨8357210, by rfl⟩ : syracuseStep 11142947 = 16714421) B16714421
theorem B7428631 : Blo 1955435 7428631 := bstep (se 1 (by rfl) ⟨5571473, by rfl⟩ : syracuseStep 7428631 = 11142947) B11142947
theorem B9904841 : Blo 1955435 9904841 := bstep (se 2 (by rfl) ⟨3714315, by rfl⟩ : syracuseStep 9904841 = 7428631) B7428631
theorem B6603227 : Blo 1955435 6603227 := bstep (se 1 (by rfl) ⟨4952420, by rfl⟩ : syracuseStep 6603227 = 9904841) B9904841
theorem B4402151 : Blo 1955435 4402151 := bstep (se 1 (by rfl) ⟨3301613, by rfl⟩ : syracuseStep 4402151 = 6603227) B6603227
theorem B2934767 : Blo 1955435 2934767 := bstep (se 1 (by rfl) ⟨2201075, by rfl⟩ : syracuseStep 2934767 = 4402151) B4402151
theorem B1956511 : Blo 1955435 1956511 := bstep (se 1 (by rfl) ⟨1467383, by rfl⟩ : syracuseStep 1956511 = 2934767) B2934767
theorem B2934773 : Blo 1955435 2934773 := bbase (se 5 (by rfl) ⟨137567, by rfl⟩ : syracuseStep 2934773 = 275135) (by norm_num)
theorem B1956515 : Blo 1955435 1956515 := bstep (se 1 (by rfl) ⟨1467386, by rfl⟩ : syracuseStep 1956515 = 2934773) B2934773
theorem B5360725 : Blo 1955435 5360725 := bbase (se 8 (by rfl) ⟨31410, by rfl⟩ : syracuseStep 5360725 = 62821) (by norm_num)
theorem B28590533 : Blo 1955435 28590533 := bstep (se 4 (by rfl) ⟨2680362, by rfl⟩ : syracuseStep 28590533 = 5360725) B5360725
theorem B19060355 : Blo 1955435 19060355 := bstep (se 1 (by rfl) ⟨14295266, by rfl⟩ : syracuseStep 19060355 = 28590533) B28590533
theorem B12706903 : Blo 1955435 12706903 := bstep (se 1 (by rfl) ⟨9530177, by rfl⟩ : syracuseStep 12706903 = 19060355) B19060355
theorem B16942537 : Blo 1955435 16942537 := bstep (se 2 (by rfl) ⟨6353451, by rfl⟩ : syracuseStep 16942537 = 12706903) B12706903
theorem B90360197 : Blo 1955435 90360197 := bstep (se 4 (by rfl) ⟨8471268, by rfl⟩ : syracuseStep 90360197 = 16942537) B16942537
theorem B60240131 : Blo 1955435 60240131 := bstep (se 1 (by rfl) ⟨45180098, by rfl⟩ : syracuseStep 60240131 = 90360197) B90360197
theorem B40160087 : Blo 1955435 40160087 := bstep (se 1 (by rfl) ⟨30120065, by rfl⟩ : syracuseStep 40160087 = 60240131) B60240131
theorem B26773391 : Blo 1955435 26773391 := bstep (se 1 (by rfl) ⟨20080043, by rfl⟩ : syracuseStep 26773391 = 40160087) B40160087
theorem B17848927 : Blo 1955435 17848927 := bstep (se 1 (by rfl) ⟨13386695, by rfl⟩ : syracuseStep 17848927 = 26773391) B26773391
theorem B23798569 : Blo 1955435 23798569 := bstep (se 2 (by rfl) ⟨8924463, by rfl⟩ : syracuseStep 23798569 = 17848927) B17848927
theorem B31731425 : Blo 1955435 31731425 := bstep (se 2 (by rfl) ⟨11899284, by rfl⟩ : syracuseStep 31731425 = 23798569) B23798569
theorem B21154283 : Blo 1955435 21154283 := bstep (se 1 (by rfl) ⟨15865712, by rfl⟩ : syracuseStep 21154283 = 31731425) B31731425
theorem B14102855 : Blo 1955435 14102855 := bstep (se 1 (by rfl) ⟨10577141, by rfl⟩ : syracuseStep 14102855 = 21154283) B21154283
theorem B9401903 : Blo 1955435 9401903 := bstep (se 1 (by rfl) ⟨7051427, by rfl⟩ : syracuseStep 9401903 = 14102855) B14102855
theorem B6267935 : Blo 1955435 6267935 := bstep (se 1 (by rfl) ⟨4700951, by rfl⟩ : syracuseStep 6267935 = 9401903) B9401903
theorem B4178623 : Blo 1955435 4178623 := bstep (se 1 (by rfl) ⟨3133967, by rfl⟩ : syracuseStep 4178623 = 6267935) B6267935
theorem B5571497 : Blo 1955435 5571497 := bstep (se 2 (by rfl) ⟨2089311, by rfl⟩ : syracuseStep 5571497 = 4178623) B4178623
theorem B3714331 : Blo 1955435 3714331 := bstep (se 1 (by rfl) ⟨2785748, by rfl⟩ : syracuseStep 3714331 = 5571497) B5571497
theorem B4952441 : Blo 1955435 4952441 := bstep (se 2 (by rfl) ⟨1857165, by rfl⟩ : syracuseStep 4952441 = 3714331) B3714331
theorem B3301627 : Blo 1955435 3301627 := bstep (se 1 (by rfl) ⟨2476220, by rfl⟩ : syracuseStep 3301627 = 4952441) B4952441
theorem B4402169 : Blo 1955435 4402169 := bstep (se 2 (by rfl) ⟨1650813, by rfl⟩ : syracuseStep 4402169 = 3301627) B3301627
theorem B2934779 : Blo 1955435 2934779 := bstep (se 1 (by rfl) ⟨2201084, by rfl⟩ : syracuseStep 2934779 = 4402169) B4402169
theorem B1956519 : Blo 1955435 1956519 := bstep (se 1 (by rfl) ⟨1467389, by rfl⟩ : syracuseStep 1956519 = 2934779) B2934779
theorem B2201089 : Blo 1955435 2201089 := bbase (se 2 (by rfl) ⟨825408, by rfl⟩ : syracuseStep 2201089 = 1650817) (by norm_num)
theorem B2934785 : Blo 1955435 2934785 := bstep (se 2 (by rfl) ⟨1100544, by rfl⟩ : syracuseStep 2934785 = 2201089) B2201089
theorem B1956523 : Blo 1955435 1956523 := bstep (se 1 (by rfl) ⟨1467392, by rfl⟩ : syracuseStep 1956523 = 2934785) B2934785
theorem B4952461 : Blo 1955435 4952461 := bbase (se 3 (by rfl) ⟨928586, by rfl⟩ : syracuseStep 4952461 = 1857173) (by norm_num)
theorem B6603281 : Blo 1955435 6603281 := bstep (se 2 (by rfl) ⟨2476230, by rfl⟩ : syracuseStep 6603281 = 4952461) B4952461
theorem B4402187 : Blo 1955435 4402187 := bstep (se 1 (by rfl) ⟨3301640, by rfl⟩ : syracuseStep 4402187 = 6603281) B6603281
theorem B2934791 : Blo 1955435 2934791 := bstep (se 1 (by rfl) ⟨2201093, by rfl⟩ : syracuseStep 2934791 = 4402187) B4402187
theorem B1956527 : Blo 1955435 1956527 := bstep (se 1 (by rfl) ⟨1467395, by rfl⟩ : syracuseStep 1956527 = 2934791) B2934791
theorem B2934797 : Blo 1955435 2934797 := bbase (se 3 (by rfl) ⟨550274, by rfl⟩ : syracuseStep 2934797 = 1100549) (by norm_num)
theorem B1956531 : Blo 1955435 1956531 := bstep (se 1 (by rfl) ⟨1467398, by rfl⟩ : syracuseStep 1956531 = 2934797) B2934797
theorem B4402205 : Blo 1955435 4402205 := bbase (se 3 (by rfl) ⟨825413, by rfl⟩ : syracuseStep 4402205 = 1650827) (by norm_num)
theorem B2934803 : Blo 1955435 2934803 := bstep (se 1 (by rfl) ⟨2201102, by rfl⟩ : syracuseStep 2934803 = 4402205) B4402205
theorem B1956535 : Blo 1955435 1956535 := bstep (se 1 (by rfl) ⟨1467401, by rfl⟩ : syracuseStep 1956535 = 2934803) B2934803
theorem B3301661 : Blo 1955435 3301661 := bbase (se 3 (by rfl) ⟨619061, by rfl⟩ : syracuseStep 3301661 = 1238123) (by norm_num)
theorem B2201107 : Blo 1955435 2201107 := bstep (se 1 (by rfl) ⟨1650830, by rfl⟩ : syracuseStep 2201107 = 3301661) B3301661
theorem B2934809 : Blo 1955435 2934809 := bstep (se 2 (by rfl) ⟨1100553, by rfl⟩ : syracuseStep 2934809 = 2201107) B2201107
theorem B1956539 : Blo 1955435 1956539 := bstep (se 1 (by rfl) ⟨1467404, by rfl⟩ : syracuseStep 1956539 = 2934809) B2934809
theorem B12536021 : Blo 1955435 12536021 := bbase (se 7 (by rfl) ⟨146906, by rfl⟩ : syracuseStep 12536021 = 293813) (by norm_num)
theorem B8357347 : Blo 1955435 8357347 := bstep (se 1 (by rfl) ⟨6268010, by rfl⟩ : syracuseStep 8357347 = 12536021) B12536021
theorem B11143129 : Blo 1955435 11143129 := bstep (se 2 (by rfl) ⟨4178673, by rfl⟩ : syracuseStep 11143129 = 8357347) B8357347
theorem B14857505 : Blo 1955435 14857505 := bstep (se 2 (by rfl) ⟨5571564, by rfl⟩ : syracuseStep 14857505 = 11143129) B11143129
theorem B9905003 : Blo 1955435 9905003 := bstep (se 1 (by rfl) ⟨7428752, by rfl⟩ : syracuseStep 9905003 = 14857505) B14857505
theorem B6603335 : Blo 1955435 6603335 := bstep (se 1 (by rfl) ⟨4952501, by rfl⟩ : syracuseStep 6603335 = 9905003) B9905003
theorem B4402223 : Blo 1955435 4402223 := bstep (se 1 (by rfl) ⟨3301667, by rfl⟩ : syracuseStep 4402223 = 6603335) B6603335
theorem B2934815 : Blo 1955435 2934815 := bstep (se 1 (by rfl) ⟨2201111, by rfl⟩ : syracuseStep 2934815 = 4402223) B4402223
theorem B1956543 : Blo 1955435 1956543 := bstep (se 1 (by rfl) ⟨1467407, by rfl⟩ : syracuseStep 1956543 = 2934815) B2934815
theorem B2934821 : Blo 1955435 2934821 := bbase (se 4 (by rfl) ⟨275139, by rfl⟩ : syracuseStep 2934821 = 550279) (by norm_num)
theorem B1956547 : Blo 1955435 1956547 := bstep (se 1 (by rfl) ⟨1467410, by rfl⟩ : syracuseStep 1956547 = 2934821) B2934821
theorem B2476261 : Blo 1955435 2476261 := bbase (se 4 (by rfl) ⟨232149, by rfl⟩ : syracuseStep 2476261 = 464299) (by norm_num)
theorem B3301681 : Blo 1955435 3301681 := bstep (se 2 (by rfl) ⟨1238130, by rfl⟩ : syracuseStep 3301681 = 2476261) B2476261
theorem B4402241 : Blo 1955435 4402241 := bstep (se 2 (by rfl) ⟨1650840, by rfl⟩ : syracuseStep 4402241 = 3301681) B3301681
theorem B2934827 : Blo 1955435 2934827 := bstep (se 1 (by rfl) ⟨2201120, by rfl⟩ : syracuseStep 2934827 = 4402241) B4402241
theorem B1956551 : Blo 1955435 1956551 := bstep (se 1 (by rfl) ⟨1467413, by rfl⟩ : syracuseStep 1956551 = 2934827) B2934827
theorem B2201125 : Blo 1955435 2201125 := bbase (se 4 (by rfl) ⟨206355, by rfl⟩ : syracuseStep 2201125 = 412711) (by norm_num)
theorem B2934833 : Blo 1955435 2934833 := bstep (se 2 (by rfl) ⟨1100562, by rfl⟩ : syracuseStep 2934833 = 2201125) B2201125
theorem B1956555 : Blo 1955435 1956555 := bstep (se 1 (by rfl) ⟨1467416, by rfl⟩ : syracuseStep 1956555 = 2934833) B2934833
theorem B3765085 : Blo 1955435 3765085 := bbase (se 3 (by rfl) ⟨705953, by rfl⟩ : syracuseStep 3765085 = 1411907) (by norm_num)
theorem B80321813 : Blo 1955435 80321813 := bstep (se 6 (by rfl) ⟨1882542, by rfl⟩ : syracuseStep 80321813 = 3765085) B3765085
theorem B53547875 : Blo 1955435 53547875 := bstep (se 1 (by rfl) ⟨40160906, by rfl⟩ : syracuseStep 53547875 = 80321813) B80321813
theorem B35698583 : Blo 1955435 35698583 := bstep (se 1 (by rfl) ⟨26773937, by rfl⟩ : syracuseStep 35698583 = 53547875) B53547875
theorem B23799055 : Blo 1955435 23799055 := bstep (se 1 (by rfl) ⟨17849291, by rfl⟩ : syracuseStep 23799055 = 35698583) B35698583
theorem B31732073 : Blo 1955435 31732073 := bstep (se 2 (by rfl) ⟨11899527, by rfl⟩ : syracuseStep 31732073 = 23799055) B23799055
theorem B21154715 : Blo 1955435 21154715 := bstep (se 1 (by rfl) ⟨15866036, by rfl⟩ : syracuseStep 21154715 = 31732073) B31732073
theorem B14103143 : Blo 1955435 14103143 := bstep (se 1 (by rfl) ⟨10577357, by rfl⟩ : syracuseStep 14103143 = 21154715) B21154715
theorem B9402095 : Blo 1955435 9402095 := bstep (se 1 (by rfl) ⟨7051571, by rfl⟩ : syracuseStep 9402095 = 14103143) B14103143
theorem B6268063 : Blo 1955435 6268063 := bstep (se 1 (by rfl) ⟨4701047, by rfl⟩ : syracuseStep 6268063 = 9402095) B9402095
theorem B8357417 : Blo 1955435 8357417 := bstep (se 2 (by rfl) ⟨3134031, by rfl⟩ : syracuseStep 8357417 = 6268063) B6268063
theorem B5571611 : Blo 1955435 5571611 := bstep (se 1 (by rfl) ⟨4178708, by rfl⟩ : syracuseStep 5571611 = 8357417) B8357417
theorem B3714407 : Blo 1955435 3714407 := bstep (se 1 (by rfl) ⟨2785805, by rfl⟩ : syracuseStep 3714407 = 5571611) B5571611
theorem B2476271 : Blo 1955435 2476271 := bstep (se 1 (by rfl) ⟨1857203, by rfl⟩ : syracuseStep 2476271 = 3714407) B3714407
theorem B6603389 : Blo 1955435 6603389 := bstep (se 3 (by rfl) ⟨1238135, by rfl⟩ : syracuseStep 6603389 = 2476271) B2476271
theorem B4402259 : Blo 1955435 4402259 := bstep (se 1 (by rfl) ⟨3301694, by rfl⟩ : syracuseStep 4402259 = 6603389) B6603389
theorem B2934839 : Blo 1955435 2934839 := bstep (se 1 (by rfl) ⟨2201129, by rfl⟩ : syracuseStep 2934839 = 4402259) B4402259
theorem B1956559 : Blo 1955435 1956559 := bstep (se 1 (by rfl) ⟨1467419, by rfl⟩ : syracuseStep 1956559 = 2934839) B2934839
theorem B2934845 : Blo 1955435 2934845 := bbase (se 3 (by rfl) ⟨550283, by rfl⟩ : syracuseStep 2934845 = 1100567) (by norm_num)
theorem B1956563 : Blo 1955435 1956563 := bstep (se 1 (by rfl) ⟨1467422, by rfl⟩ : syracuseStep 1956563 = 2934845) B2934845
theorem B4402277 : Blo 1955435 4402277 := bbase (se 4 (by rfl) ⟨412713, by rfl⟩ : syracuseStep 4402277 = 825427) (by norm_num)
theorem B2934851 : Blo 1955435 2934851 := bstep (se 1 (by rfl) ⟨2201138, by rfl⟩ : syracuseStep 2934851 = 4402277) B4402277
theorem B1956567 : Blo 1955435 1956567 := bstep (se 1 (by rfl) ⟨1467425, by rfl⟩ : syracuseStep 1956567 = 2934851) B2934851
theorem B4952573 : Blo 1955435 4952573 := bbase (se 3 (by rfl) ⟨928607, by rfl⟩ : syracuseStep 4952573 = 1857215) (by norm_num)
theorem B3301715 : Blo 1955435 3301715 := bstep (se 1 (by rfl) ⟨2476286, by rfl⟩ : syracuseStep 3301715 = 4952573) B4952573
theorem B2201143 : Blo 1955435 2201143 := bstep (se 1 (by rfl) ⟨1650857, by rfl⟩ : syracuseStep 2201143 = 3301715) B3301715
theorem B2934857 : Blo 1955435 2934857 := bstep (se 2 (by rfl) ⟨1100571, by rfl⟩ : syracuseStep 2934857 = 2201143) B2201143
theorem B1956571 : Blo 1955435 1956571 := bstep (se 1 (by rfl) ⟨1467428, by rfl⟩ : syracuseStep 1956571 = 2934857) B2934857
theorem B3714437 : Blo 1955435 3714437 := bbase (se 4 (by rfl) ⟨348228, by rfl⟩ : syracuseStep 3714437 = 696457) (by norm_num)
theorem B9905165 : Blo 1955435 9905165 := bstep (se 3 (by rfl) ⟨1857218, by rfl⟩ : syracuseStep 9905165 = 3714437) B3714437
theorem B6603443 : Blo 1955435 6603443 := bstep (se 1 (by rfl) ⟨4952582, by rfl⟩ : syracuseStep 6603443 = 9905165) B9905165
theorem B4402295 : Blo 1955435 4402295 := bstep (se 1 (by rfl) ⟨3301721, by rfl⟩ : syracuseStep 4402295 = 6603443) B6603443
theorem B2934863 : Blo 1955435 2934863 := bstep (se 1 (by rfl) ⟨2201147, by rfl⟩ : syracuseStep 2934863 = 4402295) B4402295
theorem B1956575 : Blo 1955435 1956575 := bstep (se 1 (by rfl) ⟨1467431, by rfl⟩ : syracuseStep 1956575 = 2934863) B2934863
theorem B2934869 : Blo 1955435 2934869 := bbase (se 8 (by rfl) ⟨17196, by rfl⟩ : syracuseStep 2934869 = 34393) (by norm_num)
theorem B1956579 : Blo 1955435 1956579 := bstep (se 1 (by rfl) ⟨1467434, by rfl⟩ : syracuseStep 1956579 = 2934869) B2934869
theorem B16943093 : Blo 1955435 16943093 := bbase (se 5 (by rfl) ⟨794207, by rfl⟩ : syracuseStep 16943093 = 1588415) (by norm_num)
theorem B11295395 : Blo 1955435 11295395 := bstep (se 1 (by rfl) ⟨8471546, by rfl⟩ : syracuseStep 11295395 = 16943093) B16943093
theorem B7530263 : Blo 1955435 7530263 := bstep (se 1 (by rfl) ⟨5647697, by rfl⟩ : syracuseStep 7530263 = 11295395) B11295395
theorem B5020175 : Blo 1955435 5020175 := bstep (se 1 (by rfl) ⟨3765131, by rfl⟩ : syracuseStep 5020175 = 7530263) B7530263
theorem B13387133 : Blo 1955435 13387133 := bstep (se 3 (by rfl) ⟨2510087, by rfl⟩ : syracuseStep 13387133 = 5020175) B5020175
theorem B8924755 : Blo 1955435 8924755 := bstep (se 1 (by rfl) ⟨6693566, by rfl⟩ : syracuseStep 8924755 = 13387133) B13387133
theorem B11899673 : Blo 1955435 11899673 := bstep (se 2 (by rfl) ⟨4462377, by rfl⟩ : syracuseStep 11899673 = 8924755) B8924755
theorem B7933115 : Blo 1955435 7933115 := bstep (se 1 (by rfl) ⟨5949836, by rfl⟩ : syracuseStep 7933115 = 11899673) B11899673
theorem B5288743 : Blo 1955435 5288743 := bstep (se 1 (by rfl) ⟨3966557, by rfl⟩ : syracuseStep 5288743 = 7933115) B7933115
theorem B28206629 : Blo 1955435 28206629 := bstep (se 4 (by rfl) ⟨2644371, by rfl⟩ : syracuseStep 28206629 = 5288743) B5288743
theorem B18804419 : Blo 1955435 18804419 := bstep (se 1 (by rfl) ⟨14103314, by rfl⟩ : syracuseStep 18804419 = 28206629) B28206629
theorem B12536279 : Blo 1955435 12536279 := bstep (se 1 (by rfl) ⟨9402209, by rfl⟩ : syracuseStep 12536279 = 18804419) B18804419
theorem B8357519 : Blo 1955435 8357519 := bstep (se 1 (by rfl) ⟨6268139, by rfl⟩ : syracuseStep 8357519 = 12536279) B12536279
theorem B5571679 : Blo 1955435 5571679 := bstep (se 1 (by rfl) ⟨4178759, by rfl⟩ : syracuseStep 5571679 = 8357519) B8357519
theorem B7428905 : Blo 1955435 7428905 := bstep (se 2 (by rfl) ⟨2785839, by rfl⟩ : syracuseStep 7428905 = 5571679) B5571679
theorem B4952603 : Blo 1955435 4952603 := bstep (se 1 (by rfl) ⟨3714452, by rfl⟩ : syracuseStep 4952603 = 7428905) B7428905
theorem B3301735 : Blo 1955435 3301735 := bstep (se 1 (by rfl) ⟨2476301, by rfl⟩ : syracuseStep 3301735 = 4952603) B4952603
theorem B4402313 : Blo 1955435 4402313 := bstep (se 2 (by rfl) ⟨1650867, by rfl⟩ : syracuseStep 4402313 = 3301735) B3301735
theorem B2934875 : Blo 1955435 2934875 := bstep (se 1 (by rfl) ⟨2201156, by rfl⟩ : syracuseStep 2934875 = 4402313) B4402313
theorem B1956583 : Blo 1955435 1956583 := bstep (se 1 (by rfl) ⟨1467437, by rfl⟩ : syracuseStep 1956583 = 2934875) B2934875
theorem B2201161 : Blo 1955435 2201161 := bbase (se 2 (by rfl) ⟨825435, by rfl⟩ : syracuseStep 2201161 = 1650871) (by norm_num)
theorem B2934881 : Blo 1955435 2934881 := bstep (se 2 (by rfl) ⟨1100580, by rfl⟩ : syracuseStep 2934881 = 2201161) B2201161
theorem B1956587 : Blo 1955435 1956587 := bstep (se 1 (by rfl) ⟨1467440, by rfl⟩ : syracuseStep 1956587 = 2934881) B2934881
theorem B15866293 : Blo 1955435 15866293 := bbase (se 5 (by rfl) ⟨743732, by rfl⟩ : syracuseStep 15866293 = 1487465) (by norm_num)
theorem B21155057 : Blo 1955435 21155057 := bstep (se 2 (by rfl) ⟨7933146, by rfl⟩ : syracuseStep 21155057 = 15866293) B15866293
theorem B14103371 : Blo 1955435 14103371 := bstep (se 1 (by rfl) ⟨10577528, by rfl⟩ : syracuseStep 14103371 = 21155057) B21155057
theorem B9402247 : Blo 1955435 9402247 := bstep (se 1 (by rfl) ⟨7051685, by rfl⟩ : syracuseStep 9402247 = 14103371) B14103371
theorem B12536329 : Blo 1955435 12536329 := bstep (se 2 (by rfl) ⟨4701123, by rfl⟩ : syracuseStep 12536329 = 9402247) B9402247
theorem B16715105 : Blo 1955435 16715105 := bstep (se 2 (by rfl) ⟨6268164, by rfl⟩ : syracuseStep 16715105 = 12536329) B12536329
theorem B11143403 : Blo 1955435 11143403 := bstep (se 1 (by rfl) ⟨8357552, by rfl⟩ : syracuseStep 11143403 = 16715105) B16715105
theorem B7428935 : Blo 1955435 7428935 := bstep (se 1 (by rfl) ⟨5571701, by rfl⟩ : syracuseStep 7428935 = 11143403) B11143403
theorem B4952623 : Blo 1955435 4952623 := bstep (se 1 (by rfl) ⟨3714467, by rfl⟩ : syracuseStep 4952623 = 7428935) B7428935
theorem B6603497 : Blo 1955435 6603497 := bstep (se 2 (by rfl) ⟨2476311, by rfl⟩ : syracuseStep 6603497 = 4952623) B4952623
theorem B4402331 : Blo 1955435 4402331 := bstep (se 1 (by rfl) ⟨3301748, by rfl⟩ : syracuseStep 4402331 = 6603497) B6603497
theorem B2934887 : Blo 1955435 2934887 := bstep (se 1 (by rfl) ⟨2201165, by rfl⟩ : syracuseStep 2934887 = 4402331) B4402331
theorem B1956591 : Blo 1955435 1956591 := bstep (se 1 (by rfl) ⟨1467443, by rfl⟩ : syracuseStep 1956591 = 2934887) B2934887
theorem B2934893 : Blo 1955435 2934893 := bbase (se 3 (by rfl) ⟨550292, by rfl⟩ : syracuseStep 2934893 = 1100585) (by norm_num)
theorem B1956595 : Blo 1955435 1956595 := bstep (se 1 (by rfl) ⟨1467446, by rfl⟩ : syracuseStep 1956595 = 2934893) B2934893
theorem B4402349 : Blo 1955435 4402349 := bbase (se 3 (by rfl) ⟨825440, by rfl⟩ : syracuseStep 4402349 = 1650881) (by norm_num)
theorem B2934899 : Blo 1955435 2934899 := bstep (se 1 (by rfl) ⟨2201174, by rfl⟩ : syracuseStep 2934899 = 4402349) B4402349
theorem B1956599 : Blo 1955435 1956599 := bstep (se 1 (by rfl) ⟨1467449, by rfl⟩ : syracuseStep 1956599 = 2934899) B2934899
theorem B2350577 : Blo 1955435 2350577 := bbase (se 2 (by rfl) ⟨881466, by rfl⟩ : syracuseStep 2350577 = 1762933) (by norm_num)
theorem B6268205 : Blo 1955435 6268205 := bstep (se 3 (by rfl) ⟨1175288, by rfl⟩ : syracuseStep 6268205 = 2350577) B2350577
theorem B4178803 : Blo 1955435 4178803 := bstep (se 1 (by rfl) ⟨3134102, by rfl⟩ : syracuseStep 4178803 = 6268205) B6268205
theorem B5571737 : Blo 1955435 5571737 := bstep (se 2 (by rfl) ⟨2089401, by rfl⟩ : syracuseStep 5571737 = 4178803) B4178803
theorem B3714491 : Blo 1955435 3714491 := bstep (se 1 (by rfl) ⟨2785868, by rfl⟩ : syracuseStep 3714491 = 5571737) B5571737
theorem B2476327 : Blo 1955435 2476327 := bstep (se 1 (by rfl) ⟨1857245, by rfl⟩ : syracuseStep 2476327 = 3714491) B3714491
theorem B3301769 : Blo 1955435 3301769 := bstep (se 2 (by rfl) ⟨1238163, by rfl⟩ : syracuseStep 3301769 = 2476327) B2476327
theorem B2201179 : Blo 1955435 2201179 := bstep (se 1 (by rfl) ⟨1650884, by rfl⟩ : syracuseStep 2201179 = 3301769) B3301769
theorem B2934905 : Blo 1955435 2934905 := bstep (se 2 (by rfl) ⟨1100589, by rfl⟩ : syracuseStep 2934905 = 2201179) B2201179
theorem B1956603 : Blo 1955435 1956603 := bstep (se 1 (by rfl) ⟨1467452, by rfl⟩ : syracuseStep 1956603 = 2934905) B2934905
theorem B5360965 : Blo 1955435 5360965 := bbase (se 4 (by rfl) ⟨502590, by rfl⟩ : syracuseStep 5360965 = 1005181) (by norm_num)
theorem B28591813 : Blo 1955435 28591813 := bstep (se 4 (by rfl) ⟨2680482, by rfl⟩ : syracuseStep 28591813 = 5360965) B5360965
theorem B38122417 : Blo 1955435 38122417 := bstep (se 2 (by rfl) ⟨14295906, by rfl⟩ : syracuseStep 38122417 = 28591813) B28591813
theorem B50829889 : Blo 1955435 50829889 := bstep (se 2 (by rfl) ⟨19061208, by rfl⟩ : syracuseStep 50829889 = 38122417) B38122417
theorem B67773185 : Blo 1955435 67773185 := bstep (se 2 (by rfl) ⟨25414944, by rfl⟩ : syracuseStep 67773185 = 50829889) B50829889
theorem B45182123 : Blo 1955435 45182123 := bstep (se 1 (by rfl) ⟨33886592, by rfl⟩ : syracuseStep 45182123 = 67773185) B67773185
theorem B30121415 : Blo 1955435 30121415 := bstep (se 1 (by rfl) ⟨22591061, by rfl⟩ : syracuseStep 30121415 = 45182123) B45182123
theorem B20080943 : Blo 1955435 20080943 := bstep (se 1 (by rfl) ⟨15060707, by rfl⟩ : syracuseStep 20080943 = 30121415) B30121415
theorem B13387295 : Blo 1955435 13387295 := bstep (se 1 (by rfl) ⟨10040471, by rfl⟩ : syracuseStep 13387295 = 20080943) B20080943
theorem B8924863 : Blo 1955435 8924863 := bstep (se 1 (by rfl) ⟨6693647, by rfl⟩ : syracuseStep 8924863 = 13387295) B13387295
theorem B11899817 : Blo 1955435 11899817 := bstep (se 2 (by rfl) ⟨4462431, by rfl⟩ : syracuseStep 11899817 = 8924863) B8924863
theorem B7933211 : Blo 1955435 7933211 := bstep (se 1 (by rfl) ⟨5949908, by rfl⟩ : syracuseStep 7933211 = 11899817) B11899817
theorem B5288807 : Blo 1955435 5288807 := bstep (se 1 (by rfl) ⟨3966605, by rfl⟩ : syracuseStep 5288807 = 7933211) B7933211
theorem B14103485 : Blo 1955435 14103485 := bstep (se 3 (by rfl) ⟨2644403, by rfl⟩ : syracuseStep 14103485 = 5288807) B5288807
theorem B9402323 : Blo 1955435 9402323 := bstep (se 1 (by rfl) ⟨7051742, by rfl⟩ : syracuseStep 9402323 = 14103485) B14103485
theorem B25072861 : Blo 1955435 25072861 := bstep (se 3 (by rfl) ⟨4701161, by rfl⟩ : syracuseStep 25072861 = 9402323) B9402323
theorem B33430481 : Blo 1955435 33430481 := bstep (se 2 (by rfl) ⟨12536430, by rfl⟩ : syracuseStep 33430481 = 25072861) B25072861
theorem B22286987 : Blo 1955435 22286987 := bstep (se 1 (by rfl) ⟨16715240, by rfl⟩ : syracuseStep 22286987 = 33430481) B33430481
theorem B14857991 : Blo 1955435 14857991 := bstep (se 1 (by rfl) ⟨11143493, by rfl⟩ : syracuseStep 14857991 = 22286987) B22286987
theorem B9905327 : Blo 1955435 9905327 := bstep (se 1 (by rfl) ⟨7428995, by rfl⟩ : syracuseStep 9905327 = 14857991) B14857991
theorem B6603551 : Blo 1955435 6603551 := bstep (se 1 (by rfl) ⟨4952663, by rfl⟩ : syracuseStep 6603551 = 9905327) B9905327
theorem B4402367 : Blo 1955435 4402367 := bstep (se 1 (by rfl) ⟨3301775, by rfl⟩ : syracuseStep 4402367 = 6603551) B6603551
theorem B2934911 : Blo 1955435 2934911 := bstep (se 1 (by rfl) ⟨2201183, by rfl⟩ : syracuseStep 2934911 = 4402367) B4402367
theorem B1956607 : Blo 1955435 1956607 := bstep (se 1 (by rfl) ⟨1467455, by rfl⟩ : syracuseStep 1956607 = 2934911) B2934911
theorem B2934917 : Blo 1955435 2934917 := bbase (se 4 (by rfl) ⟨275148, by rfl⟩ : syracuseStep 2934917 = 550297) (by norm_num)
theorem B1956611 : Blo 1955435 1956611 := bstep (se 1 (by rfl) ⟨1467458, by rfl⟩ : syracuseStep 1956611 = 2934917) B2934917
theorem B3301789 : Blo 1955435 3301789 := bbase (se 3 (by rfl) ⟨619085, by rfl⟩ : syracuseStep 3301789 = 1238171) (by norm_num)
theorem B4402385 : Blo 1955435 4402385 := bstep (se 2 (by rfl) ⟨1650894, by rfl⟩ : syracuseStep 4402385 = 3301789) B3301789
theorem B2934923 : Blo 1955435 2934923 := bstep (se 1 (by rfl) ⟨2201192, by rfl⟩ : syracuseStep 2934923 = 4402385) B4402385
theorem B1956615 : Blo 1955435 1956615 := bstep (se 1 (by rfl) ⟨1467461, by rfl⟩ : syracuseStep 1956615 = 2934923) B2934923
theorem B2201197 : Blo 1955435 2201197 := bbase (se 3 (by rfl) ⟨412724, by rfl⟩ : syracuseStep 2201197 = 825449) (by norm_num)
theorem B2934929 : Blo 1955435 2934929 := bstep (se 2 (by rfl) ⟨1100598, by rfl⟩ : syracuseStep 2934929 = 2201197) B2201197
theorem B1956619 : Blo 1955435 1956619 := bstep (se 1 (by rfl) ⟨1467464, by rfl⟩ : syracuseStep 1956619 = 2934929) B2934929
theorem B6603605 : Blo 1955435 6603605 := bbase (se 9 (by rfl) ⟨19346, by rfl⟩ : syracuseStep 6603605 = 38693) (by norm_num)
theorem B4402403 : Blo 1955435 4402403 := bstep (se 1 (by rfl) ⟨3301802, by rfl⟩ : syracuseStep 4402403 = 6603605) B6603605
theorem B2934935 : Blo 1955435 2934935 := bstep (se 1 (by rfl) ⟨2201201, by rfl⟩ : syracuseStep 2934935 = 4402403) B4402403
theorem B1956623 : Blo 1955435 1956623 := bstep (se 1 (by rfl) ⟨1467467, by rfl⟩ : syracuseStep 1956623 = 2934935) B2934935
theorem B2934941 : Blo 1955435 2934941 := bbase (se 3 (by rfl) ⟨550301, by rfl⟩ : syracuseStep 2934941 = 1100603) (by norm_num)
theorem B1956627 : Blo 1955435 1956627 := bstep (se 1 (by rfl) ⟨1467470, by rfl⟩ : syracuseStep 1956627 = 2934941) B2934941
theorem B4402421 : Blo 1955435 4402421 := bbase (se 5 (by rfl) ⟨206363, by rfl⟩ : syracuseStep 4402421 = 412727) (by norm_num)
theorem B2934947 : Blo 1955435 2934947 := bstep (se 1 (by rfl) ⟨2201210, by rfl⟩ : syracuseStep 2934947 = 4402421) B4402421
theorem B1956631 : Blo 1955435 1956631 := bstep (se 1 (by rfl) ⟨1467473, by rfl⟩ : syracuseStep 1956631 = 2934947) B2934947
theorem B2415193 : Blo 1955435 2415193 := bbase (se 2 (by rfl) ⟨905697, by rfl⟩ : syracuseStep 2415193 = 1811395) (by norm_num)
theorem B12881029 : Blo 1955435 12881029 := bstep (se 4 (by rfl) ⟨1207596, by rfl⟩ : syracuseStep 12881029 = 2415193) B2415193
theorem B17174705 : Blo 1955435 17174705 := bstep (se 2 (by rfl) ⟨6440514, by rfl⟩ : syracuseStep 17174705 = 12881029) B12881029
theorem B183196853 : Blo 1955435 183196853 := bstep (se 5 (by rfl) ⟨8587352, by rfl⟩ : syracuseStep 183196853 = 17174705) B17174705
theorem B122131235 : Blo 1955435 122131235 := bstep (se 1 (by rfl) ⟨91598426, by rfl⟩ : syracuseStep 122131235 = 183196853) B183196853
theorem B81420823 : Blo 1955435 81420823 := bstep (se 1 (by rfl) ⟨61065617, by rfl⟩ : syracuseStep 81420823 = 122131235) B122131235
theorem B108561097 : Blo 1955435 108561097 := bstep (se 2 (by rfl) ⟨40710411, by rfl⟩ : syracuseStep 108561097 = 81420823) B81420823
theorem B144748129 : Blo 1955435 144748129 := bstep (se 2 (by rfl) ⟨54280548, by rfl⟩ : syracuseStep 144748129 = 108561097) B108561097
theorem B192997505 : Blo 1955435 192997505 := bstep (se 2 (by rfl) ⟨72374064, by rfl⟩ : syracuseStep 192997505 = 144748129) B144748129
theorem B514660013 : Blo 1955435 514660013 := bstep (se 3 (by rfl) ⟨96498752, by rfl⟩ : syracuseStep 514660013 = 192997505) B192997505
theorem B343106675 : Blo 1955435 343106675 := bstep (se 1 (by rfl) ⟨257330006, by rfl⟩ : syracuseStep 343106675 = 514660013) B514660013
theorem B228737783 : Blo 1955435 228737783 := bstep (se 1 (by rfl) ⟨171553337, by rfl⟩ : syracuseStep 228737783 = 343106675) B343106675
theorem B152491855 : Blo 1955435 152491855 := bstep (se 1 (by rfl) ⟨114368891, by rfl⟩ : syracuseStep 152491855 = 228737783) B228737783
theorem B203322473 : Blo 1955435 203322473 := bstep (se 2 (by rfl) ⟨76245927, by rfl⟩ : syracuseStep 203322473 = 152491855) B152491855
theorem B135548315 : Blo 1955435 135548315 := bstep (se 1 (by rfl) ⟨101661236, by rfl⟩ : syracuseStep 135548315 = 203322473) B203322473
theorem B90365543 : Blo 1955435 90365543 := bstep (se 1 (by rfl) ⟨67774157, by rfl⟩ : syracuseStep 90365543 = 135548315) B135548315
theorem B60243695 : Blo 1955435 60243695 := bstep (se 1 (by rfl) ⟨45182771, by rfl⟩ : syracuseStep 60243695 = 90365543) B90365543
theorem B40162463 : Blo 1955435 40162463 := bstep (se 1 (by rfl) ⟨30121847, by rfl⟩ : syracuseStep 40162463 = 60243695) B60243695
theorem B26774975 : Blo 1955435 26774975 := bstep (se 1 (by rfl) ⟨20081231, by rfl⟩ : syracuseStep 26774975 = 40162463) B40162463
theorem B17849983 : Blo 1955435 17849983 := bstep (se 1 (by rfl) ⟨13387487, by rfl⟩ : syracuseStep 17849983 = 26774975) B26774975
theorem B23799977 : Blo 1955435 23799977 := bstep (se 2 (by rfl) ⟨8924991, by rfl⟩ : syracuseStep 23799977 = 17849983) B17849983
theorem B15866651 : Blo 1955435 15866651 := bstep (se 1 (by rfl) ⟨11899988, by rfl⟩ : syracuseStep 15866651 = 23799977) B23799977
theorem B42311069 : Blo 1955435 42311069 := bstep (se 3 (by rfl) ⟨7933325, by rfl⟩ : syracuseStep 42311069 = 15866651) B15866651
theorem B28207379 : Blo 1955435 28207379 := bstep (se 1 (by rfl) ⟨21155534, by rfl⟩ : syracuseStep 28207379 = 42311069) B42311069
theorem B18804919 : Blo 1955435 18804919 := bstep (se 1 (by rfl) ⟨14103689, by rfl⟩ : syracuseStep 18804919 = 28207379) B28207379
theorem B25073225 : Blo 1955435 25073225 := bstep (se 2 (by rfl) ⟨9402459, by rfl⟩ : syracuseStep 25073225 = 18804919) B18804919
theorem B16715483 : Blo 1955435 16715483 := bstep (se 1 (by rfl) ⟨12536612, by rfl⟩ : syracuseStep 16715483 = 25073225) B25073225
theorem B11143655 : Blo 1955435 11143655 := bstep (se 1 (by rfl) ⟨8357741, by rfl⟩ : syracuseStep 11143655 = 16715483) B16715483
theorem B7429103 : Blo 1955435 7429103 := bstep (se 1 (by rfl) ⟨5571827, by rfl⟩ : syracuseStep 7429103 = 11143655) B11143655
theorem B4952735 : Blo 1955435 4952735 := bstep (se 1 (by rfl) ⟨3714551, by rfl⟩ : syracuseStep 4952735 = 7429103) B7429103
theorem B3301823 : Blo 1955435 3301823 := bstep (se 1 (by rfl) ⟨2476367, by rfl⟩ : syracuseStep 3301823 = 4952735) B4952735
theorem B2201215 : Blo 1955435 2201215 := bstep (se 1 (by rfl) ⟨1650911, by rfl⟩ : syracuseStep 2201215 = 3301823) B3301823
theorem B2934953 : Blo 1955435 2934953 := bstep (se 2 (by rfl) ⟨1100607, by rfl⟩ : syracuseStep 2934953 = 2201215) B2201215
theorem B1956635 : Blo 1955435 1956635 := bstep (se 1 (by rfl) ⟨1467476, by rfl⟩ : syracuseStep 1956635 = 2934953) B2934953
theorem B18093557 : Blo 1955435 18093557 := bbase (se 5 (by rfl) ⟨848135, by rfl⟩ : syracuseStep 18093557 = 1696271) (by norm_num)
theorem B12062371 : Blo 1955435 12062371 := bstep (se 1 (by rfl) ⟨9046778, by rfl⟩ : syracuseStep 12062371 = 18093557) B18093557
theorem B16083161 : Blo 1955435 16083161 := bstep (se 2 (by rfl) ⟨6031185, by rfl⟩ : syracuseStep 16083161 = 12062371) B12062371
theorem B10722107 : Blo 1955435 10722107 := bstep (se 1 (by rfl) ⟨8041580, by rfl⟩ : syracuseStep 10722107 = 16083161) B16083161
theorem B7148071 : Blo 1955435 7148071 := bstep (se 1 (by rfl) ⟨5361053, by rfl⟩ : syracuseStep 7148071 = 10722107) B10722107
theorem B38123045 : Blo 1955435 38123045 := bstep (se 4 (by rfl) ⟨3574035, by rfl⟩ : syracuseStep 38123045 = 7148071) B7148071
theorem B25415363 : Blo 1955435 25415363 := bstep (se 1 (by rfl) ⟨19061522, by rfl⟩ : syracuseStep 25415363 = 38123045) B38123045
theorem B16943575 : Blo 1955435 16943575 := bstep (se 1 (by rfl) ⟨12707681, by rfl⟩ : syracuseStep 16943575 = 25415363) B25415363
theorem B22591433 : Blo 1955435 22591433 := bstep (se 2 (by rfl) ⟨8471787, by rfl⟩ : syracuseStep 22591433 = 16943575) B16943575
theorem B60243821 : Blo 1955435 60243821 := bstep (se 3 (by rfl) ⟨11295716, by rfl⟩ : syracuseStep 60243821 = 22591433) B22591433
theorem B40162547 : Blo 1955435 40162547 := bstep (se 1 (by rfl) ⟨30121910, by rfl⟩ : syracuseStep 40162547 = 60243821) B60243821
theorem B26775031 : Blo 1955435 26775031 := bstep (se 1 (by rfl) ⟨20081273, by rfl⟩ : syracuseStep 26775031 = 40162547) B40162547
theorem B35700041 : Blo 1955435 35700041 := bstep (se 2 (by rfl) ⟨13387515, by rfl⟩ : syracuseStep 35700041 = 26775031) B26775031
theorem B23800027 : Blo 1955435 23800027 := bstep (se 1 (by rfl) ⟨17850020, by rfl⟩ : syracuseStep 23800027 = 35700041) B35700041
theorem B31733369 : Blo 1955435 31733369 := bstep (se 2 (by rfl) ⟨11900013, by rfl⟩ : syracuseStep 31733369 = 23800027) B23800027
theorem B21155579 : Blo 1955435 21155579 := bstep (se 1 (by rfl) ⟨15866684, by rfl⟩ : syracuseStep 21155579 = 31733369) B31733369
theorem B14103719 : Blo 1955435 14103719 := bstep (se 1 (by rfl) ⟨10577789, by rfl⟩ : syracuseStep 14103719 = 21155579) B21155579
theorem B9402479 : Blo 1955435 9402479 := bstep (se 1 (by rfl) ⟨7051859, by rfl⟩ : syracuseStep 9402479 = 14103719) B14103719
theorem B6268319 : Blo 1955435 6268319 := bstep (se 1 (by rfl) ⟨4701239, by rfl⟩ : syracuseStep 6268319 = 9402479) B9402479
theorem B4178879 : Blo 1955435 4178879 := bstep (se 1 (by rfl) ⟨3134159, by rfl⟩ : syracuseStep 4178879 = 6268319) B6268319
theorem B2785919 : Blo 1955435 2785919 := bstep (se 1 (by rfl) ⟨2089439, by rfl⟩ : syracuseStep 2785919 = 4178879) B4178879
theorem B7429117 : Blo 1955435 7429117 := bstep (se 3 (by rfl) ⟨1392959, by rfl⟩ : syracuseStep 7429117 = 2785919) B2785919
theorem B9905489 : Blo 1955435 9905489 := bstep (se 2 (by rfl) ⟨3714558, by rfl⟩ : syracuseStep 9905489 = 7429117) B7429117
theorem B6603659 : Blo 1955435 6603659 := bstep (se 1 (by rfl) ⟨4952744, by rfl⟩ : syracuseStep 6603659 = 9905489) B9905489
theorem B4402439 : Blo 1955435 4402439 := bstep (se 1 (by rfl) ⟨3301829, by rfl⟩ : syracuseStep 4402439 = 6603659) B6603659
theorem B2934959 : Blo 1955435 2934959 := bstep (se 1 (by rfl) ⟨2201219, by rfl⟩ : syracuseStep 2934959 = 4402439) B4402439
theorem B1956639 : Blo 1955435 1956639 := bstep (se 1 (by rfl) ⟨1467479, by rfl⟩ : syracuseStep 1956639 = 2934959) B2934959
theorem B2934965 : Blo 1955435 2934965 := bbase (se 5 (by rfl) ⟨137576, by rfl⟩ : syracuseStep 2934965 = 275153) (by norm_num)
theorem B1956643 : Blo 1955435 1956643 := bstep (se 1 (by rfl) ⟨1467482, by rfl⟩ : syracuseStep 1956643 = 2934965) B2934965
theorem B4952765 : Blo 1955435 4952765 := bbase (se 3 (by rfl) ⟨928643, by rfl⟩ : syracuseStep 4952765 = 1857287) (by norm_num)
theorem B3301843 : Blo 1955435 3301843 := bstep (se 1 (by rfl) ⟨2476382, by rfl⟩ : syracuseStep 3301843 = 4952765) B4952765
theorem B4402457 : Blo 1955435 4402457 := bstep (se 2 (by rfl) ⟨1650921, by rfl⟩ : syracuseStep 4402457 = 3301843) B3301843
theorem B2934971 : Blo 1955435 2934971 := bstep (se 1 (by rfl) ⟨2201228, by rfl⟩ : syracuseStep 2934971 = 4402457) B4402457
theorem B1956647 : Blo 1955435 1956647 := bstep (se 1 (by rfl) ⟨1467485, by rfl⟩ : syracuseStep 1956647 = 2934971) B2934971
theorem B2201233 : Blo 1955435 2201233 := bbase (se 2 (by rfl) ⟨825462, by rfl⟩ : syracuseStep 2201233 = 1650925) (by norm_num)
theorem B2934977 : Blo 1955435 2934977 := bstep (se 2 (by rfl) ⟨1100616, by rfl⟩ : syracuseStep 2934977 = 2201233) B2201233
theorem B1956651 : Blo 1955435 1956651 := bstep (se 1 (by rfl) ⟨1467488, by rfl⟩ : syracuseStep 1956651 = 2934977) B2934977
theorem B3714589 : Blo 1955435 3714589 := bbase (se 3 (by rfl) ⟨696485, by rfl⟩ : syracuseStep 3714589 = 1392971) (by norm_num)
theorem B4952785 : Blo 1955435 4952785 := bstep (se 2 (by rfl) ⟨1857294, by rfl⟩ : syracuseStep 4952785 = 3714589) B3714589
theorem B6603713 : Blo 1955435 6603713 := bstep (se 2 (by rfl) ⟨2476392, by rfl⟩ : syracuseStep 6603713 = 4952785) B4952785
theorem B4402475 : Blo 1955435 4402475 := bstep (se 1 (by rfl) ⟨3301856, by rfl⟩ : syracuseStep 4402475 = 6603713) B6603713
theorem B2934983 : Blo 1955435 2934983 := bstep (se 1 (by rfl) ⟨2201237, by rfl⟩ : syracuseStep 2934983 = 4402475) B4402475
theorem B1956655 : Blo 1955435 1956655 := bstep (se 1 (by rfl) ⟨1467491, by rfl⟩ : syracuseStep 1956655 = 2934983) B2934983
theorem B2934989 : Blo 1955435 2934989 := bbase (se 3 (by rfl) ⟨550310, by rfl⟩ : syracuseStep 2934989 = 1100621) (by norm_num)
theorem B1956659 : Blo 1955435 1956659 := bstep (se 1 (by rfl) ⟨1467494, by rfl⟩ : syracuseStep 1956659 = 2934989) B2934989
theorem B4402493 : Blo 1955435 4402493 := bbase (se 3 (by rfl) ⟨825467, by rfl⟩ : syracuseStep 4402493 = 1650935) (by norm_num)
theorem B2934995 : Blo 1955435 2934995 := bstep (se 1 (by rfl) ⟨2201246, by rfl⟩ : syracuseStep 2934995 = 4402493) B4402493
theorem B1956663 : Blo 1955435 1956663 := bstep (se 1 (by rfl) ⟨1467497, by rfl⟩ : syracuseStep 1956663 = 2934995) B2934995
theorem B3301877 : Blo 1955435 3301877 := bbase (se 5 (by rfl) ⟨154775, by rfl⟩ : syracuseStep 3301877 = 309551) (by norm_num)
theorem B2201251 : Blo 1955435 2201251 := bstep (se 1 (by rfl) ⟨1650938, by rfl⟩ : syracuseStep 2201251 = 3301877) B3301877
theorem B2935001 : Blo 1955435 2935001 := bstep (se 2 (by rfl) ⟨1100625, by rfl⟩ : syracuseStep 2935001 = 2201251) B2201251
theorem B1956667 : Blo 1955435 1956667 := bstep (se 1 (by rfl) ⟨1467500, by rfl⟩ : syracuseStep 1956667 = 2935001) B2935001
theorem B6268421 : Blo 1955435 6268421 := bbase (se 4 (by rfl) ⟨587664, by rfl⟩ : syracuseStep 6268421 = 1175329) (by norm_num)
theorem B4178947 : Blo 1955435 4178947 := bstep (se 1 (by rfl) ⟨3134210, by rfl⟩ : syracuseStep 4178947 = 6268421) B6268421
theorem B5571929 : Blo 1955435 5571929 := bstep (se 2 (by rfl) ⟨2089473, by rfl⟩ : syracuseStep 5571929 = 4178947) B4178947
theorem B14858477 : Blo 1955435 14858477 := bstep (se 3 (by rfl) ⟨2785964, by rfl⟩ : syracuseStep 14858477 = 5571929) B5571929
theorem B9905651 : Blo 1955435 9905651 := bstep (se 1 (by rfl) ⟨7429238, by rfl⟩ : syracuseStep 9905651 = 14858477) B14858477
theorem B6603767 : Blo 1955435 6603767 := bstep (se 1 (by rfl) ⟨4952825, by rfl⟩ : syracuseStep 6603767 = 9905651) B9905651
theorem B4402511 : Blo 1955435 4402511 := bstep (se 1 (by rfl) ⟨3301883, by rfl⟩ : syracuseStep 4402511 = 6603767) B6603767
theorem B2935007 : Blo 1955435 2935007 := bstep (se 1 (by rfl) ⟨2201255, by rfl⟩ : syracuseStep 2935007 = 4402511) B4402511
theorem B1956671 : Blo 1955435 1956671 := bstep (se 1 (by rfl) ⟨1467503, by rfl⟩ : syracuseStep 1956671 = 2935007) B2935007
theorem B2935013 : Blo 1955435 2935013 := bbase (se 4 (by rfl) ⟨275157, by rfl⟩ : syracuseStep 2935013 = 550315) (by norm_num)
theorem B1956675 : Blo 1955435 1956675 := bstep (se 1 (by rfl) ⟨1467506, by rfl⟩ : syracuseStep 1956675 = 2935013) B2935013
theorem B4178965 : Blo 1955435 4178965 := bbase (se 6 (by rfl) ⟨97944, by rfl⟩ : syracuseStep 4178965 = 195889) (by norm_num)
theorem B5571953 : Blo 1955435 5571953 := bstep (se 2 (by rfl) ⟨2089482, by rfl⟩ : syracuseStep 5571953 = 4178965) B4178965
theorem B3714635 : Blo 1955435 3714635 := bstep (se 1 (by rfl) ⟨2785976, by rfl⟩ : syracuseStep 3714635 = 5571953) B5571953
theorem B2476423 : Blo 1955435 2476423 := bstep (se 1 (by rfl) ⟨1857317, by rfl⟩ : syracuseStep 2476423 = 3714635) B3714635
theorem B3301897 : Blo 1955435 3301897 := bstep (se 2 (by rfl) ⟨1238211, by rfl⟩ : syracuseStep 3301897 = 2476423) B2476423
theorem B4402529 : Blo 1955435 4402529 := bstep (se 2 (by rfl) ⟨1650948, by rfl⟩ : syracuseStep 4402529 = 3301897) B3301897
theorem B2935019 : Blo 1955435 2935019 := bstep (se 1 (by rfl) ⟨2201264, by rfl⟩ : syracuseStep 2935019 = 4402529) B4402529
theorem B1956679 : Blo 1955435 1956679 := bstep (se 1 (by rfl) ⟨1467509, by rfl⟩ : syracuseStep 1956679 = 2935019) B2935019
theorem B2201269 : Blo 1955435 2201269 := bbase (se 5 (by rfl) ⟨103184, by rfl⟩ : syracuseStep 2201269 = 206369) (by norm_num)
theorem B2935025 : Blo 1955435 2935025 := bstep (se 2 (by rfl) ⟨1100634, by rfl⟩ : syracuseStep 2935025 = 2201269) B2201269
theorem B1956683 : Blo 1955435 1956683 := bstep (se 1 (by rfl) ⟨1467512, by rfl⟩ : syracuseStep 1956683 = 2935025) B2935025
theorem B2476433 : Blo 1955435 2476433 := bbase (se 2 (by rfl) ⟨928662, by rfl⟩ : syracuseStep 2476433 = 1857325) (by norm_num)
theorem B6603821 : Blo 1955435 6603821 := bstep (se 3 (by rfl) ⟨1238216, by rfl⟩ : syracuseStep 6603821 = 2476433) B2476433
theorem B4402547 : Blo 1955435 4402547 := bstep (se 1 (by rfl) ⟨3301910, by rfl⟩ : syracuseStep 4402547 = 6603821) B6603821
theorem B2935031 : Blo 1955435 2935031 := bstep (se 1 (by rfl) ⟨2201273, by rfl⟩ : syracuseStep 2935031 = 4402547) B4402547
theorem B1956687 : Blo 1955435 1956687 := bstep (se 1 (by rfl) ⟨1467515, by rfl⟩ : syracuseStep 1956687 = 2935031) B2935031
theorem B2935037 : Blo 1955435 2935037 := bbase (se 3 (by rfl) ⟨550319, by rfl⟩ : syracuseStep 2935037 = 1100639) (by norm_num)
theorem B1956691 : Blo 1955435 1956691 := bstep (se 1 (by rfl) ⟨1467518, by rfl⟩ : syracuseStep 1956691 = 2935037) B2935037
theorem B4402565 : Blo 1955435 4402565 := bbase (se 4 (by rfl) ⟨412740, by rfl⟩ : syracuseStep 4402565 = 825481) (by norm_num)
theorem B2935043 : Blo 1955435 2935043 := bstep (se 1 (by rfl) ⟨2201282, by rfl⟩ : syracuseStep 2935043 = 4402565) B4402565
theorem B1956695 : Blo 1955435 1956695 := bstep (se 1 (by rfl) ⟨1467521, by rfl⟩ : syracuseStep 1956695 = 2935043) B2935043
theorem B2786005 : Blo 1955435 2786005 := bbase (se 7 (by rfl) ⟨32648, by rfl⟩ : syracuseStep 2786005 = 65297) (by norm_num)
theorem B3714673 : Blo 1955435 3714673 := bstep (se 2 (by rfl) ⟨1393002, by rfl⟩ : syracuseStep 3714673 = 2786005) B2786005
theorem B4952897 : Blo 1955435 4952897 := bstep (se 2 (by rfl) ⟨1857336, by rfl⟩ : syracuseStep 4952897 = 3714673) B3714673
theorem B3301931 : Blo 1955435 3301931 := bstep (se 1 (by rfl) ⟨2476448, by rfl⟩ : syracuseStep 3301931 = 4952897) B4952897
theorem B2201287 : Blo 1955435 2201287 := bstep (se 1 (by rfl) ⟨1650965, by rfl⟩ : syracuseStep 2201287 = 3301931) B3301931
theorem B2935049 : Blo 1955435 2935049 := bstep (se 2 (by rfl) ⟨1100643, by rfl⟩ : syracuseStep 2935049 = 2201287) B2201287
theorem B1956699 : Blo 1955435 1956699 := bstep (se 1 (by rfl) ⟨1467524, by rfl⟩ : syracuseStep 1956699 = 2935049) B2935049
theorem B9905813 : Blo 1955435 9905813 := bbase (se 6 (by rfl) ⟨232167, by rfl⟩ : syracuseStep 9905813 = 464335) (by norm_num)
theorem B6603875 : Blo 1955435 6603875 := bstep (se 1 (by rfl) ⟨4952906, by rfl⟩ : syracuseStep 6603875 = 9905813) B9905813
theorem B4402583 : Blo 1955435 4402583 := bstep (se 1 (by rfl) ⟨3301937, by rfl⟩ : syracuseStep 4402583 = 6603875) B6603875
theorem B2935055 : Blo 1955435 2935055 := bstep (se 1 (by rfl) ⟨2201291, by rfl⟩ : syracuseStep 2935055 = 4402583) B4402583
theorem B1956703 : Blo 1955435 1956703 := bstep (se 1 (by rfl) ⟨1467527, by rfl⟩ : syracuseStep 1956703 = 2935055) B2935055
theorem B2935061 : Blo 1955435 2935061 := bbase (se 6 (by rfl) ⟨68790, by rfl⟩ : syracuseStep 2935061 = 137581) (by norm_num)
theorem B1956707 : Blo 1955435 1956707 := bstep (se 1 (by rfl) ⟨1467530, by rfl⟩ : syracuseStep 1956707 = 2935061) B2935061
theorem B25074197 : Blo 1955435 25074197 := bbase (se 6 (by rfl) ⟨587676, by rfl⟩ : syracuseStep 25074197 = 1175353) (by norm_num)
theorem B16716131 : Blo 1955435 16716131 := bstep (se 1 (by rfl) ⟨12537098, by rfl⟩ : syracuseStep 16716131 = 25074197) B25074197
theorem B11144087 : Blo 1955435 11144087 := bstep (se 1 (by rfl) ⟨8358065, by rfl⟩ : syracuseStep 11144087 = 16716131) B16716131
theorem B7429391 : Blo 1955435 7429391 := bstep (se 1 (by rfl) ⟨5572043, by rfl⟩ : syracuseStep 7429391 = 11144087) B11144087
theorem B4952927 : Blo 1955435 4952927 := bstep (se 1 (by rfl) ⟨3714695, by rfl⟩ : syracuseStep 4952927 = 7429391) B7429391
theorem B3301951 : Blo 1955435 3301951 := bstep (se 1 (by rfl) ⟨2476463, by rfl⟩ : syracuseStep 3301951 = 4952927) B4952927
theorem B4402601 : Blo 1955435 4402601 := bstep (se 2 (by rfl) ⟨1650975, by rfl⟩ : syracuseStep 4402601 = 3301951) B3301951
theorem B2935067 : Blo 1955435 2935067 := bstep (se 1 (by rfl) ⟨2201300, by rfl⟩ : syracuseStep 2935067 = 4402601) B4402601
theorem B1956711 : Blo 1955435 1956711 := bstep (se 1 (by rfl) ⟨1467533, by rfl⟩ : syracuseStep 1956711 = 2935067) B2935067
theorem B2201305 : Blo 1955435 2201305 := bbase (se 2 (by rfl) ⟨825489, by rfl⟩ : syracuseStep 2201305 = 1650979) (by norm_num)
theorem B2935073 : Blo 1955435 2935073 := bstep (se 2 (by rfl) ⟨1100652, by rfl⟩ : syracuseStep 2935073 = 2201305) B2201305
theorem B1956715 : Blo 1955435 1956715 := bstep (se 1 (by rfl) ⟨1467536, by rfl⟩ : syracuseStep 1956715 = 2935073) B2935073
theorem B2089525 : Blo 1955435 2089525 := bbase (se 5 (by rfl) ⟨97946, by rfl⟩ : syracuseStep 2089525 = 195893) (by norm_num)
theorem B2786033 : Blo 1955435 2786033 := bstep (se 2 (by rfl) ⟨1044762, by rfl⟩ : syracuseStep 2786033 = 2089525) B2089525
theorem B7429421 : Blo 1955435 7429421 := bstep (se 3 (by rfl) ⟨1393016, by rfl⟩ : syracuseStep 7429421 = 2786033) B2786033
theorem B4952947 : Blo 1955435 4952947 := bstep (se 1 (by rfl) ⟨3714710, by rfl⟩ : syracuseStep 4952947 = 7429421) B7429421
theorem B6603929 : Blo 1955435 6603929 := bstep (se 2 (by rfl) ⟨2476473, by rfl⟩ : syracuseStep 6603929 = 4952947) B4952947
theorem B4402619 : Blo 1955435 4402619 := bstep (se 1 (by rfl) ⟨3301964, by rfl⟩ : syracuseStep 4402619 = 6603929) B6603929
theorem B2935079 : Blo 1955435 2935079 := bstep (se 1 (by rfl) ⟨2201309, by rfl⟩ : syracuseStep 2935079 = 4402619) B4402619
theorem B1956719 : Blo 1955435 1956719 := bstep (se 1 (by rfl) ⟨1467539, by rfl⟩ : syracuseStep 1956719 = 2935079) B2935079
theorem B2935085 : Blo 1955435 2935085 := bbase (se 3 (by rfl) ⟨550328, by rfl⟩ : syracuseStep 2935085 = 1100657) (by norm_num)
theorem B1956723 : Blo 1955435 1956723 := bstep (se 1 (by rfl) ⟨1467542, by rfl⟩ : syracuseStep 1956723 = 2935085) B2935085
theorem B4402637 : Blo 1955435 4402637 := bbase (se 3 (by rfl) ⟨825494, by rfl⟩ : syracuseStep 4402637 = 1650989) (by norm_num)
theorem B2935091 : Blo 1955435 2935091 := bstep (se 1 (by rfl) ⟨2201318, by rfl⟩ : syracuseStep 2935091 = 4402637) B4402637
theorem B1956727 : Blo 1955435 1956727 := bstep (se 1 (by rfl) ⟨1467545, by rfl⟩ : syracuseStep 1956727 = 2935091) B2935091
theorem B2476489 : Blo 1955435 2476489 := bbase (se 2 (by rfl) ⟨928683, by rfl⟩ : syracuseStep 2476489 = 1857367) (by norm_num)
theorem B3301985 : Blo 1955435 3301985 := bstep (se 2 (by rfl) ⟨1238244, by rfl⟩ : syracuseStep 3301985 = 2476489) B2476489
theorem B2201323 : Blo 1955435 2201323 := bstep (se 1 (by rfl) ⟨1650992, by rfl⟩ : syracuseStep 2201323 = 3301985) B3301985
theorem B2935097 : Blo 1955435 2935097 := bstep (se 2 (by rfl) ⟨1100661, by rfl⟩ : syracuseStep 2935097 = 2201323) B2201323
theorem B1956731 : Blo 1955435 1956731 := bstep (se 1 (by rfl) ⟨1467548, by rfl⟩ : syracuseStep 1956731 = 2935097) B2935097
theorem B18805877 : Blo 1955435 18805877 := bbase (se 5 (by rfl) ⟨881525, by rfl⟩ : syracuseStep 18805877 = 1763051) (by norm_num)
theorem B12537251 : Blo 1955435 12537251 := bstep (se 1 (by rfl) ⟨9402938, by rfl⟩ : syracuseStep 12537251 = 18805877) B18805877
theorem B8358167 : Blo 1955435 8358167 := bstep (se 1 (by rfl) ⟨6268625, by rfl⟩ : syracuseStep 8358167 = 12537251) B12537251
theorem B22288445 : Blo 1955435 22288445 := bstep (se 3 (by rfl) ⟨4179083, by rfl⟩ : syracuseStep 22288445 = 8358167) B8358167
theorem B14858963 : Blo 1955435 14858963 := bstep (se 1 (by rfl) ⟨11144222, by rfl⟩ : syracuseStep 14858963 = 22288445) B22288445
theorem B9905975 : Blo 1955435 9905975 := bstep (se 1 (by rfl) ⟨7429481, by rfl⟩ : syracuseStep 9905975 = 14858963) B14858963
theorem B6603983 : Blo 1955435 6603983 := bstep (se 1 (by rfl) ⟨4952987, by rfl⟩ : syracuseStep 6603983 = 9905975) B9905975
theorem B4402655 : Blo 1955435 4402655 := bstep (se 1 (by rfl) ⟨3301991, by rfl⟩ : syracuseStep 4402655 = 6603983) B6603983
theorem B2935103 : Blo 1955435 2935103 := bstep (se 1 (by rfl) ⟨2201327, by rfl⟩ : syracuseStep 2935103 = 4402655) B4402655
theorem B1956735 : Blo 1955435 1956735 := bstep (se 1 (by rfl) ⟨1467551, by rfl⟩ : syracuseStep 1956735 = 2935103) B2935103
theorem B2935109 : Blo 1955435 2935109 := bbase (se 4 (by rfl) ⟨275166, by rfl⟩ : syracuseStep 2935109 = 550333) (by norm_num)
theorem B1956739 : Blo 1955435 1956739 := bstep (se 1 (by rfl) ⟨1467554, by rfl⟩ : syracuseStep 1956739 = 2935109) B2935109
theorem B3302005 : Blo 1955435 3302005 := bbase (se 5 (by rfl) ⟨154781, by rfl⟩ : syracuseStep 3302005 = 309563) (by norm_num)
theorem B4402673 : Blo 1955435 4402673 := bstep (se 2 (by rfl) ⟨1651002, by rfl⟩ : syracuseStep 4402673 = 3302005) B3302005
theorem B2935115 : Blo 1955435 2935115 := bstep (se 1 (by rfl) ⟨2201336, by rfl⟩ : syracuseStep 2935115 = 4402673) B4402673
theorem B1956743 : Blo 1955435 1956743 := bstep (se 1 (by rfl) ⟨1467557, by rfl⟩ : syracuseStep 1956743 = 2935115) B2935115
theorem B2201341 : Blo 1955435 2201341 := bbase (se 3 (by rfl) ⟨412751, by rfl⟩ : syracuseStep 2201341 = 825503) (by norm_num)
theorem B2935121 : Blo 1955435 2935121 := bstep (se 2 (by rfl) ⟨1100670, by rfl⟩ : syracuseStep 2935121 = 2201341) B2201341
theorem B1956747 : Blo 1955435 1956747 := bstep (se 1 (by rfl) ⟨1467560, by rfl⟩ : syracuseStep 1956747 = 2935121) B2935121
theorem B6604037 : Blo 1955435 6604037 := bbase (se 4 (by rfl) ⟨619128, by rfl⟩ : syracuseStep 6604037 = 1238257) (by norm_num)
theorem B4402691 : Blo 1955435 4402691 := bstep (se 1 (by rfl) ⟨3302018, by rfl⟩ : syracuseStep 4402691 = 6604037) B6604037
theorem B2935127 : Blo 1955435 2935127 := bstep (se 1 (by rfl) ⟨2201345, by rfl⟩ : syracuseStep 2935127 = 4402691) B4402691
theorem B1956751 : Blo 1955435 1956751 := bstep (se 1 (by rfl) ⟨1467563, by rfl⟩ : syracuseStep 1956751 = 2935127) B2935127
theorem B2935133 : Blo 1955435 2935133 := bbase (se 3 (by rfl) ⟨550337, by rfl⟩ : syracuseStep 2935133 = 1100675) (by norm_num)
theorem B1956755 : Blo 1955435 1956755 := bstep (se 1 (by rfl) ⟨1467566, by rfl⟩ : syracuseStep 1956755 = 2935133) B2935133
theorem B4402709 : Blo 1955435 4402709 := bbase (se 6 (by rfl) ⟨103188, by rfl⟩ : syracuseStep 4402709 = 206377) (by norm_num)
theorem B2935139 : Blo 1955435 2935139 := bstep (se 1 (by rfl) ⟨2201354, by rfl⟩ : syracuseStep 2935139 = 4402709) B4402709
theorem B1956759 : Blo 1955435 1956759 := bstep (se 1 (by rfl) ⟨1467569, by rfl⟩ : syracuseStep 1956759 = 2935139) B2935139
theorem B7429589 : Blo 1955435 7429589 := bbase (se 7 (by rfl) ⟨87065, by rfl⟩ : syracuseStep 7429589 = 174131) (by norm_num)
theorem B4953059 : Blo 1955435 4953059 := bstep (se 1 (by rfl) ⟨3714794, by rfl⟩ : syracuseStep 4953059 = 7429589) B7429589
theorem B3302039 : Blo 1955435 3302039 := bstep (se 1 (by rfl) ⟨2476529, by rfl⟩ : syracuseStep 3302039 = 4953059) B4953059
theorem B2201359 : Blo 1955435 2201359 := bstep (se 1 (by rfl) ⟨1651019, by rfl⟩ : syracuseStep 2201359 = 3302039) B3302039
theorem B2935145 : Blo 1955435 2935145 := bstep (se 2 (by rfl) ⟨1100679, by rfl⟩ : syracuseStep 2935145 = 2201359) B2201359
theorem B1956763 : Blo 1955435 1956763 := bstep (se 1 (by rfl) ⟨1467572, by rfl⟩ : syracuseStep 1956763 = 2935145) B2935145
theorem B11144405 : Blo 1955435 11144405 := bbase (se 7 (by rfl) ⟨130598, by rfl⟩ : syracuseStep 11144405 = 261197) (by norm_num)
theorem B7429603 : Blo 1955435 7429603 := bstep (se 1 (by rfl) ⟨5572202, by rfl⟩ : syracuseStep 7429603 = 11144405) B11144405
theorem B9906137 : Blo 1955435 9906137 := bstep (se 2 (by rfl) ⟨3714801, by rfl⟩ : syracuseStep 9906137 = 7429603) B7429603
theorem B6604091 : Blo 1955435 6604091 := bstep (se 1 (by rfl) ⟨4953068, by rfl⟩ : syracuseStep 6604091 = 9906137) B9906137
theorem B4402727 : Blo 1955435 4402727 := bstep (se 1 (by rfl) ⟨3302045, by rfl⟩ : syracuseStep 4402727 = 6604091) B6604091
theorem B2935151 : Blo 1955435 2935151 := bstep (se 1 (by rfl) ⟨2201363, by rfl⟩ : syracuseStep 2935151 = 4402727) B4402727
theorem B1956767 : Blo 1955435 1956767 := bstep (se 1 (by rfl) ⟨1467575, by rfl⟩ : syracuseStep 1956767 = 2935151) B2935151
theorem B2935157 : Blo 1955435 2935157 := bbase (se 5 (by rfl) ⟨137585, by rfl⟩ : syracuseStep 2935157 = 275171) (by norm_num)
theorem B1956771 : Blo 1955435 1956771 := bstep (se 1 (by rfl) ⟨1467578, by rfl⟩ : syracuseStep 1956771 = 2935157) B2935157
theorem B2089585 : Blo 1955435 2089585 := bbase (se 2 (by rfl) ⟨783594, by rfl⟩ : syracuseStep 2089585 = 1567189) (by norm_num)
theorem B2786113 : Blo 1955435 2786113 := bstep (se 2 (by rfl) ⟨1044792, by rfl⟩ : syracuseStep 2786113 = 2089585) B2089585
theorem B3714817 : Blo 1955435 3714817 := bstep (se 2 (by rfl) ⟨1393056, by rfl⟩ : syracuseStep 3714817 = 2786113) B2786113
theorem B4953089 : Blo 1955435 4953089 := bstep (se 2 (by rfl) ⟨1857408, by rfl⟩ : syracuseStep 4953089 = 3714817) B3714817
theorem B3302059 : Blo 1955435 3302059 := bstep (se 1 (by rfl) ⟨2476544, by rfl⟩ : syracuseStep 3302059 = 4953089) B4953089
theorem B4402745 : Blo 1955435 4402745 := bstep (se 2 (by rfl) ⟨1651029, by rfl⟩ : syracuseStep 4402745 = 3302059) B3302059
theorem B2935163 : Blo 1955435 2935163 := bstep (se 1 (by rfl) ⟨2201372, by rfl⟩ : syracuseStep 2935163 = 4402745) B4402745
theorem B1956775 : Blo 1955435 1956775 := bstep (se 1 (by rfl) ⟨1467581, by rfl⟩ : syracuseStep 1956775 = 2935163) B2935163
theorem B2201377 : Blo 1955435 2201377 := bbase (se 2 (by rfl) ⟨825516, by rfl⟩ : syracuseStep 2201377 = 1651033) (by norm_num)
theorem B2935169 : Blo 1955435 2935169 := bstep (se 2 (by rfl) ⟨1100688, by rfl⟩ : syracuseStep 2935169 = 2201377) B2201377
theorem B1956779 : Blo 1955435 1956779 := bstep (se 1 (by rfl) ⟨1467584, by rfl⟩ : syracuseStep 1956779 = 2935169) B2935169
theorem B4953109 : Blo 1955435 4953109 := bbase (se 6 (by rfl) ⟨116088, by rfl⟩ : syracuseStep 4953109 = 232177) (by norm_num)
theorem B6604145 : Blo 1955435 6604145 := bstep (se 2 (by rfl) ⟨2476554, by rfl⟩ : syracuseStep 6604145 = 4953109) B4953109
theorem B4402763 : Blo 1955435 4402763 := bstep (se 1 (by rfl) ⟨3302072, by rfl⟩ : syracuseStep 4402763 = 6604145) B6604145
theorem B2935175 : Blo 1955435 2935175 := bstep (se 1 (by rfl) ⟨2201381, by rfl⟩ : syracuseStep 2935175 = 4402763) B4402763
theorem B1956783 : Blo 1955435 1956783 := bstep (se 1 (by rfl) ⟨1467587, by rfl⟩ : syracuseStep 1956783 = 2935175) B2935175
theorem B2935181 : Blo 1955435 2935181 := bbase (se 3 (by rfl) ⟨550346, by rfl⟩ : syracuseStep 2935181 = 1100693) (by norm_num)
theorem B1956787 : Blo 1955435 1956787 := bstep (se 1 (by rfl) ⟨1467590, by rfl⟩ : syracuseStep 1956787 = 2935181) B2935181
theorem B4402781 : Blo 1955435 4402781 := bbase (se 3 (by rfl) ⟨825521, by rfl⟩ : syracuseStep 4402781 = 1651043) (by norm_num)
theorem B2935187 : Blo 1955435 2935187 := bstep (se 1 (by rfl) ⟨2201390, by rfl⟩ : syracuseStep 2935187 = 4402781) B4402781
theorem B1956791 : Blo 1955435 1956791 := bstep (se 1 (by rfl) ⟨1467593, by rfl⟩ : syracuseStep 1956791 = 2935187) B2935187
theorem B3302093 : Blo 1955435 3302093 := bbase (se 3 (by rfl) ⟨619142, by rfl⟩ : syracuseStep 3302093 = 1238285) (by norm_num)
theorem B2201395 : Blo 1955435 2201395 := bstep (se 1 (by rfl) ⟨1651046, by rfl⟩ : syracuseStep 2201395 = 3302093) B3302093
theorem B2935193 : Blo 1955435 2935193 := bstep (se 2 (by rfl) ⟨1100697, by rfl⟩ : syracuseStep 2935193 = 2201395) B2201395
theorem B1956795 : Blo 1955435 1956795 := bstep (se 1 (by rfl) ⟨1467596, by rfl⟩ : syracuseStep 1956795 = 2935193) B2935193
theorem B2510365 : Blo 1955435 2510365 := bbase (se 3 (by rfl) ⟨470693, by rfl⟩ : syracuseStep 2510365 = 941387) (by norm_num)
theorem B3347153 : Blo 1955435 3347153 := bstep (se 2 (by rfl) ⟨1255182, by rfl⟩ : syracuseStep 3347153 = 2510365) B2510365
theorem B2231435 : Blo 1955435 2231435 := bstep (se 1 (by rfl) ⟨1673576, by rfl⟩ : syracuseStep 2231435 = 3347153) B3347153
theorem B5950493 : Blo 1955435 5950493 := bstep (se 3 (by rfl) ⟨1115717, by rfl⟩ : syracuseStep 5950493 = 2231435) B2231435
theorem B3966995 : Blo 1955435 3966995 := bstep (se 1 (by rfl) ⟨2975246, by rfl⟩ : syracuseStep 3966995 = 5950493) B5950493
theorem B10578653 : Blo 1955435 10578653 := bstep (se 3 (by rfl) ⟨1983497, by rfl⟩ : syracuseStep 10578653 = 3966995) B3966995
theorem B7052435 : Blo 1955435 7052435 := bstep (se 1 (by rfl) ⟨5289326, by rfl⟩ : syracuseStep 7052435 = 10578653) B10578653
theorem B4701623 : Blo 1955435 4701623 := bstep (se 1 (by rfl) ⟨3526217, by rfl⟩ : syracuseStep 4701623 = 7052435) B7052435
theorem B12537661 : Blo 1955435 12537661 := bstep (se 3 (by rfl) ⟨2350811, by rfl⟩ : syracuseStep 12537661 = 4701623) B4701623
theorem B16716881 : Blo 1955435 16716881 := bstep (se 2 (by rfl) ⟨6268830, by rfl⟩ : syracuseStep 16716881 = 12537661) B12537661
theorem B11144587 : Blo 1955435 11144587 := bstep (se 1 (by rfl) ⟨8358440, by rfl⟩ : syracuseStep 11144587 = 16716881) B16716881
theorem B14859449 : Blo 1955435 14859449 := bstep (se 2 (by rfl) ⟨5572293, by rfl⟩ : syracuseStep 14859449 = 11144587) B11144587
theorem B9906299 : Blo 1955435 9906299 := bstep (se 1 (by rfl) ⟨7429724, by rfl⟩ : syracuseStep 9906299 = 14859449) B14859449
theorem B6604199 : Blo 1955435 6604199 := bstep (se 1 (by rfl) ⟨4953149, by rfl⟩ : syracuseStep 6604199 = 9906299) B9906299
theorem B4402799 : Blo 1955435 4402799 := bstep (se 1 (by rfl) ⟨3302099, by rfl⟩ : syracuseStep 4402799 = 6604199) B6604199
theorem B2935199 : Blo 1955435 2935199 := bstep (se 1 (by rfl) ⟨2201399, by rfl⟩ : syracuseStep 2935199 = 4402799) B4402799
theorem B1956799 : Blo 1955435 1956799 := bstep (se 1 (by rfl) ⟨1467599, by rfl⟩ : syracuseStep 1956799 = 2935199) B2935199
theorem B2935205 : Blo 1955435 2935205 := bbase (se 4 (by rfl) ⟨275175, by rfl⟩ : syracuseStep 2935205 = 550351) (by norm_num)
theorem B1956803 : Blo 1955435 1956803 := bstep (se 1 (by rfl) ⟨1467602, by rfl⟩ : syracuseStep 1956803 = 2935205) B2935205
theorem B2476585 : Blo 1955435 2476585 := bbase (se 2 (by rfl) ⟨928719, by rfl⟩ : syracuseStep 2476585 = 1857439) (by norm_num)
theorem B3302113 : Blo 1955435 3302113 := bstep (se 2 (by rfl) ⟨1238292, by rfl⟩ : syracuseStep 3302113 = 2476585) B2476585
theorem B4402817 : Blo 1955435 4402817 := bstep (se 2 (by rfl) ⟨1651056, by rfl⟩ : syracuseStep 4402817 = 3302113) B3302113
theorem B2935211 : Blo 1955435 2935211 := bstep (se 1 (by rfl) ⟨2201408, by rfl⟩ : syracuseStep 2935211 = 4402817) B4402817
theorem B1956807 : Blo 1955435 1956807 := bstep (se 1 (by rfl) ⟨1467605, by rfl⟩ : syracuseStep 1956807 = 2935211) B2935211
theorem B2201413 : Blo 1955435 2201413 := bbase (se 4 (by rfl) ⟨206382, by rfl⟩ : syracuseStep 2201413 = 412765) (by norm_num)
theorem B2935217 : Blo 1955435 2935217 := bstep (se 2 (by rfl) ⟨1100706, by rfl⟩ : syracuseStep 2935217 = 2201413) B2201413
theorem B1956811 : Blo 1955435 1956811 := bstep (se 1 (by rfl) ⟨1467608, by rfl⟩ : syracuseStep 1956811 = 2935217) B2935217
theorem B3714893 : Blo 1955435 3714893 := bbase (se 3 (by rfl) ⟨696542, by rfl⟩ : syracuseStep 3714893 = 1393085) (by norm_num)
theorem B2476595 : Blo 1955435 2476595 := bstep (se 1 (by rfl) ⟨1857446, by rfl⟩ : syracuseStep 2476595 = 3714893) B3714893
theorem B6604253 : Blo 1955435 6604253 := bstep (se 3 (by rfl) ⟨1238297, by rfl⟩ : syracuseStep 6604253 = 2476595) B2476595
theorem B4402835 : Blo 1955435 4402835 := bstep (se 1 (by rfl) ⟨3302126, by rfl⟩ : syracuseStep 4402835 = 6604253) B6604253
theorem B2935223 : Blo 1955435 2935223 := bstep (se 1 (by rfl) ⟨2201417, by rfl⟩ : syracuseStep 2935223 = 4402835) B4402835
theorem B1956815 : Blo 1955435 1956815 := bstep (se 1 (by rfl) ⟨1467611, by rfl⟩ : syracuseStep 1956815 = 2935223) B2935223
theorem B2935229 : Blo 1955435 2935229 := bbase (se 3 (by rfl) ⟨550355, by rfl⟩ : syracuseStep 2935229 = 1100711) (by norm_num)
theorem B1956819 : Blo 1955435 1956819 := bstep (se 1 (by rfl) ⟨1467614, by rfl⟩ : syracuseStep 1956819 = 2935229) B2935229
theorem B4402853 : Blo 1955435 4402853 := bbase (se 4 (by rfl) ⟨412767, by rfl⟩ : syracuseStep 4402853 = 825535) (by norm_num)
theorem B2935235 : Blo 1955435 2935235 := bstep (se 1 (by rfl) ⟨2201426, by rfl⟩ : syracuseStep 2935235 = 4402853) B4402853
theorem B1956823 : Blo 1955435 1956823 := bstep (se 1 (by rfl) ⟨1467617, by rfl⟩ : syracuseStep 1956823 = 2935235) B2935235
theorem B4953221 : Blo 1955435 4953221 := bbase (se 4 (by rfl) ⟨464364, by rfl⟩ : syracuseStep 4953221 = 928729) (by norm_num)
theorem B3302147 : Blo 1955435 3302147 := bstep (se 1 (by rfl) ⟨2476610, by rfl⟩ : syracuseStep 3302147 = 4953221) B4953221
theorem B2201431 : Blo 1955435 2201431 := bstep (se 1 (by rfl) ⟨1651073, by rfl⟩ : syracuseStep 2201431 = 3302147) B3302147
theorem B2935241 : Blo 1955435 2935241 := bstep (se 2 (by rfl) ⟨1100715, by rfl⟩ : syracuseStep 2935241 = 2201431) B2201431
theorem B1956827 : Blo 1955435 1956827 := bstep (se 1 (by rfl) ⟨1467620, by rfl⟩ : syracuseStep 1956827 = 2935241) B2935241
theorem B4701701 : Blo 1955435 4701701 := bbase (se 4 (by rfl) ⟨440784, by rfl⟩ : syracuseStep 4701701 = 881569) (by norm_num)
theorem B3134467 : Blo 1955435 3134467 := bstep (se 1 (by rfl) ⟨2350850, by rfl⟩ : syracuseStep 3134467 = 4701701) B4701701
theorem B4179289 : Blo 1955435 4179289 := bstep (se 2 (by rfl) ⟨1567233, by rfl⟩ : syracuseStep 4179289 = 3134467) B3134467
theorem B5572385 : Blo 1955435 5572385 := bstep (se 2 (by rfl) ⟨2089644, by rfl⟩ : syracuseStep 5572385 = 4179289) B4179289
theorem B3714923 : Blo 1955435 3714923 := bstep (se 1 (by rfl) ⟨2786192, by rfl⟩ : syracuseStep 3714923 = 5572385) B5572385
theorem B9906461 : Blo 1955435 9906461 := bstep (se 3 (by rfl) ⟨1857461, by rfl⟩ : syracuseStep 9906461 = 3714923) B3714923
theorem B6604307 : Blo 1955435 6604307 := bstep (se 1 (by rfl) ⟨4953230, by rfl⟩ : syracuseStep 6604307 = 9906461) B9906461
theorem B4402871 : Blo 1955435 4402871 := bstep (se 1 (by rfl) ⟨3302153, by rfl⟩ : syracuseStep 4402871 = 6604307) B6604307
theorem B2935247 : Blo 1955435 2935247 := bstep (se 1 (by rfl) ⟨2201435, by rfl⟩ : syracuseStep 2935247 = 4402871) B4402871
theorem B1956831 : Blo 1955435 1956831 := bstep (se 1 (by rfl) ⟨1467623, by rfl⟩ : syracuseStep 1956831 = 2935247) B2935247
theorem B2935253 : Blo 1955435 2935253 := bbase (se 7 (by rfl) ⟨34397, by rfl⟩ : syracuseStep 2935253 = 68795) (by norm_num)
theorem B1956835 : Blo 1955435 1956835 := bstep (se 1 (by rfl) ⟨1467626, by rfl⟩ : syracuseStep 1956835 = 2935253) B2935253
theorem B7429877 : Blo 1955435 7429877 := bbase (se 5 (by rfl) ⟨348275, by rfl⟩ : syracuseStep 7429877 = 696551) (by norm_num)
theorem B4953251 : Blo 1955435 4953251 := bstep (se 1 (by rfl) ⟨3714938, by rfl⟩ : syracuseStep 4953251 = 7429877) B7429877
theorem B3302167 : Blo 1955435 3302167 := bstep (se 1 (by rfl) ⟨2476625, by rfl⟩ : syracuseStep 3302167 = 4953251) B4953251
theorem B4402889 : Blo 1955435 4402889 := bstep (se 2 (by rfl) ⟨1651083, by rfl⟩ : syracuseStep 4402889 = 3302167) B3302167
theorem B2935259 : Blo 1955435 2935259 := bstep (se 1 (by rfl) ⟨2201444, by rfl⟩ : syracuseStep 2935259 = 4402889) B4402889
theorem B1956839 : Blo 1955435 1956839 := bstep (se 1 (by rfl) ⟨1467629, by rfl⟩ : syracuseStep 1956839 = 2935259) B2935259
theorem B2201449 : Blo 1955435 2201449 := bbase (se 2 (by rfl) ⟨825543, by rfl⟩ : syracuseStep 2201449 = 1651087) (by norm_num)
theorem B2935265 : Blo 1955435 2935265 := bstep (se 2 (by rfl) ⟨1100724, by rfl⟩ : syracuseStep 2935265 = 2201449) B2201449
theorem B1956843 : Blo 1955435 1956843 := bstep (se 1 (by rfl) ⟨1467632, by rfl⟩ : syracuseStep 1956843 = 2935265) B2935265
theorem B3967093 : Blo 1955435 3967093 := bbase (se 5 (by rfl) ⟨185957, by rfl⟩ : syracuseStep 3967093 = 371915) (by norm_num)
theorem B5289457 : Blo 1955435 5289457 := bstep (se 2 (by rfl) ⟨1983546, by rfl⟩ : syracuseStep 5289457 = 3967093) B3967093
theorem B7052609 : Blo 1955435 7052609 := bstep (se 2 (by rfl) ⟨2644728, by rfl⟩ : syracuseStep 7052609 = 5289457) B5289457
theorem B4701739 : Blo 1955435 4701739 := bstep (se 1 (by rfl) ⟨3526304, by rfl⟩ : syracuseStep 4701739 = 7052609) B7052609
theorem B6268985 : Blo 1955435 6268985 := bstep (se 2 (by rfl) ⟨2350869, by rfl⟩ : syracuseStep 6268985 = 4701739) B4701739
theorem B4179323 : Blo 1955435 4179323 := bstep (se 1 (by rfl) ⟨3134492, by rfl⟩ : syracuseStep 4179323 = 6268985) B6268985
theorem B11144861 : Blo 1955435 11144861 := bstep (se 3 (by rfl) ⟨2089661, by rfl⟩ : syracuseStep 11144861 = 4179323) B4179323
theorem B7429907 : Blo 1955435 7429907 := bstep (se 1 (by rfl) ⟨5572430, by rfl⟩ : syracuseStep 7429907 = 11144861) B11144861
theorem B4953271 : Blo 1955435 4953271 := bstep (se 1 (by rfl) ⟨3714953, by rfl⟩ : syracuseStep 4953271 = 7429907) B7429907
theorem B6604361 : Blo 1955435 6604361 := bstep (se 2 (by rfl) ⟨2476635, by rfl⟩ : syracuseStep 6604361 = 4953271) B4953271
theorem B4402907 : Blo 1955435 4402907 := bstep (se 1 (by rfl) ⟨3302180, by rfl⟩ : syracuseStep 4402907 = 6604361) B6604361
theorem B2935271 : Blo 1955435 2935271 := bstep (se 1 (by rfl) ⟨2201453, by rfl⟩ : syracuseStep 2935271 = 4402907) B4402907
theorem B1956847 : Blo 1955435 1956847 := bstep (se 1 (by rfl) ⟨1467635, by rfl⟩ : syracuseStep 1956847 = 2935271) B2935271
theorem B2935277 : Blo 1955435 2935277 := bbase (se 3 (by rfl) ⟨550364, by rfl⟩ : syracuseStep 2935277 = 1100729) (by norm_num)
theorem B1956851 : Blo 1955435 1956851 := bstep (se 1 (by rfl) ⟨1467638, by rfl⟩ : syracuseStep 1956851 = 2935277) B2935277
theorem B4402925 : Blo 1955435 4402925 := bbase (se 3 (by rfl) ⟨825548, by rfl⟩ : syracuseStep 4402925 = 1651097) (by norm_num)
theorem B2935283 : Blo 1955435 2935283 := bstep (se 1 (by rfl) ⟨2201462, by rfl⟩ : syracuseStep 2935283 = 4402925) B4402925
theorem B1956855 : Blo 1955435 1956855 := bstep (se 1 (by rfl) ⟨1467641, by rfl⟩ : syracuseStep 1956855 = 2935283) B2935283
theorem B2350885 : Blo 1955435 2350885 := bbase (se 4 (by rfl) ⟨220395, by rfl⟩ : syracuseStep 2350885 = 440791) (by norm_num)
theorem B3134513 : Blo 1955435 3134513 := bstep (se 2 (by rfl) ⟨1175442, by rfl⟩ : syracuseStep 3134513 = 2350885) B2350885
theorem B2089675 : Blo 1955435 2089675 := bstep (se 1 (by rfl) ⟨1567256, by rfl⟩ : syracuseStep 2089675 = 3134513) B3134513
theorem B2786233 : Blo 1955435 2786233 := bstep (se 2 (by rfl) ⟨1044837, by rfl⟩ : syracuseStep 2786233 = 2089675) B2089675
theorem B3714977 : Blo 1955435 3714977 := bstep (se 2 (by rfl) ⟨1393116, by rfl⟩ : syracuseStep 3714977 = 2786233) B2786233
theorem B2476651 : Blo 1955435 2476651 := bstep (se 1 (by rfl) ⟨1857488, by rfl⟩ : syracuseStep 2476651 = 3714977) B3714977
theorem B3302201 : Blo 1955435 3302201 := bstep (se 2 (by rfl) ⟨1238325, by rfl⟩ : syracuseStep 3302201 = 2476651) B2476651
theorem B2201467 : Blo 1955435 2201467 := bstep (se 1 (by rfl) ⟨1651100, by rfl⟩ : syracuseStep 2201467 = 3302201) B3302201
theorem B2935289 : Blo 1955435 2935289 := bstep (se 2 (by rfl) ⟨1100733, by rfl⟩ : syracuseStep 2935289 = 2201467) B2201467
theorem B1956859 : Blo 1955435 1956859 := bstep (se 1 (by rfl) ⟨1467644, by rfl⟩ : syracuseStep 1956859 = 2935289) B2935289
theorem B2261953 : Blo 1955435 2261953 := bbase (se 2 (by rfl) ⟨848232, by rfl⟩ : syracuseStep 2261953 = 1696465) (by norm_num)
theorem B3015937 : Blo 1955435 3015937 := bstep (se 2 (by rfl) ⟨1130976, by rfl⟩ : syracuseStep 3015937 = 2261953) B2261953
theorem B4021249 : Blo 1955435 4021249 := bstep (se 2 (by rfl) ⟨1507968, by rfl⟩ : syracuseStep 4021249 = 3015937) B3015937
theorem B5361665 : Blo 1955435 5361665 := bstep (se 2 (by rfl) ⟨2010624, by rfl⟩ : syracuseStep 5361665 = 4021249) B4021249
theorem B57191093 : Blo 1955435 57191093 := bstep (se 5 (by rfl) ⟨2680832, by rfl⟩ : syracuseStep 57191093 = 5361665) B5361665
theorem B38127395 : Blo 1955435 38127395 := bstep (se 1 (by rfl) ⟨28595546, by rfl⟩ : syracuseStep 38127395 = 57191093) B57191093
theorem B101673053 : Blo 1955435 101673053 := bstep (se 3 (by rfl) ⟨19063697, by rfl⟩ : syracuseStep 101673053 = 38127395) B38127395
theorem B67782035 : Blo 1955435 67782035 := bstep (se 1 (by rfl) ⟨50836526, by rfl⟩ : syracuseStep 67782035 = 101673053) B101673053
theorem B180752093 : Blo 1955435 180752093 := bstep (se 3 (by rfl) ⟨33891017, by rfl⟩ : syracuseStep 180752093 = 67782035) B67782035
theorem B120501395 : Blo 1955435 120501395 := bstep (se 1 (by rfl) ⟨90376046, by rfl⟩ : syracuseStep 120501395 = 180752093) B180752093
theorem B80334263 : Blo 1955435 80334263 := bstep (se 1 (by rfl) ⟨60250697, by rfl⟩ : syracuseStep 80334263 = 120501395) B120501395
theorem B53556175 : Blo 1955435 53556175 := bstep (se 1 (by rfl) ⟨40167131, by rfl⟩ : syracuseStep 53556175 = 80334263) B80334263
theorem B71408233 : Blo 1955435 71408233 := bstep (se 2 (by rfl) ⟨26778087, by rfl⟩ : syracuseStep 71408233 = 53556175) B53556175
theorem B95210977 : Blo 1955435 95210977 := bstep (se 2 (by rfl) ⟨35704116, by rfl⟩ : syracuseStep 95210977 = 71408233) B71408233
theorem B126947969 : Blo 1955435 126947969 := bstep (se 2 (by rfl) ⟨47605488, by rfl⟩ : syracuseStep 126947969 = 95210977) B95210977
theorem B84631979 : Blo 1955435 84631979 := bstep (se 1 (by rfl) ⟨63473984, by rfl⟩ : syracuseStep 84631979 = 126947969) B126947969
theorem B56421319 : Blo 1955435 56421319 := bstep (se 1 (by rfl) ⟨42315989, by rfl⟩ : syracuseStep 56421319 = 84631979) B84631979
theorem B75228425 : Blo 1955435 75228425 := bstep (se 2 (by rfl) ⟨28210659, by rfl⟩ : syracuseStep 75228425 = 56421319) B56421319
theorem B50152283 : Blo 1955435 50152283 := bstep (se 1 (by rfl) ⟨37614212, by rfl⟩ : syracuseStep 50152283 = 75228425) B75228425
theorem B33434855 : Blo 1955435 33434855 := bstep (se 1 (by rfl) ⟨25076141, by rfl⟩ : syracuseStep 33434855 = 50152283) B50152283
theorem B22289903 : Blo 1955435 22289903 := bstep (se 1 (by rfl) ⟨16717427, by rfl⟩ : syracuseStep 22289903 = 33434855) B33434855
theorem B14859935 : Blo 1955435 14859935 := bstep (se 1 (by rfl) ⟨11144951, by rfl⟩ : syracuseStep 14859935 = 22289903) B22289903
theorem B9906623 : Blo 1955435 9906623 := bstep (se 1 (by rfl) ⟨7429967, by rfl⟩ : syracuseStep 9906623 = 14859935) B14859935
theorem B6604415 : Blo 1955435 6604415 := bstep (se 1 (by rfl) ⟨4953311, by rfl⟩ : syracuseStep 6604415 = 9906623) B9906623
theorem B4402943 : Blo 1955435 4402943 := bstep (se 1 (by rfl) ⟨3302207, by rfl⟩ : syracuseStep 4402943 = 6604415) B6604415
theorem B2935295 : Blo 1955435 2935295 := bstep (se 1 (by rfl) ⟨2201471, by rfl⟩ : syracuseStep 2935295 = 4402943) B4402943
theorem B1956863 : Blo 1955435 1956863 := bstep (se 1 (by rfl) ⟨1467647, by rfl⟩ : syracuseStep 1956863 = 2935295) B2935295
theorem B2935301 : Blo 1955435 2935301 := bbase (se 4 (by rfl) ⟨275184, by rfl⟩ : syracuseStep 2935301 = 550369) (by norm_num)
theorem B1956867 : Blo 1955435 1956867 := bstep (se 1 (by rfl) ⟨1467650, by rfl⟩ : syracuseStep 1956867 = 2935301) B2935301
theorem B3302221 : Blo 1955435 3302221 := bbase (se 3 (by rfl) ⟨619166, by rfl⟩ : syracuseStep 3302221 = 1238333) (by norm_num)
theorem B4402961 : Blo 1955435 4402961 := bstep (se 2 (by rfl) ⟨1651110, by rfl⟩ : syracuseStep 4402961 = 3302221) B3302221
theorem B2935307 : Blo 1955435 2935307 := bstep (se 1 (by rfl) ⟨2201480, by rfl⟩ : syracuseStep 2935307 = 4402961) B4402961
theorem B1956871 : Blo 1955435 1956871 := bstep (se 1 (by rfl) ⟨1467653, by rfl⟩ : syracuseStep 1956871 = 2935307) B2935307
theorem B2201485 : Blo 1955435 2201485 := bbase (se 3 (by rfl) ⟨412778, by rfl⟩ : syracuseStep 2201485 = 825557) (by norm_num)
theorem B2935313 : Blo 1955435 2935313 := bstep (se 2 (by rfl) ⟨1100742, by rfl⟩ : syracuseStep 2935313 = 2201485) B2201485
theorem B1956875 : Blo 1955435 1956875 := bstep (se 1 (by rfl) ⟨1467656, by rfl⟩ : syracuseStep 1956875 = 2935313) B2935313
theorem B6604469 : Blo 1955435 6604469 := bbase (se 5 (by rfl) ⟨309584, by rfl⟩ : syracuseStep 6604469 = 619169) (by norm_num)
theorem B4402979 : Blo 1955435 4402979 := bstep (se 1 (by rfl) ⟨3302234, by rfl⟩ : syracuseStep 4402979 = 6604469) B6604469
theorem B2935319 : Blo 1955435 2935319 := bstep (se 1 (by rfl) ⟨2201489, by rfl⟩ : syracuseStep 2935319 = 4402979) B4402979
theorem B1956879 : Blo 1955435 1956879 := bstep (se 1 (by rfl) ⟨1467659, by rfl⟩ : syracuseStep 1956879 = 2935319) B2935319
theorem B2935325 : Blo 1955435 2935325 := bbase (se 3 (by rfl) ⟨550373, by rfl⟩ : syracuseStep 2935325 = 1100747) (by norm_num)
theorem B1956883 : Blo 1955435 1956883 := bstep (se 1 (by rfl) ⟨1467662, by rfl⟩ : syracuseStep 1956883 = 2935325) B2935325
theorem B4402997 : Blo 1955435 4402997 := bbase (se 5 (by rfl) ⟨206390, by rfl⟩ : syracuseStep 4402997 = 412781) (by norm_num)
theorem B2935331 : Blo 1955435 2935331 := bstep (se 1 (by rfl) ⟨2201498, by rfl⟩ : syracuseStep 2935331 = 4402997) B4402997
theorem B1956887 : Blo 1955435 1956887 := bstep (se 1 (by rfl) ⟨1467665, by rfl⟩ : syracuseStep 1956887 = 2935331) B2935331
theorem B4701845 : Blo 1955435 4701845 := bbase (se 6 (by rfl) ⟨110199, by rfl⟩ : syracuseStep 4701845 = 220399) (by norm_num)
theorem B12538253 : Blo 1955435 12538253 := bstep (se 3 (by rfl) ⟨2350922, by rfl⟩ : syracuseStep 12538253 = 4701845) B4701845
theorem B8358835 : Blo 1955435 8358835 := bstep (se 1 (by rfl) ⟨6269126, by rfl⟩ : syracuseStep 8358835 = 12538253) B12538253
theorem B11145113 : Blo 1955435 11145113 := bstep (se 2 (by rfl) ⟨4179417, by rfl⟩ : syracuseStep 11145113 = 8358835) B8358835
theorem B7430075 : Blo 1955435 7430075 := bstep (se 1 (by rfl) ⟨5572556, by rfl⟩ : syracuseStep 7430075 = 11145113) B11145113
theorem B4953383 : Blo 1955435 4953383 := bstep (se 1 (by rfl) ⟨3715037, by rfl⟩ : syracuseStep 4953383 = 7430075) B7430075
theorem B3302255 : Blo 1955435 3302255 := bstep (se 1 (by rfl) ⟨2476691, by rfl⟩ : syracuseStep 3302255 = 4953383) B4953383
theorem B2201503 : Blo 1955435 2201503 := bstep (se 1 (by rfl) ⟨1651127, by rfl⟩ : syracuseStep 2201503 = 3302255) B3302255
theorem B2935337 : Blo 1955435 2935337 := bstep (se 2 (by rfl) ⟨1100751, by rfl⟩ : syracuseStep 2935337 = 2201503) B2201503
theorem B1956891 : Blo 1955435 1956891 := bstep (se 1 (by rfl) ⟨1467668, by rfl⟩ : syracuseStep 1956891 = 2935337) B2935337
theorem B2231545 : Blo 1955435 2231545 := bbase (se 2 (by rfl) ⟨836829, by rfl⟩ : syracuseStep 2231545 = 1673659) (by norm_num)
theorem B2975393 : Blo 1955435 2975393 := bstep (se 2 (by rfl) ⟨1115772, by rfl⟩ : syracuseStep 2975393 = 2231545) B2231545
theorem B7934381 : Blo 1955435 7934381 := bstep (se 3 (by rfl) ⟨1487696, by rfl⟩ : syracuseStep 7934381 = 2975393) B2975393
theorem B5289587 : Blo 1955435 5289587 := bstep (se 1 (by rfl) ⟨3967190, by rfl⟩ : syracuseStep 5289587 = 7934381) B7934381
theorem B3526391 : Blo 1955435 3526391 := bstep (se 1 (by rfl) ⟨2644793, by rfl⟩ : syracuseStep 3526391 = 5289587) B5289587
theorem B2350927 : Blo 1955435 2350927 := bstep (se 1 (by rfl) ⟨1763195, by rfl⟩ : syracuseStep 2350927 = 3526391) B3526391
theorem B12538277 : Blo 1955435 12538277 := bstep (se 4 (by rfl) ⟨1175463, by rfl⟩ : syracuseStep 12538277 = 2350927) B2350927
theorem B8358851 : Blo 1955435 8358851 := bstep (se 1 (by rfl) ⟨6269138, by rfl⟩ : syracuseStep 8358851 = 12538277) B12538277
theorem B5572567 : Blo 1955435 5572567 := bstep (se 1 (by rfl) ⟨4179425, by rfl⟩ : syracuseStep 5572567 = 8358851) B8358851
theorem B7430089 : Blo 1955435 7430089 := bstep (se 2 (by rfl) ⟨2786283, by rfl⟩ : syracuseStep 7430089 = 5572567) B5572567
theorem B9906785 : Blo 1955435 9906785 := bstep (se 2 (by rfl) ⟨3715044, by rfl⟩ : syracuseStep 9906785 = 7430089) B7430089
theorem B6604523 : Blo 1955435 6604523 := bstep (se 1 (by rfl) ⟨4953392, by rfl⟩ : syracuseStep 6604523 = 9906785) B9906785
theorem B4403015 : Blo 1955435 4403015 := bstep (se 1 (by rfl) ⟨3302261, by rfl⟩ : syracuseStep 4403015 = 6604523) B6604523
theorem B2935343 : Blo 1955435 2935343 := bstep (se 1 (by rfl) ⟨2201507, by rfl⟩ : syracuseStep 2935343 = 4403015) B4403015
theorem B1956895 : Blo 1955435 1956895 := bstep (se 1 (by rfl) ⟨1467671, by rfl⟩ : syracuseStep 1956895 = 2935343) B2935343
theorem B2935349 : Blo 1955435 2935349 := bbase (se 5 (by rfl) ⟨137594, by rfl⟩ : syracuseStep 2935349 = 275189) (by norm_num)
theorem B1956899 : Blo 1955435 1956899 := bstep (se 1 (by rfl) ⟨1467674, by rfl⟩ : syracuseStep 1956899 = 2935349) B2935349
theorem B4953413 : Blo 1955435 4953413 := bbase (se 4 (by rfl) ⟨464382, by rfl⟩ : syracuseStep 4953413 = 928765) (by norm_num)
theorem B3302275 : Blo 1955435 3302275 := bstep (se 1 (by rfl) ⟨2476706, by rfl⟩ : syracuseStep 3302275 = 4953413) B4953413
theorem B4403033 : Blo 1955435 4403033 := bstep (se 2 (by rfl) ⟨1651137, by rfl⟩ : syracuseStep 4403033 = 3302275) B3302275
theorem B2935355 : Blo 1955435 2935355 := bstep (se 1 (by rfl) ⟨2201516, by rfl⟩ : syracuseStep 2935355 = 4403033) B4403033
theorem B1956903 : Blo 1955435 1956903 := bstep (se 1 (by rfl) ⟨1467677, by rfl⟩ : syracuseStep 1956903 = 2935355) B2935355
theorem B2201521 : Blo 1955435 2201521 := bbase (se 2 (by rfl) ⟨825570, by rfl⟩ : syracuseStep 2201521 = 1651141) (by norm_num)
theorem B2935361 : Blo 1955435 2935361 := bstep (se 2 (by rfl) ⟨1100760, by rfl⟩ : syracuseStep 2935361 = 2201521) B2201521
theorem B1956907 : Blo 1955435 1956907 := bstep (se 1 (by rfl) ⟨1467680, by rfl⟩ : syracuseStep 1956907 = 2935361) B2935361
theorem B5572613 : Blo 1955435 5572613 := bbase (se 4 (by rfl) ⟨522432, by rfl⟩ : syracuseStep 5572613 = 1044865) (by norm_num)
theorem B3715075 : Blo 1955435 3715075 := bstep (se 1 (by rfl) ⟨2786306, by rfl⟩ : syracuseStep 3715075 = 5572613) B5572613
theorem B4953433 : Blo 1955435 4953433 := bstep (se 2 (by rfl) ⟨1857537, by rfl⟩ : syracuseStep 4953433 = 3715075) B3715075
theorem B6604577 : Blo 1955435 6604577 := bstep (se 2 (by rfl) ⟨2476716, by rfl⟩ : syracuseStep 6604577 = 4953433) B4953433
theorem B4403051 : Blo 1955435 4403051 := bstep (se 1 (by rfl) ⟨3302288, by rfl⟩ : syracuseStep 4403051 = 6604577) B6604577
theorem B2935367 : Blo 1955435 2935367 := bstep (se 1 (by rfl) ⟨2201525, by rfl⟩ : syracuseStep 2935367 = 4403051) B4403051
theorem B1956911 : Blo 1955435 1956911 := bstep (se 1 (by rfl) ⟨1467683, by rfl⟩ : syracuseStep 1956911 = 2935367) B2935367
theorem B2935373 : Blo 1955435 2935373 := bbase (se 3 (by rfl) ⟨550382, by rfl⟩ : syracuseStep 2935373 = 1100765) (by norm_num)
theorem B1956915 : Blo 1955435 1956915 := bstep (se 1 (by rfl) ⟨1467686, by rfl⟩ : syracuseStep 1956915 = 2935373) B2935373
theorem B4403069 : Blo 1955435 4403069 := bbase (se 3 (by rfl) ⟨825575, by rfl⟩ : syracuseStep 4403069 = 1651151) (by norm_num)
theorem B2935379 : Blo 1955435 2935379 := bstep (se 1 (by rfl) ⟨2201534, by rfl⟩ : syracuseStep 2935379 = 4403069) B4403069
theorem B1956919 : Blo 1955435 1956919 := bstep (se 1 (by rfl) ⟨1467689, by rfl⟩ : syracuseStep 1956919 = 2935379) B2935379
theorem B3302309 : Blo 1955435 3302309 := bbase (se 4 (by rfl) ⟨309591, by rfl⟩ : syracuseStep 3302309 = 619183) (by norm_num)
theorem B2201539 : Blo 1955435 2201539 := bstep (se 1 (by rfl) ⟨1651154, by rfl⟩ : syracuseStep 2201539 = 3302309) B3302309
theorem B2935385 : Blo 1955435 2935385 := bstep (se 2 (by rfl) ⟨1100769, by rfl⟩ : syracuseStep 2935385 = 2201539) B2201539
theorem B1956923 : Blo 1955435 1956923 := bstep (se 1 (by rfl) ⟨1467692, by rfl⟩ : syracuseStep 1956923 = 2935385) B2935385
theorem B3134621 : Blo 1955435 3134621 := bbase (se 3 (by rfl) ⟨587741, by rfl⟩ : syracuseStep 3134621 = 1175483) (by norm_num)
theorem B2089747 : Blo 1955435 2089747 := bstep (se 1 (by rfl) ⟨1567310, by rfl⟩ : syracuseStep 2089747 = 3134621) B3134621
theorem B2786329 : Blo 1955435 2786329 := bstep (se 2 (by rfl) ⟨1044873, by rfl⟩ : syracuseStep 2786329 = 2089747) B2089747
theorem B14860421 : Blo 1955435 14860421 := bstep (se 4 (by rfl) ⟨1393164, by rfl⟩ : syracuseStep 14860421 = 2786329) B2786329
theorem B9906947 : Blo 1955435 9906947 := bstep (se 1 (by rfl) ⟨7430210, by rfl⟩ : syracuseStep 9906947 = 14860421) B14860421
theorem B6604631 : Blo 1955435 6604631 := bstep (se 1 (by rfl) ⟨4953473, by rfl⟩ : syracuseStep 6604631 = 9906947) B9906947
theorem B4403087 : Blo 1955435 4403087 := bstep (se 1 (by rfl) ⟨3302315, by rfl⟩ : syracuseStep 4403087 = 6604631) B6604631
theorem B2935391 : Blo 1955435 2935391 := bstep (se 1 (by rfl) ⟨2201543, by rfl⟩ : syracuseStep 2935391 = 4403087) B4403087
theorem B1956927 : Blo 1955435 1956927 := bstep (se 1 (by rfl) ⟨1467695, by rfl⟩ : syracuseStep 1956927 = 2935391) B2935391
theorem B2935397 : Blo 1955435 2935397 := bbase (se 4 (by rfl) ⟨275193, by rfl⟩ : syracuseStep 2935397 = 550387) (by norm_num)
theorem B1956931 : Blo 1955435 1956931 := bstep (se 1 (by rfl) ⟨1467698, by rfl⟩ : syracuseStep 1956931 = 2935397) B2935397
theorem B2786341 : Blo 1955435 2786341 := bbase (se 4 (by rfl) ⟨261219, by rfl⟩ : syracuseStep 2786341 = 522439) (by norm_num)
theorem B3715121 : Blo 1955435 3715121 := bstep (se 2 (by rfl) ⟨1393170, by rfl⟩ : syracuseStep 3715121 = 2786341) B2786341
theorem B2476747 : Blo 1955435 2476747 := bstep (se 1 (by rfl) ⟨1857560, by rfl⟩ : syracuseStep 2476747 = 3715121) B3715121
theorem B3302329 : Blo 1955435 3302329 := bstep (se 2 (by rfl) ⟨1238373, by rfl⟩ : syracuseStep 3302329 = 2476747) B2476747
theorem B4403105 : Blo 1955435 4403105 := bstep (se 2 (by rfl) ⟨1651164, by rfl⟩ : syracuseStep 4403105 = 3302329) B3302329
theorem B2935403 : Blo 1955435 2935403 := bstep (se 1 (by rfl) ⟨2201552, by rfl⟩ : syracuseStep 2935403 = 4403105) B4403105
theorem B1956935 : Blo 1955435 1956935 := bstep (se 1 (by rfl) ⟨1467701, by rfl⟩ : syracuseStep 1956935 = 2935403) B2935403
theorem B2201557 : Blo 1955435 2201557 := bbase (se 7 (by rfl) ⟨25799, by rfl⟩ : syracuseStep 2201557 = 51599) (by norm_num)
theorem B2935409 : Blo 1955435 2935409 := bstep (se 2 (by rfl) ⟨1100778, by rfl⟩ : syracuseStep 2935409 = 2201557) B2201557
theorem B1956939 : Blo 1955435 1956939 := bstep (se 1 (by rfl) ⟨1467704, by rfl⟩ : syracuseStep 1956939 = 2935409) B2935409
theorem B2476757 : Blo 1955435 2476757 := bbase (se 7 (by rfl) ⟨29024, by rfl⟩ : syracuseStep 2476757 = 58049) (by norm_num)
theorem B6604685 : Blo 1955435 6604685 := bstep (se 3 (by rfl) ⟨1238378, by rfl⟩ : syracuseStep 6604685 = 2476757) B2476757
theorem B4403123 : Blo 1955435 4403123 := bstep (se 1 (by rfl) ⟨3302342, by rfl⟩ : syracuseStep 4403123 = 6604685) B6604685
theorem B2935415 : Blo 1955435 2935415 := bstep (se 1 (by rfl) ⟨2201561, by rfl⟩ : syracuseStep 2935415 = 4403123) B4403123
theorem B1956943 : Blo 1955435 1956943 := bstep (se 1 (by rfl) ⟨1467707, by rfl⟩ : syracuseStep 1956943 = 2935415) B2935415
theorem B2935421 : Blo 1955435 2935421 := bbase (se 3 (by rfl) ⟨550391, by rfl⟩ : syracuseStep 2935421 = 1100783) (by norm_num)
theorem B1956947 : Blo 1955435 1956947 := bstep (se 1 (by rfl) ⟨1467710, by rfl⟩ : syracuseStep 1956947 = 2935421) B2935421
theorem B4403141 : Blo 1955435 4403141 := bbase (se 4 (by rfl) ⟨412794, by rfl⟩ : syracuseStep 4403141 = 825589) (by norm_num)
theorem B2935427 : Blo 1955435 2935427 := bstep (se 1 (by rfl) ⟨2201570, by rfl⟩ : syracuseStep 2935427 = 4403141) B4403141
theorem B1956951 : Blo 1955435 1956951 := bstep (se 1 (by rfl) ⟨1467713, by rfl⟩ : syracuseStep 1956951 = 2935427) B2935427
theorem B8359109 : Blo 1955435 8359109 := bbase (se 4 (by rfl) ⟨783666, by rfl⟩ : syracuseStep 8359109 = 1567333) (by norm_num)
theorem B5572739 : Blo 1955435 5572739 := bstep (se 1 (by rfl) ⟨4179554, by rfl⟩ : syracuseStep 5572739 = 8359109) B8359109
theorem B3715159 : Blo 1955435 3715159 := bstep (se 1 (by rfl) ⟨2786369, by rfl⟩ : syracuseStep 3715159 = 5572739) B5572739
theorem B4953545 : Blo 1955435 4953545 := bstep (se 2 (by rfl) ⟨1857579, by rfl⟩ : syracuseStep 4953545 = 3715159) B3715159
theorem B3302363 : Blo 1955435 3302363 := bstep (se 1 (by rfl) ⟨2476772, by rfl⟩ : syracuseStep 3302363 = 4953545) B4953545
theorem B2201575 : Blo 1955435 2201575 := bstep (se 1 (by rfl) ⟨1651181, by rfl⟩ : syracuseStep 2201575 = 3302363) B3302363
theorem B2935433 : Blo 1955435 2935433 := bstep (se 2 (by rfl) ⟨1100787, by rfl⟩ : syracuseStep 2935433 = 2201575) B2201575
theorem B1956955 : Blo 1955435 1956955 := bstep (se 1 (by rfl) ⟨1467716, by rfl⟩ : syracuseStep 1956955 = 2935433) B2935433
theorem B9907109 : Blo 1955435 9907109 := bbase (se 4 (by rfl) ⟨928791, by rfl⟩ : syracuseStep 9907109 = 1857583) (by norm_num)
theorem B6604739 : Blo 1955435 6604739 := bstep (se 1 (by rfl) ⟨4953554, by rfl⟩ : syracuseStep 6604739 = 9907109) B9907109
theorem B4403159 : Blo 1955435 4403159 := bstep (se 1 (by rfl) ⟨3302369, by rfl⟩ : syracuseStep 4403159 = 6604739) B6604739
theorem B2935439 : Blo 1955435 2935439 := bstep (se 1 (by rfl) ⟨2201579, by rfl⟩ : syracuseStep 2935439 = 4403159) B4403159
theorem B1956959 : Blo 1955435 1956959 := bstep (se 1 (by rfl) ⟨1467719, by rfl⟩ : syracuseStep 1956959 = 2935439) B2935439
theorem B2935445 : Blo 1955435 2935445 := bbase (se 6 (by rfl) ⟨68799, by rfl⟩ : syracuseStep 2935445 = 137599) (by norm_num)
theorem B1956963 : Blo 1955435 1956963 := bstep (se 1 (by rfl) ⟨1467722, by rfl⟩ : syracuseStep 1956963 = 2935445) B2935445
theorem B5289781 : Blo 1955435 5289781 := bbase (se 5 (by rfl) ⟨247958, by rfl⟩ : syracuseStep 5289781 = 495917) (by norm_num)
theorem B7053041 : Blo 1955435 7053041 := bstep (se 2 (by rfl) ⟨2644890, by rfl⟩ : syracuseStep 7053041 = 5289781) B5289781
theorem B18808109 : Blo 1955435 18808109 := bstep (se 3 (by rfl) ⟨3526520, by rfl⟩ : syracuseStep 18808109 = 7053041) B7053041
theorem B12538739 : Blo 1955435 12538739 := bstep (se 1 (by rfl) ⟨9404054, by rfl⟩ : syracuseStep 12538739 = 18808109) B18808109
theorem B8359159 : Blo 1955435 8359159 := bstep (se 1 (by rfl) ⟨6269369, by rfl⟩ : syracuseStep 8359159 = 12538739) B12538739
theorem B11145545 : Blo 1955435 11145545 := bstep (se 2 (by rfl) ⟨4179579, by rfl⟩ : syracuseStep 11145545 = 8359159) B8359159
theorem B7430363 : Blo 1955435 7430363 := bstep (se 1 (by rfl) ⟨5572772, by rfl⟩ : syracuseStep 7430363 = 11145545) B11145545
theorem B4953575 : Blo 1955435 4953575 := bstep (se 1 (by rfl) ⟨3715181, by rfl⟩ : syracuseStep 4953575 = 7430363) B7430363
theorem B3302383 : Blo 1955435 3302383 := bstep (se 1 (by rfl) ⟨2476787, by rfl⟩ : syracuseStep 3302383 = 4953575) B4953575
theorem B4403177 : Blo 1955435 4403177 := bstep (se 2 (by rfl) ⟨1651191, by rfl⟩ : syracuseStep 4403177 = 3302383) B3302383
theorem B2935451 : Blo 1955435 2935451 := bstep (se 1 (by rfl) ⟨2201588, by rfl⟩ : syracuseStep 2935451 = 4403177) B4403177
theorem B1956967 : Blo 1955435 1956967 := bstep (se 1 (by rfl) ⟨1467725, by rfl⟩ : syracuseStep 1956967 = 2935451) B2935451
theorem B2201593 : Blo 1955435 2201593 := bbase (se 2 (by rfl) ⟨825597, by rfl⟩ : syracuseStep 2201593 = 1651195) (by norm_num)
theorem B2935457 : Blo 1955435 2935457 := bstep (se 2 (by rfl) ⟨1100796, by rfl⟩ : syracuseStep 2935457 = 2201593) B2201593
theorem B1956971 : Blo 1955435 1956971 := bstep (se 1 (by rfl) ⟨1467728, by rfl⟩ : syracuseStep 1956971 = 2935457) B2935457
theorem B5951029 : Blo 1955435 5951029 := bbase (se 5 (by rfl) ⟨278954, by rfl⟩ : syracuseStep 5951029 = 557909) (by norm_num)
theorem B7934705 : Blo 1955435 7934705 := bstep (se 2 (by rfl) ⟨2975514, by rfl⟩ : syracuseStep 7934705 = 5951029) B5951029
theorem B5289803 : Blo 1955435 5289803 := bstep (se 1 (by rfl) ⟨3967352, by rfl⟩ : syracuseStep 5289803 = 7934705) B7934705
theorem B3526535 : Blo 1955435 3526535 := bstep (se 1 (by rfl) ⟨2644901, by rfl⟩ : syracuseStep 3526535 = 5289803) B5289803
theorem B9404093 : Blo 1955435 9404093 := bstep (se 3 (by rfl) ⟨1763267, by rfl⟩ : syracuseStep 9404093 = 3526535) B3526535
theorem B6269395 : Blo 1955435 6269395 := bstep (se 1 (by rfl) ⟨4702046, by rfl⟩ : syracuseStep 6269395 = 9404093) B9404093
theorem B8359193 : Blo 1955435 8359193 := bstep (se 2 (by rfl) ⟨3134697, by rfl⟩ : syracuseStep 8359193 = 6269395) B6269395
theorem B5572795 : Blo 1955435 5572795 := bstep (se 1 (by rfl) ⟨4179596, by rfl⟩ : syracuseStep 5572795 = 8359193) B8359193
theorem B7430393 : Blo 1955435 7430393 := bstep (se 2 (by rfl) ⟨2786397, by rfl⟩ : syracuseStep 7430393 = 5572795) B5572795
theorem B4953595 : Blo 1955435 4953595 := bstep (se 1 (by rfl) ⟨3715196, by rfl⟩ : syracuseStep 4953595 = 7430393) B7430393
theorem B6604793 : Blo 1955435 6604793 := bstep (se 2 (by rfl) ⟨2476797, by rfl⟩ : syracuseStep 6604793 = 4953595) B4953595
theorem B4403195 : Blo 1955435 4403195 := bstep (se 1 (by rfl) ⟨3302396, by rfl⟩ : syracuseStep 4403195 = 6604793) B6604793
theorem B2935463 : Blo 1955435 2935463 := bstep (se 1 (by rfl) ⟨2201597, by rfl⟩ : syracuseStep 2935463 = 4403195) B4403195
theorem B1956975 : Blo 1955435 1956975 := bstep (se 1 (by rfl) ⟨1467731, by rfl⟩ : syracuseStep 1956975 = 2935463) B2935463
theorem B2935469 : Blo 1955435 2935469 := bbase (se 3 (by rfl) ⟨550400, by rfl⟩ : syracuseStep 2935469 = 1100801) (by norm_num)
theorem B1956979 : Blo 1955435 1956979 := bstep (se 1 (by rfl) ⟨1467734, by rfl⟩ : syracuseStep 1956979 = 2935469) B2935469
theorem B4403213 : Blo 1955435 4403213 := bbase (se 3 (by rfl) ⟨825602, by rfl⟩ : syracuseStep 4403213 = 1651205) (by norm_num)
theorem B2935475 : Blo 1955435 2935475 := bstep (se 1 (by rfl) ⟨2201606, by rfl⟩ : syracuseStep 2935475 = 4403213) B4403213
theorem B1956983 : Blo 1955435 1956983 := bstep (se 1 (by rfl) ⟨1467737, by rfl⟩ : syracuseStep 1956983 = 2935475) B2935475
theorem B2476813 : Blo 1955435 2476813 := bbase (se 3 (by rfl) ⟨464402, by rfl⟩ : syracuseStep 2476813 = 928805) (by norm_num)
theorem B3302417 : Blo 1955435 3302417 := bstep (se 2 (by rfl) ⟨1238406, by rfl⟩ : syracuseStep 3302417 = 2476813) B2476813
theorem B2201611 : Blo 1955435 2201611 := bstep (se 1 (by rfl) ⟨1651208, by rfl⟩ : syracuseStep 2201611 = 3302417) B3302417
theorem B2935481 : Blo 1955435 2935481 := bstep (se 2 (by rfl) ⟨1100805, by rfl⟩ : syracuseStep 2935481 = 2201611) B2201611
theorem B1956987 : Blo 1955435 1956987 := bstep (se 1 (by rfl) ⟨1467740, by rfl⟩ : syracuseStep 1956987 = 2935481) B2935481
theorem B5289845 : Blo 1955435 5289845 := bbase (se 5 (by rfl) ⟨247961, by rfl⟩ : syracuseStep 5289845 = 495923) (by norm_num)
theorem B14106253 : Blo 1955435 14106253 := bstep (se 3 (by rfl) ⟨2644922, by rfl⟩ : syracuseStep 14106253 = 5289845) B5289845
theorem B18808337 : Blo 1955435 18808337 := bstep (se 2 (by rfl) ⟨7053126, by rfl⟩ : syracuseStep 18808337 = 14106253) B14106253
theorem B12538891 : Blo 1955435 12538891 := bstep (se 1 (by rfl) ⟨9404168, by rfl⟩ : syracuseStep 12538891 = 18808337) B18808337
theorem B16718521 : Blo 1955435 16718521 := bstep (se 2 (by rfl) ⟨6269445, by rfl⟩ : syracuseStep 16718521 = 12538891) B12538891
theorem B22291361 : Blo 1955435 22291361 := bstep (se 2 (by rfl) ⟨8359260, by rfl⟩ : syracuseStep 22291361 = 16718521) B16718521
theorem B14860907 : Blo 1955435 14860907 := bstep (se 1 (by rfl) ⟨11145680, by rfl⟩ : syracuseStep 14860907 = 22291361) B22291361
theorem B9907271 : Blo 1955435 9907271 := bstep (se 1 (by rfl) ⟨7430453, by rfl⟩ : syracuseStep 9907271 = 14860907) B14860907
theorem B6604847 : Blo 1955435 6604847 := bstep (se 1 (by rfl) ⟨4953635, by rfl⟩ : syracuseStep 6604847 = 9907271) B9907271
theorem B4403231 : Blo 1955435 4403231 := bstep (se 1 (by rfl) ⟨3302423, by rfl⟩ : syracuseStep 4403231 = 6604847) B6604847
theorem B2935487 : Blo 1955435 2935487 := bstep (se 1 (by rfl) ⟨2201615, by rfl⟩ : syracuseStep 2935487 = 4403231) B4403231
theorem B1956991 : Blo 1955435 1956991 := bstep (se 1 (by rfl) ⟨1467743, by rfl⟩ : syracuseStep 1956991 = 2935487) B2935487
theorem B2935493 : Blo 1955435 2935493 := bbase (se 4 (by rfl) ⟨275202, by rfl⟩ : syracuseStep 2935493 = 550405) (by norm_num)
theorem B1956995 : Blo 1955435 1956995 := bstep (se 1 (by rfl) ⟨1467746, by rfl⟩ : syracuseStep 1956995 = 2935493) B2935493
theorem B3302437 : Blo 1955435 3302437 := bbase (se 4 (by rfl) ⟨309603, by rfl⟩ : syracuseStep 3302437 = 619207) (by norm_num)
theorem B4403249 : Blo 1955435 4403249 := bstep (se 2 (by rfl) ⟨1651218, by rfl⟩ : syracuseStep 4403249 = 3302437) B3302437
theorem B2935499 : Blo 1955435 2935499 := bstep (se 1 (by rfl) ⟨2201624, by rfl⟩ : syracuseStep 2935499 = 4403249) B4403249
theorem B1956999 : Blo 1955435 1956999 := bstep (se 1 (by rfl) ⟨1467749, by rfl⟩ : syracuseStep 1956999 = 2935499) B2935499
theorem B2201629 : Blo 1955435 2201629 := bbase (se 3 (by rfl) ⟨412805, by rfl⟩ : syracuseStep 2201629 = 825611) (by norm_num)
theorem B2935505 : Blo 1955435 2935505 := bstep (se 2 (by rfl) ⟨1100814, by rfl⟩ : syracuseStep 2935505 = 2201629) B2201629
theorem B1957003 : Blo 1955435 1957003 := bstep (se 1 (by rfl) ⟨1467752, by rfl⟩ : syracuseStep 1957003 = 2935505) B2935505
theorem B6604901 : Blo 1955435 6604901 := bbase (se 4 (by rfl) ⟨619209, by rfl⟩ : syracuseStep 6604901 = 1238419) (by norm_num)
theorem B4403267 : Blo 1955435 4403267 := bstep (se 1 (by rfl) ⟨3302450, by rfl⟩ : syracuseStep 4403267 = 6604901) B6604901
theorem B2935511 : Blo 1955435 2935511 := bstep (se 1 (by rfl) ⟨2201633, by rfl⟩ : syracuseStep 2935511 = 4403267) B4403267
theorem B1957007 : Blo 1955435 1957007 := bstep (se 1 (by rfl) ⟨1467755, by rfl⟩ : syracuseStep 1957007 = 2935511) B2935511
theorem B2935517 : Blo 1955435 2935517 := bbase (se 3 (by rfl) ⟨550409, by rfl⟩ : syracuseStep 2935517 = 1100819) (by norm_num)
theorem B1957011 : Blo 1955435 1957011 := bstep (se 1 (by rfl) ⟨1467758, by rfl⟩ : syracuseStep 1957011 = 2935517) B2935517
theorem B4403285 : Blo 1955435 4403285 := bbase (se 8 (by rfl) ⟨25800, by rfl⟩ : syracuseStep 4403285 = 51601) (by norm_num)
theorem B2935523 : Blo 1955435 2935523 := bstep (se 1 (by rfl) ⟨2201642, by rfl⟩ : syracuseStep 2935523 = 4403285) B4403285
theorem B1957015 : Blo 1955435 1957015 := bstep (se 1 (by rfl) ⟨1467761, by rfl⟩ : syracuseStep 1957015 = 2935523) B2935523
theorem B7934885 : Blo 1955435 7934885 := bbase (se 4 (by rfl) ⟨743895, by rfl⟩ : syracuseStep 7934885 = 1487791) (by norm_num)
theorem B5289923 : Blo 1955435 5289923 := bstep (se 1 (by rfl) ⟨3967442, by rfl⟩ : syracuseStep 5289923 = 7934885) B7934885
theorem B3526615 : Blo 1955435 3526615 := bstep (se 1 (by rfl) ⟨2644961, by rfl⟩ : syracuseStep 3526615 = 5289923) B5289923
theorem B4702153 : Blo 1955435 4702153 := bstep (se 2 (by rfl) ⟨1763307, by rfl⟩ : syracuseStep 4702153 = 3526615) B3526615
theorem B6269537 : Blo 1955435 6269537 := bstep (se 2 (by rfl) ⟨2351076, by rfl⟩ : syracuseStep 6269537 = 4702153) B4702153
theorem B4179691 : Blo 1955435 4179691 := bstep (se 1 (by rfl) ⟨3134768, by rfl⟩ : syracuseStep 4179691 = 6269537) B6269537
theorem B5572921 : Blo 1955435 5572921 := bstep (se 2 (by rfl) ⟨2089845, by rfl⟩ : syracuseStep 5572921 = 4179691) B4179691
theorem B7430561 : Blo 1955435 7430561 := bstep (se 2 (by rfl) ⟨2786460, by rfl⟩ : syracuseStep 7430561 = 5572921) B5572921
theorem B4953707 : Blo 1955435 4953707 := bstep (se 1 (by rfl) ⟨3715280, by rfl⟩ : syracuseStep 4953707 = 7430561) B7430561
theorem B3302471 : Blo 1955435 3302471 := bstep (se 1 (by rfl) ⟨2476853, by rfl⟩ : syracuseStep 3302471 = 4953707) B4953707
theorem B2201647 : Blo 1955435 2201647 := bstep (se 1 (by rfl) ⟨1651235, by rfl⟩ : syracuseStep 2201647 = 3302471) B3302471
theorem B2935529 : Blo 1955435 2935529 := bstep (se 2 (by rfl) ⟨1100823, by rfl⟩ : syracuseStep 2935529 = 2201647) B2201647
theorem B1957019 : Blo 1955435 1957019 := bstep (se 1 (by rfl) ⟨1467764, by rfl⟩ : syracuseStep 1957019 = 2935529) B2935529
theorem B3526621 : Blo 1955435 3526621 := bbase (se 3 (by rfl) ⟨661241, by rfl⟩ : syracuseStep 3526621 = 1322483) (by norm_num)
theorem B18808645 : Blo 1955435 18808645 := bstep (se 4 (by rfl) ⟨1763310, by rfl⟩ : syracuseStep 18808645 = 3526621) B3526621
theorem B25078193 : Blo 1955435 25078193 := bstep (se 2 (by rfl) ⟨9404322, by rfl⟩ : syracuseStep 25078193 = 18808645) B18808645
theorem B16718795 : Blo 1955435 16718795 := bstep (se 1 (by rfl) ⟨12539096, by rfl⟩ : syracuseStep 16718795 = 25078193) B25078193
theorem B11145863 : Blo 1955435 11145863 := bstep (se 1 (by rfl) ⟨8359397, by rfl⟩ : syracuseStep 11145863 = 16718795) B16718795
theorem B7430575 : Blo 1955435 7430575 := bstep (se 1 (by rfl) ⟨5572931, by rfl⟩ : syracuseStep 7430575 = 11145863) B11145863
theorem B9907433 : Blo 1955435 9907433 := bstep (se 2 (by rfl) ⟨3715287, by rfl⟩ : syracuseStep 9907433 = 7430575) B7430575
theorem B6604955 : Blo 1955435 6604955 := bstep (se 1 (by rfl) ⟨4953716, by rfl⟩ : syracuseStep 6604955 = 9907433) B9907433
theorem B4403303 : Blo 1955435 4403303 := bstep (se 1 (by rfl) ⟨3302477, by rfl⟩ : syracuseStep 4403303 = 6604955) B6604955
theorem B2935535 : Blo 1955435 2935535 := bstep (se 1 (by rfl) ⟨2201651, by rfl⟩ : syracuseStep 2935535 = 4403303) B4403303
theorem B1957023 : Blo 1955435 1957023 := bstep (se 1 (by rfl) ⟨1467767, by rfl⟩ : syracuseStep 1957023 = 2935535) B2935535
theorem B2935541 : Blo 1955435 2935541 := bbase (se 5 (by rfl) ⟨137603, by rfl⟩ : syracuseStep 2935541 = 275207) (by norm_num)
theorem B1957027 : Blo 1955435 1957027 := bstep (se 1 (by rfl) ⟨1467770, by rfl⟩ : syracuseStep 1957027 = 2935541) B2935541
theorem B1983733 : Blo 1955435 1983733 := bbase (se 5 (by rfl) ⟨92987, by rfl⟩ : syracuseStep 1983733 = 185975) (by norm_num)
theorem B10579909 : Blo 1955435 10579909 := bstep (se 4 (by rfl) ⟨991866, by rfl⟩ : syracuseStep 10579909 = 1983733) B1983733
theorem B14106545 : Blo 1955435 14106545 := bstep (se 2 (by rfl) ⟨5289954, by rfl⟩ : syracuseStep 14106545 = 10579909) B10579909
theorem B9404363 : Blo 1955435 9404363 := bstep (se 1 (by rfl) ⟨7053272, by rfl⟩ : syracuseStep 9404363 = 14106545) B14106545
theorem B6269575 : Blo 1955435 6269575 := bstep (se 1 (by rfl) ⟨4702181, by rfl⟩ : syracuseStep 6269575 = 9404363) B9404363
theorem B8359433 : Blo 1955435 8359433 := bstep (se 2 (by rfl) ⟨3134787, by rfl⟩ : syracuseStep 8359433 = 6269575) B6269575
theorem B5572955 : Blo 1955435 5572955 := bstep (se 1 (by rfl) ⟨4179716, by rfl⟩ : syracuseStep 5572955 = 8359433) B8359433
theorem B3715303 : Blo 1955435 3715303 := bstep (se 1 (by rfl) ⟨2786477, by rfl⟩ : syracuseStep 3715303 = 5572955) B5572955
theorem B4953737 : Blo 1955435 4953737 := bstep (se 2 (by rfl) ⟨1857651, by rfl⟩ : syracuseStep 4953737 = 3715303) B3715303
theorem B3302491 : Blo 1955435 3302491 := bstep (se 1 (by rfl) ⟨2476868, by rfl⟩ : syracuseStep 3302491 = 4953737) B4953737
theorem B4403321 : Blo 1955435 4403321 := bstep (se 2 (by rfl) ⟨1651245, by rfl⟩ : syracuseStep 4403321 = 3302491) B3302491
theorem B2935547 : Blo 1955435 2935547 := bstep (se 1 (by rfl) ⟨2201660, by rfl⟩ : syracuseStep 2935547 = 4403321) B4403321
theorem B1957031 : Blo 1955435 1957031 := bstep (se 1 (by rfl) ⟨1467773, by rfl⟩ : syracuseStep 1957031 = 2935547) B2935547
theorem B2201665 : Blo 1955435 2201665 := bbase (se 2 (by rfl) ⟨825624, by rfl⟩ : syracuseStep 2201665 = 1651249) (by norm_num)
theorem B2935553 : Blo 1955435 2935553 := bstep (se 2 (by rfl) ⟨1100832, by rfl⟩ : syracuseStep 2935553 = 2201665) B2201665
theorem B1957035 : Blo 1955435 1957035 := bstep (se 1 (by rfl) ⟨1467776, by rfl⟩ : syracuseStep 1957035 = 2935553) B2935553
theorem B4953757 : Blo 1955435 4953757 := bbase (se 3 (by rfl) ⟨928829, by rfl⟩ : syracuseStep 4953757 = 1857659) (by norm_num)
theorem B6605009 : Blo 1955435 6605009 := bstep (se 2 (by rfl) ⟨2476878, by rfl⟩ : syracuseStep 6605009 = 4953757) B4953757
theorem B4403339 : Blo 1955435 4403339 := bstep (se 1 (by rfl) ⟨3302504, by rfl⟩ : syracuseStep 4403339 = 6605009) B6605009
theorem B2935559 : Blo 1955435 2935559 := bstep (se 1 (by rfl) ⟨2201669, by rfl⟩ : syracuseStep 2935559 = 4403339) B4403339
theorem B1957039 : Blo 1955435 1957039 := bstep (se 1 (by rfl) ⟨1467779, by rfl⟩ : syracuseStep 1957039 = 2935559) B2935559
theorem B2935565 : Blo 1955435 2935565 := bbase (se 3 (by rfl) ⟨550418, by rfl⟩ : syracuseStep 2935565 = 1100837) (by norm_num)
theorem B1957043 : Blo 1955435 1957043 := bstep (se 1 (by rfl) ⟨1467782, by rfl⟩ : syracuseStep 1957043 = 2935565) B2935565
theorem B4403357 : Blo 1955435 4403357 := bbase (se 3 (by rfl) ⟨825629, by rfl⟩ : syracuseStep 4403357 = 1651259) (by norm_num)
theorem B2935571 : Blo 1955435 2935571 := bstep (se 1 (by rfl) ⟨2201678, by rfl⟩ : syracuseStep 2935571 = 4403357) B4403357
theorem B1957047 : Blo 1955435 1957047 := bstep (se 1 (by rfl) ⟨1467785, by rfl⟩ : syracuseStep 1957047 = 2935571) B2935571
theorem B3302525 : Blo 1955435 3302525 := bbase (se 3 (by rfl) ⟨619223, by rfl⟩ : syracuseStep 3302525 = 1238447) (by norm_num)
theorem B2201683 : Blo 1955435 2201683 := bstep (se 1 (by rfl) ⟨1651262, by rfl⟩ : syracuseStep 2201683 = 3302525) B3302525
theorem B2935577 : Blo 1955435 2935577 := bstep (se 2 (by rfl) ⟨1100841, by rfl⟩ : syracuseStep 2935577 = 2201683) B2201683
theorem B1957051 : Blo 1955435 1957051 := bstep (se 1 (by rfl) ⟨1467788, by rfl⟩ : syracuseStep 1957051 = 2935577) B2935577
theorem B7935029 : Blo 1955435 7935029 := bbase (se 5 (by rfl) ⟨371954, by rfl⟩ : syracuseStep 7935029 = 743909) (by norm_num)
theorem B5290019 : Blo 1955435 5290019 := bstep (se 1 (by rfl) ⟨3967514, by rfl⟩ : syracuseStep 5290019 = 7935029) B7935029
theorem B3526679 : Blo 1955435 3526679 := bstep (se 1 (by rfl) ⟨2645009, by rfl⟩ : syracuseStep 3526679 = 5290019) B5290019
theorem B9404477 : Blo 1955435 9404477 := bstep (se 3 (by rfl) ⟨1763339, by rfl⟩ : syracuseStep 9404477 = 3526679) B3526679
theorem B6269651 : Blo 1955435 6269651 := bstep (se 1 (by rfl) ⟨4702238, by rfl⟩ : syracuseStep 6269651 = 9404477) B9404477
theorem B4179767 : Blo 1955435 4179767 := bstep (se 1 (by rfl) ⟨3134825, by rfl⟩ : syracuseStep 4179767 = 6269651) B6269651
theorem B11146045 : Blo 1955435 11146045 := bstep (se 3 (by rfl) ⟨2089883, by rfl⟩ : syracuseStep 11146045 = 4179767) B4179767
theorem B14861393 : Blo 1955435 14861393 := bstep (se 2 (by rfl) ⟨5573022, by rfl⟩ : syracuseStep 14861393 = 11146045) B11146045
theorem B9907595 : Blo 1955435 9907595 := bstep (se 1 (by rfl) ⟨7430696, by rfl⟩ : syracuseStep 9907595 = 14861393) B14861393
theorem B6605063 : Blo 1955435 6605063 := bstep (se 1 (by rfl) ⟨4953797, by rfl⟩ : syracuseStep 6605063 = 9907595) B9907595
theorem B4403375 : Blo 1955435 4403375 := bstep (se 1 (by rfl) ⟨3302531, by rfl⟩ : syracuseStep 4403375 = 6605063) B6605063
theorem B2935583 : Blo 1955435 2935583 := bstep (se 1 (by rfl) ⟨2201687, by rfl⟩ : syracuseStep 2935583 = 4403375) B4403375
theorem B1957055 : Blo 1955435 1957055 := bstep (se 1 (by rfl) ⟨1467791, by rfl⟩ : syracuseStep 1957055 = 2935583) B2935583
theorem B2935589 : Blo 1955435 2935589 := bbase (se 4 (by rfl) ⟨275211, by rfl⟩ : syracuseStep 2935589 = 550423) (by norm_num)
theorem B1957059 : Blo 1955435 1957059 := bstep (se 1 (by rfl) ⟨1467794, by rfl⟩ : syracuseStep 1957059 = 2935589) B2935589
theorem B2476909 : Blo 1955435 2476909 := bbase (se 3 (by rfl) ⟨464420, by rfl⟩ : syracuseStep 2476909 = 928841) (by norm_num)
theorem B3302545 : Blo 1955435 3302545 := bstep (se 2 (by rfl) ⟨1238454, by rfl⟩ : syracuseStep 3302545 = 2476909) B2476909
theorem B4403393 : Blo 1955435 4403393 := bstep (se 2 (by rfl) ⟨1651272, by rfl⟩ : syracuseStep 4403393 = 3302545) B3302545
theorem B2935595 : Blo 1955435 2935595 := bstep (se 1 (by rfl) ⟨2201696, by rfl⟩ : syracuseStep 2935595 = 4403393) B4403393
theorem B1957063 : Blo 1955435 1957063 := bstep (se 1 (by rfl) ⟨1467797, by rfl⟩ : syracuseStep 1957063 = 2935595) B2935595
theorem B2201701 : Blo 1955435 2201701 := bbase (se 4 (by rfl) ⟨206409, by rfl⟩ : syracuseStep 2201701 = 412819) (by norm_num)
theorem B2935601 : Blo 1955435 2935601 := bstep (se 2 (by rfl) ⟨1100850, by rfl⟩ : syracuseStep 2935601 = 2201701) B2201701
theorem B1957067 : Blo 1955435 1957067 := bstep (se 1 (by rfl) ⟨1467800, by rfl⟩ : syracuseStep 1957067 = 2935601) B2935601
theorem B2089901 : Blo 1955435 2089901 := bbase (se 3 (by rfl) ⟨391856, by rfl⟩ : syracuseStep 2089901 = 783713) (by norm_num)
theorem B5573069 : Blo 1955435 5573069 := bstep (se 3 (by rfl) ⟨1044950, by rfl⟩ : syracuseStep 5573069 = 2089901) B2089901
theorem B3715379 : Blo 1955435 3715379 := bstep (se 1 (by rfl) ⟨2786534, by rfl⟩ : syracuseStep 3715379 = 5573069) B5573069
theorem B2476919 : Blo 1955435 2476919 := bstep (se 1 (by rfl) ⟨1857689, by rfl⟩ : syracuseStep 2476919 = 3715379) B3715379
theorem B6605117 : Blo 1955435 6605117 := bstep (se 3 (by rfl) ⟨1238459, by rfl⟩ : syracuseStep 6605117 = 2476919) B2476919
theorem B4403411 : Blo 1955435 4403411 := bstep (se 1 (by rfl) ⟨3302558, by rfl⟩ : syracuseStep 4403411 = 6605117) B6605117
theorem B2935607 : Blo 1955435 2935607 := bstep (se 1 (by rfl) ⟨2201705, by rfl⟩ : syracuseStep 2935607 = 4403411) B4403411
theorem B1957071 : Blo 1955435 1957071 := bstep (se 1 (by rfl) ⟨1467803, by rfl⟩ : syracuseStep 1957071 = 2935607) B2935607
theorem B2935613 : Blo 1955435 2935613 := bbase (se 3 (by rfl) ⟨550427, by rfl⟩ : syracuseStep 2935613 = 1100855) (by norm_num)
theorem B1957075 : Blo 1955435 1957075 := bstep (se 1 (by rfl) ⟨1467806, by rfl⟩ : syracuseStep 1957075 = 2935613) B2935613
theorem B4403429 : Blo 1955435 4403429 := bbase (se 4 (by rfl) ⟨412821, by rfl⟩ : syracuseStep 4403429 = 825643) (by norm_num)
theorem B2935619 : Blo 1955435 2935619 := bstep (se 1 (by rfl) ⟨2201714, by rfl⟩ : syracuseStep 2935619 = 4403429) B4403429
theorem B1957079 : Blo 1955435 1957079 := bstep (se 1 (by rfl) ⟨1467809, by rfl⟩ : syracuseStep 1957079 = 2935619) B2935619
theorem B4953869 : Blo 1955435 4953869 := bbase (se 3 (by rfl) ⟨928850, by rfl⟩ : syracuseStep 4953869 = 1857701) (by norm_num)
theorem B3302579 : Blo 1955435 3302579 := bstep (se 1 (by rfl) ⟨2476934, by rfl⟩ : syracuseStep 3302579 = 4953869) B4953869
theorem B2201719 : Blo 1955435 2201719 := bstep (se 1 (by rfl) ⟨1651289, by rfl⟩ : syracuseStep 2201719 = 3302579) B3302579
theorem B2935625 : Blo 1955435 2935625 := bstep (se 2 (by rfl) ⟨1100859, by rfl⟩ : syracuseStep 2935625 = 2201719) B2201719
theorem B1957083 : Blo 1955435 1957083 := bstep (se 1 (by rfl) ⟨1467812, by rfl⟩ : syracuseStep 1957083 = 2935625) B2935625
theorem B2786557 : Blo 1955435 2786557 := bbase (se 3 (by rfl) ⟨522479, by rfl⟩ : syracuseStep 2786557 = 1044959) (by norm_num)
theorem B3715409 : Blo 1955435 3715409 := bstep (se 2 (by rfl) ⟨1393278, by rfl⟩ : syracuseStep 3715409 = 2786557) B2786557
theorem B9907757 : Blo 1955435 9907757 := bstep (se 3 (by rfl) ⟨1857704, by rfl⟩ : syracuseStep 9907757 = 3715409) B3715409
theorem B6605171 : Blo 1955435 6605171 := bstep (se 1 (by rfl) ⟨4953878, by rfl⟩ : syracuseStep 6605171 = 9907757) B9907757
theorem B4403447 : Blo 1955435 4403447 := bstep (se 1 (by rfl) ⟨3302585, by rfl⟩ : syracuseStep 4403447 = 6605171) B6605171
theorem B2935631 : Blo 1955435 2935631 := bstep (se 1 (by rfl) ⟨2201723, by rfl⟩ : syracuseStep 2935631 = 4403447) B4403447
theorem B1957087 : Blo 1955435 1957087 := bstep (se 1 (by rfl) ⟨1467815, by rfl⟩ : syracuseStep 1957087 = 2935631) B2935631
theorem B2935637 : Blo 1955435 2935637 := bbase (se 9 (by rfl) ⟨8600, by rfl⟩ : syracuseStep 2935637 = 17201) (by norm_num)
theorem B1957091 : Blo 1955435 1957091 := bstep (se 1 (by rfl) ⟨1467818, by rfl⟩ : syracuseStep 1957091 = 2935637) B2935637
theorem B4179853 : Blo 1955435 4179853 := bbase (se 3 (by rfl) ⟨783722, by rfl⟩ : syracuseStep 4179853 = 1567445) (by norm_num)
theorem B5573137 : Blo 1955435 5573137 := bstep (se 2 (by rfl) ⟨2089926, by rfl⟩ : syracuseStep 5573137 = 4179853) B4179853
theorem B7430849 : Blo 1955435 7430849 := bstep (se 2 (by rfl) ⟨2786568, by rfl⟩ : syracuseStep 7430849 = 5573137) B5573137
theorem B4953899 : Blo 1955435 4953899 := bstep (se 1 (by rfl) ⟨3715424, by rfl⟩ : syracuseStep 4953899 = 7430849) B7430849
theorem B3302599 : Blo 1955435 3302599 := bstep (se 1 (by rfl) ⟨2476949, by rfl⟩ : syracuseStep 3302599 = 4953899) B4953899
theorem B4403465 : Blo 1955435 4403465 := bstep (se 2 (by rfl) ⟨1651299, by rfl⟩ : syracuseStep 4403465 = 3302599) B3302599
theorem B2935643 : Blo 1955435 2935643 := bstep (se 1 (by rfl) ⟨2201732, by rfl⟩ : syracuseStep 2935643 = 4403465) B4403465
theorem B1957095 : Blo 1955435 1957095 := bstep (se 1 (by rfl) ⟨1467821, by rfl⟩ : syracuseStep 1957095 = 2935643) B2935643
theorem B2201737 : Blo 1955435 2201737 := bbase (se 2 (by rfl) ⟨825651, by rfl⟩ : syracuseStep 2201737 = 1651303) (by norm_num)
theorem B2935649 : Blo 1955435 2935649 := bstep (se 2 (by rfl) ⟨1100868, by rfl⟩ : syracuseStep 2935649 = 2201737) B2201737
theorem B1957099 : Blo 1955435 1957099 := bstep (se 1 (by rfl) ⟨1467824, by rfl⟩ : syracuseStep 1957099 = 2935649) B2935649
theorem B14107061 : Blo 1955435 14107061 := bbase (se 5 (by rfl) ⟨661268, by rfl⟩ : syracuseStep 14107061 = 1322537) (by norm_num)
theorem B37618829 : Blo 1955435 37618829 := bstep (se 3 (by rfl) ⟨7053530, by rfl⟩ : syracuseStep 37618829 = 14107061) B14107061
theorem B25079219 : Blo 1955435 25079219 := bstep (se 1 (by rfl) ⟨18809414, by rfl⟩ : syracuseStep 25079219 = 37618829) B37618829
theorem B16719479 : Blo 1955435 16719479 := bstep (se 1 (by rfl) ⟨12539609, by rfl⟩ : syracuseStep 16719479 = 25079219) B25079219
theorem B11146319 : Blo 1955435 11146319 := bstep (se 1 (by rfl) ⟨8359739, by rfl⟩ : syracuseStep 11146319 = 16719479) B16719479
theorem B7430879 : Blo 1955435 7430879 := bstep (se 1 (by rfl) ⟨5573159, by rfl⟩ : syracuseStep 7430879 = 11146319) B11146319
theorem B4953919 : Blo 1955435 4953919 := bstep (se 1 (by rfl) ⟨3715439, by rfl⟩ : syracuseStep 4953919 = 7430879) B7430879
theorem B6605225 : Blo 1955435 6605225 := bstep (se 2 (by rfl) ⟨2476959, by rfl⟩ : syracuseStep 6605225 = 4953919) B4953919
theorem B4403483 : Blo 1955435 4403483 := bstep (se 1 (by rfl) ⟨3302612, by rfl⟩ : syracuseStep 4403483 = 6605225) B6605225
theorem B2935655 : Blo 1955435 2935655 := bstep (se 1 (by rfl) ⟨2201741, by rfl⟩ : syracuseStep 2935655 = 4403483) B4403483
theorem B1957103 : Blo 1955435 1957103 := bstep (se 1 (by rfl) ⟨1467827, by rfl⟩ : syracuseStep 1957103 = 2935655) B2935655
theorem B2935661 : Blo 1955435 2935661 := bbase (se 3 (by rfl) ⟨550436, by rfl⟩ : syracuseStep 2935661 = 1100873) (by norm_num)
theorem B1957107 : Blo 1955435 1957107 := bstep (se 1 (by rfl) ⟨1467830, by rfl⟩ : syracuseStep 1957107 = 2935661) B2935661
theorem B4403501 : Blo 1955435 4403501 := bbase (se 3 (by rfl) ⟨825656, by rfl⟩ : syracuseStep 4403501 = 1651313) (by norm_num)
theorem B2935667 : Blo 1955435 2935667 := bstep (se 1 (by rfl) ⟨2201750, by rfl⟩ : syracuseStep 2935667 = 4403501) B4403501
theorem B1957111 : Blo 1955435 1957111 := bstep (se 1 (by rfl) ⟨1467833, by rfl⟩ : syracuseStep 1957111 = 2935667) B2935667
theorem B6269845 : Blo 1955435 6269845 := bbase (se 6 (by rfl) ⟨146949, by rfl⟩ : syracuseStep 6269845 = 293899) (by norm_num)
theorem B8359793 : Blo 1955435 8359793 := bstep (se 2 (by rfl) ⟨3134922, by rfl⟩ : syracuseStep 8359793 = 6269845) B6269845
theorem B5573195 : Blo 1955435 5573195 := bstep (se 1 (by rfl) ⟨4179896, by rfl⟩ : syracuseStep 5573195 = 8359793) B8359793
theorem B3715463 : Blo 1955435 3715463 := bstep (se 1 (by rfl) ⟨2786597, by rfl⟩ : syracuseStep 3715463 = 5573195) B5573195
theorem B2476975 : Blo 1955435 2476975 := bstep (se 1 (by rfl) ⟨1857731, by rfl⟩ : syracuseStep 2476975 = 3715463) B3715463
theorem B3302633 : Blo 1955435 3302633 := bstep (se 2 (by rfl) ⟨1238487, by rfl⟩ : syracuseStep 3302633 = 2476975) B2476975
theorem B2201755 : Blo 1955435 2201755 := bstep (se 1 (by rfl) ⟨1651316, by rfl⟩ : syracuseStep 2201755 = 3302633) B3302633
theorem B2935673 : Blo 1955435 2935673 := bstep (se 2 (by rfl) ⟨1100877, by rfl⟩ : syracuseStep 2935673 = 2201755) B2201755
theorem B1957115 : Blo 1955435 1957115 := bstep (se 1 (by rfl) ⟨1467836, by rfl⟩ : syracuseStep 1957115 = 2935673) B2935673
theorem B5021549 : Blo 1955435 5021549 := bbase (se 3 (by rfl) ⟨941540, by rfl⟩ : syracuseStep 5021549 = 1883081) (by norm_num)
theorem B3347699 : Blo 1955435 3347699 := bstep (se 1 (by rfl) ⟨2510774, by rfl⟩ : syracuseStep 3347699 = 5021549) B5021549
theorem B35708789 : Blo 1955435 35708789 := bstep (se 5 (by rfl) ⟨1673849, by rfl⟩ : syracuseStep 35708789 = 3347699) B3347699
theorem B95223437 : Blo 1955435 95223437 := bstep (se 3 (by rfl) ⟨17854394, by rfl⟩ : syracuseStep 95223437 = 35708789) B35708789
theorem B63482291 : Blo 1955435 63482291 := bstep (se 1 (by rfl) ⟨47611718, by rfl⟩ : syracuseStep 63482291 = 95223437) B95223437
theorem B42321527 : Blo 1955435 42321527 := bstep (se 1 (by rfl) ⟨31741145, by rfl⟩ : syracuseStep 42321527 = 63482291) B63482291
theorem B28214351 : Blo 1955435 28214351 := bstep (se 1 (by rfl) ⟨21160763, by rfl⟩ : syracuseStep 28214351 = 42321527) B42321527
theorem B18809567 : Blo 1955435 18809567 := bstep (se 1 (by rfl) ⟨14107175, by rfl⟩ : syracuseStep 18809567 = 28214351) B28214351
theorem B12539711 : Blo 1955435 12539711 := bstep (se 1 (by rfl) ⟨9404783, by rfl⟩ : syracuseStep 12539711 = 18809567) B18809567
theorem B33439229 : Blo 1955435 33439229 := bstep (se 3 (by rfl) ⟨6269855, by rfl⟩ : syracuseStep 33439229 = 12539711) B12539711
theorem B22292819 : Blo 1955435 22292819 := bstep (se 1 (by rfl) ⟨16719614, by rfl⟩ : syracuseStep 22292819 = 33439229) B33439229
theorem B14861879 : Blo 1955435 14861879 := bstep (se 1 (by rfl) ⟨11146409, by rfl⟩ : syracuseStep 14861879 = 22292819) B22292819
theorem B9907919 : Blo 1955435 9907919 := bstep (se 1 (by rfl) ⟨7430939, by rfl⟩ : syracuseStep 9907919 = 14861879) B14861879
theorem B6605279 : Blo 1955435 6605279 := bstep (se 1 (by rfl) ⟨4953959, by rfl⟩ : syracuseStep 6605279 = 9907919) B9907919
theorem B4403519 : Blo 1955435 4403519 := bstep (se 1 (by rfl) ⟨3302639, by rfl⟩ : syracuseStep 4403519 = 6605279) B6605279
theorem B2935679 : Blo 1955435 2935679 := bstep (se 1 (by rfl) ⟨2201759, by rfl⟩ : syracuseStep 2935679 = 4403519) B4403519
theorem B1957119 : Blo 1955435 1957119 := bstep (se 1 (by rfl) ⟨1467839, by rfl⟩ : syracuseStep 1957119 = 2935679) B2935679
theorem B2935685 : Blo 1955435 2935685 := bbase (se 4 (by rfl) ⟨275220, by rfl⟩ : syracuseStep 2935685 = 550441) (by norm_num)
theorem B1957123 : Blo 1955435 1957123 := bstep (se 1 (by rfl) ⟨1467842, by rfl⟩ : syracuseStep 1957123 = 2935685) B2935685
theorem B3302653 : Blo 1955435 3302653 := bbase (se 3 (by rfl) ⟨619247, by rfl⟩ : syracuseStep 3302653 = 1238495) (by norm_num)
theorem B4403537 : Blo 1955435 4403537 := bstep (se 2 (by rfl) ⟨1651326, by rfl⟩ : syracuseStep 4403537 = 3302653) B3302653
theorem B2935691 : Blo 1955435 2935691 := bstep (se 1 (by rfl) ⟨2201768, by rfl⟩ : syracuseStep 2935691 = 4403537) B4403537
theorem B1957127 : Blo 1955435 1957127 := bstep (se 1 (by rfl) ⟨1467845, by rfl⟩ : syracuseStep 1957127 = 2935691) B2935691
theorem B2201773 : Blo 1955435 2201773 := bbase (se 3 (by rfl) ⟨412832, by rfl⟩ : syracuseStep 2201773 = 825665) (by norm_num)
theorem B2935697 : Blo 1955435 2935697 := bstep (se 2 (by rfl) ⟨1100886, by rfl⟩ : syracuseStep 2935697 = 2201773) B2201773
theorem B1957131 : Blo 1955435 1957131 := bstep (se 1 (by rfl) ⟨1467848, by rfl⟩ : syracuseStep 1957131 = 2935697) B2935697
theorem B6605333 : Blo 1955435 6605333 := bbase (se 6 (by rfl) ⟨154812, by rfl⟩ : syracuseStep 6605333 = 309625) (by norm_num)
theorem B4403555 : Blo 1955435 4403555 := bstep (se 1 (by rfl) ⟨3302666, by rfl⟩ : syracuseStep 4403555 = 6605333) B6605333
theorem B2935703 : Blo 1955435 2935703 := bstep (se 1 (by rfl) ⟨2201777, by rfl⟩ : syracuseStep 2935703 = 4403555) B4403555
theorem B1957135 : Blo 1955435 1957135 := bstep (se 1 (by rfl) ⟨1467851, by rfl⟩ : syracuseStep 1957135 = 2935703) B2935703
theorem B2935709 : Blo 1955435 2935709 := bbase (se 3 (by rfl) ⟨550445, by rfl⟩ : syracuseStep 2935709 = 1100891) (by norm_num)
theorem B1957139 : Blo 1955435 1957139 := bstep (se 1 (by rfl) ⟨1467854, by rfl⟩ : syracuseStep 1957139 = 2935709) B2935709
theorem B4403573 : Blo 1955435 4403573 := bbase (se 5 (by rfl) ⟨206417, by rfl⟩ : syracuseStep 4403573 = 412835) (by norm_num)
theorem B2935715 : Blo 1955435 2935715 := bstep (se 1 (by rfl) ⟨2201786, by rfl⟩ : syracuseStep 2935715 = 4403573) B4403573
theorem B1957143 : Blo 1955435 1957143 := bstep (se 1 (by rfl) ⟨1467857, by rfl⟩ : syracuseStep 1957143 = 2935715) B2935715
theorem B12539893 : Blo 1955435 12539893 := bbase (se 5 (by rfl) ⟨587807, by rfl⟩ : syracuseStep 12539893 = 1175615) (by norm_num)
theorem B16719857 : Blo 1955435 16719857 := bstep (se 2 (by rfl) ⟨6269946, by rfl⟩ : syracuseStep 16719857 = 12539893) B12539893
theorem B11146571 : Blo 1955435 11146571 := bstep (se 1 (by rfl) ⟨8359928, by rfl⟩ : syracuseStep 11146571 = 16719857) B16719857
theorem B7431047 : Blo 1955435 7431047 := bstep (se 1 (by rfl) ⟨5573285, by rfl⟩ : syracuseStep 7431047 = 11146571) B11146571
theorem B4954031 : Blo 1955435 4954031 := bstep (se 1 (by rfl) ⟨3715523, by rfl⟩ : syracuseStep 4954031 = 7431047) B7431047
theorem B3302687 : Blo 1955435 3302687 := bstep (se 1 (by rfl) ⟨2477015, by rfl⟩ : syracuseStep 3302687 = 4954031) B4954031
theorem B2201791 : Blo 1955435 2201791 := bstep (se 1 (by rfl) ⟨1651343, by rfl⟩ : syracuseStep 2201791 = 3302687) B3302687
theorem B2935721 : Blo 1955435 2935721 := bstep (se 2 (by rfl) ⟨1100895, by rfl⟩ : syracuseStep 2935721 = 2201791) B2201791
theorem B1957147 : Blo 1955435 1957147 := bstep (se 1 (by rfl) ⟨1467860, by rfl⟩ : syracuseStep 1957147 = 2935721) B2935721
theorem B7431061 : Blo 1955435 7431061 := bbase (se 6 (by rfl) ⟨174165, by rfl⟩ : syracuseStep 7431061 = 348331) (by norm_num)
theorem B9908081 : Blo 1955435 9908081 := bstep (se 2 (by rfl) ⟨3715530, by rfl⟩ : syracuseStep 9908081 = 7431061) B7431061
theorem B6605387 : Blo 1955435 6605387 := bstep (se 1 (by rfl) ⟨4954040, by rfl⟩ : syracuseStep 6605387 = 9908081) B9908081
theorem B4403591 : Blo 1955435 4403591 := bstep (se 1 (by rfl) ⟨3302693, by rfl⟩ : syracuseStep 4403591 = 6605387) B6605387
theorem B2935727 : Blo 1955435 2935727 := bstep (se 1 (by rfl) ⟨2201795, by rfl⟩ : syracuseStep 2935727 = 4403591) B4403591
theorem B1957151 : Blo 1955435 1957151 := bstep (se 1 (by rfl) ⟨1467863, by rfl⟩ : syracuseStep 1957151 = 2935727) B2935727
theorem B2935733 : Blo 1955435 2935733 := bbase (se 5 (by rfl) ⟨137612, by rfl⟩ : syracuseStep 2935733 = 275225) (by norm_num)
theorem B1957155 : Blo 1955435 1957155 := bstep (se 1 (by rfl) ⟨1467866, by rfl⟩ : syracuseStep 1957155 = 2935733) B2935733
theorem B4954061 : Blo 1955435 4954061 := bbase (se 3 (by rfl) ⟨928886, by rfl⟩ : syracuseStep 4954061 = 1857773) (by norm_num)
theorem B3302707 : Blo 1955435 3302707 := bstep (se 1 (by rfl) ⟨2477030, by rfl⟩ : syracuseStep 3302707 = 4954061) B4954061
theorem B4403609 : Blo 1955435 4403609 := bstep (se 2 (by rfl) ⟨1651353, by rfl⟩ : syracuseStep 4403609 = 3302707) B3302707
theorem B2935739 : Blo 1955435 2935739 := bstep (se 1 (by rfl) ⟨2201804, by rfl⟩ : syracuseStep 2935739 = 4403609) B4403609
theorem B1957159 : Blo 1955435 1957159 := bstep (se 1 (by rfl) ⟨1467869, by rfl⟩ : syracuseStep 1957159 = 2935739) B2935739
theorem B2201809 : Blo 1955435 2201809 := bbase (se 2 (by rfl) ⟨825678, by rfl⟩ : syracuseStep 2201809 = 1651357) (by norm_num)
theorem B2935745 : Blo 1955435 2935745 := bstep (se 2 (by rfl) ⟨1100904, by rfl⟩ : syracuseStep 2935745 = 2201809) B2201809
theorem B1957163 : Blo 1955435 1957163 := bstep (se 1 (by rfl) ⟨1467872, by rfl⟩ : syracuseStep 1957163 = 2935745) B2935745
theorem B4303829 : Blo 1955435 4303829 := bbase (se 7 (by rfl) ⟨50435, by rfl⟩ : syracuseStep 4303829 = 100871) (by norm_num)
theorem B2869219 : Blo 1955435 2869219 := bstep (se 1 (by rfl) ⟨2151914, by rfl⟩ : syracuseStep 2869219 = 4303829) B4303829
theorem B3825625 : Blo 1955435 3825625 := bstep (se 2 (by rfl) ⟨1434609, by rfl⟩ : syracuseStep 3825625 = 2869219) B2869219
theorem B5100833 : Blo 1955435 5100833 := bstep (se 2 (by rfl) ⟨1912812, by rfl⟩ : syracuseStep 5100833 = 3825625) B3825625
theorem B3400555 : Blo 1955435 3400555 := bstep (se 1 (by rfl) ⟨2550416, by rfl⟩ : syracuseStep 3400555 = 5100833) B5100833
theorem B4534073 : Blo 1955435 4534073 := bstep (se 2 (by rfl) ⟨1700277, by rfl⟩ : syracuseStep 4534073 = 3400555) B3400555
theorem B3022715 : Blo 1955435 3022715 := bstep (se 1 (by rfl) ⟨2267036, by rfl⟩ : syracuseStep 3022715 = 4534073) B4534073
theorem B2015143 : Blo 1955435 2015143 := bstep (se 1 (by rfl) ⟨1511357, by rfl⟩ : syracuseStep 2015143 = 3022715) B3022715
theorem B10747429 : Blo 1955435 10747429 := bstep (se 4 (by rfl) ⟨1007571, by rfl⟩ : syracuseStep 10747429 = 2015143) B2015143
theorem B229278485 : Blo 1955435 229278485 := bstep (se 6 (by rfl) ⟨5373714, by rfl⟩ : syracuseStep 229278485 = 10747429) B10747429
theorem B611409293 : Blo 1955435 611409293 := bstep (se 3 (by rfl) ⟨114639242, by rfl⟩ : syracuseStep 611409293 = 229278485) B229278485
theorem B407606195 : Blo 1955435 407606195 := bstep (se 1 (by rfl) ⟨305704646, by rfl⟩ : syracuseStep 407606195 = 611409293) B611409293
theorem B1086949853 : Blo 1955435 1086949853 := bstep (se 3 (by rfl) ⟨203803097, by rfl⟩ : syracuseStep 1086949853 = 407606195) B407606195
theorem B724633235 : Blo 1955435 724633235 := bstep (se 1 (by rfl) ⟨543474926, by rfl⟩ : syracuseStep 724633235 = 1086949853) B1086949853
theorem B483088823 : Blo 1955435 483088823 := bstep (se 1 (by rfl) ⟨362316617, by rfl⟩ : syracuseStep 483088823 = 724633235) B724633235
theorem B322059215 : Blo 1955435 322059215 := bstep (se 1 (by rfl) ⟨241544411, by rfl⟩ : syracuseStep 322059215 = 483088823) B483088823
theorem B214706143 : Blo 1955435 214706143 := bstep (se 1 (by rfl) ⟨161029607, by rfl⟩ : syracuseStep 214706143 = 322059215) B322059215
theorem B286274857 : Blo 1955435 286274857 := bstep (se 2 (by rfl) ⟨107353071, by rfl⟩ : syracuseStep 286274857 = 214706143) B214706143
theorem B381699809 : Blo 1955435 381699809 := bstep (se 2 (by rfl) ⟨143137428, by rfl⟩ : syracuseStep 381699809 = 286274857) B286274857
theorem B254466539 : Blo 1955435 254466539 := bstep (se 1 (by rfl) ⟨190849904, by rfl⟩ : syracuseStep 254466539 = 381699809) B381699809
theorem B169644359 : Blo 1955435 169644359 := bstep (se 1 (by rfl) ⟨127233269, by rfl⟩ : syracuseStep 169644359 = 254466539) B254466539
theorem B452384957 : Blo 1955435 452384957 := bstep (se 3 (by rfl) ⟨84822179, by rfl⟩ : syracuseStep 452384957 = 169644359) B169644359
theorem B1206359885 : Blo 1955435 1206359885 := bstep (se 3 (by rfl) ⟨226192478, by rfl⟩ : syracuseStep 1206359885 = 452384957) B452384957
theorem B804239923 : Blo 1955435 804239923 := bstep (se 1 (by rfl) ⟨603179942, by rfl⟩ : syracuseStep 804239923 = 1206359885) B1206359885
theorem B1072319897 : Blo 1955435 1072319897 := bstep (se 2 (by rfl) ⟨402119961, by rfl⟩ : syracuseStep 1072319897 = 804239923) B804239923
theorem B714879931 : Blo 1955435 714879931 := bstep (se 1 (by rfl) ⟨536159948, by rfl⟩ : syracuseStep 714879931 = 1072319897) B1072319897
theorem B953173241 : Blo 1955435 953173241 := bstep (se 2 (by rfl) ⟨357439965, by rfl⟩ : syracuseStep 953173241 = 714879931) B714879931
theorem B635448827 : Blo 1955435 635448827 := bstep (se 1 (by rfl) ⟨476586620, by rfl⟩ : syracuseStep 635448827 = 953173241) B953173241
theorem B423632551 : Blo 1955435 423632551 := bstep (se 1 (by rfl) ⟨317724413, by rfl⟩ : syracuseStep 423632551 = 635448827) B635448827
theorem B564843401 : Blo 1955435 564843401 := bstep (se 2 (by rfl) ⟨211816275, by rfl⟩ : syracuseStep 564843401 = 423632551) B423632551
theorem B376562267 : Blo 1955435 376562267 := bstep (se 1 (by rfl) ⟨282421700, by rfl⟩ : syracuseStep 376562267 = 564843401) B564843401
theorem B251041511 : Blo 1955435 251041511 := bstep (se 1 (by rfl) ⟨188281133, by rfl⟩ : syracuseStep 251041511 = 376562267) B376562267
theorem B167361007 : Blo 1955435 167361007 := bstep (se 1 (by rfl) ⟨125520755, by rfl⟩ : syracuseStep 167361007 = 251041511) B251041511
theorem B223148009 : Blo 1955435 223148009 := bstep (se 2 (by rfl) ⟨83680503, by rfl⟩ : syracuseStep 223148009 = 167361007) B167361007
theorem B148765339 : Blo 1955435 148765339 := bstep (se 1 (by rfl) ⟨111574004, by rfl⟩ : syracuseStep 148765339 = 223148009) B223148009
theorem B198353785 : Blo 1955435 198353785 := bstep (se 2 (by rfl) ⟨74382669, by rfl⟩ : syracuseStep 198353785 = 148765339) B148765339
theorem B264471713 : Blo 1955435 264471713 := bstep (se 2 (by rfl) ⟨99176892, by rfl⟩ : syracuseStep 264471713 = 198353785) B198353785
theorem B176314475 : Blo 1955435 176314475 := bstep (se 1 (by rfl) ⟨132235856, by rfl⟩ : syracuseStep 176314475 = 264471713) B264471713
theorem B117542983 : Blo 1955435 117542983 := bstep (se 1 (by rfl) ⟨88157237, by rfl⟩ : syracuseStep 117542983 = 176314475) B176314475
theorem B156723977 : Blo 1955435 156723977 := bstep (se 2 (by rfl) ⟨58771491, by rfl⟩ : syracuseStep 156723977 = 117542983) B117542983
theorem B104482651 : Blo 1955435 104482651 := bstep (se 1 (by rfl) ⟨78361988, by rfl⟩ : syracuseStep 104482651 = 156723977) B156723977
theorem B139310201 : Blo 1955435 139310201 := bstep (se 2 (by rfl) ⟨52241325, by rfl⟩ : syracuseStep 139310201 = 104482651) B104482651
theorem B92873467 : Blo 1955435 92873467 := bstep (se 1 (by rfl) ⟨69655100, by rfl⟩ : syracuseStep 92873467 = 139310201) B139310201
theorem B123831289 : Blo 1955435 123831289 := bstep (se 2 (by rfl) ⟨46436733, by rfl⟩ : syracuseStep 123831289 = 92873467) B92873467
theorem B165108385 : Blo 1955435 165108385 := bstep (se 2 (by rfl) ⟨61915644, by rfl⟩ : syracuseStep 165108385 = 123831289) B123831289
theorem B220144513 : Blo 1955435 220144513 := bstep (se 2 (by rfl) ⟨82554192, by rfl⟩ : syracuseStep 220144513 = 165108385) B165108385
theorem B293526017 : Blo 1955435 293526017 := bstep (se 2 (by rfl) ⟨110072256, by rfl⟩ : syracuseStep 293526017 = 220144513) B220144513
theorem B195684011 : Blo 1955435 195684011 := bstep (se 1 (by rfl) ⟨146763008, by rfl⟩ : syracuseStep 195684011 = 293526017) B293526017
theorem B130456007 : Blo 1955435 130456007 := bstep (se 1 (by rfl) ⟨97842005, by rfl⟩ : syracuseStep 130456007 = 195684011) B195684011
theorem B86970671 : Blo 1955435 86970671 := bstep (se 1 (by rfl) ⟨65228003, by rfl⟩ : syracuseStep 86970671 = 130456007) B130456007
theorem B57980447 : Blo 1955435 57980447 := bstep (se 1 (by rfl) ⟨43485335, by rfl⟩ : syracuseStep 57980447 = 86970671) B86970671
theorem B38653631 : Blo 1955435 38653631 := bstep (se 1 (by rfl) ⟨28990223, by rfl⟩ : syracuseStep 38653631 = 57980447) B57980447
theorem B25769087 : Blo 1955435 25769087 := bstep (se 1 (by rfl) ⟨19326815, by rfl⟩ : syracuseStep 25769087 = 38653631) B38653631
theorem B17179391 : Blo 1955435 17179391 := bstep (se 1 (by rfl) ⟨12884543, by rfl⟩ : syracuseStep 17179391 = 25769087) B25769087
theorem B11452927 : Blo 1955435 11452927 := bstep (se 1 (by rfl) ⟨8589695, by rfl⟩ : syracuseStep 11452927 = 17179391) B17179391
theorem B15270569 : Blo 1955435 15270569 := bstep (se 2 (by rfl) ⟨5726463, by rfl⟩ : syracuseStep 15270569 = 11452927) B11452927
theorem B10180379 : Blo 1955435 10180379 := bstep (se 1 (by rfl) ⟨7635284, by rfl⟩ : syracuseStep 10180379 = 15270569) B15270569
theorem B6786919 : Blo 1955435 6786919 := bstep (se 1 (by rfl) ⟨5090189, by rfl⟩ : syracuseStep 6786919 = 10180379) B10180379
theorem B36196901 : Blo 1955435 36196901 := bstep (se 4 (by rfl) ⟨3393459, by rfl⟩ : syracuseStep 36196901 = 6786919) B6786919
theorem B24131267 : Blo 1955435 24131267 := bstep (se 1 (by rfl) ⟨18098450, by rfl⟩ : syracuseStep 24131267 = 36196901) B36196901
theorem B16087511 : Blo 1955435 16087511 := bstep (se 1 (by rfl) ⟨12065633, by rfl⟩ : syracuseStep 16087511 = 24131267) B24131267
theorem B10725007 : Blo 1955435 10725007 := bstep (se 1 (by rfl) ⟨8043755, by rfl⟩ : syracuseStep 10725007 = 16087511) B16087511
theorem B14300009 : Blo 1955435 14300009 := bstep (se 2 (by rfl) ⟨5362503, by rfl⟩ : syracuseStep 14300009 = 10725007) B10725007
theorem B9533339 : Blo 1955435 9533339 := bstep (se 1 (by rfl) ⟨7150004, by rfl⟩ : syracuseStep 9533339 = 14300009) B14300009
theorem B6355559 : Blo 1955435 6355559 := bstep (se 1 (by rfl) ⟨4766669, by rfl⟩ : syracuseStep 6355559 = 9533339) B9533339
theorem B4237039 : Blo 1955435 4237039 := bstep (se 1 (by rfl) ⟨3177779, by rfl⟩ : syracuseStep 4237039 = 6355559) B6355559
theorem B22597541 : Blo 1955435 22597541 := bstep (se 4 (by rfl) ⟨2118519, by rfl⟩ : syracuseStep 22597541 = 4237039) B4237039
theorem B15065027 : Blo 1955435 15065027 := bstep (se 1 (by rfl) ⟨11298770, by rfl⟩ : syracuseStep 15065027 = 22597541) B22597541
theorem B10043351 : Blo 1955435 10043351 := bstep (se 1 (by rfl) ⟨7532513, by rfl⟩ : syracuseStep 10043351 = 15065027) B15065027
theorem B6695567 : Blo 1955435 6695567 := bstep (se 1 (by rfl) ⟨5021675, by rfl⟩ : syracuseStep 6695567 = 10043351) B10043351
theorem B4463711 : Blo 1955435 4463711 := bstep (se 1 (by rfl) ⟨3347783, by rfl⟩ : syracuseStep 4463711 = 6695567) B6695567
theorem B2975807 : Blo 1955435 2975807 := bstep (se 1 (by rfl) ⟨2231855, by rfl⟩ : syracuseStep 2975807 = 4463711) B4463711
theorem B1983871 : Blo 1955435 1983871 := bstep (se 1 (by rfl) ⟨1487903, by rfl⟩ : syracuseStep 1983871 = 2975807) B2975807
theorem B10580645 : Blo 1955435 10580645 := bstep (se 4 (by rfl) ⟨991935, by rfl⟩ : syracuseStep 10580645 = 1983871) B1983871
theorem B7053763 : Blo 1955435 7053763 := bstep (se 1 (by rfl) ⟨5290322, by rfl⟩ : syracuseStep 7053763 = 10580645) B10580645
theorem B9405017 : Blo 1955435 9405017 := bstep (se 2 (by rfl) ⟨3526881, by rfl⟩ : syracuseStep 9405017 = 7053763) B7053763
theorem B6270011 : Blo 1955435 6270011 := bstep (se 1 (by rfl) ⟨4702508, by rfl⟩ : syracuseStep 6270011 = 9405017) B9405017
theorem B4180007 : Blo 1955435 4180007 := bstep (se 1 (by rfl) ⟨3135005, by rfl⟩ : syracuseStep 4180007 = 6270011) B6270011
theorem B2786671 : Blo 1955435 2786671 := bstep (se 1 (by rfl) ⟨2090003, by rfl⟩ : syracuseStep 2786671 = 4180007) B4180007
theorem B3715561 : Blo 1955435 3715561 := bstep (se 2 (by rfl) ⟨1393335, by rfl⟩ : syracuseStep 3715561 = 2786671) B2786671
theorem B4954081 : Blo 1955435 4954081 := bstep (se 2 (by rfl) ⟨1857780, by rfl⟩ : syracuseStep 4954081 = 3715561) B3715561
theorem B6605441 : Blo 1955435 6605441 := bstep (se 2 (by rfl) ⟨2477040, by rfl⟩ : syracuseStep 6605441 = 4954081) B4954081
theorem B4403627 : Blo 1955435 4403627 := bstep (se 1 (by rfl) ⟨3302720, by rfl⟩ : syracuseStep 4403627 = 6605441) B6605441
theorem B2935751 : Blo 1955435 2935751 := bstep (se 1 (by rfl) ⟨2201813, by rfl⟩ : syracuseStep 2935751 = 4403627) B4403627
theorem B1957167 : Blo 1955435 1957167 := bstep (se 1 (by rfl) ⟨1467875, by rfl⟩ : syracuseStep 1957167 = 2935751) B2935751
theorem B2935757 : Blo 1955435 2935757 := bbase (se 3 (by rfl) ⟨550454, by rfl⟩ : syracuseStep 2935757 = 1100909) (by norm_num)
theorem B1957171 : Blo 1955435 1957171 := bstep (se 1 (by rfl) ⟨1467878, by rfl⟩ : syracuseStep 1957171 = 2935757) B2935757
theorem B4403645 : Blo 1955435 4403645 := bbase (se 3 (by rfl) ⟨825683, by rfl⟩ : syracuseStep 4403645 = 1651367) (by norm_num)
theorem B2935763 : Blo 1955435 2935763 := bstep (se 1 (by rfl) ⟨2201822, by rfl⟩ : syracuseStep 2935763 = 4403645) B4403645
theorem B1957175 : Blo 1955435 1957175 := bstep (se 1 (by rfl) ⟨1467881, by rfl⟩ : syracuseStep 1957175 = 2935763) B2935763
theorem B3302741 : Blo 1955435 3302741 := bbase (se 12 (by rfl) ⟨1209, by rfl⟩ : syracuseStep 3302741 = 2419) (by norm_num)
theorem B2201827 : Blo 1955435 2201827 := bstep (se 1 (by rfl) ⟨1651370, by rfl⟩ : syracuseStep 2201827 = 3302741) B3302741
theorem B2935769 : Blo 1955435 2935769 := bstep (se 2 (by rfl) ⟨1100913, by rfl⟩ : syracuseStep 2935769 = 2201827) B2201827
theorem B1957179 : Blo 1955435 1957179 := bstep (se 1 (by rfl) ⟨1467884, by rfl⟩ : syracuseStep 1957179 = 2935769) B2935769
theorem B2351273 : Blo 1955435 2351273 := bbase (se 2 (by rfl) ⟨881727, by rfl⟩ : syracuseStep 2351273 = 1763455) (by norm_num)
theorem B6270061 : Blo 1955435 6270061 := bstep (se 3 (by rfl) ⟨1175636, by rfl⟩ : syracuseStep 6270061 = 2351273) B2351273
theorem B8360081 : Blo 1955435 8360081 := bstep (se 2 (by rfl) ⟨3135030, by rfl⟩ : syracuseStep 8360081 = 6270061) B6270061
theorem B5573387 : Blo 1955435 5573387 := bstep (se 1 (by rfl) ⟨4180040, by rfl⟩ : syracuseStep 5573387 = 8360081) B8360081
theorem B14862365 : Blo 1955435 14862365 := bstep (se 3 (by rfl) ⟨2786693, by rfl⟩ : syracuseStep 14862365 = 5573387) B5573387
theorem B9908243 : Blo 1955435 9908243 := bstep (se 1 (by rfl) ⟨7431182, by rfl⟩ : syracuseStep 9908243 = 14862365) B14862365
theorem B6605495 : Blo 1955435 6605495 := bstep (se 1 (by rfl) ⟨4954121, by rfl⟩ : syracuseStep 6605495 = 9908243) B9908243
theorem B4403663 : Blo 1955435 4403663 := bstep (se 1 (by rfl) ⟨3302747, by rfl⟩ : syracuseStep 4403663 = 6605495) B6605495
theorem B2935775 : Blo 1955435 2935775 := bstep (se 1 (by rfl) ⟨2201831, by rfl⟩ : syracuseStep 2935775 = 4403663) B4403663
theorem B1957183 : Blo 1955435 1957183 := bstep (se 1 (by rfl) ⟨1467887, by rfl⟩ : syracuseStep 1957183 = 2935775) B2935775
theorem B2935781 : Blo 1955435 2935781 := bbase (se 4 (by rfl) ⟨275229, by rfl⟩ : syracuseStep 2935781 = 550459) (by norm_num)
theorem B1957187 : Blo 1955435 1957187 := bstep (se 1 (by rfl) ⟨1467890, by rfl⟩ : syracuseStep 1957187 = 2935781) B2935781
theorem B8360117 : Blo 1955435 8360117 := bbase (se 5 (by rfl) ⟨391880, by rfl⟩ : syracuseStep 8360117 = 783761) (by norm_num)
theorem B5573411 : Blo 1955435 5573411 := bstep (se 1 (by rfl) ⟨4180058, by rfl⟩ : syracuseStep 5573411 = 8360117) B8360117
theorem B3715607 : Blo 1955435 3715607 := bstep (se 1 (by rfl) ⟨2786705, by rfl⟩ : syracuseStep 3715607 = 5573411) B5573411
theorem B2477071 : Blo 1955435 2477071 := bstep (se 1 (by rfl) ⟨1857803, by rfl⟩ : syracuseStep 2477071 = 3715607) B3715607
theorem B3302761 : Blo 1955435 3302761 := bstep (se 2 (by rfl) ⟨1238535, by rfl⟩ : syracuseStep 3302761 = 2477071) B2477071
theorem B4403681 : Blo 1955435 4403681 := bstep (se 2 (by rfl) ⟨1651380, by rfl⟩ : syracuseStep 4403681 = 3302761) B3302761
theorem B2935787 : Blo 1955435 2935787 := bstep (se 1 (by rfl) ⟨2201840, by rfl⟩ : syracuseStep 2935787 = 4403681) B4403681
theorem B1957191 : Blo 1955435 1957191 := bstep (se 1 (by rfl) ⟨1467893, by rfl⟩ : syracuseStep 1957191 = 2935787) B2935787
theorem B2201845 : Blo 1955435 2201845 := bbase (se 5 (by rfl) ⟨103211, by rfl⟩ : syracuseStep 2201845 = 206423) (by norm_num)
theorem B2935793 : Blo 1955435 2935793 := bstep (se 2 (by rfl) ⟨1100922, by rfl⟩ : syracuseStep 2935793 = 2201845) B2201845
theorem B1957195 : Blo 1955435 1957195 := bstep (se 1 (by rfl) ⟨1467896, by rfl⟩ : syracuseStep 1957195 = 2935793) B2935793
theorem B2477081 : Blo 1955435 2477081 := bbase (se 2 (by rfl) ⟨928905, by rfl⟩ : syracuseStep 2477081 = 1857811) (by norm_num)
theorem B6605549 : Blo 1955435 6605549 := bstep (se 3 (by rfl) ⟨1238540, by rfl⟩ : syracuseStep 6605549 = 2477081) B2477081
theorem B4403699 : Blo 1955435 4403699 := bstep (se 1 (by rfl) ⟨3302774, by rfl⟩ : syracuseStep 4403699 = 6605549) B6605549
theorem B2935799 : Blo 1955435 2935799 := bstep (se 1 (by rfl) ⟨2201849, by rfl⟩ : syracuseStep 2935799 = 4403699) B4403699
theorem B1957199 : Blo 1955435 1957199 := bstep (se 1 (by rfl) ⟨1467899, by rfl⟩ : syracuseStep 1957199 = 2935799) B2935799
theorem B2935805 : Blo 1955435 2935805 := bbase (se 3 (by rfl) ⟨550463, by rfl⟩ : syracuseStep 2935805 = 1100927) (by norm_num)
theorem B1957203 : Blo 1955435 1957203 := bstep (se 1 (by rfl) ⟨1467902, by rfl⟩ : syracuseStep 1957203 = 2935805) B2935805
theorem B4403717 : Blo 1955435 4403717 := bbase (se 4 (by rfl) ⟨412848, by rfl⟩ : syracuseStep 4403717 = 825697) (by norm_num)
theorem B2935811 : Blo 1955435 2935811 := bstep (se 1 (by rfl) ⟨2201858, by rfl⟩ : syracuseStep 2935811 = 4403717) B4403717
theorem B1957207 : Blo 1955435 1957207 := bstep (se 1 (by rfl) ⟨1467905, by rfl⟩ : syracuseStep 1957207 = 2935811) B2935811
theorem B3715645 : Blo 1955435 3715645 := bbase (se 3 (by rfl) ⟨696683, by rfl⟩ : syracuseStep 3715645 = 1393367) (by norm_num)
theorem B4954193 : Blo 1955435 4954193 := bstep (se 2 (by rfl) ⟨1857822, by rfl⟩ : syracuseStep 4954193 = 3715645) B3715645
theorem B3302795 : Blo 1955435 3302795 := bstep (se 1 (by rfl) ⟨2477096, by rfl⟩ : syracuseStep 3302795 = 4954193) B4954193
theorem B2201863 : Blo 1955435 2201863 := bstep (se 1 (by rfl) ⟨1651397, by rfl⟩ : syracuseStep 2201863 = 3302795) B3302795
theorem B2935817 : Blo 1955435 2935817 := bstep (se 2 (by rfl) ⟨1100931, by rfl⟩ : syracuseStep 2935817 = 2201863) B2201863
theorem B1957211 : Blo 1955435 1957211 := bstep (se 1 (by rfl) ⟨1467908, by rfl⟩ : syracuseStep 1957211 = 2935817) B2935817
theorem B9908405 : Blo 1955435 9908405 := bbase (se 5 (by rfl) ⟨464456, by rfl⟩ : syracuseStep 9908405 = 928913) (by norm_num)
theorem B6605603 : Blo 1955435 6605603 := bstep (se 1 (by rfl) ⟨4954202, by rfl⟩ : syracuseStep 6605603 = 9908405) B9908405
theorem B4403735 : Blo 1955435 4403735 := bstep (se 1 (by rfl) ⟨3302801, by rfl⟩ : syracuseStep 4403735 = 6605603) B6605603
theorem B2935823 : Blo 1955435 2935823 := bstep (se 1 (by rfl) ⟨2201867, by rfl⟩ : syracuseStep 2935823 = 4403735) B4403735
theorem B1957215 : Blo 1955435 1957215 := bstep (se 1 (by rfl) ⟨1467911, by rfl⟩ : syracuseStep 1957215 = 2935823) B2935823
theorem B2935829 : Blo 1955435 2935829 := bbase (se 6 (by rfl) ⟨68808, by rfl⟩ : syracuseStep 2935829 = 137617) (by norm_num)
theorem B1957219 : Blo 1955435 1957219 := bstep (se 1 (by rfl) ⟨1467914, by rfl⟩ : syracuseStep 1957219 = 2935829) B2935829
theorem B4463837 : Blo 1955435 4463837 := bbase (se 3 (by rfl) ⟨836969, by rfl⟩ : syracuseStep 4463837 = 1673939) (by norm_num)
theorem B2975891 : Blo 1955435 2975891 := bstep (se 1 (by rfl) ⟨2231918, by rfl⟩ : syracuseStep 2975891 = 4463837) B4463837
theorem B31742837 : Blo 1955435 31742837 := bstep (se 5 (by rfl) ⟨1487945, by rfl⟩ : syracuseStep 31742837 = 2975891) B2975891
theorem B21161891 : Blo 1955435 21161891 := bstep (se 1 (by rfl) ⟨15871418, by rfl⟩ : syracuseStep 21161891 = 31742837) B31742837
theorem B14107927 : Blo 1955435 14107927 := bstep (se 1 (by rfl) ⟨10580945, by rfl⟩ : syracuseStep 14107927 = 21161891) B21161891
theorem B18810569 : Blo 1955435 18810569 := bstep (se 2 (by rfl) ⟨7053963, by rfl⟩ : syracuseStep 18810569 = 14107927) B14107927
theorem B12540379 : Blo 1955435 12540379 := bstep (se 1 (by rfl) ⟨9405284, by rfl⟩ : syracuseStep 12540379 = 18810569) B18810569
theorem B16720505 : Blo 1955435 16720505 := bstep (se 2 (by rfl) ⟨6270189, by rfl⟩ : syracuseStep 16720505 = 12540379) B12540379
theorem B11147003 : Blo 1955435 11147003 := bstep (se 1 (by rfl) ⟨8360252, by rfl⟩ : syracuseStep 11147003 = 16720505) B16720505
theorem B7431335 : Blo 1955435 7431335 := bstep (se 1 (by rfl) ⟨5573501, by rfl⟩ : syracuseStep 7431335 = 11147003) B11147003
theorem B4954223 : Blo 1955435 4954223 := bstep (se 1 (by rfl) ⟨3715667, by rfl⟩ : syracuseStep 4954223 = 7431335) B7431335
theorem B3302815 : Blo 1955435 3302815 := bstep (se 1 (by rfl) ⟨2477111, by rfl⟩ : syracuseStep 3302815 = 4954223) B4954223
theorem B4403753 : Blo 1955435 4403753 := bstep (se 2 (by rfl) ⟨1651407, by rfl⟩ : syracuseStep 4403753 = 3302815) B3302815
theorem B2935835 : Blo 1955435 2935835 := bstep (se 1 (by rfl) ⟨2201876, by rfl⟩ : syracuseStep 2935835 = 4403753) B4403753
theorem B1957223 : Blo 1955435 1957223 := bstep (se 1 (by rfl) ⟨1467917, by rfl⟩ : syracuseStep 1957223 = 2935835) B2935835
theorem B2201881 : Blo 1955435 2201881 := bbase (se 2 (by rfl) ⟨825705, by rfl⟩ : syracuseStep 2201881 = 1651411) (by norm_num)
theorem B2935841 : Blo 1955435 2935841 := bstep (se 2 (by rfl) ⟨1100940, by rfl⟩ : syracuseStep 2935841 = 2201881) B2201881
theorem B1957227 : Blo 1955435 1957227 := bstep (se 1 (by rfl) ⟨1467920, by rfl⟩ : syracuseStep 1957227 = 2935841) B2935841
theorem B7431365 : Blo 1955435 7431365 := bbase (se 4 (by rfl) ⟨696690, by rfl⟩ : syracuseStep 7431365 = 1393381) (by norm_num)
theorem B4954243 : Blo 1955435 4954243 := bstep (se 1 (by rfl) ⟨3715682, by rfl⟩ : syracuseStep 4954243 = 7431365) B7431365
theorem B6605657 : Blo 1955435 6605657 := bstep (se 2 (by rfl) ⟨2477121, by rfl⟩ : syracuseStep 6605657 = 4954243) B4954243
theorem B4403771 : Blo 1955435 4403771 := bstep (se 1 (by rfl) ⟨3302828, by rfl⟩ : syracuseStep 4403771 = 6605657) B6605657
theorem B2935847 : Blo 1955435 2935847 := bstep (se 1 (by rfl) ⟨2201885, by rfl⟩ : syracuseStep 2935847 = 4403771) B4403771
theorem B1957231 : Blo 1955435 1957231 := bstep (se 1 (by rfl) ⟨1467923, by rfl⟩ : syracuseStep 1957231 = 2935847) B2935847
theorem B2935853 : Blo 1955435 2935853 := bbase (se 3 (by rfl) ⟨550472, by rfl⟩ : syracuseStep 2935853 = 1100945) (by norm_num)
theorem B1957235 : Blo 1955435 1957235 := bstep (se 1 (by rfl) ⟨1467926, by rfl⟩ : syracuseStep 1957235 = 2935853) B2935853
theorem B4403789 : Blo 1955435 4403789 := bbase (se 3 (by rfl) ⟨825710, by rfl⟩ : syracuseStep 4403789 = 1651421) (by norm_num)
theorem B2935859 : Blo 1955435 2935859 := bstep (se 1 (by rfl) ⟨2201894, by rfl⟩ : syracuseStep 2935859 = 4403789) B4403789
theorem B1957239 : Blo 1955435 1957239 := bstep (se 1 (by rfl) ⟨1467929, by rfl⟩ : syracuseStep 1957239 = 2935859) B2935859
theorem B2477137 : Blo 1955435 2477137 := bbase (se 2 (by rfl) ⟨928926, by rfl⟩ : syracuseStep 2477137 = 1857853) (by norm_num)
theorem B3302849 : Blo 1955435 3302849 := bstep (se 2 (by rfl) ⟨1238568, by rfl⟩ : syracuseStep 3302849 = 2477137) B2477137
theorem B2201899 : Blo 1955435 2201899 := bstep (se 1 (by rfl) ⟨1651424, by rfl⟩ : syracuseStep 2201899 = 3302849) B3302849
theorem B2935865 : Blo 1955435 2935865 := bstep (se 2 (by rfl) ⟨1100949, by rfl⟩ : syracuseStep 2935865 = 2201899) B2201899
theorem B1957243 : Blo 1955435 1957243 := bstep (se 1 (by rfl) ⟨1467932, by rfl⟩ : syracuseStep 1957243 = 2935865) B2935865
theorem B3135133 : Blo 1955435 3135133 := bbase (se 3 (by rfl) ⟨587837, by rfl⟩ : syracuseStep 3135133 = 1175675) (by norm_num)
theorem B4180177 : Blo 1955435 4180177 := bstep (se 2 (by rfl) ⟨1567566, by rfl⟩ : syracuseStep 4180177 = 3135133) B3135133
theorem B22294277 : Blo 1955435 22294277 := bstep (se 4 (by rfl) ⟨2090088, by rfl⟩ : syracuseStep 22294277 = 4180177) B4180177
theorem B14862851 : Blo 1955435 14862851 := bstep (se 1 (by rfl) ⟨11147138, by rfl⟩ : syracuseStep 14862851 = 22294277) B22294277
theorem B9908567 : Blo 1955435 9908567 := bstep (se 1 (by rfl) ⟨7431425, by rfl⟩ : syracuseStep 9908567 = 14862851) B14862851
theorem B6605711 : Blo 1955435 6605711 := bstep (se 1 (by rfl) ⟨4954283, by rfl⟩ : syracuseStep 6605711 = 9908567) B9908567
theorem B4403807 : Blo 1955435 4403807 := bstep (se 1 (by rfl) ⟨3302855, by rfl⟩ : syracuseStep 4403807 = 6605711) B6605711
theorem B2935871 : Blo 1955435 2935871 := bstep (se 1 (by rfl) ⟨2201903, by rfl⟩ : syracuseStep 2935871 = 4403807) B4403807
theorem B1957247 : Blo 1955435 1957247 := bstep (se 1 (by rfl) ⟨1467935, by rfl⟩ : syracuseStep 1957247 = 2935871) B2935871
theorem B2935877 : Blo 1955435 2935877 := bbase (se 4 (by rfl) ⟨275238, by rfl⟩ : syracuseStep 2935877 = 550477) (by norm_num)
theorem B1957251 : Blo 1955435 1957251 := bstep (se 1 (by rfl) ⟨1467938, by rfl⟩ : syracuseStep 1957251 = 2935877) B2935877
theorem B3302869 : Blo 1955435 3302869 := bbase (se 7 (by rfl) ⟨38705, by rfl⟩ : syracuseStep 3302869 = 77411) (by norm_num)
theorem B4403825 : Blo 1955435 4403825 := bstep (se 2 (by rfl) ⟨1651434, by rfl⟩ : syracuseStep 4403825 = 3302869) B3302869
theorem B2935883 : Blo 1955435 2935883 := bstep (se 1 (by rfl) ⟨2201912, by rfl⟩ : syracuseStep 2935883 = 4403825) B4403825
theorem B1957255 : Blo 1955435 1957255 := bstep (se 1 (by rfl) ⟨1467941, by rfl⟩ : syracuseStep 1957255 = 2935883) B2935883
theorem B2201917 : Blo 1955435 2201917 := bbase (se 3 (by rfl) ⟨412859, by rfl⟩ : syracuseStep 2201917 = 825719) (by norm_num)
theorem B2935889 : Blo 1955435 2935889 := bstep (se 2 (by rfl) ⟨1100958, by rfl⟩ : syracuseStep 2935889 = 2201917) B2201917
theorem B1957259 : Blo 1955435 1957259 := bstep (se 1 (by rfl) ⟨1467944, by rfl⟩ : syracuseStep 1957259 = 2935889) B2935889
theorem B6605765 : Blo 1955435 6605765 := bbase (se 4 (by rfl) ⟨619290, by rfl⟩ : syracuseStep 6605765 = 1238581) (by norm_num)
theorem B4403843 : Blo 1955435 4403843 := bstep (se 1 (by rfl) ⟨3302882, by rfl⟩ : syracuseStep 4403843 = 6605765) B6605765
theorem B2935895 : Blo 1955435 2935895 := bstep (se 1 (by rfl) ⟨2201921, by rfl⟩ : syracuseStep 2935895 = 4403843) B4403843
theorem B1957263 : Blo 1955435 1957263 := bstep (se 1 (by rfl) ⟨1467947, by rfl⟩ : syracuseStep 1957263 = 2935895) B2935895
theorem B2935901 : Blo 1955435 2935901 := bbase (se 3 (by rfl) ⟨550481, by rfl⟩ : syracuseStep 2935901 = 1100963) (by norm_num)
theorem B1957267 : Blo 1955435 1957267 := bstep (se 1 (by rfl) ⟨1467950, by rfl⟩ : syracuseStep 1957267 = 2935901) B2935901
theorem B4403861 : Blo 1955435 4403861 := bbase (se 6 (by rfl) ⟨103215, by rfl⟩ : syracuseStep 4403861 = 206431) (by norm_num)
theorem B2935907 : Blo 1955435 2935907 := bstep (se 1 (by rfl) ⟨2201930, by rfl⟩ : syracuseStep 2935907 = 4403861) B4403861
theorem B1957271 : Blo 1955435 1957271 := bstep (se 1 (by rfl) ⟨1467953, by rfl⟩ : syracuseStep 1957271 = 2935907) B2935907
theorem B3527077 : Blo 1955435 3527077 := bbase (se 4 (by rfl) ⟨330663, by rfl⟩ : syracuseStep 3527077 = 661327) (by norm_num)
theorem B4702769 : Blo 1955435 4702769 := bstep (se 2 (by rfl) ⟨1763538, by rfl⟩ : syracuseStep 4702769 = 3527077) B3527077
theorem B3135179 : Blo 1955435 3135179 := bstep (se 1 (by rfl) ⟨2351384, by rfl⟩ : syracuseStep 3135179 = 4702769) B4702769
theorem B2090119 : Blo 1955435 2090119 := bstep (se 1 (by rfl) ⟨1567589, by rfl⟩ : syracuseStep 2090119 = 3135179) B3135179
theorem B2786825 : Blo 1955435 2786825 := bstep (se 2 (by rfl) ⟨1045059, by rfl⟩ : syracuseStep 2786825 = 2090119) B2090119
theorem B7431533 : Blo 1955435 7431533 := bstep (se 3 (by rfl) ⟨1393412, by rfl⟩ : syracuseStep 7431533 = 2786825) B2786825
theorem B4954355 : Blo 1955435 4954355 := bstep (se 1 (by rfl) ⟨3715766, by rfl⟩ : syracuseStep 4954355 = 7431533) B7431533
theorem B3302903 : Blo 1955435 3302903 := bstep (se 1 (by rfl) ⟨2477177, by rfl⟩ : syracuseStep 3302903 = 4954355) B4954355
theorem B2201935 : Blo 1955435 2201935 := bstep (se 1 (by rfl) ⟨1651451, by rfl⟩ : syracuseStep 2201935 = 3302903) B3302903
theorem B2935913 : Blo 1955435 2935913 := bstep (se 2 (by rfl) ⟨1100967, by rfl⟩ : syracuseStep 2935913 = 2201935) B2201935
theorem B1957275 : Blo 1955435 1957275 := bstep (se 1 (by rfl) ⟨1467956, by rfl⟩ : syracuseStep 1957275 = 2935913) B2935913
theorem B7054165 : Blo 1955435 7054165 := bbase (se 9 (by rfl) ⟨20666, by rfl⟩ : syracuseStep 7054165 = 41333) (by norm_num)
theorem B9405553 : Blo 1955435 9405553 := bstep (se 2 (by rfl) ⟨3527082, by rfl⟩ : syracuseStep 9405553 = 7054165) B7054165
theorem B12540737 : Blo 1955435 12540737 := bstep (se 2 (by rfl) ⟨4702776, by rfl⟩ : syracuseStep 12540737 = 9405553) B9405553
theorem B8360491 : Blo 1955435 8360491 := bstep (se 1 (by rfl) ⟨6270368, by rfl⟩ : syracuseStep 8360491 = 12540737) B12540737
theorem B11147321 : Blo 1955435 11147321 := bstep (se 2 (by rfl) ⟨4180245, by rfl⟩ : syracuseStep 11147321 = 8360491) B8360491
theorem B7431547 : Blo 1955435 7431547 := bstep (se 1 (by rfl) ⟨5573660, by rfl⟩ : syracuseStep 7431547 = 11147321) B11147321
theorem B9908729 : Blo 1955435 9908729 := bstep (se 2 (by rfl) ⟨3715773, by rfl⟩ : syracuseStep 9908729 = 7431547) B7431547
theorem B6605819 : Blo 1955435 6605819 := bstep (se 1 (by rfl) ⟨4954364, by rfl⟩ : syracuseStep 6605819 = 9908729) B9908729
theorem B4403879 : Blo 1955435 4403879 := bstep (se 1 (by rfl) ⟨3302909, by rfl⟩ : syracuseStep 4403879 = 6605819) B6605819
theorem B2935919 : Blo 1955435 2935919 := bstep (se 1 (by rfl) ⟨2201939, by rfl⟩ : syracuseStep 2935919 = 4403879) B4403879
theorem B1957279 : Blo 1955435 1957279 := bstep (se 1 (by rfl) ⟨1467959, by rfl⟩ : syracuseStep 1957279 = 2935919) B2935919
theorem B2935925 : Blo 1955435 2935925 := bbase (se 5 (by rfl) ⟨137621, by rfl⟩ : syracuseStep 2935925 = 275243) (by norm_num)
theorem B1957283 : Blo 1955435 1957283 := bstep (se 1 (by rfl) ⟨1467962, by rfl⟩ : syracuseStep 1957283 = 2935925) B2935925
theorem B3715789 : Blo 1955435 3715789 := bbase (se 3 (by rfl) ⟨696710, by rfl⟩ : syracuseStep 3715789 = 1393421) (by norm_num)
theorem B4954385 : Blo 1955435 4954385 := bstep (se 2 (by rfl) ⟨1857894, by rfl⟩ : syracuseStep 4954385 = 3715789) B3715789
theorem B3302923 : Blo 1955435 3302923 := bstep (se 1 (by rfl) ⟨2477192, by rfl⟩ : syracuseStep 3302923 = 4954385) B4954385
theorem B4403897 : Blo 1955435 4403897 := bstep (se 2 (by rfl) ⟨1651461, by rfl⟩ : syracuseStep 4403897 = 3302923) B3302923
theorem B2935931 : Blo 1955435 2935931 := bstep (se 1 (by rfl) ⟨2201948, by rfl⟩ : syracuseStep 2935931 = 4403897) B4403897
theorem B1957287 : Blo 1955435 1957287 := bstep (se 1 (by rfl) ⟨1467965, by rfl⟩ : syracuseStep 1957287 = 2935931) B2935931
theorem B2201953 : Blo 1955435 2201953 := bbase (se 2 (by rfl) ⟨825732, by rfl⟩ : syracuseStep 2201953 = 1651465) (by norm_num)
theorem B2935937 : Blo 1955435 2935937 := bstep (se 2 (by rfl) ⟨1100976, by rfl⟩ : syracuseStep 2935937 = 2201953) B2201953
theorem B1957291 : Blo 1955435 1957291 := bstep (se 1 (by rfl) ⟨1467968, by rfl⟩ : syracuseStep 1957291 = 2935937) B2935937
theorem B4954405 : Blo 1955435 4954405 := bbase (se 4 (by rfl) ⟨464475, by rfl⟩ : syracuseStep 4954405 = 928951) (by norm_num)
theorem B6605873 : Blo 1955435 6605873 := bstep (se 2 (by rfl) ⟨2477202, by rfl⟩ : syracuseStep 6605873 = 4954405) B4954405
theorem B4403915 : Blo 1955435 4403915 := bstep (se 1 (by rfl) ⟨3302936, by rfl⟩ : syracuseStep 4403915 = 6605873) B6605873
theorem B2935943 : Blo 1955435 2935943 := bstep (se 1 (by rfl) ⟨2201957, by rfl⟩ : syracuseStep 2935943 = 4403915) B4403915
theorem B1957295 : Blo 1955435 1957295 := bstep (se 1 (by rfl) ⟨1467971, by rfl⟩ : syracuseStep 1957295 = 2935943) B2935943
theorem B2935949 : Blo 1955435 2935949 := bbase (se 3 (by rfl) ⟨550490, by rfl⟩ : syracuseStep 2935949 = 1100981) (by norm_num)
theorem B1957299 : Blo 1955435 1957299 := bstep (se 1 (by rfl) ⟨1467974, by rfl⟩ : syracuseStep 1957299 = 2935949) B2935949
theorem B4403933 : Blo 1955435 4403933 := bbase (se 3 (by rfl) ⟨825737, by rfl⟩ : syracuseStep 4403933 = 1651475) (by norm_num)
theorem B2935955 : Blo 1955435 2935955 := bstep (se 1 (by rfl) ⟨2201966, by rfl⟩ : syracuseStep 2935955 = 4403933) B4403933
theorem B1957303 : Blo 1955435 1957303 := bstep (se 1 (by rfl) ⟨1467977, by rfl⟩ : syracuseStep 1957303 = 2935955) B2935955
theorem B3302957 : Blo 1955435 3302957 := bbase (se 3 (by rfl) ⟨619304, by rfl⟩ : syracuseStep 3302957 = 1238609) (by norm_num)
theorem B2201971 : Blo 1955435 2201971 := bstep (se 1 (by rfl) ⟨1651478, by rfl⟩ : syracuseStep 2201971 = 3302957) B3302957
theorem B2935961 : Blo 1955435 2935961 := bstep (se 2 (by rfl) ⟨1100985, by rfl⟩ : syracuseStep 2935961 = 2201971) B2201971
theorem B1957307 : Blo 1955435 1957307 := bstep (se 1 (by rfl) ⟨1467980, by rfl⟩ : syracuseStep 1957307 = 2935961) B2935961
theorem B6356021 : Blo 1955435 6356021 := bbase (se 5 (by rfl) ⟨297938, by rfl⟩ : syracuseStep 6356021 = 595877) (by norm_num)
theorem B67797557 : Blo 1955435 67797557 := bstep (se 5 (by rfl) ⟨3178010, by rfl⟩ : syracuseStep 67797557 = 6356021) B6356021
theorem B45198371 : Blo 1955435 45198371 := bstep (se 1 (by rfl) ⟨33898778, by rfl⟩ : syracuseStep 45198371 = 67797557) B67797557
theorem B30132247 : Blo 1955435 30132247 := bstep (se 1 (by rfl) ⟨22599185, by rfl⟩ : syracuseStep 30132247 = 45198371) B45198371
theorem B40176329 : Blo 1955435 40176329 := bstep (se 2 (by rfl) ⟨15066123, by rfl⟩ : syracuseStep 40176329 = 30132247) B30132247
theorem B107136877 : Blo 1955435 107136877 := bstep (se 3 (by rfl) ⟨20088164, by rfl⟩ : syracuseStep 107136877 = 40176329) B40176329
theorem B142849169 : Blo 1955435 142849169 := bstep (se 2 (by rfl) ⟨53568438, by rfl⟩ : syracuseStep 142849169 = 107136877) B107136877
theorem B95232779 : Blo 1955435 95232779 := bstep (se 1 (by rfl) ⟨71424584, by rfl⟩ : syracuseStep 95232779 = 142849169) B142849169
theorem B63488519 : Blo 1955435 63488519 := bstep (se 1 (by rfl) ⟨47616389, by rfl⟩ : syracuseStep 63488519 = 95232779) B95232779
theorem B42325679 : Blo 1955435 42325679 := bstep (se 1 (by rfl) ⟨31744259, by rfl⟩ : syracuseStep 42325679 = 63488519) B63488519
theorem B28217119 : Blo 1955435 28217119 := bstep (se 1 (by rfl) ⟨21162839, by rfl⟩ : syracuseStep 28217119 = 42325679) B42325679
theorem B37622825 : Blo 1955435 37622825 := bstep (se 2 (by rfl) ⟨14108559, by rfl⟩ : syracuseStep 37622825 = 28217119) B28217119
theorem B25081883 : Blo 1955435 25081883 := bstep (se 1 (by rfl) ⟨18811412, by rfl⟩ : syracuseStep 25081883 = 37622825) B37622825
theorem B16721255 : Blo 1955435 16721255 := bstep (se 1 (by rfl) ⟨12540941, by rfl⟩ : syracuseStep 16721255 = 25081883) B25081883
theorem B11147503 : Blo 1955435 11147503 := bstep (se 1 (by rfl) ⟨8360627, by rfl⟩ : syracuseStep 11147503 = 16721255) B16721255
theorem B14863337 : Blo 1955435 14863337 := bstep (se 2 (by rfl) ⟨5573751, by rfl⟩ : syracuseStep 14863337 = 11147503) B11147503
theorem B9908891 : Blo 1955435 9908891 := bstep (se 1 (by rfl) ⟨7431668, by rfl⟩ : syracuseStep 9908891 = 14863337) B14863337
theorem B6605927 : Blo 1955435 6605927 := bstep (se 1 (by rfl) ⟨4954445, by rfl⟩ : syracuseStep 6605927 = 9908891) B9908891
theorem B4403951 : Blo 1955435 4403951 := bstep (se 1 (by rfl) ⟨3302963, by rfl⟩ : syracuseStep 4403951 = 6605927) B6605927
theorem B2935967 : Blo 1955435 2935967 := bstep (se 1 (by rfl) ⟨2201975, by rfl⟩ : syracuseStep 2935967 = 4403951) B4403951
theorem B1957311 : Blo 1955435 1957311 := bstep (se 1 (by rfl) ⟨1467983, by rfl⟩ : syracuseStep 1957311 = 2935967) B2935967
theorem B2935973 : Blo 1955435 2935973 := bbase (se 4 (by rfl) ⟨275247, by rfl⟩ : syracuseStep 2935973 = 550495) (by norm_num)
theorem B1957315 : Blo 1955435 1957315 := bstep (se 1 (by rfl) ⟨1467986, by rfl⟩ : syracuseStep 1957315 = 2935973) B2935973
theorem B2477233 : Blo 1955435 2477233 := bbase (se 2 (by rfl) ⟨928962, by rfl⟩ : syracuseStep 2477233 = 1857925) (by norm_num)
theorem B3302977 : Blo 1955435 3302977 := bstep (se 2 (by rfl) ⟨1238616, by rfl⟩ : syracuseStep 3302977 = 2477233) B2477233
theorem B4403969 : Blo 1955435 4403969 := bstep (se 2 (by rfl) ⟨1651488, by rfl⟩ : syracuseStep 4403969 = 3302977) B3302977
theorem B2935979 : Blo 1955435 2935979 := bstep (se 1 (by rfl) ⟨2201984, by rfl⟩ : syracuseStep 2935979 = 4403969) B4403969
theorem B1957319 : Blo 1955435 1957319 := bstep (se 1 (by rfl) ⟨1467989, by rfl⟩ : syracuseStep 1957319 = 2935979) B2935979
theorem B2201989 : Blo 1955435 2201989 := bbase (se 4 (by rfl) ⟨206436, by rfl⟩ : syracuseStep 2201989 = 412873) (by norm_num)
theorem B2935985 : Blo 1955435 2935985 := bstep (se 2 (by rfl) ⟨1100994, by rfl⟩ : syracuseStep 2935985 = 2201989) B2201989
theorem B1957323 : Blo 1955435 1957323 := bstep (se 1 (by rfl) ⟨1467992, by rfl⟩ : syracuseStep 1957323 = 2935985) B2935985
theorem B4180349 : Blo 1955435 4180349 := bbase (se 3 (by rfl) ⟨783815, by rfl⟩ : syracuseStep 4180349 = 1567631) (by norm_num)
theorem B2786899 : Blo 1955435 2786899 := bstep (se 1 (by rfl) ⟨2090174, by rfl⟩ : syracuseStep 2786899 = 4180349) B4180349
theorem B3715865 : Blo 1955435 3715865 := bstep (se 2 (by rfl) ⟨1393449, by rfl⟩ : syracuseStep 3715865 = 2786899) B2786899
theorem B2477243 : Blo 1955435 2477243 := bstep (se 1 (by rfl) ⟨1857932, by rfl⟩ : syracuseStep 2477243 = 3715865) B3715865
theorem B6605981 : Blo 1955435 6605981 := bstep (se 3 (by rfl) ⟨1238621, by rfl⟩ : syracuseStep 6605981 = 2477243) B2477243
theorem B4403987 : Blo 1955435 4403987 := bstep (se 1 (by rfl) ⟨3302990, by rfl⟩ : syracuseStep 4403987 = 6605981) B6605981
theorem B2935991 : Blo 1955435 2935991 := bstep (se 1 (by rfl) ⟨2201993, by rfl⟩ : syracuseStep 2935991 = 4403987) B4403987
theorem B1957327 : Blo 1955435 1957327 := bstep (se 1 (by rfl) ⟨1467995, by rfl⟩ : syracuseStep 1957327 = 2935991) B2935991
theorem B2935997 : Blo 1955435 2935997 := bbase (se 3 (by rfl) ⟨550499, by rfl⟩ : syracuseStep 2935997 = 1100999) (by norm_num)
theorem B1957331 : Blo 1955435 1957331 := bstep (se 1 (by rfl) ⟨1467998, by rfl⟩ : syracuseStep 1957331 = 2935997) B2935997
theorem B4404005 : Blo 1955435 4404005 := bbase (se 4 (by rfl) ⟨412875, by rfl⟩ : syracuseStep 4404005 = 825751) (by norm_num)
theorem B2936003 : Blo 1955435 2936003 := bstep (se 1 (by rfl) ⟨2202002, by rfl⟩ : syracuseStep 2936003 = 4404005) B4404005
theorem B1957335 : Blo 1955435 1957335 := bstep (se 1 (by rfl) ⟨1468001, by rfl⟩ : syracuseStep 1957335 = 2936003) B2936003
theorem B4954517 : Blo 1955435 4954517 := bbase (se 6 (by rfl) ⟨116121, by rfl⟩ : syracuseStep 4954517 = 232243) (by norm_num)
theorem B3303011 : Blo 1955435 3303011 := bstep (se 1 (by rfl) ⟨2477258, by rfl⟩ : syracuseStep 3303011 = 4954517) B4954517
theorem B2202007 : Blo 1955435 2202007 := bstep (se 1 (by rfl) ⟨1651505, by rfl⟩ : syracuseStep 2202007 = 3303011) B3303011
theorem B2936009 : Blo 1955435 2936009 := bstep (se 2 (by rfl) ⟨1101003, by rfl⟩ : syracuseStep 2936009 = 2202007) B2202007
theorem B1957339 : Blo 1955435 1957339 := bstep (se 1 (by rfl) ⟨1468004, by rfl⟩ : syracuseStep 1957339 = 2936009) B2936009
theorem B5952149 : Blo 1955435 5952149 := bbase (se 6 (by rfl) ⟨139503, by rfl⟩ : syracuseStep 5952149 = 279007) (by norm_num)
theorem B3968099 : Blo 1955435 3968099 := bstep (se 1 (by rfl) ⟨2976074, by rfl⟩ : syracuseStep 3968099 = 5952149) B5952149
theorem B2645399 : Blo 1955435 2645399 := bstep (se 1 (by rfl) ⟨1984049, by rfl⟩ : syracuseStep 2645399 = 3968099) B3968099
theorem B7054397 : Blo 1955435 7054397 := bstep (se 3 (by rfl) ⟨1322699, by rfl⟩ : syracuseStep 7054397 = 2645399) B2645399
theorem B4702931 : Blo 1955435 4702931 := bstep (se 1 (by rfl) ⟨3527198, by rfl⟩ : syracuseStep 4702931 = 7054397) B7054397
theorem B3135287 : Blo 1955435 3135287 := bstep (se 1 (by rfl) ⟨2351465, by rfl⟩ : syracuseStep 3135287 = 4702931) B4702931
theorem B8360765 : Blo 1955435 8360765 := bstep (se 3 (by rfl) ⟨1567643, by rfl⟩ : syracuseStep 8360765 = 3135287) B3135287
theorem B5573843 : Blo 1955435 5573843 := bstep (se 1 (by rfl) ⟨4180382, by rfl⟩ : syracuseStep 5573843 = 8360765) B8360765
theorem B3715895 : Blo 1955435 3715895 := bstep (se 1 (by rfl) ⟨2786921, by rfl⟩ : syracuseStep 3715895 = 5573843) B5573843
theorem B9909053 : Blo 1955435 9909053 := bstep (se 3 (by rfl) ⟨1857947, by rfl⟩ : syracuseStep 9909053 = 3715895) B3715895
theorem B6606035 : Blo 1955435 6606035 := bstep (se 1 (by rfl) ⟨4954526, by rfl⟩ : syracuseStep 6606035 = 9909053) B9909053
theorem B4404023 : Blo 1955435 4404023 := bstep (se 1 (by rfl) ⟨3303017, by rfl⟩ : syracuseStep 4404023 = 6606035) B6606035
theorem B2936015 : Blo 1955435 2936015 := bstep (se 1 (by rfl) ⟨2202011, by rfl⟩ : syracuseStep 2936015 = 4404023) B4404023
theorem B1957343 : Blo 1955435 1957343 := bstep (se 1 (by rfl) ⟨1468007, by rfl⟩ : syracuseStep 1957343 = 2936015) B2936015
theorem B2936021 : Blo 1955435 2936021 := bbase (se 7 (by rfl) ⟨34406, by rfl⟩ : syracuseStep 2936021 = 68813) (by norm_num)
theorem B1957347 : Blo 1955435 1957347 := bstep (se 1 (by rfl) ⟨1468010, by rfl⟩ : syracuseStep 1957347 = 2936021) B2936021
theorem B2786933 : Blo 1955435 2786933 := bbase (se 5 (by rfl) ⟨130637, by rfl⟩ : syracuseStep 2786933 = 261275) (by norm_num)
theorem B7431821 : Blo 1955435 7431821 := bstep (se 3 (by rfl) ⟨1393466, by rfl⟩ : syracuseStep 7431821 = 2786933) B2786933
theorem B4954547 : Blo 1955435 4954547 := bstep (se 1 (by rfl) ⟨3715910, by rfl⟩ : syracuseStep 4954547 = 7431821) B7431821
theorem B3303031 : Blo 1955435 3303031 := bstep (se 1 (by rfl) ⟨2477273, by rfl⟩ : syracuseStep 3303031 = 4954547) B4954547
theorem B4404041 : Blo 1955435 4404041 := bstep (se 2 (by rfl) ⟨1651515, by rfl⟩ : syracuseStep 4404041 = 3303031) B3303031
theorem B2936027 : Blo 1955435 2936027 := bstep (se 1 (by rfl) ⟨2202020, by rfl⟩ : syracuseStep 2936027 = 4404041) B4404041
theorem B1957351 : Blo 1955435 1957351 := bstep (se 1 (by rfl) ⟨1468013, by rfl⟩ : syracuseStep 1957351 = 2936027) B2936027
theorem B2202025 : Blo 1955435 2202025 := bbase (se 2 (by rfl) ⟨825759, by rfl⟩ : syracuseStep 2202025 = 1651519) (by norm_num)
theorem B2936033 : Blo 1955435 2936033 := bstep (se 2 (by rfl) ⟨1101012, by rfl⟩ : syracuseStep 2936033 = 2202025) B2202025
theorem B1957355 : Blo 1955435 1957355 := bstep (se 1 (by rfl) ⟨1468016, by rfl⟩ : syracuseStep 1957355 = 2936033) B2936033
theorem B5952197 : Blo 1955435 5952197 := bbase (se 4 (by rfl) ⟨558018, by rfl⟩ : syracuseStep 5952197 = 1116037) (by norm_num)
theorem B3968131 : Blo 1955435 3968131 := bstep (se 1 (by rfl) ⟨2976098, by rfl⟩ : syracuseStep 3968131 = 5952197) B5952197
theorem B5290841 : Blo 1955435 5290841 := bstep (se 2 (by rfl) ⟨1984065, by rfl⟩ : syracuseStep 5290841 = 3968131) B3968131
theorem B3527227 : Blo 1955435 3527227 := bstep (se 1 (by rfl) ⟨2645420, by rfl⟩ : syracuseStep 3527227 = 5290841) B5290841
theorem B4702969 : Blo 1955435 4702969 := bstep (se 2 (by rfl) ⟨1763613, by rfl⟩ : syracuseStep 4702969 = 3527227) B3527227
theorem B6270625 : Blo 1955435 6270625 := bstep (se 2 (by rfl) ⟨2351484, by rfl⟩ : syracuseStep 6270625 = 4702969) B4702969
theorem B8360833 : Blo 1955435 8360833 := bstep (se 2 (by rfl) ⟨3135312, by rfl⟩ : syracuseStep 8360833 = 6270625) B6270625
theorem B11147777 : Blo 1955435 11147777 := bstep (se 2 (by rfl) ⟨4180416, by rfl⟩ : syracuseStep 11147777 = 8360833) B8360833
theorem B7431851 : Blo 1955435 7431851 := bstep (se 1 (by rfl) ⟨5573888, by rfl⟩ : syracuseStep 7431851 = 11147777) B11147777
theorem B4954567 : Blo 1955435 4954567 := bstep (se 1 (by rfl) ⟨3715925, by rfl⟩ : syracuseStep 4954567 = 7431851) B7431851
theorem B6606089 : Blo 1955435 6606089 := bstep (se 2 (by rfl) ⟨2477283, by rfl⟩ : syracuseStep 6606089 = 4954567) B4954567
theorem B4404059 : Blo 1955435 4404059 := bstep (se 1 (by rfl) ⟨3303044, by rfl⟩ : syracuseStep 4404059 = 6606089) B6606089
theorem B2936039 : Blo 1955435 2936039 := bstep (se 1 (by rfl) ⟨2202029, by rfl⟩ : syracuseStep 2936039 = 4404059) B4404059
theorem B1957359 : Blo 1955435 1957359 := bstep (se 1 (by rfl) ⟨1468019, by rfl⟩ : syracuseStep 1957359 = 2936039) B2936039
theorem B2936045 : Blo 1955435 2936045 := bbase (se 3 (by rfl) ⟨550508, by rfl⟩ : syracuseStep 2936045 = 1101017) (by norm_num)
theorem B1957363 : Blo 1955435 1957363 := bstep (se 1 (by rfl) ⟨1468022, by rfl⟩ : syracuseStep 1957363 = 2936045) B2936045
theorem B4404077 : Blo 1955435 4404077 := bbase (se 3 (by rfl) ⟨825764, by rfl⟩ : syracuseStep 4404077 = 1651529) (by norm_num)
theorem B2936051 : Blo 1955435 2936051 := bstep (se 1 (by rfl) ⟨2202038, by rfl⟩ : syracuseStep 2936051 = 4404077) B4404077
theorem B1957367 : Blo 1955435 1957367 := bstep (se 1 (by rfl) ⟨1468025, by rfl⟩ : syracuseStep 1957367 = 2936051) B2936051
theorem B3715949 : Blo 1955435 3715949 := bbase (se 3 (by rfl) ⟨696740, by rfl⟩ : syracuseStep 3715949 = 1393481) (by norm_num)
theorem B2477299 : Blo 1955435 2477299 := bstep (se 1 (by rfl) ⟨1857974, by rfl⟩ : syracuseStep 2477299 = 3715949) B3715949
theorem B3303065 : Blo 1955435 3303065 := bstep (se 2 (by rfl) ⟨1238649, by rfl⟩ : syracuseStep 3303065 = 2477299) B2477299
theorem B2202043 : Blo 1955435 2202043 := bstep (se 1 (by rfl) ⟨1651532, by rfl⟩ : syracuseStep 2202043 = 3303065) B3303065
theorem B2936057 : Blo 1955435 2936057 := bstep (se 2 (by rfl) ⟨1101021, by rfl⟩ : syracuseStep 2936057 = 2202043) B2202043
theorem B1957371 : Blo 1955435 1957371 := bstep (se 1 (by rfl) ⟨1468028, by rfl⟩ : syracuseStep 1957371 = 2936057) B2936057
theorem B2449073 : Blo 1955435 2449073 := bbase (se 2 (by rfl) ⟨918402, by rfl⟩ : syracuseStep 2449073 = 1836805) (by norm_num)
theorem B6530861 : Blo 1955435 6530861 := bstep (se 3 (by rfl) ⟨1224536, by rfl⟩ : syracuseStep 6530861 = 2449073) B2449073
theorem B4353907 : Blo 1955435 4353907 := bstep (se 1 (by rfl) ⟨3265430, by rfl⟩ : syracuseStep 4353907 = 6530861) B6530861
theorem B5805209 : Blo 1955435 5805209 := bstep (se 2 (by rfl) ⟨2176953, by rfl⟩ : syracuseStep 5805209 = 4353907) B4353907
theorem B15480557 : Blo 1955435 15480557 := bstep (se 3 (by rfl) ⟨2902604, by rfl⟩ : syracuseStep 15480557 = 5805209) B5805209
theorem B10320371 : Blo 1955435 10320371 := bstep (se 1 (by rfl) ⟨7740278, by rfl⟩ : syracuseStep 10320371 = 15480557) B15480557
theorem B6880247 : Blo 1955435 6880247 := bstep (se 1 (by rfl) ⟨5160185, by rfl⟩ : syracuseStep 6880247 = 10320371) B10320371
theorem B4586831 : Blo 1955435 4586831 := bstep (se 1 (by rfl) ⟨3440123, by rfl⟩ : syracuseStep 4586831 = 6880247) B6880247
theorem B3057887 : Blo 1955435 3057887 := bstep (se 1 (by rfl) ⟨2293415, by rfl⟩ : syracuseStep 3057887 = 4586831) B4586831
theorem B2038591 : Blo 1955435 2038591 := bstep (se 1 (by rfl) ⟨1528943, by rfl⟩ : syracuseStep 2038591 = 3057887) B3057887
theorem B10872485 : Blo 1955435 10872485 := bstep (se 4 (by rfl) ⟨1019295, by rfl⟩ : syracuseStep 10872485 = 2038591) B2038591
theorem B7248323 : Blo 1955435 7248323 := bstep (se 1 (by rfl) ⟨5436242, by rfl⟩ : syracuseStep 7248323 = 10872485) B10872485
theorem B19328861 : Blo 1955435 19328861 := bstep (se 3 (by rfl) ⟨3624161, by rfl⟩ : syracuseStep 19328861 = 7248323) B7248323
theorem B12885907 : Blo 1955435 12885907 := bstep (se 1 (by rfl) ⟨9664430, by rfl⟩ : syracuseStep 12885907 = 19328861) B19328861
theorem B17181209 : Blo 1955435 17181209 := bstep (se 2 (by rfl) ⟨6442953, by rfl⟩ : syracuseStep 17181209 = 12885907) B12885907
theorem B11454139 : Blo 1955435 11454139 := bstep (se 1 (by rfl) ⟨8590604, by rfl⟩ : syracuseStep 11454139 = 17181209) B17181209
theorem B15272185 : Blo 1955435 15272185 := bstep (se 2 (by rfl) ⟨5727069, by rfl⟩ : syracuseStep 15272185 = 11454139) B11454139
theorem B20362913 : Blo 1955435 20362913 := bstep (se 2 (by rfl) ⟨7636092, by rfl⟩ : syracuseStep 20362913 = 15272185) B15272185
theorem B13575275 : Blo 1955435 13575275 := bstep (se 1 (by rfl) ⟨10181456, by rfl⟩ : syracuseStep 13575275 = 20362913) B20362913
theorem B9050183 : Blo 1955435 9050183 := bstep (se 1 (by rfl) ⟨6787637, by rfl⟩ : syracuseStep 9050183 = 13575275) B13575275
theorem B6033455 : Blo 1955435 6033455 := bstep (se 1 (by rfl) ⟨4525091, by rfl⟩ : syracuseStep 6033455 = 9050183) B9050183
theorem B4022303 : Blo 1955435 4022303 := bstep (se 1 (by rfl) ⟨3016727, by rfl⟩ : syracuseStep 4022303 = 6033455) B6033455
theorem B42904565 : Blo 1955435 42904565 := bstep (se 5 (by rfl) ⟨2011151, by rfl⟩ : syracuseStep 42904565 = 4022303) B4022303
theorem B28603043 : Blo 1955435 28603043 := bstep (se 1 (by rfl) ⟨21452282, by rfl⟩ : syracuseStep 28603043 = 42904565) B42904565
theorem B19068695 : Blo 1955435 19068695 := bstep (se 1 (by rfl) ⟨14301521, by rfl⟩ : syracuseStep 19068695 = 28603043) B28603043
theorem B12712463 : Blo 1955435 12712463 := bstep (se 1 (by rfl) ⟨9534347, by rfl⟩ : syracuseStep 12712463 = 19068695) B19068695
theorem B8474975 : Blo 1955435 8474975 := bstep (se 1 (by rfl) ⟨6356231, by rfl⟩ : syracuseStep 8474975 = 12712463) B12712463
theorem B5649983 : Blo 1955435 5649983 := bstep (se 1 (by rfl) ⟨4237487, by rfl⟩ : syracuseStep 5649983 = 8474975) B8474975
theorem B3766655 : Blo 1955435 3766655 := bstep (se 1 (by rfl) ⟨2824991, by rfl⟩ : syracuseStep 3766655 = 5649983) B5649983
theorem B2511103 : Blo 1955435 2511103 := bstep (se 1 (by rfl) ⟨1883327, by rfl⟩ : syracuseStep 2511103 = 3766655) B3766655
theorem B3348137 : Blo 1955435 3348137 := bstep (se 2 (by rfl) ⟨1255551, by rfl⟩ : syracuseStep 3348137 = 2511103) B2511103
theorem B8928365 : Blo 1955435 8928365 := bstep (se 3 (by rfl) ⟨1674068, by rfl⟩ : syracuseStep 8928365 = 3348137) B3348137
theorem B23808973 : Blo 1955435 23808973 := bstep (se 3 (by rfl) ⟨4464182, by rfl⟩ : syracuseStep 23808973 = 8928365) B8928365
theorem B31745297 : Blo 1955435 31745297 := bstep (se 2 (by rfl) ⟨11904486, by rfl⟩ : syracuseStep 31745297 = 23808973) B23808973
theorem B21163531 : Blo 1955435 21163531 := bstep (se 1 (by rfl) ⟨15872648, by rfl⟩ : syracuseStep 21163531 = 31745297) B31745297
theorem B28218041 : Blo 1955435 28218041 := bstep (se 2 (by rfl) ⟨10581765, by rfl⟩ : syracuseStep 28218041 = 21163531) B21163531
theorem B18812027 : Blo 1955435 18812027 := bstep (se 1 (by rfl) ⟨14109020, by rfl⟩ : syracuseStep 18812027 = 28218041) B28218041
theorem B50165405 : Blo 1955435 50165405 := bstep (se 3 (by rfl) ⟨9406013, by rfl⟩ : syracuseStep 50165405 = 18812027) B18812027
theorem B33443603 : Blo 1955435 33443603 := bstep (se 1 (by rfl) ⟨25082702, by rfl⟩ : syracuseStep 33443603 = 50165405) B50165405
theorem B22295735 : Blo 1955435 22295735 := bstep (se 1 (by rfl) ⟨16721801, by rfl⟩ : syracuseStep 22295735 = 33443603) B33443603
theorem B14863823 : Blo 1955435 14863823 := bstep (se 1 (by rfl) ⟨11147867, by rfl⟩ : syracuseStep 14863823 = 22295735) B22295735
theorem B9909215 : Blo 1955435 9909215 := bstep (se 1 (by rfl) ⟨7431911, by rfl⟩ : syracuseStep 9909215 = 14863823) B14863823
theorem B6606143 : Blo 1955435 6606143 := bstep (se 1 (by rfl) ⟨4954607, by rfl⟩ : syracuseStep 6606143 = 9909215) B9909215
theorem B4404095 : Blo 1955435 4404095 := bstep (se 1 (by rfl) ⟨3303071, by rfl⟩ : syracuseStep 4404095 = 6606143) B6606143
theorem B2936063 : Blo 1955435 2936063 := bstep (se 1 (by rfl) ⟨2202047, by rfl⟩ : syracuseStep 2936063 = 4404095) B4404095
theorem B1957375 : Blo 1955435 1957375 := bstep (se 1 (by rfl) ⟨1468031, by rfl⟩ : syracuseStep 1957375 = 2936063) B2936063
theorem B2936069 : Blo 1955435 2936069 := bbase (se 4 (by rfl) ⟨275256, by rfl⟩ : syracuseStep 2936069 = 550513) (by norm_num)
theorem B1957379 : Blo 1955435 1957379 := bstep (se 1 (by rfl) ⟨1468034, by rfl⟩ : syracuseStep 1957379 = 2936069) B2936069
theorem B3303085 : Blo 1955435 3303085 := bbase (se 3 (by rfl) ⟨619328, by rfl⟩ : syracuseStep 3303085 = 1238657) (by norm_num)
theorem B4404113 : Blo 1955435 4404113 := bstep (se 2 (by rfl) ⟨1651542, by rfl⟩ : syracuseStep 4404113 = 3303085) B3303085
theorem B2936075 : Blo 1955435 2936075 := bstep (se 1 (by rfl) ⟨2202056, by rfl⟩ : syracuseStep 2936075 = 4404113) B4404113
theorem B1957383 : Blo 1955435 1957383 := bstep (se 1 (by rfl) ⟨1468037, by rfl⟩ : syracuseStep 1957383 = 2936075) B2936075
theorem B2202061 : Blo 1955435 2202061 := bbase (se 3 (by rfl) ⟨412886, by rfl⟩ : syracuseStep 2202061 = 825773) (by norm_num)
theorem B2936081 : Blo 1955435 2936081 := bstep (se 2 (by rfl) ⟨1101030, by rfl⟩ : syracuseStep 2936081 = 2202061) B2202061
theorem B1957387 : Blo 1955435 1957387 := bstep (se 1 (by rfl) ⟨1468040, by rfl⟩ : syracuseStep 1957387 = 2936081) B2936081
theorem B6606197 : Blo 1955435 6606197 := bbase (se 5 (by rfl) ⟨309665, by rfl⟩ : syracuseStep 6606197 = 619331) (by norm_num)
theorem B4404131 : Blo 1955435 4404131 := bstep (se 1 (by rfl) ⟨3303098, by rfl⟩ : syracuseStep 4404131 = 6606197) B6606197
theorem B2936087 : Blo 1955435 2936087 := bstep (se 1 (by rfl) ⟨2202065, by rfl⟩ : syracuseStep 2936087 = 4404131) B4404131
theorem B1957391 : Blo 1955435 1957391 := bstep (se 1 (by rfl) ⟨1468043, by rfl⟩ : syracuseStep 1957391 = 2936087) B2936087
theorem B2936093 : Blo 1955435 2936093 := bbase (se 3 (by rfl) ⟨550517, by rfl⟩ : syracuseStep 2936093 = 1101035) (by norm_num)
theorem B1957395 : Blo 1955435 1957395 := bstep (se 1 (by rfl) ⟨1468046, by rfl⟩ : syracuseStep 1957395 = 2936093) B2936093
theorem B4404149 : Blo 1955435 4404149 := bbase (se 5 (by rfl) ⟨206444, by rfl⟩ : syracuseStep 4404149 = 412889) (by norm_num)
theorem B2936099 : Blo 1955435 2936099 := bstep (se 1 (by rfl) ⟨2202074, by rfl⟩ : syracuseStep 2936099 = 4404149) B4404149
theorem B1957399 : Blo 1955435 1957399 := bstep (se 1 (by rfl) ⟨1468049, by rfl⟩ : syracuseStep 1957399 = 2936099) B2936099
theorem B11904661 : Blo 1955435 11904661 := bbase (se 6 (by rfl) ⟨279015, by rfl⟩ : syracuseStep 11904661 = 558031) (by norm_num)
theorem B15872881 : Blo 1955435 15872881 := bstep (se 2 (by rfl) ⟨5952330, by rfl⟩ : syracuseStep 15872881 = 11904661) B11904661
theorem B21163841 : Blo 1955435 21163841 := bstep (se 2 (by rfl) ⟨7936440, by rfl⟩ : syracuseStep 21163841 = 15872881) B15872881
theorem B14109227 : Blo 1955435 14109227 := bstep (se 1 (by rfl) ⟨10581920, by rfl⟩ : syracuseStep 14109227 = 21163841) B21163841
theorem B9406151 : Blo 1955435 9406151 := bstep (se 1 (by rfl) ⟨7054613, by rfl⟩ : syracuseStep 9406151 = 14109227) B14109227
theorem B6270767 : Blo 1955435 6270767 := bstep (se 1 (by rfl) ⟨4703075, by rfl⟩ : syracuseStep 6270767 = 9406151) B9406151
theorem B4180511 : Blo 1955435 4180511 := bstep (se 1 (by rfl) ⟨3135383, by rfl⟩ : syracuseStep 4180511 = 6270767) B6270767
theorem B11148029 : Blo 1955435 11148029 := bstep (se 3 (by rfl) ⟨2090255, by rfl⟩ : syracuseStep 11148029 = 4180511) B4180511
theorem B7432019 : Blo 1955435 7432019 := bstep (se 1 (by rfl) ⟨5574014, by rfl⟩ : syracuseStep 7432019 = 11148029) B11148029
theorem B4954679 : Blo 1955435 4954679 := bstep (se 1 (by rfl) ⟨3716009, by rfl⟩ : syracuseStep 4954679 = 7432019) B7432019
theorem B3303119 : Blo 1955435 3303119 := bstep (se 1 (by rfl) ⟨2477339, by rfl⟩ : syracuseStep 3303119 = 4954679) B4954679
theorem B2202079 : Blo 1955435 2202079 := bstep (se 1 (by rfl) ⟨1651559, by rfl⟩ : syracuseStep 2202079 = 3303119) B3303119
theorem B2936105 : Blo 1955435 2936105 := bstep (se 2 (by rfl) ⟨1101039, by rfl⟩ : syracuseStep 2936105 = 2202079) B2202079
theorem B1957403 : Blo 1955435 1957403 := bstep (se 1 (by rfl) ⟨1468052, by rfl⟩ : syracuseStep 1957403 = 2936105) B2936105
theorem B10581941 : Blo 1955435 10581941 := bbase (se 5 (by rfl) ⟨496028, by rfl⟩ : syracuseStep 10581941 = 992057) (by norm_num)
theorem B7054627 : Blo 1955435 7054627 := bstep (se 1 (by rfl) ⟨5290970, by rfl⟩ : syracuseStep 7054627 = 10581941) B10581941
theorem B9406169 : Blo 1955435 9406169 := bstep (se 2 (by rfl) ⟨3527313, by rfl⟩ : syracuseStep 9406169 = 7054627) B7054627
theorem B6270779 : Blo 1955435 6270779 := bstep (se 1 (by rfl) ⟨4703084, by rfl⟩ : syracuseStep 6270779 = 9406169) B9406169
theorem B4180519 : Blo 1955435 4180519 := bstep (se 1 (by rfl) ⟨3135389, by rfl⟩ : syracuseStep 4180519 = 6270779) B6270779
theorem B5574025 : Blo 1955435 5574025 := bstep (se 2 (by rfl) ⟨2090259, by rfl⟩ : syracuseStep 5574025 = 4180519) B4180519
theorem B7432033 : Blo 1955435 7432033 := bstep (se 2 (by rfl) ⟨2787012, by rfl⟩ : syracuseStep 7432033 = 5574025) B5574025
theorem B9909377 : Blo 1955435 9909377 := bstep (se 2 (by rfl) ⟨3716016, by rfl⟩ : syracuseStep 9909377 = 7432033) B7432033
theorem B6606251 : Blo 1955435 6606251 := bstep (se 1 (by rfl) ⟨4954688, by rfl⟩ : syracuseStep 6606251 = 9909377) B9909377
theorem B4404167 : Blo 1955435 4404167 := bstep (se 1 (by rfl) ⟨3303125, by rfl⟩ : syracuseStep 4404167 = 6606251) B6606251
theorem B2936111 : Blo 1955435 2936111 := bstep (se 1 (by rfl) ⟨2202083, by rfl⟩ : syracuseStep 2936111 = 4404167) B4404167
theorem B1957407 : Blo 1955435 1957407 := bstep (se 1 (by rfl) ⟨1468055, by rfl⟩ : syracuseStep 1957407 = 2936111) B2936111
theorem B2936117 : Blo 1955435 2936117 := bbase (se 5 (by rfl) ⟨137630, by rfl⟩ : syracuseStep 2936117 = 275261) (by norm_num)
theorem B1957411 : Blo 1955435 1957411 := bstep (se 1 (by rfl) ⟨1468058, by rfl⟩ : syracuseStep 1957411 = 2936117) B2936117
theorem B4954709 : Blo 1955435 4954709 := bbase (se 8 (by rfl) ⟨29031, by rfl⟩ : syracuseStep 4954709 = 58063) (by norm_num)
theorem B3303139 : Blo 1955435 3303139 := bstep (se 1 (by rfl) ⟨2477354, by rfl⟩ : syracuseStep 3303139 = 4954709) B4954709
theorem B4404185 : Blo 1955435 4404185 := bstep (se 2 (by rfl) ⟨1651569, by rfl⟩ : syracuseStep 4404185 = 3303139) B3303139
theorem B2936123 : Blo 1955435 2936123 := bstep (se 1 (by rfl) ⟨2202092, by rfl⟩ : syracuseStep 2936123 = 4404185) B4404185
theorem B1957415 : Blo 1955435 1957415 := bstep (se 1 (by rfl) ⟨1468061, by rfl⟩ : syracuseStep 1957415 = 2936123) B2936123
theorem B2202097 : Blo 1955435 2202097 := bbase (se 2 (by rfl) ⟨825786, by rfl⟩ : syracuseStep 2202097 = 1651573) (by norm_num)
theorem B2936129 : Blo 1955435 2936129 := bstep (se 2 (by rfl) ⟨1101048, by rfl⟩ : syracuseStep 2936129 = 2202097) B2202097
theorem B1957419 : Blo 1955435 1957419 := bstep (se 1 (by rfl) ⟨1468064, by rfl⟩ : syracuseStep 1957419 = 2936129) B2936129
theorem B3968261 : Blo 1955435 3968261 := bbase (se 4 (by rfl) ⟨372024, by rfl⟩ : syracuseStep 3968261 = 744049) (by norm_num)
theorem B2645507 : Blo 1955435 2645507 := bstep (se 1 (by rfl) ⟨1984130, by rfl⟩ : syracuseStep 2645507 = 3968261) B3968261
theorem B7054685 : Blo 1955435 7054685 := bstep (se 3 (by rfl) ⟨1322753, by rfl⟩ : syracuseStep 7054685 = 2645507) B2645507
theorem B4703123 : Blo 1955435 4703123 := bstep (se 1 (by rfl) ⟨3527342, by rfl⟩ : syracuseStep 4703123 = 7054685) B7054685
theorem B12541661 : Blo 1955435 12541661 := bstep (se 3 (by rfl) ⟨2351561, by rfl⟩ : syracuseStep 12541661 = 4703123) B4703123
theorem B8361107 : Blo 1955435 8361107 := bstep (se 1 (by rfl) ⟨6270830, by rfl⟩ : syracuseStep 8361107 = 12541661) B12541661
theorem B5574071 : Blo 1955435 5574071 := bstep (se 1 (by rfl) ⟨4180553, by rfl⟩ : syracuseStep 5574071 = 8361107) B8361107
theorem B3716047 : Blo 1955435 3716047 := bstep (se 1 (by rfl) ⟨2787035, by rfl⟩ : syracuseStep 3716047 = 5574071) B5574071
theorem B4954729 : Blo 1955435 4954729 := bstep (se 2 (by rfl) ⟨1858023, by rfl⟩ : syracuseStep 4954729 = 3716047) B3716047
theorem B6606305 : Blo 1955435 6606305 := bstep (se 2 (by rfl) ⟨2477364, by rfl⟩ : syracuseStep 6606305 = 4954729) B4954729
theorem B4404203 : Blo 1955435 4404203 := bstep (se 1 (by rfl) ⟨3303152, by rfl⟩ : syracuseStep 4404203 = 6606305) B6606305
theorem B2936135 : Blo 1955435 2936135 := bstep (se 1 (by rfl) ⟨2202101, by rfl⟩ : syracuseStep 2936135 = 4404203) B4404203
theorem B1957423 : Blo 1955435 1957423 := bstep (se 1 (by rfl) ⟨1468067, by rfl⟩ : syracuseStep 1957423 = 2936135) B2936135
theorem B2936141 : Blo 1955435 2936141 := bbase (se 3 (by rfl) ⟨550526, by rfl⟩ : syracuseStep 2936141 = 1101053) (by norm_num)
theorem B1957427 : Blo 1955435 1957427 := bstep (se 1 (by rfl) ⟨1468070, by rfl⟩ : syracuseStep 1957427 = 2936141) B2936141
theorem B4404221 : Blo 1955435 4404221 := bbase (se 3 (by rfl) ⟨825791, by rfl⟩ : syracuseStep 4404221 = 1651583) (by norm_num)
theorem B2936147 : Blo 1955435 2936147 := bstep (se 1 (by rfl) ⟨2202110, by rfl⟩ : syracuseStep 2936147 = 4404221) B4404221
theorem B1957431 : Blo 1955435 1957431 := bstep (se 1 (by rfl) ⟨1468073, by rfl⟩ : syracuseStep 1957431 = 2936147) B2936147
theorem B3303173 : Blo 1955435 3303173 := bbase (se 4 (by rfl) ⟨309672, by rfl⟩ : syracuseStep 3303173 = 619345) (by norm_num)
theorem B2202115 : Blo 1955435 2202115 := bstep (se 1 (by rfl) ⟨1651586, by rfl⟩ : syracuseStep 2202115 = 3303173) B3303173
theorem B2936153 : Blo 1955435 2936153 := bstep (se 2 (by rfl) ⟨1101057, by rfl⟩ : syracuseStep 2936153 = 2202115) B2202115
theorem B1957435 : Blo 1955435 1957435 := bstep (se 1 (by rfl) ⟨1468076, by rfl⟩ : syracuseStep 1957435 = 2936153) B2936153
theorem C0 (j : ℕ) (h1 : 488858 ≤ j) (h2 : j ≤ 489358) : Blo 1955435 (4 * j + 3) := by
  interval_cases j
  · exact B1955435
  · exact B1955439
  · exact B1955443
  · exact B1955447
  · exact B1955451
  · exact B1955455
  · exact B1955459
  · exact B1955463
  · exact B1955467
  · exact B1955471
  · exact B1955475
  · exact B1955479
  · exact B1955483
  · exact B1955487
  · exact B1955491
  · exact B1955495
  · exact B1955499
  · exact B1955503
  · exact B1955507
  · exact B1955511
  · exact B1955515
  · exact B1955519
  · exact B1955523
  · exact B1955527
  · exact B1955531
  · exact B1955535
  · exact B1955539
  · exact B1955543
  · exact B1955547
  · exact B1955551
  · exact B1955555
  · exact B1955559
  · exact B1955563
  · exact B1955567
  · exact B1955571
  · exact B1955575
  · exact B1955579
  · exact B1955583
  · exact B1955587
  · exact B1955591
  · exact B1955595
  · exact B1955599
  · exact B1955603
  · exact B1955607
  · exact B1955611
  · exact B1955615
  · exact B1955619
  · exact B1955623
  · exact B1955627
  · exact B1955631
  · exact B1955635
  · exact B1955639
  · exact B1955643
  · exact B1955647
  · exact B1955651
  · exact B1955655
  · exact B1955659
  · exact B1955663
  · exact B1955667
  · exact B1955671
  · exact B1955675
  · exact B1955679
  · exact B1955683
  · exact B1955687
  · exact B1955691
  · exact B1955695
  · exact B1955699
  · exact B1955703
  · exact B1955707
  · exact B1955711
  · exact B1955715
  · exact B1955719
  · exact B1955723
  · exact B1955727
  · exact B1955731
  · exact B1955735
  · exact B1955739
  · exact B1955743
  · exact B1955747
  · exact B1955751
  · exact B1955755
  · exact B1955759
  · exact B1955763
  · exact B1955767
  · exact B1955771
  · exact B1955775
  · exact B1955779
  · exact B1955783
  · exact B1955787
  · exact B1955791
  · exact B1955795
  · exact B1955799
  · exact B1955803
  · exact B1955807
  · exact B1955811
  · exact B1955815
  · exact B1955819
  · exact B1955823
  · exact B1955827
  · exact B1955831
  · exact B1955835
  · exact B1955839
  · exact B1955843
  · exact B1955847
  · exact B1955851
  · exact B1955855
  · exact B1955859
  · exact B1955863
  · exact B1955867
  · exact B1955871
  · exact B1955875
  · exact B1955879
  · exact B1955883
  · exact B1955887
  · exact B1955891
  · exact B1955895
  · exact B1955899
  · exact B1955903
  · exact B1955907
  · exact B1955911
  · exact B1955915
  · exact B1955919
  · exact B1955923
  · exact B1955927
  · exact B1955931
  · exact B1955935
  · exact B1955939
  · exact B1955943
  · exact B1955947
  · exact B1955951
  · exact B1955955
  · exact B1955959
  · exact B1955963
  · exact B1955967
  · exact B1955971
  · exact B1955975
  · exact B1955979
  · exact B1955983
  · exact B1955987
  · exact B1955991
  · exact B1955995
  · exact B1955999
  · exact B1956003
  · exact B1956007
  · exact B1956011
  · exact B1956015
  · exact B1956019
  · exact B1956023
  · exact B1956027
  · exact B1956031
  · exact B1956035
  · exact B1956039
  · exact B1956043
  · exact B1956047
  · exact B1956051
  · exact B1956055
  · exact B1956059
  · exact B1956063
  · exact B1956067
  · exact B1956071
  · exact B1956075
  · exact B1956079
  · exact B1956083
  · exact B1956087
  · exact B1956091
  · exact B1956095
  · exact B1956099
  · exact B1956103
  · exact B1956107
  · exact B1956111
  · exact B1956115
  · exact B1956119
  · exact B1956123
  · exact B1956127
  · exact B1956131
  · exact B1956135
  · exact B1956139
  · exact B1956143
  · exact B1956147
  · exact B1956151
  · exact B1956155
  · exact B1956159
  · exact B1956163
  · exact B1956167
  · exact B1956171
  · exact B1956175
  · exact B1956179
  · exact B1956183
  · exact B1956187
  · exact B1956191
  · exact B1956195
  · exact B1956199
  · exact B1956203
  · exact B1956207
  · exact B1956211
  · exact B1956215
  · exact B1956219
  · exact B1956223
  · exact B1956227
  · exact B1956231
  · exact B1956235
  · exact B1956239
  · exact B1956243
  · exact B1956247
  · exact B1956251
  · exact B1956255
  · exact B1956259
  · exact B1956263
  · exact B1956267
  · exact B1956271
  · exact B1956275
  · exact B1956279
  · exact B1956283
  · exact B1956287
  · exact B1956291
  · exact B1956295
  · exact B1956299
  · exact B1956303
  · exact B1956307
  · exact B1956311
  · exact B1956315
  · exact B1956319
  · exact B1956323
  · exact B1956327
  · exact B1956331
  · exact B1956335
  · exact B1956339
  · exact B1956343
  · exact B1956347
  · exact B1956351
  · exact B1956355
  · exact B1956359
  · exact B1956363
  · exact B1956367
  · exact B1956371
  · exact B1956375
  · exact B1956379
  · exact B1956383
  · exact B1956387
  · exact B1956391
  · exact B1956395
  · exact B1956399
  · exact B1956403
  · exact B1956407
  · exact B1956411
  · exact B1956415
  · exact B1956419
  · exact B1956423
  · exact B1956427
  · exact B1956431
  · exact B1956435
  · exact B1956439
  · exact B1956443
  · exact B1956447
  · exact B1956451
  · exact B1956455
  · exact B1956459
  · exact B1956463
  · exact B1956467
  · exact B1956471
  · exact B1956475
  · exact B1956479
  · exact B1956483
  · exact B1956487
  · exact B1956491
  · exact B1956495
  · exact B1956499
  · exact B1956503
  · exact B1956507
  · exact B1956511
  · exact B1956515
  · exact B1956519
  · exact B1956523
  · exact B1956527
  · exact B1956531
  · exact B1956535
  · exact B1956539
  · exact B1956543
  · exact B1956547
  · exact B1956551
  · exact B1956555
  · exact B1956559
  · exact B1956563
  · exact B1956567
  · exact B1956571
  · exact B1956575
  · exact B1956579
  · exact B1956583
  · exact B1956587
  · exact B1956591
  · exact B1956595
  · exact B1956599
  · exact B1956603
  · exact B1956607
  · exact B1956611
  · exact B1956615
  · exact B1956619
  · exact B1956623
  · exact B1956627
  · exact B1956631
  · exact B1956635
  · exact B1956639
  · exact B1956643
  · exact B1956647
  · exact B1956651
  · exact B1956655
  · exact B1956659
  · exact B1956663
  · exact B1956667
  · exact B1956671
  · exact B1956675
  · exact B1956679
  · exact B1956683
  · exact B1956687
  · exact B1956691
  · exact B1956695
  · exact B1956699
  · exact B1956703
  · exact B1956707
  · exact B1956711
  · exact B1956715
  · exact B1956719
  · exact B1956723
  · exact B1956727
  · exact B1956731
  · exact B1956735
  · exact B1956739
  · exact B1956743
  · exact B1956747
  · exact B1956751
  · exact B1956755
  · exact B1956759
  · exact B1956763
  · exact B1956767
  · exact B1956771
  · exact B1956775
  · exact B1956779
  · exact B1956783
  · exact B1956787
  · exact B1956791
  · exact B1956795
  · exact B1956799
  · exact B1956803
  · exact B1956807
  · exact B1956811
  · exact B1956815
  · exact B1956819
  · exact B1956823
  · exact B1956827
  · exact B1956831
  · exact B1956835
  · exact B1956839
  · exact B1956843
  · exact B1956847
  · exact B1956851
  · exact B1956855
  · exact B1956859
  · exact B1956863
  · exact B1956867
  · exact B1956871
  · exact B1956875
  · exact B1956879
  · exact B1956883
  · exact B1956887
  · exact B1956891
  · exact B1956895
  · exact B1956899
  · exact B1956903
  · exact B1956907
  · exact B1956911
  · exact B1956915
  · exact B1956919
  · exact B1956923
  · exact B1956927
  · exact B1956931
  · exact B1956935
  · exact B1956939
  · exact B1956943
  · exact B1956947
  · exact B1956951
  · exact B1956955
  · exact B1956959
  · exact B1956963
  · exact B1956967
  · exact B1956971
  · exact B1956975
  · exact B1956979
  · exact B1956983
  · exact B1956987
  · exact B1956991
  · exact B1956995
  · exact B1956999
  · exact B1957003
  · exact B1957007
  · exact B1957011
  · exact B1957015
  · exact B1957019
  · exact B1957023
  · exact B1957027
  · exact B1957031
  · exact B1957035
  · exact B1957039
  · exact B1957043
  · exact B1957047
  · exact B1957051
  · exact B1957055
  · exact B1957059
  · exact B1957063
  · exact B1957067
  · exact B1957071
  · exact B1957075
  · exact B1957079
  · exact B1957083
  · exact B1957087
  · exact B1957091
  · exact B1957095
  · exact B1957099
  · exact B1957103
  · exact B1957107
  · exact B1957111
  · exact B1957115
  · exact B1957119
  · exact B1957123
  · exact B1957127
  · exact B1957131
  · exact B1957135
  · exact B1957139
  · exact B1957143
  · exact B1957147
  · exact B1957151
  · exact B1957155
  · exact B1957159
  · exact B1957163
  · exact B1957167
  · exact B1957171
  · exact B1957175
  · exact B1957179
  · exact B1957183
  · exact B1957187
  · exact B1957191
  · exact B1957195
  · exact B1957199
  · exact B1957203
  · exact B1957207
  · exact B1957211
  · exact B1957215
  · exact B1957219
  · exact B1957223
  · exact B1957227
  · exact B1957231
  · exact B1957235
  · exact B1957239
  · exact B1957243
  · exact B1957247
  · exact B1957251
  · exact B1957255
  · exact B1957259
  · exact B1957263
  · exact B1957267
  · exact B1957271
  · exact B1957275
  · exact B1957279
  · exact B1957283
  · exact B1957287
  · exact B1957291
  · exact B1957295
  · exact B1957299
  · exact B1957303
  · exact B1957307
  · exact B1957311
  · exact B1957315
  · exact B1957319
  · exact B1957323
  · exact B1957327
  · exact B1957331
  · exact B1957335
  · exact B1957339
  · exact B1957343
  · exact B1957347
  · exact B1957351
  · exact B1957355
  · exact B1957359
  · exact B1957363
  · exact B1957367
  · exact B1957371
  · exact B1957375
  · exact B1957379
  · exact B1957383
  · exact B1957387
  · exact B1957391
  · exact B1957395
  · exact B1957399
  · exact B1957403
  · exact B1957407
  · exact B1957411
  · exact B1957415
  · exact B1957419
  · exact B1957423
  · exact B1957427
  · exact B1957431
  · exact B1957435
theorem solution (m : ℕ) (hlo : 1955435 ≤ m) (hhi : m ≤ 1957435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 488858 ≤ j := by omega
    have hj2 : j ≤ 489358 := by omega
    have hb : Blo 1955435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
