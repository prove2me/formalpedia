-- Prove2me | solution 1 for syracuse_descends_range_1815609_1817609
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:54:57.039079+00:00
-- url     : https://prove2.me/submissions/5485cd56-c102-4c6b-85e6-6517fd9752bc

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


theorem B3063845 : Blo 1815609 3063845 := bbase (se 4 (by rfl) ⟨287235, by rfl⟩ : syracuseStep 3063845 = 574471) (by norm_num)
theorem B4087853 : Blo 1815609 4087853 := bbase (se 3 (by rfl) ⟨766472, by rfl⟩ : syracuseStep 4087853 = 1532945) (by norm_num)
theorem B4366397 : Blo 1815609 4366397 := bbase (se 3 (by rfl) ⟨818699, by rfl⟩ : syracuseStep 4366397 = 1637399) (by norm_num)
theorem B4087925 : Blo 1815609 4087925 := bbase (se 5 (by rfl) ⟨191621, by rfl⟩ : syracuseStep 4087925 = 383243) (by norm_num)
theorem B7757957 : Blo 1815609 7757957 := bbase (se 4 (by rfl) ⟨727308, by rfl⟩ : syracuseStep 7757957 = 1454617) (by norm_num)
theorem B3063973 : Blo 1815609 3063973 := bbase (se 4 (by rfl) ⟨287247, by rfl⟩ : syracuseStep 3063973 = 574495) (by norm_num)
theorem B4087997 : Blo 1815609 4087997 := bbase (se 3 (by rfl) ⟨766499, by rfl⟩ : syracuseStep 4087997 = 1532999) (by norm_num)
theorem B4423909 : Blo 1815609 4423909 := bbase (se 4 (by rfl) ⟨414741, by rfl⟩ : syracuseStep 4423909 = 829483) (by norm_num)
theorem B3064061 : Blo 1815609 3064061 := bbase (se 3 (by rfl) ⟨574511, by rfl⟩ : syracuseStep 3064061 = 1149023) (by norm_num)
theorem B4088069 : Blo 1815609 4088069 := bbase (se 4 (by rfl) ⟨383256, by rfl⟩ : syracuseStep 4088069 = 766513) (by norm_num)
theorem B9191717 : Blo 1815609 9191717 := bbase (se 4 (by rfl) ⟨861723, by rfl⟩ : syracuseStep 9191717 = 1723447) (by norm_num)
theorem B4088141 : Blo 1815609 4088141 := bbase (se 3 (by rfl) ⟨766526, by rfl⟩ : syracuseStep 4088141 = 1533053) (by norm_num)
theorem B4596061 : Blo 1815609 4596061 := bbase (se 3 (by rfl) ⟨861761, by rfl⟩ : syracuseStep 4596061 = 1723523) (by norm_num)
theorem B6127973 : Blo 1815609 6127973 := bbase (se 4 (by rfl) ⟨574497, by rfl⟩ : syracuseStep 6127973 = 1148995) (by norm_num)
theorem B3064189 : Blo 1815609 3064189 := bbase (se 3 (by rfl) ⟨574535, by rfl⟩ : syracuseStep 3064189 = 1149071) (by norm_num)
theorem B4088213 : Blo 1815609 4088213 := bbase (se 6 (by rfl) ⟨95817, by rfl⟩ : syracuseStep 4088213 = 191635) (by norm_num)
theorem B4596173 : Blo 1815609 4596173 := bbase (se 3 (by rfl) ⟨861782, by rfl⟩ : syracuseStep 4596173 = 1723565) (by norm_num)
theorem B3064277 : Blo 1815609 3064277 := bbase (se 7 (by rfl) ⟨35909, by rfl⟩ : syracuseStep 3064277 = 71819) (by norm_num)
theorem B4088285 : Blo 1815609 4088285 := bbase (se 3 (by rfl) ⟨766553, by rfl⟩ : syracuseStep 4088285 = 1533107) (by norm_num)
theorem B3449317 : Blo 1815609 3449317 := bbase (se 4 (by rfl) ⟨323373, by rfl⟩ : syracuseStep 3449317 = 646747) (by norm_num)
theorem B4088357 : Blo 1815609 4088357 := bbase (se 4 (by rfl) ⟨383283, by rfl⟩ : syracuseStep 4088357 = 766567) (by norm_num)
theorem B10347061 : Blo 1815609 10347061 := bbase (se 5 (by rfl) ⟨485018, by rfl⟩ : syracuseStep 10347061 = 970037) (by norm_num)
theorem B3064405 : Blo 1815609 3064405 := bbase (se 8 (by rfl) ⟨17955, by rfl⟩ : syracuseStep 3064405 = 35911) (by norm_num)
theorem B4088429 : Blo 1815609 4088429 := bbase (se 3 (by rfl) ⟨766580, by rfl⟩ : syracuseStep 4088429 = 1533161) (by norm_num)
theorem B3449461 : Blo 1815609 3449461 := bbase (se 5 (by rfl) ⟨161693, by rfl⟩ : syracuseStep 3449461 = 323387) (by norm_num)
theorem B4596365 : Blo 1815609 4596365 := bbase (se 3 (by rfl) ⟨861818, by rfl⟩ : syracuseStep 4596365 = 1723637) (by norm_num)
theorem B3064493 : Blo 1815609 3064493 := bbase (se 3 (by rfl) ⟨574592, by rfl⟩ : syracuseStep 3064493 = 1149185) (by norm_num)
theorem B4088501 : Blo 1815609 4088501 := bbase (se 5 (by rfl) ⟨191648, by rfl⟩ : syracuseStep 4088501 = 383297) (by norm_num)
theorem B6898405 : Blo 1815609 6898405 := bbase (se 4 (by rfl) ⟨646725, by rfl⟩ : syracuseStep 6898405 = 1293451) (by norm_num)
theorem B4088573 : Blo 1815609 4088573 := bbase (se 3 (by rfl) ⟨766607, by rfl⟩ : syracuseStep 4088573 = 1533215) (by norm_num)
theorem B6128405 : Blo 1815609 6128405 := bbase (se 6 (by rfl) ⟨143634, by rfl⟩ : syracuseStep 6128405 = 287269) (by norm_num)
theorem B3449621 : Blo 1815609 3449621 := bbase (se 6 (by rfl) ⟨80850, by rfl⟩ : syracuseStep 3449621 = 161701) (by norm_num)
theorem B3064621 : Blo 1815609 3064621 := bbase (se 3 (by rfl) ⟨574616, by rfl⟩ : syracuseStep 3064621 = 1149233) (by norm_num)
theorem B4088645 : Blo 1815609 4088645 := bbase (se 4 (by rfl) ⟨383310, by rfl⟩ : syracuseStep 4088645 = 766621) (by norm_num)
theorem B15524693 : Blo 1815609 15524693 := bbase (se 9 (by rfl) ⟨45482, by rfl⟩ : syracuseStep 15524693 = 90965) (by norm_num)
theorem B2909029 : Blo 1815609 2909029 := bbase (se 4 (by rfl) ⟨272721, by rfl⟩ : syracuseStep 2909029 = 545443) (by norm_num)
theorem B3064709 : Blo 1815609 3064709 := bbase (se 4 (by rfl) ⟨287316, by rfl⟩ : syracuseStep 3064709 = 574633) (by norm_num)
theorem B4088717 : Blo 1815609 4088717 := bbase (se 3 (by rfl) ⟨766634, by rfl⟩ : syracuseStep 4088717 = 1533269) (by norm_num)
theorem B3449765 : Blo 1815609 3449765 := bbase (se 4 (by rfl) ⟨323415, by rfl⟩ : syracuseStep 3449765 = 646831) (by norm_num)
theorem B15516629 : Blo 1815609 15516629 := bbase (se 7 (by rfl) ⟨181835, by rfl⟩ : syracuseStep 15516629 = 363671) (by norm_num)
theorem B4088789 : Blo 1815609 4088789 := bbase (se 7 (by rfl) ⟨47915, by rfl⟩ : syracuseStep 4088789 = 95831) (by norm_num)
theorem B4596709 : Blo 1815609 4596709 := bbase (se 4 (by rfl) ⟨430941, by rfl⟩ : syracuseStep 4596709 = 861883) (by norm_num)
theorem B3064837 : Blo 1815609 3064837 := bbase (se 4 (by rfl) ⟨287328, by rfl⟩ : syracuseStep 3064837 = 574657) (by norm_num)
theorem B6898709 : Blo 1815609 6898709 := bbase (se 6 (by rfl) ⟨161688, by rfl⟩ : syracuseStep 6898709 = 323377) (by norm_num)
theorem B4088861 : Blo 1815609 4088861 := bbase (se 3 (by rfl) ⟨766661, by rfl⟩ : syracuseStep 4088861 = 1533323) (by norm_num)
theorem B4596821 : Blo 1815609 4596821 := bbase (se 8 (by rfl) ⟨26934, by rfl⟩ : syracuseStep 4596821 = 53869) (by norm_num)
theorem B3064925 : Blo 1815609 3064925 := bbase (se 3 (by rfl) ⟨574673, by rfl⟩ : syracuseStep 3064925 = 1149347) (by norm_num)
theorem B4088933 : Blo 1815609 4088933 := bbase (se 4 (by rfl) ⟨383337, by rfl⟩ : syracuseStep 4088933 = 766675) (by norm_num)
theorem B9200789 : Blo 1815609 9200789 := bbase (se 6 (by rfl) ⟨215643, by rfl⟩ : syracuseStep 9200789 = 431287) (by norm_num)
theorem B4089005 : Blo 1815609 4089005 := bbase (se 3 (by rfl) ⟨766688, by rfl⟩ : syracuseStep 4089005 = 1533377) (by norm_num)
theorem B6128837 : Blo 1815609 6128837 := bbase (se 4 (by rfl) ⟨574578, by rfl⟩ : syracuseStep 6128837 = 1149157) (by norm_num)
theorem B3450053 : Blo 1815609 3450053 := bbase (se 4 (by rfl) ⟨323442, by rfl⟩ : syracuseStep 3450053 = 646885) (by norm_num)
theorem B5817557 : Blo 1815609 5817557 := bbase (se 7 (by rfl) ⟨68174, by rfl⟩ : syracuseStep 5817557 = 136349) (by norm_num)
theorem B3065053 : Blo 1815609 3065053 := bbase (se 3 (by rfl) ⟨574697, by rfl⟩ : syracuseStep 3065053 = 1149395) (by norm_num)
theorem B4089077 : Blo 1815609 4089077 := bbase (se 5 (by rfl) ⟨191675, by rfl⟩ : syracuseStep 4089077 = 383351) (by norm_num)
theorem B4597013 : Blo 1815609 4597013 := bbase (se 6 (by rfl) ⟨107742, by rfl⟩ : syracuseStep 4597013 = 215485) (by norm_num)
theorem B33596693 : Blo 1815609 33596693 := bbase (se 6 (by rfl) ⟨787422, by rfl⟩ : syracuseStep 33596693 = 1574845) (by norm_num)
theorem B3065141 : Blo 1815609 3065141 := bbase (se 5 (by rfl) ⟨143678, by rfl⟩ : syracuseStep 3065141 = 287357) (by norm_num)
theorem B4089149 : Blo 1815609 4089149 := bbase (se 3 (by rfl) ⟨766715, by rfl⟩ : syracuseStep 4089149 = 1533431) (by norm_num)
theorem B3450205 : Blo 1815609 3450205 := bbase (se 3 (by rfl) ⟨646913, by rfl⟩ : syracuseStep 3450205 = 1293827) (by norm_num)
theorem B4089221 : Blo 1815609 4089221 := bbase (se 4 (by rfl) ⟨383364, by rfl⟩ : syracuseStep 4089221 = 766729) (by norm_num)
theorem B3065269 : Blo 1815609 3065269 := bbase (se 5 (by rfl) ⟨143684, by rfl⟩ : syracuseStep 3065269 = 287369) (by norm_num)
theorem B4089293 : Blo 1815609 4089293 := bbase (se 3 (by rfl) ⟨766742, by rfl⟩ : syracuseStep 4089293 = 1533485) (by norm_num)
theorem B5170661 : Blo 1815609 5170661 := bbase (se 4 (by rfl) ⟨484749, by rfl⟩ : syracuseStep 5170661 = 969499) (by norm_num)
theorem B2909701 : Blo 1815609 2909701 := bbase (se 4 (by rfl) ⟨272784, by rfl⟩ : syracuseStep 2909701 = 545569) (by norm_num)
theorem B3065357 : Blo 1815609 3065357 := bbase (se 3 (by rfl) ⟨574754, by rfl⟩ : syracuseStep 3065357 = 1149509) (by norm_num)
theorem B4089365 : Blo 1815609 4089365 := bbase (se 6 (by rfl) ⟨95844, by rfl⟩ : syracuseStep 4089365 = 191689) (by norm_num)
theorem B8726069 : Blo 1815609 8726069 := bbase (se 5 (by rfl) ⟨409034, by rfl⟩ : syracuseStep 8726069 = 818069) (by norm_num)
theorem B9193013 : Blo 1815609 9193013 := bbase (se 5 (by rfl) ⟨430922, by rfl⟩ : syracuseStep 9193013 = 861845) (by norm_num)
theorem B4089437 : Blo 1815609 4089437 := bbase (se 3 (by rfl) ⟨766769, by rfl⟩ : syracuseStep 4089437 = 1533539) (by norm_num)
theorem B4597357 : Blo 1815609 4597357 := bbase (se 3 (by rfl) ⟨862004, by rfl⟩ : syracuseStep 4597357 = 1724009) (by norm_num)
theorem B11634293 : Blo 1815609 11634293 := bbase (se 5 (by rfl) ⟨545357, by rfl⟩ : syracuseStep 11634293 = 1090715) (by norm_num)
theorem B3106421 : Blo 1815609 3106421 := bbase (se 5 (by rfl) ⟨145613, by rfl⟩ : syracuseStep 3106421 = 291227) (by norm_num)
theorem B6129269 : Blo 1815609 6129269 := bbase (se 5 (by rfl) ⟨287309, by rfl⟩ : syracuseStep 6129269 = 574619) (by norm_num)
theorem B4662917 : Blo 1815609 4662917 := bbase (se 4 (by rfl) ⟨437148, by rfl⟩ : syracuseStep 4662917 = 874297) (by norm_num)
theorem B3065485 : Blo 1815609 3065485 := bbase (se 3 (by rfl) ⟨574778, by rfl⟩ : syracuseStep 3065485 = 1149557) (by norm_num)
theorem B3450509 : Blo 1815609 3450509 := bbase (se 3 (by rfl) ⟨646970, by rfl⟩ : syracuseStep 3450509 = 1293941) (by norm_num)
theorem B2950805 : Blo 1815609 2950805 := bbase (se 6 (by rfl) ⟨69159, by rfl⟩ : syracuseStep 2950805 = 138319) (by norm_num)
theorem B4089509 : Blo 1815609 4089509 := bbase (se 4 (by rfl) ⟨383391, by rfl⟩ : syracuseStep 4089509 = 766783) (by norm_num)
theorem B4597469 : Blo 1815609 4597469 := bbase (se 3 (by rfl) ⟨862025, by rfl⟩ : syracuseStep 4597469 = 1724051) (by norm_num)
theorem B3065573 : Blo 1815609 3065573 := bbase (se 4 (by rfl) ⟨287397, by rfl⟩ : syracuseStep 3065573 = 574795) (by norm_num)
theorem B4089581 : Blo 1815609 4089581 := bbase (se 3 (by rfl) ⟨766796, by rfl⟩ : syracuseStep 4089581 = 1533593) (by norm_num)
theorem B3065701 : Blo 1815609 3065701 := bbase (se 4 (by rfl) ⟨287409, by rfl⟩ : syracuseStep 3065701 = 574819) (by norm_num)
theorem B4597661 : Blo 1815609 4597661 := bbase (se 3 (by rfl) ⟨862061, by rfl⟩ : syracuseStep 4597661 = 1724123) (by norm_num)
theorem B2762669 : Blo 1815609 2762669 := bbase (se 3 (by rfl) ⟨518000, by rfl⟩ : syracuseStep 2762669 = 1036001) (by norm_num)
theorem B3065789 : Blo 1815609 3065789 := bbase (se 3 (by rfl) ⟨574835, by rfl⟩ : syracuseStep 3065789 = 1149671) (by norm_num)
theorem B6129701 : Blo 1815609 6129701 := bbase (se 4 (by rfl) ⟨574659, by rfl⟩ : syracuseStep 6129701 = 1149319) (by norm_num)
theorem B6211637 : Blo 1815609 6211637 := bbase (se 5 (by rfl) ⟨291170, by rfl⟩ : syracuseStep 6211637 = 582341) (by norm_num)
theorem B3065917 : Blo 1815609 3065917 := bbase (se 3 (by rfl) ⟨574859, by rfl⟩ : syracuseStep 3065917 = 1149719) (by norm_num)
theorem B3066005 : Blo 1815609 3066005 := bbase (se 6 (by rfl) ⟨71859, by rfl⟩ : syracuseStep 3066005 = 143719) (by norm_num)
theorem B2181325 : Blo 1815609 2181325 := bbase (se 3 (by rfl) ⟨408998, by rfl⟩ : syracuseStep 2181325 = 817997) (by norm_num)
theorem B4598005 : Blo 1815609 4598005 := bbase (se 5 (by rfl) ⟨215531, by rfl⟩ : syracuseStep 4598005 = 431063) (by norm_num)
theorem B4663565 : Blo 1815609 4663565 := bbase (se 3 (by rfl) ⟨874418, by rfl⟩ : syracuseStep 4663565 = 1748837) (by norm_num)
theorem B3066133 : Blo 1815609 3066133 := bbase (se 6 (by rfl) ⟨71862, by rfl⟩ : syracuseStep 3066133 = 143725) (by norm_num)
theorem B4598117 : Blo 1815609 4598117 := bbase (se 4 (by rfl) ⟨431073, by rfl⟩ : syracuseStep 4598117 = 862147) (by norm_num)
theorem B3066221 : Blo 1815609 3066221 := bbase (se 3 (by rfl) ⟨574916, by rfl⟩ : syracuseStep 3066221 = 1149833) (by norm_num)
theorem B2394541 : Blo 1815609 2394541 := bbase (se 3 (by rfl) ⟨448976, by rfl⟩ : syracuseStep 2394541 = 897953) (by norm_num)
theorem B6130133 : Blo 1815609 6130133 := bbase (se 7 (by rfl) ⟨71837, by rfl⟩ : syracuseStep 6130133 = 143675) (by norm_num)
theorem B3066349 : Blo 1815609 3066349 := bbase (se 3 (by rfl) ⟨574940, by rfl⟩ : syracuseStep 3066349 = 1149881) (by norm_num)
theorem B2910701 : Blo 1815609 2910701 := bbase (se 3 (by rfl) ⟨545756, by rfl⟩ : syracuseStep 2910701 = 1091513) (by norm_num)
theorem B10349045 : Blo 1815609 10349045 := bbase (se 5 (by rfl) ⟨485111, by rfl⟩ : syracuseStep 10349045 = 970223) (by norm_num)
theorem B4975141 : Blo 1815609 4975141 := bbase (se 4 (by rfl) ⟨466419, by rfl⟩ : syracuseStep 4975141 = 932839) (by norm_num)
theorem B4598309 : Blo 1815609 4598309 := bbase (se 4 (by rfl) ⟨431091, by rfl⟩ : syracuseStep 4598309 = 862183) (by norm_num)
theorem B3066437 : Blo 1815609 3066437 := bbase (se 4 (by rfl) ⟨287478, by rfl⟩ : syracuseStep 3066437 = 574957) (by norm_num)
theorem B5171845 : Blo 1815609 5171845 := bbase (se 4 (by rfl) ⟨484860, by rfl⟩ : syracuseStep 5171845 = 969721) (by norm_num)
theorem B3148445 : Blo 1815609 3148445 := bbase (se 3 (by rfl) ⟨590333, by rfl⟩ : syracuseStep 3148445 = 1180667) (by norm_num)
theorem B9087653 : Blo 1815609 9087653 := bbase (se 4 (by rfl) ⟨851967, by rfl⟩ : syracuseStep 9087653 = 1703935) (by norm_num)
theorem B2329277 : Blo 1815609 2329277 := bbase (se 3 (by rfl) ⟨436739, by rfl⟩ : syracuseStep 2329277 = 873479) (by norm_num)
theorem B3066565 : Blo 1815609 3066565 := bbase (se 4 (by rfl) ⟨287490, by rfl⟩ : syracuseStep 3066565 = 574981) (by norm_num)
theorem B2042581 : Blo 1815609 2042581 := bbase (se 7 (by rfl) ⟨23936, by rfl⟩ : syracuseStep 2042581 = 47873) (by norm_num)
theorem B2042617 : Blo 1815609 2042617 := bbase (se 2 (by rfl) ⟨765981, by rfl⟩ : syracuseStep 2042617 = 1531963) (by norm_num)
theorem B17705749 : Blo 1815609 17705749 := bbase (se 6 (by rfl) ⟨414978, by rfl⟩ : syracuseStep 17705749 = 829957) (by norm_num)
theorem B2042653 : Blo 1815609 2042653 := bbase (se 3 (by rfl) ⟨382997, by rfl⟩ : syracuseStep 2042653 = 765995) (by norm_num)
theorem B3066653 : Blo 1815609 3066653 := bbase (se 3 (by rfl) ⟨574997, by rfl⟩ : syracuseStep 3066653 = 1149995) (by norm_num)
theorem B5172005 : Blo 1815609 5172005 := bbase (se 4 (by rfl) ⟨484875, by rfl⟩ : syracuseStep 5172005 = 969751) (by norm_num)
theorem B2042689 : Blo 1815609 2042689 := bbase (se 2 (by rfl) ⟨766008, by rfl⟩ : syracuseStep 2042689 = 1532017) (by norm_num)
theorem B9194309 : Blo 1815609 9194309 := bbase (se 4 (by rfl) ⟨861966, by rfl⟩ : syracuseStep 9194309 = 1723933) (by norm_num)
theorem B3681101 : Blo 1815609 3681101 := bbase (se 3 (by rfl) ⟨690206, by rfl⟩ : syracuseStep 3681101 = 1380413) (by norm_num)
theorem B2042725 : Blo 1815609 2042725 := bbase (se 4 (by rfl) ⟨191505, by rfl⟩ : syracuseStep 2042725 = 383011) (by norm_num)
theorem B4598653 : Blo 1815609 4598653 := bbase (se 3 (by rfl) ⟨862247, by rfl⟩ : syracuseStep 4598653 = 1724495) (by norm_num)
theorem B6130565 : Blo 1815609 6130565 := bbase (se 4 (by rfl) ⟨574740, by rfl⟩ : syracuseStep 6130565 = 1149481) (by norm_num)
theorem B6548357 : Blo 1815609 6548357 := bbase (se 4 (by rfl) ⟨613908, by rfl⟩ : syracuseStep 6548357 = 1227817) (by norm_num)
theorem B2042761 : Blo 1815609 2042761 := bbase (se 2 (by rfl) ⟨766035, by rfl⟩ : syracuseStep 2042761 = 1532071) (by norm_num)
theorem B3066781 : Blo 1815609 3066781 := bbase (se 3 (by rfl) ⟨575021, by rfl⟩ : syracuseStep 3066781 = 1150043) (by norm_num)
theorem B2042797 : Blo 1815609 2042797 := bbase (se 3 (by rfl) ⟨383024, by rfl⟩ : syracuseStep 2042797 = 766049) (by norm_num)
theorem B3681221 : Blo 1815609 3681221 := bbase (se 4 (by rfl) ⟨345114, by rfl⟩ : syracuseStep 3681221 = 690229) (by norm_num)
theorem B2100173 : Blo 1815609 2100173 := bbase (se 3 (by rfl) ⟨393782, by rfl⟩ : syracuseStep 2100173 = 787565) (by norm_num)
theorem B2042833 : Blo 1815609 2042833 := bbase (se 2 (by rfl) ⟨766062, by rfl⟩ : syracuseStep 2042833 = 1532125) (by norm_num)
theorem B4598765 : Blo 1815609 4598765 := bbase (se 3 (by rfl) ⟨862268, by rfl⟩ : syracuseStep 4598765 = 1724537) (by norm_num)
theorem B2042869 : Blo 1815609 2042869 := bbase (se 5 (by rfl) ⟨95759, by rfl⟩ : syracuseStep 2042869 = 191519) (by norm_num)
theorem B5598197 : Blo 1815609 5598197 := bbase (se 5 (by rfl) ⟨262415, by rfl⟩ : syracuseStep 5598197 = 524831) (by norm_num)
theorem B3066869 : Blo 1815609 3066869 := bbase (se 5 (by rfl) ⟨143759, by rfl⟩ : syracuseStep 3066869 = 287519) (by norm_num)
theorem B3877885 : Blo 1815609 3877885 := bbase (se 3 (by rfl) ⟨727103, by rfl⟩ : syracuseStep 3877885 = 1454207) (by norm_num)
theorem B5172245 : Blo 1815609 5172245 := bbase (se 6 (by rfl) ⟨121224, by rfl⟩ : syracuseStep 5172245 = 242449) (by norm_num)
theorem B2042905 : Blo 1815609 2042905 := bbase (se 2 (by rfl) ⟨766089, by rfl⟩ : syracuseStep 2042905 = 1532179) (by norm_num)
theorem B2042941 : Blo 1815609 2042941 := bbase (se 3 (by rfl) ⟨383051, by rfl⟩ : syracuseStep 2042941 = 766103) (by norm_num)
theorem B6900821 : Blo 1815609 6900821 := bbase (se 8 (by rfl) ⟨40434, by rfl⟩ : syracuseStep 6900821 = 80869) (by norm_num)
theorem B2042977 : Blo 1815609 2042977 := bbase (se 2 (by rfl) ⟨766116, by rfl⟩ : syracuseStep 2042977 = 1532233) (by norm_num)
theorem B3066997 : Blo 1815609 3066997 := bbase (se 5 (by rfl) ⟨143765, by rfl⟩ : syracuseStep 3066997 = 287531) (by norm_num)
theorem B2329733 : Blo 1815609 2329733 := bbase (se 4 (by rfl) ⟨218412, by rfl⟩ : syracuseStep 2329733 = 436825) (by norm_num)
theorem B2043013 : Blo 1815609 2043013 := bbase (se 4 (by rfl) ⟨191532, by rfl⟩ : syracuseStep 2043013 = 383065) (by norm_num)
theorem B2043049 : Blo 1815609 2043049 := bbase (se 2 (by rfl) ⟨766143, by rfl⟩ : syracuseStep 2043049 = 1532287) (by norm_num)
theorem B4598957 : Blo 1815609 4598957 := bbase (se 3 (by rfl) ⟨862304, by rfl⟩ : syracuseStep 4598957 = 1724609) (by norm_num)
theorem B2043085 : Blo 1815609 2043085 := bbase (se 3 (by rfl) ⟨383078, by rfl⟩ : syracuseStep 2043085 = 766157) (by norm_num)
theorem B2182349 : Blo 1815609 2182349 := bbase (se 3 (by rfl) ⟨409190, by rfl⟩ : syracuseStep 2182349 = 818381) (by norm_num)
theorem B3067085 : Blo 1815609 3067085 := bbase (se 3 (by rfl) ⟨575078, by rfl⟩ : syracuseStep 3067085 = 1150157) (by norm_num)
theorem B9817301 : Blo 1815609 9817301 := bbase (se 7 (by rfl) ⟨115046, by rfl⟩ : syracuseStep 9817301 = 230093) (by norm_num)
theorem B5172437 : Blo 1815609 5172437 := bbase (se 7 (by rfl) ⟨60614, by rfl⟩ : syracuseStep 5172437 = 121229) (by norm_num)
theorem B2043121 : Blo 1815609 2043121 := bbase (se 2 (by rfl) ⟨766170, by rfl⟩ : syracuseStep 2043121 = 1532341) (by norm_num)
theorem B8285429 : Blo 1815609 8285429 := bbase (se 5 (by rfl) ⟨388379, by rfl⟩ : syracuseStep 8285429 = 776759) (by norm_num)
theorem B9325813 : Blo 1815609 9325813 := bbase (se 5 (by rfl) ⟨437147, by rfl⟩ : syracuseStep 9325813 = 874295) (by norm_num)
theorem B2043157 : Blo 1815609 2043157 := bbase (se 6 (by rfl) ⟨47886, by rfl⟩ : syracuseStep 2043157 = 95773) (by norm_num)
theorem B6130997 : Blo 1815609 6130997 := bbase (se 5 (by rfl) ⟨287390, by rfl⟩ : syracuseStep 6130997 = 574781) (by norm_num)
theorem B6548789 : Blo 1815609 6548789 := bbase (se 5 (by rfl) ⟨306974, by rfl⟩ : syracuseStep 6548789 = 613949) (by norm_num)
theorem B2043193 : Blo 1815609 2043193 := bbase (se 2 (by rfl) ⟨766197, by rfl⟩ : syracuseStep 2043193 = 1532395) (by norm_num)
theorem B3067213 : Blo 1815609 3067213 := bbase (se 3 (by rfl) ⟨575102, by rfl⟩ : syracuseStep 3067213 = 1150205) (by norm_num)
theorem B2043229 : Blo 1815609 2043229 := bbase (se 3 (by rfl) ⟨383105, by rfl⟩ : syracuseStep 2043229 = 766211) (by norm_num)
theorem B7761253 : Blo 1815609 7761253 := bbase (se 4 (by rfl) ⟨727617, by rfl⟩ : syracuseStep 7761253 = 1455235) (by norm_num)
theorem B6901109 : Blo 1815609 6901109 := bbase (se 5 (by rfl) ⟨323489, by rfl⟩ : syracuseStep 6901109 = 646979) (by norm_num)
theorem B2043265 : Blo 1815609 2043265 := bbase (se 2 (by rfl) ⟨766224, by rfl⟩ : syracuseStep 2043265 = 1532449) (by norm_num)
theorem B9325973 : Blo 1815609 9325973 := bbase (se 6 (by rfl) ⟨218577, by rfl⟩ : syracuseStep 9325973 = 437155) (by norm_num)
theorem B2043301 : Blo 1815609 2043301 := bbase (se 4 (by rfl) ⟨191559, by rfl⟩ : syracuseStep 2043301 = 383119) (by norm_num)
theorem B5819813 : Blo 1815609 5819813 := bbase (se 4 (by rfl) ⟨545607, by rfl⟩ : syracuseStep 5819813 = 1091215) (by norm_num)
theorem B2043337 : Blo 1815609 2043337 := bbase (se 2 (by rfl) ⟨766251, by rfl⟩ : syracuseStep 2043337 = 1532503) (by norm_num)
theorem B3681749 : Blo 1815609 3681749 := bbase (se 7 (by rfl) ⟨43145, by rfl⟩ : syracuseStep 3681749 = 86291) (by norm_num)
theorem B2043373 : Blo 1815609 2043373 := bbase (se 3 (by rfl) ⟨383132, by rfl⟩ : syracuseStep 2043373 = 766265) (by norm_num)
theorem B4599301 : Blo 1815609 4599301 := bbase (se 4 (by rfl) ⟨431184, by rfl⟩ : syracuseStep 4599301 = 862369) (by norm_num)
theorem B2043409 : Blo 1815609 2043409 := bbase (se 2 (by rfl) ⟨766278, by rfl⟩ : syracuseStep 2043409 = 1532557) (by norm_num)
theorem B5819941 : Blo 1815609 5819941 := bbase (se 4 (by rfl) ⟨545619, by rfl⟩ : syracuseStep 5819941 = 1091239) (by norm_num)
theorem B2043445 : Blo 1815609 2043445 := bbase (se 5 (by rfl) ⟨95786, by rfl⟩ : syracuseStep 2043445 = 191573) (by norm_num)
theorem B13798997 : Blo 1815609 13798997 := bbase (se 8 (by rfl) ⟨80853, by rfl⟩ : syracuseStep 13798997 = 161707) (by norm_num)
theorem B2043481 : Blo 1815609 2043481 := bbase (se 2 (by rfl) ⟨766305, by rfl⟩ : syracuseStep 2043481 = 1532611) (by norm_num)
theorem B2723429 : Blo 1815609 2723429 := bbase (se 4 (by rfl) ⟨255321, by rfl⟩ : syracuseStep 2723429 = 510643) (by norm_num)
theorem B4599413 : Blo 1815609 4599413 := bbase (se 5 (by rfl) ⟨215597, by rfl⟩ : syracuseStep 4599413 = 431195) (by norm_num)
theorem B2723453 : Blo 1815609 2723453 := bbase (se 3 (by rfl) ⟨510647, by rfl⟩ : syracuseStep 2723453 = 1021295) (by norm_num)
theorem B2043517 : Blo 1815609 2043517 := bbase (se 3 (by rfl) ⟨383159, by rfl⟩ : syracuseStep 2043517 = 766319) (by norm_num)
theorem B3272333 : Blo 1815609 3272333 := bbase (se 3 (by rfl) ⟨613562, by rfl⟩ : syracuseStep 3272333 = 1227125) (by norm_num)
theorem B2723477 : Blo 1815609 2723477 := bbase (se 6 (by rfl) ⟨63831, by rfl⟩ : syracuseStep 2723477 = 127663) (by norm_num)
theorem B2043553 : Blo 1815609 2043553 := bbase (se 2 (by rfl) ⟨766332, by rfl⟩ : syracuseStep 2043553 = 1532665) (by norm_num)
theorem B2723501 : Blo 1815609 2723501 := bbase (se 3 (by rfl) ⟨510656, by rfl⟩ : syracuseStep 2723501 = 1021313) (by norm_num)
theorem B2723525 : Blo 1815609 2723525 := bbase (se 4 (by rfl) ⟨255330, by rfl⟩ : syracuseStep 2723525 = 510661) (by norm_num)
theorem B2330309 : Blo 1815609 2330309 := bbase (se 4 (by rfl) ⟨218466, by rfl⟩ : syracuseStep 2330309 = 436933) (by norm_num)
theorem B2043589 : Blo 1815609 2043589 := bbase (se 4 (by rfl) ⟨191586, by rfl⟩ : syracuseStep 2043589 = 383173) (by norm_num)
theorem B2723549 : Blo 1815609 2723549 := bbase (se 3 (by rfl) ⟨510665, by rfl⟩ : syracuseStep 2723549 = 1021331) (by norm_num)
theorem B6131429 : Blo 1815609 6131429 := bbase (se 4 (by rfl) ⟨574821, by rfl⟩ : syracuseStep 6131429 = 1149643) (by norm_num)
theorem B2043625 : Blo 1815609 2043625 := bbase (se 2 (by rfl) ⟨766359, by rfl⟩ : syracuseStep 2043625 = 1532719) (by norm_num)
theorem B4484845 : Blo 1815609 4484845 := bbase (se 3 (by rfl) ⟨840908, by rfl⟩ : syracuseStep 4484845 = 1681817) (by norm_num)
theorem B2723573 : Blo 1815609 2723573 := bbase (se 5 (by rfl) ⟨127667, by rfl⟩ : syracuseStep 2723573 = 255335) (by norm_num)
theorem B2723597 : Blo 1815609 2723597 := bbase (se 3 (by rfl) ⟨510674, by rfl⟩ : syracuseStep 2723597 = 1021349) (by norm_num)
theorem B2043661 : Blo 1815609 2043661 := bbase (se 3 (by rfl) ⟨383186, by rfl⟩ : syracuseStep 2043661 = 766373) (by norm_num)
theorem B2723621 : Blo 1815609 2723621 := bbase (se 4 (by rfl) ⟨255339, by rfl⟩ : syracuseStep 2723621 = 510679) (by norm_num)
theorem B2043697 : Blo 1815609 2043697 := bbase (se 2 (by rfl) ⟨766386, by rfl⟩ : syracuseStep 2043697 = 1532773) (by norm_num)
theorem B4599605 : Blo 1815609 4599605 := bbase (se 5 (by rfl) ⟨215606, by rfl⟩ : syracuseStep 4599605 = 431213) (by norm_num)
theorem B13987637 : Blo 1815609 13987637 := bbase (se 5 (by rfl) ⟨655670, by rfl⟩ : syracuseStep 13987637 = 1311341) (by norm_num)
theorem B2723645 : Blo 1815609 2723645 := bbase (se 3 (by rfl) ⟨510683, by rfl⟩ : syracuseStep 2723645 = 1021367) (by norm_num)
theorem B2723669 : Blo 1815609 2723669 := bbase (se 9 (by rfl) ⟨7979, by rfl⟩ : syracuseStep 2723669 = 15959) (by norm_num)
theorem B2043733 : Blo 1815609 2043733 := bbase (se 9 (by rfl) ⟨5987, by rfl⟩ : syracuseStep 2043733 = 11975) (by norm_num)
theorem B2723693 : Blo 1815609 2723693 := bbase (se 3 (by rfl) ⟨510692, by rfl⟩ : syracuseStep 2723693 = 1021385) (by norm_num)
theorem B6549365 : Blo 1815609 6549365 := bbase (se 5 (by rfl) ⟨307001, by rfl⟩ : syracuseStep 6549365 = 614003) (by norm_num)
theorem B2043769 : Blo 1815609 2043769 := bbase (se 2 (by rfl) ⟨766413, by rfl⟩ : syracuseStep 2043769 = 1532827) (by norm_num)
theorem B2723717 : Blo 1815609 2723717 := bbase (se 4 (by rfl) ⟨255348, by rfl⟩ : syracuseStep 2723717 = 510697) (by norm_num)
theorem B2723741 : Blo 1815609 2723741 := bbase (se 3 (by rfl) ⟨510701, by rfl⟩ : syracuseStep 2723741 = 1021403) (by norm_num)
theorem B2043805 : Blo 1815609 2043805 := bbase (se 3 (by rfl) ⟨383213, by rfl⟩ : syracuseStep 2043805 = 766427) (by norm_num)
theorem B2723765 : Blo 1815609 2723765 := bbase (se 5 (by rfl) ⟨127676, by rfl⟩ : syracuseStep 2723765 = 255353) (by norm_num)
theorem B2043841 : Blo 1815609 2043841 := bbase (se 2 (by rfl) ⟨766440, by rfl⟩ : syracuseStep 2043841 = 1532881) (by norm_num)
theorem B2723789 : Blo 1815609 2723789 := bbase (se 3 (by rfl) ⟨510710, by rfl⟩ : syracuseStep 2723789 = 1021421) (by norm_num)
theorem B2723813 : Blo 1815609 2723813 := bbase (se 4 (by rfl) ⟨255357, by rfl⟩ : syracuseStep 2723813 = 510715) (by norm_num)
theorem B2043877 : Blo 1815609 2043877 := bbase (se 4 (by rfl) ⟨191613, by rfl⟩ : syracuseStep 2043877 = 383227) (by norm_num)
theorem B13791221 : Blo 1815609 13791221 := bbase (se 5 (by rfl) ⟨646463, by rfl⟩ : syracuseStep 13791221 = 1292927) (by norm_num)
theorem B2723837 : Blo 1815609 2723837 := bbase (se 3 (by rfl) ⟨510719, by rfl⟩ : syracuseStep 2723837 = 1021439) (by norm_num)
theorem B2043913 : Blo 1815609 2043913 := bbase (se 2 (by rfl) ⟨766467, by rfl⟩ : syracuseStep 2043913 = 1532935) (by norm_num)
theorem B2723861 : Blo 1815609 2723861 := bbase (se 6 (by rfl) ⟨63840, by rfl⟩ : syracuseStep 2723861 = 127681) (by norm_num)
theorem B2723885 : Blo 1815609 2723885 := bbase (se 3 (by rfl) ⟨510728, by rfl⟩ : syracuseStep 2723885 = 1021457) (by norm_num)
theorem B2043949 : Blo 1815609 2043949 := bbase (se 3 (by rfl) ⟨383240, by rfl⟩ : syracuseStep 2043949 = 766481) (by norm_num)
theorem B2297909 : Blo 1815609 2297909 := bbase (se 5 (by rfl) ⟨107714, by rfl⟩ : syracuseStep 2297909 = 215429) (by norm_num)
theorem B2330677 : Blo 1815609 2330677 := bbase (se 5 (by rfl) ⟨109250, by rfl⟩ : syracuseStep 2330677 = 218501) (by norm_num)
theorem B2330689 : Blo 1815609 2330689 := bbase (se 2 (by rfl) ⟨874008, by rfl⟩ : syracuseStep 2330689 = 1748017) (by norm_num)
theorem B2723909 : Blo 1815609 2723909 := bbase (se 4 (by rfl) ⟨255366, by rfl⟩ : syracuseStep 2723909 = 510733) (by norm_num)
theorem B2043985 : Blo 1815609 2043985 := bbase (se 2 (by rfl) ⟨766494, by rfl⟩ : syracuseStep 2043985 = 1532989) (by norm_num)
theorem B9195605 : Blo 1815609 9195605 := bbase (se 8 (by rfl) ⟨53880, by rfl⟩ : syracuseStep 9195605 = 107761) (by norm_num)
theorem B2723933 : Blo 1815609 2723933 := bbase (se 3 (by rfl) ⟨510737, by rfl⟩ : syracuseStep 2723933 = 1021475) (by norm_num)
theorem B2297965 : Blo 1815609 2297965 := bbase (se 3 (by rfl) ⟨430868, by rfl⟩ : syracuseStep 2297965 = 861737) (by norm_num)
theorem B4141165 : Blo 1815609 4141165 := bbase (se 3 (by rfl) ⟨776468, by rfl⟩ : syracuseStep 4141165 = 1552937) (by norm_num)
theorem B2723957 : Blo 1815609 2723957 := bbase (se 5 (by rfl) ⟨127685, by rfl⟩ : syracuseStep 2723957 = 255371) (by norm_num)
theorem B2044021 : Blo 1815609 2044021 := bbase (se 5 (by rfl) ⟨95813, by rfl⟩ : syracuseStep 2044021 = 191627) (by norm_num)
theorem B3272837 : Blo 1815609 3272837 := bbase (se 4 (by rfl) ⟨306828, by rfl⟩ : syracuseStep 3272837 = 613657) (by norm_num)
theorem B2723981 : Blo 1815609 2723981 := bbase (se 3 (by rfl) ⟨510746, by rfl⟩ : syracuseStep 2723981 = 1021493) (by norm_num)
theorem B4599949 : Blo 1815609 4599949 := bbase (se 3 (by rfl) ⟨862490, by rfl⟩ : syracuseStep 4599949 = 1724981) (by norm_num)
theorem B6131861 : Blo 1815609 6131861 := bbase (se 6 (by rfl) ⟨143715, by rfl⟩ : syracuseStep 6131861 = 287431) (by norm_num)
theorem B2044057 : Blo 1815609 2044057 := bbase (se 2 (by rfl) ⟨766521, by rfl⟩ : syracuseStep 2044057 = 1533043) (by norm_num)
theorem B2724005 : Blo 1815609 2724005 := bbase (se 4 (by rfl) ⟨255375, by rfl⟩ : syracuseStep 2724005 = 510751) (by norm_num)
theorem B2330797 : Blo 1815609 2330797 := bbase (se 3 (by rfl) ⟨437024, by rfl⟩ : syracuseStep 2330797 = 874049) (by norm_num)
theorem B5173429 : Blo 1815609 5173429 := bbase (se 5 (by rfl) ⟨242504, by rfl⟩ : syracuseStep 5173429 = 485009) (by norm_num)
theorem B2724029 : Blo 1815609 2724029 := bbase (se 3 (by rfl) ⟨510755, by rfl⟩ : syracuseStep 2724029 = 1021511) (by norm_num)
theorem B2044093 : Blo 1815609 2044093 := bbase (se 3 (by rfl) ⟨383267, by rfl⟩ : syracuseStep 2044093 = 766535) (by norm_num)
theorem B2298061 : Blo 1815609 2298061 := bbase (se 3 (by rfl) ⟨430886, by rfl⟩ : syracuseStep 2298061 = 861773) (by norm_num)
theorem B2724053 : Blo 1815609 2724053 := bbase (se 7 (by rfl) ⟨31922, by rfl⟩ : syracuseStep 2724053 = 63845) (by norm_num)
theorem B2044129 : Blo 1815609 2044129 := bbase (se 2 (by rfl) ⟨766548, by rfl⟩ : syracuseStep 2044129 = 1533097) (by norm_num)
theorem B2724077 : Blo 1815609 2724077 := bbase (se 3 (by rfl) ⟨510764, by rfl⟩ : syracuseStep 2724077 = 1021529) (by norm_num)
theorem B4600061 : Blo 1815609 4600061 := bbase (se 3 (by rfl) ⟨862511, by rfl⟩ : syracuseStep 4600061 = 1725023) (by norm_num)
theorem B2724101 : Blo 1815609 2724101 := bbase (se 4 (by rfl) ⟨255384, by rfl⟩ : syracuseStep 2724101 = 510769) (by norm_num)
theorem B2044165 : Blo 1815609 2044165 := bbase (se 4 (by rfl) ⟨191640, by rfl⟩ : syracuseStep 2044165 = 383281) (by norm_num)
theorem B2724125 : Blo 1815609 2724125 := bbase (se 3 (by rfl) ⟨510773, by rfl⟩ : syracuseStep 2724125 = 1021547) (by norm_num)
theorem B2044201 : Blo 1815609 2044201 := bbase (se 2 (by rfl) ⟨766575, by rfl⟩ : syracuseStep 2044201 = 1533151) (by norm_num)
theorem B2724149 : Blo 1815609 2724149 := bbase (se 5 (by rfl) ⟨127694, by rfl⟩ : syracuseStep 2724149 = 255389) (by norm_num)
theorem B2724173 : Blo 1815609 2724173 := bbase (se 3 (by rfl) ⟨510782, by rfl⟩ : syracuseStep 2724173 = 1021565) (by norm_num)
theorem B2044237 : Blo 1815609 2044237 := bbase (se 3 (by rfl) ⟨383294, by rfl⟩ : syracuseStep 2044237 = 766589) (by norm_num)
theorem B2724197 : Blo 1815609 2724197 := bbase (se 4 (by rfl) ⟨255393, by rfl⟩ : syracuseStep 2724197 = 510787) (by norm_num)
theorem B2044273 : Blo 1815609 2044273 := bbase (se 2 (by rfl) ⟨766602, by rfl⟩ : syracuseStep 2044273 = 1533205) (by norm_num)
theorem B2298233 : Blo 1815609 2298233 := bbase (se 2 (by rfl) ⟨861837, by rfl⟩ : syracuseStep 2298233 = 1723675) (by norm_num)
theorem B2183545 : Blo 1815609 2183545 := bbase (se 2 (by rfl) ⟨818829, by rfl⟩ : syracuseStep 2183545 = 1637659) (by norm_num)
theorem B2724221 : Blo 1815609 2724221 := bbase (se 3 (by rfl) ⟨510791, by rfl⟩ : syracuseStep 2724221 = 1021583) (by norm_num)
theorem B2724245 : Blo 1815609 2724245 := bbase (se 6 (by rfl) ⟨63849, by rfl⟩ : syracuseStep 2724245 = 127699) (by norm_num)
theorem B2044309 : Blo 1815609 2044309 := bbase (se 6 (by rfl) ⟨47913, by rfl⟩ : syracuseStep 2044309 = 95827) (by norm_num)
theorem B2724269 : Blo 1815609 2724269 := bbase (se 3 (by rfl) ⟨510800, by rfl⟩ : syracuseStep 2724269 = 1021601) (by norm_num)
theorem B2298289 : Blo 1815609 2298289 := bbase (se 2 (by rfl) ⟨861858, by rfl⟩ : syracuseStep 2298289 = 1723717) (by norm_num)
theorem B11645365 : Blo 1815609 11645365 := bbase (se 5 (by rfl) ⟨545876, by rfl⟩ : syracuseStep 11645365 = 1091753) (by norm_num)
theorem B2044345 : Blo 1815609 2044345 := bbase (se 2 (by rfl) ⟨766629, by rfl⟩ : syracuseStep 2044345 = 1533259) (by norm_num)
theorem B4600253 : Blo 1815609 4600253 := bbase (se 3 (by rfl) ⟨862547, by rfl⟩ : syracuseStep 4600253 = 1725095) (by norm_num)
theorem B2724293 : Blo 1815609 2724293 := bbase (se 4 (by rfl) ⟨255402, by rfl⟩ : syracuseStep 2724293 = 510805) (by norm_num)
theorem B5525957 : Blo 1815609 5525957 := bbase (se 4 (by rfl) ⟨518058, by rfl⟩ : syracuseStep 5525957 = 1036117) (by norm_num)
theorem B38302165 : Blo 1815609 38302165 := bbase (se 7 (by rfl) ⟨448853, by rfl⟩ : syracuseStep 38302165 = 897707) (by norm_num)
theorem B70808021 : Blo 1815609 70808021 := bbase (se 7 (by rfl) ⟨829781, by rfl⟩ : syracuseStep 70808021 = 1659563) (by norm_num)
theorem B2724317 : Blo 1815609 2724317 := bbase (se 3 (by rfl) ⟨510809, by rfl⟩ : syracuseStep 2724317 = 1021619) (by norm_num)
theorem B3879389 : Blo 1815609 3879389 := bbase (se 3 (by rfl) ⟨727385, by rfl⟩ : syracuseStep 3879389 = 1454771) (by norm_num)
theorem B2044381 : Blo 1815609 2044381 := bbase (se 3 (by rfl) ⟨383321, by rfl⟩ : syracuseStep 2044381 = 766643) (by norm_num)
theorem B2331109 : Blo 1815609 2331109 := bbase (se 4 (by rfl) ⟨218541, by rfl⟩ : syracuseStep 2331109 = 437083) (by norm_num)
theorem B2724341 : Blo 1815609 2724341 := bbase (se 5 (by rfl) ⟨127703, by rfl⟩ : syracuseStep 2724341 = 255407) (by norm_num)
theorem B2044417 : Blo 1815609 2044417 := bbase (se 2 (by rfl) ⟨766656, by rfl⟩ : syracuseStep 2044417 = 1533313) (by norm_num)
theorem B2724365 : Blo 1815609 2724365 := bbase (se 3 (by rfl) ⟨510818, by rfl⟩ : syracuseStep 2724365 = 1021637) (by norm_num)
theorem B2298385 : Blo 1815609 2298385 := bbase (se 2 (by rfl) ⟨861894, by rfl⟩ : syracuseStep 2298385 = 1723789) (by norm_num)
theorem B11637269 : Blo 1815609 11637269 := bbase (se 6 (by rfl) ⟨272748, by rfl⟩ : syracuseStep 11637269 = 545497) (by norm_num)
theorem B2585125 : Blo 1815609 2585125 := bbase (se 4 (by rfl) ⟨242355, by rfl⟩ : syracuseStep 2585125 = 484711) (by norm_num)
theorem B2724389 : Blo 1815609 2724389 := bbase (se 4 (by rfl) ⟨255411, by rfl⟩ : syracuseStep 2724389 = 510823) (by norm_num)
theorem B2044453 : Blo 1815609 2044453 := bbase (se 4 (by rfl) ⟨191667, by rfl⟩ : syracuseStep 2044453 = 383335) (by norm_num)
theorem B2724413 : Blo 1815609 2724413 := bbase (se 3 (by rfl) ⟨510827, by rfl⟩ : syracuseStep 2724413 = 1021655) (by norm_num)
theorem B6132293 : Blo 1815609 6132293 := bbase (se 4 (by rfl) ⟨574902, by rfl⟩ : syracuseStep 6132293 = 1149805) (by norm_num)
theorem B2044489 : Blo 1815609 2044489 := bbase (se 2 (by rfl) ⟨766683, by rfl⟩ : syracuseStep 2044489 = 1533367) (by norm_num)
theorem B2724437 : Blo 1815609 2724437 := bbase (se 8 (by rfl) ⟨15963, by rfl⟩ : syracuseStep 2724437 = 31927) (by norm_num)
theorem B2724461 : Blo 1815609 2724461 := bbase (se 3 (by rfl) ⟨510836, by rfl⟩ : syracuseStep 2724461 = 1021673) (by norm_num)
theorem B3879533 : Blo 1815609 3879533 := bbase (se 3 (by rfl) ⟨727412, by rfl⟩ : syracuseStep 3879533 = 1454825) (by norm_num)
theorem B2044525 : Blo 1815609 2044525 := bbase (se 3 (by rfl) ⟨383348, by rfl⟩ : syracuseStep 2044525 = 766697) (by norm_num)
theorem B2724485 : Blo 1815609 2724485 := bbase (se 4 (by rfl) ⟨255420, by rfl⟩ : syracuseStep 2724485 = 510841) (by norm_num)
theorem B2044561 : Blo 1815609 2044561 := bbase (se 2 (by rfl) ⟨766710, by rfl⟩ : syracuseStep 2044561 = 1533421) (by norm_num)
theorem B10351253 : Blo 1815609 10351253 := bbase (se 6 (by rfl) ⟨242607, by rfl⟩ : syracuseStep 10351253 = 485215) (by norm_num)
theorem B2724509 : Blo 1815609 2724509 := bbase (se 3 (by rfl) ⟨510845, by rfl⟩ : syracuseStep 2724509 = 1021691) (by norm_num)
theorem B2724533 : Blo 1815609 2724533 := bbase (se 5 (by rfl) ⟨127712, by rfl⟩ : syracuseStep 2724533 = 255425) (by norm_num)
theorem B2044597 : Blo 1815609 2044597 := bbase (se 5 (by rfl) ⟨95840, by rfl⟩ : syracuseStep 2044597 = 191681) (by norm_num)
theorem B2298557 : Blo 1815609 2298557 := bbase (se 3 (by rfl) ⟨430979, by rfl⟩ : syracuseStep 2298557 = 861959) (by norm_num)
theorem B2724557 : Blo 1815609 2724557 := bbase (se 3 (by rfl) ⟨510854, by rfl⟩ : syracuseStep 2724557 = 1021709) (by norm_num)
theorem B2044633 : Blo 1815609 2044633 := bbase (se 2 (by rfl) ⟨766737, by rfl⟩ : syracuseStep 2044633 = 1533475) (by norm_num)
theorem B2724581 : Blo 1815609 2724581 := bbase (se 4 (by rfl) ⟨255429, by rfl⟩ : syracuseStep 2724581 = 510859) (by norm_num)
theorem B2298613 : Blo 1815609 2298613 := bbase (se 5 (by rfl) ⟨107747, by rfl⟩ : syracuseStep 2298613 = 215495) (by norm_num)
theorem B2724605 : Blo 1815609 2724605 := bbase (se 3 (by rfl) ⟨510863, by rfl⟩ : syracuseStep 2724605 = 1021727) (by norm_num)
theorem B2044669 : Blo 1815609 2044669 := bbase (se 3 (by rfl) ⟨383375, by rfl⟩ : syracuseStep 2044669 = 766751) (by norm_num)
theorem B2724629 : Blo 1815609 2724629 := bbase (se 6 (by rfl) ⟨63858, by rfl⟩ : syracuseStep 2724629 = 127717) (by norm_num)
theorem B4600597 : Blo 1815609 4600597 := bbase (se 6 (by rfl) ⟨107826, by rfl⟩ : syracuseStep 4600597 = 215653) (by norm_num)
theorem B2044705 : Blo 1815609 2044705 := bbase (se 2 (by rfl) ⟨766764, by rfl⟩ : syracuseStep 2044705 = 1533529) (by norm_num)
theorem B2724653 : Blo 1815609 2724653 := bbase (se 3 (by rfl) ⟨510872, by rfl⟩ : syracuseStep 2724653 = 1021745) (by norm_num)
theorem B2331437 : Blo 1815609 2331437 := bbase (se 3 (by rfl) ⟨437144, by rfl⟩ : syracuseStep 2331437 = 874289) (by norm_num)
theorem B2724677 : Blo 1815609 2724677 := bbase (se 4 (by rfl) ⟨255438, by rfl⟩ : syracuseStep 2724677 = 510877) (by norm_num)
theorem B2044741 : Blo 1815609 2044741 := bbase (se 4 (by rfl) ⟨191694, by rfl⟩ : syracuseStep 2044741 = 383389) (by norm_num)
theorem B2298709 : Blo 1815609 2298709 := bbase (se 9 (by rfl) ⟨6734, by rfl⟩ : syracuseStep 2298709 = 13469) (by norm_num)
theorem B2724701 : Blo 1815609 2724701 := bbase (se 3 (by rfl) ⟨510881, by rfl⟩ : syracuseStep 2724701 = 1021763) (by norm_num)
theorem B2044777 : Blo 1815609 2044777 := bbase (se 2 (by rfl) ⟨766791, by rfl⟩ : syracuseStep 2044777 = 1533583) (by norm_num)
theorem B3273581 : Blo 1815609 3273581 := bbase (se 3 (by rfl) ⟨613796, by rfl⟩ : syracuseStep 3273581 = 1227593) (by norm_num)
theorem B2724725 : Blo 1815609 2724725 := bbase (se 5 (by rfl) ⟨127721, by rfl⟩ : syracuseStep 2724725 = 255443) (by norm_num)
theorem B4600709 : Blo 1815609 4600709 := bbase (se 4 (by rfl) ⟨431316, by rfl⟩ : syracuseStep 4600709 = 862633) (by norm_num)
theorem B2724749 : Blo 1815609 2724749 := bbase (se 3 (by rfl) ⟨510890, by rfl⟩ : syracuseStep 2724749 = 1021781) (by norm_num)
theorem B2724773 : Blo 1815609 2724773 := bbase (se 4 (by rfl) ⟨255447, by rfl⟩ : syracuseStep 2724773 = 510895) (by norm_num)
theorem B6894517 : Blo 1815609 6894517 := bbase (se 5 (by rfl) ⟨323180, by rfl⟩ : syracuseStep 6894517 = 646361) (by norm_num)
theorem B2724797 : Blo 1815609 2724797 := bbase (se 3 (by rfl) ⟨510899, by rfl⟩ : syracuseStep 2724797 = 1021799) (by norm_num)
theorem B2724821 : Blo 1815609 2724821 := bbase (se 7 (by rfl) ⟨31931, by rfl⟩ : syracuseStep 2724821 = 63863) (by norm_num)
theorem B3879893 : Blo 1815609 3879893 := bbase (se 7 (by rfl) ⟨45467, by rfl⟩ : syracuseStep 3879893 = 90935) (by norm_num)
theorem B2724845 : Blo 1815609 2724845 := bbase (se 3 (by rfl) ⟨510908, by rfl⟩ : syracuseStep 2724845 = 1021817) (by norm_num)
theorem B6132725 : Blo 1815609 6132725 := bbase (se 5 (by rfl) ⟨287471, by rfl⟩ : syracuseStep 6132725 = 574943) (by norm_num)
theorem B2298881 : Blo 1815609 2298881 := bbase (se 2 (by rfl) ⟨862080, by rfl⟩ : syracuseStep 2298881 = 1724161) (by norm_num)
theorem B2724869 : Blo 1815609 2724869 := bbase (se 4 (by rfl) ⟨255456, by rfl⟩ : syracuseStep 2724869 = 510913) (by norm_num)
theorem B2585621 : Blo 1815609 2585621 := bbase (se 6 (by rfl) ⟨60600, by rfl⟩ : syracuseStep 2585621 = 121201) (by norm_num)
theorem B2724893 : Blo 1815609 2724893 := bbase (se 3 (by rfl) ⟨510917, by rfl⟩ : syracuseStep 2724893 = 1021835) (by norm_num)
theorem B2724917 : Blo 1815609 2724917 := bbase (se 5 (by rfl) ⟨127730, by rfl⟩ : syracuseStep 2724917 = 255461) (by norm_num)
theorem B2298937 : Blo 1815609 2298937 := bbase (se 2 (by rfl) ⟨862101, by rfl⟩ : syracuseStep 2298937 = 1724203) (by norm_num)
theorem B2724941 : Blo 1815609 2724941 := bbase (se 3 (by rfl) ⟨510926, by rfl⟩ : syracuseStep 2724941 = 1021853) (by norm_num)
theorem B2724965 : Blo 1815609 2724965 := bbase (se 4 (by rfl) ⟨255465, by rfl⟩ : syracuseStep 2724965 = 510931) (by norm_num)
theorem B2724989 : Blo 1815609 2724989 := bbase (se 3 (by rfl) ⟨510935, by rfl⟩ : syracuseStep 2724989 = 1021871) (by norm_num)
theorem B2725013 : Blo 1815609 2725013 := bbase (se 6 (by rfl) ⟨63867, by rfl⟩ : syracuseStep 2725013 = 127735) (by norm_num)
theorem B2299033 : Blo 1815609 2299033 := bbase (se 2 (by rfl) ⟨862137, by rfl⟩ : syracuseStep 2299033 = 1724275) (by norm_num)
theorem B2725037 : Blo 1815609 2725037 := bbase (se 3 (by rfl) ⟨510944, by rfl⟩ : syracuseStep 2725037 = 1021889) (by norm_num)
theorem B2725061 : Blo 1815609 2725061 := bbase (se 4 (by rfl) ⟨255474, by rfl⟩ : syracuseStep 2725061 = 510949) (by norm_num)
theorem B2725085 : Blo 1815609 2725085 := bbase (se 3 (by rfl) ⟨510953, by rfl⟩ : syracuseStep 2725085 = 1021907) (by norm_num)
theorem B6894821 : Blo 1815609 6894821 := bbase (se 4 (by rfl) ⟨646389, by rfl⟩ : syracuseStep 6894821 = 1292779) (by norm_num)
theorem B2725109 : Blo 1815609 2725109 := bbase (se 5 (by rfl) ⟨127739, by rfl⟩ : syracuseStep 2725109 = 255479) (by norm_num)
theorem B4142333 : Blo 1815609 4142333 := bbase (se 3 (by rfl) ⟨776687, by rfl⟩ : syracuseStep 4142333 = 1553375) (by norm_num)
theorem B5174533 : Blo 1815609 5174533 := bbase (se 4 (by rfl) ⟨485112, by rfl⟩ : syracuseStep 5174533 = 970225) (by norm_num)
theorem B2725133 : Blo 1815609 2725133 := bbase (se 3 (by rfl) ⟨510962, by rfl⟩ : syracuseStep 2725133 = 1021925) (by norm_num)
theorem B2725157 : Blo 1815609 2725157 := bbase (se 4 (by rfl) ⟨255483, by rfl⟩ : syracuseStep 2725157 = 510967) (by norm_num)
theorem B2725181 : Blo 1815609 2725181 := bbase (se 3 (by rfl) ⟨510971, by rfl⟩ : syracuseStep 2725181 = 1021943) (by norm_num)
theorem B2299205 : Blo 1815609 2299205 := bbase (se 4 (by rfl) ⟨215550, by rfl⟩ : syracuseStep 2299205 = 431101) (by norm_num)
theorem B2725205 : Blo 1815609 2725205 := bbase (se 14 (by rfl) ⟨249, by rfl⟩ : syracuseStep 2725205 = 499) (by norm_num)
theorem B2692445 : Blo 1815609 2692445 := bbase (se 3 (by rfl) ⟨504833, by rfl⟩ : syracuseStep 2692445 = 1009667) (by norm_num)
theorem B9196901 : Blo 1815609 9196901 := bbase (se 4 (by rfl) ⟨862209, by rfl⟩ : syracuseStep 9196901 = 1724419) (by norm_num)
theorem B2725229 : Blo 1815609 2725229 := bbase (se 3 (by rfl) ⟨510980, by rfl⟩ : syracuseStep 2725229 = 1021961) (by norm_num)
theorem B2299261 : Blo 1815609 2299261 := bbase (se 3 (by rfl) ⟨431111, by rfl⟩ : syracuseStep 2299261 = 862223) (by norm_num)
theorem B2725253 : Blo 1815609 2725253 := bbase (se 4 (by rfl) ⟨255492, by rfl⟩ : syracuseStep 2725253 = 510985) (by norm_num)
theorem B4142477 : Blo 1815609 4142477 := bbase (se 3 (by rfl) ⟨776714, by rfl⟩ : syracuseStep 4142477 = 1553429) (by norm_num)
theorem B2725277 : Blo 1815609 2725277 := bbase (se 3 (by rfl) ⟨510989, by rfl⟩ : syracuseStep 2725277 = 1021979) (by norm_num)
theorem B1938853 : Blo 1815609 1938853 := bbase (se 4 (by rfl) ⟨181767, by rfl⟩ : syracuseStep 1938853 = 363535) (by norm_num)
theorem B6133157 : Blo 1815609 6133157 := bbase (se 4 (by rfl) ⟨574983, by rfl⟩ : syracuseStep 6133157 = 1149967) (by norm_num)
theorem B2725301 : Blo 1815609 2725301 := bbase (se 5 (by rfl) ⟨127748, by rfl⟩ : syracuseStep 2725301 = 255497) (by norm_num)
theorem B4085189 : Blo 1815609 4085189 := bbase (se 4 (by rfl) ⟨382986, by rfl⟩ : syracuseStep 4085189 = 765973) (by norm_num)
theorem B2725325 : Blo 1815609 2725325 := bbase (se 3 (by rfl) ⟨510998, by rfl⟩ : syracuseStep 2725325 = 1021997) (by norm_num)
theorem B2299357 : Blo 1815609 2299357 := bbase (se 3 (by rfl) ⟨431129, by rfl⟩ : syracuseStep 2299357 = 862259) (by norm_num)
theorem B2725349 : Blo 1815609 2725349 := bbase (se 4 (by rfl) ⟨255501, by rfl⟩ : syracuseStep 2725349 = 511003) (by norm_num)
theorem B2725373 : Blo 1815609 2725373 := bbase (se 3 (by rfl) ⟨511007, by rfl⟩ : syracuseStep 2725373 = 1022015) (by norm_num)
theorem B4085261 : Blo 1815609 4085261 := bbase (se 3 (by rfl) ⟨765986, by rfl⟩ : syracuseStep 4085261 = 1531973) (by norm_num)
theorem B2725397 : Blo 1815609 2725397 := bbase (se 6 (by rfl) ⟨63876, by rfl⟩ : syracuseStep 2725397 = 127753) (by norm_num)
theorem B2725421 : Blo 1815609 2725421 := bbase (se 3 (by rfl) ⟨511016, by rfl⟩ : syracuseStep 2725421 = 1022033) (by norm_num)
theorem B2586173 : Blo 1815609 2586173 := bbase (se 3 (by rfl) ⟨484907, by rfl⟩ : syracuseStep 2586173 = 969815) (by norm_num)
theorem B2725445 : Blo 1815609 2725445 := bbase (se 4 (by rfl) ⟨255510, by rfl⟩ : syracuseStep 2725445 = 511021) (by norm_num)
theorem B4085333 : Blo 1815609 4085333 := bbase (se 8 (by rfl) ⟨23937, by rfl⟩ : syracuseStep 4085333 = 47875) (by norm_num)
theorem B2725469 : Blo 1815609 2725469 := bbase (se 3 (by rfl) ⟨511025, by rfl⟩ : syracuseStep 2725469 = 1022051) (by norm_num)
theorem B2725493 : Blo 1815609 2725493 := bbase (se 5 (by rfl) ⟨127757, by rfl⟩ : syracuseStep 2725493 = 255515) (by norm_num)
theorem B2299529 : Blo 1815609 2299529 := bbase (se 2 (by rfl) ⟨862323, by rfl⟩ : syracuseStep 2299529 = 1724647) (by norm_num)
theorem B2725517 : Blo 1815609 2725517 := bbase (se 3 (by rfl) ⟨511034, by rfl⟩ : syracuseStep 2725517 = 1022069) (by norm_num)
theorem B4085405 : Blo 1815609 4085405 := bbase (se 3 (by rfl) ⟨766013, by rfl⟩ : syracuseStep 4085405 = 1532027) (by norm_num)
theorem B2725541 : Blo 1815609 2725541 := bbase (se 4 (by rfl) ⟨255519, by rfl⟩ : syracuseStep 2725541 = 511039) (by norm_num)
theorem B2455213 : Blo 1815609 2455213 := bbase (se 3 (by rfl) ⟨460352, by rfl⟩ : syracuseStep 2455213 = 920705) (by norm_num)
theorem B2725565 : Blo 1815609 2725565 := bbase (se 3 (by rfl) ⟨511043, by rfl⟩ : syracuseStep 2725565 = 1022087) (by norm_num)
theorem B2299585 : Blo 1815609 2299585 := bbase (se 2 (by rfl) ⟨862344, by rfl⟩ : syracuseStep 2299585 = 1724689) (by norm_num)
theorem B2725589 : Blo 1815609 2725589 := bbase (se 7 (by rfl) ⟨31940, by rfl⟩ : syracuseStep 2725589 = 63881) (by norm_num)
theorem B4085477 : Blo 1815609 4085477 := bbase (se 4 (by rfl) ⟨383013, by rfl⟩ : syracuseStep 4085477 = 766027) (by norm_num)
theorem B2725613 : Blo 1815609 2725613 := bbase (se 3 (by rfl) ⟨511052, by rfl⟩ : syracuseStep 2725613 = 1022105) (by norm_num)
theorem B2725637 : Blo 1815609 2725637 := bbase (se 4 (by rfl) ⟨255528, by rfl⟩ : syracuseStep 2725637 = 511057) (by norm_num)
theorem B2725661 : Blo 1815609 2725661 := bbase (se 3 (by rfl) ⟨511061, by rfl⟩ : syracuseStep 2725661 = 1022123) (by norm_num)
theorem B2299681 : Blo 1815609 2299681 := bbase (se 2 (by rfl) ⟨862380, by rfl⟩ : syracuseStep 2299681 = 1724761) (by norm_num)
theorem B4085549 : Blo 1815609 4085549 := bbase (se 3 (by rfl) ⟨766040, by rfl⟩ : syracuseStep 4085549 = 1532081) (by norm_num)
theorem B16570165 : Blo 1815609 16570165 := bbase (se 5 (by rfl) ⟨776726, by rfl⟩ : syracuseStep 16570165 = 1553453) (by norm_num)
theorem B2725685 : Blo 1815609 2725685 := bbase (se 5 (by rfl) ⟨127766, by rfl⟩ : syracuseStep 2725685 = 255533) (by norm_num)
theorem B3880781 : Blo 1815609 3880781 := bbase (se 3 (by rfl) ⟨727646, by rfl⟩ : syracuseStep 3880781 = 1455293) (by norm_num)
theorem B2725709 : Blo 1815609 2725709 := bbase (se 3 (by rfl) ⟨511070, by rfl⟩ : syracuseStep 2725709 = 1022141) (by norm_num)
theorem B6133589 : Blo 1815609 6133589 := bbase (se 9 (by rfl) ⟨17969, by rfl⟩ : syracuseStep 6133589 = 35939) (by norm_num)
theorem B1939297 : Blo 1815609 1939297 := bbase (se 2 (by rfl) ⟨727236, by rfl⟩ : syracuseStep 1939297 = 1454473) (by norm_num)
theorem B2725733 : Blo 1815609 2725733 := bbase (se 4 (by rfl) ⟨255537, by rfl⟩ : syracuseStep 2725733 = 511075) (by norm_num)
theorem B4085621 : Blo 1815609 4085621 := bbase (se 5 (by rfl) ⟨191513, by rfl⟩ : syracuseStep 4085621 = 383027) (by norm_num)
theorem B2725757 : Blo 1815609 2725757 := bbase (se 3 (by rfl) ⟨511079, by rfl⟩ : syracuseStep 2725757 = 1022159) (by norm_num)
theorem B2455429 : Blo 1815609 2455429 := bbase (se 4 (by rfl) ⟨230196, by rfl⟩ : syracuseStep 2455429 = 460393) (by norm_num)
theorem B2725781 : Blo 1815609 2725781 := bbase (se 6 (by rfl) ⟨63885, by rfl⟩ : syracuseStep 2725781 = 127771) (by norm_num)
theorem B8288165 : Blo 1815609 8288165 := bbase (se 4 (by rfl) ⟨777015, by rfl⟩ : syracuseStep 8288165 = 1554031) (by norm_num)
theorem B2725805 : Blo 1815609 2725805 := bbase (se 3 (by rfl) ⟨511088, by rfl⟩ : syracuseStep 2725805 = 1022177) (by norm_num)
theorem B1841077 : Blo 1815609 1841077 := bbase (se 5 (by rfl) ⟨86300, by rfl⟩ : syracuseStep 1841077 = 172601) (by norm_num)
theorem B4085693 : Blo 1815609 4085693 := bbase (se 3 (by rfl) ⟨766067, by rfl⟩ : syracuseStep 4085693 = 1532135) (by norm_num)
theorem B2455493 : Blo 1815609 2455493 := bbase (se 4 (by rfl) ⟨230202, by rfl⟩ : syracuseStep 2455493 = 460405) (by norm_num)
theorem B2725829 : Blo 1815609 2725829 := bbase (se 4 (by rfl) ⟨255546, by rfl⟩ : syracuseStep 2725829 = 511093) (by norm_num)
theorem B2299853 : Blo 1815609 2299853 := bbase (se 3 (by rfl) ⟨431222, by rfl⟩ : syracuseStep 2299853 = 862445) (by norm_num)
theorem B1939421 : Blo 1815609 1939421 := bbase (se 3 (by rfl) ⟨363641, by rfl⟩ : syracuseStep 1939421 = 727283) (by norm_num)
theorem B2725853 : Blo 1815609 2725853 := bbase (se 3 (by rfl) ⟨511097, by rfl⟩ : syracuseStep 2725853 = 1022195) (by norm_num)
theorem B2725877 : Blo 1815609 2725877 := bbase (se 5 (by rfl) ⟨127775, by rfl⟩ : syracuseStep 2725877 = 255551) (by norm_num)
theorem B4085765 : Blo 1815609 4085765 := bbase (se 4 (by rfl) ⟨383040, by rfl⟩ : syracuseStep 4085765 = 766081) (by norm_num)
theorem B2299909 : Blo 1815609 2299909 := bbase (se 4 (by rfl) ⟨215616, by rfl⟩ : syracuseStep 2299909 = 431233) (by norm_num)
theorem B2725901 : Blo 1815609 2725901 := bbase (se 3 (by rfl) ⟨511106, by rfl⟩ : syracuseStep 2725901 = 1022213) (by norm_num)
theorem B2725925 : Blo 1815609 2725925 := bbase (se 4 (by rfl) ⟨255555, by rfl⟩ : syracuseStep 2725925 = 511111) (by norm_num)
theorem B2725949 : Blo 1815609 2725949 := bbase (se 3 (by rfl) ⟨511115, by rfl⟩ : syracuseStep 2725949 = 1022231) (by norm_num)
theorem B3881029 : Blo 1815609 3881029 := bbase (se 4 (by rfl) ⟨363846, by rfl⟩ : syracuseStep 3881029 = 727693) (by norm_num)
theorem B6993989 : Blo 1815609 6993989 := bbase (se 4 (by rfl) ⟨655686, by rfl⟩ : syracuseStep 6993989 = 1311373) (by norm_num)
theorem B4085837 : Blo 1815609 4085837 := bbase (se 3 (by rfl) ⟨766094, by rfl⟩ : syracuseStep 4085837 = 1532189) (by norm_num)
theorem B2725973 : Blo 1815609 2725973 := bbase (se 8 (by rfl) ⟨15972, by rfl⟩ : syracuseStep 2725973 = 31945) (by norm_num)
theorem B5240933 : Blo 1815609 5240933 := bbase (se 4 (by rfl) ⟨491337, by rfl⟩ : syracuseStep 5240933 = 982675) (by norm_num)
theorem B2300005 : Blo 1815609 2300005 := bbase (se 4 (by rfl) ⟨215625, by rfl⟩ : syracuseStep 2300005 = 431251) (by norm_num)
theorem B2725997 : Blo 1815609 2725997 := bbase (se 3 (by rfl) ⟨511124, by rfl⟩ : syracuseStep 2725997 = 1022249) (by norm_num)
theorem B2726021 : Blo 1815609 2726021 := bbase (se 4 (by rfl) ⟨255564, by rfl⟩ : syracuseStep 2726021 = 511129) (by norm_num)
theorem B4085909 : Blo 1815609 4085909 := bbase (se 6 (by rfl) ⟨95763, by rfl⟩ : syracuseStep 4085909 = 191527) (by norm_num)
theorem B2726045 : Blo 1815609 2726045 := bbase (se 3 (by rfl) ⟨511133, by rfl⟩ : syracuseStep 2726045 = 1022267) (by norm_num)
theorem B1841329 : Blo 1815609 1841329 := bbase (se 2 (by rfl) ⟨690498, by rfl⟩ : syracuseStep 1841329 = 1380997) (by norm_num)
theorem B2726069 : Blo 1815609 2726069 := bbase (se 5 (by rfl) ⟨127784, by rfl⟩ : syracuseStep 2726069 = 255569) (by norm_num)
theorem B2726093 : Blo 1815609 2726093 := bbase (se 3 (by rfl) ⟨511142, by rfl⟩ : syracuseStep 2726093 = 1022285) (by norm_num)
theorem B4143317 : Blo 1815609 4143317 := bbase (se 7 (by rfl) ⟨48554, by rfl⟩ : syracuseStep 4143317 = 97109) (by norm_num)
theorem B1939673 : Blo 1815609 1939673 := bbase (se 2 (by rfl) ⟨727377, by rfl⟩ : syracuseStep 1939673 = 1454755) (by norm_num)
theorem B4085981 : Blo 1815609 4085981 := bbase (se 3 (by rfl) ⟨766121, by rfl⟩ : syracuseStep 4085981 = 1532243) (by norm_num)
theorem B2726117 : Blo 1815609 2726117 := bbase (se 4 (by rfl) ⟨255573, by rfl⟩ : syracuseStep 2726117 = 511147) (by norm_num)
theorem B2726141 : Blo 1815609 2726141 := bbase (se 3 (by rfl) ⟨511151, by rfl⟩ : syracuseStep 2726141 = 1022303) (by norm_num)
theorem B6134021 : Blo 1815609 6134021 := bbase (se 4 (by rfl) ⟨575064, by rfl⟩ : syracuseStep 6134021 = 1150129) (by norm_num)
theorem B2300177 : Blo 1815609 2300177 := bbase (se 2 (by rfl) ⟨862566, by rfl⟩ : syracuseStep 2300177 = 1725133) (by norm_num)
theorem B3275029 : Blo 1815609 3275029 := bbase (se 6 (by rfl) ⟨76758, by rfl⟩ : syracuseStep 3275029 = 153517) (by norm_num)
theorem B2726165 : Blo 1815609 2726165 := bbase (se 6 (by rfl) ⟨63894, by rfl⟩ : syracuseStep 2726165 = 127789) (by norm_num)
theorem B4086053 : Blo 1815609 4086053 := bbase (se 4 (by rfl) ⟨383067, by rfl⟩ : syracuseStep 4086053 = 766135) (by norm_num)
theorem B2586925 : Blo 1815609 2586925 := bbase (se 3 (by rfl) ⟨485048, by rfl⟩ : syracuseStep 2586925 = 970097) (by norm_num)
theorem B2726189 : Blo 1815609 2726189 := bbase (se 3 (by rfl) ⟨511160, by rfl⟩ : syracuseStep 2726189 = 1022321) (by norm_num)
theorem B8730949 : Blo 1815609 8730949 := bbase (se 4 (by rfl) ⟨818526, by rfl⟩ : syracuseStep 8730949 = 1637053) (by norm_num)
theorem B2726213 : Blo 1815609 2726213 := bbase (se 4 (by rfl) ⟨255582, by rfl⟩ : syracuseStep 2726213 = 511165) (by norm_num)
theorem B2300233 : Blo 1815609 2300233 := bbase (se 2 (by rfl) ⟨862587, by rfl⟩ : syracuseStep 2300233 = 1725175) (by norm_num)
theorem B3275101 : Blo 1815609 3275101 := bbase (se 3 (by rfl) ⟨614081, by rfl⟩ : syracuseStep 3275101 = 1228163) (by norm_num)
theorem B2726237 : Blo 1815609 2726237 := bbase (se 3 (by rfl) ⟨511169, by rfl⟩ : syracuseStep 2726237 = 1022339) (by norm_num)
theorem B2070893 : Blo 1815609 2070893 := bbase (se 3 (by rfl) ⟨388292, by rfl⟩ : syracuseStep 2070893 = 776585) (by norm_num)
theorem B4086125 : Blo 1815609 4086125 := bbase (se 3 (by rfl) ⟨766148, by rfl⟩ : syracuseStep 4086125 = 1532297) (by norm_num)
theorem B2726261 : Blo 1815609 2726261 := bbase (se 5 (by rfl) ⟨127793, by rfl⟩ : syracuseStep 2726261 = 255587) (by norm_num)
theorem B5822837 : Blo 1815609 5822837 := bbase (se 5 (by rfl) ⟨272945, by rfl⟩ : syracuseStep 5822837 = 545891) (by norm_num)
theorem B2726285 : Blo 1815609 2726285 := bbase (se 3 (by rfl) ⟨511178, by rfl⟩ : syracuseStep 2726285 = 1022357) (by norm_num)
theorem B7756181 : Blo 1815609 7756181 := bbase (se 6 (by rfl) ⟨181785, by rfl⟩ : syracuseStep 7756181 = 363571) (by norm_num)
theorem B2726309 : Blo 1815609 2726309 := bbase (se 4 (by rfl) ⟨255591, by rfl⟩ : syracuseStep 2726309 = 511183) (by norm_num)
theorem B2300329 : Blo 1815609 2300329 := bbase (se 2 (by rfl) ⟨862623, by rfl⟩ : syracuseStep 2300329 = 1725247) (by norm_num)
theorem B4086197 : Blo 1815609 4086197 := bbase (se 5 (by rfl) ⟨191540, by rfl⟩ : syracuseStep 4086197 = 383081) (by norm_num)
theorem B2726333 : Blo 1815609 2726333 := bbase (se 3 (by rfl) ⟨511187, by rfl⟩ : syracuseStep 2726333 = 1022375) (by norm_num)
theorem B6543829 : Blo 1815609 6543829 := bbase (se 7 (by rfl) ⟨76685, by rfl⟩ : syracuseStep 6543829 = 153371) (by norm_num)
theorem B2726357 : Blo 1815609 2726357 := bbase (se 7 (by rfl) ⟨31949, by rfl⟩ : syracuseStep 2726357 = 63899) (by norm_num)
theorem B2726381 : Blo 1815609 2726381 := bbase (se 3 (by rfl) ⟨511196, by rfl⟩ : syracuseStep 2726381 = 1022393) (by norm_num)
theorem B4086269 : Blo 1815609 4086269 := bbase (se 3 (by rfl) ⟨766175, by rfl⟩ : syracuseStep 4086269 = 1532351) (by norm_num)
theorem B2726405 : Blo 1815609 2726405 := bbase (se 4 (by rfl) ⟨255600, by rfl⟩ : syracuseStep 2726405 = 511201) (by norm_num)
theorem B3881533 : Blo 1815609 3881533 := bbase (se 3 (by rfl) ⟨727787, by rfl⟩ : syracuseStep 3881533 = 1455575) (by norm_num)
theorem B4086341 : Blo 1815609 4086341 := bbase (se 4 (by rfl) ⟨383094, by rfl⟩ : syracuseStep 4086341 = 766189) (by norm_num)
theorem B3447373 : Blo 1815609 3447373 := bbase (se 3 (by rfl) ⟨646382, by rfl⟩ : syracuseStep 3447373 = 1292765) (by norm_num)
theorem B78608981 : Blo 1815609 78608981 := bbase (se 8 (by rfl) ⟨460599, by rfl⟩ : syracuseStep 78608981 = 921199) (by norm_num)
theorem B8968805 : Blo 1815609 8968805 := bbase (se 4 (by rfl) ⟨840825, by rfl⟩ : syracuseStep 8968805 = 1681651) (by norm_num)
theorem B9198197 : Blo 1815609 9198197 := bbase (se 5 (by rfl) ⟨431165, by rfl⟩ : syracuseStep 9198197 = 862331) (by norm_num)
theorem B4086413 : Blo 1815609 4086413 := bbase (se 3 (by rfl) ⟨766202, by rfl⟩ : syracuseStep 4086413 = 1532405) (by norm_num)
theorem B2488973 : Blo 1815609 2488973 := bbase (se 3 (by rfl) ⟨466682, by rfl⟩ : syracuseStep 2488973 = 933365) (by norm_num)
theorem B1940117 : Blo 1815609 1940117 := bbase (se 6 (by rfl) ⟨45471, by rfl⟩ : syracuseStep 1940117 = 90943) (by norm_num)
theorem B7363237 : Blo 1815609 7363237 := bbase (se 4 (by rfl) ⟨690303, by rfl⟩ : syracuseStep 7363237 = 1380607) (by norm_num)
theorem B7756469 : Blo 1815609 7756469 := bbase (se 5 (by rfl) ⟨363584, by rfl⟩ : syracuseStep 7756469 = 727169) (by norm_num)
theorem B4086485 : Blo 1815609 4086485 := bbase (se 7 (by rfl) ⟨47888, by rfl⟩ : syracuseStep 4086485 = 95777) (by norm_num)
theorem B4365013 : Blo 1815609 4365013 := bbase (se 7 (by rfl) ⟨51152, by rfl⟩ : syracuseStep 4365013 = 102305) (by norm_num)
theorem B3447517 : Blo 1815609 3447517 := bbase (se 3 (by rfl) ⟨646409, by rfl⟩ : syracuseStep 3447517 = 1292819) (by norm_num)
theorem B4086557 : Blo 1815609 4086557 := bbase (se 3 (by rfl) ⟨766229, by rfl⟩ : syracuseStep 4086557 = 1532459) (by norm_num)
theorem B4086629 : Blo 1815609 4086629 := bbase (se 4 (by rfl) ⟨383121, by rfl⟩ : syracuseStep 4086629 = 766243) (by norm_num)
theorem B3447677 : Blo 1815609 3447677 := bbase (se 3 (by rfl) ⟨646439, by rfl⟩ : syracuseStep 3447677 = 1292879) (by norm_num)
theorem B1940365 : Blo 1815609 1940365 := bbase (se 3 (by rfl) ⟨363818, by rfl⟩ : syracuseStep 1940365 = 727637) (by norm_num)
theorem B4086701 : Blo 1815609 4086701 := bbase (se 3 (by rfl) ⟨766256, by rfl⟩ : syracuseStep 4086701 = 1532513) (by norm_num)
theorem B4365245 : Blo 1815609 4365245 := bbase (se 3 (by rfl) ⟨818483, by rfl⟩ : syracuseStep 4365245 = 1636967) (by norm_num)
theorem B4086773 : Blo 1815609 4086773 := bbase (se 5 (by rfl) ⟨191567, by rfl⟩ : syracuseStep 4086773 = 383135) (by norm_num)
theorem B3447821 : Blo 1815609 3447821 := bbase (se 3 (by rfl) ⟨646466, by rfl⟩ : syracuseStep 3447821 = 1292933) (by norm_num)
theorem B4086845 : Blo 1815609 4086845 := bbase (se 3 (by rfl) ⟨766283, by rfl⟩ : syracuseStep 4086845 = 1532567) (by norm_num)
theorem B2587717 : Blo 1815609 2587717 := bbase (se 4 (by rfl) ⟨242598, by rfl⟩ : syracuseStep 2587717 = 485197) (by norm_num)
theorem B4365389 : Blo 1815609 4365389 := bbase (se 3 (by rfl) ⟨818510, by rfl⟩ : syracuseStep 4365389 = 1637021) (by norm_num)
theorem B4086917 : Blo 1815609 4086917 := bbase (se 4 (by rfl) ⟨383148, by rfl⟩ : syracuseStep 4086917 = 766297) (by norm_num)
theorem B4086989 : Blo 1815609 4086989 := bbase (se 3 (by rfl) ⟨766310, by rfl⟩ : syracuseStep 4086989 = 1532621) (by norm_num)
theorem B4087061 : Blo 1815609 4087061 := bbase (se 6 (by rfl) ⟨95790, by rfl⟩ : syracuseStep 4087061 = 191581) (by norm_num)
theorem B6896933 : Blo 1815609 6896933 := bbase (se 4 (by rfl) ⟨646587, by rfl⟩ : syracuseStep 6896933 = 1293175) (by norm_num)
theorem B3448109 : Blo 1815609 3448109 := bbase (se 3 (by rfl) ⟨646520, by rfl⟩ : syracuseStep 3448109 = 1293041) (by norm_num)
theorem B4365629 : Blo 1815609 4365629 := bbase (se 3 (by rfl) ⟨818555, by rfl⟩ : syracuseStep 4365629 = 1637111) (by norm_num)
theorem B1940809 : Blo 1815609 1940809 := bbase (se 2 (by rfl) ⟨727803, by rfl⟩ : syracuseStep 1940809 = 1455607) (by norm_num)
theorem B14736725 : Blo 1815609 14736725 := bbase (se 11 (by rfl) ⟨10793, by rfl⟩ : syracuseStep 14736725 = 21587) (by norm_num)
theorem B4087133 : Blo 1815609 4087133 := bbase (se 3 (by rfl) ⟨766337, by rfl⟩ : syracuseStep 4087133 = 1532675) (by norm_num)
theorem B1940869 : Blo 1815609 1940869 := bbase (se 4 (by rfl) ⟨181956, by rfl⟩ : syracuseStep 1940869 = 363913) (by norm_num)
theorem B10345877 : Blo 1815609 10345877 := bbase (se 6 (by rfl) ⟨242481, by rfl⟩ : syracuseStep 10345877 = 484963) (by norm_num)
theorem B7757221 : Blo 1815609 7757221 := bbase (se 4 (by rfl) ⟨727239, by rfl⟩ : syracuseStep 7757221 = 1454479) (by norm_num)
theorem B4087205 : Blo 1815609 4087205 := bbase (se 4 (by rfl) ⟨383175, by rfl⟩ : syracuseStep 4087205 = 766351) (by norm_num)
theorem B3448261 : Blo 1815609 3448261 := bbase (se 4 (by rfl) ⟨323274, by rfl⟩ : syracuseStep 3448261 = 646549) (by norm_num)
theorem B4144613 : Blo 1815609 4144613 := bbase (se 4 (by rfl) ⟨388557, by rfl⟩ : syracuseStep 4144613 = 777115) (by norm_num)
theorem B4087277 : Blo 1815609 4087277 := bbase (se 3 (by rfl) ⟨766364, by rfl⟩ : syracuseStep 4087277 = 1532729) (by norm_num)
theorem B14736917 : Blo 1815609 14736917 := bbase (se 6 (by rfl) ⟨345396, by rfl⟩ : syracuseStep 14736917 = 690793) (by norm_num)
theorem B4087349 : Blo 1815609 4087349 := bbase (se 5 (by rfl) ⟨191594, by rfl⟩ : syracuseStep 4087349 = 383189) (by norm_num)
theorem B6897221 : Blo 1815609 6897221 := bbase (se 4 (by rfl) ⟨646614, by rfl⟩ : syracuseStep 6897221 = 1293229) (by norm_num)
theorem B4087421 : Blo 1815609 4087421 := bbase (se 3 (by rfl) ⟨766391, by rfl⟩ : syracuseStep 4087421 = 1532783) (by norm_num)
theorem B4087493 : Blo 1815609 4087493 := bbase (se 4 (by rfl) ⟨383202, by rfl⟩ : syracuseStep 4087493 = 766405) (by norm_num)
theorem B3448565 : Blo 1815609 3448565 := bbase (se 5 (by rfl) ⟨161651, by rfl⟩ : syracuseStep 3448565 = 323303) (by norm_num)
theorem B3931909 : Blo 1815609 3931909 := bbase (se 4 (by rfl) ⟨368616, by rfl⟩ : syracuseStep 3931909 = 737233) (by norm_num)
theorem B4087565 : Blo 1815609 4087565 := bbase (se 3 (by rfl) ⟨766418, by rfl⟩ : syracuseStep 4087565 = 1532837) (by norm_num)
theorem B4087637 : Blo 1815609 4087637 := bbase (se 9 (by rfl) ⟨11975, by rfl⟩ : syracuseStep 4087637 = 23951) (by norm_num)
theorem B9199493 : Blo 1815609 9199493 := bbase (se 4 (by rfl) ⟨862452, by rfl⟩ : syracuseStep 9199493 = 1724905) (by norm_num)
theorem B4087709 : Blo 1815609 4087709 := bbase (se 3 (by rfl) ⟨766445, by rfl⟩ : syracuseStep 4087709 = 1532891) (by norm_num)
theorem B4087781 : Blo 1815609 4087781 := bbase (se 4 (by rfl) ⟨383229, by rfl⟩ : syracuseStep 4087781 = 766459) (by norm_num)
theorem B4087889 : Blo 1815609 4087889 := bstep (se 2 (by rfl) ⟨1532958, by rfl⟩ : syracuseStep 4087889 = 3065917) B3065917
theorem B4087907 : Blo 1815609 4087907 := bstep (se 1 (by rfl) ⟨3065930, by rfl⟩ : syracuseStep 4087907 = 6131861) B6131861
theorem B6127757 : Blo 1815609 6127757 := bstep (se 3 (by rfl) ⟨1148954, by rfl⟩ : syracuseStep 6127757 = 2297909) B2297909
theorem B3063953 : Blo 1815609 3063953 := bstep (se 2 (by rfl) ⟨1148982, by rfl⟩ : syracuseStep 3063953 = 2297965) B2297965
theorem B5521553 : Blo 1815609 5521553 := bstep (se 2 (by rfl) ⟨2070582, by rfl⟩ : syracuseStep 5521553 = 4141165) B4141165
theorem B6127811 : Blo 1815609 6127811 := bstep (se 1 (by rfl) ⟨4595858, by rfl⟩ : syracuseStep 6127811 = 9191717) B9191717
theorem B13787333 : Blo 1815609 13787333 := bstep (se 4 (by rfl) ⟨1292562, by rfl⟩ : syracuseStep 13787333 = 2585125) B2585125
theorem B6897905 : Blo 1815609 6897905 := bstep (se 2 (by rfl) ⟨2586714, by rfl⟩ : syracuseStep 6897905 = 5173429) B5173429
theorem B2908433 : Blo 1815609 2908433 := bstep (se 2 (by rfl) ⟨1090662, by rfl⟩ : syracuseStep 2908433 = 2181325) B2181325
theorem B3064081 : Blo 1815609 3064081 := bstep (se 2 (by rfl) ⟨1149030, by rfl⟩ : syracuseStep 3064081 = 2298061) B2298061
theorem B5898545 : Blo 1815609 5898545 := bstep (se 2 (by rfl) ⟨2211954, by rfl⟩ : syracuseStep 5898545 = 4423909) B4423909
theorem B3064115 : Blo 1815609 3064115 := bstep (se 1 (by rfl) ⟨2298086, by rfl⟩ : syracuseStep 3064115 = 4596173) B4596173
theorem B7758179 : Blo 1815609 7758179 := bstep (se 1 (by rfl) ⟨5818634, by rfl⟩ : syracuseStep 7758179 = 11637269) B11637269
theorem B4088177 : Blo 1815609 4088177 := bstep (se 2 (by rfl) ⟨1533066, by rfl⟩ : syracuseStep 4088177 = 3066133) B3066133
theorem B4366705 : Blo 1815609 4366705 := bstep (se 2 (by rfl) ⟨1637514, by rfl⟩ : syracuseStep 4366705 = 3275029) B3275029
theorem B4088195 : Blo 1815609 4088195 := bstep (se 1 (by rfl) ⟨3066146, by rfl⟩ : syracuseStep 4088195 = 6132293) B6132293
theorem B3449233 : Blo 1815609 3449233 := bstep (se 2 (by rfl) ⟨1293462, by rfl⟩ : syracuseStep 3449233 = 2586925) B2586925
theorem B11641265 : Blo 1815609 11641265 := bstep (se 2 (by rfl) ⟨4365474, by rfl⟩ : syracuseStep 11641265 = 8730949) B8730949
theorem B3064243 : Blo 1815609 3064243 := bstep (se 1 (by rfl) ⟨2298182, by rfl⟩ : syracuseStep 3064243 = 4596365) B4596365
theorem B6128081 : Blo 1815609 6128081 := bstep (se 2 (by rfl) ⟨2298030, by rfl⟩ : syracuseStep 6128081 = 4596061) B4596061
theorem B4366801 : Blo 1815609 4366801 := bstep (se 2 (by rfl) ⟨1637550, by rfl⟩ : syracuseStep 4366801 = 3275101) B3275101
theorem B9200141 : Blo 1815609 9200141 := bstep (se 3 (by rfl) ⟨1725026, by rfl⟩ : syracuseStep 9200141 = 3450053) B3450053
theorem B3064385 : Blo 1815609 3064385 := bstep (se 2 (by rfl) ⟨1149144, by rfl⟩ : syracuseStep 3064385 = 2298289) B2298289
theorem B8725105 : Blo 1815609 8725105 := bstep (se 2 (by rfl) ⟨3271914, by rfl⟩ : syracuseStep 8725105 = 6543829) B6543829
theorem B51069553 : Blo 1815609 51069553 := bstep (se 2 (by rfl) ⟨19151082, by rfl⟩ : syracuseStep 51069553 = 38302165) B38302165
theorem B22094477 : Blo 1815609 22094477 := bstep (se 3 (by rfl) ⟨4142714, by rfl⟩ : syracuseStep 22094477 = 8285429) B8285429
theorem B4088465 : Blo 1815609 4088465 := bstep (se 2 (by rfl) ⟨1533174, by rfl⟩ : syracuseStep 4088465 = 3066349) B3066349
theorem B4088483 : Blo 1815609 4088483 := bstep (se 1 (by rfl) ⟨3066362, by rfl⟩ : syracuseStep 4088483 = 6132725) B6132725
theorem B3064513 : Blo 1815609 3064513 := bstep (se 2 (by rfl) ⟨1149192, by rfl⟩ : syracuseStep 3064513 = 2298385) B2298385
theorem B3064547 : Blo 1815609 3064547 := bstep (se 1 (by rfl) ⟨2298410, by rfl⟩ : syracuseStep 3064547 = 4596821) B4596821
theorem B13796081 : Blo 1815609 13796081 := bstep (se 2 (by rfl) ⟨5173530, by rfl⟩ : syracuseStep 13796081 = 10347061) B10347061
theorem B4596497 : Blo 1815609 4596497 := bstep (se 2 (by rfl) ⟨1723686, by rfl⟩ : syracuseStep 4596497 = 3447373) B3447373
theorem B4596547 : Blo 1815609 4596547 := bstep (se 1 (by rfl) ⟨3447410, by rfl⟩ : syracuseStep 4596547 = 6894821) B6894821
theorem B2761555 : Blo 1815609 2761555 := bstep (se 1 (by rfl) ⟨2071166, by rfl⟩ : syracuseStep 2761555 = 4142333) B4142333
theorem B3064675 : Blo 1815609 3064675 := bstep (se 1 (by rfl) ⟨2298506, by rfl⟩ : syracuseStep 3064675 = 4597013) B4597013
theorem B22397795 : Blo 1815609 22397795 := bstep (se 1 (by rfl) ⟨16798346, by rfl⟩ : syracuseStep 22397795 = 33596693) B33596693
theorem B4088753 : Blo 1815609 4088753 := bstep (se 2 (by rfl) ⟨1533282, by rfl⟩ : syracuseStep 4088753 = 3066565) B3066565
theorem B2761651 : Blo 1815609 2761651 := bstep (se 1 (by rfl) ⟨2071238, by rfl⟩ : syracuseStep 2761651 = 4142477) B4142477
theorem B4088771 : Blo 1815609 4088771 := bstep (se 1 (by rfl) ⟨3066578, by rfl⟩ : syracuseStep 4088771 = 6133157) B6133157
theorem B5522381 : Blo 1815609 5522381 := bstep (se 3 (by rfl) ⟨1035446, by rfl⟩ : syracuseStep 5522381 = 2070893) B2070893
theorem B4596689 : Blo 1815609 4596689 := bstep (se 2 (by rfl) ⟨1723758, by rfl⟩ : syracuseStep 4596689 = 3447517) B3447517
theorem B6128621 : Blo 1815609 6128621 := bstep (se 3 (by rfl) ⟨1149116, by rfl⟩ : syracuseStep 6128621 = 2298233) B2298233
theorem B3064817 : Blo 1815609 3064817 := bstep (se 2 (by rfl) ⟨1149306, by rfl⟩ : syracuseStep 3064817 = 2298613) B2298613
theorem B5817379 : Blo 1815609 5817379 := bstep (se 1 (by rfl) ⟨4363034, by rfl⟩ : syracuseStep 5817379 = 8726069) B8726069
theorem B6128675 : Blo 1815609 6128675 := bstep (se 1 (by rfl) ⟨4596506, by rfl⟩ : syracuseStep 6128675 = 9193013) B9193013
theorem B1967203 : Blo 1815609 1967203 := bstep (se 1 (by rfl) ⟨1475402, by rfl⟩ : syracuseStep 1967203 = 2950805) B2950805
theorem B3064945 : Blo 1815609 3064945 := bstep (se 2 (by rfl) ⟨1149354, by rfl⟩ : syracuseStep 3064945 = 2298709) B2298709
theorem B3064979 : Blo 1815609 3064979 := bstep (se 1 (by rfl) ⟨2298734, by rfl⟩ : syracuseStep 3064979 = 4597469) B4597469
theorem B4089041 : Blo 1815609 4089041 := bstep (se 2 (by rfl) ⟨1533390, by rfl⟩ : syracuseStep 4089041 = 3066781) B3066781
theorem B4089059 : Blo 1815609 4089059 := bstep (se 1 (by rfl) ⟨3066794, by rfl⟩ : syracuseStep 4089059 = 6133589) B6133589
theorem B9192689 : Blo 1815609 9192689 := bstep (se 2 (by rfl) ⟨3447258, by rfl⟩ : syracuseStep 9192689 = 6894517) B6894517
theorem B11052301 : Blo 1815609 11052301 := bstep (se 3 (by rfl) ⟨2072306, by rfl⟩ : syracuseStep 11052301 = 4144613) B4144613
theorem B3065107 : Blo 1815609 3065107 := bstep (se 1 (by rfl) ⟨2298830, by rfl⟩ : syracuseStep 3065107 = 4597661) B4597661
theorem B6128945 : Blo 1815609 6128945 := bstep (se 2 (by rfl) ⟨2298354, by rfl⟩ : syracuseStep 6128945 = 4596709) B4596709
theorem B5170513 : Blo 1815609 5170513 := bstep (se 2 (by rfl) ⟨1938942, by rfl⟩ : syracuseStep 5170513 = 3877885) B3877885
theorem B4662659 : Blo 1815609 4662659 := bstep (se 1 (by rfl) ⟨3496994, by rfl⟩ : syracuseStep 4662659 = 6993989) B6993989
theorem B39298445 : Blo 1815609 39298445 := bstep (se 3 (by rfl) ⟨7368458, by rfl⟩ : syracuseStep 39298445 = 14736917) B14736917
theorem B3065249 : Blo 1815609 3065249 := bstep (se 2 (by rfl) ⟨1149468, by rfl⟩ : syracuseStep 3065249 = 2298937) B2298937
theorem B3450289 : Blo 1815609 3450289 := bstep (se 2 (by rfl) ⟨1293858, by rfl⟩ : syracuseStep 3450289 = 2587717) B2587717
theorem B4089329 : Blo 1815609 4089329 := bstep (se 2 (by rfl) ⟨1533498, by rfl⟩ : syracuseStep 4089329 = 3066997) B3066997
theorem B4089347 : Blo 1815609 4089347 := bstep (se 1 (by rfl) ⟨3067010, by rfl⟩ : syracuseStep 4089347 = 6134021) B6134021
theorem B3065377 : Blo 1815609 3065377 := bstep (se 2 (by rfl) ⟨1149516, by rfl⟩ : syracuseStep 3065377 = 2299033) B2299033
theorem B3065411 : Blo 1815609 3065411 := bstep (se 1 (by rfl) ⟨2299058, by rfl⟩ : syracuseStep 3065411 = 4598117) B4598117
theorem B5170787 : Blo 1815609 5170787 := bstep (se 1 (by rfl) ⟨3878090, by rfl⟩ : syracuseStep 5170787 = 7756181) B7756181
theorem B31024781 : Blo 1815609 31024781 := bstep (se 3 (by rfl) ⟨5817146, by rfl⟩ : syracuseStep 31024781 = 11634293) B11634293
theorem B6899363 : Blo 1815609 6899363 := bstep (se 1 (by rfl) ⟨5174522, by rfl⟩ : syracuseStep 6899363 = 10349045) B10349045
theorem B6899377 : Blo 1815609 6899377 := bstep (se 2 (by rfl) ⟨2587266, by rfl⟩ : syracuseStep 6899377 = 5174533) B5174533
theorem B3065539 : Blo 1815609 3065539 := bstep (se 1 (by rfl) ⟨2299154, by rfl⟩ : syracuseStep 3065539 = 4598309) B4598309
theorem B8726221 : Blo 1815609 8726221 := bstep (se 3 (by rfl) ⟨1636166, by rfl⟩ : syracuseStep 8726221 = 3272333) B3272333
theorem B6637261 : Blo 1815609 6637261 := bstep (se 3 (by rfl) ⟨1244486, by rfl⟩ : syracuseStep 6637261 = 2488973) B2488973
theorem B52405987 : Blo 1815609 52405987 := bstep (se 1 (by rfl) ⟨39304490, by rfl⟩ : syracuseStep 52405987 = 78608981) B78608981
theorem B4089617 : Blo 1815609 4089617 := bstep (se 2 (by rfl) ⟨1533606, by rfl⟩ : syracuseStep 4089617 = 3067213) B3067213
theorem B2098963 : Blo 1815609 2098963 := bstep (se 1 (by rfl) ⟨1574222, by rfl⟩ : syracuseStep 2098963 = 3148445) B3148445
theorem B5170979 : Blo 1815609 5170979 := bstep (se 1 (by rfl) ⟨3878234, by rfl⟩ : syracuseStep 5170979 = 7756469) B7756469
theorem B10348337 : Blo 1815609 10348337 := bstep (se 2 (by rfl) ⟨3880626, by rfl⟩ : syracuseStep 10348337 = 7761253) B7761253
theorem B6211405 : Blo 1815609 6211405 := bstep (se 3 (by rfl) ⟨1164638, by rfl⟩ : syracuseStep 6211405 = 2329277) B2329277
theorem B6129485 : Blo 1815609 6129485 := bstep (se 3 (by rfl) ⟨1149278, by rfl⟩ : syracuseStep 6129485 = 2298557) B2298557
theorem B3065681 : Blo 1815609 3065681 := bstep (se 2 (by rfl) ⟨1149630, by rfl⟩ : syracuseStep 3065681 = 2299261) B2299261
theorem B6129539 : Blo 1815609 6129539 := bstep (se 1 (by rfl) ⟨4597154, by rfl⟩ : syracuseStep 6129539 = 9194309) B9194309
theorem B4597681 : Blo 1815609 4597681 := bstep (se 2 (by rfl) ⟨1724130, by rfl⟩ : syracuseStep 4597681 = 3448261) B3448261
theorem B3065809 : Blo 1815609 3065809 := bstep (se 2 (by rfl) ⟨1149678, by rfl⟩ : syracuseStep 3065809 = 2299357) B2299357
theorem B2910163 : Blo 1815609 2910163 := bstep (se 1 (by rfl) ⟨2182622, by rfl⟩ : syracuseStep 2910163 = 4365245) B4365245
theorem B3065843 : Blo 1815609 3065843 := bstep (se 1 (by rfl) ⟨2299382, by rfl⟩ : syracuseStep 3065843 = 4598765) B4598765
theorem B7759921 : Blo 1815609 7759921 := bstep (se 2 (by rfl) ⟨2909970, by rfl⟩ : syracuseStep 7759921 = 5819941) B5819941
theorem B2910259 : Blo 1815609 2910259 := bstep (se 1 (by rfl) ⟨2182694, by rfl⟩ : syracuseStep 2910259 = 4365389) B4365389
theorem B3065971 : Blo 1815609 3065971 := bstep (se 1 (by rfl) ⟨2299478, by rfl⟩ : syracuseStep 3065971 = 4598957) B4598957
theorem B6129809 : Blo 1815609 6129809 := bstep (se 2 (by rfl) ⟨2298678, by rfl⟩ : syracuseStep 6129809 = 4597357) B4597357
theorem B4597955 : Blo 1815609 4597955 := bstep (se 1 (by rfl) ⟨3448466, by rfl⟩ : syracuseStep 4597955 = 6896933) B6896933
theorem B2910419 : Blo 1815609 2910419 := bstep (se 1 (by rfl) ⟨2182814, by rfl⟩ : syracuseStep 2910419 = 4365629) B4365629
theorem B9824483 : Blo 1815609 9824483 := bstep (se 1 (by rfl) ⟨7368362, by rfl⟩ : syracuseStep 9824483 = 14736725) B14736725
theorem B3066113 : Blo 1815609 3066113 := bstep (se 2 (by rfl) ⟨1149792, by rfl⟩ : syracuseStep 3066113 = 2299585) B2299585
theorem B3066241 : Blo 1815609 3066241 := bstep (se 2 (by rfl) ⟨1149840, by rfl⟩ : syracuseStep 3066241 = 2299681) B2299681
theorem B4598147 : Blo 1815609 4598147 := bstep (se 1 (by rfl) ⟨3448610, by rfl⟩ : syracuseStep 4598147 = 6897221) B6897221
theorem B3066275 : Blo 1815609 3066275 := bstep (se 1 (by rfl) ⟨2299706, by rfl⟩ : syracuseStep 3066275 = 4599413) B4599413
theorem B9816589 : Blo 1815609 9816589 := bstep (se 3 (by rfl) ⟨1840610, by rfl⟩ : syracuseStep 9816589 = 3681221) B3681221
theorem B6547981 : Blo 1815609 6547981 := bstep (se 3 (by rfl) ⟨1227746, by rfl⟩ : syracuseStep 6547981 = 2455493) B2455493
theorem B3066403 : Blo 1815609 3066403 := bstep (se 1 (by rfl) ⟨2299802, by rfl⟩ : syracuseStep 3066403 = 4599605) B4599605
theorem B9325091 : Blo 1815609 9325091 := bstep (se 1 (by rfl) ⟨6993818, by rfl⟩ : syracuseStep 9325091 = 13987637) B13987637
theorem B5171789 : Blo 1815609 5171789 := bstep (se 3 (by rfl) ⟨969710, by rfl⟩ : syracuseStep 5171789 = 1939421) B1939421
theorem B9194147 : Blo 1815609 9194147 := bstep (se 1 (by rfl) ⟨6895610, by rfl⟩ : syracuseStep 9194147 = 13791221) B13791221
theorem B6130349 : Blo 1815609 6130349 := bstep (se 3 (by rfl) ⟨1149440, by rfl⟩ : syracuseStep 6130349 = 2298881) B2298881
theorem B3066545 : Blo 1815609 3066545 := bstep (se 2 (by rfl) ⟨1149954, by rfl⟩ : syracuseStep 3066545 = 2299909) B2299909
theorem B2042563 : Blo 1815609 2042563 := bstep (se 1 (by rfl) ⟨1531922, by rfl⟩ : syracuseStep 2042563 = 3063845) B3063845
theorem B15518405 : Blo 1815609 15518405 := bstep (se 4 (by rfl) ⟨1454850, by rfl⟩ : syracuseStep 15518405 = 2909701) B2909701
theorem B6130403 : Blo 1815609 6130403 := bstep (se 1 (by rfl) ⟨4597802, by rfl⟩ : syracuseStep 6130403 = 9195605) B9195605
theorem B3107585 : Blo 1815609 3107585 := bstep (se 2 (by rfl) ⟨1165344, by rfl⟩ : syracuseStep 3107585 = 2330689) B2330689
theorem B5171971 : Blo 1815609 5171971 := bstep (se 1 (by rfl) ⟨3878978, by rfl⟩ : syracuseStep 5171971 = 7757957) B7757957
theorem B3066673 : Blo 1815609 3066673 := bstep (se 2 (by rfl) ⟨1150002, by rfl⟩ : syracuseStep 3066673 = 2300005) B2300005
theorem B11643725 : Blo 1815609 11643725 := bstep (se 3 (by rfl) ⟨2183198, by rfl⟩ : syracuseStep 11643725 = 4366397) B4366397
theorem B2042707 : Blo 1815609 2042707 := bstep (se 1 (by rfl) ⟨1532030, by rfl⟩ : syracuseStep 2042707 = 3064061) B3064061
theorem B3066707 : Blo 1815609 3066707 := bstep (se 1 (by rfl) ⟨2300030, by rfl⟩ : syracuseStep 3066707 = 4600061) B4600061
theorem B3107729 : Blo 1815609 3107729 := bstep (se 2 (by rfl) ⟨1165398, by rfl⟩ : syracuseStep 3107729 = 2330797) B2330797
theorem B12430277 : Blo 1815609 12430277 := bstep (se 4 (by rfl) ⟨1165338, by rfl⟩ : syracuseStep 12430277 = 2330677) B2330677
theorem B3066835 : Blo 1815609 3066835 := bstep (se 1 (by rfl) ⟨2300126, by rfl⟩ : syracuseStep 3066835 = 4600253) B4600253
theorem B2042851 : Blo 1815609 2042851 := bstep (se 1 (by rfl) ⟨1532138, by rfl⟩ : syracuseStep 2042851 = 3064277) B3064277
theorem B47205347 : Blo 1815609 47205347 := bstep (se 1 (by rfl) ⟨35404010, by rfl⟩ : syracuseStep 47205347 = 70808021) B70808021
theorem B6130673 : Blo 1815609 6130673 := bstep (se 2 (by rfl) ⟨2299002, by rfl⟩ : syracuseStep 6130673 = 4598005) B4598005
theorem B6212621 : Blo 1815609 6212621 := bstep (se 3 (by rfl) ⟨1164866, by rfl⟩ : syracuseStep 6212621 = 2329733) B2329733
theorem B3066977 : Blo 1815609 3066977 := bstep (se 2 (by rfl) ⟨1150116, by rfl⟩ : syracuseStep 3066977 = 2300233) B2300233
theorem B6900835 : Blo 1815609 6900835 := bstep (se 1 (by rfl) ⟨5175626, by rfl⟩ : syracuseStep 6900835 = 10351253) B10351253
theorem B2042995 : Blo 1815609 2042995 := bstep (se 1 (by rfl) ⟨1532246, by rfl⟩ : syracuseStep 2042995 = 3064493) B3064493
theorem B2911393 : Blo 1815609 2911393 := bstep (se 2 (by rfl) ⟨1091772, by rfl⟩ : syracuseStep 2911393 = 2183545) B2183545
theorem B5819597 : Blo 1815609 5819597 := bstep (se 3 (by rfl) ⟨1091174, by rfl⟩ : syracuseStep 5819597 = 2182349) B2182349
theorem B3067105 : Blo 1815609 3067105 := bstep (se 2 (by rfl) ⟨1150164, by rfl⟩ : syracuseStep 3067105 = 2300329) B2300329
theorem B10349795 : Blo 1815609 10349795 := bstep (se 1 (by rfl) ⟨7762346, by rfl⟩ : syracuseStep 10349795 = 15524693) B15524693
theorem B5172461 : Blo 1815609 5172461 := bstep (se 3 (by rfl) ⟨969836, by rfl⟩ : syracuseStep 5172461 = 1939673) B1939673
theorem B15527153 : Blo 1815609 15527153 := bstep (se 2 (by rfl) ⟨5822682, by rfl⟩ : syracuseStep 15527153 = 11645365) B11645365
theorem B2182387 : Blo 1815609 2182387 := bstep (se 1 (by rfl) ⟨1636790, by rfl⟩ : syracuseStep 2182387 = 3273581) B3273581
theorem B2043139 : Blo 1815609 2043139 := bstep (se 1 (by rfl) ⟨1532354, by rfl⟩ : syracuseStep 2043139 = 3064709) B3064709
theorem B3067139 : Blo 1815609 3067139 := bstep (se 1 (by rfl) ⟨2300354, by rfl⟩ : syracuseStep 3067139 = 4600709) B4600709
theorem B4599089 : Blo 1815609 4599089 := bstep (se 2 (by rfl) ⟨1724658, by rfl⟩ : syracuseStep 4599089 = 3449317) B3449317
theorem B3108145 : Blo 1815609 3108145 := bstep (se 2 (by rfl) ⟨1165554, by rfl⟩ : syracuseStep 3108145 = 2331109) B2331109
theorem B4599139 : Blo 1815609 4599139 := bstep (se 1 (by rfl) ⟨3449354, by rfl⟩ : syracuseStep 4599139 = 6898709) B6898709
theorem B2043283 : Blo 1815609 2043283 := bstep (se 1 (by rfl) ⟨1532462, by rfl⟩ : syracuseStep 2043283 = 3064925) B3064925
theorem B9194957 : Blo 1815609 9194957 := bstep (se 3 (by rfl) ⟨1724054, by rfl⟩ : syracuseStep 9194957 = 3448109) B3448109
theorem B3878371 : Blo 1815609 3878371 := bstep (se 1 (by rfl) ⟨2908778, by rfl⟩ : syracuseStep 3878371 = 5817557) B5817557
theorem B4599281 : Blo 1815609 4599281 := bstep (se 2 (by rfl) ⟨1724730, by rfl⟩ : syracuseStep 4599281 = 3449461) B3449461
theorem B6131213 : Blo 1815609 6131213 := bstep (se 3 (by rfl) ⟨1149602, by rfl⟩ : syracuseStep 6131213 = 2299205) B2299205
theorem B2043427 : Blo 1815609 2043427 := bstep (se 1 (by rfl) ⟨1532570, by rfl⟩ : syracuseStep 2043427 = 3065141) B3065141
theorem B9817649 : Blo 1815609 9817649 := bstep (se 2 (by rfl) ⟨3681618, by rfl⟩ : syracuseStep 9817649 = 7363237) B7363237
theorem B6131267 : Blo 1815609 6131267 := bstep (se 1 (by rfl) ⟨4598450, by rfl⟩ : syracuseStep 6131267 = 9196901) B9196901
theorem B7179853 : Blo 1815609 7179853 := bstep (se 3 (by rfl) ⟨1346222, by rfl⟩ : syracuseStep 7179853 = 2692445) B2692445
theorem B2723441 : Blo 1815609 2723441 := bstep (se 2 (by rfl) ⟨1021290, by rfl⟩ : syracuseStep 2723441 = 2042581) B2042581
theorem B5820017 : Blo 1815609 5820017 := bstep (se 2 (by rfl) ⟨2182506, by rfl⟩ : syracuseStep 5820017 = 4365013) B4365013
theorem B2723459 : Blo 1815609 2723459 := bstep (se 1 (by rfl) ⟨2042594, by rfl⟩ : syracuseStep 2723459 = 4085189) B4085189
theorem B2723489 : Blo 1815609 2723489 := bstep (se 2 (by rfl) ⟨1021308, by rfl⟩ : syracuseStep 2723489 = 2042617) B2042617
theorem B2723507 : Blo 1815609 2723507 := bstep (se 1 (by rfl) ⟨2042630, by rfl⟩ : syracuseStep 2723507 = 4085261) B4085261
theorem B2043571 : Blo 1815609 2043571 := bstep (se 1 (by rfl) ⟨1532678, by rfl⟩ : syracuseStep 2043571 = 3065357) B3065357
theorem B2723537 : Blo 1815609 2723537 := bstep (se 2 (by rfl) ⟨1021326, by rfl⟩ : syracuseStep 2723537 = 2042653) B2042653
theorem B2723555 : Blo 1815609 2723555 := bstep (se 1 (by rfl) ⟨2042666, by rfl⟩ : syracuseStep 2723555 = 4085333) B4085333
theorem B2723585 : Blo 1815609 2723585 := bstep (se 2 (by rfl) ⟨1021344, by rfl⟩ : syracuseStep 2723585 = 2042689) B2042689
theorem B3108611 : Blo 1815609 3108611 := bstep (se 1 (by rfl) ⟨2331458, by rfl⟩ : syracuseStep 3108611 = 4662917) B4662917
theorem B2723603 : Blo 1815609 2723603 := bstep (se 1 (by rfl) ⟨2042702, by rfl⟩ : syracuseStep 2723603 = 4085405) B4085405
theorem B2723633 : Blo 1815609 2723633 := bstep (se 2 (by rfl) ⟨1021362, by rfl⟩ : syracuseStep 2723633 = 2042725) B2042725
theorem B3878705 : Blo 1815609 3878705 := bstep (se 2 (by rfl) ⟨1454514, by rfl⟩ : syracuseStep 3878705 = 2909029) B2909029
theorem B2723651 : Blo 1815609 2723651 := bstep (se 1 (by rfl) ⟨2042738, by rfl⟩ : syracuseStep 2723651 = 4085477) B4085477
theorem B2043715 : Blo 1815609 2043715 := bstep (se 1 (by rfl) ⟨1532786, by rfl⟩ : syracuseStep 2043715 = 3065573) B3065573
theorem B6131537 : Blo 1815609 6131537 := bstep (se 2 (by rfl) ⟨2299326, by rfl⟩ : syracuseStep 6131537 = 4598653) B4598653
theorem B2723681 : Blo 1815609 2723681 := bstep (se 2 (by rfl) ⟨1021380, by rfl⟩ : syracuseStep 2723681 = 2042761) B2042761
theorem B2723699 : Blo 1815609 2723699 := bstep (se 1 (by rfl) ⟨2042774, by rfl⟩ : syracuseStep 2723699 = 4085549) B4085549
theorem B2723729 : Blo 1815609 2723729 := bstep (se 2 (by rfl) ⟨1021398, by rfl⟩ : syracuseStep 2723729 = 2042797) B2042797
theorem B2723747 : Blo 1815609 2723747 := bstep (se 1 (by rfl) ⟨2042810, by rfl⟩ : syracuseStep 2723747 = 4085621) B4085621
theorem B2723777 : Blo 1815609 2723777 := bstep (se 2 (by rfl) ⟨1021416, by rfl⟩ : syracuseStep 2723777 = 2042833) B2042833
theorem B5525443 : Blo 1815609 5525443 := bstep (se 1 (by rfl) ⟨4144082, by rfl⟩ : syracuseStep 5525443 = 8288165) B8288165
theorem B7761869 : Blo 1815609 7761869 := bstep (se 3 (by rfl) ⟨1455350, by rfl⟩ : syracuseStep 7761869 = 2910701) B2910701
theorem B2723795 : Blo 1815609 2723795 := bstep (se 1 (by rfl) ⟨2042846, by rfl⟩ : syracuseStep 2723795 = 4085693) B4085693
theorem B2043859 : Blo 1815609 2043859 := bstep (se 1 (by rfl) ⟨1532894, by rfl⟩ : syracuseStep 2043859 = 3065789) B3065789
theorem B2723825 : Blo 1815609 2723825 := bstep (se 2 (by rfl) ⟨1021434, by rfl⟩ : syracuseStep 2723825 = 2042869) B2042869
theorem B2723843 : Blo 1815609 2723843 := bstep (se 1 (by rfl) ⟨2042882, by rfl⟩ : syracuseStep 2723843 = 4085765) B4085765
theorem B2723873 : Blo 1815609 2723873 := bstep (se 2 (by rfl) ⟨1021452, by rfl⟩ : syracuseStep 2723873 = 2042905) B2042905
theorem B4141091 : Blo 1815609 4141091 := bstep (se 1 (by rfl) ⟨3105818, by rfl⟩ : syracuseStep 4141091 = 6211637) B6211637
theorem B2723891 : Blo 1815609 2723891 := bstep (se 1 (by rfl) ⟨2042918, by rfl⟩ : syracuseStep 2723891 = 4085837) B4085837
theorem B34910261 : Blo 1815609 34910261 := bstep (se 5 (by rfl) ⟨1636418, by rfl⟩ : syracuseStep 34910261 = 3272837) B3272837
theorem B3493955 : Blo 1815609 3493955 := bstep (se 1 (by rfl) ⟨2620466, by rfl⟩ : syracuseStep 3493955 = 5240933) B5240933
theorem B2723921 : Blo 1815609 2723921 := bstep (se 2 (by rfl) ⟨1021470, by rfl⟩ : syracuseStep 2723921 = 2042941) B2042941
theorem B2723939 : Blo 1815609 2723939 := bstep (se 1 (by rfl) ⟨2042954, by rfl⟩ : syracuseStep 2723939 = 4085909) B4085909
theorem B2044003 : Blo 1815609 2044003 := bstep (se 1 (by rfl) ⟨1533002, by rfl⟩ : syracuseStep 2044003 = 3066005) B3066005
theorem B2723969 : Blo 1815609 2723969 := bstep (se 2 (by rfl) ⟨1021488, by rfl⟩ : syracuseStep 2723969 = 2042977) B2042977
theorem B2723987 : Blo 1815609 2723987 := bstep (se 1 (by rfl) ⟨2042990, by rfl⟩ : syracuseStep 2723987 = 4085981) B4085981
theorem B2724017 : Blo 1815609 2724017 := bstep (se 2 (by rfl) ⟨1021506, by rfl⟩ : syracuseStep 2724017 = 2043013) B2043013
theorem B3109043 : Blo 1815609 3109043 := bstep (se 1 (by rfl) ⟨2331782, by rfl⟩ : syracuseStep 3109043 = 4663565) B4663565
theorem B2724035 : Blo 1815609 2724035 := bstep (se 1 (by rfl) ⟨2043026, by rfl⟩ : syracuseStep 2724035 = 4086053) B4086053
theorem B2724065 : Blo 1815609 2724065 := bstep (se 2 (by rfl) ⟨1021524, by rfl⟩ : syracuseStep 2724065 = 2043049) B2043049
theorem B2724083 : Blo 1815609 2724083 := bstep (se 1 (by rfl) ⟨2043062, by rfl⟩ : syracuseStep 2724083 = 4086125) B4086125
theorem B2044147 : Blo 1815609 2044147 := bstep (se 1 (by rfl) ⟨1533110, by rfl⟩ : syracuseStep 2044147 = 3066221) B3066221
theorem B2724113 : Blo 1815609 2724113 := bstep (se 2 (by rfl) ⟨1021542, by rfl⟩ : syracuseStep 2724113 = 2043085) B2043085
theorem B2724131 : Blo 1815609 2724131 := bstep (se 1 (by rfl) ⟨2043098, by rfl⟩ : syracuseStep 2724131 = 4086197) B4086197
theorem B2724161 : Blo 1815609 2724161 := bstep (se 2 (by rfl) ⟨1021560, by rfl⟩ : syracuseStep 2724161 = 2043121) B2043121
theorem B2724179 : Blo 1815609 2724179 := bstep (se 1 (by rfl) ⟨2043134, by rfl⟩ : syracuseStep 2724179 = 4086269) B4086269
theorem B6132077 : Blo 1815609 6132077 := bstep (se 3 (by rfl) ⟨1149764, by rfl⟩ : syracuseStep 6132077 = 2299529) B2299529
theorem B2724209 : Blo 1815609 2724209 := bstep (se 2 (by rfl) ⟨1021578, by rfl⟩ : syracuseStep 2724209 = 2043157) B2043157
theorem B2724227 : Blo 1815609 2724227 := bstep (se 1 (by rfl) ⟨2043170, by rfl⟩ : syracuseStep 2724227 = 4086341) B4086341
theorem B2044291 : Blo 1815609 2044291 := bstep (se 1 (by rfl) ⟨1533218, by rfl⟩ : syracuseStep 2044291 = 3066437) B3066437
theorem B5173645 : Blo 1815609 5173645 := bstep (se 3 (by rfl) ⟨970058, by rfl⟩ : syracuseStep 5173645 = 1940117) B1940117
theorem B2724257 : Blo 1815609 2724257 := bstep (se 2 (by rfl) ⟨1021596, by rfl⟩ : syracuseStep 2724257 = 2043193) B2043193
theorem B6132131 : Blo 1815609 6132131 := bstep (se 1 (by rfl) ⟨4599098, by rfl⟩ : syracuseStep 6132131 = 9198197) B9198197
theorem B2724275 : Blo 1815609 2724275 := bstep (se 1 (by rfl) ⟨2043206, by rfl⟩ : syracuseStep 2724275 = 4086413) B4086413
theorem B6058435 : Blo 1815609 6058435 := bstep (se 1 (by rfl) ⟨4543826, by rfl⟩ : syracuseStep 6058435 = 9087653) B9087653
theorem B2724305 : Blo 1815609 2724305 := bstep (se 2 (by rfl) ⟨1021614, by rfl⟩ : syracuseStep 2724305 = 2043229) B2043229
theorem B4600273 : Blo 1815609 4600273 := bstep (se 2 (by rfl) ⟨1725102, by rfl⟩ : syracuseStep 4600273 = 3450205) B3450205
theorem B2724323 : Blo 1815609 2724323 := bstep (se 1 (by rfl) ⟨2043242, by rfl⟩ : syracuseStep 2724323 = 4086485) B4086485
theorem B2724353 : Blo 1815609 2724353 := bstep (se 2 (by rfl) ⟨1021632, by rfl⟩ : syracuseStep 2724353 = 2043265) B2043265
theorem B6214157 : Blo 1815609 6214157 := bstep (se 3 (by rfl) ⟨1165154, by rfl⟩ : syracuseStep 6214157 = 2330309) B2330309
theorem B2724371 : Blo 1815609 2724371 := bstep (se 1 (by rfl) ⟨2043278, by rfl⟩ : syracuseStep 2724371 = 4086557) B4086557
theorem B2044435 : Blo 1815609 2044435 := bstep (se 1 (by rfl) ⟨1533326, by rfl⟩ : syracuseStep 2044435 = 3066653) B3066653
theorem B2585137 : Blo 1815609 2585137 := bstep (se 2 (by rfl) ⟨969426, by rfl⟩ : syracuseStep 2585137 = 1938853) B1938853
theorem B10342961 : Blo 1815609 10342961 := bstep (se 2 (by rfl) ⟨3878610, by rfl⟩ : syracuseStep 10342961 = 7757221) B7757221
theorem B2454067 : Blo 1815609 2454067 := bstep (se 1 (by rfl) ⟨1840550, by rfl⟩ : syracuseStep 2454067 = 3681101) B3681101
theorem B2724401 : Blo 1815609 2724401 := bstep (se 2 (by rfl) ⟨1021650, by rfl⟩ : syracuseStep 2724401 = 2043301) B2043301
theorem B2724419 : Blo 1815609 2724419 := bstep (se 1 (by rfl) ⟨2043314, by rfl⟩ : syracuseStep 2724419 = 4086629) B4086629
theorem B2298451 : Blo 1815609 2298451 := bstep (se 1 (by rfl) ⟨1723838, by rfl⟩ : syracuseStep 2298451 = 3447677) B3447677
theorem B2724449 : Blo 1815609 2724449 := bstep (se 2 (by rfl) ⟨1021668, by rfl⟩ : syracuseStep 2724449 = 2043337) B2043337
theorem B2724467 : Blo 1815609 2724467 := bstep (se 1 (by rfl) ⟨2043350, by rfl⟩ : syracuseStep 2724467 = 4086701) B4086701
theorem B2724497 : Blo 1815609 2724497 := bstep (se 2 (by rfl) ⟨1021686, by rfl⟩ : syracuseStep 2724497 = 2043373) B2043373
theorem B3732131 : Blo 1815609 3732131 := bstep (se 1 (by rfl) ⟨2799098, by rfl⟩ : syracuseStep 3732131 = 5598197) B5598197
theorem B2724515 : Blo 1815609 2724515 := bstep (se 1 (by rfl) ⟨2043386, by rfl⟩ : syracuseStep 2724515 = 4086773) B4086773
theorem B2044579 : Blo 1815609 2044579 := bstep (se 1 (by rfl) ⟨1533434, by rfl⟩ : syracuseStep 2044579 = 3066869) B3066869
theorem B6132401 : Blo 1815609 6132401 := bstep (se 2 (by rfl) ⟨2299650, by rfl⟩ : syracuseStep 6132401 = 4599301) B4599301
theorem B2298547 : Blo 1815609 2298547 := bstep (se 1 (by rfl) ⟨1723910, by rfl⟩ : syracuseStep 2298547 = 3447821) B3447821
theorem B2724545 : Blo 1815609 2724545 := bstep (se 2 (by rfl) ⟨1021704, by rfl⟩ : syracuseStep 2724545 = 2043409) B2043409
theorem B2724563 : Blo 1815609 2724563 := bstep (se 1 (by rfl) ⟨2043422, by rfl⟩ : syracuseStep 2724563 = 4086845) B4086845
theorem B4600547 : Blo 1815609 4600547 := bstep (se 1 (by rfl) ⟨3450410, by rfl⟩ : syracuseStep 4600547 = 6900821) B6900821
theorem B2724593 : Blo 1815609 2724593 := bstep (se 2 (by rfl) ⟨1021722, by rfl⟩ : syracuseStep 2724593 = 2043445) B2043445
theorem B2724611 : Blo 1815609 2724611 := bstep (se 1 (by rfl) ⟨2043458, by rfl⟩ : syracuseStep 2724611 = 4086917) B4086917
theorem B2724641 : Blo 1815609 2724641 := bstep (se 2 (by rfl) ⟨1021740, by rfl⟩ : syracuseStep 2724641 = 2043481) B2043481
theorem B2724659 : Blo 1815609 2724659 := bstep (se 1 (by rfl) ⟨2043494, by rfl⟩ : syracuseStep 2724659 = 4086989) B4086989
theorem B22401845 : Blo 1815609 22401845 := bstep (se 5 (by rfl) ⟨1050086, by rfl⟩ : syracuseStep 22401845 = 2100173) B2100173
theorem B2044723 : Blo 1815609 2044723 := bstep (se 1 (by rfl) ⟨1533542, by rfl⟩ : syracuseStep 2044723 = 3067085) B3067085
theorem B2724689 : Blo 1815609 2724689 := bstep (se 2 (by rfl) ⟨1021758, by rfl⟩ : syracuseStep 2724689 = 2043517) B2043517
theorem B2724707 : Blo 1815609 2724707 := bstep (se 1 (by rfl) ⟨2043530, by rfl⟩ : syracuseStep 2724707 = 4087061) B4087061
theorem B2724737 : Blo 1815609 2724737 := bstep (se 2 (by rfl) ⟨1021776, by rfl⟩ : syracuseStep 2724737 = 2043553) B2043553
theorem B3273617 : Blo 1815609 3273617 := bstep (se 2 (by rfl) ⟨1227606, by rfl⟩ : syracuseStep 3273617 = 2455213) B2455213
theorem B2724755 : Blo 1815609 2724755 := bstep (se 1 (by rfl) ⟨2043566, by rfl⟩ : syracuseStep 2724755 = 4087133) B4087133
theorem B4600739 : Blo 1815609 4600739 := bstep (se 1 (by rfl) ⟨3450554, by rfl⟩ : syracuseStep 4600739 = 6901109) B6901109
theorem B2724785 : Blo 1815609 2724785 := bstep (se 2 (by rfl) ⟨1021794, by rfl⟩ : syracuseStep 2724785 = 2043589) B2043589
theorem B2724803 : Blo 1815609 2724803 := bstep (se 1 (by rfl) ⟨2043602, by rfl⟩ : syracuseStep 2724803 = 4087205) B4087205
theorem B3879875 : Blo 1815609 3879875 := bstep (se 1 (by rfl) ⟨2909906, by rfl⟩ : syracuseStep 3879875 = 5819813) B5819813
theorem B2724833 : Blo 1815609 2724833 := bstep (se 2 (by rfl) ⟨1021812, by rfl⟩ : syracuseStep 2724833 = 2043625) B2043625
theorem B2454499 : Blo 1815609 2454499 := bstep (se 1 (by rfl) ⟨1840874, by rfl⟩ : syracuseStep 2454499 = 3681749) B3681749
theorem B2724851 : Blo 1815609 2724851 := bstep (se 1 (by rfl) ⟨2043638, by rfl⟩ : syracuseStep 2724851 = 4087277) B4087277
theorem B2724881 : Blo 1815609 2724881 := bstep (se 2 (by rfl) ⟨1021830, by rfl⟩ : syracuseStep 2724881 = 2043661) B2043661
theorem B2724899 : Blo 1815609 2724899 := bstep (se 1 (by rfl) ⟨2043674, by rfl⟩ : syracuseStep 2724899 = 4087349) B4087349
theorem B2724929 : Blo 1815609 2724929 := bstep (se 2 (by rfl) ⟨1021848, by rfl⟩ : syracuseStep 2724929 = 2043697) B2043697
theorem B1815619 : Blo 1815609 1815619 := bstep (se 1 (by rfl) ⟨1361714, by rfl⟩ : syracuseStep 1815619 = 2723429) B2723429
theorem B1815635 : Blo 1815609 1815635 := bstep (se 1 (by rfl) ⟨1361726, by rfl⟩ : syracuseStep 1815635 = 2723453) B2723453
theorem B2724947 : Blo 1815609 2724947 := bstep (se 1 (by rfl) ⟨2043710, by rfl⟩ : syracuseStep 2724947 = 4087421) B4087421
theorem B1815651 : Blo 1815609 1815651 := bstep (se 1 (by rfl) ⟨1361738, by rfl⟩ : syracuseStep 1815651 = 2723477) B2723477
theorem B2724977 : Blo 1815609 2724977 := bstep (se 2 (by rfl) ⟨1021866, by rfl⟩ : syracuseStep 2724977 = 2043733) B2043733
theorem B1815667 : Blo 1815609 1815667 := bstep (se 1 (by rfl) ⟨1361750, by rfl⟩ : syracuseStep 1815667 = 2723501) B2723501
theorem B2585729 : Blo 1815609 2585729 := bstep (se 2 (by rfl) ⟨969648, by rfl⟩ : syracuseStep 2585729 = 1939297) B1939297
theorem B1815683 : Blo 1815609 1815683 := bstep (se 1 (by rfl) ⟨1361762, by rfl⟩ : syracuseStep 1815683 = 2723525) B2723525
theorem B2724995 : Blo 1815609 2724995 := bstep (se 1 (by rfl) ⟨2043746, by rfl⟩ : syracuseStep 2724995 = 4087493) B4087493
theorem B1815699 : Blo 1815609 1815699 := bstep (se 1 (by rfl) ⟨1361774, by rfl⟩ : syracuseStep 1815699 = 2723549) B2723549
theorem B2725025 : Blo 1815609 2725025 := bstep (se 2 (by rfl) ⟨1021884, by rfl⟩ : syracuseStep 2725025 = 2043769) B2043769
theorem B1815715 : Blo 1815609 1815715 := bstep (se 1 (by rfl) ⟨1361786, by rfl⟩ : syracuseStep 1815715 = 2723573) B2723573
theorem B2299043 : Blo 1815609 2299043 := bstep (se 1 (by rfl) ⟨1724282, by rfl⟩ : syracuseStep 2299043 = 3448565) B3448565
theorem B3273905 : Blo 1815609 3273905 := bstep (se 2 (by rfl) ⟨1227714, by rfl⟩ : syracuseStep 3273905 = 2455429) B2455429
theorem B1815731 : Blo 1815609 1815731 := bstep (se 1 (by rfl) ⟨1361798, by rfl⟩ : syracuseStep 1815731 = 2723597) B2723597
theorem B2725043 : Blo 1815609 2725043 := bstep (se 1 (by rfl) ⟨2043782, by rfl⟩ : syracuseStep 2725043 = 4087565) B4087565
theorem B1815747 : Blo 1815609 1815747 := bstep (se 1 (by rfl) ⟨1361810, by rfl⟩ : syracuseStep 1815747 = 2723621) B2723621
theorem B6132941 : Blo 1815609 6132941 := bstep (se 3 (by rfl) ⟨1149926, by rfl⟩ : syracuseStep 6132941 = 2299853) B2299853
theorem B2725073 : Blo 1815609 2725073 := bstep (se 2 (by rfl) ⟨1021902, by rfl⟩ : syracuseStep 2725073 = 2043805) B2043805
theorem B1815763 : Blo 1815609 1815763 := bstep (se 1 (by rfl) ⟨1361822, by rfl⟩ : syracuseStep 1815763 = 2723645) B2723645
theorem B1815779 : Blo 1815609 1815779 := bstep (se 1 (by rfl) ⟨1361834, by rfl⟩ : syracuseStep 1815779 = 2723669) B2723669
theorem B2725091 : Blo 1815609 2725091 := bstep (se 1 (by rfl) ⟨2043818, by rfl⟩ : syracuseStep 2725091 = 4087637) B4087637
theorem B2454769 : Blo 1815609 2454769 := bstep (se 2 (by rfl) ⟨920538, by rfl⟩ : syracuseStep 2454769 = 1841077) B1841077
theorem B1815795 : Blo 1815609 1815795 := bstep (se 1 (by rfl) ⟨1361846, by rfl⟩ : syracuseStep 1815795 = 2723693) B2723693
theorem B2725121 : Blo 1815609 2725121 := bstep (se 2 (by rfl) ⟨1021920, by rfl⟩ : syracuseStep 2725121 = 2043841) B2043841
theorem B1815811 : Blo 1815609 1815811 := bstep (se 1 (by rfl) ⟨1361858, by rfl⟩ : syracuseStep 1815811 = 2723717) B2723717
theorem B6132995 : Blo 1815609 6132995 := bstep (se 1 (by rfl) ⟨4599746, by rfl⟩ : syracuseStep 6132995 = 9199493) B9199493
theorem B1815827 : Blo 1815609 1815827 := bstep (se 1 (by rfl) ⟨1361870, by rfl⟩ : syracuseStep 1815827 = 2723741) B2723741
theorem B2725139 : Blo 1815609 2725139 := bstep (se 1 (by rfl) ⟨2043854, by rfl⟩ : syracuseStep 2725139 = 4087709) B4087709
theorem B1815843 : Blo 1815609 1815843 := bstep (se 1 (by rfl) ⟨1361882, by rfl⟩ : syracuseStep 1815843 = 2723765) B2723765
theorem B2725169 : Blo 1815609 2725169 := bstep (se 2 (by rfl) ⟨1021938, by rfl⟩ : syracuseStep 2725169 = 2043877) B2043877
theorem B1815859 : Blo 1815609 1815859 := bstep (se 1 (by rfl) ⟨1361894, by rfl⟩ : syracuseStep 1815859 = 2723789) B2723789
theorem B1815875 : Blo 1815609 1815875 := bstep (se 1 (by rfl) ⟨1361906, by rfl⟩ : syracuseStep 1815875 = 2723813) B2723813
theorem B2725187 : Blo 1815609 2725187 := bstep (se 1 (by rfl) ⟨2043890, by rfl⟩ : syracuseStep 2725187 = 4087781) B4087781
theorem B1815891 : Blo 1815609 1815891 := bstep (se 1 (by rfl) ⟨1361918, by rfl⟩ : syracuseStep 1815891 = 2723837) B2723837
theorem B2725217 : Blo 1815609 2725217 := bstep (se 2 (by rfl) ⟨1021956, by rfl⟩ : syracuseStep 2725217 = 2043913) B2043913
theorem B1815907 : Blo 1815609 1815907 := bstep (se 1 (by rfl) ⟨1361930, by rfl⟩ : syracuseStep 1815907 = 2723861) B2723861
theorem B1815923 : Blo 1815609 1815923 := bstep (se 1 (by rfl) ⟨1361942, by rfl⟩ : syracuseStep 1815923 = 2723885) B2723885
theorem B2725235 : Blo 1815609 2725235 := bstep (se 1 (by rfl) ⟨2043926, by rfl⟩ : syracuseStep 2725235 = 4087853) B4087853
theorem B1815939 : Blo 1815609 1815939 := bstep (se 1 (by rfl) ⟨1361954, by rfl⟩ : syracuseStep 1815939 = 2723909) B2723909
theorem B6894989 : Blo 1815609 6894989 := bstep (se 3 (by rfl) ⟨1292810, by rfl⟩ : syracuseStep 6894989 = 2585621) B2585621
theorem B1815955 : Blo 1815609 1815955 := bstep (se 1 (by rfl) ⟨1361966, by rfl⟩ : syracuseStep 1815955 = 2723933) B2723933
theorem B2725265 : Blo 1815609 2725265 := bstep (se 2 (by rfl) ⟨1021974, by rfl⟩ : syracuseStep 2725265 = 2043949) B2043949
theorem B1815971 : Blo 1815609 1815971 := bstep (se 1 (by rfl) ⟨1361978, by rfl⟩ : syracuseStep 1815971 = 2723957) B2723957
theorem B2725283 : Blo 1815609 2725283 := bstep (se 1 (by rfl) ⟨2043962, by rfl⟩ : syracuseStep 2725283 = 4087925) B4087925
theorem B5174705 : Blo 1815609 5174705 := bstep (se 2 (by rfl) ⟨1940514, by rfl⟩ : syracuseStep 5174705 = 3881029) B3881029
theorem B1815987 : Blo 1815609 1815987 := bstep (se 1 (by rfl) ⟨1361990, by rfl⟩ : syracuseStep 1815987 = 2723981) B2723981
theorem B2725313 : Blo 1815609 2725313 := bstep (se 2 (by rfl) ⟨1021992, by rfl⟩ : syracuseStep 2725313 = 2043985) B2043985
theorem B1816003 : Blo 1815609 1816003 := bstep (se 1 (by rfl) ⟨1362002, by rfl⟩ : syracuseStep 1816003 = 2724005) B2724005
theorem B1816019 : Blo 1815609 1816019 := bstep (se 1 (by rfl) ⟨1362014, by rfl⟩ : syracuseStep 1816019 = 2724029) B2724029
theorem B2725331 : Blo 1815609 2725331 := bstep (se 1 (by rfl) ⟨2043998, by rfl⟩ : syracuseStep 2725331 = 4087997) B4087997
theorem B1816035 : Blo 1815609 1816035 := bstep (se 1 (by rfl) ⟨1362026, by rfl⟩ : syracuseStep 1816035 = 2724053) B2724053
theorem B2725361 : Blo 1815609 2725361 := bstep (se 2 (by rfl) ⟨1022010, by rfl⟩ : syracuseStep 2725361 = 2044021) B2044021
theorem B1816051 : Blo 1815609 1816051 := bstep (se 1 (by rfl) ⟨1362038, by rfl⟩ : syracuseStep 1816051 = 2724077) B2724077
theorem B1816067 : Blo 1815609 1816067 := bstep (se 1 (by rfl) ⟨1362050, by rfl⟩ : syracuseStep 1816067 = 2724101) B2724101
theorem B2725379 : Blo 1815609 2725379 := bstep (se 1 (by rfl) ⟨2044034, by rfl⟩ : syracuseStep 2725379 = 4088069) B4088069
theorem B6133265 : Blo 1815609 6133265 := bstep (se 2 (by rfl) ⟨2299974, by rfl⟩ : syracuseStep 6133265 = 4599949) B4599949
theorem B1816083 : Blo 1815609 1816083 := bstep (se 1 (by rfl) ⟨1362062, by rfl⟩ : syracuseStep 1816083 = 2724125) B2724125
theorem B2725409 : Blo 1815609 2725409 := bstep (se 2 (by rfl) ⟨1022028, by rfl⟩ : syracuseStep 2725409 = 2044057) B2044057
theorem B1816099 : Blo 1815609 1816099 := bstep (se 1 (by rfl) ⟨1362074, by rfl⟩ : syracuseStep 1816099 = 2724149) B2724149
theorem B4085297 : Blo 1815609 4085297 := bstep (se 2 (by rfl) ⟨1531986, by rfl⟩ : syracuseStep 4085297 = 3063973) B3063973
theorem B1816115 : Blo 1815609 1816115 := bstep (se 1 (by rfl) ⟨1362086, by rfl⟩ : syracuseStep 1816115 = 2724173) B2724173
theorem B2725427 : Blo 1815609 2725427 := bstep (se 1 (by rfl) ⟨2044070, by rfl⟩ : syracuseStep 2725427 = 4088141) B4088141
theorem B2455105 : Blo 1815609 2455105 := bstep (se 2 (by rfl) ⟨920664, by rfl⟩ : syracuseStep 2455105 = 1841329) B1841329
theorem B4085315 : Blo 1815609 4085315 := bstep (se 1 (by rfl) ⟨3063986, by rfl⟩ : syracuseStep 4085315 = 6127973) B6127973
theorem B1816131 : Blo 1815609 1816131 := bstep (se 1 (by rfl) ⟨1362098, by rfl⟩ : syracuseStep 1816131 = 2724197) B2724197
theorem B2725457 : Blo 1815609 2725457 := bstep (se 2 (by rfl) ⟨1022046, by rfl⟩ : syracuseStep 2725457 = 2044093) B2044093
theorem B1816147 : Blo 1815609 1816147 := bstep (se 1 (by rfl) ⟨1362110, by rfl⟩ : syracuseStep 1816147 = 2724221) B2724221
theorem B1816163 : Blo 1815609 1816163 := bstep (se 1 (by rfl) ⟨1362122, by rfl⟩ : syracuseStep 1816163 = 2724245) B2724245
theorem B2725475 : Blo 1815609 2725475 := bstep (se 1 (by rfl) ⟨2044106, by rfl⟩ : syracuseStep 2725475 = 4088213) B4088213
theorem B1816179 : Blo 1815609 1816179 := bstep (se 1 (by rfl) ⟨1362134, by rfl⟩ : syracuseStep 1816179 = 2724269) B2724269
theorem B2725505 : Blo 1815609 2725505 := bstep (se 2 (by rfl) ⟨1022064, by rfl⟩ : syracuseStep 2725505 = 2044129) B2044129
theorem B1816195 : Blo 1815609 1816195 := bstep (se 1 (by rfl) ⟨1362146, by rfl⟩ : syracuseStep 1816195 = 2724293) B2724293
theorem B3683971 : Blo 1815609 3683971 := bstep (se 1 (by rfl) ⟨2762978, by rfl⟩ : syracuseStep 3683971 = 5525957) B5525957
theorem B1816211 : Blo 1815609 1816211 := bstep (se 1 (by rfl) ⟨1362158, by rfl⟩ : syracuseStep 1816211 = 2724317) B2724317
theorem B2586259 : Blo 1815609 2586259 := bstep (se 1 (by rfl) ⟨1939694, by rfl⟩ : syracuseStep 2586259 = 3879389) B3879389
theorem B2725523 : Blo 1815609 2725523 := bstep (se 1 (by rfl) ⟨2044142, by rfl⟩ : syracuseStep 2725523 = 4088285) B4088285
theorem B1816227 : Blo 1815609 1816227 := bstep (se 1 (by rfl) ⟨1362170, by rfl⟩ : syracuseStep 1816227 = 2724341) B2724341
theorem B1816243 : Blo 1815609 1816243 := bstep (se 1 (by rfl) ⟨1362182, by rfl⟩ : syracuseStep 1816243 = 2724365) B2724365
theorem B2725553 : Blo 1815609 2725553 := bstep (se 2 (by rfl) ⟨1022082, by rfl⟩ : syracuseStep 2725553 = 2044165) B2044165
theorem B1816259 : Blo 1815609 1816259 := bstep (se 1 (by rfl) ⟨1362194, by rfl⟩ : syracuseStep 1816259 = 2724389) B2724389
theorem B2725571 : Blo 1815609 2725571 := bstep (se 1 (by rfl) ⟨2044178, by rfl⟩ : syracuseStep 2725571 = 4088357) B4088357
theorem B1816275 : Blo 1815609 1816275 := bstep (se 1 (by rfl) ⟨1362206, by rfl⟩ : syracuseStep 1816275 = 2724413) B2724413
theorem B2725601 : Blo 1815609 2725601 := bstep (se 2 (by rfl) ⟨1022100, by rfl⟩ : syracuseStep 2725601 = 2044201) B2044201
theorem B1816291 : Blo 1815609 1816291 := bstep (se 1 (by rfl) ⟨1362218, by rfl⟩ : syracuseStep 1816291 = 2724437) B2724437
theorem B1816307 : Blo 1815609 1816307 := bstep (se 1 (by rfl) ⟨1362230, by rfl⟩ : syracuseStep 1816307 = 2724461) B2724461
theorem B2725619 : Blo 1815609 2725619 := bstep (se 1 (by rfl) ⟨2044214, by rfl⟩ : syracuseStep 2725619 = 4088429) B4088429
theorem B1816323 : Blo 1815609 1816323 := bstep (se 1 (by rfl) ⟨1362242, by rfl⟩ : syracuseStep 1816323 = 2724485) B2724485
theorem B2725649 : Blo 1815609 2725649 := bstep (se 2 (by rfl) ⟨1022118, by rfl⟩ : syracuseStep 2725649 = 2044237) B2044237
theorem B1816339 : Blo 1815609 1816339 := bstep (se 1 (by rfl) ⟨1362254, by rfl⟩ : syracuseStep 1816339 = 2724509) B2724509
theorem B1816355 : Blo 1815609 1816355 := bstep (se 1 (by rfl) ⟨1362266, by rfl⟩ : syracuseStep 1816355 = 2724533) B2724533
theorem B2725667 : Blo 1815609 2725667 := bstep (se 1 (by rfl) ⟨2044250, by rfl⟩ : syracuseStep 2725667 = 4088501) B4088501
theorem B1816371 : Blo 1815609 1816371 := bstep (se 1 (by rfl) ⟨1362278, by rfl⟩ : syracuseStep 1816371 = 2724557) B2724557
theorem B2725697 : Blo 1815609 2725697 := bstep (se 2 (by rfl) ⟨1022136, by rfl⟩ : syracuseStep 2725697 = 2044273) B2044273
theorem B1816387 : Blo 1815609 1816387 := bstep (se 1 (by rfl) ⟨1362290, by rfl⟩ : syracuseStep 1816387 = 2724581) B2724581
theorem B4085585 : Blo 1815609 4085585 := bstep (se 2 (by rfl) ⟨1532094, by rfl⟩ : syracuseStep 4085585 = 3064189) B3064189
theorem B1816403 : Blo 1815609 1816403 := bstep (se 1 (by rfl) ⟨1362302, by rfl⟩ : syracuseStep 1816403 = 2724605) B2724605
theorem B2725715 : Blo 1815609 2725715 := bstep (se 1 (by rfl) ⟨2044286, by rfl⟩ : syracuseStep 2725715 = 4088573) B4088573
theorem B4085603 : Blo 1815609 4085603 := bstep (se 1 (by rfl) ⟨3064202, by rfl⟩ : syracuseStep 4085603 = 6128405) B6128405
theorem B1816419 : Blo 1815609 1816419 := bstep (se 1 (by rfl) ⟨1362314, by rfl⟩ : syracuseStep 1816419 = 2724629) B2724629
theorem B2299747 : Blo 1815609 2299747 := bstep (se 1 (by rfl) ⟨1724810, by rfl⟩ : syracuseStep 2299747 = 3449621) B3449621
theorem B2725745 : Blo 1815609 2725745 := bstep (se 2 (by rfl) ⟨1022154, by rfl⟩ : syracuseStep 2725745 = 2044309) B2044309
theorem B1816435 : Blo 1815609 1816435 := bstep (se 1 (by rfl) ⟨1362326, by rfl⟩ : syracuseStep 1816435 = 2724653) B2724653
theorem B1816451 : Blo 1815609 1816451 := bstep (se 1 (by rfl) ⟨1362338, by rfl⟩ : syracuseStep 1816451 = 2724677) B2724677
theorem B2725763 : Blo 1815609 2725763 := bstep (se 1 (by rfl) ⟨2044322, by rfl⟩ : syracuseStep 2725763 = 4088645) B4088645
theorem B26179469 : Blo 1815609 26179469 := bstep (se 3 (by rfl) ⟨4908650, by rfl⟩ : syracuseStep 26179469 = 9817301) B9817301
theorem B13793165 : Blo 1815609 13793165 := bstep (se 3 (by rfl) ⟨2586218, by rfl⟩ : syracuseStep 13793165 = 5172437) B5172437
theorem B11048845 : Blo 1815609 11048845 := bstep (se 3 (by rfl) ⟨2071658, by rfl⟩ : syracuseStep 11048845 = 4143317) B4143317
theorem B3192721 : Blo 1815609 3192721 := bstep (se 2 (by rfl) ⟨1197270, by rfl⟩ : syracuseStep 3192721 = 2394541) B2394541
theorem B1816467 : Blo 1815609 1816467 := bstep (se 1 (by rfl) ⟨1362350, by rfl⟩ : syracuseStep 1816467 = 2724701) B2724701
theorem B2725793 : Blo 1815609 2725793 := bstep (se 2 (by rfl) ⟨1022172, by rfl⟩ : syracuseStep 2725793 = 2044345) B2044345
theorem B1816483 : Blo 1815609 1816483 := bstep (se 1 (by rfl) ⟨1362362, by rfl⟩ : syracuseStep 1816483 = 2724725) B2724725
theorem B1816499 : Blo 1815609 1816499 := bstep (se 1 (by rfl) ⟨1362374, by rfl⟩ : syracuseStep 1816499 = 2724749) B2724749
theorem B2725811 : Blo 1815609 2725811 := bstep (se 1 (by rfl) ⟨2044358, by rfl⟩ : syracuseStep 2725811 = 4088717) B4088717
theorem B1816515 : Blo 1815609 1816515 := bstep (se 1 (by rfl) ⟨1362386, by rfl⟩ : syracuseStep 1816515 = 2724773) B2724773
theorem B2299843 : Blo 1815609 2299843 := bstep (se 1 (by rfl) ⟨1724882, by rfl⟩ : syracuseStep 2299843 = 3449765) B3449765
theorem B2725841 : Blo 1815609 2725841 := bstep (se 2 (by rfl) ⟨1022190, by rfl⟩ : syracuseStep 2725841 = 2044381) B2044381
theorem B1816531 : Blo 1815609 1816531 := bstep (se 1 (by rfl) ⟨1362398, by rfl⟩ : syracuseStep 1816531 = 2724797) B2724797
theorem B10344419 : Blo 1815609 10344419 := bstep (se 1 (by rfl) ⟨7758314, by rfl⟩ : syracuseStep 10344419 = 15516629) B15516629
theorem B1816547 : Blo 1815609 1816547 := bstep (se 1 (by rfl) ⟨1362410, by rfl⟩ : syracuseStep 1816547 = 2724821) B2724821
theorem B2586595 : Blo 1815609 2586595 := bstep (se 1 (by rfl) ⟨1939946, by rfl⟩ : syracuseStep 2586595 = 3879893) B3879893
theorem B2725859 : Blo 1815609 2725859 := bstep (se 1 (by rfl) ⟨2044394, by rfl⟩ : syracuseStep 2725859 = 4088789) B4088789
theorem B1816563 : Blo 1815609 1816563 := bstep (se 1 (by rfl) ⟨1362422, by rfl⟩ : syracuseStep 1816563 = 2724845) B2724845
theorem B2725889 : Blo 1815609 2725889 := bstep (se 2 (by rfl) ⟨1022208, by rfl⟩ : syracuseStep 2725889 = 2044417) B2044417
theorem B1816579 : Blo 1815609 1816579 := bstep (se 1 (by rfl) ⟨1362434, by rfl⟩ : syracuseStep 1816579 = 2724869) B2724869
theorem B1816595 : Blo 1815609 1816595 := bstep (se 1 (by rfl) ⟨1362446, by rfl⟩ : syracuseStep 1816595 = 2724893) B2724893
theorem B2725907 : Blo 1815609 2725907 := bstep (se 1 (by rfl) ⟨2044430, by rfl⟩ : syracuseStep 2725907 = 4088861) B4088861
theorem B1816611 : Blo 1815609 1816611 := bstep (se 1 (by rfl) ⟨1362458, by rfl⟩ : syracuseStep 1816611 = 2724917) B2724917
theorem B6133805 : Blo 1815609 6133805 := bstep (se 3 (by rfl) ⟨1150088, by rfl⟩ : syracuseStep 6133805 = 2300177) B2300177
theorem B6633521 : Blo 1815609 6633521 := bstep (se 2 (by rfl) ⟨2487570, by rfl⟩ : syracuseStep 6633521 = 4975141) B4975141
theorem B2725937 : Blo 1815609 2725937 := bstep (se 2 (by rfl) ⟨1022226, by rfl⟩ : syracuseStep 2725937 = 2044453) B2044453
theorem B1816627 : Blo 1815609 1816627 := bstep (se 1 (by rfl) ⟨1362470, by rfl⟩ : syracuseStep 1816627 = 2724941) B2724941
theorem B1816643 : Blo 1815609 1816643 := bstep (se 1 (by rfl) ⟨1362482, by rfl⟩ : syracuseStep 1816643 = 2724965) B2724965
theorem B2725955 : Blo 1815609 2725955 := bstep (se 1 (by rfl) ⟨2044466, by rfl⟩ : syracuseStep 2725955 = 4088933) B4088933
theorem B5175377 : Blo 1815609 5175377 := bstep (se 2 (by rfl) ⟨1940766, by rfl⟩ : syracuseStep 5175377 = 3881533) B3881533
theorem B1816659 : Blo 1815609 1816659 := bstep (se 1 (by rfl) ⟨1362494, by rfl⟩ : syracuseStep 1816659 = 2724989) B2724989
theorem B2725985 : Blo 1815609 2725985 := bstep (se 2 (by rfl) ⟨1022244, by rfl⟩ : syracuseStep 2725985 = 2044489) B2044489
theorem B1816675 : Blo 1815609 1816675 := bstep (se 1 (by rfl) ⟨1362506, by rfl⟩ : syracuseStep 1816675 = 2725013) B2725013
theorem B6133859 : Blo 1815609 6133859 := bstep (se 1 (by rfl) ⟨4600394, by rfl⟩ : syracuseStep 6133859 = 9200789) B9200789
theorem B4085873 : Blo 1815609 4085873 := bstep (se 2 (by rfl) ⟨1532202, by rfl⟩ : syracuseStep 4085873 = 3064405) B3064405
theorem B1816691 : Blo 1815609 1816691 := bstep (se 1 (by rfl) ⟨1362518, by rfl⟩ : syracuseStep 1816691 = 2725037) B2725037
theorem B2726003 : Blo 1815609 2726003 := bstep (se 1 (by rfl) ⟨2044502, by rfl⟩ : syracuseStep 2726003 = 4089005) B4089005
theorem B4085891 : Blo 1815609 4085891 := bstep (se 1 (by rfl) ⟨3064418, by rfl⟩ : syracuseStep 4085891 = 6128837) B6128837
theorem B1816707 : Blo 1815609 1816707 := bstep (se 1 (by rfl) ⟨1362530, by rfl⟩ : syracuseStep 1816707 = 2725061) B2725061
theorem B17463437 : Blo 1815609 17463437 := bstep (se 3 (by rfl) ⟨3274394, by rfl⟩ : syracuseStep 17463437 = 6548789) B6548789
theorem B2726033 : Blo 1815609 2726033 := bstep (se 2 (by rfl) ⟨1022262, by rfl⟩ : syracuseStep 2726033 = 2044525) B2044525
theorem B1816723 : Blo 1815609 1816723 := bstep (se 1 (by rfl) ⟨1362542, by rfl⟩ : syracuseStep 1816723 = 2725085) B2725085
theorem B1816739 : Blo 1815609 1816739 := bstep (se 1 (by rfl) ⟨1362554, by rfl⟩ : syracuseStep 1816739 = 2725109) B2725109
theorem B2726051 : Blo 1815609 2726051 := bstep (se 1 (by rfl) ⟨2044538, by rfl⟩ : syracuseStep 2726051 = 4089077) B4089077
theorem B6895793 : Blo 1815609 6895793 := bstep (se 2 (by rfl) ⟨2585922, by rfl⟩ : syracuseStep 6895793 = 5171845) B5171845
theorem B1816755 : Blo 1815609 1816755 := bstep (se 1 (by rfl) ⟨1362566, by rfl⟩ : syracuseStep 1816755 = 2725133) B2725133
theorem B2726081 : Blo 1815609 2726081 := bstep (se 2 (by rfl) ⟨1022280, by rfl⟩ : syracuseStep 2726081 = 2044561) B2044561
theorem B1816771 : Blo 1815609 1816771 := bstep (se 1 (by rfl) ⟨1362578, by rfl⟩ : syracuseStep 1816771 = 2725157) B2725157
theorem B1816787 : Blo 1815609 1816787 := bstep (se 1 (by rfl) ⟨1362590, by rfl⟩ : syracuseStep 1816787 = 2725181) B2725181
theorem B2726099 : Blo 1815609 2726099 := bstep (se 1 (by rfl) ⟨2044574, by rfl⟩ : syracuseStep 2726099 = 4089149) B4089149
theorem B1816803 : Blo 1815609 1816803 := bstep (se 1 (by rfl) ⟨1362602, by rfl⟩ : syracuseStep 1816803 = 2725205) B2725205
theorem B2726129 : Blo 1815609 2726129 := bstep (se 2 (by rfl) ⟨1022298, by rfl⟩ : syracuseStep 2726129 = 2044597) B2044597
theorem B1816819 : Blo 1815609 1816819 := bstep (se 1 (by rfl) ⟨1362614, by rfl⟩ : syracuseStep 1816819 = 2725229) B2725229
theorem B1816835 : Blo 1815609 1816835 := bstep (se 1 (by rfl) ⟨1362626, by rfl⟩ : syracuseStep 1816835 = 2725253) B2725253
theorem B2726147 : Blo 1815609 2726147 := bstep (se 1 (by rfl) ⟨2044610, by rfl⟩ : syracuseStep 2726147 = 4089221) B4089221
theorem B1816851 : Blo 1815609 1816851 := bstep (se 1 (by rfl) ⟨1362638, by rfl⟩ : syracuseStep 1816851 = 2725277) B2725277
theorem B2726177 : Blo 1815609 2726177 := bstep (se 2 (by rfl) ⟨1022316, by rfl⟩ : syracuseStep 2726177 = 2044633) B2044633
theorem B1816867 : Blo 1815609 1816867 := bstep (se 1 (by rfl) ⟨1362650, by rfl⟩ : syracuseStep 1816867 = 2725301) B2725301
theorem B9197873 : Blo 1815609 9197873 := bstep (se 2 (by rfl) ⟨3449202, by rfl⟩ : syracuseStep 9197873 = 6898405) B6898405
theorem B1816883 : Blo 1815609 1816883 := bstep (se 1 (by rfl) ⟨1362662, by rfl⟩ : syracuseStep 1816883 = 2725325) B2725325
theorem B2726195 : Blo 1815609 2726195 := bstep (se 1 (by rfl) ⟨2044646, by rfl⟩ : syracuseStep 2726195 = 4089293) B4089293
theorem B3447107 : Blo 1815609 3447107 := bstep (se 1 (by rfl) ⟨2585330, by rfl⟩ : syracuseStep 3447107 = 5170661) B5170661
theorem B1816899 : Blo 1815609 1816899 := bstep (se 1 (by rfl) ⟨1362674, by rfl⟩ : syracuseStep 1816899 = 2725349) B2725349
theorem B2726225 : Blo 1815609 2726225 := bstep (se 2 (by rfl) ⟨1022334, by rfl⟩ : syracuseStep 2726225 = 2044669) B2044669
theorem B1816915 : Blo 1815609 1816915 := bstep (se 1 (by rfl) ⟨1362686, by rfl⟩ : syracuseStep 1816915 = 2725373) B2725373
theorem B1816931 : Blo 1815609 1816931 := bstep (se 1 (by rfl) ⟨1362698, by rfl⟩ : syracuseStep 1816931 = 2725397) B2725397
theorem B2726243 : Blo 1815609 2726243 := bstep (se 1 (by rfl) ⟨2044682, by rfl⟩ : syracuseStep 2726243 = 4089365) B4089365
theorem B23607665 : Blo 1815609 23607665 := bstep (se 2 (by rfl) ⟨8852874, by rfl⟩ : syracuseStep 23607665 = 17705749) B17705749
theorem B6134129 : Blo 1815609 6134129 := bstep (se 2 (by rfl) ⟨2300298, by rfl⟩ : syracuseStep 6134129 = 4600597) B4600597
theorem B1816947 : Blo 1815609 1816947 := bstep (se 1 (by rfl) ⟨1362710, by rfl⟩ : syracuseStep 1816947 = 2725421) B2725421
theorem B2726273 : Blo 1815609 2726273 := bstep (se 2 (by rfl) ⟨1022352, by rfl⟩ : syracuseStep 2726273 = 2044705) B2044705
theorem B1816963 : Blo 1815609 1816963 := bstep (se 1 (by rfl) ⟨1362722, by rfl⟩ : syracuseStep 1816963 = 2725445) B2725445
theorem B24869261 : Blo 1815609 24869261 := bstep (se 3 (by rfl) ⟨4662986, by rfl⟩ : syracuseStep 24869261 = 9325973) B9325973
theorem B4086161 : Blo 1815609 4086161 := bstep (se 2 (by rfl) ⟨1532310, by rfl⟩ : syracuseStep 4086161 = 3064621) B3064621
theorem B1816979 : Blo 1815609 1816979 := bstep (se 1 (by rfl) ⟨1362734, by rfl⟩ : syracuseStep 1816979 = 2725469) B2725469
theorem B2726291 : Blo 1815609 2726291 := bstep (se 1 (by rfl) ⟨2044718, by rfl⟩ : syracuseStep 2726291 = 4089437) B4089437
theorem B2070947 : Blo 1815609 2070947 := bstep (se 1 (by rfl) ⟨1553210, by rfl⟩ : syracuseStep 2070947 = 3106421) B3106421
theorem B4086179 : Blo 1815609 4086179 := bstep (se 1 (by rfl) ⟨3064634, by rfl⟩ : syracuseStep 4086179 = 6129269) B6129269
theorem B1816995 : Blo 1815609 1816995 := bstep (se 1 (by rfl) ⟨1362746, by rfl⟩ : syracuseStep 1816995 = 2725493) B2725493
theorem B2726321 : Blo 1815609 2726321 := bstep (se 2 (by rfl) ⟨1022370, by rfl⟩ : syracuseStep 2726321 = 2044741) B2044741
theorem B1817011 : Blo 1815609 1817011 := bstep (se 1 (by rfl) ⟨1362758, by rfl⟩ : syracuseStep 1817011 = 2725517) B2725517
theorem B2300339 : Blo 1815609 2300339 := bstep (se 1 (by rfl) ⟨1725254, by rfl⟩ : syracuseStep 2300339 = 3450509) B3450509
theorem B1817027 : Blo 1815609 1817027 := bstep (se 1 (by rfl) ⟨1362770, by rfl⟩ : syracuseStep 1817027 = 2725541) B2725541
theorem B2726339 : Blo 1815609 2726339 := bstep (se 1 (by rfl) ⟨2044754, by rfl⟩ : syracuseStep 2726339 = 4089509) B4089509
theorem B1817043 : Blo 1815609 1817043 := bstep (se 1 (by rfl) ⟨1362782, by rfl⟩ : syracuseStep 1817043 = 2725565) B2725565
theorem B2726369 : Blo 1815609 2726369 := bstep (se 2 (by rfl) ⟨1022388, by rfl⟩ : syracuseStep 2726369 = 2044777) B2044777
theorem B1817059 : Blo 1815609 1817059 := bstep (se 1 (by rfl) ⟨1362794, by rfl⟩ : syracuseStep 1817059 = 2725589) B2725589
theorem B1817075 : Blo 1815609 1817075 := bstep (se 1 (by rfl) ⟨1362806, by rfl⟩ : syracuseStep 1817075 = 2725613) B2725613
theorem B2726387 : Blo 1815609 2726387 := bstep (se 1 (by rfl) ⟨2044790, by rfl⟩ : syracuseStep 2726387 = 4089581) B4089581
theorem B1817091 : Blo 1815609 1817091 := bstep (se 1 (by rfl) ⟨1362818, by rfl⟩ : syracuseStep 1817091 = 2725637) B2725637
theorem B2587153 : Blo 1815609 2587153 := bstep (se 2 (by rfl) ⟨970182, by rfl⟩ : syracuseStep 2587153 = 1940365) B1940365
theorem B1817107 : Blo 1815609 1817107 := bstep (se 1 (by rfl) ⟨1362830, by rfl⟩ : syracuseStep 1817107 = 2725661) B2725661
theorem B1817123 : Blo 1815609 1817123 := bstep (se 1 (by rfl) ⟨1362842, by rfl⟩ : syracuseStep 1817123 = 2725685) B2725685
theorem B2587187 : Blo 1815609 2587187 := bstep (se 1 (by rfl) ⟨1940390, by rfl⟩ : syracuseStep 2587187 = 3880781) B3880781
theorem B1817139 : Blo 1815609 1817139 := bstep (se 1 (by rfl) ⟨1362854, by rfl⟩ : syracuseStep 1817139 = 2725709) B2725709
theorem B1817155 : Blo 1815609 1817155 := bstep (se 1 (by rfl) ⟨1362866, by rfl⟩ : syracuseStep 1817155 = 2725733) B2725733
theorem B1817171 : Blo 1815609 1817171 := bstep (se 1 (by rfl) ⟨1362878, by rfl⟩ : syracuseStep 1817171 = 2725757) B2725757
theorem B1817187 : Blo 1815609 1817187 := bstep (se 1 (by rfl) ⟨1362890, by rfl⟩ : syracuseStep 1817187 = 2725781) B2725781
theorem B1841779 : Blo 1815609 1841779 := bstep (se 1 (by rfl) ⟨1381334, by rfl⟩ : syracuseStep 1841779 = 2762669) B2762669
theorem B1817203 : Blo 1815609 1817203 := bstep (se 1 (by rfl) ⟨1362902, by rfl⟩ : syracuseStep 1817203 = 2725805) B2725805
theorem B1817219 : Blo 1815609 1817219 := bstep (se 1 (by rfl) ⟨1362914, by rfl⟩ : syracuseStep 1817219 = 2725829) B2725829
theorem B1817235 : Blo 1815609 1817235 := bstep (se 1 (by rfl) ⟨1362926, by rfl⟩ : syracuseStep 1817235 = 2725853) B2725853
theorem B1817251 : Blo 1815609 1817251 := bstep (se 1 (by rfl) ⟨1362938, by rfl⟩ : syracuseStep 1817251 = 2725877) B2725877
theorem B4086449 : Blo 1815609 4086449 := bstep (se 2 (by rfl) ⟨1532418, by rfl⟩ : syracuseStep 4086449 = 3064837) B3064837
theorem B1817267 : Blo 1815609 1817267 := bstep (se 1 (by rfl) ⟨1362950, by rfl⟩ : syracuseStep 1817267 = 2725901) B2725901
theorem B4086467 : Blo 1815609 4086467 := bstep (se 1 (by rfl) ⟨3064850, by rfl⟩ : syracuseStep 4086467 = 6129701) B6129701
theorem B20970181 : Blo 1815609 20970181 := bstep (se 4 (by rfl) ⟨1965954, by rfl⟩ : syracuseStep 20970181 = 3931909) B3931909
theorem B1817283 : Blo 1815609 1817283 := bstep (se 1 (by rfl) ⟨1362962, by rfl⟩ : syracuseStep 1817283 = 2725925) B2725925
theorem B1817299 : Blo 1815609 1817299 := bstep (se 1 (by rfl) ⟨1362974, by rfl⟩ : syracuseStep 1817299 = 2725949) B2725949
theorem B1817315 : Blo 1815609 1817315 := bstep (se 1 (by rfl) ⟨1362986, by rfl⟩ : syracuseStep 1817315 = 2725973) B2725973
theorem B1817331 : Blo 1815609 1817331 := bstep (se 1 (by rfl) ⟨1362998, by rfl⟩ : syracuseStep 1817331 = 2725997) B2725997
theorem B1817347 : Blo 1815609 1817347 := bstep (se 1 (by rfl) ⟨1363010, by rfl⟩ : syracuseStep 1817347 = 2726021) B2726021
theorem B1817363 : Blo 1815609 1817363 := bstep (se 1 (by rfl) ⟨1363022, by rfl⟩ : syracuseStep 1817363 = 2726045) B2726045
theorem B1817379 : Blo 1815609 1817379 := bstep (se 1 (by rfl) ⟨1363034, by rfl⟩ : syracuseStep 1817379 = 2726069) B2726069
theorem B1817395 : Blo 1815609 1817395 := bstep (se 1 (by rfl) ⟨1363046, by rfl⟩ : syracuseStep 1817395 = 2726093) B2726093
theorem B1817411 : Blo 1815609 1817411 := bstep (se 1 (by rfl) ⟨1363058, by rfl⟩ : syracuseStep 1817411 = 2726117) B2726117
theorem B6896461 : Blo 1815609 6896461 := bstep (se 3 (by rfl) ⟨1293086, by rfl⟩ : syracuseStep 6896461 = 2586173) B2586173
theorem B1817427 : Blo 1815609 1817427 := bstep (se 1 (by rfl) ⟨1363070, by rfl⟩ : syracuseStep 1817427 = 2726141) B2726141
theorem B1817443 : Blo 1815609 1817443 := bstep (se 1 (by rfl) ⟨1363082, by rfl⟩ : syracuseStep 1817443 = 2726165) B2726165
theorem B1817459 : Blo 1815609 1817459 := bstep (se 1 (by rfl) ⟨1363094, by rfl⟩ : syracuseStep 1817459 = 2726189) B2726189
theorem B1817475 : Blo 1815609 1817475 := bstep (se 1 (by rfl) ⟨1363106, by rfl⟩ : syracuseStep 1817475 = 2726213) B2726213
theorem B1817491 : Blo 1815609 1817491 := bstep (se 1 (by rfl) ⟨1363118, by rfl⟩ : syracuseStep 1817491 = 2726237) B2726237
theorem B1817507 : Blo 1815609 1817507 := bstep (se 1 (by rfl) ⟨1363130, by rfl⟩ : syracuseStep 1817507 = 2726261) B2726261
theorem B3881891 : Blo 1815609 3881891 := bstep (se 1 (by rfl) ⟨2911418, by rfl⟩ : syracuseStep 3881891 = 5822837) B5822837
theorem B1817523 : Blo 1815609 1817523 := bstep (se 1 (by rfl) ⟨1363142, by rfl⟩ : syracuseStep 1817523 = 2726285) B2726285
theorem B1817539 : Blo 1815609 1817539 := bstep (se 1 (by rfl) ⟨1363154, by rfl⟩ : syracuseStep 1817539 = 2726309) B2726309
theorem B10345421 : Blo 1815609 10345421 := bstep (se 3 (by rfl) ⟨1939766, by rfl⟩ : syracuseStep 10345421 = 3879533) B3879533
theorem B4086737 : Blo 1815609 4086737 := bstep (se 2 (by rfl) ⟨1532526, by rfl⟩ : syracuseStep 4086737 = 3065053) B3065053
theorem B1817555 : Blo 1815609 1817555 := bstep (se 1 (by rfl) ⟨1363166, by rfl⟩ : syracuseStep 1817555 = 2726333) B2726333
theorem B4086755 : Blo 1815609 4086755 := bstep (se 1 (by rfl) ⟨3065066, by rfl⟩ : syracuseStep 4086755 = 6130133) B6130133
theorem B1817571 : Blo 1815609 1817571 := bstep (se 1 (by rfl) ⟨1363178, by rfl⟩ : syracuseStep 1817571 = 2726357) B2726357
theorem B12434417 : Blo 1815609 12434417 := bstep (se 2 (by rfl) ⟨4662906, by rfl⟩ : syracuseStep 12434417 = 9325813) B9325813
theorem B1817587 : Blo 1815609 1817587 := bstep (se 1 (by rfl) ⟨1363190, by rfl⟩ : syracuseStep 1817587 = 2726381) B2726381
theorem B1817603 : Blo 1815609 1817603 := bstep (se 1 (by rfl) ⟨1363202, by rfl⟩ : syracuseStep 1817603 = 2726405) B2726405
theorem B5979203 : Blo 1815609 5979203 := bstep (se 1 (by rfl) ⟨4484402, by rfl⟩ : syracuseStep 5979203 = 8968805) B8968805
theorem B2587745 : Blo 1815609 2587745 := bstep (se 2 (by rfl) ⟨970404, by rfl⟩ : syracuseStep 2587745 = 1940809) B1940809
theorem B2587825 : Blo 1815609 2587825 := bstep (se 2 (by rfl) ⟨970434, by rfl⟩ : syracuseStep 2587825 = 1940869) B1940869
theorem B3448003 : Blo 1815609 3448003 := bstep (se 1 (by rfl) ⟨2586002, by rfl⟩ : syracuseStep 3448003 = 5172005) B5172005
theorem B4087025 : Blo 1815609 4087025 := bstep (se 2 (by rfl) ⟨1532634, by rfl⟩ : syracuseStep 4087025 = 3065269) B3065269
theorem B4087043 : Blo 1815609 4087043 := bstep (se 1 (by rfl) ⟨3065282, by rfl⟩ : syracuseStep 4087043 = 6130565) B6130565
theorem B4365571 : Blo 1815609 4365571 := bstep (se 1 (by rfl) ⟨3274178, by rfl⟩ : syracuseStep 4365571 = 6548357) B6548357
theorem B3448163 : Blo 1815609 3448163 := bstep (se 1 (by rfl) ⟨2586122, by rfl⟩ : syracuseStep 3448163 = 5172245) B5172245
theorem B6217165 : Blo 1815609 6217165 := bstep (se 3 (by rfl) ⟨1165718, by rfl⟩ : syracuseStep 6217165 = 2331437) B2331437
theorem B4087313 : Blo 1815609 4087313 := bstep (se 2 (by rfl) ⟨1532742, by rfl⟩ : syracuseStep 4087313 = 3065485) B3065485
theorem B4087331 : Blo 1815609 4087331 := bstep (se 1 (by rfl) ⟨3065498, by rfl⟩ : syracuseStep 4087331 = 6130997) B6130997
theorem B6897251 : Blo 1815609 6897251 := bstep (se 1 (by rfl) ⟨5172938, by rfl⟩ : syracuseStep 6897251 = 10345877) B10345877
theorem B5979793 : Blo 1815609 5979793 := bstep (se 2 (by rfl) ⟨2242422, by rfl⟩ : syracuseStep 5979793 = 4484845) B4484845
theorem B9199331 : Blo 1815609 9199331 := bstep (se 1 (by rfl) ⟨6899498, by rfl⟩ : syracuseStep 9199331 = 13798997) B13798997
theorem B22093553 : Blo 1815609 22093553 := bstep (se 2 (by rfl) ⟨8285082, by rfl⟩ : syracuseStep 22093553 = 16570165) B16570165
theorem B4087601 : Blo 1815609 4087601 := bstep (se 2 (by rfl) ⟨1532850, by rfl⟩ : syracuseStep 4087601 = 3065701) B3065701
theorem B4087619 : Blo 1815609 4087619 := bstep (se 1 (by rfl) ⟨3065714, by rfl⟩ : syracuseStep 4087619 = 6131429) B6131429
theorem B4366243 : Blo 1815609 4366243 := bstep (se 1 (by rfl) ⟨3274682, by rfl⟩ : syracuseStep 4366243 = 6549365) B6549365
theorem B2760727 : Blo 1815609 2760727 := bstep (se 1 (by rfl) ⟨2070545, by rfl⟩ : syracuseStep 2760727 = 4141091) B4141091
theorem B23273507 : Blo 1815609 23273507 := bstep (se 1 (by rfl) ⟨17455130, by rfl⟩ : syracuseStep 23273507 = 34910261) B34910261
theorem B10346561 : Blo 1815609 10346561 := bstep (se 2 (by rfl) ⟨3879960, by rfl⟩ : syracuseStep 10346561 = 7759921) B7759921
theorem B9191555 : Blo 1815609 9191555 := bstep (se 1 (by rfl) ⟨6893666, by rfl⟩ : syracuseStep 9191555 = 13787333) B13787333
theorem B4087961 : Blo 1815609 4087961 := bstep (se 2 (by rfl) ⟨1532985, by rfl⟩ : syracuseStep 4087961 = 3065971) B3065971
theorem B3932363 : Blo 1815609 3932363 := bstep (se 1 (by rfl) ⟨2949272, by rfl⟩ : syracuseStep 3932363 = 5898545) B5898545
theorem B4088051 : Blo 1815609 4088051 := bstep (se 1 (by rfl) ⟨3066038, by rfl⟩ : syracuseStep 4088051 = 6132077) B6132077
theorem B4088087 : Blo 1815609 4088087 := bstep (se 1 (by rfl) ⟨3066065, by rfl⟩ : syracuseStep 4088087 = 6132131) B6132131
theorem B14729651 : Blo 1815609 14729651 := bstep (se 1 (by rfl) ⟨11047238, by rfl⟩ : syracuseStep 14729651 = 22094477) B22094477
theorem B4088267 : Blo 1815609 4088267 := bstep (se 1 (by rfl) ⟨3066200, by rfl⟩ : syracuseStep 4088267 = 6132401) B6132401
theorem B8290781 : Blo 1815609 8290781 := bstep (se 3 (by rfl) ⟨1554521, by rfl⟩ : syracuseStep 8290781 = 3109043) B3109043
theorem B4088321 : Blo 1815609 4088321 := bstep (se 2 (by rfl) ⟨1533120, by rfl⟩ : syracuseStep 4088321 = 3066241) B3066241
theorem B3064331 : Blo 1815609 3064331 := bstep (se 1 (by rfl) ⟨2298248, by rfl⟩ : syracuseStep 3064331 = 4596497) B4596497
theorem B6898193 : Blo 1815609 6898193 := bstep (se 2 (by rfl) ⟨2586822, by rfl⟩ : syracuseStep 6898193 = 5173645) B5173645
theorem B14934563 : Blo 1815609 14934563 := bstep (se 1 (by rfl) ⟨11200922, by rfl⟩ : syracuseStep 14934563 = 22401845) B22401845
theorem B8077913 : Blo 1815609 8077913 := bstep (se 2 (by rfl) ⟨3029217, by rfl⟩ : syracuseStep 8077913 = 6058435) B6058435
theorem B3064459 : Blo 1815609 3064459 := bstep (se 1 (by rfl) ⟨2298344, by rfl⟩ : syracuseStep 3064459 = 4596689) B4596689
theorem B3449537 : Blo 1815609 3449537 := bstep (se 2 (by rfl) ⟨1293576, by rfl⟩ : syracuseStep 3449537 = 2587153) B2587153
theorem B4088537 : Blo 1815609 4088537 := bstep (se 2 (by rfl) ⟨1533201, by rfl⟩ : syracuseStep 4088537 = 3066403) B3066403
theorem B3064601 : Blo 1815609 3064601 := bstep (se 2 (by rfl) ⟨1149225, by rfl⟩ : syracuseStep 3064601 = 2298451) B2298451
theorem B4088627 : Blo 1815609 4088627 := bstep (se 1 (by rfl) ⟨3066470, by rfl⟩ : syracuseStep 4088627 = 6132941) B6132941
theorem B11633473 : Blo 1815609 11633473 := bstep (se 2 (by rfl) ⟨4362552, by rfl⟩ : syracuseStep 11633473 = 8725105) B8725105
theorem B6128459 : Blo 1815609 6128459 := bstep (se 1 (by rfl) ⟨4596344, by rfl⟩ : syracuseStep 6128459 = 9192689) B9192689
theorem B4088663 : Blo 1815609 4088663 := bstep (se 1 (by rfl) ⟨3066497, by rfl⟩ : syracuseStep 4088663 = 6132995) B6132995
theorem B3064729 : Blo 1815609 3064729 := bstep (se 2 (by rfl) ⟨1149273, by rfl⟩ : syracuseStep 3064729 = 2298547) B2298547
theorem B27960241 : Blo 1815609 27960241 := bstep (se 2 (by rfl) ⟨10485090, by rfl⟩ : syracuseStep 27960241 = 20970181) B20970181
theorem B4596659 : Blo 1815609 4596659 := bstep (se 1 (by rfl) ⟨3447494, by rfl⟩ : syracuseStep 4596659 = 6894989) B6894989
theorem B26198963 : Blo 1815609 26198963 := bstep (se 1 (by rfl) ⟨19649222, by rfl⟩ : syracuseStep 26198963 = 39298445) B39298445
theorem B3449803 : Blo 1815609 3449803 := bstep (se 1 (by rfl) ⟨2587352, by rfl⟩ : syracuseStep 3449803 = 5174705) B5174705
theorem B4088843 : Blo 1815609 4088843 := bstep (se 1 (by rfl) ⟨3066632, by rfl⟩ : syracuseStep 4088843 = 6133265) B6133265
theorem B4088897 : Blo 1815609 4088897 := bstep (se 2 (by rfl) ⟨1533336, by rfl⟩ : syracuseStep 4088897 = 3066673) B3066673
theorem B6128729 : Blo 1815609 6128729 := bstep (se 2 (by rfl) ⟨2298273, by rfl⟩ : syracuseStep 6128729 = 4596547) B4596547
theorem B5522525 : Blo 1815609 5522525 := bstep (se 3 (by rfl) ⟨1035473, by rfl⟩ : syracuseStep 5522525 = 2070947) B2070947
theorem B6898891 : Blo 1815609 6898891 := bstep (se 1 (by rfl) ⟨5174168, by rfl⟩ : syracuseStep 6898891 = 10348337) B10348337
theorem B13092101 : Blo 1815609 13092101 := bstep (se 4 (by rfl) ⟨1227384, by rfl⟩ : syracuseStep 13092101 = 2454769) B2454769
theorem B4089113 : Blo 1815609 4089113 := bstep (se 2 (by rfl) ⟨1533417, by rfl⟩ : syracuseStep 4089113 = 3066835) B3066835
theorem B4089203 : Blo 1815609 4089203 := bstep (se 1 (by rfl) ⟨3066902, by rfl⟩ : syracuseStep 4089203 = 6133805) B6133805
theorem B3450251 : Blo 1815609 3450251 := bstep (se 1 (by rfl) ⟨2587688, by rfl⟩ : syracuseStep 3450251 = 5175377) B5175377
theorem B4089239 : Blo 1815609 4089239 := bstep (se 1 (by rfl) ⟨3066929, by rfl⟩ : syracuseStep 4089239 = 6133859) B6133859
theorem B11642291 : Blo 1815609 11642291 := bstep (se 1 (by rfl) ⟨8731718, by rfl⟩ : syracuseStep 11642291 = 17463437) B17463437
theorem B4597195 : Blo 1815609 4597195 := bstep (se 1 (by rfl) ⟨3447896, by rfl⟩ : syracuseStep 4597195 = 6895793) B6895793
theorem B3065303 : Blo 1815609 3065303 := bstep (se 1 (by rfl) ⟨2298977, by rfl⟩ : syracuseStep 3065303 = 4597955) B4597955
theorem B2622937 : Blo 1815609 2622937 := bstep (se 2 (by rfl) ⟨983601, by rfl⟩ : syracuseStep 2622937 = 1967203) B1967203
theorem B9201113 : Blo 1815609 9201113 := bstep (se 2 (by rfl) ⟨3450417, by rfl⟩ : syracuseStep 9201113 = 6900835) B6900835
theorem B6899165 : Blo 1815609 6899165 := bstep (se 3 (by rfl) ⟨1293593, by rfl⟩ : syracuseStep 6899165 = 2587187) B2587187
theorem B3450433 : Blo 1815609 3450433 := bstep (se 2 (by rfl) ⟨1293912, by rfl⟩ : syracuseStep 3450433 = 2587825) B2587825
theorem B15738443 : Blo 1815609 15738443 := bstep (se 1 (by rfl) ⟨11803832, by rfl⟩ : syracuseStep 15738443 = 23607665) B23607665
theorem B4089419 : Blo 1815609 4089419 := bstep (se 1 (by rfl) ⟨3067064, by rfl⟩ : syracuseStep 4089419 = 6134129) B6134129
theorem B3065431 : Blo 1815609 3065431 := bstep (se 1 (by rfl) ⟨2299073, by rfl⟩ : syracuseStep 3065431 = 4598147) B4598147
theorem B4597337 : Blo 1815609 4597337 := bstep (se 2 (by rfl) ⟨1724001, by rfl⟩ : syracuseStep 4597337 = 3448003) B3448003
theorem B4089473 : Blo 1815609 4089473 := bstep (se 2 (by rfl) ⟨1533552, by rfl⟩ : syracuseStep 4089473 = 3067105) B3067105
theorem B2909849 : Blo 1815609 2909849 := bstep (se 2 (by rfl) ⟨1091193, by rfl⟩ : syracuseStep 2909849 = 2182387) B2182387
theorem B6129431 : Blo 1815609 6129431 := bstep (se 1 (by rfl) ⟨4597073, by rfl⟩ : syracuseStep 6129431 = 9194147) B9194147
theorem B13789277 : Blo 1815609 13789277 := bstep (se 3 (by rfl) ⟨2585489, by rfl⟩ : syracuseStep 13789277 = 5170979) B5170979
theorem B6899863 : Blo 1815609 6899863 := bstep (se 1 (by rfl) ⟨5174897, by rfl⟩ : syracuseStep 6899863 = 10349795) B10349795
theorem B7973057 : Blo 1815609 7973057 := bstep (se 2 (by rfl) ⟨2989896, by rfl⟩ : syracuseStep 7973057 = 5979793) B5979793
theorem B3066059 : Blo 1815609 3066059 := bstep (se 1 (by rfl) ⟨2299544, by rfl⟩ : syracuseStep 3066059 = 4599089) B4599089
theorem B11634961 : Blo 1815609 11634961 := bstep (se 2 (by rfl) ⟨4363110, by rfl⟩ : syracuseStep 11634961 = 8726221) B8726221
theorem B8849681 : Blo 1815609 8849681 := bstep (se 2 (by rfl) ⟨3318630, by rfl⟩ : syracuseStep 8849681 = 6637261) B6637261
theorem B6129971 : Blo 1815609 6129971 := bstep (se 1 (by rfl) ⟨4597478, by rfl⟩ : syracuseStep 6129971 = 9194957) B9194957
theorem B3066187 : Blo 1815609 3066187 := bstep (se 1 (by rfl) ⟨2299640, by rfl⟩ : syracuseStep 3066187 = 4599281) B4599281
theorem B4598167 : Blo 1815609 4598167 := bstep (se 1 (by rfl) ⟨3448625, by rfl⟩ : syracuseStep 4598167 = 6897251) B6897251
theorem B3066329 : Blo 1815609 3066329 := bstep (se 2 (by rfl) ⟨1149873, by rfl⟩ : syracuseStep 3066329 = 2299747) B2299747
theorem B14731793 : Blo 1815609 14731793 := bstep (se 2 (by rfl) ⟨5524422, by rfl⟩ : syracuseStep 14731793 = 11048845) B11048845
theorem B6130241 : Blo 1815609 6130241 := bstep (se 2 (by rfl) ⟨2298840, by rfl⟩ : syracuseStep 6130241 = 4597681) B4597681
theorem B7367257 : Blo 1815609 7367257 := bstep (se 2 (by rfl) ⟨2762721, by rfl⟩ : syracuseStep 7367257 = 5525443) B5525443
theorem B3066457 : Blo 1815609 3066457 := bstep (se 2 (by rfl) ⟨1149921, by rfl⟩ : syracuseStep 3066457 = 2299843) B2299843
theorem B125880925 : Blo 1815609 125880925 := bstep (se 3 (by rfl) ⟨23602673, by rfl⟩ : syracuseStep 125880925 = 47205347) B47205347
theorem B2042635 : Blo 1815609 2042635 := bstep (se 1 (by rfl) ⟨1531976, by rfl⟩ : syracuseStep 2042635 = 3063953) B3063953
theorem B3681035 : Blo 1815609 3681035 := bstep (se 1 (by rfl) ⟨2760776, by rfl⟩ : syracuseStep 3681035 = 5521553) B5521553
theorem B4598603 : Blo 1815609 4598603 := bstep (se 1 (by rfl) ⟨3448952, by rfl⟩ : syracuseStep 4598603 = 6897905) B6897905
theorem B9317213 : Blo 1815609 9317213 := bstep (se 3 (by rfl) ⟨1746977, by rfl⟩ : syracuseStep 9317213 = 3493955) B3493955
theorem B2042743 : Blo 1815609 2042743 := bstep (se 1 (by rfl) ⟨1532057, by rfl⟩ : syracuseStep 2042743 = 3064115) B3064115
theorem B5172119 : Blo 1815609 5172119 := bstep (se 1 (by rfl) ⟨3879089, by rfl⟩ : syracuseStep 5172119 = 7758179) B7758179
theorem B6900653 : Blo 1815609 6900653 := bstep (se 3 (by rfl) ⟨1293872, by rfl⟩ : syracuseStep 6900653 = 2587745) B2587745
theorem B7760843 : Blo 1815609 7760843 := bstep (se 1 (by rfl) ⟨5820632, by rfl⟩ : syracuseStep 7760843 = 11641265) B11641265
theorem B68111381 : Blo 1815609 68111381 := bstep (se 6 (by rfl) ⟨1596360, by rfl⟩ : syracuseStep 68111381 = 3192721) B3192721
theorem B2042923 : Blo 1815609 2042923 := bstep (se 1 (by rfl) ⟨1532192, by rfl⟩ : syracuseStep 2042923 = 3064385) B3064385
theorem B6130781 : Blo 1815609 6130781 := bstep (se 3 (by rfl) ⟨1149521, by rfl⟩ : syracuseStep 6130781 = 2299043) B2299043
theorem B2043031 : Blo 1815609 2043031 := bstep (se 1 (by rfl) ⟨1532273, by rfl⟩ : syracuseStep 2043031 = 3064547) B3064547
theorem B3067031 : Blo 1815609 3067031 := bstep (se 1 (by rfl) ⟨2300273, by rfl⟩ : syracuseStep 3067031 = 4600547) B4600547
theorem B4598977 : Blo 1815609 4598977 := bstep (se 2 (by rfl) ⟨1724616, by rfl⟩ : syracuseStep 4598977 = 3449233) B3449233
theorem B2182411 : Blo 1815609 2182411 := bstep (se 1 (by rfl) ⟨1636808, by rfl⟩ : syracuseStep 2182411 = 3273617) B3273617
theorem B3067159 : Blo 1815609 3067159 := bstep (se 1 (by rfl) ⟨2300369, by rfl⟩ : syracuseStep 3067159 = 4600739) B4600739
theorem B3681587 : Blo 1815609 3681587 := bstep (se 1 (by rfl) ⟨2761190, by rfl⟩ : syracuseStep 3681587 = 5522381) B5522381
theorem B2043211 : Blo 1815609 2043211 := bstep (se 1 (by rfl) ⟨1532408, by rfl⟩ : syracuseStep 2043211 = 3064817) B3064817
theorem B3272089 : Blo 1815609 3272089 := bstep (se 2 (by rfl) ⟨1227033, by rfl⟩ : syracuseStep 3272089 = 2454067) B2454067
theorem B2043319 : Blo 1815609 2043319 := bstep (se 1 (by rfl) ⟨1532489, by rfl⟩ : syracuseStep 2043319 = 3064979) B3064979
theorem B3108439 : Blo 1815609 3108439 := bstep (se 1 (by rfl) ⟨2331329, by rfl⟩ : syracuseStep 3108439 = 4662659) B4662659
theorem B2723417 : Blo 1815609 2723417 := bstep (se 2 (by rfl) ⟨1021281, by rfl⟩ : syracuseStep 2723417 = 2042563) B2042563
theorem B2043499 : Blo 1815609 2043499 := bstep (se 1 (by rfl) ⟨1532624, by rfl⟩ : syracuseStep 2043499 = 3065249) B3065249
theorem B2723531 : Blo 1815609 2723531 := bstep (se 1 (by rfl) ⟨2042648, by rfl⟩ : syracuseStep 2723531 = 4085297) B4085297
theorem B2723543 : Blo 1815609 2723543 := bstep (se 1 (by rfl) ⟨2042657, by rfl⟩ : syracuseStep 2723543 = 4085315) B4085315
theorem B2043607 : Blo 1815609 2043607 := bstep (se 1 (by rfl) ⟨1532705, by rfl⟩ : syracuseStep 2043607 = 3065411) B3065411
theorem B9195281 : Blo 1815609 9195281 := bstep (se 2 (by rfl) ⟨3448230, by rfl⟩ : syracuseStep 9195281 = 6896461) B6896461
theorem B4599575 : Blo 1815609 4599575 := bstep (se 1 (by rfl) ⟨3449681, by rfl⟩ : syracuseStep 4599575 = 6899363) B6899363
theorem B2723609 : Blo 1815609 2723609 := bstep (se 2 (by rfl) ⟨1021353, by rfl⟩ : syracuseStep 2723609 = 2042707) B2042707
theorem B3682073 : Blo 1815609 3682073 := bstep (se 2 (by rfl) ⟨1380777, by rfl⟩ : syracuseStep 3682073 = 2761555) B2761555
theorem B2723723 : Blo 1815609 2723723 := bstep (se 1 (by rfl) ⟨2042792, by rfl⟩ : syracuseStep 2723723 = 4085585) B4085585
theorem B2043787 : Blo 1815609 2043787 := bstep (se 1 (by rfl) ⟨1532840, by rfl⟩ : syracuseStep 2043787 = 3065681) B3065681
theorem B2723735 : Blo 1815609 2723735 := bstep (se 1 (by rfl) ⟨2042801, by rfl⟩ : syracuseStep 2723735 = 4085603) B4085603
theorem B17452979 : Blo 1815609 17452979 := bstep (se 1 (by rfl) ⟨13089734, by rfl⟩ : syracuseStep 17452979 = 26179469) B26179469
theorem B9195443 : Blo 1815609 9195443 := bstep (se 1 (by rfl) ⟨6896582, by rfl⟩ : syracuseStep 9195443 = 13793165) B13793165
theorem B2723801 : Blo 1815609 2723801 := bstep (se 2 (by rfl) ⟨1021425, by rfl⟩ : syracuseStep 2723801 = 2042851) B2042851
theorem B3272665 : Blo 1815609 3272665 := bstep (se 2 (by rfl) ⟨1227249, by rfl⟩ : syracuseStep 3272665 = 2454499) B2454499
theorem B2043895 : Blo 1815609 2043895 := bstep (se 1 (by rfl) ⟨1532921, by rfl⟩ : syracuseStep 2043895 = 3065843) B3065843
theorem B2723915 : Blo 1815609 2723915 := bstep (se 1 (by rfl) ⟨2042936, by rfl⟩ : syracuseStep 2723915 = 4085873) B4085873
theorem B2723927 : Blo 1815609 2723927 := bstep (se 1 (by rfl) ⟨2042945, by rfl⟩ : syracuseStep 2723927 = 4085891) B4085891
theorem B24866909 : Blo 1815609 24866909 := bstep (se 3 (by rfl) ⟨4662545, by rfl⟩ : syracuseStep 24866909 = 9325091) B9325091
theorem B11194469 : Blo 1815609 11194469 := bstep (se 4 (by rfl) ⟨1049481, by rfl⟩ : syracuseStep 11194469 = 2098963) B2098963
theorem B6549655 : Blo 1815609 6549655 := bstep (se 1 (by rfl) ⟨4912241, by rfl⟩ : syracuseStep 6549655 = 9824483) B9824483
theorem B2723993 : Blo 1815609 2723993 := bstep (se 2 (by rfl) ⟨1021497, by rfl⟩ : syracuseStep 2723993 = 2042995) B2042995
theorem B2044075 : Blo 1815609 2044075 := bstep (se 1 (by rfl) ⟨1533056, by rfl⟩ : syracuseStep 2044075 = 3066113) B3066113
theorem B6131915 : Blo 1815609 6131915 := bstep (se 1 (by rfl) ⟨4598936, by rfl⟩ : syracuseStep 6131915 = 9197873) B9197873
theorem B2298071 : Blo 1815609 2298071 := bstep (se 1 (by rfl) ⟨1723553, by rfl⟩ : syracuseStep 2298071 = 3447107) B3447107
theorem B2724107 : Blo 1815609 2724107 := bstep (se 1 (by rfl) ⟨2043080, by rfl⟩ : syracuseStep 2724107 = 4086161) B4086161
theorem B2724119 : Blo 1815609 2724119 := bstep (se 1 (by rfl) ⟨2043089, by rfl⟩ : syracuseStep 2724119 = 4086179) B4086179
theorem B2044183 : Blo 1815609 2044183 := bstep (se 1 (by rfl) ⟨1533137, by rfl⟩ : syracuseStep 2044183 = 3066275) B3066275
theorem B15520045 : Blo 1815609 15520045 := bstep (se 3 (by rfl) ⟨2910008, by rfl⟩ : syracuseStep 15520045 = 5820017) B5820017
theorem B2724185 : Blo 1815609 2724185 := bstep (se 2 (by rfl) ⟨1021569, by rfl⟩ : syracuseStep 2724185 = 2043139) B2043139
theorem B5820761 : Blo 1815609 5820761 := bstep (se 2 (by rfl) ⟨2182785, by rfl⟩ : syracuseStep 5820761 = 4365571) B4365571
theorem B6894017 : Blo 1815609 6894017 := bstep (se 2 (by rfl) ⟨2585256, by rfl⟩ : syracuseStep 6894017 = 5170513) B5170513
theorem B2724299 : Blo 1815609 2724299 := bstep (se 1 (by rfl) ⟨2043224, by rfl⟩ : syracuseStep 2724299 = 4086449) B4086449
theorem B2044363 : Blo 1815609 2044363 := bstep (se 1 (by rfl) ⟨1533272, by rfl⟩ : syracuseStep 2044363 = 3066545) B3066545
theorem B2724311 : Blo 1815609 2724311 := bstep (se 1 (by rfl) ⟨2043233, by rfl⟩ : syracuseStep 2724311 = 4086467) B4086467
theorem B6132185 : Blo 1815609 6132185 := bstep (se 2 (by rfl) ⟨2299569, by rfl⟩ : syracuseStep 6132185 = 4599139) B4599139
theorem B2724377 : Blo 1815609 2724377 := bstep (se 2 (by rfl) ⟨1021641, by rfl⟩ : syracuseStep 2724377 = 2043283) B2043283
theorem B7762483 : Blo 1815609 7762483 := bstep (se 1 (by rfl) ⟨5821862, by rfl⟩ : syracuseStep 7762483 = 11643725) B11643725
theorem B2044471 : Blo 1815609 2044471 := bstep (se 1 (by rfl) ⟨1533353, by rfl⟩ : syracuseStep 2044471 = 3066707) B3066707
theorem B4600385 : Blo 1815609 4600385 := bstep (se 2 (by rfl) ⟨1725144, by rfl⟩ : syracuseStep 4600385 = 3450289) B3450289
theorem B8286851 : Blo 1815609 8286851 := bstep (se 1 (by rfl) ⟨6215138, by rfl⟩ : syracuseStep 8286851 = 12430277) B12430277
theorem B2724491 : Blo 1815609 2724491 := bstep (se 1 (by rfl) ⟨2043368, by rfl⟩ : syracuseStep 2724491 = 4086737) B4086737
theorem B2724503 : Blo 1815609 2724503 := bstep (se 1 (by rfl) ⟨2043377, by rfl⟩ : syracuseStep 2724503 = 4086755) B4086755
theorem B8286893 : Blo 1815609 8286893 := bstep (se 3 (by rfl) ⟨1553792, by rfl⟩ : syracuseStep 8286893 = 3107585) B3107585
theorem B4141747 : Blo 1815609 4141747 := bstep (se 1 (by rfl) ⟨3106310, by rfl⟩ : syracuseStep 4141747 = 6212621) B6212621
theorem B3986135 : Blo 1815609 3986135 := bstep (se 1 (by rfl) ⟨2989601, by rfl⟩ : syracuseStep 3986135 = 5979203) B5979203
theorem B2724569 : Blo 1815609 2724569 := bstep (se 2 (by rfl) ⟨1021713, by rfl⟩ : syracuseStep 2724569 = 2043427) B2043427
theorem B2044651 : Blo 1815609 2044651 := bstep (se 1 (by rfl) ⟨1533488, by rfl⟩ : syracuseStep 2044651 = 3066977) B3066977
theorem B3273473 : Blo 1815609 3273473 := bstep (se 2 (by rfl) ⟨1227552, by rfl⟩ : syracuseStep 3273473 = 2455105) B2455105
theorem B9573137 : Blo 1815609 9573137 := bstep (se 2 (by rfl) ⟨3589926, by rfl⟩ : syracuseStep 9573137 = 7179853) B7179853
theorem B10343213 : Blo 1815609 10343213 := bstep (se 3 (by rfl) ⟨1939352, by rfl⟩ : syracuseStep 10343213 = 3878705) B3878705
theorem B3879731 : Blo 1815609 3879731 := bstep (se 1 (by rfl) ⟨2909798, by rfl⟩ : syracuseStep 3879731 = 5819597) B5819597
theorem B2724683 : Blo 1815609 2724683 := bstep (se 1 (by rfl) ⟨2043512, by rfl⟩ : syracuseStep 2724683 = 4087025) B4087025
theorem B10351435 : Blo 1815609 10351435 := bstep (se 1 (by rfl) ⟨7763576, by rfl⟩ : syracuseStep 10351435 = 15527153) B15527153
theorem B2724695 : Blo 1815609 2724695 := bstep (se 1 (by rfl) ⟨2043521, by rfl⟩ : syracuseStep 2724695 = 4087043) B4087043
theorem B2044759 : Blo 1815609 2044759 := bstep (se 1 (by rfl) ⟨1533569, by rfl⟩ : syracuseStep 2044759 = 3067139) B3067139
theorem B4911961 : Blo 1815609 4911961 := bstep (se 2 (by rfl) ⟨1841985, by rfl⟩ : syracuseStep 4911961 = 3683971) B3683971
theorem B23286629 : Blo 1815609 23286629 := bstep (se 4 (by rfl) ⟨2183121, by rfl⟩ : syracuseStep 23286629 = 4366243) B4366243
theorem B2298775 : Blo 1815609 2298775 := bstep (se 1 (by rfl) ⟨1724081, by rfl⟩ : syracuseStep 2298775 = 3448163) B3448163
theorem B2724761 : Blo 1815609 2724761 := bstep (se 2 (by rfl) ⟨1021785, by rfl⟩ : syracuseStep 2724761 = 2043571) B2043571
theorem B69874649 : Blo 1815609 69874649 := bstep (se 2 (by rfl) ⟨26202993, by rfl⟩ : syracuseStep 69874649 = 52405987) B52405987
theorem B2724875 : Blo 1815609 2724875 := bstep (se 1 (by rfl) ⟨2043656, by rfl⟩ : syracuseStep 2724875 = 4087313) B4087313
theorem B1089483797 : Blo 1815609 1089483797 := bstep (se 6 (by rfl) ⟨25534776, by rfl⟩ : syracuseStep 1089483797 = 51069553) B51069553
theorem B2724887 : Blo 1815609 2724887 := bstep (se 1 (by rfl) ⟨2043665, by rfl⟩ : syracuseStep 2724887 = 4087331) B4087331
theorem B1815627 : Blo 1815609 1815627 := bstep (se 1 (by rfl) ⟨1361720, by rfl⟩ : syracuseStep 1815627 = 2723441) B2723441
theorem B1815639 : Blo 1815609 1815639 := bstep (se 1 (by rfl) ⟨1361729, by rfl⟩ : syracuseStep 1815639 = 2723459) B2723459
theorem B2724953 : Blo 1815609 2724953 := bstep (se 2 (by rfl) ⟨1021857, by rfl⟩ : syracuseStep 2724953 = 2043715) B2043715
theorem B10351709 : Blo 1815609 10351709 := bstep (se 3 (by rfl) ⟨1940945, by rfl⟩ : syracuseStep 10351709 = 3881891) B3881891
theorem B1815659 : Blo 1815609 1815659 := bstep (se 1 (by rfl) ⟨1361744, by rfl⟩ : syracuseStep 1815659 = 2723489) B2723489
theorem B1815671 : Blo 1815609 1815671 := bstep (se 1 (by rfl) ⟨1361753, by rfl⟩ : syracuseStep 1815671 = 2723507) B2723507
theorem B1815691 : Blo 1815609 1815691 := bstep (se 1 (by rfl) ⟨1361768, by rfl⟩ : syracuseStep 1815691 = 2723537) B2723537
theorem B1815703 : Blo 1815609 1815703 := bstep (se 1 (by rfl) ⟨1361777, by rfl⟩ : syracuseStep 1815703 = 2723555) B2723555
theorem B6132887 : Blo 1815609 6132887 := bstep (se 1 (by rfl) ⟨4599665, by rfl⟩ : syracuseStep 6132887 = 9199331) B9199331
theorem B1815723 : Blo 1815609 1815723 := bstep (se 1 (by rfl) ⟨1361792, by rfl⟩ : syracuseStep 1815723 = 2723585) B2723585
theorem B1815735 : Blo 1815609 1815735 := bstep (se 1 (by rfl) ⟨1361801, by rfl⟩ : syracuseStep 1815735 = 2723603) B2723603
theorem B1815755 : Blo 1815609 1815755 := bstep (se 1 (by rfl) ⟨1361816, by rfl⟩ : syracuseStep 1815755 = 2723633) B2723633
theorem B2725067 : Blo 1815609 2725067 := bstep (se 1 (by rfl) ⟨2043800, by rfl⟩ : syracuseStep 2725067 = 4087601) B4087601
theorem B1815767 : Blo 1815609 1815767 := bstep (se 1 (by rfl) ⟨1361825, by rfl⟩ : syracuseStep 1815767 = 2723651) B2723651
theorem B2725079 : Blo 1815609 2725079 := bstep (se 1 (by rfl) ⟨2043809, by rfl⟩ : syracuseStep 2725079 = 4087619) B4087619
theorem B1815787 : Blo 1815609 1815787 := bstep (se 1 (by rfl) ⟨1361840, by rfl⟩ : syracuseStep 1815787 = 2723681) B2723681
theorem B1815799 : Blo 1815609 1815799 := bstep (se 1 (by rfl) ⟨1361849, by rfl⟩ : syracuseStep 1815799 = 2723699) B2723699
theorem B1815819 : Blo 1815609 1815819 := bstep (se 1 (by rfl) ⟨1361864, by rfl⟩ : syracuseStep 1815819 = 2723729) B2723729
theorem B1815831 : Blo 1815609 1815831 := bstep (se 1 (by rfl) ⟨1361873, by rfl⟩ : syracuseStep 1815831 = 2723747) B2723747
theorem B2725145 : Blo 1815609 2725145 := bstep (se 2 (by rfl) ⟨1021929, by rfl⟩ : syracuseStep 2725145 = 2043859) B2043859
theorem B3880217 : Blo 1815609 3880217 := bstep (se 2 (by rfl) ⟨1455081, by rfl⟩ : syracuseStep 3880217 = 2910163) B2910163
theorem B1815851 : Blo 1815609 1815851 := bstep (se 1 (by rfl) ⟨1361888, by rfl⟩ : syracuseStep 1815851 = 2723777) B2723777
theorem B5174579 : Blo 1815609 5174579 := bstep (se 1 (by rfl) ⟨3880934, by rfl⟩ : syracuseStep 5174579 = 7761869) B7761869
theorem B1815863 : Blo 1815609 1815863 := bstep (se 1 (by rfl) ⟨1361897, by rfl⟩ : syracuseStep 1815863 = 2723795) B2723795
theorem B1815883 : Blo 1815609 1815883 := bstep (se 1 (by rfl) ⟨1361912, by rfl⟩ : syracuseStep 1815883 = 2723825) B2723825
theorem B1815895 : Blo 1815609 1815895 := bstep (se 1 (by rfl) ⟨1361921, by rfl⟩ : syracuseStep 1815895 = 2723843) B2723843
theorem B1815915 : Blo 1815609 1815915 := bstep (se 1 (by rfl) ⟨1361936, by rfl⟩ : syracuseStep 1815915 = 2723873) B2723873
theorem B1815927 : Blo 1815609 1815927 := bstep (se 1 (by rfl) ⟨1361945, by rfl⟩ : syracuseStep 1815927 = 2723891) B2723891
theorem B1815947 : Blo 1815609 1815947 := bstep (se 1 (by rfl) ⟨1361960, by rfl⟩ : syracuseStep 1815947 = 2723921) B2723921
theorem B2725259 : Blo 1815609 2725259 := bstep (se 1 (by rfl) ⟨2043944, by rfl⟩ : syracuseStep 2725259 = 4087889) B4087889
theorem B1815959 : Blo 1815609 1815959 := bstep (se 1 (by rfl) ⟨1361969, by rfl⟩ : syracuseStep 1815959 = 2723939) B2723939
theorem B2725271 : Blo 1815609 2725271 := bstep (se 1 (by rfl) ⟨2043953, by rfl⟩ : syracuseStep 2725271 = 4087907) B4087907
theorem B1815979 : Blo 1815609 1815979 := bstep (se 1 (by rfl) ⟨1361984, by rfl⟩ : syracuseStep 1815979 = 2723969) B2723969
theorem B4085171 : Blo 1815609 4085171 := bstep (se 1 (by rfl) ⟨3063878, by rfl⟩ : syracuseStep 4085171 = 6127757) B6127757
theorem B1815991 : Blo 1815609 1815991 := bstep (se 1 (by rfl) ⟨1361993, by rfl⟩ : syracuseStep 1815991 = 2723987) B2723987
theorem B1816011 : Blo 1815609 1816011 := bstep (se 1 (by rfl) ⟨1362008, by rfl⟩ : syracuseStep 1816011 = 2724017) B2724017
theorem B4085207 : Blo 1815609 4085207 := bstep (se 1 (by rfl) ⟨3063905, by rfl⟩ : syracuseStep 4085207 = 6127811) B6127811
theorem B1816023 : Blo 1815609 1816023 := bstep (se 1 (by rfl) ⟨1362017, by rfl⟩ : syracuseStep 1816023 = 2724035) B2724035
theorem B2725337 : Blo 1815609 2725337 := bstep (se 2 (by rfl) ⟨1022001, by rfl⟩ : syracuseStep 2725337 = 2044003) B2044003
theorem B1816043 : Blo 1815609 1816043 := bstep (se 1 (by rfl) ⟨1362032, by rfl⟩ : syracuseStep 1816043 = 2724065) B2724065
theorem B1816055 : Blo 1815609 1816055 := bstep (se 1 (by rfl) ⟨1362041, by rfl⟩ : syracuseStep 1816055 = 2724083) B2724083
theorem B1816075 : Blo 1815609 1816075 := bstep (se 1 (by rfl) ⟨1362056, by rfl⟩ : syracuseStep 1816075 = 2724113) B2724113
theorem B1816087 : Blo 1815609 1816087 := bstep (se 1 (by rfl) ⟨1362065, by rfl⟩ : syracuseStep 1816087 = 2724131) B2724131
theorem B1816107 : Blo 1815609 1816107 := bstep (se 1 (by rfl) ⟨1362080, by rfl⟩ : syracuseStep 1816107 = 2724161) B2724161
theorem B1816119 : Blo 1815609 1816119 := bstep (se 1 (by rfl) ⟨1362089, by rfl⟩ : syracuseStep 1816119 = 2724179) B2724179
theorem B1816139 : Blo 1815609 1816139 := bstep (se 1 (by rfl) ⟨1362104, by rfl⟩ : syracuseStep 1816139 = 2724209) B2724209
theorem B2725451 : Blo 1815609 2725451 := bstep (se 1 (by rfl) ⟨2044088, by rfl⟩ : syracuseStep 2725451 = 4088177) B4088177
theorem B1816151 : Blo 1815609 1816151 := bstep (se 1 (by rfl) ⟨1362113, by rfl⟩ : syracuseStep 1816151 = 2724227) B2724227
theorem B2725463 : Blo 1815609 2725463 := bstep (se 1 (by rfl) ⟨2044097, by rfl⟩ : syracuseStep 2725463 = 4088195) B4088195
theorem B15521381 : Blo 1815609 15521381 := bstep (se 4 (by rfl) ⟨1455129, by rfl⟩ : syracuseStep 15521381 = 2910259) B2910259
theorem B1816171 : Blo 1815609 1816171 := bstep (se 1 (by rfl) ⟨1362128, by rfl⟩ : syracuseStep 1816171 = 2724257) B2724257
theorem B1816183 : Blo 1815609 1816183 := bstep (se 1 (by rfl) ⟨1362137, by rfl⟩ : syracuseStep 1816183 = 2724275) B2724275
theorem B4085387 : Blo 1815609 4085387 := bstep (se 1 (by rfl) ⟨3064040, by rfl⟩ : syracuseStep 4085387 = 6128081) B6128081
theorem B1816203 : Blo 1815609 1816203 := bstep (se 1 (by rfl) ⟨1362152, by rfl⟩ : syracuseStep 1816203 = 2724305) B2724305
theorem B1816215 : Blo 1815609 1816215 := bstep (se 1 (by rfl) ⟨1362161, by rfl⟩ : syracuseStep 1816215 = 2724323) B2724323
theorem B2725529 : Blo 1815609 2725529 := bstep (se 2 (by rfl) ⟨1022073, by rfl⟩ : syracuseStep 2725529 = 2044147) B2044147
theorem B1816235 : Blo 1815609 1816235 := bstep (se 1 (by rfl) ⟨1362176, by rfl⟩ : syracuseStep 1816235 = 2724353) B2724353
theorem B6895277 : Blo 1815609 6895277 := bstep (se 3 (by rfl) ⟨1292864, by rfl⟩ : syracuseStep 6895277 = 2585729) B2585729
theorem B4142771 : Blo 1815609 4142771 := bstep (se 1 (by rfl) ⟨3107078, by rfl⟩ : syracuseStep 4142771 = 6214157) B6214157
theorem B6133427 : Blo 1815609 6133427 := bstep (se 1 (by rfl) ⟨4600070, by rfl⟩ : syracuseStep 6133427 = 9200141) B9200141
theorem B1816247 : Blo 1815609 1816247 := bstep (se 1 (by rfl) ⟨1362185, by rfl⟩ : syracuseStep 1816247 = 2724371) B2724371
theorem B4085441 : Blo 1815609 4085441 := bstep (se 2 (by rfl) ⟨1532040, by rfl⟩ : syracuseStep 4085441 = 3064081) B3064081
theorem B6895307 : Blo 1815609 6895307 := bstep (se 1 (by rfl) ⟨5171480, by rfl⟩ : syracuseStep 6895307 = 10342961) B10342961
theorem B1816267 : Blo 1815609 1816267 := bstep (se 1 (by rfl) ⟨1362200, by rfl⟩ : syracuseStep 1816267 = 2724401) B2724401
theorem B1816279 : Blo 1815609 1816279 := bstep (se 1 (by rfl) ⟨1362209, by rfl⟩ : syracuseStep 1816279 = 2724419) B2724419
theorem B1816299 : Blo 1815609 1816299 := bstep (se 1 (by rfl) ⟨1362224, by rfl⟩ : syracuseStep 1816299 = 2724449) B2724449
theorem B1816311 : Blo 1815609 1816311 := bstep (se 1 (by rfl) ⟨1362233, by rfl⟩ : syracuseStep 1816311 = 2724467) B2724467
theorem B1816331 : Blo 1815609 1816331 := bstep (se 1 (by rfl) ⟨1362248, by rfl⟩ : syracuseStep 1816331 = 2724497) B2724497
theorem B2725643 : Blo 1815609 2725643 := bstep (se 1 (by rfl) ⟨2044232, by rfl⟩ : syracuseStep 2725643 = 4088465) B4088465
theorem B2488087 : Blo 1815609 2488087 := bstep (se 1 (by rfl) ⟨1866065, by rfl⟩ : syracuseStep 2488087 = 3732131) B3732131
theorem B1816343 : Blo 1815609 1816343 := bstep (se 1 (by rfl) ⟨1362257, by rfl⟩ : syracuseStep 1816343 = 2724515) B2724515
theorem B2725655 : Blo 1815609 2725655 := bstep (se 1 (by rfl) ⟨2044241, by rfl⟩ : syracuseStep 2725655 = 4088483) B4088483
theorem B1816363 : Blo 1815609 1816363 := bstep (se 1 (by rfl) ⟨1362272, by rfl⟩ : syracuseStep 1816363 = 2724545) B2724545
theorem B8730413 : Blo 1815609 8730413 := bstep (se 3 (by rfl) ⟨1636952, by rfl⟩ : syracuseStep 8730413 = 3273905) B3273905
theorem B1816375 : Blo 1815609 1816375 := bstep (se 1 (by rfl) ⟨1362281, by rfl⟩ : syracuseStep 1816375 = 2724563) B2724563
theorem B5822273 : Blo 1815609 5822273 := bstep (se 2 (by rfl) ⟨2183352, by rfl⟩ : syracuseStep 5822273 = 4366705) B4366705
theorem B1816395 : Blo 1815609 1816395 := bstep (se 1 (by rfl) ⟨1362296, by rfl⟩ : syracuseStep 1816395 = 2724593) B2724593
theorem B9197387 : Blo 1815609 9197387 := bstep (se 1 (by rfl) ⟨6898040, by rfl⟩ : syracuseStep 9197387 = 13796081) B13796081
theorem B1816407 : Blo 1815609 1816407 := bstep (se 1 (by rfl) ⟨1362305, by rfl⟩ : syracuseStep 1816407 = 2724611) B2724611
theorem B2725721 : Blo 1815609 2725721 := bstep (se 2 (by rfl) ⟨1022145, by rfl⟩ : syracuseStep 2725721 = 2044291) B2044291
theorem B1816427 : Blo 1815609 1816427 := bstep (se 1 (by rfl) ⟨1362320, by rfl⟩ : syracuseStep 1816427 = 2724641) B2724641
theorem B1816439 : Blo 1815609 1816439 := bstep (se 1 (by rfl) ⟨1362329, by rfl⟩ : syracuseStep 1816439 = 2724659) B2724659
theorem B1816459 : Blo 1815609 1816459 := bstep (se 1 (by rfl) ⟨1362344, by rfl⟩ : syracuseStep 1816459 = 2724689) B2724689
theorem B1816471 : Blo 1815609 1816471 := bstep (se 1 (by rfl) ⟨1362353, by rfl⟩ : syracuseStep 1816471 = 2724707) B2724707
theorem B14931863 : Blo 1815609 14931863 := bstep (se 1 (by rfl) ⟨11198897, by rfl⟩ : syracuseStep 14931863 = 22397795) B22397795
theorem B4085657 : Blo 1815609 4085657 := bstep (se 2 (by rfl) ⟨1532121, by rfl⟩ : syracuseStep 4085657 = 3064243) B3064243
theorem B1816491 : Blo 1815609 1816491 := bstep (se 1 (by rfl) ⟨1362368, by rfl⟩ : syracuseStep 1816491 = 2724737) B2724737
theorem B1816503 : Blo 1815609 1816503 := bstep (se 1 (by rfl) ⟨1362377, by rfl⟩ : syracuseStep 1816503 = 2724755) B2724755
theorem B6133697 : Blo 1815609 6133697 := bstep (se 2 (by rfl) ⟨2300136, by rfl⟩ : syracuseStep 6133697 = 4600273) B4600273
theorem B1816523 : Blo 1815609 1816523 := bstep (se 1 (by rfl) ⟨1362392, by rfl⟩ : syracuseStep 1816523 = 2724785) B2724785
theorem B2725835 : Blo 1815609 2725835 := bstep (se 1 (by rfl) ⟨2044376, by rfl⟩ : syracuseStep 2725835 = 4088753) B4088753
theorem B1816535 : Blo 1815609 1816535 := bstep (se 1 (by rfl) ⟨1362401, by rfl⟩ : syracuseStep 1816535 = 2724803) B2724803
theorem B2586583 : Blo 1815609 2586583 := bstep (se 1 (by rfl) ⟨1939937, by rfl⟩ : syracuseStep 2586583 = 3879875) B3879875
theorem B2725847 : Blo 1815609 2725847 := bstep (se 1 (by rfl) ⟨2044385, by rfl⟩ : syracuseStep 2725847 = 4088771) B4088771
theorem B1816555 : Blo 1815609 1816555 := bstep (se 1 (by rfl) ⟨1362416, by rfl⟩ : syracuseStep 1816555 = 2724833) B2724833
theorem B4085747 : Blo 1815609 4085747 := bstep (se 1 (by rfl) ⟨3064310, by rfl⟩ : syracuseStep 4085747 = 6128621) B6128621
theorem B1816567 : Blo 1815609 1816567 := bstep (se 1 (by rfl) ⟨1362425, by rfl⟩ : syracuseStep 1816567 = 2724851) B2724851
theorem B1816587 : Blo 1815609 1816587 := bstep (se 1 (by rfl) ⟨1362440, by rfl⟩ : syracuseStep 1816587 = 2724881) B2724881
theorem B13088785 : Blo 1815609 13088785 := bstep (se 2 (by rfl) ⟨4908294, by rfl⟩ : syracuseStep 13088785 = 9816589) B9816589
theorem B8730641 : Blo 1815609 8730641 := bstep (se 2 (by rfl) ⟨3273990, by rfl⟩ : syracuseStep 8730641 = 6547981) B6547981
theorem B4085783 : Blo 1815609 4085783 := bstep (se 1 (by rfl) ⟨3064337, by rfl⟩ : syracuseStep 4085783 = 6128675) B6128675
theorem B1816599 : Blo 1815609 1816599 := bstep (se 1 (by rfl) ⟨1362449, by rfl⟩ : syracuseStep 1816599 = 2724899) B2724899
theorem B2725913 : Blo 1815609 2725913 := bstep (se 2 (by rfl) ⟨1022217, by rfl⟩ : syracuseStep 2725913 = 2044435) B2044435
theorem B1816619 : Blo 1815609 1816619 := bstep (se 1 (by rfl) ⟨1362464, by rfl⟩ : syracuseStep 1816619 = 2724929) B2724929
theorem B7755821 : Blo 1815609 7755821 := bstep (se 3 (by rfl) ⟨1454216, by rfl⟩ : syracuseStep 7755821 = 2908433) B2908433
theorem B1816631 : Blo 1815609 1816631 := bstep (se 1 (by rfl) ⟨1362473, by rfl⟩ : syracuseStep 1816631 = 2724947) B2724947
theorem B3446849 : Blo 1815609 3446849 := bstep (se 2 (by rfl) ⟨1292568, by rfl⟩ : syracuseStep 3446849 = 2585137) B2585137
theorem B1816651 : Blo 1815609 1816651 := bstep (se 1 (by rfl) ⟨1362488, by rfl⟩ : syracuseStep 1816651 = 2724977) B2724977
theorem B1816663 : Blo 1815609 1816663 := bstep (se 1 (by rfl) ⟨1362497, by rfl⟩ : syracuseStep 1816663 = 2724995) B2724995
theorem B1816683 : Blo 1815609 1816683 := bstep (se 1 (by rfl) ⟨1362512, by rfl⟩ : syracuseStep 1816683 = 2725025) B2725025
theorem B1816695 : Blo 1815609 1816695 := bstep (se 1 (by rfl) ⟨1362521, by rfl⟩ : syracuseStep 1816695 = 2725043) B2725043
theorem B1816715 : Blo 1815609 1816715 := bstep (se 1 (by rfl) ⟨1362536, by rfl⟩ : syracuseStep 1816715 = 2725073) B2725073
theorem B2726027 : Blo 1815609 2726027 := bstep (se 1 (by rfl) ⟨2044520, by rfl⟩ : syracuseStep 2726027 = 4089041) B4089041
theorem B1816727 : Blo 1815609 1816727 := bstep (se 1 (by rfl) ⟨1362545, by rfl⟩ : syracuseStep 1816727 = 2725091) B2725091
theorem B2726039 : Blo 1815609 2726039 := bstep (se 1 (by rfl) ⟨2044529, by rfl⟩ : syracuseStep 2726039 = 4089059) B4089059
theorem B2455705 : Blo 1815609 2455705 := bstep (se 2 (by rfl) ⟨920889, by rfl⟩ : syracuseStep 2455705 = 1841779) B1841779
theorem B1816747 : Blo 1815609 1816747 := bstep (se 1 (by rfl) ⟨1362560, by rfl⟩ : syracuseStep 1816747 = 2725121) B2725121
theorem B1816759 : Blo 1815609 1816759 := bstep (se 1 (by rfl) ⟨1362569, by rfl⟩ : syracuseStep 1816759 = 2725139) B2725139
theorem B4085963 : Blo 1815609 4085963 := bstep (se 1 (by rfl) ⟨3064472, by rfl⟩ : syracuseStep 4085963 = 6128945) B6128945
theorem B1816779 : Blo 1815609 1816779 := bstep (se 1 (by rfl) ⟨1362584, by rfl⟩ : syracuseStep 1816779 = 2725169) B2725169
theorem B1816791 : Blo 1815609 1816791 := bstep (se 1 (by rfl) ⟨1362593, by rfl⟩ : syracuseStep 1816791 = 2725187) B2725187
theorem B2726105 : Blo 1815609 2726105 := bstep (se 2 (by rfl) ⟨1022289, by rfl⟩ : syracuseStep 2726105 = 2044579) B2044579
theorem B1816811 : Blo 1815609 1816811 := bstep (se 1 (by rfl) ⟨1362608, by rfl⟩ : syracuseStep 1816811 = 2725217) B2725217
theorem B1816823 : Blo 1815609 1816823 := bstep (se 1 (by rfl) ⟨1362617, by rfl⟩ : syracuseStep 1816823 = 2725235) B2725235
theorem B4086017 : Blo 1815609 4086017 := bstep (se 2 (by rfl) ⟨1532256, by rfl⟩ : syracuseStep 4086017 = 3064513) B3064513
theorem B1816843 : Blo 1815609 1816843 := bstep (se 1 (by rfl) ⟨1362632, by rfl⟩ : syracuseStep 1816843 = 2725265) B2725265
theorem B1816855 : Blo 1815609 1816855 := bstep (se 1 (by rfl) ⟨1362641, by rfl⟩ : syracuseStep 1816855 = 2725283) B2725283
theorem B1816875 : Blo 1815609 1816875 := bstep (se 1 (by rfl) ⟨1362656, by rfl⟩ : syracuseStep 1816875 = 2725313) B2725313
theorem B1816887 : Blo 1815609 1816887 := bstep (se 1 (by rfl) ⟨1362665, by rfl⟩ : syracuseStep 1816887 = 2725331) B2725331
theorem B1816907 : Blo 1815609 1816907 := bstep (se 1 (by rfl) ⟨1362680, by rfl⟩ : syracuseStep 1816907 = 2725361) B2725361
theorem B2726219 : Blo 1815609 2726219 := bstep (se 1 (by rfl) ⟨2044664, by rfl⟩ : syracuseStep 2726219 = 4089329) B4089329
theorem B1816919 : Blo 1815609 1816919 := bstep (se 1 (by rfl) ⟨1362689, by rfl⟩ : syracuseStep 1816919 = 2725379) B2725379
theorem B2726231 : Blo 1815609 2726231 := bstep (se 1 (by rfl) ⟨2044673, by rfl⟩ : syracuseStep 2726231 = 4089347) B4089347
theorem B6895961 : Blo 1815609 6895961 := bstep (se 2 (by rfl) ⟨2585985, by rfl⟩ : syracuseStep 6895961 = 5171971) B5171971
theorem B1816939 : Blo 1815609 1816939 := bstep (se 1 (by rfl) ⟨1362704, by rfl⟩ : syracuseStep 1816939 = 2725409) B2725409
theorem B1816951 : Blo 1815609 1816951 := bstep (se 1 (by rfl) ⟨1362713, by rfl⟩ : syracuseStep 1816951 = 2725427) B2725427
theorem B1816971 : Blo 1815609 1816971 := bstep (se 1 (by rfl) ⟨1362728, by rfl⟩ : syracuseStep 1816971 = 2725457) B2725457
theorem B3447191 : Blo 1815609 3447191 := bstep (se 1 (by rfl) ⟨2585393, by rfl⟩ : syracuseStep 3447191 = 5170787) B5170787
theorem B1816983 : Blo 1815609 1816983 := bstep (se 1 (by rfl) ⟨1362737, by rfl⟩ : syracuseStep 1816983 = 2725475) B2725475
theorem B2726297 : Blo 1815609 2726297 := bstep (se 2 (by rfl) ⟨1022361, by rfl⟩ : syracuseStep 2726297 = 2044723) B2044723
theorem B1817003 : Blo 1815609 1817003 := bstep (se 1 (by rfl) ⟨1362752, by rfl⟩ : syracuseStep 1817003 = 2725505) B2725505
theorem B20683187 : Blo 1815609 20683187 := bstep (se 1 (by rfl) ⟨15512390, by rfl⟩ : syracuseStep 20683187 = 31024781) B31024781
theorem B1817015 : Blo 1815609 1817015 := bstep (se 1 (by rfl) ⟨1362761, by rfl⟩ : syracuseStep 1817015 = 2725523) B2725523
theorem B1817035 : Blo 1815609 1817035 := bstep (se 1 (by rfl) ⟨1362776, by rfl⟩ : syracuseStep 1817035 = 2725553) B2725553
theorem B1817047 : Blo 1815609 1817047 := bstep (se 1 (by rfl) ⟨1362785, by rfl⟩ : syracuseStep 1817047 = 2725571) B2725571
theorem B4086233 : Blo 1815609 4086233 := bstep (se 2 (by rfl) ⟨1532337, by rfl⟩ : syracuseStep 4086233 = 3064675) B3064675
theorem B6134237 : Blo 1815609 6134237 := bstep (se 3 (by rfl) ⟨1150169, by rfl⟩ : syracuseStep 6134237 = 2300339) B2300339
theorem B1817067 : Blo 1815609 1817067 := bstep (se 1 (by rfl) ⟨1362800, by rfl⟩ : syracuseStep 1817067 = 2725601) B2725601
theorem B1817079 : Blo 1815609 1817079 := bstep (se 1 (by rfl) ⟨1362809, by rfl⟩ : syracuseStep 1817079 = 2725619) B2725619
theorem B1817099 : Blo 1815609 1817099 := bstep (se 1 (by rfl) ⟨1362824, by rfl⟩ : syracuseStep 1817099 = 2725649) B2725649
theorem B2726411 : Blo 1815609 2726411 := bstep (se 1 (by rfl) ⟨2044808, by rfl⟩ : syracuseStep 2726411 = 4089617) B4089617
theorem B1817111 : Blo 1815609 1817111 := bstep (se 1 (by rfl) ⟨1362833, by rfl⟩ : syracuseStep 1817111 = 2725667) B2725667
theorem B1817131 : Blo 1815609 1817131 := bstep (se 1 (by rfl) ⟨1362848, by rfl⟩ : syracuseStep 1817131 = 2725697) B2725697
theorem B4086323 : Blo 1815609 4086323 := bstep (se 1 (by rfl) ⟨3064742, by rfl⟩ : syracuseStep 4086323 = 6129485) B6129485
theorem B1817143 : Blo 1815609 1817143 := bstep (se 1 (by rfl) ⟨1362857, by rfl⟩ : syracuseStep 1817143 = 2725715) B2725715
theorem B1817163 : Blo 1815609 1817163 := bstep (se 1 (by rfl) ⟨1362872, by rfl⟩ : syracuseStep 1817163 = 2725745) B2725745
theorem B4086359 : Blo 1815609 4086359 := bstep (se 1 (by rfl) ⟨3064769, by rfl⟩ : syracuseStep 4086359 = 6129539) B6129539
theorem B1817175 : Blo 1815609 1817175 := bstep (se 1 (by rfl) ⟨1362881, by rfl⟩ : syracuseStep 1817175 = 2725763) B2725763
theorem B1817195 : Blo 1815609 1817195 := bstep (se 1 (by rfl) ⟨1362896, by rfl⟩ : syracuseStep 1817195 = 2725793) B2725793
theorem B1817207 : Blo 1815609 1817207 := bstep (se 1 (by rfl) ⟨1362905, by rfl⟩ : syracuseStep 1817207 = 2725811) B2725811
theorem B1817227 : Blo 1815609 1817227 := bstep (se 1 (by rfl) ⟨1362920, by rfl⟩ : syracuseStep 1817227 = 2725841) B2725841
theorem B6896279 : Blo 1815609 6896279 := bstep (se 1 (by rfl) ⟨5172209, by rfl⟩ : syracuseStep 6896279 = 10344419) B10344419
theorem B1817239 : Blo 1815609 1817239 := bstep (se 1 (by rfl) ⟨1362929, by rfl⟩ : syracuseStep 1817239 = 2725859) B2725859
theorem B1817259 : Blo 1815609 1817259 := bstep (se 1 (by rfl) ⟨1362944, by rfl⟩ : syracuseStep 1817259 = 2725889) B2725889
theorem B1817271 : Blo 1815609 1817271 := bstep (se 1 (by rfl) ⟨1362953, by rfl⟩ : syracuseStep 1817271 = 2725907) B2725907
theorem B4422347 : Blo 1815609 4422347 := bstep (se 1 (by rfl) ⟨3316760, by rfl⟩ : syracuseStep 4422347 = 6633521) B6633521
theorem B1817291 : Blo 1815609 1817291 := bstep (se 1 (by rfl) ⟨1362968, by rfl⟩ : syracuseStep 1817291 = 2725937) B2725937
theorem B1817303 : Blo 1815609 1817303 := bstep (se 1 (by rfl) ⟨1362977, by rfl⟩ : syracuseStep 1817303 = 2725955) B2725955
theorem B7756505 : Blo 1815609 7756505 := bstep (se 2 (by rfl) ⟨2908689, by rfl⟩ : syracuseStep 7756505 = 5817379) B5817379
theorem B1817323 : Blo 1815609 1817323 := bstep (se 1 (by rfl) ⟨1362992, by rfl⟩ : syracuseStep 1817323 = 2725985) B2725985
theorem B1817335 : Blo 1815609 1817335 := bstep (se 1 (by rfl) ⟨1363001, by rfl⟩ : syracuseStep 1817335 = 2726003) B2726003
theorem B4086539 : Blo 1815609 4086539 := bstep (se 1 (by rfl) ⟨3064904, by rfl⟩ : syracuseStep 4086539 = 6129809) B6129809
theorem B1817355 : Blo 1815609 1817355 := bstep (se 1 (by rfl) ⟨1363016, by rfl⟩ : syracuseStep 1817355 = 2726033) B2726033
theorem B1817367 : Blo 1815609 1817367 := bstep (se 1 (by rfl) ⟨1363025, by rfl⟩ : syracuseStep 1817367 = 2726051) B2726051
theorem B1817387 : Blo 1815609 1817387 := bstep (se 1 (by rfl) ⟨1363040, by rfl⟩ : syracuseStep 1817387 = 2726081) B2726081
theorem B1940279 : Blo 1815609 1940279 := bstep (se 1 (by rfl) ⟨1455209, by rfl⟩ : syracuseStep 1940279 = 2910419) B2910419
theorem B1817399 : Blo 1815609 1817399 := bstep (se 1 (by rfl) ⟨1363049, by rfl⟩ : syracuseStep 1817399 = 2726099) B2726099
theorem B4086593 : Blo 1815609 4086593 := bstep (se 2 (by rfl) ⟨1532472, by rfl⟩ : syracuseStep 4086593 = 3064945) B3064945
theorem B1817419 : Blo 1815609 1817419 := bstep (se 1 (by rfl) ⟨1363064, by rfl⟩ : syracuseStep 1817419 = 2726129) B2726129
theorem B1817431 : Blo 1815609 1817431 := bstep (se 1 (by rfl) ⟨1363073, by rfl⟩ : syracuseStep 1817431 = 2726147) B2726147
theorem B1817451 : Blo 1815609 1817451 := bstep (se 1 (by rfl) ⟨1363088, by rfl⟩ : syracuseStep 1817451 = 2726177) B2726177
theorem B1817463 : Blo 1815609 1817463 := bstep (se 1 (by rfl) ⟨1363097, by rfl⟩ : syracuseStep 1817463 = 2726195) B2726195
theorem B3881857 : Blo 1815609 3881857 := bstep (se 2 (by rfl) ⟨1455696, by rfl⟩ : syracuseStep 3881857 = 2911393) B2911393
theorem B1817483 : Blo 1815609 1817483 := bstep (se 1 (by rfl) ⟨1363112, by rfl⟩ : syracuseStep 1817483 = 2726225) B2726225
theorem B1817495 : Blo 1815609 1817495 := bstep (se 1 (by rfl) ⟨1363121, by rfl⟩ : syracuseStep 1817495 = 2726243) B2726243
theorem B1817515 : Blo 1815609 1817515 := bstep (se 1 (by rfl) ⟨1363136, by rfl⟩ : syracuseStep 1817515 = 2726273) B2726273
theorem B16579507 : Blo 1815609 16579507 := bstep (se 1 (by rfl) ⟨12434630, by rfl⟩ : syracuseStep 16579507 = 24869261) B24869261
theorem B1817527 : Blo 1815609 1817527 := bstep (se 1 (by rfl) ⟨1363145, by rfl⟩ : syracuseStep 1817527 = 2726291) B2726291
theorem B1817547 : Blo 1815609 1817547 := bstep (se 1 (by rfl) ⟨1363160, by rfl⟩ : syracuseStep 1817547 = 2726321) B2726321
theorem B1817559 : Blo 1815609 1817559 := bstep (se 1 (by rfl) ⟨1363169, by rfl⟩ : syracuseStep 1817559 = 2726339) B2726339
theorem B1817579 : Blo 1815609 1817579 := bstep (se 1 (by rfl) ⟨1363184, by rfl⟩ : syracuseStep 1817579 = 2726369) B2726369
theorem B1817591 : Blo 1815609 1817591 := bstep (se 1 (by rfl) ⟨1363193, by rfl⟩ : syracuseStep 1817591 = 2726387) B2726387
theorem B14736401 : Blo 1815609 14736401 := bstep (se 2 (by rfl) ⟨5526150, by rfl⟩ : syracuseStep 14736401 = 11052301) B11052301
theorem B4086809 : Blo 1815609 4086809 := bstep (se 2 (by rfl) ⟨1532553, by rfl⟩ : syracuseStep 4086809 = 3065107) B3065107
theorem B3447859 : Blo 1815609 3447859 := bstep (se 1 (by rfl) ⟨2585894, by rfl⟩ : syracuseStep 3447859 = 5171789) B5171789
theorem B4144193 : Blo 1815609 4144193 := bstep (se 2 (by rfl) ⟨1554072, by rfl⟩ : syracuseStep 4144193 = 3108145) B3108145
theorem B4086899 : Blo 1815609 4086899 := bstep (se 1 (by rfl) ⟨3065174, by rfl⟩ : syracuseStep 4086899 = 6130349) B6130349
theorem B10345603 : Blo 1815609 10345603 := bstep (se 1 (by rfl) ⟨7759202, by rfl⟩ : syracuseStep 10345603 = 15518405) B15518405
theorem B4086935 : Blo 1815609 4086935 := bstep (se 1 (by rfl) ⟨3065201, by rfl⟩ : syracuseStep 4086935 = 6130403) B6130403
theorem B2071819 : Blo 1815609 2071819 := bstep (se 1 (by rfl) ⟨1553864, by rfl⟩ : syracuseStep 2071819 = 3107729) B3107729
theorem B8289553 : Blo 1815609 8289553 := bstep (se 2 (by rfl) ⟨3108582, by rfl⟩ : syracuseStep 8289553 = 6217165) B6217165
theorem B6896947 : Blo 1815609 6896947 := bstep (se 1 (by rfl) ⟨5172710, by rfl⟩ : syracuseStep 6896947 = 10345421) B10345421
theorem B4087115 : Blo 1815609 4087115 := bstep (se 1 (by rfl) ⟨3065336, by rfl⟩ : syracuseStep 4087115 = 6130673) B6130673
theorem B8289611 : Blo 1815609 8289611 := bstep (se 1 (by rfl) ⟨6217208, by rfl⟩ : syracuseStep 8289611 = 12434417) B12434417
theorem B4087169 : Blo 1815609 4087169 := bstep (se 2 (by rfl) ⟨1532688, by rfl⟩ : syracuseStep 4087169 = 3065377) B3065377
theorem B3448307 : Blo 1815609 3448307 := bstep (se 1 (by rfl) ⟨2586230, by rfl⟩ : syracuseStep 3448307 = 5172461) B5172461
theorem B3448345 : Blo 1815609 3448345 := bstep (se 2 (by rfl) ⟨1293129, by rfl⟩ : syracuseStep 3448345 = 2586259) B2586259
theorem B9199169 : Blo 1815609 9199169 := bstep (se 2 (by rfl) ⟨3449688, by rfl⟩ : syracuseStep 9199169 = 6899377) B6899377
theorem B4087385 : Blo 1815609 4087385 := bstep (se 2 (by rfl) ⟨1532769, by rfl⟩ : syracuseStep 4087385 = 3065539) B3065539
theorem B14728805 : Blo 1815609 14728805 := bstep (se 4 (by rfl) ⟨1380825, by rfl⟩ : syracuseStep 14728805 = 2761651) B2761651
theorem B4087475 : Blo 1815609 4087475 := bstep (se 1 (by rfl) ⟨3065606, by rfl⟩ : syracuseStep 4087475 = 6131213) B6131213
theorem B6545099 : Blo 1815609 6545099 := bstep (se 1 (by rfl) ⟨4908824, by rfl⟩ : syracuseStep 6545099 = 9817649) B9817649
theorem B4087511 : Blo 1815609 4087511 := bstep (se 1 (by rfl) ⟨3065633, by rfl⟩ : syracuseStep 4087511 = 6131267) B6131267
theorem B23289605 : Blo 1815609 23289605 := bstep (se 4 (by rfl) ⟨2183400, by rfl⟩ : syracuseStep 23289605 = 4366801) B4366801
theorem B8281873 : Blo 1815609 8281873 := bstep (se 2 (by rfl) ⟨3105702, by rfl⟩ : syracuseStep 8281873 = 6211405) B6211405
theorem B14729035 : Blo 1815609 14729035 := bstep (se 1 (by rfl) ⟨11046776, by rfl⟩ : syracuseStep 14729035 = 22093553) B22093553
theorem B2072407 : Blo 1815609 2072407 := bstep (se 1 (by rfl) ⟨1554305, by rfl⟩ : syracuseStep 2072407 = 3108611) B3108611
theorem B20684645 : Blo 1815609 20684645 := bstep (se 4 (by rfl) ⟨1939185, by rfl⟩ : syracuseStep 20684645 = 3878371) B3878371
theorem B4087691 : Blo 1815609 4087691 := bstep (se 1 (by rfl) ⟨3065768, by rfl⟩ : syracuseStep 4087691 = 6131537) B6131537
theorem B4087745 : Blo 1815609 4087745 := bstep (se 2 (by rfl) ⟨1532904, by rfl⟩ : syracuseStep 4087745 = 3065809) B3065809
theorem B3448793 : Blo 1815609 3448793 := bstep (se 2 (by rfl) ⟨1293297, by rfl⟩ : syracuseStep 3448793 = 2586595) B2586595
theorem B15515671 : Blo 1815609 15515671 := bstep (se 1 (by rfl) ⟨11636753, by rfl⟩ : syracuseStep 15515671 = 23273507) B23273507
theorem B6897707 : Blo 1815609 6897707 := bstep (se 1 (by rfl) ⟨5173280, by rfl⟩ : syracuseStep 6897707 = 10346561) B10346561
theorem B7462979 : Blo 1815609 7462979 := bstep (se 1 (by rfl) ⟨5597234, by rfl⟩ : syracuseStep 7462979 = 11194469) B11194469
theorem B6127703 : Blo 1815609 6127703 := bstep (se 1 (by rfl) ⟨4595777, by rfl⟩ : syracuseStep 6127703 = 9191555) B9191555
theorem B2621575 : Blo 1815609 2621575 := bstep (se 1 (by rfl) ⟨1966181, by rfl⟩ : syracuseStep 2621575 = 3932363) B3932363
theorem B4087943 : Blo 1815609 4087943 := bstep (se 1 (by rfl) ⟨3065957, by rfl⟩ : syracuseStep 4087943 = 6131915) B6131915
theorem B9199817 : Blo 1815609 9199817 := bstep (se 2 (by rfl) ⟨3449931, by rfl⟩ : syracuseStep 9199817 = 6899863) B6899863
theorem B8732873 : Blo 1815609 8732873 := bstep (se 2 (by rfl) ⟨3274827, by rfl⟩ : syracuseStep 8732873 = 6549655) B6549655
theorem B4596011 : Blo 1815609 4596011 := bstep (se 1 (by rfl) ⟨3447008, by rfl⟩ : syracuseStep 4596011 = 6894017) B6894017
theorem B4088123 : Blo 1815609 4088123 := bstep (se 1 (by rfl) ⟨3066092, by rfl⟩ : syracuseStep 4088123 = 6132185) B6132185
theorem B20693393 : Blo 1815609 20693393 := bstep (se 2 (by rfl) ⟨7760022, by rfl⟩ : syracuseStep 20693393 = 15520045) B15520045
theorem B4088249 : Blo 1815609 4088249 := bstep (se 2 (by rfl) ⟨1533093, by rfl⟩ : syracuseStep 4088249 = 3066187) B3066187
theorem B6382091 : Blo 1815609 6382091 := bstep (se 1 (by rfl) ⟨4786568, by rfl⟩ : syracuseStep 6382091 = 9573137) B9573137
theorem B6128189 : Blo 1815609 6128189 := bstep (se 3 (by rfl) ⟨1149035, by rfl⟩ : syracuseStep 6128189 = 2298071) B2298071
theorem B15524419 : Blo 1815609 15524419 := bstep (se 1 (by rfl) ⟨11643314, by rfl⟩ : syracuseStep 15524419 = 23286629) B23286629
theorem B3064439 : Blo 1815609 3064439 := bstep (se 1 (by rfl) ⟨2298329, by rfl⟩ : syracuseStep 3064439 = 4596659) B4596659
theorem B17465975 : Blo 1815609 17465975 := bstep (se 1 (by rfl) ⟨13099481, by rfl⟩ : syracuseStep 17465975 = 26198963) B26198963
theorem B4088591 : Blo 1815609 4088591 := bstep (se 1 (by rfl) ⟨3066443, by rfl⟩ : syracuseStep 4088591 = 6132887) B6132887
theorem B4088609 : Blo 1815609 4088609 := bstep (se 2 (by rfl) ⟨1533228, by rfl⟩ : syracuseStep 4088609 = 3066457) B3066457
theorem B3449719 : Blo 1815609 3449719 := bstep (se 1 (by rfl) ⟨2587289, by rfl⟩ : syracuseStep 3449719 = 5174579) B5174579
theorem B5522329 : Blo 1815609 5522329 := bstep (se 2 (by rfl) ⟨2070873, by rfl⟩ : syracuseStep 5522329 = 4141747) B4141747
theorem B3064891 : Blo 1815609 3064891 := bstep (se 1 (by rfl) ⟨2298668, by rfl⟩ : syracuseStep 3064891 = 4597337) B4597337
theorem B10347587 : Blo 1815609 10347587 := bstep (se 1 (by rfl) ⟨7760690, by rfl⟩ : syracuseStep 10347587 = 15521381) B15521381
theorem B4596851 : Blo 1815609 4596851 := bstep (se 1 (by rfl) ⟨3447638, by rfl⟩ : syracuseStep 4596851 = 6895277) B6895277
theorem B2761847 : Blo 1815609 2761847 := bstep (se 1 (by rfl) ⟨2071385, by rfl⟩ : syracuseStep 2761847 = 4142771) B4142771
theorem B4088951 : Blo 1815609 4088951 := bstep (se 1 (by rfl) ⟨3066713, by rfl⟩ : syracuseStep 4088951 = 6133427) B6133427
theorem B4596871 : Blo 1815609 4596871 := bstep (se 1 (by rfl) ⟨3447653, by rfl⟩ : syracuseStep 4596871 = 6895307) B6895307
theorem B3065033 : Blo 1815609 3065033 := bstep (se 2 (by rfl) ⟨1149387, by rfl⟩ : syracuseStep 3065033 = 2298775) B2298775
theorem B9954575 : Blo 1815609 9954575 := bstep (se 1 (by rfl) ⟨7465931, by rfl⟩ : syracuseStep 9954575 = 14931863) B14931863
theorem B4089131 : Blo 1815609 4089131 := bstep (se 1 (by rfl) ⟨3066848, by rfl⟩ : syracuseStep 4089131 = 6133697) B6133697
theorem B5170547 : Blo 1815609 5170547 := bstep (se 1 (by rfl) ⟨3877910, by rfl⟩ : syracuseStep 5170547 = 7755821) B7755821
theorem B9192851 : Blo 1815609 9192851 := bstep (se 1 (by rfl) ⟨6894638, by rfl⟩ : syracuseStep 9192851 = 13789277) B13789277
theorem B4597145 : Blo 1815609 4597145 := bstep (se 2 (by rfl) ⟨1723929, by rfl⟩ : syracuseStep 4597145 = 3447859) B3447859
theorem B5899787 : Blo 1815609 5899787 := bstep (se 1 (by rfl) ⟨4424840, by rfl⟩ : syracuseStep 5899787 = 8849681) B8849681
theorem B4597307 : Blo 1815609 4597307 := bstep (se 1 (by rfl) ⟨3447980, by rfl⟩ : syracuseStep 4597307 = 6895961) B6895961
theorem B13788791 : Blo 1815609 13788791 := bstep (se 1 (by rfl) ⟨10341593, by rfl⟩ : syracuseStep 13788791 = 20683187) B20683187
theorem B4089491 : Blo 1815609 4089491 := bstep (se 1 (by rfl) ⟨3067118, by rfl⟩ : syracuseStep 4089491 = 6134237) B6134237
theorem B2909881 : Blo 1815609 2909881 := bstep (se 2 (by rfl) ⟨1091205, by rfl⟩ : syracuseStep 2909881 = 2182411) B2182411
theorem B2762425 : Blo 1815609 2762425 := bstep (se 2 (by rfl) ⟨1035909, by rfl⟩ : syracuseStep 2762425 = 2071819) B2071819
theorem B11052737 : Blo 1815609 11052737 := bstep (se 2 (by rfl) ⟨4144776, by rfl⟩ : syracuseStep 11052737 = 8289553) B8289553
theorem B4089545 : Blo 1815609 4089545 := bstep (se 2 (by rfl) ⟨1533579, by rfl⟩ : syracuseStep 4089545 = 3067159) B3067159
theorem B7759597 : Blo 1815609 7759597 := bstep (se 3 (by rfl) ⟨1454924, by rfl⟩ : syracuseStep 7759597 = 2909849) B2909849
theorem B4597519 : Blo 1815609 4597519 := bstep (se 1 (by rfl) ⟨3448139, by rfl⟩ : syracuseStep 4597519 = 6896279) B6896279
theorem B5171003 : Blo 1815609 5171003 := bstep (se 1 (by rfl) ⟨3878252, by rfl⟩ : syracuseStep 5171003 = 7756505) B7756505
theorem B3065735 : Blo 1815609 3065735 := bstep (se 1 (by rfl) ⟨2299301, by rfl⟩ : syracuseStep 3065735 = 4598603) B4598603
theorem B6211475 : Blo 1815609 6211475 := bstep (se 1 (by rfl) ⟨4658606, by rfl⟩ : syracuseStep 6211475 = 9317213) B9317213
theorem B6129593 : Blo 1815609 6129593 := bstep (se 2 (by rfl) ⟨2298597, by rfl⟩ : syracuseStep 6129593 = 4597195) B4597195
theorem B9824267 : Blo 1815609 9824267 := bstep (se 1 (by rfl) ⟨7368200, by rfl⟩ : syracuseStep 9824267 = 14736401) B14736401
theorem B4597793 : Blo 1815609 4597793 := bstep (se 2 (by rfl) ⟨1724172, by rfl⟩ : syracuseStep 4597793 = 3448345) B3448345
theorem B2762795 : Blo 1815609 2762795 := bstep (se 1 (by rfl) ⟨2072096, by rfl⟩ : syracuseStep 2762795 = 4144193) B4144193
theorem B19638713 : Blo 1815609 19638713 := bstep (se 2 (by rfl) ⟨7364517, by rfl⟩ : syracuseStep 19638713 = 14729035) B14729035
theorem B2763209 : Blo 1815609 2763209 := bstep (se 2 (by rfl) ⟨1036203, by rfl⟩ : syracuseStep 2763209 = 2072407) B2072407
theorem B15526403 : Blo 1815609 15526403 := bstep (se 1 (by rfl) ⟨11644802, by rfl⟩ : syracuseStep 15526403 = 23289605) B23289605
theorem B6130187 : Blo 1815609 6130187 := bstep (se 1 (by rfl) ⟨4597640, by rfl⟩ : syracuseStep 6130187 = 9195281) B9195281
theorem B3066383 : Blo 1815609 3066383 := bstep (se 1 (by rfl) ⟨2299787, by rfl⟩ : syracuseStep 3066383 = 4599575) B4599575
theorem B13789763 : Blo 1815609 13789763 := bstep (se 1 (by rfl) ⟨10342322, by rfl⟩ : syracuseStep 13789763 = 20684645) B20684645
theorem B11635319 : Blo 1815609 11635319 := bstep (se 1 (by rfl) ⟨8726489, by rfl⟩ : syracuseStep 11635319 = 17452979) B17452979
theorem B6130295 : Blo 1815609 6130295 := bstep (se 1 (by rfl) ⟨4597721, by rfl⟩ : syracuseStep 6130295 = 9195443) B9195443
theorem B17451713 : Blo 1815609 17451713 := bstep (se 2 (by rfl) ⟨6544392, by rfl⟩ : syracuseStep 17451713 = 13088785) B13088785
theorem B3680969 : Blo 1815609 3680969 := bstep (se 2 (by rfl) ⟨1380363, by rfl⟩ : syracuseStep 3680969 = 2760727) B2760727
theorem B2042887 : Blo 1815609 2042887 := bstep (se 1 (by rfl) ⟨1532165, by rfl⟩ : syracuseStep 2042887 = 3064331) B3064331
theorem B4598795 : Blo 1815609 4598795 := bstep (se 1 (by rfl) ⟨3449096, by rfl⟩ : syracuseStep 4598795 = 6898193) B6898193
theorem B9956375 : Blo 1815609 9956375 := bstep (se 1 (by rfl) ⟨7467281, by rfl⟩ : syracuseStep 9956375 = 14934563) B14934563
theorem B3066923 : Blo 1815609 3066923 := bstep (se 1 (by rfl) ⟨2300192, by rfl⟩ : syracuseStep 3066923 = 4600385) B4600385
theorem B5385275 : Blo 1815609 5385275 := bstep (se 1 (by rfl) ⟨4038956, by rfl⟩ : syracuseStep 5385275 = 8077913) B8077913
theorem B5524567 : Blo 1815609 5524567 := bstep (se 1 (by rfl) ⟨4143425, by rfl⟩ : syracuseStep 5524567 = 8286851) B8286851
theorem B5524595 : Blo 1815609 5524595 := bstep (se 1 (by rfl) ⟨4143446, by rfl⟩ : syracuseStep 5524595 = 8286893) B8286893
theorem B39292037 : Blo 1815609 39292037 := bstep (se 4 (by rfl) ⟨3683628, by rfl⟩ : syracuseStep 39292037 = 7367257) B7367257
theorem B2657423 : Blo 1815609 2657423 := bstep (se 1 (by rfl) ⟨1993067, by rfl⟩ : syracuseStep 2657423 = 3986135) B3986135
theorem B2182315 : Blo 1815609 2182315 := bstep (se 1 (by rfl) ⟨1636736, by rfl⟩ : syracuseStep 2182315 = 3273473) B3273473
theorem B2043067 : Blo 1815609 2043067 := bstep (se 1 (by rfl) ⟨1532300, by rfl⟩ : syracuseStep 2043067 = 3064601) B3064601
theorem B6130889 : Blo 1815609 6130889 := bstep (se 2 (by rfl) ⟨2299083, by rfl⟩ : syracuseStep 6130889 = 4598167) B4598167
theorem B20696309 : Blo 1815609 20696309 := bstep (se 5 (by rfl) ⟨970139, by rfl⟩ : syracuseStep 20696309 = 1940279) B1940279
theorem B46583099 : Blo 1815609 46583099 := bstep (se 1 (by rfl) ⟨34937324, by rfl⟩ : syracuseStep 46583099 = 69874649) B69874649
theorem B3681683 : Blo 1815609 3681683 := bstep (se 1 (by rfl) ⟨2761262, by rfl⟩ : syracuseStep 3681683 = 5522525) B5522525
theorem B6901139 : Blo 1815609 6901139 := bstep (se 1 (by rfl) ⟨5175854, by rfl⟩ : syracuseStep 6901139 = 10351709) B10351709
theorem B10349977 : Blo 1815609 10349977 := bstep (se 2 (by rfl) ⟨3881241, by rfl⟩ : syracuseStep 10349977 = 7762483) B7762483
theorem B167841233 : Blo 1815609 167841233 := bstep (se 2 (by rfl) ⟨62940462, by rfl⟩ : syracuseStep 167841233 = 125880925) B125880925
theorem B8728067 : Blo 1815609 8728067 := bstep (se 1 (by rfl) ⟨6546050, by rfl⟩ : syracuseStep 8728067 = 13092101) B13092101
theorem B2723447 : Blo 1815609 2723447 := bstep (se 1 (by rfl) ⟨2042585, by rfl⟩ : syracuseStep 2723447 = 4085171) B4085171
theorem B7761527 : Blo 1815609 7761527 := bstep (se 1 (by rfl) ⟨5821145, by rfl⟩ : syracuseStep 7761527 = 11642291) B11642291
theorem B2723471 : Blo 1815609 2723471 := bstep (se 1 (by rfl) ⟨2042603, by rfl⟩ : syracuseStep 2723471 = 4085207) B4085207
theorem B2043535 : Blo 1815609 2043535 := bstep (se 1 (by rfl) ⟨1532651, by rfl⟩ : syracuseStep 2043535 = 3065303) B3065303
theorem B4599443 : Blo 1815609 4599443 := bstep (se 1 (by rfl) ⟨3449582, by rfl⟩ : syracuseStep 4599443 = 6899165) B6899165
theorem B2723513 : Blo 1815609 2723513 := bstep (se 2 (by rfl) ⟨1021317, by rfl⟩ : syracuseStep 2723513 = 2042635) B2042635
theorem B15511297 : Blo 1815609 15511297 := bstep (se 2 (by rfl) ⟨5816736, by rfl⟩ : syracuseStep 15511297 = 11633473) B11633473
theorem B2723591 : Blo 1815609 2723591 := bstep (se 1 (by rfl) ⟨2042693, by rfl⟩ : syracuseStep 2723591 = 4085387) B4085387
theorem B6549281 : Blo 1815609 6549281 := bstep (se 2 (by rfl) ⟨2455980, by rfl⟩ : syracuseStep 6549281 = 4911961) B4911961
theorem B2723627 : Blo 1815609 2723627 := bstep (se 1 (by rfl) ⟨2042720, by rfl⟩ : syracuseStep 2723627 = 4085441) B4085441
theorem B2723657 : Blo 1815609 2723657 := bstep (se 2 (by rfl) ⟨1021371, by rfl⟩ : syracuseStep 2723657 = 2042743) B2042743
theorem B5820275 : Blo 1815609 5820275 := bstep (se 1 (by rfl) ⟨4365206, by rfl⟩ : syracuseStep 5820275 = 8730413) B8730413
theorem B6131591 : Blo 1815609 6131591 := bstep (se 1 (by rfl) ⟨4598693, by rfl⟩ : syracuseStep 6131591 = 9197387) B9197387
theorem B22106009 : Blo 1815609 22106009 := bstep (se 2 (by rfl) ⟨8289753, by rfl⟩ : syracuseStep 22106009 = 16579507) B16579507
theorem B4599737 : Blo 1815609 4599737 := bstep (se 2 (by rfl) ⟨1724901, by rfl⟩ : syracuseStep 4599737 = 3449803) B3449803
theorem B2723771 : Blo 1815609 2723771 := bstep (se 1 (by rfl) ⟨2042828, by rfl⟩ : syracuseStep 2723771 = 4085657) B4085657
theorem B2723831 : Blo 1815609 2723831 := bstep (se 1 (by rfl) ⟨2042873, by rfl⟩ : syracuseStep 2723831 = 4085747) B4085747
theorem B5820427 : Blo 1815609 5820427 := bstep (se 1 (by rfl) ⟨4365320, by rfl⟩ : syracuseStep 5820427 = 8730641) B8730641
theorem B2723855 : Blo 1815609 2723855 := bstep (se 1 (by rfl) ⟨2042891, by rfl⟩ : syracuseStep 2723855 = 4085783) B4085783
theorem B2297899 : Blo 1815609 2297899 := bstep (se 1 (by rfl) ⟨1723424, by rfl⟩ : syracuseStep 2297899 = 3446849) B3446849
theorem B2723897 : Blo 1815609 2723897 := bstep (se 2 (by rfl) ⟨1021461, by rfl⟩ : syracuseStep 2723897 = 2042923) B2042923
theorem B2723975 : Blo 1815609 2723975 := bstep (se 1 (by rfl) ⟨2042981, by rfl⟩ : syracuseStep 2723975 = 4085963) B4085963
theorem B2044039 : Blo 1815609 2044039 := bstep (se 1 (by rfl) ⟨1533029, by rfl⟩ : syracuseStep 2044039 = 3066059) B3066059
theorem B2724011 : Blo 1815609 2724011 := bstep (se 1 (by rfl) ⟨2043008, by rfl⟩ : syracuseStep 2724011 = 4086017) B4086017
theorem B2724041 : Blo 1815609 2724041 := bstep (se 2 (by rfl) ⟨1021515, by rfl⟩ : syracuseStep 2724041 = 2043031) B2043031
theorem B6131969 : Blo 1815609 6131969 := bstep (se 2 (by rfl) ⟨2299488, by rfl⟩ : syracuseStep 6131969 = 4598977) B4598977
theorem B2298127 : Blo 1815609 2298127 := bstep (se 1 (by rfl) ⟨1723595, by rfl⟩ : syracuseStep 2298127 = 3447191) B3447191
theorem B2724155 : Blo 1815609 2724155 := bstep (se 1 (by rfl) ⟨2043116, by rfl⟩ : syracuseStep 2724155 = 4086233) B4086233
theorem B2044219 : Blo 1815609 2044219 := bstep (se 1 (by rfl) ⟨1533164, by rfl⟩ : syracuseStep 2044219 = 3066329) B3066329
theorem B2724215 : Blo 1815609 2724215 := bstep (se 1 (by rfl) ⟨2043161, by rfl⟩ : syracuseStep 2724215 = 4086323) B4086323
theorem B2724239 : Blo 1815609 2724239 := bstep (se 1 (by rfl) ⟨2043179, by rfl⟩ : syracuseStep 2724239 = 4086359) B4086359
theorem B9195929 : Blo 1815609 9195929 := bstep (se 2 (by rfl) ⟨3448473, by rfl⟩ : syracuseStep 9195929 = 6896947) B6896947
theorem B2724281 : Blo 1815609 2724281 := bstep (se 2 (by rfl) ⟨1021605, by rfl⟩ : syracuseStep 2724281 = 2043211) B2043211
theorem B2454023 : Blo 1815609 2454023 := bstep (se 1 (by rfl) ⟨1840517, by rfl⟩ : syracuseStep 2454023 = 3681035) B3681035
theorem B2724359 : Blo 1815609 2724359 := bstep (se 1 (by rfl) ⟨2043269, by rfl⟩ : syracuseStep 2724359 = 4086539) B4086539
theorem B4362785 : Blo 1815609 4362785 := bstep (se 2 (by rfl) ⟨1636044, by rfl⟩ : syracuseStep 4362785 = 3272089) B3272089
theorem B2724395 : Blo 1815609 2724395 := bstep (se 1 (by rfl) ⟨2043296, by rfl⟩ : syracuseStep 2724395 = 4086593) B4086593
theorem B2724425 : Blo 1815609 2724425 := bstep (se 2 (by rfl) ⟨1021659, by rfl⟩ : syracuseStep 2724425 = 2043319) B2043319
theorem B4600435 : Blo 1815609 4600435 := bstep (se 1 (by rfl) ⟨3450326, by rfl⟩ : syracuseStep 4600435 = 6900653) B6900653
theorem B5173895 : Blo 1815609 5173895 := bstep (se 1 (by rfl) ⟨3880421, by rfl⟩ : syracuseStep 5173895 = 7760843) B7760843
theorem B2724539 : Blo 1815609 2724539 := bstep (se 1 (by rfl) ⟨2043404, by rfl⟩ : syracuseStep 2724539 = 4086809) B4086809
theorem B2724599 : Blo 1815609 2724599 := bstep (se 1 (by rfl) ⟨2043449, by rfl⟩ : syracuseStep 2724599 = 4086899) B4086899
theorem B4600577 : Blo 1815609 4600577 := bstep (se 2 (by rfl) ⟨1725216, by rfl⟩ : syracuseStep 4600577 = 3450433) B3450433
theorem B2724623 : Blo 1815609 2724623 := bstep (se 1 (by rfl) ⟨2043467, by rfl⟩ : syracuseStep 2724623 = 4086935) B4086935
theorem B2044687 : Blo 1815609 2044687 := bstep (se 1 (by rfl) ⟨1533515, by rfl⟩ : syracuseStep 2044687 = 3067031) B3067031
theorem B2724665 : Blo 1815609 2724665 := bstep (se 2 (by rfl) ⟨1021749, by rfl⟩ : syracuseStep 2724665 = 2043499) B2043499
theorem B2454391 : Blo 1815609 2454391 := bstep (se 1 (by rfl) ⟨1840793, by rfl⟩ : syracuseStep 2454391 = 3681587) B3681587
theorem B2724743 : Blo 1815609 2724743 := bstep (se 1 (by rfl) ⟨2043557, by rfl⟩ : syracuseStep 2724743 = 4087115) B4087115
theorem B5526407 : Blo 1815609 5526407 := bstep (se 1 (by rfl) ⟨4144805, by rfl⟩ : syracuseStep 5526407 = 8289611) B8289611
theorem B2724779 : Blo 1815609 2724779 := bstep (se 1 (by rfl) ⟨2043584, by rfl⟩ : syracuseStep 2724779 = 4087169) B4087169
theorem B2724809 : Blo 1815609 2724809 := bstep (se 2 (by rfl) ⟨1021803, by rfl⟩ : syracuseStep 2724809 = 2043607) B2043607
theorem B2298871 : Blo 1815609 2298871 := bstep (se 1 (by rfl) ⟨1724153, by rfl⟩ : syracuseStep 2298871 = 3448307) B3448307
theorem B6132779 : Blo 1815609 6132779 := bstep (se 1 (by rfl) ⟨4599584, by rfl⟩ : syracuseStep 6132779 = 9199169) B9199169
theorem B1815611 : Blo 1815609 1815611 := bstep (se 1 (by rfl) ⟨1361708, by rfl⟩ : syracuseStep 1815611 = 2723417) B2723417
theorem B2724923 : Blo 1815609 2724923 := bstep (se 1 (by rfl) ⟨2043692, by rfl⟩ : syracuseStep 2724923 = 4087385) B4087385
theorem B9819203 : Blo 1815609 9819203 := bstep (se 1 (by rfl) ⟨7364402, by rfl⟩ : syracuseStep 9819203 = 14728805) B14728805
theorem B2724983 : Blo 1815609 2724983 := bstep (se 1 (by rfl) ⟨2043737, by rfl⟩ : syracuseStep 2724983 = 4087475) B4087475
theorem B1815687 : Blo 1815609 1815687 := bstep (se 1 (by rfl) ⟨1361765, by rfl⟩ : syracuseStep 1815687 = 2723531) B2723531
theorem B4363399 : Blo 1815609 4363399 := bstep (se 1 (by rfl) ⟨3272549, by rfl⟩ : syracuseStep 4363399 = 6545099) B6545099
theorem B1815695 : Blo 1815609 1815695 := bstep (se 1 (by rfl) ⟨1361771, by rfl⟩ : syracuseStep 1815695 = 2723543) B2723543
theorem B2725007 : Blo 1815609 2725007 := bstep (se 1 (by rfl) ⟨2043755, by rfl⟩ : syracuseStep 2725007 = 4087511) B4087511
theorem B2725049 : Blo 1815609 2725049 := bstep (se 2 (by rfl) ⟨1021893, by rfl⟩ : syracuseStep 2725049 = 2043787) B2043787
theorem B1815739 : Blo 1815609 1815739 := bstep (se 1 (by rfl) ⟨1361804, by rfl⟩ : syracuseStep 1815739 = 2723609) B2723609
theorem B2454715 : Blo 1815609 2454715 := bstep (se 1 (by rfl) ⟨1841036, by rfl⟩ : syracuseStep 2454715 = 3682073) B3682073
theorem B1815815 : Blo 1815609 1815815 := bstep (se 1 (by rfl) ⟨1361861, by rfl⟩ : syracuseStep 1815815 = 2723723) B2723723
theorem B2725127 : Blo 1815609 2725127 := bstep (se 1 (by rfl) ⟨2043845, by rfl⟩ : syracuseStep 2725127 = 4087691) B4087691
theorem B1815823 : Blo 1815609 1815823 := bstep (se 1 (by rfl) ⟨1361867, by rfl⟩ : syracuseStep 1815823 = 2723735) B2723735
theorem B4363553 : Blo 1815609 4363553 := bstep (se 2 (by rfl) ⟨1636332, by rfl⟩ : syracuseStep 4363553 = 3272665) B3272665
theorem B2725163 : Blo 1815609 2725163 := bstep (se 1 (by rfl) ⟨2043872, by rfl⟩ : syracuseStep 2725163 = 4087745) B4087745
theorem B1815867 : Blo 1815609 1815867 := bstep (se 1 (by rfl) ⟨1361900, by rfl⟩ : syracuseStep 1815867 = 2723801) B2723801
theorem B2299195 : Blo 1815609 2299195 := bstep (se 1 (by rfl) ⟨1724396, by rfl⟩ : syracuseStep 2299195 = 3448793) B3448793
theorem B2725193 : Blo 1815609 2725193 := bstep (se 2 (by rfl) ⟨1021947, by rfl⟩ : syracuseStep 2725193 = 2043895) B2043895
theorem B1815943 : Blo 1815609 1815943 := bstep (se 1 (by rfl) ⟨1361957, by rfl⟩ : syracuseStep 1815943 = 2723915) B2723915
theorem B2905290125 : Blo 1815609 2905290125 := bstep (se 3 (by rfl) ⟨544741898, by rfl⟩ : syracuseStep 2905290125 = 1089483797) B1089483797
theorem B1815951 : Blo 1815609 1815951 := bstep (se 1 (by rfl) ⟨1361963, by rfl⟩ : syracuseStep 1815951 = 2723927) B2723927
theorem B181630349 : Blo 1815609 181630349 := bstep (se 3 (by rfl) ⟨34055690, by rfl⟩ : syracuseStep 181630349 = 68111381) B68111381
theorem B16577939 : Blo 1815609 16577939 := bstep (se 1 (by rfl) ⟨12433454, by rfl⟩ : syracuseStep 16577939 = 24866909) B24866909
theorem B1815995 : Blo 1815609 1815995 := bstep (se 1 (by rfl) ⟨1361996, by rfl⟩ : syracuseStep 1815995 = 2723993) B2723993
theorem B2725307 : Blo 1815609 2725307 := bstep (se 1 (by rfl) ⟨2043980, by rfl⟩ : syracuseStep 2725307 = 4087961) B4087961
theorem B2725367 : Blo 1815609 2725367 := bstep (se 1 (by rfl) ⟨2044025, by rfl⟩ : syracuseStep 2725367 = 4088051) B4088051
theorem B1816071 : Blo 1815609 1816071 := bstep (se 1 (by rfl) ⟨1362053, by rfl⟩ : syracuseStep 1816071 = 2724107) B2724107
theorem B1816079 : Blo 1815609 1816079 := bstep (se 1 (by rfl) ⟨1362059, by rfl⟩ : syracuseStep 1816079 = 2724119) B2724119
theorem B2725391 : Blo 1815609 2725391 := bstep (se 1 (by rfl) ⟨2044043, by rfl⟩ : syracuseStep 2725391 = 4088087) B4088087
theorem B3274273 : Blo 1815609 3274273 := bstep (se 2 (by rfl) ⟨1227852, by rfl⟩ : syracuseStep 3274273 = 2455705) B2455705
theorem B2725433 : Blo 1815609 2725433 := bstep (se 2 (by rfl) ⟨1022037, by rfl⟩ : syracuseStep 2725433 = 2044075) B2044075
theorem B1816123 : Blo 1815609 1816123 := bstep (se 1 (by rfl) ⟨1362092, by rfl⟩ : syracuseStep 1816123 = 2724185) B2724185
theorem B9819767 : Blo 1815609 9819767 := bstep (se 1 (by rfl) ⟨7364825, by rfl⟩ : syracuseStep 9819767 = 14729651) B14729651
theorem B1816199 : Blo 1815609 1816199 := bstep (se 1 (by rfl) ⟨1362149, by rfl⟩ : syracuseStep 1816199 = 2724299) B2724299
theorem B2725511 : Blo 1815609 2725511 := bstep (se 1 (by rfl) ⟨2044133, by rfl⟩ : syracuseStep 2725511 = 4088267) B4088267
theorem B1816207 : Blo 1815609 1816207 := bstep (se 1 (by rfl) ⟨1362155, by rfl⟩ : syracuseStep 1816207 = 2724311) B2724311
theorem B5527187 : Blo 1815609 5527187 := bstep (se 1 (by rfl) ⟨4145390, by rfl⟩ : syracuseStep 5527187 = 8290781) B8290781
theorem B2725547 : Blo 1815609 2725547 := bstep (se 1 (by rfl) ⟨2044160, by rfl⟩ : syracuseStep 2725547 = 4088321) B4088321
theorem B1816251 : Blo 1815609 1816251 := bstep (se 1 (by rfl) ⟨1362188, by rfl⟩ : syracuseStep 1816251 = 2724377) B2724377
theorem B15513281 : Blo 1815609 15513281 := bstep (se 2 (by rfl) ⟨5817480, by rfl⟩ : syracuseStep 15513281 = 11634961) B11634961
theorem B2725577 : Blo 1815609 2725577 := bstep (se 2 (by rfl) ⟨1022091, by rfl⟩ : syracuseStep 2725577 = 2044183) B2044183
theorem B1816327 : Blo 1815609 1816327 := bstep (se 1 (by rfl) ⟨1362245, by rfl⟩ : syracuseStep 1816327 = 2724491) B2724491
theorem B1816335 : Blo 1815609 1816335 := bstep (se 1 (by rfl) ⟨1362251, by rfl⟩ : syracuseStep 1816335 = 2724503) B2724503
theorem B16578341 : Blo 1815609 16578341 := bstep (se 4 (by rfl) ⟨1554219, by rfl⟩ : syracuseStep 16578341 = 3108439) B3108439
theorem B2299691 : Blo 1815609 2299691 := bstep (se 1 (by rfl) ⟨1724768, by rfl⟩ : syracuseStep 2299691 = 3449537) B3449537
theorem B1816379 : Blo 1815609 1816379 := bstep (se 1 (by rfl) ⟨1362284, by rfl⟩ : syracuseStep 1816379 = 2724569) B2724569
theorem B2725691 : Blo 1815609 2725691 := bstep (se 1 (by rfl) ⟨2044268, by rfl⟩ : syracuseStep 2725691 = 4088537) B4088537
theorem B6895475 : Blo 1815609 6895475 := bstep (se 1 (by rfl) ⟨5171606, by rfl⟩ : syracuseStep 6895475 = 10343213) B10343213
theorem B2586487 : Blo 1815609 2586487 := bstep (se 1 (by rfl) ⟨1939865, by rfl⟩ : syracuseStep 2586487 = 3879731) B3879731
theorem B2725751 : Blo 1815609 2725751 := bstep (se 1 (by rfl) ⟨2044313, by rfl⟩ : syracuseStep 2725751 = 4088627) B4088627
theorem B4085639 : Blo 1815609 4085639 := bstep (se 1 (by rfl) ⟨3064229, by rfl⟩ : syracuseStep 4085639 = 6128459) B6128459
theorem B1816455 : Blo 1815609 1816455 := bstep (se 1 (by rfl) ⟨1362341, by rfl⟩ : syracuseStep 1816455 = 2724683) B2724683
theorem B1816463 : Blo 1815609 1816463 := bstep (se 1 (by rfl) ⟨1362347, by rfl⟩ : syracuseStep 1816463 = 2724695) B2724695
theorem B2725775 : Blo 1815609 2725775 := bstep (se 1 (by rfl) ⟨2044331, by rfl⟩ : syracuseStep 2725775 = 4088663) B4088663
theorem B2725817 : Blo 1815609 2725817 := bstep (se 2 (by rfl) ⟨1022181, by rfl⟩ : syracuseStep 2725817 = 2044363) B2044363
theorem B1816507 : Blo 1815609 1816507 := bstep (se 1 (by rfl) ⟨1362380, by rfl⟩ : syracuseStep 1816507 = 2724761) B2724761
theorem B1816583 : Blo 1815609 1816583 := bstep (se 1 (by rfl) ⟨1362437, by rfl⟩ : syracuseStep 1816583 = 2724875) B2724875
theorem B2725895 : Blo 1815609 2725895 := bstep (se 1 (by rfl) ⟨2044421, by rfl⟩ : syracuseStep 2725895 = 4088843) B4088843
theorem B1816591 : Blo 1815609 1816591 := bstep (se 1 (by rfl) ⟨1362443, by rfl⟩ : syracuseStep 1816591 = 2724887) B2724887
theorem B2725931 : Blo 1815609 2725931 := bstep (se 1 (by rfl) ⟨2044448, by rfl⟩ : syracuseStep 2725931 = 4088897) B4088897
theorem B4085819 : Blo 1815609 4085819 := bstep (se 1 (by rfl) ⟨3064364, by rfl⟩ : syracuseStep 4085819 = 6128729) B6128729
theorem B1816635 : Blo 1815609 1816635 := bstep (se 1 (by rfl) ⟨1362476, by rfl⟩ : syracuseStep 1816635 = 2724953) B2724953
theorem B2725961 : Blo 1815609 2725961 := bstep (se 2 (by rfl) ⟨1022235, by rfl⟩ : syracuseStep 2725961 = 2044471) B2044471
theorem B1816711 : Blo 1815609 1816711 := bstep (se 1 (by rfl) ⟨1362533, by rfl⟩ : syracuseStep 1816711 = 2725067) B2725067
theorem B1816719 : Blo 1815609 1816719 := bstep (se 1 (by rfl) ⟨1362539, by rfl⟩ : syracuseStep 1816719 = 2725079) B2725079
theorem B4085945 : Blo 1815609 4085945 := bstep (se 2 (by rfl) ⟨1532229, by rfl⟩ : syracuseStep 4085945 = 3064459) B3064459
theorem B1816763 : Blo 1815609 1816763 := bstep (se 1 (by rfl) ⟨1362572, by rfl⟩ : syracuseStep 1816763 = 2725145) B2725145
theorem B2586811 : Blo 1815609 2586811 := bstep (se 1 (by rfl) ⟨1940108, by rfl⟩ : syracuseStep 2586811 = 3880217) B3880217
theorem B2726075 : Blo 1815609 2726075 := bstep (se 1 (by rfl) ⟨2044556, by rfl⟩ : syracuseStep 2726075 = 4089113) B4089113
theorem B15522029 : Blo 1815609 15522029 := bstep (se 3 (by rfl) ⟨2910380, by rfl⟩ : syracuseStep 15522029 = 5820761) B5820761
theorem B2726135 : Blo 1815609 2726135 := bstep (se 1 (by rfl) ⟨2044601, by rfl⟩ : syracuseStep 2726135 = 4089203) B4089203
theorem B1816839 : Blo 1815609 1816839 := bstep (se 1 (by rfl) ⟨1362629, by rfl⟩ : syracuseStep 1816839 = 2725259) B2725259
theorem B2300167 : Blo 1815609 2300167 := bstep (se 1 (by rfl) ⟨1725125, by rfl⟩ : syracuseStep 2300167 = 3450251) B3450251
theorem B1816847 : Blo 1815609 1816847 := bstep (se 1 (by rfl) ⟨1362635, by rfl⟩ : syracuseStep 1816847 = 2725271) B2725271
theorem B2726159 : Blo 1815609 2726159 := bstep (se 1 (by rfl) ⟨2044619, by rfl⟩ : syracuseStep 2726159 = 4089239) B4089239
theorem B2726201 : Blo 1815609 2726201 := bstep (se 2 (by rfl) ⟨1022325, by rfl⟩ : syracuseStep 2726201 = 2044651) B2044651
theorem B1816891 : Blo 1815609 1816891 := bstep (se 1 (by rfl) ⟨1362668, by rfl⟩ : syracuseStep 1816891 = 2725337) B2725337
theorem B6134075 : Blo 1815609 6134075 := bstep (se 1 (by rfl) ⟨4600556, by rfl⟩ : syracuseStep 6134075 = 9201113) B9201113
theorem B1816967 : Blo 1815609 1816967 := bstep (se 1 (by rfl) ⟨1362725, by rfl⟩ : syracuseStep 1816967 = 2725451) B2725451
theorem B10492295 : Blo 1815609 10492295 := bstep (se 1 (by rfl) ⟨7869221, by rfl⟩ : syracuseStep 10492295 = 15738443) B15738443
theorem B2726279 : Blo 1815609 2726279 := bstep (se 1 (by rfl) ⟨2044709, by rfl⟩ : syracuseStep 2726279 = 4089419) B4089419
theorem B1816975 : Blo 1815609 1816975 := bstep (se 1 (by rfl) ⟨1362731, by rfl⟩ : syracuseStep 1816975 = 2725463) B2725463
theorem B2726315 : Blo 1815609 2726315 := bstep (se 1 (by rfl) ⟨2044736, by rfl⟩ : syracuseStep 2726315 = 4089473) B4089473
theorem B13801913 : Blo 1815609 13801913 := bstep (se 2 (by rfl) ⟨5175717, by rfl⟩ : syracuseStep 13801913 = 10351435) B10351435
theorem B1817019 : Blo 1815609 1817019 := bstep (se 1 (by rfl) ⟨1362764, by rfl⟩ : syracuseStep 1817019 = 2725529) B2725529
theorem B2726345 : Blo 1815609 2726345 := bstep (se 2 (by rfl) ⟨1022379, by rfl⟩ : syracuseStep 2726345 = 2044759) B2044759
theorem B5175809 : Blo 1815609 5175809 := bstep (se 2 (by rfl) ⟨1940928, by rfl⟩ : syracuseStep 5175809 = 3881857) B3881857
theorem B1817095 : Blo 1815609 1817095 := bstep (se 1 (by rfl) ⟨1362821, by rfl⟩ : syracuseStep 1817095 = 2725643) B2725643
theorem B4086287 : Blo 1815609 4086287 := bstep (se 1 (by rfl) ⟨3064715, by rfl⟩ : syracuseStep 4086287 = 6129431) B6129431
theorem B1817103 : Blo 1815609 1817103 := bstep (se 1 (by rfl) ⟨1362827, by rfl⟩ : syracuseStep 1817103 = 2725655) B2725655
theorem B4086305 : Blo 1815609 4086305 := bstep (se 2 (by rfl) ⟨1532364, by rfl⟩ : syracuseStep 4086305 = 3064729) B3064729
theorem B3881515 : Blo 1815609 3881515 := bstep (se 1 (by rfl) ⟨2911136, by rfl⟩ : syracuseStep 3881515 = 5822273) B5822273
theorem B1817147 : Blo 1815609 1817147 := bstep (se 1 (by rfl) ⟨1362860, by rfl⟩ : syracuseStep 1817147 = 2725721) B2725721
theorem B37280321 : Blo 1815609 37280321 := bstep (se 2 (by rfl) ⟨13980120, by rfl⟩ : syracuseStep 37280321 = 27960241) B27960241
theorem B1817223 : Blo 1815609 1817223 := bstep (se 1 (by rfl) ⟨1362917, by rfl⟩ : syracuseStep 1817223 = 2725835) B2725835
theorem B1817231 : Blo 1815609 1817231 := bstep (se 1 (by rfl) ⟨1362923, by rfl⟩ : syracuseStep 1817231 = 2725847) B2725847
theorem B1817275 : Blo 1815609 1817275 := bstep (se 1 (by rfl) ⟨1362956, by rfl⟩ : syracuseStep 1817275 = 2725913) B2725913
theorem B1817351 : Blo 1815609 1817351 := bstep (se 1 (by rfl) ⟨1363013, by rfl⟩ : syracuseStep 1817351 = 2726027) B2726027
theorem B1817359 : Blo 1815609 1817359 := bstep (se 1 (by rfl) ⟨1363019, by rfl⟩ : syracuseStep 1817359 = 2726039) B2726039
theorem B5315371 : Blo 1815609 5315371 := bstep (se 1 (by rfl) ⟨3986528, by rfl⟩ : syracuseStep 5315371 = 7973057) B7973057
theorem B1817403 : Blo 1815609 1817403 := bstep (se 1 (by rfl) ⟨1363052, by rfl⟩ : syracuseStep 1817403 = 2726105) B2726105
theorem B13794137 : Blo 1815609 13794137 := bstep (se 2 (by rfl) ⟨5172801, by rfl⟩ : syracuseStep 13794137 = 10345603) B10345603
theorem B4086647 : Blo 1815609 4086647 := bstep (se 1 (by rfl) ⟨3064985, by rfl⟩ : syracuseStep 4086647 = 6129971) B6129971
theorem B1817479 : Blo 1815609 1817479 := bstep (se 1 (by rfl) ⟨1363109, by rfl⟩ : syracuseStep 1817479 = 2726219) B2726219
theorem B1817487 : Blo 1815609 1817487 := bstep (se 1 (by rfl) ⟨1363115, by rfl⟩ : syracuseStep 1817487 = 2726231) B2726231
theorem B9198521 : Blo 1815609 9198521 := bstep (se 2 (by rfl) ⟨3449445, by rfl⟩ : syracuseStep 9198521 = 6898891) B6898891
theorem B1817531 : Blo 1815609 1817531 := bstep (se 1 (by rfl) ⟨1363148, by rfl⟩ : syracuseStep 1817531 = 2726297) B2726297
theorem B1817607 : Blo 1815609 1817607 := bstep (se 1 (by rfl) ⟨1363205, by rfl⟩ : syracuseStep 1817607 = 2726411) B2726411
theorem B9821195 : Blo 1815609 9821195 := bstep (se 1 (by rfl) ⟨7365896, by rfl⟩ : syracuseStep 9821195 = 14731793) B14731793
theorem B4086827 : Blo 1815609 4086827 := bstep (se 1 (by rfl) ⟨3065120, by rfl⟩ : syracuseStep 4086827 = 6130241) B6130241
theorem B2948231 : Blo 1815609 2948231 := bstep (se 1 (by rfl) ⟨2211173, by rfl⟩ : syracuseStep 2948231 = 4422347) B4422347
theorem B3448079 : Blo 1815609 3448079 := bstep (se 1 (by rfl) ⟨2586059, by rfl⟩ : syracuseStep 3448079 = 5172119) B5172119
theorem B3497249 : Blo 1815609 3497249 := bstep (se 2 (by rfl) ⟨1311468, by rfl⟩ : syracuseStep 3497249 = 2622937) B2622937
theorem B4087187 : Blo 1815609 4087187 := bstep (se 1 (by rfl) ⟨3065390, by rfl⟩ : syracuseStep 4087187 = 6130781) B6130781
theorem B4087241 : Blo 1815609 4087241 := bstep (se 2 (by rfl) ⟨1532715, by rfl⟩ : syracuseStep 4087241 = 3065431) B3065431
theorem B11042497 : Blo 1815609 11042497 := bstep (se 2 (by rfl) ⟨4140936, by rfl⟩ : syracuseStep 11042497 = 8281873) B8281873
theorem B3317449 : Blo 1815609 3317449 := bstep (se 2 (by rfl) ⟨1244043, by rfl⟩ : syracuseStep 3317449 = 2488087) B2488087
theorem B13795109 : Blo 1815609 13795109 := bstep (se 4 (by rfl) ⟨1293291, by rfl⟩ : syracuseStep 13795109 = 2586583) B2586583
theorem B3063865 : Blo 1815609 3063865 := bstep (se 2 (by rfl) ⟨1148949, by rfl⟩ : syracuseStep 3063865 = 2297899) B2297899
theorem B4087979 : Blo 1815609 4087979 := bstep (se 1 (by rfl) ⟨3065984, by rfl⟩ : syracuseStep 4087979 = 6131969) B6131969
theorem B3064007 : Blo 1815609 3064007 := bstep (se 1 (by rfl) ⟨2298005, by rfl⟩ : syracuseStep 3064007 = 4596011) B4596011
theorem B3449081 : Blo 1815609 3449081 := bstep (se 2 (by rfl) ⟨1293405, by rfl⟩ : syracuseStep 3449081 = 2586811) B2586811
theorem B13795595 : Blo 1815609 13795595 := bstep (se 1 (by rfl) ⟨10346696, by rfl⟩ : syracuseStep 13795595 = 20693393) B20693393
theorem B3064169 : Blo 1815609 3064169 := bstep (se 2 (by rfl) ⟨1149063, by rfl⟩ : syracuseStep 3064169 = 2298127) B2298127
theorem B2908523 : Blo 1815609 2908523 := bstep (se 1 (by rfl) ⟨2181392, by rfl⟩ : syracuseStep 2908523 = 4362785) B4362785
theorem B7086461 : Blo 1815609 7086461 := bstep (se 3 (by rfl) ⟨1328711, by rfl⟩ : syracuseStep 7086461 = 2657423) B2657423
theorem B4088519 : Blo 1815609 4088519 := bstep (se 1 (by rfl) ⟨3066389, by rfl⟩ : syracuseStep 4088519 = 6132779) B6132779
theorem B6898391 : Blo 1815609 6898391 := bstep (se 1 (by rfl) ⟨5173793, by rfl⟩ : syracuseStep 6898391 = 10347587) B10347587
theorem B3064567 : Blo 1815609 3064567 := bstep (se 1 (by rfl) ⟨2298425, by rfl⟩ : syracuseStep 3064567 = 4596851) B4596851
theorem B6636383 : Blo 1815609 6636383 := bstep (se 1 (by rfl) ⟨4977287, by rfl⟩ : syracuseStep 6636383 = 9954575) B9954575
theorem B2909035 : Blo 1815609 2909035 := bstep (se 1 (by rfl) ⟨2181776, by rfl⟩ : syracuseStep 2909035 = 4363553) B4363553
theorem B1936860083 : Blo 1815609 1936860083 := bstep (se 1 (by rfl) ⟨1452645062, by rfl⟩ : syracuseStep 1936860083 = 2905290125) B2905290125
theorem B121086899 : Blo 1815609 121086899 := bstep (se 1 (by rfl) ⟨90815174, by rfl⟩ : syracuseStep 121086899 = 181630349) B181630349
theorem B6128567 : Blo 1815609 6128567 := bstep (se 1 (by rfl) ⟨4596425, by rfl⟩ : syracuseStep 6128567 = 9192851) B9192851
theorem B11051959 : Blo 1815609 11051959 := bstep (se 1 (by rfl) ⟨8288969, by rfl⟩ : syracuseStep 11051959 = 16577939) B16577939
theorem B3064763 : Blo 1815609 3064763 := bstep (se 1 (by rfl) ⟨2298572, by rfl⟩ : syracuseStep 3064763 = 4597145) B4597145
theorem B3933191 : Blo 1815609 3933191 := bstep (se 1 (by rfl) ⟨2949893, by rfl⟩ : syracuseStep 3933191 = 5899787) B5899787
theorem B3064871 : Blo 1815609 3064871 := bstep (se 1 (by rfl) ⟨2298653, by rfl⟩ : syracuseStep 3064871 = 4597307) B4597307
theorem B9192527 : Blo 1815609 9192527 := bstep (se 1 (by rfl) ⟨6894395, by rfl⟩ : syracuseStep 9192527 = 13788791) B13788791
theorem B6546511 : Blo 1815609 6546511 := bstep (se 1 (by rfl) ⟨4909883, by rfl⟩ : syracuseStep 6546511 = 9819767) B9819767
theorem B11052227 : Blo 1815609 11052227 := bstep (se 1 (by rfl) ⟨8289170, by rfl⟩ : syracuseStep 11052227 = 16578341) B16578341
theorem B4596983 : Blo 1815609 4596983 := bstep (se 1 (by rfl) ⟨3447737, by rfl⟩ : syracuseStep 4596983 = 6895475) B6895475
theorem B3065161 : Blo 1815609 3065161 := bstep (se 2 (by rfl) ⟨1149435, by rfl⟩ : syracuseStep 3065161 = 2298871) B2298871
theorem B3065195 : Blo 1815609 3065195 := bstep (se 1 (by rfl) ⟨2298896, by rfl⟩ : syracuseStep 3065195 = 4597793) B4597793
theorem B10348019 : Blo 1815609 10348019 := bstep (se 1 (by rfl) ⟨7761014, by rfl⟩ : syracuseStep 10348019 = 15522029) B15522029
theorem B5817865 : Blo 1815609 5817865 := bstep (se 2 (by rfl) ⟨2181699, by rfl⟩ : syracuseStep 5817865 = 4363399) B4363399
theorem B6129161 : Blo 1815609 6129161 := bstep (se 2 (by rfl) ⟨2298435, by rfl⟩ : syracuseStep 6129161 = 4596871) B4596871
theorem B4089383 : Blo 1815609 4089383 := bstep (se 1 (by rfl) ⟨3067037, by rfl⟩ : syracuseStep 4089383 = 6134075) B6134075
theorem B2909753 : Blo 1815609 2909753 := bstep (se 2 (by rfl) ⟨1091157, by rfl⟩ : syracuseStep 2909753 = 2182315) B2182315
theorem B9201275 : Blo 1815609 9201275 := bstep (se 1 (by rfl) ⟨6900956, by rfl⟩ : syracuseStep 9201275 = 13801913) B13801913
theorem B3450539 : Blo 1815609 3450539 := bstep (se 1 (by rfl) ⟨2587904, by rfl⟩ : syracuseStep 3450539 = 5175809) B5175809
theorem B13797053 : Blo 1815609 13797053 := bstep (se 3 (by rfl) ⟨2586947, by rfl⟩ : syracuseStep 13797053 = 5173895) B5173895
theorem B9193175 : Blo 1815609 9193175 := bstep (se 1 (by rfl) ⟨6894881, by rfl⟩ : syracuseStep 9193175 = 13789763) B13789763
theorem B3065593 : Blo 1815609 3065593 := bstep (se 2 (by rfl) ⟨1149597, by rfl⟩ : syracuseStep 3065593 = 2299195) B2299195
theorem B11634475 : Blo 1815609 11634475 := bstep (se 1 (by rfl) ⟨8725856, by rfl⟩ : syracuseStep 11634475 = 17451713) B17451713
theorem B9815917 : Blo 1815609 9815917 := bstep (se 3 (by rfl) ⟨1840484, by rfl⟩ : syracuseStep 9815917 = 3680969) B3680969
theorem B6547463 : Blo 1815609 6547463 := bstep (se 1 (by rfl) ⟨4910597, by rfl⟩ : syracuseStep 6547463 = 9821195) B9821195
theorem B3065863 : Blo 1815609 3065863 := bstep (se 1 (by rfl) ⟨2299397, by rfl⟩ : syracuseStep 3065863 = 4598795) B4598795
theorem B6637583 : Blo 1815609 6637583 := bstep (se 1 (by rfl) ⟨4978187, by rfl⟩ : syracuseStep 6637583 = 9956375) B9956375
theorem B3590183 : Blo 1815609 3590183 := bstep (se 1 (by rfl) ⟨2692637, by rfl⟩ : syracuseStep 3590183 = 5385275) B5385275
theorem B13797539 : Blo 1815609 13797539 := bstep (se 1 (by rfl) ⟨10348154, by rfl⟩ : syracuseStep 13797539 = 20696309) B20696309
theorem B14723329 : Blo 1815609 14723329 := bstep (se 2 (by rfl) ⟨5521248, by rfl⟩ : syracuseStep 14723329 = 11042497) B11042497
theorem B5818711 : Blo 1815609 5818711 := bstep (se 1 (by rfl) ⟨4364033, by rfl⟩ : syracuseStep 5818711 = 8728067) B8728067
theorem B6130025 : Blo 1815609 6130025 := bstep (se 2 (by rfl) ⟨2298759, by rfl⟩ : syracuseStep 6130025 = 4597519) B4597519
theorem B3066295 : Blo 1815609 3066295 := bstep (se 1 (by rfl) ⟨2299721, by rfl⟩ : syracuseStep 3066295 = 4599443) B4599443
theorem B3066491 : Blo 1815609 3066491 := bstep (se 1 (by rfl) ⟨2299868, by rfl⟩ : syracuseStep 3066491 = 4599737) B4599737
theorem B4598471 : Blo 1815609 4598471 := bstep (se 1 (by rfl) ⟨3448853, by rfl⟩ : syracuseStep 4598471 = 6897707) B6897707
theorem B20687561 : Blo 1815609 20687561 := bstep (se 2 (by rfl) ⟨7757835, by rfl⟩ : syracuseStep 20687561 = 15515671) B15515671
theorem B4975319 : Blo 1815609 4975319 := bstep (se 1 (by rfl) ⟨3731489, by rfl⟩ : syracuseStep 4975319 = 7462979) B7462979
theorem B31042277 : Blo 1815609 31042277 := bstep (se 4 (by rfl) ⟨2910213, by rfl⟩ : syracuseStep 31042277 = 5820427) B5820427
theorem B7367453 : Blo 1815609 7367453 := bstep (se 3 (by rfl) ⟨1381397, by rfl⟩ : syracuseStep 7367453 = 2762795) B2762795
theorem B26184541 : Blo 1815609 26184541 := bstep (se 3 (by rfl) ⟨4909601, by rfl⟩ : syracuseStep 26184541 = 9819203) B9819203
theorem B6130619 : Blo 1815609 6130619 := bstep (se 1 (by rfl) ⟨4597964, by rfl⟩ : syracuseStep 6130619 = 9195929) B9195929
theorem B3066889 : Blo 1815609 3066889 := bstep (se 2 (by rfl) ⟨1150083, by rfl⟩ : syracuseStep 3066889 = 2300167) B2300167
theorem B2042959 : Blo 1815609 2042959 := bstep (se 1 (by rfl) ⟨1532219, by rfl⟩ : syracuseStep 2042959 = 3064439) B3064439
theorem B11643983 : Blo 1815609 11643983 := bstep (se 1 (by rfl) ⟨8732987, by rfl⟩ : syracuseStep 11643983 = 17465975) B17465975
theorem B3067051 : Blo 1815609 3067051 := bstep (se 1 (by rfl) ⟨2300288, by rfl⟩ : syracuseStep 3067051 = 4600577) B4600577
theorem B2043355 : Blo 1815609 2043355 := bstep (se 1 (by rfl) ⟨1532516, by rfl⟩ : syracuseStep 2043355 = 3065033) B3065033
theorem B27979453 : Blo 1815609 27979453 := bstep (se 3 (by rfl) ⟨5246147, by rfl⟩ : syracuseStep 27979453 = 10492295) B10492295
theorem B10342187 : Blo 1815609 10342187 := bstep (se 1 (by rfl) ⟨7756640, by rfl⟩ : syracuseStep 10342187 = 15513281) B15513281
theorem B7368491 : Blo 1815609 7368491 := bstep (se 1 (by rfl) ⟨5526368, by rfl⟩ : syracuseStep 7368491 = 11052737) B11052737
theorem B4599625 : Blo 1815609 4599625 := bstep (se 2 (by rfl) ⟨1724859, by rfl⟩ : syracuseStep 4599625 = 3449719) B3449719
theorem B2723759 : Blo 1815609 2723759 := bstep (se 1 (by rfl) ⟨2042819, by rfl⟩ : syracuseStep 2723759 = 4085639) B4085639
theorem B2043823 : Blo 1815609 2043823 := bstep (se 1 (by rfl) ⟨1532867, by rfl⟩ : syracuseStep 2043823 = 3065735) B3065735
theorem B4140983 : Blo 1815609 4140983 := bstep (se 1 (by rfl) ⟨3105737, by rfl⟩ : syracuseStep 4140983 = 6211475) B6211475
theorem B6549511 : Blo 1815609 6549511 := bstep (se 1 (by rfl) ⟨4912133, by rfl⟩ : syracuseStep 6549511 = 9824267) B9824267
theorem B2723849 : Blo 1815609 2723849 := bstep (se 2 (by rfl) ⟨1021443, by rfl⟩ : syracuseStep 2723849 = 2042887) B2042887
theorem B17018909 : Blo 1815609 17018909 := bstep (se 3 (by rfl) ⟨3191045, by rfl⟩ : syracuseStep 17018909 = 6382091) B6382091
theorem B2723879 : Blo 1815609 2723879 := bstep (se 1 (by rfl) ⟨2042909, by rfl⟩ : syracuseStep 2723879 = 4085819) B4085819
theorem B2723963 : Blo 1815609 2723963 := bstep (se 1 (by rfl) ⟨2042972, by rfl⟩ : syracuseStep 2723963 = 4085945) B4085945
theorem B28348645 : Blo 1815609 28348645 := bstep (se 4 (by rfl) ⟨2657685, by rfl⟩ : syracuseStep 28348645 = 5315371) B5315371
theorem B2724089 : Blo 1815609 2724089 := bstep (se 2 (by rfl) ⟨1021533, by rfl⟩ : syracuseStep 2724089 = 2043067) B2043067
theorem B3272953 : Blo 1815609 3272953 := bstep (se 2 (by rfl) ⟨1227357, by rfl⟩ : syracuseStep 3272953 = 2454715) B2454715
theorem B10350935 : Blo 1815609 10350935 := bstep (se 1 (by rfl) ⟨7763201, by rfl⟩ : syracuseStep 10350935 = 15526403) B15526403
theorem B2724191 : Blo 1815609 2724191 := bstep (se 1 (by rfl) ⟨2043143, by rfl⟩ : syracuseStep 2724191 = 4086287) B4086287
theorem B2044255 : Blo 1815609 2044255 := bstep (se 1 (by rfl) ⟨1533191, by rfl⟩ : syracuseStep 2044255 = 3066383) B3066383
theorem B2724203 : Blo 1815609 2724203 := bstep (se 1 (by rfl) ⟨2043152, by rfl⟩ : syracuseStep 2724203 = 4086305) B4086305
theorem B13799969 : Blo 1815609 13799969 := bstep (se 2 (by rfl) ⟨5174988, by rfl⟩ : syracuseStep 13799969 = 10349977) B10349977
theorem B9196091 : Blo 1815609 9196091 := bstep (se 1 (by rfl) ⟨6897068, by rfl⟩ : syracuseStep 9196091 = 13794137) B13794137
theorem B2724431 : Blo 1815609 2724431 := bstep (se 1 (by rfl) ⟨2043323, by rfl⟩ : syracuseStep 2724431 = 4086647) B4086647
theorem B6132347 : Blo 1815609 6132347 := bstep (se 1 (by rfl) ⟨4599260, by rfl⟩ : syracuseStep 6132347 = 9198521) B9198521
theorem B2724551 : Blo 1815609 2724551 := bstep (se 1 (by rfl) ⟨2043413, by rfl⟩ : syracuseStep 2724551 = 4086827) B4086827
theorem B2044615 : Blo 1815609 2044615 := bstep (se 1 (by rfl) ⟨1533461, by rfl⟩ : syracuseStep 2044615 = 3066923) B3066923
theorem B3683063 : Blo 1815609 3683063 := bstep (se 1 (by rfl) ⟨2762297, by rfl⟩ : syracuseStep 3683063 = 5524595) B5524595
theorem B26194691 : Blo 1815609 26194691 := bstep (se 1 (by rfl) ⟨19646018, by rfl⟩ : syracuseStep 26194691 = 39292037) B39292037
theorem B6132509 : Blo 1815609 6132509 := bstep (se 3 (by rfl) ⟨1149845, by rfl⟩ : syracuseStep 6132509 = 2299691) B2299691
theorem B2298719 : Blo 1815609 2298719 := bstep (se 1 (by rfl) ⟨1724039, by rfl⟩ : syracuseStep 2298719 = 3448079) B3448079
theorem B2724713 : Blo 1815609 2724713 := bstep (se 2 (by rfl) ⟨1021767, by rfl⟩ : syracuseStep 2724713 = 2043535) B2043535
theorem B2331499 : Blo 1815609 2331499 := bstep (se 1 (by rfl) ⟨1748624, by rfl⟩ : syracuseStep 2331499 = 3497249) B3497249
theorem B3879841 : Blo 1815609 3879841 := bstep (se 2 (by rfl) ⟨1454940, by rfl⟩ : syracuseStep 3879841 = 2909881) B2909881
theorem B3683233 : Blo 1815609 3683233 := bstep (se 2 (by rfl) ⟨1381212, by rfl⟩ : syracuseStep 3683233 = 2762425) B2762425
theorem B2454455 : Blo 1815609 2454455 := bstep (se 1 (by rfl) ⟨1840841, by rfl⟩ : syracuseStep 2454455 = 3681683) B3681683
theorem B2724791 : Blo 1815609 2724791 := bstep (se 1 (by rfl) ⟨2043593, by rfl⟩ : syracuseStep 2724791 = 4087187) B4087187
theorem B4600759 : Blo 1815609 4600759 := bstep (se 1 (by rfl) ⟨3450569, by rfl⟩ : syracuseStep 4600759 = 6901139) B6901139
theorem B2724827 : Blo 1815609 2724827 := bstep (se 1 (by rfl) ⟨2043620, by rfl⟩ : syracuseStep 2724827 = 4087241) B4087241
theorem B20681729 : Blo 1815609 20681729 := bstep (se 2 (by rfl) ⟨7755648, by rfl⟩ : syracuseStep 20681729 = 15511297) B15511297
theorem B1815631 : Blo 1815609 1815631 := bstep (se 1 (by rfl) ⟨1361723, by rfl⟩ : syracuseStep 1815631 = 2723447) B2723447
theorem B5174351 : Blo 1815609 5174351 := bstep (se 1 (by rfl) ⟨3880763, by rfl⟩ : syracuseStep 5174351 = 7761527) B7761527
theorem B1815647 : Blo 1815609 1815647 := bstep (se 1 (by rfl) ⟨1361735, by rfl⟩ : syracuseStep 1815647 = 2723471) B2723471
theorem B1815675 : Blo 1815609 1815675 := bstep (se 1 (by rfl) ⟨1361756, by rfl⟩ : syracuseStep 1815675 = 2723513) B2723513
theorem B1815727 : Blo 1815609 1815727 := bstep (se 1 (by rfl) ⟨1361795, by rfl⟩ : syracuseStep 1815727 = 2723591) B2723591
theorem B9196739 : Blo 1815609 9196739 := bstep (se 1 (by rfl) ⟨6897554, by rfl⟩ : syracuseStep 9196739 = 13795109) B13795109
theorem B1815751 : Blo 1815609 1815751 := bstep (se 1 (by rfl) ⟨1361813, by rfl⟩ : syracuseStep 1815751 = 2723627) B2723627
theorem B1815771 : Blo 1815609 1815771 := bstep (se 1 (by rfl) ⟨1361828, by rfl⟩ : syracuseStep 1815771 = 2723657) B2723657
theorem B3880183 : Blo 1815609 3880183 := bstep (se 1 (by rfl) ⟨2910137, by rfl⟩ : syracuseStep 3880183 = 5820275) B5820275
theorem B1815847 : Blo 1815609 1815847 := bstep (se 1 (by rfl) ⟨1361885, by rfl⟩ : syracuseStep 1815847 = 2723771) B2723771
theorem B1815887 : Blo 1815609 1815887 := bstep (se 1 (by rfl) ⟨1361915, by rfl⟩ : syracuseStep 1815887 = 2723831) B2723831
theorem B1815903 : Blo 1815609 1815903 := bstep (se 1 (by rfl) ⟨1361927, by rfl⟩ : syracuseStep 1815903 = 2723855) B2723855
theorem B1815931 : Blo 1815609 1815931 := bstep (se 1 (by rfl) ⟨1361948, by rfl⟩ : syracuseStep 1815931 = 2723897) B2723897
theorem B4085135 : Blo 1815609 4085135 := bstep (se 1 (by rfl) ⟨3063851, by rfl⟩ : syracuseStep 4085135 = 6127703) B6127703
theorem B1815983 : Blo 1815609 1815983 := bstep (se 1 (by rfl) ⟨1361987, by rfl⟩ : syracuseStep 1815983 = 2723975) B2723975
theorem B2725295 : Blo 1815609 2725295 := bstep (se 1 (by rfl) ⟨2043971, by rfl⟩ : syracuseStep 2725295 = 4087943) B4087943
theorem B1816007 : Blo 1815609 1816007 := bstep (se 1 (by rfl) ⟨1362005, by rfl⟩ : syracuseStep 1816007 = 2724011) B2724011
theorem B1816027 : Blo 1815609 1816027 := bstep (se 1 (by rfl) ⟨1362020, by rfl⟩ : syracuseStep 1816027 = 2724041) B2724041
theorem B6133211 : Blo 1815609 6133211 := bstep (se 1 (by rfl) ⟨4599908, by rfl⟩ : syracuseStep 6133211 = 9199817) B9199817
theorem B5821915 : Blo 1815609 5821915 := bstep (se 1 (by rfl) ⟨4366436, by rfl⟩ : syracuseStep 5821915 = 8732873) B8732873
theorem B2725385 : Blo 1815609 2725385 := bstep (se 2 (by rfl) ⟨1022019, by rfl⟩ : syracuseStep 2725385 = 2044039) B2044039
theorem B1816103 : Blo 1815609 1816103 := bstep (se 1 (by rfl) ⟨1362077, by rfl⟩ : syracuseStep 1816103 = 2724155) B2724155
theorem B2725415 : Blo 1815609 2725415 := bstep (se 1 (by rfl) ⟨2044061, by rfl⟩ : syracuseStep 2725415 = 4088123) B4088123
theorem B1816143 : Blo 1815609 1816143 := bstep (se 1 (by rfl) ⟨1362107, by rfl⟩ : syracuseStep 1816143 = 2724215) B2724215
theorem B1816159 : Blo 1815609 1816159 := bstep (se 1 (by rfl) ⟨1362119, by rfl⟩ : syracuseStep 1816159 = 2724239) B2724239
theorem B1816187 : Blo 1815609 1816187 := bstep (se 1 (by rfl) ⟨1362140, by rfl⟩ : syracuseStep 1816187 = 2724281) B2724281
theorem B2725499 : Blo 1815609 2725499 := bstep (se 1 (by rfl) ⟨2044124, by rfl⟩ : syracuseStep 2725499 = 4088249) B4088249
theorem B1816239 : Blo 1815609 1816239 := bstep (se 1 (by rfl) ⟨1362179, by rfl⟩ : syracuseStep 1816239 = 2724359) B2724359
theorem B1816263 : Blo 1815609 1816263 := bstep (se 1 (by rfl) ⟨1362197, by rfl⟩ : syracuseStep 1816263 = 2724395) B2724395
theorem B4085459 : Blo 1815609 4085459 := bstep (se 1 (by rfl) ⟨3064094, by rfl⟩ : syracuseStep 4085459 = 6128189) B6128189
theorem B1816283 : Blo 1815609 1816283 := bstep (se 1 (by rfl) ⟨1362212, by rfl⟩ : syracuseStep 1816283 = 2724425) B2724425
theorem B2725625 : Blo 1815609 2725625 := bstep (se 2 (by rfl) ⟨1022109, by rfl⟩ : syracuseStep 2725625 = 2044219) B2044219
theorem B1816359 : Blo 1815609 1816359 := bstep (se 1 (by rfl) ⟨1362269, by rfl⟩ : syracuseStep 1816359 = 2724539) B2724539
theorem B1816399 : Blo 1815609 1816399 := bstep (se 1 (by rfl) ⟨1362299, by rfl⟩ : syracuseStep 1816399 = 2724599) B2724599
theorem B1816415 : Blo 1815609 1816415 := bstep (se 1 (by rfl) ⟨1362311, by rfl⟩ : syracuseStep 1816415 = 2724623) B2724623
theorem B2725727 : Blo 1815609 2725727 := bstep (se 1 (by rfl) ⟨2044295, by rfl⟩ : syracuseStep 2725727 = 4088591) B4088591
theorem B2725739 : Blo 1815609 2725739 := bstep (se 1 (by rfl) ⟨2044304, by rfl⟩ : syracuseStep 2725739 = 4088609) B4088609
theorem B1816443 : Blo 1815609 1816443 := bstep (se 1 (by rfl) ⟨1362332, by rfl⟩ : syracuseStep 1816443 = 2724665) B2724665
theorem B1816495 : Blo 1815609 1816495 := bstep (se 1 (by rfl) ⟨1362371, by rfl⟩ : syracuseStep 1816495 = 2724743) B2724743
theorem B1816519 : Blo 1815609 1816519 := bstep (se 1 (by rfl) ⟨1362389, by rfl⟩ : syracuseStep 1816519 = 2724779) B2724779
theorem B1816539 : Blo 1815609 1816539 := bstep (se 1 (by rfl) ⟨1362404, by rfl⟩ : syracuseStep 1816539 = 2724809) B2724809
theorem B13981733 : Blo 1815609 13981733 := bstep (se 4 (by rfl) ⟨1310787, by rfl⟩ : syracuseStep 13981733 = 2621575) B2621575
theorem B1816615 : Blo 1815609 1816615 := bstep (se 1 (by rfl) ⟨1362461, by rfl⟩ : syracuseStep 1816615 = 2724923) B2724923
theorem B5175353 : Blo 1815609 5175353 := bstep (se 2 (by rfl) ⟨1940757, by rfl⟩ : syracuseStep 5175353 = 3881515) B3881515
theorem B1841231 : Blo 1815609 1841231 := bstep (se 1 (by rfl) ⟨1380923, by rfl⟩ : syracuseStep 1841231 = 2761847) B2761847
theorem B1816655 : Blo 1815609 1816655 := bstep (se 1 (by rfl) ⟨1362491, by rfl⟩ : syracuseStep 1816655 = 2724983) B2724983
theorem B2725967 : Blo 1815609 2725967 := bstep (se 1 (by rfl) ⟨2044475, by rfl⟩ : syracuseStep 2725967 = 4088951) B4088951
theorem B20699225 : Blo 1815609 20699225 := bstep (se 2 (by rfl) ⟨7762209, by rfl⟩ : syracuseStep 20699225 = 15524419) B15524419
theorem B1816671 : Blo 1815609 1816671 := bstep (se 1 (by rfl) ⟨1362503, by rfl⟩ : syracuseStep 1816671 = 2725007) B2725007
theorem B1816699 : Blo 1815609 1816699 := bstep (se 1 (by rfl) ⟨1362524, by rfl⟩ : syracuseStep 1816699 = 2725049) B2725049
theorem B6133913 : Blo 1815609 6133913 := bstep (se 2 (by rfl) ⟨2300217, by rfl⟩ : syracuseStep 6133913 = 4600435) B4600435
theorem B1816751 : Blo 1815609 1816751 := bstep (se 1 (by rfl) ⟨1362563, by rfl⟩ : syracuseStep 1816751 = 2725127) B2725127
theorem B1816775 : Blo 1815609 1816775 := bstep (se 1 (by rfl) ⟨1362581, by rfl⟩ : syracuseStep 1816775 = 2725163) B2725163
theorem B2726087 : Blo 1815609 2726087 := bstep (se 1 (by rfl) ⟨2044565, by rfl⟩ : syracuseStep 2726087 = 4089131) B4089131
theorem B1816795 : Blo 1815609 1816795 := bstep (se 1 (by rfl) ⟨1362596, by rfl⟩ : syracuseStep 1816795 = 2725193) B2725193
theorem B3447031 : Blo 1815609 3447031 := bstep (se 1 (by rfl) ⟨2585273, by rfl⟩ : syracuseStep 3447031 = 5170547) B5170547
theorem B1816871 : Blo 1815609 1816871 := bstep (se 1 (by rfl) ⟨1362653, by rfl⟩ : syracuseStep 1816871 = 2725307) B2725307
theorem B1816911 : Blo 1815609 1816911 := bstep (se 1 (by rfl) ⟨1362683, by rfl⟩ : syracuseStep 1816911 = 2725367) B2725367
theorem B1816927 : Blo 1815609 1816927 := bstep (se 1 (by rfl) ⟨1362695, by rfl⟩ : syracuseStep 1816927 = 2725391) B2725391
theorem B2726249 : Blo 1815609 2726249 := bstep (se 2 (by rfl) ⟨1022343, by rfl⟩ : syracuseStep 2726249 = 2044687) B2044687
theorem B1816955 : Blo 1815609 1816955 := bstep (se 1 (by rfl) ⟨1362716, by rfl⟩ : syracuseStep 1816955 = 2725433) B2725433
theorem B1817007 : Blo 1815609 1817007 := bstep (se 1 (by rfl) ⟨1362755, by rfl⟩ : syracuseStep 1817007 = 2725511) B2725511
theorem B2726327 : Blo 1815609 2726327 := bstep (se 1 (by rfl) ⟨2044745, by rfl⟩ : syracuseStep 2726327 = 4089491) B4089491
theorem B3684791 : Blo 1815609 3684791 := bstep (se 1 (by rfl) ⟨2763593, by rfl⟩ : syracuseStep 3684791 = 5527187) B5527187
theorem B1817031 : Blo 1815609 1817031 := bstep (se 1 (by rfl) ⟨1362773, by rfl⟩ : syracuseStep 1817031 = 2725547) B2725547
theorem B1817051 : Blo 1815609 1817051 := bstep (se 1 (by rfl) ⟨1362788, by rfl⟩ : syracuseStep 1817051 = 2725577) B2725577
theorem B2726363 : Blo 1815609 2726363 := bstep (se 1 (by rfl) ⟨2044772, by rfl⟩ : syracuseStep 2726363 = 4089545) B4089545
theorem B52369901 : Blo 1815609 52369901 := bstep (se 3 (by rfl) ⟨9819356, by rfl⟩ : syracuseStep 52369901 = 19638713) B19638713
theorem B7363105 : Blo 1815609 7363105 := bstep (se 2 (by rfl) ⟨2761164, by rfl⟩ : syracuseStep 7363105 = 5522329) B5522329
theorem B3447335 : Blo 1815609 3447335 := bstep (se 1 (by rfl) ⟨2585501, by rfl⟩ : syracuseStep 3447335 = 5171003) B5171003
theorem B1817127 : Blo 1815609 1817127 := bstep (se 1 (by rfl) ⟨1362845, by rfl⟩ : syracuseStep 1817127 = 2725691) B2725691
theorem B1817167 : Blo 1815609 1817167 := bstep (se 1 (by rfl) ⟨1362875, by rfl⟩ : syracuseStep 1817167 = 2725751) B2725751
theorem B1817183 : Blo 1815609 1817183 := bstep (se 1 (by rfl) ⟨1362887, by rfl⟩ : syracuseStep 1817183 = 2725775) B2725775
theorem B4086395 : Blo 1815609 4086395 := bstep (se 1 (by rfl) ⟨3064796, by rfl⟩ : syracuseStep 4086395 = 6129593) B6129593
theorem B1817211 : Blo 1815609 1817211 := bstep (se 1 (by rfl) ⟨1362908, by rfl⟩ : syracuseStep 1817211 = 2725817) B2725817
theorem B1817263 : Blo 1815609 1817263 := bstep (se 1 (by rfl) ⟨1362947, by rfl⟩ : syracuseStep 1817263 = 2725895) B2725895
theorem B6544061 : Blo 1815609 6544061 := bstep (se 3 (by rfl) ⟨1227011, by rfl⟩ : syracuseStep 6544061 = 2454023) B2454023
theorem B1817287 : Blo 1815609 1817287 := bstep (se 1 (by rfl) ⟨1362965, by rfl⟩ : syracuseStep 1817287 = 2725931) B2725931
theorem B1817307 : Blo 1815609 1817307 := bstep (se 1 (by rfl) ⟨1362980, by rfl⟩ : syracuseStep 1817307 = 2725961) B2725961
theorem B4086521 : Blo 1815609 4086521 := bstep (se 2 (by rfl) ⟨1532445, by rfl⟩ : syracuseStep 4086521 = 3064891) B3064891
theorem B1817383 : Blo 1815609 1817383 := bstep (se 1 (by rfl) ⟨1363037, by rfl⟩ : syracuseStep 1817383 = 2726075) B2726075
theorem B1817423 : Blo 1815609 1817423 := bstep (se 1 (by rfl) ⟨1363067, by rfl⟩ : syracuseStep 1817423 = 2726135) B2726135
theorem B1817439 : Blo 1815609 1817439 := bstep (se 1 (by rfl) ⟨1363079, by rfl⟩ : syracuseStep 1817439 = 2726159) B2726159
theorem B1817467 : Blo 1815609 1817467 := bstep (se 1 (by rfl) ⟨1363100, by rfl⟩ : syracuseStep 1817467 = 2726201) B2726201
theorem B1817519 : Blo 1815609 1817519 := bstep (se 1 (by rfl) ⟨1363139, by rfl⟩ : syracuseStep 1817519 = 2726279) B2726279
theorem B1817543 : Blo 1815609 1817543 := bstep (se 1 (by rfl) ⟨1363157, by rfl⟩ : syracuseStep 1817543 = 2726315) B2726315
theorem B1842139 : Blo 1815609 1842139 := bstep (se 1 (by rfl) ⟨1381604, by rfl⟩ : syracuseStep 1842139 = 2763209) B2763209
theorem B1817563 : Blo 1815609 1817563 := bstep (se 1 (by rfl) ⟨1363172, by rfl⟩ : syracuseStep 1817563 = 2726345) B2726345
theorem B4086791 : Blo 1815609 4086791 := bstep (se 1 (by rfl) ⟨3065093, by rfl⟩ : syracuseStep 4086791 = 6130187) B6130187
theorem B24853547 : Blo 1815609 24853547 := bstep (se 1 (by rfl) ⟨18640160, by rfl⟩ : syracuseStep 24853547 = 37280321) B37280321
theorem B7756879 : Blo 1815609 7756879 := bstep (se 1 (by rfl) ⟨5817659, by rfl⟩ : syracuseStep 7756879 = 11635319) B11635319
theorem B4086863 : Blo 1815609 4086863 := bstep (se 1 (by rfl) ⟨3065147, by rfl⟩ : syracuseStep 4086863 = 6130295) B6130295
theorem B117857429 : Blo 1815609 117857429 := bstep (se 6 (by rfl) ⟨2762283, by rfl⟩ : syracuseStep 117857429 = 5524567) B5524567
theorem B13090085 : Blo 1815609 13090085 := bstep (se 4 (by rfl) ⟨1227195, by rfl⟩ : syracuseStep 13090085 = 2454391) B2454391
theorem B4365697 : Blo 1815609 4365697 := bstep (se 2 (by rfl) ⟨1637136, by rfl⟩ : syracuseStep 4365697 = 3274273) B3274273
theorem B1965487 : Blo 1815609 1965487 := bstep (se 1 (by rfl) ⟨1474115, by rfl⟩ : syracuseStep 1965487 = 2948231) B2948231
theorem B4087259 : Blo 1815609 4087259 := bstep (se 1 (by rfl) ⟨3065444, by rfl⟩ : syracuseStep 4087259 = 6130889) B6130889
theorem B31055399 : Blo 1815609 31055399 := bstep (se 1 (by rfl) ⟨23291549, by rfl⟩ : syracuseStep 31055399 = 46583099) B46583099
theorem B4423265 : Blo 1815609 4423265 := bstep (se 2 (by rfl) ⟨1658724, by rfl⟩ : syracuseStep 4423265 = 3317449) B3317449
theorem B111894155 : Blo 1815609 111894155 := bstep (se 1 (by rfl) ⟨83920616, by rfl⟩ : syracuseStep 111894155 = 167841233) B167841233
theorem B10346129 : Blo 1815609 10346129 := bstep (se 2 (by rfl) ⟨3879798, by rfl⟩ : syracuseStep 10346129 = 7759597) B7759597
theorem B14737085 : Blo 1815609 14737085 := bstep (se 3 (by rfl) ⟨2763203, by rfl⟩ : syracuseStep 14737085 = 5526407) B5526407
theorem B3448649 : Blo 1815609 3448649 := bstep (se 2 (by rfl) ⟨1293243, by rfl⟩ : syracuseStep 3448649 = 2586487) B2586487
theorem B4366187 : Blo 1815609 4366187 := bstep (se 1 (by rfl) ⟨3274640, by rfl⟩ : syracuseStep 4366187 = 6549281) B6549281
theorem B4087727 : Blo 1815609 4087727 := bstep (se 1 (by rfl) ⟨3065795, by rfl⟩ : syracuseStep 4087727 = 6131591) B6131591
theorem B14737339 : Blo 1815609 14737339 := bstep (se 1 (by rfl) ⟨11053004, by rfl⟩ : syracuseStep 14737339 = 22106009) B22106009
theorem B4087817 : Blo 1815609 4087817 := bstep (se 2 (by rfl) ⟨1532931, by rfl⟩ : syracuseStep 4087817 = 3065863) B3065863
theorem B8732681 : Blo 1815609 8732681 := bstep (se 2 (by rfl) ⟨3274755, by rfl⟩ : syracuseStep 8732681 = 6549511) B6549511
theorem B11345939 : Blo 1815609 11345939 := bstep (se 1 (by rfl) ⟨8509454, by rfl⟩ : syracuseStep 11345939 = 17018909) B17018909
theorem B4596041 : Blo 1815609 4596041 := bstep (se 2 (by rfl) ⟨1723515, by rfl⟩ : syracuseStep 4596041 = 3447031) B3447031
theorem B9199979 : Blo 1815609 9199979 := bstep (se 1 (by rfl) ⟨6899984, by rfl⟩ : syracuseStep 9199979 = 13799969) B13799969
theorem B34914725 : Blo 1815609 34914725 := bstep (se 4 (by rfl) ⟨3273255, by rfl⟩ : syracuseStep 34914725 = 6546511) B6546511
theorem B4088231 : Blo 1815609 4088231 := bstep (se 1 (by rfl) ⟨3066173, by rfl⟩ : syracuseStep 4088231 = 6132347) B6132347
theorem B7758281 : Blo 1815609 7758281 := bstep (se 2 (by rfl) ⟨2909355, by rfl⟩ : syracuseStep 7758281 = 5818711) B5818711
theorem B4088339 : Blo 1815609 4088339 := bstep (se 1 (by rfl) ⟨3066254, by rfl⟩ : syracuseStep 4088339 = 6132509) B6132509
theorem B4424255 : Blo 1815609 4424255 := bstep (se 1 (by rfl) ⟨3318191, by rfl⟩ : syracuseStep 4424255 = 6636383) B6636383
theorem B4088393 : Blo 1815609 4088393 := bstep (se 2 (by rfl) ⟨1533147, by rfl⟩ : syracuseStep 4088393 = 3066295) B3066295
theorem B1291240055 : Blo 1815609 1291240055 := bstep (se 1 (by rfl) ⟨968430041, by rfl⟩ : syracuseStep 1291240055 = 1936860083) B1936860083
theorem B80724599 : Blo 1815609 80724599 := bstep (se 1 (by rfl) ⟨60543449, by rfl⟩ : syracuseStep 80724599 = 121086899) B121086899
theorem B13787819 : Blo 1815609 13787819 := bstep (se 1 (by rfl) ⟨10340864, by rfl⟩ : syracuseStep 13787819 = 20681729) B20681729
theorem B6128351 : Blo 1815609 6128351 := bstep (se 1 (by rfl) ⟨4596263, by rfl⟩ : syracuseStep 6128351 = 9192527) B9192527
theorem B3449567 : Blo 1815609 3449567 := bstep (se 1 (by rfl) ⟨2587175, by rfl⟩ : syracuseStep 3449567 = 5174351) B5174351
theorem B3064655 : Blo 1815609 3064655 := bstep (se 1 (by rfl) ⟨2298491, by rfl⟩ : syracuseStep 3064655 = 4596983) B4596983
theorem B4088807 : Blo 1815609 4088807 := bstep (se 1 (by rfl) ⟨3066605, by rfl⟩ : syracuseStep 4088807 = 6133211) B6133211
theorem B6898679 : Blo 1815609 6898679 := bstep (se 1 (by rfl) ⟨5174009, by rfl⟩ : syracuseStep 6898679 = 10348019) B10348019
theorem B6128783 : Blo 1815609 6128783 := bstep (se 1 (by rfl) ⟨4596587, by rfl⟩ : syracuseStep 6128783 = 9193175) B9193175
theorem B4089185 : Blo 1815609 4089185 := bstep (se 2 (by rfl) ⟨1533444, by rfl⟩ : syracuseStep 4089185 = 3066889) B3066889
theorem B4089275 : Blo 1815609 4089275 := bstep (se 1 (by rfl) ⟨3066956, by rfl⟩ : syracuseStep 4089275 = 6133913) B6133913
theorem B4089401 : Blo 1815609 4089401 := bstep (se 2 (by rfl) ⟨1533525, by rfl⟩ : syracuseStep 4089401 = 3067051) B3067051
theorem B9201437 : Blo 1815609 9201437 := bstep (se 3 (by rfl) ⟨1725269, by rfl⟩ : syracuseStep 9201437 = 3450539) B3450539
theorem B3065647 : Blo 1815609 3065647 := bstep (se 1 (by rfl) ⟨2299235, by rfl⟩ : syracuseStep 3065647 = 4598471) B4598471
theorem B20694851 : Blo 1815609 20694851 := bstep (se 1 (by rfl) ⟨15521138, by rfl⟩ : syracuseStep 20694851 = 31042277) B31042277
theorem B78571619 : Blo 1815609 78571619 := bstep (se 1 (by rfl) ⟨58928714, by rfl⟩ : syracuseStep 78571619 = 117857429) B117857429
theorem B8726723 : Blo 1815609 8726723 := bstep (se 1 (by rfl) ⟨6545042, by rfl⟩ : syracuseStep 8726723 = 13090085) B13090085
theorem B6129917 : Blo 1815609 6129917 := bstep (se 3 (by rfl) ⟨1149359, by rfl⟩ : syracuseStep 6129917 = 2298719) B2298719
theorem B20703599 : Blo 1815609 20703599 := bstep (se 1 (by rfl) ⟨15527699, by rfl⟩ : syracuseStep 20703599 = 31055399) B31055399
theorem B9824723 : Blo 1815609 9824723 := bstep (se 1 (by rfl) ⟨7368542, by rfl⟩ : syracuseStep 9824723 = 14737085) B14737085
theorem B2910791 : Blo 1815609 2910791 := bstep (se 1 (by rfl) ⟨2183093, by rfl⟩ : syracuseStep 2910791 = 4366187) B4366187
theorem B10488509 : Blo 1815609 10488509 := bstep (se 3 (by rfl) ⟨1966595, by rfl⟩ : syracuseStep 10488509 = 3933191) B3933191
theorem B2042671 : Blo 1815609 2042671 := bstep (se 1 (by rfl) ⟨1532003, by rfl⟩ : syracuseStep 2042671 = 3064007) B3064007
theorem B4909949 : Blo 1815609 4909949 := bstep (se 3 (by rfl) ⟨920615, by rfl⟩ : syracuseStep 4909949 = 1841231) B1841231
theorem B6900623 : Blo 1815609 6900623 := bstep (se 1 (by rfl) ⟨5175467, by rfl⟩ : syracuseStep 6900623 = 10350935) B10350935
theorem B2042779 : Blo 1815609 2042779 := bstep (se 1 (by rfl) ⟨1532084, by rfl⟩ : syracuseStep 2042779 = 3064169) B3064169
theorem B19631105 : Blo 1815609 19631105 := bstep (se 2 (by rfl) ⟨7361664, by rfl⟩ : syracuseStep 19631105 = 14723329) B14723329
theorem B6130727 : Blo 1815609 6130727 := bstep (se 1 (by rfl) ⟨4598045, by rfl⟩ : syracuseStep 6130727 = 9196091) B9196091
theorem B4598927 : Blo 1815609 4598927 := bstep (se 1 (by rfl) ⟨3449195, by rfl⟩ : syracuseStep 4598927 = 6898391) B6898391
theorem B2043175 : Blo 1815609 2043175 := bstep (se 1 (by rfl) ⟨1532381, by rfl⟩ : syracuseStep 2043175 = 3064763) B3064763
theorem B2043247 : Blo 1815609 2043247 := bstep (se 1 (by rfl) ⟨1532435, by rfl⟩ : syracuseStep 2043247 = 3064871) B3064871
theorem B6131159 : Blo 1815609 6131159 := bstep (se 1 (by rfl) ⟨4598369, by rfl⟩ : syracuseStep 6131159 = 9196739) B9196739
theorem B2043463 : Blo 1815609 2043463 := bstep (se 1 (by rfl) ⟨1532597, by rfl⟩ : syracuseStep 2043463 = 3065195) B3065195
theorem B2723423 : Blo 1815609 2723423 := bstep (se 1 (by rfl) ⟨2042567, by rfl⟩ : syracuseStep 2723423 = 4085135) B4085135
theorem B2723639 : Blo 1815609 2723639 := bstep (se 1 (by rfl) ⟨2042729, by rfl⟩ : syracuseStep 2723639 = 4085459) B4085459
theorem B3878713 : Blo 1815609 3878713 := bstep (se 2 (by rfl) ⟨1454517, by rfl⟩ : syracuseStep 3878713 = 2909035) B2909035
theorem B3108665 : Blo 1815609 3108665 := bstep (se 2 (by rfl) ⟨1165749, by rfl⟩ : syracuseStep 3108665 = 2331499) B2331499
theorem B9826109 : Blo 1815609 9826109 := bstep (se 3 (by rfl) ⟨1842395, by rfl⟩ : syracuseStep 9826109 = 3684791) B3684791
theorem B5173121 : Blo 1815609 5173121 := bstep (se 2 (by rfl) ⟨1939920, by rfl⟩ : syracuseStep 5173121 = 3879841) B3879841
theorem B4910977 : Blo 1815609 4910977 := bstep (se 2 (by rfl) ⟨1841616, by rfl⟩ : syracuseStep 4910977 = 3683233) B3683233
theorem B13799483 : Blo 1815609 13799483 := bstep (se 1 (by rfl) ⟨10349612, by rfl⟩ : syracuseStep 13799483 = 20699225) B20699225
theorem B2723945 : Blo 1815609 2723945 := bstep (se 2 (by rfl) ⟨1021479, by rfl⟩ : syracuseStep 2723945 = 2042959) B2042959
theorem B10342505 : Blo 1815609 10342505 := bstep (se 2 (by rfl) ⟨3878439, by rfl⟩ : syracuseStep 10342505 = 7756879) B7756879
theorem B5173577 : Blo 1815609 5173577 := bstep (se 2 (by rfl) ⟨1940091, by rfl⟩ : syracuseStep 5173577 = 3880183) B3880183
theorem B2298223 : Blo 1815609 2298223 := bstep (se 1 (by rfl) ⟨1723667, by rfl⟩ : syracuseStep 2298223 = 3447335) B3447335
theorem B2724263 : Blo 1815609 2724263 := bstep (se 1 (by rfl) ⟨2043197, by rfl⟩ : syracuseStep 2724263 = 4086395) B4086395
theorem B2044327 : Blo 1815609 2044327 := bstep (se 1 (by rfl) ⟨1533245, by rfl⟩ : syracuseStep 2044327 = 3066491) B3066491
theorem B4362707 : Blo 1815609 4362707 := bstep (se 1 (by rfl) ⟨3272030, by rfl⟩ : syracuseStep 4362707 = 6544061) B6544061
theorem B13791707 : Blo 1815609 13791707 := bstep (se 1 (by rfl) ⟨10343780, by rfl⟩ : syracuseStep 13791707 = 20687561) B20687561
theorem B2724347 : Blo 1815609 2724347 := bstep (se 1 (by rfl) ⟨2043260, by rfl⟩ : syracuseStep 2724347 = 4086521) B4086521
theorem B5820929 : Blo 1815609 5820929 := bstep (se 2 (by rfl) ⟨2182848, by rfl⟩ : syracuseStep 5820929 = 4365697) B4365697
theorem B4911635 : Blo 1815609 4911635 := bstep (se 1 (by rfl) ⟨3683726, by rfl⟩ : syracuseStep 4911635 = 7367453) B7367453
theorem B2724473 : Blo 1815609 2724473 := bstep (se 2 (by rfl) ⟨1021677, by rfl⟩ : syracuseStep 2724473 = 2043355) B2043355
theorem B7762553 : Blo 1815609 7762553 := bstep (se 2 (by rfl) ⟨2910957, by rfl⟩ : syracuseStep 7762553 = 5821915) B5821915
theorem B2724527 : Blo 1815609 2724527 := bstep (se 1 (by rfl) ⟨2043395, by rfl⟩ : syracuseStep 2724527 = 4086791) B4086791
theorem B16569031 : Blo 1815609 16569031 := bstep (se 1 (by rfl) ⟨12426773, by rfl⟩ : syracuseStep 16569031 = 24853547) B24853547
theorem B2724575 : Blo 1815609 2724575 := bstep (se 1 (by rfl) ⟨2043431, by rfl⟩ : syracuseStep 2724575 = 4086863) B4086863
theorem B7762655 : Blo 1815609 7762655 := bstep (se 1 (by rfl) ⟨5821991, by rfl⟩ : syracuseStep 7762655 = 11643983) B11643983
theorem B604771093 : Blo 1815609 604771093 := bstep (se 6 (by rfl) ⟨14174322, by rfl⟩ : syracuseStep 604771093 = 28348645) B28348645
theorem B2724839 : Blo 1815609 2724839 := bstep (se 1 (by rfl) ⟨2043629, by rfl⟩ : syracuseStep 2724839 = 4087259) B4087259
theorem B15512633 : Blo 1815609 15512633 := bstep (se 2 (by rfl) ⟨5817237, by rfl⟩ : syracuseStep 15512633 = 11634475) B11634475
theorem B6132833 : Blo 1815609 6132833 := bstep (se 2 (by rfl) ⟨2299812, by rfl⟩ : syracuseStep 6132833 = 4599625) B4599625
theorem B13087889 : Blo 1815609 13087889 := bstep (se 2 (by rfl) ⟨4907958, by rfl⟩ : syracuseStep 13087889 = 9815917) B9815917
theorem B6894791 : Blo 1815609 6894791 := bstep (se 1 (by rfl) ⟨5171093, by rfl⟩ : syracuseStep 6894791 = 10342187) B10342187
theorem B4912327 : Blo 1815609 4912327 := bstep (se 1 (by rfl) ⟨3684245, by rfl⟩ : syracuseStep 4912327 = 7368491) B7368491
theorem B2299099 : Blo 1815609 2299099 := bstep (se 1 (by rfl) ⟨1724324, by rfl⟩ : syracuseStep 2299099 = 3448649) B3448649
theorem B2725097 : Blo 1815609 2725097 := bstep (se 2 (by rfl) ⟨1021911, by rfl⟩ : syracuseStep 2725097 = 2043823) B2043823
theorem B19649785 : Blo 1815609 19649785 := bstep (se 2 (by rfl) ⟨7368669, by rfl⟩ : syracuseStep 19649785 = 14737339) B14737339
theorem B1815839 : Blo 1815609 1815839 := bstep (se 1 (by rfl) ⟨1361879, by rfl⟩ : syracuseStep 1815839 = 2723759) B2723759
theorem B2725151 : Blo 1815609 2725151 := bstep (se 1 (by rfl) ⟨2043863, by rfl⟩ : syracuseStep 2725151 = 4087727) B4087727
theorem B1815899 : Blo 1815609 1815899 := bstep (se 1 (by rfl) ⟨1361924, by rfl⟩ : syracuseStep 1815899 = 2723849) B2723849
theorem B1815919 : Blo 1815609 1815919 := bstep (se 1 (by rfl) ⟨1361939, by rfl⟩ : syracuseStep 1815919 = 2723879) B2723879
theorem B17700221 : Blo 1815609 17700221 := bstep (se 3 (by rfl) ⟨3318791, by rfl⟩ : syracuseStep 17700221 = 6637583) B6637583
theorem B4085153 : Blo 1815609 4085153 := bstep (se 2 (by rfl) ⟨1531932, by rfl⟩ : syracuseStep 4085153 = 3063865) B3063865
theorem B1815975 : Blo 1815609 1815975 := bstep (se 1 (by rfl) ⟨1361981, by rfl⟩ : syracuseStep 1815975 = 2723963) B2723963
theorem B9573821 : Blo 1815609 9573821 := bstep (se 3 (by rfl) ⟨1795091, by rfl⟩ : syracuseStep 9573821 = 3590183) B3590183
theorem B2725319 : Blo 1815609 2725319 := bstep (se 1 (by rfl) ⟨2043989, by rfl⟩ : syracuseStep 2725319 = 4087979) B4087979
theorem B13800941 : Blo 1815609 13800941 := bstep (se 3 (by rfl) ⟨2587676, by rfl⟩ : syracuseStep 13800941 = 5175353) B5175353
theorem B1816059 : Blo 1815609 1816059 := bstep (se 1 (by rfl) ⟨1362044, by rfl⟩ : syracuseStep 1816059 = 2724089) B2724089
theorem B39269893 : Blo 1815609 39269893 := bstep (se 4 (by rfl) ⟨3681552, by rfl⟩ : syracuseStep 39269893 = 7363105) B7363105
theorem B9197063 : Blo 1815609 9197063 := bstep (se 1 (by rfl) ⟨6897797, by rfl⟩ : syracuseStep 9197063 = 13795595) B13795595
theorem B1816127 : Blo 1815609 1816127 := bstep (se 1 (by rfl) ⟨1362095, by rfl⟩ : syracuseStep 1816127 = 2724191) B2724191
theorem B1939015 : Blo 1815609 1939015 := bstep (se 1 (by rfl) ⟨1454261, by rfl⟩ : syracuseStep 1939015 = 2908523) B2908523
theorem B1816135 : Blo 1815609 1816135 := bstep (se 1 (by rfl) ⟨1362101, by rfl⟩ : syracuseStep 1816135 = 2724203) B2724203
theorem B4363937 : Blo 1815609 4363937 := bstep (se 2 (by rfl) ⟨1636476, by rfl⟩ : syracuseStep 4363937 = 3272953) B3272953
theorem B1816287 : Blo 1815609 1816287 := bstep (se 1 (by rfl) ⟨1362215, by rfl⟩ : syracuseStep 1816287 = 2724431) B2724431
theorem B2725673 : Blo 1815609 2725673 := bstep (se 2 (by rfl) ⟨1022127, by rfl⟩ : syracuseStep 2725673 = 2044255) B2044255
theorem B1816367 : Blo 1815609 1816367 := bstep (se 1 (by rfl) ⟨1362275, by rfl⟩ : syracuseStep 1816367 = 2724551) B2724551
theorem B2725679 : Blo 1815609 2725679 := bstep (se 1 (by rfl) ⟨2044259, by rfl⟩ : syracuseStep 2725679 = 4088519) B4088519
theorem B2455375 : Blo 1815609 2455375 := bstep (se 1 (by rfl) ⟨1841531, by rfl⟩ : syracuseStep 2455375 = 3683063) B3683063
theorem B17463127 : Blo 1815609 17463127 := bstep (se 1 (by rfl) ⟨13097345, by rfl⟩ : syracuseStep 17463127 = 26194691) B26194691
theorem B29472605 : Blo 1815609 29472605 := bstep (se 3 (by rfl) ⟨5526113, by rfl⟩ : syracuseStep 29472605 = 11052227) B11052227
theorem B1816475 : Blo 1815609 1816475 := bstep (se 1 (by rfl) ⟨1362356, by rfl⟩ : syracuseStep 1816475 = 2724713) B2724713
theorem B4085711 : Blo 1815609 4085711 := bstep (se 1 (by rfl) ⟨3064283, by rfl⟩ : syracuseStep 4085711 = 6128567) B6128567
theorem B1816527 : Blo 1815609 1816527 := bstep (se 1 (by rfl) ⟨1362395, by rfl⟩ : syracuseStep 1816527 = 2724791) B2724791
theorem B1816551 : Blo 1815609 1816551 := bstep (se 1 (by rfl) ⟨1362413, by rfl⟩ : syracuseStep 1816551 = 2724827) B2724827
theorem B9197549 : Blo 1815609 9197549 := bstep (se 3 (by rfl) ⟨1724540, by rfl⟩ : syracuseStep 9197549 = 3449081) B3449081
theorem B2726153 : Blo 1815609 2726153 := bstep (se 2 (by rfl) ⟨1022307, by rfl⟩ : syracuseStep 2726153 = 2044615) B2044615
theorem B1816863 : Blo 1815609 1816863 := bstep (se 1 (by rfl) ⟨1362647, by rfl⟩ : syracuseStep 1816863 = 2725295) B2725295
theorem B4086089 : Blo 1815609 4086089 := bstep (se 2 (by rfl) ⟨1532283, by rfl⟩ : syracuseStep 4086089 = 3064567) B3064567
theorem B18897229 : Blo 1815609 18897229 := bstep (se 3 (by rfl) ⟨3543230, by rfl⟩ : syracuseStep 18897229 = 7086461) B7086461
theorem B4086107 : Blo 1815609 4086107 := bstep (se 1 (by rfl) ⟨3064580, by rfl⟩ : syracuseStep 4086107 = 6129161) B6129161
theorem B1816923 : Blo 1815609 1816923 := bstep (se 1 (by rfl) ⟨1362692, by rfl⟩ : syracuseStep 1816923 = 2725385) B2725385
theorem B1816943 : Blo 1815609 1816943 := bstep (se 1 (by rfl) ⟨1362707, by rfl⟩ : syracuseStep 1816943 = 2725415) B2725415
theorem B2726255 : Blo 1815609 2726255 := bstep (se 1 (by rfl) ⟨2044691, by rfl⟩ : syracuseStep 2726255 = 4089383) B4089383
theorem B1939835 : Blo 1815609 1939835 := bstep (se 1 (by rfl) ⟨1454876, by rfl⟩ : syracuseStep 1939835 = 2909753) B2909753
theorem B1816999 : Blo 1815609 1816999 := bstep (se 1 (by rfl) ⟨1362749, by rfl⟩ : syracuseStep 1816999 = 2725499) B2725499
theorem B6134183 : Blo 1815609 6134183 := bstep (se 1 (by rfl) ⟨4600637, by rfl⟩ : syracuseStep 6134183 = 9201275) B9201275
theorem B34912721 : Blo 1815609 34912721 := bstep (se 2 (by rfl) ⟨13092270, by rfl⟩ : syracuseStep 34912721 = 26184541) B26184541
theorem B9198035 : Blo 1815609 9198035 := bstep (se 1 (by rfl) ⟨6898526, by rfl⟩ : syracuseStep 9198035 = 13797053) B13797053
theorem B1817083 : Blo 1815609 1817083 := bstep (se 1 (by rfl) ⟨1362812, by rfl⟩ : syracuseStep 1817083 = 2725625) B2725625
theorem B1817151 : Blo 1815609 1817151 := bstep (se 1 (by rfl) ⟨1362863, by rfl⟩ : syracuseStep 1817151 = 2725727) B2725727
theorem B1817159 : Blo 1815609 1817159 := bstep (se 1 (by rfl) ⟨1362869, by rfl⟩ : syracuseStep 1817159 = 2725739) B2725739
theorem B14735945 : Blo 1815609 14735945 := bstep (se 2 (by rfl) ⟨5525979, by rfl⟩ : syracuseStep 14735945 = 11051959) B11051959
theorem B6134345 : Blo 1815609 6134345 := bstep (se 2 (by rfl) ⟨2300379, by rfl⟩ : syracuseStep 6134345 = 4600759) B4600759
theorem B2456185 : Blo 1815609 2456185 := bstep (se 2 (by rfl) ⟨921069, by rfl⟩ : syracuseStep 2456185 = 1842139) B1842139
theorem B4364975 : Blo 1815609 4364975 := bstep (se 1 (by rfl) ⟨3273731, by rfl⟩ : syracuseStep 4364975 = 6547463) B6547463
theorem B9321155 : Blo 1815609 9321155 := bstep (se 1 (by rfl) ⟨6990866, by rfl⟩ : syracuseStep 9321155 = 13981733) B13981733
theorem B1817311 : Blo 1815609 1817311 := bstep (se 1 (by rfl) ⟨1362983, by rfl⟩ : syracuseStep 1817311 = 2725967) B2725967
theorem B9198359 : Blo 1815609 9198359 := bstep (se 1 (by rfl) ⟨6898769, by rfl⟩ : syracuseStep 9198359 = 13797539) B13797539
theorem B1817391 : Blo 1815609 1817391 := bstep (se 1 (by rfl) ⟨1363043, by rfl⟩ : syracuseStep 1817391 = 2726087) B2726087
theorem B4086683 : Blo 1815609 4086683 := bstep (se 1 (by rfl) ⟨3065012, by rfl⟩ : syracuseStep 4086683 = 6130025) B6130025
theorem B1817499 : Blo 1815609 1817499 := bstep (se 1 (by rfl) ⟨1363124, by rfl⟩ : syracuseStep 1817499 = 2726249) B2726249
theorem B1817551 : Blo 1815609 1817551 := bstep (se 1 (by rfl) ⟨1363163, by rfl⟩ : syracuseStep 1817551 = 2726327) B2726327
theorem B1817575 : Blo 1815609 1817575 := bstep (se 1 (by rfl) ⟨1363181, by rfl⟩ : syracuseStep 1817575 = 2726363) B2726363
theorem B34913267 : Blo 1815609 34913267 := bstep (se 1 (by rfl) ⟨26184950, by rfl⟩ : syracuseStep 34913267 = 52369901) B52369901
theorem B4086881 : Blo 1815609 4086881 := bstep (se 2 (by rfl) ⟨1532580, by rfl⟩ : syracuseStep 4086881 = 3065161) B3065161
theorem B3316879 : Blo 1815609 3316879 := bstep (se 1 (by rfl) ⟨2487659, by rfl⟩ : syracuseStep 3316879 = 4975319) B4975319
theorem B2620649 : Blo 1815609 2620649 := bstep (se 2 (by rfl) ⟨982743, by rfl⟩ : syracuseStep 2620649 = 1965487) B1965487
theorem B4087079 : Blo 1815609 4087079 := bstep (se 1 (by rfl) ⟨3065309, by rfl⟩ : syracuseStep 4087079 = 6130619) B6130619
theorem B7757153 : Blo 1815609 7757153 := bstep (se 2 (by rfl) ⟨2908932, by rfl⟩ : syracuseStep 7757153 = 5817865) B5817865
theorem B37305937 : Blo 1815609 37305937 := bstep (se 2 (by rfl) ⟨13989726, by rfl⟩ : syracuseStep 37305937 = 27979453) B27979453
theorem B4087457 : Blo 1815609 4087457 := bstep (se 2 (by rfl) ⟨1532796, by rfl⟩ : syracuseStep 4087457 = 3065593) B3065593
theorem B2948843 : Blo 1815609 2948843 := bstep (se 1 (by rfl) ⟨2211632, by rfl⟩ : syracuseStep 2948843 = 4423265) B4423265
theorem B74596103 : Blo 1815609 74596103 := bstep (se 1 (by rfl) ⟨55947077, by rfl⟩ : syracuseStep 74596103 = 111894155) B111894155
theorem B6897419 : Blo 1815609 6897419 := bstep (se 1 (by rfl) ⟨5173064, by rfl⟩ : syracuseStep 6897419 = 10346129) B10346129
theorem B6545213 : Blo 1815609 6545213 := bstep (se 3 (by rfl) ⟨1227227, by rfl⟩ : syracuseStep 6545213 = 2454455) B2454455
theorem B2760655 : Blo 1815609 2760655 := bstep (se 1 (by rfl) ⟨2070491, by rfl⟩ : syracuseStep 2760655 = 4140983) B4140983
theorem B9199655 : Blo 1815609 9199655 := bstep (se 1 (by rfl) ⟨6899741, by rfl⟩ : syracuseStep 9199655 = 13799483) B13799483
theorem B3064027 : Blo 1815609 3064027 := bstep (se 1 (by rfl) ⟨2298020, by rfl⟩ : syracuseStep 3064027 = 4596041) B4596041
theorem B3449051 : Blo 1815609 3449051 := bstep (se 1 (by rfl) ⟨2586788, by rfl⟩ : syracuseStep 3449051 = 5173577) B5173577
theorem B2908471 : Blo 1815609 2908471 := bstep (se 1 (by rfl) ⟨2181353, by rfl⟩ : syracuseStep 2908471 = 4362707) B4362707
theorem B2949503 : Blo 1815609 2949503 := bstep (se 1 (by rfl) ⟨2212127, by rfl⟩ : syracuseStep 2949503 = 4424255) B4424255
theorem B9191879 : Blo 1815609 9191879 := bstep (se 1 (by rfl) ⟨6893909, by rfl⟩ : syracuseStep 9191879 = 13787819) B13787819
theorem B3064297 : Blo 1815609 3064297 := bstep (se 2 (by rfl) ⟨1149111, by rfl⟩ : syracuseStep 3064297 = 2298223) B2298223
theorem B4088555 : Blo 1815609 4088555 := bstep (se 1 (by rfl) ⟨3066416, by rfl⟩ : syracuseStep 4088555 = 6132833) B6132833
theorem B8725259 : Blo 1815609 8725259 := bstep (se 1 (by rfl) ⟨6543944, by rfl⟩ : syracuseStep 8725259 = 13087889) B13087889
theorem B4596527 : Blo 1815609 4596527 := bstep (se 1 (by rfl) ⟨3447395, by rfl⟩ : syracuseStep 4596527 = 6894791) B6894791
theorem B6382547 : Blo 1815609 6382547 := bstep (se 1 (by rfl) ⟨4786910, by rfl⟩ : syracuseStep 6382547 = 9573821) B9573821
theorem B9200627 : Blo 1815609 9200627 := bstep (se 1 (by rfl) ⟨6900470, by rfl⟩ : syracuseStep 9200627 = 13800941) B13800941
theorem B2909291 : Blo 1815609 2909291 := bstep (se 1 (by rfl) ⟨2181968, by rfl⟩ : syracuseStep 2909291 = 4363937) B4363937
theorem B13796567 : Blo 1815609 13796567 := bstep (se 1 (by rfl) ⟨10347425, by rfl⟩ : syracuseStep 13796567 = 20694851) B20694851
theorem B52381079 : Blo 1815609 52381079 := bstep (se 1 (by rfl) ⟨39285809, by rfl⟩ : syracuseStep 52381079 = 78571619) B78571619
theorem B3225445829 : Blo 1815609 3225445829 := bstep (se 4 (by rfl) ⟨302385546, by rfl⟩ : syracuseStep 3225445829 = 604771093) B604771093
theorem B5817815 : Blo 1815609 5817815 := bstep (se 1 (by rfl) ⟨4363361, by rfl⟩ : syracuseStep 5817815 = 8726723) B8726723
theorem B4089455 : Blo 1815609 4089455 := bstep (se 1 (by rfl) ⟨3067091, by rfl⟩ : syracuseStep 4089455 = 6134183) B6134183
theorem B3065465 : Blo 1815609 3065465 := bstep (se 2 (by rfl) ⟨1149549, by rfl⟩ : syracuseStep 3065465 = 2299099) B2299099
theorem B23275147 : Blo 1815609 23275147 := bstep (se 1 (by rfl) ⟨17456360, by rfl⟩ : syracuseStep 23275147 = 34912721) B34912721
theorem B26199713 : Blo 1815609 26199713 := bstep (se 2 (by rfl) ⟨9824892, by rfl⟩ : syracuseStep 26199713 = 19649785) B19649785
theorem B111814357 : Blo 1815609 111814357 := bstep (se 7 (by rfl) ⟨1310324, by rfl⟩ : syracuseStep 111814357 = 2620649) B2620649
theorem B9823963 : Blo 1815609 9823963 := bstep (se 1 (by rfl) ⟨7367972, by rfl⟩ : syracuseStep 9823963 = 14735945) B14735945
theorem B4089563 : Blo 1815609 4089563 := bstep (se 1 (by rfl) ⟨3067172, by rfl⟩ : syracuseStep 4089563 = 6134345) B6134345
theorem B23275511 : Blo 1815609 23275511 := bstep (se 1 (by rfl) ⟨17456633, by rfl⟩ : syracuseStep 23275511 = 34913267) B34913267
theorem B3065951 : Blo 1815609 3065951 := bstep (se 1 (by rfl) ⟨2299463, by rfl⟩ : syracuseStep 3065951 = 4598927) B4598927
theorem B5171435 : Blo 1815609 5171435 := bstep (se 1 (by rfl) ⟨3878576, by rfl⟩ : syracuseStep 5171435 = 7757153) B7757153
theorem B5171617 : Blo 1815609 5171617 := bstep (se 2 (by rfl) ⟨1939356, by rfl⟩ : syracuseStep 5171617 = 3878713) B3878713
theorem B23284169 : Blo 1815609 23284169 := bstep (se 2 (by rfl) ⟨8731563, by rfl⟩ : syracuseStep 23284169 = 17463127) B17463127
theorem B6547969 : Blo 1815609 6547969 := bstep (se 2 (by rfl) ⟨2455488, by rfl⟩ : syracuseStep 6547969 = 4910977) B4910977
theorem B4598279 : Blo 1815609 4598279 := bstep (se 1 (by rfl) ⟨3448709, by rfl⟩ : syracuseStep 4598279 = 6897419) B6897419
theorem B3680873 : Blo 1815609 3680873 := bstep (se 2 (by rfl) ⟨1380327, by rfl⟩ : syracuseStep 3680873 = 2760655) B2760655
theorem B7563959 : Blo 1815609 7563959 := bstep (se 1 (by rfl) ⟨5672969, by rfl⟩ : syracuseStep 7563959 = 11345939) B11345939
theorem B23276483 : Blo 1815609 23276483 := bstep (se 1 (by rfl) ⟨17457362, by rfl⟩ : syracuseStep 23276483 = 34914725) B34914725
theorem B5172187 : Blo 1815609 5172187 := bstep (se 1 (by rfl) ⟨3879140, by rfl⟩ : syracuseStep 5172187 = 7758281) B7758281
theorem B9194471 : Blo 1815609 9194471 := bstep (se 1 (by rfl) ⟨6895853, by rfl⟩ : syracuseStep 9194471 = 13791707) B13791707
theorem B860826703 : Blo 1815609 860826703 := bstep (se 1 (by rfl) ⟨645620027, by rfl⟩ : syracuseStep 860826703 = 1291240055) B1291240055
theorem B53816399 : Blo 1815609 53816399 := bstep (se 1 (by rfl) ⟨40362299, by rfl⟩ : syracuseStep 53816399 = 80724599) B80724599
theorem B2043103 : Blo 1815609 2043103 := bstep (se 1 (by rfl) ⟨1532327, by rfl⟩ : syracuseStep 2043103 = 3064655) B3064655
theorem B4599119 : Blo 1815609 4599119 := bstep (se 1 (by rfl) ⟨3449339, by rfl⟩ : syracuseStep 4599119 = 6898679) B6898679
theorem B10341755 : Blo 1815609 10341755 := bstep (se 1 (by rfl) ⟨7756316, by rfl⟩ : syracuseStep 10341755 = 15512633) B15512633
theorem B17690021 : Blo 1815609 17690021 := bstep (se 4 (by rfl) ⟨1658439, by rfl⟩ : syracuseStep 17690021 = 3316879) B3316879
theorem B11800147 : Blo 1815609 11800147 := bstep (se 1 (by rfl) ⟨8850110, by rfl⟩ : syracuseStep 11800147 = 17700221) B17700221
theorem B2723435 : Blo 1815609 2723435 := bstep (se 1 (by rfl) ⟨2042576, by rfl⟩ : syracuseStep 2723435 = 4085153) B4085153
theorem B5172893 : Blo 1815609 5172893 := bstep (se 3 (by rfl) ⟨969917, by rfl⟩ : syracuseStep 5172893 = 1939835) B1939835
theorem B6131375 : Blo 1815609 6131375 := bstep (se 1 (by rfl) ⟨4598531, by rfl⟩ : syracuseStep 6131375 = 9197063) B9197063
theorem B2723561 : Blo 1815609 2723561 := bstep (se 2 (by rfl) ⟨1021335, by rfl⟩ : syracuseStep 2723561 = 2042671) B2042671
theorem B2723705 : Blo 1815609 2723705 := bstep (se 2 (by rfl) ⟨1021389, by rfl⟩ : syracuseStep 2723705 = 2042779) B2042779
theorem B19648403 : Blo 1815609 19648403 := bstep (se 1 (by rfl) ⟨14736302, by rfl⟩ : syracuseStep 19648403 = 29472605) B29472605
theorem B2723807 : Blo 1815609 2723807 := bstep (se 1 (by rfl) ⟨2042855, by rfl⟩ : syracuseStep 2723807 = 4085711) B4085711
theorem B6131699 : Blo 1815609 6131699 := bstep (se 1 (by rfl) ⟨4598774, by rfl⟩ : syracuseStep 6131699 = 9197549) B9197549
theorem B2724059 : Blo 1815609 2724059 := bstep (se 1 (by rfl) ⟨2043044, by rfl⟩ : syracuseStep 2724059 = 4086089) B4086089
theorem B2724071 : Blo 1815609 2724071 := bstep (se 1 (by rfl) ⟨2043053, by rfl⟩ : syracuseStep 2724071 = 4086107) B4086107
theorem B6549769 : Blo 1815609 6549769 := bstep (se 2 (by rfl) ⟨2456163, by rfl⟩ : syracuseStep 6549769 = 4912327) B4912327
theorem B6132023 : Blo 1815609 6132023 := bstep (se 1 (by rfl) ⟨4599017, by rfl⟩ : syracuseStep 6132023 = 9198035) B9198035
theorem B6549815 : Blo 1815609 6549815 := bstep (se 1 (by rfl) ⟨4912361, by rfl⟩ : syracuseStep 6549815 = 9824723) B9824723
theorem B2724233 : Blo 1815609 2724233 := bstep (se 2 (by rfl) ⟨1021587, by rfl⟩ : syracuseStep 2724233 = 2043175) B2043175
theorem B6992339 : Blo 1815609 6992339 := bstep (se 1 (by rfl) ⟨5244254, by rfl⟩ : syracuseStep 6992339 = 10488509) B10488509
theorem B6214103 : Blo 1815609 6214103 := bstep (se 1 (by rfl) ⟨4660577, by rfl⟩ : syracuseStep 6214103 = 9321155) B9321155
theorem B2724329 : Blo 1815609 2724329 := bstep (se 2 (by rfl) ⟨1021623, by rfl⟩ : syracuseStep 2724329 = 2043247) B2043247
theorem B6132239 : Blo 1815609 6132239 := bstep (se 1 (by rfl) ⟨4599179, by rfl⟩ : syracuseStep 6132239 = 9198359) B9198359
theorem B3273299 : Blo 1815609 3273299 := bstep (se 1 (by rfl) ⟨2454974, by rfl⟩ : syracuseStep 3273299 = 4909949) B4909949
theorem B4600415 : Blo 1815609 4600415 := bstep (se 1 (by rfl) ⟨3450311, by rfl⟩ : syracuseStep 4600415 = 6900623) B6900623
theorem B2724455 : Blo 1815609 2724455 := bstep (se 1 (by rfl) ⟨2043341, by rfl⟩ : syracuseStep 2724455 = 4086683) B4086683
theorem B13087403 : Blo 1815609 13087403 := bstep (se 1 (by rfl) ⟨9815552, by rfl⟩ : syracuseStep 13087403 = 19631105) B19631105
theorem B52359857 : Blo 1815609 52359857 := bstep (se 2 (by rfl) ⟨19634946, by rfl⟩ : syracuseStep 52359857 = 39269893) B39269893
theorem B2724587 : Blo 1815609 2724587 := bstep (se 1 (by rfl) ⟨2043440, by rfl⟩ : syracuseStep 2724587 = 4086881) B4086881
theorem B2585353 : Blo 1815609 2585353 := bstep (se 2 (by rfl) ⟨969507, by rfl⟩ : syracuseStep 2585353 = 1939015) B1939015
theorem B2724617 : Blo 1815609 2724617 := bstep (se 2 (by rfl) ⟨1021731, by rfl⟩ : syracuseStep 2724617 = 2043463) B2043463
theorem B2724719 : Blo 1815609 2724719 := bstep (se 1 (by rfl) ⟨2043539, by rfl⟩ : syracuseStep 2724719 = 4087079) B4087079
theorem B1815615 : Blo 1815609 1815615 := bstep (se 1 (by rfl) ⟨1361711, by rfl⟩ : syracuseStep 1815615 = 2723423) B2723423
theorem B3273833 : Blo 1815609 3273833 := bstep (se 2 (by rfl) ⟨1227687, by rfl⟩ : syracuseStep 3273833 = 2455375) B2455375
theorem B2724971 : Blo 1815609 2724971 := bstep (se 1 (by rfl) ⟨2043728, by rfl⟩ : syracuseStep 2724971 = 4087457) B4087457
theorem B49730735 : Blo 1815609 49730735 := bstep (se 1 (by rfl) ⟨37298051, by rfl⟩ : syracuseStep 49730735 = 74596103) B74596103
theorem B1815759 : Blo 1815609 1815759 := bstep (se 1 (by rfl) ⟨1361819, by rfl⟩ : syracuseStep 1815759 = 2723639) B2723639
theorem B4363475 : Blo 1815609 4363475 := bstep (se 1 (by rfl) ⟨3272606, by rfl⟩ : syracuseStep 4363475 = 6545213) B6545213
theorem B6550739 : Blo 1815609 6550739 := bstep (se 1 (by rfl) ⟨4913054, by rfl⟩ : syracuseStep 6550739 = 9826109) B9826109
theorem B2725211 : Blo 1815609 2725211 := bstep (se 1 (by rfl) ⟨2043908, by rfl⟩ : syracuseStep 2725211 = 4087817) B4087817
theorem B5821787 : Blo 1815609 5821787 := bstep (se 1 (by rfl) ⟨4366340, by rfl⟩ : syracuseStep 5821787 = 8732681) B8732681
theorem B1815963 : Blo 1815609 1815963 := bstep (se 1 (by rfl) ⟨1361972, by rfl⟩ : syracuseStep 1815963 = 2723945) B2723945
theorem B6895003 : Blo 1815609 6895003 := bstep (se 1 (by rfl) ⟨5171252, by rfl⟩ : syracuseStep 6895003 = 10342505) B10342505
theorem B6133319 : Blo 1815609 6133319 := bstep (se 1 (by rfl) ⟨4599989, by rfl⟩ : syracuseStep 6133319 = 9199979) B9199979
theorem B1816175 : Blo 1815609 1816175 := bstep (se 1 (by rfl) ⟨1362131, by rfl⟩ : syracuseStep 1816175 = 2724263) B2724263
theorem B2725487 : Blo 1815609 2725487 := bstep (se 1 (by rfl) ⟨2044115, by rfl⟩ : syracuseStep 2725487 = 4088231) B4088231
theorem B1816231 : Blo 1815609 1816231 := bstep (se 1 (by rfl) ⟨1362173, by rfl⟩ : syracuseStep 1816231 = 2724347) B2724347
theorem B3880619 : Blo 1815609 3880619 := bstep (se 1 (by rfl) ⟨2910464, by rfl⟩ : syracuseStep 3880619 = 5820929) B5820929
theorem B2725559 : Blo 1815609 2725559 := bstep (se 1 (by rfl) ⟨2044169, by rfl⟩ : syracuseStep 2725559 = 4088339) B4088339
theorem B2725595 : Blo 1815609 2725595 := bstep (se 1 (by rfl) ⟨2044196, by rfl⟩ : syracuseStep 2725595 = 4088393) B4088393
theorem B1816315 : Blo 1815609 1816315 := bstep (se 1 (by rfl) ⟨1362236, by rfl⟩ : syracuseStep 1816315 = 2724473) B2724473
theorem B5175035 : Blo 1815609 5175035 := bstep (se 1 (by rfl) ⟨3881276, by rfl⟩ : syracuseStep 5175035 = 7762553) B7762553
theorem B25196305 : Blo 1815609 25196305 := bstep (se 2 (by rfl) ⟨9448614, by rfl⟩ : syracuseStep 25196305 = 18897229) B18897229
theorem B1816351 : Blo 1815609 1816351 := bstep (se 1 (by rfl) ⟨1362263, by rfl⟩ : syracuseStep 1816351 = 2724527) B2724527
theorem B4085567 : Blo 1815609 4085567 := bstep (se 1 (by rfl) ⟨3064175, by rfl⟩ : syracuseStep 4085567 = 6128351) B6128351
theorem B1816383 : Blo 1815609 1816383 := bstep (se 1 (by rfl) ⟨1362287, by rfl⟩ : syracuseStep 1816383 = 2724575) B2724575
theorem B5175103 : Blo 1815609 5175103 := bstep (se 1 (by rfl) ⟨3881327, by rfl⟩ : syracuseStep 5175103 = 7762655) B7762655
theorem B2725769 : Blo 1815609 2725769 := bstep (se 2 (by rfl) ⟨1022163, by rfl⟩ : syracuseStep 2725769 = 2044327) B2044327
theorem B1816559 : Blo 1815609 1816559 := bstep (se 1 (by rfl) ⟨1362419, by rfl⟩ : syracuseStep 1816559 = 2724839) B2724839
theorem B2725871 : Blo 1815609 2725871 := bstep (se 1 (by rfl) ⟨2044403, by rfl⟩ : syracuseStep 2725871 = 4088807) B4088807
theorem B4085855 : Blo 1815609 4085855 := bstep (se 1 (by rfl) ⟨3064391, by rfl⟩ : syracuseStep 4085855 = 6128783) B6128783
theorem B1816731 : Blo 1815609 1816731 := bstep (se 1 (by rfl) ⟨1362548, by rfl⟩ : syracuseStep 1816731 = 2725097) B2725097
theorem B3274913 : Blo 1815609 3274913 := bstep (se 2 (by rfl) ⟨1228092, by rfl⟩ : syracuseStep 3274913 = 2456185) B2456185
theorem B1816767 : Blo 1815609 1816767 := bstep (se 1 (by rfl) ⟨1362575, by rfl⟩ : syracuseStep 1816767 = 2725151) B2725151
theorem B2726123 : Blo 1815609 2726123 := bstep (se 1 (by rfl) ⟨2044592, by rfl⟩ : syracuseStep 2726123 = 4089185) B4089185
theorem B22092041 : Blo 1815609 22092041 := bstep (se 2 (by rfl) ⟨8284515, by rfl⟩ : syracuseStep 22092041 = 16569031) B16569031
theorem B2726183 : Blo 1815609 2726183 := bstep (se 1 (by rfl) ⟨2044637, by rfl⟩ : syracuseStep 2726183 = 4089275) B4089275
theorem B1816879 : Blo 1815609 1816879 := bstep (se 1 (by rfl) ⟨1362659, by rfl⟩ : syracuseStep 1816879 = 2725319) B2725319
theorem B2726267 : Blo 1815609 2726267 := bstep (se 1 (by rfl) ⟨2044700, by rfl⟩ : syracuseStep 2726267 = 4089401) B4089401
theorem B6134291 : Blo 1815609 6134291 := bstep (se 1 (by rfl) ⟨4600718, by rfl⟩ : syracuseStep 6134291 = 9201437) B9201437
theorem B1817115 : Blo 1815609 1817115 := bstep (se 1 (by rfl) ⟨1362836, by rfl⟩ : syracuseStep 1817115 = 2725673) B2725673
theorem B1817119 : Blo 1815609 1817119 := bstep (se 1 (by rfl) ⟨1362839, by rfl⟩ : syracuseStep 1817119 = 2725679) B2725679
theorem B13097693 : Blo 1815609 13097693 := bstep (se 3 (by rfl) ⟨2455817, by rfl⟩ : syracuseStep 13097693 = 4911635) B4911635
theorem B4086611 : Blo 1815609 4086611 := bstep (se 1 (by rfl) ⟨3064958, by rfl⟩ : syracuseStep 4086611 = 6129917) B6129917
theorem B1817435 : Blo 1815609 1817435 := bstep (se 1 (by rfl) ⟨1363076, by rfl⟩ : syracuseStep 1817435 = 2726153) B2726153
theorem B1817503 : Blo 1815609 1817503 := bstep (se 1 (by rfl) ⟨1363127, by rfl⟩ : syracuseStep 1817503 = 2726255) B2726255
theorem B13802399 : Blo 1815609 13802399 := bstep (se 1 (by rfl) ⟨10351799, by rfl⟩ : syracuseStep 13802399 = 20703599) B20703599
theorem B1940527 : Blo 1815609 1940527 := bstep (se 1 (by rfl) ⟨1455395, by rfl⟩ : syracuseStep 1940527 = 2910791) B2910791
theorem B11639933 : Blo 1815609 11639933 := bstep (se 3 (by rfl) ⟨2182487, by rfl⟩ : syracuseStep 11639933 = 4364975) B4364975
theorem B9198845 : Blo 1815609 9198845 := bstep (se 3 (by rfl) ⟨1724783, by rfl⟩ : syracuseStep 9198845 = 3449567) B3449567
theorem B7863581 : Blo 1815609 7863581 := bstep (se 3 (by rfl) ⟨1474421, by rfl⟩ : syracuseStep 7863581 = 2948843) B2948843
theorem B4087151 : Blo 1815609 4087151 := bstep (se 1 (by rfl) ⟨3065363, by rfl⟩ : syracuseStep 4087151 = 6130727) B6130727
theorem B49741249 : Blo 1815609 49741249 := bstep (se 2 (by rfl) ⟨18652968, by rfl⟩ : syracuseStep 49741249 = 37305937) B37305937
theorem B8289773 : Blo 1815609 8289773 := bstep (se 3 (by rfl) ⟨1554332, by rfl⟩ : syracuseStep 8289773 = 3108665) B3108665
theorem B4087439 : Blo 1815609 4087439 := bstep (se 1 (by rfl) ⟨3065579, by rfl⟩ : syracuseStep 4087439 = 6131159) B6131159
theorem B4087529 : Blo 1815609 4087529 := bstep (se 2 (by rfl) ⟨1532823, by rfl⟩ : syracuseStep 4087529 = 3065647) B3065647
theorem B3448747 : Blo 1815609 3448747 := bstep (se 1 (by rfl) ⟨2586560, by rfl⟩ : syracuseStep 3448747 = 5173121) B5173121
theorem B4088015 : Blo 1815609 4088015 := bstep (se 1 (by rfl) ⟨3066011, by rfl⟩ : syracuseStep 4088015 = 6132023) B6132023
theorem B4366543 : Blo 1815609 4366543 := bstep (se 1 (by rfl) ⟨3274907, by rfl⟩ : syracuseStep 4366543 = 6549815) B6549815
theorem B7758109 : Blo 1815609 7758109 := bstep (se 3 (by rfl) ⟨1454645, by rfl⟩ : syracuseStep 7758109 = 2909291) B2909291
theorem B6127919 : Blo 1815609 6127919 := bstep (se 1 (by rfl) ⟨4595939, by rfl⟩ : syracuseStep 6127919 = 9191879) B9191879
theorem B4088159 : Blo 1815609 4088159 := bstep (se 1 (by rfl) ⟨3066119, by rfl⟩ : syracuseStep 4088159 = 6132239) B6132239
theorem B8733025 : Blo 1815609 8733025 := bstep (se 2 (by rfl) ⟨3274884, by rfl⟩ : syracuseStep 8733025 = 6549769) B6549769
theorem B8733101 : Blo 1815609 8733101 := bstep (se 3 (by rfl) ⟨1637456, by rfl⟩ : syracuseStep 8733101 = 3274913) B3274913
theorem B8724935 : Blo 1815609 8724935 := bstep (se 1 (by rfl) ⟨6543701, by rfl⟩ : syracuseStep 8724935 = 13087403) B13087403
theorem B34906571 : Blo 1815609 34906571 := bstep (se 1 (by rfl) ⟨26179928, by rfl⟩ : syracuseStep 34906571 = 52359857) B52359857
theorem B3064351 : Blo 1815609 3064351 := bstep (se 1 (by rfl) ⟨2298263, by rfl⟩ : syracuseStep 3064351 = 4596527) B4596527
theorem B33153823 : Blo 1815609 33153823 := bstep (se 1 (by rfl) ⟨24865367, by rfl⟩ : syracuseStep 33153823 = 49730735) B49730735
theorem B4367159 : Blo 1815609 4367159 := bstep (se 1 (by rfl) ⟨3275369, by rfl⟩ : syracuseStep 4367159 = 6550739) B6550739
theorem B4088879 : Blo 1815609 4088879 := bstep (se 1 (by rfl) ⟨3066659, by rfl⟩ : syracuseStep 4088879 = 6133319) B6133319
theorem B17466475 : Blo 1815609 17466475 := bstep (se 1 (by rfl) ⟨13099856, by rfl⟩ : syracuseStep 17466475 = 26199713) B26199713
theorem B3450023 : Blo 1815609 3450023 := bstep (se 1 (by rfl) ⟨2587517, by rfl⟩ : syracuseStep 3450023 = 5175035) B5175035
theorem B18646237 : Blo 1815609 18646237 := bstep (se 3 (by rfl) ⟨3496169, by rfl⟩ : syracuseStep 18646237 = 6992339) B6992339
theorem B15517007 : Blo 1815609 15517007 := bstep (se 1 (by rfl) ⟨11637755, by rfl⟩ : syracuseStep 15517007 = 23275511) B23275511
theorem B3065519 : Blo 1815609 3065519 := bstep (se 1 (by rfl) ⟨2299139, by rfl⟩ : syracuseStep 3065519 = 4598279) B4598279
theorem B4089527 : Blo 1815609 4089527 := bstep (se 1 (by rfl) ⟨3067145, by rfl⟩ : syracuseStep 4089527 = 6134291) B6134291
theorem B9193337 : Blo 1815609 9193337 := bstep (se 2 (by rfl) ⟨3447501, by rfl⟩ : syracuseStep 9193337 = 6895003) B6895003
theorem B9201599 : Blo 1815609 9201599 := bstep (se 1 (by rfl) ⟨6901199, by rfl⟩ : syracuseStep 9201599 = 13802399) B13802399
theorem B15517655 : Blo 1815609 15517655 := bstep (se 1 (by rfl) ⟨11638241, by rfl⟩ : syracuseStep 15517655 = 23276483) B23276483
theorem B6129647 : Blo 1815609 6129647 := bstep (se 1 (by rfl) ⟨4597235, by rfl⟩ : syracuseStep 6129647 = 9194471) B9194471
theorem B23267357 : Blo 1815609 23267357 := bstep (se 3 (by rfl) ⟨4362629, by rfl⟩ : syracuseStep 23267357 = 8725259) B8725259
theorem B7759955 : Blo 1815609 7759955 := bstep (se 1 (by rfl) ⟨5819966, by rfl⟩ : syracuseStep 7759955 = 11639933) B11639933
theorem B31033529 : Blo 1815609 31033529 := bstep (se 2 (by rfl) ⟨11637573, by rfl⟩ : syracuseStep 31033529 = 23275147) B23275147
theorem B3066079 : Blo 1815609 3066079 := bstep (se 1 (by rfl) ⟨2299559, by rfl⟩ : syracuseStep 3066079 = 4599119) B4599119
theorem B6900137 : Blo 1815609 6900137 := bstep (se 2 (by rfl) ⟨2587551, by rfl⟩ : syracuseStep 6900137 = 5175103) B5175103
theorem B4598329 : Blo 1815609 4598329 := bstep (se 2 (by rfl) ⟨1724373, by rfl⟩ : syracuseStep 4598329 = 3448747) B3448747
theorem B10349477 : Blo 1815609 10349477 := bstep (se 4 (by rfl) ⟨970263, by rfl⟩ : syracuseStep 10349477 = 1940527) B1940527
theorem B2182199 : Blo 1815609 2182199 := bstep (se 1 (by rfl) ⟨1636649, by rfl⟩ : syracuseStep 2182199 = 3273299) B3273299
theorem B3066943 : Blo 1815609 3066943 := bstep (se 1 (by rfl) ⟨2300207, by rfl⟩ : syracuseStep 3066943 = 4600415) B4600415
theorem B3877961 : Blo 1815609 3877961 := bstep (se 2 (by rfl) ⟨1454235, by rfl⟩ : syracuseStep 3877961 = 2908471) B2908471
theorem B4255031 : Blo 1815609 4255031 := bstep (se 1 (by rfl) ⟨3191273, by rfl⟩ : syracuseStep 4255031 = 6382547) B6382547
theorem B58912109 : Blo 1815609 58912109 := bstep (se 3 (by rfl) ⟨11046020, by rfl⟩ : syracuseStep 58912109 = 22092041) B22092041
theorem B2182555 : Blo 1815609 2182555 := bstep (se 1 (by rfl) ⟨1636916, by rfl⟩ : syracuseStep 2182555 = 3273833) B3273833
theorem B2150297219 : Blo 1815609 2150297219 := bstep (se 1 (by rfl) ⟨1612722914, by rfl⟩ : syracuseStep 2150297219 = 3225445829) B3225445829
theorem B3878543 : Blo 1815609 3878543 := bstep (se 1 (by rfl) ⟨2908907, by rfl⟩ : syracuseStep 3878543 = 5817815) B5817815
theorem B2043643 : Blo 1815609 2043643 := bstep (se 1 (by rfl) ⟨1532732, by rfl⟩ : syracuseStep 2043643 = 3065465) B3065465
theorem B2723711 : Blo 1815609 2723711 := bstep (se 1 (by rfl) ⟨2042783, by rfl⟩ : syracuseStep 2723711 = 4085567) B4085567
theorem B31461365 : Blo 1815609 31461365 := bstep (se 5 (by rfl) ⟨1474751, by rfl⟩ : syracuseStep 31461365 = 2949503) B2949503
theorem B2723903 : Blo 1815609 2723903 := bstep (se 1 (by rfl) ⟨2042927, by rfl⟩ : syracuseStep 2723903 = 4085855) B4085855
theorem B2043967 : Blo 1815609 2043967 := bstep (se 1 (by rfl) ⟨1532975, by rfl⟩ : syracuseStep 2043967 = 3065951) B3065951
theorem B1147768937 : Blo 1815609 1147768937 := bstep (se 2 (by rfl) ⟨430413351, by rfl⟩ : syracuseStep 1147768937 = 860826703) B860826703
theorem B2724137 : Blo 1815609 2724137 := bstep (se 2 (by rfl) ⟨1021551, by rfl⟩ : syracuseStep 2724137 = 2043103) B2043103
theorem B2453915 : Blo 1815609 2453915 := bstep (se 1 (by rfl) ⟨1840436, by rfl⟩ : syracuseStep 2453915 = 3680873) B3680873
theorem B5042639 : Blo 1815609 5042639 := bstep (se 1 (by rfl) ⟨3781979, by rfl⟩ : syracuseStep 5042639 = 7563959) B7563959
theorem B2724407 : Blo 1815609 2724407 := bstep (se 1 (by rfl) ⟨2043305, by rfl⟩ : syracuseStep 2724407 = 4086611) B4086611
theorem B35877599 : Blo 1815609 35877599 := bstep (se 1 (by rfl) ⟨26908199, by rfl⟩ : syracuseStep 35877599 = 53816399) B53816399
theorem B15733529 : Blo 1815609 15733529 := bstep (se 2 (by rfl) ⟨5900073, by rfl⟩ : syracuseStep 15733529 = 11800147) B11800147
theorem B6132563 : Blo 1815609 6132563 := bstep (se 1 (by rfl) ⟨4599422, by rfl⟩ : syracuseStep 6132563 = 9198845) B9198845
theorem B46543733 : Blo 1815609 46543733 := bstep (se 5 (by rfl) ⟨2181737, by rfl⟩ : syracuseStep 46543733 = 4363475) B4363475
theorem B2724767 : Blo 1815609 2724767 := bstep (se 1 (by rfl) ⟨2043575, by rfl⟩ : syracuseStep 2724767 = 4087151) B4087151
theorem B6894503 : Blo 1815609 6894503 := bstep (se 1 (by rfl) ⟨5170877, by rfl⟩ : syracuseStep 6894503 = 10341755) B10341755
theorem B11793347 : Blo 1815609 11793347 := bstep (se 1 (by rfl) ⟨8845010, by rfl⟩ : syracuseStep 11793347 = 17690021) B17690021
theorem B5526515 : Blo 1815609 5526515 := bstep (se 1 (by rfl) ⟨4144886, by rfl⟩ : syracuseStep 5526515 = 8289773) B8289773
theorem B1815623 : Blo 1815609 1815623 := bstep (se 1 (by rfl) ⟨1361717, by rfl⟩ : syracuseStep 1815623 = 2723435) B2723435
theorem B2724959 : Blo 1815609 2724959 := bstep (se 1 (by rfl) ⟨2043719, by rfl⟩ : syracuseStep 2724959 = 4087439) B4087439
theorem B1815707 : Blo 1815609 1815707 := bstep (se 1 (by rfl) ⟨1361780, by rfl⟩ : syracuseStep 1815707 = 2723561) B2723561
theorem B2725019 : Blo 1815609 2725019 := bstep (se 1 (by rfl) ⟨2043764, by rfl⟩ : syracuseStep 2725019 = 4087529) B4087529
theorem B1815803 : Blo 1815609 1815803 := bstep (se 1 (by rfl) ⟨1361852, by rfl⟩ : syracuseStep 1815803 = 2723705) B2723705
theorem B1815871 : Blo 1815609 1815871 := bstep (se 1 (by rfl) ⟨1361903, by rfl⟩ : syracuseStep 1815871 = 2723807) B2723807
theorem B6133103 : Blo 1815609 6133103 := bstep (se 1 (by rfl) ⟨4599827, by rfl⟩ : syracuseStep 6133103 = 9199655) B9199655
theorem B1816039 : Blo 1815609 1816039 := bstep (se 1 (by rfl) ⟨1362029, by rfl⟩ : syracuseStep 1816039 = 2724059) B2724059
theorem B2299367 : Blo 1815609 2299367 := bstep (se 1 (by rfl) ⟨1724525, by rfl⟩ : syracuseStep 2299367 = 3449051) B3449051
theorem B1816047 : Blo 1815609 1816047 := bstep (se 1 (by rfl) ⟨1362035, by rfl⟩ : syracuseStep 1816047 = 2724071) B2724071
theorem B1816155 : Blo 1815609 1816155 := bstep (se 1 (by rfl) ⟨1362116, by rfl⟩ : syracuseStep 1816155 = 2724233) B2724233
theorem B4085369 : Blo 1815609 4085369 := bstep (se 2 (by rfl) ⟨1532013, by rfl⟩ : syracuseStep 4085369 = 3064027) B3064027
theorem B4142735 : Blo 1815609 4142735 := bstep (se 1 (by rfl) ⟨3107051, by rfl⟩ : syracuseStep 4142735 = 6214103) B6214103
theorem B1816219 : Blo 1815609 1816219 := bstep (se 1 (by rfl) ⟨1362164, by rfl⟩ : syracuseStep 1816219 = 2724329) B2724329
theorem B1816303 : Blo 1815609 1816303 := bstep (se 1 (by rfl) ⟨1362227, by rfl⟩ : syracuseStep 1816303 = 2724455) B2724455
theorem B1816391 : Blo 1815609 1816391 := bstep (se 1 (by rfl) ⟨1362293, by rfl⟩ : syracuseStep 1816391 = 2724587) B2724587
theorem B2725703 : Blo 1815609 2725703 := bstep (se 1 (by rfl) ⟨2044277, by rfl⟩ : syracuseStep 2725703 = 4088555) B4088555
theorem B1816411 : Blo 1815609 1816411 := bstep (se 1 (by rfl) ⟨1362308, by rfl⟩ : syracuseStep 1816411 = 2724617) B2724617
theorem B6895489 : Blo 1815609 6895489 := bstep (se 2 (by rfl) ⟨2585808, by rfl⟩ : syracuseStep 6895489 = 5171617) B5171617
theorem B1816479 : Blo 1815609 1816479 := bstep (se 1 (by rfl) ⟨1362359, by rfl⟩ : syracuseStep 1816479 = 2724719) B2724719
theorem B4085729 : Blo 1815609 4085729 := bstep (se 2 (by rfl) ⟨1532148, by rfl⟩ : syracuseStep 4085729 = 3064297) B3064297
theorem B6133751 : Blo 1815609 6133751 := bstep (se 1 (by rfl) ⟨4600313, by rfl⟩ : syracuseStep 6133751 = 9200627) B9200627
theorem B8730625 : Blo 1815609 8730625 := bstep (se 2 (by rfl) ⟨3273984, by rfl⟩ : syracuseStep 8730625 = 6547969) B6547969
theorem B1816647 : Blo 1815609 1816647 := bstep (se 1 (by rfl) ⟨1362485, by rfl⟩ : syracuseStep 1816647 = 2724971) B2724971
theorem B20969549 : Blo 1815609 20969549 := bstep (se 3 (by rfl) ⟨3931790, by rfl⟩ : syracuseStep 20969549 = 7863581) B7863581
theorem B9197711 : Blo 1815609 9197711 := bstep (se 1 (by rfl) ⟨6898283, by rfl⟩ : syracuseStep 9197711 = 13796567) B13796567
theorem B1816807 : Blo 1815609 1816807 := bstep (se 1 (by rfl) ⟨1362605, by rfl⟩ : syracuseStep 1816807 = 2725211) B2725211
theorem B3881191 : Blo 1815609 3881191 := bstep (se 1 (by rfl) ⟨2910893, by rfl⟩ : syracuseStep 3881191 = 5821787) B5821787
theorem B34920719 : Blo 1815609 34920719 := bstep (se 1 (by rfl) ⟨26190539, by rfl⟩ : syracuseStep 34920719 = 52381079) B52381079
theorem B3447137 : Blo 1815609 3447137 := bstep (se 2 (by rfl) ⟨1292676, by rfl⟩ : syracuseStep 3447137 = 2585353) B2585353
theorem B1816991 : Blo 1815609 1816991 := bstep (se 1 (by rfl) ⟨1362743, by rfl⟩ : syracuseStep 1816991 = 2725487) B2725487
theorem B2726303 : Blo 1815609 2726303 := bstep (se 1 (by rfl) ⟨2044727, by rfl⟩ : syracuseStep 2726303 = 4089455) B4089455
theorem B2587079 : Blo 1815609 2587079 := bstep (se 1 (by rfl) ⟨1940309, by rfl⟩ : syracuseStep 2587079 = 3880619) B3880619
theorem B1817039 : Blo 1815609 1817039 := bstep (se 1 (by rfl) ⟨1362779, by rfl⟩ : syracuseStep 1817039 = 2725559) B2725559
theorem B1817063 : Blo 1815609 1817063 := bstep (se 1 (by rfl) ⟨1362797, by rfl⟩ : syracuseStep 1817063 = 2725595) B2725595
theorem B2726375 : Blo 1815609 2726375 := bstep (se 1 (by rfl) ⟨2044781, by rfl⟩ : syracuseStep 2726375 = 4089563) B4089563
theorem B1817179 : Blo 1815609 1817179 := bstep (se 1 (by rfl) ⟨1362884, by rfl⟩ : syracuseStep 1817179 = 2725769) B2725769
theorem B6896249 : Blo 1815609 6896249 := bstep (se 2 (by rfl) ⟨2586093, by rfl⟩ : syracuseStep 6896249 = 5172187) B5172187
theorem B1817247 : Blo 1815609 1817247 := bstep (se 1 (by rfl) ⟨1362935, by rfl⟩ : syracuseStep 1817247 = 2725871) B2725871
theorem B3447623 : Blo 1815609 3447623 := bstep (se 1 (by rfl) ⟨2585717, by rfl⟩ : syracuseStep 3447623 = 5171435) B5171435
theorem B1817415 : Blo 1815609 1817415 := bstep (se 1 (by rfl) ⟨1363061, by rfl⟩ : syracuseStep 1817415 = 2726123) B2726123
theorem B1817455 : Blo 1815609 1817455 := bstep (se 1 (by rfl) ⟨1363091, by rfl⟩ : syracuseStep 1817455 = 2726183) B2726183
theorem B1817511 : Blo 1815609 1817511 := bstep (se 1 (by rfl) ⟨1363133, by rfl⟩ : syracuseStep 1817511 = 2726267) B2726267
theorem B15522779 : Blo 1815609 15522779 := bstep (se 1 (by rfl) ⟨11642084, by rfl⟩ : syracuseStep 15522779 = 23284169) B23284169
theorem B8731795 : Blo 1815609 8731795 := bstep (se 1 (by rfl) ⟨6548846, by rfl⟩ : syracuseStep 8731795 = 13097693) B13097693
theorem B66321665 : Blo 1815609 66321665 := bstep (se 2 (by rfl) ⟨24870624, by rfl⟩ : syracuseStep 66321665 = 49741249) B49741249
theorem B149085809 : Blo 1815609 149085809 := bstep (se 2 (by rfl) ⟨55907178, by rfl⟩ : syracuseStep 149085809 = 111814357) B111814357
theorem B13098617 : Blo 1815609 13098617 := bstep (se 2 (by rfl) ⟨4911981, by rfl⟩ : syracuseStep 13098617 = 9823963) B9823963
theorem B33595073 : Blo 1815609 33595073 := bstep (se 2 (by rfl) ⟨12598152, by rfl⟩ : syracuseStep 33595073 = 25196305) B25196305
theorem B3448595 : Blo 1815609 3448595 := bstep (se 1 (by rfl) ⟨2586446, by rfl⟩ : syracuseStep 3448595 = 5172893) B5172893
theorem B4087583 : Blo 1815609 4087583 := bstep (se 1 (by rfl) ⟨3065687, by rfl⟩ : syracuseStep 4087583 = 6131375) B6131375
theorem B13098935 : Blo 1815609 13098935 := bstep (se 1 (by rfl) ⟨9824201, by rfl⟩ : syracuseStep 13098935 = 19648403) B19648403
theorem B4087799 : Blo 1815609 4087799 := bstep (se 1 (by rfl) ⟨3065849, by rfl⟩ : syracuseStep 4087799 = 6131699) B6131699
theorem B11640833 : Blo 1815609 11640833 := bstep (se 2 (by rfl) ⟨4365312, by rfl⟩ : syracuseStep 11640833 = 8730625) B8730625
theorem B4088105 : Blo 1815609 4088105 := bstep (se 2 (by rfl) ⟨1533039, by rfl⟩ : syracuseStep 4088105 = 3066079) B3066079
theorem B5816623 : Blo 1815609 5816623 := bstep (se 1 (by rfl) ⟨4362467, by rfl⟩ : syracuseStep 5816623 = 8724935) B8724935
theorem B4088375 : Blo 1815609 4088375 := bstep (se 1 (by rfl) ⟨3066281, by rfl⟩ : syracuseStep 4088375 = 6132563) B6132563
theorem B4596335 : Blo 1815609 4596335 := bstep (se 1 (by rfl) ⟨3447251, by rfl⟩ : syracuseStep 4596335 = 6894503) B6894503
theorem B11346749 : Blo 1815609 11346749 := bstep (se 3 (by rfl) ⟨2127515, by rfl⟩ : syracuseStep 11346749 = 4255031) B4255031
theorem B4088735 : Blo 1815609 4088735 := bstep (se 1 (by rfl) ⟨3066551, by rfl⟩ : syracuseStep 4088735 = 6133103) B6133103
theorem B9192365 : Blo 1815609 9192365 := bstep (se 3 (by rfl) ⟨1723568, by rfl⟩ : syracuseStep 9192365 = 3447137) B3447137
theorem B44205097 : Blo 1815609 44205097 := bstep (se 2 (by rfl) ⟨16576911, by rfl⟩ : syracuseStep 44205097 = 33153823) B33153823
theorem B2761823 : Blo 1815609 2761823 := bstep (se 1 (by rfl) ⟨2071367, by rfl⟩ : syracuseStep 2761823 = 4142735) B4142735
theorem B6898877 : Blo 1815609 6898877 := bstep (se 3 (by rfl) ⟨1293539, by rfl⟩ : syracuseStep 6898877 = 2587079) B2587079
theorem B6128891 : Blo 1815609 6128891 := bstep (se 1 (by rfl) ⟨4596668, by rfl⟩ : syracuseStep 6128891 = 9193337) B9193337
theorem B4089167 : Blo 1815609 4089167 := bstep (se 1 (by rfl) ⟨3066875, by rfl⟩ : syracuseStep 4089167 = 6133751) B6133751
theorem B4089257 : Blo 1815609 4089257 := bstep (se 2 (by rfl) ⟨1533471, by rfl⟩ : syracuseStep 4089257 = 3066943) B3066943
theorem B11642393 : Blo 1815609 11642393 := bstep (se 2 (by rfl) ⟨4365897, by rfl⟩ : syracuseStep 11642393 = 8731795) B8731795
theorem B4597499 : Blo 1815609 4597499 := bstep (se 1 (by rfl) ⟨3448124, by rfl⟩ : syracuseStep 4597499 = 6896249) B6896249
theorem B6899651 : Blo 1815609 6899651 := bstep (se 1 (by rfl) ⟨5174738, by rfl⟩ : syracuseStep 6899651 = 10349477) B10349477
theorem B10348519 : Blo 1815609 10348519 := bstep (se 1 (by rfl) ⟨7761389, by rfl⟩ : syracuseStep 10348519 = 15522779) B15522779
theorem B44214443 : Blo 1815609 44214443 := bstep (se 1 (by rfl) ⟨33160832, by rfl⟩ : syracuseStep 44214443 = 66321665) B66321665
theorem B9193661 : Blo 1815609 9193661 := bstep (se 3 (by rfl) ⟨1723811, by rfl⟩ : syracuseStep 9193661 = 3447623) B3447623
theorem B39274739 : Blo 1815609 39274739 := bstep (se 1 (by rfl) ⟨29456054, by rfl⟩ : syracuseStep 39274739 = 58912109) B58912109
theorem B9193985 : Blo 1815609 9193985 := bstep (se 2 (by rfl) ⟨3447744, by rfl⟩ : syracuseStep 9193985 = 6895489) B6895489
theorem B20974243 : Blo 1815609 20974243 := bstep (se 1 (by rfl) ⟨15730682, by rfl⟩ : syracuseStep 20974243 = 31461365) B31461365
theorem B5819197 : Blo 1815609 5819197 := bstep (se 3 (by rfl) ⟨1091099, by rfl⟩ : syracuseStep 5819197 = 2182199) B2182199
theorem B10341229 : Blo 1815609 10341229 := bstep (se 3 (by rfl) ⟨1938980, by rfl⟩ : syracuseStep 10341229 = 3877961) B3877961
theorem B11644033 : Blo 1815609 11644033 := bstep (se 2 (by rfl) ⟨4366512, by rfl⟩ : syracuseStep 11644033 = 8733025) B8733025
theorem B10489019 : Blo 1815609 10489019 := bstep (se 1 (by rfl) ⟨7866764, by rfl⟩ : syracuseStep 10489019 = 15733529) B15733529
theorem B2911439 : Blo 1815609 2911439 := bstep (se 1 (by rfl) ⟨2183579, by rfl⟩ : syracuseStep 2911439 = 4367159) B4367159
theorem B6131105 : Blo 1815609 6131105 := bstep (se 2 (by rfl) ⟨2299164, by rfl⟩ : syracuseStep 6131105 = 4598329) B4598329
theorem B2723579 : Blo 1815609 2723579 := bstep (se 1 (by rfl) ⟨2042684, by rfl⟩ : syracuseStep 2723579 = 4085369) B4085369
theorem B2043679 : Blo 1815609 2043679 := bstep (se 1 (by rfl) ⟨1532759, by rfl⟩ : syracuseStep 2043679 = 3065519) B3065519
theorem B13447037 : Blo 1815609 13447037 := bstep (se 3 (by rfl) ⟨2521319, by rfl⟩ : syracuseStep 13447037 = 5042639) B5042639
theorem B6131645 : Blo 1815609 6131645 := bstep (se 3 (by rfl) ⟨1149683, by rfl⟩ : syracuseStep 6131645 = 2299367) B2299367
theorem B2723819 : Blo 1815609 2723819 := bstep (se 1 (by rfl) ⟨2042864, by rfl⟩ : syracuseStep 2723819 = 4085729) B4085729
theorem B15511571 : Blo 1815609 15511571 := bstep (se 1 (by rfl) ⟨11633678, by rfl⟩ : syracuseStep 15511571 = 23267357) B23267357
theorem B13979699 : Blo 1815609 13979699 := bstep (se 1 (by rfl) ⟨10484774, by rfl⟩ : syracuseStep 13979699 = 20969549) B20969549
theorem B5173303 : Blo 1815609 5173303 := bstep (se 1 (by rfl) ⟨3879977, by rfl⟩ : syracuseStep 5173303 = 7759955) B7759955
theorem B6131807 : Blo 1815609 6131807 := bstep (se 1 (by rfl) ⟨4598855, by rfl⟩ : syracuseStep 6131807 = 9197711) B9197711
theorem B20689019 : Blo 1815609 20689019 := bstep (se 1 (by rfl) ⟨15516764, by rfl⟩ : syracuseStep 20689019 = 31033529) B31033529
theorem B4600091 : Blo 1815609 4600091 := bstep (se 1 (by rfl) ⟨3450068, by rfl⟩ : syracuseStep 4600091 = 6900137) B6900137
theorem B5734125917 : Blo 1815609 5734125917 := bstep (se 3 (by rfl) ⟨1075148609, by rfl⟩ : syracuseStep 5734125917 = 2150297219) B2150297219
theorem B9196253 : Blo 1815609 9196253 := bstep (se 3 (by rfl) ⟨1724297, by rfl⟩ : syracuseStep 9196253 = 3448595) B3448595
theorem B2724857 : Blo 1815609 2724857 := bstep (se 2 (by rfl) ⟨1021821, by rfl⟩ : syracuseStep 2724857 = 2043643) B2043643
theorem B99390539 : Blo 1815609 99390539 := bstep (se 1 (by rfl) ⟨74542904, by rfl⟩ : syracuseStep 99390539 = 149085809) B149085809
theorem B2585695 : Blo 1815609 2585695 := bstep (se 1 (by rfl) ⟨1939271, by rfl⟩ : syracuseStep 2585695 = 3878543) B3878543
theorem B2725055 : Blo 1815609 2725055 := bstep (se 1 (by rfl) ⟨2043791, by rfl⟩ : syracuseStep 2725055 = 4087583) B4087583
theorem B1815807 : Blo 1815609 1815807 := bstep (se 1 (by rfl) ⟨1361855, by rfl⟩ : syracuseStep 1815807 = 2723711) B2723711
theorem B2725199 : Blo 1815609 2725199 := bstep (se 1 (by rfl) ⟨2043899, by rfl⟩ : syracuseStep 2725199 = 4087799) B4087799
theorem B1815935 : Blo 1815609 1815935 := bstep (se 1 (by rfl) ⟨1361951, by rfl⟩ : syracuseStep 1815935 = 2723903) B2723903
theorem B765179291 : Blo 1815609 765179291 := bstep (se 1 (by rfl) ⟨573884468, by rfl⟩ : syracuseStep 765179291 = 1147768937) B1147768937
theorem B2725289 : Blo 1815609 2725289 := bstep (se 2 (by rfl) ⟨1021983, by rfl⟩ : syracuseStep 2725289 = 2043967) B2043967
theorem B2725343 : Blo 1815609 2725343 := bstep (se 1 (by rfl) ⟨2044007, by rfl⟩ : syracuseStep 2725343 = 4088015) B4088015
theorem B1816091 : Blo 1815609 1816091 := bstep (se 1 (by rfl) ⟨1362068, by rfl⟩ : syracuseStep 1816091 = 2724137) B2724137
theorem B4085279 : Blo 1815609 4085279 := bstep (se 1 (by rfl) ⟨3063959, by rfl⟩ : syracuseStep 4085279 = 6127919) B6127919
theorem B2725439 : Blo 1815609 2725439 := bstep (se 1 (by rfl) ⟨2044079, by rfl⟩ : syracuseStep 2725439 = 4088159) B4088159
theorem B5822057 : Blo 1815609 5822057 := bstep (se 2 (by rfl) ⟨2183271, by rfl⟩ : syracuseStep 5822057 = 4366543) B4366543
theorem B23271047 : Blo 1815609 23271047 := bstep (se 1 (by rfl) ⟨17453285, by rfl⟩ : syracuseStep 23271047 = 34906571) B34906571
theorem B5174921 : Blo 1815609 5174921 := bstep (se 2 (by rfl) ⟨1940595, by rfl⟩ : syracuseStep 5174921 = 3881191) B3881191
theorem B1816271 : Blo 1815609 1816271 := bstep (se 1 (by rfl) ⟨1362203, by rfl⟩ : syracuseStep 1816271 = 2724407) B2724407
theorem B10344145 : Blo 1815609 10344145 := bstep (se 2 (by rfl) ⟨3879054, by rfl⟩ : syracuseStep 10344145 = 7758109) B7758109
theorem B23918399 : Blo 1815609 23918399 := bstep (se 1 (by rfl) ⟨17938799, by rfl⟩ : syracuseStep 23918399 = 35877599) B35877599
theorem B31029155 : Blo 1815609 31029155 := bstep (se 1 (by rfl) ⟨23271866, by rfl⟩ : syracuseStep 31029155 = 46543733) B46543733
theorem B1816511 : Blo 1815609 1816511 := bstep (se 1 (by rfl) ⟨1362383, by rfl⟩ : syracuseStep 1816511 = 2724767) B2724767
theorem B7862231 : Blo 1815609 7862231 := bstep (se 1 (by rfl) ⟨5896673, by rfl⟩ : syracuseStep 7862231 = 11793347) B11793347
theorem B2725919 : Blo 1815609 2725919 := bstep (se 1 (by rfl) ⟨2044439, by rfl⟩ : syracuseStep 2725919 = 4088879) B4088879
theorem B4085801 : Blo 1815609 4085801 := bstep (se 2 (by rfl) ⟨1532175, by rfl⟩ : syracuseStep 4085801 = 3064351) B3064351
theorem B1816639 : Blo 1815609 1816639 := bstep (se 1 (by rfl) ⟨1362479, by rfl⟩ : syracuseStep 1816639 = 2724959) B2724959
theorem B1816679 : Blo 1815609 1816679 := bstep (se 1 (by rfl) ⟨1362509, by rfl⟩ : syracuseStep 1816679 = 2725019) B2725019
theorem B2300015 : Blo 1815609 2300015 := bstep (se 1 (by rfl) ⟨1725011, by rfl⟩ : syracuseStep 2300015 = 3450023) B3450023
theorem B10344671 : Blo 1815609 10344671 := bstep (se 1 (by rfl) ⟨7758503, by rfl⟩ : syracuseStep 10344671 = 15517007) B15517007
theorem B6543773 : Blo 1815609 6543773 := bstep (se 3 (by rfl) ⟨1226957, by rfl⟩ : syracuseStep 6543773 = 2453915) B2453915
theorem B23288269 : Blo 1815609 23288269 := bstep (se 3 (by rfl) ⟨4366550, by rfl⟩ : syracuseStep 23288269 = 8733101) B8733101
theorem B2726351 : Blo 1815609 2726351 := bstep (se 1 (by rfl) ⟨2044763, by rfl⟩ : syracuseStep 2726351 = 4089527) B4089527
theorem B1817135 : Blo 1815609 1817135 := bstep (se 1 (by rfl) ⟨1362851, by rfl⟩ : syracuseStep 1817135 = 2725703) B2725703
theorem B6134399 : Blo 1815609 6134399 := bstep (se 1 (by rfl) ⟨4600799, by rfl⟩ : syracuseStep 6134399 = 9201599) B9201599
theorem B10345103 : Blo 1815609 10345103 := bstep (se 1 (by rfl) ⟨7758827, by rfl⟩ : syracuseStep 10345103 = 15517655) B15517655
theorem B4086431 : Blo 1815609 4086431 := bstep (se 1 (by rfl) ⟨3064823, by rfl⟩ : syracuseStep 4086431 = 6129647) B6129647
theorem B23288633 : Blo 1815609 23288633 := bstep (se 2 (by rfl) ⟨8733237, by rfl⟩ : syracuseStep 23288633 = 17466475) B17466475
theorem B23280479 : Blo 1815609 23280479 := bstep (se 1 (by rfl) ⟨17460359, by rfl⟩ : syracuseStep 23280479 = 34920719) B34920719
theorem B1817535 : Blo 1815609 1817535 := bstep (se 1 (by rfl) ⟨1363151, by rfl⟩ : syracuseStep 1817535 = 2726303) B2726303
theorem B24861649 : Blo 1815609 24861649 := bstep (se 2 (by rfl) ⟨9323118, by rfl⟩ : syracuseStep 24861649 = 18646237) B18646237
theorem B1817583 : Blo 1815609 1817583 := bstep (se 1 (by rfl) ⟨1363187, by rfl⟩ : syracuseStep 1817583 = 2726375) B2726375
theorem B11640293 : Blo 1815609 11640293 := bstep (se 4 (by rfl) ⟨1091277, by rfl⟩ : syracuseStep 11640293 = 2182555) B2182555
theorem B8732411 : Blo 1815609 8732411 := bstep (se 1 (by rfl) ⟨6549308, by rfl⟩ : syracuseStep 8732411 = 13098617) B13098617
theorem B22396715 : Blo 1815609 22396715 := bstep (se 1 (by rfl) ⟨16797536, by rfl⟩ : syracuseStep 22396715 = 33595073) B33595073
theorem B8732623 : Blo 1815609 8732623 := bstep (se 1 (by rfl) ⟨6549467, by rfl⟩ : syracuseStep 8732623 = 13098935) B13098935
theorem B14737373 : Blo 1815609 14737373 := bstep (se 3 (by rfl) ⟨2763257, by rfl⟩ : syracuseStep 14737373 = 5526515) B5526515
theorem B4087871 : Blo 1815609 4087871 := bstep (se 1 (by rfl) ⟨3065903, by rfl⟩ : syracuseStep 4087871 = 6131807) B6131807
theorem B6897737 : Blo 1815609 6897737 := bstep (se 2 (by rfl) ⟨2586651, by rfl⟩ : syracuseStep 6897737 = 5173303) B5173303
theorem B3064223 : Blo 1815609 3064223 := bstep (se 1 (by rfl) ⟨2298167, by rfl⟩ : syracuseStep 3064223 = 4596335) B4596335
theorem B6128243 : Blo 1815609 6128243 := bstep (se 1 (by rfl) ⟨4596182, by rfl⟩ : syracuseStep 6128243 = 9192365) B9192365
theorem B7758929 : Blo 1815609 7758929 := bstep (se 2 (by rfl) ⟨2909598, by rfl⟩ : syracuseStep 7758929 = 5819197) B5819197
theorem B3449947 : Blo 1815609 3449947 := bstep (se 1 (by rfl) ⟨2587460, by rfl⟩ : syracuseStep 3449947 = 5174921) B5174921
theorem B13788305 : Blo 1815609 13788305 := bstep (se 2 (by rfl) ⟨5170614, by rfl⟩ : syracuseStep 13788305 = 10341229) B10341229
theorem B3064999 : Blo 1815609 3064999 := bstep (se 1 (by rfl) ⟨2298749, by rfl⟩ : syracuseStep 3064999 = 4597499) B4597499
theorem B20686103 : Blo 1815609 20686103 := bstep (se 1 (by rfl) ⟨15514577, by rfl⟩ : syracuseStep 20686103 = 31029155) B31029155
theorem B29476295 : Blo 1815609 29476295 := bstep (se 1 (by rfl) ⟨22107221, by rfl⟩ : syracuseStep 29476295 = 44214443) B44214443
theorem B6129107 : Blo 1815609 6129107 := bstep (se 1 (by rfl) ⟨4596830, by rfl⟩ : syracuseStep 6129107 = 9193661) B9193661
theorem B26183159 : Blo 1815609 26183159 := bstep (se 1 (by rfl) ⟨19637369, by rfl⟩ : syracuseStep 26183159 = 39274739) B39274739
theorem B15525377 : Blo 1815609 15525377 := bstep (se 2 (by rfl) ⟨5822016, by rfl⟩ : syracuseStep 15525377 = 11644033) B11644033
theorem B6129323 : Blo 1815609 6129323 := bstep (se 1 (by rfl) ⟨4596992, by rfl⟩ : syracuseStep 6129323 = 9193985) B9193985
theorem B4089599 : Blo 1815609 4089599 := bstep (se 1 (by rfl) ⟨3067199, by rfl⟩ : syracuseStep 4089599 = 6134399) B6134399
theorem B15525755 : Blo 1815609 15525755 := bstep (se 1 (by rfl) ⟨11644316, by rfl⟩ : syracuseStep 15525755 = 23288633) B23288633
theorem B7760195 : Blo 1815609 7760195 := bstep (se 1 (by rfl) ⟨5820146, by rfl⟩ : syracuseStep 7760195 = 11640293) B11640293
theorem B35858765 : Blo 1815609 35858765 := bstep (se 3 (by rfl) ⟨6723518, by rfl⟩ : syracuseStep 35858765 = 13447037) B13447037
theorem B20965949 : Blo 1815609 20965949 := bstep (se 3 (by rfl) ⟨3931115, by rfl⟩ : syracuseStep 20965949 = 7862231) B7862231
theorem B11643497 : Blo 1815609 11643497 := bstep (se 2 (by rfl) ⟨4366311, by rfl⟩ : syracuseStep 11643497 = 8732623) B8732623
theorem B13798025 : Blo 1815609 13798025 := bstep (se 2 (by rfl) ⟨5174259, by rfl⟩ : syracuseStep 13798025 = 10348519) B10348519
theorem B9824915 : Blo 1815609 9824915 := bstep (se 1 (by rfl) ⟨7368686, by rfl⟩ : syracuseStep 9824915 = 14737373) B14737373
theorem B7760555 : Blo 1815609 7760555 := bstep (se 1 (by rfl) ⟨5820416, by rfl⟩ : syracuseStep 7760555 = 11640833) B11640833
theorem B10341047 : Blo 1815609 10341047 := bstep (se 1 (by rfl) ⟨7755785, by rfl⟩ : syracuseStep 10341047 = 15511571) B15511571
theorem B3066727 : Blo 1815609 3066727 := bstep (se 1 (by rfl) ⟨2300045, by rfl⟩ : syracuseStep 3066727 = 4600091) B4600091
theorem B3822750611 : Blo 1815609 3822750611 := bstep (se 1 (by rfl) ⟨2867062958, by rfl⟩ : syracuseStep 3822750611 = 5734125917) B5734125917
theorem B6130835 : Blo 1815609 6130835 := bstep (se 1 (by rfl) ⟨4598126, by rfl⟩ : syracuseStep 6130835 = 9196253) B9196253
theorem B27970717 : Blo 1815609 27970717 := bstep (se 3 (by rfl) ⟨5244509, by rfl⟩ : syracuseStep 27970717 = 10489019) B10489019
theorem B7564499 : Blo 1815609 7564499 := bstep (se 1 (by rfl) ⟨5673374, by rfl⟩ : syracuseStep 7564499 = 11346749) B11346749
theorem B31051025 : Blo 1815609 31051025 := bstep (se 2 (by rfl) ⟨11644134, by rfl⟩ : syracuseStep 31051025 = 23288269) B23288269
theorem B66260359 : Blo 1815609 66260359 := bstep (se 1 (by rfl) ⟨49695269, by rfl⟩ : syracuseStep 66260359 = 99390539) B99390539
theorem B4599251 : Blo 1815609 4599251 := bstep (se 1 (by rfl) ⟨3449438, by rfl⟩ : syracuseStep 4599251 = 6898877) B6898877
theorem B510119527 : Blo 1815609 510119527 := bstep (se 1 (by rfl) ⟨382589645, by rfl⟩ : syracuseStep 510119527 = 765179291) B765179291
theorem B7761595 : Blo 1815609 7761595 := bstep (se 1 (by rfl) ⟨5821196, by rfl⟩ : syracuseStep 7761595 = 11642393) B11642393
theorem B2723519 : Blo 1815609 2723519 := bstep (se 1 (by rfl) ⟨2042639, by rfl⟩ : syracuseStep 2723519 = 4085279) B4085279
theorem B15945599 : Blo 1815609 15945599 := bstep (se 1 (by rfl) ⟨11959199, by rfl⟩ : syracuseStep 15945599 = 23918399) B23918399
theorem B33148865 : Blo 1815609 33148865 := bstep (se 2 (by rfl) ⟨12430824, by rfl⟩ : syracuseStep 33148865 = 24861649) B24861649
theorem B4599767 : Blo 1815609 4599767 := bstep (se 1 (by rfl) ⟨3449825, by rfl⟩ : syracuseStep 4599767 = 6899651) B6899651
theorem B2723867 : Blo 1815609 2723867 := bstep (se 1 (by rfl) ⟨2042900, by rfl⟩ : syracuseStep 2723867 = 4085801) B4085801
theorem B4362515 : Blo 1815609 4362515 := bstep (se 1 (by rfl) ⟨3271886, by rfl⟩ : syracuseStep 4362515 = 6543773) B6543773
theorem B2724287 : Blo 1815609 2724287 := bstep (se 1 (by rfl) ⟨2043215, by rfl⟩ : syracuseStep 2724287 = 4086431) B4086431
theorem B15520319 : Blo 1815609 15520319 := bstep (se 1 (by rfl) ⟨11640239, by rfl⟩ : syracuseStep 15520319 = 23280479) B23280479
theorem B13792193 : Blo 1815609 13792193 := bstep (se 2 (by rfl) ⟨5172072, by rfl⟩ : syracuseStep 13792193 = 10344145) B10344145
theorem B2724905 : Blo 1815609 2724905 := bstep (se 2 (by rfl) ⟨1021839, by rfl⟩ : syracuseStep 2724905 = 2043679) B2043679
theorem B1815719 : Blo 1815609 1815719 := bstep (se 1 (by rfl) ⟨1361789, by rfl⟩ : syracuseStep 1815719 = 2723579) B2723579
theorem B5821607 : Blo 1815609 5821607 := bstep (se 1 (by rfl) ⟨4366205, by rfl⟩ : syracuseStep 5821607 = 8732411) B8732411
theorem B14931143 : Blo 1815609 14931143 := bstep (se 1 (by rfl) ⟨11198357, by rfl⟩ : syracuseStep 14931143 = 22396715) B22396715
theorem B1815879 : Blo 1815609 1815879 := bstep (se 1 (by rfl) ⟨1361909, by rfl⟩ : syracuseStep 1815879 = 2723819) B2723819
theorem B9319799 : Blo 1815609 9319799 := bstep (se 1 (by rfl) ⟨6989849, by rfl⟩ : syracuseStep 9319799 = 13979699) B13979699
theorem B13792679 : Blo 1815609 13792679 := bstep (se 1 (by rfl) ⟨10344509, by rfl⟩ : syracuseStep 13792679 = 20689019) B20689019
theorem B2725403 : Blo 1815609 2725403 := bstep (se 1 (by rfl) ⟨2044052, by rfl⟩ : syracuseStep 2725403 = 4088105) B4088105
theorem B6133373 : Blo 1815609 6133373 := bstep (se 3 (by rfl) ⟨1150007, by rfl⟩ : syracuseStep 6133373 = 2300015) B2300015
theorem B2725583 : Blo 1815609 2725583 := bstep (se 1 (by rfl) ⟨2044187, by rfl⟩ : syracuseStep 2725583 = 4088375) B4088375
theorem B7755497 : Blo 1815609 7755497 := bstep (se 2 (by rfl) ⟨2908311, by rfl⟩ : syracuseStep 7755497 = 5816623) B5816623
theorem B2725823 : Blo 1815609 2725823 := bstep (se 1 (by rfl) ⟨2044367, by rfl⟩ : syracuseStep 2725823 = 4088735) B4088735
theorem B1816571 : Blo 1815609 1816571 := bstep (se 1 (by rfl) ⟨1362428, by rfl⟩ : syracuseStep 1816571 = 2724857) B2724857
theorem B1841215 : Blo 1815609 1841215 := bstep (se 1 (by rfl) ⟨1380911, by rfl⟩ : syracuseStep 1841215 = 2761823) B2761823
theorem B1816703 : Blo 1815609 1816703 := bstep (se 1 (by rfl) ⟨1362527, by rfl⟩ : syracuseStep 1816703 = 2725055) B2725055
theorem B4085927 : Blo 1815609 4085927 := bstep (se 1 (by rfl) ⟨3064445, by rfl⟩ : syracuseStep 4085927 = 6128891) B6128891
theorem B27965657 : Blo 1815609 27965657 := bstep (se 2 (by rfl) ⟨10487121, by rfl⟩ : syracuseStep 27965657 = 20974243) B20974243
theorem B1816799 : Blo 1815609 1816799 := bstep (se 1 (by rfl) ⟨1362599, by rfl⟩ : syracuseStep 1816799 = 2725199) B2725199
theorem B2726111 : Blo 1815609 2726111 := bstep (se 1 (by rfl) ⟨2044583, by rfl⟩ : syracuseStep 2726111 = 4089167) B4089167
theorem B1816859 : Blo 1815609 1816859 := bstep (se 1 (by rfl) ⟨1362644, by rfl⟩ : syracuseStep 1816859 = 2725289) B2725289
theorem B2726171 : Blo 1815609 2726171 := bstep (se 1 (by rfl) ⟨2044628, by rfl⟩ : syracuseStep 2726171 = 4089257) B4089257
theorem B1816895 : Blo 1815609 1816895 := bstep (se 1 (by rfl) ⟨1362671, by rfl⟩ : syracuseStep 1816895 = 2725343) B2725343
theorem B1816959 : Blo 1815609 1816959 := bstep (se 1 (by rfl) ⟨1362719, by rfl⟩ : syracuseStep 1816959 = 2725439) B2725439
theorem B3881371 : Blo 1815609 3881371 := bstep (se 1 (by rfl) ⟨2911028, by rfl⟩ : syracuseStep 3881371 = 5822057) B5822057
theorem B15514031 : Blo 1815609 15514031 := bstep (se 1 (by rfl) ⟨11635523, by rfl⟩ : syracuseStep 15514031 = 23271047) B23271047
theorem B1817279 : Blo 1815609 1817279 := bstep (se 1 (by rfl) ⟨1362959, by rfl⟩ : syracuseStep 1817279 = 2725919) B2725919
theorem B58940129 : Blo 1815609 58940129 := bstep (se 2 (by rfl) ⟨22102548, by rfl⟩ : syracuseStep 58940129 = 44205097) B44205097
theorem B3447593 : Blo 1815609 3447593 := bstep (se 2 (by rfl) ⟨1292847, by rfl⟩ : syracuseStep 3447593 = 2585695) B2585695
theorem B6896447 : Blo 1815609 6896447 := bstep (se 1 (by rfl) ⟨5172335, by rfl⟩ : syracuseStep 6896447 = 10344671) B10344671
theorem B1817567 : Blo 1815609 1817567 := bstep (se 1 (by rfl) ⟨1363175, by rfl⟩ : syracuseStep 1817567 = 2726351) B2726351
theorem B6896735 : Blo 1815609 6896735 := bstep (se 1 (by rfl) ⟨5172551, by rfl⟩ : syracuseStep 6896735 = 10345103) B10345103
theorem B1940959 : Blo 1815609 1940959 := bstep (se 1 (by rfl) ⟨1455719, by rfl⟩ : syracuseStep 1940959 = 2911439) B2911439
theorem B4087403 : Blo 1815609 4087403 := bstep (se 1 (by rfl) ⟨3065552, by rfl⟩ : syracuseStep 4087403 = 6131105) B6131105
theorem B4087763 : Blo 1815609 4087763 := bstep (se 1 (by rfl) ⟨3065822, by rfl⟩ : syracuseStep 4087763 = 6131645) B6131645
theorem B2908343 : Blo 1815609 2908343 := bstep (se 1 (by rfl) ⟨2181257, by rfl⟩ : syracuseStep 2908343 = 4362515) B4362515
theorem B10346879 : Blo 1815609 10346879 := bstep (se 1 (by rfl) ⟨7760159, by rfl⟩ : syracuseStep 10346879 = 15520319) B15520319
theorem B9192203 : Blo 1815609 9192203 := bstep (se 1 (by rfl) ⟨6894152, by rfl⟩ : syracuseStep 9192203 = 13788305) B13788305
theorem B9954095 : Blo 1815609 9954095 := bstep (se 1 (by rfl) ⟨7465571, by rfl⟩ : syracuseStep 9954095 = 14931143) B14931143
theorem B4088915 : Blo 1815609 4088915 := bstep (se 1 (by rfl) ⟨3066686, by rfl⟩ : syracuseStep 4088915 = 6133373) B6133373
theorem B4088969 : Blo 1815609 4088969 := bstep (se 2 (by rfl) ⟨1533363, by rfl⟩ : syracuseStep 4088969 = 3066727) B3066727
theorem B5170331 : Blo 1815609 5170331 := bstep (se 1 (by rfl) ⟨3877748, by rfl⟩ : syracuseStep 5170331 = 7755497) B7755497
theorem B23905843 : Blo 1815609 23905843 := bstep (se 1 (by rfl) ⟨17929382, by rfl⟩ : syracuseStep 23905843 = 35858765) B35858765
theorem B13977299 : Blo 1815609 13977299 := bstep (se 1 (by rfl) ⟨10482974, by rfl⟩ : syracuseStep 13977299 = 20965949) B20965949
theorem B4597631 : Blo 1815609 4597631 := bstep (se 1 (by rfl) ⟨3448223, by rfl⟩ : syracuseStep 4597631 = 6896447) B6896447
theorem B2548500407 : Blo 1815609 2548500407 := bstep (se 1 (by rfl) ⟨1911375305, by rfl⟩ : syracuseStep 2548500407 = 3822750611) B3822750611
theorem B4597823 : Blo 1815609 4597823 := bstep (se 1 (by rfl) ⟨3448367, by rfl⟩ : syracuseStep 4597823 = 6896735) B6896735
theorem B680159369 : Blo 1815609 680159369 := bstep (se 2 (by rfl) ⟨255059763, by rfl⟩ : syracuseStep 680159369 = 510119527) B510119527
theorem B10348793 : Blo 1815609 10348793 := bstep (se 2 (by rfl) ⟨3880797, by rfl⟩ : syracuseStep 10348793 = 7761595) B7761595
theorem B3066167 : Blo 1815609 3066167 := bstep (se 1 (by rfl) ⟨2299625, by rfl⟩ : syracuseStep 3066167 = 4599251) B4599251
theorem B3066511 : Blo 1815609 3066511 := bstep (se 1 (by rfl) ⟨2299883, by rfl⟩ : syracuseStep 3066511 = 4599767) B4599767
theorem B4598491 : Blo 1815609 4598491 := bstep (se 1 (by rfl) ⟨3448868, by rfl⟩ : syracuseStep 4598491 = 6897737) B6897737
theorem B2042815 : Blo 1815609 2042815 := bstep (se 1 (by rfl) ⟨1532111, by rfl⟩ : syracuseStep 2042815 = 3064223) B3064223
theorem B9194795 : Blo 1815609 9194795 := bstep (se 1 (by rfl) ⟨6896096, by rfl⟩ : syracuseStep 9194795 = 13792193) B13792193
theorem B13790735 : Blo 1815609 13790735 := bstep (se 1 (by rfl) ⟨10343051, by rfl⟩ : syracuseStep 13790735 = 20686103) B20686103
theorem B6213199 : Blo 1815609 6213199 := bstep (se 1 (by rfl) ⟨4659899, by rfl⟩ : syracuseStep 6213199 = 9319799) B9319799
theorem B9195119 : Blo 1815609 9195119 := bstep (se 1 (by rfl) ⟨6896339, by rfl⟩ : syracuseStep 9195119 = 13792679) B13792679
theorem B10350251 : Blo 1815609 10350251 := bstep (se 1 (by rfl) ⟨7762688, by rfl⟩ : syracuseStep 10350251 = 15525377) B15525377
theorem B10350503 : Blo 1815609 10350503 := bstep (se 1 (by rfl) ⟨7762877, by rfl⟩ : syracuseStep 10350503 = 15525755) B15525755
theorem B2723951 : Blo 1815609 2723951 := bstep (se 1 (by rfl) ⟨2042963, by rfl⟩ : syracuseStep 2723951 = 4085927) B4085927
theorem B4599929 : Blo 1815609 4599929 := bstep (se 2 (by rfl) ⟨1724973, by rfl⟩ : syracuseStep 4599929 = 3449947) B3449947
theorem B37294289 : Blo 1815609 37294289 := bstep (se 2 (by rfl) ⟨13985358, by rfl⟩ : syracuseStep 37294289 = 27970717) B27970717
theorem B5173463 : Blo 1815609 5173463 := bstep (se 1 (by rfl) ⟨3880097, by rfl⟩ : syracuseStep 5173463 = 7760195) B7760195
theorem B10342687 : Blo 1815609 10342687 := bstep (se 1 (by rfl) ⟨7757015, by rfl⟩ : syracuseStep 10342687 = 15514031) B15514031
theorem B7762331 : Blo 1815609 7762331 := bstep (se 1 (by rfl) ⟨5821748, by rfl⟩ : syracuseStep 7762331 = 11643497) B11643497
theorem B6549943 : Blo 1815609 6549943 := bstep (se 1 (by rfl) ⟨4912457, by rfl⟩ : syracuseStep 6549943 = 9824915) B9824915
theorem B5173703 : Blo 1815609 5173703 := bstep (se 1 (by rfl) ⟨3880277, by rfl⟩ : syracuseStep 5173703 = 7760555) B7760555
theorem B6894031 : Blo 1815609 6894031 := bstep (se 1 (by rfl) ⟨5170523, by rfl⟩ : syracuseStep 6894031 = 10341047) B10341047
theorem B39293419 : Blo 1815609 39293419 := bstep (se 1 (by rfl) ⟨29470064, by rfl⟩ : syracuseStep 39293419 = 58940129) B58940129
theorem B88347145 : Blo 1815609 88347145 := bstep (se 2 (by rfl) ⟨33130179, by rfl⟩ : syracuseStep 88347145 = 66260359) B66260359
theorem B2298395 : Blo 1815609 2298395 := bstep (se 1 (by rfl) ⟨1723796, by rfl⟩ : syracuseStep 2298395 = 3447593) B3447593
theorem B5042999 : Blo 1815609 5042999 := bstep (se 1 (by rfl) ⟨3782249, by rfl⟩ : syracuseStep 5042999 = 7564499) B7564499
theorem B2724935 : Blo 1815609 2724935 := bstep (se 1 (by rfl) ⟨2043701, by rfl⟩ : syracuseStep 2724935 = 4087403) B4087403
theorem B1815679 : Blo 1815609 1815679 := bstep (se 1 (by rfl) ⟨1361759, by rfl⟩ : syracuseStep 1815679 = 2723519) B2723519
theorem B10630399 : Blo 1815609 10630399 := bstep (se 1 (by rfl) ⟨7972799, by rfl⟩ : syracuseStep 10630399 = 15945599) B15945599
theorem B22099243 : Blo 1815609 22099243 := bstep (se 1 (by rfl) ⟨16574432, by rfl⟩ : syracuseStep 22099243 = 33148865) B33148865
theorem B2725175 : Blo 1815609 2725175 := bstep (se 1 (by rfl) ⟨2043881, by rfl⟩ : syracuseStep 2725175 = 4087763) B4087763
theorem B1815911 : Blo 1815609 1815911 := bstep (se 1 (by rfl) ⟨1361933, by rfl⟩ : syracuseStep 1815911 = 2723867) B2723867
theorem B2725247 : Blo 1815609 2725247 := bstep (se 1 (by rfl) ⟨2043935, by rfl⟩ : syracuseStep 2725247 = 4087871) B4087871
theorem B2454953 : Blo 1815609 2454953 := bstep (se 2 (by rfl) ⟨920607, by rfl⟩ : syracuseStep 2454953 = 1841215) B1841215
theorem B20690477 : Blo 1815609 20690477 := bstep (se 3 (by rfl) ⟨3879464, by rfl⟩ : syracuseStep 20690477 = 7758929) B7758929
theorem B1816191 : Blo 1815609 1816191 := bstep (se 1 (by rfl) ⟨1362143, by rfl⟩ : syracuseStep 1816191 = 2724287) B2724287
theorem B4085495 : Blo 1815609 4085495 := bstep (se 1 (by rfl) ⟨3064121, by rfl⟩ : syracuseStep 4085495 = 6128243) B6128243
theorem B5175161 : Blo 1815609 5175161 := bstep (se 2 (by rfl) ⟨1940685, by rfl⟩ : syracuseStep 5175161 = 3881371) B3881371
theorem B1816603 : Blo 1815609 1816603 := bstep (se 1 (by rfl) ⟨1362452, by rfl⟩ : syracuseStep 1816603 = 2724905) B2724905
theorem B3881071 : Blo 1815609 3881071 := bstep (se 1 (by rfl) ⟨2910803, by rfl⟩ : syracuseStep 3881071 = 5821607) B5821607
theorem B19650863 : Blo 1815609 19650863 := bstep (se 1 (by rfl) ⟨14738147, by rfl⟩ : syracuseStep 19650863 = 29476295) B29476295
theorem B4086071 : Blo 1815609 4086071 := bstep (se 1 (by rfl) ⟨3064553, by rfl⟩ : syracuseStep 4086071 = 6129107) B6129107
theorem B17455439 : Blo 1815609 17455439 := bstep (se 1 (by rfl) ⟨13091579, by rfl⟩ : syracuseStep 17455439 = 26183159) B26183159
theorem B1816935 : Blo 1815609 1816935 := bstep (se 1 (by rfl) ⟨1362701, by rfl⟩ : syracuseStep 1816935 = 2725403) B2725403
theorem B4086215 : Blo 1815609 4086215 := bstep (se 1 (by rfl) ⟨3064661, by rfl⟩ : syracuseStep 4086215 = 6129323) B6129323
theorem B1817055 : Blo 1815609 1817055 := bstep (se 1 (by rfl) ⟨1362791, by rfl⟩ : syracuseStep 1817055 = 2725583) B2725583
theorem B2726399 : Blo 1815609 2726399 := bstep (se 1 (by rfl) ⟨2044799, by rfl⟩ : syracuseStep 2726399 = 4089599) B4089599
theorem B1817215 : Blo 1815609 1817215 := bstep (se 1 (by rfl) ⟨1362911, by rfl⟩ : syracuseStep 1817215 = 2725823) B2725823
theorem B18643771 : Blo 1815609 18643771 := bstep (se 1 (by rfl) ⟨13982828, by rfl⟩ : syracuseStep 18643771 = 27965657) B27965657
theorem B1817407 : Blo 1815609 1817407 := bstep (se 1 (by rfl) ⟨1363055, by rfl⟩ : syracuseStep 1817407 = 2726111) B2726111
theorem B1817447 : Blo 1815609 1817447 := bstep (se 1 (by rfl) ⟨1363085, by rfl⟩ : syracuseStep 1817447 = 2726171) B2726171
theorem B4086665 : Blo 1815609 4086665 := bstep (se 2 (by rfl) ⟨1532499, by rfl⟩ : syracuseStep 4086665 = 3064999) B3064999
theorem B9198683 : Blo 1815609 9198683 := bstep (se 1 (by rfl) ⟨6899012, by rfl⟩ : syracuseStep 9198683 = 13798025) B13798025
theorem B2587945 : Blo 1815609 2587945 := bstep (se 2 (by rfl) ⟨970479, by rfl⟩ : syracuseStep 2587945 = 1940959) B1940959
theorem B4087223 : Blo 1815609 4087223 := bstep (se 1 (by rfl) ⟨3065417, by rfl⟩ : syracuseStep 4087223 = 6130835) B6130835
theorem B20700683 : Blo 1815609 20700683 := bstep (se 1 (by rfl) ⟨15525512, by rfl⟩ : syracuseStep 20700683 = 31051025) B31051025
theorem B24862859 : Blo 1815609 24862859 := bstep (se 1 (by rfl) ⟨18647144, by rfl⟩ : syracuseStep 24862859 = 37294289) B37294289
theorem B3448975 : Blo 1815609 3448975 := bstep (se 1 (by rfl) ⟨2586731, by rfl⟩ : syracuseStep 3448975 = 5173463) B5173463
theorem B6897919 : Blo 1815609 6897919 := bstep (se 1 (by rfl) ⟨5173439, by rfl⟩ : syracuseStep 6897919 = 10346879) B10346879
theorem B3449135 : Blo 1815609 3449135 := bstep (se 1 (by rfl) ⟨2586851, by rfl⟩ : syracuseStep 3449135 = 5173703) B5173703
theorem B106177013 : Blo 1815609 106177013 := bstep (se 5 (by rfl) ⟨4977047, by rfl⟩ : syracuseStep 106177013 = 9954095) B9954095
theorem B6128135 : Blo 1815609 6128135 := bstep (se 1 (by rfl) ⟨4596101, by rfl⟩ : syracuseStep 6128135 = 9192203) B9192203
theorem B8733257 : Blo 1815609 8733257 := bstep (se 2 (by rfl) ⟨3274971, by rfl⟩ : syracuseStep 8733257 = 6549943) B6549943
theorem B9192041 : Blo 1815609 9192041 := bstep (se 2 (by rfl) ⟨3447015, by rfl⟩ : syracuseStep 9192041 = 6894031) B6894031
theorem B4088681 : Blo 1815609 4088681 := bstep (se 2 (by rfl) ⟨1533255, by rfl⟩ : syracuseStep 4088681 = 3066511) B3066511
theorem B6546541 : Blo 1815609 6546541 := bstep (se 3 (by rfl) ⟨1227476, by rfl⟩ : syracuseStep 6546541 = 2454953) B2454953
theorem B3450107 : Blo 1815609 3450107 := bstep (se 1 (by rfl) ⟨2587580, by rfl⟩ : syracuseStep 3450107 = 5175161) B5175161
theorem B3065087 : Blo 1815609 3065087 := bstep (se 1 (by rfl) ⟨2298815, by rfl⟩ : syracuseStep 3065087 = 4597631) B4597631
theorem B3065215 : Blo 1815609 3065215 := bstep (se 1 (by rfl) ⟨2298911, by rfl⟩ : syracuseStep 3065215 = 4597823) B4597823
theorem B6129053 : Blo 1815609 6129053 := bstep (se 3 (by rfl) ⟨1149197, by rfl⟩ : syracuseStep 6129053 = 2298395) B2298395
theorem B6899195 : Blo 1815609 6899195 := bstep (se 1 (by rfl) ⟨5174396, by rfl⟩ : syracuseStep 6899195 = 10348793) B10348793
theorem B13100575 : Blo 1815609 13100575 := bstep (se 1 (by rfl) ⟨9825431, by rfl⟩ : syracuseStep 13100575 = 19650863) B19650863
theorem B14173865 : Blo 1815609 14173865 := bstep (se 2 (by rfl) ⟨5315199, by rfl⟩ : syracuseStep 14173865 = 10630399) B10630399
theorem B3450593 : Blo 1815609 3450593 := bstep (se 2 (by rfl) ⟨1293972, by rfl⟩ : syracuseStep 3450593 = 2587945) B2587945
theorem B8284265 : Blo 1815609 8284265 := bstep (se 2 (by rfl) ⟨3106599, by rfl⟩ : syracuseStep 8284265 = 6213199) B6213199
theorem B6129863 : Blo 1815609 6129863 := bstep (se 1 (by rfl) ⟨4597397, by rfl⟩ : syracuseStep 6129863 = 9194795) B9194795
theorem B9193823 : Blo 1815609 9193823 := bstep (se 1 (by rfl) ⟨6895367, by rfl⟩ : syracuseStep 9193823 = 13790735) B13790735
theorem B6130079 : Blo 1815609 6130079 := bstep (se 1 (by rfl) ⟨4597559, by rfl⟩ : syracuseStep 6130079 = 9195119) B9195119
theorem B6900167 : Blo 1815609 6900167 := bstep (se 1 (by rfl) ⟨5175125, by rfl⟩ : syracuseStep 6900167 = 10350251) B10350251
theorem B6900335 : Blo 1815609 6900335 := bstep (se 1 (by rfl) ⟨5175251, by rfl⟩ : syracuseStep 6900335 = 10350503) B10350503
theorem B3066619 : Blo 1815609 3066619 := bstep (se 1 (by rfl) ⟨2299964, by rfl⟩ : syracuseStep 3066619 = 4599929) B4599929
theorem B13790249 : Blo 1815609 13790249 := bstep (se 2 (by rfl) ⟨5171343, by rfl⟩ : syracuseStep 13790249 = 10342687) B10342687
theorem B3361999 : Blo 1815609 3361999 := bstep (se 1 (by rfl) ⟨2521499, by rfl⟩ : syracuseStep 3361999 = 5042999) B5042999
theorem B52391225 : Blo 1815609 52391225 := bstep (se 2 (by rfl) ⟨19646709, by rfl⟩ : syracuseStep 52391225 = 39293419) B39293419
theorem B117796193 : Blo 1815609 117796193 := bstep (se 2 (by rfl) ⟨44173572, by rfl⟩ : syracuseStep 117796193 = 88347145) B88347145
theorem B6131321 : Blo 1815609 6131321 := bstep (se 2 (by rfl) ⟨2299245, by rfl⟩ : syracuseStep 6131321 = 4598491) B4598491
theorem B24858361 : Blo 1815609 24858361 := bstep (se 2 (by rfl) ⟨9321885, by rfl⟩ : syracuseStep 24858361 = 18643771) B18643771
theorem B9318199 : Blo 1815609 9318199 := bstep (se 1 (by rfl) ⟨6988649, by rfl⟩ : syracuseStep 9318199 = 13977299) B13977299
theorem B2723663 : Blo 1815609 2723663 := bstep (se 1 (by rfl) ⟨2042747, by rfl⟩ : syracuseStep 2723663 = 4085495) B4085495
theorem B2723753 : Blo 1815609 2723753 := bstep (se 2 (by rfl) ⟨1021407, by rfl⟩ : syracuseStep 2723753 = 2042815) B2042815
theorem B1699000271 : Blo 1815609 1699000271 := bstep (se 1 (by rfl) ⟨1274250203, by rfl⟩ : syracuseStep 1699000271 = 2548500407) B2548500407
theorem B453439579 : Blo 1815609 453439579 := bstep (se 1 (by rfl) ⟨340079684, by rfl⟩ : syracuseStep 453439579 = 680159369) B680159369
theorem B2724047 : Blo 1815609 2724047 := bstep (se 1 (by rfl) ⟨2043035, by rfl⟩ : syracuseStep 2724047 = 4086071) B4086071
theorem B2044111 : Blo 1815609 2044111 := bstep (se 1 (by rfl) ⟨1533083, by rfl⟩ : syracuseStep 2044111 = 3066167) B3066167
theorem B11636959 : Blo 1815609 11636959 := bstep (se 1 (by rfl) ⟨8727719, by rfl⟩ : syracuseStep 11636959 = 17455439) B17455439
theorem B2724143 : Blo 1815609 2724143 := bstep (se 1 (by rfl) ⟨2043107, by rfl⟩ : syracuseStep 2724143 = 4086215) B4086215
theorem B2724443 : Blo 1815609 2724443 := bstep (se 1 (by rfl) ⟨2043332, by rfl⟩ : syracuseStep 2724443 = 4086665) B4086665
theorem B6132455 : Blo 1815609 6132455 := bstep (se 1 (by rfl) ⟨4599341, by rfl⟩ : syracuseStep 6132455 = 9198683) B9198683
theorem B2724815 : Blo 1815609 2724815 := bstep (se 1 (by rfl) ⟨2043611, by rfl⟩ : syracuseStep 2724815 = 4087223) B4087223
theorem B13800455 : Blo 1815609 13800455 := bstep (se 1 (by rfl) ⟨10350341, by rfl⟩ : syracuseStep 13800455 = 20700683) B20700683
theorem B1815967 : Blo 1815609 1815967 := bstep (se 1 (by rfl) ⟨1361975, by rfl⟩ : syracuseStep 1815967 = 2723951) B2723951
theorem B5174761 : Blo 1815609 5174761 := bstep (se 2 (by rfl) ⟨1940535, by rfl⟩ : syracuseStep 5174761 = 3881071) B3881071
theorem B127497829 : Blo 1815609 127497829 := bstep (se 4 (by rfl) ⟨11952921, by rfl⟩ : syracuseStep 127497829 = 23905843) B23905843
theorem B5174887 : Blo 1815609 5174887 := bstep (se 1 (by rfl) ⟨3881165, by rfl⟩ : syracuseStep 5174887 = 7762331) B7762331
theorem B7755581 : Blo 1815609 7755581 := bstep (se 3 (by rfl) ⟨1454171, by rfl⟩ : syracuseStep 7755581 = 2908343) B2908343
theorem B1816623 : Blo 1815609 1816623 := bstep (se 1 (by rfl) ⟨1362467, by rfl⟩ : syracuseStep 1816623 = 2724935) B2724935
theorem B2725943 : Blo 1815609 2725943 := bstep (se 1 (by rfl) ⟨2044457, by rfl⟩ : syracuseStep 2725943 = 4088915) B4088915
theorem B2725979 : Blo 1815609 2725979 := bstep (se 1 (by rfl) ⟨2044484, by rfl⟩ : syracuseStep 2725979 = 4088969) B4088969
theorem B3446887 : Blo 1815609 3446887 := bstep (se 1 (by rfl) ⟨2585165, by rfl⟩ : syracuseStep 3446887 = 5170331) B5170331
theorem B1816783 : Blo 1815609 1816783 := bstep (se 1 (by rfl) ⟨1362587, by rfl⟩ : syracuseStep 1816783 = 2725175) B2725175
theorem B1816831 : Blo 1815609 1816831 := bstep (se 1 (by rfl) ⟨1362623, by rfl⟩ : syracuseStep 1816831 = 2725247) B2725247
theorem B13793651 : Blo 1815609 13793651 := bstep (se 1 (by rfl) ⟨10345238, by rfl⟩ : syracuseStep 13793651 = 20690477) B20690477
theorem B1817599 : Blo 1815609 1817599 := bstep (se 1 (by rfl) ⟨1363199, by rfl⟩ : syracuseStep 1817599 = 2726399) B2726399
theorem B29465657 : Blo 1815609 29465657 := bstep (se 2 (by rfl) ⟨11049621, by rfl⟩ : syracuseStep 29465657 = 22099243) B22099243
theorem B604586105 : Blo 1815609 604586105 := bstep (se 2 (by rfl) ⟨226719789, by rfl⟩ : syracuseStep 604586105 = 453439579) B453439579
theorem B4595849 : Blo 1815609 4595849 := bstep (se 2 (by rfl) ⟨1723443, by rfl⟩ : syracuseStep 4595849 = 3446887) B3446887
theorem B15515945 : Blo 1815609 15515945 := bstep (se 2 (by rfl) ⟨5818479, by rfl⟩ : syracuseStep 15515945 = 11636959) B11636959
theorem B6128027 : Blo 1815609 6128027 := bstep (se 1 (by rfl) ⟨4596020, by rfl⟩ : syracuseStep 6128027 = 9192041) B9192041
theorem B4088303 : Blo 1815609 4088303 := bstep (se 1 (by rfl) ⟨3066227, by rfl⟩ : syracuseStep 4088303 = 6132455) B6132455
theorem B9200303 : Blo 1815609 9200303 := bstep (se 1 (by rfl) ⟨6900227, by rfl⟩ : syracuseStep 9200303 = 13800455) B13800455
theorem B4088825 : Blo 1815609 4088825 := bstep (se 2 (by rfl) ⟨1533309, by rfl⟩ : syracuseStep 4088825 = 3066619) B3066619
theorem B5170387 : Blo 1815609 5170387 := bstep (se 1 (by rfl) ⟨3877790, by rfl⟩ : syracuseStep 5170387 = 7755581) B7755581
theorem B5522843 : Blo 1815609 5522843 := bstep (se 1 (by rfl) ⟨4142132, by rfl⟩ : syracuseStep 5522843 = 8284265) B8284265
theorem B6129215 : Blo 1815609 6129215 := bstep (se 1 (by rfl) ⟨4596911, by rfl⟩ : syracuseStep 6129215 = 9193823) B9193823
theorem B4482665 : Blo 1815609 4482665 := bstep (se 2 (by rfl) ⟨1680999, by rfl⟩ : syracuseStep 4482665 = 3361999) B3361999
theorem B6899681 : Blo 1815609 6899681 := bstep (se 2 (by rfl) ⟨2587380, by rfl⟩ : syracuseStep 6899681 = 5174761) B5174761
theorem B9193499 : Blo 1815609 9193499 := bstep (se 1 (by rfl) ⟨6895124, by rfl⟩ : syracuseStep 9193499 = 13790249) B13790249
theorem B17467433 : Blo 1815609 17467433 := bstep (se 2 (by rfl) ⟨6550287, by rfl⟩ : syracuseStep 17467433 = 13100575) B13100575
theorem B6899849 : Blo 1815609 6899849 := bstep (se 2 (by rfl) ⟨2587443, by rfl⟩ : syracuseStep 6899849 = 5174887) B5174887
theorem B78530795 : Blo 1815609 78530795 := bstep (se 1 (by rfl) ⟨58898096, by rfl⟩ : syracuseStep 78530795 = 117796193) B117796193
theorem B16575239 : Blo 1815609 16575239 := bstep (se 1 (by rfl) ⟨12431429, by rfl⟩ : syracuseStep 16575239 = 24862859) B24862859
theorem B4598633 : Blo 1815609 4598633 := bstep (se 2 (by rfl) ⟨1724487, by rfl⟩ : syracuseStep 4598633 = 3448975) B3448975
theorem B2043391 : Blo 1815609 2043391 := bstep (se 1 (by rfl) ⟨1532543, by rfl⟩ : syracuseStep 2043391 = 3065087) B3065087
theorem B4599463 : Blo 1815609 4599463 := bstep (se 1 (by rfl) ⟨3449597, by rfl⟩ : syracuseStep 4599463 = 6899195) B6899195
theorem B9449243 : Blo 1815609 9449243 := bstep (se 1 (by rfl) ⟨7086932, by rfl⟩ : syracuseStep 9449243 = 14173865) B14173865
theorem B8728721 : Blo 1815609 8728721 := bstep (se 2 (by rfl) ⟨3273270, by rfl⟩ : syracuseStep 8728721 = 6546541) B6546541
theorem B9195767 : Blo 1815609 9195767 := bstep (se 1 (by rfl) ⟨6896825, by rfl⟩ : syracuseStep 9195767 = 13793651) B13793651
theorem B4600111 : Blo 1815609 4600111 := bstep (se 1 (by rfl) ⟨3450083, by rfl⟩ : syracuseStep 4600111 = 6900167) B6900167
theorem B4600223 : Blo 1815609 4600223 := bstep (se 1 (by rfl) ⟨3450167, by rfl⟩ : syracuseStep 4600223 = 6900335) B6900335
theorem B169997105 : Blo 1815609 169997105 := bstep (se 2 (by rfl) ⟨63748914, by rfl⟩ : syracuseStep 169997105 = 127497829) B127497829
theorem B34927483 : Blo 1815609 34927483 := bstep (se 1 (by rfl) ⟨26195612, by rfl⟩ : syracuseStep 34927483 = 52391225) B52391225
theorem B12424265 : Blo 1815609 12424265 := bstep (se 2 (by rfl) ⟨4659099, by rfl⟩ : syracuseStep 12424265 = 9318199) B9318199
theorem B1815775 : Blo 1815609 1815775 := bstep (se 1 (by rfl) ⟨1361831, by rfl⟩ : syracuseStep 1815775 = 2723663) B2723663
theorem B1815835 : Blo 1815609 1815835 := bstep (se 1 (by rfl) ⟨1361876, by rfl⟩ : syracuseStep 1815835 = 2723753) B2723753
theorem B1816031 : Blo 1815609 1816031 := bstep (se 1 (by rfl) ⟨1362023, by rfl⟩ : syracuseStep 1816031 = 2724047) B2724047
theorem B1816095 : Blo 1815609 1816095 := bstep (se 1 (by rfl) ⟨1362071, by rfl⟩ : syracuseStep 1816095 = 2724143) B2724143
theorem B2299423 : Blo 1815609 2299423 := bstep (se 1 (by rfl) ⟨1724567, by rfl⟩ : syracuseStep 2299423 = 3449135) B3449135
theorem B2725481 : Blo 1815609 2725481 := bstep (se 2 (by rfl) ⟨1022055, by rfl⟩ : syracuseStep 2725481 = 2044111) B2044111
theorem B70784675 : Blo 1815609 70784675 := bstep (se 1 (by rfl) ⟨53088506, by rfl⟩ : syracuseStep 70784675 = 106177013) B106177013
theorem B9197225 : Blo 1815609 9197225 := bstep (se 2 (by rfl) ⟨3448959, by rfl⟩ : syracuseStep 9197225 = 6897919) B6897919
theorem B4085423 : Blo 1815609 4085423 := bstep (se 1 (by rfl) ⟨3064067, by rfl⟩ : syracuseStep 4085423 = 6128135) B6128135
theorem B5822171 : Blo 1815609 5822171 := bstep (se 1 (by rfl) ⟨4366628, by rfl⟩ : syracuseStep 5822171 = 8733257) B8733257
theorem B1816295 : Blo 1815609 1816295 := bstep (se 1 (by rfl) ⟨1362221, by rfl⟩ : syracuseStep 1816295 = 2724443) B2724443
theorem B2725787 : Blo 1815609 2725787 := bstep (se 1 (by rfl) ⟨2044340, by rfl⟩ : syracuseStep 2725787 = 4088681) B4088681
theorem B1816543 : Blo 1815609 1816543 := bstep (se 1 (by rfl) ⟨1362407, by rfl⟩ : syracuseStep 1816543 = 2724815) B2724815
theorem B2300071 : Blo 1815609 2300071 := bstep (se 1 (by rfl) ⟨1725053, by rfl⟩ : syracuseStep 2300071 = 3450107) B3450107
theorem B4086035 : Blo 1815609 4086035 := bstep (se 1 (by rfl) ⟨3064526, by rfl⟩ : syracuseStep 4086035 = 6129053) B6129053
theorem B2300395 : Blo 1815609 2300395 := bstep (se 1 (by rfl) ⟨1725296, by rfl⟩ : syracuseStep 2300395 = 3450593) B3450593
theorem B1817295 : Blo 1815609 1817295 := bstep (se 1 (by rfl) ⟨1362971, by rfl⟩ : syracuseStep 1817295 = 2725943) B2725943
theorem B1817319 : Blo 1815609 1817319 := bstep (se 1 (by rfl) ⟨1362989, by rfl⟩ : syracuseStep 1817319 = 2725979) B2725979
theorem B4086575 : Blo 1815609 4086575 := bstep (se 1 (by rfl) ⟨3064931, by rfl⟩ : syracuseStep 4086575 = 6129863) B6129863
theorem B4086719 : Blo 1815609 4086719 := bstep (se 1 (by rfl) ⟨3065039, by rfl⟩ : syracuseStep 4086719 = 6130079) B6130079
theorem B4086953 : Blo 1815609 4086953 := bstep (se 2 (by rfl) ⟨1532607, by rfl⟩ : syracuseStep 4086953 = 3065215) B3065215
theorem B19643771 : Blo 1815609 19643771 := bstep (se 1 (by rfl) ⟨14732828, by rfl⟩ : syracuseStep 19643771 = 29465657) B29465657
theorem B33144481 : Blo 1815609 33144481 := bstep (se 2 (by rfl) ⟨12429180, by rfl⟩ : syracuseStep 33144481 = 24858361) B24858361
theorem B4087547 : Blo 1815609 4087547 := bstep (se 1 (by rfl) ⟨3065660, by rfl⟩ : syracuseStep 4087547 = 6131321) B6131321
theorem B1132666847 : Blo 1815609 1132666847 := bstep (se 1 (by rfl) ⟨849500135, by rfl⟩ : syracuseStep 1132666847 = 1699000271) B1699000271
theorem B3063899 : Blo 1815609 3063899 := bstep (se 1 (by rfl) ⟨2297924, by rfl⟩ : syracuseStep 3063899 = 4595849) B4595849
theorem B8282843 : Blo 1815609 8282843 := bstep (se 1 (by rfl) ⟨6212132, by rfl⟩ : syracuseStep 8282843 = 12424265) B12424265
theorem B6128999 : Blo 1815609 6128999 := bstep (se 1 (by rfl) ⟨4596749, by rfl⟩ : syracuseStep 6128999 = 9193499) B9193499
theorem B3065755 : Blo 1815609 3065755 := bstep (se 1 (by rfl) ⟨2299316, by rfl⟩ : syracuseStep 3065755 = 4598633) B4598633
theorem B3065897 : Blo 1815609 3065897 := bstep (se 2 (by rfl) ⟨1149711, by rfl⟩ : syracuseStep 3065897 = 2299423) B2299423
theorem B403057403 : Blo 1815609 403057403 := bstep (se 1 (by rfl) ⟨302293052, by rfl⟩ : syracuseStep 403057403 = 604586105) B604586105
theorem B5819147 : Blo 1815609 5819147 := bstep (se 1 (by rfl) ⟨4364360, by rfl⟩ : syracuseStep 5819147 = 8728721) B8728721
theorem B6130511 : Blo 1815609 6130511 := bstep (se 1 (by rfl) ⟨4597883, by rfl⟩ : syracuseStep 6130511 = 9195767) B9195767
theorem B3066761 : Blo 1815609 3066761 := bstep (se 2 (by rfl) ⟨1150035, by rfl⟩ : syracuseStep 3066761 = 2300071) B2300071
theorem B3066815 : Blo 1815609 3066815 := bstep (se 1 (by rfl) ⟨2300111, by rfl⟩ : syracuseStep 3066815 = 4600223) B4600223
theorem B113331403 : Blo 1815609 113331403 := bstep (se 1 (by rfl) ⟨84998552, by rfl⟩ : syracuseStep 113331403 = 169997105) B169997105
theorem B3067193 : Blo 1815609 3067193 := bstep (se 2 (by rfl) ⟨1150197, by rfl⟩ : syracuseStep 3067193 = 2300395) B2300395
theorem B3681895 : Blo 1815609 3681895 := bstep (se 1 (by rfl) ⟨2761421, by rfl⟩ : syracuseStep 3681895 = 5522843) B5522843
theorem B47189783 : Blo 1815609 47189783 := bstep (se 1 (by rfl) ⟨35392337, by rfl⟩ : syracuseStep 47189783 = 70784675) B70784675
theorem B6131483 : Blo 1815609 6131483 := bstep (se 1 (by rfl) ⟨4598612, by rfl⟩ : syracuseStep 6131483 = 9197225) B9197225
theorem B2723615 : Blo 1815609 2723615 := bstep (se 1 (by rfl) ⟨2042711, by rfl⟩ : syracuseStep 2723615 = 4085423) B4085423
theorem B4599787 : Blo 1815609 4599787 := bstep (se 1 (by rfl) ⟨3449840, by rfl⟩ : syracuseStep 4599787 = 6899681) B6899681
theorem B11644955 : Blo 1815609 11644955 := bstep (se 1 (by rfl) ⟨8733716, by rfl⟩ : syracuseStep 11644955 = 17467433) B17467433
theorem B4599899 : Blo 1815609 4599899 := bstep (se 1 (by rfl) ⟨3449924, by rfl⟩ : syracuseStep 4599899 = 6899849) B6899849
theorem B2724023 : Blo 1815609 2724023 := bstep (se 1 (by rfl) ⟨2043017, by rfl⟩ : syracuseStep 2724023 = 4086035) B4086035
theorem B6893849 : Blo 1815609 6893849 := bstep (se 2 (by rfl) ⟨2585193, by rfl⟩ : syracuseStep 6893849 = 5170387) B5170387
theorem B2724383 : Blo 1815609 2724383 := bstep (se 1 (by rfl) ⟨2043287, by rfl⟩ : syracuseStep 2724383 = 4086575) B4086575
theorem B2724479 : Blo 1815609 2724479 := bstep (se 1 (by rfl) ⟨2043359, by rfl⟩ : syracuseStep 2724479 = 4086719) B4086719
theorem B2724521 : Blo 1815609 2724521 := bstep (se 2 (by rfl) ⟨1021695, by rfl⟩ : syracuseStep 2724521 = 2043391) B2043391
theorem B44200637 : Blo 1815609 44200637 := bstep (se 3 (by rfl) ⟨8287619, by rfl⟩ : syracuseStep 44200637 = 16575239) B16575239
theorem B2724635 : Blo 1815609 2724635 := bstep (se 1 (by rfl) ⟨2043476, by rfl⟩ : syracuseStep 2724635 = 4086953) B4086953
theorem B44192641 : Blo 1815609 44192641 := bstep (se 2 (by rfl) ⟨16572240, by rfl⟩ : syracuseStep 44192641 = 33144481) B33144481
theorem B6132617 : Blo 1815609 6132617 := bstep (se 2 (by rfl) ⟨2299731, by rfl⟩ : syracuseStep 6132617 = 4599463) B4599463
theorem B13095847 : Blo 1815609 13095847 := bstep (se 1 (by rfl) ⟨9821885, by rfl⟩ : syracuseStep 13095847 = 19643771) B19643771
theorem B2725031 : Blo 1815609 2725031 := bstep (se 1 (by rfl) ⟨2043773, by rfl⟩ : syracuseStep 2725031 = 4087547) B4087547
theorem B755111231 : Blo 1815609 755111231 := bstep (se 1 (by rfl) ⟨566333423, by rfl⟩ : syracuseStep 755111231 = 1132666847) B1132666847
theorem B10343963 : Blo 1815609 10343963 := bstep (se 1 (by rfl) ⟨7757972, by rfl⟩ : syracuseStep 10343963 = 15515945) B15515945
theorem B4085351 : Blo 1815609 4085351 := bstep (se 1 (by rfl) ⟨3064013, by rfl⟩ : syracuseStep 4085351 = 6128027) B6128027
theorem B2725535 : Blo 1815609 2725535 := bstep (se 1 (by rfl) ⟨2044151, by rfl⟩ : syracuseStep 2725535 = 4088303) B4088303
theorem B6133481 : Blo 1815609 6133481 := bstep (se 2 (by rfl) ⟨2300055, by rfl⟩ : syracuseStep 6133481 = 4600111) B4600111
theorem B6133535 : Blo 1815609 6133535 := bstep (se 1 (by rfl) ⟨4600151, by rfl⟩ : syracuseStep 6133535 = 9200303) B9200303
theorem B2725883 : Blo 1815609 2725883 := bstep (se 1 (by rfl) ⟨2044412, by rfl⟩ : syracuseStep 2725883 = 4088825) B4088825
theorem B4086143 : Blo 1815609 4086143 := bstep (se 1 (by rfl) ⟨3064607, by rfl⟩ : syracuseStep 4086143 = 6129215) B6129215
theorem B2988443 : Blo 1815609 2988443 := bstep (se 1 (by rfl) ⟨2241332, by rfl⟩ : syracuseStep 2988443 = 4482665) B4482665
theorem B1816987 : Blo 1815609 1816987 := bstep (se 1 (by rfl) ⟨1362740, by rfl⟩ : syracuseStep 1816987 = 2725481) B2725481
theorem B3881447 : Blo 1815609 3881447 := bstep (se 1 (by rfl) ⟨2911085, by rfl⟩ : syracuseStep 3881447 = 5822171) B5822171
theorem B46569977 : Blo 1815609 46569977 := bstep (se 2 (by rfl) ⟨17463741, by rfl⟩ : syracuseStep 46569977 = 34927483) B34927483
theorem B1817191 : Blo 1815609 1817191 := bstep (se 1 (by rfl) ⟨1362893, by rfl⟩ : syracuseStep 1817191 = 2725787) B2725787
theorem B52353863 : Blo 1815609 52353863 := bstep (se 1 (by rfl) ⟨39265397, by rfl⟩ : syracuseStep 52353863 = 78530795) B78530795
theorem B6299495 : Blo 1815609 6299495 := bstep (se 1 (by rfl) ⟨4724621, by rfl⟩ : syracuseStep 6299495 = 9449243) B9449243
theorem B4595899 : Blo 1815609 4595899 := bstep (se 1 (by rfl) ⟨3446924, by rfl⟩ : syracuseStep 4595899 = 6893849) B6893849
theorem B29467091 : Blo 1815609 29467091 := bstep (se 1 (by rfl) ⟨22100318, by rfl⟩ : syracuseStep 29467091 = 44200637) B44200637
theorem B5521895 : Blo 1815609 5521895 := bstep (se 1 (by rfl) ⟨4141421, by rfl⟩ : syracuseStep 5521895 = 8282843) B8282843
theorem B4088411 : Blo 1815609 4088411 := bstep (se 1 (by rfl) ⟨3066308, by rfl⟩ : syracuseStep 4088411 = 6132617) B6132617
theorem B503407487 : Blo 1815609 503407487 := bstep (se 1 (by rfl) ⟨377555615, by rfl⟩ : syracuseStep 503407487 = 755111231) B755111231
theorem B4088987 : Blo 1815609 4088987 := bstep (se 1 (by rfl) ⟨3066740, by rfl⟩ : syracuseStep 4088987 = 6133481) B6133481
theorem B4089023 : Blo 1815609 4089023 := bstep (se 1 (by rfl) ⟨3066767, by rfl⟩ : syracuseStep 4089023 = 6133535) B6133535
theorem B1992295 : Blo 1815609 1992295 := bstep (se 1 (by rfl) ⟨1494221, by rfl⟩ : syracuseStep 1992295 = 2988443) B2988443
theorem B4909193 : Blo 1815609 4909193 := bstep (se 2 (by rfl) ⟨1840947, by rfl⟩ : syracuseStep 4909193 = 3681895) B3681895
theorem B31459855 : Blo 1815609 31459855 := bstep (se 1 (by rfl) ⟨23594891, by rfl⟩ : syracuseStep 31459855 = 47189783) B47189783
theorem B2042599 : Blo 1815609 2042599 := bstep (se 1 (by rfl) ⟨1531949, by rfl⟩ : syracuseStep 2042599 = 3063899) B3063899
theorem B3066599 : Blo 1815609 3066599 := bstep (se 1 (by rfl) ⟨2299949, by rfl⟩ : syracuseStep 3066599 = 4599899) B4599899
theorem B2723567 : Blo 1815609 2723567 := bstep (se 1 (by rfl) ⟨2042675, by rfl⟩ : syracuseStep 2723567 = 4085351) B4085351
theorem B17461129 : Blo 1815609 17461129 := bstep (se 2 (by rfl) ⟨6547923, by rfl⟩ : syracuseStep 17461129 = 13095847) B13095847
theorem B2043931 : Blo 1815609 2043931 := bstep (se 1 (by rfl) ⟨1532948, by rfl⟩ : syracuseStep 2043931 = 3065897) B3065897
theorem B2724095 : Blo 1815609 2724095 := bstep (se 1 (by rfl) ⟨2043071, by rfl⟩ : syracuseStep 2724095 = 4086143) B4086143
theorem B3879431 : Blo 1815609 3879431 := bstep (se 1 (by rfl) ⟨2909573, by rfl⟩ : syracuseStep 3879431 = 5819147) B5819147
theorem B34902575 : Blo 1815609 34902575 := bstep (se 1 (by rfl) ⟨26176931, by rfl⟩ : syracuseStep 34902575 = 52353863) B52353863
theorem B2044507 : Blo 1815609 2044507 := bstep (se 1 (by rfl) ⟨1533380, by rfl⟩ : syracuseStep 2044507 = 3066761) B3066761
theorem B2044543 : Blo 1815609 2044543 := bstep (se 1 (by rfl) ⟨1533407, by rfl⟩ : syracuseStep 2044543 = 3066815) B3066815
theorem B2044795 : Blo 1815609 2044795 := bstep (se 1 (by rfl) ⟨1533596, by rfl⟩ : syracuseStep 2044795 = 3067193) B3067193
theorem B1815743 : Blo 1815609 1815743 := bstep (se 1 (by rfl) ⟨1361807, by rfl⟩ : syracuseStep 1815743 = 2723615) B2723615
theorem B4199663 : Blo 1815609 4199663 := bstep (se 1 (by rfl) ⟨3149747, by rfl⟩ : syracuseStep 4199663 = 6299495) B6299495
theorem B6133049 : Blo 1815609 6133049 := bstep (se 2 (by rfl) ⟨2299893, by rfl⟩ : syracuseStep 6133049 = 4599787) B4599787
theorem B7763303 : Blo 1815609 7763303 := bstep (se 1 (by rfl) ⟨5822477, by rfl⟩ : syracuseStep 7763303 = 11644955) B11644955
theorem B1816015 : Blo 1815609 1816015 := bstep (se 1 (by rfl) ⟨1362011, by rfl⟩ : syracuseStep 1816015 = 2724023) B2724023
theorem B1816255 : Blo 1815609 1816255 := bstep (se 1 (by rfl) ⟨1362191, by rfl⟩ : syracuseStep 1816255 = 2724383) B2724383
theorem B1816319 : Blo 1815609 1816319 := bstep (se 1 (by rfl) ⟨1362239, by rfl⟩ : syracuseStep 1816319 = 2724479) B2724479
theorem B1816347 : Blo 1815609 1816347 := bstep (se 1 (by rfl) ⟨1362260, by rfl⟩ : syracuseStep 1816347 = 2724521) B2724521
theorem B1816423 : Blo 1815609 1816423 := bstep (se 1 (by rfl) ⟨1362317, by rfl⟩ : syracuseStep 1816423 = 2724635) B2724635
theorem B1816687 : Blo 1815609 1816687 := bstep (se 1 (by rfl) ⟨1362515, by rfl⟩ : syracuseStep 1816687 = 2725031) B2725031
theorem B4085999 : Blo 1815609 4085999 := bstep (se 1 (by rfl) ⟨3064499, by rfl⟩ : syracuseStep 4085999 = 6128999) B6128999
theorem B6895975 : Blo 1815609 6895975 := bstep (se 1 (by rfl) ⟨5171981, by rfl⟩ : syracuseStep 6895975 = 10343963) B10343963
theorem B1817023 : Blo 1815609 1817023 := bstep (se 1 (by rfl) ⟨1362767, by rfl⟩ : syracuseStep 1817023 = 2725535) B2725535
theorem B58923521 : Blo 1815609 58923521 := bstep (se 2 (by rfl) ⟨22096320, by rfl⟩ : syracuseStep 58923521 = 44192641) B44192641
theorem B1817255 : Blo 1815609 1817255 := bstep (se 1 (by rfl) ⟨1362941, by rfl⟩ : syracuseStep 1817255 = 2725883) B2725883
theorem B151108537 : Blo 1815609 151108537 := bstep (se 2 (by rfl) ⟨56665701, by rfl⟩ : syracuseStep 151108537 = 113331403) B113331403
theorem B2587631 : Blo 1815609 2587631 := bstep (se 1 (by rfl) ⟨1940723, by rfl⟩ : syracuseStep 2587631 = 3881447) B3881447
theorem B31046651 : Blo 1815609 31046651 := bstep (se 1 (by rfl) ⟨23284988, by rfl⟩ : syracuseStep 31046651 = 46569977) B46569977
theorem B268704935 : Blo 1815609 268704935 := bstep (se 1 (by rfl) ⟨201528701, by rfl⟩ : syracuseStep 268704935 = 403057403) B403057403
theorem B4087007 : Blo 1815609 4087007 := bstep (se 1 (by rfl) ⟨3065255, by rfl⟩ : syracuseStep 4087007 = 6130511) B6130511
theorem B4087655 : Blo 1815609 4087655 := bstep (se 1 (by rfl) ⟨3065741, by rfl⟩ : syracuseStep 4087655 = 6131483) B6131483
theorem B4087673 : Blo 1815609 4087673 := bstep (se 2 (by rfl) ⟨1532877, by rfl⟩ : syracuseStep 4087673 = 3065755) B3065755
theorem B6127865 : Blo 1815609 6127865 := bstep (se 2 (by rfl) ⟨2297949, by rfl⟩ : syracuseStep 6127865 = 4595899) B4595899
theorem B19644727 : Blo 1815609 19644727 := bstep (se 1 (by rfl) ⟨14733545, by rfl⟩ : syracuseStep 19644727 = 29467091) B29467091
theorem B10625573 : Blo 1815609 10625573 := bstep (se 4 (by rfl) ⟨996147, by rfl⟩ : syracuseStep 10625573 = 1992295) B1992295
theorem B4088699 : Blo 1815609 4088699 := bstep (se 1 (by rfl) ⟨3066524, by rfl⟩ : syracuseStep 4088699 = 6133049) B6133049
theorem B20702141 : Blo 1815609 20702141 := bstep (se 3 (by rfl) ⟨3881651, by rfl⟩ : syracuseStep 20702141 = 7763303) B7763303
theorem B39282347 : Blo 1815609 39282347 := bstep (se 1 (by rfl) ⟨29461760, by rfl⟩ : syracuseStep 39282347 = 58923521) B58923521
theorem B179136623 : Blo 1815609 179136623 := bstep (se 1 (by rfl) ⟨134352467, by rfl⟩ : syracuseStep 179136623 = 268704935) B268704935
theorem B6900349 : Blo 1815609 6900349 := bstep (se 3 (by rfl) ⟨1293815, by rfl⟩ : syracuseStep 6900349 = 2587631) B2587631
theorem B3681263 : Blo 1815609 3681263 := bstep (se 1 (by rfl) ⟨2760947, by rfl⟩ : syracuseStep 3681263 = 5521895) B5521895
theorem B23268383 : Blo 1815609 23268383 := bstep (se 1 (by rfl) ⟨17451287, by rfl⟩ : syracuseStep 23268383 = 34902575) B34902575
theorem B9194633 : Blo 1815609 9194633 := bstep (se 2 (by rfl) ⟨3447987, by rfl⟩ : syracuseStep 9194633 = 6895975) B6895975
theorem B335604991 : Blo 1815609 335604991 := bstep (se 1 (by rfl) ⟨251703743, by rfl⟩ : syracuseStep 335604991 = 503407487) B503407487
theorem B41946473 : Blo 1815609 41946473 := bstep (se 2 (by rfl) ⟨15729927, by rfl⟩ : syracuseStep 41946473 = 31459855) B31459855
theorem B2723465 : Blo 1815609 2723465 := bstep (se 2 (by rfl) ⟨1021299, by rfl⟩ : syracuseStep 2723465 = 2042599) B2042599
theorem B201478049 : Blo 1815609 201478049 := bstep (se 2 (by rfl) ⟨75554268, by rfl⟩ : syracuseStep 201478049 = 151108537) B151108537
theorem B3272795 : Blo 1815609 3272795 := bstep (se 1 (by rfl) ⟨2454596, by rfl⟩ : syracuseStep 3272795 = 4909193) B4909193
theorem B2723999 : Blo 1815609 2723999 := bstep (se 1 (by rfl) ⟨2042999, by rfl⟩ : syracuseStep 2723999 = 4085999) B4085999
theorem B2044399 : Blo 1815609 2044399 := bstep (se 1 (by rfl) ⟨1533299, by rfl⟩ : syracuseStep 2044399 = 3066599) B3066599
theorem B20697767 : Blo 1815609 20697767 := bstep (se 1 (by rfl) ⟨15523325, by rfl⟩ : syracuseStep 20697767 = 31046651) B31046651
theorem B2724671 : Blo 1815609 2724671 := bstep (se 1 (by rfl) ⟨2043503, by rfl⟩ : syracuseStep 2724671 = 4087007) B4087007
theorem B1815711 : Blo 1815609 1815711 := bstep (se 1 (by rfl) ⟨1361783, by rfl⟩ : syracuseStep 1815711 = 2723567) B2723567
theorem B2725103 : Blo 1815609 2725103 := bstep (se 1 (by rfl) ⟨2043827, by rfl⟩ : syracuseStep 2725103 = 4087655) B4087655
theorem B2725115 : Blo 1815609 2725115 := bstep (se 1 (by rfl) ⟨2043836, by rfl⟩ : syracuseStep 2725115 = 4087673) B4087673
theorem B2725241 : Blo 1815609 2725241 := bstep (se 2 (by rfl) ⟨1021965, by rfl⟩ : syracuseStep 2725241 = 2043931) B2043931
theorem B1816063 : Blo 1815609 1816063 := bstep (se 1 (by rfl) ⟨1362047, by rfl⟩ : syracuseStep 1816063 = 2724095) B2724095
theorem B2586287 : Blo 1815609 2586287 := bstep (se 1 (by rfl) ⟨1939715, by rfl⟩ : syracuseStep 2586287 = 3879431) B3879431
theorem B2725607 : Blo 1815609 2725607 := bstep (se 1 (by rfl) ⟨2044205, by rfl⟩ : syracuseStep 2725607 = 4088411) B4088411
theorem B2725991 : Blo 1815609 2725991 := bstep (se 1 (by rfl) ⟨2044493, by rfl⟩ : syracuseStep 2725991 = 4088987) B4088987
theorem B2726009 : Blo 1815609 2726009 := bstep (se 2 (by rfl) ⟨1022253, by rfl⟩ : syracuseStep 2726009 = 2044507) B2044507
theorem B2726015 : Blo 1815609 2726015 := bstep (se 1 (by rfl) ⟨2044511, by rfl⟩ : syracuseStep 2726015 = 4089023) B4089023
theorem B2799775 : Blo 1815609 2799775 := bstep (se 1 (by rfl) ⟨2099831, by rfl⟩ : syracuseStep 2799775 = 4199663) B4199663
theorem B2726057 : Blo 1815609 2726057 := bstep (se 2 (by rfl) ⟨1022271, by rfl⟩ : syracuseStep 2726057 = 2044543) B2044543
theorem B2726393 : Blo 1815609 2726393 := bstep (se 2 (by rfl) ⟨1022397, by rfl⟩ : syracuseStep 2726393 = 2044795) B2044795
theorem B23281505 : Blo 1815609 23281505 := bstep (se 2 (by rfl) ⟨8730564, by rfl⟩ : syracuseStep 23281505 = 17461129) B17461129
theorem B9200465 : Blo 1815609 9200465 := bstep (se 2 (by rfl) ⟨3450174, by rfl⟩ : syracuseStep 9200465 = 6900349) B6900349
theorem B119424415 : Blo 1815609 119424415 := bstep (se 1 (by rfl) ⟨89568311, by rfl⟩ : syracuseStep 119424415 = 179136623) B179136623
theorem B447473321 : Blo 1815609 447473321 := bstep (se 2 (by rfl) ⟨167802495, by rfl⟩ : syracuseStep 447473321 = 335604991) B335604991
theorem B104752925 : Blo 1815609 104752925 := bstep (se 3 (by rfl) ⟨19641173, by rfl⟩ : syracuseStep 104752925 = 39282347) B39282347
theorem B6129755 : Blo 1815609 6129755 := bstep (se 1 (by rfl) ⟨4597316, by rfl⟩ : syracuseStep 6129755 = 9194633) B9194633
theorem B134318699 : Blo 1815609 134318699 := bstep (se 1 (by rfl) ⟨100739024, by rfl⟩ : syracuseStep 134318699 = 201478049) B201478049
theorem B2181863 : Blo 1815609 2181863 := bstep (se 1 (by rfl) ⟨1636397, by rfl⟩ : syracuseStep 2181863 = 3272795) B3272795
theorem B26192969 : Blo 1815609 26192969 := bstep (se 2 (by rfl) ⟨9822363, by rfl⟩ : syracuseStep 26192969 = 19644727) B19644727
theorem B13798511 : Blo 1815609 13798511 := bstep (se 1 (by rfl) ⟨10348883, by rfl⟩ : syracuseStep 13798511 = 20697767) B20697767
theorem B2454175 : Blo 1815609 2454175 := bstep (se 1 (by rfl) ⟨1840631, by rfl⟩ : syracuseStep 2454175 = 3681263) B3681263
theorem B15512255 : Blo 1815609 15512255 := bstep (se 1 (by rfl) ⟨11634191, by rfl⟩ : syracuseStep 15512255 = 23268383) B23268383
theorem B27964315 : Blo 1815609 27964315 := bstep (se 1 (by rfl) ⟨20973236, by rfl⟩ : syracuseStep 27964315 = 41946473) B41946473
theorem B1815643 : Blo 1815609 1815643 := bstep (se 1 (by rfl) ⟨1361732, by rfl⟩ : syracuseStep 1815643 = 2723465) B2723465
theorem B15521003 : Blo 1815609 15521003 := bstep (se 1 (by rfl) ⟨11640752, by rfl⟩ : syracuseStep 15521003 = 23281505) B23281505
theorem B1815999 : Blo 1815609 1815999 := bstep (se 1 (by rfl) ⟨1361999, by rfl⟩ : syracuseStep 1815999 = 2723999) B2723999
theorem B4085243 : Blo 1815609 4085243 := bstep (se 1 (by rfl) ⟨3063932, by rfl⟩ : syracuseStep 4085243 = 6127865) B6127865
theorem B3733033 : Blo 1815609 3733033 := bstep (se 2 (by rfl) ⟨1399887, by rfl⟩ : syracuseStep 3733033 = 2799775) B2799775
theorem B7083715 : Blo 1815609 7083715 := bstep (se 1 (by rfl) ⟨5312786, by rfl⟩ : syracuseStep 7083715 = 10625573) B10625573
theorem B1816447 : Blo 1815609 1816447 := bstep (se 1 (by rfl) ⟨1362335, by rfl⟩ : syracuseStep 1816447 = 2724671) B2724671
theorem B2725799 : Blo 1815609 2725799 := bstep (se 1 (by rfl) ⟨2044349, by rfl⟩ : syracuseStep 2725799 = 4088699) B4088699
theorem B13801427 : Blo 1815609 13801427 := bstep (se 1 (by rfl) ⟨10351070, by rfl⟩ : syracuseStep 13801427 = 20702141) B20702141
theorem B2725865 : Blo 1815609 2725865 := bstep (se 2 (by rfl) ⟨1022199, by rfl⟩ : syracuseStep 2725865 = 2044399) B2044399
theorem B1816735 : Blo 1815609 1816735 := bstep (se 1 (by rfl) ⟨1362551, by rfl⟩ : syracuseStep 1816735 = 2725103) B2725103
theorem B1816743 : Blo 1815609 1816743 := bstep (se 1 (by rfl) ⟨1362557, by rfl⟩ : syracuseStep 1816743 = 2725115) B2725115
theorem B1816827 : Blo 1815609 1816827 := bstep (se 1 (by rfl) ⟨1362620, by rfl⟩ : syracuseStep 1816827 = 2725241) B2725241
theorem B1817071 : Blo 1815609 1817071 := bstep (se 1 (by rfl) ⟨1362803, by rfl⟩ : syracuseStep 1817071 = 2725607) B2725607
theorem B1817327 : Blo 1815609 1817327 := bstep (se 1 (by rfl) ⟨1362995, by rfl⟩ : syracuseStep 1817327 = 2725991) B2725991
theorem B1817339 : Blo 1815609 1817339 := bstep (se 1 (by rfl) ⟨1363004, by rfl⟩ : syracuseStep 1817339 = 2726009) B2726009
theorem B1817343 : Blo 1815609 1817343 := bstep (se 1 (by rfl) ⟨1363007, by rfl⟩ : syracuseStep 1817343 = 2726015) B2726015
theorem B1817371 : Blo 1815609 1817371 := bstep (se 1 (by rfl) ⟨1363028, by rfl⟩ : syracuseStep 1817371 = 2726057) B2726057
theorem B1817595 : Blo 1815609 1817595 := bstep (se 1 (by rfl) ⟨1363196, by rfl⟩ : syracuseStep 1817595 = 2726393) B2726393
theorem B6896765 : Blo 1815609 6896765 := bstep (se 3 (by rfl) ⟨1293143, by rfl⟩ : syracuseStep 6896765 = 2586287) B2586287
theorem B10347335 : Blo 1815609 10347335 := bstep (se 1 (by rfl) ⟨7760501, by rfl⟩ : syracuseStep 10347335 = 15521003) B15521003
theorem B9200951 : Blo 1815609 9200951 := bstep (se 1 (by rfl) ⟨6900713, by rfl⟩ : syracuseStep 9200951 = 13801427) B13801427
theorem B5818301 : Blo 1815609 5818301 := bstep (se 3 (by rfl) ⟨1090931, by rfl⟩ : syracuseStep 5818301 = 2181863) B2181863
theorem B4597843 : Blo 1815609 4597843 := bstep (se 1 (by rfl) ⟨3448382, by rfl⟩ : syracuseStep 4597843 = 6896765) B6896765
theorem B10341503 : Blo 1815609 10341503 := bstep (se 1 (by rfl) ⟨7756127, by rfl⟩ : syracuseStep 10341503 = 15512255) B15512255
theorem B3272233 : Blo 1815609 3272233 := bstep (se 2 (by rfl) ⟨1227087, by rfl⟩ : syracuseStep 3272233 = 2454175) B2454175
theorem B2723495 : Blo 1815609 2723495 := bstep (se 1 (by rfl) ⟨2042621, by rfl⟩ : syracuseStep 2723495 = 4085243) B4085243
theorem B298315547 : Blo 1815609 298315547 := bstep (se 1 (by rfl) ⟨223736660, by rfl⟩ : syracuseStep 298315547 = 447473321) B447473321
theorem B37285753 : Blo 1815609 37285753 := bstep (se 2 (by rfl) ⟨13982157, by rfl⟩ : syracuseStep 37285753 = 27964315) B27964315
theorem B159232553 : Blo 1815609 159232553 := bstep (se 2 (by rfl) ⟨59712207, by rfl⟩ : syracuseStep 159232553 = 119424415) B119424415
theorem B17461979 : Blo 1815609 17461979 := bstep (se 1 (by rfl) ⟨13096484, by rfl⟩ : syracuseStep 17461979 = 26192969) B26192969
theorem B4977377 : Blo 1815609 4977377 := bstep (se 2 (by rfl) ⟨1866516, by rfl⟩ : syracuseStep 4977377 = 3733033) B3733033
theorem B6133643 : Blo 1815609 6133643 := bstep (se 1 (by rfl) ⟨4600232, by rfl⟩ : syracuseStep 6133643 = 9200465) B9200465
theorem B69835283 : Blo 1815609 69835283 := bstep (se 1 (by rfl) ⟨52376462, by rfl⟩ : syracuseStep 69835283 = 104752925) B104752925
theorem B1817199 : Blo 1815609 1817199 := bstep (se 1 (by rfl) ⟨1362899, by rfl⟩ : syracuseStep 1817199 = 2725799) B2725799
theorem B1817243 : Blo 1815609 1817243 := bstep (se 1 (by rfl) ⟨1362932, by rfl⟩ : syracuseStep 1817243 = 2725865) B2725865
theorem B4086503 : Blo 1815609 4086503 := bstep (se 1 (by rfl) ⟨3064877, by rfl⟩ : syracuseStep 4086503 = 6129755) B6129755
theorem B89545799 : Blo 1815609 89545799 := bstep (se 1 (by rfl) ⟨67159349, by rfl⟩ : syracuseStep 89545799 = 134318699) B134318699
theorem B9199007 : Blo 1815609 9199007 := bstep (se 1 (by rfl) ⟨6899255, by rfl⟩ : syracuseStep 9199007 = 13798511) B13798511
theorem B9444953 : Blo 1815609 9444953 := bstep (se 2 (by rfl) ⟨3541857, by rfl⟩ : syracuseStep 9444953 = 7083715) B7083715
theorem B11641319 : Blo 1815609 11641319 := bstep (se 1 (by rfl) ⟨8730989, by rfl⟩ : syracuseStep 11641319 = 17461979) B17461979
theorem B3318251 : Blo 1815609 3318251 := bstep (se 1 (by rfl) ⟨2488688, by rfl⟩ : syracuseStep 3318251 = 4977377) B4977377
theorem B6898223 : Blo 1815609 6898223 := bstep (se 1 (by rfl) ⟨5173667, by rfl⟩ : syracuseStep 6898223 = 10347335) B10347335
theorem B4089095 : Blo 1815609 4089095 := bstep (se 1 (by rfl) ⟨3066821, by rfl⟩ : syracuseStep 4089095 = 6133643) B6133643
theorem B46556855 : Blo 1815609 46556855 := bstep (se 1 (by rfl) ⟨34917641, by rfl⟩ : syracuseStep 46556855 = 69835283) B69835283
theorem B59697199 : Blo 1815609 59697199 := bstep (se 1 (by rfl) ⟨44772899, by rfl⟩ : syracuseStep 59697199 = 89545799) B89545799
theorem B6130457 : Blo 1815609 6130457 := bstep (se 2 (by rfl) ⟨2298921, by rfl⟩ : syracuseStep 6130457 = 4597843) B4597843
theorem B106155035 : Blo 1815609 106155035 := bstep (se 1 (by rfl) ⟨79616276, by rfl⟩ : syracuseStep 106155035 = 159232553) B159232553
theorem B3878867 : Blo 1815609 3878867 := bstep (se 1 (by rfl) ⟨2909150, by rfl⟩ : syracuseStep 3878867 = 5818301) B5818301
theorem B2724335 : Blo 1815609 2724335 := bstep (se 1 (by rfl) ⟨2043251, by rfl⟩ : syracuseStep 2724335 = 4086503) B4086503
theorem B4362977 : Blo 1815609 4362977 := bstep (se 2 (by rfl) ⟨1636116, by rfl⟩ : syracuseStep 4362977 = 3272233) B3272233
theorem B6894335 : Blo 1815609 6894335 := bstep (se 1 (by rfl) ⟨5170751, by rfl⟩ : syracuseStep 6894335 = 10341503) B10341503
theorem B6132671 : Blo 1815609 6132671 := bstep (se 1 (by rfl) ⟨4599503, by rfl⟩ : syracuseStep 6132671 = 9199007) B9199007
theorem B6296635 : Blo 1815609 6296635 := bstep (se 1 (by rfl) ⟨4722476, by rfl⟩ : syracuseStep 6296635 = 9444953) B9444953
theorem B1815663 : Blo 1815609 1815663 := bstep (se 1 (by rfl) ⟨1361747, by rfl⟩ : syracuseStep 1815663 = 2723495) B2723495
theorem B49714337 : Blo 1815609 49714337 := bstep (se 2 (by rfl) ⟨18642876, by rfl⟩ : syracuseStep 49714337 = 37285753) B37285753
theorem B6133967 : Blo 1815609 6133967 := bstep (se 1 (by rfl) ⟨4600475, by rfl⟩ : syracuseStep 6133967 = 9200951) B9200951
theorem B198877031 : Blo 1815609 198877031 := bstep (se 1 (by rfl) ⟨149157773, by rfl⟩ : syracuseStep 198877031 = 298315547) B298315547
theorem B2908651 : Blo 1815609 2908651 := bstep (se 1 (by rfl) ⟨2181488, by rfl⟩ : syracuseStep 2908651 = 4362977) B4362977
theorem B4596223 : Blo 1815609 4596223 := bstep (se 1 (by rfl) ⟨3447167, by rfl⟩ : syracuseStep 4596223 = 6894335) B6894335
theorem B4088447 : Blo 1815609 4088447 := bstep (se 1 (by rfl) ⟨3066335, by rfl⟩ : syracuseStep 4088447 = 6132671) B6132671
theorem B8848669 : Blo 1815609 8848669 := bstep (se 3 (by rfl) ⟨1659125, by rfl⟩ : syracuseStep 8848669 = 3318251) B3318251
theorem B4089311 : Blo 1815609 4089311 := bstep (se 1 (by rfl) ⟨3066983, by rfl⟩ : syracuseStep 4089311 = 6133967) B6133967
theorem B79596265 : Blo 1815609 79596265 := bstep (se 2 (by rfl) ⟨29848599, by rfl⟩ : syracuseStep 79596265 = 59697199) B59697199
theorem B33582053 : Blo 1815609 33582053 := bstep (se 4 (by rfl) ⟨3148317, by rfl⟩ : syracuseStep 33582053 = 6296635) B6296635
theorem B7760879 : Blo 1815609 7760879 := bstep (se 1 (by rfl) ⟨5820659, by rfl⟩ : syracuseStep 7760879 = 11641319) B11641319
theorem B4598815 : Blo 1815609 4598815 := bstep (se 1 (by rfl) ⟨3449111, by rfl⟩ : syracuseStep 4598815 = 6898223) B6898223
theorem B10343645 : Blo 1815609 10343645 := bstep (se 3 (by rfl) ⟨1939433, by rfl⟩ : syracuseStep 10343645 = 3878867) B3878867
theorem B132584687 : Blo 1815609 132584687 := bstep (se 1 (by rfl) ⟨99438515, by rfl⟩ : syracuseStep 132584687 = 198877031) B198877031
theorem B1816223 : Blo 1815609 1816223 := bstep (se 1 (by rfl) ⟨1362167, by rfl⟩ : syracuseStep 1816223 = 2724335) B2724335
theorem B33142891 : Blo 1815609 33142891 := bstep (se 1 (by rfl) ⟨24857168, by rfl⟩ : syracuseStep 33142891 = 49714337) B49714337
theorem B2726063 : Blo 1815609 2726063 := bstep (se 1 (by rfl) ⟨2044547, by rfl⟩ : syracuseStep 2726063 = 4089095) B4089095
theorem B31037903 : Blo 1815609 31037903 := bstep (se 1 (by rfl) ⟨23278427, by rfl⟩ : syracuseStep 31037903 = 46556855) B46556855
theorem B4086971 : Blo 1815609 4086971 := bstep (se 1 (by rfl) ⟨3065228, by rfl⟩ : syracuseStep 4086971 = 6130457) B6130457
theorem B70770023 : Blo 1815609 70770023 := bstep (se 1 (by rfl) ⟨53077517, by rfl⟩ : syracuseStep 70770023 = 106155035) B106155035
theorem B6128297 : Blo 1815609 6128297 := bstep (se 2 (by rfl) ⟨2298111, by rfl⟩ : syracuseStep 6128297 = 4596223) B4596223
theorem B106128353 : Blo 1815609 106128353 := bstep (se 2 (by rfl) ⟨39798132, by rfl⟩ : syracuseStep 106128353 = 79596265) B79596265
theorem B11798225 : Blo 1815609 11798225 := bstep (se 2 (by rfl) ⟨4424334, by rfl⟩ : syracuseStep 11798225 = 8848669) B8848669
theorem B47180015 : Blo 1815609 47180015 := bstep (se 1 (by rfl) ⟨35385011, by rfl⟩ : syracuseStep 47180015 = 70770023) B70770023
theorem B44190521 : Blo 1815609 44190521 := bstep (se 2 (by rfl) ⟨16571445, by rfl⟩ : syracuseStep 44190521 = 33142891) B33142891
theorem B3878201 : Blo 1815609 3878201 := bstep (se 2 (by rfl) ⟨1454325, by rfl⟩ : syracuseStep 3878201 = 2908651) B2908651
theorem B6131753 : Blo 1815609 6131753 := bstep (se 2 (by rfl) ⟨2299407, by rfl⟩ : syracuseStep 6131753 = 4598815) B4598815
theorem B5173919 : Blo 1815609 5173919 := bstep (se 1 (by rfl) ⟨3880439, by rfl⟩ : syracuseStep 5173919 = 7760879) B7760879
theorem B2724647 : Blo 1815609 2724647 := bstep (se 1 (by rfl) ⟨2043485, by rfl⟩ : syracuseStep 2724647 = 4086971) B4086971
theorem B2725631 : Blo 1815609 2725631 := bstep (se 1 (by rfl) ⟨2044223, by rfl⟩ : syracuseStep 2725631 = 4088447) B4088447
theorem B6895763 : Blo 1815609 6895763 := bstep (se 1 (by rfl) ⟨5171822, by rfl⟩ : syracuseStep 6895763 = 10343645) B10343645
theorem B88389791 : Blo 1815609 88389791 := bstep (se 1 (by rfl) ⟨66292343, by rfl⟩ : syracuseStep 88389791 = 132584687) B132584687
theorem B2726207 : Blo 1815609 2726207 := bstep (se 1 (by rfl) ⟨2044655, by rfl⟩ : syracuseStep 2726207 = 4089311) B4089311
theorem B1817375 : Blo 1815609 1817375 := bstep (se 1 (by rfl) ⟨1363031, by rfl⟩ : syracuseStep 1817375 = 2726063) B2726063
theorem B20691935 : Blo 1815609 20691935 := bstep (se 1 (by rfl) ⟨15518951, by rfl⟩ : syracuseStep 20691935 = 31037903) B31037903
theorem B22388035 : Blo 1815609 22388035 := bstep (se 1 (by rfl) ⟨16791026, by rfl⟩ : syracuseStep 22388035 = 33582053) B33582053
theorem B4087835 : Blo 1815609 4087835 := bstep (se 1 (by rfl) ⟨3065876, by rfl⟩ : syracuseStep 4087835 = 6131753) B6131753
theorem B3449279 : Blo 1815609 3449279 := bstep (se 1 (by rfl) ⟨2586959, by rfl⟩ : syracuseStep 3449279 = 5173919) B5173919
theorem B7865483 : Blo 1815609 7865483 := bstep (se 1 (by rfl) ⟨5899112, by rfl⟩ : syracuseStep 7865483 = 11798225) B11798225
theorem B4597175 : Blo 1815609 4597175 := bstep (se 1 (by rfl) ⟨3447881, by rfl⟩ : syracuseStep 4597175 = 6895763) B6895763
theorem B58926527 : Blo 1815609 58926527 := bstep (se 1 (by rfl) ⟨44194895, by rfl⟩ : syracuseStep 58926527 = 88389791) B88389791
theorem B29460347 : Blo 1815609 29460347 := bstep (se 1 (by rfl) ⟨22095260, by rfl⟩ : syracuseStep 29460347 = 44190521) B44190521
theorem B31453343 : Blo 1815609 31453343 := bstep (se 1 (by rfl) ⟨23590007, by rfl⟩ : syracuseStep 31453343 = 47180015) B47180015
theorem B2585467 : Blo 1815609 2585467 := bstep (se 1 (by rfl) ⟨1939100, by rfl⟩ : syracuseStep 2585467 = 3878201) B3878201
theorem B4085531 : Blo 1815609 4085531 := bstep (se 1 (by rfl) ⟨3064148, by rfl⟩ : syracuseStep 4085531 = 6128297) B6128297
theorem B1816431 : Blo 1815609 1816431 := bstep (se 1 (by rfl) ⟨1362323, by rfl⟩ : syracuseStep 1816431 = 2724647) B2724647
theorem B1817087 : Blo 1815609 1817087 := bstep (se 1 (by rfl) ⟨1362815, by rfl⟩ : syracuseStep 1817087 = 2725631) B2725631
theorem B1817471 : Blo 1815609 1817471 := bstep (se 1 (by rfl) ⟨1363103, by rfl⟩ : syracuseStep 1817471 = 2726207) B2726207
theorem B29850713 : Blo 1815609 29850713 := bstep (se 2 (by rfl) ⟨11194017, by rfl⟩ : syracuseStep 29850713 = 22388035) B22388035
theorem B13794623 : Blo 1815609 13794623 := bstep (se 1 (by rfl) ⟨10345967, by rfl⟩ : syracuseStep 13794623 = 20691935) B20691935
theorem B283008941 : Blo 1815609 283008941 := bstep (se 3 (by rfl) ⟨53064176, by rfl⟩ : syracuseStep 283008941 = 106128353) B106128353
theorem B3064783 : Blo 1815609 3064783 := bstep (se 1 (by rfl) ⟨2298587, by rfl⟩ : syracuseStep 3064783 = 4597175) B4597175
theorem B19900475 : Blo 1815609 19900475 := bstep (se 1 (by rfl) ⟨14925356, by rfl⟩ : syracuseStep 19900475 = 29850713) B29850713
theorem B188672627 : Blo 1815609 188672627 := bstep (se 1 (by rfl) ⟨141504470, by rfl⟩ : syracuseStep 188672627 = 283008941) B283008941
theorem B20974621 : Blo 1815609 20974621 := bstep (se 3 (by rfl) ⟨3932741, by rfl⟩ : syracuseStep 20974621 = 7865483) B7865483
theorem B39284351 : Blo 1815609 39284351 := bstep (se 1 (by rfl) ⟨29463263, by rfl⟩ : syracuseStep 39284351 = 58926527) B58926527
theorem B2723687 : Blo 1815609 2723687 := bstep (se 1 (by rfl) ⟨2042765, by rfl⟩ : syracuseStep 2723687 = 4085531) B4085531
theorem B19640231 : Blo 1815609 19640231 := bstep (se 1 (by rfl) ⟨14730173, by rfl⟩ : syracuseStep 19640231 = 29460347) B29460347
theorem B9196415 : Blo 1815609 9196415 := bstep (se 1 (by rfl) ⟨6897311, by rfl⟩ : syracuseStep 9196415 = 13794623) B13794623
theorem B2725223 : Blo 1815609 2725223 := bstep (se 1 (by rfl) ⟨2043917, by rfl⟩ : syracuseStep 2725223 = 4087835) B4087835
theorem B20968895 : Blo 1815609 20968895 := bstep (se 1 (by rfl) ⟨15726671, by rfl⟩ : syracuseStep 20968895 = 31453343) B31453343
theorem B2299519 : Blo 1815609 2299519 := bstep (se 1 (by rfl) ⟨1724639, by rfl⟩ : syracuseStep 2299519 = 3449279) B3449279
theorem B3447289 : Blo 1815609 3447289 := bstep (se 2 (by rfl) ⟨1292733, by rfl⟩ : syracuseStep 3447289 = 2585467) B2585467
theorem B4596385 : Blo 1815609 4596385 := bstep (se 2 (by rfl) ⟨1723644, by rfl⟩ : syracuseStep 4596385 = 3447289) B3447289
theorem B125781751 : Blo 1815609 125781751 := bstep (se 1 (by rfl) ⟨94336313, by rfl⟩ : syracuseStep 125781751 = 188672627) B188672627
theorem B3066025 : Blo 1815609 3066025 := bstep (se 2 (by rfl) ⟨1149759, by rfl⟩ : syracuseStep 3066025 = 2299519) B2299519
theorem B13093487 : Blo 1815609 13093487 := bstep (se 1 (by rfl) ⟨9820115, by rfl⟩ : syracuseStep 13093487 = 19640231) B19640231
theorem B6130943 : Blo 1815609 6130943 := bstep (se 1 (by rfl) ⟨4598207, by rfl⟩ : syracuseStep 6130943 = 9196415) B9196415
theorem B13979263 : Blo 1815609 13979263 := bstep (se 1 (by rfl) ⟨10484447, by rfl⟩ : syracuseStep 13979263 = 20968895) B20968895
theorem B13266983 : Blo 1815609 13266983 := bstep (se 1 (by rfl) ⟨9950237, by rfl⟩ : syracuseStep 13266983 = 19900475) B19900475
theorem B1815791 : Blo 1815609 1815791 := bstep (se 1 (by rfl) ⟨1361843, by rfl⟩ : syracuseStep 1815791 = 2723687) B2723687
theorem B1816815 : Blo 1815609 1816815 := bstep (se 1 (by rfl) ⟨1362611, by rfl⟩ : syracuseStep 1816815 = 2725223) B2725223
theorem B4086377 : Blo 1815609 4086377 := bstep (se 2 (by rfl) ⟨1532391, by rfl⟩ : syracuseStep 4086377 = 3064783) B3064783
theorem B27966161 : Blo 1815609 27966161 := bstep (se 2 (by rfl) ⟨10487310, by rfl⟩ : syracuseStep 27966161 = 20974621) B20974621
theorem B26189567 : Blo 1815609 26189567 := bstep (se 1 (by rfl) ⟨19642175, by rfl⟩ : syracuseStep 26189567 = 39284351) B39284351
theorem B4088033 : Blo 1815609 4088033 := bstep (se 2 (by rfl) ⟨1533012, by rfl⟩ : syracuseStep 4088033 = 3066025) B3066025
theorem B6128513 : Blo 1815609 6128513 := bstep (se 2 (by rfl) ⟨2298192, by rfl⟩ : syracuseStep 6128513 = 4596385) B4596385
theorem B18639017 : Blo 1815609 18639017 := bstep (se 2 (by rfl) ⟨6989631, by rfl⟩ : syracuseStep 18639017 = 13979263) B13979263
theorem B167709001 : Blo 1815609 167709001 := bstep (se 2 (by rfl) ⟨62890875, by rfl⟩ : syracuseStep 167709001 = 125781751) B125781751
theorem B17459711 : Blo 1815609 17459711 := bstep (se 1 (by rfl) ⟨13094783, by rfl⟩ : syracuseStep 17459711 = 26189567) B26189567
theorem B2724251 : Blo 1815609 2724251 := bstep (se 1 (by rfl) ⟨2043188, by rfl⟩ : syracuseStep 2724251 = 4086377) B4086377
theorem B8728991 : Blo 1815609 8728991 := bstep (se 1 (by rfl) ⟨6546743, by rfl⟩ : syracuseStep 8728991 = 13093487) B13093487
theorem B8844655 : Blo 1815609 8844655 := bstep (se 1 (by rfl) ⟨6633491, by rfl⟩ : syracuseStep 8844655 = 13266983) B13266983
theorem B18644107 : Blo 1815609 18644107 := bstep (se 1 (by rfl) ⟨13983080, by rfl⟩ : syracuseStep 18644107 = 27966161) B27966161
theorem B4087295 : Blo 1815609 4087295 := bstep (se 1 (by rfl) ⟨3065471, by rfl⟩ : syracuseStep 4087295 = 6130943) B6130943
theorem B5819327 : Blo 1815609 5819327 := bstep (se 1 (by rfl) ⟨4364495, by rfl⟩ : syracuseStep 5819327 = 8728991) B8728991
theorem B223612001 : Blo 1815609 223612001 := bstep (se 2 (by rfl) ⟨83854500, by rfl⟩ : syracuseStep 223612001 = 167709001) B167709001
theorem B24858809 : Blo 1815609 24858809 := bstep (se 2 (by rfl) ⟨9322053, by rfl⟩ : syracuseStep 24858809 = 18644107) B18644107
theorem B11792873 : Blo 1815609 11792873 := bstep (se 2 (by rfl) ⟨4422327, by rfl⟩ : syracuseStep 11792873 = 8844655) B8844655
theorem B2724863 : Blo 1815609 2724863 := bstep (se 1 (by rfl) ⟨2043647, by rfl⟩ : syracuseStep 2724863 = 4087295) B4087295
theorem B2725355 : Blo 1815609 2725355 := bstep (se 1 (by rfl) ⟨2044016, by rfl⟩ : syracuseStep 2725355 = 4088033) B4088033
theorem B1816167 : Blo 1815609 1816167 := bstep (se 1 (by rfl) ⟨1362125, by rfl⟩ : syracuseStep 1816167 = 2724251) B2724251
theorem B4085675 : Blo 1815609 4085675 := bstep (se 1 (by rfl) ⟨3064256, by rfl⟩ : syracuseStep 4085675 = 6128513) B6128513
theorem B12426011 : Blo 1815609 12426011 := bstep (se 1 (by rfl) ⟨9319508, by rfl⟩ : syracuseStep 12426011 = 18639017) B18639017
theorem B11639807 : Blo 1815609 11639807 := bstep (se 1 (by rfl) ⟨8729855, by rfl⟩ : syracuseStep 11639807 = 17459711) B17459711
theorem B16572539 : Blo 1815609 16572539 := bstep (se 1 (by rfl) ⟨12429404, by rfl⟩ : syracuseStep 16572539 = 24858809) B24858809
theorem B8284007 : Blo 1815609 8284007 := bstep (se 1 (by rfl) ⟨6213005, by rfl⟩ : syracuseStep 8284007 = 12426011) B12426011
theorem B7759871 : Blo 1815609 7759871 := bstep (se 1 (by rfl) ⟨5819903, by rfl⟩ : syracuseStep 7759871 = 11639807) B11639807
theorem B2723783 : Blo 1815609 2723783 := bstep (se 1 (by rfl) ⟨2042837, by rfl⟩ : syracuseStep 2723783 = 4085675) B4085675
theorem B3879551 : Blo 1815609 3879551 := bstep (se 1 (by rfl) ⟨2909663, by rfl⟩ : syracuseStep 3879551 = 5819327) B5819327
theorem B149074667 : Blo 1815609 149074667 := bstep (se 1 (by rfl) ⟨111806000, by rfl⟩ : syracuseStep 149074667 = 223612001) B223612001
theorem B7861915 : Blo 1815609 7861915 := bstep (se 1 (by rfl) ⟨5896436, by rfl⟩ : syracuseStep 7861915 = 11792873) B11792873
theorem B1816575 : Blo 1815609 1816575 := bstep (se 1 (by rfl) ⟨1362431, by rfl⟩ : syracuseStep 1816575 = 2724863) B2724863
theorem B1816903 : Blo 1815609 1816903 := bstep (se 1 (by rfl) ⟨1362677, by rfl⟩ : syracuseStep 1816903 = 2725355) B2725355
theorem B5522671 : Blo 1815609 5522671 := bstep (se 1 (by rfl) ⟨4142003, by rfl⟩ : syracuseStep 5522671 = 8284007) B8284007
theorem B5173247 : Blo 1815609 5173247 := bstep (se 1 (by rfl) ⟨3879935, by rfl⟩ : syracuseStep 5173247 = 7759871) B7759871
theorem B10482553 : Blo 1815609 10482553 := bstep (se 2 (by rfl) ⟨3930957, by rfl⟩ : syracuseStep 10482553 = 7861915) B7861915
theorem B1815855 : Blo 1815609 1815855 := bstep (se 1 (by rfl) ⟨1361891, by rfl⟩ : syracuseStep 1815855 = 2723783) B2723783
theorem B11048359 : Blo 1815609 11048359 := bstep (se 1 (by rfl) ⟨8286269, by rfl⟩ : syracuseStep 11048359 = 16572539) B16572539
theorem B2586367 : Blo 1815609 2586367 := bstep (se 1 (by rfl) ⟨1939775, by rfl⟩ : syracuseStep 2586367 = 3879551) B3879551
theorem B99383111 : Blo 1815609 99383111 := bstep (se 1 (by rfl) ⟨74537333, by rfl⟩ : syracuseStep 99383111 = 149074667) B149074667
theorem B14731145 : Blo 1815609 14731145 := bstep (se 2 (by rfl) ⟨5524179, by rfl⟩ : syracuseStep 14731145 = 11048359) B11048359
theorem B55906949 : Blo 1815609 55906949 := bstep (se 4 (by rfl) ⟨5241276, by rfl⟩ : syracuseStep 55906949 = 10482553) B10482553
theorem B66255407 : Blo 1815609 66255407 := bstep (se 1 (by rfl) ⟨49691555, by rfl⟩ : syracuseStep 66255407 = 99383111) B99383111
theorem B7363561 : Blo 1815609 7363561 := bstep (se 2 (by rfl) ⟨2761335, by rfl⟩ : syracuseStep 7363561 = 5522671) B5522671
theorem B3448489 : Blo 1815609 3448489 := bstep (se 2 (by rfl) ⟨1293183, by rfl⟩ : syracuseStep 3448489 = 2586367) B2586367
theorem B3448831 : Blo 1815609 3448831 := bstep (se 1 (by rfl) ⟨2586623, by rfl⟩ : syracuseStep 3448831 = 5173247) B5173247
theorem B4597985 : Blo 1815609 4597985 := bstep (se 2 (by rfl) ⟨1724244, by rfl⟩ : syracuseStep 4597985 = 3448489) B3448489
theorem B4598441 : Blo 1815609 4598441 := bstep (se 2 (by rfl) ⟨1724415, by rfl⟩ : syracuseStep 4598441 = 3448831) B3448831
theorem B9818081 : Blo 1815609 9818081 := bstep (se 2 (by rfl) ⟨3681780, by rfl⟩ : syracuseStep 9818081 = 7363561) B7363561
theorem B37271299 : Blo 1815609 37271299 := bstep (se 1 (by rfl) ⟨27953474, by rfl⟩ : syracuseStep 37271299 = 55906949) B55906949
theorem B9820763 : Blo 1815609 9820763 := bstep (se 1 (by rfl) ⟨7365572, by rfl⟩ : syracuseStep 9820763 = 14731145) B14731145
theorem B44170271 : Blo 1815609 44170271 := bstep (se 1 (by rfl) ⟨33127703, by rfl⟩ : syracuseStep 44170271 = 66255407) B66255407
theorem B3065323 : Blo 1815609 3065323 := bstep (se 1 (by rfl) ⟨2298992, by rfl⟩ : syracuseStep 3065323 = 4597985) B4597985
theorem B6547175 : Blo 1815609 6547175 := bstep (se 1 (by rfl) ⟨4910381, by rfl⟩ : syracuseStep 6547175 = 9820763) B9820763
theorem B3065627 : Blo 1815609 3065627 := bstep (se 1 (by rfl) ⟨2299220, by rfl⟩ : syracuseStep 3065627 = 4598441) B4598441
theorem B49695065 : Blo 1815609 49695065 := bstep (se 2 (by rfl) ⟨18635649, by rfl⟩ : syracuseStep 49695065 = 37271299) B37271299
theorem B29446847 : Blo 1815609 29446847 := bstep (se 1 (by rfl) ⟨22085135, by rfl⟩ : syracuseStep 29446847 = 44170271) B44170271
theorem B6545387 : Blo 1815609 6545387 := bstep (se 1 (by rfl) ⟨4909040, by rfl⟩ : syracuseStep 6545387 = 9818081) B9818081
theorem B33130043 : Blo 1815609 33130043 := bstep (se 1 (by rfl) ⟨24847532, by rfl⟩ : syracuseStep 33130043 = 49695065) B49695065
theorem B19631231 : Blo 1815609 19631231 := bstep (se 1 (by rfl) ⟨14723423, by rfl⟩ : syracuseStep 19631231 = 29446847) B29446847
theorem B2043751 : Blo 1815609 2043751 := bstep (se 1 (by rfl) ⟨1532813, by rfl⟩ : syracuseStep 2043751 = 3065627) B3065627
theorem B17454365 : Blo 1815609 17454365 := bstep (se 3 (by rfl) ⟨3272693, by rfl⟩ : syracuseStep 17454365 = 6545387) B6545387
theorem B4364783 : Blo 1815609 4364783 := bstep (se 1 (by rfl) ⟨3273587, by rfl⟩ : syracuseStep 4364783 = 6547175) B6547175
theorem B4087097 : Blo 1815609 4087097 := bstep (se 2 (by rfl) ⟨1532661, by rfl⟩ : syracuseStep 4087097 = 3065323) B3065323
theorem B22086695 : Blo 1815609 22086695 := bstep (se 1 (by rfl) ⟨16565021, by rfl⟩ : syracuseStep 22086695 = 33130043) B33130043
theorem B2909855 : Blo 1815609 2909855 := bstep (se 1 (by rfl) ⟨2182391, by rfl⟩ : syracuseStep 2909855 = 4364783) B4364783
theorem B11636243 : Blo 1815609 11636243 := bstep (se 1 (by rfl) ⟨8727182, by rfl⟩ : syracuseStep 11636243 = 17454365) B17454365
theorem B13087487 : Blo 1815609 13087487 := bstep (se 1 (by rfl) ⟨9815615, by rfl⟩ : syracuseStep 13087487 = 19631231) B19631231
theorem B2724731 : Blo 1815609 2724731 := bstep (se 1 (by rfl) ⟨2043548, by rfl⟩ : syracuseStep 2724731 = 4087097) B4087097
theorem B2725001 : Blo 1815609 2725001 := bstep (se 2 (by rfl) ⟨1021875, by rfl⟩ : syracuseStep 2725001 = 2043751) B2043751
theorem B8724991 : Blo 1815609 8724991 := bstep (se 1 (by rfl) ⟨6543743, by rfl⟩ : syracuseStep 8724991 = 13087487) B13087487
theorem B7759613 : Blo 1815609 7759613 := bstep (se 3 (by rfl) ⟨1454927, by rfl⟩ : syracuseStep 7759613 = 2909855) B2909855
theorem B14724463 : Blo 1815609 14724463 := bstep (se 1 (by rfl) ⟨11043347, by rfl⟩ : syracuseStep 14724463 = 22086695) B22086695
theorem B1816487 : Blo 1815609 1816487 := bstep (se 1 (by rfl) ⟨1362365, by rfl⟩ : syracuseStep 1816487 = 2724731) B2724731
theorem B1816667 : Blo 1815609 1816667 := bstep (se 1 (by rfl) ⟨1362500, by rfl⟩ : syracuseStep 1816667 = 2725001) B2725001
theorem B7757495 : Blo 1815609 7757495 := bstep (se 1 (by rfl) ⟨5818121, by rfl⟩ : syracuseStep 7757495 = 11636243) B11636243
theorem B11633321 : Blo 1815609 11633321 := bstep (se 2 (by rfl) ⟨4362495, by rfl⟩ : syracuseStep 11633321 = 8724991) B8724991
theorem B5171663 : Blo 1815609 5171663 := bstep (se 1 (by rfl) ⟨3878747, by rfl⟩ : syracuseStep 5171663 = 7757495) B7757495
theorem B5173075 : Blo 1815609 5173075 := bstep (se 1 (by rfl) ⟨3879806, by rfl⟩ : syracuseStep 5173075 = 7759613) B7759613
theorem B19632617 : Blo 1815609 19632617 := bstep (se 2 (by rfl) ⟨7362231, by rfl⟩ : syracuseStep 19632617 = 14724463) B14724463
theorem B13088411 : Blo 1815609 13088411 := bstep (se 1 (by rfl) ⟨9816308, by rfl⟩ : syracuseStep 13088411 = 19632617) B19632617
theorem B7755547 : Blo 1815609 7755547 := bstep (se 1 (by rfl) ⟨5816660, by rfl⟩ : syracuseStep 7755547 = 11633321) B11633321
theorem B3447775 : Blo 1815609 3447775 := bstep (se 1 (by rfl) ⟨2585831, by rfl⟩ : syracuseStep 3447775 = 5171663) B5171663
theorem B6897433 : Blo 1815609 6897433 := bstep (se 2 (by rfl) ⟨2586537, by rfl⟩ : syracuseStep 6897433 = 5173075) B5173075
theorem B8725607 : Blo 1815609 8725607 := bstep (se 1 (by rfl) ⟨6544205, by rfl⟩ : syracuseStep 8725607 = 13088411) B13088411
theorem B4597033 : Blo 1815609 4597033 := bstep (se 2 (by rfl) ⟨1723887, by rfl⟩ : syracuseStep 4597033 = 3447775) B3447775
theorem B10340729 : Blo 1815609 10340729 := bstep (se 2 (by rfl) ⟨3877773, by rfl⟩ : syracuseStep 10340729 = 7755547) B7755547
theorem B9196577 : Blo 1815609 9196577 := bstep (se 2 (by rfl) ⟨3448716, by rfl⟩ : syracuseStep 9196577 = 6897433) B6897433
theorem B5817071 : Blo 1815609 5817071 := bstep (se 1 (by rfl) ⟨4362803, by rfl⟩ : syracuseStep 5817071 = 8725607) B8725607
theorem B6129377 : Blo 1815609 6129377 := bstep (se 2 (by rfl) ⟨2298516, by rfl⟩ : syracuseStep 6129377 = 4597033) B4597033
theorem B6131051 : Blo 1815609 6131051 := bstep (se 1 (by rfl) ⟨4598288, by rfl⟩ : syracuseStep 6131051 = 9196577) B9196577
theorem B6893819 : Blo 1815609 6893819 := bstep (se 1 (by rfl) ⟨5170364, by rfl⟩ : syracuseStep 6893819 = 10340729) B10340729
theorem B4595879 : Blo 1815609 4595879 := bstep (se 1 (by rfl) ⟨3446909, by rfl⟩ : syracuseStep 4595879 = 6893819) B6893819
theorem B3878047 : Blo 1815609 3878047 := bstep (se 1 (by rfl) ⟨2908535, by rfl⟩ : syracuseStep 3878047 = 5817071) B5817071
theorem B4086251 : Blo 1815609 4086251 := bstep (se 1 (by rfl) ⟨3064688, by rfl⟩ : syracuseStep 4086251 = 6129377) B6129377
theorem B4087367 : Blo 1815609 4087367 := bstep (se 1 (by rfl) ⟨3065525, by rfl⟩ : syracuseStep 4087367 = 6131051) B6131051
theorem B3063919 : Blo 1815609 3063919 := bstep (se 1 (by rfl) ⟨2297939, by rfl⟩ : syracuseStep 3063919 = 4595879) B4595879
theorem B5170729 : Blo 1815609 5170729 := bstep (se 2 (by rfl) ⟨1939023, by rfl⟩ : syracuseStep 5170729 = 3878047) B3878047
theorem B2724167 : Blo 1815609 2724167 := bstep (se 1 (by rfl) ⟨2043125, by rfl⟩ : syracuseStep 2724167 = 4086251) B4086251
theorem B2724911 : Blo 1815609 2724911 := bstep (se 1 (by rfl) ⟨2043683, by rfl⟩ : syracuseStep 2724911 = 4087367) B4087367
theorem B6894305 : Blo 1815609 6894305 := bstep (se 2 (by rfl) ⟨2585364, by rfl⟩ : syracuseStep 6894305 = 5170729) B5170729
theorem B4085225 : Blo 1815609 4085225 := bstep (se 2 (by rfl) ⟨1531959, by rfl⟩ : syracuseStep 4085225 = 3063919) B3063919
theorem B1816111 : Blo 1815609 1816111 := bstep (se 1 (by rfl) ⟨1362083, by rfl⟩ : syracuseStep 1816111 = 2724167) B2724167
theorem B1816607 : Blo 1815609 1816607 := bstep (se 1 (by rfl) ⟨1362455, by rfl⟩ : syracuseStep 1816607 = 2724911) B2724911
theorem B4596203 : Blo 1815609 4596203 := bstep (se 1 (by rfl) ⟨3447152, by rfl⟩ : syracuseStep 4596203 = 6894305) B6894305
theorem B2723483 : Blo 1815609 2723483 := bstep (se 1 (by rfl) ⟨2042612, by rfl⟩ : syracuseStep 2723483 = 4085225) B4085225
theorem B3064135 : Blo 1815609 3064135 := bstep (se 1 (by rfl) ⟨2298101, by rfl⟩ : syracuseStep 3064135 = 4596203) B4596203
theorem B1815655 : Blo 1815609 1815655 := bstep (se 1 (by rfl) ⟨1361741, by rfl⟩ : syracuseStep 1815655 = 2723483) B2723483
theorem B4085513 : Blo 1815609 4085513 := bstep (se 2 (by rfl) ⟨1532067, by rfl⟩ : syracuseStep 4085513 = 3064135) B3064135
theorem B2723675 : Blo 1815609 2723675 := bstep (se 1 (by rfl) ⟨2042756, by rfl⟩ : syracuseStep 2723675 = 4085513) B4085513
theorem B1815783 : Blo 1815609 1815783 := bstep (se 1 (by rfl) ⟨1361837, by rfl⟩ : syracuseStep 1815783 = 2723675) B2723675

theorem C0 (j : ℕ) (h1 : 453902 ≤ j) (h2 : j ≤ 454401) : Blo 1815609 (4 * j + 3) := by
  interval_cases j
  · exact B1815611
  · exact B1815615
  · exact B1815619
  · exact B1815623
  · exact B1815627
  · exact B1815631
  · exact B1815635
  · exact B1815639
  · exact B1815643
  · exact B1815647
  · exact B1815651
  · exact B1815655
  · exact B1815659
  · exact B1815663
  · exact B1815667
  · exact B1815671
  · exact B1815675
  · exact B1815679
  · exact B1815683
  · exact B1815687
  · exact B1815691
  · exact B1815695
  · exact B1815699
  · exact B1815703
  · exact B1815707
  · exact B1815711
  · exact B1815715
  · exact B1815719
  · exact B1815723
  · exact B1815727
  · exact B1815731
  · exact B1815735
  · exact B1815739
  · exact B1815743
  · exact B1815747
  · exact B1815751
  · exact B1815755
  · exact B1815759
  · exact B1815763
  · exact B1815767
  · exact B1815771
  · exact B1815775
  · exact B1815779
  · exact B1815783
  · exact B1815787
  · exact B1815791
  · exact B1815795
  · exact B1815799
  · exact B1815803
  · exact B1815807
  · exact B1815811
  · exact B1815815
  · exact B1815819
  · exact B1815823
  · exact B1815827
  · exact B1815831
  · exact B1815835
  · exact B1815839
  · exact B1815843
  · exact B1815847
  · exact B1815851
  · exact B1815855
  · exact B1815859
  · exact B1815863
  · exact B1815867
  · exact B1815871
  · exact B1815875
  · exact B1815879
  · exact B1815883
  · exact B1815887
  · exact B1815891
  · exact B1815895
  · exact B1815899
  · exact B1815903
  · exact B1815907
  · exact B1815911
  · exact B1815915
  · exact B1815919
  · exact B1815923
  · exact B1815927
  · exact B1815931
  · exact B1815935
  · exact B1815939
  · exact B1815943
  · exact B1815947
  · exact B1815951
  · exact B1815955
  · exact B1815959
  · exact B1815963
  · exact B1815967
  · exact B1815971
  · exact B1815975
  · exact B1815979
  · exact B1815983
  · exact B1815987
  · exact B1815991
  · exact B1815995
  · exact B1815999
  · exact B1816003
  · exact B1816007
  · exact B1816011
  · exact B1816015
  · exact B1816019
  · exact B1816023
  · exact B1816027
  · exact B1816031
  · exact B1816035
  · exact B1816039
  · exact B1816043
  · exact B1816047
  · exact B1816051
  · exact B1816055
  · exact B1816059
  · exact B1816063
  · exact B1816067
  · exact B1816071
  · exact B1816075
  · exact B1816079
  · exact B1816083
  · exact B1816087
  · exact B1816091
  · exact B1816095
  · exact B1816099
  · exact B1816103
  · exact B1816107
  · exact B1816111
  · exact B1816115
  · exact B1816119
  · exact B1816123
  · exact B1816127
  · exact B1816131
  · exact B1816135
  · exact B1816139
  · exact B1816143
  · exact B1816147
  · exact B1816151
  · exact B1816155
  · exact B1816159
  · exact B1816163
  · exact B1816167
  · exact B1816171
  · exact B1816175
  · exact B1816179
  · exact B1816183
  · exact B1816187
  · exact B1816191
  · exact B1816195
  · exact B1816199
  · exact B1816203
  · exact B1816207
  · exact B1816211
  · exact B1816215
  · exact B1816219
  · exact B1816223
  · exact B1816227
  · exact B1816231
  · exact B1816235
  · exact B1816239
  · exact B1816243
  · exact B1816247
  · exact B1816251
  · exact B1816255
  · exact B1816259
  · exact B1816263
  · exact B1816267
  · exact B1816271
  · exact B1816275
  · exact B1816279
  · exact B1816283
  · exact B1816287
  · exact B1816291
  · exact B1816295
  · exact B1816299
  · exact B1816303
  · exact B1816307
  · exact B1816311
  · exact B1816315
  · exact B1816319
  · exact B1816323
  · exact B1816327
  · exact B1816331
  · exact B1816335
  · exact B1816339
  · exact B1816343
  · exact B1816347
  · exact B1816351
  · exact B1816355
  · exact B1816359
  · exact B1816363
  · exact B1816367
  · exact B1816371
  · exact B1816375
  · exact B1816379
  · exact B1816383
  · exact B1816387
  · exact B1816391
  · exact B1816395
  · exact B1816399
  · exact B1816403
  · exact B1816407
  · exact B1816411
  · exact B1816415
  · exact B1816419
  · exact B1816423
  · exact B1816427
  · exact B1816431
  · exact B1816435
  · exact B1816439
  · exact B1816443
  · exact B1816447
  · exact B1816451
  · exact B1816455
  · exact B1816459
  · exact B1816463
  · exact B1816467
  · exact B1816471
  · exact B1816475
  · exact B1816479
  · exact B1816483
  · exact B1816487
  · exact B1816491
  · exact B1816495
  · exact B1816499
  · exact B1816503
  · exact B1816507
  · exact B1816511
  · exact B1816515
  · exact B1816519
  · exact B1816523
  · exact B1816527
  · exact B1816531
  · exact B1816535
  · exact B1816539
  · exact B1816543
  · exact B1816547
  · exact B1816551
  · exact B1816555
  · exact B1816559
  · exact B1816563
  · exact B1816567
  · exact B1816571
  · exact B1816575
  · exact B1816579
  · exact B1816583
  · exact B1816587
  · exact B1816591
  · exact B1816595
  · exact B1816599
  · exact B1816603
  · exact B1816607
  · exact B1816611
  · exact B1816615
  · exact B1816619
  · exact B1816623
  · exact B1816627
  · exact B1816631
  · exact B1816635
  · exact B1816639
  · exact B1816643
  · exact B1816647
  · exact B1816651
  · exact B1816655
  · exact B1816659
  · exact B1816663
  · exact B1816667
  · exact B1816671
  · exact B1816675
  · exact B1816679
  · exact B1816683
  · exact B1816687
  · exact B1816691
  · exact B1816695
  · exact B1816699
  · exact B1816703
  · exact B1816707
  · exact B1816711
  · exact B1816715
  · exact B1816719
  · exact B1816723
  · exact B1816727
  · exact B1816731
  · exact B1816735
  · exact B1816739
  · exact B1816743
  · exact B1816747
  · exact B1816751
  · exact B1816755
  · exact B1816759
  · exact B1816763
  · exact B1816767
  · exact B1816771
  · exact B1816775
  · exact B1816779
  · exact B1816783
  · exact B1816787
  · exact B1816791
  · exact B1816795
  · exact B1816799
  · exact B1816803
  · exact B1816807
  · exact B1816811
  · exact B1816815
  · exact B1816819
  · exact B1816823
  · exact B1816827
  · exact B1816831
  · exact B1816835
  · exact B1816839
  · exact B1816843
  · exact B1816847
  · exact B1816851
  · exact B1816855
  · exact B1816859
  · exact B1816863
  · exact B1816867
  · exact B1816871
  · exact B1816875
  · exact B1816879
  · exact B1816883
  · exact B1816887
  · exact B1816891
  · exact B1816895
  · exact B1816899
  · exact B1816903
  · exact B1816907
  · exact B1816911
  · exact B1816915
  · exact B1816919
  · exact B1816923
  · exact B1816927
  · exact B1816931
  · exact B1816935
  · exact B1816939
  · exact B1816943
  · exact B1816947
  · exact B1816951
  · exact B1816955
  · exact B1816959
  · exact B1816963
  · exact B1816967
  · exact B1816971
  · exact B1816975
  · exact B1816979
  · exact B1816983
  · exact B1816987
  · exact B1816991
  · exact B1816995
  · exact B1816999
  · exact B1817003
  · exact B1817007
  · exact B1817011
  · exact B1817015
  · exact B1817019
  · exact B1817023
  · exact B1817027
  · exact B1817031
  · exact B1817035
  · exact B1817039
  · exact B1817043
  · exact B1817047
  · exact B1817051
  · exact B1817055
  · exact B1817059
  · exact B1817063
  · exact B1817067
  · exact B1817071
  · exact B1817075
  · exact B1817079
  · exact B1817083
  · exact B1817087
  · exact B1817091
  · exact B1817095
  · exact B1817099
  · exact B1817103
  · exact B1817107
  · exact B1817111
  · exact B1817115
  · exact B1817119
  · exact B1817123
  · exact B1817127
  · exact B1817131
  · exact B1817135
  · exact B1817139
  · exact B1817143
  · exact B1817147
  · exact B1817151
  · exact B1817155
  · exact B1817159
  · exact B1817163
  · exact B1817167
  · exact B1817171
  · exact B1817175
  · exact B1817179
  · exact B1817183
  · exact B1817187
  · exact B1817191
  · exact B1817195
  · exact B1817199
  · exact B1817203
  · exact B1817207
  · exact B1817211
  · exact B1817215
  · exact B1817219
  · exact B1817223
  · exact B1817227
  · exact B1817231
  · exact B1817235
  · exact B1817239
  · exact B1817243
  · exact B1817247
  · exact B1817251
  · exact B1817255
  · exact B1817259
  · exact B1817263
  · exact B1817267
  · exact B1817271
  · exact B1817275
  · exact B1817279
  · exact B1817283
  · exact B1817287
  · exact B1817291
  · exact B1817295
  · exact B1817299
  · exact B1817303
  · exact B1817307
  · exact B1817311
  · exact B1817315
  · exact B1817319
  · exact B1817323
  · exact B1817327
  · exact B1817331
  · exact B1817335
  · exact B1817339
  · exact B1817343
  · exact B1817347
  · exact B1817351
  · exact B1817355
  · exact B1817359
  · exact B1817363
  · exact B1817367
  · exact B1817371
  · exact B1817375
  · exact B1817379
  · exact B1817383
  · exact B1817387
  · exact B1817391
  · exact B1817395
  · exact B1817399
  · exact B1817403
  · exact B1817407
  · exact B1817411
  · exact B1817415
  · exact B1817419
  · exact B1817423
  · exact B1817427
  · exact B1817431
  · exact B1817435
  · exact B1817439
  · exact B1817443
  · exact B1817447
  · exact B1817451
  · exact B1817455
  · exact B1817459
  · exact B1817463
  · exact B1817467
  · exact B1817471
  · exact B1817475
  · exact B1817479
  · exact B1817483
  · exact B1817487
  · exact B1817491
  · exact B1817495
  · exact B1817499
  · exact B1817503
  · exact B1817507
  · exact B1817511
  · exact B1817515
  · exact B1817519
  · exact B1817523
  · exact B1817527
  · exact B1817531
  · exact B1817535
  · exact B1817539
  · exact B1817543
  · exact B1817547
  · exact B1817551
  · exact B1817555
  · exact B1817559
  · exact B1817563
  · exact B1817567
  · exact B1817571
  · exact B1817575
  · exact B1817579
  · exact B1817583
  · exact B1817587
  · exact B1817591
  · exact B1817595
  · exact B1817599
  · exact B1817603
  · exact B1817607

theorem solution (m : ℕ) (hlo : 1815609 ≤ m) (hhi : m ≤ 1817609) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 453902 ≤ j := by omega
    have hj2 : j ≤ 454401 := by omega
    have hb : Blo 1815609 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
