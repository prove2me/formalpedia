-- Prove2me | solution 1 for syracuse_descends_range_1435537_1437537
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:42:19.623786+00:00
-- url     : https://prove2.me/submissions/5328eb51-4643-44b6-908c-8d88d822cc07

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


theorem B2154509 : Blo 1435537 2154509 := bbase (se 3 (by rfl) ⟨403970, by rfl⟩ : syracuseStep 2154509 = 807941) (by norm_num)
theorem B4849685 : Blo 1435537 4849685 := bbase (se 6 (by rfl) ⟨113664, by rfl⟩ : syracuseStep 4849685 = 227329) (by norm_num)
theorem B2154533 : Blo 1435537 2154533 := bbase (se 4 (by rfl) ⟨201987, by rfl⟩ : syracuseStep 2154533 = 403975) (by norm_num)
theorem B2154557 : Blo 1435537 2154557 := bbase (se 3 (by rfl) ⟨403979, by rfl⟩ : syracuseStep 2154557 = 807959) (by norm_num)
theorem B3637325 : Blo 1435537 3637325 := bbase (se 3 (by rfl) ⟨681998, by rfl⟩ : syracuseStep 3637325 = 1363997) (by norm_num)
theorem B2154581 : Blo 1435537 2154581 := bbase (se 8 (by rfl) ⟨12624, by rfl⟩ : syracuseStep 2154581 = 25249) (by norm_num)
theorem B5455957 : Blo 1435537 5455957 := bbase (se 8 (by rfl) ⟨31968, by rfl⟩ : syracuseStep 5455957 = 63937) (by norm_num)
theorem B2424917 : Blo 1435537 2424917 := bbase (se 8 (by rfl) ⟨14208, by rfl⟩ : syracuseStep 2424917 = 28417) (by norm_num)
theorem B1818713 : Blo 1435537 1818713 := bbase (se 2 (by rfl) ⟨682017, by rfl⟩ : syracuseStep 1818713 = 1364035) (by norm_num)
theorem B2588773 : Blo 1435537 2588773 := bbase (se 4 (by rfl) ⟨242697, by rfl⟩ : syracuseStep 2588773 = 485395) (by norm_num)
theorem B2154605 : Blo 1435537 2154605 := bbase (se 3 (by rfl) ⟨403988, by rfl⟩ : syracuseStep 2154605 = 807977) (by norm_num)
theorem B2154629 : Blo 1435537 2154629 := bbase (se 4 (by rfl) ⟨201996, by rfl⟩ : syracuseStep 2154629 = 403993) (by norm_num)
theorem B1818769 : Blo 1435537 1818769 := bbase (se 2 (by rfl) ⟨682038, by rfl⟩ : syracuseStep 1818769 = 1364077) (by norm_num)
theorem B2154653 : Blo 1435537 2154653 := bbase (se 3 (by rfl) ⟨403997, by rfl⟩ : syracuseStep 2154653 = 807995) (by norm_num)
theorem B2728093 : Blo 1435537 2728093 := bbase (se 3 (by rfl) ⟨511517, by rfl⟩ : syracuseStep 2728093 = 1023035) (by norm_num)
theorem B2154677 : Blo 1435537 2154677 := bbase (se 5 (by rfl) ⟨101000, by rfl⟩ : syracuseStep 2154677 = 202001) (by norm_num)
theorem B1638581 : Blo 1435537 1638581 := bbase (se 5 (by rfl) ⟨76808, by rfl⟩ : syracuseStep 1638581 = 153617) (by norm_num)
theorem B3031229 : Blo 1435537 3031229 := bbase (se 3 (by rfl) ⟨568355, by rfl⟩ : syracuseStep 3031229 = 1136711) (by norm_num)
theorem B2154701 : Blo 1435537 2154701 := bbase (se 3 (by rfl) ⟨404006, by rfl⟩ : syracuseStep 2154701 = 808013) (by norm_num)
theorem B6553813 : Blo 1435537 6553813 := bbase (se 7 (by rfl) ⟨76802, by rfl⟩ : syracuseStep 6553813 = 153605) (by norm_num)
theorem B2425045 : Blo 1435537 2425045 := bbase (se 7 (by rfl) ⟨28418, by rfl⟩ : syracuseStep 2425045 = 56837) (by norm_num)
theorem B2154725 : Blo 1435537 2154725 := bbase (se 4 (by rfl) ⟨202005, by rfl⟩ : syracuseStep 2154725 = 404011) (by norm_num)
theorem B1818865 : Blo 1435537 1818865 := bbase (se 2 (by rfl) ⟨682074, by rfl⟩ : syracuseStep 1818865 = 1364149) (by norm_num)
theorem B2154749 : Blo 1435537 2154749 := bbase (se 3 (by rfl) ⟨404015, by rfl⟩ : syracuseStep 2154749 = 808031) (by norm_num)
theorem B2154773 : Blo 1435537 2154773 := bbase (se 6 (by rfl) ⟨50502, by rfl⟩ : syracuseStep 2154773 = 101005) (by norm_num)
theorem B2154797 : Blo 1435537 2154797 := bbase (se 3 (by rfl) ⟨404024, by rfl⟩ : syracuseStep 2154797 = 808049) (by norm_num)
theorem B2728237 : Blo 1435537 2728237 := bbase (se 3 (by rfl) ⟨511544, by rfl⟩ : syracuseStep 2728237 = 1023089) (by norm_num)
theorem B2425133 : Blo 1435537 2425133 := bbase (se 3 (by rfl) ⟨454712, by rfl⟩ : syracuseStep 2425133 = 909425) (by norm_num)
theorem B2588981 : Blo 1435537 2588981 := bbase (se 5 (by rfl) ⟨121358, by rfl⟩ : syracuseStep 2588981 = 242717) (by norm_num)
theorem B2154821 : Blo 1435537 2154821 := bbase (se 4 (by rfl) ⟨202014, by rfl⟩ : syracuseStep 2154821 = 404029) (by norm_num)
theorem B6906197 : Blo 1435537 6906197 := bbase (se 10 (by rfl) ⟨10116, by rfl⟩ : syracuseStep 6906197 = 20233) (by norm_num)
theorem B2154845 : Blo 1435537 2154845 := bbase (se 3 (by rfl) ⟨404033, by rfl⟩ : syracuseStep 2154845 = 808067) (by norm_num)
theorem B2154869 : Blo 1435537 2154869 := bbase (se 5 (by rfl) ⟨101009, by rfl⟩ : syracuseStep 2154869 = 202019) (by norm_num)
theorem B5456261 : Blo 1435537 5456261 := bbase (se 4 (by rfl) ⟨511524, by rfl⟩ : syracuseStep 5456261 = 1023049) (by norm_num)
theorem B2154893 : Blo 1435537 2154893 := bbase (se 3 (by rfl) ⟨404042, by rfl⟩ : syracuseStep 2154893 = 808085) (by norm_num)
theorem B1819037 : Blo 1435537 1819037 := bbase (se 3 (by rfl) ⟨341069, by rfl⟩ : syracuseStep 1819037 = 682139) (by norm_num)
theorem B2154917 : Blo 1435537 2154917 := bbase (se 4 (by rfl) ⟨202023, by rfl⟩ : syracuseStep 2154917 = 404047) (by norm_num)
theorem B3637669 : Blo 1435537 3637669 := bbase (se 4 (by rfl) ⟨341031, by rfl⟩ : syracuseStep 3637669 = 682063) (by norm_num)
theorem B2425261 : Blo 1435537 2425261 := bbase (se 3 (by rfl) ⟨454736, by rfl⟩ : syracuseStep 2425261 = 909473) (by norm_num)
theorem B7274933 : Blo 1435537 7274933 := bbase (se 5 (by rfl) ⟨341012, by rfl⟩ : syracuseStep 7274933 = 682025) (by norm_num)
theorem B2154941 : Blo 1435537 2154941 := bbase (se 3 (by rfl) ⟨404051, by rfl⟩ : syracuseStep 2154941 = 808103) (by norm_num)
theorem B4850117 : Blo 1435537 4850117 := bbase (se 4 (by rfl) ⟨454698, by rfl⟩ : syracuseStep 4850117 = 909397) (by norm_num)
theorem B2728397 : Blo 1435537 2728397 := bbase (se 3 (by rfl) ⟨511574, by rfl⟩ : syracuseStep 2728397 = 1023149) (by norm_num)
theorem B2154965 : Blo 1435537 2154965 := bbase (se 7 (by rfl) ⟨25253, by rfl⟩ : syracuseStep 2154965 = 50507) (by norm_num)
theorem B1819093 : Blo 1435537 1819093 := bbase (se 7 (by rfl) ⟨21317, by rfl⟩ : syracuseStep 1819093 = 42635) (by norm_num)
theorem B3498461 : Blo 1435537 3498461 := bbase (se 3 (by rfl) ⟨655961, by rfl⟩ : syracuseStep 3498461 = 1311923) (by norm_num)
theorem B2154989 : Blo 1435537 2154989 := bbase (se 3 (by rfl) ⟨404060, by rfl⟩ : syracuseStep 2154989 = 808121) (by norm_num)
theorem B5825029 : Blo 1435537 5825029 := bbase (se 4 (by rfl) ⟨546096, by rfl⟩ : syracuseStep 5825029 = 1092193) (by norm_num)
theorem B2155013 : Blo 1435537 2155013 := bbase (se 4 (by rfl) ⟨202032, by rfl⟩ : syracuseStep 2155013 = 404065) (by norm_num)
theorem B2425349 : Blo 1435537 2425349 := bbase (se 4 (by rfl) ⟨227376, by rfl⟩ : syracuseStep 2425349 = 454753) (by norm_num)
theorem B3637781 : Blo 1435537 3637781 := bbase (se 6 (by rfl) ⟨85260, by rfl⟩ : syracuseStep 3637781 = 170521) (by norm_num)
theorem B2155037 : Blo 1435537 2155037 := bbase (se 3 (by rfl) ⟨404069, by rfl⟩ : syracuseStep 2155037 = 808139) (by norm_num)
theorem B2155061 : Blo 1435537 2155061 := bbase (se 5 (by rfl) ⟨101018, by rfl⟩ : syracuseStep 2155061 = 202037) (by norm_num)
theorem B1819189 : Blo 1435537 1819189 := bbase (se 5 (by rfl) ⟨85274, by rfl⟩ : syracuseStep 1819189 = 170549) (by norm_num)
theorem B2155085 : Blo 1435537 2155085 := bbase (se 3 (by rfl) ⟨404078, by rfl⟩ : syracuseStep 2155085 = 808157) (by norm_num)
theorem B2728541 : Blo 1435537 2728541 := bbase (se 3 (by rfl) ⟨511601, by rfl⟩ : syracuseStep 2728541 = 1023203) (by norm_num)
theorem B2155109 : Blo 1435537 2155109 := bbase (se 4 (by rfl) ⟨202041, by rfl⟩ : syracuseStep 2155109 = 404083) (by norm_num)
theorem B2155133 : Blo 1435537 2155133 := bbase (se 3 (by rfl) ⟨404087, by rfl⟩ : syracuseStep 2155133 = 808175) (by norm_num)
theorem B2425477 : Blo 1435537 2425477 := bbase (se 4 (by rfl) ⟨227388, by rfl⟩ : syracuseStep 2425477 = 454777) (by norm_num)
theorem B2155157 : Blo 1435537 2155157 := bbase (se 6 (by rfl) ⟨50511, by rfl⟩ : syracuseStep 2155157 = 101023) (by norm_num)
theorem B2589349 : Blo 1435537 2589349 := bbase (se 4 (by rfl) ⟨242751, by rfl⟩ : syracuseStep 2589349 = 485503) (by norm_num)
theorem B2155181 : Blo 1435537 2155181 := bbase (se 3 (by rfl) ⟨404096, by rfl⟩ : syracuseStep 2155181 = 808193) (by norm_num)
theorem B2155205 : Blo 1435537 2155205 := bbase (se 4 (by rfl) ⟨202050, by rfl⟩ : syracuseStep 2155205 = 404101) (by norm_num)
theorem B12264149 : Blo 1435537 12264149 := bbase (se 7 (by rfl) ⟨143720, by rfl⟩ : syracuseStep 12264149 = 287441) (by norm_num)
theorem B3637973 : Blo 1435537 3637973 := bbase (se 7 (by rfl) ⟨42632, by rfl⟩ : syracuseStep 3637973 = 85265) (by norm_num)
theorem B2155229 : Blo 1435537 2155229 := bbase (se 3 (by rfl) ⟨404105, by rfl⟩ : syracuseStep 2155229 = 808211) (by norm_num)
theorem B2425565 : Blo 1435537 2425565 := bbase (se 3 (by rfl) ⟨454793, by rfl⟩ : syracuseStep 2425565 = 909587) (by norm_num)
theorem B1819361 : Blo 1435537 1819361 := bbase (se 2 (by rfl) ⟨682260, by rfl⟩ : syracuseStep 1819361 = 1364521) (by norm_num)
theorem B8176373 : Blo 1435537 8176373 := bbase (se 5 (by rfl) ⟨383267, by rfl⟩ : syracuseStep 8176373 = 766535) (by norm_num)
theorem B2155253 : Blo 1435537 2155253 := bbase (se 5 (by rfl) ⟨101027, by rfl⟩ : syracuseStep 2155253 = 202055) (by norm_num)
theorem B2155277 : Blo 1435537 2155277 := bbase (se 3 (by rfl) ⟨404114, by rfl⟩ : syracuseStep 2155277 = 808229) (by norm_num)
theorem B3449621 : Blo 1435537 3449621 := bbase (se 6 (by rfl) ⟨80850, by rfl⟩ : syracuseStep 3449621 = 161701) (by norm_num)
theorem B2155301 : Blo 1435537 2155301 := bbase (se 4 (by rfl) ⟨202059, by rfl⟩ : syracuseStep 2155301 = 404119) (by norm_num)
theorem B2155325 : Blo 1435537 2155325 := bbase (se 3 (by rfl) ⟨404123, by rfl⟩ : syracuseStep 2155325 = 808247) (by norm_num)
theorem B2155349 : Blo 1435537 2155349 := bbase (se 9 (by rfl) ⟨6314, by rfl⟩ : syracuseStep 2155349 = 12629) (by norm_num)
theorem B2425693 : Blo 1435537 2425693 := bbase (se 3 (by rfl) ⟨454817, by rfl⟩ : syracuseStep 2425693 = 909635) (by norm_num)
theorem B4088677 : Blo 1435537 4088677 := bbase (se 4 (by rfl) ⟨383313, by rfl⟩ : syracuseStep 4088677 = 766627) (by norm_num)
theorem B2155373 : Blo 1435537 2155373 := bbase (se 3 (by rfl) ⟨404132, by rfl⟩ : syracuseStep 2155373 = 808265) (by norm_num)
theorem B4850549 : Blo 1435537 4850549 := bbase (se 5 (by rfl) ⟨227369, by rfl⟩ : syracuseStep 4850549 = 454739) (by norm_num)
theorem B2728829 : Blo 1435537 2728829 := bbase (se 3 (by rfl) ⟨511655, by rfl⟩ : syracuseStep 2728829 = 1023311) (by norm_num)
theorem B2155397 : Blo 1435537 2155397 := bbase (se 4 (by rfl) ⟨202068, by rfl⟩ : syracuseStep 2155397 = 404137) (by norm_num)
theorem B2155421 : Blo 1435537 2155421 := bbase (se 3 (by rfl) ⟨404141, by rfl⟩ : syracuseStep 2155421 = 808283) (by norm_num)
theorem B2155445 : Blo 1435537 2155445 := bbase (se 5 (by rfl) ⟨101036, by rfl⟩ : syracuseStep 2155445 = 202073) (by norm_num)
theorem B2425781 : Blo 1435537 2425781 := bbase (se 5 (by rfl) ⟨113708, by rfl⟩ : syracuseStep 2425781 = 227417) (by norm_num)
theorem B2155469 : Blo 1435537 2155469 := bbase (se 3 (by rfl) ⟨404150, by rfl⟩ : syracuseStep 2155469 = 808301) (by norm_num)
theorem B3548125 : Blo 1435537 3548125 := bbase (se 3 (by rfl) ⟨665273, by rfl⟩ : syracuseStep 3548125 = 1330547) (by norm_num)
theorem B2155493 : Blo 1435537 2155493 := bbase (se 4 (by rfl) ⟨202077, by rfl⟩ : syracuseStep 2155493 = 404155) (by norm_num)
theorem B2155517 : Blo 1435537 2155517 := bbase (se 3 (by rfl) ⟨404159, by rfl⟩ : syracuseStep 2155517 = 808319) (by norm_num)
theorem B2155541 : Blo 1435537 2155541 := bbase (se 6 (by rfl) ⟨50520, by rfl⟩ : syracuseStep 2155541 = 101041) (by norm_num)
theorem B2728981 : Blo 1435537 2728981 := bbase (se 6 (by rfl) ⟨63960, by rfl⟩ : syracuseStep 2728981 = 127921) (by norm_num)
theorem B2155565 : Blo 1435537 2155565 := bbase (se 3 (by rfl) ⟨404168, by rfl⟩ : syracuseStep 2155565 = 808337) (by norm_num)
theorem B3638317 : Blo 1435537 3638317 := bbase (se 3 (by rfl) ⟨682184, by rfl⟩ : syracuseStep 3638317 = 1364369) (by norm_num)
theorem B2155589 : Blo 1435537 2155589 := bbase (se 4 (by rfl) ⟨202086, by rfl⟩ : syracuseStep 2155589 = 404173) (by norm_num)
theorem B2155613 : Blo 1435537 2155613 := bbase (se 3 (by rfl) ⟨404177, by rfl⟩ : syracuseStep 2155613 = 808355) (by norm_num)
theorem B2155637 : Blo 1435537 2155637 := bbase (se 5 (by rfl) ⟨101045, by rfl⟩ : syracuseStep 2155637 = 202091) (by norm_num)
theorem B1533053 : Blo 1435537 1533053 := bbase (se 3 (by rfl) ⟨287447, by rfl⟩ : syracuseStep 1533053 = 574895) (by norm_num)
theorem B2155661 : Blo 1435537 2155661 := bbase (se 3 (by rfl) ⟨404186, by rfl⟩ : syracuseStep 2155661 = 808373) (by norm_num)
theorem B3450005 : Blo 1435537 3450005 := bbase (se 6 (by rfl) ⟨80859, by rfl⟩ : syracuseStep 3450005 = 161719) (by norm_num)
theorem B3638429 : Blo 1435537 3638429 := bbase (se 3 (by rfl) ⟨682205, by rfl⟩ : syracuseStep 3638429 = 1364411) (by norm_num)
theorem B1615009 : Blo 1435537 1615009 := bbase (se 2 (by rfl) ⟨605628, by rfl⟩ : syracuseStep 1615009 = 1211257) (by norm_num)
theorem B2155685 : Blo 1435537 2155685 := bbase (se 4 (by rfl) ⟨202095, by rfl⟩ : syracuseStep 2155685 = 404191) (by norm_num)
theorem B2155709 : Blo 1435537 2155709 := bbase (se 3 (by rfl) ⟨404195, by rfl⟩ : syracuseStep 2155709 = 808391) (by norm_num)
theorem B1615045 : Blo 1435537 1615045 := bbase (se 4 (by rfl) ⟨151410, by rfl⟩ : syracuseStep 1615045 = 302821) (by norm_num)
theorem B3450053 : Blo 1435537 3450053 := bbase (se 4 (by rfl) ⟨323442, by rfl⟩ : syracuseStep 3450053 = 646885) (by norm_num)
theorem B3450061 : Blo 1435537 3450061 := bbase (se 3 (by rfl) ⟨646886, by rfl⟩ : syracuseStep 3450061 = 1293773) (by norm_num)
theorem B2155733 : Blo 1435537 2155733 := bbase (se 7 (by rfl) ⟨25262, by rfl⟩ : syracuseStep 2155733 = 50525) (by norm_num)
theorem B1615081 : Blo 1435537 1615081 := bbase (se 2 (by rfl) ⟨605655, by rfl⟩ : syracuseStep 1615081 = 1211311) (by norm_num)
theorem B2155757 : Blo 1435537 2155757 := bbase (se 3 (by rfl) ⟨404204, by rfl⟩ : syracuseStep 2155757 = 808409) (by norm_num)
theorem B2073853 : Blo 1435537 2073853 := bbase (se 3 (by rfl) ⟨388847, by rfl⟩ : syracuseStep 2073853 = 777695) (by norm_num)
theorem B2155781 : Blo 1435537 2155781 := bbase (se 4 (by rfl) ⟨202104, by rfl⟩ : syracuseStep 2155781 = 404209) (by norm_num)
theorem B1615117 : Blo 1435537 1615117 := bbase (se 3 (by rfl) ⟨302834, by rfl⟩ : syracuseStep 1615117 = 605669) (by norm_num)
theorem B2155805 : Blo 1435537 2155805 := bbase (se 3 (by rfl) ⟨404213, by rfl⟩ : syracuseStep 2155805 = 808427) (by norm_num)
theorem B4850981 : Blo 1435537 4850981 := bbase (se 4 (by rfl) ⟨454779, by rfl⟩ : syracuseStep 4850981 = 909559) (by norm_num)
theorem B1615153 : Blo 1435537 1615153 := bbase (se 2 (by rfl) ⟨605682, by rfl⟩ : syracuseStep 1615153 = 1211365) (by norm_num)
theorem B2155829 : Blo 1435537 2155829 := bbase (se 5 (by rfl) ⟨101054, by rfl⟩ : syracuseStep 2155829 = 202109) (by norm_num)
theorem B3278141 : Blo 1435537 3278141 := bbase (se 3 (by rfl) ⟨614651, by rfl⟩ : syracuseStep 3278141 = 1229303) (by norm_num)
theorem B2155853 : Blo 1435537 2155853 := bbase (se 3 (by rfl) ⟨404222, by rfl⟩ : syracuseStep 2155853 = 808445) (by norm_num)
theorem B1942861 : Blo 1435537 1942861 := bbase (se 3 (by rfl) ⟨364286, by rfl⟩ : syracuseStep 1942861 = 728573) (by norm_num)
theorem B1615189 : Blo 1435537 1615189 := bbase (se 12 (by rfl) ⟨591, by rfl⟩ : syracuseStep 1615189 = 1183) (by norm_num)
theorem B251790677 : Blo 1435537 251790677 := bbase (se 12 (by rfl) ⟨92208, by rfl⟩ : syracuseStep 251790677 = 184417) (by norm_num)
theorem B3638621 : Blo 1435537 3638621 := bbase (se 3 (by rfl) ⟨682241, by rfl⟩ : syracuseStep 3638621 = 1364483) (by norm_num)
theorem B2155877 : Blo 1435537 2155877 := bbase (se 4 (by rfl) ⟨202113, by rfl⟩ : syracuseStep 2155877 = 404227) (by norm_num)
theorem B1615225 : Blo 1435537 1615225 := bbase (se 2 (by rfl) ⟨605709, by rfl⟩ : syracuseStep 1615225 = 1211419) (by norm_num)
theorem B2155901 : Blo 1435537 2155901 := bbase (se 3 (by rfl) ⟨404231, by rfl⟩ : syracuseStep 2155901 = 808463) (by norm_num)
theorem B2155925 : Blo 1435537 2155925 := bbase (se 6 (by rfl) ⟨50529, by rfl⟩ : syracuseStep 2155925 = 101059) (by norm_num)
theorem B1615261 : Blo 1435537 1615261 := bbase (se 3 (by rfl) ⟨302861, by rfl⟩ : syracuseStep 1615261 = 605723) (by norm_num)
theorem B2155949 : Blo 1435537 2155949 := bbase (se 3 (by rfl) ⟨404240, by rfl⟩ : syracuseStep 2155949 = 808481) (by norm_num)
theorem B2590141 : Blo 1435537 2590141 := bbase (se 3 (by rfl) ⟨485651, by rfl⟩ : syracuseStep 2590141 = 971303) (by norm_num)
theorem B1615297 : Blo 1435537 1615297 := bbase (se 2 (by rfl) ⟨605736, by rfl⟩ : syracuseStep 1615297 = 1211473) (by norm_num)
theorem B2155973 : Blo 1435537 2155973 := bbase (se 4 (by rfl) ⟨202122, by rfl⟩ : syracuseStep 2155973 = 404245) (by norm_num)
theorem B2590157 : Blo 1435537 2590157 := bbase (se 3 (by rfl) ⟨485654, by rfl⟩ : syracuseStep 2590157 = 971309) (by norm_num)
theorem B2155997 : Blo 1435537 2155997 := bbase (se 3 (by rfl) ⟨404249, by rfl⟩ : syracuseStep 2155997 = 808499) (by norm_num)
theorem B1615333 : Blo 1435537 1615333 := bbase (se 4 (by rfl) ⟨151437, by rfl⟩ : syracuseStep 1615333 = 302875) (by norm_num)
theorem B2156021 : Blo 1435537 2156021 := bbase (se 5 (by rfl) ⟨101063, by rfl⟩ : syracuseStep 2156021 = 202127) (by norm_num)
theorem B1615369 : Blo 1435537 1615369 := bbase (se 2 (by rfl) ⟨605763, by rfl⟩ : syracuseStep 1615369 = 1211527) (by norm_num)
theorem B2156045 : Blo 1435537 2156045 := bbase (se 3 (by rfl) ⟨404258, by rfl⟩ : syracuseStep 2156045 = 808517) (by norm_num)
theorem B2156069 : Blo 1435537 2156069 := bbase (se 4 (by rfl) ⟨202131, by rfl⟩ : syracuseStep 2156069 = 404263) (by norm_num)
theorem B1615405 : Blo 1435537 1615405 := bbase (se 3 (by rfl) ⟨302888, by rfl⟩ : syracuseStep 1615405 = 605777) (by norm_num)
theorem B1533497 : Blo 1435537 1533497 := bbase (se 2 (by rfl) ⟨575061, by rfl⟩ : syracuseStep 1533497 = 1150123) (by norm_num)
theorem B2156093 : Blo 1435537 2156093 := bbase (se 3 (by rfl) ⟨404267, by rfl⟩ : syracuseStep 2156093 = 808535) (by norm_num)
theorem B1615441 : Blo 1435537 1615441 := bbase (se 2 (by rfl) ⟨605790, by rfl⟩ : syracuseStep 1615441 = 1211581) (by norm_num)
theorem B2156117 : Blo 1435537 2156117 := bbase (se 8 (by rfl) ⟨12633, by rfl⟩ : syracuseStep 2156117 = 25267) (by norm_num)
theorem B2156141 : Blo 1435537 2156141 := bbase (se 3 (by rfl) ⟨404276, by rfl⟩ : syracuseStep 2156141 = 808553) (by norm_num)
theorem B1615477 : Blo 1435537 1615477 := bbase (se 5 (by rfl) ⟨75725, by rfl⟩ : syracuseStep 1615477 = 151451) (by norm_num)
theorem B2156165 : Blo 1435537 2156165 := bbase (se 4 (by rfl) ⟨202140, by rfl⟩ : syracuseStep 2156165 = 404281) (by norm_num)
theorem B7767701 : Blo 1435537 7767701 := bbase (se 6 (by rfl) ⟨182055, by rfl⟩ : syracuseStep 7767701 = 364111) (by norm_num)
theorem B1615513 : Blo 1435537 1615513 := bbase (se 2 (by rfl) ⟨605817, by rfl⟩ : syracuseStep 1615513 = 1211635) (by norm_num)
theorem B2156189 : Blo 1435537 2156189 := bbase (se 3 (by rfl) ⟨404285, by rfl⟩ : syracuseStep 2156189 = 808571) (by norm_num)
theorem B2590373 : Blo 1435537 2590373 := bbase (se 4 (by rfl) ⟨242847, by rfl⟩ : syracuseStep 2590373 = 485695) (by norm_num)
theorem B2156213 : Blo 1435537 2156213 := bbase (se 5 (by rfl) ⟨101072, by rfl⟩ : syracuseStep 2156213 = 202145) (by norm_num)
theorem B1615549 : Blo 1435537 1615549 := bbase (se 3 (by rfl) ⟨302915, by rfl⟩ : syracuseStep 1615549 = 605831) (by norm_num)
theorem B7276229 : Blo 1435537 7276229 := bbase (se 4 (by rfl) ⟨682146, by rfl⟩ : syracuseStep 7276229 = 1364293) (by norm_num)
theorem B2156237 : Blo 1435537 2156237 := bbase (se 3 (by rfl) ⟨404294, by rfl⟩ : syracuseStep 2156237 = 808589) (by norm_num)
theorem B4851413 : Blo 1435537 4851413 := bbase (se 7 (by rfl) ⟨56852, by rfl⟩ : syracuseStep 4851413 = 113705) (by norm_num)
theorem B1615585 : Blo 1435537 1615585 := bbase (se 2 (by rfl) ⟨605844, by rfl⟩ : syracuseStep 1615585 = 1211689) (by norm_num)
theorem B2156261 : Blo 1435537 2156261 := bbase (se 4 (by rfl) ⟨202149, by rfl⟩ : syracuseStep 2156261 = 404299) (by norm_num)
theorem B2156285 : Blo 1435537 2156285 := bbase (se 3 (by rfl) ⟨404303, by rfl⟩ : syracuseStep 2156285 = 808607) (by norm_num)
theorem B1615621 : Blo 1435537 1615621 := bbase (se 4 (by rfl) ⟨151464, by rfl⟩ : syracuseStep 1615621 = 302929) (by norm_num)
theorem B1615657 : Blo 1435537 1615657 := bbase (se 2 (by rfl) ⟨605871, by rfl⟩ : syracuseStep 1615657 = 1211743) (by norm_num)
theorem B1533745 : Blo 1435537 1533745 := bbase (se 2 (by rfl) ⟨575154, by rfl⟩ : syracuseStep 1533745 = 1150309) (by norm_num)
theorem B1615693 : Blo 1435537 1615693 := bbase (se 3 (by rfl) ⟨302942, by rfl⟩ : syracuseStep 1615693 = 605885) (by norm_num)
theorem B1615729 : Blo 1435537 1615729 := bbase (se 2 (by rfl) ⟨605898, by rfl⟩ : syracuseStep 1615729 = 1211797) (by norm_num)
theorem B2074501 : Blo 1435537 2074501 := bbase (se 4 (by rfl) ⟨194484, by rfl⟩ : syracuseStep 2074501 = 388969) (by norm_num)
theorem B8177557 : Blo 1435537 8177557 := bbase (se 6 (by rfl) ⟨191661, by rfl⟩ : syracuseStep 8177557 = 383323) (by norm_num)
theorem B1615765 : Blo 1435537 1615765 := bbase (se 6 (by rfl) ⟨37869, by rfl⟩ : syracuseStep 1615765 = 75739) (by norm_num)
theorem B2762669 : Blo 1435537 2762669 := bbase (se 3 (by rfl) ⟨518000, by rfl⟩ : syracuseStep 2762669 = 1036001) (by norm_num)
theorem B4089781 : Blo 1435537 4089781 := bbase (se 5 (by rfl) ⟨191708, by rfl⟩ : syracuseStep 4089781 = 383417) (by norm_num)
theorem B1615801 : Blo 1435537 1615801 := bbase (se 2 (by rfl) ⟨605925, by rfl⟩ : syracuseStep 1615801 = 1211851) (by norm_num)
theorem B1615837 : Blo 1435537 1615837 := bbase (se 3 (by rfl) ⟨302969, by rfl⟩ : syracuseStep 1615837 = 605939) (by norm_num)
theorem B6899701 : Blo 1435537 6899701 := bbase (se 5 (by rfl) ⟨323423, by rfl⟩ : syracuseStep 6899701 = 646847) (by norm_num)
theorem B6998005 : Blo 1435537 6998005 := bbase (se 5 (by rfl) ⟨328031, by rfl⟩ : syracuseStep 6998005 = 656063) (by norm_num)
theorem B1615873 : Blo 1435537 1615873 := bbase (se 2 (by rfl) ⟨605952, by rfl⟩ : syracuseStep 1615873 = 1211905) (by norm_num)
theorem B1615909 : Blo 1435537 1615909 := bbase (se 4 (by rfl) ⟨151491, by rfl⟩ : syracuseStep 1615909 = 302983) (by norm_num)
theorem B1615945 : Blo 1435537 1615945 := bbase (se 2 (by rfl) ⟨605979, by rfl⟩ : syracuseStep 1615945 = 1211959) (by norm_num)
theorem B7268453 : Blo 1435537 7268453 := bbase (se 4 (by rfl) ⟨681417, by rfl⟩ : syracuseStep 7268453 = 1362835) (by norm_num)
theorem B1615981 : Blo 1435537 1615981 := bbase (se 3 (by rfl) ⟨302996, by rfl⟩ : syracuseStep 1615981 = 605993) (by norm_num)
theorem B1616017 : Blo 1435537 1616017 := bbase (se 2 (by rfl) ⟨606006, by rfl⟩ : syracuseStep 1616017 = 1212013) (by norm_num)
theorem B3451061 : Blo 1435537 3451061 := bbase (se 5 (by rfl) ⟨161768, by rfl⟩ : syracuseStep 3451061 = 323537) (by norm_num)
theorem B1616053 : Blo 1435537 1616053 := bbase (se 5 (by rfl) ⟨75752, by rfl⟩ : syracuseStep 1616053 = 151505) (by norm_num)
theorem B1616089 : Blo 1435537 1616089 := bbase (se 2 (by rfl) ⟨606033, by rfl⟩ : syracuseStep 1616089 = 1212067) (by norm_num)
theorem B1534177 : Blo 1435537 1534177 := bbase (se 2 (by rfl) ⟨575316, by rfl⟩ : syracuseStep 1534177 = 1150633) (by norm_num)
theorem B1616125 : Blo 1435537 1616125 := bbase (se 3 (by rfl) ⟨303023, by rfl⟩ : syracuseStep 1616125 = 606047) (by norm_num)
theorem B3229973 : Blo 1435537 3229973 := bbase (se 6 (by rfl) ⟨75702, by rfl⟩ : syracuseStep 3229973 = 151405) (by norm_num)
theorem B1616161 : Blo 1435537 1616161 := bbase (se 2 (by rfl) ⟨606060, by rfl⟩ : syracuseStep 1616161 = 1212121) (by norm_num)
theorem B1534249 : Blo 1435537 1534249 := bbase (se 2 (by rfl) ⟨575343, by rfl⟩ : syracuseStep 1534249 = 1150687) (by norm_num)
theorem B10914101 : Blo 1435537 10914101 := bbase (se 5 (by rfl) ⟨511598, by rfl⟩ : syracuseStep 10914101 = 1023197) (by norm_num)
theorem B1616197 : Blo 1435537 1616197 := bbase (se 4 (by rfl) ⟨151518, by rfl⟩ : syracuseStep 1616197 = 303037) (by norm_num)
theorem B3230045 : Blo 1435537 3230045 := bbase (se 3 (by rfl) ⟨605633, by rfl⟩ : syracuseStep 3230045 = 1211267) (by norm_num)
theorem B1616233 : Blo 1435537 1616233 := bbase (se 2 (by rfl) ⟨606087, by rfl⟩ : syracuseStep 1616233 = 1212175) (by norm_num)
theorem B3451253 : Blo 1435537 3451253 := bbase (se 5 (by rfl) ⟨161777, by rfl⟩ : syracuseStep 3451253 = 323555) (by norm_num)
theorem B1616269 : Blo 1435537 1616269 := bbase (se 3 (by rfl) ⟨303050, by rfl⟩ : syracuseStep 1616269 = 606101) (by norm_num)
theorem B1575329 : Blo 1435537 1575329 := bbase (se 2 (by rfl) ⟨590748, by rfl⟩ : syracuseStep 1575329 = 1181497) (by norm_num)
theorem B3230117 : Blo 1435537 3230117 := bbase (se 4 (by rfl) ⟨302823, by rfl⟩ : syracuseStep 3230117 = 605647) (by norm_num)
theorem B3066277 : Blo 1435537 3066277 := bbase (se 4 (by rfl) ⟨287463, by rfl⟩ : syracuseStep 3066277 = 574927) (by norm_num)
theorem B1616305 : Blo 1435537 1616305 := bbase (se 2 (by rfl) ⟨606114, by rfl⟩ : syracuseStep 1616305 = 1212229) (by norm_num)
theorem B1616341 : Blo 1435537 1616341 := bbase (se 7 (by rfl) ⟨18941, by rfl⟩ : syracuseStep 1616341 = 37883) (by norm_num)
theorem B3230189 : Blo 1435537 3230189 := bbase (se 3 (by rfl) ⟨605660, by rfl⟩ : syracuseStep 3230189 = 1211321) (by norm_num)
theorem B3500525 : Blo 1435537 3500525 := bbase (se 3 (by rfl) ⟨656348, by rfl⟩ : syracuseStep 3500525 = 1312697) (by norm_num)
theorem B1616377 : Blo 1435537 1616377 := bbase (se 2 (by rfl) ⟨606141, by rfl⟩ : syracuseStep 1616377 = 1212283) (by norm_num)
theorem B1616413 : Blo 1435537 1616413 := bbase (se 3 (by rfl) ⟨303077, by rfl⟩ : syracuseStep 1616413 = 606155) (by norm_num)
theorem B3230261 : Blo 1435537 3230261 := bbase (se 5 (by rfl) ⟨151418, by rfl⟩ : syracuseStep 3230261 = 302837) (by norm_num)
theorem B1616449 : Blo 1435537 1616449 := bbase (se 2 (by rfl) ⟨606168, by rfl⟩ : syracuseStep 1616449 = 1212337) (by norm_num)
theorem B1616485 : Blo 1435537 1616485 := bbase (se 4 (by rfl) ⟨151545, by rfl⟩ : syracuseStep 1616485 = 303091) (by norm_num)
theorem B3230333 : Blo 1435537 3230333 := bbase (se 3 (by rfl) ⟨605687, by rfl⟩ : syracuseStep 3230333 = 1211375) (by norm_num)
theorem B1616521 : Blo 1435537 1616521 := bbase (se 2 (by rfl) ⟨606195, by rfl⟩ : syracuseStep 1616521 = 1212391) (by norm_num)
theorem B1534621 : Blo 1435537 1534621 := bbase (se 3 (by rfl) ⟨287741, by rfl⟩ : syracuseStep 1534621 = 575483) (by norm_num)
theorem B1616557 : Blo 1435537 1616557 := bbase (se 3 (by rfl) ⟨303104, by rfl⟩ : syracuseStep 1616557 = 606209) (by norm_num)
theorem B3230405 : Blo 1435537 3230405 := bbase (se 4 (by rfl) ⟨302850, by rfl⟩ : syracuseStep 3230405 = 605701) (by norm_num)
theorem B1616593 : Blo 1435537 1616593 := bbase (se 2 (by rfl) ⟨606222, by rfl⟩ : syracuseStep 1616593 = 1212445) (by norm_num)
theorem B10906325 : Blo 1435537 10906325 := bbase (se 7 (by rfl) ⟨127808, by rfl⟩ : syracuseStep 10906325 = 255617) (by norm_num)
theorem B5827301 : Blo 1435537 5827301 := bbase (se 4 (by rfl) ⟨546309, by rfl⟩ : syracuseStep 5827301 = 1092619) (by norm_num)
theorem B1616629 : Blo 1435537 1616629 := bbase (se 5 (by rfl) ⟨75779, by rfl⟩ : syracuseStep 1616629 = 151559) (by norm_num)
theorem B3230477 : Blo 1435537 3230477 := bbase (se 3 (by rfl) ⟨605714, by rfl⟩ : syracuseStep 3230477 = 1211429) (by norm_num)
theorem B13814549 : Blo 1435537 13814549 := bbase (se 6 (by rfl) ⟨323778, by rfl⟩ : syracuseStep 13814549 = 647557) (by norm_num)
theorem B1616665 : Blo 1435537 1616665 := bbase (se 2 (by rfl) ⟨606249, by rfl⟩ : syracuseStep 1616665 = 1212499) (by norm_num)
theorem B3066653 : Blo 1435537 3066653 := bbase (se 3 (by rfl) ⟨574997, by rfl⟩ : syracuseStep 3066653 = 1149995) (by norm_num)
theorem B1616701 : Blo 1435537 1616701 := bbase (se 3 (by rfl) ⟨303131, by rfl⟩ : syracuseStep 1616701 = 606263) (by norm_num)
theorem B3230549 : Blo 1435537 3230549 := bbase (se 9 (by rfl) ⟨9464, by rfl⟩ : syracuseStep 3230549 = 18929) (by norm_num)
theorem B1616737 : Blo 1435537 1616737 := bbase (se 2 (by rfl) ⟨606276, by rfl⟩ : syracuseStep 1616737 = 1212553) (by norm_num)
theorem B5450597 : Blo 1435537 5450597 := bbase (se 4 (by rfl) ⟨510993, by rfl⟩ : syracuseStep 5450597 = 1021987) (by norm_num)
theorem B1616773 : Blo 1435537 1616773 := bbase (se 4 (by rfl) ⟨151572, by rfl⟩ : syracuseStep 1616773 = 303145) (by norm_num)
theorem B6138773 : Blo 1435537 6138773 := bbase (se 6 (by rfl) ⟨143877, by rfl⟩ : syracuseStep 6138773 = 287755) (by norm_num)
theorem B3230621 : Blo 1435537 3230621 := bbase (se 3 (by rfl) ⟨605741, by rfl⟩ : syracuseStep 3230621 = 1211483) (by norm_num)
theorem B1616809 : Blo 1435537 1616809 := bbase (se 2 (by rfl) ⟨606303, by rfl⟩ : syracuseStep 1616809 = 1212607) (by norm_num)
theorem B3787709 : Blo 1435537 3787709 := bbase (se 3 (by rfl) ⟨710195, by rfl⟩ : syracuseStep 3787709 = 1420391) (by norm_num)
theorem B1616845 : Blo 1435537 1616845 := bbase (se 3 (by rfl) ⟨303158, by rfl⟩ : syracuseStep 1616845 = 606317) (by norm_num)
theorem B7277525 : Blo 1435537 7277525 := bbase (se 7 (by rfl) ⟨85283, by rfl⟩ : syracuseStep 7277525 = 170567) (by norm_num)
theorem B3230693 : Blo 1435537 3230693 := bbase (se 4 (by rfl) ⟨302877, by rfl⟩ : syracuseStep 3230693 = 605755) (by norm_num)
theorem B1616881 : Blo 1435537 1616881 := bbase (se 2 (by rfl) ⟨606330, by rfl⟩ : syracuseStep 1616881 = 1212661) (by norm_num)
theorem B1616917 : Blo 1435537 1616917 := bbase (se 6 (by rfl) ⟨37896, by rfl⟩ : syracuseStep 1616917 = 75793) (by norm_num)
theorem B1534997 : Blo 1435537 1534997 := bbase (se 6 (by rfl) ⟨35976, by rfl⟩ : syracuseStep 1534997 = 71953) (by norm_num)
theorem B4148261 : Blo 1435537 4148261 := bbase (se 4 (by rfl) ⟨388899, by rfl⟩ : syracuseStep 4148261 = 777799) (by norm_num)
theorem B3230765 : Blo 1435537 3230765 := bbase (se 3 (by rfl) ⟨605768, by rfl⟩ : syracuseStep 3230765 = 1211537) (by norm_num)
theorem B1616953 : Blo 1435537 1616953 := bbase (se 2 (by rfl) ⟨606357, by rfl⟩ : syracuseStep 1616953 = 1212715) (by norm_num)
theorem B4148309 : Blo 1435537 4148309 := bbase (se 8 (by rfl) ⟨24306, by rfl⟩ : syracuseStep 4148309 = 48613) (by norm_num)
theorem B1616989 : Blo 1435537 1616989 := bbase (se 3 (by rfl) ⟨303185, by rfl⟩ : syracuseStep 1616989 = 606371) (by norm_num)
theorem B1535069 : Blo 1435537 1535069 := bbase (se 3 (by rfl) ⟨287825, by rfl⟩ : syracuseStep 1535069 = 575651) (by norm_num)
theorem B6220901 : Blo 1435537 6220901 := bbase (se 4 (by rfl) ⟨583209, by rfl⟩ : syracuseStep 6220901 = 1166419) (by norm_num)
theorem B3230837 : Blo 1435537 3230837 := bbase (se 5 (by rfl) ⟨151445, by rfl⟩ : syracuseStep 3230837 = 302891) (by norm_num)
theorem B9202805 : Blo 1435537 9202805 := bbase (se 5 (by rfl) ⟨431381, by rfl⟩ : syracuseStep 9202805 = 862763) (by norm_num)
theorem B1617025 : Blo 1435537 1617025 := bbase (se 2 (by rfl) ⟨606384, by rfl⟩ : syracuseStep 1617025 = 1212769) (by norm_num)
theorem B5450885 : Blo 1435537 5450885 := bbase (se 4 (by rfl) ⟨511020, by rfl⟩ : syracuseStep 5450885 = 1022041) (by norm_num)
theorem B1617061 : Blo 1435537 1617061 := bbase (se 4 (by rfl) ⟨151599, by rfl⟩ : syracuseStep 1617061 = 303199) (by norm_num)
theorem B4369589 : Blo 1435537 4369589 := bbase (se 5 (by rfl) ⟨204824, by rfl⟩ : syracuseStep 4369589 = 409649) (by norm_num)
theorem B3230909 : Blo 1435537 3230909 := bbase (se 3 (by rfl) ⟨605795, by rfl⟩ : syracuseStep 3230909 = 1211591) (by norm_num)
theorem B4598981 : Blo 1435537 4598981 := bbase (se 4 (by rfl) ⟨431154, by rfl⟩ : syracuseStep 4598981 = 862309) (by norm_num)
theorem B1617097 : Blo 1435537 1617097 := bbase (se 2 (by rfl) ⟨606411, by rfl⟩ : syracuseStep 1617097 = 1212823) (by norm_num)
theorem B1617133 : Blo 1435537 1617133 := bbase (se 3 (by rfl) ⟨303212, by rfl⟩ : syracuseStep 1617133 = 606425) (by norm_num)
theorem B2911477 : Blo 1435537 2911477 := bbase (se 5 (by rfl) ⟨136475, by rfl⟩ : syracuseStep 2911477 = 272951) (by norm_num)
theorem B3230981 : Blo 1435537 3230981 := bbase (se 4 (by rfl) ⟨302904, by rfl⟩ : syracuseStep 3230981 = 605809) (by norm_num)
theorem B1617169 : Blo 1435537 1617169 := bbase (se 2 (by rfl) ⟨606438, by rfl⟩ : syracuseStep 1617169 = 1212877) (by norm_num)
theorem B2764061 : Blo 1435537 2764061 := bbase (se 3 (by rfl) ⟨518261, by rfl⟩ : syracuseStep 2764061 = 1036523) (by norm_num)
theorem B3108149 : Blo 1435537 3108149 := bbase (se 5 (by rfl) ⟨145694, by rfl⟩ : syracuseStep 3108149 = 291389) (by norm_num)
theorem B1617205 : Blo 1435537 1617205 := bbase (se 5 (by rfl) ⟨75806, by rfl⟩ : syracuseStep 1617205 = 151613) (by norm_num)
theorem B3231053 : Blo 1435537 3231053 := bbase (se 3 (by rfl) ⟨605822, by rfl⟩ : syracuseStep 3231053 = 1211645) (by norm_num)
theorem B7269749 : Blo 1435537 7269749 := bbase (se 5 (by rfl) ⟨340769, by rfl⟩ : syracuseStep 7269749 = 681539) (by norm_num)
theorem B3231125 : Blo 1435537 3231125 := bbase (se 6 (by rfl) ⟨75729, by rfl⟩ : syracuseStep 3231125 = 151459) (by norm_num)
theorem B4091285 : Blo 1435537 4091285 := bbase (se 6 (by rfl) ⟨95889, by rfl⟩ : syracuseStep 4091285 = 191779) (by norm_num)
theorem B7769557 : Blo 1435537 7769557 := bbase (se 7 (by rfl) ⟨91049, by rfl⟩ : syracuseStep 7769557 = 182099) (by norm_num)
theorem B3231197 : Blo 1435537 3231197 := bbase (se 3 (by rfl) ⟨605849, by rfl⟩ : syracuseStep 3231197 = 1211699) (by norm_num)
theorem B2215397 : Blo 1435537 2215397 := bbase (se 4 (by rfl) ⟨207693, by rfl⟩ : syracuseStep 2215397 = 415387) (by norm_num)
theorem B3231269 : Blo 1435537 3231269 := bbase (se 4 (by rfl) ⟨302931, by rfl⟩ : syracuseStep 3231269 = 605863) (by norm_num)
theorem B3231341 : Blo 1435537 3231341 := bbase (se 3 (by rfl) ⟨605876, by rfl⟩ : syracuseStep 3231341 = 1211753) (by norm_num)
theorem B12267125 : Blo 1435537 12267125 := bbase (se 5 (by rfl) ⟨575021, by rfl⟩ : syracuseStep 12267125 = 1150043) (by norm_num)
theorem B3231413 : Blo 1435537 3231413 := bbase (se 5 (by rfl) ⟨151472, by rfl⟩ : syracuseStep 3231413 = 302945) (by norm_num)
theorem B3231485 : Blo 1435537 3231485 := bbase (se 3 (by rfl) ⟨605903, by rfl⟩ : syracuseStep 3231485 = 1211807) (by norm_num)
theorem B4845365 : Blo 1435537 4845365 := bbase (se 5 (by rfl) ⟨227126, by rfl⟩ : syracuseStep 4845365 = 454253) (by norm_num)
theorem B3231557 : Blo 1435537 3231557 := bbase (se 4 (by rfl) ⟨302958, by rfl⟩ : syracuseStep 3231557 = 605917) (by norm_num)
theorem B8179541 : Blo 1435537 8179541 := bbase (se 9 (by rfl) ⟨23963, by rfl⟩ : syracuseStep 8179541 = 47927) (by norm_num)
theorem B3108701 : Blo 1435537 3108701 := bbase (se 3 (by rfl) ⟨582881, by rfl⟩ : syracuseStep 3108701 = 1165763) (by norm_num)
theorem B3231629 : Blo 1435537 3231629 := bbase (se 3 (by rfl) ⟨605930, by rfl⟩ : syracuseStep 3231629 = 1211861) (by norm_num)
theorem B3231701 : Blo 1435537 3231701 := bbase (se 7 (by rfl) ⟨37871, by rfl⟩ : syracuseStep 3231701 = 75743) (by norm_num)
theorem B3231773 : Blo 1435537 3231773 := bbase (se 3 (by rfl) ⟨605957, by rfl⟩ : syracuseStep 3231773 = 1211915) (by norm_num)
theorem B3231845 : Blo 1435537 3231845 := bbase (se 4 (by rfl) ⟨302985, by rfl⟩ : syracuseStep 3231845 = 605971) (by norm_num)
theorem B3231917 : Blo 1435537 3231917 := bbase (se 3 (by rfl) ⟨605984, by rfl⟩ : syracuseStep 3231917 = 1211969) (by norm_num)
theorem B4845797 : Blo 1435537 4845797 := bbase (se 4 (by rfl) ⟨454293, by rfl⟩ : syracuseStep 4845797 = 908587) (by norm_num)
theorem B3231989 : Blo 1435537 3231989 := bbase (se 5 (by rfl) ⟨151499, by rfl⟩ : syracuseStep 3231989 = 302999) (by norm_num)
theorem B3453205 : Blo 1435537 3453205 := bbase (se 6 (by rfl) ⟨80934, by rfl⟩ : syracuseStep 3453205 = 161869) (by norm_num)
theorem B5452069 : Blo 1435537 5452069 := bbase (se 4 (by rfl) ⟨511131, by rfl⟩ : syracuseStep 5452069 = 1022263) (by norm_num)
theorem B3232061 : Blo 1435537 3232061 := bbase (se 3 (by rfl) ⟨606011, by rfl⟩ : syracuseStep 3232061 = 1212023) (by norm_num)
theorem B9326933 : Blo 1435537 9326933 := bbase (se 10 (by rfl) ⟨13662, by rfl⟩ : syracuseStep 9326933 = 27325) (by norm_num)
theorem B3232133 : Blo 1435537 3232133 := bbase (se 4 (by rfl) ⟨303012, by rfl⟩ : syracuseStep 3232133 = 606025) (by norm_num)
theorem B3068293 : Blo 1435537 3068293 := bbase (se 4 (by rfl) ⟨287652, by rfl⟩ : syracuseStep 3068293 = 575305) (by norm_num)
theorem B3232205 : Blo 1435537 3232205 := bbase (se 3 (by rfl) ⟨606038, by rfl⟩ : syracuseStep 3232205 = 1212077) (by norm_num)
theorem B2765261 : Blo 1435537 2765261 := bbase (se 3 (by rfl) ⟨518486, by rfl⟩ : syracuseStep 2765261 = 1036973) (by norm_num)
theorem B7188965 : Blo 1435537 7188965 := bbase (se 4 (by rfl) ⟨673965, by rfl⟩ : syracuseStep 7188965 = 1347931) (by norm_num)
theorem B3232277 : Blo 1435537 3232277 := bbase (se 6 (by rfl) ⟨75756, by rfl⟩ : syracuseStep 3232277 = 151513) (by norm_num)
theorem B5452373 : Blo 1435537 5452373 := bbase (se 8 (by rfl) ⟨31947, by rfl⟩ : syracuseStep 5452373 = 63895) (by norm_num)
theorem B2183773 : Blo 1435537 2183773 := bbase (se 3 (by rfl) ⟨409457, by rfl⟩ : syracuseStep 2183773 = 818915) (by norm_num)
theorem B3232349 : Blo 1435537 3232349 := bbase (se 3 (by rfl) ⟨606065, by rfl⟩ : syracuseStep 3232349 = 1212131) (by norm_num)
theorem B3633781 : Blo 1435537 3633781 := bbase (se 5 (by rfl) ⟨170333, by rfl⟩ : syracuseStep 3633781 = 340667) (by norm_num)
theorem B2044549 : Blo 1435537 2044549 := bbase (se 4 (by rfl) ⟨191676, by rfl⟩ : syracuseStep 2044549 = 383353) (by norm_num)
theorem B7271045 : Blo 1435537 7271045 := bbase (se 4 (by rfl) ⟨681660, by rfl⟩ : syracuseStep 7271045 = 1363321) (by norm_num)
theorem B4846229 : Blo 1435537 4846229 := bbase (se 6 (by rfl) ⟨113583, by rfl⟩ : syracuseStep 4846229 = 227167) (by norm_num)
theorem B3232421 : Blo 1435537 3232421 := bbase (se 4 (by rfl) ⟨303039, by rfl⟩ : syracuseStep 3232421 = 606079) (by norm_num)
theorem B3633893 : Blo 1435537 3633893 := bbase (se 4 (by rfl) ⟨340677, by rfl⟩ : syracuseStep 3633893 = 681355) (by norm_num)
theorem B3232493 : Blo 1435537 3232493 := bbase (se 3 (by rfl) ⟨606092, by rfl⟩ : syracuseStep 3232493 = 1212185) (by norm_num)
theorem B6132469 : Blo 1435537 6132469 := bbase (se 5 (by rfl) ⟨287459, by rfl⟩ : syracuseStep 6132469 = 574919) (by norm_num)
theorem B6132485 : Blo 1435537 6132485 := bbase (se 4 (by rfl) ⟨574920, by rfl⟩ : syracuseStep 6132485 = 1149841) (by norm_num)
theorem B3232565 : Blo 1435537 3232565 := bbase (se 5 (by rfl) ⟨151526, by rfl⟩ : syracuseStep 3232565 = 303053) (by norm_num)
theorem B3232637 : Blo 1435537 3232637 := bbase (se 3 (by rfl) ⟨606119, by rfl⟩ : syracuseStep 3232637 = 1212239) (by norm_num)
theorem B4666261 : Blo 1435537 4666261 := bbase (se 6 (by rfl) ⟨109365, by rfl⟩ : syracuseStep 4666261 = 218731) (by norm_num)
theorem B3634085 : Blo 1435537 3634085 := bbase (se 4 (by rfl) ⟨340695, by rfl⟩ : syracuseStep 3634085 = 681391) (by norm_num)
theorem B3232709 : Blo 1435537 3232709 := bbase (se 4 (by rfl) ⟨303066, by rfl⟩ : syracuseStep 3232709 = 606133) (by norm_num)
theorem B4092869 : Blo 1435537 4092869 := bbase (se 4 (by rfl) ⟨383706, by rfl⟩ : syracuseStep 4092869 = 767413) (by norm_num)
theorem B3232781 : Blo 1435537 3232781 := bbase (se 3 (by rfl) ⟨606146, by rfl⟩ : syracuseStep 3232781 = 1212293) (by norm_num)
theorem B1725473 : Blo 1435537 1725473 := bbase (se 2 (by rfl) ⟨647052, by rfl⟩ : syracuseStep 1725473 = 1294105) (by norm_num)
theorem B5395493 : Blo 1435537 5395493 := bbase (se 4 (by rfl) ⟨505827, by rfl⟩ : syracuseStep 5395493 = 1011655) (by norm_num)
theorem B4846661 : Blo 1435537 4846661 := bbase (se 4 (by rfl) ⟨454374, by rfl⟩ : syracuseStep 4846661 = 908749) (by norm_num)
theorem B3232853 : Blo 1435537 3232853 := bbase (se 8 (by rfl) ⟨18942, by rfl⟩ : syracuseStep 3232853 = 37885) (by norm_num)
theorem B2593885 : Blo 1435537 2593885 := bbase (se 3 (by rfl) ⟨486353, by rfl⟩ : syracuseStep 2593885 = 972707) (by norm_num)
theorem B5821589 : Blo 1435537 5821589 := bbase (se 6 (by rfl) ⟨136443, by rfl⟩ : syracuseStep 5821589 = 272887) (by norm_num)
theorem B3232925 : Blo 1435537 3232925 := bbase (se 3 (by rfl) ⟨606173, by rfl⟩ : syracuseStep 3232925 = 1212347) (by norm_num)
theorem B1455329 : Blo 1435537 1455329 := bbase (se 2 (by rfl) ⟨545748, by rfl⟩ : syracuseStep 1455329 = 1091497) (by norm_num)
theorem B3232997 : Blo 1435537 3232997 := bbase (se 4 (by rfl) ⟨303093, by rfl⟩ : syracuseStep 3232997 = 606187) (by norm_num)
theorem B1455341 : Blo 1435537 1455341 := bbase (se 3 (by rfl) ⟨272876, by rfl⟩ : syracuseStep 1455341 = 545753) (by norm_num)
theorem B3634429 : Blo 1435537 3634429 := bbase (se 3 (by rfl) ⟨681455, by rfl⟩ : syracuseStep 3634429 = 1362911) (by norm_num)
theorem B3069181 : Blo 1435537 3069181 := bbase (se 3 (by rfl) ⟨575471, by rfl⟩ : syracuseStep 3069181 = 1150943) (by norm_num)
theorem B1455365 : Blo 1435537 1455365 := bbase (se 4 (by rfl) ⟨136440, by rfl⟩ : syracuseStep 1455365 = 272881) (by norm_num)
theorem B5248277 : Blo 1435537 5248277 := bbase (se 6 (by rfl) ⟨123006, by rfl⟩ : syracuseStep 5248277 = 246013) (by norm_num)
theorem B1725733 : Blo 1435537 1725733 := bbase (se 4 (by rfl) ⟨161787, by rfl⟩ : syracuseStep 1725733 = 323575) (by norm_num)
theorem B3233069 : Blo 1435537 3233069 := bbase (se 3 (by rfl) ⟨606200, by rfl⟩ : syracuseStep 3233069 = 1212401) (by norm_num)
theorem B1725781 : Blo 1435537 1725781 := bbase (se 16 (by rfl) ⟨39, by rfl⟩ : syracuseStep 1725781 = 79) (by norm_num)
theorem B3634541 : Blo 1435537 3634541 := bbase (se 3 (by rfl) ⟨681476, by rfl⟩ : syracuseStep 3634541 = 1362953) (by norm_num)
theorem B3233141 : Blo 1435537 3233141 := bbase (se 5 (by rfl) ⟨151553, by rfl⟩ : syracuseStep 3233141 = 303107) (by norm_num)
theorem B2332045 : Blo 1435537 2332045 := bbase (se 3 (by rfl) ⟨437258, by rfl⟩ : syracuseStep 2332045 = 874517) (by norm_num)
theorem B2045341 : Blo 1435537 2045341 := bbase (se 3 (by rfl) ⟨383501, by rfl⟩ : syracuseStep 2045341 = 767003) (by norm_num)
theorem B3233213 : Blo 1435537 3233213 := bbase (se 3 (by rfl) ⟨606227, by rfl⟩ : syracuseStep 3233213 = 1212455) (by norm_num)
theorem B2184653 : Blo 1435537 2184653 := bbase (se 3 (by rfl) ⟨409622, by rfl⟩ : syracuseStep 2184653 = 819245) (by norm_num)
theorem B4847093 : Blo 1435537 4847093 := bbase (se 5 (by rfl) ⟨227207, by rfl⟩ : syracuseStep 4847093 = 454415) (by norm_num)
theorem B3233285 : Blo 1435537 3233285 := bbase (se 4 (by rfl) ⟨303120, by rfl⟩ : syracuseStep 3233285 = 606241) (by norm_num)
theorem B2725397 : Blo 1435537 2725397 := bbase (se 6 (by rfl) ⟨63876, by rfl⟩ : syracuseStep 2725397 = 127753) (by norm_num)
theorem B3634733 : Blo 1435537 3634733 := bbase (se 3 (by rfl) ⟨681512, by rfl⟩ : syracuseStep 3634733 = 1363025) (by norm_num)
theorem B3233357 : Blo 1435537 3233357 := bbase (se 3 (by rfl) ⟨606254, by rfl⟩ : syracuseStep 3233357 = 1212509) (by norm_num)
theorem B2299477 : Blo 1435537 2299477 := bbase (se 8 (by rfl) ⟨13473, by rfl⟩ : syracuseStep 2299477 = 26947) (by norm_num)
theorem B4093541 : Blo 1435537 4093541 := bbase (se 4 (by rfl) ⟨383769, by rfl⟩ : syracuseStep 4093541 = 767539) (by norm_num)
theorem B3233429 : Blo 1435537 3233429 := bbase (se 6 (by rfl) ⟨75783, by rfl⟩ : syracuseStep 3233429 = 151567) (by norm_num)
theorem B8410837 : Blo 1435537 8410837 := bbase (se 7 (by rfl) ⟨98564, by rfl⟩ : syracuseStep 8410837 = 197129) (by norm_num)
theorem B3233501 : Blo 1435537 3233501 := bbase (se 3 (by rfl) ⟨606281, by rfl⟩ : syracuseStep 3233501 = 1212563) (by norm_num)
theorem B2045677 : Blo 1435537 2045677 := bbase (se 3 (by rfl) ⟨383564, by rfl⟩ : syracuseStep 2045677 = 767129) (by norm_num)
theorem B3069677 : Blo 1435537 3069677 := bbase (se 3 (by rfl) ⟨575564, by rfl⟩ : syracuseStep 3069677 = 1151129) (by norm_num)
theorem B2422541 : Blo 1435537 2422541 := bbase (se 3 (by rfl) ⟨454226, by rfl⟩ : syracuseStep 2422541 = 908453) (by norm_num)
theorem B27997973 : Blo 1435537 27997973 := bbase (se 6 (by rfl) ⟨656202, by rfl⟩ : syracuseStep 27997973 = 1312405) (by norm_num)
theorem B3233573 : Blo 1435537 3233573 := bbase (se 4 (by rfl) ⟨303147, by rfl⟩ : syracuseStep 3233573 = 606295) (by norm_num)
theorem B1455949 : Blo 1435537 1455949 := bbase (se 3 (by rfl) ⟨272990, by rfl⟩ : syracuseStep 1455949 = 545981) (by norm_num)
theorem B3233645 : Blo 1435537 3233645 := bbase (se 3 (by rfl) ⟨606308, by rfl⟩ : syracuseStep 3233645 = 1212617) (by norm_num)
theorem B3635077 : Blo 1435537 3635077 := bbase (se 4 (by rfl) ⟨340788, by rfl⟩ : syracuseStep 3635077 = 681577) (by norm_num)
theorem B2422669 : Blo 1435537 2422669 := bbase (se 3 (by rfl) ⟨454250, by rfl⟩ : syracuseStep 2422669 = 908501) (by norm_num)
theorem B7272341 : Blo 1435537 7272341 := bbase (se 6 (by rfl) ⟨170445, by rfl⟩ : syracuseStep 7272341 = 340891) (by norm_num)
theorem B4847525 : Blo 1435537 4847525 := bbase (se 4 (by rfl) ⟨454455, by rfl⟩ : syracuseStep 4847525 = 908911) (by norm_num)
theorem B3233717 : Blo 1435537 3233717 := bbase (se 5 (by rfl) ⟨151580, by rfl⟩ : syracuseStep 3233717 = 303161) (by norm_num)
theorem B2045893 : Blo 1435537 2045893 := bbase (se 4 (by rfl) ⟨191802, by rfl⟩ : syracuseStep 2045893 = 383605) (by norm_num)
theorem B2422757 : Blo 1435537 2422757 := bbase (se 4 (by rfl) ⟨227133, by rfl⟩ : syracuseStep 2422757 = 454267) (by norm_num)
theorem B3635189 : Blo 1435537 3635189 := bbase (se 5 (by rfl) ⟨170399, by rfl⟩ : syracuseStep 3635189 = 340799) (by norm_num)
theorem B8181749 : Blo 1435537 8181749 := bbase (se 5 (by rfl) ⟨383519, by rfl⟩ : syracuseStep 8181749 = 767039) (by norm_num)
theorem B1726453 : Blo 1435537 1726453 := bbase (se 5 (by rfl) ⟨80927, by rfl⟩ : syracuseStep 1726453 = 161855) (by norm_num)
theorem B3233789 : Blo 1435537 3233789 := bbase (se 3 (by rfl) ⟨606335, by rfl⟩ : syracuseStep 3233789 = 1212671) (by norm_num)
theorem B3233861 : Blo 1435537 3233861 := bbase (se 4 (by rfl) ⟨303174, by rfl⟩ : syracuseStep 3233861 = 606349) (by norm_num)
theorem B2422885 : Blo 1435537 2422885 := bbase (se 4 (by rfl) ⟨227145, by rfl⟩ : syracuseStep 2422885 = 454291) (by norm_num)
theorem B3233933 : Blo 1435537 3233933 := bbase (se 3 (by rfl) ⟨606362, by rfl⟩ : syracuseStep 3233933 = 1212725) (by norm_num)
theorem B3545245 : Blo 1435537 3545245 := bbase (se 3 (by rfl) ⟨664733, by rfl⟩ : syracuseStep 3545245 = 1329467) (by norm_num)
theorem B3635381 : Blo 1435537 3635381 := bbase (se 5 (by rfl) ⟨170408, by rfl⟩ : syracuseStep 3635381 = 340817) (by norm_num)
theorem B9828533 : Blo 1435537 9828533 := bbase (se 5 (by rfl) ⟨460712, by rfl⟩ : syracuseStep 9828533 = 921425) (by norm_num)
theorem B2422973 : Blo 1435537 2422973 := bbase (se 3 (by rfl) ⟨454307, by rfl⟩ : syracuseStep 2422973 = 908615) (by norm_num)
theorem B27982037 : Blo 1435537 27982037 := bbase (se 7 (by rfl) ⟨327914, by rfl⟩ : syracuseStep 27982037 = 655829) (by norm_num)
theorem B3234005 : Blo 1435537 3234005 := bbase (se 7 (by rfl) ⟨37898, by rfl⟩ : syracuseStep 3234005 = 75797) (by norm_num)
theorem B2726149 : Blo 1435537 2726149 := bbase (se 4 (by rfl) ⟨255576, by rfl⟩ : syracuseStep 2726149 = 511153) (by norm_num)
theorem B3275029 : Blo 1435537 3275029 := bbase (se 6 (by rfl) ⟨76758, by rfl⟩ : syracuseStep 3275029 = 153517) (by norm_num)
theorem B3234077 : Blo 1435537 3234077 := bbase (se 3 (by rfl) ⟨606389, by rfl⟩ : syracuseStep 3234077 = 1212779) (by norm_num)
theorem B10361141 : Blo 1435537 10361141 := bbase (se 5 (by rfl) ⟨485678, by rfl⟩ : syracuseStep 10361141 = 971357) (by norm_num)
theorem B2423101 : Blo 1435537 2423101 := bbase (se 3 (by rfl) ⟨454331, by rfl⟩ : syracuseStep 2423101 = 908663) (by norm_num)
theorem B2046269 : Blo 1435537 2046269 := bbase (se 3 (by rfl) ⟨383675, by rfl⟩ : syracuseStep 2046269 = 767351) (by norm_num)
theorem B4847957 : Blo 1435537 4847957 := bbase (se 10 (by rfl) ⟨7101, by rfl⟩ : syracuseStep 4847957 = 14203) (by norm_num)
theorem B1816921 : Blo 1435537 1816921 := bbase (se 2 (by rfl) ⟨681345, by rfl⟩ : syracuseStep 1816921 = 1362691) (by norm_num)
theorem B3275101 : Blo 1435537 3275101 := bbase (se 3 (by rfl) ⟨614081, by rfl⟩ : syracuseStep 3275101 = 1228163) (by norm_num)
theorem B3234149 : Blo 1435537 3234149 := bbase (se 4 (by rfl) ⟨303201, by rfl⟩ : syracuseStep 3234149 = 606403) (by norm_num)
theorem B2423189 : Blo 1435537 2423189 := bbase (se 6 (by rfl) ⟨56793, by rfl⟩ : syracuseStep 2423189 = 113587) (by norm_num)
theorem B2726293 : Blo 1435537 2726293 := bbase (se 6 (by rfl) ⟨63897, by rfl⟩ : syracuseStep 2726293 = 127795) (by norm_num)
theorem B3234221 : Blo 1435537 3234221 := bbase (se 3 (by rfl) ⟨606416, by rfl⟩ : syracuseStep 3234221 = 1212833) (by norm_num)
theorem B3275221 : Blo 1435537 3275221 := bbase (se 7 (by rfl) ⟨38381, by rfl⟩ : syracuseStep 3275221 = 76763) (by norm_num)
theorem B3234293 : Blo 1435537 3234293 := bbase (se 5 (by rfl) ⟨151607, by rfl⟩ : syracuseStep 3234293 = 303215) (by norm_num)
theorem B2300413 : Blo 1435537 2300413 := bbase (se 3 (by rfl) ⟨431327, by rfl⟩ : syracuseStep 2300413 = 862655) (by norm_num)
theorem B1817093 : Blo 1435537 1817093 := bbase (se 4 (by rfl) ⟨170352, by rfl⟩ : syracuseStep 1817093 = 340705) (by norm_num)
theorem B3635725 : Blo 1435537 3635725 := bbase (se 3 (by rfl) ⟨681698, by rfl⟩ : syracuseStep 3635725 = 1363397) (by norm_num)
theorem B2423317 : Blo 1435537 2423317 := bbase (se 6 (by rfl) ⟨56796, by rfl⟩ : syracuseStep 2423317 = 113593) (by norm_num)
theorem B5175845 : Blo 1435537 5175845 := bbase (se 4 (by rfl) ⟨485235, by rfl⟩ : syracuseStep 5175845 = 970471) (by norm_num)
theorem B2726453 : Blo 1435537 2726453 := bbase (se 5 (by rfl) ⟨127802, by rfl⟩ : syracuseStep 2726453 = 255605) (by norm_num)
theorem B1817149 : Blo 1435537 1817149 := bbase (se 3 (by rfl) ⟨340715, by rfl⟩ : syracuseStep 1817149 = 681431) (by norm_num)
theorem B3234365 : Blo 1435537 3234365 := bbase (se 3 (by rfl) ⟨606443, by rfl⟩ : syracuseStep 3234365 = 1212887) (by norm_num)
theorem B78608981 : Blo 1435537 78608981 := bbase (se 8 (by rfl) ⟨460599, by rfl⟩ : syracuseStep 78608981 = 921199) (by norm_num)
theorem B2423405 : Blo 1435537 2423405 := bbase (se 3 (by rfl) ⟨454388, by rfl⟩ : syracuseStep 2423405 = 908777) (by norm_num)
theorem B3635837 : Blo 1435537 3635837 := bbase (se 3 (by rfl) ⟨681719, by rfl⟩ : syracuseStep 3635837 = 1363439) (by norm_num)
theorem B3234437 : Blo 1435537 3234437 := bbase (se 4 (by rfl) ⟨303228, by rfl⟩ : syracuseStep 3234437 = 606457) (by norm_num)
theorem B5454485 : Blo 1435537 5454485 := bbase (se 6 (by rfl) ⟨127839, by rfl⟩ : syracuseStep 5454485 = 255679) (by norm_num)
theorem B1817245 : Blo 1435537 1817245 := bbase (se 3 (by rfl) ⟨340733, by rfl⟩ : syracuseStep 1817245 = 681467) (by norm_num)
theorem B2726597 : Blo 1435537 2726597 := bbase (se 4 (by rfl) ⟨255618, by rfl⟩ : syracuseStep 2726597 = 511237) (by norm_num)
theorem B2423533 : Blo 1435537 2423533 := bbase (se 3 (by rfl) ⟨454412, by rfl⟩ : syracuseStep 2423533 = 908825) (by norm_num)
theorem B6904565 : Blo 1435537 6904565 := bbase (se 5 (by rfl) ⟨323651, by rfl⟩ : syracuseStep 6904565 = 647303) (by norm_num)
theorem B4848389 : Blo 1435537 4848389 := bbase (se 4 (by rfl) ⟨454536, by rfl⟩ : syracuseStep 4848389 = 909073) (by norm_num)
theorem B3636029 : Blo 1435537 3636029 := bbase (se 3 (by rfl) ⟨681755, by rfl⟩ : syracuseStep 3636029 = 1363511) (by norm_num)
theorem B2423621 : Blo 1435537 2423621 := bbase (se 4 (by rfl) ⟨227214, by rfl⟩ : syracuseStep 2423621 = 454429) (by norm_num)
theorem B1817417 : Blo 1435537 1817417 := bbase (se 2 (by rfl) ⟨681531, by rfl⟩ : syracuseStep 1817417 = 1363063) (by norm_num)
theorem B2153309 : Blo 1435537 2153309 := bbase (se 3 (by rfl) ⟨403745, by rfl⟩ : syracuseStep 2153309 = 807491) (by norm_num)
theorem B2153333 : Blo 1435537 2153333 := bbase (se 5 (by rfl) ⟨100937, by rfl⟩ : syracuseStep 2153333 = 201875) (by norm_num)
theorem B1817473 : Blo 1435537 1817473 := bbase (se 2 (by rfl) ⟨681552, by rfl⟩ : syracuseStep 1817473 = 1363105) (by norm_num)
theorem B2153357 : Blo 1435537 2153357 := bbase (se 3 (by rfl) ⟨403754, by rfl⟩ : syracuseStep 2153357 = 807509) (by norm_num)
theorem B2153381 : Blo 1435537 2153381 := bbase (se 4 (by rfl) ⟨201879, by rfl⟩ : syracuseStep 2153381 = 403759) (by norm_num)
theorem B5454773 : Blo 1435537 5454773 := bbase (se 5 (by rfl) ⟨255692, by rfl⟩ : syracuseStep 5454773 = 511385) (by norm_num)
theorem B2153405 : Blo 1435537 2153405 := bbase (se 3 (by rfl) ⟨403763, by rfl⟩ : syracuseStep 2153405 = 807527) (by norm_num)
theorem B2423749 : Blo 1435537 2423749 := bbase (se 4 (by rfl) ⟨227226, by rfl⟩ : syracuseStep 2423749 = 454453) (by norm_num)
theorem B2153429 : Blo 1435537 2153429 := bbase (se 7 (by rfl) ⟨25235, by rfl⟩ : syracuseStep 2153429 = 50471) (by norm_num)
theorem B6134741 : Blo 1435537 6134741 := bbase (se 7 (by rfl) ⟨71891, by rfl⟩ : syracuseStep 6134741 = 143783) (by norm_num)
theorem B1817569 : Blo 1435537 1817569 := bbase (se 2 (by rfl) ⟨681588, by rfl⟩ : syracuseStep 1817569 = 1363177) (by norm_num)
theorem B2726885 : Blo 1435537 2726885 := bbase (se 4 (by rfl) ⟨255645, by rfl⟩ : syracuseStep 2726885 = 511291) (by norm_num)
theorem B2153453 : Blo 1435537 2153453 := bbase (se 3 (by rfl) ⟨403772, by rfl⟩ : syracuseStep 2153453 = 807545) (by norm_num)
theorem B8739829 : Blo 1435537 8739829 := bbase (se 5 (by rfl) ⟨409679, by rfl⟩ : syracuseStep 8739829 = 819359) (by norm_num)
theorem B2153477 : Blo 1435537 2153477 := bbase (se 4 (by rfl) ⟨201888, by rfl⟩ : syracuseStep 2153477 = 403777) (by norm_num)
theorem B3111949 : Blo 1435537 3111949 := bbase (se 3 (by rfl) ⟨583490, by rfl⟩ : syracuseStep 3111949 = 1166981) (by norm_num)
theorem B4602901 : Blo 1435537 4602901 := bbase (se 6 (by rfl) ⟨107880, by rfl⟩ : syracuseStep 4602901 = 215761) (by norm_num)
theorem B2153501 : Blo 1435537 2153501 := bbase (se 3 (by rfl) ⟨403781, by rfl⟩ : syracuseStep 2153501 = 807563) (by norm_num)
theorem B2423837 : Blo 1435537 2423837 := bbase (se 3 (by rfl) ⟨454469, by rfl⟩ : syracuseStep 2423837 = 908939) (by norm_num)
theorem B2153525 : Blo 1435537 2153525 := bbase (se 5 (by rfl) ⟨100946, by rfl⟩ : syracuseStep 2153525 = 201893) (by norm_num)
theorem B2153549 : Blo 1435537 2153549 := bbase (se 3 (by rfl) ⟨403790, by rfl⟩ : syracuseStep 2153549 = 807581) (by norm_num)
theorem B2153573 : Blo 1435537 2153573 := bbase (se 4 (by rfl) ⟨201897, by rfl⟩ : syracuseStep 2153573 = 403795) (by norm_num)
theorem B2153597 : Blo 1435537 2153597 := bbase (se 3 (by rfl) ⟨403799, by rfl⟩ : syracuseStep 2153597 = 807599) (by norm_num)
theorem B2727037 : Blo 1435537 2727037 := bbase (se 3 (by rfl) ⟨511319, by rfl⟩ : syracuseStep 2727037 = 1022639) (by norm_num)
theorem B1817741 : Blo 1435537 1817741 := bbase (se 3 (by rfl) ⟨340826, by rfl⟩ : syracuseStep 1817741 = 681653) (by norm_num)
theorem B2153621 : Blo 1435537 2153621 := bbase (se 6 (by rfl) ⟨50475, by rfl⟩ : syracuseStep 2153621 = 100951) (by norm_num)
theorem B3636373 : Blo 1435537 3636373 := bbase (se 6 (by rfl) ⟨85227, by rfl⟩ : syracuseStep 3636373 = 170455) (by norm_num)
theorem B2423965 : Blo 1435537 2423965 := bbase (se 3 (by rfl) ⟨454493, by rfl⟩ : syracuseStep 2423965 = 908987) (by norm_num)
theorem B7273637 : Blo 1435537 7273637 := bbase (se 4 (by rfl) ⟨681903, by rfl⟩ : syracuseStep 7273637 = 1363807) (by norm_num)
theorem B2153645 : Blo 1435537 2153645 := bbase (se 3 (by rfl) ⟨403808, by rfl⟩ : syracuseStep 2153645 = 807617) (by norm_num)
theorem B4848821 : Blo 1435537 4848821 := bbase (se 5 (by rfl) ⟨227288, by rfl⟩ : syracuseStep 4848821 = 454577) (by norm_num)
theorem B2153669 : Blo 1435537 2153669 := bbase (se 4 (by rfl) ⟨201906, by rfl⟩ : syracuseStep 2153669 = 403813) (by norm_num)
theorem B1817797 : Blo 1435537 1817797 := bbase (se 4 (by rfl) ⟨170418, by rfl⟩ : syracuseStep 1817797 = 340837) (by norm_num)
theorem B5823701 : Blo 1435537 5823701 := bbase (se 7 (by rfl) ⟨68246, by rfl⟩ : syracuseStep 5823701 = 136493) (by norm_num)
theorem B3366101 : Blo 1435537 3366101 := bbase (se 7 (by rfl) ⟨39446, by rfl⟩ : syracuseStep 3366101 = 78893) (by norm_num)
theorem B2153693 : Blo 1435537 2153693 := bbase (se 3 (by rfl) ⟨403817, by rfl⟩ : syracuseStep 2153693 = 807635) (by norm_num)
theorem B2153717 : Blo 1435537 2153717 := bbase (se 5 (by rfl) ⟨100955, by rfl⟩ : syracuseStep 2153717 = 201911) (by norm_num)
theorem B2424053 : Blo 1435537 2424053 := bbase (se 5 (by rfl) ⟨113627, by rfl⟩ : syracuseStep 2424053 = 227255) (by norm_num)
theorem B3636485 : Blo 1435537 3636485 := bbase (se 4 (by rfl) ⟨340920, by rfl⟩ : syracuseStep 3636485 = 681841) (by norm_num)
theorem B2153741 : Blo 1435537 2153741 := bbase (se 3 (by rfl) ⟨403826, by rfl⟩ : syracuseStep 2153741 = 807653) (by norm_num)
theorem B4603157 : Blo 1435537 4603157 := bbase (se 6 (by rfl) ⟨107886, by rfl⟩ : syracuseStep 4603157 = 215773) (by norm_num)
theorem B2153765 : Blo 1435537 2153765 := bbase (se 4 (by rfl) ⟨201915, by rfl⟩ : syracuseStep 2153765 = 403831) (by norm_num)
theorem B1817893 : Blo 1435537 1817893 := bbase (se 4 (by rfl) ⟨170427, by rfl⟩ : syracuseStep 1817893 = 340855) (by norm_num)
theorem B4914485 : Blo 1435537 4914485 := bbase (se 5 (by rfl) ⟨230366, by rfl⟩ : syracuseStep 4914485 = 460733) (by norm_num)
theorem B2153789 : Blo 1435537 2153789 := bbase (se 3 (by rfl) ⟨403835, by rfl⟩ : syracuseStep 2153789 = 807671) (by norm_num)
theorem B2153813 : Blo 1435537 2153813 := bbase (se 11 (by rfl) ⟨1577, by rfl⟩ : syracuseStep 2153813 = 3155) (by norm_num)
theorem B2153837 : Blo 1435537 2153837 := bbase (se 3 (by rfl) ⟨403844, by rfl⟩ : syracuseStep 2153837 = 807689) (by norm_num)
theorem B2424181 : Blo 1435537 2424181 := bbase (se 5 (by rfl) ⟨113633, by rfl⟩ : syracuseStep 2424181 = 227267) (by norm_num)
theorem B2153861 : Blo 1435537 2153861 := bbase (se 4 (by rfl) ⟨201924, by rfl⟩ : syracuseStep 2153861 = 403849) (by norm_num)
theorem B2153885 : Blo 1435537 2153885 := bbase (se 3 (by rfl) ⟨403853, by rfl⟩ : syracuseStep 2153885 = 807707) (by norm_num)
theorem B2727341 : Blo 1435537 2727341 := bbase (se 3 (by rfl) ⟨511376, by rfl⟩ : syracuseStep 2727341 = 1022753) (by norm_num)
theorem B2153909 : Blo 1435537 2153909 := bbase (se 5 (by rfl) ⟨100964, by rfl⟩ : syracuseStep 2153909 = 201929) (by norm_num)
theorem B3636677 : Blo 1435537 3636677 := bbase (se 4 (by rfl) ⟨340938, by rfl⟩ : syracuseStep 3636677 = 681877) (by norm_num)
theorem B2153933 : Blo 1435537 2153933 := bbase (se 3 (by rfl) ⟨403862, by rfl⟩ : syracuseStep 2153933 = 807725) (by norm_num)
theorem B2424269 : Blo 1435537 2424269 := bbase (se 3 (by rfl) ⟨454550, by rfl⟩ : syracuseStep 2424269 = 909101) (by norm_num)
theorem B1818065 : Blo 1435537 1818065 := bbase (se 2 (by rfl) ⟨681774, by rfl⟩ : syracuseStep 1818065 = 1363549) (by norm_num)
theorem B4144613 : Blo 1435537 4144613 := bbase (se 4 (by rfl) ⟨388557, by rfl⟩ : syracuseStep 4144613 = 777115) (by norm_num)
theorem B2153957 : Blo 1435537 2153957 := bbase (se 4 (by rfl) ⟨201933, by rfl⟩ : syracuseStep 2153957 = 403867) (by norm_num)
theorem B3276269 : Blo 1435537 3276269 := bbase (se 3 (by rfl) ⟨614300, by rfl⟩ : syracuseStep 3276269 = 1228601) (by norm_num)
theorem B2153981 : Blo 1435537 2153981 := bbase (se 3 (by rfl) ⟨403871, by rfl⟩ : syracuseStep 2153981 = 807743) (by norm_num)
theorem B1818121 : Blo 1435537 1818121 := bbase (se 2 (by rfl) ⟨681795, by rfl⟩ : syracuseStep 1818121 = 1363591) (by norm_num)
theorem B2154005 : Blo 1435537 2154005 := bbase (se 6 (by rfl) ⟨50484, by rfl⟩ : syracuseStep 2154005 = 100969) (by norm_num)
theorem B2154029 : Blo 1435537 2154029 := bbase (se 3 (by rfl) ⟨403880, by rfl⟩ : syracuseStep 2154029 = 807761) (by norm_num)
theorem B1842737 : Blo 1435537 1842737 := bbase (se 2 (by rfl) ⟨691026, by rfl⟩ : syracuseStep 1842737 = 1382053) (by norm_num)
theorem B2154053 : Blo 1435537 2154053 := bbase (se 4 (by rfl) ⟨201942, by rfl⟩ : syracuseStep 2154053 = 403885) (by norm_num)
theorem B2424397 : Blo 1435537 2424397 := bbase (se 3 (by rfl) ⟨454574, by rfl⟩ : syracuseStep 2424397 = 909149) (by norm_num)
theorem B2154077 : Blo 1435537 2154077 := bbase (se 3 (by rfl) ⟨403889, by rfl⟩ : syracuseStep 2154077 = 807779) (by norm_num)
theorem B4849253 : Blo 1435537 4849253 := bbase (se 4 (by rfl) ⟨454617, by rfl⟩ : syracuseStep 4849253 = 909235) (by norm_num)
theorem B1818217 : Blo 1435537 1818217 := bbase (se 2 (by rfl) ⟨681831, by rfl⟩ : syracuseStep 1818217 = 1363663) (by norm_num)
theorem B2154101 : Blo 1435537 2154101 := bbase (se 5 (by rfl) ⟨100973, by rfl⟩ : syracuseStep 2154101 = 201947) (by norm_num)
theorem B2154125 : Blo 1435537 2154125 := bbase (se 3 (by rfl) ⟨403898, by rfl⟩ : syracuseStep 2154125 = 807797) (by norm_num)
theorem B2154149 : Blo 1435537 2154149 := bbase (se 4 (by rfl) ⟨201951, by rfl⟩ : syracuseStep 2154149 = 403903) (by norm_num)
theorem B2424485 : Blo 1435537 2424485 := bbase (se 4 (by rfl) ⟨227295, by rfl⟩ : syracuseStep 2424485 = 454591) (by norm_num)
theorem B2301605 : Blo 1435537 2301605 := bbase (se 4 (by rfl) ⟨215775, by rfl⟩ : syracuseStep 2301605 = 431551) (by norm_num)
theorem B2154173 : Blo 1435537 2154173 := bbase (se 3 (by rfl) ⟨403907, by rfl⟩ : syracuseStep 2154173 = 807815) (by norm_num)
theorem B3546821 : Blo 1435537 3546821 := bbase (se 4 (by rfl) ⟨332514, by rfl⟩ : syracuseStep 3546821 = 665029) (by norm_num)
theorem B2154197 : Blo 1435537 2154197 := bbase (se 7 (by rfl) ⟨25244, by rfl⟩ : syracuseStep 2154197 = 50489) (by norm_num)
theorem B2154221 : Blo 1435537 2154221 := bbase (se 3 (by rfl) ⟨403916, by rfl⟩ : syracuseStep 2154221 = 807833) (by norm_num)
theorem B2154245 : Blo 1435537 2154245 := bbase (se 4 (by rfl) ⟨201960, by rfl⟩ : syracuseStep 2154245 = 403921) (by norm_num)
theorem B1818389 : Blo 1435537 1818389 := bbase (se 6 (by rfl) ⟨42618, by rfl⟩ : syracuseStep 1818389 = 85237) (by norm_num)
theorem B2154269 : Blo 1435537 2154269 := bbase (se 3 (by rfl) ⟨403925, by rfl⟩ : syracuseStep 2154269 = 807851) (by norm_num)
theorem B3637021 : Blo 1435537 3637021 := bbase (se 3 (by rfl) ⟨681941, by rfl⟩ : syracuseStep 3637021 = 1363883) (by norm_num)
theorem B2424613 : Blo 1435537 2424613 := bbase (se 4 (by rfl) ⟨227307, by rfl⟩ : syracuseStep 2424613 = 454615) (by norm_num)
theorem B2154293 : Blo 1435537 2154293 := bbase (se 5 (by rfl) ⟨100982, by rfl⟩ : syracuseStep 2154293 = 201965) (by norm_num)
theorem B2154317 : Blo 1435537 2154317 := bbase (se 3 (by rfl) ⟨403934, by rfl⟩ : syracuseStep 2154317 = 807869) (by norm_num)
theorem B1818445 : Blo 1435537 1818445 := bbase (se 3 (by rfl) ⟨340958, by rfl⟩ : syracuseStep 1818445 = 681917) (by norm_num)
theorem B2154341 : Blo 1435537 2154341 := bbase (se 4 (by rfl) ⟨201969, by rfl⟩ : syracuseStep 2154341 = 403939) (by norm_num)
theorem B2301797 : Blo 1435537 2301797 := bbase (se 4 (by rfl) ⟨215793, by rfl⟩ : syracuseStep 2301797 = 431587) (by norm_num)
theorem B2154365 : Blo 1435537 2154365 := bbase (se 3 (by rfl) ⟨403943, by rfl⟩ : syracuseStep 2154365 = 807887) (by norm_num)
theorem B2424701 : Blo 1435537 2424701 := bbase (se 3 (by rfl) ⟨454631, by rfl⟩ : syracuseStep 2424701 = 909263) (by norm_num)
theorem B3637133 : Blo 1435537 3637133 := bbase (se 3 (by rfl) ⟨681962, by rfl⟩ : syracuseStep 3637133 = 1363925) (by norm_num)
theorem B2154389 : Blo 1435537 2154389 := bbase (se 6 (by rfl) ⟨50493, by rfl⟩ : syracuseStep 2154389 = 100987) (by norm_num)
theorem B2154413 : Blo 1435537 2154413 := bbase (se 3 (by rfl) ⟨403952, by rfl⟩ : syracuseStep 2154413 = 807905) (by norm_num)
theorem B1818541 : Blo 1435537 1818541 := bbase (se 3 (by rfl) ⟨340976, by rfl⟩ : syracuseStep 1818541 = 681953) (by norm_num)
theorem B2154437 : Blo 1435537 2154437 := bbase (se 4 (by rfl) ⟨201978, by rfl⟩ : syracuseStep 2154437 = 403957) (by norm_num)
theorem B2154461 : Blo 1435537 2154461 := bbase (se 3 (by rfl) ⟨403961, by rfl⟩ : syracuseStep 2154461 = 807923) (by norm_num)
theorem B2154485 : Blo 1435537 2154485 := bbase (se 5 (by rfl) ⟨100991, by rfl⟩ : syracuseStep 2154485 = 201983) (by norm_num)
theorem B2424829 : Blo 1435537 2424829 := bbase (se 3 (by rfl) ⟨454655, by rfl⟩ : syracuseStep 2424829 = 909311) (by norm_num)
theorem B2154497 : Blo 1435537 2154497 := bstep (se 2 (by rfl) ⟨807936, by rfl⟩ : syracuseStep 2154497 = 1615873) B1615873
theorem B2154515 : Blo 1435537 2154515 := bstep (se 1 (by rfl) ⟨1615886, by rfl⟩ : syracuseStep 2154515 = 3231773) B3231773
theorem B2154545 : Blo 1435537 2154545 := bstep (se 2 (by rfl) ⟨807954, by rfl⟩ : syracuseStep 2154545 = 1615909) B1615909
theorem B2424883 : Blo 1435537 2424883 := bstep (se 1 (by rfl) ⟨1818662, by rfl⟩ : syracuseStep 2424883 = 3637325) B3637325
theorem B2154563 : Blo 1435537 2154563 := bstep (se 1 (by rfl) ⟨1615922, by rfl⟩ : syracuseStep 2154563 = 3231845) B3231845
theorem B16597061 : Blo 1435537 16597061 := bstep (se 4 (by rfl) ⟨1555974, by rfl⟩ : syracuseStep 16597061 = 3111949) B3111949
theorem B2154593 : Blo 1435537 2154593 := bstep (se 2 (by rfl) ⟨807972, by rfl⟩ : syracuseStep 2154593 = 1615945) B1615945
theorem B7274609 : Blo 1435537 7274609 := bstep (se 2 (by rfl) ⟨2727978, by rfl⟩ : syracuseStep 7274609 = 5455957) B5455957
theorem B2154611 : Blo 1435537 2154611 := bstep (se 1 (by rfl) ⟨1615958, by rfl⟩ : syracuseStep 2154611 = 3231917) B3231917
theorem B2154641 : Blo 1435537 2154641 := bstep (se 2 (by rfl) ⟨807990, by rfl⟩ : syracuseStep 2154641 = 1615981) B1615981
theorem B2154659 : Blo 1435537 2154659 := bstep (se 1 (by rfl) ⟨1615994, by rfl⟩ : syracuseStep 2154659 = 3231989) B3231989
theorem B2154689 : Blo 1435537 2154689 := bstep (se 2 (by rfl) ⟨808008, by rfl⟩ : syracuseStep 2154689 = 1616017) B1616017
theorem B2425025 : Blo 1435537 2425025 := bstep (se 2 (by rfl) ⟨909384, by rfl⟩ : syracuseStep 2425025 = 1818769) B1818769
theorem B4726993 : Blo 1435537 4726993 := bstep (se 2 (by rfl) ⟨1772622, by rfl⟩ : syracuseStep 4726993 = 3545245) B3545245
theorem B3637457 : Blo 1435537 3637457 := bstep (se 2 (by rfl) ⟨1364046, by rfl⟩ : syracuseStep 3637457 = 2728093) B2728093
theorem B2154707 : Blo 1435537 2154707 := bstep (se 1 (by rfl) ⟨1616030, by rfl⟩ : syracuseStep 2154707 = 3232061) B3232061
theorem B6217955 : Blo 1435537 6217955 := bstep (se 1 (by rfl) ⟨4663466, by rfl⟩ : syracuseStep 6217955 = 9326933) B9326933
theorem B4604131 : Blo 1435537 4604131 := bstep (se 1 (by rfl) ⟨3453098, by rfl⟩ : syracuseStep 4604131 = 6906197) B6906197
theorem B4849901 : Blo 1435537 4849901 := bstep (se 3 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 4849901 = 1818713) B1818713
theorem B2154737 : Blo 1435537 2154737 := bstep (se 2 (by rfl) ⟨808026, by rfl⟩ : syracuseStep 2154737 = 1616053) B1616053
theorem B2154755 : Blo 1435537 2154755 := bstep (se 1 (by rfl) ⟨1616066, by rfl⟩ : syracuseStep 2154755 = 3232133) B3232133
theorem B3637507 : Blo 1435537 3637507 := bstep (se 1 (by rfl) ⟨2728130, by rfl⟩ : syracuseStep 3637507 = 5456261) B5456261
theorem B16589069 : Blo 1435537 16589069 := bstep (se 3 (by rfl) ⟨3110450, by rfl⟩ : syracuseStep 16589069 = 6220901) B6220901
theorem B2154785 : Blo 1435537 2154785 := bstep (se 2 (by rfl) ⟨808044, by rfl⟩ : syracuseStep 2154785 = 1616089) B1616089
theorem B4849955 : Blo 1435537 4849955 := bstep (se 1 (by rfl) ⟨3637466, by rfl⟩ : syracuseStep 4849955 = 7274933) B7274933
theorem B2154803 : Blo 1435537 2154803 := bstep (se 1 (by rfl) ⟨1616102, by rfl⟩ : syracuseStep 2154803 = 3232205) B3232205
theorem B1843507 : Blo 1435537 1843507 := bstep (se 1 (by rfl) ⟨1382630, by rfl⟩ : syracuseStep 1843507 = 2765261) B2765261
theorem B1818931 : Blo 1435537 1818931 := bstep (se 1 (by rfl) ⟨1364198, by rfl⟩ : syracuseStep 1818931 = 2728397) B2728397
theorem B2425153 : Blo 1435537 2425153 := bstep (se 2 (by rfl) ⟨909432, by rfl⟩ : syracuseStep 2425153 = 1818865) B1818865
theorem B4792643 : Blo 1435537 4792643 := bstep (se 1 (by rfl) ⟨3594482, by rfl⟩ : syracuseStep 4792643 = 7188965) B7188965
theorem B4088141 : Blo 1435537 4088141 := bstep (se 3 (by rfl) ⟨766526, by rfl⟩ : syracuseStep 4088141 = 1533053) B1533053
theorem B2154833 : Blo 1435537 2154833 := bstep (se 2 (by rfl) ⟨808062, by rfl⟩ : syracuseStep 2154833 = 1616125) B1616125
theorem B2154851 : Blo 1435537 2154851 := bstep (se 1 (by rfl) ⟨1616138, by rfl⟩ : syracuseStep 2154851 = 3232277) B3232277
theorem B2425187 : Blo 1435537 2425187 := bstep (se 1 (by rfl) ⟨1818890, by rfl⟩ : syracuseStep 2425187 = 3637781) B3637781
theorem B4366705 : Blo 1435537 4366705 := bstep (se 2 (by rfl) ⟨1637514, by rfl⟩ : syracuseStep 4366705 = 3275029) B3275029
theorem B4604273 : Blo 1435537 4604273 := bstep (se 2 (by rfl) ⟨1726602, by rfl⟩ : syracuseStep 4604273 = 3453205) B3453205
theorem B2154881 : Blo 1435537 2154881 := bstep (se 2 (by rfl) ⟨808080, by rfl⟩ : syracuseStep 2154881 = 1616161) B1616161
theorem B15524237 : Blo 1435537 15524237 := bstep (se 3 (by rfl) ⟨2910794, by rfl⟩ : syracuseStep 15524237 = 5821589) B5821589
theorem B3637649 : Blo 1435537 3637649 := bstep (se 2 (by rfl) ⟨1364118, by rfl⟩ : syracuseStep 3637649 = 2728237) B2728237
theorem B2154899 : Blo 1435537 2154899 := bstep (se 1 (by rfl) ⟨1616174, by rfl⟩ : syracuseStep 2154899 = 3232349) B3232349
theorem B1819027 : Blo 1435537 1819027 := bstep (se 1 (by rfl) ⟨1364270, by rfl⟩ : syracuseStep 1819027 = 2728541) B2728541
theorem B2154929 : Blo 1435537 2154929 := bstep (se 2 (by rfl) ⟨808098, by rfl⟩ : syracuseStep 2154929 = 1616197) B1616197
theorem B2154947 : Blo 1435537 2154947 := bstep (se 1 (by rfl) ⟨1616210, by rfl⟩ : syracuseStep 2154947 = 3232421) B3232421
theorem B4366801 : Blo 1435537 4366801 := bstep (se 2 (by rfl) ⟨1637550, by rfl⟩ : syracuseStep 4366801 = 3275101) B3275101
theorem B2154977 : Blo 1435537 2154977 := bstep (se 2 (by rfl) ⟨808116, by rfl⟩ : syracuseStep 2154977 = 1616233) B1616233
theorem B8176099 : Blo 1435537 8176099 := bstep (se 1 (by rfl) ⟨6132074, by rfl⟩ : syracuseStep 8176099 = 12264149) B12264149
theorem B2425315 : Blo 1435537 2425315 := bstep (se 1 (by rfl) ⟨1818986, by rfl⟩ : syracuseStep 2425315 = 3637973) B3637973
theorem B2154995 : Blo 1435537 2154995 := bstep (se 1 (by rfl) ⟨1616246, by rfl⟩ : syracuseStep 2154995 = 3232493) B3232493
theorem B4088323 : Blo 1435537 4088323 := bstep (se 1 (by rfl) ⟨3066242, by rfl⟩ : syracuseStep 4088323 = 6132485) B6132485
theorem B9200141 : Blo 1435537 9200141 := bstep (se 3 (by rfl) ⟨1725026, by rfl⟩ : syracuseStep 9200141 = 3450053) B3450053
theorem B2155025 : Blo 1435537 2155025 := bstep (se 2 (by rfl) ⟨808134, by rfl⟩ : syracuseStep 2155025 = 1616269) B1616269
theorem B2155043 : Blo 1435537 2155043 := bstep (se 1 (by rfl) ⟨1616282, by rfl⟩ : syracuseStep 2155043 = 3232565) B3232565
theorem B4088369 : Blo 1435537 4088369 := bstep (se 2 (by rfl) ⟨1533138, by rfl⟩ : syracuseStep 4088369 = 3066277) B3066277
theorem B4850225 : Blo 1435537 4850225 := bstep (se 2 (by rfl) ⟨1818834, by rfl⟩ : syracuseStep 4850225 = 3637669) B3637669
theorem B2155073 : Blo 1435537 2155073 := bstep (se 2 (by rfl) ⟨808152, by rfl⟩ : syracuseStep 2155073 = 1616305) B1616305
theorem B2155091 : Blo 1435537 2155091 := bstep (se 1 (by rfl) ⟨1616318, by rfl⟩ : syracuseStep 2155091 = 3232637) B3232637
theorem B4366961 : Blo 1435537 4366961 := bstep (se 2 (by rfl) ⟨1637610, by rfl⟩ : syracuseStep 4366961 = 3275221) B3275221
theorem B2155121 : Blo 1435537 2155121 := bstep (se 2 (by rfl) ⟨808170, by rfl⟩ : syracuseStep 2155121 = 1616341) B1616341
theorem B2425457 : Blo 1435537 2425457 := bstep (se 2 (by rfl) ⟨909546, by rfl⟩ : syracuseStep 2425457 = 1819093) B1819093
theorem B2155139 : Blo 1435537 2155139 := bstep (se 1 (by rfl) ⟨1616354, by rfl⟩ : syracuseStep 2155139 = 3232709) B3232709
theorem B2728579 : Blo 1435537 2728579 := bstep (se 1 (by rfl) ⟨2046434, by rfl⟩ : syracuseStep 2728579 = 4092869) B4092869
theorem B2155169 : Blo 1435537 2155169 := bstep (se 2 (by rfl) ⟨808188, by rfl⟩ : syracuseStep 2155169 = 1616377) B1616377
theorem B7766705 : Blo 1435537 7766705 := bstep (se 2 (by rfl) ⟨2912514, by rfl⟩ : syracuseStep 7766705 = 5825029) B5825029
theorem B2155187 : Blo 1435537 2155187 := bstep (se 1 (by rfl) ⟨1616390, by rfl⟩ : syracuseStep 2155187 = 3232781) B3232781
theorem B3596995 : Blo 1435537 3596995 := bstep (se 1 (by rfl) ⟨2697746, by rfl⟩ : syracuseStep 3596995 = 5395493) B5395493
theorem B2155217 : Blo 1435537 2155217 := bstep (se 2 (by rfl) ⟨808206, by rfl⟩ : syracuseStep 2155217 = 1616413) B1616413
theorem B2155235 : Blo 1435537 2155235 := bstep (se 1 (by rfl) ⟨1616426, by rfl⟩ : syracuseStep 2155235 = 3232853) B3232853
theorem B2425585 : Blo 1435537 2425585 := bstep (se 2 (by rfl) ⟨909594, by rfl⟩ : syracuseStep 2425585 = 1819189) B1819189
theorem B2155265 : Blo 1435537 2155265 := bstep (se 2 (by rfl) ⟨808224, by rfl⟩ : syracuseStep 2155265 = 1616449) B1616449
theorem B2155283 : Blo 1435537 2155283 := bstep (se 1 (by rfl) ⟨1616462, by rfl⟩ : syracuseStep 2155283 = 3232925) B3232925
theorem B2425619 : Blo 1435537 2425619 := bstep (se 1 (by rfl) ⟨1819214, by rfl⟩ : syracuseStep 2425619 = 3638429) B3638429
theorem B2155313 : Blo 1435537 2155313 := bstep (se 2 (by rfl) ⟨808242, by rfl⟩ : syracuseStep 2155313 = 1616485) B1616485
theorem B2155331 : Blo 1435537 2155331 := bstep (se 1 (by rfl) ⟨1616498, by rfl⟩ : syracuseStep 2155331 = 3232997) B3232997
theorem B5456717 : Blo 1435537 5456717 := bstep (se 3 (by rfl) ⟨1023134, by rfl⟩ : syracuseStep 5456717 = 2046269) B2046269
theorem B2155361 : Blo 1435537 2155361 := bstep (se 2 (by rfl) ⟨808260, by rfl⟩ : syracuseStep 2155361 = 1616521) B1616521
theorem B3498851 : Blo 1435537 3498851 := bstep (se 1 (by rfl) ⟨2624138, by rfl⟩ : syracuseStep 3498851 = 5248277) B5248277
theorem B2155379 : Blo 1435537 2155379 := bstep (se 1 (by rfl) ⟨1616534, by rfl⟩ : syracuseStep 2155379 = 3233069) B3233069
theorem B2155409 : Blo 1435537 2155409 := bstep (se 2 (by rfl) ⟨808278, by rfl⟩ : syracuseStep 2155409 = 1616557) B1616557
theorem B2425747 : Blo 1435537 2425747 := bstep (se 1 (by rfl) ⟨1819310, by rfl⟩ : syracuseStep 2425747 = 3638621) B3638621
theorem B2155427 : Blo 1435537 2155427 := bstep (se 1 (by rfl) ⟨1616570, by rfl⟩ : syracuseStep 2155427 = 3233141) B3233141
theorem B2155457 : Blo 1435537 2155457 := bstep (se 2 (by rfl) ⟨808296, by rfl⟩ : syracuseStep 2155457 = 1616593) B1616593
theorem B2155475 : Blo 1435537 2155475 := bstep (se 1 (by rfl) ⟨1616606, by rfl⟩ : syracuseStep 2155475 = 3233213) B3233213
theorem B8176625 : Blo 1435537 8176625 := bstep (se 2 (by rfl) ⟨3066234, by rfl⟩ : syracuseStep 8176625 = 6132469) B6132469
theorem B2155505 : Blo 1435537 2155505 := bstep (se 2 (by rfl) ⟨808314, by rfl⟩ : syracuseStep 2155505 = 1616629) B1616629
theorem B2155523 : Blo 1435537 2155523 := bstep (se 1 (by rfl) ⟨1616642, by rfl⟩ : syracuseStep 2155523 = 3233285) B3233285
theorem B2155553 : Blo 1435537 2155553 := bstep (se 2 (by rfl) ⟨808332, by rfl⟩ : syracuseStep 2155553 = 1616665) B1616665
theorem B2155571 : Blo 1435537 2155571 := bstep (se 1 (by rfl) ⟨1616678, by rfl⟩ : syracuseStep 2155571 = 3233357) B3233357
theorem B2729027 : Blo 1435537 2729027 := bstep (se 1 (by rfl) ⟨2046770, by rfl⟩ : syracuseStep 2729027 = 4093541) B4093541
theorem B4850765 : Blo 1435537 4850765 := bstep (se 3 (by rfl) ⟨909518, by rfl⟩ : syracuseStep 4850765 = 1819037) B1819037
theorem B2155601 : Blo 1435537 2155601 := bstep (se 2 (by rfl) ⟨808350, by rfl⟩ : syracuseStep 2155601 = 1616701) B1616701
theorem B5178467 : Blo 1435537 5178467 := bstep (se 1 (by rfl) ⟨3883850, by rfl⟩ : syracuseStep 5178467 = 7767701) B7767701
theorem B2155619 : Blo 1435537 2155619 := bstep (se 1 (by rfl) ⟨1616714, by rfl⟩ : syracuseStep 2155619 = 3233429) B3233429
theorem B2155649 : Blo 1435537 2155649 := bstep (se 2 (by rfl) ⟨808368, by rfl⟩ : syracuseStep 2155649 = 1616737) B1616737
theorem B4850819 : Blo 1435537 4850819 := bstep (se 1 (by rfl) ⟨3638114, by rfl⟩ : syracuseStep 4850819 = 7276229) B7276229
theorem B2155667 : Blo 1435537 2155667 := bstep (se 1 (by rfl) ⟨1616750, by rfl⟩ : syracuseStep 2155667 = 3233501) B3233501
theorem B2155697 : Blo 1435537 2155697 := bstep (se 2 (by rfl) ⟨808386, by rfl⟩ : syracuseStep 2155697 = 1616773) B1616773
theorem B1615027 : Blo 1435537 1615027 := bstep (se 1 (by rfl) ⟨1211270, by rfl⟩ : syracuseStep 1615027 = 2422541) B2422541
theorem B2155715 : Blo 1435537 2155715 := bstep (se 1 (by rfl) ⟨1616786, by rfl⟩ : syracuseStep 2155715 = 3233573) B3233573
theorem B5825741 : Blo 1435537 5825741 := bstep (se 3 (by rfl) ⟨1092326, by rfl⟩ : syracuseStep 5825741 = 2184653) B2184653
theorem B2155745 : Blo 1435537 2155745 := bstep (se 2 (by rfl) ⟨808404, by rfl⟩ : syracuseStep 2155745 = 1616809) B1616809
theorem B2155763 : Blo 1435537 2155763 := bstep (se 1 (by rfl) ⟨1616822, by rfl⟩ : syracuseStep 2155763 = 3233645) B3233645
theorem B11052301 : Blo 1435537 11052301 := bstep (se 3 (by rfl) ⟨2072306, by rfl⟩ : syracuseStep 11052301 = 4144613) B4144613
theorem B5907725 : Blo 1435537 5907725 := bstep (se 3 (by rfl) ⟨1107698, by rfl⟩ : syracuseStep 5907725 = 2215397) B2215397
theorem B2155793 : Blo 1435537 2155793 := bstep (se 2 (by rfl) ⟨808422, by rfl⟩ : syracuseStep 2155793 = 1616845) B1616845
theorem B2155811 : Blo 1435537 2155811 := bstep (se 1 (by rfl) ⟨1616858, by rfl⟩ : syracuseStep 2155811 = 3233717) B3233717
theorem B2155841 : Blo 1435537 2155841 := bstep (se 2 (by rfl) ⟨808440, by rfl⟩ : syracuseStep 2155841 = 1616881) B1616881
theorem B1615171 : Blo 1435537 1615171 := bstep (se 1 (by rfl) ⟨1211378, by rfl⟩ : syracuseStep 1615171 = 2422757) B2422757
theorem B11060549 : Blo 1435537 11060549 := bstep (se 4 (by rfl) ⟨1036926, by rfl⟩ : syracuseStep 11060549 = 2073853) B2073853
theorem B16368965 : Blo 1435537 16368965 := bstep (se 4 (by rfl) ⟨1534590, by rfl⟩ : syracuseStep 16368965 = 3069181) B3069181
theorem B2155859 : Blo 1435537 2155859 := bstep (se 1 (by rfl) ⟨1616894, by rfl⟩ : syracuseStep 2155859 = 3233789) B3233789
theorem B6137201 : Blo 1435537 6137201 := bstep (se 2 (by rfl) ⟨2301450, by rfl⟩ : syracuseStep 6137201 = 4602901) B4602901
theorem B2155889 : Blo 1435537 2155889 := bstep (se 2 (by rfl) ⟨808458, by rfl⟩ : syracuseStep 2155889 = 1616917) B1616917
theorem B3638641 : Blo 1435537 3638641 := bstep (se 2 (by rfl) ⟨1364490, by rfl⟩ : syracuseStep 3638641 = 2728981) B2728981
theorem B2155907 : Blo 1435537 2155907 := bstep (se 1 (by rfl) ⟨1616930, by rfl⟩ : syracuseStep 2155907 = 3233861) B3233861
theorem B4851089 : Blo 1435537 4851089 := bstep (se 2 (by rfl) ⟨1819158, by rfl⟩ : syracuseStep 4851089 = 3638317) B3638317
theorem B2155937 : Blo 1435537 2155937 := bstep (se 2 (by rfl) ⟨808476, by rfl⟩ : syracuseStep 2155937 = 1616953) B1616953
theorem B2155955 : Blo 1435537 2155955 := bstep (se 1 (by rfl) ⟨1616966, by rfl⟩ : syracuseStep 2155955 = 3233933) B3233933
theorem B3458513 : Blo 1435537 3458513 := bstep (se 2 (by rfl) ⟨1296942, by rfl⟩ : syracuseStep 3458513 = 2593885) B2593885
theorem B2155985 : Blo 1435537 2155985 := bstep (se 2 (by rfl) ⟨808494, by rfl⟩ : syracuseStep 2155985 = 1616989) B1616989
theorem B1615315 : Blo 1435537 1615315 := bstep (se 1 (by rfl) ⟨1211486, by rfl⟩ : syracuseStep 1615315 = 2422973) B2422973
theorem B2156003 : Blo 1435537 2156003 := bstep (se 1 (by rfl) ⟨1617002, by rfl⟩ : syracuseStep 2156003 = 3234005) B3234005
theorem B2156033 : Blo 1435537 2156033 := bstep (se 2 (by rfl) ⟨808512, by rfl⟩ : syracuseStep 2156033 = 1617025) B1617025
theorem B2156051 : Blo 1435537 2156051 := bstep (se 1 (by rfl) ⟨1617038, by rfl⟩ : syracuseStep 2156051 = 3234077) B3234077
theorem B7276067 : Blo 1435537 7276067 := bstep (se 1 (by rfl) ⟨5457050, by rfl⟩ : syracuseStep 7276067 = 10914101) B10914101
theorem B6907427 : Blo 1435537 6907427 := bstep (se 1 (by rfl) ⟨5180570, by rfl⟩ : syracuseStep 6907427 = 10361141) B10361141
theorem B2156081 : Blo 1435537 2156081 := bstep (se 2 (by rfl) ⟨808530, by rfl⟩ : syracuseStep 2156081 = 1617061) B1617061
theorem B2156099 : Blo 1435537 2156099 := bstep (se 1 (by rfl) ⟨1617074, by rfl⟩ : syracuseStep 2156099 = 3234149) B3234149
theorem B1615459 : Blo 1435537 1615459 := bstep (se 1 (by rfl) ⟨1211594, by rfl⟩ : syracuseStep 1615459 = 2423189) B2423189
theorem B2156129 : Blo 1435537 2156129 := bstep (se 2 (by rfl) ⟨808548, by rfl⟩ : syracuseStep 2156129 = 1617097) B1617097
theorem B2156147 : Blo 1435537 2156147 := bstep (se 1 (by rfl) ⟨1617110, by rfl⟩ : syracuseStep 2156147 = 3234221) B3234221
theorem B2156177 : Blo 1435537 2156177 := bstep (se 2 (by rfl) ⟨808566, by rfl⟩ : syracuseStep 2156177 = 1617133) B1617133
theorem B2156195 : Blo 1435537 2156195 := bstep (se 1 (by rfl) ⟨1617146, by rfl⟩ : syracuseStep 2156195 = 3234293) B3234293
theorem B2156225 : Blo 1435537 2156225 := bstep (se 2 (by rfl) ⟨808584, by rfl⟩ : syracuseStep 2156225 = 1617169) B1617169
theorem B3450563 : Blo 1435537 3450563 := bstep (se 1 (by rfl) ⟨2587922, by rfl⟩ : syracuseStep 3450563 = 5175845) B5175845
theorem B2156243 : Blo 1435537 2156243 := bstep (se 1 (by rfl) ⟨1617182, by rfl⟩ : syracuseStep 2156243 = 3234365) B3234365
theorem B52405987 : Blo 1435537 52405987 := bstep (se 1 (by rfl) ⟨39304490, by rfl⟩ : syracuseStep 52405987 = 78608981) B78608981
theorem B2156273 : Blo 1435537 2156273 := bstep (se 2 (by rfl) ⟨808602, by rfl⟩ : syracuseStep 2156273 = 1617205) B1617205
theorem B1615603 : Blo 1435537 1615603 := bstep (se 1 (by rfl) ⟨1211702, by rfl⟩ : syracuseStep 1615603 = 2423405) B2423405
theorem B2156291 : Blo 1435537 2156291 := bstep (se 1 (by rfl) ⟨1617218, by rfl⟩ : syracuseStep 2156291 = 3234437) B3234437
theorem B2590481 : Blo 1435537 2590481 := bstep (se 2 (by rfl) ⟨971430, by rfl⟩ : syracuseStep 2590481 = 1942861) B1942861
theorem B3884867 : Blo 1435537 3884867 := bstep (se 1 (by rfl) ⟨2913650, by rfl⟩ : syracuseStep 3884867 = 5827301) B5827301
theorem B9209699 : Blo 1435537 9209699 := bstep (se 1 (by rfl) ⟨6907274, by rfl⟩ : syracuseStep 9209699 = 13814549) B13814549
theorem B1615747 : Blo 1435537 1615747 := bstep (se 1 (by rfl) ⟨1211810, by rfl⟩ : syracuseStep 1615747 = 2423621) B2423621
theorem B1435539 : Blo 1435537 1435539 := bstep (se 1 (by rfl) ⟨1076654, by rfl⟩ : syracuseStep 1435539 = 2153309) B2153309
theorem B1435555 : Blo 1435537 1435555 := bstep (se 1 (by rfl) ⟨1076666, by rfl⟩ : syracuseStep 1435555 = 2153333) B2153333
theorem B4851629 : Blo 1435537 4851629 := bstep (se 3 (by rfl) ⟨909680, by rfl⟩ : syracuseStep 4851629 = 1819361) B1819361
theorem B1435571 : Blo 1435537 1435571 := bstep (se 1 (by rfl) ⟨1076678, by rfl⟩ : syracuseStep 1435571 = 2153357) B2153357
theorem B1435587 : Blo 1435537 1435587 := bstep (se 1 (by rfl) ⟨1076690, by rfl⟩ : syracuseStep 1435587 = 2153381) B2153381
theorem B8185805 : Blo 1435537 8185805 := bstep (se 3 (by rfl) ⟨1534838, by rfl⟩ : syracuseStep 8185805 = 3069677) B3069677
theorem B1435603 : Blo 1435537 1435603 := bstep (se 1 (by rfl) ⟨1076702, by rfl⟩ : syracuseStep 1435603 = 2153405) B2153405
theorem B1435619 : Blo 1435537 1435619 := bstep (se 1 (by rfl) ⟨1076714, by rfl⟩ : syracuseStep 1435619 = 2153429) B2153429
theorem B4089827 : Blo 1435537 4089827 := bstep (se 1 (by rfl) ⟨3067370, by rfl⟩ : syracuseStep 4089827 = 6134741) B6134741
theorem B4851683 : Blo 1435537 4851683 := bstep (se 1 (by rfl) ⟨3638762, by rfl⟩ : syracuseStep 4851683 = 7277525) B7277525
theorem B1435635 : Blo 1435537 1435635 := bstep (se 1 (by rfl) ⟨1076726, by rfl⟩ : syracuseStep 1435635 = 2153453) B2153453
theorem B1435651 : Blo 1435537 1435651 := bstep (se 1 (by rfl) ⟨1076738, by rfl⟩ : syracuseStep 1435651 = 2153477) B2153477
theorem B1435667 : Blo 1435537 1435667 := bstep (se 1 (by rfl) ⟨1076750, by rfl⟩ : syracuseStep 1435667 = 2153501) B2153501
theorem B1615891 : Blo 1435537 1615891 := bstep (se 1 (by rfl) ⟨1211918, by rfl⟩ : syracuseStep 1615891 = 2423837) B2423837
theorem B1435683 : Blo 1435537 1435683 := bstep (se 1 (by rfl) ⟨1076762, by rfl⟩ : syracuseStep 1435683 = 2153525) B2153525
theorem B1435699 : Blo 1435537 1435699 := bstep (se 1 (by rfl) ⟨1076774, by rfl⟩ : syracuseStep 1435699 = 2153549) B2153549
theorem B1435715 : Blo 1435537 1435715 := bstep (se 1 (by rfl) ⟨1076786, by rfl⟩ : syracuseStep 1435715 = 2153573) B2153573
theorem B1435731 : Blo 1435537 1435731 := bstep (se 1 (by rfl) ⟨1076798, by rfl⟩ : syracuseStep 1435731 = 2153597) B2153597
theorem B1435747 : Blo 1435537 1435747 := bstep (se 1 (by rfl) ⟨1076810, by rfl⟩ : syracuseStep 1435747 = 2153621) B2153621
theorem B3065969 : Blo 1435537 3065969 := bstep (se 2 (by rfl) ⟨1149738, by rfl⟩ : syracuseStep 3065969 = 2299477) B2299477
theorem B1435763 : Blo 1435537 1435763 := bstep (se 1 (by rfl) ⟨1076822, by rfl⟩ : syracuseStep 1435763 = 2153645) B2153645
theorem B3065987 : Blo 1435537 3065987 := bstep (se 1 (by rfl) ⟨2299490, by rfl⟩ : syracuseStep 3065987 = 4598981) B4598981
theorem B1435779 : Blo 1435537 1435779 := bstep (se 1 (by rfl) ⟨1076834, by rfl⟩ : syracuseStep 1435779 = 2153669) B2153669
theorem B1435795 : Blo 1435537 1435795 := bstep (se 1 (by rfl) ⟨1076846, by rfl⟩ : syracuseStep 1435795 = 2153693) B2153693
theorem B1435811 : Blo 1435537 1435811 := bstep (se 1 (by rfl) ⟨1076858, by rfl⟩ : syracuseStep 1435811 = 2153717) B2153717
theorem B1616035 : Blo 1435537 1616035 := bstep (se 1 (by rfl) ⟨1212026, by rfl⟩ : syracuseStep 1616035 = 2424053) B2424053
theorem B1435827 : Blo 1435537 1435827 := bstep (se 1 (by rfl) ⟨1076870, by rfl⟩ : syracuseStep 1435827 = 2153741) B2153741
theorem B1435843 : Blo 1435537 1435843 := bstep (se 1 (by rfl) ⟨1076882, by rfl⟩ : syracuseStep 1435843 = 2153765) B2153765
theorem B1435859 : Blo 1435537 1435859 := bstep (se 1 (by rfl) ⟨1076894, by rfl⟩ : syracuseStep 1435859 = 2153789) B2153789
theorem B1435875 : Blo 1435537 1435875 := bstep (se 1 (by rfl) ⟨1076906, by rfl⟩ : syracuseStep 1435875 = 2153813) B2153813
theorem B1435891 : Blo 1435537 1435891 := bstep (se 1 (by rfl) ⟨1076918, by rfl⟩ : syracuseStep 1435891 = 2153837) B2153837
theorem B1435907 : Blo 1435537 1435907 := bstep (se 1 (by rfl) ⟨1076930, by rfl⟩ : syracuseStep 1435907 = 2153861) B2153861
theorem B6138125 : Blo 1435537 6138125 := bstep (se 3 (by rfl) ⟨1150898, by rfl⟩ : syracuseStep 6138125 = 2301797) B2301797
theorem B1435923 : Blo 1435537 1435923 := bstep (se 1 (by rfl) ⟨1076942, by rfl⟩ : syracuseStep 1435923 = 2153885) B2153885
theorem B1435939 : Blo 1435537 1435939 := bstep (se 1 (by rfl) ⟨1076954, by rfl⟩ : syracuseStep 1435939 = 2153909) B2153909
theorem B1435955 : Blo 1435537 1435955 := bstep (se 1 (by rfl) ⟨1076966, by rfl⟩ : syracuseStep 1435955 = 2153933) B2153933
theorem B1616179 : Blo 1435537 1616179 := bstep (se 1 (by rfl) ⟨1212134, by rfl⟩ : syracuseStep 1616179 = 2424269) B2424269
theorem B1435971 : Blo 1435537 1435971 := bstep (se 1 (by rfl) ⟨1076978, by rfl⟩ : syracuseStep 1435971 = 2153957) B2153957
theorem B7276877 : Blo 1435537 7276877 := bstep (se 3 (by rfl) ⟨1364414, by rfl⟩ : syracuseStep 7276877 = 2728829) B2728829
theorem B1435987 : Blo 1435537 1435987 := bstep (se 1 (by rfl) ⟨1076990, by rfl⟩ : syracuseStep 1435987 = 2153981) B2153981
theorem B1436003 : Blo 1435537 1436003 := bstep (se 1 (by rfl) ⟨1077002, by rfl⟩ : syracuseStep 1436003 = 2154005) B2154005
theorem B1436019 : Blo 1435537 1436019 := bstep (se 1 (by rfl) ⟨1077014, by rfl⟩ : syracuseStep 1436019 = 2154029) B2154029
theorem B1436035 : Blo 1435537 1436035 := bstep (se 1 (by rfl) ⟨1077026, by rfl⟩ : syracuseStep 1436035 = 2154053) B2154053
theorem B1436051 : Blo 1435537 1436051 := bstep (se 1 (by rfl) ⟨1077038, by rfl⟩ : syracuseStep 1436051 = 2154077) B2154077
theorem B8178083 : Blo 1435537 8178083 := bstep (se 1 (by rfl) ⟨6133562, by rfl⟩ : syracuseStep 8178083 = 12267125) B12267125
theorem B1436067 : Blo 1435537 1436067 := bstep (se 1 (by rfl) ⟨1077050, by rfl⟩ : syracuseStep 1436067 = 2154101) B2154101
theorem B1436083 : Blo 1435537 1436083 := bstep (se 1 (by rfl) ⟨1077062, by rfl⟩ : syracuseStep 1436083 = 2154125) B2154125
theorem B1436099 : Blo 1435537 1436099 := bstep (se 1 (by rfl) ⟨1077074, by rfl⟩ : syracuseStep 1436099 = 2154149) B2154149
theorem B1616323 : Blo 1435537 1616323 := bstep (se 1 (by rfl) ⟨1212242, by rfl⟩ : syracuseStep 1616323 = 2424485) B2424485
theorem B1534403 : Blo 1435537 1534403 := bstep (se 1 (by rfl) ⟨1150802, by rfl⟩ : syracuseStep 1534403 = 2301605) B2301605
theorem B1436115 : Blo 1435537 1436115 := bstep (se 1 (by rfl) ⟨1077086, by rfl⟩ : syracuseStep 1436115 = 2154173) B2154173
theorem B1436131 : Blo 1435537 1436131 := bstep (se 1 (by rfl) ⟨1077098, by rfl⟩ : syracuseStep 1436131 = 2154197) B2154197
theorem B1436147 : Blo 1435537 1436147 := bstep (se 1 (by rfl) ⟨1077110, by rfl⟩ : syracuseStep 1436147 = 2154221) B2154221
theorem B1436163 : Blo 1435537 1436163 := bstep (se 1 (by rfl) ⟨1077122, by rfl⟩ : syracuseStep 1436163 = 2154245) B2154245
theorem B3230225 : Blo 1435537 3230225 := bstep (se 2 (by rfl) ⟨1211334, by rfl⟩ : syracuseStep 3230225 = 2422669) B2422669
theorem B1436179 : Blo 1435537 1436179 := bstep (se 1 (by rfl) ⟨1077134, by rfl⟩ : syracuseStep 1436179 = 2154269) B2154269
theorem B3230243 : Blo 1435537 3230243 := bstep (se 1 (by rfl) ⟨2422682, by rfl⟩ : syracuseStep 3230243 = 4845365) B4845365
theorem B1436195 : Blo 1435537 1436195 := bstep (se 1 (by rfl) ⟨1077146, by rfl⟩ : syracuseStep 1436195 = 2154293) B2154293
theorem B1436211 : Blo 1435537 1436211 := bstep (se 1 (by rfl) ⟨1077158, by rfl⟩ : syracuseStep 1436211 = 2154317) B2154317
theorem B1436227 : Blo 1435537 1436227 := bstep (se 1 (by rfl) ⟨1077170, by rfl⟩ : syracuseStep 1436227 = 2154341) B2154341
theorem B1436243 : Blo 1435537 1436243 := bstep (se 1 (by rfl) ⟨1077182, by rfl⟩ : syracuseStep 1436243 = 2154365) B2154365
theorem B1616467 : Blo 1435537 1616467 := bstep (se 1 (by rfl) ⟨1212350, by rfl⟩ : syracuseStep 1616467 = 2424701) B2424701
theorem B1436259 : Blo 1435537 1436259 := bstep (se 1 (by rfl) ⟨1077194, by rfl⟩ : syracuseStep 1436259 = 2154389) B2154389
theorem B1436275 : Blo 1435537 1436275 := bstep (se 1 (by rfl) ⟨1077206, by rfl⟩ : syracuseStep 1436275 = 2154413) B2154413
theorem B1436291 : Blo 1435537 1436291 := bstep (se 1 (by rfl) ⟨1077218, by rfl⟩ : syracuseStep 1436291 = 2154437) B2154437
theorem B1436307 : Blo 1435537 1436307 := bstep (se 1 (by rfl) ⟨1077230, by rfl⟩ : syracuseStep 1436307 = 2154461) B2154461
theorem B1436323 : Blo 1435537 1436323 := bstep (se 1 (by rfl) ⟨1077242, by rfl⟩ : syracuseStep 1436323 = 2154485) B2154485
theorem B1436339 : Blo 1435537 1436339 := bstep (se 1 (by rfl) ⟨1077254, by rfl⟩ : syracuseStep 1436339 = 2154509) B2154509
theorem B1436355 : Blo 1435537 1436355 := bstep (se 1 (by rfl) ⟨1077266, by rfl⟩ : syracuseStep 1436355 = 2154533) B2154533
theorem B1436371 : Blo 1435537 1436371 := bstep (se 1 (by rfl) ⟨1077278, by rfl⟩ : syracuseStep 1436371 = 2154557) B2154557
theorem B1436387 : Blo 1435537 1436387 := bstep (se 1 (by rfl) ⟨1077290, by rfl⟩ : syracuseStep 1436387 = 2154581) B2154581
theorem B1616611 : Blo 1435537 1616611 := bstep (se 1 (by rfl) ⟨1212458, by rfl⟩ : syracuseStep 1616611 = 2424917) B2424917
theorem B1436403 : Blo 1435537 1436403 := bstep (se 1 (by rfl) ⟨1077302, by rfl⟩ : syracuseStep 1436403 = 2154605) B2154605
theorem B1436419 : Blo 1435537 1436419 := bstep (se 1 (by rfl) ⟨1077314, by rfl⟩ : syracuseStep 1436419 = 2154629) B2154629
theorem B1436435 : Blo 1435537 1436435 := bstep (se 1 (by rfl) ⟨1077326, by rfl⟩ : syracuseStep 1436435 = 2154653) B2154653
theorem B1436451 : Blo 1435537 1436451 := bstep (se 1 (by rfl) ⟨1077338, by rfl⟩ : syracuseStep 1436451 = 2154677) B2154677
theorem B3230513 : Blo 1435537 3230513 := bstep (se 2 (by rfl) ⟨1211442, by rfl⟩ : syracuseStep 3230513 = 2422885) B2422885
theorem B3451697 : Blo 1435537 3451697 := bstep (se 2 (by rfl) ⟨1294386, by rfl⟩ : syracuseStep 3451697 = 2588773) B2588773
theorem B1436467 : Blo 1435537 1436467 := bstep (se 1 (by rfl) ⟨1077350, by rfl⟩ : syracuseStep 1436467 = 2154701) B2154701
theorem B3230531 : Blo 1435537 3230531 := bstep (se 1 (by rfl) ⟨2422898, by rfl⟩ : syracuseStep 3230531 = 4845797) B4845797
theorem B1436483 : Blo 1435537 1436483 := bstep (se 1 (by rfl) ⟨1077362, by rfl⟩ : syracuseStep 1436483 = 2154725) B2154725
theorem B1436499 : Blo 1435537 1436499 := bstep (se 1 (by rfl) ⟨1077374, by rfl⟩ : syracuseStep 1436499 = 2154749) B2154749
theorem B1436515 : Blo 1435537 1436515 := bstep (se 1 (by rfl) ⟨1077386, by rfl⟩ : syracuseStep 1436515 = 2154773) B2154773
theorem B1436531 : Blo 1435537 1436531 := bstep (se 1 (by rfl) ⟨1077398, by rfl⟩ : syracuseStep 1436531 = 2154797) B2154797
theorem B1616755 : Blo 1435537 1616755 := bstep (se 1 (by rfl) ⟨1212566, by rfl⟩ : syracuseStep 1616755 = 2425133) B2425133
theorem B1436547 : Blo 1435537 1436547 := bstep (se 1 (by rfl) ⟨1077410, by rfl⟩ : syracuseStep 1436547 = 2154821) B2154821
theorem B1436563 : Blo 1435537 1436563 := bstep (se 1 (by rfl) ⟨1077422, by rfl⟩ : syracuseStep 1436563 = 2154845) B2154845
theorem B1436579 : Blo 1435537 1436579 := bstep (se 1 (by rfl) ⟨1077434, by rfl⟩ : syracuseStep 1436579 = 2154869) B2154869
theorem B1436595 : Blo 1435537 1436595 := bstep (se 1 (by rfl) ⟨1077446, by rfl⟩ : syracuseStep 1436595 = 2154893) B2154893
theorem B1436611 : Blo 1435537 1436611 := bstep (se 1 (by rfl) ⟨1077458, by rfl⟩ : syracuseStep 1436611 = 2154917) B2154917
theorem B1436627 : Blo 1435537 1436627 := bstep (se 1 (by rfl) ⟨1077470, by rfl⟩ : syracuseStep 1436627 = 2154941) B2154941
theorem B1436643 : Blo 1435537 1436643 := bstep (se 1 (by rfl) ⟨1077482, by rfl⟩ : syracuseStep 1436643 = 2154965) B2154965
theorem B1436659 : Blo 1435537 1436659 := bstep (se 1 (by rfl) ⟨1077494, by rfl⟩ : syracuseStep 1436659 = 2154989) B2154989
theorem B1436675 : Blo 1435537 1436675 := bstep (se 1 (by rfl) ⟨1077506, by rfl⟩ : syracuseStep 1436675 = 2155013) B2155013
theorem B1616899 : Blo 1435537 1616899 := bstep (se 1 (by rfl) ⟨1212674, by rfl⟩ : syracuseStep 1616899 = 2425349) B2425349
theorem B1436691 : Blo 1435537 1436691 := bstep (se 1 (by rfl) ⟨1077518, by rfl⟩ : syracuseStep 1436691 = 2155037) B2155037
theorem B1436707 : Blo 1435537 1436707 := bstep (se 1 (by rfl) ⟨1077530, by rfl⟩ : syracuseStep 1436707 = 2155061) B2155061
theorem B7269425 : Blo 1435537 7269425 := bstep (se 2 (by rfl) ⟨2726034, by rfl⟩ : syracuseStep 7269425 = 5452069) B5452069
theorem B1436723 : Blo 1435537 1436723 := bstep (se 1 (by rfl) ⟨1077542, by rfl⟩ : syracuseStep 1436723 = 2155085) B2155085
theorem B1436739 : Blo 1435537 1436739 := bstep (se 1 (by rfl) ⟨1077554, by rfl⟩ : syracuseStep 1436739 = 2155109) B2155109
theorem B3230801 : Blo 1435537 3230801 := bstep (se 2 (by rfl) ⟨1211550, by rfl⟩ : syracuseStep 3230801 = 2423101) B2423101
theorem B1436755 : Blo 1435537 1436755 := bstep (se 1 (by rfl) ⟨1077566, by rfl⟩ : syracuseStep 1436755 = 2155133) B2155133
theorem B3230819 : Blo 1435537 3230819 := bstep (se 1 (by rfl) ⟨2423114, by rfl⟩ : syracuseStep 3230819 = 4846229) B4846229
theorem B1436771 : Blo 1435537 1436771 := bstep (se 1 (by rfl) ⟨1077578, by rfl⟩ : syracuseStep 1436771 = 2155157) B2155157
theorem B1436787 : Blo 1435537 1436787 := bstep (se 1 (by rfl) ⟨1077590, by rfl⟩ : syracuseStep 1436787 = 2155181) B2155181
theorem B1436803 : Blo 1435537 1436803 := bstep (se 1 (by rfl) ⟨1077602, by rfl⟩ : syracuseStep 1436803 = 2155205) B2155205
theorem B1436819 : Blo 1435537 1436819 := bstep (se 1 (by rfl) ⟨1077614, by rfl⟩ : syracuseStep 1436819 = 2155229) B2155229
theorem B1617043 : Blo 1435537 1617043 := bstep (se 1 (by rfl) ⟨1212782, by rfl⟩ : syracuseStep 1617043 = 2425565) B2425565
theorem B5450915 : Blo 1435537 5450915 := bstep (se 1 (by rfl) ⟨4088186, by rfl⟩ : syracuseStep 5450915 = 8176373) B8176373
theorem B1436835 : Blo 1435537 1436835 := bstep (se 1 (by rfl) ⟨1077626, by rfl⟩ : syracuseStep 1436835 = 2155253) B2155253
theorem B4091057 : Blo 1435537 4091057 := bstep (se 2 (by rfl) ⟨1534146, by rfl⟩ : syracuseStep 4091057 = 3068293) B3068293
theorem B1436851 : Blo 1435537 1436851 := bstep (se 1 (by rfl) ⟨1077638, by rfl⟩ : syracuseStep 1436851 = 2155277) B2155277
theorem B1436867 : Blo 1435537 1436867 := bstep (se 1 (by rfl) ⟨1077650, by rfl⟩ : syracuseStep 1436867 = 2155301) B2155301
theorem B1436883 : Blo 1435537 1436883 := bstep (se 1 (by rfl) ⟨1077662, by rfl⟩ : syracuseStep 1436883 = 2155325) B2155325
theorem B1436899 : Blo 1435537 1436899 := bstep (se 1 (by rfl) ⟨1077674, by rfl⟩ : syracuseStep 1436899 = 2155349) B2155349
theorem B1436915 : Blo 1435537 1436915 := bstep (se 1 (by rfl) ⟨1077686, by rfl⟩ : syracuseStep 1436915 = 2155373) B2155373
theorem B1436931 : Blo 1435537 1436931 := bstep (se 1 (by rfl) ⟨1077698, by rfl⟩ : syracuseStep 1436931 = 2155397) B2155397
theorem B1436947 : Blo 1435537 1436947 := bstep (se 1 (by rfl) ⟨1077710, by rfl⟩ : syracuseStep 1436947 = 2155421) B2155421
theorem B1436963 : Blo 1435537 1436963 := bstep (se 1 (by rfl) ⟨1077722, by rfl⟩ : syracuseStep 1436963 = 2155445) B2155445
theorem B1617187 : Blo 1435537 1617187 := bstep (se 1 (by rfl) ⟨1212890, by rfl⟩ : syracuseStep 1617187 = 2425781) B2425781
theorem B1436979 : Blo 1435537 1436979 := bstep (se 1 (by rfl) ⟨1077734, by rfl⟩ : syracuseStep 1436979 = 2155469) B2155469
theorem B1436995 : Blo 1435537 1436995 := bstep (se 1 (by rfl) ⟨1077746, by rfl⟩ : syracuseStep 1436995 = 2155493) B2155493
theorem B3067217 : Blo 1435537 3067217 := bstep (se 2 (by rfl) ⟨1150206, by rfl⟩ : syracuseStep 3067217 = 2300413) B2300413
theorem B1437011 : Blo 1435537 1437011 := bstep (se 1 (by rfl) ⟨1077758, by rfl⟩ : syracuseStep 1437011 = 2155517) B2155517
theorem B1437027 : Blo 1435537 1437027 := bstep (se 1 (by rfl) ⟨1077770, by rfl⟩ : syracuseStep 1437027 = 2155541) B2155541
theorem B3231089 : Blo 1435537 3231089 := bstep (se 2 (by rfl) ⟨1211658, by rfl⟩ : syracuseStep 3231089 = 2423317) B2423317
theorem B1437043 : Blo 1435537 1437043 := bstep (se 1 (by rfl) ⟨1077782, by rfl⟩ : syracuseStep 1437043 = 2155565) B2155565
theorem B3231107 : Blo 1435537 3231107 := bstep (se 1 (by rfl) ⟨2423330, by rfl⟩ : syracuseStep 3231107 = 4846661) B4846661
theorem B1437059 : Blo 1435537 1437059 := bstep (se 1 (by rfl) ⟨1077794, by rfl⟩ : syracuseStep 1437059 = 2155589) B2155589
theorem B1437075 : Blo 1435537 1437075 := bstep (se 1 (by rfl) ⟨1077806, by rfl⟩ : syracuseStep 1437075 = 2155613) B2155613
theorem B1437091 : Blo 1435537 1437091 := bstep (se 1 (by rfl) ⟨1077818, by rfl⟩ : syracuseStep 1437091 = 2155637) B2155637
theorem B1437107 : Blo 1435537 1437107 := bstep (se 1 (by rfl) ⟨1077830, by rfl⟩ : syracuseStep 1437107 = 2155661) B2155661
theorem B1437123 : Blo 1435537 1437123 := bstep (se 1 (by rfl) ⟨1077842, by rfl⟩ : syracuseStep 1437123 = 2155685) B2155685
theorem B2911697 : Blo 1435537 2911697 := bstep (se 2 (by rfl) ⟨1091886, by rfl⟩ : syracuseStep 2911697 = 2183773) B2183773
theorem B1437139 : Blo 1435537 1437139 := bstep (se 1 (by rfl) ⟨1077854, by rfl⟩ : syracuseStep 1437139 = 2155709) B2155709
theorem B1437155 : Blo 1435537 1437155 := bstep (se 1 (by rfl) ⟨1077866, by rfl⟩ : syracuseStep 1437155 = 2155733) B2155733
theorem B4845041 : Blo 1435537 4845041 := bstep (se 2 (by rfl) ⟨1816890, by rfl⟩ : syracuseStep 4845041 = 3633781) B3633781
theorem B1437171 : Blo 1435537 1437171 := bstep (se 1 (by rfl) ⟨1077878, by rfl⟩ : syracuseStep 1437171 = 2155757) B2155757
theorem B1437187 : Blo 1435537 1437187 := bstep (se 1 (by rfl) ⟨1077890, by rfl⟩ : syracuseStep 1437187 = 2155781) B2155781
theorem B1437203 : Blo 1435537 1437203 := bstep (se 1 (by rfl) ⟨1077902, by rfl⟩ : syracuseStep 1437203 = 2155805) B2155805
theorem B1437219 : Blo 1435537 1437219 := bstep (se 1 (by rfl) ⟨1077914, by rfl⟩ : syracuseStep 1437219 = 2155829) B2155829
theorem B3452465 : Blo 1435537 3452465 := bstep (se 2 (by rfl) ⟨1294674, by rfl⟩ : syracuseStep 3452465 = 2589349) B2589349
theorem B1437235 : Blo 1435537 1437235 := bstep (se 1 (by rfl) ⟨1077926, by rfl⟩ : syracuseStep 1437235 = 2155853) B2155853
theorem B1437251 : Blo 1435537 1437251 := bstep (se 1 (by rfl) ⟨1077938, by rfl⟩ : syracuseStep 1437251 = 2155877) B2155877
theorem B1437267 : Blo 1435537 1437267 := bstep (se 1 (by rfl) ⟨1077950, by rfl⟩ : syracuseStep 1437267 = 2155901) B2155901
theorem B1437283 : Blo 1435537 1437283 := bstep (se 1 (by rfl) ⟨1077962, by rfl⟩ : syracuseStep 1437283 = 2155925) B2155925
theorem B1437299 : Blo 1435537 1437299 := bstep (se 1 (by rfl) ⟨1077974, by rfl⟩ : syracuseStep 1437299 = 2155949) B2155949
theorem B1437315 : Blo 1435537 1437315 := bstep (se 1 (by rfl) ⟨1077986, by rfl⟩ : syracuseStep 1437315 = 2155973) B2155973
theorem B9203341 : Blo 1435537 9203341 := bstep (se 3 (by rfl) ⟨1725626, by rfl⟩ : syracuseStep 9203341 = 3451253) B3451253
theorem B3231377 : Blo 1435537 3231377 := bstep (se 2 (by rfl) ⟨1211766, by rfl⟩ : syracuseStep 3231377 = 2423533) B2423533
theorem B1437331 : Blo 1435537 1437331 := bstep (se 1 (by rfl) ⟨1077998, by rfl⟩ : syracuseStep 1437331 = 2155997) B2155997
theorem B3231395 : Blo 1435537 3231395 := bstep (se 1 (by rfl) ⟨2423546, by rfl⟩ : syracuseStep 3231395 = 4847093) B4847093
theorem B1437347 : Blo 1435537 1437347 := bstep (se 1 (by rfl) ⟨1078010, by rfl⟩ : syracuseStep 1437347 = 2156021) B2156021
theorem B1437363 : Blo 1435537 1437363 := bstep (se 1 (by rfl) ⟨1078022, by rfl⟩ : syracuseStep 1437363 = 2156045) B2156045
theorem B1437379 : Blo 1435537 1437379 := bstep (se 1 (by rfl) ⟨1078034, by rfl⟩ : syracuseStep 1437379 = 2156069) B2156069
theorem B1437395 : Blo 1435537 1437395 := bstep (se 1 (by rfl) ⟨1078046, by rfl⟩ : syracuseStep 1437395 = 2156093) B2156093
theorem B1437411 : Blo 1435537 1437411 := bstep (se 1 (by rfl) ⟨1078058, by rfl⟩ : syracuseStep 1437411 = 2156117) B2156117
theorem B1437427 : Blo 1435537 1437427 := bstep (se 1 (by rfl) ⟨1078070, by rfl⟩ : syracuseStep 1437427 = 2156141) B2156141
theorem B1437443 : Blo 1435537 1437443 := bstep (se 1 (by rfl) ⟨1078082, by rfl⟩ : syracuseStep 1437443 = 2156165) B2156165
theorem B1437459 : Blo 1435537 1437459 := bstep (se 1 (by rfl) ⟨1078094, by rfl⟩ : syracuseStep 1437459 = 2156189) B2156189
theorem B1437475 : Blo 1435537 1437475 := bstep (se 1 (by rfl) ⟨1078106, by rfl⟩ : syracuseStep 1437475 = 2156213) B2156213
theorem B5451569 : Blo 1435537 5451569 := bstep (se 2 (by rfl) ⟨2044338, by rfl⟩ : syracuseStep 5451569 = 4088677) B4088677
theorem B1437491 : Blo 1435537 1437491 := bstep (se 1 (by rfl) ⟨1078118, by rfl⟩ : syracuseStep 1437491 = 2156237) B2156237
theorem B1437507 : Blo 1435537 1437507 := bstep (se 1 (by rfl) ⟨1078130, by rfl⟩ : syracuseStep 1437507 = 2156261) B2156261
theorem B1437523 : Blo 1435537 1437523 := bstep (se 1 (by rfl) ⟨1078142, by rfl⟩ : syracuseStep 1437523 = 2156285) B2156285
theorem B18665315 : Blo 1435537 18665315 := bstep (se 1 (by rfl) ⟨13998986, by rfl⟩ : syracuseStep 18665315 = 27997973) B27997973
theorem B6221681 : Blo 1435537 6221681 := bstep (se 2 (by rfl) ⟨2333130, by rfl⟩ : syracuseStep 6221681 = 4666261) B4666261
theorem B3231665 : Blo 1435537 3231665 := bstep (se 2 (by rfl) ⟨1211874, by rfl⟩ : syracuseStep 3231665 = 2423749) B2423749
theorem B3231683 : Blo 1435537 3231683 := bstep (se 1 (by rfl) ⟨2423762, by rfl⟩ : syracuseStep 3231683 = 4847525) B4847525
theorem B4730833 : Blo 1435537 4730833 := bstep (se 2 (by rfl) ⟨1774062, by rfl⟩ : syracuseStep 4730833 = 3548125) B3548125
theorem B4845581 : Blo 1435537 4845581 := bstep (se 3 (by rfl) ⟨908546, by rfl⟩ : syracuseStep 4845581 = 1817093) B1817093
theorem B4845635 : Blo 1435537 4845635 := bstep (se 1 (by rfl) ⟨3634226, by rfl⟩ : syracuseStep 4845635 = 7268453) B7268453
theorem B3231953 : Blo 1435537 3231953 := bstep (se 2 (by rfl) ⟨1211982, by rfl⟩ : syracuseStep 3231953 = 2423965) B2423965
theorem B3231971 : Blo 1435537 3231971 := bstep (se 1 (by rfl) ⟨2423978, by rfl⟩ : syracuseStep 3231971 = 4847957) B4847957
theorem B8179973 : Blo 1435537 8179973 := bstep (se 4 (by rfl) ⟨766872, by rfl⟩ : syracuseStep 8179973 = 1533745) B1533745
theorem B4600081 : Blo 1435537 4600081 := bstep (se 2 (by rfl) ⟨1725030, by rfl⟩ : syracuseStep 4600081 = 3450061) B3450061
theorem B4845905 : Blo 1435537 4845905 := bstep (se 2 (by rfl) ⟨1817214, by rfl⟩ : syracuseStep 4845905 = 3634429) B3634429
theorem B7270883 : Blo 1435537 7270883 := bstep (se 1 (by rfl) ⟨5453162, by rfl⟩ : syracuseStep 7270883 = 10906325) B10906325
theorem B3232241 : Blo 1435537 3232241 := bstep (se 2 (by rfl) ⟨1212090, by rfl⟩ : syracuseStep 3232241 = 2424181) B2424181
theorem B3232259 : Blo 1435537 3232259 := bstep (se 1 (by rfl) ⟨2424194, by rfl⟩ : syracuseStep 3232259 = 4848389) B4848389
theorem B3109393 : Blo 1435537 3109393 := bstep (se 2 (by rfl) ⟨1166022, by rfl⟩ : syracuseStep 3109393 = 2332045) B2332045
theorem B2044435 : Blo 1435537 2044435 := bstep (se 1 (by rfl) ⟨1533326, by rfl⟩ : syracuseStep 2044435 = 3066653) B3066653
theorem B17478197 : Blo 1435537 17478197 := bstep (se 5 (by rfl) ⟨819290, by rfl⟩ : syracuseStep 17478197 = 1638581) B1638581
theorem B3633731 : Blo 1435537 3633731 := bstep (se 1 (by rfl) ⟨2725298, by rfl⟩ : syracuseStep 3633731 = 5450597) B5450597
theorem B3453521 : Blo 1435537 3453521 := bstep (se 2 (by rfl) ⟨1295070, by rfl⟩ : syracuseStep 3453521 = 2590141) B2590141
theorem B4092515 : Blo 1435537 4092515 := bstep (se 1 (by rfl) ⟨3069386, by rfl⟩ : syracuseStep 4092515 = 6138773) B6138773
theorem B10359409 : Blo 1435537 10359409 := bstep (se 2 (by rfl) ⟨3884778, by rfl⟩ : syracuseStep 10359409 = 7769557) B7769557
theorem B2765507 : Blo 1435537 2765507 := bstep (se 1 (by rfl) ⟨2074130, by rfl⟩ : syracuseStep 2765507 = 4148261) B4148261
theorem B2765539 : Blo 1435537 2765539 := bstep (se 1 (by rfl) ⟨2074154, by rfl⟩ : syracuseStep 2765539 = 4148309) B4148309
theorem B3633923 : Blo 1435537 3633923 := bstep (se 1 (by rfl) ⟨2725442, by rfl⟩ : syracuseStep 3633923 = 5450885) B5450885
theorem B3232529 : Blo 1435537 3232529 := bstep (se 2 (by rfl) ⟨1212198, by rfl⟩ : syracuseStep 3232529 = 2424397) B2424397
theorem B3232547 : Blo 1435537 3232547 := bstep (se 1 (by rfl) ⟨2424410, by rfl⟩ : syracuseStep 3232547 = 4848821) B4848821
theorem B2913059 : Blo 1435537 2913059 := bstep (se 1 (by rfl) ⟨2184794, by rfl⟩ : syracuseStep 2913059 = 4369589) B4369589
theorem B3068771 : Blo 1435537 3068771 := bstep (se 1 (by rfl) ⟨2301578, by rfl⟩ : syracuseStep 3068771 = 4603157) B4603157
theorem B4846445 : Blo 1435537 4846445 := bstep (se 3 (by rfl) ⟨908708, by rfl⟩ : syracuseStep 4846445 = 1817417) B1817417
theorem B4846499 : Blo 1435537 4846499 := bstep (se 1 (by rfl) ⟨3634874, by rfl⟩ : syracuseStep 4846499 = 7269749) B7269749
theorem B2184179 : Blo 1435537 2184179 := bstep (se 1 (by rfl) ⟨1638134, by rfl⟩ : syracuseStep 2184179 = 3276269) B3276269
theorem B3232817 : Blo 1435537 3232817 := bstep (se 2 (by rfl) ⟨1212306, by rfl⟩ : syracuseStep 3232817 = 2424613) B2424613
theorem B3232835 : Blo 1435537 3232835 := bstep (se 1 (by rfl) ⟨2424626, by rfl⟩ : syracuseStep 3232835 = 4849253) B4849253
theorem B2364547 : Blo 1435537 2364547 := bstep (se 1 (by rfl) ⟨1773410, by rfl⟩ : syracuseStep 2364547 = 3546821) B3546821
theorem B4846769 : Blo 1435537 4846769 := bstep (se 2 (by rfl) ⟨1817538, by rfl⟩ : syracuseStep 4846769 = 3635077) B3635077
theorem B2766001 : Blo 1435537 2766001 := bstep (se 2 (by rfl) ⟨1037250, by rfl⟩ : syracuseStep 2766001 = 2074501) B2074501
theorem B5453027 : Blo 1435537 5453027 := bstep (se 1 (by rfl) ⟨4089770, by rfl⟩ : syracuseStep 5453027 = 8179541) B8179541
theorem B5453041 : Blo 1435537 5453041 := bstep (se 2 (by rfl) ⟨2044890, by rfl⟩ : syracuseStep 5453041 = 4089781) B4089781
theorem B7271693 : Blo 1435537 7271693 := bstep (se 3 (by rfl) ⟨1363442, by rfl⟩ : syracuseStep 7271693 = 2726885) B2726885
theorem B3233105 : Blo 1435537 3233105 := bstep (se 2 (by rfl) ⟨1212414, by rfl⟩ : syracuseStep 3233105 = 2424829) B2424829
theorem B3233123 : Blo 1435537 3233123 := bstep (se 1 (by rfl) ⟨2424842, by rfl⟩ : syracuseStep 3233123 = 4849685) B4849685
theorem B4093325 : Blo 1435537 4093325 := bstep (se 3 (by rfl) ⟨767498, by rfl⟩ : syracuseStep 4093325 = 1534997) B1534997
theorem B4601261 : Blo 1435537 4601261 := bstep (se 3 (by rfl) ⟨862736, by rfl⟩ : syracuseStep 4601261 = 1725473) B1725473
theorem B4093517 : Blo 1435537 4093517 := bstep (se 3 (by rfl) ⟨767534, by rfl⟩ : syracuseStep 4093517 = 1535069) B1535069
theorem B8738417 : Blo 1435537 8738417 := bstep (se 2 (by rfl) ⟨3276906, by rfl⟩ : syracuseStep 8738417 = 6553813) B6553813
theorem B3233393 : Blo 1435537 3233393 := bstep (se 2 (by rfl) ⟨1212522, by rfl⟩ : syracuseStep 3233393 = 2425045) B2425045
theorem B2045569 : Blo 1435537 2045569 := bstep (se 2 (by rfl) ⟨767088, by rfl⟩ : syracuseStep 2045569 = 1534177) B1534177
theorem B3233411 : Blo 1435537 3233411 := bstep (se 1 (by rfl) ⟨2425058, by rfl⟩ : syracuseStep 3233411 = 4850117) B4850117
theorem B2332307 : Blo 1435537 2332307 := bstep (se 1 (by rfl) ⟨1749230, by rfl⟩ : syracuseStep 2332307 = 3498461) B3498461
theorem B3634865 : Blo 1435537 3634865 := bstep (se 2 (by rfl) ⟨1363074, by rfl⟩ : syracuseStep 3634865 = 2726149) B2726149
theorem B4847309 : Blo 1435537 4847309 := bstep (se 3 (by rfl) ⟨908870, by rfl⟩ : syracuseStep 4847309 = 1817741) B1817741
theorem B2045665 : Blo 1435537 2045665 := bstep (se 2 (by rfl) ⟨767124, by rfl⟩ : syracuseStep 2045665 = 1534249) B1534249
theorem B3634915 : Blo 1435537 3634915 := bstep (se 1 (by rfl) ⟨2726186, by rfl⟩ : syracuseStep 3634915 = 5452373) B5452373
theorem B4847363 : Blo 1435537 4847363 := bstep (se 1 (by rfl) ⟨3635522, by rfl⟩ : syracuseStep 4847363 = 7271045) B7271045
theorem B2422561 : Blo 1435537 2422561 := bstep (se 2 (by rfl) ⟨908460, by rfl⟩ : syracuseStep 2422561 = 1816921) B1816921
theorem B2422595 : Blo 1435537 2422595 := bstep (se 1 (by rfl) ⟨1816946, by rfl⟩ : syracuseStep 2422595 = 3633893) B3633893
theorem B8083277 : Blo 1435537 8083277 := bstep (se 3 (by rfl) ⟨1515614, by rfl⟩ : syracuseStep 8083277 = 3031229) B3031229
theorem B2299747 : Blo 1435537 2299747 := bstep (se 1 (by rfl) ⟨1724810, by rfl⟩ : syracuseStep 2299747 = 3449621) B3449621
theorem B3635057 : Blo 1435537 3635057 := bstep (se 2 (by rfl) ⟨1363146, by rfl⟩ : syracuseStep 3635057 = 2726293) B2726293
theorem B74618765 : Blo 1435537 74618765 := bstep (se 3 (by rfl) ⟨13991018, by rfl⟩ : syracuseStep 74618765 = 27982037) B27982037
theorem B3233681 : Blo 1435537 3233681 := bstep (se 2 (by rfl) ⟨1212630, by rfl⟩ : syracuseStep 3233681 = 2425261) B2425261
theorem B3233699 : Blo 1435537 3233699 := bstep (se 1 (by rfl) ⟨2425274, by rfl⟩ : syracuseStep 3233699 = 4850549) B4850549
theorem B3880877 : Blo 1435537 3880877 := bstep (se 3 (by rfl) ⟨727664, by rfl⟩ : syracuseStep 3880877 = 1455329) B1455329
theorem B16357301 : Blo 1435537 16357301 := bstep (se 5 (by rfl) ⟨766748, by rfl⟩ : syracuseStep 16357301 = 1533497) B1533497
theorem B2422723 : Blo 1435537 2422723 := bstep (se 1 (by rfl) ⟨1817042, by rfl⟩ : syracuseStep 2422723 = 3634085) B3634085
theorem B3880909 : Blo 1435537 3880909 := bstep (se 3 (by rfl) ⟨727670, by rfl⟩ : syracuseStep 3880909 = 1455341) B1455341
theorem B3880973 : Blo 1435537 3880973 := bstep (se 3 (by rfl) ⟨727682, by rfl⟩ : syracuseStep 3880973 = 1455365) B1455365
theorem B4847633 : Blo 1435537 4847633 := bstep (se 2 (by rfl) ⟨1817862, by rfl⟩ : syracuseStep 4847633 = 3635725) B3635725
theorem B2422865 : Blo 1435537 2422865 := bstep (se 2 (by rfl) ⟨908574, by rfl⟩ : syracuseStep 2422865 = 1817149) B1817149
theorem B2300003 : Blo 1435537 2300003 := bstep (se 1 (by rfl) ⟨1725002, by rfl⟩ : syracuseStep 2300003 = 3450005) B3450005
theorem B6903949 : Blo 1435537 6903949 := bstep (se 3 (by rfl) ⟨1294490, by rfl⟩ : syracuseStep 6903949 = 2588981) B2588981
theorem B2726065 : Blo 1435537 2726065 := bstep (se 2 (by rfl) ⟨1022274, by rfl⟩ : syracuseStep 2726065 = 2044549) B2044549
theorem B3233969 : Blo 1435537 3233969 := bstep (se 2 (by rfl) ⟨1212738, by rfl⟩ : syracuseStep 3233969 = 2425477) B2425477
theorem B3233987 : Blo 1435537 3233987 := bstep (se 1 (by rfl) ⟨2425490, by rfl⟩ : syracuseStep 3233987 = 4850981) B4850981
theorem B2422993 : Blo 1435537 2422993 := bstep (se 2 (by rfl) ⟨908622, by rfl⟩ : syracuseStep 2422993 = 1817245) B1817245
theorem B2046161 : Blo 1435537 2046161 := bstep (se 2 (by rfl) ⟨767310, by rfl⟩ : syracuseStep 2046161 = 1534621) B1534621
theorem B2185427 : Blo 1435537 2185427 := bstep (se 1 (by rfl) ⟨1639070, by rfl⟩ : syracuseStep 2185427 = 3278141) B3278141
theorem B167860451 : Blo 1435537 167860451 := bstep (se 1 (by rfl) ⟨125895338, by rfl⟩ : syracuseStep 167860451 = 251790677) B251790677
theorem B2423027 : Blo 1435537 2423027 := bstep (se 1 (by rfl) ⟨1817270, by rfl⟩ : syracuseStep 2423027 = 3634541) B3634541
theorem B1726771 : Blo 1435537 1726771 := bstep (se 1 (by rfl) ⟨1295078, by rfl⟩ : syracuseStep 1726771 = 2590157) B2590157
theorem B1816931 : Blo 1435537 1816931 := bstep (se 1 (by rfl) ⟨1362698, by rfl⟩ : syracuseStep 1816931 = 2725397) B2725397
theorem B2423155 : Blo 1435537 2423155 := bstep (se 1 (by rfl) ⟨1817366, by rfl⟩ : syracuseStep 2423155 = 3634733) B3634733
theorem B4200877 : Blo 1435537 4200877 := bstep (se 3 (by rfl) ⟨787664, by rfl⟩ : syracuseStep 4200877 = 1575329) B1575329
theorem B1726915 : Blo 1435537 1726915 := bstep (se 1 (by rfl) ⟨1295186, by rfl⟩ : syracuseStep 1726915 = 2590373) B2590373
theorem B3234257 : Blo 1435537 3234257 := bstep (se 2 (by rfl) ⟨1212846, by rfl⟩ : syracuseStep 3234257 = 2425693) B2425693
theorem B3234275 : Blo 1435537 3234275 := bstep (se 1 (by rfl) ⟨2425706, by rfl⟩ : syracuseStep 3234275 = 4851413) B4851413
theorem B2423297 : Blo 1435537 2423297 := bstep (se 2 (by rfl) ⟨908736, by rfl⟩ : syracuseStep 2423297 = 1817473) B1817473
theorem B4848173 : Blo 1435537 4848173 := bstep (se 3 (by rfl) ⟨909032, by rfl⟩ : syracuseStep 4848173 = 1818065) B1818065
theorem B4848227 : Blo 1435537 4848227 := bstep (se 1 (by rfl) ⟨3636170, by rfl⟩ : syracuseStep 4848227 = 7272341) B7272341
theorem B1841779 : Blo 1435537 1841779 := bstep (se 1 (by rfl) ⟨1381334, by rfl⟩ : syracuseStep 1841779 = 2762669) B2762669
theorem B2423425 : Blo 1435537 2423425 := bstep (se 2 (by rfl) ⟨908784, by rfl⟩ : syracuseStep 2423425 = 1817569) B1817569
theorem B2423459 : Blo 1435537 2423459 := bstep (se 1 (by rfl) ⟨1817594, by rfl⟩ : syracuseStep 2423459 = 3635189) B3635189
theorem B5454499 : Blo 1435537 5454499 := bstep (se 1 (by rfl) ⟨4090874, by rfl⟩ : syracuseStep 5454499 = 8181749) B8181749
theorem B2423587 : Blo 1435537 2423587 := bstep (se 1 (by rfl) ⟨1817690, by rfl⟩ : syracuseStep 2423587 = 3635381) B3635381
theorem B2300707 : Blo 1435537 2300707 := bstep (se 1 (by rfl) ⟨1725530, by rfl⟩ : syracuseStep 2300707 = 3451061) B3451061
theorem B6552355 : Blo 1435537 6552355 := bstep (se 1 (by rfl) ⟨4914266, by rfl⟩ : syracuseStep 6552355 = 9828533) B9828533
theorem B4913965 : Blo 1435537 4913965 := bstep (se 3 (by rfl) ⟨921368, by rfl⟩ : syracuseStep 4913965 = 1842737) B1842737
theorem B3636049 : Blo 1435537 3636049 := bstep (se 2 (by rfl) ⟨1363518, by rfl⟩ : syracuseStep 3636049 = 2727037) B2727037
theorem B2153315 : Blo 1435537 2153315 := bstep (se 1 (by rfl) ⟨1614986, by rfl⟩ : syracuseStep 2153315 = 3229973) B3229973
theorem B4848497 : Blo 1435537 4848497 := bstep (se 2 (by rfl) ⟨1818186, by rfl⟩ : syracuseStep 4848497 = 3636373) B3636373
theorem B2153345 : Blo 1435537 2153345 := bstep (se 2 (by rfl) ⟨807504, by rfl⟩ : syracuseStep 2153345 = 1615009) B1615009
theorem B2153363 : Blo 1435537 2153363 := bstep (se 1 (by rfl) ⟨1615022, by rfl⟩ : syracuseStep 2153363 = 3230045) B3230045
theorem B2153393 : Blo 1435537 2153393 := bstep (se 2 (by rfl) ⟨807522, by rfl⟩ : syracuseStep 2153393 = 1615045) B1615045
theorem B2423729 : Blo 1435537 2423729 := bstep (se 2 (by rfl) ⟨908898, by rfl⟩ : syracuseStep 2423729 = 1817797) B1817797
theorem B2153411 : Blo 1435537 2153411 := bstep (se 1 (by rfl) ⟨1615058, by rfl⟩ : syracuseStep 2153411 = 3230117) B3230117
theorem B2153441 : Blo 1435537 2153441 := bstep (se 2 (by rfl) ⟨807540, by rfl⟩ : syracuseStep 2153441 = 1615081) B1615081
theorem B3881969 : Blo 1435537 3881969 := bstep (se 2 (by rfl) ⟨1455738, by rfl⟩ : syracuseStep 3881969 = 2911477) B2911477
theorem B2153459 : Blo 1435537 2153459 := bstep (se 1 (by rfl) ⟨1615094, by rfl⟩ : syracuseStep 2153459 = 3230189) B3230189
theorem B2333683 : Blo 1435537 2333683 := bstep (se 1 (by rfl) ⟨1750262, by rfl⟩ : syracuseStep 2333683 = 3500525) B3500525
theorem B2153489 : Blo 1435537 2153489 := bstep (se 2 (by rfl) ⟨807558, by rfl⟩ : syracuseStep 2153489 = 1615117) B1615117
theorem B2153507 : Blo 1435537 2153507 := bstep (se 1 (by rfl) ⟨1615130, by rfl⟩ : syracuseStep 2153507 = 3230261) B3230261
theorem B1817635 : Blo 1435537 1817635 := bstep (se 1 (by rfl) ⟨1363226, by rfl⟩ : syracuseStep 1817635 = 2726453) B2726453
theorem B2423857 : Blo 1435537 2423857 := bstep (se 2 (by rfl) ⟨908946, by rfl⟩ : syracuseStep 2423857 = 1817893) B1817893
theorem B2300977 : Blo 1435537 2300977 := bstep (se 2 (by rfl) ⟨862866, by rfl⟩ : syracuseStep 2300977 = 1725733) B1725733
theorem B2153537 : Blo 1435537 2153537 := bstep (se 2 (by rfl) ⟨807576, by rfl⟩ : syracuseStep 2153537 = 1615153) B1615153
theorem B2153555 : Blo 1435537 2153555 := bstep (se 1 (by rfl) ⟨1615166, by rfl⟩ : syracuseStep 2153555 = 3230333) B3230333
theorem B2423891 : Blo 1435537 2423891 := bstep (se 1 (by rfl) ⟨1817918, by rfl⟩ : syracuseStep 2423891 = 3635837) B3635837
theorem B3636323 : Blo 1435537 3636323 := bstep (se 1 (by rfl) ⟨2727242, by rfl⟩ : syracuseStep 3636323 = 5454485) B5454485
theorem B2153585 : Blo 1435537 2153585 := bstep (se 2 (by rfl) ⟨807594, by rfl⟩ : syracuseStep 2153585 = 1615189) B1615189
theorem B2301041 : Blo 1435537 2301041 := bstep (se 2 (by rfl) ⟨862890, by rfl⟩ : syracuseStep 2301041 = 1725781) B1725781
theorem B2153603 : Blo 1435537 2153603 := bstep (se 1 (by rfl) ⟨1615202, by rfl⟩ : syracuseStep 2153603 = 3230405) B3230405
theorem B1817731 : Blo 1435537 1817731 := bstep (se 1 (by rfl) ⟨1363298, by rfl⟩ : syracuseStep 1817731 = 2726597) B2726597
theorem B2153633 : Blo 1435537 2153633 := bstep (se 2 (by rfl) ⟨807612, by rfl⟩ : syracuseStep 2153633 = 1615225) B1615225
theorem B4603043 : Blo 1435537 4603043 := bstep (se 1 (by rfl) ⟨3452282, by rfl⟩ : syracuseStep 4603043 = 6904565) B6904565
theorem B2153651 : Blo 1435537 2153651 := bstep (se 1 (by rfl) ⟨1615238, by rfl⟩ : syracuseStep 2153651 = 3230477) B3230477
theorem B2153681 : Blo 1435537 2153681 := bstep (se 2 (by rfl) ⟨807630, by rfl⟩ : syracuseStep 2153681 = 1615261) B1615261
theorem B2727121 : Blo 1435537 2727121 := bstep (se 2 (by rfl) ⟨1022670, by rfl⟩ : syracuseStep 2727121 = 2045341) B2045341
theorem B2424019 : Blo 1435537 2424019 := bstep (se 1 (by rfl) ⟨1818014, by rfl⟩ : syracuseStep 2424019 = 3636029) B3636029
theorem B2153699 : Blo 1435537 2153699 := bstep (se 1 (by rfl) ⟨1615274, by rfl⟩ : syracuseStep 2153699 = 3230549) B3230549
theorem B2153729 : Blo 1435537 2153729 := bstep (se 2 (by rfl) ⟨807648, by rfl⟩ : syracuseStep 2153729 = 1615297) B1615297
theorem B2153747 : Blo 1435537 2153747 := bstep (se 1 (by rfl) ⟨1615310, by rfl⟩ : syracuseStep 2153747 = 3230621) B3230621
theorem B3636515 : Blo 1435537 3636515 := bstep (se 1 (by rfl) ⟨2727386, by rfl⟩ : syracuseStep 3636515 = 5454773) B5454773
theorem B2153777 : Blo 1435537 2153777 := bstep (se 2 (by rfl) ⟨807666, by rfl⟩ : syracuseStep 2153777 = 1615333) B1615333
theorem B2153795 : Blo 1435537 2153795 := bstep (se 1 (by rfl) ⟨1615346, by rfl⟩ : syracuseStep 2153795 = 3230693) B3230693
theorem B2153825 : Blo 1435537 2153825 := bstep (se 2 (by rfl) ⟨807684, by rfl⟩ : syracuseStep 2153825 = 1615369) B1615369
theorem B2424161 : Blo 1435537 2424161 := bstep (se 2 (by rfl) ⟨909060, by rfl⟩ : syracuseStep 2424161 = 1818121) B1818121
theorem B2153843 : Blo 1435537 2153843 := bstep (se 1 (by rfl) ⟨1615382, by rfl⟩ : syracuseStep 2153843 = 3230765) B3230765
theorem B4849037 : Blo 1435537 4849037 := bstep (se 3 (by rfl) ⟨909194, by rfl⟩ : syracuseStep 4849037 = 1818389) B1818389
theorem B2153873 : Blo 1435537 2153873 := bstep (se 2 (by rfl) ⟨807702, by rfl⟩ : syracuseStep 2153873 = 1615405) B1615405
theorem B2153891 : Blo 1435537 2153891 := bstep (se 1 (by rfl) ⟨1615418, by rfl⟩ : syracuseStep 2153891 = 3230837) B3230837
theorem B6135203 : Blo 1435537 6135203 := bstep (se 1 (by rfl) ⟨4601402, by rfl⟩ : syracuseStep 6135203 = 9202805) B9202805
theorem B2153921 : Blo 1435537 2153921 := bstep (se 2 (by rfl) ⟨807720, by rfl⟩ : syracuseStep 2153921 = 1615441) B1615441
theorem B4849091 : Blo 1435537 4849091 := bstep (se 1 (by rfl) ⟨3636818, by rfl⟩ : syracuseStep 4849091 = 7273637) B7273637
theorem B2153939 : Blo 1435537 2153939 := bstep (se 1 (by rfl) ⟨1615454, by rfl⟩ : syracuseStep 2153939 = 3230909) B3230909
theorem B2424289 : Blo 1435537 2424289 := bstep (se 2 (by rfl) ⟨909108, by rfl⟩ : syracuseStep 2424289 = 1818217) B1818217
theorem B3882467 : Blo 1435537 3882467 := bstep (se 1 (by rfl) ⟨2911850, by rfl⟩ : syracuseStep 3882467 = 5823701) B5823701
theorem B2244067 : Blo 1435537 2244067 := bstep (se 1 (by rfl) ⟨1683050, by rfl⟩ : syracuseStep 2244067 = 3366101) B3366101
theorem B2153969 : Blo 1435537 2153969 := bstep (se 2 (by rfl) ⟨807738, by rfl⟩ : syracuseStep 2153969 = 1615477) B1615477
theorem B2153987 : Blo 1435537 2153987 := bstep (se 1 (by rfl) ⟨1615490, by rfl⟩ : syracuseStep 2153987 = 3230981) B3230981
theorem B2424323 : Blo 1435537 2424323 := bstep (se 1 (by rfl) ⟨1818242, by rfl⟩ : syracuseStep 2424323 = 3636485) B3636485
theorem B1842707 : Blo 1435537 1842707 := bstep (se 1 (by rfl) ⟨1382030, by rfl⟩ : syracuseStep 1842707 = 2764061) B2764061
theorem B2154017 : Blo 1435537 2154017 := bstep (se 2 (by rfl) ⟨807756, by rfl⟩ : syracuseStep 2154017 = 1615513) B1615513
theorem B2072099 : Blo 1435537 2072099 := bstep (se 1 (by rfl) ⟨1554074, by rfl⟩ : syracuseStep 2072099 = 3108149) B3108149
theorem B3276323 : Blo 1435537 3276323 := bstep (se 1 (by rfl) ⟨2457242, by rfl⟩ : syracuseStep 3276323 = 4914485) B4914485
theorem B2154035 : Blo 1435537 2154035 := bstep (se 1 (by rfl) ⟨1615526, by rfl⟩ : syracuseStep 2154035 = 3231053) B3231053
theorem B8289869 : Blo 1435537 8289869 := bstep (se 3 (by rfl) ⟨1554350, by rfl⟩ : syracuseStep 8289869 = 3108701) B3108701
theorem B2154065 : Blo 1435537 2154065 := bstep (se 2 (by rfl) ⟨807774, by rfl⟩ : syracuseStep 2154065 = 1615549) B1615549
theorem B2154083 : Blo 1435537 2154083 := bstep (se 1 (by rfl) ⟨1615562, by rfl⟩ : syracuseStep 2154083 = 3231125) B3231125
theorem B2727523 : Blo 1435537 2727523 := bstep (se 1 (by rfl) ⟨2045642, by rfl⟩ : syracuseStep 2727523 = 4091285) B4091285
theorem B11214449 : Blo 1435537 11214449 := bstep (se 2 (by rfl) ⟨4205418, by rfl⟩ : syracuseStep 11214449 = 8410837) B8410837
theorem B1818227 : Blo 1435537 1818227 := bstep (se 1 (by rfl) ⟨1363670, by rfl⟩ : syracuseStep 1818227 = 2727341) B2727341
theorem B2154113 : Blo 1435537 2154113 := bstep (se 2 (by rfl) ⟨807792, by rfl⟩ : syracuseStep 2154113 = 1615585) B1615585
theorem B2424451 : Blo 1435537 2424451 := bstep (se 1 (by rfl) ⟨1818338, by rfl⟩ : syracuseStep 2424451 = 3636677) B3636677
theorem B2727569 : Blo 1435537 2727569 := bstep (se 2 (by rfl) ⟨1022838, by rfl⟩ : syracuseStep 2727569 = 2045677) B2045677
theorem B2154131 : Blo 1435537 2154131 := bstep (se 1 (by rfl) ⟨1615598, by rfl⟩ : syracuseStep 2154131 = 3231197) B3231197
theorem B2154161 : Blo 1435537 2154161 := bstep (se 2 (by rfl) ⟨807810, by rfl⟩ : syracuseStep 2154161 = 1615621) B1615621
theorem B2154179 : Blo 1435537 2154179 := bstep (se 1 (by rfl) ⟨1615634, by rfl⟩ : syracuseStep 2154179 = 3231269) B3231269
theorem B4849361 : Blo 1435537 4849361 := bstep (se 2 (by rfl) ⟨1818510, by rfl⟩ : syracuseStep 4849361 = 3637021) B3637021
theorem B2154209 : Blo 1435537 2154209 := bstep (se 2 (by rfl) ⟨807828, by rfl⟩ : syracuseStep 2154209 = 1615657) B1615657
theorem B2154227 : Blo 1435537 2154227 := bstep (se 1 (by rfl) ⟨1615670, by rfl⟩ : syracuseStep 2154227 = 3231341) B3231341
theorem B2154257 : Blo 1435537 2154257 := bstep (se 2 (by rfl) ⟨807846, by rfl⟩ : syracuseStep 2154257 = 1615693) B1615693
theorem B1941265 : Blo 1435537 1941265 := bstep (se 2 (by rfl) ⟨727974, by rfl⟩ : syracuseStep 1941265 = 1455949) B1455949
theorem B2424593 : Blo 1435537 2424593 := bstep (se 2 (by rfl) ⟨909222, by rfl⟩ : syracuseStep 2424593 = 1818445) B1818445
theorem B2154275 : Blo 1435537 2154275 := bstep (se 1 (by rfl) ⟨1615706, by rfl⟩ : syracuseStep 2154275 = 3231413) B3231413
theorem B2154305 : Blo 1435537 2154305 := bstep (se 2 (by rfl) ⟨807864, by rfl⟩ : syracuseStep 2154305 = 1615729) B1615729
theorem B10100557 : Blo 1435537 10100557 := bstep (se 3 (by rfl) ⟨1893854, by rfl⟩ : syracuseStep 10100557 = 3787709) B3787709
theorem B2154323 : Blo 1435537 2154323 := bstep (se 1 (by rfl) ⟨1615742, by rfl⟩ : syracuseStep 2154323 = 3231485) B3231485
theorem B10903409 : Blo 1435537 10903409 := bstep (se 2 (by rfl) ⟨4088778, by rfl⟩ : syracuseStep 10903409 = 8177557) B8177557
theorem B2154353 : Blo 1435537 2154353 := bstep (se 2 (by rfl) ⟨807882, by rfl⟩ : syracuseStep 2154353 = 1615765) B1615765
theorem B2154371 : Blo 1435537 2154371 := bstep (se 1 (by rfl) ⟨1615778, by rfl⟩ : syracuseStep 2154371 = 3231557) B3231557
theorem B2424721 : Blo 1435537 2424721 := bstep (se 2 (by rfl) ⟨909270, by rfl⟩ : syracuseStep 2424721 = 1818541) B1818541
theorem B2154401 : Blo 1435537 2154401 := bstep (se 2 (by rfl) ⟨807900, by rfl⟩ : syracuseStep 2154401 = 1615801) B1615801
theorem B2727857 : Blo 1435537 2727857 := bstep (se 2 (by rfl) ⟨1022946, by rfl⟩ : syracuseStep 2727857 = 2045893) B2045893
theorem B2154419 : Blo 1435537 2154419 := bstep (se 1 (by rfl) ⟨1615814, by rfl⟩ : syracuseStep 2154419 = 3231629) B3231629
theorem B2424755 : Blo 1435537 2424755 := bstep (se 1 (by rfl) ⟨1818566, by rfl⟩ : syracuseStep 2424755 = 3637133) B3637133
theorem B46612421 : Blo 1435537 46612421 := bstep (se 4 (by rfl) ⟨4369914, by rfl⟩ : syracuseStep 46612421 = 8739829) B8739829
theorem B9207749 : Blo 1435537 9207749 := bstep (se 4 (by rfl) ⟨863226, by rfl⟩ : syracuseStep 9207749 = 1726453) B1726453
theorem B2154449 : Blo 1435537 2154449 := bstep (se 2 (by rfl) ⟨807918, by rfl⟩ : syracuseStep 2154449 = 1615837) B1615837
theorem B2154467 : Blo 1435537 2154467 := bstep (se 1 (by rfl) ⟨1615850, by rfl⟩ : syracuseStep 2154467 = 3231701) B3231701
theorem B9199601 : Blo 1435537 9199601 := bstep (se 2 (by rfl) ⟨3449850, by rfl⟩ : syracuseStep 9199601 = 6899701) B6899701
theorem B9330673 : Blo 1435537 9330673 := bstep (se 2 (by rfl) ⟨3499002, by rfl⟩ : syracuseStep 9330673 = 6998005) B6998005
theorem B2154521 : Blo 1435537 2154521 := bstep (se 2 (by rfl) ⟨807945, by rfl⟩ : syracuseStep 2154521 = 1615891) B1615891
theorem B4849739 : Blo 1435537 4849739 := bstep (se 1 (by rfl) ⟨3637304, by rfl⟩ : syracuseStep 4849739 = 7274609) B7274609
theorem B2154635 : Blo 1435537 2154635 := bstep (se 1 (by rfl) ⟨1615976, by rfl⟩ : syracuseStep 2154635 = 3231953) B3231953
theorem B2424971 : Blo 1435537 2424971 := bstep (se 1 (by rfl) ⟨1818728, by rfl⟩ : syracuseStep 2424971 = 3637457) B3637457
theorem B4145303 : Blo 1435537 4145303 := bstep (se 1 (by rfl) ⟨3108977, by rfl⟩ : syracuseStep 4145303 = 6217955) B6217955
theorem B2154647 : Blo 1435537 2154647 := bstep (se 1 (by rfl) ⟨1615985, by rfl⟩ : syracuseStep 2154647 = 3231971) B3231971
theorem B11059379 : Blo 1435537 11059379 := bstep (se 1 (by rfl) ⟨8294534, by rfl⟩ : syracuseStep 11059379 = 16589069) B16589069
theorem B3195095 : Blo 1435537 3195095 := bstep (se 1 (by rfl) ⟨2396321, by rfl⟩ : syracuseStep 3195095 = 4792643) B4792643
theorem B2154713 : Blo 1435537 2154713 := bstep (se 2 (by rfl) ⟨808017, by rfl⟩ : syracuseStep 2154713 = 1616035) B1616035
theorem B2425099 : Blo 1435537 2425099 := bstep (se 1 (by rfl) ⟨1818824, by rfl⟩ : syracuseStep 2425099 = 3637649) B3637649
theorem B8175917 : Blo 1435537 8175917 := bstep (se 3 (by rfl) ⟨1532984, by rfl⟩ : syracuseStep 8175917 = 3065969) B3065969
theorem B2154827 : Blo 1435537 2154827 := bstep (se 1 (by rfl) ⟨1616120, by rfl⟩ : syracuseStep 2154827 = 3232241) B3232241
theorem B2154839 : Blo 1435537 2154839 := bstep (se 1 (by rfl) ⟨1616129, by rfl⟩ : syracuseStep 2154839 = 3232259) B3232259
theorem B4850009 : Blo 1435537 4850009 := bstep (se 2 (by rfl) ⟨1818753, by rfl⟩ : syracuseStep 4850009 = 3637507) B3637507
theorem B2728343 : Blo 1435537 2728343 := bstep (se 1 (by rfl) ⟨2046257, by rfl⟩ : syracuseStep 2728343 = 4092515) B4092515
theorem B2154905 : Blo 1435537 2154905 := bstep (se 2 (by rfl) ⟨808089, by rfl⟩ : syracuseStep 2154905 = 1616179) B1616179
theorem B2458009 : Blo 1435537 2458009 := bstep (se 2 (by rfl) ⟨921753, by rfl⟩ : syracuseStep 2458009 = 1843507) B1843507
theorem B2425241 : Blo 1435537 2425241 := bstep (se 2 (by rfl) ⟨909465, by rfl⟩ : syracuseStep 2425241 = 1818931) B1818931
theorem B2302361 : Blo 1435537 2302361 := bstep (se 2 (by rfl) ⟨863385, by rfl⟩ : syracuseStep 2302361 = 1726771) B1726771
theorem B5177803 : Blo 1435537 5177803 := bstep (se 1 (by rfl) ⟨3883352, by rfl⟩ : syracuseStep 5177803 = 7766705) B7766705
theorem B2155019 : Blo 1435537 2155019 := bstep (se 1 (by rfl) ⟨1616264, by rfl⟩ : syracuseStep 2155019 = 3232529) B3232529
theorem B2155031 : Blo 1435537 2155031 := bstep (se 1 (by rfl) ⟨1616273, by rfl⟩ : syracuseStep 2155031 = 3232547) B3232547
theorem B1942039 : Blo 1435537 1942039 := bstep (se 1 (by rfl) ⟨1456529, by rfl⟩ : syracuseStep 1942039 = 2913059) B2913059
theorem B2425369 : Blo 1435537 2425369 := bstep (se 2 (by rfl) ⟨909513, by rfl⟩ : syracuseStep 2425369 = 1819027) B1819027
theorem B5456429 : Blo 1435537 5456429 := bstep (se 3 (by rfl) ⟨1023080, by rfl⟩ : syracuseStep 5456429 = 2046161) B2046161
theorem B3637811 : Blo 1435537 3637811 := bstep (se 1 (by rfl) ⟨2728358, by rfl⟩ : syracuseStep 3637811 = 5456717) B5456717
theorem B2155097 : Blo 1435537 2155097 := bstep (se 2 (by rfl) ⟨808161, by rfl⟩ : syracuseStep 2155097 = 1616323) B1616323
theorem B2302553 : Blo 1435537 2302553 := bstep (se 2 (by rfl) ⟨863457, by rfl⟩ : syracuseStep 2302553 = 1726915) B1726915
theorem B447627869 : Blo 1435537 447627869 := bstep (se 3 (by rfl) ⟨83930225, by rfl⟩ : syracuseStep 447627869 = 167860451) B167860451
theorem B2155211 : Blo 1435537 2155211 := bstep (se 1 (by rfl) ⟨1616408, by rfl⟩ : syracuseStep 2155211 = 3232817) B3232817
theorem B2155223 : Blo 1435537 2155223 := bstep (se 1 (by rfl) ⟨1616417, by rfl⟩ : syracuseStep 2155223 = 3232835) B3232835
theorem B1819351 : Blo 1435537 1819351 := bstep (se 1 (by rfl) ⟨1364513, by rfl⟩ : syracuseStep 1819351 = 2729027) B2729027
theorem B2155289 : Blo 1435537 2155289 := bstep (se 2 (by rfl) ⟨808233, by rfl⟩ : syracuseStep 2155289 = 1616467) B1616467
theorem B13812545 : Blo 1435537 13812545 := bstep (se 2 (by rfl) ⟨5179704, by rfl⟩ : syracuseStep 13812545 = 10359409) B10359409
theorem B3638105 : Blo 1435537 3638105 := bstep (se 2 (by rfl) ⟨1364289, by rfl⟩ : syracuseStep 3638105 = 2728579) B2728579
theorem B7373699 : Blo 1435537 7373699 := bstep (se 1 (by rfl) ⟨5530274, by rfl⟩ : syracuseStep 7373699 = 11060549) B11060549
theorem B10912643 : Blo 1435537 10912643 := bstep (se 1 (by rfl) ⟨8184482, by rfl⟩ : syracuseStep 10912643 = 16368965) B16368965
theorem B2155403 : Blo 1435537 2155403 := bstep (se 1 (by rfl) ⟨1616552, by rfl⟩ : syracuseStep 2155403 = 3233105) B3233105
theorem B2155415 : Blo 1435537 2155415 := bstep (se 1 (by rfl) ⟨1616561, by rfl⟩ : syracuseStep 2155415 = 3233123) B3233123
theorem B2728883 : Blo 1435537 2728883 := bstep (se 1 (by rfl) ⟨2046662, by rfl⟩ : syracuseStep 2728883 = 4093325) B4093325
theorem B2155481 : Blo 1435537 2155481 := bstep (se 2 (by rfl) ⟨808305, by rfl⟩ : syracuseStep 2155481 = 1616611) B1616611
theorem B3687385 : Blo 1435537 3687385 := bstep (se 2 (by rfl) ⟨1382769, by rfl⟩ : syracuseStep 3687385 = 2765539) B2765539
theorem B4850711 : Blo 1435537 4850711 := bstep (se 1 (by rfl) ⟨3638033, by rfl⟩ : syracuseStep 4850711 = 7276067) B7276067
theorem B4604951 : Blo 1435537 4604951 := bstep (se 1 (by rfl) ⟨3453713, by rfl⟩ : syracuseStep 4604951 = 6907427) B6907427
theorem B5825611 : Blo 1435537 5825611 := bstep (se 1 (by rfl) ⟨4369208, by rfl⟩ : syracuseStep 5825611 = 8738417) B8738417
theorem B2155595 : Blo 1435537 2155595 := bstep (se 1 (by rfl) ⟨1616696, by rfl⟩ : syracuseStep 2155595 = 3233393) B3233393
theorem B2155607 : Blo 1435537 2155607 := bstep (se 1 (by rfl) ⟨1616705, by rfl⟩ : syracuseStep 2155607 = 3233411) B3233411
theorem B2155673 : Blo 1435537 2155673 := bstep (se 2 (by rfl) ⟨808377, by rfl⟩ : syracuseStep 2155673 = 1616755) B1616755
theorem B1615063 : Blo 1435537 1615063 := bstep (se 1 (by rfl) ⟨1211297, by rfl⟩ : syracuseStep 1615063 = 2422595) B2422595
theorem B2589911 : Blo 1435537 2589911 := bstep (se 1 (by rfl) ⟨1942433, by rfl⟩ : syracuseStep 2589911 = 3884867) B3884867
theorem B2155787 : Blo 1435537 2155787 := bstep (se 1 (by rfl) ⟨1616840, by rfl⟩ : syracuseStep 2155787 = 3233681) B3233681
theorem B2155799 : Blo 1435537 2155799 := bstep (se 1 (by rfl) ⟨1616849, by rfl⟩ : syracuseStep 2155799 = 3233699) B3233699
theorem B10904867 : Blo 1435537 10904867 := bstep (se 1 (by rfl) ⟨8178650, by rfl⟩ : syracuseStep 10904867 = 16357301) B16357301
theorem B5457203 : Blo 1435537 5457203 := bstep (se 1 (by rfl) ⟨4092902, by rfl⟩ : syracuseStep 5457203 = 8185805) B8185805
theorem B2155865 : Blo 1435537 2155865 := bstep (se 2 (by rfl) ⟨808449, by rfl⟩ : syracuseStep 2155865 = 1616899) B1616899
theorem B1615243 : Blo 1435537 1615243 := bstep (se 1 (by rfl) ⟨1211432, by rfl⟩ : syracuseStep 1615243 = 2422865) B2422865
theorem B1533335 : Blo 1435537 1533335 := bstep (se 1 (by rfl) ⟨1150001, by rfl⟩ : syracuseStep 1533335 = 2300003) B2300003
theorem B2155979 : Blo 1435537 2155979 := bstep (se 1 (by rfl) ⟨1616984, by rfl⟩ : syracuseStep 2155979 = 3233969) B3233969
theorem B2155991 : Blo 1435537 2155991 := bstep (se 1 (by rfl) ⟨1616993, by rfl⟩ : syracuseStep 2155991 = 3233987) B3233987
theorem B1615351 : Blo 1435537 1615351 := bstep (se 1 (by rfl) ⟨1211513, by rfl⟩ : syracuseStep 1615351 = 2423027) B2423027
theorem B2156057 : Blo 1435537 2156057 := bstep (se 2 (by rfl) ⟨808521, by rfl⟩ : syracuseStep 2156057 = 1617043) B1617043
theorem B9209389 : Blo 1435537 9209389 := bstep (se 3 (by rfl) ⟨1726760, by rfl⟩ : syracuseStep 9209389 = 3453521) B3453521
theorem B4851251 : Blo 1435537 4851251 := bstep (se 1 (by rfl) ⟨3638438, by rfl⟩ : syracuseStep 4851251 = 7276877) B7276877
theorem B3688001 : Blo 1435537 3688001 := bstep (se 2 (by rfl) ⟨1383000, by rfl⟩ : syracuseStep 3688001 = 2766001) B2766001
theorem B26207813 : Blo 1435537 26207813 := bstep (se 4 (by rfl) ⟨2456982, by rfl⟩ : syracuseStep 26207813 = 4913965) B4913965
theorem B2156171 : Blo 1435537 2156171 := bstep (se 1 (by rfl) ⟨1617128, by rfl⟩ : syracuseStep 2156171 = 3234257) B3234257
theorem B2156183 : Blo 1435537 2156183 := bstep (se 1 (by rfl) ⟨1617137, by rfl⟩ : syracuseStep 2156183 = 3234275) B3234275
theorem B1615531 : Blo 1435537 1615531 := bstep (se 1 (by rfl) ⟨1211648, by rfl⟩ : syracuseStep 1615531 = 2423297) B2423297
theorem B2156249 : Blo 1435537 2156249 := bstep (se 2 (by rfl) ⟨808593, by rfl⟩ : syracuseStep 2156249 = 1617187) B1617187
theorem B1615639 : Blo 1435537 1615639 := bstep (se 1 (by rfl) ⟨1211729, by rfl⟩ : syracuseStep 1615639 = 2423459) B2423459
theorem B4851521 : Blo 1435537 4851521 := bstep (se 2 (by rfl) ⟨1819320, by rfl⟩ : syracuseStep 4851521 = 3638641) B3638641
theorem B7374685 : Blo 1435537 7374685 := bstep (se 3 (by rfl) ⟨1382753, by rfl⟩ : syracuseStep 7374685 = 2765507) B2765507
theorem B1435543 : Blo 1435537 1435543 := bstep (se 1 (by rfl) ⟨1076657, by rfl⟩ : syracuseStep 1435543 = 2153315) B2153315
theorem B1435563 : Blo 1435537 1435563 := bstep (se 1 (by rfl) ⟨1076672, by rfl⟩ : syracuseStep 1435563 = 2153345) B2153345
theorem B1435575 : Blo 1435537 1435575 := bstep (se 1 (by rfl) ⟨1076681, by rfl⟩ : syracuseStep 1435575 = 2153363) B2153363
theorem B1435595 : Blo 1435537 1435595 := bstep (se 1 (by rfl) ⟨1076696, by rfl⟩ : syracuseStep 1435595 = 2153393) B2153393
theorem B1615819 : Blo 1435537 1615819 := bstep (se 1 (by rfl) ⟨1211864, by rfl⟩ : syracuseStep 1615819 = 2423729) B2423729
theorem B1435607 : Blo 1435537 1435607 := bstep (se 1 (by rfl) ⟨1076705, by rfl⟩ : syracuseStep 1435607 = 2153411) B2153411
theorem B1435627 : Blo 1435537 1435627 := bstep (se 1 (by rfl) ⟨1076720, by rfl⟩ : syracuseStep 1435627 = 2153441) B2153441
theorem B1435639 : Blo 1435537 1435639 := bstep (se 1 (by rfl) ⟨1076729, by rfl⟩ : syracuseStep 1435639 = 2153459) B2153459
theorem B1435659 : Blo 1435537 1435659 := bstep (se 1 (by rfl) ⟨1076744, by rfl⟩ : syracuseStep 1435659 = 2153489) B2153489
theorem B1435671 : Blo 1435537 1435671 := bstep (se 1 (by rfl) ⟨1076753, by rfl⟩ : syracuseStep 1435671 = 2153507) B2153507
theorem B1435691 : Blo 1435537 1435691 := bstep (se 1 (by rfl) ⟨1076768, by rfl⟩ : syracuseStep 1435691 = 2153537) B2153537
theorem B6907949 : Blo 1435537 6907949 := bstep (se 3 (by rfl) ⟨1295240, by rfl⟩ : syracuseStep 6907949 = 2590481) B2590481
theorem B1435703 : Blo 1435537 1435703 := bstep (se 1 (by rfl) ⟨1076777, by rfl⟩ : syracuseStep 1435703 = 2153555) B2153555
theorem B1615927 : Blo 1435537 1615927 := bstep (se 1 (by rfl) ⟨1211945, by rfl⟩ : syracuseStep 1615927 = 2423891) B2423891
theorem B1435723 : Blo 1435537 1435723 := bstep (se 1 (by rfl) ⟨1076792, by rfl⟩ : syracuseStep 1435723 = 2153585) B2153585
theorem B1534027 : Blo 1435537 1534027 := bstep (se 1 (by rfl) ⟨1150520, by rfl⟩ : syracuseStep 1534027 = 2301041) B2301041
theorem B1435735 : Blo 1435537 1435735 := bstep (se 1 (by rfl) ⟨1076801, by rfl⟩ : syracuseStep 1435735 = 2153603) B2153603
theorem B1435755 : Blo 1435537 1435755 := bstep (se 1 (by rfl) ⟨1076816, by rfl⟩ : syracuseStep 1435755 = 2153633) B2153633
theorem B1435767 : Blo 1435537 1435767 := bstep (se 1 (by rfl) ⟨1076825, by rfl⟩ : syracuseStep 1435767 = 2153651) B2153651
theorem B1435787 : Blo 1435537 1435787 := bstep (se 1 (by rfl) ⟨1076840, by rfl⟩ : syracuseStep 1435787 = 2153681) B2153681
theorem B1435799 : Blo 1435537 1435799 := bstep (se 1 (by rfl) ⟨1076849, by rfl⟩ : syracuseStep 1435799 = 2153699) B2153699
theorem B1435819 : Blo 1435537 1435819 := bstep (se 1 (by rfl) ⟨1076864, by rfl⟩ : syracuseStep 1435819 = 2153729) B2153729
theorem B1435831 : Blo 1435537 1435831 := bstep (se 1 (by rfl) ⟨1076873, by rfl⟩ : syracuseStep 1435831 = 2153747) B2153747
theorem B1435851 : Blo 1435537 1435851 := bstep (se 1 (by rfl) ⟨1076888, by rfl⟩ : syracuseStep 1435851 = 2153777) B2153777
theorem B1435863 : Blo 1435537 1435863 := bstep (se 1 (by rfl) ⟨1076897, by rfl⟩ : syracuseStep 1435863 = 2153795) B2153795
theorem B1435883 : Blo 1435537 1435883 := bstep (se 1 (by rfl) ⟨1076912, by rfl⟩ : syracuseStep 1435883 = 2153825) B2153825
theorem B1616107 : Blo 1435537 1616107 := bstep (se 1 (by rfl) ⟨1212080, by rfl⟩ : syracuseStep 1616107 = 2424161) B2424161
theorem B1435895 : Blo 1435537 1435895 := bstep (se 1 (by rfl) ⟨1076921, by rfl⟩ : syracuseStep 1435895 = 2153843) B2153843
theorem B1435915 : Blo 1435537 1435915 := bstep (se 1 (by rfl) ⟨1076936, by rfl⟩ : syracuseStep 1435915 = 2153873) B2153873
theorem B1435927 : Blo 1435537 1435927 := bstep (se 1 (by rfl) ⟨1076945, by rfl⟩ : syracuseStep 1435927 = 2153891) B2153891
theorem B4090135 : Blo 1435537 4090135 := bstep (se 1 (by rfl) ⟨3067601, by rfl⟩ : syracuseStep 4090135 = 6135203) B6135203
theorem B1435947 : Blo 1435537 1435947 := bstep (se 1 (by rfl) ⟨1076960, by rfl⟩ : syracuseStep 1435947 = 2153921) B2153921
theorem B1435959 : Blo 1435537 1435959 := bstep (se 1 (by rfl) ⟨1076969, by rfl⟩ : syracuseStep 1435959 = 2153939) B2153939
theorem B3230027 : Blo 1435537 3230027 := bstep (se 1 (by rfl) ⟨2422520, by rfl⟩ : syracuseStep 3230027 = 4845041) B4845041
theorem B1435979 : Blo 1435537 1435979 := bstep (se 1 (by rfl) ⟨1076984, by rfl⟩ : syracuseStep 1435979 = 2153969) B2153969
theorem B1435991 : Blo 1435537 1435991 := bstep (se 1 (by rfl) ⟨1076993, by rfl⟩ : syracuseStep 1435991 = 2153987) B2153987
theorem B1616215 : Blo 1435537 1616215 := bstep (se 1 (by rfl) ⟨1212161, by rfl⟩ : syracuseStep 1616215 = 2424323) B2424323
theorem B1436011 : Blo 1435537 1436011 := bstep (se 1 (by rfl) ⟨1077008, by rfl⟩ : syracuseStep 1436011 = 2154017) B2154017
theorem B1436023 : Blo 1435537 1436023 := bstep (se 1 (by rfl) ⟨1077017, by rfl⟩ : syracuseStep 1436023 = 2154035) B2154035
theorem B3230081 : Blo 1435537 3230081 := bstep (se 2 (by rfl) ⟨1211280, by rfl⟩ : syracuseStep 3230081 = 2422561) B2422561
theorem B1436043 : Blo 1435537 1436043 := bstep (se 1 (by rfl) ⟨1077032, by rfl⟩ : syracuseStep 1436043 = 2154065) B2154065
theorem B1436055 : Blo 1435537 1436055 := bstep (se 1 (by rfl) ⟨1077041, by rfl⟩ : syracuseStep 1436055 = 2154083) B2154083
theorem B1436075 : Blo 1435537 1436075 := bstep (se 1 (by rfl) ⟨1077056, by rfl⟩ : syracuseStep 1436075 = 2154113) B2154113
theorem B1436087 : Blo 1435537 1436087 := bstep (se 1 (by rfl) ⟨1077065, by rfl⟩ : syracuseStep 1436087 = 2154131) B2154131
theorem B1436107 : Blo 1435537 1436107 := bstep (se 1 (by rfl) ⟨1077080, by rfl⟩ : syracuseStep 1436107 = 2154161) B2154161
theorem B10349005 : Blo 1435537 10349005 := bstep (se 3 (by rfl) ⟨1940438, by rfl⟩ : syracuseStep 10349005 = 3880877) B3880877
theorem B1436119 : Blo 1435537 1436119 := bstep (se 1 (by rfl) ⟨1077089, by rfl⟩ : syracuseStep 1436119 = 2154179) B2154179
theorem B3066329 : Blo 1435537 3066329 := bstep (se 2 (by rfl) ⟨1149873, by rfl⟩ : syracuseStep 3066329 = 2299747) B2299747
theorem B1436139 : Blo 1435537 1436139 := bstep (se 1 (by rfl) ⟨1077104, by rfl⟩ : syracuseStep 1436139 = 2154209) B2154209
theorem B1436151 : Blo 1435537 1436151 := bstep (se 1 (by rfl) ⟨1077113, by rfl⟩ : syracuseStep 1436151 = 2154227) B2154227
theorem B1436171 : Blo 1435537 1436171 := bstep (se 1 (by rfl) ⟨1077128, by rfl⟩ : syracuseStep 1436171 = 2154257) B2154257
theorem B1616395 : Blo 1435537 1616395 := bstep (se 1 (by rfl) ⟨1212296, by rfl⟩ : syracuseStep 1616395 = 2424593) B2424593
theorem B1436183 : Blo 1435537 1436183 := bstep (se 1 (by rfl) ⟨1077137, by rfl⟩ : syracuseStep 1436183 = 2154275) B2154275
theorem B1436203 : Blo 1435537 1436203 := bstep (se 1 (by rfl) ⟨1077152, by rfl⟩ : syracuseStep 1436203 = 2154305) B2154305
theorem B1436215 : Blo 1435537 1436215 := bstep (se 1 (by rfl) ⟨1077161, by rfl⟩ : syracuseStep 1436215 = 2154323) B2154323
theorem B7268939 : Blo 1435537 7268939 := bstep (se 1 (by rfl) ⟨5451704, by rfl⟩ : syracuseStep 7268939 = 10903409) B10903409
theorem B1436235 : Blo 1435537 1436235 := bstep (se 1 (by rfl) ⟨1077176, by rfl⟩ : syracuseStep 1436235 = 2154353) B2154353
theorem B4147787 : Blo 1435537 4147787 := bstep (se 1 (by rfl) ⟨3110840, by rfl⟩ : syracuseStep 4147787 = 6221681) B6221681
theorem B1436247 : Blo 1435537 1436247 := bstep (se 1 (by rfl) ⟨1077185, by rfl⟩ : syracuseStep 1436247 = 2154371) B2154371
theorem B3230297 : Blo 1435537 3230297 := bstep (se 2 (by rfl) ⟨1211361, by rfl⟩ : syracuseStep 3230297 = 2422723) B2422723
theorem B1436267 : Blo 1435537 1436267 := bstep (se 1 (by rfl) ⟨1077200, by rfl⟩ : syracuseStep 1436267 = 2154401) B2154401
theorem B1436279 : Blo 1435537 1436279 := bstep (se 1 (by rfl) ⟨1077209, by rfl⟩ : syracuseStep 1436279 = 2154419) B2154419
theorem B1616503 : Blo 1435537 1616503 := bstep (se 1 (by rfl) ⟨1212377, by rfl⟩ : syracuseStep 1616503 = 2424755) B2424755
theorem B31074947 : Blo 1435537 31074947 := bstep (se 1 (by rfl) ⟨23306210, by rfl⟩ : syracuseStep 31074947 = 46612421) B46612421
theorem B6138499 : Blo 1435537 6138499 := bstep (se 1 (by rfl) ⟨4603874, by rfl⟩ : syracuseStep 6138499 = 9207749) B9207749
theorem B1436299 : Blo 1435537 1436299 := bstep (se 1 (by rfl) ⟨1077224, by rfl⟩ : syracuseStep 1436299 = 2154449) B2154449
theorem B1436311 : Blo 1435537 1436311 := bstep (se 1 (by rfl) ⟨1077233, by rfl⟩ : syracuseStep 1436311 = 2154467) B2154467
theorem B1436331 : Blo 1435537 1436331 := bstep (se 1 (by rfl) ⟨1077248, by rfl⟩ : syracuseStep 1436331 = 2154497) B2154497
theorem B3230387 : Blo 1435537 3230387 := bstep (se 1 (by rfl) ⟨2422790, by rfl⟩ : syracuseStep 3230387 = 4845581) B4845581
theorem B1436343 : Blo 1435537 1436343 := bstep (se 1 (by rfl) ⟨1077257, by rfl⟩ : syracuseStep 1436343 = 2154515) B2154515
theorem B1436363 : Blo 1435537 1436363 := bstep (se 1 (by rfl) ⟨1077272, by rfl⟩ : syracuseStep 1436363 = 2154545) B2154545
theorem B10349261 : Blo 1435537 10349261 := bstep (se 3 (by rfl) ⟨1940486, by rfl⟩ : syracuseStep 10349261 = 3880973) B3880973
theorem B3230423 : Blo 1435537 3230423 := bstep (se 1 (by rfl) ⟨2422817, by rfl⟩ : syracuseStep 3230423 = 4845635) B4845635
theorem B1436375 : Blo 1435537 1436375 := bstep (se 1 (by rfl) ⟨1077281, by rfl⟩ : syracuseStep 1436375 = 2154563) B2154563
theorem B1436395 : Blo 1435537 1436395 := bstep (se 1 (by rfl) ⟨1077296, by rfl⟩ : syracuseStep 1436395 = 2154593) B2154593
theorem B1436407 : Blo 1435537 1436407 := bstep (se 1 (by rfl) ⟨1077305, by rfl⟩ : syracuseStep 1436407 = 2154611) B2154611
theorem B16583429 : Blo 1435537 16583429 := bstep (se 4 (by rfl) ⟨1554696, by rfl⟩ : syracuseStep 16583429 = 3109393) B3109393
theorem B1436427 : Blo 1435537 1436427 := bstep (se 1 (by rfl) ⟨1077320, by rfl⟩ : syracuseStep 1436427 = 2154641) B2154641
theorem B1436439 : Blo 1435537 1436439 := bstep (se 1 (by rfl) ⟨1077329, by rfl⟩ : syracuseStep 1436439 = 2154659) B2154659
theorem B1436459 : Blo 1435537 1436459 := bstep (se 1 (by rfl) ⟨1077344, by rfl⟩ : syracuseStep 1436459 = 2154689) B2154689
theorem B1616683 : Blo 1435537 1616683 := bstep (se 1 (by rfl) ⟨1212512, by rfl⟩ : syracuseStep 1616683 = 2425025) B2425025
theorem B1436471 : Blo 1435537 1436471 := bstep (se 1 (by rfl) ⟨1077353, by rfl⟩ : syracuseStep 1436471 = 2154707) B2154707
theorem B1436491 : Blo 1435537 1436491 := bstep (se 1 (by rfl) ⟨1077368, by rfl⟩ : syracuseStep 1436491 = 2154737) B2154737
theorem B1436503 : Blo 1435537 1436503 := bstep (se 1 (by rfl) ⟨1077377, by rfl⟩ : syracuseStep 1436503 = 2154755) B2154755
theorem B1436523 : Blo 1435537 1436523 := bstep (se 1 (by rfl) ⟨1077392, by rfl⟩ : syracuseStep 1436523 = 2154785) B2154785
theorem B1436535 : Blo 1435537 1436535 := bstep (se 1 (by rfl) ⟨1077401, by rfl⟩ : syracuseStep 1436535 = 2154803) B2154803
theorem B3230603 : Blo 1435537 3230603 := bstep (se 1 (by rfl) ⟨2422952, by rfl⟩ : syracuseStep 3230603 = 4845905) B4845905
theorem B1436555 : Blo 1435537 1436555 := bstep (se 1 (by rfl) ⟨1077416, by rfl⟩ : syracuseStep 1436555 = 2154833) B2154833
theorem B1436567 : Blo 1435537 1436567 := bstep (se 1 (by rfl) ⟨1077425, by rfl⟩ : syracuseStep 1436567 = 2154851) B2154851
theorem B1616791 : Blo 1435537 1616791 := bstep (se 1 (by rfl) ⟨1212593, by rfl⟩ : syracuseStep 1616791 = 2425187) B2425187
theorem B1436587 : Blo 1435537 1436587 := bstep (se 1 (by rfl) ⟨1077440, by rfl⟩ : syracuseStep 1436587 = 2154881) B2154881
theorem B1436599 : Blo 1435537 1436599 := bstep (se 1 (by rfl) ⟨1077449, by rfl⟩ : syracuseStep 1436599 = 2154899) B2154899
theorem B3230657 : Blo 1435537 3230657 := bstep (se 2 (by rfl) ⟨1211496, by rfl⟩ : syracuseStep 3230657 = 2422993) B2422993
theorem B6302657 : Blo 1435537 6302657 := bstep (se 2 (by rfl) ⟨2363496, by rfl⟩ : syracuseStep 6302657 = 4726993) B4726993
theorem B1436619 : Blo 1435537 1436619 := bstep (se 1 (by rfl) ⟨1077464, by rfl⟩ : syracuseStep 1436619 = 2154929) B2154929
theorem B1436631 : Blo 1435537 1436631 := bstep (se 1 (by rfl) ⟨1077473, by rfl⟩ : syracuseStep 1436631 = 2154947) B2154947
theorem B6138841 : Blo 1435537 6138841 := bstep (se 2 (by rfl) ⟨2302065, by rfl⟩ : syracuseStep 6138841 = 4604131) B4604131
theorem B1436651 : Blo 1435537 1436651 := bstep (se 1 (by rfl) ⟨1077488, by rfl⟩ : syracuseStep 1436651 = 2154977) B2154977
theorem B1436663 : Blo 1435537 1436663 := bstep (se 1 (by rfl) ⟨1077497, by rfl⟩ : syracuseStep 1436663 = 2154995) B2154995
theorem B1436683 : Blo 1435537 1436683 := bstep (se 1 (by rfl) ⟨1077512, by rfl⟩ : syracuseStep 1436683 = 2155025) B2155025
theorem B1436695 : Blo 1435537 1436695 := bstep (se 1 (by rfl) ⟨1077521, by rfl⟩ : syracuseStep 1436695 = 2155043) B2155043
theorem B11652131 : Blo 1435537 11652131 := bstep (se 1 (by rfl) ⟨8739098, by rfl⟩ : syracuseStep 11652131 = 17478197) B17478197
theorem B1436715 : Blo 1435537 1436715 := bstep (se 1 (by rfl) ⟨1077536, by rfl⟩ : syracuseStep 1436715 = 2155073) B2155073
theorem B1436727 : Blo 1435537 1436727 := bstep (se 1 (by rfl) ⟨1077545, by rfl⟩ : syracuseStep 1436727 = 2155091) B2155091
theorem B2911307 : Blo 1435537 2911307 := bstep (se 1 (by rfl) ⟨2183480, by rfl⟩ : syracuseStep 2911307 = 4366961) B4366961
theorem B1436747 : Blo 1435537 1436747 := bstep (se 1 (by rfl) ⟨1077560, by rfl⟩ : syracuseStep 1436747 = 2155121) B2155121
theorem B1616971 : Blo 1435537 1616971 := bstep (se 1 (by rfl) ⟨1212728, by rfl⟩ : syracuseStep 1616971 = 2425457) B2425457
theorem B1436759 : Blo 1435537 1436759 := bstep (se 1 (by rfl) ⟨1077569, by rfl⟩ : syracuseStep 1436759 = 2155139) B2155139
theorem B1436779 : Blo 1435537 1436779 := bstep (se 1 (by rfl) ⟨1077584, by rfl⟩ : syracuseStep 1436779 = 2155169) B2155169
theorem B1436791 : Blo 1435537 1436791 := bstep (se 1 (by rfl) ⟨1077593, by rfl⟩ : syracuseStep 1436791 = 2155187) B2155187
theorem B1436811 : Blo 1435537 1436811 := bstep (se 1 (by rfl) ⟨1077608, by rfl⟩ : syracuseStep 1436811 = 2155217) B2155217
theorem B1436823 : Blo 1435537 1436823 := bstep (se 1 (by rfl) ⟨1077617, by rfl⟩ : syracuseStep 1436823 = 2155235) B2155235
theorem B3230873 : Blo 1435537 3230873 := bstep (se 2 (by rfl) ⟨1211577, by rfl⟩ : syracuseStep 3230873 = 2423155) B2423155
theorem B1436843 : Blo 1435537 1436843 := bstep (se 1 (by rfl) ⟨1077632, by rfl⟩ : syracuseStep 1436843 = 2155265) B2155265
theorem B1436855 : Blo 1435537 1436855 := bstep (se 1 (by rfl) ⟨1077641, by rfl⟩ : syracuseStep 1436855 = 2155283) B2155283
theorem B1617079 : Blo 1435537 1617079 := bstep (se 1 (by rfl) ⟨1212809, by rfl⟩ : syracuseStep 1617079 = 2425619) B2425619
theorem B1436875 : Blo 1435537 1436875 := bstep (se 1 (by rfl) ⟨1077656, by rfl⟩ : syracuseStep 1436875 = 2155313) B2155313
theorem B15535309 : Blo 1435537 15535309 := bstep (se 3 (by rfl) ⟨2912870, by rfl⟩ : syracuseStep 15535309 = 5825741) B5825741
theorem B1436887 : Blo 1435537 1436887 := bstep (se 1 (by rfl) ⟨1077665, by rfl⟩ : syracuseStep 1436887 = 2155331) B2155331
theorem B1436907 : Blo 1435537 1436907 := bstep (se 1 (by rfl) ⟨1077680, by rfl⟩ : syracuseStep 1436907 = 2155361) B2155361
theorem B3230963 : Blo 1435537 3230963 := bstep (se 1 (by rfl) ⟨2423222, by rfl⟩ : syracuseStep 3230963 = 4846445) B4846445
theorem B1436919 : Blo 1435537 1436919 := bstep (se 1 (by rfl) ⟨1077689, by rfl⟩ : syracuseStep 1436919 = 2155379) B2155379
theorem B1436939 : Blo 1435537 1436939 := bstep (se 1 (by rfl) ⟨1077704, by rfl⟩ : syracuseStep 1436939 = 2155409) B2155409
theorem B3230999 : Blo 1435537 3230999 := bstep (se 1 (by rfl) ⟨2423249, by rfl⟩ : syracuseStep 3230999 = 4846499) B4846499
theorem B1436951 : Blo 1435537 1436951 := bstep (se 1 (by rfl) ⟨1077713, by rfl⟩ : syracuseStep 1436951 = 2155427) B2155427
theorem B1436971 : Blo 1435537 1436971 := bstep (se 1 (by rfl) ⟨1077728, by rfl⟩ : syracuseStep 1436971 = 2155457) B2155457
theorem B1436983 : Blo 1435537 1436983 := bstep (se 1 (by rfl) ⟨1077737, by rfl⟩ : syracuseStep 1436983 = 2155475) B2155475
theorem B5451083 : Blo 1435537 5451083 := bstep (se 1 (by rfl) ⟨4088312, by rfl⟩ : syracuseStep 5451083 = 8176625) B8176625
theorem B1437003 : Blo 1435537 1437003 := bstep (se 1 (by rfl) ⟨1077752, by rfl⟩ : syracuseStep 1437003 = 2155505) B2155505
theorem B1437015 : Blo 1435537 1437015 := bstep (se 1 (by rfl) ⟨1077761, by rfl⟩ : syracuseStep 1437015 = 2155523) B2155523
theorem B5451097 : Blo 1435537 5451097 := bstep (se 2 (by rfl) ⟨2044161, by rfl⟩ : syracuseStep 5451097 = 4088323) B4088323
theorem B1437035 : Blo 1435537 1437035 := bstep (se 1 (by rfl) ⟨1077776, by rfl⟩ : syracuseStep 1437035 = 2155553) B2155553
theorem B1437047 : Blo 1435537 1437047 := bstep (se 1 (by rfl) ⟨1077785, by rfl⟩ : syracuseStep 1437047 = 2155571) B2155571
theorem B1437067 : Blo 1435537 1437067 := bstep (se 1 (by rfl) ⟨1077800, by rfl⟩ : syracuseStep 1437067 = 2155601) B2155601
theorem B3452311 : Blo 1435537 3452311 := bstep (se 1 (by rfl) ⟨2589233, by rfl⟩ : syracuseStep 3452311 = 5178467) B5178467
theorem B1437079 : Blo 1435537 1437079 := bstep (se 1 (by rfl) ⟨1077809, by rfl⟩ : syracuseStep 1437079 = 2155619) B2155619
theorem B1437099 : Blo 1435537 1437099 := bstep (se 1 (by rfl) ⟨1077824, by rfl⟩ : syracuseStep 1437099 = 2155649) B2155649
theorem B1437111 : Blo 1435537 1437111 := bstep (se 1 (by rfl) ⟨1077833, by rfl⟩ : syracuseStep 1437111 = 2155667) B2155667
theorem B3231179 : Blo 1435537 3231179 := bstep (se 1 (by rfl) ⟨2423384, by rfl⟩ : syracuseStep 3231179 = 4846769) B4846769
theorem B1437131 : Blo 1435537 1437131 := bstep (se 1 (by rfl) ⟨1077848, by rfl⟩ : syracuseStep 1437131 = 2155697) B2155697
theorem B1437143 : Blo 1435537 1437143 := bstep (se 1 (by rfl) ⟨1077857, by rfl⟩ : syracuseStep 1437143 = 2155715) B2155715
theorem B1437163 : Blo 1435537 1437163 := bstep (se 1 (by rfl) ⟨1077872, by rfl⟩ : syracuseStep 1437163 = 2155745) B2155745
theorem B1437175 : Blo 1435537 1437175 := bstep (se 1 (by rfl) ⟨1077881, by rfl⟩ : syracuseStep 1437175 = 2155763) B2155763
theorem B3231233 : Blo 1435537 3231233 := bstep (se 2 (by rfl) ⟨1211712, by rfl⟩ : syracuseStep 3231233 = 2423425) B2423425
theorem B1437195 : Blo 1435537 1437195 := bstep (se 1 (by rfl) ⟨1077896, by rfl⟩ : syracuseStep 1437195 = 2155793) B2155793
theorem B1437207 : Blo 1435537 1437207 := bstep (se 1 (by rfl) ⟨1077905, by rfl⟩ : syracuseStep 1437207 = 2155811) B2155811
theorem B1437227 : Blo 1435537 1437227 := bstep (se 1 (by rfl) ⟨1077920, by rfl⟩ : syracuseStep 1437227 = 2155841) B2155841
theorem B1437239 : Blo 1435537 1437239 := bstep (se 1 (by rfl) ⟨1077929, by rfl⟩ : syracuseStep 1437239 = 2155859) B2155859
theorem B4091467 : Blo 1435537 4091467 := bstep (se 1 (by rfl) ⟨3068600, by rfl⟩ : syracuseStep 4091467 = 6137201) B6137201
theorem B1437259 : Blo 1435537 1437259 := bstep (se 1 (by rfl) ⟨1077944, by rfl⟩ : syracuseStep 1437259 = 2155889) B2155889
theorem B1437271 : Blo 1435537 1437271 := bstep (se 1 (by rfl) ⟨1077953, by rfl⟩ : syracuseStep 1437271 = 2155907) B2155907
theorem B4795993 : Blo 1435537 4795993 := bstep (se 2 (by rfl) ⟨1798497, by rfl⟩ : syracuseStep 4795993 = 3596995) B3596995
theorem B4845149 : Blo 1435537 4845149 := bstep (se 3 (by rfl) ⟨908465, by rfl⟩ : syracuseStep 4845149 = 1816931) B1816931
theorem B1437291 : Blo 1435537 1437291 := bstep (se 1 (by rfl) ⟨1077968, by rfl⟩ : syracuseStep 1437291 = 2155937) B2155937
theorem B3067507 : Blo 1435537 3067507 := bstep (se 1 (by rfl) ⟨2300630, by rfl⟩ : syracuseStep 3067507 = 4601261) B4601261
theorem B1437303 : Blo 1435537 1437303 := bstep (se 1 (by rfl) ⟨1077977, by rfl⟩ : syracuseStep 1437303 = 2155955) B2155955
theorem B2305675 : Blo 1435537 2305675 := bstep (se 1 (by rfl) ⟨1729256, by rfl⟩ : syracuseStep 2305675 = 3458513) B3458513
theorem B1437323 : Blo 1435537 1437323 := bstep (se 1 (by rfl) ⟨1077992, by rfl⟩ : syracuseStep 1437323 = 2155985) B2155985
theorem B1437335 : Blo 1435537 1437335 := bstep (se 1 (by rfl) ⟨1078001, by rfl⟩ : syracuseStep 1437335 = 2156003) B2156003
theorem B1437355 : Blo 1435537 1437355 := bstep (se 1 (by rfl) ⟨1078016, by rfl⟩ : syracuseStep 1437355 = 2156033) B2156033
theorem B1437367 : Blo 1435537 1437367 := bstep (se 1 (by rfl) ⟨1078025, by rfl⟩ : syracuseStep 1437367 = 2156051) B2156051
theorem B1437387 : Blo 1435537 1437387 := bstep (se 1 (by rfl) ⟨1078040, by rfl⟩ : syracuseStep 1437387 = 2156081) B2156081
theorem B41397965 : Blo 1435537 41397965 := bstep (se 3 (by rfl) ⟨7762118, by rfl⟩ : syracuseStep 41397965 = 15524237) B15524237
theorem B1437399 : Blo 1435537 1437399 := bstep (se 1 (by rfl) ⟨1078049, by rfl⟩ : syracuseStep 1437399 = 2156099) B2156099
theorem B3231449 : Blo 1435537 3231449 := bstep (se 2 (by rfl) ⟨1211793, by rfl⟩ : syracuseStep 3231449 = 2423587) B2423587
theorem B8736473 : Blo 1435537 8736473 := bstep (se 2 (by rfl) ⟨3276177, by rfl⟩ : syracuseStep 8736473 = 6552355) B6552355
theorem B1437419 : Blo 1435537 1437419 := bstep (se 1 (by rfl) ⟨1078064, by rfl⟩ : syracuseStep 1437419 = 2156129) B2156129
theorem B1437431 : Blo 1435537 1437431 := bstep (se 1 (by rfl) ⟨1078073, by rfl⟩ : syracuseStep 1437431 = 2156147) B2156147
theorem B1437451 : Blo 1435537 1437451 := bstep (se 1 (by rfl) ⟨1078088, by rfl⟩ : syracuseStep 1437451 = 2156177) B2156177
theorem B1437463 : Blo 1435537 1437463 := bstep (se 1 (by rfl) ⟨1078097, by rfl⟩ : syracuseStep 1437463 = 2156195) B2156195
theorem B1437483 : Blo 1435537 1437483 := bstep (se 1 (by rfl) ⟨1078112, by rfl⟩ : syracuseStep 1437483 = 2156225) B2156225
theorem B3231539 : Blo 1435537 3231539 := bstep (se 1 (by rfl) ⟨2423654, by rfl⟩ : syracuseStep 3231539 = 4847309) B4847309
theorem B1437495 : Blo 1435537 1437495 := bstep (se 1 (by rfl) ⟨1078121, by rfl⟩ : syracuseStep 1437495 = 2156243) B2156243
theorem B1437515 : Blo 1435537 1437515 := bstep (se 1 (by rfl) ⟨1078136, by rfl⟩ : syracuseStep 1437515 = 2156273) B2156273
theorem B3231575 : Blo 1435537 3231575 := bstep (se 1 (by rfl) ⟨2423681, by rfl⟩ : syracuseStep 3231575 = 4847363) B4847363
theorem B1437527 : Blo 1435537 1437527 := bstep (se 1 (by rfl) ⟨1078145, by rfl⟩ : syracuseStep 1437527 = 2156291) B2156291
theorem B4091741 : Blo 1435537 4091741 := bstep (se 3 (by rfl) ⟨767201, by rfl⟩ : syracuseStep 4091741 = 1534403) B1534403
theorem B6139799 : Blo 1435537 6139799 := bstep (se 1 (by rfl) ⟨4604849, by rfl⟩ : syracuseStep 6139799 = 9209699) B9209699
theorem B49745843 : Blo 1435537 49745843 := bstep (se 1 (by rfl) ⟨37309382, by rfl⟩ : syracuseStep 49745843 = 74618765) B74618765
theorem B3231755 : Blo 1435537 3231755 := bstep (se 1 (by rfl) ⟨2423816, by rfl⟩ : syracuseStep 3231755 = 4847633) B4847633
theorem B3231809 : Blo 1435537 3231809 := bstep (se 2 (by rfl) ⟨1211928, by rfl⟩ : syracuseStep 3231809 = 2423857) B2423857
theorem B3067969 : Blo 1435537 3067969 := bstep (se 2 (by rfl) ⟨1150488, by rfl⟩ : syracuseStep 3067969 = 2300977) B2300977
theorem B2043991 : Blo 1435537 2043991 := bstep (se 1 (by rfl) ⟨1532993, by rfl⟩ : syracuseStep 2043991 = 3065987) B3065987
theorem B5525597 : Blo 1435537 5525597 := bstep (se 3 (by rfl) ⟨1036049, by rfl⟩ : syracuseStep 5525597 = 2072099) B2072099
theorem B4092083 : Blo 1435537 4092083 := bstep (se 1 (by rfl) ⟨3069062, by rfl⟩ : syracuseStep 4092083 = 6138125) B6138125
theorem B22106317 : Blo 1435537 22106317 := bstep (se 3 (by rfl) ⟨4144934, by rfl⟩ : syracuseStep 22106317 = 8289869) B8289869
theorem B10916045 : Blo 1435537 10916045 := bstep (se 3 (by rfl) ⟨2046758, by rfl⟩ : syracuseStep 10916045 = 4093517) B4093517
theorem B5452055 : Blo 1435537 5452055 := bstep (se 1 (by rfl) ⟨4089041, by rfl⟩ : syracuseStep 5452055 = 8178083) B8178083
theorem B3232025 : Blo 1435537 3232025 := bstep (se 2 (by rfl) ⟨1212009, by rfl⟩ : syracuseStep 3232025 = 2424019) B2424019
theorem B7270721 : Blo 1435537 7270721 := bstep (se 2 (by rfl) ⟨2726520, by rfl⟩ : syracuseStep 7270721 = 5453041) B5453041
theorem B3232115 : Blo 1435537 3232115 := bstep (se 1 (by rfl) ⟨2424086, by rfl⟩ : syracuseStep 3232115 = 4848173) B4848173
theorem B3232151 : Blo 1435537 3232151 := bstep (se 1 (by rfl) ⟨2424113, by rfl⟩ : syracuseStep 3232151 = 4848227) B4848227
theorem B3232331 : Blo 1435537 3232331 := bstep (se 1 (by rfl) ⟨2424248, by rfl⟩ : syracuseStep 3232331 = 4848497) B4848497
theorem B3232385 : Blo 1435537 3232385 := bstep (se 2 (by rfl) ⟨1212144, by rfl⟩ : syracuseStep 3232385 = 2424289) B2424289
theorem B4846283 : Blo 1435537 4846283 := bstep (se 1 (by rfl) ⟨3634712, by rfl⟩ : syracuseStep 4846283 = 7269425) B7269425
theorem B3633943 : Blo 1435537 3633943 := bstep (se 1 (by rfl) ⟨2725457, by rfl⟩ : syracuseStep 3633943 = 5450915) B5450915
theorem B3068695 : Blo 1435537 3068695 := bstep (se 1 (by rfl) ⟨2301521, by rfl⟩ : syracuseStep 3068695 = 4603043) B4603043
theorem B3232601 : Blo 1435537 3232601 := bstep (se 2 (by rfl) ⟨1212225, by rfl⟩ : syracuseStep 3232601 = 2424451) B2424451
theorem B2044811 : Blo 1435537 2044811 := bstep (se 1 (by rfl) ⟨1533608, by rfl⟩ : syracuseStep 2044811 = 3067217) B3067217
theorem B3232691 : Blo 1435537 3232691 := bstep (se 1 (by rfl) ⟨2424518, by rfl⟩ : syracuseStep 3232691 = 4849037) B4849037
theorem B3232727 : Blo 1435537 3232727 := bstep (se 1 (by rfl) ⟨2424545, by rfl⟩ : syracuseStep 3232727 = 4849091) B4849091
theorem B4846553 : Blo 1435537 4846553 := bstep (se 2 (by rfl) ⟨1817457, by rfl⟩ : syracuseStep 4846553 = 3634915) B3634915
theorem B69874649 : Blo 1435537 69874649 := bstep (se 2 (by rfl) ⟨26202993, by rfl⟩ : syracuseStep 69874649 = 52405987) B52405987
theorem B2184215 : Blo 1435537 2184215 := bstep (se 1 (by rfl) ⟨1638161, by rfl⟩ : syracuseStep 2184215 = 3276323) B3276323
theorem B7476299 : Blo 1435537 7476299 := bstep (se 1 (by rfl) ⟨5607224, by rfl⟩ : syracuseStep 7476299 = 11214449) B11214449
theorem B3232907 : Blo 1435537 3232907 := bstep (se 1 (by rfl) ⟨2424680, by rfl⟩ : syracuseStep 3232907 = 4849361) B4849361
theorem B3232961 : Blo 1435537 3232961 := bstep (se 2 (by rfl) ⟨1212360, by rfl⟩ : syracuseStep 3232961 = 2424721) B2424721
theorem B3634379 : Blo 1435537 3634379 := bstep (se 1 (by rfl) ⟨2725784, by rfl⟩ : syracuseStep 3634379 = 5451569) B5451569
theorem B5174545 : Blo 1435537 5174545 := bstep (se 2 (by rfl) ⟨1940454, by rfl⟩ : syracuseStep 5174545 = 3880909) B3880909
theorem B12440897 : Blo 1435537 12440897 := bstep (se 2 (by rfl) ⟨4665336, by rfl⟩ : syracuseStep 12440897 = 9330673) B9330673
theorem B6133067 : Blo 1435537 6133067 := bstep (se 1 (by rfl) ⟨4599800, by rfl⟩ : syracuseStep 6133067 = 9199601) B9199601
theorem B11064707 : Blo 1435537 11064707 := bstep (se 1 (by rfl) ⟨8298530, by rfl⟩ : syracuseStep 11064707 = 16597061) B16597061
theorem B3233177 : Blo 1435537 3233177 := bstep (se 2 (by rfl) ⟨1212441, by rfl⟩ : syracuseStep 3233177 = 2424883) B2424883
theorem B3233267 : Blo 1435537 3233267 := bstep (se 1 (by rfl) ⟨2424950, by rfl⟩ : syracuseStep 3233267 = 4849901) B4849901
theorem B5453315 : Blo 1435537 5453315 := bstep (se 1 (by rfl) ⟨4089986, by rfl⟩ : syracuseStep 5453315 = 8179973) B8179973
theorem B9205265 : Blo 1435537 9205265 := bstep (se 2 (by rfl) ⟨3451974, by rfl⟩ : syracuseStep 9205265 = 6903949) B6903949
theorem B3233303 : Blo 1435537 3233303 := bstep (se 1 (by rfl) ⟨2424977, by rfl⟩ : syracuseStep 3233303 = 4849955) B4849955
theorem B2725427 : Blo 1435537 2725427 := bstep (se 1 (by rfl) ⟨2044070, by rfl⟩ : syracuseStep 2725427 = 4088141) B4088141
theorem B3634753 : Blo 1435537 3634753 := bstep (se 2 (by rfl) ⟨1363032, by rfl⟩ : syracuseStep 3634753 = 2726065) B2726065
theorem B3069515 : Blo 1435537 3069515 := bstep (se 1 (by rfl) ⟨2302136, by rfl⟩ : syracuseStep 3069515 = 4604273) B4604273
theorem B4847255 : Blo 1435537 4847255 := bstep (se 1 (by rfl) ⟨3635441, by rfl⟩ : syracuseStep 4847255 = 7270883) B7270883
theorem B6133427 : Blo 1435537 6133427 := bstep (se 1 (by rfl) ⟨4600070, by rfl⟩ : syracuseStep 6133427 = 9200141) B9200141
theorem B2725579 : Blo 1435537 2725579 := bstep (se 1 (by rfl) ⟨2044184, by rfl⟩ : syracuseStep 2725579 = 4088369) B4088369
theorem B3233483 : Blo 1435537 3233483 := bstep (se 1 (by rfl) ⟨2425112, by rfl⟩ : syracuseStep 3233483 = 4850225) B4850225
theorem B2422487 : Blo 1435537 2422487 := bstep (se 1 (by rfl) ⟨1816865, by rfl⟩ : syracuseStep 2422487 = 3633731) B3633731
theorem B3233537 : Blo 1435537 3233537 := bstep (se 2 (by rfl) ⟨1212576, by rfl⟩ : syracuseStep 3233537 = 2425153) B2425153
theorem B5822273 : Blo 1435537 5822273 := bstep (se 2 (by rfl) ⟨2183352, by rfl⟩ : syracuseStep 5822273 = 4366705) B4366705
theorem B2422615 : Blo 1435537 2422615 := bstep (se 1 (by rfl) ⟨1816961, by rfl⟩ : syracuseStep 2422615 = 3633923) B3633923
theorem B5601169 : Blo 1435537 5601169 := bstep (se 2 (by rfl) ⟨2100438, by rfl⟩ : syracuseStep 5601169 = 4200877) B4200877
theorem B2332567 : Blo 1435537 2332567 := bstep (se 1 (by rfl) ⟨1749425, by rfl⟩ : syracuseStep 2332567 = 3498851) B3498851
theorem B10901465 : Blo 1435537 10901465 := bstep (se 2 (by rfl) ⟨4088049, by rfl⟩ : syracuseStep 10901465 = 8176099) B8176099
theorem B3233753 : Blo 1435537 3233753 := bstep (se 2 (by rfl) ⟨1212657, by rfl⟩ : syracuseStep 3233753 = 2425315) B2425315
theorem B2725913 : Blo 1435537 2725913 := bstep (se 2 (by rfl) ⟨1022217, by rfl⟩ : syracuseStep 2725913 = 2044435) B2044435
theorem B3233843 : Blo 1435537 3233843 := bstep (se 1 (by rfl) ⟨2425382, by rfl⟩ : syracuseStep 3233843 = 4850765) B4850765
theorem B3233879 : Blo 1435537 3233879 := bstep (se 1 (by rfl) ⟨2425409, by rfl⟩ : syracuseStep 3233879 = 4850819) B4850819
theorem B3635351 : Blo 1435537 3635351 := bstep (se 1 (by rfl) ⟨2726513, by rfl⟩ : syracuseStep 3635351 = 5453027) B5453027
theorem B2455705 : Blo 1435537 2455705 := bstep (se 2 (by rfl) ⟨920889, by rfl⟩ : syracuseStep 2455705 = 1841779) B1841779
theorem B4847795 : Blo 1435537 4847795 := bstep (se 1 (by rfl) ⟨3635846, by rfl⟩ : syracuseStep 4847795 = 7271693) B7271693
theorem B3938483 : Blo 1435537 3938483 := bstep (se 1 (by rfl) ⟨2953862, by rfl⟩ : syracuseStep 3938483 = 5907725) B5907725
theorem B7272665 : Blo 1435537 7272665 := bstep (se 2 (by rfl) ⟨2727249, by rfl⟩ : syracuseStep 7272665 = 5454499) B5454499
theorem B3234059 : Blo 1435537 3234059 := bstep (se 1 (by rfl) ⟨2425544, by rfl⟩ : syracuseStep 3234059 = 4851089) B4851089
theorem B3234113 : Blo 1435537 3234113 := bstep (se 2 (by rfl) ⟨1212792, by rfl⟩ : syracuseStep 3234113 = 2425585) B2425585
theorem B1554871 : Blo 1435537 1554871 := bstep (se 1 (by rfl) ⟨1166153, by rfl⟩ : syracuseStep 1554871 = 2332307) B2332307
theorem B4848065 : Blo 1435537 4848065 := bstep (se 2 (by rfl) ⟨1818024, by rfl⟩ : syracuseStep 4848065 = 3636049) B3636049
theorem B2423243 : Blo 1435537 2423243 := bstep (se 1 (by rfl) ⟨1817432, by rfl⟩ : syracuseStep 2423243 = 3634865) B3634865
theorem B2300375 : Blo 1435537 2300375 := bstep (se 1 (by rfl) ⟨1725281, by rfl⟩ : syracuseStep 2300375 = 3450563) B3450563
theorem B10910213 : Blo 1435537 10910213 := bstep (se 4 (by rfl) ⟨1022832, by rfl⟩ : syracuseStep 10910213 = 2045665) B2045665
theorem B3234329 : Blo 1435537 3234329 := bstep (se 2 (by rfl) ⟨1212873, by rfl⟩ : syracuseStep 3234329 = 2425747) B2425747
theorem B5388851 : Blo 1435537 5388851 := bstep (se 1 (by rfl) ⟨4041638, by rfl⟩ : syracuseStep 5388851 = 8083277) B8083277
theorem B2423371 : Blo 1435537 2423371 := bstep (se 1 (by rfl) ⟨1817528, by rfl⟩ : syracuseStep 2423371 = 3635057) B3635057
theorem B3234419 : Blo 1435537 3234419 := bstep (se 1 (by rfl) ⟨2425814, by rfl⟩ : syracuseStep 3234419 = 4851629) B4851629
theorem B2726551 : Blo 1435537 2726551 := bstep (se 1 (by rfl) ⟨2044913, by rfl⟩ : syracuseStep 2726551 = 4089827) B4089827
theorem B3234455 : Blo 1435537 3234455 := bstep (se 1 (by rfl) ⟨2425841, by rfl⟩ : syracuseStep 3234455 = 4851683) B4851683
theorem B3111577 : Blo 1435537 3111577 := bstep (se 2 (by rfl) ⟨1166841, by rfl⟩ : syracuseStep 3111577 = 2333683) B2333683
theorem B2423513 : Blo 1435537 2423513 := bstep (se 2 (by rfl) ⟨908817, by rfl⟩ : syracuseStep 2423513 = 1817635) B1817635
theorem B4913885 : Blo 1435537 4913885 := bstep (se 3 (by rfl) ⟨921353, by rfl⟩ : syracuseStep 4913885 = 1842707) B1842707
theorem B24533765 : Blo 1435537 24533765 := bstep (se 4 (by rfl) ⟨2300040, by rfl⟩ : syracuseStep 24533765 = 4600081) B4600081
theorem B10353413 : Blo 1435537 10353413 := bstep (se 4 (by rfl) ⟨970632, by rfl⟩ : syracuseStep 10353413 = 1941265) B1941265
theorem B1456951 : Blo 1435537 1456951 := bstep (se 1 (by rfl) ⟨1092713, by rfl⟩ : syracuseStep 1456951 = 2185427) B2185427
theorem B2423641 : Blo 1435537 2423641 := bstep (se 2 (by rfl) ⟨908865, by rfl⟩ : syracuseStep 2423641 = 1817731) B1817731
theorem B3152729 : Blo 1435537 3152729 := bstep (se 2 (by rfl) ⟨1182273, by rfl⟩ : syracuseStep 3152729 = 2364547) B2364547
theorem B12270437 : Blo 1435537 12270437 := bstep (se 4 (by rfl) ⟨1150353, by rfl⟩ : syracuseStep 12270437 = 2300707) B2300707
theorem B2153369 : Blo 1435537 2153369 := bstep (se 2 (by rfl) ⟨807513, by rfl⟩ : syracuseStep 2153369 = 1615027) B1615027
theorem B3636161 : Blo 1435537 3636161 := bstep (se 2 (by rfl) ⟨1363560, by rfl⟩ : syracuseStep 3636161 = 2727121) B2727121
theorem B4848605 : Blo 1435537 4848605 := bstep (se 3 (by rfl) ⟨909113, by rfl⟩ : syracuseStep 4848605 = 1818227) B1818227
theorem B2153483 : Blo 1435537 2153483 := bstep (se 1 (by rfl) ⟨1615112, by rfl⟩ : syracuseStep 2153483 = 3230225) B3230225
theorem B14736401 : Blo 1435537 14736401 := bstep (se 2 (by rfl) ⟨5526150, by rfl⟩ : syracuseStep 14736401 = 11052301) B11052301
theorem B2153495 : Blo 1435537 2153495 := bstep (se 1 (by rfl) ⟨1615121, by rfl⟩ : syracuseStep 2153495 = 3230243) B3230243
theorem B53869637 : Blo 1435537 53869637 := bstep (se 4 (by rfl) ⟨5050278, by rfl⟩ : syracuseStep 53869637 = 10100557) B10100557
theorem B2153561 : Blo 1435537 2153561 := bstep (se 2 (by rfl) ⟨807585, by rfl⟩ : syracuseStep 2153561 = 1615171) B1615171
theorem B2153675 : Blo 1435537 2153675 := bstep (se 1 (by rfl) ⟨1615256, by rfl⟩ : syracuseStep 2153675 = 3230513) B3230513
theorem B2301131 : Blo 1435537 2301131 := bstep (se 1 (by rfl) ⟨1725848, by rfl⟩ : syracuseStep 2301131 = 3451697) B3451697
theorem B2153687 : Blo 1435537 2153687 := bstep (se 1 (by rfl) ⟨1615265, by rfl⟩ : syracuseStep 2153687 = 3230531) B3230531
theorem B2153753 : Blo 1435537 2153753 := bstep (se 2 (by rfl) ⟨807657, by rfl⟩ : syracuseStep 2153753 = 1615315) B1615315
theorem B2587979 : Blo 1435537 2587979 := bstep (se 1 (by rfl) ⟨1940984, by rfl⟩ : syracuseStep 2587979 = 3881969) B3881969
theorem B2153867 : Blo 1435537 2153867 := bstep (se 1 (by rfl) ⟨1615400, by rfl⟩ : syracuseStep 2153867 = 3230801) B3230801
theorem B2153879 : Blo 1435537 2153879 := bstep (se 1 (by rfl) ⟨1615409, by rfl⟩ : syracuseStep 2153879 = 3230819) B3230819
theorem B2424215 : Blo 1435537 2424215 := bstep (se 1 (by rfl) ⟨1818161, by rfl⟩ : syracuseStep 2424215 = 3636323) B3636323
theorem B2727371 : Blo 1435537 2727371 := bstep (se 1 (by rfl) ⟨2045528, by rfl⟩ : syracuseStep 2727371 = 4091057) B4091057
theorem B2153945 : Blo 1435537 2153945 := bstep (se 2 (by rfl) ⟨807729, by rfl⟩ : syracuseStep 2153945 = 1615459) B1615459
theorem B3636697 : Blo 1435537 3636697 := bstep (se 2 (by rfl) ⟨1363761, by rfl⟩ : syracuseStep 3636697 = 2727523) B2727523
theorem B2727425 : Blo 1435537 2727425 := bstep (se 2 (by rfl) ⟨1022784, by rfl⟩ : syracuseStep 2727425 = 2045569) B2045569
theorem B12271121 : Blo 1435537 12271121 := bstep (se 2 (by rfl) ⟨4601670, by rfl⟩ : syracuseStep 12271121 = 9203341) B9203341
theorem B2424343 : Blo 1435537 2424343 := bstep (se 1 (by rfl) ⟨1818257, by rfl⟩ : syracuseStep 2424343 = 3636515) B3636515
theorem B2154059 : Blo 1435537 2154059 := bstep (se 1 (by rfl) ⟨1615544, by rfl⟩ : syracuseStep 2154059 = 3231089) B3231089
theorem B2154071 : Blo 1435537 2154071 := bstep (se 1 (by rfl) ⟨1615553, by rfl⟩ : syracuseStep 2154071 = 3231107) B3231107
theorem B8183389 : Blo 1435537 8183389 := bstep (se 3 (by rfl) ⟨1534385, by rfl⟩ : syracuseStep 8183389 = 3068771) B3068771
theorem B1941131 : Blo 1435537 1941131 := bstep (se 1 (by rfl) ⟨1455848, by rfl⟩ : syracuseStep 1941131 = 2911697) B2911697
theorem B2588311 : Blo 1435537 2588311 := bstep (se 1 (by rfl) ⟨1941233, by rfl⟩ : syracuseStep 2588311 = 3882467) B3882467
theorem B2154137 : Blo 1435537 2154137 := bstep (se 2 (by rfl) ⟨807801, by rfl⟩ : syracuseStep 2154137 = 1615603) B1615603
theorem B2301643 : Blo 1435537 2301643 := bstep (se 1 (by rfl) ⟨1726232, by rfl⟩ : syracuseStep 2301643 = 3452465) B3452465
theorem B23289605 : Blo 1435537 23289605 := bstep (se 4 (by rfl) ⟨2183400, by rfl⟩ : syracuseStep 23289605 = 4366801) B4366801
theorem B2154251 : Blo 1435537 2154251 := bstep (se 1 (by rfl) ⟨1615688, by rfl⟩ : syracuseStep 2154251 = 3231377) B3231377
theorem B1818379 : Blo 1435537 1818379 := bstep (se 1 (by rfl) ⟨1363784, by rfl⟩ : syracuseStep 1818379 = 2727569) B2727569
theorem B2154263 : Blo 1435537 2154263 := bstep (se 1 (by rfl) ⟨1615697, by rfl⟩ : syracuseStep 2154263 = 3231395) B3231395
theorem B7274285 : Blo 1435537 7274285 := bstep (se 3 (by rfl) ⟨1363928, by rfl⟩ : syracuseStep 7274285 = 2727857) B2727857
theorem B2154329 : Blo 1435537 2154329 := bstep (se 2 (by rfl) ⟨807873, by rfl⟩ : syracuseStep 2154329 = 1615747) B1615747
theorem B11968357 : Blo 1435537 11968357 := bstep (se 4 (by rfl) ⟨1122033, by rfl⟩ : syracuseStep 11968357 = 2244067) B2244067
theorem B12443543 : Blo 1435537 12443543 := bstep (se 1 (by rfl) ⟨9332657, by rfl⟩ : syracuseStep 12443543 = 18665315) B18665315
theorem B6307777 : Blo 1435537 6307777 := bstep (se 2 (by rfl) ⟨2365416, by rfl⟩ : syracuseStep 6307777 = 4730833) B4730833
theorem B2154443 : Blo 1435537 2154443 := bstep (se 1 (by rfl) ⟨1615832, by rfl⟩ : syracuseStep 2154443 = 3231665) B3231665
theorem B2154455 : Blo 1435537 2154455 := bstep (se 1 (by rfl) ⟨1615841, by rfl⟩ : syracuseStep 2154455 = 3231683) B3231683
theorem B5824477 : Blo 1435537 5824477 := bstep (se 3 (by rfl) ⟨1092089, by rfl⟩ : syracuseStep 5824477 = 2184179) B2184179
theorem B2154503 : Blo 1435537 2154503 := bstep (se 1 (by rfl) ⟨1615877, by rfl⟩ : syracuseStep 2154503 = 3231755) B3231755
theorem B2154539 : Blo 1435537 2154539 := bstep (se 1 (by rfl) ⟨1615904, by rfl⟩ : syracuseStep 2154539 = 3231809) B3231809
theorem B12279869 : Blo 1435537 12279869 := bstep (se 3 (by rfl) ⟨2302475, by rfl⟩ : syracuseStep 12279869 = 4604951) B4604951
theorem B2154569 : Blo 1435537 2154569 := bstep (se 2 (by rfl) ⟨807963, by rfl⟩ : syracuseStep 2154569 = 1615927) B1615927
theorem B31072349 : Blo 1435537 31072349 := bstep (se 3 (by rfl) ⟨5826065, by rfl⟩ : syracuseStep 31072349 = 11652131) B11652131
theorem B7372919 : Blo 1435537 7372919 := bstep (se 1 (by rfl) ⟨5529689, by rfl⟩ : syracuseStep 7372919 = 11059379) B11059379
theorem B2728055 : Blo 1435537 2728055 := bstep (se 1 (by rfl) ⟨2046041, by rfl⟩ : syracuseStep 2728055 = 4092083) B4092083
theorem B2154683 : Blo 1435537 2154683 := bstep (se 1 (by rfl) ⟨1616012, by rfl⟩ : syracuseStep 2154683 = 3232025) B3232025
theorem B23298293 : Blo 1435537 23298293 := bstep (se 5 (by rfl) ⟨1092107, by rfl⟩ : syracuseStep 23298293 = 2184215) B2184215
theorem B2154743 : Blo 1435537 2154743 := bstep (se 1 (by rfl) ⟨1616057, by rfl⟩ : syracuseStep 2154743 = 3232115) B3232115
theorem B2154767 : Blo 1435537 2154767 := bstep (se 1 (by rfl) ⟨1616075, by rfl⟩ : syracuseStep 2154767 = 3232151) B3232151
theorem B29475089 : Blo 1435537 29475089 := bstep (se 2 (by rfl) ⟨11053158, by rfl⟩ : syracuseStep 29475089 = 22106317) B22106317
theorem B2154809 : Blo 1435537 2154809 := bstep (se 2 (by rfl) ⟨808053, by rfl⟩ : syracuseStep 2154809 = 1616107) B1616107
theorem B3637619 : Blo 1435537 3637619 := bstep (se 1 (by rfl) ⟨2728214, by rfl⟩ : syracuseStep 3637619 = 5456429) B5456429
theorem B2425207 : Blo 1435537 2425207 := bstep (se 1 (by rfl) ⟨1818905, by rfl⟩ : syracuseStep 2425207 = 3637811) B3637811
theorem B2154887 : Blo 1435537 2154887 := bstep (se 1 (by rfl) ⟨1616165, by rfl⟩ : syracuseStep 2154887 = 3232331) B3232331
theorem B298418579 : Blo 1435537 298418579 := bstep (se 1 (by rfl) ⟨223813934, by rfl⟩ : syracuseStep 298418579 = 447627869) B447627869
theorem B2154923 : Blo 1435537 2154923 := bstep (se 1 (by rfl) ⟨1616192, by rfl⟩ : syracuseStep 2154923 = 3232385) B3232385
theorem B2154953 : Blo 1435537 2154953 := bstep (se 2 (by rfl) ⟨808107, by rfl⟩ : syracuseStep 2154953 = 1616215) B1616215
theorem B10502621 : Blo 1435537 10502621 := bstep (se 3 (by rfl) ⟨1969241, by rfl⟩ : syracuseStep 10502621 = 3938483) B3938483
theorem B3277345 : Blo 1435537 3277345 := bstep (se 2 (by rfl) ⟨1229004, by rfl⟩ : syracuseStep 3277345 = 2458009) B2458009
theorem B2155067 : Blo 1435537 2155067 := bstep (se 1 (by rfl) ⟨1616300, by rfl⟩ : syracuseStep 2155067 = 3232601) B3232601
theorem B2425403 : Blo 1435537 2425403 := bstep (se 1 (by rfl) ⟨1819052, by rfl⟩ : syracuseStep 2425403 = 3638105) B3638105
theorem B2073161 : Blo 1435537 2073161 := bstep (se 2 (by rfl) ⟨777435, by rfl⟩ : syracuseStep 2073161 = 1554871) B1554871
theorem B4915799 : Blo 1435537 4915799 := bstep (se 1 (by rfl) ⟨3686849, by rfl⟩ : syracuseStep 4915799 = 7373699) B7373699
theorem B7275095 : Blo 1435537 7275095 := bstep (se 1 (by rfl) ⟨5456321, by rfl⟩ : syracuseStep 7275095 = 10912643) B10912643
theorem B2155127 : Blo 1435537 2155127 := bstep (se 1 (by rfl) ⟨1616345, by rfl⟩ : syracuseStep 2155127 = 3232691) B3232691
theorem B1819255 : Blo 1435537 1819255 := bstep (se 1 (by rfl) ⟨1364441, by rfl⟩ : syracuseStep 1819255 = 2728883) B2728883
theorem B2155151 : Blo 1435537 2155151 := bstep (se 1 (by rfl) ⟨1616363, by rfl⟩ : syracuseStep 2155151 = 3232727) B3232727
theorem B2155193 : Blo 1435537 2155193 := bstep (se 2 (by rfl) ⟨808197, by rfl⟩ : syracuseStep 2155193 = 1616395) B1616395
theorem B12296933 : Blo 1435537 12296933 := bstep (se 4 (by rfl) ⟨1152837, by rfl⟩ : syracuseStep 12296933 = 2305675) B2305675
theorem B2155271 : Blo 1435537 2155271 := bstep (se 1 (by rfl) ⟨1616453, by rfl⟩ : syracuseStep 2155271 = 3232907) B3232907
theorem B2155307 : Blo 1435537 2155307 := bstep (se 1 (by rfl) ⟨1616480, by rfl⟩ : syracuseStep 2155307 = 3232961) B3232961
theorem B2155337 : Blo 1435537 2155337 := bstep (se 2 (by rfl) ⟨808251, by rfl⟩ : syracuseStep 2155337 = 1616503) B1616503
theorem B8184665 : Blo 1435537 8184665 := bstep (se 2 (by rfl) ⟨3069249, by rfl⟩ : syracuseStep 8184665 = 6138499) B6138499
theorem B3638135 : Blo 1435537 3638135 := bstep (se 1 (by rfl) ⟨2728601, by rfl⟩ : syracuseStep 3638135 = 5457203) B5457203
theorem B4088711 : Blo 1435537 4088711 := bstep (se 1 (by rfl) ⟨3066533, by rfl⟩ : syracuseStep 4088711 = 6133067) B6133067
theorem B2155451 : Blo 1435537 2155451 := bstep (se 1 (by rfl) ⟨1616588, by rfl⟩ : syracuseStep 2155451 = 3233177) B3233177
theorem B2425801 : Blo 1435537 2425801 := bstep (se 2 (by rfl) ⟨909675, by rfl⟩ : syracuseStep 2425801 = 1819351) B1819351
theorem B2155511 : Blo 1435537 2155511 := bstep (se 1 (by rfl) ⟨1616633, by rfl⟩ : syracuseStep 2155511 = 3233267) B3233267
theorem B6136843 : Blo 1435537 6136843 := bstep (se 1 (by rfl) ⟨4602632, by rfl⟩ : syracuseStep 6136843 = 9205265) B9205265
theorem B2155535 : Blo 1435537 2155535 := bstep (se 1 (by rfl) ⟨1616651, by rfl⟩ : syracuseStep 2155535 = 3233303) B3233303
theorem B2458667 : Blo 1435537 2458667 := bstep (se 1 (by rfl) ⟨1844000, by rfl⟩ : syracuseStep 2458667 = 3688001) B3688001
theorem B2155577 : Blo 1435537 2155577 := bstep (se 2 (by rfl) ⟨808341, by rfl⟩ : syracuseStep 2155577 = 1616683) B1616683
theorem B4088893 : Blo 1435537 4088893 := bstep (se 3 (by rfl) ⟨766667, by rfl⟩ : syracuseStep 4088893 = 1533335) B1533335
theorem B7275581 : Blo 1435537 7275581 := bstep (se 3 (by rfl) ⟨1364171, by rfl⟩ : syracuseStep 7275581 = 2728343) B2728343
theorem B1942601 : Blo 1435537 1942601 := bstep (se 2 (by rfl) ⟨728475, by rfl⟩ : syracuseStep 1942601 = 1456951) B1456951
theorem B4088951 : Blo 1435537 4088951 := bstep (se 1 (by rfl) ⟨3066713, by rfl⟩ : syracuseStep 4088951 = 6133427) B6133427
theorem B2155655 : Blo 1435537 2155655 := bstep (se 1 (by rfl) ⟨1616741, by rfl⟩ : syracuseStep 2155655 = 3233483) B3233483
theorem B1614991 : Blo 1435537 1614991 := bstep (se 1 (by rfl) ⟨1211243, by rfl⟩ : syracuseStep 1614991 = 2422487) B2422487
theorem B2155691 : Blo 1435537 2155691 := bstep (se 1 (by rfl) ⟨1616768, by rfl⟩ : syracuseStep 2155691 = 3233537) B3233537
theorem B2155721 : Blo 1435537 2155721 := bstep (se 2 (by rfl) ⟨808395, by rfl⟩ : syracuseStep 2155721 = 1616791) B1616791
theorem B4916513 : Blo 1435537 4916513 := bstep (se 2 (by rfl) ⟨1843692, by rfl⟩ : syracuseStep 4916513 = 3687385) B3687385
theorem B8185121 : Blo 1435537 8185121 := bstep (se 2 (by rfl) ⟨3069420, by rfl⟩ : syracuseStep 8185121 = 6138841) B6138841
theorem B7267643 : Blo 1435537 7267643 := bstep (se 1 (by rfl) ⟨5450732, by rfl⟩ : syracuseStep 7267643 = 10901465) B10901465
theorem B2155835 : Blo 1435537 2155835 := bstep (se 1 (by rfl) ⟨1616876, by rfl⟩ : syracuseStep 2155835 = 3233753) B3233753
theorem B4605299 : Blo 1435537 4605299 := bstep (se 1 (by rfl) ⟨3453974, by rfl⟩ : syracuseStep 4605299 = 6907949) B6907949
theorem B2155895 : Blo 1435537 2155895 := bstep (se 1 (by rfl) ⟨1616921, by rfl⟩ : syracuseStep 2155895 = 3233843) B3233843
theorem B2155919 : Blo 1435537 2155919 := bstep (se 1 (by rfl) ⟨1616939, by rfl⟩ : syracuseStep 2155919 = 3233879) B3233879
theorem B2155961 : Blo 1435537 2155961 := bstep (se 2 (by rfl) ⟨808485, by rfl⟩ : syracuseStep 2155961 = 1616971) B1616971
theorem B7267805 : Blo 1435537 7267805 := bstep (se 3 (by rfl) ⟨1362713, by rfl⟩ : syracuseStep 7267805 = 2725427) B2725427
theorem B2156039 : Blo 1435537 2156039 := bstep (se 1 (by rfl) ⟨1617029, by rfl⟩ : syracuseStep 2156039 = 3234059) B3234059
theorem B11060765 : Blo 1435537 11060765 := bstep (se 3 (by rfl) ⟨2073893, by rfl⟩ : syracuseStep 11060765 = 4147787) B4147787
theorem B8185373 : Blo 1435537 8185373 := bstep (se 3 (by rfl) ⟨1534757, by rfl⟩ : syracuseStep 8185373 = 3069515) B3069515
theorem B2156075 : Blo 1435537 2156075 := bstep (se 1 (by rfl) ⟨1617056, by rfl⟩ : syracuseStep 2156075 = 3234113) B3234113
theorem B2156105 : Blo 1435537 2156105 := bstep (se 2 (by rfl) ⟨808539, by rfl⟩ : syracuseStep 2156105 = 1617079) B1617079
theorem B1615495 : Blo 1435537 1615495 := bstep (se 1 (by rfl) ⟨1211621, by rfl⟩ : syracuseStep 1615495 = 2423243) B2423243
theorem B1533583 : Blo 1435537 1533583 := bstep (se 1 (by rfl) ⟨1150187, by rfl⟩ : syracuseStep 1533583 = 2300375) B2300375
theorem B2156219 : Blo 1435537 2156219 := bstep (se 1 (by rfl) ⟨1617164, by rfl⟩ : syracuseStep 2156219 = 3234329) B3234329
theorem B6899393 : Blo 1435537 6899393 := bstep (se 2 (by rfl) ⟨2587272, by rfl⟩ : syracuseStep 6899393 = 5174545) B5174545
theorem B2156279 : Blo 1435537 2156279 := bstep (se 1 (by rfl) ⟨1617209, by rfl⟩ : syracuseStep 2156279 = 3234419) B3234419
theorem B2156303 : Blo 1435537 2156303 := bstep (se 1 (by rfl) ⟨1617227, by rfl⟩ : syracuseStep 2156303 = 3234455) B3234455
theorem B7268129 : Blo 1435537 7268129 := bstep (se 2 (by rfl) ⟨2725548, by rfl⟩ : syracuseStep 7268129 = 5451097) B5451097
theorem B6899507 : Blo 1435537 6899507 := bstep (se 1 (by rfl) ⟨5174630, by rfl⟩ : syracuseStep 6899507 = 10349261) B10349261
theorem B1615675 : Blo 1435537 1615675 := bstep (se 1 (by rfl) ⟨1211756, by rfl⟩ : syracuseStep 1615675 = 2423513) B2423513
theorem B1435579 : Blo 1435537 1435579 := bstep (se 1 (by rfl) ⟨1076684, by rfl⟩ : syracuseStep 1435579 = 2153369) B2153369
theorem B1435655 : Blo 1435537 1435655 := bstep (se 1 (by rfl) ⟨1076741, by rfl⟩ : syracuseStep 1435655 = 2153483) B2153483
theorem B9824267 : Blo 1435537 9824267 := bstep (se 1 (by rfl) ⟨7368200, by rfl⟩ : syracuseStep 9824267 = 14736401) B14736401
theorem B1435663 : Blo 1435537 1435663 := bstep (se 1 (by rfl) ⟨1076747, by rfl⟩ : syracuseStep 1435663 = 2153495) B2153495
theorem B1435707 : Blo 1435537 1435707 := bstep (se 1 (by rfl) ⟨1076780, by rfl⟩ : syracuseStep 1435707 = 2153561) B2153561
theorem B1435783 : Blo 1435537 1435783 := bstep (se 1 (by rfl) ⟨1076837, by rfl⟩ : syracuseStep 1435783 = 2153675) B2153675
theorem B1534087 : Blo 1435537 1534087 := bstep (se 1 (by rfl) ⟨1150565, by rfl⟩ : syracuseStep 1534087 = 2301131) B2301131
theorem B1435791 : Blo 1435537 1435791 := bstep (se 1 (by rfl) ⟨1076843, by rfl⟩ : syracuseStep 1435791 = 2153687) B2153687
theorem B4090009 : Blo 1435537 4090009 := bstep (se 2 (by rfl) ⟨1533753, by rfl⟩ : syracuseStep 4090009 = 3067507) B3067507
theorem B36833453 : Blo 1435537 36833453 := bstep (se 3 (by rfl) ⟨6906272, by rfl⟩ : syracuseStep 36833453 = 13812545) B13812545
theorem B1435835 : Blo 1435537 1435835 := bstep (se 1 (by rfl) ⟨1076876, by rfl⟩ : syracuseStep 1435835 = 2153753) B2153753
theorem B3451081 : Blo 1435537 3451081 := bstep (se 2 (by rfl) ⟨1294155, by rfl⟩ : syracuseStep 3451081 = 2588311) B2588311
theorem B8407277 : Blo 1435537 8407277 := bstep (se 3 (by rfl) ⟨1576364, by rfl⟩ : syracuseStep 8407277 = 3152729) B3152729
theorem B34081013 : Blo 1435537 34081013 := bstep (se 5 (by rfl) ⟨1597547, by rfl⟩ : syracuseStep 34081013 = 3195095) B3195095
theorem B1435911 : Blo 1435537 1435911 := bstep (se 1 (by rfl) ⟨1076933, by rfl⟩ : syracuseStep 1435911 = 2153867) B2153867
theorem B1435919 : Blo 1435537 1435919 := bstep (se 1 (by rfl) ⟨1076939, by rfl⟩ : syracuseStep 1435919 = 2153879) B2153879
theorem B1616143 : Blo 1435537 1616143 := bstep (se 1 (by rfl) ⟨1212107, by rfl⟩ : syracuseStep 1616143 = 2424215) B2424215
theorem B1435963 : Blo 1435537 1435963 := bstep (se 1 (by rfl) ⟨1076972, by rfl⟩ : syracuseStep 1435963 = 2153945) B2153945
theorem B1436039 : Blo 1435537 1436039 := bstep (se 1 (by rfl) ⟨1077029, by rfl⟩ : syracuseStep 1436039 = 2154059) B2154059
theorem B1436047 : Blo 1435537 1436047 := bstep (se 1 (by rfl) ⟨1077035, by rfl⟩ : syracuseStep 1436047 = 2154071) B2154071
theorem B3230099 : Blo 1435537 3230099 := bstep (se 1 (by rfl) ⟨2422574, by rfl⟩ : syracuseStep 3230099 = 4845149) B4845149
theorem B1436091 : Blo 1435537 1436091 := bstep (se 1 (by rfl) ⟨1077068, by rfl⟩ : syracuseStep 1436091 = 2154137) B2154137
theorem B3230153 : Blo 1435537 3230153 := bstep (se 2 (by rfl) ⟨1211307, by rfl⟩ : syracuseStep 3230153 = 2422615) B2422615
theorem B9832913 : Blo 1435537 9832913 := bstep (se 2 (by rfl) ⟨3687342, by rfl⟩ : syracuseStep 9832913 = 7374685) B7374685
theorem B15526403 : Blo 1435537 15526403 := bstep (se 1 (by rfl) ⟨11644802, by rfl⟩ : syracuseStep 15526403 = 23289605) B23289605
theorem B1436167 : Blo 1435537 1436167 := bstep (se 1 (by rfl) ⟨1077125, by rfl⟩ : syracuseStep 1436167 = 2154251) B2154251
theorem B1436175 : Blo 1435537 1436175 := bstep (se 1 (by rfl) ⟨1077131, by rfl⟩ : syracuseStep 1436175 = 2154263) B2154263
theorem B1436219 : Blo 1435537 1436219 := bstep (se 1 (by rfl) ⟨1077164, by rfl⟩ : syracuseStep 1436219 = 2154329) B2154329
theorem B33163895 : Blo 1435537 33163895 := bstep (se 1 (by rfl) ⟨24872921, by rfl⟩ : syracuseStep 33163895 = 49745843) B49745843
theorem B1436295 : Blo 1435537 1436295 := bstep (se 1 (by rfl) ⟨1077221, by rfl⟩ : syracuseStep 1436295 = 2154443) B2154443
theorem B1436303 : Blo 1435537 1436303 := bstep (se 1 (by rfl) ⟨1077227, by rfl⟩ : syracuseStep 1436303 = 2154455) B2154455
theorem B1436347 : Blo 1435537 1436347 := bstep (se 1 (by rfl) ⟨1077260, by rfl⟩ : syracuseStep 1436347 = 2154521) B2154521
theorem B7269101 : Blo 1435537 7269101 := bstep (se 3 (by rfl) ⟨1362956, by rfl⟩ : syracuseStep 7269101 = 2725913) B2725913
theorem B4090625 : Blo 1435537 4090625 := bstep (se 2 (by rfl) ⟨1533984, by rfl⟩ : syracuseStep 4090625 = 3067969) B3067969
theorem B1436423 : Blo 1435537 1436423 := bstep (se 1 (by rfl) ⟨1077317, by rfl⟩ : syracuseStep 1436423 = 2154635) B2154635
theorem B1616647 : Blo 1435537 1616647 := bstep (se 1 (by rfl) ⟨1212485, by rfl⟩ : syracuseStep 1616647 = 2424971) B2424971
theorem B1436431 : Blo 1435537 1436431 := bstep (se 1 (by rfl) ⟨1077323, by rfl⟩ : syracuseStep 1436431 = 2154647) B2154647
theorem B10357541 : Blo 1435537 10357541 := bstep (se 4 (by rfl) ⟨971019, by rfl⟩ : syracuseStep 10357541 = 1942039) B1942039
theorem B7277363 : Blo 1435537 7277363 := bstep (se 1 (by rfl) ⟨5458022, by rfl⟩ : syracuseStep 7277363 = 10916045) B10916045
theorem B1436475 : Blo 1435537 1436475 := bstep (se 1 (by rfl) ⟨1077356, by rfl⟩ : syracuseStep 1436475 = 2154713) B2154713
theorem B5450611 : Blo 1435537 5450611 := bstep (se 1 (by rfl) ⟨4087958, by rfl⟩ : syracuseStep 5450611 = 8175917) B8175917
theorem B1436551 : Blo 1435537 1436551 := bstep (se 1 (by rfl) ⟨1077413, by rfl⟩ : syracuseStep 1436551 = 2154827) B2154827
theorem B1436559 : Blo 1435537 1436559 := bstep (se 1 (by rfl) ⟨1077419, by rfl⟩ : syracuseStep 1436559 = 2154839) B2154839
theorem B1436603 : Blo 1435537 1436603 := bstep (se 1 (by rfl) ⟨1077452, by rfl⟩ : syracuseStep 1436603 = 2154905) B2154905
theorem B1616827 : Blo 1435537 1616827 := bstep (se 1 (by rfl) ⟨1212620, by rfl⟩ : syracuseStep 1616827 = 2425241) B2425241
theorem B1534907 : Blo 1435537 1534907 := bstep (se 1 (by rfl) ⟨1151180, by rfl⟩ : syracuseStep 1534907 = 2302361) B2302361
theorem B1436679 : Blo 1435537 1436679 := bstep (se 1 (by rfl) ⟨1077509, by rfl⟩ : syracuseStep 1436679 = 2155019) B2155019
theorem B1436687 : Blo 1435537 1436687 := bstep (se 1 (by rfl) ⟨1077515, by rfl⟩ : syracuseStep 1436687 = 2155031) B2155031
theorem B1436731 : Blo 1435537 1436731 := bstep (se 1 (by rfl) ⟨1077548, by rfl⟩ : syracuseStep 1436731 = 2155097) B2155097
theorem B1535035 : Blo 1435537 1535035 := bstep (se 1 (by rfl) ⟨1151276, by rfl⟩ : syracuseStep 1535035 = 2302553) B2302553
theorem B11054141 : Blo 1435537 11054141 := bstep (se 3 (by rfl) ⟨2072651, by rfl⟩ : syracuseStep 11054141 = 4145303) B4145303
theorem B25578629 : Blo 1435537 25578629 := bstep (se 4 (by rfl) ⟨2397996, by rfl⟩ : syracuseStep 25578629 = 4795993) B4795993
theorem B3230855 : Blo 1435537 3230855 := bstep (se 1 (by rfl) ⟨2423141, by rfl⟩ : syracuseStep 3230855 = 4846283) B4846283
theorem B1436807 : Blo 1435537 1436807 := bstep (se 1 (by rfl) ⟨1077605, by rfl⟩ : syracuseStep 1436807 = 2155211) B2155211
theorem B1436815 : Blo 1435537 1436815 := bstep (se 1 (by rfl) ⟨1077611, by rfl⟩ : syracuseStep 1436815 = 2155223) B2155223
theorem B1436859 : Blo 1435537 1436859 := bstep (se 1 (by rfl) ⟨1077644, by rfl⟩ : syracuseStep 1436859 = 2155289) B2155289
theorem B1436935 : Blo 1435537 1436935 := bstep (se 1 (by rfl) ⟨1077701, by rfl⟩ : syracuseStep 1436935 = 2155403) B2155403
theorem B1436943 : Blo 1435537 1436943 := bstep (se 1 (by rfl) ⟨1077707, by rfl⟩ : syracuseStep 1436943 = 2155415) B2155415
theorem B13798673 : Blo 1435537 13798673 := bstep (se 2 (by rfl) ⟨5174502, by rfl⟩ : syracuseStep 13798673 = 10349005) B10349005
theorem B3231035 : Blo 1435537 3231035 := bstep (se 1 (by rfl) ⟨2423276, by rfl⟩ : syracuseStep 3231035 = 4846553) B4846553
theorem B46583099 : Blo 1435537 46583099 := bstep (se 1 (by rfl) ⟨34937324, by rfl⟩ : syracuseStep 46583099 = 69874649) B69874649
theorem B1436987 : Blo 1435537 1436987 := bstep (se 1 (by rfl) ⟨1077740, by rfl⟩ : syracuseStep 1436987 = 2155481) B2155481
theorem B1437063 : Blo 1435537 1437063 := bstep (se 1 (by rfl) ⟨1077797, by rfl⟩ : syracuseStep 1437063 = 2155595) B2155595
theorem B4984199 : Blo 1435537 4984199 := bstep (se 1 (by rfl) ⟨3738149, by rfl⟩ : syracuseStep 4984199 = 7476299) B7476299
theorem B1437071 : Blo 1435537 1437071 := bstep (se 1 (by rfl) ⟨1077803, by rfl⟩ : syracuseStep 1437071 = 2155607) B2155607
theorem B3231161 : Blo 1435537 3231161 := bstep (se 2 (by rfl) ⟨1211685, by rfl⟩ : syracuseStep 3231161 = 2423371) B2423371
theorem B1437115 : Blo 1435537 1437115 := bstep (se 1 (by rfl) ⟨1077836, by rfl⟩ : syracuseStep 1437115 = 2155673) B2155673
theorem B1437191 : Blo 1435537 1437191 := bstep (se 1 (by rfl) ⟨1077893, by rfl⟩ : syracuseStep 1437191 = 2155787) B2155787
theorem B1437199 : Blo 1435537 1437199 := bstep (se 1 (by rfl) ⟨1077899, by rfl⟩ : syracuseStep 1437199 = 2155799) B2155799
theorem B7269911 : Blo 1435537 7269911 := bstep (se 1 (by rfl) ⟨5452433, by rfl⟩ : syracuseStep 7269911 = 10904867) B10904867
theorem B8293931 : Blo 1435537 8293931 := bstep (se 1 (by rfl) ⟨6220448, by rfl⟩ : syracuseStep 8293931 = 12440897) B12440897
theorem B1437243 : Blo 1435537 1437243 := bstep (se 1 (by rfl) ⟨1077932, by rfl⟩ : syracuseStep 1437243 = 2155865) B2155865
theorem B7376471 : Blo 1435537 7376471 := bstep (se 1 (by rfl) ⟨5532353, by rfl⟩ : syracuseStep 7376471 = 11064707) B11064707
theorem B1437319 : Blo 1435537 1437319 := bstep (se 1 (by rfl) ⟨1077989, by rfl⟩ : syracuseStep 1437319 = 2155979) B2155979
theorem B1437327 : Blo 1435537 1437327 := bstep (se 1 (by rfl) ⟨1077995, by rfl⟩ : syracuseStep 1437327 = 2155991) B2155991
theorem B1437371 : Blo 1435537 1437371 := bstep (se 1 (by rfl) ⟨1078028, by rfl⟩ : syracuseStep 1437371 = 2156057) B2156057
theorem B4845257 : Blo 1435537 4845257 := bstep (se 2 (by rfl) ⟨1816971, by rfl⟩ : syracuseStep 4845257 = 3633943) B3633943
theorem B4091593 : Blo 1435537 4091593 := bstep (se 2 (by rfl) ⟨1534347, by rfl⟩ : syracuseStep 4091593 = 3068695) B3068695
theorem B1437447 : Blo 1435537 1437447 := bstep (se 1 (by rfl) ⟨1078085, by rfl⟩ : syracuseStep 1437447 = 2156171) B2156171
theorem B3231503 : Blo 1435537 3231503 := bstep (se 1 (by rfl) ⟨2423627, by rfl⟩ : syracuseStep 3231503 = 4847255) B4847255
theorem B1437455 : Blo 1435537 1437455 := bstep (se 1 (by rfl) ⟨1078091, by rfl⟩ : syracuseStep 1437455 = 2156183) B2156183
theorem B3231521 : Blo 1435537 3231521 := bstep (se 2 (by rfl) ⟨1211820, by rfl⟩ : syracuseStep 3231521 = 2423641) B2423641
theorem B1437499 : Blo 1435537 1437499 := bstep (se 1 (by rfl) ⟨1078124, by rfl⟩ : syracuseStep 1437499 = 2156249) B2156249
theorem B3231863 : Blo 1435537 3231863 := bstep (se 1 (by rfl) ⟨2423897, by rfl⟩ : syracuseStep 3231863 = 4847795) B4847795
theorem B20713745 : Blo 1435537 20713745 := bstep (se 2 (by rfl) ⟨7767654, by rfl⟩ : syracuseStep 20713745 = 15535309) B15535309
theorem B3232043 : Blo 1435537 3232043 := bstep (se 1 (by rfl) ⟨2424032, by rfl⟩ : syracuseStep 3232043 = 4848065) B4848065
theorem B2044219 : Blo 1435537 2044219 := bstep (se 1 (by rfl) ⟨1533164, by rfl⟩ : syracuseStep 2044219 = 3066329) B3066329
theorem B3592567 : Blo 1435537 3592567 := bstep (se 1 (by rfl) ⟨2694425, by rfl⟩ : syracuseStep 3592567 = 5388851) B5388851
theorem B4845959 : Blo 1435537 4845959 := bstep (se 1 (by rfl) ⟨3634469, by rfl⟩ : syracuseStep 4845959 = 7268939) B7268939
theorem B16355843 : Blo 1435537 16355843 := bstep (se 1 (by rfl) ⟨12266882, by rfl⟩ : syracuseStep 16355843 = 24533765) B24533765
theorem B11055619 : Blo 1435537 11055619 := bstep (se 1 (by rfl) ⟨8291714, by rfl⟩ : syracuseStep 11055619 = 16583429) B16583429
theorem B6902275 : Blo 1435537 6902275 := bstep (se 1 (by rfl) ⟨5176706, by rfl⟩ : syracuseStep 6902275 = 10353413) B10353413
theorem B8180291 : Blo 1435537 8180291 := bstep (se 1 (by rfl) ⟨6135218, by rfl⟩ : syracuseStep 8180291 = 12270437) B12270437
theorem B13103693 : Blo 1435537 13103693 := bstep (se 3 (by rfl) ⟨2456942, by rfl⟩ : syracuseStep 13103693 = 4913885) B4913885
theorem B3232403 : Blo 1435537 3232403 := bstep (se 1 (by rfl) ⟨2424302, by rfl⟩ : syracuseStep 3232403 = 4848605) B4848605
theorem B3232457 : Blo 1435537 3232457 := bstep (se 2 (by rfl) ⟨1212171, by rfl⟩ : syracuseStep 3232457 = 2424343) B2424343
theorem B4846337 : Blo 1435537 4846337 := bstep (se 2 (by rfl) ⟨1817376, by rfl⟩ : syracuseStep 4846337 = 3634753) B3634753
theorem B29872901 : Blo 1435537 29872901 := bstep (se 4 (by rfl) ⟨2800584, by rfl⟩ : syracuseStep 29872901 = 5601169) B5601169
theorem B3634055 : Blo 1435537 3634055 := bstep (se 1 (by rfl) ⟨2725541, by rfl⟩ : syracuseStep 3634055 = 5451083) B5451083
theorem B1725319 : Blo 1435537 1725319 := bstep (se 1 (by rfl) ⟨1293989, by rfl⟩ : syracuseStep 1725319 = 2587979) B2587979
theorem B3634105 : Blo 1435537 3634105 := bstep (se 2 (by rfl) ⟨1362789, by rfl⟩ : syracuseStep 3634105 = 2725579) B2725579
theorem B3068857 : Blo 1435537 3068857 := bstep (se 2 (by rfl) ⟨1150821, by rfl⟩ : syracuseStep 3068857 = 2301643) B2301643
theorem B33641477 : Blo 1435537 33641477 := bstep (se 4 (by rfl) ⟨3153888, by rfl⟩ : syracuseStep 33641477 = 6307777) B6307777
theorem B8180747 : Blo 1435537 8180747 := bstep (se 1 (by rfl) ⟨6135560, by rfl⟩ : syracuseStep 8180747 = 12271121) B12271121
theorem B5452829 : Blo 1435537 5452829 := bstep (se 3 (by rfl) ⟨1022405, by rfl⟩ : syracuseStep 5452829 = 2044811) B2044811
theorem B16807085 : Blo 1435537 16807085 := bstep (se 3 (by rfl) ⟨3151328, by rfl⟩ : syracuseStep 16807085 = 6302657) B6302657
theorem B3110089 : Blo 1435537 3110089 := bstep (se 2 (by rfl) ⟨1166283, by rfl⟩ : syracuseStep 3110089 = 2332567) B2332567
theorem B8295695 : Blo 1435537 8295695 := bstep (se 1 (by rfl) ⟨6221771, by rfl⟩ : syracuseStep 8295695 = 12443543) B12443543
theorem B4093199 : Blo 1435537 4093199 := bstep (se 1 (by rfl) ⟨3069899, by rfl⟩ : syracuseStep 4093199 = 6139799) B6139799
theorem B3233159 : Blo 1435537 3233159 := bstep (se 1 (by rfl) ⟨2424869, by rfl⟩ : syracuseStep 3233159 = 4849739) B4849739
theorem B3683731 : Blo 1435537 3683731 := bstep (se 1 (by rfl) ⟨2762798, by rfl⟩ : syracuseStep 3683731 = 5525597) B5525597
theorem B2045369 : Blo 1435537 2045369 := bstep (se 2 (by rfl) ⟨767013, by rfl⟩ : syracuseStep 2045369 = 1534027) B1534027
theorem B2725321 : Blo 1435537 2725321 := bstep (se 2 (by rfl) ⟨1021995, by rfl⟩ : syracuseStep 2725321 = 2043991) B2043991
theorem B143652365 : Blo 1435537 143652365 := bstep (se 3 (by rfl) ⟨26934818, by rfl⟩ : syracuseStep 143652365 = 53869637) B53869637
theorem B3634703 : Blo 1435537 3634703 := bstep (se 1 (by rfl) ⟨2726027, by rfl⟩ : syracuseStep 3634703 = 5452055) B5452055
theorem B7763485 : Blo 1435537 7763485 := bstep (se 3 (by rfl) ⟨1455653, by rfl⟩ : syracuseStep 7763485 = 2911307) B2911307
theorem B3274273 : Blo 1435537 3274273 := bstep (se 2 (by rfl) ⟨1227852, by rfl⟩ : syracuseStep 3274273 = 2455705) B2455705
theorem B4847147 : Blo 1435537 4847147 := bstep (se 1 (by rfl) ⟨3635360, by rfl⟩ : syracuseStep 4847147 = 7270721) B7270721
theorem B3233339 : Blo 1435537 3233339 := bstep (se 1 (by rfl) ⟨2425004, by rfl⟩ : syracuseStep 3233339 = 4850009) B4850009
theorem B3233465 : Blo 1435537 3233465 := bstep (se 2 (by rfl) ⟨1212549, by rfl⟩ : syracuseStep 3233465 = 2425099) B2425099
theorem B5453513 : Blo 1435537 5453513 := bstep (se 2 (by rfl) ⟨2045067, by rfl⟩ : syracuseStep 5453513 = 4090135) B4090135
theorem B31069925 : Blo 1435537 31069925 := bstep (se 4 (by rfl) ⟨2912805, by rfl⟩ : syracuseStep 31069925 = 5825611) B5825611
theorem B6903737 : Blo 1435537 6903737 := bstep (se 2 (by rfl) ⟨2588901, by rfl⟩ : syracuseStep 6903737 = 5177803) B5177803
theorem B3233807 : Blo 1435537 3233807 := bstep (se 1 (by rfl) ⟨2425355, by rfl⟩ : syracuseStep 3233807 = 4850711) B4850711
theorem B3233825 : Blo 1435537 3233825 := bstep (se 2 (by rfl) ⟨1212684, by rfl⟩ : syracuseStep 3233825 = 2425369) B2425369
theorem B16595077 : Blo 1435537 16595077 := bstep (se 4 (by rfl) ⟨1555788, by rfl⟩ : syracuseStep 16595077 = 3111577) B3111577
theorem B2422919 : Blo 1435537 2422919 := bstep (se 1 (by rfl) ⟨1817189, by rfl⟩ : syracuseStep 2422919 = 3634379) B3634379
theorem B1726607 : Blo 1435537 1726607 := bstep (se 1 (by rfl) ⟨1294955, by rfl⟩ : syracuseStep 1726607 = 2589911) B2589911
theorem B3635401 : Blo 1435537 3635401 := bstep (se 2 (by rfl) ⟨1363275, by rfl⟩ : syracuseStep 3635401 = 2726551) B2726551
theorem B3635543 : Blo 1435537 3635543 := bstep (se 1 (by rfl) ⟨2726657, by rfl⟩ : syracuseStep 3635543 = 5453315) B5453315
theorem B3234167 : Blo 1435537 3234167 := bstep (se 1 (by rfl) ⟨2425625, by rfl⟩ : syracuseStep 3234167 = 4851251) B4851251
theorem B17471875 : Blo 1435537 17471875 := bstep (se 1 (by rfl) ⟨13103906, by rfl⟩ : syracuseStep 17471875 = 26207813) B26207813
theorem B7272989 : Blo 1435537 7272989 := bstep (se 3 (by rfl) ⟨1363685, by rfl⟩ : syracuseStep 7272989 = 2727371) B2727371
theorem B3881515 : Blo 1435537 3881515 := bstep (se 1 (by rfl) ⟨2911136, by rfl⟩ : syracuseStep 3881515 = 5822273) B5822273
theorem B3234347 : Blo 1435537 3234347 := bstep (se 1 (by rfl) ⟨2425760, by rfl⟩ : syracuseStep 3234347 = 4851521) B4851521
theorem B2423567 : Blo 1435537 2423567 := bstep (se 1 (by rfl) ⟨1817675, by rfl⟩ : syracuseStep 2423567 = 3635351) B3635351
theorem B4848443 : Blo 1435537 4848443 := bstep (se 1 (by rfl) ⟨3636332, by rfl⟩ : syracuseStep 4848443 = 7272665) B7272665
theorem B2153351 : Blo 1435537 2153351 := bstep (se 1 (by rfl) ⟨1615013, by rfl⟩ : syracuseStep 2153351 = 3230027) B3230027
theorem B2153387 : Blo 1435537 2153387 := bstep (se 1 (by rfl) ⟨1615040, by rfl⟩ : syracuseStep 2153387 = 3230081) B3230081
theorem B2153417 : Blo 1435537 2153417 := bstep (se 2 (by rfl) ⟨807531, by rfl⟩ : syracuseStep 2153417 = 1615063) B1615063
theorem B7273475 : Blo 1435537 7273475 := bstep (se 1 (by rfl) ⟨5455106, by rfl⟩ : syracuseStep 7273475 = 10910213) B10910213
theorem B5176349 : Blo 1435537 5176349 := bstep (se 3 (by rfl) ⟨970565, by rfl⟩ : syracuseStep 5176349 = 1941131) B1941131
theorem B2153531 : Blo 1435537 2153531 := bstep (se 1 (by rfl) ⟨1615148, by rfl⟩ : syracuseStep 2153531 = 3230297) B3230297
theorem B20716631 : Blo 1435537 20716631 := bstep (se 1 (by rfl) ⟨15537473, by rfl⟩ : syracuseStep 20716631 = 31074947) B31074947
theorem B2153591 : Blo 1435537 2153591 := bstep (se 1 (by rfl) ⟨1615193, by rfl⟩ : syracuseStep 2153591 = 3230387) B3230387
theorem B2153615 : Blo 1435537 2153615 := bstep (se 1 (by rfl) ⟨1615211, by rfl⟩ : syracuseStep 2153615 = 3230423) B3230423
theorem B2153657 : Blo 1435537 2153657 := bstep (se 2 (by rfl) ⟨807621, by rfl⟩ : syracuseStep 2153657 = 1615243) B1615243
theorem B4603081 : Blo 1435537 4603081 := bstep (se 2 (by rfl) ⟨1726155, by rfl⟩ : syracuseStep 4603081 = 3452311) B3452311
theorem B2153735 : Blo 1435537 2153735 := bstep (se 1 (by rfl) ⟨1615301, by rfl⟩ : syracuseStep 2153735 = 3230603) B3230603
theorem B4848929 : Blo 1435537 4848929 := bstep (se 2 (by rfl) ⟨1818348, by rfl⟩ : syracuseStep 4848929 = 3636697) B3636697
theorem B2153771 : Blo 1435537 2153771 := bstep (se 1 (by rfl) ⟨1615328, by rfl⟩ : syracuseStep 2153771 = 3230657) B3230657
theorem B2424107 : Blo 1435537 2424107 := bstep (se 1 (by rfl) ⟨1818080, by rfl⟩ : syracuseStep 2424107 = 3636161) B3636161
theorem B2153801 : Blo 1435537 2153801 := bstep (se 2 (by rfl) ⟨807675, by rfl⟩ : syracuseStep 2153801 = 1615351) B1615351
theorem B12279185 : Blo 1435537 12279185 := bstep (se 2 (by rfl) ⟨4604694, by rfl⟩ : syracuseStep 12279185 = 9209389) B9209389
theorem B5455289 : Blo 1435537 5455289 := bstep (se 2 (by rfl) ⟨2045733, by rfl⟩ : syracuseStep 5455289 = 4091467) B4091467
theorem B2153915 : Blo 1435537 2153915 := bstep (se 1 (by rfl) ⟨1615436, by rfl⟩ : syracuseStep 2153915 = 3230873) B3230873
theorem B10911185 : Blo 1435537 10911185 := bstep (se 2 (by rfl) ⟨4091694, by rfl⟩ : syracuseStep 10911185 = 8183389) B8183389
theorem B2153975 : Blo 1435537 2153975 := bstep (se 1 (by rfl) ⟨1615481, by rfl⟩ : syracuseStep 2153975 = 3230963) B3230963
theorem B2153999 : Blo 1435537 2153999 := bstep (se 1 (by rfl) ⟨1615499, by rfl⟩ : syracuseStep 2153999 = 3230999) B3230999
theorem B2154041 : Blo 1435537 2154041 := bstep (se 2 (by rfl) ⟨807765, by rfl⟩ : syracuseStep 2154041 = 1615531) B1615531
theorem B2154119 : Blo 1435537 2154119 := bstep (se 1 (by rfl) ⟨1615589, by rfl⟩ : syracuseStep 2154119 = 3231179) B3231179
theorem B2154155 : Blo 1435537 2154155 := bstep (se 1 (by rfl) ⟨1615616, by rfl⟩ : syracuseStep 2154155 = 3231233) B3231233
theorem B1818283 : Blo 1435537 1818283 := bstep (se 1 (by rfl) ⟨1363712, by rfl⟩ : syracuseStep 1818283 = 2727425) B2727425
theorem B2424505 : Blo 1435537 2424505 := bstep (se 2 (by rfl) ⟨909189, by rfl⟩ : syracuseStep 2424505 = 1818379) B1818379
theorem B2154185 : Blo 1435537 2154185 := bstep (se 2 (by rfl) ⟨807819, by rfl⟩ : syracuseStep 2154185 = 1615639) B1615639
theorem B15957809 : Blo 1435537 15957809 := bstep (se 2 (by rfl) ⟨5984178, by rfl⟩ : syracuseStep 15957809 = 11968357) B11968357
theorem B27598643 : Blo 1435537 27598643 := bstep (se 1 (by rfl) ⟨20698982, by rfl⟩ : syracuseStep 27598643 = 41397965) B41397965
theorem B2154299 : Blo 1435537 2154299 := bstep (se 1 (by rfl) ⟨1615724, by rfl⟩ : syracuseStep 2154299 = 3231449) B3231449
theorem B5824315 : Blo 1435537 5824315 := bstep (se 1 (by rfl) ⟨4368236, by rfl⟩ : syracuseStep 5824315 = 8736473) B8736473
theorem B4849523 : Blo 1435537 4849523 := bstep (se 1 (by rfl) ⟨3637142, by rfl⟩ : syracuseStep 4849523 = 7274285) B7274285
theorem B2154359 : Blo 1435537 2154359 := bstep (se 1 (by rfl) ⟨1615769, by rfl⟩ : syracuseStep 2154359 = 3231539) B3231539
theorem B2154383 : Blo 1435537 2154383 := bstep (se 1 (by rfl) ⟨1615787, by rfl⟩ : syracuseStep 2154383 = 3231575) B3231575
theorem B2727827 : Blo 1435537 2727827 := bstep (se 1 (by rfl) ⟨2045870, by rfl⟩ : syracuseStep 2727827 = 4091741) B4091741
theorem B2154425 : Blo 1435537 2154425 := bstep (se 2 (by rfl) ⟨807909, by rfl⟩ : syracuseStep 2154425 = 1615819) B1615819
theorem B7765969 : Blo 1435537 7765969 := bstep (se 2 (by rfl) ⟨2912238, by rfl⟩ : syracuseStep 7765969 = 5824477) B5824477
theorem B2154575 : Blo 1435537 2154575 := bstep (se 1 (by rfl) ⟨1615931, by rfl⟩ : syracuseStep 2154575 = 3231863) B3231863
theorem B4915279 : Blo 1435537 4915279 := bstep (se 1 (by rfl) ⟨3686459, by rfl⟩ : syracuseStep 4915279 = 7372919) B7372919
theorem B1818703 : Blo 1435537 1818703 := bstep (se 1 (by rfl) ⟨1364027, by rfl⟩ : syracuseStep 1818703 = 2728055) B2728055
theorem B15532195 : Blo 1435537 15532195 := bstep (se 1 (by rfl) ⟨11649146, by rfl⟩ : syracuseStep 15532195 = 23298293) B23298293
theorem B22126769 : Blo 1435537 22126769 := bstep (se 2 (by rfl) ⟨8297538, by rfl⟩ : syracuseStep 22126769 = 16595077) B16595077
theorem B2154695 : Blo 1435537 2154695 := bstep (se 1 (by rfl) ⟨1616021, by rfl⟩ : syracuseStep 2154695 = 3232043) B3232043
theorem B2425079 : Blo 1435537 2425079 := bstep (se 1 (by rfl) ⟨1818809, by rfl⟩ : syracuseStep 2425079 = 3637619) B3637619
theorem B10903895 : Blo 1435537 10903895 := bstep (se 1 (by rfl) ⟨8177921, by rfl⟩ : syracuseStep 10903895 = 16355843) B16355843
theorem B2154857 : Blo 1435537 2154857 := bstep (se 2 (by rfl) ⟨808071, by rfl⟩ : syracuseStep 2154857 = 1616143) B1616143
theorem B4604285 : Blo 1435537 4604285 := bstep (se 3 (by rfl) ⟨863303, by rfl⟩ : syracuseStep 4604285 = 1726607) B1726607
theorem B3277199 : Blo 1435537 3277199 := bstep (se 1 (by rfl) ⟨2457899, by rfl⟩ : syracuseStep 3277199 = 4915799) B4915799
theorem B4850063 : Blo 1435537 4850063 := bstep (se 1 (by rfl) ⟨3637547, by rfl⟩ : syracuseStep 4850063 = 7275095) B7275095
theorem B2154935 : Blo 1435537 2154935 := bstep (se 1 (by rfl) ⟨1616201, by rfl⟩ : syracuseStep 2154935 = 3232403) B3232403
theorem B2154971 : Blo 1435537 2154971 := bstep (se 1 (by rfl) ⟨1616228, by rfl⟩ : syracuseStep 2154971 = 3232457) B3232457
theorem B19915267 : Blo 1435537 19915267 := bstep (se 1 (by rfl) ⟨14936450, by rfl⟩ : syracuseStep 19915267 = 29872901) B29872901
theorem B5456443 : Blo 1435537 5456443 := bstep (se 1 (by rfl) ⟨4092332, by rfl⟩ : syracuseStep 5456443 = 8184665) B8184665
theorem B2425423 : Blo 1435537 2425423 := bstep (se 1 (by rfl) ⟨1819067, by rfl⟩ : syracuseStep 2425423 = 3638135) B3638135
theorem B1639111 : Blo 1435537 1639111 := bstep (se 1 (by rfl) ⟨1229333, by rfl⟩ : syracuseStep 1639111 = 2458667) B2458667
theorem B4850387 : Blo 1435537 4850387 := bstep (se 1 (by rfl) ⟨3637790, by rfl⟩ : syracuseStep 4850387 = 7275581) B7275581
theorem B2425673 : Blo 1435537 2425673 := bstep (se 2 (by rfl) ⟨909627, by rfl⟩ : syracuseStep 2425673 = 1819255) B1819255
theorem B5530463 : Blo 1435537 5530463 := bstep (se 1 (by rfl) ⟨4147847, by rfl⟩ : syracuseStep 5530463 = 8295695) B8295695
theorem B2728799 : Blo 1435537 2728799 := bstep (se 1 (by rfl) ⟨2046599, by rfl⟩ : syracuseStep 2728799 = 4093199) B4093199
theorem B3277675 : Blo 1435537 3277675 := bstep (se 1 (by rfl) ⟨2458256, by rfl⟩ : syracuseStep 3277675 = 4916513) B4916513
theorem B5456747 : Blo 1435537 5456747 := bstep (se 1 (by rfl) ⟨4092560, by rfl⟩ : syracuseStep 5456747 = 8185121) B8185121
theorem B2155439 : Blo 1435537 2155439 := bstep (se 1 (by rfl) ⟨1616579, by rfl⟩ : syracuseStep 2155439 = 3233159) B3233159
theorem B2155529 : Blo 1435537 2155529 := bstep (se 2 (by rfl) ⟨808323, by rfl⟩ : syracuseStep 2155529 = 1616647) B1616647
theorem B7373843 : Blo 1435537 7373843 := bstep (se 1 (by rfl) ⟨5530382, by rfl⟩ : syracuseStep 7373843 = 11060765) B11060765
theorem B5456915 : Blo 1435537 5456915 := bstep (se 1 (by rfl) ⟨4092686, by rfl⟩ : syracuseStep 5456915 = 8185373) B8185373
theorem B2155559 : Blo 1435537 2155559 := bstep (se 1 (by rfl) ⟨1616669, by rfl⟩ : syracuseStep 2155559 = 3233339) B3233339
theorem B2155643 : Blo 1435537 2155643 := bstep (se 1 (by rfl) ⟨1616732, by rfl⟩ : syracuseStep 2155643 = 3233465) B3233465
theorem B7267481 : Blo 1435537 7267481 := bstep (se 2 (by rfl) ⟨2725305, by rfl⟩ : syracuseStep 7267481 = 5450611) B5450611
theorem B2155769 : Blo 1435537 2155769 := bstep (se 2 (by rfl) ⟨808413, by rfl⟩ : syracuseStep 2155769 = 1616827) B1616827
theorem B2155871 : Blo 1435537 2155871 := bstep (se 1 (by rfl) ⟨1616903, by rfl⟩ : syracuseStep 2155871 = 3233807) B3233807
theorem B2155883 : Blo 1435537 2155883 := bstep (se 1 (by rfl) ⟨1616912, by rfl⟩ : syracuseStep 2155883 = 3233825) B3233825
theorem B1615279 : Blo 1435537 1615279 := bstep (se 1 (by rfl) ⟨1211459, by rfl⟩ : syracuseStep 1615279 = 2422919) B2422919
theorem B5604851 : Blo 1435537 5604851 := bstep (se 1 (by rfl) ⟨4203638, by rfl⟩ : syracuseStep 5604851 = 8407277) B8407277
theorem B2156111 : Blo 1435537 2156111 := bstep (se 1 (by rfl) ⟨1617083, by rfl⟩ : syracuseStep 2156111 = 3234167) B3234167
theorem B4146785 : Blo 1435537 4146785 := bstep (se 2 (by rfl) ⟨1555044, by rfl⟩ : syracuseStep 4146785 = 3110089) B3110089
theorem B6137441 : Blo 1435537 6137441 := bstep (se 2 (by rfl) ⟨2301540, by rfl⟩ : syracuseStep 6137441 = 4603081) B4603081
theorem B6555275 : Blo 1435537 6555275 := bstep (se 1 (by rfl) ⟨4916456, by rfl⟩ : syracuseStep 6555275 = 9832913) B9832913
theorem B2156231 : Blo 1435537 2156231 := bstep (se 1 (by rfl) ⟨1617173, by rfl⟩ : syracuseStep 2156231 = 3234347) B3234347
theorem B1615711 : Blo 1435537 1615711 := bstep (se 1 (by rfl) ⟨1211783, by rfl⟩ : syracuseStep 1615711 = 2423567) B2423567
theorem B4851575 : Blo 1435537 4851575 := bstep (se 1 (by rfl) ⟨3638681, by rfl⟩ : syracuseStep 4851575 = 7277363) B7277363
theorem B1435567 : Blo 1435537 1435567 := bstep (se 1 (by rfl) ⟨1076675, by rfl⟩ : syracuseStep 1435567 = 2153351) B2153351
theorem B1435591 : Blo 1435537 1435591 := bstep (se 1 (by rfl) ⟨1076693, by rfl⟩ : syracuseStep 1435591 = 2153387) B2153387
theorem B1435611 : Blo 1435537 1435611 := bstep (se 1 (by rfl) ⟨1076708, by rfl⟩ : syracuseStep 1435611 = 2153417) B2153417
theorem B3450899 : Blo 1435537 3450899 := bstep (se 1 (by rfl) ⟨2588174, by rfl⟩ : syracuseStep 3450899 = 5176349) B5176349
theorem B9201701 : Blo 1435537 9201701 := bstep (se 4 (by rfl) ⟨862659, by rfl⟩ : syracuseStep 9201701 = 1725319) B1725319
theorem B1435687 : Blo 1435537 1435687 := bstep (se 1 (by rfl) ⟨1076765, by rfl⟩ : syracuseStep 1435687 = 2153531) B2153531
theorem B1435727 : Blo 1435537 1435727 := bstep (se 1 (by rfl) ⟨1076795, by rfl⟩ : syracuseStep 1435727 = 2153591) B2153591
theorem B1435743 : Blo 1435537 1435743 := bstep (se 1 (by rfl) ⟨1076807, by rfl⟩ : syracuseStep 1435743 = 2153615) B2153615
theorem B1435771 : Blo 1435537 1435771 := bstep (se 1 (by rfl) ⟨1076828, by rfl⟩ : syracuseStep 1435771 = 2153657) B2153657
theorem B1435823 : Blo 1435537 1435823 := bstep (se 1 (by rfl) ⟨1076867, by rfl⟩ : syracuseStep 1435823 = 2153735) B2153735
theorem B1435847 : Blo 1435537 1435847 := bstep (se 1 (by rfl) ⟨1076885, by rfl⟩ : syracuseStep 1435847 = 2153771) B2153771
theorem B1616071 : Blo 1435537 1616071 := bstep (se 1 (by rfl) ⟨1212053, by rfl⟩ : syracuseStep 1616071 = 2424107) B2424107
theorem B1435867 : Blo 1435537 1435867 := bstep (se 1 (by rfl) ⟨1076900, by rfl⟩ : syracuseStep 1435867 = 2153801) B2153801
theorem B8186123 : Blo 1435537 8186123 := bstep (se 1 (by rfl) ⟨6139592, by rfl⟩ : syracuseStep 8186123 = 12279185) B12279185
theorem B1435943 : Blo 1435537 1435943 := bstep (se 1 (by rfl) ⟨1076957, by rfl⟩ : syracuseStep 1435943 = 2153915) B2153915
theorem B1435983 : Blo 1435537 1435983 := bstep (se 1 (by rfl) ⟨1076987, by rfl⟩ : syracuseStep 1435983 = 2153975) B2153975
theorem B1435999 : Blo 1435537 1435999 := bstep (se 1 (by rfl) ⟨1076999, by rfl⟩ : syracuseStep 1435999 = 2153999) B2153999
theorem B1436027 : Blo 1435537 1436027 := bstep (se 1 (by rfl) ⟨1077020, by rfl⟩ : syracuseStep 1436027 = 2154041) B2154041
theorem B4917647 : Blo 1435537 4917647 := bstep (se 1 (by rfl) ⟨3688235, by rfl⟩ : syracuseStep 4917647 = 7376471) B7376471
theorem B1436079 : Blo 1435537 1436079 := bstep (se 1 (by rfl) ⟨1077059, by rfl⟩ : syracuseStep 1436079 = 2154119) B2154119
theorem B1436103 : Blo 1435537 1436103 := bstep (se 1 (by rfl) ⟨1077077, by rfl⟩ : syracuseStep 1436103 = 2154155) B2154155
theorem B3230171 : Blo 1435537 3230171 := bstep (se 1 (by rfl) ⟨2422628, by rfl⟩ : syracuseStep 3230171 = 4845257) B4845257
theorem B1436123 : Blo 1435537 1436123 := bstep (se 1 (by rfl) ⟨1077092, by rfl⟩ : syracuseStep 1436123 = 2154185) B2154185
theorem B1436199 : Blo 1435537 1436199 := bstep (se 1 (by rfl) ⟨1077149, by rfl⟩ : syracuseStep 1436199 = 2154299) B2154299
theorem B1436239 : Blo 1435537 1436239 := bstep (se 1 (by rfl) ⟨1077179, by rfl⟩ : syracuseStep 1436239 = 2154359) B2154359
theorem B1436255 : Blo 1435537 1436255 := bstep (se 1 (by rfl) ⟨1077191, by rfl⟩ : syracuseStep 1436255 = 2154383) B2154383
theorem B1436283 : Blo 1435537 1436283 := bstep (se 1 (by rfl) ⟨1077212, by rfl⟩ : syracuseStep 1436283 = 2154425) B2154425
theorem B1436335 : Blo 1435537 1436335 := bstep (se 1 (by rfl) ⟨1077251, by rfl⟩ : syracuseStep 1436335 = 2154503) B2154503
theorem B1436359 : Blo 1435537 1436359 := bstep (se 1 (by rfl) ⟨1077269, by rfl⟩ : syracuseStep 1436359 = 2154539) B2154539
theorem B8186579 : Blo 1435537 8186579 := bstep (se 1 (by rfl) ⟨6139934, by rfl⟩ : syracuseStep 8186579 = 12279869) B12279869
theorem B1436379 : Blo 1435537 1436379 := bstep (se 1 (by rfl) ⟨1077284, by rfl⟩ : syracuseStep 1436379 = 2154569) B2154569
theorem B1436455 : Blo 1435537 1436455 := bstep (se 1 (by rfl) ⟨1077341, by rfl⟩ : syracuseStep 1436455 = 2154683) B2154683
theorem B1436495 : Blo 1435537 1436495 := bstep (se 1 (by rfl) ⟨1077371, by rfl⟩ : syracuseStep 1436495 = 2154743) B2154743
theorem B1436511 : Blo 1435537 1436511 := bstep (se 1 (by rfl) ⟨1077383, by rfl⟩ : syracuseStep 1436511 = 2154767) B2154767
theorem B5180269 : Blo 1435537 5180269 := bstep (se 3 (by rfl) ⟨971300, by rfl⟩ : syracuseStep 5180269 = 1942601) B1942601
theorem B1436539 : Blo 1435537 1436539 := bstep (se 1 (by rfl) ⟨1077404, by rfl⟩ : syracuseStep 1436539 = 2154809) B2154809
theorem B3230639 : Blo 1435537 3230639 := bstep (se 1 (by rfl) ⟨2422979, by rfl⟩ : syracuseStep 3230639 = 4845959) B4845959
theorem B1436591 : Blo 1435537 1436591 := bstep (se 1 (by rfl) ⟨1077443, by rfl⟩ : syracuseStep 1436591 = 2154887) B2154887
theorem B198945719 : Blo 1435537 198945719 := bstep (se 1 (by rfl) ⟨149209289, by rfl⟩ : syracuseStep 198945719 = 298418579) B298418579
theorem B1436615 : Blo 1435537 1436615 := bstep (se 1 (by rfl) ⟨1077461, by rfl⟩ : syracuseStep 1436615 = 2154923) B2154923
theorem B1436635 : Blo 1435537 1436635 := bstep (se 1 (by rfl) ⟨1077476, by rfl⟩ : syracuseStep 1436635 = 2154953) B2154953
theorem B1436711 : Blo 1435537 1436711 := bstep (se 1 (by rfl) ⟨1077533, by rfl⟩ : syracuseStep 1436711 = 2155067) B2155067
theorem B1616935 : Blo 1435537 1616935 := bstep (se 1 (by rfl) ⟨1212701, by rfl⟩ : syracuseStep 1616935 = 2425403) B2425403
theorem B8735795 : Blo 1435537 8735795 := bstep (se 1 (by rfl) ⟨6551846, by rfl⟩ : syracuseStep 8735795 = 13103693) B13103693
theorem B1436751 : Blo 1435537 1436751 := bstep (se 1 (by rfl) ⟨1077563, by rfl⟩ : syracuseStep 1436751 = 2155127) B2155127
theorem B1436767 : Blo 1435537 1436767 := bstep (se 1 (by rfl) ⟨1077575, by rfl⟩ : syracuseStep 1436767 = 2155151) B2155151
theorem B1436795 : Blo 1435537 1436795 := bstep (se 1 (by rfl) ⟨1077596, by rfl⟩ : syracuseStep 1436795 = 2155193) B2155193
theorem B3230891 : Blo 1435537 3230891 := bstep (se 1 (by rfl) ⟨2423168, by rfl⟩ : syracuseStep 3230891 = 4846337) B4846337
theorem B1436847 : Blo 1435537 1436847 := bstep (se 1 (by rfl) ⟨1077635, by rfl⟩ : syracuseStep 1436847 = 2155271) B2155271
theorem B1436871 : Blo 1435537 1436871 := bstep (se 1 (by rfl) ⟨1077653, by rfl⟩ : syracuseStep 1436871 = 2155307) B2155307
theorem B1436891 : Blo 1435537 1436891 := bstep (se 1 (by rfl) ⟨1077668, by rfl⟩ : syracuseStep 1436891 = 2155337) B2155337
theorem B1436967 : Blo 1435537 1436967 := bstep (se 1 (by rfl) ⟨1077725, by rfl⟩ : syracuseStep 1436967 = 2155451) B2155451
theorem B1437007 : Blo 1435537 1437007 := bstep (se 1 (by rfl) ⟨1077755, by rfl⟩ : syracuseStep 1437007 = 2155511) B2155511
theorem B14740825 : Blo 1435537 14740825 := bstep (se 2 (by rfl) ⟨5527809, by rfl⟩ : syracuseStep 14740825 = 11055619) B11055619
theorem B9203033 : Blo 1435537 9203033 := bstep (se 2 (by rfl) ⟨3451137, by rfl⟩ : syracuseStep 9203033 = 6902275) B6902275
theorem B1437023 : Blo 1435537 1437023 := bstep (se 1 (by rfl) ⟨1077767, by rfl⟩ : syracuseStep 1437023 = 2155535) B2155535
theorem B1437051 : Blo 1435537 1437051 := bstep (se 1 (by rfl) ⟨1077788, by rfl⟩ : syracuseStep 1437051 = 2155577) B2155577
theorem B4369793 : Blo 1435537 4369793 := bstep (se 2 (by rfl) ⟨1638672, by rfl⟩ : syracuseStep 4369793 = 3277345) B3277345
theorem B1437103 : Blo 1435537 1437103 := bstep (se 1 (by rfl) ⟨1077827, by rfl⟩ : syracuseStep 1437103 = 2155655) B2155655
theorem B1437127 : Blo 1435537 1437127 := bstep (se 1 (by rfl) ⟨1077845, by rfl⟩ : syracuseStep 1437127 = 2155691) B2155691
theorem B1437147 : Blo 1435537 1437147 := bstep (se 1 (by rfl) ⟨1077860, by rfl⟩ : syracuseStep 1437147 = 2155721) B2155721
theorem B4845095 : Blo 1435537 4845095 := bstep (se 1 (by rfl) ⟨3633821, by rfl⟩ : syracuseStep 4845095 = 7267643) B7267643
theorem B1437223 : Blo 1435537 1437223 := bstep (se 1 (by rfl) ⟨1077917, by rfl⟩ : syracuseStep 1437223 = 2155835) B2155835
theorem B1437263 : Blo 1435537 1437263 := bstep (se 1 (by rfl) ⟨1077947, by rfl⟩ : syracuseStep 1437263 = 2155895) B2155895
theorem B1437279 : Blo 1435537 1437279 := bstep (se 1 (by rfl) ⟨1077959, by rfl⟩ : syracuseStep 1437279 = 2155919) B2155919
theorem B1437307 : Blo 1435537 1437307 := bstep (se 1 (by rfl) ⟨1077980, by rfl⟩ : syracuseStep 1437307 = 2155961) B2155961
theorem B4845203 : Blo 1435537 4845203 := bstep (se 1 (by rfl) ⟨3633902, by rfl⟩ : syracuseStep 4845203 = 7267805) B7267805
theorem B1437359 : Blo 1435537 1437359 := bstep (se 1 (by rfl) ⟨1078019, by rfl⟩ : syracuseStep 1437359 = 2156039) B2156039
theorem B95768243 : Blo 1435537 95768243 := bstep (se 1 (by rfl) ⟨71826182, by rfl⟩ : syracuseStep 95768243 = 143652365) B143652365
theorem B3231431 : Blo 1435537 3231431 := bstep (se 1 (by rfl) ⟨2423573, by rfl⟩ : syracuseStep 3231431 = 4847147) B4847147
theorem B1437383 : Blo 1435537 1437383 := bstep (se 1 (by rfl) ⟨1078037, by rfl⟩ : syracuseStep 1437383 = 2156075) B2156075
theorem B1437403 : Blo 1435537 1437403 := bstep (se 1 (by rfl) ⟨1078052, by rfl⟩ : syracuseStep 1437403 = 2156105) B2156105
theorem B1437479 : Blo 1435537 1437479 := bstep (se 1 (by rfl) ⟨1078109, by rfl⟩ : syracuseStep 1437479 = 2156219) B2156219
theorem B4599595 : Blo 1435537 4599595 := bstep (se 1 (by rfl) ⟨3449696, by rfl⟩ : syracuseStep 4599595 = 6899393) B6899393
theorem B20713283 : Blo 1435537 20713283 := bstep (se 1 (by rfl) ⟨15534962, by rfl⟩ : syracuseStep 20713283 = 31069925) B31069925
theorem B1437519 : Blo 1435537 1437519 := bstep (se 1 (by rfl) ⟨1078139, by rfl⟩ : syracuseStep 1437519 = 2156279) B2156279
theorem B1437535 : Blo 1435537 1437535 := bstep (se 1 (by rfl) ⟨1078151, by rfl⟩ : syracuseStep 1437535 = 2156303) B2156303
theorem B4845419 : Blo 1435537 4845419 := bstep (se 1 (by rfl) ⟨3634064, by rfl⟩ : syracuseStep 4845419 = 7268129) B7268129
theorem B4599671 : Blo 1435537 4599671 := bstep (se 1 (by rfl) ⟨3449753, by rfl⟩ : syracuseStep 4599671 = 6899507) B6899507
theorem B4845473 : Blo 1435537 4845473 := bstep (se 2 (by rfl) ⟨1817052, by rfl⟩ : syracuseStep 4845473 = 3634105) B3634105
theorem B4091809 : Blo 1435537 4091809 := bstep (se 2 (by rfl) ⟨1534428, by rfl⟩ : syracuseStep 4091809 = 3068857) B3068857
theorem B6549511 : Blo 1435537 6549511 := bstep (se 1 (by rfl) ⟨4912133, by rfl⟩ : syracuseStep 6549511 = 9824267) B9824267
theorem B5451857 : Blo 1435537 5451857 := bstep (se 2 (by rfl) ⟨2044446, by rfl⟩ : syracuseStep 5451857 = 4088893) B4088893
theorem B24555635 : Blo 1435537 24555635 := bstep (se 1 (by rfl) ⟨18416726, by rfl⟩ : syracuseStep 24555635 = 36833453) B36833453
theorem B22720675 : Blo 1435537 22720675 := bstep (se 1 (by rfl) ⟨17040506, by rfl⟩ : syracuseStep 22720675 = 34081013) B34081013
theorem B10350935 : Blo 1435537 10350935 := bstep (se 1 (by rfl) ⟨7763201, by rfl⟩ : syracuseStep 10350935 = 15526403) B15526403
theorem B4846067 : Blo 1435537 4846067 := bstep (se 1 (by rfl) ⟨3634550, by rfl⟩ : syracuseStep 4846067 = 7269101) B7269101
theorem B4911641 : Blo 1435537 4911641 := bstep (se 2 (by rfl) ⟨1841865, by rfl⟩ : syracuseStep 4911641 = 3683731) B3683731
theorem B3232295 : Blo 1435537 3232295 := bstep (se 1 (by rfl) ⟨2424221, by rfl⟩ : syracuseStep 3232295 = 4848443) B4848443
theorem B3633761 : Blo 1435537 3633761 := bstep (se 2 (by rfl) ⟨1362660, by rfl⟩ : syracuseStep 3633761 = 2725321) B2725321
theorem B10351313 : Blo 1435537 10351313 := bstep (se 2 (by rfl) ⟨3881742, by rfl⟩ : syracuseStep 10351313 = 7763485) B7763485
theorem B7369427 : Blo 1435537 7369427 := bstep (se 1 (by rfl) ⟨5527070, by rfl⟩ : syracuseStep 7369427 = 11054141) B11054141
theorem B17052419 : Blo 1435537 17052419 := bstep (se 1 (by rfl) ⟨12789314, by rfl⟩ : syracuseStep 17052419 = 25578629) B25578629
theorem B2044777 : Blo 1435537 2044777 := bstep (se 2 (by rfl) ⟨766791, by rfl⟩ : syracuseStep 2044777 = 1533583) B1533583
theorem B3232619 : Blo 1435537 3232619 := bstep (se 1 (by rfl) ⟨2424464, by rfl⟩ : syracuseStep 3232619 = 4848929) B4848929
theorem B3232673 : Blo 1435537 3232673 := bstep (se 2 (by rfl) ⟨1212252, by rfl⟩ : syracuseStep 3232673 = 2424505) B2424505
theorem B3322799 : Blo 1435537 3322799 := bstep (se 1 (by rfl) ⟨2492099, by rfl⟩ : syracuseStep 3322799 = 4984199) B4984199
theorem B4846607 : Blo 1435537 4846607 := bstep (se 1 (by rfl) ⟨3634955, by rfl⟩ : syracuseStep 4846607 = 7269911) B7269911
theorem B4093085 : Blo 1435537 4093085 := bstep (se 3 (by rfl) ⟨767453, by rfl⟩ : syracuseStep 4093085 = 1534907) B1534907
theorem B10638539 : Blo 1435537 10638539 := bstep (se 1 (by rfl) ⟨7978904, by rfl⟩ : syracuseStep 10638539 = 15957809) B15957809
theorem B3233015 : Blo 1435537 3233015 := bstep (se 1 (by rfl) ⟨2424761, by rfl⟩ : syracuseStep 3233015 = 4849523) B4849523
theorem B20714899 : Blo 1435537 20714899 := bstep (se 1 (by rfl) ⟨15536174, by rfl⟩ : syracuseStep 20714899 = 31072349) B31072349
theorem B2045449 : Blo 1435537 2045449 := bstep (se 2 (by rfl) ⟨767043, by rfl⟩ : syracuseStep 2045449 = 1534087) B1534087
theorem B19650059 : Blo 1435537 19650059 := bstep (se 1 (by rfl) ⟨14737544, by rfl⟩ : syracuseStep 19650059 = 29475089) B29475089
theorem B13809163 : Blo 1435537 13809163 := bstep (se 1 (by rfl) ⟨10356872, by rfl⟩ : syracuseStep 13809163 = 20713745) B20713745
theorem B5453345 : Blo 1435537 5453345 := bstep (se 2 (by rfl) ⟨2045004, by rfl⟩ : syracuseStep 5453345 = 4090009) B4090009
theorem B4847201 : Blo 1435537 4847201 := bstep (se 2 (by rfl) ⟨1817700, by rfl⟩ : syracuseStep 4847201 = 3635401) B3635401
theorem B4601441 : Blo 1435537 4601441 := bstep (se 2 (by rfl) ⟨1725540, by rfl⟩ : syracuseStep 4601441 = 3451081) B3451081
theorem B7001747 : Blo 1435537 7001747 := bstep (se 1 (by rfl) ⟨5251310, by rfl⟩ : syracuseStep 7001747 = 10502621) B10502621
theorem B5453527 : Blo 1435537 5453527 := bstep (se 1 (by rfl) ⟨4090145, by rfl⟩ : syracuseStep 5453527 = 8180291) B8180291
theorem B2725625 : Blo 1435537 2725625 := bstep (se 2 (by rfl) ⟨1022109, by rfl⟩ : syracuseStep 2725625 = 2044219) B2044219
theorem B8197955 : Blo 1435537 8197955 := bstep (se 1 (by rfl) ⟨6148466, by rfl⟩ : syracuseStep 8197955 = 12296933) B12296933
theorem B4790089 : Blo 1435537 4790089 := bstep (se 2 (by rfl) ⟨1796283, by rfl⟩ : syracuseStep 4790089 = 3592567) B3592567
theorem B3233609 : Blo 1435537 3233609 := bstep (se 2 (by rfl) ⟨1212603, by rfl⟩ : syracuseStep 3233609 = 2425207) B2425207
theorem B23295833 : Blo 1435537 23295833 := bstep (se 2 (by rfl) ⟨8735937, by rfl⟩ : syracuseStep 23295833 = 17471875) B17471875
theorem B2422703 : Blo 1435537 2422703 := bstep (se 1 (by rfl) ⟨1817027, by rfl⟩ : syracuseStep 2422703 = 3634055) B3634055
theorem B2725807 : Blo 1435537 2725807 := bstep (se 1 (by rfl) ⟨2044355, by rfl⟩ : syracuseStep 2725807 = 4088711) B4088711
theorem B22427651 : Blo 1435537 22427651 := bstep (se 1 (by rfl) ⟨16820738, by rfl⟩ : syracuseStep 22427651 = 33641477) B33641477
theorem B5453831 : Blo 1435537 5453831 := bstep (se 1 (by rfl) ⟨4090373, by rfl⟩ : syracuseStep 5453831 = 8180747) B8180747
theorem B3635219 : Blo 1435537 3635219 := bstep (se 1 (by rfl) ⟨2726414, by rfl⟩ : syracuseStep 3635219 = 5452829) B5452829
theorem B5175353 : Blo 1435537 5175353 := bstep (se 2 (by rfl) ⟨1940757, by rfl⟩ : syracuseStep 5175353 = 3881515) B3881515
theorem B2725967 : Blo 1435537 2725967 := bstep (se 1 (by rfl) ⟨2044475, by rfl⟩ : syracuseStep 2725967 = 4088951) B4088951
theorem B11204723 : Blo 1435537 11204723 := bstep (se 1 (by rfl) ⟨8403542, by rfl⟩ : syracuseStep 11204723 = 16807085) B16807085
theorem B3070199 : Blo 1435537 3070199 := bstep (se 1 (by rfl) ⟨2302649, by rfl⟩ : syracuseStep 3070199 = 4605299) B4605299
theorem B2423135 : Blo 1435537 2423135 := bstep (se 1 (by rfl) ⟨1817351, by rfl⟩ : syracuseStep 2423135 = 3634703) B3634703
theorem B3635675 : Blo 1435537 3635675 := bstep (se 1 (by rfl) ⟨2726756, by rfl⟩ : syracuseStep 3635675 = 5453513) B5453513
theorem B5454317 : Blo 1435537 5454317 := bstep (se 3 (by rfl) ⟨1022684, by rfl⟩ : syracuseStep 5454317 = 2045369) B2045369
theorem B3234401 : Blo 1435537 3234401 := bstep (se 2 (by rfl) ⟨1212900, by rfl⟩ : syracuseStep 3234401 = 2425801) B2425801
theorem B4602491 : Blo 1435537 4602491 := bstep (se 1 (by rfl) ⟨3451868, by rfl⟩ : syracuseStep 4602491 = 6903737) B6903737
theorem B8182457 : Blo 1435537 8182457 := bstep (se 2 (by rfl) ⟨3068421, by rfl⟩ : syracuseStep 8182457 = 6136843) B6136843
theorem B2046713 : Blo 1435537 2046713 := bstep (se 2 (by rfl) ⟨767517, by rfl⟩ : syracuseStep 2046713 = 1535035) B1535035
theorem B2153321 : Blo 1435537 2153321 := bstep (se 2 (by rfl) ⟨807495, by rfl⟩ : syracuseStep 2153321 = 1614991) B1614991
theorem B5528429 : Blo 1435537 5528429 := bstep (se 3 (by rfl) ⟨1036580, by rfl⟩ : syracuseStep 5528429 = 2073161) B2073161
theorem B2423695 : Blo 1435537 2423695 := bstep (se 1 (by rfl) ⟨1817771, by rfl⟩ : syracuseStep 2423695 = 3635543) B3635543
theorem B2153399 : Blo 1435537 2153399 := bstep (se 1 (by rfl) ⟨1615049, by rfl⟩ : syracuseStep 2153399 = 3230099) B3230099
theorem B2153435 : Blo 1435537 2153435 := bstep (se 1 (by rfl) ⟨1615076, by rfl⟩ : syracuseStep 2153435 = 3230153) B3230153
theorem B4848659 : Blo 1435537 4848659 := bstep (se 1 (by rfl) ⟨3636494, by rfl⟩ : syracuseStep 4848659 = 7272989) B7272989
theorem B22109263 : Blo 1435537 22109263 := bstep (se 1 (by rfl) ⟨16581947, by rfl⟩ : syracuseStep 22109263 = 33163895) B33163895
theorem B2727083 : Blo 1435537 2727083 := bstep (se 1 (by rfl) ⟨2045312, by rfl⟩ : syracuseStep 2727083 = 4090625) B4090625
theorem B6905027 : Blo 1435537 6905027 := bstep (se 1 (by rfl) ⟨5178770, by rfl⟩ : syracuseStep 6905027 = 10357541) B10357541
theorem B4848983 : Blo 1435537 4848983 := bstep (se 1 (by rfl) ⟨3636737, by rfl⟩ : syracuseStep 4848983 = 7273475) B7273475
theorem B4365697 : Blo 1435537 4365697 := bstep (se 2 (by rfl) ⟨1637136, by rfl⟩ : syracuseStep 4365697 = 3274273) B3274273
theorem B13811087 : Blo 1435537 13811087 := bstep (se 1 (by rfl) ⟨10358315, by rfl⟩ : syracuseStep 13811087 = 20716631) B20716631
theorem B2153903 : Blo 1435537 2153903 := bstep (se 1 (by rfl) ⟨1615427, by rfl⟩ : syracuseStep 2153903 = 3230855) B3230855
theorem B2153993 : Blo 1435537 2153993 := bstep (se 2 (by rfl) ⟨807747, by rfl⟩ : syracuseStep 2153993 = 1615495) B1615495
theorem B9199115 : Blo 1435537 9199115 := bstep (se 1 (by rfl) ⟨6899336, by rfl⟩ : syracuseStep 9199115 = 13798673) B13798673
theorem B2154023 : Blo 1435537 2154023 := bstep (se 1 (by rfl) ⟨1615517, by rfl⟩ : syracuseStep 2154023 = 3231035) B3231035
theorem B31055399 : Blo 1435537 31055399 := bstep (se 1 (by rfl) ⟨23291549, by rfl⟩ : syracuseStep 31055399 = 46583099) B46583099
theorem B2424377 : Blo 1435537 2424377 := bstep (se 2 (by rfl) ⟨909141, by rfl⟩ : syracuseStep 2424377 = 1818283) B1818283
theorem B5455457 : Blo 1435537 5455457 := bstep (se 2 (by rfl) ⟨2045796, by rfl⟩ : syracuseStep 5455457 = 4091593) B4091593
theorem B2154107 : Blo 1435537 2154107 := bstep (se 1 (by rfl) ⟨1615580, by rfl⟩ : syracuseStep 2154107 = 3231161) B3231161
theorem B3636859 : Blo 1435537 3636859 := bstep (se 1 (by rfl) ⟨2727644, by rfl⟩ : syracuseStep 3636859 = 5455289) B5455289
theorem B7274123 : Blo 1435537 7274123 := bstep (se 1 (by rfl) ⟨5455592, by rfl⟩ : syracuseStep 7274123 = 10911185) B10911185
theorem B5529287 : Blo 1435537 5529287 := bstep (se 1 (by rfl) ⟨4146965, by rfl⟩ : syracuseStep 5529287 = 8293931) B8293931
theorem B2154233 : Blo 1435537 2154233 := bstep (se 2 (by rfl) ⟨807837, by rfl⟩ : syracuseStep 2154233 = 1615675) B1615675
theorem B7765753 : Blo 1435537 7765753 := bstep (se 2 (by rfl) ⟨2912157, by rfl⟩ : syracuseStep 7765753 = 5824315) B5824315
theorem B2154335 : Blo 1435537 2154335 := bstep (se 1 (by rfl) ⟨1615751, by rfl⟩ : syracuseStep 2154335 = 3231503) B3231503
theorem B2154347 : Blo 1435537 2154347 := bstep (se 1 (by rfl) ⟨1615760, by rfl⟩ : syracuseStep 2154347 = 3231521) B3231521
theorem B18399095 : Blo 1435537 18399095 := bstep (se 1 (by rfl) ⟨13799321, by rfl⟩ : syracuseStep 18399095 = 27598643) B27598643
theorem B1818551 : Blo 1435537 1818551 := bstep (se 1 (by rfl) ⟨1363913, by rfl⟩ : syracuseStep 1818551 = 2727827) B2727827
theorem B10354625 : Blo 1435537 10354625 := bstep (se 2 (by rfl) ⟨3882984, by rfl⟩ : syracuseStep 10354625 = 7765969) B7765969
theorem B8732681 : Blo 1435537 8732681 := bstep (se 2 (by rfl) ⟨3274755, by rfl⟩ : syracuseStep 8732681 = 6549511) B6549511
theorem B6553705 : Blo 1435537 6553705 := bstep (se 2 (by rfl) ⟨2457639, by rfl⟩ : syracuseStep 6553705 = 4915279) B4915279
theorem B2424937 : Blo 1435537 2424937 := bstep (se 2 (by rfl) ⟨909351, by rfl⟩ : syracuseStep 2424937 = 1818703) B1818703
theorem B30294233 : Blo 1435537 30294233 := bstep (se 2 (by rfl) ⟨11360337, by rfl⟩ : syracuseStep 30294233 = 22720675) B22720675
theorem B20709593 : Blo 1435537 20709593 := bstep (se 2 (by rfl) ⟨7766097, by rfl⟩ : syracuseStep 20709593 = 15532195) B15532195
theorem B2154761 : Blo 1435537 2154761 := bstep (se 2 (by rfl) ⟨808035, by rfl⟩ : syracuseStep 2154761 = 1616071) B1616071
theorem B2154863 : Blo 1435537 2154863 := bstep (se 1 (by rfl) ⟨1616147, by rfl⟩ : syracuseStep 2154863 = 3232295) B3232295
theorem B117916069 : Blo 1435537 117916069 := bstep (se 4 (by rfl) ⟨11054631, by rfl⟩ : syracuseStep 117916069 = 22109263) B22109263
theorem B3686975 : Blo 1435537 3686975 := bstep (se 1 (by rfl) ⟨2765231, by rfl⟩ : syracuseStep 3686975 = 5530463) B5530463
theorem B1819199 : Blo 1435537 1819199 := bstep (se 1 (by rfl) ⟨1364399, by rfl⟩ : syracuseStep 1819199 = 2728799) B2728799
theorem B2155079 : Blo 1435537 2155079 := bstep (se 1 (by rfl) ⟨1616309, by rfl⟩ : syracuseStep 2155079 = 3232619) B3232619
theorem B3637831 : Blo 1435537 3637831 := bstep (se 1 (by rfl) ⟨2728373, by rfl⟩ : syracuseStep 3637831 = 5456747) B5456747
theorem B2155115 : Blo 1435537 2155115 := bstep (se 1 (by rfl) ⟨1616336, by rfl⟩ : syracuseStep 2155115 = 3232673) B3232673
theorem B4915895 : Blo 1435537 4915895 := bstep (se 1 (by rfl) ⟨3686921, by rfl⟩ : syracuseStep 4915895 = 7373843) B7373843
theorem B3637943 : Blo 1435537 3637943 := bstep (se 1 (by rfl) ⟨2728457, by rfl⟩ : syracuseStep 3637943 = 5456915) B5456915
theorem B7275257 : Blo 1435537 7275257 := bstep (se 2 (by rfl) ⟨2728221, by rfl⟩ : syracuseStep 7275257 = 5456443) B5456443
theorem B2728723 : Blo 1435537 2728723 := bstep (se 1 (by rfl) ⟨2046542, by rfl⟩ : syracuseStep 2728723 = 4093085) B4093085
theorem B2155343 : Blo 1435537 2155343 := bstep (se 1 (by rfl) ⟨1616507, by rfl⟩ : syracuseStep 2155343 = 3233015) B3233015
theorem B3736567 : Blo 1435537 3736567 := bstep (se 1 (by rfl) ⟨2802425, by rfl⟩ : syracuseStep 3736567 = 5604851) B5604851
theorem B13100039 : Blo 1435537 13100039 := bstep (se 1 (by rfl) ⟨9825029, by rfl⟩ : syracuseStep 13100039 = 19650059) B19650059
theorem B6907025 : Blo 1435537 6907025 := bstep (se 2 (by rfl) ⟨2590134, by rfl⟩ : syracuseStep 6907025 = 5180269) B5180269
theorem B5465303 : Blo 1435537 5465303 := bstep (se 1 (by rfl) ⟨4098977, by rfl⟩ : syracuseStep 5465303 = 8197955) B8197955
theorem B2155739 : Blo 1435537 2155739 := bstep (se 1 (by rfl) ⟨1616804, by rfl⟩ : syracuseStep 2155739 = 3233609) B3233609
theorem B1615135 : Blo 1435537 1615135 := bstep (se 1 (by rfl) ⟨1211351, by rfl⟩ : syracuseStep 1615135 = 2422703) B2422703
theorem B2155913 : Blo 1435537 2155913 := bstep (se 2 (by rfl) ⟨808467, by rfl⟩ : syracuseStep 2155913 = 1616935) B1616935
theorem B5457415 : Blo 1435537 5457415 := bstep (se 1 (by rfl) ⟨4093061, by rfl⟩ : syracuseStep 5457415 = 8186123) B8186123
theorem B1615423 : Blo 1435537 1615423 := bstep (se 1 (by rfl) ⟨1211567, by rfl⟩ : syracuseStep 1615423 = 2423135) B2423135
theorem B3278431 : Blo 1435537 3278431 := bstep (se 1 (by rfl) ⟨2458823, by rfl⟩ : syracuseStep 3278431 = 4917647) B4917647
theorem B2156267 : Blo 1435537 2156267 := bstep (se 1 (by rfl) ⟨1617200, by rfl⟩ : syracuseStep 2156267 = 3234401) B3234401
theorem B19654433 : Blo 1435537 19654433 := bstep (se 2 (by rfl) ⟨7370412, by rfl⟩ : syracuseStep 19654433 = 14740825) B14740825
theorem B5457719 : Blo 1435537 5457719 := bstep (se 1 (by rfl) ⟨4093289, by rfl⟩ : syracuseStep 5457719 = 8186579) B8186579
theorem B1435547 : Blo 1435537 1435547 := bstep (se 1 (by rfl) ⟨1076660, by rfl⟩ : syracuseStep 1435547 = 2153321) B2153321
theorem B1435599 : Blo 1435537 1435599 := bstep (se 1 (by rfl) ⟨1076699, by rfl⟩ : syracuseStep 1435599 = 2153399) B2153399
theorem B132630479 : Blo 1435537 132630479 := bstep (se 1 (by rfl) ⟨99472859, by rfl⟩ : syracuseStep 132630479 = 198945719) B198945719
theorem B1435623 : Blo 1435537 1435623 := bstep (se 1 (by rfl) ⟨1076717, by rfl⟩ : syracuseStep 1435623 = 2153435) B2153435
theorem B5457901 : Blo 1435537 5457901 := bstep (se 3 (by rfl) ⟨1023356, by rfl⟩ : syracuseStep 5457901 = 2046713) B2046713
theorem B1435935 : Blo 1435537 1435935 := bstep (se 1 (by rfl) ⟨1076951, by rfl⟩ : syracuseStep 1435935 = 2153903) B2153903
theorem B12265789 : Blo 1435537 12265789 := bstep (se 3 (by rfl) ⟨2299835, by rfl⟩ : syracuseStep 12265789 = 4599671) B4599671
theorem B1435995 : Blo 1435537 1435995 := bstep (se 1 (by rfl) ⟨1076996, by rfl⟩ : syracuseStep 1435995 = 2153993) B2153993
theorem B3230063 : Blo 1435537 3230063 := bstep (se 1 (by rfl) ⟨2422547, by rfl⟩ : syracuseStep 3230063 = 4845095) B4845095
theorem B1436015 : Blo 1435537 1436015 := bstep (se 1 (by rfl) ⟨1077011, by rfl⟩ : syracuseStep 1436015 = 2154023) B2154023
theorem B20703599 : Blo 1435537 20703599 := bstep (se 1 (by rfl) ⟨15527699, by rfl⟩ : syracuseStep 20703599 = 31055399) B31055399
theorem B1616251 : Blo 1435537 1616251 := bstep (se 1 (by rfl) ⟨1212188, by rfl⟩ : syracuseStep 1616251 = 2424377) B2424377
theorem B1436071 : Blo 1435537 1436071 := bstep (se 1 (by rfl) ⟨1077053, by rfl⟩ : syracuseStep 1436071 = 2154107) B2154107
theorem B3230135 : Blo 1435537 3230135 := bstep (se 1 (by rfl) ⟨2422601, by rfl⟩ : syracuseStep 3230135 = 4845203) B4845203
theorem B1436155 : Blo 1435537 1436155 := bstep (se 1 (by rfl) ⟨1077116, by rfl⟩ : syracuseStep 1436155 = 2154233) B2154233
theorem B1436223 : Blo 1435537 1436223 := bstep (se 1 (by rfl) ⟨1077167, by rfl⟩ : syracuseStep 1436223 = 2154335) B2154335
theorem B3230279 : Blo 1435537 3230279 := bstep (se 1 (by rfl) ⟨2422709, by rfl⟩ : syracuseStep 3230279 = 4845419) B4845419
theorem B1436231 : Blo 1435537 1436231 := bstep (se 1 (by rfl) ⟨1077173, by rfl⟩ : syracuseStep 1436231 = 2154347) B2154347
theorem B12266063 : Blo 1435537 12266063 := bstep (se 1 (by rfl) ⟨9199547, by rfl⟩ : syracuseStep 12266063 = 18399095) B18399095
theorem B3230315 : Blo 1435537 3230315 := bstep (se 1 (by rfl) ⟨2422736, by rfl⟩ : syracuseStep 3230315 = 4845473) B4845473
theorem B1436383 : Blo 1435537 1436383 := bstep (se 1 (by rfl) ⟨1077287, by rfl⟩ : syracuseStep 1436383 = 2154575) B2154575
theorem B16370423 : Blo 1435537 16370423 := bstep (se 1 (by rfl) ⟨12277817, by rfl⟩ : syracuseStep 16370423 = 24555635) B24555635
theorem B1436463 : Blo 1435537 1436463 := bstep (se 1 (by rfl) ⟨1077347, by rfl⟩ : syracuseStep 1436463 = 2154695) B2154695
theorem B1616719 : Blo 1435537 1616719 := bstep (se 1 (by rfl) ⟨1212539, by rfl⟩ : syracuseStep 1616719 = 2425079) B2425079
theorem B7269263 : Blo 1435537 7269263 := bstep (se 1 (by rfl) ⟨5451947, by rfl⟩ : syracuseStep 7269263 = 10903895) B10903895
theorem B6900623 : Blo 1435537 6900623 := bstep (se 1 (by rfl) ⟨5175467, by rfl⟩ : syracuseStep 6900623 = 10350935) B10350935
theorem B1436571 : Blo 1435537 1436571 := bstep (se 1 (by rfl) ⟨1077428, by rfl⟩ : syracuseStep 1436571 = 2154857) B2154857
theorem B1436623 : Blo 1435537 1436623 := bstep (se 1 (by rfl) ⟨1077467, by rfl⟩ : syracuseStep 1436623 = 2154935) B2154935
theorem B1436647 : Blo 1435537 1436647 := bstep (se 1 (by rfl) ⟨1077485, by rfl⟩ : syracuseStep 1436647 = 2154971) B2154971
theorem B3230711 : Blo 1435537 3230711 := bstep (se 1 (by rfl) ⟨2423033, by rfl⟩ : syracuseStep 3230711 = 4846067) B4846067
theorem B6900875 : Blo 1435537 6900875 := bstep (se 1 (by rfl) ⟨5175656, by rfl⟩ : syracuseStep 6900875 = 10351313) B10351313
theorem B1617115 : Blo 1435537 1617115 := bstep (se 1 (by rfl) ⟨1212836, by rfl⟩ : syracuseStep 1617115 = 2425673) B2425673
theorem B1436959 : Blo 1435537 1436959 := bstep (se 1 (by rfl) ⟨1077719, by rfl⟩ : syracuseStep 1436959 = 2155439) B2155439
theorem B2215199 : Blo 1435537 2215199 := bstep (se 1 (by rfl) ⟨1661399, by rfl⟩ : syracuseStep 2215199 = 3322799) B3322799
theorem B26553689 : Blo 1435537 26553689 := bstep (se 2 (by rfl) ⟨9957633, by rfl⟩ : syracuseStep 26553689 = 19915267) B19915267
theorem B1437019 : Blo 1435537 1437019 := bstep (se 1 (by rfl) ⟨1077764, by rfl⟩ : syracuseStep 1437019 = 2155529) B2155529
theorem B3231071 : Blo 1435537 3231071 := bstep (se 1 (by rfl) ⟨2423303, by rfl⟩ : syracuseStep 3231071 = 4846607) B4846607
theorem B1437039 : Blo 1435537 1437039 := bstep (se 1 (by rfl) ⟨1077779, by rfl⟩ : syracuseStep 1437039 = 2155559) B2155559
theorem B1437095 : Blo 1435537 1437095 := bstep (se 1 (by rfl) ⟨1077821, by rfl⟩ : syracuseStep 1437095 = 2155643) B2155643
theorem B4844987 : Blo 1435537 4844987 := bstep (se 1 (by rfl) ⟨3633740, by rfl⟩ : syracuseStep 4844987 = 7267481) B7267481
theorem B1437179 : Blo 1435537 1437179 := bstep (se 1 (by rfl) ⟨1077884, by rfl⟩ : syracuseStep 1437179 = 2155769) B2155769
theorem B1437247 : Blo 1435537 1437247 := bstep (se 1 (by rfl) ⟨1077935, by rfl⟩ : syracuseStep 1437247 = 2155871) B2155871
theorem B1437255 : Blo 1435537 1437255 := bstep (se 1 (by rfl) ⟨1077941, by rfl⟩ : syracuseStep 1437255 = 2155883) B2155883
theorem B11652781 : Blo 1435537 11652781 := bstep (se 3 (by rfl) ⟨2184896, by rfl⟩ : syracuseStep 11652781 = 4369793) B4369793
theorem B1437407 : Blo 1435537 1437407 := bstep (se 1 (by rfl) ⟨1078055, by rfl⟩ : syracuseStep 1437407 = 2156111) B2156111
theorem B3231467 : Blo 1435537 3231467 := bstep (se 1 (by rfl) ⟨2423600, by rfl⟩ : syracuseStep 3231467 = 4847201) B4847201
theorem B3067627 : Blo 1435537 3067627 := bstep (se 1 (by rfl) ⟨2300720, by rfl⟩ : syracuseStep 3067627 = 4601441) B4601441
theorem B2764523 : Blo 1435537 2764523 := bstep (se 1 (by rfl) ⟨2073392, by rfl⟩ : syracuseStep 2764523 = 4146785) B4146785
theorem B4091627 : Blo 1435537 4091627 := bstep (se 1 (by rfl) ⟨3068720, by rfl⟩ : syracuseStep 4091627 = 6137441) B6137441
theorem B4370183 : Blo 1435537 4370183 := bstep (se 1 (by rfl) ⟨3277637, by rfl⟩ : syracuseStep 4370183 = 6555275) B6555275
theorem B1437487 : Blo 1435537 1437487 := bstep (se 1 (by rfl) ⟨1078115, by rfl⟩ : syracuseStep 1437487 = 2156231) B2156231
theorem B3231593 : Blo 1435537 3231593 := bstep (se 2 (by rfl) ⟨1211847, by rfl⟩ : syracuseStep 3231593 = 2423695) B2423695
theorem B25547141 : Blo 1435537 25547141 := bstep (se 4 (by rfl) ⟨2395044, by rfl⟩ : syracuseStep 25547141 = 4790089) B4790089
theorem B3068327 : Blo 1435537 3068327 := bstep (se 1 (by rfl) ⟨2301245, by rfl⟩ : syracuseStep 3068327 = 4602491) B4602491
theorem B5820929 : Blo 1435537 5820929 := bstep (se 2 (by rfl) ⟨2182848, by rfl⟩ : syracuseStep 5820929 = 4365697) B4365697
theorem B27619865 : Blo 1435537 27619865 := bstep (se 2 (by rfl) ⟨10357449, by rfl⟩ : syracuseStep 27619865 = 20714899) B20714899
theorem B3232439 : Blo 1435537 3232439 := bstep (se 1 (by rfl) ⟨2424329, by rfl⟩ : syracuseStep 3232439 = 4848659) B4848659
theorem B18412217 : Blo 1435537 18412217 := bstep (se 2 (by rfl) ⟨6904581, by rfl⟩ : syracuseStep 18412217 = 13809163) B13809163
theorem B3232655 : Blo 1435537 3232655 := bstep (se 1 (by rfl) ⟨2424491, by rfl⟩ : syracuseStep 3232655 = 4848983) B4848983
theorem B7271369 : Blo 1435537 7271369 := bstep (se 2 (by rfl) ⟨2726763, by rfl⟩ : syracuseStep 7271369 = 5453527) B5453527
theorem B6132743 : Blo 1435537 6132743 := bstep (se 1 (by rfl) ⟨4599557, by rfl⟩ : syracuseStep 6132743 = 9199115) B9199115
theorem B6132793 : Blo 1435537 6132793 := bstep (se 2 (by rfl) ⟨2299797, by rfl⟩ : syracuseStep 6132793 = 4599595) B4599595
theorem B63845495 : Blo 1435537 63845495 := bstep (se 1 (by rfl) ⟨47884121, by rfl⟩ : syracuseStep 63845495 = 95768243) B95768243
theorem B13808855 : Blo 1435537 13808855 := bstep (se 1 (by rfl) ⟨10356641, by rfl⟩ : syracuseStep 13808855 = 20713283) B20713283
theorem B3634409 : Blo 1435537 3634409 := bstep (se 2 (by rfl) ⟨1362903, by rfl⟩ : syracuseStep 3634409 = 2725807) B2725807
theorem B6903083 : Blo 1435537 6903083 := bstep (se 1 (by rfl) ⟨5177312, by rfl⟩ : syracuseStep 6903083 = 10354625) B10354625
theorem B59807069 : Blo 1435537 59807069 := bstep (se 3 (by rfl) ⟨11213825, by rfl⟩ : syracuseStep 59807069 = 22427651) B22427651
theorem B3634571 : Blo 1435537 3634571 := bstep (se 1 (by rfl) ⟨2725928, by rfl⟩ : syracuseStep 3634571 = 5451857) B5451857
theorem B14751179 : Blo 1435537 14751179 := bstep (se 1 (by rfl) ⟨11063384, by rfl⟩ : syracuseStep 14751179 = 22126769) B22126769
theorem B13800941 : Blo 1435537 13800941 := bstep (se 3 (by rfl) ⟨2587676, by rfl⟩ : syracuseStep 13800941 = 5175353) B5175353
theorem B3069523 : Blo 1435537 3069523 := bstep (se 1 (by rfl) ⟨2302142, by rfl⟩ : syracuseStep 3069523 = 4604285) B4604285
theorem B3233375 : Blo 1435537 3233375 := bstep (se 1 (by rfl) ⟨2425031, by rfl⟩ : syracuseStep 3233375 = 4850063) B4850063
theorem B3274427 : Blo 1435537 3274427 := bstep (se 1 (by rfl) ⟨2455820, by rfl⟩ : syracuseStep 3274427 = 4911641) B4911641
theorem B2422507 : Blo 1435537 2422507 := bstep (se 1 (by rfl) ⟨1816880, by rfl⟩ : syracuseStep 2422507 = 3633761) B3633761
theorem B3233591 : Blo 1435537 3233591 := bstep (se 1 (by rfl) ⟨2425193, by rfl⟩ : syracuseStep 3233591 = 4850387) B4850387
theorem B11368279 : Blo 1435537 11368279 := bstep (se 1 (by rfl) ⟨8526209, by rfl⟩ : syracuseStep 11368279 = 17052419) B17052419
theorem B3233897 : Blo 1435537 3233897 := bstep (se 2 (by rfl) ⟨1212711, by rfl⟩ : syracuseStep 3233897 = 2425423) B2425423
theorem B7092359 : Blo 1435537 7092359 := bstep (se 1 (by rfl) ⟨5319269, by rfl⟩ : syracuseStep 7092359 = 10638539) B10638539
theorem B2185481 : Blo 1435537 2185481 := bstep (se 2 (by rfl) ⟨819555, by rfl⟩ : syracuseStep 2185481 = 1639111) B1639111
theorem B3635563 : Blo 1435537 3635563 := bstep (se 1 (by rfl) ⟨2726672, by rfl⟩ : syracuseStep 3635563 = 5453345) B5453345
theorem B8739197 : Blo 1435537 8739197 := bstep (se 3 (by rfl) ⟨1638599, by rfl⟩ : syracuseStep 8739197 = 3277199) B3277199
theorem B4667831 : Blo 1435537 4667831 := bstep (se 1 (by rfl) ⟨3500873, by rfl⟩ : syracuseStep 4667831 = 7001747) B7001747
theorem B2726369 : Blo 1435537 2726369 := bstep (se 2 (by rfl) ⟨1022388, by rfl⟩ : syracuseStep 2726369 = 2044777) B2044777
theorem B1817083 : Blo 1435537 1817083 := bstep (se 1 (by rfl) ⟨1362812, by rfl⟩ : syracuseStep 1817083 = 2725625) B2725625
theorem B15530555 : Blo 1435537 15530555 := bstep (se 1 (by rfl) ⟨11647916, by rfl⟩ : syracuseStep 15530555 = 23295833) B23295833
theorem B3234383 : Blo 1435537 3234383 := bstep (se 1 (by rfl) ⟨2425787, by rfl⟩ : syracuseStep 3234383 = 4851575) B4851575
theorem B3635887 : Blo 1435537 3635887 := bstep (se 1 (by rfl) ⟨2726915, by rfl⟩ : syracuseStep 3635887 = 5453831) B5453831
theorem B2423479 : Blo 1435537 2423479 := bstep (se 1 (by rfl) ⟨1817609, by rfl⟩ : syracuseStep 2423479 = 3635219) B3635219
theorem B2300599 : Blo 1435537 2300599 := bstep (se 1 (by rfl) ⟨1725449, by rfl⟩ : syracuseStep 2300599 = 3450899) B3450899
theorem B6134467 : Blo 1435537 6134467 := bstep (se 1 (by rfl) ⟨4600850, by rfl⟩ : syracuseStep 6134467 = 9201701) B9201701
theorem B1817311 : Blo 1435537 1817311 := bstep (se 1 (by rfl) ⟨1362983, by rfl⟩ : syracuseStep 1817311 = 2725967) B2725967
theorem B7469815 : Blo 1435537 7469815 := bstep (se 1 (by rfl) ⟨5602361, by rfl⟩ : syracuseStep 7469815 = 11204723) B11204723
theorem B2046799 : Blo 1435537 2046799 := bstep (se 1 (by rfl) ⟨1535099, by rfl⟩ : syracuseStep 2046799 = 3070199) B3070199
theorem B2153447 : Blo 1435537 2153447 := bstep (se 1 (by rfl) ⟨1615085, by rfl⟩ : syracuseStep 2153447 = 3230171) B3230171
theorem B2423783 : Blo 1435537 2423783 := bstep (se 1 (by rfl) ⟨1817837, by rfl⟩ : syracuseStep 2423783 = 3635675) B3635675
theorem B3636211 : Blo 1435537 3636211 := bstep (se 1 (by rfl) ⟨2727158, by rfl⟩ : syracuseStep 3636211 = 5454317) B5454317
theorem B5454971 : Blo 1435537 5454971 := bstep (se 1 (by rfl) ⟨4091228, by rfl⟩ : syracuseStep 5454971 = 8182457) B8182457
theorem B19651805 : Blo 1435537 19651805 := bstep (se 3 (by rfl) ⟨3684713, by rfl⟩ : syracuseStep 19651805 = 7369427) B7369427
theorem B17480933 : Blo 1435537 17480933 := bstep (se 4 (by rfl) ⟨1638837, by rfl⟩ : syracuseStep 17480933 = 3277675) B3277675
theorem B2153705 : Blo 1435537 2153705 := bstep (se 2 (by rfl) ⟨807639, by rfl⟩ : syracuseStep 2153705 = 1615279) B1615279
theorem B3685619 : Blo 1435537 3685619 := bstep (se 1 (by rfl) ⟨2764214, by rfl⟩ : syracuseStep 3685619 = 5528429) B5528429
theorem B2153759 : Blo 1435537 2153759 := bstep (se 1 (by rfl) ⟨1615319, by rfl⟩ : syracuseStep 2153759 = 3230639) B3230639
theorem B2727265 : Blo 1435537 2727265 := bstep (se 2 (by rfl) ⟨1022724, by rfl⟩ : syracuseStep 2727265 = 2045449) B2045449
theorem B5823863 : Blo 1435537 5823863 := bstep (se 1 (by rfl) ⟨4367897, by rfl⟩ : syracuseStep 5823863 = 8735795) B8735795
theorem B2153927 : Blo 1435537 2153927 := bstep (se 1 (by rfl) ⟨1615445, by rfl⟩ : syracuseStep 2153927 = 3230891) B3230891
theorem B1818055 : Blo 1435537 1818055 := bstep (se 1 (by rfl) ⟨1363541, by rfl⟩ : syracuseStep 1818055 = 2727083) B2727083
theorem B4603351 : Blo 1435537 4603351 := bstep (se 1 (by rfl) ⟨3452513, by rfl⟩ : syracuseStep 4603351 = 6905027) B6905027
theorem B4849145 : Blo 1435537 4849145 := bstep (se 2 (by rfl) ⟨1818429, by rfl⟩ : syracuseStep 4849145 = 3636859) B3636859
theorem B6135355 : Blo 1435537 6135355 := bstep (se 1 (by rfl) ⟨4601516, by rfl⟩ : syracuseStep 6135355 = 9203033) B9203033
theorem B9207391 : Blo 1435537 9207391 := bstep (se 1 (by rfl) ⟨6905543, by rfl⟩ : syracuseStep 9207391 = 13811087) B13811087
theorem B10354337 : Blo 1435537 10354337 := bstep (se 2 (by rfl) ⟨3882876, by rfl⟩ : syracuseStep 10354337 = 7765753) B7765753
theorem B3636971 : Blo 1435537 3636971 := bstep (se 1 (by rfl) ⟨2727728, by rfl⟩ : syracuseStep 3636971 = 5455457) B5455457
theorem B4849415 : Blo 1435537 4849415 := bstep (se 1 (by rfl) ⟨3637061, by rfl⟩ : syracuseStep 4849415 = 7274123) B7274123
theorem B2154281 : Blo 1435537 2154281 := bstep (se 2 (by rfl) ⟨807855, by rfl⟩ : syracuseStep 2154281 = 1615711) B1615711
theorem B2154287 : Blo 1435537 2154287 := bstep (se 1 (by rfl) ⟨1615715, by rfl⟩ : syracuseStep 2154287 = 3231431) B3231431
theorem B3686191 : Blo 1435537 3686191 := bstep (se 1 (by rfl) ⟨2764643, by rfl⟩ : syracuseStep 3686191 = 5529287) B5529287
theorem B4849469 : Blo 1435537 4849469 := bstep (se 3 (by rfl) ⟨909275, by rfl⟩ : syracuseStep 4849469 = 1818551) B1818551
theorem B5455745 : Blo 1435537 5455745 := bstep (se 2 (by rfl) ⟨2045904, by rfl⟩ : syracuseStep 5455745 = 4091809) B4091809
theorem B17031427 : Blo 1435537 17031427 := bstep (se 1 (by rfl) ⟨12773570, by rfl⟩ : syracuseStep 17031427 = 25547141) B25547141
theorem B2457983 : Blo 1435537 2457983 := bstep (se 1 (by rfl) ⟨1843487, by rfl⟩ : syracuseStep 2457983 = 3686975) B3686975
theorem B2154959 : Blo 1435537 2154959 := bstep (se 1 (by rfl) ⟨1616219, by rfl⟩ : syracuseStep 2154959 = 3232439) B3232439
theorem B2425295 : Blo 1435537 2425295 := bstep (se 1 (by rfl) ⟨1818971, by rfl⟩ : syracuseStep 2425295 = 3637943) B3637943
theorem B2155001 : Blo 1435537 2155001 := bstep (se 2 (by rfl) ⟨808125, by rfl⟩ : syracuseStep 2155001 = 1616251) B1616251
theorem B4850171 : Blo 1435537 4850171 := bstep (se 1 (by rfl) ⟨3637628, by rfl⟩ : syracuseStep 4850171 = 7275257) B7275257
theorem B157221425 : Blo 1435537 157221425 := bstep (se 2 (by rfl) ⟨58958034, by rfl⟩ : syracuseStep 157221425 = 117916069) B117916069
theorem B2155103 : Blo 1435537 2155103 := bstep (se 1 (by rfl) ⟨1616327, by rfl⟩ : syracuseStep 2155103 = 3232655) B3232655
theorem B4088495 : Blo 1435537 4088495 := bstep (se 1 (by rfl) ⟨3066371, by rfl⟩ : syracuseStep 4088495 = 6132743) B6132743
theorem B8733359 : Blo 1435537 8733359 := bstep (se 1 (by rfl) ⟨6550019, by rfl⟩ : syracuseStep 8733359 = 13100039) B13100039
theorem B4850441 : Blo 1435537 4850441 := bstep (se 2 (by rfl) ⟨1818915, by rfl⟩ : syracuseStep 4850441 = 3637831) B3637831
theorem B4604683 : Blo 1435537 4604683 := bstep (se 1 (by rfl) ⟨3453512, by rfl⟩ : syracuseStep 4604683 = 6907025) B6907025
theorem B18408221 : Blo 1435537 18408221 := bstep (se 3 (by rfl) ⟨3451541, by rfl⟩ : syracuseStep 18408221 = 6903083) B6903083
theorem B39871379 : Blo 1435537 39871379 := bstep (se 1 (by rfl) ⟨29903534, by rfl⟩ : syracuseStep 39871379 = 59807069) B59807069
theorem B9200627 : Blo 1435537 9200627 := bstep (se 1 (by rfl) ⟨6900470, by rfl⟩ : syracuseStep 9200627 = 13800941) B13800941
theorem B3638297 : Blo 1435537 3638297 := bstep (se 2 (by rfl) ⟨1364361, by rfl⟩ : syracuseStep 3638297 = 2728723) B2728723
theorem B2155583 : Blo 1435537 2155583 := bstep (se 1 (by rfl) ⟨1616687, by rfl⟩ : syracuseStep 2155583 = 3233375) B3233375
theorem B2155625 : Blo 1435537 2155625 := bstep (se 2 (by rfl) ⟨808359, by rfl⟩ : syracuseStep 2155625 = 1616719) B1616719
theorem B2729065 : Blo 1435537 2729065 := bstep (se 2 (by rfl) ⟨1023399, by rfl⟩ : syracuseStep 2729065 = 2046799) B2046799
theorem B2155727 : Blo 1435537 2155727 := bstep (se 1 (by rfl) ⟨1616795, by rfl⟩ : syracuseStep 2155727 = 3233591) B3233591
theorem B3638479 : Blo 1435537 3638479 := bstep (se 1 (by rfl) ⟨2728859, by rfl⟩ : syracuseStep 3638479 = 5457719) B5457719
theorem B2155931 : Blo 1435537 2155931 := bstep (se 1 (by rfl) ⟨1616948, by rfl⟩ : syracuseStep 2155931 = 3233897) B3233897
theorem B8177057 : Blo 1435537 8177057 := bstep (se 2 (by rfl) ⟨3066396, by rfl⟩ : syracuseStep 8177057 = 6132793) B6132793
theorem B4728239 : Blo 1435537 4728239 := bstep (se 1 (by rfl) ⟨3546179, by rfl⟩ : syracuseStep 4728239 = 7092359) B7092359
theorem B4851197 : Blo 1435537 4851197 := bstep (se 3 (by rfl) ⟨909599, by rfl⟩ : syracuseStep 4851197 = 1819199) B1819199
theorem B5826131 : Blo 1435537 5826131 := bstep (se 1 (by rfl) ⟨4369598, by rfl⟩ : syracuseStep 5826131 = 8739197) B8739197
theorem B2156153 : Blo 1435537 2156153 := bstep (se 2 (by rfl) ⟨808557, by rfl⟩ : syracuseStep 2156153 = 1617115) B1617115
theorem B8177375 : Blo 1435537 8177375 := bstep (se 1 (by rfl) ⟨6133031, by rfl⟩ : syracuseStep 8177375 = 12266063) B12266063
theorem B2156255 : Blo 1435537 2156255 := bstep (se 1 (by rfl) ⟨1617191, by rfl⟩ : syracuseStep 2156255 = 3234383) B3234383
theorem B13109053 : Blo 1435537 13109053 := bstep (se 3 (by rfl) ⟨2457947, by rfl⟩ : syracuseStep 13109053 = 4915895) B4915895
theorem B10913615 : Blo 1435537 10913615 := bstep (se 1 (by rfl) ⟨8185211, by rfl⟩ : syracuseStep 10913615 = 16370423) B16370423
theorem B6137801 : Blo 1435537 6137801 := bstep (se 2 (by rfl) ⟨2301675, by rfl⟩ : syracuseStep 6137801 = 4603351) B4603351
theorem B1435631 : Blo 1435537 1435631 := bstep (se 1 (by rfl) ⟨1076723, by rfl⟩ : syracuseStep 1435631 = 2153447) B2153447
theorem B1615855 : Blo 1435537 1615855 := bstep (se 1 (by rfl) ⟨1211891, by rfl⟩ : syracuseStep 1615855 = 2423783) B2423783
theorem B7276553 : Blo 1435537 7276553 := bstep (se 2 (by rfl) ⟨2728707, by rfl⟩ : syracuseStep 7276553 = 5457415) B5457415
theorem B13101203 : Blo 1435537 13101203 := bstep (se 1 (by rfl) ⟨9825902, by rfl⟩ : syracuseStep 13101203 = 19651805) B19651805
theorem B1435803 : Blo 1435537 1435803 := bstep (se 1 (by rfl) ⟨1076852, by rfl⟩ : syracuseStep 1435803 = 2153705) B2153705
theorem B1435839 : Blo 1435537 1435839 := bstep (se 1 (by rfl) ⟨1076879, by rfl⟩ : syracuseStep 1435839 = 2153759) B2153759
theorem B1476799 : Blo 1435537 1476799 := bstep (se 1 (by rfl) ⟨1107599, by rfl⟩ : syracuseStep 1476799 = 2215199) B2215199
theorem B3229991 : Blo 1435537 3229991 := bstep (se 1 (by rfl) ⟨2422493, by rfl⟩ : syracuseStep 3229991 = 4844987) B4844987
theorem B1435951 : Blo 1435537 1435951 := bstep (se 1 (by rfl) ⟨1076963, by rfl⟩ : syracuseStep 1435951 = 2153927) B2153927
theorem B3230009 : Blo 1435537 3230009 := bstep (se 2 (by rfl) ⟨1211253, by rfl⟩ : syracuseStep 3230009 = 2422507) B2422507
theorem B4090169 : Blo 1435537 4090169 := bstep (se 2 (by rfl) ⟨1533813, by rfl⟩ : syracuseStep 4090169 = 3067627) B3067627
theorem B15157705 : Blo 1435537 15157705 := bstep (se 2 (by rfl) ⟨5684139, by rfl⟩ : syracuseStep 15157705 = 11368279) B11368279
theorem B1436187 : Blo 1435537 1436187 := bstep (se 1 (by rfl) ⟨1077140, by rfl⟩ : syracuseStep 1436187 = 2154281) B2154281
theorem B1436191 : Blo 1435537 1436191 := bstep (se 1 (by rfl) ⟨1077143, by rfl⟩ : syracuseStep 1436191 = 2154287) B2154287
theorem B7277201 : Blo 1435537 7277201 := bstep (se 2 (by rfl) ⟨2728950, by rfl⟩ : syracuseStep 7277201 = 5457901) B5457901
theorem B20196155 : Blo 1435537 20196155 := bstep (se 1 (by rfl) ⟨15147116, by rfl⟩ : syracuseStep 20196155 = 30294233) B30294233
theorem B13806395 : Blo 1435537 13806395 := bstep (se 1 (by rfl) ⟨10354796, by rfl⟩ : syracuseStep 13806395 = 20709593) B20709593
theorem B1436507 : Blo 1435537 1436507 := bstep (se 1 (by rfl) ⟨1077380, by rfl⟩ : syracuseStep 1436507 = 2154761) B2154761
theorem B1436575 : Blo 1435537 1436575 := bstep (se 1 (by rfl) ⟨1077431, by rfl⟩ : syracuseStep 1436575 = 2154863) B2154863
theorem B1436719 : Blo 1435537 1436719 := bstep (se 1 (by rfl) ⟨1077539, by rfl⟩ : syracuseStep 1436719 = 2155079) B2155079
theorem B1436743 : Blo 1435537 1436743 := bstep (se 1 (by rfl) ⟨1077557, by rfl⟩ : syracuseStep 1436743 = 2155115) B2155115
theorem B16354385 : Blo 1435537 16354385 := bstep (se 2 (by rfl) ⟨6132894, by rfl⟩ : syracuseStep 16354385 = 12265789) B12265789
theorem B12274811 : Blo 1435537 12274811 := bstep (se 1 (by rfl) ⟨9206108, by rfl⟩ : syracuseStep 12274811 = 18412217) B18412217
theorem B1436895 : Blo 1435537 1436895 := bstep (se 1 (by rfl) ⟨1077671, by rfl⟩ : syracuseStep 1436895 = 2155343) B2155343
theorem B5827949 : Blo 1435537 5827949 := bstep (se 3 (by rfl) ⟨1092740, by rfl⟩ : syracuseStep 5827949 = 2185481) B2185481
theorem B1437159 : Blo 1435537 1437159 := bstep (se 1 (by rfl) ⟨1077869, by rfl⟩ : syracuseStep 1437159 = 2155739) B2155739
theorem B3231305 : Blo 1435537 3231305 := bstep (se 2 (by rfl) ⟨1211739, by rfl⟩ : syracuseStep 3231305 = 2423479) B2423479
theorem B3067465 : Blo 1435537 3067465 := bstep (se 2 (by rfl) ⟨1150299, by rfl⟩ : syracuseStep 3067465 = 2300599) B2300599
theorem B8179289 : Blo 1435537 8179289 := bstep (se 2 (by rfl) ⟨3067233, by rfl⟩ : syracuseStep 8179289 = 6134467) B6134467
theorem B1437275 : Blo 1435537 1437275 := bstep (se 1 (by rfl) ⟨1077956, by rfl⟩ : syracuseStep 1437275 = 2155913) B2155913
theorem B9834119 : Blo 1435537 9834119 := bstep (se 1 (by rfl) ⟨7375589, by rfl⟩ : syracuseStep 9834119 = 14751179) B14751179
theorem B2182951 : Blo 1435537 2182951 := bstep (se 1 (by rfl) ⟨1637213, by rfl⟩ : syracuseStep 2182951 = 3274427) B3274427
theorem B1437511 : Blo 1435537 1437511 := bstep (se 1 (by rfl) ⟨1078133, by rfl⟩ : syracuseStep 1437511 = 2156267) B2156267
theorem B13102955 : Blo 1435537 13102955 := bstep (se 1 (by rfl) ⟨9827216, by rfl⟩ : syracuseStep 13102955 = 19654433) B19654433
theorem B88420319 : Blo 1435537 88420319 := bstep (se 1 (by rfl) ⟨66315239, by rfl⟩ : syracuseStep 88420319 = 132630479) B132630479
theorem B4846175 : Blo 1435537 4846175 := bstep (se 1 (by rfl) ⟨3634631, by rfl⟩ : syracuseStep 4846175 = 7269263) B7269263
theorem B4600415 : Blo 1435537 4600415 := bstep (se 1 (by rfl) ⟨3450311, by rfl⟩ : syracuseStep 4600415 = 6900623) B6900623
theorem B8180473 : Blo 1435537 8180473 := bstep (se 2 (by rfl) ⟨3067677, by rfl⟩ : syracuseStep 8180473 = 6135355) B6135355
theorem B4600583 : Blo 1435537 4600583 := bstep (se 1 (by rfl) ⟨3450437, by rfl⟩ : syracuseStep 4600583 = 6900875) B6900875
theorem B4092697 : Blo 1435537 4092697 := bstep (se 2 (by rfl) ⟨1534761, by rfl⟩ : syracuseStep 4092697 = 3069523) B3069523
theorem B12276521 : Blo 1435537 12276521 := bstep (se 2 (by rfl) ⟨4603695, by rfl⟩ : syracuseStep 12276521 = 9207391) B9207391
theorem B4371241 : Blo 1435537 4371241 := bstep (se 2 (by rfl) ⟨1639215, by rfl⟩ : syracuseStep 4371241 = 3278431) B3278431
theorem B11653955 : Blo 1435537 11653955 := bstep (se 1 (by rfl) ⟨8740466, by rfl⟩ : syracuseStep 11653955 = 17480933) B17480933
theorem B15537041 : Blo 1435537 15537041 := bstep (se 2 (by rfl) ⟨5826390, by rfl⟩ : syracuseStep 15537041 = 11652781) B11652781
theorem B3232763 : Blo 1435537 3232763 := bstep (se 1 (by rfl) ⟨2424572, by rfl⟩ : syracuseStep 3232763 = 4849145) B4849145
theorem B6902891 : Blo 1435537 6902891 := bstep (se 1 (by rfl) ⟨5177168, by rfl⟩ : syracuseStep 6902891 = 10354337) B10354337
theorem B3232943 : Blo 1435537 3232943 := bstep (se 1 (by rfl) ⟨2424707, by rfl⟩ : syracuseStep 3232943 = 4849415) B4849415
theorem B2913455 : Blo 1435537 2913455 := bstep (se 1 (by rfl) ⟨2185091, by rfl⟩ : syracuseStep 2913455 = 4370183) B4370183
theorem B3232979 : Blo 1435537 3232979 := bstep (se 1 (by rfl) ⟨2424734, by rfl⟩ : syracuseStep 3232979 = 4849469) B4849469
theorem B19928357 : Blo 1435537 19928357 := bstep (se 4 (by rfl) ⟨1868283, by rfl⟩ : syracuseStep 19928357 = 3736567) B3736567
theorem B5821787 : Blo 1435537 5821787 := bstep (se 1 (by rfl) ⟨4366340, by rfl⟩ : syracuseStep 5821787 = 8732681) B8732681
theorem B8738273 : Blo 1435537 8738273 := bstep (se 2 (by rfl) ⟨3276852, by rfl⟩ : syracuseStep 8738273 = 6553705) B6553705
theorem B3233249 : Blo 1435537 3233249 := bstep (se 2 (by rfl) ⟨1212468, by rfl⟩ : syracuseStep 3233249 = 2424937) B2424937
theorem B3880619 : Blo 1435537 3880619 := bstep (se 1 (by rfl) ⟨2910464, by rfl⟩ : syracuseStep 3880619 = 5820929) B5820929
theorem B18413243 : Blo 1435537 18413243 := bstep (se 1 (by rfl) ⟨13809932, by rfl⟩ : syracuseStep 18413243 = 27619865) B27619865
theorem B4847417 : Blo 1435537 4847417 := bstep (se 2 (by rfl) ⟨1817781, by rfl⟩ : syracuseStep 4847417 = 3635563) B3635563
theorem B4847579 : Blo 1435537 4847579 := bstep (se 1 (by rfl) ⟨3635684, by rfl⟩ : syracuseStep 4847579 = 7271369) B7271369
theorem B9828317 : Blo 1435537 9828317 := bstep (se 3 (by rfl) ⟨1842809, by rfl⟩ : syracuseStep 9828317 = 3685619) B3685619
theorem B2422777 : Blo 1435537 2422777 := bstep (se 2 (by rfl) ⟨908541, by rfl⟩ : syracuseStep 2422777 = 1817083) B1817083
theorem B42563663 : Blo 1435537 42563663 := bstep (se 1 (by rfl) ⟨31922747, by rfl⟩ : syracuseStep 42563663 = 63845495) B63845495
theorem B3643535 : Blo 1435537 3643535 := bstep (se 1 (by rfl) ⟨2732651, by rfl⟩ : syracuseStep 3643535 = 5465303) B5465303
theorem B9205903 : Blo 1435537 9205903 := bstep (se 1 (by rfl) ⟨6904427, by rfl⟩ : syracuseStep 9205903 = 13808855) B13808855
theorem B2422939 : Blo 1435537 2422939 := bstep (se 1 (by rfl) ⟨1817204, by rfl⟩ : syracuseStep 2422939 = 3634409) B3634409
theorem B4847849 : Blo 1435537 4847849 := bstep (se 2 (by rfl) ⟨1817943, by rfl⟩ : syracuseStep 4847849 = 3635887) B3635887
theorem B2423047 : Blo 1435537 2423047 := bstep (se 1 (by rfl) ⟨1817285, by rfl⟩ : syracuseStep 2423047 = 3634571) B3634571
theorem B2423081 : Blo 1435537 2423081 := bstep (se 2 (by rfl) ⟨908655, by rfl⟩ : syracuseStep 2423081 = 1817311) B1817311
theorem B9959753 : Blo 1435537 9959753 := bstep (se 2 (by rfl) ⟨3734907, by rfl⟩ : syracuseStep 9959753 = 7469815) B7469815
theorem B8182205 : Blo 1435537 8182205 := bstep (se 3 (by rfl) ⟨1534163, by rfl⟩ : syracuseStep 8182205 = 3068327) B3068327
theorem B4848281 : Blo 1435537 4848281 := bstep (se 2 (by rfl) ⟨1818105, by rfl⟩ : syracuseStep 4848281 = 3636211) B3636211
theorem B2153375 : Blo 1435537 2153375 := bstep (se 1 (by rfl) ⟨1615031, by rfl⟩ : syracuseStep 2153375 = 3230063) B3230063
theorem B13802399 : Blo 1435537 13802399 := bstep (se 1 (by rfl) ⟨10351799, by rfl⟩ : syracuseStep 13802399 = 20703599) B20703599
theorem B19659685 : Blo 1435537 19659685 := bstep (se 4 (by rfl) ⟨1843095, by rfl⟩ : syracuseStep 19659685 = 3686191) B3686191
theorem B2153423 : Blo 1435537 2153423 := bstep (se 1 (by rfl) ⟨1615067, by rfl⟩ : syracuseStep 2153423 = 3230135) B3230135
theorem B3111887 : Blo 1435537 3111887 := bstep (se 1 (by rfl) ⟨2333915, by rfl⟩ : syracuseStep 3111887 = 4667831) B4667831
theorem B1817579 : Blo 1435537 1817579 := bstep (se 1 (by rfl) ⟨1363184, by rfl⟩ : syracuseStep 1817579 = 2726369) B2726369
theorem B10353703 : Blo 1435537 10353703 := bstep (se 1 (by rfl) ⟨7765277, by rfl⟩ : syracuseStep 10353703 = 15530555) B15530555
theorem B2153513 : Blo 1435537 2153513 := bstep (se 2 (by rfl) ⟨807567, by rfl⟩ : syracuseStep 2153513 = 1615135) B1615135
theorem B2153519 : Blo 1435537 2153519 := bstep (se 1 (by rfl) ⟨1615139, by rfl⟩ : syracuseStep 2153519 = 3230279) B3230279
theorem B2153543 : Blo 1435537 2153543 := bstep (se 1 (by rfl) ⟨1615157, by rfl⟩ : syracuseStep 2153543 = 3230315) B3230315
theorem B3636353 : Blo 1435537 3636353 := bstep (se 2 (by rfl) ⟨1363632, by rfl⟩ : syracuseStep 3636353 = 2727265) B2727265
theorem B2424073 : Blo 1435537 2424073 := bstep (se 2 (by rfl) ⟨909027, by rfl⟩ : syracuseStep 2424073 = 1818055) B1818055
theorem B2153807 : Blo 1435537 2153807 := bstep (se 1 (by rfl) ⟨1615355, by rfl⟩ : syracuseStep 2153807 = 3230711) B3230711
theorem B3636647 : Blo 1435537 3636647 := bstep (se 1 (by rfl) ⟨2727485, by rfl⟩ : syracuseStep 3636647 = 5454971) B5454971
theorem B2153897 : Blo 1435537 2153897 := bstep (se 2 (by rfl) ⟨807711, by rfl⟩ : syracuseStep 2153897 = 1615423) B1615423
theorem B17702459 : Blo 1435537 17702459 := bstep (se 1 (by rfl) ⟨13276844, by rfl⟩ : syracuseStep 17702459 = 26553689) B26553689
theorem B2154047 : Blo 1435537 2154047 := bstep (se 1 (by rfl) ⟨1615535, by rfl⟩ : syracuseStep 2154047 = 3231071) B3231071
theorem B3882575 : Blo 1435537 3882575 := bstep (se 1 (by rfl) ⟨2911931, by rfl⟩ : syracuseStep 3882575 = 5823863) B5823863
theorem B2154311 : Blo 1435537 2154311 := bstep (se 1 (by rfl) ⟨1615733, by rfl⟩ : syracuseStep 2154311 = 3231467) B3231467
theorem B1843015 : Blo 1435537 1843015 := bstep (se 1 (by rfl) ⟨1382261, by rfl⟩ : syracuseStep 1843015 = 2764523) B2764523
theorem B2424647 : Blo 1435537 2424647 := bstep (se 1 (by rfl) ⟨1818485, by rfl⟩ : syracuseStep 2424647 = 3636971) B3636971
theorem B2727751 : Blo 1435537 2727751 := bstep (se 1 (by rfl) ⟨2045813, by rfl⟩ : syracuseStep 2727751 = 4091627) B4091627
theorem B2154395 : Blo 1435537 2154395 := bstep (se 1 (by rfl) ⟨1615796, by rfl⟩ : syracuseStep 2154395 = 3231593) B3231593
theorem B3637163 : Blo 1435537 3637163 := bstep (se 1 (by rfl) ⟨2727872, by rfl⟩ : syracuseStep 3637163 = 5455745) B5455745
theorem B12272147 : Blo 1435537 12272147 := bstep (se 1 (by rfl) ⟨9204110, by rfl⟩ : syracuseStep 12272147 = 18408221) B18408221
theorem B8184347 : Blo 1435537 8184347 := bstep (se 1 (by rfl) ⟨6138260, by rfl⟩ : syracuseStep 8184347 = 12276521) B12276521
theorem B20210273 : Blo 1435537 20210273 := bstep (se 2 (by rfl) ⟨7578852, by rfl⟩ : syracuseStep 20210273 = 15157705) B15157705
theorem B2155175 : Blo 1435537 2155175 := bstep (se 1 (by rfl) ⟨1616381, by rfl⟩ : syracuseStep 2155175 = 3232763) B3232763
theorem B2425531 : Blo 1435537 2425531 := bstep (se 1 (by rfl) ⟨1819148, by rfl⟩ : syracuseStep 2425531 = 3638297) B3638297
theorem B2155295 : Blo 1435537 2155295 := bstep (se 1 (by rfl) ⟨1616471, by rfl⟩ : syracuseStep 2155295 = 3232943) B3232943
theorem B1942303 : Blo 1435537 1942303 := bstep (se 1 (by rfl) ⟨1456727, by rfl⟩ : syracuseStep 1942303 = 2913455) B2913455
theorem B2155319 : Blo 1435537 2155319 := bstep (se 1 (by rfl) ⟨1616489, by rfl⟩ : syracuseStep 2155319 = 3232979) B3232979
theorem B5825515 : Blo 1435537 5825515 := bstep (se 1 (by rfl) ⟨4369136, by rfl⟩ : syracuseStep 5825515 = 8738273) B8738273
theorem B2155499 : Blo 1435537 2155499 := bstep (se 1 (by rfl) ⟨1616624, by rfl⟩ : syracuseStep 2155499 = 3233249) B3233249
theorem B6554621 : Blo 1435537 6554621 := bstep (se 3 (by rfl) ⟨1228991, by rfl⟩ : syracuseStep 6554621 = 2457983) B2457983
theorem B5456929 : Blo 1435537 5456929 := bstep (se 2 (by rfl) ⟨2046348, by rfl⟩ : syracuseStep 5456929 = 4092697) B4092697
theorem B3884087 : Blo 1435537 3884087 := bstep (se 1 (by rfl) ⟨2913065, by rfl⟩ : syracuseStep 3884087 = 5826131) B5826131
theorem B7275743 : Blo 1435537 7275743 := bstep (se 1 (by rfl) ⟨5456807, by rfl⟩ : syracuseStep 7275743 = 10913615) B10913615
theorem B4851035 : Blo 1435537 4851035 := bstep (se 1 (by rfl) ⟨3638276, by rfl⟩ : syracuseStep 4851035 = 7276553) B7276553
theorem B13804937 : Blo 1435537 13804937 := bstep (se 2 (by rfl) ⟨5176851, by rfl⟩ : syracuseStep 13804937 = 10353703) B10353703
theorem B3638753 : Blo 1435537 3638753 := bstep (se 2 (by rfl) ⟨1364532, by rfl⟩ : syracuseStep 3638753 = 2729065) B2729065
theorem B1615387 : Blo 1435537 1615387 := bstep (se 1 (by rfl) ⟨1211540, by rfl⟩ : syracuseStep 1615387 = 2423081) B2423081
theorem B4851305 : Blo 1435537 4851305 := bstep (se 2 (by rfl) ⟨1819239, by rfl⟩ : syracuseStep 4851305 = 3638479) B3638479
theorem B4851467 : Blo 1435537 4851467 := bstep (se 1 (by rfl) ⟨3638600, by rfl⟩ : syracuseStep 4851467 = 7277201) B7277201
theorem B1435583 : Blo 1435537 1435583 := bstep (se 1 (by rfl) ⟨1076687, by rfl⟩ : syracuseStep 1435583 = 2153375) B2153375
theorem B9201599 : Blo 1435537 9201599 := bstep (se 1 (by rfl) ⟨6901199, by rfl⟩ : syracuseStep 9201599 = 13802399) B13802399
theorem B1435615 : Blo 1435537 1435615 := bstep (se 1 (by rfl) ⟨1076711, by rfl⟩ : syracuseStep 1435615 = 2153423) B2153423
theorem B2074591 : Blo 1435537 2074591 := bstep (se 1 (by rfl) ⟨1555943, by rfl⟩ : syracuseStep 2074591 = 3111887) B3111887
theorem B1435675 : Blo 1435537 1435675 := bstep (se 1 (by rfl) ⟨1076756, by rfl⟩ : syracuseStep 1435675 = 2153513) B2153513
theorem B1435679 : Blo 1435537 1435679 := bstep (se 1 (by rfl) ⟨1076759, by rfl⟩ : syracuseStep 1435679 = 2153519) B2153519
theorem B1435695 : Blo 1435537 1435695 := bstep (se 1 (by rfl) ⟨1076771, by rfl⟩ : syracuseStep 1435695 = 2153543) B2153543
theorem B4089953 : Blo 1435537 4089953 := bstep (se 2 (by rfl) ⟨1533732, by rfl⟩ : syracuseStep 4089953 = 3067465) B3067465
theorem B1435871 : Blo 1435537 1435871 := bstep (se 1 (by rfl) ⟨1076903, by rfl⟩ : syracuseStep 1435871 = 2153807) B2153807
theorem B3885299 : Blo 1435537 3885299 := bstep (se 1 (by rfl) ⟨2913974, by rfl⟩ : syracuseStep 3885299 = 5827949) B5827949
theorem B1435931 : Blo 1435537 1435931 := bstep (se 1 (by rfl) ⟨1076948, by rfl⟩ : syracuseStep 1435931 = 2153897) B2153897
theorem B1436031 : Blo 1435537 1436031 := bstep (se 1 (by rfl) ⟨1077023, by rfl⟩ : syracuseStep 1436031 = 2154047) B2154047
theorem B2910601 : Blo 1435537 2910601 := bstep (se 2 (by rfl) ⟨1091475, by rfl⟩ : syracuseStep 2910601 = 2182951) B2182951
theorem B6556079 : Blo 1435537 6556079 := bstep (se 1 (by rfl) ⟨4917059, by rfl⟩ : syracuseStep 6556079 = 9834119) B9834119
theorem B1436207 : Blo 1435537 1436207 := bstep (se 1 (by rfl) ⟨1077155, by rfl⟩ : syracuseStep 1436207 = 2154311) B2154311
theorem B1616431 : Blo 1435537 1616431 := bstep (se 1 (by rfl) ⟨1212323, by rfl⟩ : syracuseStep 1616431 = 2424647) B2424647
theorem B8735303 : Blo 1435537 8735303 := bstep (se 1 (by rfl) ⟨6551477, by rfl⟩ : syracuseStep 8735303 = 13102955) B13102955
theorem B1436263 : Blo 1435537 1436263 := bstep (se 1 (by rfl) ⟨1077197, by rfl⟩ : syracuseStep 1436263 = 2154395) B2154395
theorem B3230369 : Blo 1435537 3230369 := bstep (se 2 (by rfl) ⟨1211388, by rfl⟩ : syracuseStep 3230369 = 2422777) B2422777
theorem B12274537 : Blo 1435537 12274537 := bstep (se 2 (by rfl) ⟨4602951, by rfl⟩ : syracuseStep 12274537 = 9205903) B9205903
theorem B3230585 : Blo 1435537 3230585 := bstep (se 2 (by rfl) ⟨1211469, by rfl⟩ : syracuseStep 3230585 = 2422939) B2422939
theorem B1436639 : Blo 1435537 1436639 := bstep (se 1 (by rfl) ⟨1077479, by rfl⟩ : syracuseStep 1436639 = 2154959) B2154959
theorem B1616863 : Blo 1435537 1616863 := bstep (se 1 (by rfl) ⟨1212647, by rfl⟩ : syracuseStep 1616863 = 2425295) B2425295
theorem B1436667 : Blo 1435537 1436667 := bstep (se 1 (by rfl) ⟨1077500, by rfl⟩ : syracuseStep 1436667 = 2155001) B2155001
theorem B3230729 : Blo 1435537 3230729 := bstep (se 2 (by rfl) ⟨1211523, by rfl⟩ : syracuseStep 3230729 = 2423047) B2423047
theorem B3230783 : Blo 1435537 3230783 := bstep (se 1 (by rfl) ⟨2423087, by rfl⟩ : syracuseStep 3230783 = 4846175) B4846175
theorem B1436735 : Blo 1435537 1436735 := bstep (se 1 (by rfl) ⟨1077551, by rfl⟩ : syracuseStep 1436735 = 2155103) B2155103
theorem B3067055 : Blo 1435537 3067055 := bstep (se 1 (by rfl) ⟨2300291, by rfl⟩ : syracuseStep 3067055 = 4600583) B4600583
theorem B7769303 : Blo 1435537 7769303 := bstep (se 1 (by rfl) ⟨5826977, by rfl⟩ : syracuseStep 7769303 = 11653955) B11653955
theorem B10358027 : Blo 1435537 10358027 := bstep (se 1 (by rfl) ⟨7768520, by rfl⟩ : syracuseStep 10358027 = 15537041) B15537041
theorem B1437055 : Blo 1435537 1437055 := bstep (se 1 (by rfl) ⟨1077791, by rfl⟩ : syracuseStep 1437055 = 2155583) B2155583
theorem B1437083 : Blo 1435537 1437083 := bstep (se 1 (by rfl) ⟨1077812, by rfl⟩ : syracuseStep 1437083 = 2155625) B2155625
theorem B1437151 : Blo 1435537 1437151 := bstep (se 1 (by rfl) ⟨1077863, by rfl⟩ : syracuseStep 1437151 = 2155727) B2155727
theorem B1437287 : Blo 1435537 1437287 := bstep (se 1 (by rfl) ⟨1077965, by rfl⟩ : syracuseStep 1437287 = 2155931) B2155931
theorem B5451371 : Blo 1435537 5451371 := bstep (se 1 (by rfl) ⟨4088528, by rfl⟩ : syracuseStep 5451371 = 8177057) B8177057
theorem B10907297 : Blo 1435537 10907297 := bstep (se 2 (by rfl) ⟨4090236, by rfl⟩ : syracuseStep 10907297 = 8180473) B8180473
theorem B7876261 : Blo 1435537 7876261 := bstep (se 4 (by rfl) ⟨738399, by rfl⟩ : syracuseStep 7876261 = 1476799) B1476799
theorem B6139577 : Blo 1435537 6139577 := bstep (se 2 (by rfl) ⟨2302341, by rfl⟩ : syracuseStep 6139577 = 4604683) B4604683
theorem B5828321 : Blo 1435537 5828321 := bstep (se 2 (by rfl) ⟨2185620, by rfl⟩ : syracuseStep 5828321 = 4371241) B4371241
theorem B1437435 : Blo 1435537 1437435 := bstep (se 1 (by rfl) ⟨1078076, by rfl⟩ : syracuseStep 1437435 = 2156153) B2156153
theorem B12275495 : Blo 1435537 12275495 := bstep (se 1 (by rfl) ⟨9206621, by rfl⟩ : syracuseStep 12275495 = 18413243) B18413243
theorem B5451583 : Blo 1435537 5451583 := bstep (se 1 (by rfl) ⟨4088687, by rfl⟩ : syracuseStep 5451583 = 8177375) B8177375
theorem B1437503 : Blo 1435537 1437503 := bstep (se 1 (by rfl) ⟨1078127, by rfl⟩ : syracuseStep 1437503 = 2156255) B2156255
theorem B3231611 : Blo 1435537 3231611 := bstep (se 1 (by rfl) ⟨2423708, by rfl⟩ : syracuseStep 3231611 = 4847417) B4847417
theorem B4091867 : Blo 1435537 4091867 := bstep (se 1 (by rfl) ⟨3068900, by rfl⟩ : syracuseStep 4091867 = 6137801) B6137801
theorem B3231719 : Blo 1435537 3231719 := bstep (se 1 (by rfl) ⟨2423789, by rfl⟩ : syracuseStep 3231719 = 4847579) B4847579
theorem B2429023 : Blo 1435537 2429023 := bstep (se 1 (by rfl) ⟨1821767, by rfl⟩ : syracuseStep 2429023 = 3643535) B3643535
theorem B3231899 : Blo 1435537 3231899 := bstep (se 1 (by rfl) ⟨2423924, by rfl⟩ : syracuseStep 3231899 = 4847849) B4847849
theorem B6639835 : Blo 1435537 6639835 := bstep (se 1 (by rfl) ⟨4979876, by rfl⟩ : syracuseStep 6639835 = 9959753) B9959753
theorem B12267773 : Blo 1435537 12267773 := bstep (se 3 (by rfl) ⟨2300207, by rfl⟩ : syracuseStep 12267773 = 4600415) B4600415
theorem B3232097 : Blo 1435537 3232097 := bstep (se 2 (by rfl) ⟨1212036, by rfl⟩ : syracuseStep 3232097 = 2424073) B2424073
theorem B3232187 : Blo 1435537 3232187 := bstep (se 1 (by rfl) ⟨2424140, by rfl⟩ : syracuseStep 3232187 = 4848281) B4848281
theorem B13464103 : Blo 1435537 13464103 := bstep (se 1 (by rfl) ⟨10098077, by rfl⟩ : syracuseStep 13464103 = 20196155) B20196155
theorem B9204263 : Blo 1435537 9204263 := bstep (se 1 (by rfl) ⟨6903197, by rfl⟩ : syracuseStep 9204263 = 13806395) B13806395
theorem B11801639 : Blo 1435537 11801639 := bstep (se 1 (by rfl) ⟨8851229, by rfl⟩ : syracuseStep 11801639 = 17702459) B17702459
theorem B5452859 : Blo 1435537 5452859 := bstep (se 1 (by rfl) ⟨4089644, by rfl⟩ : syracuseStep 5452859 = 8179289) B8179289
theorem B17478737 : Blo 1435537 17478737 := bstep (se 2 (by rfl) ⟨6554526, by rfl⟩ : syracuseStep 17478737 = 13109053) B13109053
theorem B4846877 : Blo 1435537 4846877 := bstep (se 3 (by rfl) ⟨908789, by rfl⟩ : syracuseStep 4846877 = 1817579) B1817579
theorem B58946879 : Blo 1435537 58946879 := bstep (se 1 (by rfl) ⟨44210159, by rfl⟩ : syracuseStep 58946879 = 88420319) B88420319
theorem B363337109 : Blo 1435537 363337109 := bstep (se 6 (by rfl) ⟨8515713, by rfl⟩ : syracuseStep 363337109 = 17031427) B17031427
theorem B3233447 : Blo 1435537 3233447 := bstep (se 1 (by rfl) ⟨2425085, by rfl⟩ : syracuseStep 3233447 = 4850171) B4850171
theorem B104814283 : Blo 1435537 104814283 := bstep (se 1 (by rfl) ⟨78610712, by rfl⟩ : syracuseStep 104814283 = 157221425) B157221425
theorem B34936541 : Blo 1435537 34936541 := bstep (se 3 (by rfl) ⟨6550601, by rfl⟩ : syracuseStep 34936541 = 13101203) B13101203
theorem B2725663 : Blo 1435537 2725663 := bstep (se 1 (by rfl) ⟨2044247, by rfl⟩ : syracuseStep 2725663 = 4088495) B4088495
theorem B5822239 : Blo 1435537 5822239 := bstep (se 1 (by rfl) ⟨4366679, by rfl⟩ : syracuseStep 5822239 = 8733359) B8733359
theorem B3233627 : Blo 1435537 3233627 := bstep (se 1 (by rfl) ⟨2425220, by rfl⟩ : syracuseStep 3233627 = 4850441) B4850441
theorem B26580919 : Blo 1435537 26580919 := bstep (se 1 (by rfl) ⟨19935689, by rfl⟩ : syracuseStep 26580919 = 39871379) B39871379
theorem B6133751 : Blo 1435537 6133751 := bstep (se 1 (by rfl) ⟨4600313, by rfl⟩ : syracuseStep 6133751 = 9200627) B9200627
theorem B4601927 : Blo 1435537 4601927 := bstep (se 1 (by rfl) ⟨3451445, by rfl⟩ : syracuseStep 4601927 = 6902891) B6902891
theorem B13285571 : Blo 1435537 13285571 := bstep (se 1 (by rfl) ⟨9964178, by rfl⟩ : syracuseStep 13285571 = 19928357) B19928357
theorem B3881191 : Blo 1435537 3881191 := bstep (se 1 (by rfl) ⟨2910893, by rfl⟩ : syracuseStep 3881191 = 5821787) B5821787
theorem B3152159 : Blo 1435537 3152159 := bstep (se 1 (by rfl) ⟨2364119, by rfl⟩ : syracuseStep 3152159 = 4728239) B4728239
theorem B3234131 : Blo 1435537 3234131 := bstep (se 1 (by rfl) ⟨2425598, by rfl⟩ : syracuseStep 3234131 = 4851197) B4851197
theorem B2587079 : Blo 1435537 2587079 := bstep (se 1 (by rfl) ⟨1940309, by rfl⟩ : syracuseStep 2587079 = 3880619) B3880619
theorem B26212913 : Blo 1435537 26212913 := bstep (se 2 (by rfl) ⟨9829842, by rfl⟩ : syracuseStep 26212913 = 19659685) B19659685
theorem B6552211 : Blo 1435537 6552211 := bstep (se 1 (by rfl) ⟨4914158, by rfl⟩ : syracuseStep 6552211 = 9828317) B9828317
theorem B28375775 : Blo 1435537 28375775 := bstep (se 1 (by rfl) ⟨21281831, by rfl⟩ : syracuseStep 28375775 = 42563663) B42563663
theorem B2153327 : Blo 1435537 2153327 := bstep (se 1 (by rfl) ⟨1614995, by rfl⟩ : syracuseStep 2153327 = 3229991) B3229991
theorem B2153339 : Blo 1435537 2153339 := bstep (se 1 (by rfl) ⟨1615004, by rfl⟩ : syracuseStep 2153339 = 3230009) B3230009
theorem B2726779 : Blo 1435537 2726779 := bstep (se 1 (by rfl) ⟨2045084, by rfl⟩ : syracuseStep 2726779 = 4090169) B4090169
theorem B5454803 : Blo 1435537 5454803 := bstep (se 1 (by rfl) ⟨4091102, by rfl⟩ : syracuseStep 5454803 = 8182205) B8182205
theorem B10902923 : Blo 1435537 10902923 := bstep (se 1 (by rfl) ⟨8177192, by rfl⟩ : syracuseStep 10902923 = 16354385) B16354385
theorem B8183207 : Blo 1435537 8183207 := bstep (se 1 (by rfl) ⟨6137405, by rfl⟩ : syracuseStep 8183207 = 12274811) B12274811
theorem B2424235 : Blo 1435537 2424235 := bstep (se 1 (by rfl) ⟨1818176, by rfl⟩ : syracuseStep 2424235 = 3636353) B3636353
theorem B2424431 : Blo 1435537 2424431 := bstep (se 1 (by rfl) ⟨1818323, by rfl⟩ : syracuseStep 2424431 = 3636647) B3636647
theorem B2154203 : Blo 1435537 2154203 := bstep (se 1 (by rfl) ⟨1615652, by rfl⟩ : syracuseStep 2154203 = 3231305) B3231305
theorem B2588383 : Blo 1435537 2588383 := bstep (se 1 (by rfl) ⟨1941287, by rfl⟩ : syracuseStep 2588383 = 3882575) B3882575
theorem B2457353 : Blo 1435537 2457353 := bstep (se 2 (by rfl) ⟨921507, by rfl⟩ : syracuseStep 2457353 = 1843015) B1843015
theorem B3637001 : Blo 1435537 3637001 := bstep (se 2 (by rfl) ⟨1363875, by rfl⟩ : syracuseStep 3637001 = 2727751) B2727751
theorem B2424775 : Blo 1435537 2424775 := bstep (se 1 (by rfl) ⟨1818581, by rfl⟩ : syracuseStep 2424775 = 3637163) B3637163
theorem B2154473 : Blo 1435537 2154473 := bstep (se 2 (by rfl) ⟨807927, by rfl⟩ : syracuseStep 2154473 = 1615855) B1615855
theorem B2154599 : Blo 1435537 2154599 := bstep (se 1 (by rfl) ⟨1615949, by rfl⟩ : syracuseStep 2154599 = 3231899) B3231899
theorem B2154731 : Blo 1435537 2154731 := bstep (se 1 (by rfl) ⟨1616048, by rfl⟩ : syracuseStep 2154731 = 3232097) B3232097
theorem B2154791 : Blo 1435537 2154791 := bstep (se 1 (by rfl) ⟨1616093, by rfl⟩ : syracuseStep 2154791 = 3232187) B3232187
theorem B5456231 : Blo 1435537 5456231 := bstep (se 1 (by rfl) ⟨4092173, by rfl⟩ : syracuseStep 5456231 = 8184347) B8184347
theorem B6136175 : Blo 1435537 6136175 := bstep (se 1 (by rfl) ⟨4602131, by rfl⟩ : syracuseStep 6136175 = 9204263) B9204263
theorem B2589391 : Blo 1435537 2589391 := bstep (se 1 (by rfl) ⟨1942043, by rfl⟩ : syracuseStep 2589391 = 3884087) B3884087
theorem B2155241 : Blo 1435537 2155241 := bstep (se 2 (by rfl) ⟨808215, by rfl⟩ : syracuseStep 2155241 = 1616431) B1616431
theorem B4850495 : Blo 1435537 4850495 := bstep (se 1 (by rfl) ⟨3637871, by rfl⟩ : syracuseStep 4850495 = 7275743) B7275743
theorem B39297919 : Blo 1435537 39297919 := bstep (se 1 (by rfl) ⟨29473439, by rfl⟩ : syracuseStep 39297919 = 58946879) B58946879
theorem B2425835 : Blo 1435537 2425835 := bstep (se 1 (by rfl) ⟨1819376, by rfl⟩ : syracuseStep 2425835 = 3638753) B3638753
theorem B2589737 : Blo 1435537 2589737 := bstep (se 2 (by rfl) ⟨971151, by rfl⟩ : syracuseStep 2589737 = 1942303) B1942303
theorem B2155631 : Blo 1435537 2155631 := bstep (se 1 (by rfl) ⟨1616723, by rfl⟩ : syracuseStep 2155631 = 3233447) B3233447
theorem B17482877 : Blo 1435537 17482877 := bstep (se 3 (by rfl) ⟨3278039, by rfl⟩ : syracuseStep 17482877 = 6556079) B6556079
theorem B23291027 : Blo 1435537 23291027 := bstep (se 1 (by rfl) ⟨17468270, by rfl⟩ : syracuseStep 23291027 = 34936541) B34936541
theorem B6898877 : Blo 1435537 6898877 := bstep (se 3 (by rfl) ⟨1293539, by rfl⟩ : syracuseStep 6898877 = 2587079) B2587079
theorem B2155751 : Blo 1435537 2155751 := bstep (se 1 (by rfl) ⟨1616813, by rfl⟩ : syracuseStep 2155751 = 3233627) B3233627
theorem B2155817 : Blo 1435537 2155817 := bstep (se 2 (by rfl) ⟨808431, by rfl⟩ : syracuseStep 2155817 = 1616863) B1616863
theorem B7767353 : Blo 1435537 7767353 := bstep (se 2 (by rfl) ⟨2912757, by rfl⟩ : syracuseStep 7767353 = 5825515) B5825515
theorem B4089167 : Blo 1435537 4089167 := bstep (se 1 (by rfl) ⟨3066875, by rfl⟩ : syracuseStep 4089167 = 6133751) B6133751
theorem B7275905 : Blo 1435537 7275905 := bstep (se 2 (by rfl) ⟨2728464, by rfl⟩ : syracuseStep 7275905 = 5456929) B5456929
theorem B2590199 : Blo 1435537 2590199 := bstep (se 1 (by rfl) ⟨1942649, by rfl⟩ : syracuseStep 2590199 = 3885299) B3885299
theorem B2156087 : Blo 1435537 2156087 := bstep (se 1 (by rfl) ⟨1617065, by rfl⟩ : syracuseStep 2156087 = 3234131) B3234131
theorem B17475275 : Blo 1435537 17475275 := bstep (se 1 (by rfl) ⟨13106456, by rfl⟩ : syracuseStep 17475275 = 26212913) B26212913
theorem B18917183 : Blo 1435537 18917183 := bstep (se 1 (by rfl) ⟨14187887, by rfl⟩ : syracuseStep 18917183 = 28375775) B28375775
theorem B1435551 : Blo 1435537 1435551 := bstep (se 1 (by rfl) ⟨1076663, by rfl⟩ : syracuseStep 1435551 = 2153327) B2153327
theorem B1435559 : Blo 1435537 1435559 := bstep (se 1 (by rfl) ⟨1076669, by rfl⟩ : syracuseStep 1435559 = 2153339) B2153339
theorem B15542189 : Blo 1435537 15542189 := bstep (se 3 (by rfl) ⟨2914160, by rfl⟩ : syracuseStep 15542189 = 5828321) B5828321
theorem B5179535 : Blo 1435537 5179535 := bstep (se 1 (by rfl) ⟨3884651, by rfl⟩ : syracuseStep 5179535 = 7769303) B7769303
theorem B7268615 : Blo 1435537 7268615 := bstep (se 1 (by rfl) ⟨5451461, by rfl⟩ : syracuseStep 7268615 = 10902923) B10902923
theorem B3451177 : Blo 1435537 3451177 := bstep (se 2 (by rfl) ⟨1294191, by rfl⟩ : syracuseStep 3451177 = 2588383) B2588383
theorem B1616287 : Blo 1435537 1616287 := bstep (se 1 (by rfl) ⟨1212215, by rfl⟩ : syracuseStep 1616287 = 2424431) B2424431
theorem B7268777 : Blo 1435537 7268777 := bstep (se 2 (by rfl) ⟨2725791, by rfl⟩ : syracuseStep 7268777 = 5451583) B5451583
theorem B1436135 : Blo 1435537 1436135 := bstep (se 1 (by rfl) ⟨1077101, by rfl⟩ : syracuseStep 1436135 = 2154203) B2154203
theorem B35441225 : Blo 1435537 35441225 := bstep (se 2 (by rfl) ⟨13290459, by rfl⟩ : syracuseStep 35441225 = 26580919) B26580919
theorem B1436315 : Blo 1435537 1436315 := bstep (se 1 (by rfl) ⟨1077236, by rfl⟩ : syracuseStep 1436315 = 2154473) B2154473
theorem B3238697 : Blo 1435537 3238697 := bstep (se 2 (by rfl) ⟨1214511, by rfl⟩ : syracuseStep 3238697 = 2429023) B2429023
theorem B8178515 : Blo 1435537 8178515 := bstep (se 1 (by rfl) ⟨6133886, by rfl⟩ : syracuseStep 8178515 = 12267773) B12267773
theorem B33623029 : Blo 1435537 33623029 := bstep (se 5 (by rfl) ⟨1576079, by rfl⟩ : syracuseStep 33623029 = 3152159) B3152159
theorem B1436783 : Blo 1435537 1436783 := bstep (se 1 (by rfl) ⟨1077587, by rfl⟩ : syracuseStep 1436783 = 2155175) B2155175
theorem B1436863 : Blo 1435537 1436863 := bstep (se 1 (by rfl) ⟨1077647, by rfl⟩ : syracuseStep 1436863 = 2155295) B2155295
theorem B1436879 : Blo 1435537 1436879 := bstep (se 1 (by rfl) ⟨1077659, by rfl⟩ : syracuseStep 1436879 = 2155319) B2155319
theorem B1436999 : Blo 1435537 1436999 := bstep (se 1 (by rfl) ⟨1077749, by rfl⟩ : syracuseStep 1436999 = 2155499) B2155499
theorem B4369747 : Blo 1435537 4369747 := bstep (se 1 (by rfl) ⟨3277310, by rfl⟩ : syracuseStep 4369747 = 6554621) B6554621
theorem B17952137 : Blo 1435537 17952137 := bstep (se 2 (by rfl) ⟨6732051, by rfl⟩ : syracuseStep 17952137 = 13464103) B13464103
theorem B11652491 : Blo 1435537 11652491 := bstep (se 1 (by rfl) ⟨8739368, by rfl⟩ : syracuseStep 11652491 = 17478737) B17478737
theorem B3231251 : Blo 1435537 3231251 := bstep (se 1 (by rfl) ⟨2423438, by rfl⟩ : syracuseStep 3231251 = 4846877) B4846877
theorem B8736281 : Blo 1435537 8736281 := bstep (se 2 (by rfl) ⟨3276105, by rfl⟩ : syracuseStep 8736281 = 6552211) B6552211
theorem B9203291 : Blo 1435537 9203291 := bstep (se 1 (by rfl) ⟨6902468, by rfl⟩ : syracuseStep 9203291 = 13804937) B13804937
theorem B242224739 : Blo 1435537 242224739 := bstep (se 1 (by rfl) ⟨181668554, by rfl⟩ : syracuseStep 242224739 = 363337109) B363337109
theorem B3067951 : Blo 1435537 3067951 := bstep (se 1 (by rfl) ⟨2300963, by rfl⟩ : syracuseStep 3067951 = 4601927) B4601927
theorem B23294141 : Blo 1435537 23294141 := bstep (se 3 (by rfl) ⟨4367651, by rfl⟩ : syracuseStep 23294141 = 8735303) B8735303
theorem B3232313 : Blo 1435537 3232313 := bstep (se 2 (by rfl) ⟨1212117, by rfl⟩ : syracuseStep 3232313 = 2424235) B2424235
theorem B2044703 : Blo 1435537 2044703 := bstep (se 1 (by rfl) ⟨1533527, by rfl⟩ : syracuseStep 2044703 = 3067055) B3067055
theorem B139752377 : Blo 1435537 139752377 := bstep (se 2 (by rfl) ⟨52407141, by rfl⟩ : syracuseStep 139752377 = 104814283) B104814283
theorem B3634217 : Blo 1435537 3634217 := bstep (se 2 (by rfl) ⟨1362831, by rfl⟩ : syracuseStep 3634217 = 2725663) B2725663
theorem B7762985 : Blo 1435537 7762985 := bstep (se 2 (by rfl) ⟨2911119, by rfl⟩ : syracuseStep 7762985 = 5822239) B5822239
theorem B3634247 : Blo 1435537 3634247 := bstep (se 1 (by rfl) ⟨2725685, by rfl⟩ : syracuseStep 3634247 = 5451371) B5451371
theorem B7271531 : Blo 1435537 7271531 := bstep (se 1 (by rfl) ⟨5453648, by rfl⟩ : syracuseStep 7271531 = 10907297) B10907297
theorem B4093051 : Blo 1435537 4093051 := bstep (se 1 (by rfl) ⟨3069788, by rfl⟩ : syracuseStep 4093051 = 6139577) B6139577
theorem B11064485 : Blo 1435537 11064485 := bstep (se 4 (by rfl) ⟨1037295, by rfl⟩ : syracuseStep 11064485 = 2074591) B2074591
theorem B3233033 : Blo 1435537 3233033 := bstep (se 2 (by rfl) ⟨1212387, by rfl⟩ : syracuseStep 3233033 = 2424775) B2424775
theorem B31471037 : Blo 1435537 31471037 := bstep (se 3 (by rfl) ⟨5900819, by rfl⟩ : syracuseStep 31471037 = 11801639) B11801639
theorem B8853113 : Blo 1435537 8853113 := bstep (se 2 (by rfl) ⟨3319917, by rfl⟩ : syracuseStep 8853113 = 6639835) B6639835
theorem B5174921 : Blo 1435537 5174921 := bstep (se 2 (by rfl) ⟨1940595, by rfl⟩ : syracuseStep 5174921 = 3881191) B3881191
theorem B8181431 : Blo 1435537 8181431 := bstep (se 1 (by rfl) ⟨6136073, by rfl⟩ : syracuseStep 8181431 = 12272147) B12272147
theorem B13473515 : Blo 1435537 13473515 := bstep (se 1 (by rfl) ⟨10105136, by rfl⟩ : syracuseStep 13473515 = 20210273) B20210273
theorem B3880801 : Blo 1435537 3880801 := bstep (se 2 (by rfl) ⟨1455300, by rfl⟩ : syracuseStep 3880801 = 2910601) B2910601
theorem B3635239 : Blo 1435537 3635239 := bstep (se 1 (by rfl) ⟨2726429, by rfl⟩ : syracuseStep 3635239 = 5452859) B5452859
theorem B42006725 : Blo 1435537 42006725 := bstep (se 4 (by rfl) ⟨3938130, by rfl⟩ : syracuseStep 42006725 = 7876261) B7876261
theorem B3234023 : Blo 1435537 3234023 := bstep (se 1 (by rfl) ⟨2425517, by rfl⟩ : syracuseStep 3234023 = 4851035) B4851035
theorem B3234041 : Blo 1435537 3234041 := bstep (se 2 (by rfl) ⟨1212765, by rfl⟩ : syracuseStep 3234041 = 2425531) B2425531
theorem B3234203 : Blo 1435537 3234203 := bstep (se 1 (by rfl) ⟨2425652, by rfl⟩ : syracuseStep 3234203 = 4851305) B4851305
theorem B16366049 : Blo 1435537 16366049 := bstep (se 2 (by rfl) ⟨6137268, by rfl⟩ : syracuseStep 16366049 = 12274537) B12274537
theorem B3635705 : Blo 1435537 3635705 := bstep (se 2 (by rfl) ⟨1363389, by rfl⟩ : syracuseStep 3635705 = 2726779) B2726779
theorem B3234311 : Blo 1435537 3234311 := bstep (se 1 (by rfl) ⟨2425733, by rfl⟩ : syracuseStep 3234311 = 4851467) B4851467
theorem B6134399 : Blo 1435537 6134399 := bstep (se 1 (by rfl) ⟨4600799, by rfl⟩ : syracuseStep 6134399 = 9201599) B9201599
theorem B2726635 : Blo 1435537 2726635 := bstep (se 1 (by rfl) ⟨2044976, by rfl⟩ : syracuseStep 2726635 = 4089953) B4089953
theorem B2153579 : Blo 1435537 2153579 := bstep (se 1 (by rfl) ⟨1615184, by rfl⟩ : syracuseStep 2153579 = 3230369) B3230369
theorem B2153723 : Blo 1435537 2153723 := bstep (se 1 (by rfl) ⟨1615292, by rfl⟩ : syracuseStep 2153723 = 3230585) B3230585
theorem B3636535 : Blo 1435537 3636535 := bstep (se 1 (by rfl) ⟨2727401, by rfl⟩ : syracuseStep 3636535 = 5454803) B5454803
theorem B2153819 : Blo 1435537 2153819 := bstep (se 1 (by rfl) ⟨1615364, by rfl⟩ : syracuseStep 2153819 = 3230729) B3230729
theorem B141712757 : Blo 1435537 141712757 := bstep (se 5 (by rfl) ⟨6642785, by rfl⟩ : syracuseStep 141712757 = 13285571) B13285571
theorem B2153849 : Blo 1435537 2153849 := bstep (se 2 (by rfl) ⟨807693, by rfl⟩ : syracuseStep 2153849 = 1615387) B1615387
theorem B2153855 : Blo 1435537 2153855 := bstep (se 1 (by rfl) ⟨1615391, by rfl⟩ : syracuseStep 2153855 = 3230783) B3230783
theorem B6905351 : Blo 1435537 6905351 := bstep (se 1 (by rfl) ⟨5179013, by rfl⟩ : syracuseStep 6905351 = 10358027) B10358027
theorem B5455471 : Blo 1435537 5455471 := bstep (se 1 (by rfl) ⟨4091603, by rfl⟩ : syracuseStep 5455471 = 8183207) B8183207
theorem B1638235 : Blo 1435537 1638235 := bstep (se 1 (by rfl) ⟨1228676, by rfl⟩ : syracuseStep 1638235 = 2457353) B2457353
theorem B2424667 : Blo 1435537 2424667 := bstep (se 1 (by rfl) ⟨1818500, by rfl⟩ : syracuseStep 2424667 = 3637001) B3637001
theorem B8183663 : Blo 1435537 8183663 := bstep (se 1 (by rfl) ⟨6137747, by rfl⟩ : syracuseStep 8183663 = 12275495) B12275495
theorem B2154407 : Blo 1435537 2154407 := bstep (se 1 (by rfl) ⟨1615805, by rfl⟩ : syracuseStep 2154407 = 3231611) B3231611
theorem B2727911 : Blo 1435537 2727911 := bstep (se 1 (by rfl) ⟨2045933, by rfl⟩ : syracuseStep 2727911 = 4091867) B4091867
theorem B2154479 : Blo 1435537 2154479 := bstep (se 1 (by rfl) ⟨1615859, by rfl⟩ : syracuseStep 2154479 = 3231719) B3231719
theorem B3637487 : Blo 1435537 3637487 := bstep (se 1 (by rfl) ⟨2728115, by rfl⟩ : syracuseStep 3637487 = 5456231) B5456231
theorem B2154875 : Blo 1435537 2154875 := bstep (se 1 (by rfl) ⟨1616156, by rfl⟩ : syracuseStep 2154875 = 3232313) B3232313
theorem B27623861 : Blo 1435537 27623861 := bstep (se 5 (by rfl) ⟨1294868, by rfl⟩ : syracuseStep 27623861 = 2589737) B2589737
theorem B2155049 : Blo 1435537 2155049 := bstep (se 2 (by rfl) ⟨808143, by rfl⟩ : syracuseStep 2155049 = 1616287) B1616287
theorem B93168251 : Blo 1435537 93168251 := bstep (se 1 (by rfl) ⟨69876188, by rfl⟩ : syracuseStep 93168251 = 139752377) B139752377
theorem B2155355 : Blo 1435537 2155355 := bstep (se 1 (by rfl) ⟨1616516, by rfl⟩ : syracuseStep 2155355 = 3233033) B3233033
theorem B4850603 : Blo 1435537 4850603 := bstep (se 1 (by rfl) ⟨3637952, by rfl⟩ : syracuseStep 4850603 = 7275905) B7275905
theorem B20980691 : Blo 1435537 20980691 := bstep (se 1 (by rfl) ⟨15735518, by rfl⟩ : syracuseStep 20980691 = 31471037) B31471037
theorem B3449947 : Blo 1435537 3449947 := bstep (se 1 (by rfl) ⟨2587460, by rfl⟩ : syracuseStep 3449947 = 5174921) B5174921
theorem B52397225 : Blo 1435537 52397225 := bstep (se 2 (by rfl) ⟨19648959, by rfl⟩ : syracuseStep 52397225 = 39297919) B39297919
theorem B2156015 : Blo 1435537 2156015 := bstep (se 1 (by rfl) ⟨1617011, by rfl⟩ : syracuseStep 2156015 = 3234023) B3234023
theorem B5457401 : Blo 1435537 5457401 := bstep (se 2 (by rfl) ⟨2046525, by rfl⟩ : syracuseStep 5457401 = 4093051) B4093051
theorem B2156027 : Blo 1435537 2156027 := bstep (se 1 (by rfl) ⟨1617020, by rfl⟩ : syracuseStep 2156027 = 3234041) B3234041
theorem B2156135 : Blo 1435537 2156135 := bstep (se 1 (by rfl) ⟨1617101, by rfl⟩ : syracuseStep 2156135 = 3234203) B3234203
theorem B2156207 : Blo 1435537 2156207 := bstep (se 1 (by rfl) ⟨1617155, by rfl⟩ : syracuseStep 2156207 = 3234311) B3234311
theorem B23627483 : Blo 1435537 23627483 := bstep (se 1 (by rfl) ⟨17720612, by rfl⟩ : syracuseStep 23627483 = 35441225) B35441225
theorem B4089599 : Blo 1435537 4089599 := bstep (se 1 (by rfl) ⟨3067199, by rfl⟩ : syracuseStep 4089599 = 6134399) B6134399
theorem B5826329 : Blo 1435537 5826329 := bstep (se 2 (by rfl) ⟨2184873, by rfl⟩ : syracuseStep 5826329 = 4369747) B4369747
theorem B1435719 : Blo 1435537 1435719 := bstep (se 1 (by rfl) ⟨1076789, by rfl⟩ : syracuseStep 1435719 = 2153579) B2153579
theorem B1435815 : Blo 1435537 1435815 := bstep (se 1 (by rfl) ⟨1076861, by rfl⟩ : syracuseStep 1435815 = 2153723) B2153723
theorem B1435879 : Blo 1435537 1435879 := bstep (se 1 (by rfl) ⟨1076909, by rfl⟩ : syracuseStep 1435879 = 2153819) B2153819
theorem B1435899 : Blo 1435537 1435899 := bstep (se 1 (by rfl) ⟨1076924, by rfl⟩ : syracuseStep 1435899 = 2153849) B2153849
theorem B1435903 : Blo 1435537 1435903 := bstep (se 1 (by rfl) ⟨1076927, by rfl⟩ : syracuseStep 1435903 = 2153855) B2153855
theorem B7768327 : Blo 1435537 7768327 := bstep (se 1 (by rfl) ⟨5826245, by rfl⟩ : syracuseStep 7768327 = 11652491) B11652491
theorem B161483159 : Blo 1435537 161483159 := bstep (se 1 (by rfl) ⟨121112369, by rfl⟩ : syracuseStep 161483159 = 242224739) B242224739
theorem B1436271 : Blo 1435537 1436271 := bstep (se 1 (by rfl) ⟨1077203, by rfl⟩ : syracuseStep 1436271 = 2154407) B2154407
theorem B1436319 : Blo 1435537 1436319 := bstep (se 1 (by rfl) ⟨1077239, by rfl⟩ : syracuseStep 1436319 = 2154479) B2154479
theorem B4090601 : Blo 1435537 4090601 := bstep (se 2 (by rfl) ⟨1533975, by rfl⟩ : syracuseStep 4090601 = 3067951) B3067951
theorem B1436399 : Blo 1435537 1436399 := bstep (se 1 (by rfl) ⟨1077299, by rfl⟩ : syracuseStep 1436399 = 2154599) B2154599
theorem B1436487 : Blo 1435537 1436487 := bstep (se 1 (by rfl) ⟨1077365, by rfl⟩ : syracuseStep 1436487 = 2154731) B2154731
theorem B1436527 : Blo 1435537 1436527 := bstep (se 1 (by rfl) ⟨1077395, by rfl⟩ : syracuseStep 1436527 = 2154791) B2154791
theorem B1436827 : Blo 1435537 1436827 := bstep (se 1 (by rfl) ⟨1077620, by rfl⟩ : syracuseStep 1436827 = 2155241) B2155241
theorem B1617223 : Blo 1435537 1617223 := bstep (se 1 (by rfl) ⟨1212917, by rfl⟩ : syracuseStep 1617223 = 2425835) B2425835
theorem B1437087 : Blo 1435537 1437087 := bstep (se 1 (by rfl) ⟨1077815, by rfl⟩ : syracuseStep 1437087 = 2155631) B2155631
theorem B15527351 : Blo 1435537 15527351 := bstep (se 1 (by rfl) ⟨11645513, by rfl⟩ : syracuseStep 15527351 = 23291027) B23291027
theorem B4599251 : Blo 1435537 4599251 := bstep (se 1 (by rfl) ⟨3449438, by rfl⟩ : syracuseStep 4599251 = 6898877) B6898877
theorem B20712941 : Blo 1435537 20712941 := bstep (se 3 (by rfl) ⟨3883676, by rfl⟩ : syracuseStep 20712941 = 7767353) B7767353
theorem B1437167 : Blo 1435537 1437167 := bstep (se 1 (by rfl) ⟨1077875, by rfl⟩ : syracuseStep 1437167 = 2155751) B2155751
theorem B1437211 : Blo 1435537 1437211 := bstep (se 1 (by rfl) ⟨1077908, by rfl⟩ : syracuseStep 1437211 = 2155817) B2155817
theorem B16363133 : Blo 1435537 16363133 := bstep (se 3 (by rfl) ⟨3068087, by rfl⟩ : syracuseStep 16363133 = 6136175) B6136175
theorem B1437391 : Blo 1435537 1437391 := bstep (se 1 (by rfl) ⟨1078043, by rfl⟩ : syracuseStep 1437391 = 2156087) B2156087
theorem B5902075 : Blo 1435537 5902075 := bstep (se 1 (by rfl) ⟨4426556, by rfl⟩ : syracuseStep 5902075 = 8853113) B8853113
theorem B8982343 : Blo 1435537 8982343 := bstep (se 1 (by rfl) ⟨6736757, by rfl⟩ : syracuseStep 8982343 = 13473515) B13473515
theorem B44830705 : Blo 1435537 44830705 := bstep (se 2 (by rfl) ⟨16811514, by rfl⟩ : syracuseStep 44830705 = 33623029) B33623029
theorem B3453023 : Blo 1435537 3453023 := bstep (se 1 (by rfl) ⟨2589767, by rfl⟩ : syracuseStep 3453023 = 5179535) B5179535
theorem B28004483 : Blo 1435537 28004483 := bstep (se 1 (by rfl) ⟨21003362, by rfl⟩ : syracuseStep 28004483 = 42006725) B42006725
theorem B4845743 : Blo 1435537 4845743 := bstep (se 1 (by rfl) ⟨3634307, by rfl⟩ : syracuseStep 4845743 = 7268615) B7268615
theorem B4845851 : Blo 1435537 4845851 := bstep (se 1 (by rfl) ⟨3634388, by rfl⟩ : syracuseStep 4845851 = 7268777) B7268777
theorem B2159131 : Blo 1435537 2159131 := bstep (se 1 (by rfl) ⟨1619348, by rfl⟩ : syracuseStep 2159131 = 3238697) B3238697
theorem B46600733 : Blo 1435537 46600733 := bstep (se 3 (by rfl) ⟨8737637, by rfl⟩ : syracuseStep 46600733 = 17475275) B17475275
theorem B5452343 : Blo 1435537 5452343 := bstep (se 1 (by rfl) ⟨4089257, by rfl⟩ : syracuseStep 5452343 = 8178515) B8178515
theorem B5452541 : Blo 1435537 5452541 := bstep (se 3 (by rfl) ⟨1022351, by rfl⟩ : syracuseStep 5452541 = 2044703) B2044703
theorem B94475171 : Blo 1435537 94475171 := bstep (se 1 (by rfl) ⟨70856378, by rfl⟩ : syracuseStep 94475171 = 141712757) B141712757
theorem B2184313 : Blo 1435537 2184313 := bstep (se 2 (by rfl) ⟨819117, by rfl⟩ : syracuseStep 2184313 = 1638235) B1638235
theorem B3232889 : Blo 1435537 3232889 := bstep (se 2 (by rfl) ⟨1212333, by rfl⟩ : syracuseStep 3232889 = 2424667) B2424667
theorem B5174401 : Blo 1435537 5174401 := bstep (se 2 (by rfl) ⟨1940400, by rfl⟩ : syracuseStep 5174401 = 3880801) B3880801
theorem B4846985 : Blo 1435537 4846985 := bstep (se 2 (by rfl) ⟨1817619, by rfl⟩ : syracuseStep 4846985 = 3635239) B3635239
theorem B15529427 : Blo 1435537 15529427 := bstep (se 1 (by rfl) ⟨11647070, by rfl⟩ : syracuseStep 15529427 = 23294141) B23294141
theorem B4601569 : Blo 1435537 4601569 := bstep (se 2 (by rfl) ⟨1725588, by rfl⟩ : syracuseStep 4601569 = 3451177) B3451177
theorem B29505293 : Blo 1435537 29505293 := bstep (se 3 (by rfl) ⟨5532242, by rfl⟩ : syracuseStep 29505293 = 11064485) B11064485
theorem B3233663 : Blo 1435537 3233663 := bstep (se 1 (by rfl) ⟨2425247, by rfl⟩ : syracuseStep 3233663 = 4850495) B4850495
theorem B2422811 : Blo 1435537 2422811 := bstep (se 1 (by rfl) ⟨1817108, by rfl⟩ : syracuseStep 2422811 = 3634217) B3634217
theorem B5175323 : Blo 1435537 5175323 := bstep (se 1 (by rfl) ⟨3881492, by rfl⟩ : syracuseStep 5175323 = 7762985) B7762985
theorem B2422831 : Blo 1435537 2422831 := bstep (se 1 (by rfl) ⟨1817123, by rfl⟩ : syracuseStep 2422831 = 3634247) B3634247
theorem B4847687 : Blo 1435537 4847687 := bstep (se 1 (by rfl) ⟨3635765, by rfl⟩ : syracuseStep 4847687 = 7271531) B7271531
theorem B11655251 : Blo 1435537 11655251 := bstep (se 1 (by rfl) ⟨8741438, by rfl⟩ : syracuseStep 11655251 = 17482877) B17482877
theorem B2726111 : Blo 1435537 2726111 := bstep (se 1 (by rfl) ⟨2044583, by rfl⟩ : syracuseStep 2726111 = 4089167) B4089167
theorem B3635513 : Blo 1435537 3635513 := bstep (se 2 (by rfl) ⟨1363317, by rfl⟩ : syracuseStep 3635513 = 2726635) B2726635
theorem B1726799 : Blo 1435537 1726799 := bstep (se 1 (by rfl) ⟨1295099, by rfl⟩ : syracuseStep 1726799 = 2590199) B2590199
theorem B13810085 : Blo 1435537 13810085 := bstep (se 4 (by rfl) ⟨1294695, by rfl⟩ : syracuseStep 13810085 = 2589391) B2589391
theorem B5454287 : Blo 1435537 5454287 := bstep (se 1 (by rfl) ⟨4090715, by rfl⟩ : syracuseStep 5454287 = 8181431) B8181431
theorem B10361459 : Blo 1435537 10361459 := bstep (se 1 (by rfl) ⟨7771094, by rfl⟩ : syracuseStep 10361459 = 15542189) B15542189
theorem B10910699 : Blo 1435537 10910699 := bstep (se 1 (by rfl) ⟨8183024, by rfl⟩ : syracuseStep 10910699 = 16366049) B16366049
theorem B2423803 : Blo 1435537 2423803 := bstep (se 1 (by rfl) ⟨1817852, by rfl⟩ : syracuseStep 2423803 = 3635705) B3635705
theorem B4848713 : Blo 1435537 4848713 := bstep (se 2 (by rfl) ⟨1818267, by rfl⟩ : syracuseStep 4848713 = 3636535) B3636535
theorem B7273961 : Blo 1435537 7273961 := bstep (se 2 (by rfl) ⟨2727735, by rfl⟩ : syracuseStep 7273961 = 5455471) B5455471
theorem B50445821 : Blo 1435537 50445821 := bstep (se 3 (by rfl) ⟨9458591, by rfl⟩ : syracuseStep 50445821 = 18917183) B18917183
theorem B11968091 : Blo 1435537 11968091 := bstep (se 1 (by rfl) ⟨8976068, by rfl⟩ : syracuseStep 11968091 = 17952137) B17952137
theorem B4603567 : Blo 1435537 4603567 := bstep (se 1 (by rfl) ⟨3452675, by rfl⟩ : syracuseStep 4603567 = 6905351) B6905351
theorem B2154167 : Blo 1435537 2154167 := bstep (se 1 (by rfl) ⟨1615625, by rfl⟩ : syracuseStep 2154167 = 3231251) B3231251
theorem B5824187 : Blo 1435537 5824187 := bstep (se 1 (by rfl) ⟨4368140, by rfl⟩ : syracuseStep 5824187 = 8736281) B8736281
theorem B6135527 : Blo 1435537 6135527 := bstep (se 1 (by rfl) ⟨4601645, by rfl⟩ : syracuseStep 6135527 = 9203291) B9203291
theorem B5455775 : Blo 1435537 5455775 := bstep (se 1 (by rfl) ⟨4091831, by rfl⟩ : syracuseStep 5455775 = 8183663) B8183663
theorem B1818607 : Blo 1435537 1818607 := bstep (se 1 (by rfl) ⟨1363955, by rfl⟩ : syracuseStep 1818607 = 2727911) B2727911
theorem B2302015 : Blo 1435537 2302015 := bstep (se 1 (by rfl) ⟨1726511, by rfl⟩ : syracuseStep 2302015 = 3453023) B3453023
theorem B18669655 : Blo 1435537 18669655 := bstep (se 1 (by rfl) ⟨14002241, by rfl⟩ : syracuseStep 18669655 = 28004483) B28004483
theorem B2424991 : Blo 1435537 2424991 := bstep (se 1 (by rfl) ⟨1818743, by rfl⟩ : syracuseStep 2424991 = 3637487) B3637487
theorem B18415907 : Blo 1435537 18415907 := bstep (se 1 (by rfl) ⟨13811930, by rfl⟩ : syracuseStep 18415907 = 27623861) B27623861
theorem B62112167 : Blo 1435537 62112167 := bstep (se 1 (by rfl) ⟨46584125, by rfl⟩ : syracuseStep 62112167 = 93168251) B93168251
theorem B2155259 : Blo 1435537 2155259 := bstep (se 1 (by rfl) ⟨1616444, by rfl⟩ : syracuseStep 2155259 = 3232889) B3232889
theorem B34931483 : Blo 1435537 34931483 := bstep (se 1 (by rfl) ⟨26198612, by rfl⟩ : syracuseStep 34931483 = 52397225) B52397225
theorem B4604797 : Blo 1435537 4604797 := bstep (se 3 (by rfl) ⟨863399, by rfl⟩ : syracuseStep 4604797 = 1726799) B1726799
theorem B3638267 : Blo 1435537 3638267 := bstep (se 1 (by rfl) ⟨2728700, by rfl⟩ : syracuseStep 3638267 = 5457401) B5457401
theorem B430621757 : Blo 1435537 430621757 := bstep (se 3 (by rfl) ⟨80741579, by rfl⟩ : syracuseStep 430621757 = 161483159) B161483159
theorem B19670195 : Blo 1435537 19670195 := bstep (se 1 (by rfl) ⟨14752646, by rfl⟩ : syracuseStep 19670195 = 29505293) B29505293
theorem B3884219 : Blo 1435537 3884219 := bstep (se 1 (by rfl) ⟨2913164, by rfl⟩ : syracuseStep 3884219 = 5826329) B5826329
theorem B2155775 : Blo 1435537 2155775 := bstep (se 1 (by rfl) ⟨1616831, by rfl⟩ : syracuseStep 2155775 = 3233663) B3233663
theorem B1615207 : Blo 1435537 1615207 := bstep (se 1 (by rfl) ⟨1211405, by rfl⟩ : syracuseStep 1615207 = 2422811) B2422811
theorem B3450215 : Blo 1435537 3450215 := bstep (se 1 (by rfl) ⟨2587661, by rfl⟩ : syracuseStep 3450215 = 5175323) B5175323
theorem B6899201 : Blo 1435537 6899201 := bstep (se 2 (by rfl) ⟨2587200, by rfl⟩ : syracuseStep 6899201 = 5174401) B5174401
theorem B2156297 : Blo 1435537 2156297 := bstep (se 2 (by rfl) ⟨808611, by rfl⟩ : syracuseStep 2156297 = 1617223) B1617223
theorem B6138089 : Blo 1435537 6138089 := bstep (se 2 (by rfl) ⟨2301783, by rfl⟩ : syracuseStep 6138089 = 4603567) B4603567
theorem B3066167 : Blo 1435537 3066167 := bstep (se 1 (by rfl) ⟨2299625, by rfl⟩ : syracuseStep 3066167 = 4599251) B4599251
theorem B33630547 : Blo 1435537 33630547 := bstep (se 1 (by rfl) ⟨25222910, by rfl⟩ : syracuseStep 33630547 = 50445821) B50445821
theorem B1436111 : Blo 1435537 1436111 := bstep (se 1 (by rfl) ⟨1077083, by rfl⟩ : syracuseStep 1436111 = 2154167) B2154167
theorem B4090351 : Blo 1435537 4090351 := bstep (se 1 (by rfl) ⟨3067763, by rfl⟩ : syracuseStep 4090351 = 6135527) B6135527
theorem B3230441 : Blo 1435537 3230441 := bstep (se 2 (by rfl) ⟨1211415, by rfl⟩ : syracuseStep 3230441 = 2422831) B2422831
theorem B3230495 : Blo 1435537 3230495 := bstep (se 1 (by rfl) ⟨2422871, by rfl⟩ : syracuseStep 3230495 = 4845743) B4845743
theorem B3230567 : Blo 1435537 3230567 := bstep (se 1 (by rfl) ⟨2422925, by rfl⟩ : syracuseStep 3230567 = 4845851) B4845851
theorem B1436583 : Blo 1435537 1436583 := bstep (se 1 (by rfl) ⟨1077437, by rfl⟩ : syracuseStep 1436583 = 2154875) B2154875
theorem B10357769 : Blo 1435537 10357769 := bstep (se 2 (by rfl) ⟨3884163, by rfl⟩ : syracuseStep 10357769 = 7768327) B7768327
theorem B31067155 : Blo 1435537 31067155 := bstep (se 1 (by rfl) ⟨23300366, by rfl⟩ : syracuseStep 31067155 = 46600733) B46600733
theorem B1436699 : Blo 1435537 1436699 := bstep (se 1 (by rfl) ⟨1077524, by rfl⟩ : syracuseStep 1436699 = 2155049) B2155049
theorem B1436903 : Blo 1435537 1436903 := bstep (se 1 (by rfl) ⟨1077677, by rfl⟩ : syracuseStep 1436903 = 2155355) B2155355
theorem B13987127 : Blo 1435537 13987127 := bstep (se 1 (by rfl) ⟨10490345, by rfl⟩ : syracuseStep 13987127 = 20980691) B20980691
theorem B2878841 : Blo 1435537 2878841 := bstep (se 2 (by rfl) ⟨1079565, by rfl⟩ : syracuseStep 2878841 = 2159131) B2159131
theorem B3231323 : Blo 1435537 3231323 := bstep (se 1 (by rfl) ⟨2423492, by rfl⟩ : syracuseStep 3231323 = 4846985) B4846985
theorem B1437343 : Blo 1435537 1437343 := bstep (se 1 (by rfl) ⟨1078007, by rfl⟩ : syracuseStep 1437343 = 2156015) B2156015
theorem B1437351 : Blo 1435537 1437351 := bstep (se 1 (by rfl) ⟨1078013, by rfl⟩ : syracuseStep 1437351 = 2156027) B2156027
theorem B1437423 : Blo 1435537 1437423 := bstep (se 1 (by rfl) ⟨1078067, by rfl⟩ : syracuseStep 1437423 = 2156135) B2156135
theorem B1437471 : Blo 1435537 1437471 := bstep (se 1 (by rfl) ⟨1078103, by rfl⟩ : syracuseStep 1437471 = 2156207) B2156207
theorem B31477733 : Blo 1435537 31477733 := bstep (se 4 (by rfl) ⟨2951037, by rfl⟩ : syracuseStep 31477733 = 5902075) B5902075
theorem B3231737 : Blo 1435537 3231737 := bstep (se 2 (by rfl) ⟨1211901, by rfl⟩ : syracuseStep 3231737 = 2423803) B2423803
theorem B3231791 : Blo 1435537 3231791 := bstep (se 1 (by rfl) ⟨2423843, by rfl⟩ : syracuseStep 3231791 = 4847687) B4847687
theorem B7770167 : Blo 1435537 7770167 := bstep (se 1 (by rfl) ⟨5827625, by rfl⟩ : syracuseStep 7770167 = 11655251) B11655251
theorem B4599929 : Blo 1435537 4599929 := bstep (se 2 (by rfl) ⟨1724973, by rfl⟩ : syracuseStep 4599929 = 3449947) B3449947
theorem B2912417 : Blo 1435537 2912417 := bstep (se 2 (by rfl) ⟨1092156, by rfl⟩ : syracuseStep 2912417 = 2184313) B2184313
theorem B10908269 : Blo 1435537 10908269 := bstep (se 3 (by rfl) ⟨2045300, by rfl⟩ : syracuseStep 10908269 = 4090601) B4090601
theorem B3232475 : Blo 1435537 3232475 := bstep (se 1 (by rfl) ⟨2424356, by rfl⟩ : syracuseStep 3232475 = 4848713) B4848713
theorem B10351567 : Blo 1435537 10351567 := bstep (se 1 (by rfl) ⟨7763675, by rfl⟩ : syracuseStep 10351567 = 15527351) B15527351
theorem B13808627 : Blo 1435537 13808627 := bstep (se 1 (by rfl) ⟨10356470, by rfl⟩ : syracuseStep 13808627 = 20712941) B20712941
theorem B10908755 : Blo 1435537 10908755 := bstep (se 1 (by rfl) ⟨8181566, by rfl⟩ : syracuseStep 10908755 = 16363133) B16363133
theorem B251933789 : Blo 1435537 251933789 := bstep (se 3 (by rfl) ⟨47237585, by rfl⟩ : syracuseStep 251933789 = 94475171) B94475171
theorem B59774273 : Blo 1435537 59774273 := bstep (se 2 (by rfl) ⟨22415352, by rfl⟩ : syracuseStep 59774273 = 44830705) B44830705
theorem B3634895 : Blo 1435537 3634895 := bstep (se 1 (by rfl) ⟨2726171, by rfl⟩ : syracuseStep 3634895 = 5452343) B5452343
theorem B3635027 : Blo 1435537 3635027 := bstep (se 1 (by rfl) ⟨2726270, by rfl⟩ : syracuseStep 3635027 = 5452541) B5452541
theorem B3233735 : Blo 1435537 3233735 := bstep (se 1 (by rfl) ⟨2425301, by rfl⟩ : syracuseStep 3233735 = 4850603) B4850603
theorem B10352951 : Blo 1435537 10352951 := bstep (se 1 (by rfl) ⟨7764713, by rfl⟩ : syracuseStep 10352951 = 15529427) B15529427
theorem B15751655 : Blo 1435537 15751655 := bstep (se 1 (by rfl) ⟨11813741, by rfl⟩ : syracuseStep 15751655 = 23627483) B23627483
theorem B2726399 : Blo 1435537 2726399 := bstep (se 1 (by rfl) ⟨2044799, by rfl⟩ : syracuseStep 2726399 = 4089599) B4089599
theorem B1817407 : Blo 1435537 1817407 := bstep (se 1 (by rfl) ⟨1363055, by rfl⟩ : syracuseStep 1817407 = 2726111) B2726111
theorem B2423675 : Blo 1435537 2423675 := bstep (se 1 (by rfl) ⟨1817756, by rfl⟩ : syracuseStep 2423675 = 3635513) B3635513
theorem B9206723 : Blo 1435537 9206723 := bstep (se 1 (by rfl) ⟨6905042, by rfl⟩ : syracuseStep 9206723 = 13810085) B13810085
theorem B27630557 : Blo 1435537 27630557 := bstep (se 3 (by rfl) ⟨5180729, by rfl⟩ : syracuseStep 27630557 = 10361459) B10361459
theorem B3636191 : Blo 1435537 3636191 := bstep (se 1 (by rfl) ⟨2727143, by rfl⟩ : syracuseStep 3636191 = 5454287) B5454287
theorem B7273799 : Blo 1435537 7273799 := bstep (se 1 (by rfl) ⟨5455349, by rfl⟩ : syracuseStep 7273799 = 10910699) B10910699
theorem B6135425 : Blo 1435537 6135425 := bstep (se 2 (by rfl) ⟨2300784, by rfl⟩ : syracuseStep 6135425 = 4601569) B4601569
theorem B4849307 : Blo 1435537 4849307 := bstep (se 1 (by rfl) ⟨3636980, by rfl⟩ : syracuseStep 4849307 = 7273961) B7273961
theorem B7978727 : Blo 1435537 7978727 := bstep (se 1 (by rfl) ⟨5984045, by rfl⟩ : syracuseStep 7978727 = 11968091) B11968091
theorem B11976457 : Blo 1435537 11976457 := bstep (se 2 (by rfl) ⟨4491171, by rfl⟩ : syracuseStep 11976457 = 8982343) B8982343
theorem B3882791 : Blo 1435537 3882791 := bstep (se 1 (by rfl) ⟨2912093, by rfl⟩ : syracuseStep 3882791 = 5824187) B5824187
theorem B3637183 : Blo 1435537 3637183 := bstep (se 1 (by rfl) ⟨2727887, by rfl⟩ : syracuseStep 3637183 = 5455775) B5455775
theorem B2424809 : Blo 1435537 2424809 := bstep (se 2 (by rfl) ⟨909303, by rfl⟩ : syracuseStep 2424809 = 1818607) B1818607
theorem B2154527 : Blo 1435537 2154527 := bstep (se 1 (by rfl) ⟨1615895, by rfl⟩ : syracuseStep 2154527 = 3231791) B3231791
theorem B1941611 : Blo 1435537 1941611 := bstep (se 1 (by rfl) ⟨1456208, by rfl⟩ : syracuseStep 1941611 = 2912417) B2912417
theorem B2154983 : Blo 1435537 2154983 := bstep (se 1 (by rfl) ⟨1616237, by rfl⟩ : syracuseStep 2154983 = 3232475) B3232475
theorem B2425511 : Blo 1435537 2425511 := bstep (se 1 (by rfl) ⟨1819133, by rfl⟩ : syracuseStep 2425511 = 3638267) B3638267
theorem B287081171 : Blo 1435537 287081171 := bstep (se 1 (by rfl) ⟨215310878, by rfl⟩ : syracuseStep 287081171 = 430621757) B430621757
theorem B2589479 : Blo 1435537 2589479 := bstep (se 1 (by rfl) ⟨1942109, by rfl⟩ : syracuseStep 2589479 = 3884219) B3884219
theorem B37299005 : Blo 1435537 37299005 := bstep (se 3 (by rfl) ⟨6993563, by rfl⟩ : syracuseStep 37299005 = 13987127) B13987127
theorem B9200573 : Blo 1435537 9200573 := bstep (se 3 (by rfl) ⟨1725107, by rfl⟩ : syracuseStep 9200573 = 3450215) B3450215
theorem B2155823 : Blo 1435537 2155823 := bstep (se 1 (by rfl) ⟨1616867, by rfl⟩ : syracuseStep 2155823 = 3233735) B3233735
theorem B1615783 : Blo 1435537 1615783 := bstep (se 1 (by rfl) ⟨1211837, by rfl⟩ : syracuseStep 1615783 = 2423675) B2423675
theorem B21276605 : Blo 1435537 21276605 := bstep (se 3 (by rfl) ⟨3989363, by rfl⟩ : syracuseStep 21276605 = 7978727) B7978727
theorem B1919227 : Blo 1435537 1919227 := bstep (se 1 (by rfl) ⟨1439420, by rfl⟩ : syracuseStep 1919227 = 2878841) B2878841
theorem B15968609 : Blo 1435537 15968609 := bstep (se 2 (by rfl) ⟨5988228, by rfl⟩ : syracuseStep 15968609 = 11976457) B11976457
theorem B4090283 : Blo 1435537 4090283 := bstep (se 1 (by rfl) ⟨3067712, by rfl⟩ : syracuseStep 4090283 = 6135425) B6135425
theorem B1616539 : Blo 1435537 1616539 := bstep (se 1 (by rfl) ⟨1212404, by rfl⟩ : syracuseStep 1616539 = 2424809) B2424809
theorem B5180111 : Blo 1435537 5180111 := bstep (se 1 (by rfl) ⟨3885083, by rfl⟩ : syracuseStep 5180111 = 7770167) B7770167
theorem B3066619 : Blo 1435537 3066619 := bstep (se 1 (by rfl) ⟨2299964, by rfl⟩ : syracuseStep 3066619 = 4599929) B4599929
theorem B1436839 : Blo 1435537 1436839 := bstep (se 1 (by rfl) ⟨1077629, by rfl⟩ : syracuseStep 1436839 = 2155259) B2155259
theorem B167955859 : Blo 1435537 167955859 := bstep (se 1 (by rfl) ⟨125966894, by rfl⟩ : syracuseStep 167955859 = 251933789) B251933789
theorem B1437183 : Blo 1435537 1437183 := bstep (se 1 (by rfl) ⟨1077887, by rfl⟩ : syracuseStep 1437183 = 2155775) B2155775
theorem B39849515 : Blo 1435537 39849515 := bstep (se 1 (by rfl) ⟨29887136, by rfl⟩ : syracuseStep 39849515 = 59774273) B59774273
theorem B4599467 : Blo 1435537 4599467 := bstep (se 1 (by rfl) ⟨3449600, by rfl⟩ : syracuseStep 4599467 = 6899201) B6899201
theorem B6139729 : Blo 1435537 6139729 := bstep (se 2 (by rfl) ⟨2302398, by rfl⟩ : syracuseStep 6139729 = 4604797) B4604797
theorem B1437531 : Blo 1435537 1437531 := bstep (se 1 (by rfl) ⟨1078148, by rfl⟩ : syracuseStep 1437531 = 2156297) B2156297
theorem B7270397 : Blo 1435537 7270397 := bstep (se 3 (by rfl) ⟨1363199, by rfl⟩ : syracuseStep 7270397 = 2726399) B2726399
theorem B41422873 : Blo 1435537 41422873 := bstep (se 2 (by rfl) ⟨15533577, by rfl⟩ : syracuseStep 41422873 = 31067155) B31067155
theorem B4092059 : Blo 1435537 4092059 := bstep (se 1 (by rfl) ⟨3069044, by rfl⟩ : syracuseStep 4092059 = 6138089) B6138089
theorem B2044111 : Blo 1435537 2044111 := bstep (se 1 (by rfl) ⟨1533083, by rfl⟩ : syracuseStep 2044111 = 3066167) B3066167
theorem B6901967 : Blo 1435537 6901967 := bstep (se 1 (by rfl) ⟨5176475, by rfl⟩ : syracuseStep 6901967 = 10352951) B10352951
theorem B18420371 : Blo 1435537 18420371 := bstep (se 1 (by rfl) ⟨13815278, by rfl⟩ : syracuseStep 18420371 = 27630557) B27630557
theorem B3232871 : Blo 1435537 3232871 := bstep (se 1 (by rfl) ⟨2424653, by rfl⟩ : syracuseStep 3232871 = 4849307) B4849307
theorem B20985155 : Blo 1435537 20985155 := bstep (se 1 (by rfl) ⟨15738866, by rfl⟩ : syracuseStep 20985155 = 31477733) B31477733
theorem B3069353 : Blo 1435537 3069353 := bstep (se 2 (by rfl) ⟨1151007, by rfl⟩ : syracuseStep 3069353 = 2302015) B2302015
theorem B12277271 : Blo 1435537 12277271 := bstep (se 1 (by rfl) ⟨9207953, by rfl⟩ : syracuseStep 12277271 = 18415907) B18415907
theorem B3233321 : Blo 1435537 3233321 := bstep (se 2 (by rfl) ⟨1212495, by rfl⟩ : syracuseStep 3233321 = 2424991) B2424991
theorem B41408111 : Blo 1435537 41408111 := bstep (se 1 (by rfl) ⟨31056083, by rfl⟩ : syracuseStep 41408111 = 62112167) B62112167
theorem B7272179 : Blo 1435537 7272179 := bstep (se 1 (by rfl) ⟨5454134, by rfl⟩ : syracuseStep 7272179 = 10908269) B10908269
theorem B44840729 : Blo 1435537 44840729 := bstep (se 2 (by rfl) ⟨16815273, by rfl⟩ : syracuseStep 44840729 = 33630547) B33630547
theorem B99571493 : Blo 1435537 99571493 := bstep (se 4 (by rfl) ⟨9334827, by rfl⟩ : syracuseStep 99571493 = 18669655) B18669655
theorem B23287655 : Blo 1435537 23287655 := bstep (se 1 (by rfl) ⟨17465741, by rfl⟩ : syracuseStep 23287655 = 34931483) B34931483
theorem B5453801 : Blo 1435537 5453801 := bstep (se 2 (by rfl) ⟨2045175, by rfl⟩ : syracuseStep 5453801 = 4090351) B4090351
theorem B9205751 : Blo 1435537 9205751 := bstep (se 1 (by rfl) ⟨6904313, by rfl⟩ : syracuseStep 9205751 = 13808627) B13808627
theorem B7272503 : Blo 1435537 7272503 := bstep (se 1 (by rfl) ⟨5454377, by rfl⟩ : syracuseStep 7272503 = 10908755) B10908755
theorem B13113463 : Blo 1435537 13113463 := bstep (se 1 (by rfl) ⟨9835097, by rfl⟩ : syracuseStep 13113463 = 19670195) B19670195
theorem B2423209 : Blo 1435537 2423209 := bstep (se 2 (by rfl) ⟨908703, by rfl⟩ : syracuseStep 2423209 = 1817407) B1817407
theorem B2423263 : Blo 1435537 2423263 := bstep (se 1 (by rfl) ⟨1817447, by rfl⟩ : syracuseStep 2423263 = 3634895) B3634895
theorem B2423351 : Blo 1435537 2423351 := bstep (se 1 (by rfl) ⟨1817513, by rfl⟩ : syracuseStep 2423351 = 3635027) B3635027
theorem B13802089 : Blo 1435537 13802089 := bstep (se 2 (by rfl) ⟨5175783, by rfl⟩ : syracuseStep 13802089 = 10351567) B10351567
theorem B10501103 : Blo 1435537 10501103 := bstep (se 1 (by rfl) ⟨7875827, by rfl⟩ : syracuseStep 10501103 = 15751655) B15751655
theorem B2153609 : Blo 1435537 2153609 := bstep (se 2 (by rfl) ⟨807603, by rfl⟩ : syracuseStep 2153609 = 1615207) B1615207
theorem B2153627 : Blo 1435537 2153627 := bstep (se 1 (by rfl) ⟨1615220, by rfl⟩ : syracuseStep 2153627 = 3230441) B3230441
theorem B2153663 : Blo 1435537 2153663 := bstep (se 1 (by rfl) ⟨1615247, by rfl⟩ : syracuseStep 2153663 = 3230495) B3230495
theorem B2153711 : Blo 1435537 2153711 := bstep (se 1 (by rfl) ⟨1615283, by rfl⟩ : syracuseStep 2153711 = 3230567) B3230567
theorem B2424127 : Blo 1435537 2424127 := bstep (se 1 (by rfl) ⟨1818095, by rfl⟩ : syracuseStep 2424127 = 3636191) B3636191
theorem B6905179 : Blo 1435537 6905179 := bstep (se 1 (by rfl) ⟨5178884, by rfl⟩ : syracuseStep 6905179 = 10357769) B10357769
theorem B4849199 : Blo 1435537 4849199 := bstep (se 1 (by rfl) ⟨3636899, by rfl⟩ : syracuseStep 4849199 = 7273799) B7273799
theorem B2154215 : Blo 1435537 2154215 := bstep (se 1 (by rfl) ⟨1615661, by rfl⟩ : syracuseStep 2154215 = 3231323) B3231323
theorem B24551261 : Blo 1435537 24551261 := bstep (se 3 (by rfl) ⟨4603361, by rfl⟩ : syracuseStep 24551261 = 9206723) B9206723
theorem B2588527 : Blo 1435537 2588527 := bstep (se 1 (by rfl) ⟨1941395, by rfl⟩ : syracuseStep 2588527 = 3882791) B3882791
theorem B4849577 : Blo 1435537 4849577 := bstep (se 2 (by rfl) ⟨1818591, by rfl⟩ : syracuseStep 4849577 = 3637183) B3637183
theorem B2154491 : Blo 1435537 2154491 := bstep (se 1 (by rfl) ⟨1615868, by rfl⟩ : syracuseStep 2154491 = 3231737) B3231737
theorem B55230497 : Blo 1435537 55230497 := bstep (se 2 (by rfl) ⟨20711436, by rfl⟩ : syracuseStep 55230497 = 41422873) B41422873
theorem B5177629 : Blo 1435537 5177629 := bstep (se 3 (by rfl) ⟨970805, by rfl⟩ : syracuseStep 5177629 = 1941611) B1941611
theorem B10912157 : Blo 1435537 10912157 := bstep (se 3 (by rfl) ⟨2046029, by rfl⟩ : syracuseStep 10912157 = 4092059) B4092059
theorem B12280247 : Blo 1435537 12280247 := bstep (se 1 (by rfl) ⟨9210185, by rfl⟩ : syracuseStep 12280247 = 18420371) B18420371
theorem B2155247 : Blo 1435537 2155247 := bstep (se 1 (by rfl) ⟨1616435, by rfl⟩ : syracuseStep 2155247 = 3232871) B3232871
theorem B2155385 : Blo 1435537 2155385 := bstep (se 2 (by rfl) ⟨808269, by rfl⟩ : syracuseStep 2155385 = 1616539) B1616539
theorem B4088825 : Blo 1435537 4088825 := bstep (se 2 (by rfl) ⟨1533309, by rfl⟩ : syracuseStep 4088825 = 3066619) B3066619
theorem B8184847 : Blo 1435537 8184847 := bstep (se 1 (by rfl) ⟨6138635, by rfl⟩ : syracuseStep 8184847 = 12277271) B12277271
theorem B2155547 : Blo 1435537 2155547 := bstep (se 1 (by rfl) ⟨1616660, by rfl⟩ : syracuseStep 2155547 = 3233321) B3233321
theorem B29893819 : Blo 1435537 29893819 := bstep (se 1 (by rfl) ⟨22420364, by rfl⟩ : syracuseStep 29893819 = 44840729) B44840729
theorem B66380995 : Blo 1435537 66380995 := bstep (se 1 (by rfl) ⟨49785746, by rfl⟩ : syracuseStep 66380995 = 99571493) B99571493
theorem B15525103 : Blo 1435537 15525103 := bstep (se 1 (by rfl) ⟨11643827, by rfl⟩ : syracuseStep 15525103 = 23287655) B23287655
theorem B6137167 : Blo 1435537 6137167 := bstep (se 1 (by rfl) ⟨4602875, by rfl⟩ : syracuseStep 6137167 = 9205751) B9205751
theorem B1615567 : Blo 1435537 1615567 := bstep (se 1 (by rfl) ⟨1211675, by rfl⟩ : syracuseStep 1615567 = 2423351) B2423351
theorem B1435739 : Blo 1435537 1435739 := bstep (se 1 (by rfl) ⟨1076804, by rfl⟩ : syracuseStep 1435739 = 2153609) B2153609
theorem B1435751 : Blo 1435537 1435751 := bstep (se 1 (by rfl) ⟨1076813, by rfl⟩ : syracuseStep 1435751 = 2153627) B2153627
theorem B1435775 : Blo 1435537 1435775 := bstep (se 1 (by rfl) ⟨1076831, by rfl⟩ : syracuseStep 1435775 = 2153663) B2153663
theorem B1435807 : Blo 1435537 1435807 := bstep (se 1 (by rfl) ⟨1076855, by rfl⟩ : syracuseStep 1435807 = 2153711) B2153711
theorem B8186305 : Blo 1435537 8186305 := bstep (se 2 (by rfl) ⟨3069864, by rfl⟩ : syracuseStep 8186305 = 6139729) B6139729
theorem B3066311 : Blo 1435537 3066311 := bstep (se 1 (by rfl) ⟨2299733, by rfl⟩ : syracuseStep 3066311 = 4599467) B4599467
theorem B3451369 : Blo 1435537 3451369 := bstep (se 2 (by rfl) ⟨1294263, by rfl⟩ : syracuseStep 3451369 = 2588527) B2588527
theorem B1436143 : Blo 1435537 1436143 := bstep (se 1 (by rfl) ⟨1077107, by rfl⟩ : syracuseStep 1436143 = 2154215) B2154215
theorem B28002941 : Blo 1435537 28002941 := bstep (se 3 (by rfl) ⟨5250551, by rfl⟩ : syracuseStep 28002941 = 10501103) B10501103
theorem B1436327 : Blo 1435537 1436327 := bstep (se 1 (by rfl) ⟨1077245, by rfl⟩ : syracuseStep 1436327 = 2154491) B2154491
theorem B1436351 : Blo 1435537 1436351 := bstep (se 1 (by rfl) ⟨1077263, by rfl⟩ : syracuseStep 1436351 = 2154527) B2154527
theorem B17484617 : Blo 1435537 17484617 := bstep (se 2 (by rfl) ⟨6556731, by rfl⟩ : syracuseStep 17484617 = 13113463) B13113463
theorem B1436655 : Blo 1435537 1436655 := bstep (se 1 (by rfl) ⟨1077491, by rfl⟩ : syracuseStep 1436655 = 2154983) B2154983
theorem B2558969 : Blo 1435537 2558969 := bstep (se 2 (by rfl) ⟨959613, by rfl⟩ : syracuseStep 2558969 = 1919227) B1919227
theorem B1617007 : Blo 1435537 1617007 := bstep (se 1 (by rfl) ⟨1212755, by rfl⟩ : syracuseStep 1617007 = 2425511) B2425511
theorem B24866003 : Blo 1435537 24866003 := bstep (se 1 (by rfl) ⟨18649502, by rfl⟩ : syracuseStep 24866003 = 37299005) B37299005
theorem B3230945 : Blo 1435537 3230945 := bstep (se 2 (by rfl) ⟨1211604, by rfl⟩ : syracuseStep 3230945 = 2423209) B2423209
theorem B3231017 : Blo 1435537 3231017 := bstep (se 2 (by rfl) ⟨1211631, by rfl⟩ : syracuseStep 3231017 = 2423263) B2423263
theorem B18402785 : Blo 1435537 18402785 := bstep (se 2 (by rfl) ⟨6901044, by rfl⟩ : syracuseStep 18402785 = 13802089) B13802089
theorem B1437215 : Blo 1435537 1437215 := bstep (se 1 (by rfl) ⟨1077911, by rfl⟩ : syracuseStep 1437215 = 2155823) B2155823
theorem B10645739 : Blo 1435537 10645739 := bstep (se 1 (by rfl) ⟨7984304, by rfl⟩ : syracuseStep 10645739 = 15968609) B15968609
theorem B3232169 : Blo 1435537 3232169 := bstep (se 2 (by rfl) ⟨1212063, by rfl⟩ : syracuseStep 3232169 = 2424127) B2424127
theorem B3453407 : Blo 1435537 3453407 := bstep (se 1 (by rfl) ⟨2590055, by rfl⟩ : syracuseStep 3453407 = 5180111) B5180111
theorem B223941145 : Blo 1435537 223941145 := bstep (se 2 (by rfl) ⟨83977929, by rfl⟩ : syracuseStep 223941145 = 167955859) B167955859
theorem B3232799 : Blo 1435537 3232799 := bstep (se 1 (by rfl) ⟨2424599, by rfl⟩ : syracuseStep 3232799 = 4849199) B4849199
theorem B3233051 : Blo 1435537 3233051 := bstep (se 1 (by rfl) ⟨2424788, by rfl⟩ : syracuseStep 3233051 = 4849577) B4849577
theorem B4846931 : Blo 1435537 4846931 := bstep (se 1 (by rfl) ⟨3635198, by rfl⟩ : syracuseStep 4846931 = 7270397) B7270397
theorem B2725481 : Blo 1435537 2725481 := bstep (se 2 (by rfl) ⟨1022055, by rfl⟩ : syracuseStep 2725481 = 2044111) B2044111
theorem B191387447 : Blo 1435537 191387447 := bstep (se 1 (by rfl) ⟨143540585, by rfl⟩ : syracuseStep 191387447 = 287081171) B287081171
theorem B1726319 : Blo 1435537 1726319 := bstep (se 1 (by rfl) ⟨1294739, by rfl⟩ : syracuseStep 1726319 = 2589479) B2589479
theorem B18405245 : Blo 1435537 18405245 := bstep (se 3 (by rfl) ⟨3450983, by rfl⟩ : syracuseStep 18405245 = 6901967) B6901967
theorem B6133715 : Blo 1435537 6133715 := bstep (se 1 (by rfl) ⟨4600286, by rfl⟩ : syracuseStep 6133715 = 9200573) B9200573
theorem B13990103 : Blo 1435537 13990103 := bstep (se 1 (by rfl) ⟨10492577, by rfl⟩ : syracuseStep 13990103 = 20985155) B20985155
theorem B2046235 : Blo 1435537 2046235 := bstep (se 1 (by rfl) ⟨1534676, by rfl⟩ : syracuseStep 2046235 = 3069353) B3069353
theorem B27605407 : Blo 1435537 27605407 := bstep (se 1 (by rfl) ⟨20704055, by rfl⟩ : syracuseStep 27605407 = 41408111) B41408111
theorem B4848119 : Blo 1435537 4848119 := bstep (se 1 (by rfl) ⟨3636089, by rfl⟩ : syracuseStep 4848119 = 7272179) B7272179
theorem B3635867 : Blo 1435537 3635867 := bstep (se 1 (by rfl) ⟨2726900, by rfl⟩ : syracuseStep 3635867 = 5453801) B5453801
theorem B4848335 : Blo 1435537 4848335 := bstep (se 1 (by rfl) ⟨3636251, by rfl⟩ : syracuseStep 4848335 = 7272503) B7272503
theorem B2726855 : Blo 1435537 2726855 := bstep (se 1 (by rfl) ⟨2045141, by rfl⟩ : syracuseStep 2726855 = 4090283) B4090283
theorem B9206905 : Blo 1435537 9206905 := bstep (se 2 (by rfl) ⟨3452589, by rfl⟩ : syracuseStep 9206905 = 6905179) B6905179
theorem B26566343 : Blo 1435537 26566343 := bstep (se 1 (by rfl) ⟨19924757, by rfl⟩ : syracuseStep 26566343 = 39849515) B39849515
theorem B56737613 : Blo 1435537 56737613 := bstep (se 3 (by rfl) ⟨10638302, by rfl⟩ : syracuseStep 56737613 = 21276605) B21276605
theorem B2154377 : Blo 1435537 2154377 := bstep (se 2 (by rfl) ⟨807891, by rfl⟩ : syracuseStep 2154377 = 1615783) B1615783
theorem B16367507 : Blo 1435537 16367507 := bstep (se 1 (by rfl) ⟨12275630, by rfl⟩ : syracuseStep 16367507 = 24551261) B24551261
theorem B7274771 : Blo 1435537 7274771 := bstep (se 1 (by rfl) ⟨5456078, by rfl⟩ : syracuseStep 7274771 = 10912157) B10912157
theorem B2154779 : Blo 1435537 2154779 := bstep (se 1 (by rfl) ⟨1616084, by rfl⟩ : syracuseStep 2154779 = 3232169) B3232169
theorem B2302271 : Blo 1435537 2302271 := bstep (se 1 (by rfl) ⟨1726703, by rfl⟩ : syracuseStep 2302271 = 3453407) B3453407
theorem B2728313 : Blo 1435537 2728313 := bstep (se 2 (by rfl) ⟨1023117, by rfl⟩ : syracuseStep 2728313 = 2046235) B2046235
theorem B36807209 : Blo 1435537 36807209 := bstep (se 2 (by rfl) ⟨13802703, by rfl⟩ : syracuseStep 36807209 = 27605407) B27605407
theorem B2155199 : Blo 1435537 2155199 := bstep (se 1 (by rfl) ⟨1616399, by rfl⟩ : syracuseStep 2155199 = 3232799) B3232799
theorem B2155367 : Blo 1435537 2155367 := bstep (se 1 (by rfl) ⟨1616525, by rfl⟩ : syracuseStep 2155367 = 3233051) B3233051
theorem B127591631 : Blo 1435537 127591631 := bstep (se 1 (by rfl) ⟨95693723, by rfl⟩ : syracuseStep 127591631 = 191387447) B191387447
theorem B4089143 : Blo 1435537 4089143 := bstep (se 1 (by rfl) ⟨3066857, by rfl⟩ : syracuseStep 4089143 = 6133715) B6133715
theorem B10913129 : Blo 1435537 10913129 := bstep (se 2 (by rfl) ⟨4092423, by rfl⟩ : syracuseStep 10913129 = 8184847) B8184847
theorem B2156009 : Blo 1435537 2156009 := bstep (se 2 (by rfl) ⟨808503, by rfl⟩ : syracuseStep 2156009 = 1617007) B1617007
theorem B88507993 : Blo 1435537 88507993 := bstep (se 2 (by rfl) ⟨33190497, by rfl⟩ : syracuseStep 88507993 = 66380995) B66380995
theorem B1705979 : Blo 1435537 1705979 := bstep (se 1 (by rfl) ⟨1279484, by rfl⟩ : syracuseStep 1705979 = 2558969) B2558969
theorem B37825075 : Blo 1435537 37825075 := bstep (se 1 (by rfl) ⟨28368806, by rfl⟩ : syracuseStep 37825075 = 56737613) B56737613
theorem B1436251 : Blo 1435537 1436251 := bstep (se 1 (by rfl) ⟨1077188, by rfl⟩ : syracuseStep 1436251 = 2154377) B2154377
theorem B7097159 : Blo 1435537 7097159 := bstep (se 1 (by rfl) ⟨5322869, by rfl⟩ : syracuseStep 7097159 = 10645739) B10645739
theorem B8186831 : Blo 1435537 8186831 := bstep (se 1 (by rfl) ⟨6140123, by rfl⟩ : syracuseStep 8186831 = 12280247) B12280247
theorem B1436831 : Blo 1435537 1436831 := bstep (se 1 (by rfl) ⟨1077623, by rfl⟩ : syracuseStep 1436831 = 2155247) B2155247
theorem B1436923 : Blo 1435537 1436923 := bstep (se 1 (by rfl) ⟨1077692, by rfl⟩ : syracuseStep 1436923 = 2155385) B2155385
theorem B10915073 : Blo 1435537 10915073 := bstep (se 2 (by rfl) ⟨4093152, by rfl⟩ : syracuseStep 10915073 = 8186305) B8186305
theorem B1437031 : Blo 1435537 1437031 := bstep (se 1 (by rfl) ⟨1077773, by rfl⟩ : syracuseStep 1437031 = 2155547) B2155547
theorem B3231287 : Blo 1435537 3231287 := bstep (se 1 (by rfl) ⟨2423465, by rfl⟩ : syracuseStep 3231287 = 4846931) B4846931
theorem B9326735 : Blo 1435537 9326735 := bstep (se 1 (by rfl) ⟨6995051, by rfl⟩ : syracuseStep 9326735 = 13990103) B13990103
theorem B12275873 : Blo 1435537 12275873 := bstep (se 2 (by rfl) ⟨4603452, by rfl⟩ : syracuseStep 12275873 = 9206905) B9206905
theorem B39858425 : Blo 1435537 39858425 := bstep (se 2 (by rfl) ⟨14946909, by rfl⟩ : syracuseStep 39858425 = 29893819) B29893819
theorem B2044207 : Blo 1435537 2044207 := bstep (se 1 (by rfl) ⟨1533155, by rfl⟩ : syracuseStep 2044207 = 3066311) B3066311
theorem B3232079 : Blo 1435537 3232079 := bstep (se 1 (by rfl) ⟨2424059, by rfl⟩ : syracuseStep 3232079 = 4848119) B4848119
theorem B3232223 : Blo 1435537 3232223 := bstep (se 1 (by rfl) ⟨2424167, by rfl⟩ : syracuseStep 3232223 = 4848335) B4848335
theorem B16577335 : Blo 1435537 16577335 := bstep (se 1 (by rfl) ⟨12433001, by rfl⟩ : syracuseStep 16577335 = 24866003) B24866003
theorem B46625645 : Blo 1435537 46625645 := bstep (se 3 (by rfl) ⟨8742308, by rfl⟩ : syracuseStep 46625645 = 17484617) B17484617
theorem B12268523 : Blo 1435537 12268523 := bstep (se 1 (by rfl) ⟨9201392, by rfl⟩ : syracuseStep 12268523 = 18402785) B18402785
theorem B36820331 : Blo 1435537 36820331 := bstep (se 1 (by rfl) ⟨27615248, by rfl⟩ : syracuseStep 36820331 = 55230497) B55230497
theorem B6903505 : Blo 1435537 6903505 := bstep (se 2 (by rfl) ⟨2588814, by rfl⟩ : syracuseStep 6903505 = 5177629) B5177629
theorem B4601825 : Blo 1435537 4601825 := bstep (se 2 (by rfl) ⟨1725684, by rfl⟩ : syracuseStep 4601825 = 3451369) B3451369
theorem B2725883 : Blo 1435537 2725883 := bstep (se 1 (by rfl) ⟨2044412, by rfl⟩ : syracuseStep 2725883 = 4088825) B4088825
theorem B298588193 : Blo 1435537 298588193 := bstep (se 2 (by rfl) ⟨111970572, by rfl⟩ : syracuseStep 298588193 = 223941145) B223941145
theorem B1816987 : Blo 1435537 1816987 := bstep (se 1 (by rfl) ⟨1362740, by rfl⟩ : syracuseStep 1816987 = 2725481) B2725481
theorem B12270163 : Blo 1435537 12270163 := bstep (se 1 (by rfl) ⟨9202622, by rfl⟩ : syracuseStep 12270163 = 18405245) B18405245
theorem B20700137 : Blo 1435537 20700137 := bstep (se 2 (by rfl) ⟨7762551, by rfl⟩ : syracuseStep 20700137 = 15525103) B15525103
theorem B18668627 : Blo 1435537 18668627 := bstep (se 1 (by rfl) ⟨14001470, by rfl⟩ : syracuseStep 18668627 = 28002941) B28002941
theorem B2423911 : Blo 1435537 2423911 := bstep (se 1 (by rfl) ⟨1817933, by rfl⟩ : syracuseStep 2423911 = 3635867) B3635867
theorem B8182889 : Blo 1435537 8182889 := bstep (se 2 (by rfl) ⟨3068583, by rfl⟩ : syracuseStep 8182889 = 6137167) B6137167
theorem B1817903 : Blo 1435537 1817903 := bstep (se 1 (by rfl) ⟨1363427, by rfl⟩ : syracuseStep 1817903 = 2726855) B2726855
theorem B2153963 : Blo 1435537 2153963 := bstep (se 1 (by rfl) ⟨1615472, by rfl⟩ : syracuseStep 2153963 = 3230945) B3230945
theorem B2154011 : Blo 1435537 2154011 := bstep (se 1 (by rfl) ⟨1615508, by rfl⟩ : syracuseStep 2154011 = 3231017) B3231017
theorem B2154089 : Blo 1435537 2154089 := bstep (se 2 (by rfl) ⟨807783, by rfl⟩ : syracuseStep 2154089 = 1615567) B1615567
theorem B4603517 : Blo 1435537 4603517 := bstep (se 3 (by rfl) ⟨863159, by rfl⟩ : syracuseStep 4603517 = 1726319) B1726319
theorem B17710895 : Blo 1435537 17710895 := bstep (se 1 (by rfl) ⟨13283171, by rfl⟩ : syracuseStep 17710895 = 26566343) B26566343
theorem B10911671 : Blo 1435537 10911671 := bstep (se 1 (by rfl) ⟨8183753, by rfl⟩ : syracuseStep 10911671 = 16367507) B16367507
theorem B6217823 : Blo 1435537 6217823 := bstep (se 1 (by rfl) ⟨4663367, by rfl⟩ : syracuseStep 6217823 = 9326735) B9326735
theorem B8183915 : Blo 1435537 8183915 := bstep (se 1 (by rfl) ⟨6137936, by rfl⟩ : syracuseStep 8183915 = 12275873) B12275873
theorem B4849847 : Blo 1435537 4849847 := bstep (se 1 (by rfl) ⟨3637385, by rfl⟩ : syracuseStep 4849847 = 7274771) B7274771
theorem B2154719 : Blo 1435537 2154719 := bstep (se 1 (by rfl) ⟨1616039, by rfl⟩ : syracuseStep 2154719 = 3232079) B3232079
theorem B1818875 : Blo 1435537 1818875 := bstep (se 1 (by rfl) ⟨1364156, by rfl⟩ : syracuseStep 1818875 = 2728313) B2728313
theorem B2154815 : Blo 1435537 2154815 := bstep (se 1 (by rfl) ⟨1616111, by rfl⟩ : syracuseStep 2154815 = 3232223) B3232223
theorem B16360217 : Blo 1435537 16360217 := bstep (se 2 (by rfl) ⟨6135081, by rfl⟩ : syracuseStep 16360217 = 12270163) B12270163
theorem B10904381 : Blo 1435537 10904381 := bstep (se 3 (by rfl) ⟨2044571, by rfl⟩ : syracuseStep 10904381 = 4089143) B4089143
theorem B7275419 : Blo 1435537 7275419 := bstep (se 1 (by rfl) ⟨5456564, by rfl⟩ : syracuseStep 7275419 = 10913129) B10913129
theorem B22103113 : Blo 1435537 22103113 := bstep (se 2 (by rfl) ⟨8288667, by rfl⟩ : syracuseStep 22103113 = 16577335) B16577335
theorem B199058795 : Blo 1435537 199058795 := bstep (se 1 (by rfl) ⟨149294096, by rfl⟩ : syracuseStep 199058795 = 298588193) B298588193
theorem B5457887 : Blo 1435537 5457887 := bstep (se 1 (by rfl) ⟨4093415, by rfl⟩ : syracuseStep 5457887 = 8186831) B8186831
theorem B12445751 : Blo 1435537 12445751 := bstep (se 1 (by rfl) ⟨9334313, by rfl⟩ : syracuseStep 12445751 = 18668627) B18668627
theorem B7276715 : Blo 1435537 7276715 := bstep (se 1 (by rfl) ⟨5457536, by rfl⟩ : syracuseStep 7276715 = 10915073) B10915073
theorem B1435975 : Blo 1435537 1435975 := bstep (se 1 (by rfl) ⟨1076981, by rfl⟩ : syracuseStep 1435975 = 2153963) B2153963
theorem B1436007 : Blo 1435537 1436007 := bstep (se 1 (by rfl) ⟨1077005, by rfl⟩ : syracuseStep 1436007 = 2154011) B2154011
theorem B1436059 : Blo 1435537 1436059 := bstep (se 1 (by rfl) ⟨1077044, by rfl⟩ : syracuseStep 1436059 = 2154089) B2154089
theorem B11807263 : Blo 1435537 11807263 := bstep (se 1 (by rfl) ⟨8855447, by rfl⟩ : syracuseStep 11807263 = 17710895) B17710895
theorem B4549277 : Blo 1435537 4549277 := bstep (se 3 (by rfl) ⟨852989, by rfl⟩ : syracuseStep 4549277 = 1705979) B1705979
theorem B1436519 : Blo 1435537 1436519 := bstep (se 1 (by rfl) ⟨1077389, by rfl⟩ : syracuseStep 1436519 = 2154779) B2154779
theorem B1534847 : Blo 1435537 1534847 := bstep (se 1 (by rfl) ⟨1151135, by rfl⟩ : syracuseStep 1534847 = 2302271) B2302271
theorem B24538139 : Blo 1435537 24538139 := bstep (se 1 (by rfl) ⟨18403604, by rfl⟩ : syracuseStep 24538139 = 36807209) B36807209
theorem B1436799 : Blo 1435537 1436799 := bstep (se 1 (by rfl) ⟨1077599, by rfl⟩ : syracuseStep 1436799 = 2155199) B2155199
theorem B1436911 : Blo 1435537 1436911 := bstep (se 1 (by rfl) ⟨1077683, by rfl⟩ : syracuseStep 1436911 = 2155367) B2155367
theorem B31083763 : Blo 1435537 31083763 := bstep (se 1 (by rfl) ⟨23312822, by rfl⟩ : syracuseStep 31083763 = 46625645) B46625645
theorem B8179015 : Blo 1435537 8179015 := bstep (se 1 (by rfl) ⟨6134261, by rfl⟩ : syracuseStep 8179015 = 12268523) B12268523
theorem B85061087 : Blo 1435537 85061087 := bstep (se 1 (by rfl) ⟨63795815, by rfl⟩ : syracuseStep 85061087 = 127591631) B127591631
theorem B24546887 : Blo 1435537 24546887 := bstep (se 1 (by rfl) ⟨18410165, by rfl⟩ : syracuseStep 24546887 = 36820331) B36820331
theorem B1437339 : Blo 1435537 1437339 := bstep (se 1 (by rfl) ⟨1078004, by rfl⟩ : syracuseStep 1437339 = 2156009) B2156009
theorem B3067883 : Blo 1435537 3067883 := bstep (se 1 (by rfl) ⟨2300912, by rfl⟩ : syracuseStep 3067883 = 4601825) B4601825
theorem B3231881 : Blo 1435537 3231881 := bstep (se 2 (by rfl) ⟨1211955, by rfl⟩ : syracuseStep 3231881 = 2423911) B2423911
theorem B4731439 : Blo 1435537 4731439 := bstep (se 1 (by rfl) ⟨3548579, by rfl⟩ : syracuseStep 4731439 = 7097159) B7097159
theorem B13800091 : Blo 1435537 13800091 := bstep (se 1 (by rfl) ⟨10350068, by rfl⟩ : syracuseStep 13800091 = 20700137) B20700137
theorem B118010657 : Blo 1435537 118010657 := bstep (se 2 (by rfl) ⟨44253996, by rfl⟩ : syracuseStep 118010657 = 88507993) B88507993
theorem B9204673 : Blo 1435537 9204673 := bstep (se 2 (by rfl) ⟨3451752, by rfl⟩ : syracuseStep 9204673 = 6903505) B6903505
theorem B3069011 : Blo 1435537 3069011 := bstep (se 1 (by rfl) ⟨2301758, by rfl⟩ : syracuseStep 3069011 = 4603517) B4603517
theorem B26572283 : Blo 1435537 26572283 := bstep (se 1 (by rfl) ⟨19929212, by rfl⟩ : syracuseStep 26572283 = 39858425) B39858425
theorem B201733733 : Blo 1435537 201733733 := bstep (se 4 (by rfl) ⟨18912537, by rfl⟩ : syracuseStep 201733733 = 37825075) B37825075
theorem B2422649 : Blo 1435537 2422649 := bstep (se 2 (by rfl) ⟨908493, by rfl⟩ : syracuseStep 2422649 = 1816987) B1816987
theorem B4847741 : Blo 1435537 4847741 := bstep (se 3 (by rfl) ⟨908951, by rfl⟩ : syracuseStep 4847741 = 1817903) B1817903
theorem B1817255 : Blo 1435537 1817255 := bstep (se 1 (by rfl) ⟨1362941, by rfl⟩ : syracuseStep 1817255 = 2725883) B2725883
theorem B10902437 : Blo 1435537 10902437 := bstep (se 4 (by rfl) ⟨1022103, by rfl⟩ : syracuseStep 10902437 = 2044207) B2044207
theorem B5455259 : Blo 1435537 5455259 := bstep (se 1 (by rfl) ⟨4091444, by rfl⟩ : syracuseStep 5455259 = 8182889) B8182889
theorem B2154191 : Blo 1435537 2154191 := bstep (se 1 (by rfl) ⟨1615643, by rfl⟩ : syracuseStep 2154191 = 3231287) B3231287
theorem B7274447 : Blo 1435537 7274447 := bstep (se 1 (by rfl) ⟨5455835, by rfl⟩ : syracuseStep 7274447 = 10911671) B10911671
theorem B4145215 : Blo 1435537 4145215 := bstep (se 1 (by rfl) ⟨3108911, by rfl⟩ : syracuseStep 4145215 = 6217823) B6217823
theorem B5455943 : Blo 1435537 5455943 := bstep (se 1 (by rfl) ⟨4091957, by rfl⟩ : syracuseStep 5455943 = 8183915) B8183915
theorem B2154587 : Blo 1435537 2154587 := bstep (se 1 (by rfl) ⟨1615940, by rfl⟩ : syracuseStep 2154587 = 3231881) B3231881
theorem B4850279 : Blo 1435537 4850279 := bstep (se 1 (by rfl) ⟨3637709, by rfl⟩ : syracuseStep 4850279 = 7275419) B7275419
theorem B4850333 : Blo 1435537 4850333 := bstep (se 3 (by rfl) ⟨909437, by rfl⟩ : syracuseStep 4850333 = 1818875) B1818875
theorem B6308585 : Blo 1435537 6308585 := bstep (se 2 (by rfl) ⟨2365719, by rfl⟩ : syracuseStep 6308585 = 4731439) B4731439
theorem B18400121 : Blo 1435537 18400121 := bstep (se 2 (by rfl) ⟨6900045, by rfl⟩ : syracuseStep 18400121 = 13800091) B13800091
theorem B134489155 : Blo 1435537 134489155 := bstep (se 1 (by rfl) ⟨100866866, by rfl⟩ : syracuseStep 134489155 = 201733733) B201733733
theorem B1615099 : Blo 1435537 1615099 := bstep (se 1 (by rfl) ⟨1211324, by rfl⟩ : syracuseStep 1615099 = 2422649) B2422649
theorem B12272897 : Blo 1435537 12272897 := bstep (se 2 (by rfl) ⟨4602336, by rfl⟩ : syracuseStep 12272897 = 9204673) B9204673
theorem B3638591 : Blo 1435537 3638591 := bstep (se 1 (by rfl) ⟨2728943, by rfl⟩ : syracuseStep 3638591 = 5457887) B5457887
theorem B4851143 : Blo 1435537 4851143 := bstep (se 1 (by rfl) ⟨3638357, by rfl⟩ : syracuseStep 4851143 = 7276715) B7276715
theorem B41445017 : Blo 1435537 41445017 := bstep (se 2 (by rfl) ⟨15541881, by rfl⟩ : syracuseStep 41445017 = 31083763) B31083763
theorem B10905353 : Blo 1435537 10905353 := bstep (se 2 (by rfl) ⟨4089507, by rfl⟩ : syracuseStep 10905353 = 8179015) B8179015
theorem B7268291 : Blo 1435537 7268291 := bstep (se 1 (by rfl) ⟨5451218, by rfl⟩ : syracuseStep 7268291 = 10902437) B10902437
theorem B56707391 : Blo 1435537 56707391 := bstep (se 1 (by rfl) ⟨42530543, by rfl⟩ : syracuseStep 56707391 = 85061087) B85061087
theorem B1436127 : Blo 1435537 1436127 := bstep (se 1 (by rfl) ⟨1077095, by rfl⟩ : syracuseStep 1436127 = 2154191) B2154191
theorem B1436479 : Blo 1435537 1436479 := bstep (se 1 (by rfl) ⟨1077359, by rfl⟩ : syracuseStep 1436479 = 2154719) B2154719
theorem B1436543 : Blo 1435537 1436543 := bstep (se 1 (by rfl) ⟨1077407, by rfl⟩ : syracuseStep 1436543 = 2154815) B2154815
theorem B10906811 : Blo 1435537 10906811 := bstep (se 1 (by rfl) ⟨8180108, by rfl⟩ : syracuseStep 10906811 = 16360217) B16360217
theorem B7269587 : Blo 1435537 7269587 := bstep (se 1 (by rfl) ⟨5452190, by rfl⟩ : syracuseStep 7269587 = 10904381) B10904381
theorem B132705863 : Blo 1435537 132705863 := bstep (se 1 (by rfl) ⟨99529397, by rfl⟩ : syracuseStep 132705863 = 199058795) B199058795
theorem B17714855 : Blo 1435537 17714855 := bstep (se 1 (by rfl) ⟨13286141, by rfl⟩ : syracuseStep 17714855 = 26572283) B26572283
theorem B3231827 : Blo 1435537 3231827 := bstep (se 1 (by rfl) ⟨2423870, by rfl⟩ : syracuseStep 3231827 = 4847741) B4847741
theorem B29470817 : Blo 1435537 29470817 := bstep (se 2 (by rfl) ⟨11051556, by rfl⟩ : syracuseStep 29470817 = 22103113) B22103113
theorem B4846013 : Blo 1435537 4846013 := bstep (se 3 (by rfl) ⟨908627, by rfl⟩ : syracuseStep 4846013 = 1817255) B1817255
theorem B4092925 : Blo 1435537 4092925 := bstep (se 3 (by rfl) ⟨767423, by rfl⟩ : syracuseStep 4092925 = 1534847) B1534847
theorem B16364591 : Blo 1435537 16364591 := bstep (se 1 (by rfl) ⟨12273443, by rfl⟩ : syracuseStep 16364591 = 24546887) B24546887
theorem B2045255 : Blo 1435537 2045255 := bstep (se 1 (by rfl) ⟨1533941, by rfl⟩ : syracuseStep 2045255 = 3067883) B3067883
theorem B3233231 : Blo 1435537 3233231 := bstep (se 1 (by rfl) ⟨2424923, by rfl⟩ : syracuseStep 3233231 = 4849847) B4849847
theorem B78673771 : Blo 1435537 78673771 := bstep (se 1 (by rfl) ⟨59005328, by rfl⟩ : syracuseStep 78673771 = 118010657) B118010657
theorem B15743017 : Blo 1435537 15743017 := bstep (se 2 (by rfl) ⟨5903631, by rfl⟩ : syracuseStep 15743017 = 11807263) B11807263
theorem B2046007 : Blo 1435537 2046007 := bstep (se 1 (by rfl) ⟨1534505, by rfl⟩ : syracuseStep 2046007 = 3069011) B3069011
theorem B8297167 : Blo 1435537 8297167 := bstep (se 1 (by rfl) ⟨6222875, by rfl⟩ : syracuseStep 8297167 = 12445751) B12445751
theorem B12131405 : Blo 1435537 12131405 := bstep (se 3 (by rfl) ⟨2274638, by rfl⟩ : syracuseStep 12131405 = 4549277) B4549277
theorem B16358759 : Blo 1435537 16358759 := bstep (se 1 (by rfl) ⟨12269069, by rfl⟩ : syracuseStep 16358759 = 24538139) B24538139
theorem B3636839 : Blo 1435537 3636839 := bstep (se 1 (by rfl) ⟨2727629, by rfl⟩ : syracuseStep 3636839 = 5455259) B5455259
theorem B4849631 : Blo 1435537 4849631 := bstep (se 1 (by rfl) ⟨3637223, by rfl⟩ : syracuseStep 4849631 = 7274447) B7274447
theorem B3637295 : Blo 1435537 3637295 := bstep (se 1 (by rfl) ⟨2727971, by rfl⟩ : syracuseStep 3637295 = 5455943) B5455943
theorem B2154551 : Blo 1435537 2154551 := bstep (se 1 (by rfl) ⟨1615913, by rfl⟩ : syracuseStep 2154551 = 3231827) B3231827
theorem B2728009 : Blo 1435537 2728009 := bstep (se 2 (by rfl) ⟨1023003, by rfl⟩ : syracuseStep 2728009 = 2046007) B2046007
theorem B2425727 : Blo 1435537 2425727 := bstep (se 1 (by rfl) ⟨1819295, by rfl⟩ : syracuseStep 2425727 = 3638591) B3638591
theorem B2155487 : Blo 1435537 2155487 := bstep (se 1 (by rfl) ⟨1616615, by rfl⟩ : syracuseStep 2155487 = 3233231) B3233231
theorem B5457233 : Blo 1435537 5457233 := bstep (se 2 (by rfl) ⟨2046462, by rfl⟩ : syracuseStep 5457233 = 4092925) B4092925
theorem B8087603 : Blo 1435537 8087603 := bstep (se 1 (by rfl) ⟨6065702, by rfl⟩ : syracuseStep 8087603 = 12131405) B12131405
theorem B10905839 : Blo 1435537 10905839 := bstep (se 1 (by rfl) ⟨8179379, by rfl⟩ : syracuseStep 10905839 = 16358759) B16358759
theorem B1436391 : Blo 1435537 1436391 := bstep (se 1 (by rfl) ⟨1077293, by rfl⟩ : syracuseStep 1436391 = 2154587) B2154587
theorem B19647211 : Blo 1435537 19647211 := bstep (se 1 (by rfl) ⟨14735408, by rfl⟩ : syracuseStep 19647211 = 29470817) B29470817
theorem B83962757 : Blo 1435537 83962757 := bstep (se 4 (by rfl) ⟨7871508, by rfl⟩ : syracuseStep 83962757 = 15743017) B15743017
theorem B3230675 : Blo 1435537 3230675 := bstep (se 1 (by rfl) ⟨2423006, by rfl⟩ : syracuseStep 3230675 = 4846013) B4846013
theorem B4205723 : Blo 1435537 4205723 := bstep (se 1 (by rfl) ⟨3154292, by rfl⟩ : syracuseStep 4205723 = 6308585) B6308585
theorem B12266747 : Blo 1435537 12266747 := bstep (se 1 (by rfl) ⟨9200060, by rfl⟩ : syracuseStep 12266747 = 18400121) B18400121
theorem B11062889 : Blo 1435537 11062889 := bstep (se 2 (by rfl) ⟨4148583, by rfl⟩ : syracuseStep 11062889 = 8297167) B8297167
theorem B7270235 : Blo 1435537 7270235 := bstep (se 1 (by rfl) ⟨5452676, by rfl⟩ : syracuseStep 7270235 = 10905353) B10905353
theorem B4845527 : Blo 1435537 4845527 := bstep (se 1 (by rfl) ⟨3634145, by rfl⟩ : syracuseStep 4845527 = 7268291) B7268291
theorem B179318873 : Blo 1435537 179318873 := bstep (se 2 (by rfl) ⟨67244577, by rfl⟩ : syracuseStep 179318873 = 134489155) B134489155
theorem B7271207 : Blo 1435537 7271207 := bstep (se 1 (by rfl) ⟨5453405, by rfl⟩ : syracuseStep 7271207 = 10906811) B10906811
theorem B4846391 : Blo 1435537 4846391 := bstep (se 1 (by rfl) ⟨3634793, by rfl⟩ : syracuseStep 4846391 = 7269587) B7269587
theorem B88470575 : Blo 1435537 88470575 := bstep (se 1 (by rfl) ⟨66352931, by rfl⟩ : syracuseStep 88470575 = 132705863) B132705863
theorem B11809903 : Blo 1435537 11809903 := bstep (se 1 (by rfl) ⟨8857427, by rfl⟩ : syracuseStep 11809903 = 17714855) B17714855
theorem B3233087 : Blo 1435537 3233087 := bstep (se 1 (by rfl) ⟨2424815, by rfl⟩ : syracuseStep 3233087 = 4849631) B4849631
theorem B5526953 : Blo 1435537 5526953 := bstep (se 2 (by rfl) ⟨2072607, by rfl⟩ : syracuseStep 5526953 = 4145215) B4145215
theorem B3233519 : Blo 1435537 3233519 := bstep (se 1 (by rfl) ⟨2425139, by rfl⟩ : syracuseStep 3233519 = 4850279) B4850279
theorem B3233555 : Blo 1435537 3233555 := bstep (se 1 (by rfl) ⟨2425166, by rfl⟩ : syracuseStep 3233555 = 4850333) B4850333
theorem B10909727 : Blo 1435537 10909727 := bstep (se 1 (by rfl) ⟨8182295, by rfl⟩ : syracuseStep 10909727 = 16364591) B16364591
theorem B8181931 : Blo 1435537 8181931 := bstep (se 1 (by rfl) ⟨6136448, by rfl⟩ : syracuseStep 8181931 = 12272897) B12272897
theorem B5454013 : Blo 1435537 5454013 := bstep (se 3 (by rfl) ⟨1022627, by rfl⟩ : syracuseStep 5454013 = 2045255) B2045255
theorem B3234095 : Blo 1435537 3234095 := bstep (se 1 (by rfl) ⟨2425571, by rfl⟩ : syracuseStep 3234095 = 4851143) B4851143
theorem B27630011 : Blo 1435537 27630011 := bstep (se 1 (by rfl) ⟨20722508, by rfl⟩ : syracuseStep 27630011 = 41445017) B41445017
theorem B37804927 : Blo 1435537 37804927 := bstep (se 1 (by rfl) ⟨28353695, by rfl⟩ : syracuseStep 37804927 = 56707391) B56707391
theorem B2153465 : Blo 1435537 2153465 := bstep (se 2 (by rfl) ⟨807549, by rfl⟩ : syracuseStep 2153465 = 1615099) B1615099
theorem B2424559 : Blo 1435537 2424559 := bstep (se 1 (by rfl) ⟨1818419, by rfl⟩ : syracuseStep 2424559 = 3636839) B3636839
theorem B104898361 : Blo 1435537 104898361 := bstep (se 2 (by rfl) ⟨39336885, by rfl⟩ : syracuseStep 104898361 = 78673771) B78673771
theorem B2424863 : Blo 1435537 2424863 := bstep (se 1 (by rfl) ⟨1818647, by rfl⟩ : syracuseStep 2424863 = 3637295) B3637295
theorem B119545915 : Blo 1435537 119545915 := bstep (se 1 (by rfl) ⟨89659436, by rfl⟩ : syracuseStep 119545915 = 179318873) B179318873
theorem B3637345 : Blo 1435537 3637345 := bstep (se 2 (by rfl) ⟨1364004, by rfl⟩ : syracuseStep 3637345 = 2728009) B2728009
theorem B11215261 : Blo 1435537 11215261 := bstep (se 3 (by rfl) ⟨2102861, by rfl⟩ : syracuseStep 11215261 = 4205723) B4205723
theorem B2155391 : Blo 1435537 2155391 := bstep (se 1 (by rfl) ⟨1616543, by rfl⟩ : syracuseStep 2155391 = 3233087) B3233087
theorem B3638155 : Blo 1435537 3638155 := bstep (se 1 (by rfl) ⟨2728616, by rfl⟩ : syracuseStep 3638155 = 5457233) B5457233
theorem B2155679 : Blo 1435537 2155679 := bstep (se 1 (by rfl) ⟨1616759, by rfl⟩ : syracuseStep 2155679 = 3233519) B3233519
theorem B50406569 : Blo 1435537 50406569 := bstep (se 2 (by rfl) ⟨18902463, by rfl⟩ : syracuseStep 50406569 = 37804927) B37804927
theorem B2155703 : Blo 1435537 2155703 := bstep (se 1 (by rfl) ⟨1616777, by rfl⟩ : syracuseStep 2155703 = 3233555) B3233555
theorem B15746537 : Blo 1435537 15746537 := bstep (se 2 (by rfl) ⟨5904951, by rfl⟩ : syracuseStep 15746537 = 11809903) B11809903
theorem B2156063 : Blo 1435537 2156063 := bstep (se 1 (by rfl) ⟨1617047, by rfl⟩ : syracuseStep 2156063 = 3234095) B3234095
theorem B1435643 : Blo 1435537 1435643 := bstep (se 1 (by rfl) ⟨1076732, by rfl⟩ : syracuseStep 1435643 = 2153465) B2153465
theorem B8177831 : Blo 1435537 8177831 := bstep (se 1 (by rfl) ⟨6133373, by rfl⟩ : syracuseStep 8177831 = 12266747) B12266747
theorem B7375259 : Blo 1435537 7375259 := bstep (se 1 (by rfl) ⟨5531444, by rfl⟩ : syracuseStep 7375259 = 11062889) B11062889
theorem B139864481 : Blo 1435537 139864481 := bstep (se 2 (by rfl) ⟨52449180, by rfl⟩ : syracuseStep 139864481 = 104898361) B104898361
theorem B3230351 : Blo 1435537 3230351 := bstep (se 1 (by rfl) ⟨2422763, by rfl⟩ : syracuseStep 3230351 = 4845527) B4845527
theorem B1436367 : Blo 1435537 1436367 := bstep (se 1 (by rfl) ⟨1077275, by rfl⟩ : syracuseStep 1436367 = 2154551) B2154551
theorem B3230927 : Blo 1435537 3230927 := bstep (se 1 (by rfl) ⟨2423195, by rfl⟩ : syracuseStep 3230927 = 4846391) B4846391
theorem B1617151 : Blo 1435537 1617151 := bstep (se 1 (by rfl) ⟨1212863, by rfl⟩ : syracuseStep 1617151 = 2425727) B2425727
theorem B1436991 : Blo 1435537 1436991 := bstep (se 1 (by rfl) ⟨1077743, by rfl⟩ : syracuseStep 1436991 = 2155487) B2155487
theorem B7270559 : Blo 1435537 7270559 := bstep (se 1 (by rfl) ⟨5452919, by rfl⟩ : syracuseStep 7270559 = 10905839) B10905839
theorem B18420007 : Blo 1435537 18420007 := bstep (se 1 (by rfl) ⟨13815005, by rfl⟩ : syracuseStep 18420007 = 27630011) B27630011
theorem B3232745 : Blo 1435537 3232745 := bstep (se 2 (by rfl) ⟨1212279, by rfl⟩ : syracuseStep 3232745 = 2424559) B2424559
theorem B4846823 : Blo 1435537 4846823 := bstep (se 1 (by rfl) ⟨3635117, by rfl⟩ : syracuseStep 4846823 = 7270235) B7270235
theorem B21566941 : Blo 1435537 21566941 := bstep (se 3 (by rfl) ⟨4043801, by rfl⟩ : syracuseStep 21566941 = 8087603) B8087603
theorem B10909241 : Blo 1435537 10909241 := bstep (se 2 (by rfl) ⟨4090965, by rfl⟩ : syracuseStep 10909241 = 8181931) B8181931
theorem B7272017 : Blo 1435537 7272017 := bstep (se 2 (by rfl) ⟨2727006, by rfl⟩ : syracuseStep 7272017 = 5454013) B5454013
theorem B4847471 : Blo 1435537 4847471 := bstep (se 1 (by rfl) ⟨3635603, by rfl⟩ : syracuseStep 4847471 = 7271207) B7271207
theorem B58980383 : Blo 1435537 58980383 := bstep (se 1 (by rfl) ⟨44235287, by rfl⟩ : syracuseStep 58980383 = 88470575) B88470575
theorem B3684635 : Blo 1435537 3684635 := bstep (se 1 (by rfl) ⟨2763476, by rfl⟩ : syracuseStep 3684635 = 5526953) B5526953
theorem B26196281 : Blo 1435537 26196281 := bstep (se 2 (by rfl) ⟨9823605, by rfl⟩ : syracuseStep 26196281 = 19647211) B19647211
theorem B7273151 : Blo 1435537 7273151 := bstep (se 1 (by rfl) ⟨5454863, by rfl⟩ : syracuseStep 7273151 = 10909727) B10909727
theorem B55975171 : Blo 1435537 55975171 := bstep (se 1 (by rfl) ⟨41981378, by rfl⟩ : syracuseStep 55975171 = 83962757) B83962757
theorem B2153783 : Blo 1435537 2153783 := bstep (se 1 (by rfl) ⟨1615337, by rfl⟩ : syracuseStep 2153783 = 3230675) B3230675
theorem B4849793 : Blo 1435537 4849793 := bstep (se 2 (by rfl) ⟨1818672, by rfl⟩ : syracuseStep 4849793 = 3637345) B3637345
theorem B24560009 : Blo 1435537 24560009 := bstep (se 2 (by rfl) ⟨9210003, by rfl⟩ : syracuseStep 24560009 = 18420007) B18420007
theorem B2155163 : Blo 1435537 2155163 := bstep (se 1 (by rfl) ⟨1616372, by rfl⟩ : syracuseStep 2155163 = 3232745) B3232745
theorem B33604379 : Blo 1435537 33604379 := bstep (se 1 (by rfl) ⟨25203284, by rfl⟩ : syracuseStep 33604379 = 50406569) B50406569
theorem B4850873 : Blo 1435537 4850873 := bstep (se 2 (by rfl) ⟨1819077, by rfl⟩ : syracuseStep 4850873 = 3638155) B3638155
theorem B93242987 : Blo 1435537 93242987 := bstep (se 1 (by rfl) ⟨69932240, by rfl⟩ : syracuseStep 93242987 = 139864481) B139864481
theorem B2156201 : Blo 1435537 2156201 := bstep (se 2 (by rfl) ⟨808575, by rfl⟩ : syracuseStep 2156201 = 1617151) B1617151
theorem B1435855 : Blo 1435537 1435855 := bstep (se 1 (by rfl) ⟨1076891, by rfl⟩ : syracuseStep 1435855 = 2153783) B2153783
theorem B1616575 : Blo 1435537 1616575 := bstep (se 1 (by rfl) ⟨1212431, by rfl⟩ : syracuseStep 1616575 = 2424863) B2424863
theorem B159394553 : Blo 1435537 159394553 := bstep (se 2 (by rfl) ⟨59772957, by rfl⟩ : syracuseStep 159394553 = 119545915) B119545915
theorem B14953681 : Blo 1435537 14953681 := bstep (se 2 (by rfl) ⟨5607630, by rfl⟩ : syracuseStep 14953681 = 11215261) B11215261
theorem B1436927 : Blo 1435537 1436927 := bstep (se 1 (by rfl) ⟨1077695, by rfl⟩ : syracuseStep 1436927 = 2155391) B2155391
theorem B1437119 : Blo 1435537 1437119 := bstep (se 1 (by rfl) ⟨1077839, by rfl⟩ : syracuseStep 1437119 = 2155679) B2155679
theorem B1437135 : Blo 1435537 1437135 := bstep (se 1 (by rfl) ⟨1077851, by rfl⟩ : syracuseStep 1437135 = 2155703) B2155703
theorem B3231215 : Blo 1435537 3231215 := bstep (se 1 (by rfl) ⟨2423411, by rfl⟩ : syracuseStep 3231215 = 4846823) B4846823
theorem B10497691 : Blo 1435537 10497691 := bstep (se 1 (by rfl) ⟨7873268, by rfl⟩ : syracuseStep 10497691 = 15746537) B15746537
theorem B1437375 : Blo 1435537 1437375 := bstep (se 1 (by rfl) ⟨1078031, by rfl⟩ : syracuseStep 1437375 = 2156063) B2156063
theorem B3231647 : Blo 1435537 3231647 := bstep (se 1 (by rfl) ⟨2423735, by rfl⟩ : syracuseStep 3231647 = 4847471) B4847471
theorem B5451887 : Blo 1435537 5451887 := bstep (se 1 (by rfl) ⟨4088915, by rfl⟩ : syracuseStep 5451887 = 8177831) B8177831
theorem B74633561 : Blo 1435537 74633561 := bstep (se 2 (by rfl) ⟨27987585, by rfl⟩ : syracuseStep 74633561 = 55975171) B55975171
theorem B4847039 : Blo 1435537 4847039 := bstep (se 1 (by rfl) ⟨3635279, by rfl⟩ : syracuseStep 4847039 = 7270559) B7270559
theorem B7272827 : Blo 1435537 7272827 := bstep (se 1 (by rfl) ⟨5454620, by rfl⟩ : syracuseStep 7272827 = 10909241) B10909241
theorem B4848011 : Blo 1435537 4848011 := bstep (se 1 (by rfl) ⟨3636008, by rfl⟩ : syracuseStep 4848011 = 7272017) B7272017
theorem B19667357 : Blo 1435537 19667357 := bstep (se 3 (by rfl) ⟨3687629, by rfl⟩ : syracuseStep 19667357 = 7375259) B7375259
theorem B39320255 : Blo 1435537 39320255 := bstep (se 1 (by rfl) ⟨29490191, by rfl⟩ : syracuseStep 39320255 = 58980383) B58980383
theorem B2456423 : Blo 1435537 2456423 := bstep (se 1 (by rfl) ⟨1842317, by rfl⟩ : syracuseStep 2456423 = 3684635) B3684635
theorem B17464187 : Blo 1435537 17464187 := bstep (se 1 (by rfl) ⟨13098140, by rfl⟩ : syracuseStep 17464187 = 26196281) B26196281
theorem B2153567 : Blo 1435537 2153567 := bstep (se 1 (by rfl) ⟨1615175, by rfl⟩ : syracuseStep 2153567 = 3230351) B3230351
theorem B4848767 : Blo 1435537 4848767 := bstep (se 1 (by rfl) ⟨3636575, by rfl⟩ : syracuseStep 4848767 = 7273151) B7273151
theorem B460094741 : Blo 1435537 460094741 := bstep (se 6 (by rfl) ⟨10783470, by rfl⟩ : syracuseStep 460094741 = 21566941) B21566941
theorem B2153951 : Blo 1435537 2153951 := bstep (se 1 (by rfl) ⟨1615463, by rfl⟩ : syracuseStep 2153951 = 3230927) B3230927
theorem B2155433 : Blo 1435537 2155433 := bstep (se 2 (by rfl) ⟨808287, by rfl⟩ : syracuseStep 2155433 = 1616575) B1616575
theorem B62161991 : Blo 1435537 62161991 := bstep (se 1 (by rfl) ⟨46621493, by rfl⟩ : syracuseStep 62161991 = 93242987) B93242987
theorem B11642791 : Blo 1435537 11642791 := bstep (se 1 (by rfl) ⟨8732093, by rfl⟩ : syracuseStep 11642791 = 17464187) B17464187
theorem B1435711 : Blo 1435537 1435711 := bstep (se 1 (by rfl) ⟨1076783, by rfl⟩ : syracuseStep 1435711 = 2153567) B2153567
theorem B1435967 : Blo 1435537 1435967 := bstep (se 1 (by rfl) ⟨1076975, by rfl⟩ : syracuseStep 1435967 = 2153951) B2153951
theorem B1436775 : Blo 1435537 1436775 := bstep (se 1 (by rfl) ⟨1077581, by rfl⟩ : syracuseStep 1436775 = 2155163) B2155163
theorem B3231359 : Blo 1435537 3231359 := bstep (se 1 (by rfl) ⟨2423519, by rfl⟩ : syracuseStep 3231359 = 4847039) B4847039
theorem B1437467 : Blo 1435537 1437467 := bstep (se 1 (by rfl) ⟨1078100, by rfl⟩ : syracuseStep 1437467 = 2156201) B2156201
theorem B3232007 : Blo 1435537 3232007 := bstep (se 1 (by rfl) ⟨2424005, by rfl⟩ : syracuseStep 3232007 = 4848011) B4848011
theorem B13111571 : Blo 1435537 13111571 := bstep (se 1 (by rfl) ⟨9833678, by rfl⟩ : syracuseStep 13111571 = 19667357) B19667357
theorem B106263035 : Blo 1435537 106263035 := bstep (se 1 (by rfl) ⟨79697276, by rfl⟩ : syracuseStep 106263035 = 159394553) B159394553
theorem B3232511 : Blo 1435537 3232511 := bstep (se 1 (by rfl) ⟨2424383, by rfl⟩ : syracuseStep 3232511 = 4848767) B4848767
theorem B306729827 : Blo 1435537 306729827 := bstep (se 1 (by rfl) ⟨230047370, by rfl⟩ : syracuseStep 306729827 = 460094741) B460094741
theorem B13996921 : Blo 1435537 13996921 := bstep (se 2 (by rfl) ⟨5248845, by rfl⟩ : syracuseStep 13996921 = 10497691) B10497691
theorem B3634591 : Blo 1435537 3634591 := bstep (se 1 (by rfl) ⟨2725943, by rfl⟩ : syracuseStep 3634591 = 5451887) B5451887
theorem B3233195 : Blo 1435537 3233195 := bstep (se 1 (by rfl) ⟨2424896, by rfl⟩ : syracuseStep 3233195 = 4849793) B4849793
theorem B49755707 : Blo 1435537 49755707 := bstep (se 1 (by rfl) ⟨37316780, by rfl⟩ : syracuseStep 49755707 = 74633561) B74633561
theorem B16373339 : Blo 1435537 16373339 := bstep (se 1 (by rfl) ⟨12280004, by rfl⟩ : syracuseStep 16373339 = 24560009) B24560009
theorem B22402919 : Blo 1435537 22402919 := bstep (se 1 (by rfl) ⟨16802189, by rfl⟩ : syracuseStep 22402919 = 33604379) B33604379
theorem B3233915 : Blo 1435537 3233915 := bstep (se 1 (by rfl) ⟨2425436, by rfl⟩ : syracuseStep 3233915 = 4850873) B4850873
theorem B4848551 : Blo 1435537 4848551 := bstep (se 1 (by rfl) ⟨3636413, by rfl⟩ : syracuseStep 4848551 = 7272827) B7272827
theorem B19938241 : Blo 1435537 19938241 := bstep (se 2 (by rfl) ⟨7476840, by rfl⟩ : syracuseStep 19938241 = 14953681) B14953681
theorem B26213503 : Blo 1435537 26213503 := bstep (se 1 (by rfl) ⟨19660127, by rfl⟩ : syracuseStep 26213503 = 39320255) B39320255
theorem B1637615 : Blo 1435537 1637615 := bstep (se 1 (by rfl) ⟨1228211, by rfl⟩ : syracuseStep 1637615 = 2456423) B2456423
theorem B2154143 : Blo 1435537 2154143 := bstep (se 1 (by rfl) ⟨1615607, by rfl⟩ : syracuseStep 2154143 = 3231215) B3231215
theorem B2154431 : Blo 1435537 2154431 := bstep (se 1 (by rfl) ⟨1615823, by rfl⟩ : syracuseStep 2154431 = 3231647) B3231647
theorem B2154671 : Blo 1435537 2154671 := bstep (se 1 (by rfl) ⟨1616003, by rfl⟩ : syracuseStep 2154671 = 3232007) B3232007
theorem B8741047 : Blo 1435537 8741047 := bstep (se 1 (by rfl) ⟨6555785, by rfl⟩ : syracuseStep 8741047 = 13111571) B13111571
theorem B2155007 : Blo 1435537 2155007 := bstep (se 1 (by rfl) ⟨1616255, by rfl⟩ : syracuseStep 2155007 = 3232511) B3232511
theorem B4366973 : Blo 1435537 4366973 := bstep (se 3 (by rfl) ⟨818807, by rfl⟩ : syracuseStep 4366973 = 1637615) B1637615
theorem B2155463 : Blo 1435537 2155463 := bstep (se 1 (by rfl) ⟨1616597, by rfl⟩ : syracuseStep 2155463 = 3233195) B3233195
theorem B33170471 : Blo 1435537 33170471 := bstep (se 1 (by rfl) ⟨24877853, by rfl⟩ : syracuseStep 33170471 = 49755707) B49755707
theorem B18662561 : Blo 1435537 18662561 := bstep (se 2 (by rfl) ⟨6998460, by rfl⟩ : syracuseStep 18662561 = 13996921) B13996921
theorem B14935279 : Blo 1435537 14935279 := bstep (se 1 (by rfl) ⟨11201459, by rfl⟩ : syracuseStep 14935279 = 22402919) B22402919
theorem B2155943 : Blo 1435537 2155943 := bstep (se 1 (by rfl) ⟨1616957, by rfl⟩ : syracuseStep 2155943 = 3233915) B3233915
theorem B1436095 : Blo 1435537 1436095 := bstep (se 1 (by rfl) ⟨1077071, by rfl⟩ : syracuseStep 1436095 = 2154143) B2154143
theorem B1436287 : Blo 1435537 1436287 := bstep (se 1 (by rfl) ⟨1077215, by rfl⟩ : syracuseStep 1436287 = 2154431) B2154431
theorem B1436955 : Blo 1435537 1436955 := bstep (se 1 (by rfl) ⟨1077716, by rfl⟩ : syracuseStep 1436955 = 2155433) B2155433
theorem B10915559 : Blo 1435537 10915559 := bstep (se 1 (by rfl) ⟨8186669, by rfl⟩ : syracuseStep 10915559 = 16373339) B16373339
theorem B34951337 : Blo 1435537 34951337 := bstep (se 2 (by rfl) ⟨13106751, by rfl⟩ : syracuseStep 34951337 = 26213503) B26213503
theorem B4846121 : Blo 1435537 4846121 := bstep (se 2 (by rfl) ⟨1817295, by rfl⟩ : syracuseStep 4846121 = 3634591) B3634591
theorem B3232367 : Blo 1435537 3232367 := bstep (se 1 (by rfl) ⟨2424275, by rfl⟩ : syracuseStep 3232367 = 4848551) B4848551
theorem B106337285 : Blo 1435537 106337285 := bstep (se 4 (by rfl) ⟨9969120, by rfl⟩ : syracuseStep 106337285 = 19938241) B19938241
theorem B70842023 : Blo 1435537 70842023 := bstep (se 1 (by rfl) ⟨53131517, by rfl⟩ : syracuseStep 70842023 = 106263035) B106263035
theorem B204486551 : Blo 1435537 204486551 := bstep (se 1 (by rfl) ⟨153364913, by rfl⟩ : syracuseStep 204486551 = 306729827) B306729827
theorem B41441327 : Blo 1435537 41441327 := bstep (se 1 (by rfl) ⟨31080995, by rfl⟩ : syracuseStep 41441327 = 62161991) B62161991
theorem B2154239 : Blo 1435537 2154239 := bstep (se 1 (by rfl) ⟨1615679, by rfl⟩ : syracuseStep 2154239 = 3231359) B3231359
theorem B15523721 : Blo 1435537 15523721 := bstep (se 2 (by rfl) ⟨5821395, by rfl⟩ : syracuseStep 15523721 = 11642791) B11642791
theorem B2154911 : Blo 1435537 2154911 := bstep (se 1 (by rfl) ⟨1616183, by rfl⟩ : syracuseStep 2154911 = 3232367) B3232367
theorem B47228015 : Blo 1435537 47228015 := bstep (se 1 (by rfl) ⟨35421011, by rfl⟩ : syracuseStep 47228015 = 70842023) B70842023
theorem B136324367 : Blo 1435537 136324367 := bstep (se 1 (by rfl) ⟨102243275, by rfl⟩ : syracuseStep 136324367 = 204486551) B204486551
theorem B7277039 : Blo 1435537 7277039 := bstep (se 1 (by rfl) ⟨5457779, by rfl⟩ : syracuseStep 7277039 = 10915559) B10915559
theorem B1436159 : Blo 1435537 1436159 := bstep (se 1 (by rfl) ⟨1077119, by rfl⟩ : syracuseStep 1436159 = 2154239) B2154239
theorem B10349147 : Blo 1435537 10349147 := bstep (se 1 (by rfl) ⟨7761860, by rfl⟩ : syracuseStep 10349147 = 15523721) B15523721
theorem B23300891 : Blo 1435537 23300891 := bstep (se 1 (by rfl) ⟨17475668, by rfl⟩ : syracuseStep 23300891 = 34951337) B34951337
theorem B1436447 : Blo 1435537 1436447 := bstep (se 1 (by rfl) ⟨1077335, by rfl⟩ : syracuseStep 1436447 = 2154671) B2154671
theorem B1436671 : Blo 1435537 1436671 := bstep (se 1 (by rfl) ⟨1077503, by rfl⟩ : syracuseStep 1436671 = 2155007) B2155007
theorem B3230747 : Blo 1435537 3230747 := bstep (se 1 (by rfl) ⟨2423060, by rfl⟩ : syracuseStep 3230747 = 4846121) B4846121
theorem B2911315 : Blo 1435537 2911315 := bstep (se 1 (by rfl) ⟨2183486, by rfl⟩ : syracuseStep 2911315 = 4366973) B4366973
theorem B1436975 : Blo 1435537 1436975 := bstep (se 1 (by rfl) ⟨1077731, by rfl⟩ : syracuseStep 1436975 = 2155463) B2155463
theorem B22113647 : Blo 1435537 22113647 := bstep (se 1 (by rfl) ⟨16585235, by rfl⟩ : syracuseStep 22113647 = 33170471) B33170471
theorem B1437295 : Blo 1435537 1437295 := bstep (se 1 (by rfl) ⟨1077971, by rfl⟩ : syracuseStep 1437295 = 2155943) B2155943
theorem B27627551 : Blo 1435537 27627551 := bstep (se 1 (by rfl) ⟨20720663, by rfl⟩ : syracuseStep 27627551 = 41441327) B41441327
theorem B11654729 : Blo 1435537 11654729 := bstep (se 2 (by rfl) ⟨4370523, by rfl⟩ : syracuseStep 11654729 = 8741047) B8741047
theorem B70891523 : Blo 1435537 70891523 := bstep (se 1 (by rfl) ⟨53168642, by rfl⟩ : syracuseStep 70891523 = 106337285) B106337285
theorem B12441707 : Blo 1435537 12441707 := bstep (se 1 (by rfl) ⟨9331280, by rfl⟩ : syracuseStep 12441707 = 18662561) B18662561
theorem B19913705 : Blo 1435537 19913705 := bstep (se 2 (by rfl) ⟨7467639, by rfl⟩ : syracuseStep 19913705 = 14935279) B14935279
theorem B90882911 : Blo 1435537 90882911 := bstep (se 1 (by rfl) ⟨68162183, by rfl⟩ : syracuseStep 90882911 = 136324367) B136324367
theorem B47261015 : Blo 1435537 47261015 := bstep (se 1 (by rfl) ⟨35445761, by rfl⟩ : syracuseStep 47261015 = 70891523) B70891523
theorem B4851359 : Blo 1435537 4851359 := bstep (se 1 (by rfl) ⟨3638519, by rfl⟩ : syracuseStep 4851359 = 7277039) B7277039
theorem B6899431 : Blo 1435537 6899431 := bstep (se 1 (by rfl) ⟨5174573, by rfl⟩ : syracuseStep 6899431 = 10349147) B10349147
theorem B15533927 : Blo 1435537 15533927 := bstep (se 1 (by rfl) ⟨11650445, by rfl⟩ : syracuseStep 15533927 = 23300891) B23300891
theorem B18418367 : Blo 1435537 18418367 := bstep (se 1 (by rfl) ⟨13813775, by rfl⟩ : syracuseStep 18418367 = 27627551) B27627551
theorem B1436607 : Blo 1435537 1436607 := bstep (se 1 (by rfl) ⟨1077455, by rfl⟩ : syracuseStep 1436607 = 2154911) B2154911
theorem B31485343 : Blo 1435537 31485343 := bstep (se 1 (by rfl) ⟨23614007, by rfl⟩ : syracuseStep 31485343 = 47228015) B47228015
theorem B7769819 : Blo 1435537 7769819 := bstep (se 1 (by rfl) ⟨5827364, by rfl⟩ : syracuseStep 7769819 = 11654729) B11654729
theorem B8294471 : Blo 1435537 8294471 := bstep (se 1 (by rfl) ⟨6220853, by rfl⟩ : syracuseStep 8294471 = 12441707) B12441707
theorem B13275803 : Blo 1435537 13275803 := bstep (se 1 (by rfl) ⟨9956852, by rfl⟩ : syracuseStep 13275803 = 19913705) B19913705
theorem B14742431 : Blo 1435537 14742431 := bstep (se 1 (by rfl) ⟨11056823, by rfl⟩ : syracuseStep 14742431 = 22113647) B22113647
theorem B3881753 : Blo 1435537 3881753 := bstep (se 2 (by rfl) ⟨1455657, by rfl⟩ : syracuseStep 3881753 = 2911315) B2911315
theorem B2153831 : Blo 1435537 2153831 := bstep (se 1 (by rfl) ⟨1615373, by rfl⟩ : syracuseStep 2153831 = 3230747) B3230747
theorem B5529647 : Blo 1435537 5529647 := bstep (se 1 (by rfl) ⟨4147235, by rfl⟩ : syracuseStep 5529647 = 8294471) B8294471
theorem B60588607 : Blo 1435537 60588607 := bstep (se 1 (by rfl) ⟨45441455, by rfl⟩ : syracuseStep 60588607 = 90882911) B90882911
theorem B31507343 : Blo 1435537 31507343 := bstep (se 1 (by rfl) ⟨23630507, by rfl⟩ : syracuseStep 31507343 = 47261015) B47261015
theorem B10355951 : Blo 1435537 10355951 := bstep (se 1 (by rfl) ⟨7766963, by rfl⟩ : syracuseStep 10355951 = 15533927) B15533927
theorem B1435887 : Blo 1435537 1435887 := bstep (se 1 (by rfl) ⟨1076915, by rfl⟩ : syracuseStep 1435887 = 2153831) B2153831
theorem B5179879 : Blo 1435537 5179879 := bstep (se 1 (by rfl) ⟨3884909, by rfl⟩ : syracuseStep 5179879 = 7769819) B7769819
theorem B8850535 : Blo 1435537 8850535 := bstep (se 1 (by rfl) ⟨6637901, by rfl⟩ : syracuseStep 8850535 = 13275803) B13275803
theorem B41980457 : Blo 1435537 41980457 := bstep (se 2 (by rfl) ⟨15742671, by rfl⟩ : syracuseStep 41980457 = 31485343) B31485343
theorem B9828287 : Blo 1435537 9828287 := bstep (se 1 (by rfl) ⟨7371215, by rfl⟩ : syracuseStep 9828287 = 14742431) B14742431
theorem B3234239 : Blo 1435537 3234239 := bstep (se 1 (by rfl) ⟨2425679, by rfl⟩ : syracuseStep 3234239 = 4851359) B4851359
theorem B12278911 : Blo 1435537 12278911 := bstep (se 1 (by rfl) ⟨9209183, by rfl⟩ : syracuseStep 12278911 = 18418367) B18418367
theorem B2587835 : Blo 1435537 2587835 := bstep (se 1 (by rfl) ⟨1940876, by rfl⟩ : syracuseStep 2587835 = 3881753) B3881753
theorem B9199241 : Blo 1435537 9199241 := bstep (se 2 (by rfl) ⟨3449715, by rfl⟩ : syracuseStep 9199241 = 6899431) B6899431
theorem B14745725 : Blo 1435537 14745725 := bstep (se 3 (by rfl) ⟨2764823, by rfl⟩ : syracuseStep 14745725 = 5529647) B5529647
theorem B47202853 : Blo 1435537 47202853 := bstep (se 4 (by rfl) ⟨4425267, by rfl⟩ : syracuseStep 47202853 = 8850535) B8850535
theorem B21004895 : Blo 1435537 21004895 := bstep (se 1 (by rfl) ⟨15753671, by rfl⟩ : syracuseStep 21004895 = 31507343) B31507343
theorem B6906505 : Blo 1435537 6906505 := bstep (se 2 (by rfl) ⟨2589939, by rfl⟩ : syracuseStep 6906505 = 5179879) B5179879
theorem B2156159 : Blo 1435537 2156159 := bstep (se 1 (by rfl) ⟨1617119, by rfl⟩ : syracuseStep 2156159 = 3234239) B3234239
theorem B27986971 : Blo 1435537 27986971 := bstep (se 1 (by rfl) ⟨20990228, by rfl⟩ : syracuseStep 27986971 = 41980457) B41980457
theorem B80784809 : Blo 1435537 80784809 := bstep (se 2 (by rfl) ⟨30294303, by rfl⟩ : syracuseStep 80784809 = 60588607) B60588607
theorem B16371881 : Blo 1435537 16371881 := bstep (se 2 (by rfl) ⟨6139455, by rfl⟩ : syracuseStep 16371881 = 12278911) B12278911
theorem B1725223 : Blo 1435537 1725223 := bstep (se 1 (by rfl) ⟨1293917, by rfl⟩ : syracuseStep 1725223 = 2587835) B2587835
theorem B6132827 : Blo 1435537 6132827 := bstep (se 1 (by rfl) ⟨4599620, by rfl⟩ : syracuseStep 6132827 = 9199241) B9199241
theorem B6903967 : Blo 1435537 6903967 := bstep (se 1 (by rfl) ⟨5177975, by rfl⟩ : syracuseStep 6903967 = 10355951) B10355951
theorem B6552191 : Blo 1435537 6552191 := bstep (se 1 (by rfl) ⟨4914143, by rfl⟩ : syracuseStep 6552191 = 9828287) B9828287
theorem B9830483 : Blo 1435537 9830483 := bstep (se 1 (by rfl) ⟨7372862, by rfl⟩ : syracuseStep 9830483 = 14745725) B14745725
theorem B4088551 : Blo 1435537 4088551 := bstep (se 1 (by rfl) ⟨3066413, by rfl⟩ : syracuseStep 4088551 = 6132827) B6132827
theorem B9208673 : Blo 1435537 9208673 := bstep (se 2 (by rfl) ⟨3453252, by rfl⟩ : syracuseStep 9208673 = 6906505) B6906505
theorem B37315961 : Blo 1435537 37315961 := bstep (se 2 (by rfl) ⟨13993485, by rfl⟩ : syracuseStep 37315961 = 27986971) B27986971
theorem B53856539 : Blo 1435537 53856539 := bstep (se 1 (by rfl) ⟨40392404, by rfl⟩ : syracuseStep 53856539 = 80784809) B80784809
theorem B10914587 : Blo 1435537 10914587 := bstep (se 1 (by rfl) ⟨8185940, by rfl⟩ : syracuseStep 10914587 = 16371881) B16371881
theorem B14003263 : Blo 1435537 14003263 := bstep (se 1 (by rfl) ⟨10502447, by rfl⟩ : syracuseStep 14003263 = 21004895) B21004895
theorem B1437439 : Blo 1435537 1437439 := bstep (se 1 (by rfl) ⟨1078079, by rfl⟩ : syracuseStep 1437439 = 2156159) B2156159
theorem B9205289 : Blo 1435537 9205289 := bstep (se 2 (by rfl) ⟨3451983, by rfl⟩ : syracuseStep 9205289 = 6903967) B6903967
theorem B62937137 : Blo 1435537 62937137 := bstep (se 2 (by rfl) ⟨23601426, by rfl⟩ : syracuseStep 62937137 = 47202853) B47202853
theorem B2300297 : Blo 1435537 2300297 := bstep (se 2 (by rfl) ⟨862611, by rfl⟩ : syracuseStep 2300297 = 1725223) B1725223
theorem B17472509 : Blo 1435537 17472509 := bstep (se 3 (by rfl) ⟨3276095, by rfl⟩ : syracuseStep 17472509 = 6552191) B6552191
theorem B6553655 : Blo 1435537 6553655 := bstep (se 1 (by rfl) ⟨4915241, by rfl⟩ : syracuseStep 6553655 = 9830483) B9830483
theorem B6136859 : Blo 1435537 6136859 := bstep (se 1 (by rfl) ⟨4602644, by rfl⟩ : syracuseStep 6136859 = 9205289) B9205289
theorem B7276391 : Blo 1435537 7276391 := bstep (se 1 (by rfl) ⟨5457293, by rfl⟩ : syracuseStep 7276391 = 10914587) B10914587
theorem B6139115 : Blo 1435537 6139115 := bstep (se 1 (by rfl) ⟨4604336, by rfl⟩ : syracuseStep 6139115 = 9208673) B9208673
theorem B5451401 : Blo 1435537 5451401 := bstep (se 2 (by rfl) ⟨2044275, by rfl⟩ : syracuseStep 5451401 = 4088551) B4088551
theorem B74684069 : Blo 1435537 74684069 := bstep (se 4 (by rfl) ⟨7001631, by rfl⟩ : syracuseStep 74684069 = 14003263) B14003263
theorem B24877307 : Blo 1435537 24877307 := bstep (se 1 (by rfl) ⟨18657980, by rfl⟩ : syracuseStep 24877307 = 37315961) B37315961
theorem B6134125 : Blo 1435537 6134125 := bstep (se 3 (by rfl) ⟨1150148, by rfl⟩ : syracuseStep 6134125 = 2300297) B2300297
theorem B41958091 : Blo 1435537 41958091 := bstep (se 1 (by rfl) ⟨31468568, by rfl⟩ : syracuseStep 41958091 = 62937137) B62937137
theorem B35904359 : Blo 1435537 35904359 := bstep (se 1 (by rfl) ⟨26928269, by rfl⟩ : syracuseStep 35904359 = 53856539) B53856539
theorem B11648339 : Blo 1435537 11648339 := bstep (se 1 (by rfl) ⟨8736254, by rfl⟩ : syracuseStep 11648339 = 17472509) B17472509
theorem B55944121 : Blo 1435537 55944121 := bstep (se 2 (by rfl) ⟨20979045, by rfl⟩ : syracuseStep 55944121 = 41958091) B41958091
theorem B4850927 : Blo 1435537 4850927 := bstep (se 1 (by rfl) ⟨3638195, by rfl⟩ : syracuseStep 4850927 = 7276391) B7276391
theorem B4369103 : Blo 1435537 4369103 := bstep (se 1 (by rfl) ⟨3276827, by rfl⟩ : syracuseStep 4369103 = 6553655) B6553655
theorem B8178833 : Blo 1435537 8178833 := bstep (se 2 (by rfl) ⟨3067062, by rfl⟩ : syracuseStep 8178833 = 6134125) B6134125
theorem B4091239 : Blo 1435537 4091239 := bstep (se 1 (by rfl) ⟨3068429, by rfl⟩ : syracuseStep 4091239 = 6136859) B6136859
theorem B16584871 : Blo 1435537 16584871 := bstep (se 1 (by rfl) ⟨12438653, by rfl⟩ : syracuseStep 16584871 = 24877307) B24877307
theorem B4092743 : Blo 1435537 4092743 := bstep (se 1 (by rfl) ⟨3069557, by rfl⟩ : syracuseStep 4092743 = 6139115) B6139115
theorem B3634267 : Blo 1435537 3634267 := bstep (se 1 (by rfl) ⟨2725700, by rfl⟩ : syracuseStep 3634267 = 5451401) B5451401
theorem B49789379 : Blo 1435537 49789379 := bstep (se 1 (by rfl) ⟨37342034, by rfl⟩ : syracuseStep 49789379 = 74684069) B74684069
theorem B23936239 : Blo 1435537 23936239 := bstep (se 1 (by rfl) ⟨17952179, by rfl⟩ : syracuseStep 23936239 = 35904359) B35904359
theorem B7765559 : Blo 1435537 7765559 := bstep (se 1 (by rfl) ⟨5824169, by rfl⟩ : syracuseStep 7765559 = 11648339) B11648339
theorem B2728495 : Blo 1435537 2728495 := bstep (se 1 (by rfl) ⟨2046371, by rfl⟩ : syracuseStep 2728495 = 4092743) B4092743
theorem B22113161 : Blo 1435537 22113161 := bstep (se 2 (by rfl) ⟨8292435, by rfl⟩ : syracuseStep 22113161 = 16584871) B16584871
theorem B74592161 : Blo 1435537 74592161 := bstep (se 2 (by rfl) ⟨27972060, by rfl⟩ : syracuseStep 74592161 = 55944121) B55944121
theorem B127659941 : Blo 1435537 127659941 := bstep (se 4 (by rfl) ⟨11968119, by rfl⟩ : syracuseStep 127659941 = 23936239) B23936239
theorem B4845689 : Blo 1435537 4845689 := bstep (se 2 (by rfl) ⟨1817133, by rfl⟩ : syracuseStep 4845689 = 3634267) B3634267
theorem B2912735 : Blo 1435537 2912735 := bstep (se 1 (by rfl) ⟨2184551, by rfl⟩ : syracuseStep 2912735 = 4369103) B4369103
theorem B5452555 : Blo 1435537 5452555 := bstep (se 1 (by rfl) ⟨4089416, by rfl⟩ : syracuseStep 5452555 = 8178833) B8178833
theorem B3233951 : Blo 1435537 3233951 := bstep (se 1 (by rfl) ⟨2425463, by rfl⟩ : syracuseStep 3233951 = 4850927) B4850927
theorem B33192919 : Blo 1435537 33192919 := bstep (se 1 (by rfl) ⟨24894689, by rfl⟩ : syracuseStep 33192919 = 49789379) B49789379
theorem B5454985 : Blo 1435537 5454985 := bstep (se 2 (by rfl) ⟨2045619, by rfl⟩ : syracuseStep 5454985 = 4091239) B4091239
theorem B5177039 : Blo 1435537 5177039 := bstep (se 1 (by rfl) ⟨3882779, by rfl⟩ : syracuseStep 5177039 = 7765559) B7765559
theorem B1941823 : Blo 1435537 1941823 := bstep (se 1 (by rfl) ⟨1456367, by rfl⟩ : syracuseStep 1941823 = 2912735) B2912735
theorem B3637993 : Blo 1435537 3637993 := bstep (se 2 (by rfl) ⟨1364247, by rfl⟩ : syracuseStep 3637993 = 2728495) B2728495
theorem B2155967 : Blo 1435537 2155967 := bstep (se 1 (by rfl) ⟨1616975, by rfl⟩ : syracuseStep 2155967 = 3233951) B3233951
theorem B13805437 : Blo 1435537 13805437 := bstep (se 3 (by rfl) ⟨2588519, by rfl⟩ : syracuseStep 13805437 = 5177039) B5177039
theorem B49728107 : Blo 1435537 49728107 := bstep (se 1 (by rfl) ⟨37296080, by rfl⟩ : syracuseStep 49728107 = 74592161) B74592161
theorem B3230459 : Blo 1435537 3230459 := bstep (se 1 (by rfl) ⟨2422844, by rfl⟩ : syracuseStep 3230459 = 4845689) B4845689
theorem B7270073 : Blo 1435537 7270073 := bstep (se 2 (by rfl) ⟨2726277, by rfl⟩ : syracuseStep 7270073 = 5452555) B5452555
theorem B44257225 : Blo 1435537 44257225 := bstep (se 2 (by rfl) ⟨16596459, by rfl⟩ : syracuseStep 44257225 = 33192919) B33192919
theorem B14742107 : Blo 1435537 14742107 := bstep (se 1 (by rfl) ⟨11056580, by rfl⟩ : syracuseStep 14742107 = 22113161) B22113161
theorem B7273313 : Blo 1435537 7273313 := bstep (se 2 (by rfl) ⟨2727492, by rfl⟩ : syracuseStep 7273313 = 5454985) B5454985
theorem B85106627 : Blo 1435537 85106627 := bstep (se 1 (by rfl) ⟨63829970, by rfl⟩ : syracuseStep 85106627 = 127659941) B127659941
theorem B2589097 : Blo 1435537 2589097 := bstep (se 2 (by rfl) ⟨970911, by rfl⟩ : syracuseStep 2589097 = 1941823) B1941823
theorem B4850657 : Blo 1435537 4850657 := bstep (se 2 (by rfl) ⟨1818996, by rfl⟩ : syracuseStep 4850657 = 3637993) B3637993
theorem B59009633 : Blo 1435537 59009633 := bstep (se 2 (by rfl) ⟨22128612, by rfl⟩ : syracuseStep 59009633 = 44257225) B44257225
theorem B1437311 : Blo 1435537 1437311 := bstep (se 1 (by rfl) ⟨1077983, by rfl⟩ : syracuseStep 1437311 = 2155967) B2155967
theorem B132608285 : Blo 1435537 132608285 := bstep (se 3 (by rfl) ⟨24864053, by rfl⟩ : syracuseStep 132608285 = 49728107) B49728107
theorem B4846715 : Blo 1435537 4846715 := bstep (se 1 (by rfl) ⟨3635036, by rfl⟩ : syracuseStep 4846715 = 7270073) B7270073
theorem B9828071 : Blo 1435537 9828071 := bstep (se 1 (by rfl) ⟨7371053, by rfl⟩ : syracuseStep 9828071 = 14742107) B14742107
theorem B2153639 : Blo 1435537 2153639 := bstep (se 1 (by rfl) ⟨1615229, by rfl⟩ : syracuseStep 2153639 = 3230459) B3230459
theorem B4848875 : Blo 1435537 4848875 := bstep (se 1 (by rfl) ⟨3636656, by rfl⟩ : syracuseStep 4848875 = 7273313) B7273313
theorem B18407249 : Blo 1435537 18407249 := bstep (se 2 (by rfl) ⟨6902718, by rfl⟩ : syracuseStep 18407249 = 13805437) B13805437
theorem B56737751 : Blo 1435537 56737751 := bstep (se 1 (by rfl) ⟨42553313, by rfl⟩ : syracuseStep 56737751 = 85106627) B85106627
theorem B39339755 : Blo 1435537 39339755 := bstep (se 1 (by rfl) ⟨29504816, by rfl⟩ : syracuseStep 39339755 = 59009633) B59009633
theorem B1435759 : Blo 1435537 1435759 := bstep (se 1 (by rfl) ⟨1076819, by rfl⟩ : syracuseStep 1435759 = 2153639) B2153639
theorem B151300669 : Blo 1435537 151300669 := bstep (se 3 (by rfl) ⟨28368875, by rfl⟩ : syracuseStep 151300669 = 56737751) B56737751
theorem B3452129 : Blo 1435537 3452129 := bstep (se 2 (by rfl) ⟨1294548, by rfl⟩ : syracuseStep 3452129 = 2589097) B2589097
theorem B3231143 : Blo 1435537 3231143 := bstep (se 1 (by rfl) ⟨2423357, by rfl⟩ : syracuseStep 3231143 = 4846715) B4846715
theorem B3232583 : Blo 1435537 3232583 := bstep (se 1 (by rfl) ⟨2424437, by rfl⟩ : syracuseStep 3232583 = 4848875) B4848875
theorem B88405523 : Blo 1435537 88405523 := bstep (se 1 (by rfl) ⟨66304142, by rfl⟩ : syracuseStep 88405523 = 132608285) B132608285
theorem B3233771 : Blo 1435537 3233771 := bstep (se 1 (by rfl) ⟨2425328, by rfl⟩ : syracuseStep 3233771 = 4850657) B4850657
theorem B6552047 : Blo 1435537 6552047 := bstep (se 1 (by rfl) ⟨4914035, by rfl⟩ : syracuseStep 6552047 = 9828071) B9828071
theorem B12271499 : Blo 1435537 12271499 := bstep (se 1 (by rfl) ⟨9203624, by rfl⟩ : syracuseStep 12271499 = 18407249) B18407249
theorem B2155055 : Blo 1435537 2155055 := bstep (se 1 (by rfl) ⟨1616291, by rfl⟩ : syracuseStep 2155055 = 3232583) B3232583
theorem B2155847 : Blo 1435537 2155847 := bstep (se 1 (by rfl) ⟨1616885, by rfl⟩ : syracuseStep 2155847 = 3233771) B3233771
theorem B58937015 : Blo 1435537 58937015 := bstep (se 1 (by rfl) ⟨44202761, by rfl⟩ : syracuseStep 58937015 = 88405523) B88405523
theorem B26226503 : Blo 1435537 26226503 := bstep (se 1 (by rfl) ⟨19669877, by rfl⟩ : syracuseStep 26226503 = 39339755) B39339755
theorem B8180999 : Blo 1435537 8180999 := bstep (se 1 (by rfl) ⟨6135749, by rfl⟩ : syracuseStep 8180999 = 12271499) B12271499
theorem B201734225 : Blo 1435537 201734225 := bstep (se 2 (by rfl) ⟨75650334, by rfl⟩ : syracuseStep 201734225 = 151300669) B151300669
theorem B17472125 : Blo 1435537 17472125 := bstep (se 3 (by rfl) ⟨3276023, by rfl⟩ : syracuseStep 17472125 = 6552047) B6552047
theorem B2301419 : Blo 1435537 2301419 := bstep (se 1 (by rfl) ⟨1726064, by rfl⟩ : syracuseStep 2301419 = 3452129) B3452129
theorem B2154095 : Blo 1435537 2154095 := bstep (se 1 (by rfl) ⟨1615571, by rfl⟩ : syracuseStep 2154095 = 3231143) B3231143
theorem B6137117 : Blo 1435537 6137117 := bstep (se 3 (by rfl) ⟨1150709, by rfl⟩ : syracuseStep 6137117 = 2301419) B2301419
theorem B134489483 : Blo 1435537 134489483 := bstep (se 1 (by rfl) ⟨100867112, by rfl⟩ : syracuseStep 134489483 = 201734225) B201734225
theorem B157165373 : Blo 1435537 157165373 := bstep (se 3 (by rfl) ⟨29468507, by rfl⟩ : syracuseStep 157165373 = 58937015) B58937015
theorem B1436063 : Blo 1435537 1436063 := bstep (se 1 (by rfl) ⟨1077047, by rfl⟩ : syracuseStep 1436063 = 2154095) B2154095
theorem B17484335 : Blo 1435537 17484335 := bstep (se 1 (by rfl) ⟨13113251, by rfl⟩ : syracuseStep 17484335 = 26226503) B26226503
theorem B1436703 : Blo 1435537 1436703 := bstep (se 1 (by rfl) ⟨1077527, by rfl⟩ : syracuseStep 1436703 = 2155055) B2155055
theorem B1437231 : Blo 1435537 1437231 := bstep (se 1 (by rfl) ⟨1077923, by rfl⟩ : syracuseStep 1437231 = 2155847) B2155847
theorem B5453999 : Blo 1435537 5453999 := bstep (se 1 (by rfl) ⟨4090499, by rfl⟩ : syracuseStep 5453999 = 8180999) B8180999
theorem B11648083 : Blo 1435537 11648083 := bstep (se 1 (by rfl) ⟨8736062, by rfl⟩ : syracuseStep 11648083 = 17472125) B17472125
theorem B104776915 : Blo 1435537 104776915 := bstep (se 1 (by rfl) ⟨78582686, by rfl⟩ : syracuseStep 104776915 = 157165373) B157165373
theorem B4091411 : Blo 1435537 4091411 := bstep (se 1 (by rfl) ⟨3068558, by rfl⟩ : syracuseStep 4091411 = 6137117) B6137117
theorem B89659655 : Blo 1435537 89659655 := bstep (se 1 (by rfl) ⟨67244741, by rfl⟩ : syracuseStep 89659655 = 134489483) B134489483
theorem B15530777 : Blo 1435537 15530777 := bstep (se 2 (by rfl) ⟨5824041, by rfl⟩ : syracuseStep 15530777 = 11648083) B11648083
theorem B3635999 : Blo 1435537 3635999 := bstep (se 1 (by rfl) ⟨2726999, by rfl⟩ : syracuseStep 3635999 = 5453999) B5453999
theorem B11656223 : Blo 1435537 11656223 := bstep (se 1 (by rfl) ⟨8742167, by rfl⟩ : syracuseStep 11656223 = 17484335) B17484335
theorem B59773103 : Blo 1435537 59773103 := bstep (se 1 (by rfl) ⟨44829827, by rfl⟩ : syracuseStep 59773103 = 89659655) B89659655
theorem B139702553 : Blo 1435537 139702553 := bstep (se 2 (by rfl) ⟨52388457, by rfl⟩ : syracuseStep 139702553 = 104776915) B104776915
theorem B7770815 : Blo 1435537 7770815 := bstep (se 1 (by rfl) ⟨5828111, by rfl⟩ : syracuseStep 7770815 = 11656223) B11656223
theorem B10353851 : Blo 1435537 10353851 := bstep (se 1 (by rfl) ⟨7765388, by rfl⟩ : syracuseStep 10353851 = 15530777) B15530777
theorem B2423999 : Blo 1435537 2423999 := bstep (se 1 (by rfl) ⟨1817999, by rfl⟩ : syracuseStep 2423999 = 3635999) B3635999
theorem B2727607 : Blo 1435537 2727607 := bstep (se 1 (by rfl) ⟨2045705, by rfl⟩ : syracuseStep 2727607 = 4091411) B4091411
theorem B93135035 : Blo 1435537 93135035 := bstep (se 1 (by rfl) ⟨69851276, by rfl⟩ : syracuseStep 93135035 = 139702553) B139702553
theorem B1615999 : Blo 1435537 1615999 := bstep (se 1 (by rfl) ⟨1211999, by rfl⟩ : syracuseStep 1615999 = 2423999) B2423999
theorem B39848735 : Blo 1435537 39848735 := bstep (se 1 (by rfl) ⟨29886551, by rfl⟩ : syracuseStep 39848735 = 59773103) B59773103
theorem B5180543 : Blo 1435537 5180543 := bstep (se 1 (by rfl) ⟨3885407, by rfl⟩ : syracuseStep 5180543 = 7770815) B7770815
theorem B6902567 : Blo 1435537 6902567 := bstep (se 1 (by rfl) ⟨5176925, by rfl⟩ : syracuseStep 6902567 = 10353851) B10353851
theorem B3636809 : Blo 1435537 3636809 := bstep (se 2 (by rfl) ⟨1363803, by rfl⟩ : syracuseStep 3636809 = 2727607) B2727607
theorem B2154665 : Blo 1435537 2154665 := bstep (se 2 (by rfl) ⟨807999, by rfl⟩ : syracuseStep 2154665 = 1615999) B1615999
theorem B62090023 : Blo 1435537 62090023 := bstep (se 1 (by rfl) ⟨46567517, by rfl⟩ : syracuseStep 62090023 = 93135035) B93135035
theorem B3453695 : Blo 1435537 3453695 := bstep (se 1 (by rfl) ⟨2590271, by rfl⟩ : syracuseStep 3453695 = 5180543) B5180543
theorem B4601711 : Blo 1435537 4601711 := bstep (se 1 (by rfl) ⟨3451283, by rfl⟩ : syracuseStep 4601711 = 6902567) B6902567
theorem B26565823 : Blo 1435537 26565823 := bstep (se 1 (by rfl) ⟨19924367, by rfl⟩ : syracuseStep 26565823 = 39848735) B39848735
theorem B2424539 : Blo 1435537 2424539 := bstep (se 1 (by rfl) ⟨1818404, by rfl⟩ : syracuseStep 2424539 = 3636809) B3636809
theorem B2302463 : Blo 1435537 2302463 := bstep (se 1 (by rfl) ⟨1726847, by rfl⟩ : syracuseStep 2302463 = 3453695) B3453695
theorem B1616359 : Blo 1435537 1616359 := bstep (se 1 (by rfl) ⟨1212269, by rfl⟩ : syracuseStep 1616359 = 2424539) B2424539
theorem B1436443 : Blo 1435537 1436443 := bstep (se 1 (by rfl) ⟨1077332, by rfl⟩ : syracuseStep 1436443 = 2154665) B2154665
theorem B3067807 : Blo 1435537 3067807 := bstep (se 1 (by rfl) ⟨2300855, by rfl⟩ : syracuseStep 3067807 = 4601711) B4601711
theorem B82786697 : Blo 1435537 82786697 := bstep (se 2 (by rfl) ⟨31045011, by rfl⟩ : syracuseStep 82786697 = 62090023) B62090023
theorem B35421097 : Blo 1435537 35421097 := bstep (se 2 (by rfl) ⟨13282911, by rfl⟩ : syracuseStep 35421097 = 26565823) B26565823
theorem B2155145 : Blo 1435537 2155145 := bstep (se 2 (by rfl) ⟨808179, by rfl⟩ : syracuseStep 2155145 = 1616359) B1616359
theorem B47228129 : Blo 1435537 47228129 := bstep (se 2 (by rfl) ⟨17710548, by rfl⟩ : syracuseStep 47228129 = 35421097) B35421097
theorem B55191131 : Blo 1435537 55191131 := bstep (se 1 (by rfl) ⟨41393348, by rfl⟩ : syracuseStep 55191131 = 82786697) B82786697
theorem B4090409 : Blo 1435537 4090409 := bstep (se 2 (by rfl) ⟨1533903, by rfl⟩ : syracuseStep 4090409 = 3067807) B3067807
theorem B6139901 : Blo 1435537 6139901 := bstep (se 3 (by rfl) ⟨1151231, by rfl⟩ : syracuseStep 6139901 = 2302463) B2302463
theorem B1436763 : Blo 1435537 1436763 := bstep (se 1 (by rfl) ⟨1077572, by rfl⟩ : syracuseStep 1436763 = 2155145) B2155145
theorem B31485419 : Blo 1435537 31485419 := bstep (se 1 (by rfl) ⟨23614064, by rfl⟩ : syracuseStep 31485419 = 47228129) B47228129
theorem B36794087 : Blo 1435537 36794087 := bstep (se 1 (by rfl) ⟨27595565, by rfl⟩ : syracuseStep 36794087 = 55191131) B55191131
theorem B4093267 : Blo 1435537 4093267 := bstep (se 1 (by rfl) ⟨3069950, by rfl⟩ : syracuseStep 4093267 = 6139901) B6139901
theorem B2726939 : Blo 1435537 2726939 := bstep (se 1 (by rfl) ⟨2045204, by rfl⟩ : syracuseStep 2726939 = 4090409) B4090409
theorem B5457689 : Blo 1435537 5457689 := bstep (se 2 (by rfl) ⟨2046633, by rfl⟩ : syracuseStep 5457689 = 4093267) B4093267
theorem B20990279 : Blo 1435537 20990279 := bstep (se 1 (by rfl) ⟨15742709, by rfl⟩ : syracuseStep 20990279 = 31485419) B31485419
theorem B24529391 : Blo 1435537 24529391 := bstep (se 1 (by rfl) ⟨18397043, by rfl⟩ : syracuseStep 24529391 = 36794087) B36794087
theorem B1817959 : Blo 1435537 1817959 := bstep (se 1 (by rfl) ⟨1363469, by rfl⟩ : syracuseStep 1817959 = 2726939) B2726939
theorem B3638459 : Blo 1435537 3638459 := bstep (se 1 (by rfl) ⟨2728844, by rfl⟩ : syracuseStep 3638459 = 5457689) B5457689
theorem B16352927 : Blo 1435537 16352927 := bstep (se 1 (by rfl) ⟨12264695, by rfl⟩ : syracuseStep 16352927 = 24529391) B24529391
theorem B55974077 : Blo 1435537 55974077 := bstep (se 3 (by rfl) ⟨10495139, by rfl⟩ : syracuseStep 55974077 = 20990279) B20990279
theorem B2423945 : Blo 1435537 2423945 := bstep (se 2 (by rfl) ⟨908979, by rfl⟩ : syracuseStep 2423945 = 1817959) B1817959
theorem B2425639 : Blo 1435537 2425639 := bstep (se 1 (by rfl) ⟨1819229, by rfl⟩ : syracuseStep 2425639 = 3638459) B3638459
theorem B37316051 : Blo 1435537 37316051 := bstep (se 1 (by rfl) ⟨27987038, by rfl⟩ : syracuseStep 37316051 = 55974077) B55974077
theorem B1615963 : Blo 1435537 1615963 := bstep (se 1 (by rfl) ⟨1211972, by rfl⟩ : syracuseStep 1615963 = 2423945) B2423945
theorem B10901951 : Blo 1435537 10901951 := bstep (se 1 (by rfl) ⟨8176463, by rfl⟩ : syracuseStep 10901951 = 16352927) B16352927
theorem B2154617 : Blo 1435537 2154617 := bstep (se 2 (by rfl) ⟨807981, by rfl⟩ : syracuseStep 2154617 = 1615963) B1615963
theorem B7267967 : Blo 1435537 7267967 := bstep (se 1 (by rfl) ⟨5450975, by rfl⟩ : syracuseStep 7267967 = 10901951) B10901951
theorem B24877367 : Blo 1435537 24877367 := bstep (se 1 (by rfl) ⟨18658025, by rfl⟩ : syracuseStep 24877367 = 37316051) B37316051
theorem B3234185 : Blo 1435537 3234185 := bstep (se 2 (by rfl) ⟨1212819, by rfl⟩ : syracuseStep 3234185 = 2425639) B2425639
theorem B2156123 : Blo 1435537 2156123 := bstep (se 1 (by rfl) ⟨1617092, by rfl⟩ : syracuseStep 2156123 = 3234185) B3234185
theorem B1436411 : Blo 1435537 1436411 := bstep (se 1 (by rfl) ⟨1077308, by rfl⟩ : syracuseStep 1436411 = 2154617) B2154617
theorem B4845311 : Blo 1435537 4845311 := bstep (se 1 (by rfl) ⟨3633983, by rfl⟩ : syracuseStep 4845311 = 7267967) B7267967
theorem B16584911 : Blo 1435537 16584911 := bstep (se 1 (by rfl) ⟨12438683, by rfl⟩ : syracuseStep 16584911 = 24877367) B24877367
theorem B3230207 : Blo 1435537 3230207 := bstep (se 1 (by rfl) ⟨2422655, by rfl⟩ : syracuseStep 3230207 = 4845311) B4845311
theorem B1437415 : Blo 1435537 1437415 := bstep (se 1 (by rfl) ⟨1078061, by rfl⟩ : syracuseStep 1437415 = 2156123) B2156123
theorem B11056607 : Blo 1435537 11056607 := bstep (se 1 (by rfl) ⟨8292455, by rfl⟩ : syracuseStep 11056607 = 16584911) B16584911
theorem B7371071 : Blo 1435537 7371071 := bstep (se 1 (by rfl) ⟨5528303, by rfl⟩ : syracuseStep 7371071 = 11056607) B11056607
theorem B2153471 : Blo 1435537 2153471 := bstep (se 1 (by rfl) ⟨1615103, by rfl⟩ : syracuseStep 2153471 = 3230207) B3230207
theorem B1435647 : Blo 1435537 1435647 := bstep (se 1 (by rfl) ⟨1076735, by rfl⟩ : syracuseStep 1435647 = 2153471) B2153471
theorem B4914047 : Blo 1435537 4914047 := bstep (se 1 (by rfl) ⟨3685535, by rfl⟩ : syracuseStep 4914047 = 7371071) B7371071
theorem B13104125 : Blo 1435537 13104125 := bstep (se 3 (by rfl) ⟨2457023, by rfl⟩ : syracuseStep 13104125 = 4914047) B4914047
theorem B8736083 : Blo 1435537 8736083 := bstep (se 1 (by rfl) ⟨6552062, by rfl⟩ : syracuseStep 8736083 = 13104125) B13104125
theorem B5824055 : Blo 1435537 5824055 := bstep (se 1 (by rfl) ⟨4368041, by rfl⟩ : syracuseStep 5824055 = 8736083) B8736083
theorem B3882703 : Blo 1435537 3882703 := bstep (se 1 (by rfl) ⟨2912027, by rfl⟩ : syracuseStep 3882703 = 5824055) B5824055
theorem B5176937 : Blo 1435537 5176937 := bstep (se 2 (by rfl) ⟨1941351, by rfl⟩ : syracuseStep 5176937 = 3882703) B3882703
theorem B3451291 : Blo 1435537 3451291 := bstep (se 1 (by rfl) ⟨2588468, by rfl⟩ : syracuseStep 3451291 = 5176937) B5176937
theorem B18406885 : Blo 1435537 18406885 := bstep (se 4 (by rfl) ⟨1725645, by rfl⟩ : syracuseStep 18406885 = 3451291) B3451291
theorem B24542513 : Blo 1435537 24542513 := bstep (se 2 (by rfl) ⟨9203442, by rfl⟩ : syracuseStep 24542513 = 18406885) B18406885
theorem B16361675 : Blo 1435537 16361675 := bstep (se 1 (by rfl) ⟨12271256, by rfl⟩ : syracuseStep 16361675 = 24542513) B24542513
theorem B10907783 : Blo 1435537 10907783 := bstep (se 1 (by rfl) ⟨8180837, by rfl⟩ : syracuseStep 10907783 = 16361675) B16361675
theorem B7271855 : Blo 1435537 7271855 := bstep (se 1 (by rfl) ⟨5453891, by rfl⟩ : syracuseStep 7271855 = 10907783) B10907783
theorem B4847903 : Blo 1435537 4847903 := bstep (se 1 (by rfl) ⟨3635927, by rfl⟩ : syracuseStep 4847903 = 7271855) B7271855
theorem B3231935 : Blo 1435537 3231935 := bstep (se 1 (by rfl) ⟨2423951, by rfl⟩ : syracuseStep 3231935 = 4847903) B4847903
theorem B2154623 : Blo 1435537 2154623 := bstep (se 1 (by rfl) ⟨1615967, by rfl⟩ : syracuseStep 2154623 = 3231935) B3231935
theorem B1436415 : Blo 1435537 1436415 := bstep (se 1 (by rfl) ⟨1077311, by rfl⟩ : syracuseStep 1436415 = 2154623) B2154623

theorem C0 (j : ℕ) (h1 : 358884 ≤ j) (h2 : j ≤ 359383) : Blo 1435537 (4 * j + 3) := by
  interval_cases j
  · exact B1435539
  · exact B1435543
  · exact B1435547
  · exact B1435551
  · exact B1435555
  · exact B1435559
  · exact B1435563
  · exact B1435567
  · exact B1435571
  · exact B1435575
  · exact B1435579
  · exact B1435583
  · exact B1435587
  · exact B1435591
  · exact B1435595
  · exact B1435599
  · exact B1435603
  · exact B1435607
  · exact B1435611
  · exact B1435615
  · exact B1435619
  · exact B1435623
  · exact B1435627
  · exact B1435631
  · exact B1435635
  · exact B1435639
  · exact B1435643
  · exact B1435647
  · exact B1435651
  · exact B1435655
  · exact B1435659
  · exact B1435663
  · exact B1435667
  · exact B1435671
  · exact B1435675
  · exact B1435679
  · exact B1435683
  · exact B1435687
  · exact B1435691
  · exact B1435695
  · exact B1435699
  · exact B1435703
  · exact B1435707
  · exact B1435711
  · exact B1435715
  · exact B1435719
  · exact B1435723
  · exact B1435727
  · exact B1435731
  · exact B1435735
  · exact B1435739
  · exact B1435743
  · exact B1435747
  · exact B1435751
  · exact B1435755
  · exact B1435759
  · exact B1435763
  · exact B1435767
  · exact B1435771
  · exact B1435775
  · exact B1435779
  · exact B1435783
  · exact B1435787
  · exact B1435791
  · exact B1435795
  · exact B1435799
  · exact B1435803
  · exact B1435807
  · exact B1435811
  · exact B1435815
  · exact B1435819
  · exact B1435823
  · exact B1435827
  · exact B1435831
  · exact B1435835
  · exact B1435839
  · exact B1435843
  · exact B1435847
  · exact B1435851
  · exact B1435855
  · exact B1435859
  · exact B1435863
  · exact B1435867
  · exact B1435871
  · exact B1435875
  · exact B1435879
  · exact B1435883
  · exact B1435887
  · exact B1435891
  · exact B1435895
  · exact B1435899
  · exact B1435903
  · exact B1435907
  · exact B1435911
  · exact B1435915
  · exact B1435919
  · exact B1435923
  · exact B1435927
  · exact B1435931
  · exact B1435935
  · exact B1435939
  · exact B1435943
  · exact B1435947
  · exact B1435951
  · exact B1435955
  · exact B1435959
  · exact B1435963
  · exact B1435967
  · exact B1435971
  · exact B1435975
  · exact B1435979
  · exact B1435983
  · exact B1435987
  · exact B1435991
  · exact B1435995
  · exact B1435999
  · exact B1436003
  · exact B1436007
  · exact B1436011
  · exact B1436015
  · exact B1436019
  · exact B1436023
  · exact B1436027
  · exact B1436031
  · exact B1436035
  · exact B1436039
  · exact B1436043
  · exact B1436047
  · exact B1436051
  · exact B1436055
  · exact B1436059
  · exact B1436063
  · exact B1436067
  · exact B1436071
  · exact B1436075
  · exact B1436079
  · exact B1436083
  · exact B1436087
  · exact B1436091
  · exact B1436095
  · exact B1436099
  · exact B1436103
  · exact B1436107
  · exact B1436111
  · exact B1436115
  · exact B1436119
  · exact B1436123
  · exact B1436127
  · exact B1436131
  · exact B1436135
  · exact B1436139
  · exact B1436143
  · exact B1436147
  · exact B1436151
  · exact B1436155
  · exact B1436159
  · exact B1436163
  · exact B1436167
  · exact B1436171
  · exact B1436175
  · exact B1436179
  · exact B1436183
  · exact B1436187
  · exact B1436191
  · exact B1436195
  · exact B1436199
  · exact B1436203
  · exact B1436207
  · exact B1436211
  · exact B1436215
  · exact B1436219
  · exact B1436223
  · exact B1436227
  · exact B1436231
  · exact B1436235
  · exact B1436239
  · exact B1436243
  · exact B1436247
  · exact B1436251
  · exact B1436255
  · exact B1436259
  · exact B1436263
  · exact B1436267
  · exact B1436271
  · exact B1436275
  · exact B1436279
  · exact B1436283
  · exact B1436287
  · exact B1436291
  · exact B1436295
  · exact B1436299
  · exact B1436303
  · exact B1436307
  · exact B1436311
  · exact B1436315
  · exact B1436319
  · exact B1436323
  · exact B1436327
  · exact B1436331
  · exact B1436335
  · exact B1436339
  · exact B1436343
  · exact B1436347
  · exact B1436351
  · exact B1436355
  · exact B1436359
  · exact B1436363
  · exact B1436367
  · exact B1436371
  · exact B1436375
  · exact B1436379
  · exact B1436383
  · exact B1436387
  · exact B1436391
  · exact B1436395
  · exact B1436399
  · exact B1436403
  · exact B1436407
  · exact B1436411
  · exact B1436415
  · exact B1436419
  · exact B1436423
  · exact B1436427
  · exact B1436431
  · exact B1436435
  · exact B1436439
  · exact B1436443
  · exact B1436447
  · exact B1436451
  · exact B1436455
  · exact B1436459
  · exact B1436463
  · exact B1436467
  · exact B1436471
  · exact B1436475
  · exact B1436479
  · exact B1436483
  · exact B1436487
  · exact B1436491
  · exact B1436495
  · exact B1436499
  · exact B1436503
  · exact B1436507
  · exact B1436511
  · exact B1436515
  · exact B1436519
  · exact B1436523
  · exact B1436527
  · exact B1436531
  · exact B1436535
  · exact B1436539
  · exact B1436543
  · exact B1436547
  · exact B1436551
  · exact B1436555
  · exact B1436559
  · exact B1436563
  · exact B1436567
  · exact B1436571
  · exact B1436575
  · exact B1436579
  · exact B1436583
  · exact B1436587
  · exact B1436591
  · exact B1436595
  · exact B1436599
  · exact B1436603
  · exact B1436607
  · exact B1436611
  · exact B1436615
  · exact B1436619
  · exact B1436623
  · exact B1436627
  · exact B1436631
  · exact B1436635
  · exact B1436639
  · exact B1436643
  · exact B1436647
  · exact B1436651
  · exact B1436655
  · exact B1436659
  · exact B1436663
  · exact B1436667
  · exact B1436671
  · exact B1436675
  · exact B1436679
  · exact B1436683
  · exact B1436687
  · exact B1436691
  · exact B1436695
  · exact B1436699
  · exact B1436703
  · exact B1436707
  · exact B1436711
  · exact B1436715
  · exact B1436719
  · exact B1436723
  · exact B1436727
  · exact B1436731
  · exact B1436735
  · exact B1436739
  · exact B1436743
  · exact B1436747
  · exact B1436751
  · exact B1436755
  · exact B1436759
  · exact B1436763
  · exact B1436767
  · exact B1436771
  · exact B1436775
  · exact B1436779
  · exact B1436783
  · exact B1436787
  · exact B1436791
  · exact B1436795
  · exact B1436799
  · exact B1436803
  · exact B1436807
  · exact B1436811
  · exact B1436815
  · exact B1436819
  · exact B1436823
  · exact B1436827
  · exact B1436831
  · exact B1436835
  · exact B1436839
  · exact B1436843
  · exact B1436847
  · exact B1436851
  · exact B1436855
  · exact B1436859
  · exact B1436863
  · exact B1436867
  · exact B1436871
  · exact B1436875
  · exact B1436879
  · exact B1436883
  · exact B1436887
  · exact B1436891
  · exact B1436895
  · exact B1436899
  · exact B1436903
  · exact B1436907
  · exact B1436911
  · exact B1436915
  · exact B1436919
  · exact B1436923
  · exact B1436927
  · exact B1436931
  · exact B1436935
  · exact B1436939
  · exact B1436943
  · exact B1436947
  · exact B1436951
  · exact B1436955
  · exact B1436959
  · exact B1436963
  · exact B1436967
  · exact B1436971
  · exact B1436975
  · exact B1436979
  · exact B1436983
  · exact B1436987
  · exact B1436991
  · exact B1436995
  · exact B1436999
  · exact B1437003
  · exact B1437007
  · exact B1437011
  · exact B1437015
  · exact B1437019
  · exact B1437023
  · exact B1437027
  · exact B1437031
  · exact B1437035
  · exact B1437039
  · exact B1437043
  · exact B1437047
  · exact B1437051
  · exact B1437055
  · exact B1437059
  · exact B1437063
  · exact B1437067
  · exact B1437071
  · exact B1437075
  · exact B1437079
  · exact B1437083
  · exact B1437087
  · exact B1437091
  · exact B1437095
  · exact B1437099
  · exact B1437103
  · exact B1437107
  · exact B1437111
  · exact B1437115
  · exact B1437119
  · exact B1437123
  · exact B1437127
  · exact B1437131
  · exact B1437135
  · exact B1437139
  · exact B1437143
  · exact B1437147
  · exact B1437151
  · exact B1437155
  · exact B1437159
  · exact B1437163
  · exact B1437167
  · exact B1437171
  · exact B1437175
  · exact B1437179
  · exact B1437183
  · exact B1437187
  · exact B1437191
  · exact B1437195
  · exact B1437199
  · exact B1437203
  · exact B1437207
  · exact B1437211
  · exact B1437215
  · exact B1437219
  · exact B1437223
  · exact B1437227
  · exact B1437231
  · exact B1437235
  · exact B1437239
  · exact B1437243
  · exact B1437247
  · exact B1437251
  · exact B1437255
  · exact B1437259
  · exact B1437263
  · exact B1437267
  · exact B1437271
  · exact B1437275
  · exact B1437279
  · exact B1437283
  · exact B1437287
  · exact B1437291
  · exact B1437295
  · exact B1437299
  · exact B1437303
  · exact B1437307
  · exact B1437311
  · exact B1437315
  · exact B1437319
  · exact B1437323
  · exact B1437327
  · exact B1437331
  · exact B1437335
  · exact B1437339
  · exact B1437343
  · exact B1437347
  · exact B1437351
  · exact B1437355
  · exact B1437359
  · exact B1437363
  · exact B1437367
  · exact B1437371
  · exact B1437375
  · exact B1437379
  · exact B1437383
  · exact B1437387
  · exact B1437391
  · exact B1437395
  · exact B1437399
  · exact B1437403
  · exact B1437407
  · exact B1437411
  · exact B1437415
  · exact B1437419
  · exact B1437423
  · exact B1437427
  · exact B1437431
  · exact B1437435
  · exact B1437439
  · exact B1437443
  · exact B1437447
  · exact B1437451
  · exact B1437455
  · exact B1437459
  · exact B1437463
  · exact B1437467
  · exact B1437471
  · exact B1437475
  · exact B1437479
  · exact B1437483
  · exact B1437487
  · exact B1437491
  · exact B1437495
  · exact B1437499
  · exact B1437503
  · exact B1437507
  · exact B1437511
  · exact B1437515
  · exact B1437519
  · exact B1437523
  · exact B1437527
  · exact B1437531
  · exact B1437535

theorem solution (m : ℕ) (hlo : 1435537 ≤ m) (hhi : m ≤ 1437537) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 358884 ≤ j := by omega
    have hj2 : j ≤ 359383 := by omega
    have hb : Blo 1435537 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
