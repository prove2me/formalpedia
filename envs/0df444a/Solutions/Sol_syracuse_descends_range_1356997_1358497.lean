-- Prove2me | solution 1 for syracuse_descends_range_1356997_1358497
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:53.781089+00:00
-- url     : https://prove2.me/submissions/4ad58f6f-e073-48bc-91c2-0b4f2c9c0a32

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


theorem B3055661 : Blo 1356997 3055661 := bbase (se 3 (by rfl) ⟨572936, by rfl⟩ : syracuseStep 3055661 = 1145873) (by norm_num)
theorem B6873173 : Blo 1356997 6873173 := bbase (se 8 (by rfl) ⟨40272, by rfl⟩ : syracuseStep 6873173 = 80545) (by norm_num)
theorem B6701173 : Blo 1356997 6701173 := bbase (se 5 (by rfl) ⟨314117, by rfl⟩ : syracuseStep 6701173 = 628235) (by norm_num)
theorem B3055733 : Blo 1356997 3055733 := bbase (se 5 (by rfl) ⟨143237, by rfl⟩ : syracuseStep 3055733 = 286475) (by norm_num)
theorem B2900117 : Blo 1356997 2900117 := bbase (se 6 (by rfl) ⟨67971, by rfl⟩ : syracuseStep 2900117 = 135943) (by norm_num)
theorem B3670181 : Blo 1356997 3670181 := bbase (se 4 (by rfl) ⟨344079, by rfl⟩ : syracuseStep 3670181 = 688159) (by norm_num)
theorem B3055805 : Blo 1356997 3055805 := bbase (se 3 (by rfl) ⟨572963, by rfl⟩ : syracuseStep 3055805 = 1145927) (by norm_num)
theorem B4350149 : Blo 1356997 4350149 := bbase (se 4 (by rfl) ⟨407826, by rfl⟩ : syracuseStep 4350149 = 815653) (by norm_num)
theorem B5152997 : Blo 1356997 5152997 := bbase (se 4 (by rfl) ⟨483093, by rfl⟩ : syracuseStep 5152997 = 966187) (by norm_num)
theorem B1450229 : Blo 1356997 1450229 := bbase (se 5 (by rfl) ⟨67979, by rfl⟩ : syracuseStep 1450229 = 135959) (by norm_num)
theorem B3055877 : Blo 1356997 3055877 := bbase (se 4 (by rfl) ⟨286488, by rfl⟩ : syracuseStep 3055877 = 572977) (by norm_num)
theorem B1376561 : Blo 1356997 1376561 := bbase (se 2 (by rfl) ⟨516210, by rfl⟩ : syracuseStep 1376561 = 1032421) (by norm_num)
theorem B4350277 : Blo 1356997 4350277 := bbase (se 4 (by rfl) ⟨407838, by rfl⟩ : syracuseStep 4350277 = 815677) (by norm_num)
theorem B3055949 : Blo 1356997 3055949 := bbase (se 3 (by rfl) ⟨572990, by rfl⟩ : syracuseStep 3055949 = 1145981) (by norm_num)
theorem B1376609 : Blo 1356997 1376609 := bbase (se 2 (by rfl) ⟨516228, by rfl⟩ : syracuseStep 1376609 = 1032457) (by norm_num)
theorem B2064781 : Blo 1356997 2064781 := bbase (se 3 (by rfl) ⟨387146, by rfl⟩ : syracuseStep 2064781 = 774293) (by norm_num)
theorem B3056021 : Blo 1356997 3056021 := bbase (se 6 (by rfl) ⟨71625, by rfl⟩ : syracuseStep 3056021 = 143251) (by norm_num)
theorem B3096997 : Blo 1356997 3096997 := bbase (se 4 (by rfl) ⟨290343, by rfl⟩ : syracuseStep 3096997 = 580687) (by norm_num)
theorem B1933741 : Blo 1356997 1933741 := bbase (se 3 (by rfl) ⟨362576, by rfl⟩ : syracuseStep 1933741 = 725153) (by norm_num)
theorem B3867061 : Blo 1356997 3867061 := bbase (se 5 (by rfl) ⟨181268, by rfl⟩ : syracuseStep 3867061 = 362537) (by norm_num)
theorem B3056093 : Blo 1356997 3056093 := bbase (se 3 (by rfl) ⟨573017, by rfl⟩ : syracuseStep 3056093 = 1146035) (by norm_num)
theorem B5366245 : Blo 1356997 5366245 := bbase (se 4 (by rfl) ⟨503085, by rfl⟩ : syracuseStep 5366245 = 1006171) (by norm_num)
theorem B4645349 : Blo 1356997 4645349 := bbase (se 4 (by rfl) ⟨435501, by rfl⟩ : syracuseStep 4645349 = 871003) (by norm_num)
theorem B1450477 : Blo 1356997 1450477 := bbase (se 3 (by rfl) ⟨271964, by rfl⟩ : syracuseStep 1450477 = 543929) (by norm_num)
theorem B3056165 : Blo 1356997 3056165 := bbase (se 4 (by rfl) ⟨286515, by rfl⟩ : syracuseStep 3056165 = 573031) (by norm_num)
theorem B3056237 : Blo 1356997 3056237 := bbase (se 3 (by rfl) ⟨573044, by rfl⟩ : syracuseStep 3056237 = 1146089) (by norm_num)
theorem B1548941 : Blo 1356997 1548941 := bbase (se 3 (by rfl) ⟨290426, by rfl⟩ : syracuseStep 1548941 = 580853) (by norm_num)
theorem B3056309 : Blo 1356997 3056309 := bbase (se 5 (by rfl) ⟨143264, by rfl⟩ : syracuseStep 3056309 = 286529) (by norm_num)
theorem B6521573 : Blo 1356997 6521573 := bbase (se 4 (by rfl) ⟨611397, by rfl⟩ : syracuseStep 6521573 = 1222795) (by norm_num)
theorem B3056381 : Blo 1356997 3056381 := bbase (se 3 (by rfl) ⟨573071, by rfl⟩ : syracuseStep 3056381 = 1146143) (by norm_num)
theorem B4580117 : Blo 1356997 4580117 := bbase (se 6 (by rfl) ⟨107346, by rfl⟩ : syracuseStep 4580117 = 214693) (by norm_num)
theorem B1860389 : Blo 1356997 1860389 := bbase (se 4 (by rfl) ⟨174411, by rfl⟩ : syracuseStep 1860389 = 348823) (by norm_num)
theorem B3056453 : Blo 1356997 3056453 := bbase (se 4 (by rfl) ⟨286542, by rfl⟩ : syracuseStep 3056453 = 573085) (by norm_num)
theorem B3056525 : Blo 1356997 3056525 := bbase (se 3 (by rfl) ⟨573098, by rfl⟩ : syracuseStep 3056525 = 1146197) (by norm_num)
theorem B3056597 : Blo 1356997 3056597 := bbase (se 7 (by rfl) ⟨35819, by rfl⟩ : syracuseStep 3056597 = 71639) (by norm_num)
theorem B1631225 : Blo 1356997 1631225 := bbase (se 2 (by rfl) ⟨611709, by rfl⟩ : syracuseStep 1631225 = 1223419) (by norm_num)
theorem B2901005 : Blo 1356997 2901005 := bbase (se 3 (by rfl) ⟨543938, by rfl⟩ : syracuseStep 2901005 = 1087877) (by norm_num)
theorem B7734325 : Blo 1356997 7734325 := bbase (se 5 (by rfl) ⟨362546, by rfl⟩ : syracuseStep 7734325 = 725093) (by norm_num)
theorem B4580549 : Blo 1356997 4580549 := bbase (se 4 (by rfl) ⟨429426, by rfl⟩ : syracuseStep 4580549 = 858853) (by norm_num)
theorem B2901253 : Blo 1356997 2901253 := bbase (se 4 (by rfl) ⟨271992, by rfl⟩ : syracuseStep 2901253 = 543985) (by norm_num)
theorem B3671381 : Blo 1356997 3671381 := bbase (se 12 (by rfl) ⟨1344, by rfl⟩ : syracuseStep 3671381 = 2689) (by norm_num)
theorem B6874469 : Blo 1356997 6874469 := bbase (se 4 (by rfl) ⟨644481, by rfl⟩ : syracuseStep 6874469 = 1288963) (by norm_num)
theorem B3868165 : Blo 1356997 3868165 := bbase (se 4 (by rfl) ⟨362640, by rfl⟩ : syracuseStep 3868165 = 725281) (by norm_num)
theorem B10315349 : Blo 1356997 10315349 := bbase (se 8 (by rfl) ⟨60441, by rfl⟩ : syracuseStep 10315349 = 120883) (by norm_num)
theorem B4580981 : Blo 1356997 4580981 := bbase (se 5 (by rfl) ⟨214733, by rfl⟩ : syracuseStep 4580981 = 429467) (by norm_num)
theorem B5801701 : Blo 1356997 5801701 := bbase (se 4 (by rfl) ⟨543909, by rfl⟩ : syracuseStep 5801701 = 1087819) (by norm_num)
theorem B10307573 : Blo 1356997 10307573 := bbase (se 5 (by rfl) ⟨483167, by rfl⟩ : syracuseStep 10307573 = 966335) (by norm_num)
theorem B3483661 : Blo 1356997 3483661 := bbase (se 3 (by rfl) ⟨653186, by rfl⟩ : syracuseStep 3483661 = 1306373) (by norm_num)
theorem B4581413 : Blo 1356997 4581413 := bbase (se 4 (by rfl) ⟨429507, by rfl⟩ : syracuseStep 4581413 = 859015) (by norm_num)
theorem B5155109 : Blo 1356997 5155109 := bbase (se 4 (by rfl) ⟨483291, by rfl⟩ : syracuseStep 5155109 = 966583) (by norm_num)
theorem B3262765 : Blo 1356997 3262765 := bbase (se 3 (by rfl) ⟨611768, by rfl⟩ : syracuseStep 3262765 = 1223537) (by norm_num)
theorem B3434957 : Blo 1356997 3434957 := bbase (se 3 (by rfl) ⟨644054, by rfl⟩ : syracuseStep 3434957 = 1288109) (by norm_num)
theorem B4581845 : Blo 1356997 4581845 := bbase (se 7 (by rfl) ⟨53693, by rfl⟩ : syracuseStep 4581845 = 107387) (by norm_num)
theorem B3262997 : Blo 1356997 3262997 := bbase (se 6 (by rfl) ⟨76476, by rfl⟩ : syracuseStep 3262997 = 152953) (by norm_num)
theorem B2648621 : Blo 1356997 2648621 := bbase (se 3 (by rfl) ⟨496616, by rfl⟩ : syracuseStep 2648621 = 993233) (by norm_num)
theorem B5155397 : Blo 1356997 5155397 := bbase (se 4 (by rfl) ⟨483318, by rfl⟩ : syracuseStep 5155397 = 966637) (by norm_num)
theorem B6875765 : Blo 1356997 6875765 := bbase (se 5 (by rfl) ⟨322301, by rfl⟩ : syracuseStep 6875765 = 644603) (by norm_num)
theorem B3435149 : Blo 1356997 3435149 := bbase (se 3 (by rfl) ⟨644090, by rfl⟩ : syracuseStep 3435149 = 1288181) (by norm_num)
theorem B3263141 : Blo 1356997 3263141 := bbase (se 4 (by rfl) ⟨305919, by rfl⟩ : syracuseStep 3263141 = 611839) (by norm_num)
theorem B2321237 : Blo 1356997 2321237 := bbase (se 9 (by rfl) ⟨6800, by rfl⟩ : syracuseStep 2321237 = 13601) (by norm_num)
theorem B1526629 : Blo 1356997 1526629 := bbase (se 4 (by rfl) ⟨143121, by rfl⟩ : syracuseStep 1526629 = 286243) (by norm_num)
theorem B4582277 : Blo 1356997 4582277 := bbase (se 4 (by rfl) ⟨429588, by rfl⟩ : syracuseStep 4582277 = 859177) (by norm_num)
theorem B1526665 : Blo 1356997 1526665 := bbase (se 2 (by rfl) ⟨572499, by rfl⟩ : syracuseStep 1526665 = 1144999) (by norm_num)
theorem B3263381 : Blo 1356997 3263381 := bbase (se 6 (by rfl) ⟨76485, by rfl⟩ : syracuseStep 3263381 = 152971) (by norm_num)
theorem B1526701 : Blo 1356997 1526701 := bbase (se 3 (by rfl) ⟨286256, by rfl⟩ : syracuseStep 1526701 = 572513) (by norm_num)
theorem B1526737 : Blo 1356997 1526737 := bbase (se 2 (by rfl) ⟨572526, by rfl⟩ : syracuseStep 1526737 = 1145053) (by norm_num)
theorem B3435493 : Blo 1356997 3435493 := bbase (se 4 (by rfl) ⟨322077, by rfl⟩ : syracuseStep 3435493 = 644155) (by norm_num)
theorem B1526773 : Blo 1356997 1526773 := bbase (se 5 (by rfl) ⟨71567, by rfl⟩ : syracuseStep 1526773 = 143135) (by norm_num)
theorem B7736309 : Blo 1356997 7736309 := bbase (se 5 (by rfl) ⟨362639, by rfl⟩ : syracuseStep 7736309 = 725279) (by norm_num)
theorem B1526809 : Blo 1356997 1526809 := bbase (se 2 (by rfl) ⟨572553, by rfl⟩ : syracuseStep 1526809 = 1145107) (by norm_num)
theorem B1526845 : Blo 1356997 1526845 := bbase (se 3 (by rfl) ⟨286283, by rfl⟩ : syracuseStep 1526845 = 572567) (by norm_num)
theorem B3435605 : Blo 1356997 3435605 := bbase (se 8 (by rfl) ⟨20130, by rfl⟩ : syracuseStep 3435605 = 40261) (by norm_num)
theorem B1526881 : Blo 1356997 1526881 := bbase (se 2 (by rfl) ⟨572580, by rfl⟩ : syracuseStep 1526881 = 1145161) (by norm_num)
theorem B1526917 : Blo 1356997 1526917 := bbase (se 4 (by rfl) ⟨143148, by rfl⟩ : syracuseStep 1526917 = 286297) (by norm_num)
theorem B1526953 : Blo 1356997 1526953 := bbase (se 2 (by rfl) ⟨572607, by rfl⟩ : syracuseStep 1526953 = 1145215) (by norm_num)
theorem B8694965 : Blo 1356997 8694965 := bbase (se 5 (by rfl) ⟨407576, by rfl⟩ : syracuseStep 8694965 = 815153) (by norm_num)
theorem B6196421 : Blo 1356997 6196421 := bbase (se 4 (by rfl) ⟨580914, by rfl⟩ : syracuseStep 6196421 = 1161829) (by norm_num)
theorem B1526989 : Blo 1356997 1526989 := bbase (se 3 (by rfl) ⟨286310, by rfl⟩ : syracuseStep 1526989 = 572621) (by norm_num)
theorem B1527025 : Blo 1356997 1527025 := bbase (se 2 (by rfl) ⟨572634, by rfl⟩ : syracuseStep 1527025 = 1145269) (by norm_num)
theorem B2174197 : Blo 1356997 2174197 := bbase (se 5 (by rfl) ⟨101915, by rfl⟩ : syracuseStep 2174197 = 203831) (by norm_num)
theorem B3435797 : Blo 1356997 3435797 := bbase (se 6 (by rfl) ⟨80526, by rfl⟩ : syracuseStep 3435797 = 161053) (by norm_num)
theorem B1527061 : Blo 1356997 1527061 := bbase (se 6 (by rfl) ⟨35790, by rfl⟩ : syracuseStep 1527061 = 71581) (by norm_num)
theorem B4582709 : Blo 1356997 4582709 := bbase (se 5 (by rfl) ⟨214814, by rfl⟩ : syracuseStep 4582709 = 429629) (by norm_num)
theorem B1527097 : Blo 1356997 1527097 := bbase (se 2 (by rfl) ⟨572661, by rfl⟩ : syracuseStep 1527097 = 1145323) (by norm_num)
theorem B1527133 : Blo 1356997 1527133 := bbase (se 3 (by rfl) ⟨286337, by rfl⟩ : syracuseStep 1527133 = 572675) (by norm_num)
theorem B2649437 : Blo 1356997 2649437 := bbase (se 3 (by rfl) ⟨496769, by rfl⟩ : syracuseStep 2649437 = 993539) (by norm_num)
theorem B1527169 : Blo 1356997 1527169 := bbase (se 2 (by rfl) ⟨572688, by rfl⟩ : syracuseStep 1527169 = 1145377) (by norm_num)
theorem B1527205 : Blo 1356997 1527205 := bbase (se 4 (by rfl) ⟨143175, by rfl⟩ : syracuseStep 1527205 = 286351) (by norm_num)
theorem B1527241 : Blo 1356997 1527241 := bbase (se 2 (by rfl) ⟨572715, by rfl⟩ : syracuseStep 1527241 = 1145431) (by norm_num)
theorem B1527277 : Blo 1356997 1527277 := bbase (se 3 (by rfl) ⟨286364, by rfl⟩ : syracuseStep 1527277 = 572729) (by norm_num)
theorem B1527313 : Blo 1356997 1527313 := bbase (se 2 (by rfl) ⟨572742, by rfl⟩ : syracuseStep 1527313 = 1145485) (by norm_num)
theorem B1527349 : Blo 1356997 1527349 := bbase (se 5 (by rfl) ⟨71594, by rfl⟩ : syracuseStep 1527349 = 143189) (by norm_num)
theorem B1527385 : Blo 1356997 1527385 := bbase (se 2 (by rfl) ⟨572769, by rfl⟩ : syracuseStep 1527385 = 1145539) (by norm_num)
theorem B3436141 : Blo 1356997 3436141 := bbase (se 3 (by rfl) ⟨644276, by rfl⟩ : syracuseStep 3436141 = 1288553) (by norm_num)
theorem B1527421 : Blo 1356997 1527421 := bbase (se 3 (by rfl) ⟨286391, by rfl⟩ : syracuseStep 1527421 = 572783) (by norm_num)
theorem B1527457 : Blo 1356997 1527457 := bbase (se 2 (by rfl) ⟨572796, by rfl⟩ : syracuseStep 1527457 = 1145593) (by norm_num)
theorem B1527493 : Blo 1356997 1527493 := bbase (se 4 (by rfl) ⟨143202, by rfl⟩ : syracuseStep 1527493 = 286405) (by norm_num)
theorem B3436253 : Blo 1356997 3436253 := bbase (se 3 (by rfl) ⟨644297, by rfl⟩ : syracuseStep 3436253 = 1288595) (by norm_num)
theorem B4583141 : Blo 1356997 4583141 := bbase (se 4 (by rfl) ⟨429669, by rfl⟩ : syracuseStep 4583141 = 859339) (by norm_num)
theorem B5156581 : Blo 1356997 5156581 := bbase (se 4 (by rfl) ⟨483429, by rfl⟩ : syracuseStep 5156581 = 966859) (by norm_num)
theorem B1527529 : Blo 1356997 1527529 := bbase (se 2 (by rfl) ⟨572823, by rfl⟩ : syracuseStep 1527529 = 1145647) (by norm_num)
theorem B1527565 : Blo 1356997 1527565 := bbase (se 3 (by rfl) ⟨286418, by rfl⟩ : syracuseStep 1527565 = 572837) (by norm_num)
theorem B3018541 : Blo 1356997 3018541 := bbase (se 3 (by rfl) ⟨565976, by rfl⟩ : syracuseStep 3018541 = 1131953) (by norm_num)
theorem B1527601 : Blo 1356997 1527601 := bbase (se 2 (by rfl) ⟨572850, by rfl⟩ : syracuseStep 1527601 = 1145701) (by norm_num)
theorem B2035517 : Blo 1356997 2035517 := bbase (se 3 (by rfl) ⟨381659, by rfl⟩ : syracuseStep 2035517 = 763319) (by norm_num)
theorem B2035541 : Blo 1356997 2035541 := bbase (se 9 (by rfl) ⟨5963, by rfl⟩ : syracuseStep 2035541 = 11927) (by norm_num)
theorem B1527637 : Blo 1356997 1527637 := bbase (se 9 (by rfl) ⟨4475, by rfl⟩ : syracuseStep 1527637 = 8951) (by norm_num)
theorem B2035565 : Blo 1356997 2035565 := bbase (se 3 (by rfl) ⟨381668, by rfl⟩ : syracuseStep 2035565 = 763337) (by norm_num)
theorem B1527673 : Blo 1356997 1527673 := bbase (se 2 (by rfl) ⟨572877, by rfl⟩ : syracuseStep 1527673 = 1145755) (by norm_num)
theorem B2035589 : Blo 1356997 2035589 := bbase (se 4 (by rfl) ⟨190836, by rfl⟩ : syracuseStep 2035589 = 381673) (by norm_num)
theorem B1765253 : Blo 1356997 1765253 := bbase (se 4 (by rfl) ⟨165492, by rfl⟩ : syracuseStep 1765253 = 330985) (by norm_num)
theorem B4894597 : Blo 1356997 4894597 := bbase (se 4 (by rfl) ⟨458868, by rfl⟩ : syracuseStep 4894597 = 917737) (by norm_num)
theorem B6877061 : Blo 1356997 6877061 := bbase (se 4 (by rfl) ⟨644724, by rfl⟩ : syracuseStep 6877061 = 1289449) (by norm_num)
theorem B2174869 : Blo 1356997 2174869 := bbase (se 6 (by rfl) ⟨50973, by rfl⟩ : syracuseStep 2174869 = 101947) (by norm_num)
theorem B2035613 : Blo 1356997 2035613 := bbase (se 3 (by rfl) ⟨381677, by rfl⟩ : syracuseStep 2035613 = 763355) (by norm_num)
theorem B3436445 : Blo 1356997 3436445 := bbase (se 3 (by rfl) ⟨644333, by rfl⟩ : syracuseStep 3436445 = 1288667) (by norm_num)
theorem B1527709 : Blo 1356997 1527709 := bbase (se 3 (by rfl) ⟨286445, by rfl⟩ : syracuseStep 1527709 = 572891) (by norm_num)
theorem B2035637 : Blo 1356997 2035637 := bbase (se 5 (by rfl) ⟨95420, by rfl⟩ : syracuseStep 2035637 = 190841) (by norm_num)
theorem B1527745 : Blo 1356997 1527745 := bbase (se 2 (by rfl) ⟨572904, by rfl⟩ : syracuseStep 1527745 = 1145809) (by norm_num)
theorem B2035661 : Blo 1356997 2035661 := bbase (se 3 (by rfl) ⟨381686, by rfl⟩ : syracuseStep 2035661 = 763373) (by norm_num)
theorem B2035685 : Blo 1356997 2035685 := bbase (se 4 (by rfl) ⟨190845, by rfl⟩ : syracuseStep 2035685 = 381691) (by norm_num)
theorem B1527781 : Blo 1356997 1527781 := bbase (se 4 (by rfl) ⟨143229, by rfl⟩ : syracuseStep 1527781 = 286459) (by norm_num)
theorem B2035709 : Blo 1356997 2035709 := bbase (se 3 (by rfl) ⟨381695, by rfl⟩ : syracuseStep 2035709 = 763391) (by norm_num)
theorem B1527817 : Blo 1356997 1527817 := bbase (se 2 (by rfl) ⟨572931, by rfl⟩ : syracuseStep 1527817 = 1145863) (by norm_num)
theorem B2035733 : Blo 1356997 2035733 := bbase (se 6 (by rfl) ⟨47712, by rfl⟩ : syracuseStep 2035733 = 95425) (by norm_num)
theorem B5156885 : Blo 1356997 5156885 := bbase (se 6 (by rfl) ⟨120864, by rfl⟩ : syracuseStep 5156885 = 241729) (by norm_num)
theorem B2035757 : Blo 1356997 2035757 := bbase (se 3 (by rfl) ⟨381704, by rfl⟩ : syracuseStep 2035757 = 763409) (by norm_num)
theorem B1527853 : Blo 1356997 1527853 := bbase (se 3 (by rfl) ⟨286472, by rfl⟩ : syracuseStep 1527853 = 572945) (by norm_num)
theorem B2035781 : Blo 1356997 2035781 := bbase (se 4 (by rfl) ⟨190854, by rfl⟩ : syracuseStep 2035781 = 381709) (by norm_num)
theorem B2576461 : Blo 1356997 2576461 := bbase (se 3 (by rfl) ⟨483086, by rfl⟩ : syracuseStep 2576461 = 966173) (by norm_num)
theorem B1527889 : Blo 1356997 1527889 := bbase (se 2 (by rfl) ⟨572958, by rfl⟩ : syracuseStep 1527889 = 1145917) (by norm_num)
theorem B2035805 : Blo 1356997 2035805 := bbase (se 3 (by rfl) ⟨381713, by rfl⟩ : syracuseStep 2035805 = 763427) (by norm_num)
theorem B2035829 : Blo 1356997 2035829 := bbase (se 5 (by rfl) ⟨95429, by rfl⟩ : syracuseStep 2035829 = 190859) (by norm_num)
theorem B1527925 : Blo 1356997 1527925 := bbase (se 5 (by rfl) ⟨71621, by rfl⟩ : syracuseStep 1527925 = 143243) (by norm_num)
theorem B2035853 : Blo 1356997 2035853 := bbase (se 3 (by rfl) ⟨381722, by rfl⟩ : syracuseStep 2035853 = 763445) (by norm_num)
theorem B4583573 : Blo 1356997 4583573 := bbase (se 6 (by rfl) ⟨107427, by rfl⟩ : syracuseStep 4583573 = 214855) (by norm_num)
theorem B1527961 : Blo 1356997 1527961 := bbase (se 2 (by rfl) ⟨572985, by rfl⟩ : syracuseStep 1527961 = 1145971) (by norm_num)
theorem B2035877 : Blo 1356997 2035877 := bbase (se 4 (by rfl) ⟨190863, by rfl⟩ : syracuseStep 2035877 = 381727) (by norm_num)
theorem B2035901 : Blo 1356997 2035901 := bbase (se 3 (by rfl) ⟨381731, by rfl⟩ : syracuseStep 2035901 = 763463) (by norm_num)
theorem B1675453 : Blo 1356997 1675453 := bbase (se 3 (by rfl) ⟨314147, by rfl⟩ : syracuseStep 1675453 = 628295) (by norm_num)
theorem B1527997 : Blo 1356997 1527997 := bbase (se 3 (by rfl) ⟨286499, by rfl⟩ : syracuseStep 1527997 = 572999) (by norm_num)
theorem B2035925 : Blo 1356997 2035925 := bbase (se 7 (by rfl) ⟨23858, by rfl⟩ : syracuseStep 2035925 = 47717) (by norm_num)
theorem B2576605 : Blo 1356997 2576605 := bbase (se 3 (by rfl) ⟨483113, by rfl⟩ : syracuseStep 2576605 = 966227) (by norm_num)
theorem B1528033 : Blo 1356997 1528033 := bbase (se 2 (by rfl) ⟨573012, by rfl⟩ : syracuseStep 1528033 = 1146025) (by norm_num)
theorem B2035949 : Blo 1356997 2035949 := bbase (se 3 (by rfl) ⟨381740, by rfl⟩ : syracuseStep 2035949 = 763481) (by norm_num)
theorem B2355437 : Blo 1356997 2355437 := bbase (se 3 (by rfl) ⟨441644, by rfl⟩ : syracuseStep 2355437 = 883289) (by norm_num)
theorem B3436789 : Blo 1356997 3436789 := bbase (se 5 (by rfl) ⟨161099, by rfl⟩ : syracuseStep 3436789 = 322199) (by norm_num)
theorem B2035973 : Blo 1356997 2035973 := bbase (se 4 (by rfl) ⟨190872, by rfl⟩ : syracuseStep 2035973 = 381745) (by norm_num)
theorem B1528069 : Blo 1356997 1528069 := bbase (se 4 (by rfl) ⟨143256, by rfl⟩ : syracuseStep 1528069 = 286513) (by norm_num)
theorem B2035997 : Blo 1356997 2035997 := bbase (se 3 (by rfl) ⟨381749, by rfl⟩ : syracuseStep 2035997 = 763499) (by norm_num)
theorem B1528105 : Blo 1356997 1528105 := bbase (se 2 (by rfl) ⟨573039, by rfl⟩ : syracuseStep 1528105 = 1146079) (by norm_num)
theorem B2036021 : Blo 1356997 2036021 := bbase (se 5 (by rfl) ⟨95438, by rfl⟩ : syracuseStep 2036021 = 190877) (by norm_num)
theorem B2036045 : Blo 1356997 2036045 := bbase (se 3 (by rfl) ⟨381758, by rfl⟩ : syracuseStep 2036045 = 763517) (by norm_num)
theorem B1528141 : Blo 1356997 1528141 := bbase (se 3 (by rfl) ⟨286526, by rfl⟩ : syracuseStep 1528141 = 573053) (by norm_num)
theorem B2036069 : Blo 1356997 2036069 := bbase (se 4 (by rfl) ⟨190881, by rfl⟩ : syracuseStep 2036069 = 381763) (by norm_num)
theorem B3436901 : Blo 1356997 3436901 := bbase (se 4 (by rfl) ⟨322209, by rfl⟩ : syracuseStep 3436901 = 644419) (by norm_num)
theorem B1528177 : Blo 1356997 1528177 := bbase (se 2 (by rfl) ⟨573066, by rfl⟩ : syracuseStep 1528177 = 1146133) (by norm_num)
theorem B2290045 : Blo 1356997 2290045 := bbase (se 3 (by rfl) ⟨429383, by rfl⟩ : syracuseStep 2290045 = 858767) (by norm_num)
theorem B2576765 : Blo 1356997 2576765 := bbase (se 3 (by rfl) ⟨483143, by rfl⟩ : syracuseStep 2576765 = 966287) (by norm_num)
theorem B2036093 : Blo 1356997 2036093 := bbase (se 3 (by rfl) ⟨381767, by rfl⟩ : syracuseStep 2036093 = 763535) (by norm_num)
theorem B2036117 : Blo 1356997 2036117 := bbase (se 6 (by rfl) ⟨47721, by rfl⟩ : syracuseStep 2036117 = 95443) (by norm_num)
theorem B1528213 : Blo 1356997 1528213 := bbase (se 6 (by rfl) ⟨35817, by rfl⟩ : syracuseStep 1528213 = 71635) (by norm_num)
theorem B2036141 : Blo 1356997 2036141 := bbase (se 3 (by rfl) ⟨381776, by rfl⟩ : syracuseStep 2036141 = 763553) (by norm_num)
theorem B1528249 : Blo 1356997 1528249 := bbase (se 2 (by rfl) ⟨573093, by rfl⟩ : syracuseStep 1528249 = 1146187) (by norm_num)
theorem B2036165 : Blo 1356997 2036165 := bbase (se 4 (by rfl) ⟨190890, by rfl⟩ : syracuseStep 2036165 = 381781) (by norm_num)
theorem B2290133 : Blo 1356997 2290133 := bbase (se 7 (by rfl) ⟨26837, by rfl⟩ : syracuseStep 2290133 = 53675) (by norm_num)
theorem B2036189 : Blo 1356997 2036189 := bbase (se 3 (by rfl) ⟨381785, by rfl⟩ : syracuseStep 2036189 = 763571) (by norm_num)
theorem B1528285 : Blo 1356997 1528285 := bbase (se 3 (by rfl) ⟨286553, by rfl⟩ : syracuseStep 1528285 = 573107) (by norm_num)
theorem B2036213 : Blo 1356997 2036213 := bbase (se 5 (by rfl) ⟨95447, by rfl⟩ : syracuseStep 2036213 = 190895) (by norm_num)
theorem B2576909 : Blo 1356997 2576909 := bbase (se 3 (by rfl) ⟨483170, by rfl⟩ : syracuseStep 2576909 = 966341) (by norm_num)
theorem B2036237 : Blo 1356997 2036237 := bbase (se 3 (by rfl) ⟨381794, by rfl⟩ : syracuseStep 2036237 = 763589) (by norm_num)
theorem B2036261 : Blo 1356997 2036261 := bbase (se 4 (by rfl) ⟨190899, by rfl⟩ : syracuseStep 2036261 = 381799) (by norm_num)
theorem B3437093 : Blo 1356997 3437093 := bbase (se 4 (by rfl) ⟨322227, by rfl⟩ : syracuseStep 3437093 = 644455) (by norm_num)
theorem B2036285 : Blo 1356997 2036285 := bbase (se 3 (by rfl) ⟨381803, by rfl⟩ : syracuseStep 2036285 = 763607) (by norm_num)
theorem B5222981 : Blo 1356997 5222981 := bbase (se 4 (by rfl) ⟨489654, by rfl⟩ : syracuseStep 5222981 = 979309) (by norm_num)
theorem B4584005 : Blo 1356997 4584005 := bbase (se 4 (by rfl) ⟨429750, by rfl⟩ : syracuseStep 4584005 = 859501) (by norm_num)
theorem B2290261 : Blo 1356997 2290261 := bbase (se 8 (by rfl) ⟨13419, by rfl⟩ : syracuseStep 2290261 = 26839) (by norm_num)
theorem B2036309 : Blo 1356997 2036309 := bbase (se 8 (by rfl) ⟨11931, by rfl⟩ : syracuseStep 2036309 = 23863) (by norm_num)
theorem B2036333 : Blo 1356997 2036333 := bbase (se 3 (by rfl) ⟨381812, by rfl⟩ : syracuseStep 2036333 = 763625) (by norm_num)
theorem B2036357 : Blo 1356997 2036357 := bbase (se 4 (by rfl) ⟨190908, by rfl⟩ : syracuseStep 2036357 = 381817) (by norm_num)
theorem B1766021 : Blo 1356997 1766021 := bbase (se 4 (by rfl) ⟨165564, by rfl⟩ : syracuseStep 1766021 = 331129) (by norm_num)
theorem B2036381 : Blo 1356997 2036381 := bbase (se 3 (by rfl) ⟨381821, by rfl⟩ : syracuseStep 2036381 = 763643) (by norm_num)
theorem B2290349 : Blo 1356997 2290349 := bbase (se 3 (by rfl) ⟨429440, by rfl⟩ : syracuseStep 2290349 = 858881) (by norm_num)
theorem B2036405 : Blo 1356997 2036405 := bbase (se 5 (by rfl) ⟨95456, by rfl⟩ : syracuseStep 2036405 = 190913) (by norm_num)
theorem B2036429 : Blo 1356997 2036429 := bbase (se 3 (by rfl) ⟨381830, by rfl⟩ : syracuseStep 2036429 = 763661) (by norm_num)
theorem B2036453 : Blo 1356997 2036453 := bbase (se 4 (by rfl) ⟨190917, by rfl⟩ : syracuseStep 2036453 = 381835) (by norm_num)
theorem B2036477 : Blo 1356997 2036477 := bbase (se 3 (by rfl) ⟨381839, by rfl⟩ : syracuseStep 2036477 = 763679) (by norm_num)
theorem B5796629 : Blo 1356997 5796629 := bbase (se 6 (by rfl) ⟨135858, by rfl⟩ : syracuseStep 5796629 = 271717) (by norm_num)
theorem B2036501 : Blo 1356997 2036501 := bbase (se 6 (by rfl) ⟨47730, by rfl⟩ : syracuseStep 2036501 = 95461) (by norm_num)
theorem B2446109 : Blo 1356997 2446109 := bbase (se 3 (by rfl) ⟨458645, by rfl⟩ : syracuseStep 2446109 = 917291) (by norm_num)
theorem B2290477 : Blo 1356997 2290477 := bbase (se 3 (by rfl) ⟨429464, by rfl⟩ : syracuseStep 2290477 = 858929) (by norm_num)
theorem B2577197 : Blo 1356997 2577197 := bbase (se 3 (by rfl) ⟨483224, by rfl⟩ : syracuseStep 2577197 = 966449) (by norm_num)
theorem B2036525 : Blo 1356997 2036525 := bbase (se 3 (by rfl) ⟨381848, by rfl⟩ : syracuseStep 2036525 = 763697) (by norm_num)
theorem B2036549 : Blo 1356997 2036549 := bbase (se 4 (by rfl) ⟨190926, by rfl⟩ : syracuseStep 2036549 = 381853) (by norm_num)
theorem B2036573 : Blo 1356997 2036573 := bbase (se 3 (by rfl) ⟨381857, by rfl⟩ : syracuseStep 2036573 = 763715) (by norm_num)
theorem B2036597 : Blo 1356997 2036597 := bbase (se 5 (by rfl) ⟨95465, by rfl⟩ : syracuseStep 2036597 = 190931) (by norm_num)
theorem B3437437 : Blo 1356997 3437437 := bbase (se 3 (by rfl) ⟨644519, by rfl⟩ : syracuseStep 3437437 = 1289039) (by norm_num)
theorem B2175869 : Blo 1356997 2175869 := bbase (se 3 (by rfl) ⟨407975, by rfl⟩ : syracuseStep 2175869 = 815951) (by norm_num)
theorem B2290565 : Blo 1356997 2290565 := bbase (se 4 (by rfl) ⟨214740, by rfl⟩ : syracuseStep 2290565 = 429481) (by norm_num)
theorem B2036621 : Blo 1356997 2036621 := bbase (se 3 (by rfl) ⟨381866, by rfl⟩ : syracuseStep 2036621 = 763733) (by norm_num)
theorem B2036645 : Blo 1356997 2036645 := bbase (se 4 (by rfl) ⟨190935, by rfl⟩ : syracuseStep 2036645 = 381871) (by norm_num)
theorem B2036669 : Blo 1356997 2036669 := bbase (se 3 (by rfl) ⟨381875, by rfl⟩ : syracuseStep 2036669 = 763751) (by norm_num)
theorem B2577349 : Blo 1356997 2577349 := bbase (se 4 (by rfl) ⟨241626, by rfl⟩ : syracuseStep 2577349 = 483253) (by norm_num)
theorem B2036693 : Blo 1356997 2036693 := bbase (se 7 (by rfl) ⟨23867, by rfl⟩ : syracuseStep 2036693 = 47735) (by norm_num)
theorem B5297125 : Blo 1356997 5297125 := bbase (se 4 (by rfl) ⟨496605, by rfl⟩ : syracuseStep 5297125 = 993211) (by norm_num)
theorem B2036717 : Blo 1356997 2036717 := bbase (se 3 (by rfl) ⟨381884, by rfl⟩ : syracuseStep 2036717 = 763769) (by norm_num)
theorem B3437549 : Blo 1356997 3437549 := bbase (se 3 (by rfl) ⟨644540, by rfl⟩ : syracuseStep 3437549 = 1289081) (by norm_num)
theorem B4584437 : Blo 1356997 4584437 := bbase (se 5 (by rfl) ⟨214895, by rfl⟩ : syracuseStep 4584437 = 429791) (by norm_num)
theorem B2290693 : Blo 1356997 2290693 := bbase (se 4 (by rfl) ⟨214752, by rfl⟩ : syracuseStep 2290693 = 429505) (by norm_num)
theorem B2036741 : Blo 1356997 2036741 := bbase (se 4 (by rfl) ⟨190944, by rfl⟩ : syracuseStep 2036741 = 381889) (by norm_num)
theorem B2036765 : Blo 1356997 2036765 := bbase (se 3 (by rfl) ⟨381893, by rfl⟩ : syracuseStep 2036765 = 763787) (by norm_num)
theorem B5796917 : Blo 1356997 5796917 := bbase (se 5 (by rfl) ⟨271730, by rfl⟩ : syracuseStep 5796917 = 543461) (by norm_num)
theorem B2036789 : Blo 1356997 2036789 := bbase (se 5 (by rfl) ⟨95474, by rfl⟩ : syracuseStep 2036789 = 190949) (by norm_num)
theorem B2036813 : Blo 1356997 2036813 := bbase (se 3 (by rfl) ⟨381902, by rfl⟩ : syracuseStep 2036813 = 763805) (by norm_num)
theorem B2290781 : Blo 1356997 2290781 := bbase (se 3 (by rfl) ⟨429521, by rfl⟩ : syracuseStep 2290781 = 859043) (by norm_num)
theorem B2036837 : Blo 1356997 2036837 := bbase (se 4 (by rfl) ⟨190953, by rfl⟩ : syracuseStep 2036837 = 381907) (by norm_num)
theorem B2937973 : Blo 1356997 2937973 := bbase (se 5 (by rfl) ⟨137717, by rfl⟩ : syracuseStep 2937973 = 275435) (by norm_num)
theorem B2036861 : Blo 1356997 2036861 := bbase (se 3 (by rfl) ⟨381911, by rfl⟩ : syracuseStep 2036861 = 763823) (by norm_num)
theorem B2036885 : Blo 1356997 2036885 := bbase (se 6 (by rfl) ⟨47739, by rfl⟩ : syracuseStep 2036885 = 95479) (by norm_num)
theorem B4895909 : Blo 1356997 4895909 := bbase (se 4 (by rfl) ⟨458991, by rfl⟩ : syracuseStep 4895909 = 917983) (by norm_num)
theorem B2036909 : Blo 1356997 2036909 := bbase (se 3 (by rfl) ⟨381920, by rfl⟩ : syracuseStep 2036909 = 763841) (by norm_num)
theorem B3437741 : Blo 1356997 3437741 := bbase (se 3 (by rfl) ⟨644576, by rfl⟩ : syracuseStep 3437741 = 1289153) (by norm_num)
theorem B2036933 : Blo 1356997 2036933 := bbase (se 4 (by rfl) ⟨190962, by rfl⟩ : syracuseStep 2036933 = 381925) (by norm_num)
theorem B1717453 : Blo 1356997 1717453 := bbase (se 3 (by rfl) ⟨322022, by rfl⟩ : syracuseStep 1717453 = 644045) (by norm_num)
theorem B2290909 : Blo 1356997 2290909 := bbase (se 3 (by rfl) ⟨429545, by rfl⟩ : syracuseStep 2290909 = 859091) (by norm_num)
theorem B2036957 : Blo 1356997 2036957 := bbase (se 3 (by rfl) ⟨381929, by rfl⟩ : syracuseStep 2036957 = 763859) (by norm_num)
theorem B2323685 : Blo 1356997 2323685 := bbase (se 4 (by rfl) ⟨217845, by rfl⟩ : syracuseStep 2323685 = 435691) (by norm_num)
theorem B2577653 : Blo 1356997 2577653 := bbase (se 5 (by rfl) ⟨120827, by rfl⟩ : syracuseStep 2577653 = 241655) (by norm_num)
theorem B2036981 : Blo 1356997 2036981 := bbase (se 5 (by rfl) ⟨95483, by rfl⟩ : syracuseStep 2036981 = 190967) (by norm_num)
theorem B2037005 : Blo 1356997 2037005 := bbase (se 3 (by rfl) ⟨381938, by rfl⟩ : syracuseStep 2037005 = 763877) (by norm_num)
theorem B2446613 : Blo 1356997 2446613 := bbase (se 6 (by rfl) ⟨57342, by rfl⟩ : syracuseStep 2446613 = 114685) (by norm_num)
theorem B2037029 : Blo 1356997 2037029 := bbase (se 4 (by rfl) ⟨190971, by rfl⟩ : syracuseStep 2037029 = 381943) (by norm_num)
theorem B2290997 : Blo 1356997 2290997 := bbase (se 5 (by rfl) ⟨107390, by rfl⟩ : syracuseStep 2290997 = 214781) (by norm_num)
theorem B2037053 : Blo 1356997 2037053 := bbase (se 3 (by rfl) ⟨381947, by rfl⟩ : syracuseStep 2037053 = 763895) (by norm_num)
theorem B2037077 : Blo 1356997 2037077 := bbase (se 14 (by rfl) ⟨186, by rfl⟩ : syracuseStep 2037077 = 373) (by norm_num)
theorem B2037101 : Blo 1356997 2037101 := bbase (se 3 (by rfl) ⟨381956, by rfl⟩ : syracuseStep 2037101 = 763913) (by norm_num)
theorem B1717625 : Blo 1356997 1717625 := bbase (se 2 (by rfl) ⟨644109, by rfl⟩ : syracuseStep 1717625 = 1288219) (by norm_num)
theorem B2037125 : Blo 1356997 2037125 := bbase (se 4 (by rfl) ⟨190980, by rfl⟩ : syracuseStep 2037125 = 381961) (by norm_num)
theorem B2037149 : Blo 1356997 2037149 := bbase (se 3 (by rfl) ⟨381965, by rfl⟩ : syracuseStep 2037149 = 763931) (by norm_num)
theorem B4584869 : Blo 1356997 4584869 := bbase (se 4 (by rfl) ⟨429831, by rfl⟩ : syracuseStep 4584869 = 859663) (by norm_num)
theorem B1717681 : Blo 1356997 1717681 := bbase (se 2 (by rfl) ⟨644130, by rfl⟩ : syracuseStep 1717681 = 1288261) (by norm_num)
theorem B2291125 : Blo 1356997 2291125 := bbase (se 5 (by rfl) ⟨107396, by rfl⟩ : syracuseStep 2291125 = 214793) (by norm_num)
theorem B2037173 : Blo 1356997 2037173 := bbase (se 5 (by rfl) ⟨95492, by rfl⟩ : syracuseStep 2037173 = 190985) (by norm_num)
theorem B2037197 : Blo 1356997 2037197 := bbase (se 3 (by rfl) ⟨381974, by rfl⟩ : syracuseStep 2037197 = 763949) (by norm_num)
theorem B2037221 : Blo 1356997 2037221 := bbase (se 4 (by rfl) ⟨190989, by rfl⟩ : syracuseStep 2037221 = 381979) (by norm_num)
theorem B6526453 : Blo 1356997 6526453 := bbase (se 5 (by rfl) ⟨305927, by rfl⟩ : syracuseStep 6526453 = 611855) (by norm_num)
theorem B2037245 : Blo 1356997 2037245 := bbase (se 3 (by rfl) ⟨381983, by rfl⟩ : syracuseStep 2037245 = 763967) (by norm_num)
theorem B3438085 : Blo 1356997 3438085 := bbase (se 4 (by rfl) ⟨322320, by rfl⟩ : syracuseStep 3438085 = 644641) (by norm_num)
theorem B2291213 : Blo 1356997 2291213 := bbase (se 3 (by rfl) ⟨429602, by rfl⟩ : syracuseStep 2291213 = 859205) (by norm_num)
theorem B1717777 : Blo 1356997 1717777 := bbase (se 2 (by rfl) ⟨644166, by rfl⟩ : syracuseStep 1717777 = 1288333) (by norm_num)
theorem B2037269 : Blo 1356997 2037269 := bbase (se 6 (by rfl) ⟨47748, by rfl⟩ : syracuseStep 2037269 = 95497) (by norm_num)
theorem B2037293 : Blo 1356997 2037293 := bbase (se 3 (by rfl) ⟨381992, by rfl⟩ : syracuseStep 2037293 = 763985) (by norm_num)
theorem B6870581 : Blo 1356997 6870581 := bbase (se 5 (by rfl) ⟨322058, by rfl⟩ : syracuseStep 6870581 = 644117) (by norm_num)
theorem B1742405 : Blo 1356997 1742405 := bbase (se 4 (by rfl) ⟨163350, by rfl⟩ : syracuseStep 1742405 = 326701) (by norm_num)
theorem B2037317 : Blo 1356997 2037317 := bbase (se 4 (by rfl) ⟨190998, by rfl⟩ : syracuseStep 2037317 = 381997) (by norm_num)
theorem B11605589 : Blo 1356997 11605589 := bbase (se 8 (by rfl) ⟨68001, by rfl⟩ : syracuseStep 11605589 = 136003) (by norm_num)
theorem B2037341 : Blo 1356997 2037341 := bbase (se 3 (by rfl) ⟨382001, by rfl⟩ : syracuseStep 2037341 = 764003) (by norm_num)
theorem B2037365 : Blo 1356997 2037365 := bbase (se 5 (by rfl) ⟨95501, by rfl⟩ : syracuseStep 2037365 = 191003) (by norm_num)
theorem B3438197 : Blo 1356997 3438197 := bbase (se 5 (by rfl) ⟨161165, by rfl⟩ : syracuseStep 3438197 = 322331) (by norm_num)
theorem B2291341 : Blo 1356997 2291341 := bbase (se 3 (by rfl) ⟨429626, by rfl⟩ : syracuseStep 2291341 = 859253) (by norm_num)
theorem B2037389 : Blo 1356997 2037389 := bbase (se 3 (by rfl) ⟨382010, by rfl⟩ : syracuseStep 2037389 = 764021) (by norm_num)
theorem B2037413 : Blo 1356997 2037413 := bbase (se 4 (by rfl) ⟨191007, by rfl⟩ : syracuseStep 2037413 = 382015) (by norm_num)
theorem B1717949 : Blo 1356997 1717949 := bbase (se 3 (by rfl) ⟨322115, by rfl⟩ : syracuseStep 1717949 = 644231) (by norm_num)
theorem B2037437 : Blo 1356997 2037437 := bbase (se 3 (by rfl) ⟨382019, by rfl⟩ : syracuseStep 2037437 = 764039) (by norm_num)
theorem B11597525 : Blo 1356997 11597525 := bbase (se 7 (by rfl) ⟨135908, by rfl⟩ : syracuseStep 11597525 = 271817) (by norm_num)
theorem B2037461 : Blo 1356997 2037461 := bbase (se 7 (by rfl) ⟨23876, by rfl⟩ : syracuseStep 2037461 = 47753) (by norm_num)
theorem B3864293 : Blo 1356997 3864293 := bbase (se 4 (by rfl) ⟨362277, by rfl⟩ : syracuseStep 3864293 = 724555) (by norm_num)
theorem B3053285 : Blo 1356997 3053285 := bbase (se 4 (by rfl) ⟨286245, by rfl⟩ : syracuseStep 3053285 = 572491) (by norm_num)
theorem B2291429 : Blo 1356997 2291429 := bbase (se 4 (by rfl) ⟨214821, by rfl⟩ : syracuseStep 2291429 = 429643) (by norm_num)
theorem B2037485 : Blo 1356997 2037485 := bbase (se 3 (by rfl) ⟨382028, by rfl⟩ : syracuseStep 2037485 = 764057) (by norm_num)
theorem B1718005 : Blo 1356997 1718005 := bbase (se 5 (by rfl) ⟨80531, by rfl⟩ : syracuseStep 1718005 = 161063) (by norm_num)
theorem B2037509 : Blo 1356997 2037509 := bbase (se 4 (by rfl) ⟨191016, by rfl⟩ : syracuseStep 2037509 = 382033) (by norm_num)
theorem B2037533 : Blo 1356997 2037533 := bbase (se 3 (by rfl) ⟨382037, by rfl⟩ : syracuseStep 2037533 = 764075) (by norm_num)
theorem B5797669 : Blo 1356997 5797669 := bbase (se 4 (by rfl) ⟨543531, by rfl⟩ : syracuseStep 5797669 = 1087063) (by norm_num)
theorem B3053357 : Blo 1356997 3053357 := bbase (se 3 (by rfl) ⟨572504, by rfl⟩ : syracuseStep 3053357 = 1145009) (by norm_num)
theorem B2037557 : Blo 1356997 2037557 := bbase (se 5 (by rfl) ⟨95510, by rfl⟩ : syracuseStep 2037557 = 191021) (by norm_num)
theorem B3438389 : Blo 1356997 3438389 := bbase (se 5 (by rfl) ⟨161174, by rfl⟩ : syracuseStep 3438389 = 322349) (by norm_num)
theorem B2037581 : Blo 1356997 2037581 := bbase (se 3 (by rfl) ⟨382046, by rfl⟩ : syracuseStep 2037581 = 764093) (by norm_num)
theorem B1718101 : Blo 1356997 1718101 := bbase (se 9 (by rfl) ⟨5033, by rfl⟩ : syracuseStep 1718101 = 10067) (by norm_num)
theorem B2291557 : Blo 1356997 2291557 := bbase (se 4 (by rfl) ⟨214833, by rfl⟩ : syracuseStep 2291557 = 429667) (by norm_num)
theorem B2037605 : Blo 1356997 2037605 := bbase (se 4 (by rfl) ⟨191025, by rfl⟩ : syracuseStep 2037605 = 382051) (by norm_num)
theorem B2791277 : Blo 1356997 2791277 := bbase (se 3 (by rfl) ⟨523364, by rfl⟩ : syracuseStep 2791277 = 1046729) (by norm_num)
theorem B3053429 : Blo 1356997 3053429 := bbase (se 5 (by rfl) ⟨143129, by rfl⟩ : syracuseStep 3053429 = 286259) (by norm_num)
theorem B2037629 : Blo 1356997 2037629 := bbase (se 3 (by rfl) ⟨382055, by rfl⟩ : syracuseStep 2037629 = 764111) (by norm_num)
theorem B2037653 : Blo 1356997 2037653 := bbase (se 6 (by rfl) ⟨47757, by rfl⟩ : syracuseStep 2037653 = 95515) (by norm_num)
theorem B2037677 : Blo 1356997 2037677 := bbase (se 3 (by rfl) ⟨382064, by rfl⟩ : syracuseStep 2037677 = 764129) (by norm_num)
theorem B3053501 : Blo 1356997 3053501 := bbase (se 3 (by rfl) ⟨572531, by rfl⟩ : syracuseStep 3053501 = 1145063) (by norm_num)
theorem B2291645 : Blo 1356997 2291645 := bbase (se 3 (by rfl) ⟨429683, by rfl⟩ : syracuseStep 2291645 = 859367) (by norm_num)
theorem B2037701 : Blo 1356997 2037701 := bbase (se 4 (by rfl) ⟨191034, by rfl⟩ : syracuseStep 2037701 = 382069) (by norm_num)
theorem B2037725 : Blo 1356997 2037725 := bbase (se 3 (by rfl) ⟨382073, by rfl⟩ : syracuseStep 2037725 = 764147) (by norm_num)
theorem B2578405 : Blo 1356997 2578405 := bbase (se 4 (by rfl) ⟨241725, by rfl⟩ : syracuseStep 2578405 = 483451) (by norm_num)
theorem B4347893 : Blo 1356997 4347893 := bbase (se 5 (by rfl) ⟨203807, by rfl⟩ : syracuseStep 4347893 = 407615) (by norm_num)
theorem B6191093 : Blo 1356997 6191093 := bbase (se 5 (by rfl) ⟨290207, by rfl⟩ : syracuseStep 6191093 = 580415) (by norm_num)
theorem B1718273 : Blo 1356997 1718273 := bbase (se 2 (by rfl) ⟨644352, by rfl⟩ : syracuseStep 1718273 = 1288705) (by norm_num)
theorem B3053573 : Blo 1356997 3053573 := bbase (se 4 (by rfl) ⟨286272, by rfl⟩ : syracuseStep 3053573 = 572545) (by norm_num)
theorem B1718329 : Blo 1356997 1718329 := bbase (se 2 (by rfl) ⟨644373, by rfl⟩ : syracuseStep 1718329 = 1288747) (by norm_num)
theorem B2291773 : Blo 1356997 2291773 := bbase (se 3 (by rfl) ⟨429707, by rfl⟩ : syracuseStep 2291773 = 859415) (by norm_num)
theorem B3053645 : Blo 1356997 3053645 := bbase (se 3 (by rfl) ⟨572558, by rfl⟩ : syracuseStep 3053645 = 1145117) (by norm_num)
theorem B8697941 : Blo 1356997 8697941 := bbase (se 8 (by rfl) ⟨50964, by rfl⟩ : syracuseStep 8697941 = 101929) (by norm_num)
theorem B2578549 : Blo 1356997 2578549 := bbase (se 5 (by rfl) ⟨120869, by rfl⟩ : syracuseStep 2578549 = 241739) (by norm_num)
theorem B3053717 : Blo 1356997 3053717 := bbase (se 6 (by rfl) ⟨71571, by rfl⟩ : syracuseStep 3053717 = 143143) (by norm_num)
theorem B2291861 : Blo 1356997 2291861 := bbase (se 6 (by rfl) ⟨53715, by rfl⟩ : syracuseStep 2291861 = 107431) (by norm_num)
theorem B1718425 : Blo 1356997 1718425 := bbase (se 2 (by rfl) ⟨644409, by rfl⟩ : syracuseStep 1718425 = 1288819) (by norm_num)
theorem B3053789 : Blo 1356997 3053789 := bbase (se 3 (by rfl) ⟨572585, by rfl⟩ : syracuseStep 3053789 = 1145171) (by norm_num)
theorem B2291989 : Blo 1356997 2291989 := bbase (se 6 (by rfl) ⟨53718, by rfl⟩ : syracuseStep 2291989 = 107437) (by norm_num)
theorem B2578709 : Blo 1356997 2578709 := bbase (se 6 (by rfl) ⟨60438, by rfl⟩ : syracuseStep 2578709 = 120877) (by norm_num)
theorem B3053861 : Blo 1356997 3053861 := bbase (se 4 (by rfl) ⟨286299, by rfl⟩ : syracuseStep 3053861 = 572599) (by norm_num)
theorem B1718597 : Blo 1356997 1718597 := bbase (se 4 (by rfl) ⟨161118, by rfl⟩ : syracuseStep 1718597 = 322237) (by norm_num)
theorem B3053933 : Blo 1356997 3053933 := bbase (se 3 (by rfl) ⟨572612, by rfl⟩ : syracuseStep 3053933 = 1145225) (by norm_num)
theorem B2292077 : Blo 1356997 2292077 := bbase (se 3 (by rfl) ⟨429764, by rfl⟩ : syracuseStep 2292077 = 859529) (by norm_num)
theorem B1718653 : Blo 1356997 1718653 := bbase (se 3 (by rfl) ⟨322247, by rfl⟩ : syracuseStep 1718653 = 644495) (by norm_num)
theorem B2685349 : Blo 1356997 2685349 := bbase (se 4 (by rfl) ⟨251751, by rfl⟩ : syracuseStep 2685349 = 503503) (by norm_num)
theorem B2578853 : Blo 1356997 2578853 := bbase (se 4 (by rfl) ⟨241767, by rfl⟩ : syracuseStep 2578853 = 483535) (by norm_num)
theorem B3054005 : Blo 1356997 3054005 := bbase (se 5 (by rfl) ⟨143156, by rfl⟩ : syracuseStep 3054005 = 286313) (by norm_num)
theorem B2513357 : Blo 1356997 2513357 := bbase (se 3 (by rfl) ⟨471254, by rfl⟩ : syracuseStep 2513357 = 942509) (by norm_num)
theorem B1718749 : Blo 1356997 1718749 := bbase (se 3 (by rfl) ⟨322265, by rfl⟩ : syracuseStep 1718749 = 644531) (by norm_num)
theorem B2292205 : Blo 1356997 2292205 := bbase (se 3 (by rfl) ⟨429788, by rfl⟩ : syracuseStep 2292205 = 859577) (by norm_num)
theorem B3054077 : Blo 1356997 3054077 := bbase (se 3 (by rfl) ⟨572639, by rfl⟩ : syracuseStep 3054077 = 1145279) (by norm_num)
theorem B5798405 : Blo 1356997 5798405 := bbase (se 4 (by rfl) ⟨543600, by rfl⟩ : syracuseStep 5798405 = 1087201) (by norm_num)
theorem B3578381 : Blo 1356997 3578381 := bbase (se 3 (by rfl) ⟨670946, by rfl⟩ : syracuseStep 3578381 = 1341893) (by norm_num)
theorem B3054149 : Blo 1356997 3054149 := bbase (se 4 (by rfl) ⟨286326, by rfl⟩ : syracuseStep 3054149 = 572653) (by norm_num)
theorem B2292293 : Blo 1356997 2292293 := bbase (se 4 (by rfl) ⟨214902, by rfl⟩ : syracuseStep 2292293 = 429805) (by norm_num)
theorem B2611805 : Blo 1356997 2611805 := bbase (se 3 (by rfl) ⟨489713, by rfl⟩ : syracuseStep 2611805 = 979427) (by norm_num)
theorem B1489537 : Blo 1356997 1489537 := bbase (se 2 (by rfl) ⟨558576, by rfl⟩ : syracuseStep 1489537 = 1117153) (by norm_num)
theorem B1718921 : Blo 1356997 1718921 := bbase (se 2 (by rfl) ⟨644595, by rfl⟩ : syracuseStep 1718921 = 1289191) (by norm_num)
theorem B3054221 : Blo 1356997 3054221 := bbase (se 3 (by rfl) ⟨572666, by rfl⟩ : syracuseStep 3054221 = 1145333) (by norm_num)
theorem B1718977 : Blo 1356997 1718977 := bbase (se 2 (by rfl) ⟨644616, by rfl⟩ : syracuseStep 1718977 = 1289233) (by norm_num)
theorem B2292421 : Blo 1356997 2292421 := bbase (se 4 (by rfl) ⟨214914, by rfl⟩ : syracuseStep 2292421 = 429829) (by norm_num)
theorem B3054293 : Blo 1356997 3054293 := bbase (se 7 (by rfl) ⟨35792, by rfl⟩ : syracuseStep 3054293 = 71585) (by norm_num)
theorem B3054365 : Blo 1356997 3054365 := bbase (se 3 (by rfl) ⟨572693, by rfl⟩ : syracuseStep 3054365 = 1145387) (by norm_num)
theorem B1719073 : Blo 1356997 1719073 := bbase (se 2 (by rfl) ⟨644652, by rfl⟩ : syracuseStep 1719073 = 1289305) (by norm_num)
theorem B6871877 : Blo 1356997 6871877 := bbase (se 4 (by rfl) ⟨644238, by rfl⟩ : syracuseStep 6871877 = 1288477) (by norm_num)
theorem B3054437 : Blo 1356997 3054437 := bbase (se 4 (by rfl) ⟨286353, by rfl⟩ : syracuseStep 3054437 = 572707) (by norm_num)
theorem B2939773 : Blo 1356997 2939773 := bbase (se 3 (by rfl) ⟨551207, by rfl⟩ : syracuseStep 2939773 = 1102415) (by norm_num)
theorem B3865477 : Blo 1356997 3865477 := bbase (se 4 (by rfl) ⟨362388, by rfl⟩ : syracuseStep 3865477 = 724777) (by norm_num)
theorem B3054509 : Blo 1356997 3054509 := bbase (se 3 (by rfl) ⟨572720, by rfl⟩ : syracuseStep 3054509 = 1145441) (by norm_num)
theorem B1719245 : Blo 1356997 1719245 := bbase (se 3 (by rfl) ⟨322358, by rfl⟩ : syracuseStep 1719245 = 644717) (by norm_num)
theorem B3054581 : Blo 1356997 3054581 := bbase (se 5 (by rfl) ⟨143183, by rfl⟩ : syracuseStep 3054581 = 286367) (by norm_num)
theorem B1719301 : Blo 1356997 1719301 := bbase (se 4 (by rfl) ⟨161184, by rfl⟩ : syracuseStep 1719301 = 322369) (by norm_num)
theorem B3865637 : Blo 1356997 3865637 := bbase (se 4 (by rfl) ⟨362403, by rfl⟩ : syracuseStep 3865637 = 724807) (by norm_num)
theorem B3054653 : Blo 1356997 3054653 := bbase (se 3 (by rfl) ⟨572747, by rfl⟩ : syracuseStep 3054653 = 1145495) (by norm_num)
theorem B2751565 : Blo 1356997 2751565 := bbase (se 3 (by rfl) ⟨515918, by rfl⟩ : syracuseStep 2751565 = 1031837) (by norm_num)
theorem B3054725 : Blo 1356997 3054725 := bbase (se 4 (by rfl) ⟨286380, by rfl⟩ : syracuseStep 3054725 = 572761) (by norm_num)
theorem B1932437 : Blo 1356997 1932437 := bbase (se 6 (by rfl) ⟨45291, by rfl⟩ : syracuseStep 1932437 = 90583) (by norm_num)
theorem B2751661 : Blo 1356997 2751661 := bbase (se 3 (by rfl) ⟨515936, by rfl⟩ : syracuseStep 2751661 = 1031873) (by norm_num)
theorem B3054797 : Blo 1356997 3054797 := bbase (se 3 (by rfl) ⟨572774, by rfl⟩ : syracuseStep 3054797 = 1145549) (by norm_num)
theorem B3865877 : Blo 1356997 3865877 := bbase (se 6 (by rfl) ⟨90606, by rfl⟩ : syracuseStep 3865877 = 181213) (by norm_num)
theorem B3054869 : Blo 1356997 3054869 := bbase (se 6 (by rfl) ⟨71598, by rfl⟩ : syracuseStep 3054869 = 143197) (by norm_num)
theorem B3054941 : Blo 1356997 3054941 := bbase (se 3 (by rfl) ⟨572801, by rfl⟩ : syracuseStep 3054941 = 1145603) (by norm_num)
theorem B3055013 : Blo 1356997 3055013 := bbase (se 4 (by rfl) ⟨286407, by rfl⟩ : syracuseStep 3055013 = 572815) (by norm_num)
theorem B1449409 : Blo 1356997 1449409 := bbase (se 2 (by rfl) ⟨543528, by rfl⟩ : syracuseStep 1449409 = 1087057) (by norm_num)
theorem B3866069 : Blo 1356997 3866069 := bbase (se 7 (by rfl) ⟨45305, by rfl⟩ : syracuseStep 3866069 = 90611) (by norm_num)
theorem B3055085 : Blo 1356997 3055085 := bbase (se 3 (by rfl) ⟨572828, by rfl⟩ : syracuseStep 3055085 = 1145657) (by norm_num)
theorem B3669509 : Blo 1356997 3669509 := bbase (se 4 (by rfl) ⟨344016, by rfl⟩ : syracuseStep 3669509 = 688033) (by norm_num)
theorem B3055157 : Blo 1356997 3055157 := bbase (se 5 (by rfl) ⟨143210, by rfl⟩ : syracuseStep 3055157 = 286421) (by norm_num)
theorem B1449533 : Blo 1356997 1449533 := bbase (se 3 (by rfl) ⟨271787, by rfl⟩ : syracuseStep 1449533 = 543575) (by norm_num)
theorem B3055229 : Blo 1356997 3055229 := bbase (se 3 (by rfl) ⟨572855, by rfl⟩ : syracuseStep 3055229 = 1145711) (by norm_num)
theorem B2899613 : Blo 1356997 2899613 := bbase (se 3 (by rfl) ⟨543677, by rfl⟩ : syracuseStep 2899613 = 1087355) (by norm_num)
theorem B1932989 : Blo 1356997 1932989 := bbase (se 3 (by rfl) ⟨362435, by rfl⟩ : syracuseStep 1932989 = 724871) (by norm_num)
theorem B3055301 : Blo 1356997 3055301 := bbase (se 4 (by rfl) ⟨286434, by rfl⟩ : syracuseStep 3055301 = 572869) (by norm_num)
theorem B2940637 : Blo 1356997 2940637 := bbase (se 3 (by rfl) ⟨551369, by rfl⟩ : syracuseStep 2940637 = 1102739) (by norm_num)
theorem B2752237 : Blo 1356997 2752237 := bbase (se 3 (by rfl) ⟨516044, by rfl⟩ : syracuseStep 2752237 = 1032089) (by norm_num)
theorem B1548029 : Blo 1356997 1548029 := bbase (se 3 (by rfl) ⟨290255, by rfl⟩ : syracuseStep 1548029 = 580511) (by norm_num)
theorem B3055373 : Blo 1356997 3055373 := bbase (se 3 (by rfl) ⟨572882, by rfl⟩ : syracuseStep 3055373 = 1145765) (by norm_num)
theorem B6610709 : Blo 1356997 6610709 := bbase (se 6 (by rfl) ⟨154938, by rfl⟩ : syracuseStep 6610709 = 309877) (by norm_num)
theorem B2899757 : Blo 1356997 2899757 := bbase (se 3 (by rfl) ⟨543704, by rfl⟩ : syracuseStep 2899757 = 1087409) (by norm_num)
theorem B4644661 : Blo 1356997 4644661 := bbase (se 5 (by rfl) ⟨217718, by rfl⟩ : syracuseStep 4644661 = 435437) (by norm_num)
theorem B1449785 : Blo 1356997 1449785 := bbase (se 2 (by rfl) ⟨543669, by rfl⟩ : syracuseStep 1449785 = 1087339) (by norm_num)
theorem B3055445 : Blo 1356997 3055445 := bbase (se 9 (by rfl) ⟨8951, by rfl⟩ : syracuseStep 3055445 = 17903) (by norm_num)
theorem B3669877 : Blo 1356997 3669877 := bbase (se 5 (by rfl) ⟨172025, by rfl⟩ : syracuseStep 3669877 = 344051) (by norm_num)
theorem B7733141 : Blo 1356997 7733141 := bbase (se 6 (by rfl) ⟨181245, by rfl⟩ : syracuseStep 7733141 = 362491) (by norm_num)
theorem B3055517 : Blo 1356997 3055517 := bbase (se 3 (by rfl) ⟨572909, by rfl⟩ : syracuseStep 3055517 = 1145819) (by norm_num)
theorem B5152693 : Blo 1356997 5152693 := bbase (se 5 (by rfl) ⟨241532, by rfl⟩ : syracuseStep 5152693 = 483065) (by norm_num)
theorem B2654165 : Blo 1356997 2654165 := bbase (se 7 (by rfl) ⟨31103, by rfl⟩ : syracuseStep 2654165 = 62207) (by norm_num)
theorem B3055589 : Blo 1356997 3055589 := bbase (se 4 (by rfl) ⟨286461, by rfl⟩ : syracuseStep 3055589 = 572923) (by norm_num)
theorem B4644881 : Blo 1356997 4644881 := bstep (se 2 (by rfl) ⟨1741830, by rfl⟩ : syracuseStep 4644881 = 3483661) B3483661
theorem B3055697 : Blo 1356997 3055697 := bstep (se 2 (by rfl) ⟨1145886, by rfl⟩ : syracuseStep 3055697 = 2291773) B2291773
theorem B1933411 : Blo 1356997 1933411 := bstep (se 1 (by rfl) ⟨1450058, by rfl⟩ : syracuseStep 1933411 = 2900117) B2900117
theorem B3055715 : Blo 1356997 3055715 := bstep (se 1 (by rfl) ⟨2291786, by rfl⟩ : syracuseStep 3055715 = 4583573) B4583573
theorem B2900099 : Blo 1356997 2900099 := bstep (se 1 (by rfl) ⟨2175074, by rfl⟩ : syracuseStep 2900099 = 4350149) B4350149
theorem B3096899 : Blo 1356997 3096899 := bstep (se 1 (by rfl) ⟨2322674, by rfl⟩ : syracuseStep 3096899 = 4645349) B4645349
theorem B3055985 : Blo 1356997 3055985 := bstep (se 2 (by rfl) ⟨1145994, by rfl⟩ : syracuseStep 3055985 = 2291989) B2291989
theorem B3056003 : Blo 1356997 3056003 := bstep (se 1 (by rfl) ⟨2292002, by rfl⟩ : syracuseStep 3056003 = 4584005) B4584005
theorem B5153165 : Blo 1356997 5153165 := bstep (se 3 (by rfl) ⟨966218, by rfl⟩ : syracuseStep 5153165 = 1932437) B1932437
theorem B4350353 : Blo 1356997 4350353 := bstep (se 2 (by rfl) ⟨1631382, by rfl⟩ : syracuseStep 4350353 = 3262765) B3262765
theorem B5800369 : Blo 1356997 5800369 := bstep (se 2 (by rfl) ⟨2175138, by rfl⟩ : syracuseStep 5800369 = 4350277) B4350277
theorem B2753041 : Blo 1356997 2753041 := bstep (se 2 (by rfl) ⟨1032390, by rfl⟩ : syracuseStep 2753041 = 2064781) B2064781
theorem B1630739 : Blo 1356997 1630739 := bstep (se 1 (by rfl) ⟨1223054, by rfl⟩ : syracuseStep 1630739 = 2446109) B2446109
theorem B3580465 : Blo 1356997 3580465 := bstep (se 2 (by rfl) ⟨1342674, by rfl⟩ : syracuseStep 3580465 = 2685349) B2685349
theorem B3867277 : Blo 1356997 3867277 := bstep (se 3 (by rfl) ⟨725114, by rfl⟩ : syracuseStep 3867277 = 1450229) B1450229
theorem B1933969 : Blo 1356997 1933969 := bstep (se 2 (by rfl) ⟨725238, by rfl⟩ : syracuseStep 1933969 = 1450477) B1450477
theorem B3056273 : Blo 1356997 3056273 := bstep (se 2 (by rfl) ⟨1146102, by rfl⟩ : syracuseStep 3056273 = 2292205) B2292205
theorem B3056291 : Blo 1356997 3056291 := bstep (se 1 (by rfl) ⟨2292218, by rfl⟩ : syracuseStep 3056291 = 4584437) B4584437
theorem B1934003 : Blo 1356997 1934003 := bstep (se 1 (by rfl) ⟨1450502, by rfl⟩ : syracuseStep 1934003 = 2901005) B2901005
theorem B66069269 : Blo 1356997 66069269 := bstep (se 6 (by rfl) ⟨1548498, by rfl⟩ : syracuseStep 66069269 = 3096997) B3096997
theorem B3670829 : Blo 1356997 3670829 := bstep (se 3 (by rfl) ⟨688280, by rfl⟩ : syracuseStep 3670829 = 1376561) B1376561
theorem B1631075 : Blo 1356997 1631075 := bstep (se 1 (by rfl) ⟨1223306, by rfl⟩ : syracuseStep 1631075 = 2446613) B2446613
theorem B3670957 : Blo 1356997 3670957 := bstep (se 3 (by rfl) ⟨688304, by rfl⟩ : syracuseStep 3670957 = 1376609) B1376609
theorem B3056561 : Blo 1356997 3056561 := bstep (se 2 (by rfl) ⟨1146210, by rfl⟩ : syracuseStep 3056561 = 2292421) B2292421
theorem B3056579 : Blo 1356997 3056579 := bstep (se 1 (by rfl) ⟨2292434, by rfl⟩ : syracuseStep 3056579 = 4584869) B4584869
theorem B4580333 : Blo 1356997 4580333 := bstep (se 3 (by rfl) ⟨858812, by rfl⟩ : syracuseStep 4580333 = 1717625) B1717625
theorem B4580387 : Blo 1356997 4580387 := bstep (se 1 (by rfl) ⟨3435290, by rfl⟩ : syracuseStep 4580387 = 6870581) B6870581
theorem B5153969 : Blo 1356997 5153969 := bstep (se 2 (by rfl) ⟨1932738, by rfl⟩ : syracuseStep 5153969 = 3865477) B3865477
theorem B1860851 : Blo 1356997 1860851 := bstep (se 1 (by rfl) ⟨1395638, by rfl⟩ : syracuseStep 1860851 = 2791277) B2791277
theorem B4580657 : Blo 1356997 4580657 := bstep (se 2 (by rfl) ⟨1717746, by rfl⟩ : syracuseStep 4580657 = 3435493) B3435493
theorem B7062833 : Blo 1356997 7062833 := bstep (se 2 (by rfl) ⟨2648562, by rfl⟩ : syracuseStep 7062833 = 5297125) B5297125
theorem B3917297 : Blo 1356997 3917297 := bstep (se 2 (by rfl) ⟨1468986, by rfl⟩ : syracuseStep 3917297 = 2937973) B2937973
theorem B13927949 : Blo 1356997 13927949 := bstep (se 3 (by rfl) ⟨2611490, by rfl⟩ : syracuseStep 13927949 = 5222981) B5222981
theorem B4646413 : Blo 1356997 4646413 := bstep (se 3 (by rfl) ⟨871202, by rfl⟩ : syracuseStep 4646413 = 1742405) B1742405
theorem B6964813 : Blo 1356997 6964813 := bstep (se 3 (by rfl) ⟨1305902, by rfl⟩ : syracuseStep 6964813 = 2611805) B2611805
theorem B3868337 : Blo 1356997 3868337 := bstep (se 2 (by rfl) ⟨1450626, by rfl⟩ : syracuseStep 3868337 = 2901253) B2901253
theorem B2385587 : Blo 1356997 2385587 := bstep (se 1 (by rfl) ⟨1789190, by rfl⟩ : syracuseStep 2385587 = 3578381) B3578381
theorem B4130509 : Blo 1356997 4130509 := bstep (se 3 (by rfl) ⟨774470, by rfl⟩ : syracuseStep 4130509 = 1548941) B1548941
theorem B4581197 : Blo 1356997 4581197 := bstep (se 3 (by rfl) ⟨858974, by rfl⟩ : syracuseStep 4581197 = 1717949) B1717949
theorem B5154637 : Blo 1356997 5154637 := bstep (se 3 (by rfl) ⟨966494, by rfl⟩ : syracuseStep 5154637 = 1932989) B1932989
theorem B4581251 : Blo 1356997 4581251 := bstep (se 1 (by rfl) ⟨3435938, by rfl⟩ : syracuseStep 4581251 = 6871877) B6871877
theorem B8701937 : Blo 1356997 8701937 := bstep (se 2 (by rfl) ⟨3263226, by rfl⟩ : syracuseStep 8701937 = 6526453) B6526453
theorem B4130947 : Blo 1356997 4130947 := bstep (se 1 (by rfl) ⟨3098210, by rfl⟩ : syracuseStep 4130947 = 6196421) B6196421
theorem B4581521 : Blo 1356997 4581521 := bstep (se 2 (by rfl) ⟨1718070, by rfl⟩ : syracuseStep 4581521 = 3436141) B3436141
theorem B6875441 : Blo 1356997 6875441 := bstep (se 2 (by rfl) ⟨2578290, by rfl⟩ : syracuseStep 6875441 = 5156581) B5156581
theorem B7735601 : Blo 1356997 7735601 := bstep (se 2 (by rfl) ⟨2900850, by rfl⟩ : syracuseStep 7735601 = 5801701) B5801701
theorem B5802317 : Blo 1356997 5802317 := bstep (se 3 (by rfl) ⟨1087934, by rfl⟩ : syracuseStep 5802317 = 2175869) B2175869
theorem B4024721 : Blo 1356997 4024721 := bstep (se 2 (by rfl) ⟨1509270, by rfl⟩ : syracuseStep 4024721 = 3018541) B3018541
theorem B4893169 : Blo 1356997 4893169 := bstep (se 2 (by rfl) ⟨1834938, by rfl⟩ : syracuseStep 4893169 = 3669877) B3669877
theorem B5155427 : Blo 1356997 5155427 := bstep (se 1 (by rfl) ⟨3866570, by rfl⟩ : syracuseStep 5155427 = 7733141) B7733141
theorem B16509581 : Blo 1356997 16509581 := bstep (se 3 (by rfl) ⟨3095546, by rfl⟩ : syracuseStep 16509581 = 6191093) B6191093
theorem B4582061 : Blo 1356997 4582061 := bstep (se 3 (by rfl) ⟨859136, by rfl⟩ : syracuseStep 4582061 = 1718273) B1718273
theorem B4582115 : Blo 1356997 4582115 := bstep (se 1 (by rfl) ⟨3436586, by rfl⟩ : syracuseStep 4582115 = 6873173) B6873173
theorem B3435281 : Blo 1356997 3435281 := bstep (se 2 (by rfl) ⟨1288230, by rfl⟩ : syracuseStep 3435281 = 2576461) B2576461
theorem B3435331 : Blo 1356997 3435331 := bstep (se 1 (by rfl) ⟨2576498, by rfl⟩ : syracuseStep 3435331 = 5152997) B5152997
theorem B3435473 : Blo 1356997 3435473 := bstep (se 2 (by rfl) ⟨1288302, by rfl⟩ : syracuseStep 3435473 = 2576605) B2576605
theorem B1526755 : Blo 1356997 1526755 := bstep (se 1 (by rfl) ⟨1145066, by rfl⟩ : syracuseStep 1526755 = 2290133) B2290133
theorem B4582385 : Blo 1356997 4582385 := bstep (se 2 (by rfl) ⟨1718394, by rfl⟩ : syracuseStep 4582385 = 3436789) B3436789
theorem B1526899 : Blo 1356997 1526899 := bstep (se 1 (by rfl) ⟨1145174, by rfl⟩ : syracuseStep 1526899 = 2290349) B2290349
theorem B23186573 : Blo 1356997 23186573 := bstep (se 3 (by rfl) ⟨4347482, by rfl⟩ : syracuseStep 23186573 = 8694965) B8694965
theorem B5156081 : Blo 1356997 5156081 := bstep (se 2 (by rfl) ⟨1933530, by rfl⟩ : syracuseStep 5156081 = 3867061) B3867061
theorem B1527043 : Blo 1356997 1527043 := bstep (se 1 (by rfl) ⟨1145282, by rfl⟩ : syracuseStep 1527043 = 2290565) B2290565
theorem B6196493 : Blo 1356997 6196493 := bstep (se 3 (by rfl) ⟨1161842, by rfl⟩ : syracuseStep 6196493 = 2323685) B2323685
theorem B7154993 : Blo 1356997 7154993 := bstep (se 2 (by rfl) ⟨2683122, by rfl⟩ : syracuseStep 7154993 = 5366245) B5366245
theorem B1527187 : Blo 1356997 1527187 := bstep (se 1 (by rfl) ⟨1145390, by rfl⟩ : syracuseStep 1527187 = 2290781) B2290781
theorem B3263939 : Blo 1356997 3263939 := bstep (se 1 (by rfl) ⟨2447954, by rfl⟩ : syracuseStep 3263939 = 4895909) B4895909
theorem B1986049 : Blo 1356997 1986049 := bstep (se 2 (by rfl) ⟨744768, by rfl⟩ : syracuseStep 1986049 = 1489537) B1489537
theorem B4582925 : Blo 1356997 4582925 := bstep (se 3 (by rfl) ⟨859298, by rfl⟩ : syracuseStep 4582925 = 1718597) B1718597
theorem B1527331 : Blo 1356997 1527331 := bstep (se 1 (by rfl) ⟨1145498, by rfl⟩ : syracuseStep 1527331 = 2290997) B2290997
theorem B4582979 : Blo 1356997 4582979 := bstep (se 1 (by rfl) ⟨3437234, by rfl⟩ : syracuseStep 4582979 = 6874469) B6874469
theorem B1527475 : Blo 1356997 1527475 := bstep (se 1 (by rfl) ⟨1145606, by rfl⟩ : syracuseStep 1527475 = 2291213) B2291213
theorem B6876899 : Blo 1356997 6876899 := bstep (se 1 (by rfl) ⟨5157674, by rfl⟩ : syracuseStep 6876899 = 10315349) B10315349
theorem B7737059 : Blo 1356997 7737059 := bstep (se 1 (by rfl) ⟨5802794, by rfl⟩ : syracuseStep 7737059 = 11605589) B11605589
theorem B2035505 : Blo 1356997 2035505 := bstep (se 2 (by rfl) ⟨763314, by rfl⟩ : syracuseStep 2035505 = 1526629) B1526629
theorem B2576195 : Blo 1356997 2576195 := bstep (se 1 (by rfl) ⟨1932146, by rfl⟩ : syracuseStep 2576195 = 3864293) B3864293
theorem B2035523 : Blo 1356997 2035523 := bstep (se 1 (by rfl) ⟨1526642, by rfl⟩ : syracuseStep 2035523 = 3053285) B3053285
theorem B1527619 : Blo 1356997 1527619 := bstep (se 1 (by rfl) ⟨1145714, by rfl⟩ : syracuseStep 1527619 = 2291429) B2291429
theorem B3919697 : Blo 1356997 3919697 := bstep (se 2 (by rfl) ⟨1469886, by rfl⟩ : syracuseStep 3919697 = 2939773) B2939773
theorem B4583249 : Blo 1356997 4583249 := bstep (se 2 (by rfl) ⟨1718718, by rfl⟩ : syracuseStep 4583249 = 3437437) B3437437
theorem B2035553 : Blo 1356997 2035553 := bstep (se 2 (by rfl) ⟨763332, by rfl⟩ : syracuseStep 2035553 = 1526665) B1526665
theorem B2035571 : Blo 1356997 2035571 := bstep (se 1 (by rfl) ⟨1526678, by rfl⟩ : syracuseStep 2035571 = 3053357) B3053357
theorem B10309517 : Blo 1356997 10309517 := bstep (se 3 (by rfl) ⟨1933034, by rfl⟩ : syracuseStep 10309517 = 3866069) B3866069
theorem B2035601 : Blo 1356997 2035601 := bstep (se 2 (by rfl) ⟨763350, by rfl⟩ : syracuseStep 2035601 = 1526701) B1526701
theorem B2035619 : Blo 1356997 2035619 := bstep (se 1 (by rfl) ⟨1526714, by rfl⟩ : syracuseStep 2035619 = 3053429) B3053429
theorem B3436465 : Blo 1356997 3436465 := bstep (se 2 (by rfl) ⟨1288674, by rfl⟩ : syracuseStep 3436465 = 2577349) B2577349
theorem B2035649 : Blo 1356997 2035649 := bstep (se 2 (by rfl) ⟨763368, by rfl⟩ : syracuseStep 2035649 = 1526737) B1526737
theorem B2035667 : Blo 1356997 2035667 := bstep (se 1 (by rfl) ⟨1526750, by rfl⟩ : syracuseStep 2035667 = 3053501) B3053501
theorem B1527763 : Blo 1356997 1527763 := bstep (se 1 (by rfl) ⟨1145822, by rfl⟩ : syracuseStep 1527763 = 2291645) B2291645
theorem B2035697 : Blo 1356997 2035697 := bstep (se 2 (by rfl) ⟨763386, by rfl⟩ : syracuseStep 2035697 = 1526773) B1526773
theorem B2035715 : Blo 1356997 2035715 := bstep (se 1 (by rfl) ⟨1526786, by rfl⟩ : syracuseStep 2035715 = 3053573) B3053573
theorem B9785357 : Blo 1356997 9785357 := bstep (se 3 (by rfl) ⟨1834754, by rfl⟩ : syracuseStep 9785357 = 3669509) B3669509
theorem B2035745 : Blo 1356997 2035745 := bstep (se 2 (by rfl) ⟨763404, by rfl⟩ : syracuseStep 2035745 = 1526809) B1526809
theorem B2035763 : Blo 1356997 2035763 := bstep (se 1 (by rfl) ⟨1526822, by rfl⟩ : syracuseStep 2035763 = 3053645) B3053645
theorem B2035793 : Blo 1356997 2035793 := bstep (se 2 (by rfl) ⟨763422, by rfl⟩ : syracuseStep 2035793 = 1526845) B1526845
theorem B2035811 : Blo 1356997 2035811 := bstep (se 1 (by rfl) ⟨1526858, by rfl⟩ : syracuseStep 2035811 = 3053717) B3053717
theorem B1527907 : Blo 1356997 1527907 := bstep (se 1 (by rfl) ⟨1145930, by rfl⟩ : syracuseStep 1527907 = 2291861) B2291861
theorem B2035841 : Blo 1356997 2035841 := bstep (se 2 (by rfl) ⟨763440, by rfl⟩ : syracuseStep 2035841 = 1526881) B1526881
theorem B2035859 : Blo 1356997 2035859 := bstep (se 1 (by rfl) ⟨1526894, by rfl⟩ : syracuseStep 2035859 = 3053789) B3053789
theorem B2035889 : Blo 1356997 2035889 := bstep (se 2 (by rfl) ⟨763458, by rfl⟩ : syracuseStep 2035889 = 1526917) B1526917
theorem B2035907 : Blo 1356997 2035907 := bstep (se 1 (by rfl) ⟨1526930, by rfl⟩ : syracuseStep 2035907 = 3053861) B3053861
theorem B3436739 : Blo 1356997 3436739 := bstep (se 1 (by rfl) ⟨2577554, by rfl⟩ : syracuseStep 3436739 = 5155109) B5155109
theorem B79376597 : Blo 1356997 79376597 := bstep (se 7 (by rfl) ⟨930194, by rfl⟩ : syracuseStep 79376597 = 1860389) B1860389
theorem B2035937 : Blo 1356997 2035937 := bstep (se 2 (by rfl) ⟨763476, by rfl⟩ : syracuseStep 2035937 = 1526953) B1526953
theorem B2035955 : Blo 1356997 2035955 := bstep (se 1 (by rfl) ⟨1526966, by rfl⟩ : syracuseStep 2035955 = 3053933) B3053933
theorem B1528051 : Blo 1356997 1528051 := bstep (se 1 (by rfl) ⟨1146038, by rfl⟩ : syracuseStep 1528051 = 2292077) B2292077
theorem B2289937 : Blo 1356997 2289937 := bstep (se 2 (by rfl) ⟨858726, by rfl⟩ : syracuseStep 2289937 = 1717453) B1717453
theorem B2035985 : Blo 1356997 2035985 := bstep (se 2 (by rfl) ⟨763494, by rfl⟩ : syracuseStep 2035985 = 1526989) B1526989
theorem B2036003 : Blo 1356997 2036003 := bstep (se 1 (by rfl) ⟨1527002, by rfl⟩ : syracuseStep 2036003 = 3054005) B3054005
theorem B2289971 : Blo 1356997 2289971 := bstep (se 1 (by rfl) ⟨1717478, by rfl⟩ : syracuseStep 2289971 = 3434957) B3434957
theorem B1675571 : Blo 1356997 1675571 := bstep (se 1 (by rfl) ⟨1256678, by rfl⟩ : syracuseStep 1675571 = 2513357) B2513357
theorem B2036033 : Blo 1356997 2036033 := bstep (se 2 (by rfl) ⟨763512, by rfl⟩ : syracuseStep 2036033 = 1527025) B1527025
theorem B2036051 : Blo 1356997 2036051 := bstep (se 1 (by rfl) ⟨1527038, by rfl⟩ : syracuseStep 2036051 = 3054077) B3054077
theorem B2175331 : Blo 1356997 2175331 := bstep (se 1 (by rfl) ⟨1631498, by rfl⟩ : syracuseStep 2175331 = 3262997) B3262997
theorem B4583789 : Blo 1356997 4583789 := bstep (se 3 (by rfl) ⟨859460, by rfl⟩ : syracuseStep 4583789 = 1718921) B1718921
theorem B2036081 : Blo 1356997 2036081 := bstep (se 2 (by rfl) ⟨763530, by rfl⟩ : syracuseStep 2036081 = 1527061) B1527061
theorem B1765747 : Blo 1356997 1765747 := bstep (se 1 (by rfl) ⟨1324310, by rfl⟩ : syracuseStep 1765747 = 2648621) B2648621
theorem B2036099 : Blo 1356997 2036099 := bstep (se 1 (by rfl) ⟨1527074, by rfl⟩ : syracuseStep 2036099 = 3054149) B3054149
theorem B3436931 : Blo 1356997 3436931 := bstep (se 1 (by rfl) ⟨2577698, by rfl⟩ : syracuseStep 3436931 = 5155397) B5155397
theorem B1528195 : Blo 1356997 1528195 := bstep (se 1 (by rfl) ⟨1146146, by rfl⟩ : syracuseStep 1528195 = 2292293) B2292293
theorem B2036129 : Blo 1356997 2036129 := bstep (se 2 (by rfl) ⟨763548, by rfl⟩ : syracuseStep 2036129 = 1527097) B1527097
theorem B4583843 : Blo 1356997 4583843 := bstep (se 1 (by rfl) ⟨3437882, by rfl⟩ : syracuseStep 4583843 = 6875765) B6875765
theorem B2290099 : Blo 1356997 2290099 := bstep (se 1 (by rfl) ⟨1717574, by rfl⟩ : syracuseStep 2290099 = 3435149) B3435149
theorem B2036147 : Blo 1356997 2036147 := bstep (se 1 (by rfl) ⟨1527110, by rfl⟩ : syracuseStep 2036147 = 3054221) B3054221
theorem B2175427 : Blo 1356997 2175427 := bstep (se 1 (by rfl) ⟨1631570, by rfl⟩ : syracuseStep 2175427 = 3263141) B3263141
theorem B2036177 : Blo 1356997 2036177 := bstep (se 2 (by rfl) ⟨763566, by rfl⟩ : syracuseStep 2036177 = 1527133) B1527133
theorem B2036195 : Blo 1356997 2036195 := bstep (se 1 (by rfl) ⟨1527146, by rfl⟩ : syracuseStep 2036195 = 3054293) B3054293
theorem B2036225 : Blo 1356997 2036225 := bstep (se 2 (by rfl) ⟨763584, by rfl⟩ : syracuseStep 2036225 = 1527169) B1527169
theorem B2036243 : Blo 1356997 2036243 := bstep (se 1 (by rfl) ⟨1527182, by rfl⟩ : syracuseStep 2036243 = 3054365) B3054365
theorem B2036273 : Blo 1356997 2036273 := bstep (se 2 (by rfl) ⟨763602, by rfl⟩ : syracuseStep 2036273 = 1527205) B1527205
theorem B2290241 : Blo 1356997 2290241 := bstep (se 2 (by rfl) ⟨858840, by rfl⟩ : syracuseStep 2290241 = 1717681) B1717681
theorem B2036291 : Blo 1356997 2036291 := bstep (se 1 (by rfl) ⟨1527218, by rfl⟩ : syracuseStep 2036291 = 3054437) B3054437
theorem B2036321 : Blo 1356997 2036321 := bstep (se 2 (by rfl) ⟨763620, by rfl⟩ : syracuseStep 2036321 = 1527241) B1527241
theorem B2175587 : Blo 1356997 2175587 := bstep (se 1 (by rfl) ⟨1631690, by rfl⟩ : syracuseStep 2175587 = 3263381) B3263381
theorem B2036339 : Blo 1356997 2036339 := bstep (se 1 (by rfl) ⟨1527254, by rfl⟩ : syracuseStep 2036339 = 3054509) B3054509
theorem B2036369 : Blo 1356997 2036369 := bstep (se 2 (by rfl) ⟨763638, by rfl⟩ : syracuseStep 2036369 = 1527277) B1527277
theorem B2036387 : Blo 1356997 2036387 := bstep (se 1 (by rfl) ⟨1527290, by rfl⟩ : syracuseStep 2036387 = 3054581) B3054581
theorem B5157539 : Blo 1356997 5157539 := bstep (se 1 (by rfl) ⟨3868154, by rfl⟩ : syracuseStep 5157539 = 7736309) B7736309
theorem B4584113 : Blo 1356997 4584113 := bstep (se 2 (by rfl) ⟨1719042, by rfl⟩ : syracuseStep 4584113 = 3438085) B3438085
theorem B5157553 : Blo 1356997 5157553 := bstep (se 2 (by rfl) ⟨1934082, by rfl⟩ : syracuseStep 5157553 = 3868165) B3868165
theorem B2290369 : Blo 1356997 2290369 := bstep (se 2 (by rfl) ⟨858888, by rfl⟩ : syracuseStep 2290369 = 1717777) B1717777
theorem B2036417 : Blo 1356997 2036417 := bstep (se 2 (by rfl) ⟨763656, by rfl⟩ : syracuseStep 2036417 = 1527313) B1527313
theorem B2577091 : Blo 1356997 2577091 := bstep (se 1 (by rfl) ⟨1932818, by rfl⟩ : syracuseStep 2577091 = 3865637) B3865637
theorem B2036435 : Blo 1356997 2036435 := bstep (se 1 (by rfl) ⟨1527326, by rfl⟩ : syracuseStep 2036435 = 3054653) B3054653
theorem B2290403 : Blo 1356997 2290403 := bstep (se 1 (by rfl) ⟨1717802, by rfl⟩ : syracuseStep 2290403 = 3435605) B3435605
theorem B2036465 : Blo 1356997 2036465 := bstep (se 2 (by rfl) ⟨763674, by rfl⟩ : syracuseStep 2036465 = 1527349) B1527349
theorem B2036483 : Blo 1356997 2036483 := bstep (se 1 (by rfl) ⟨1527362, by rfl⟩ : syracuseStep 2036483 = 3054725) B3054725
theorem B2036513 : Blo 1356997 2036513 := bstep (se 2 (by rfl) ⟨763692, by rfl⟩ : syracuseStep 2036513 = 1527385) B1527385
theorem B2036531 : Blo 1356997 2036531 := bstep (se 1 (by rfl) ⟨1527398, by rfl⟩ : syracuseStep 2036531 = 3054797) B3054797
theorem B2036561 : Blo 1356997 2036561 := bstep (se 2 (by rfl) ⟨763710, by rfl⟩ : syracuseStep 2036561 = 1527421) B1527421
theorem B2290531 : Blo 1356997 2290531 := bstep (se 1 (by rfl) ⟨1717898, by rfl⟩ : syracuseStep 2290531 = 3435797) B3435797
theorem B2577251 : Blo 1356997 2577251 := bstep (se 1 (by rfl) ⟨1932938, by rfl⟩ : syracuseStep 2577251 = 3865877) B3865877
theorem B2036579 : Blo 1356997 2036579 := bstep (se 1 (by rfl) ⟨1527434, by rfl⟩ : syracuseStep 2036579 = 3054869) B3054869
theorem B2036609 : Blo 1356997 2036609 := bstep (se 2 (by rfl) ⟨763728, by rfl⟩ : syracuseStep 2036609 = 1527457) B1527457
theorem B2036627 : Blo 1356997 2036627 := bstep (se 1 (by rfl) ⟨1527470, by rfl⟩ : syracuseStep 2036627 = 3054941) B3054941
theorem B1766291 : Blo 1356997 1766291 := bstep (se 1 (by rfl) ⟨1324718, by rfl⟩ : syracuseStep 1766291 = 2649437) B2649437
theorem B2036657 : Blo 1356997 2036657 := bstep (se 2 (by rfl) ⟨763746, by rfl⟩ : syracuseStep 2036657 = 1527493) B1527493
theorem B2036675 : Blo 1356997 2036675 := bstep (se 1 (by rfl) ⟨1527506, by rfl⟩ : syracuseStep 2036675 = 3055013) B3055013
theorem B3920849 : Blo 1356997 3920849 := bstep (se 2 (by rfl) ⟨1470318, by rfl⟩ : syracuseStep 3920849 = 2940637) B2940637
theorem B2036705 : Blo 1356997 2036705 := bstep (se 2 (by rfl) ⟨763764, by rfl⟩ : syracuseStep 2036705 = 1527529) B1527529
theorem B2290673 : Blo 1356997 2290673 := bstep (se 2 (by rfl) ⟨859002, by rfl⟩ : syracuseStep 2290673 = 1718005) B1718005
theorem B2036723 : Blo 1356997 2036723 := bstep (se 1 (by rfl) ⟨1527542, by rfl⟩ : syracuseStep 2036723 = 3055085) B3055085
theorem B4707341 : Blo 1356997 4707341 := bstep (se 3 (by rfl) ⟨882626, by rfl⟩ : syracuseStep 4707341 = 1765253) B1765253
theorem B2036753 : Blo 1356997 2036753 := bstep (se 2 (by rfl) ⟨763782, by rfl⟩ : syracuseStep 2036753 = 1527565) B1527565
theorem B2036771 : Blo 1356997 2036771 := bstep (se 1 (by rfl) ⟨1527578, by rfl⟩ : syracuseStep 2036771 = 3055157) B3055157
theorem B7730225 : Blo 1356997 7730225 := bstep (se 2 (by rfl) ⟨2898834, by rfl⟩ : syracuseStep 7730225 = 5797669) B5797669
theorem B2036801 : Blo 1356997 2036801 := bstep (se 2 (by rfl) ⟨763800, by rfl⟩ : syracuseStep 2036801 = 1527601) B1527601
theorem B2036819 : Blo 1356997 2036819 := bstep (se 1 (by rfl) ⟨1527614, by rfl⟩ : syracuseStep 2036819 = 3055229) B3055229
theorem B2290801 : Blo 1356997 2290801 := bstep (se 2 (by rfl) ⟨859050, by rfl⟩ : syracuseStep 2290801 = 1718101) B1718101
theorem B2036849 : Blo 1356997 2036849 := bstep (se 2 (by rfl) ⟨763818, by rfl⟩ : syracuseStep 2036849 = 1527637) B1527637
theorem B2036867 : Blo 1356997 2036867 := bstep (se 1 (by rfl) ⟨1527650, by rfl⟩ : syracuseStep 2036867 = 3055301) B3055301
theorem B2290835 : Blo 1356997 2290835 := bstep (se 1 (by rfl) ⟨1718126, by rfl⟩ : syracuseStep 2290835 = 3436253) B3436253
theorem B2036897 : Blo 1356997 2036897 := bstep (se 2 (by rfl) ⟨763836, by rfl⟩ : syracuseStep 2036897 = 1527673) B1527673
theorem B6526129 : Blo 1356997 6526129 := bstep (se 2 (by rfl) ⟨2447298, by rfl⟩ : syracuseStep 6526129 = 4894597) B4894597
theorem B2036915 : Blo 1356997 2036915 := bstep (se 1 (by rfl) ⟨1527686, by rfl⟩ : syracuseStep 2036915 = 3055373) B3055373
theorem B4584653 : Blo 1356997 4584653 := bstep (se 3 (by rfl) ⟨859622, by rfl⟩ : syracuseStep 4584653 = 1719245) B1719245
theorem B2036945 : Blo 1356997 2036945 := bstep (se 2 (by rfl) ⟨763854, by rfl⟩ : syracuseStep 2036945 = 1527709) B1527709
theorem B1357011 : Blo 1356997 1357011 := bstep (se 1 (by rfl) ⟨1017758, by rfl⟩ : syracuseStep 1357011 = 2035517) B2035517
theorem B1357027 : Blo 1356997 1357027 := bstep (se 1 (by rfl) ⟨1017770, by rfl⟩ : syracuseStep 1357027 = 2035541) B2035541
theorem B2036963 : Blo 1356997 2036963 := bstep (se 1 (by rfl) ⟨1527722, by rfl⟩ : syracuseStep 2036963 = 3055445) B3055445
theorem B6870257 : Blo 1356997 6870257 := bstep (se 2 (by rfl) ⟨2576346, by rfl⟩ : syracuseStep 6870257 = 5152693) B5152693
theorem B1357043 : Blo 1356997 1357043 := bstep (se 1 (by rfl) ⟨1017782, by rfl⟩ : syracuseStep 1357043 = 2035565) B2035565
theorem B2036993 : Blo 1356997 2036993 := bstep (se 2 (by rfl) ⟨763872, by rfl⟩ : syracuseStep 2036993 = 1527745) B1527745
theorem B1357059 : Blo 1356997 1357059 := bstep (se 1 (by rfl) ⟨1017794, by rfl⟩ : syracuseStep 1357059 = 2035589) B2035589
theorem B4584707 : Blo 1356997 4584707 := bstep (se 1 (by rfl) ⟨3438530, by rfl⟩ : syracuseStep 4584707 = 6877061) B6877061
theorem B1357075 : Blo 1356997 1357075 := bstep (se 1 (by rfl) ⟨1017806, by rfl⟩ : syracuseStep 1357075 = 2035613) B2035613
theorem B2290963 : Blo 1356997 2290963 := bstep (se 1 (by rfl) ⟨1718222, by rfl⟩ : syracuseStep 2290963 = 3436445) B3436445
theorem B2037011 : Blo 1356997 2037011 := bstep (se 1 (by rfl) ⟨1527758, by rfl⟩ : syracuseStep 2037011 = 3055517) B3055517
theorem B1357091 : Blo 1356997 1357091 := bstep (se 1 (by rfl) ⟨1017818, by rfl⟩ : syracuseStep 1357091 = 2035637) B2035637
theorem B2037041 : Blo 1356997 2037041 := bstep (se 2 (by rfl) ⟨763890, by rfl⟩ : syracuseStep 2037041 = 1527781) B1527781
theorem B3437873 : Blo 1356997 3437873 := bstep (se 2 (by rfl) ⟨1289202, by rfl⟩ : syracuseStep 3437873 = 2578405) B2578405
theorem B1357107 : Blo 1356997 1357107 := bstep (se 1 (by rfl) ⟨1017830, by rfl⟩ : syracuseStep 1357107 = 2035661) B2035661
theorem B1357123 : Blo 1356997 1357123 := bstep (se 1 (by rfl) ⟨1017842, by rfl⟩ : syracuseStep 1357123 = 2035685) B2035685
theorem B2037059 : Blo 1356997 2037059 := bstep (se 1 (by rfl) ⟨1527794, by rfl⟩ : syracuseStep 2037059 = 3055589) B3055589
theorem B1357139 : Blo 1356997 1357139 := bstep (se 1 (by rfl) ⟨1017854, by rfl⟩ : syracuseStep 1357139 = 2035709) B2035709
theorem B2037089 : Blo 1356997 2037089 := bstep (se 2 (by rfl) ⟨763908, by rfl⟩ : syracuseStep 2037089 = 1527817) B1527817
theorem B1357155 : Blo 1356997 1357155 := bstep (se 1 (by rfl) ⟨1017866, by rfl⟩ : syracuseStep 1357155 = 2035733) B2035733
theorem B3437923 : Blo 1356997 3437923 := bstep (se 1 (by rfl) ⟨2578442, by rfl⟩ : syracuseStep 3437923 = 5156885) B5156885
theorem B1357171 : Blo 1356997 1357171 := bstep (se 1 (by rfl) ⟨1017878, by rfl⟩ : syracuseStep 1357171 = 2035757) B2035757
theorem B2037107 : Blo 1356997 2037107 := bstep (se 1 (by rfl) ⟨1527830, by rfl⟩ : syracuseStep 2037107 = 3055661) B3055661
theorem B1357187 : Blo 1356997 1357187 := bstep (se 1 (by rfl) ⟨1017890, by rfl⟩ : syracuseStep 1357187 = 2035781) B2035781
theorem B2037137 : Blo 1356997 2037137 := bstep (se 2 (by rfl) ⟨763926, by rfl⟩ : syracuseStep 2037137 = 1527853) B1527853
theorem B1357203 : Blo 1356997 1357203 := bstep (se 1 (by rfl) ⟨1017902, by rfl⟩ : syracuseStep 1357203 = 2035805) B2035805
theorem B2291105 : Blo 1356997 2291105 := bstep (se 2 (by rfl) ⟨859164, by rfl⟩ : syracuseStep 2291105 = 1718329) B1718329
theorem B1357219 : Blo 1356997 1357219 := bstep (se 1 (by rfl) ⟨1017914, by rfl⟩ : syracuseStep 1357219 = 2035829) B2035829
theorem B2037155 : Blo 1356997 2037155 := bstep (se 1 (by rfl) ⟨1527866, by rfl⟩ : syracuseStep 2037155 = 3055733) B3055733
theorem B1357235 : Blo 1356997 1357235 := bstep (se 1 (by rfl) ⟨1017926, by rfl⟩ : syracuseStep 1357235 = 2035853) B2035853
theorem B2037185 : Blo 1356997 2037185 := bstep (se 2 (by rfl) ⟨763944, by rfl⟩ : syracuseStep 2037185 = 1527889) B1527889
theorem B1357251 : Blo 1356997 1357251 := bstep (se 1 (by rfl) ⟨1017938, by rfl⟩ : syracuseStep 1357251 = 2035877) B2035877
theorem B2446787 : Blo 1356997 2446787 := bstep (se 1 (by rfl) ⟨1835090, by rfl⟩ : syracuseStep 2446787 = 3670181) B3670181
theorem B1357267 : Blo 1356997 1357267 := bstep (se 1 (by rfl) ⟨1017950, by rfl⟩ : syracuseStep 1357267 = 2035901) B2035901
theorem B2037203 : Blo 1356997 2037203 := bstep (se 1 (by rfl) ⟨1527902, by rfl⟩ : syracuseStep 2037203 = 3055805) B3055805
theorem B1357283 : Blo 1356997 1357283 := bstep (se 1 (by rfl) ⟨1017962, by rfl⟩ : syracuseStep 1357283 = 2035925) B2035925
theorem B2037233 : Blo 1356997 2037233 := bstep (se 2 (by rfl) ⟨763962, by rfl⟩ : syracuseStep 2037233 = 1527925) B1527925
theorem B3438065 : Blo 1356997 3438065 := bstep (se 2 (by rfl) ⟨1289274, by rfl⟩ : syracuseStep 3438065 = 2578549) B2578549
theorem B1357299 : Blo 1356997 1357299 := bstep (se 1 (by rfl) ⟨1017974, by rfl⟩ : syracuseStep 1357299 = 2035949) B2035949
theorem B1570291 : Blo 1356997 1570291 := bstep (se 1 (by rfl) ⟨1177718, by rfl⟩ : syracuseStep 1570291 = 2355437) B2355437
theorem B1357315 : Blo 1356997 1357315 := bstep (se 1 (by rfl) ⟨1017986, by rfl⟩ : syracuseStep 1357315 = 2035973) B2035973
theorem B2037251 : Blo 1356997 2037251 := bstep (se 1 (by rfl) ⟨1527938, by rfl⟩ : syracuseStep 2037251 = 3055877) B3055877
theorem B1357331 : Blo 1356997 1357331 := bstep (se 1 (by rfl) ⟨1017998, by rfl⟩ : syracuseStep 1357331 = 2035997) B2035997
theorem B2291233 : Blo 1356997 2291233 := bstep (se 2 (by rfl) ⟨859212, by rfl⟩ : syracuseStep 2291233 = 1718425) B1718425
theorem B2037281 : Blo 1356997 2037281 := bstep (se 2 (by rfl) ⟨763980, by rfl⟩ : syracuseStep 2037281 = 1527961) B1527961
theorem B1357347 : Blo 1356997 1357347 := bstep (se 1 (by rfl) ⟨1018010, by rfl⟩ : syracuseStep 1357347 = 2036021) B2036021
theorem B1357363 : Blo 1356997 1357363 := bstep (se 1 (by rfl) ⟨1018022, by rfl⟩ : syracuseStep 1357363 = 2036045) B2036045
theorem B2037299 : Blo 1356997 2037299 := bstep (se 1 (by rfl) ⟨1527974, by rfl⟩ : syracuseStep 2037299 = 3055949) B3055949
theorem B1357379 : Blo 1356997 1357379 := bstep (se 1 (by rfl) ⟨1018034, by rfl⟩ : syracuseStep 1357379 = 2036069) B2036069
theorem B2291267 : Blo 1356997 2291267 := bstep (se 1 (by rfl) ⟨1718450, by rfl⟩ : syracuseStep 2291267 = 3436901) B3436901
theorem B2233937 : Blo 1356997 2233937 := bstep (se 2 (by rfl) ⟨837726, by rfl⟩ : syracuseStep 2233937 = 1675453) B1675453
theorem B2037329 : Blo 1356997 2037329 := bstep (se 2 (by rfl) ⟨763998, by rfl⟩ : syracuseStep 2037329 = 1527997) B1527997
theorem B1717843 : Blo 1356997 1717843 := bstep (se 1 (by rfl) ⟨1288382, by rfl⟩ : syracuseStep 1717843 = 2576765) B2576765
theorem B1357395 : Blo 1356997 1357395 := bstep (se 1 (by rfl) ⟨1018046, by rfl⟩ : syracuseStep 1357395 = 2036093) B2036093
theorem B1357411 : Blo 1356997 1357411 := bstep (se 1 (by rfl) ⟨1018058, by rfl⟩ : syracuseStep 1357411 = 2036117) B2036117
theorem B2037347 : Blo 1356997 2037347 := bstep (se 1 (by rfl) ⟨1528010, by rfl⟩ : syracuseStep 2037347 = 3056021) B3056021
theorem B1357427 : Blo 1356997 1357427 := bstep (se 1 (by rfl) ⟨1018070, by rfl⟩ : syracuseStep 1357427 = 2036141) B2036141
theorem B2037377 : Blo 1356997 2037377 := bstep (se 2 (by rfl) ⟨764016, by rfl⟩ : syracuseStep 2037377 = 1528033) B1528033
theorem B1357443 : Blo 1356997 1357443 := bstep (se 1 (by rfl) ⟨1018082, by rfl⟩ : syracuseStep 1357443 = 2036165) B2036165
theorem B1357459 : Blo 1356997 1357459 := bstep (se 1 (by rfl) ⟨1018094, by rfl⟩ : syracuseStep 1357459 = 2036189) B2036189
theorem B2037395 : Blo 1356997 2037395 := bstep (se 1 (by rfl) ⟨1528046, by rfl⟩ : syracuseStep 2037395 = 3056093) B3056093
theorem B1357475 : Blo 1356997 1357475 := bstep (se 1 (by rfl) ⟨1018106, by rfl⟩ : syracuseStep 1357475 = 2036213) B2036213
theorem B2037425 : Blo 1356997 2037425 := bstep (se 2 (by rfl) ⟨764034, by rfl⟩ : syracuseStep 2037425 = 1528069) B1528069
theorem B1717939 : Blo 1356997 1717939 := bstep (se 1 (by rfl) ⟨1288454, by rfl⟩ : syracuseStep 1717939 = 2576909) B2576909
theorem B1357491 : Blo 1356997 1357491 := bstep (se 1 (by rfl) ⟨1018118, by rfl⟩ : syracuseStep 1357491 = 2036237) B2036237
theorem B1357507 : Blo 1356997 1357507 := bstep (se 1 (by rfl) ⟨1018130, by rfl⟩ : syracuseStep 1357507 = 2036261) B2036261
theorem B2291395 : Blo 1356997 2291395 := bstep (se 1 (by rfl) ⟨1718546, by rfl⟩ : syracuseStep 2291395 = 3437093) B3437093
theorem B2037443 : Blo 1356997 2037443 := bstep (se 1 (by rfl) ⟨1528082, by rfl⟩ : syracuseStep 2037443 = 3056165) B3056165
theorem B1357523 : Blo 1356997 1357523 := bstep (se 1 (by rfl) ⟨1018142, by rfl⟩ : syracuseStep 1357523 = 2036285) B2036285
theorem B2037473 : Blo 1356997 2037473 := bstep (se 2 (by rfl) ⟨764052, by rfl⟩ : syracuseStep 2037473 = 1528105) B1528105
theorem B1357539 : Blo 1356997 1357539 := bstep (se 1 (by rfl) ⟨1018154, by rfl⟩ : syracuseStep 1357539 = 2036309) B2036309
theorem B1357555 : Blo 1356997 1357555 := bstep (se 1 (by rfl) ⟨1018166, by rfl⟩ : syracuseStep 1357555 = 2036333) B2036333
theorem B2037491 : Blo 1356997 2037491 := bstep (se 1 (by rfl) ⟨1528118, by rfl⟩ : syracuseStep 2037491 = 3056237) B3056237
theorem B1357571 : Blo 1356997 1357571 := bstep (se 1 (by rfl) ⟨1018178, by rfl⟩ : syracuseStep 1357571 = 2036357) B2036357
theorem B2037521 : Blo 1356997 2037521 := bstep (se 2 (by rfl) ⟨764070, by rfl⟩ : syracuseStep 2037521 = 1528141) B1528141
theorem B1357587 : Blo 1356997 1357587 := bstep (se 1 (by rfl) ⟨1018190, by rfl⟩ : syracuseStep 1357587 = 2036381) B2036381
theorem B1357603 : Blo 1356997 1357603 := bstep (se 1 (by rfl) ⟨1018202, by rfl⟩ : syracuseStep 1357603 = 2036405) B2036405
theorem B2037539 : Blo 1356997 2037539 := bstep (se 1 (by rfl) ⟨1528154, by rfl⟩ : syracuseStep 2037539 = 3056309) B3056309
theorem B1357619 : Blo 1356997 1357619 := bstep (se 1 (by rfl) ⟨1018214, by rfl⟩ : syracuseStep 1357619 = 2036429) B2036429
theorem B2037569 : Blo 1356997 2037569 := bstep (se 2 (by rfl) ⟨764088, by rfl⟩ : syracuseStep 2037569 = 1528177) B1528177
theorem B4347715 : Blo 1356997 4347715 := bstep (se 1 (by rfl) ⟨3260786, by rfl⟩ : syracuseStep 4347715 = 6521573) B6521573
theorem B1357635 : Blo 1356997 1357635 := bstep (se 1 (by rfl) ⟨1018226, by rfl⟩ : syracuseStep 1357635 = 2036453) B2036453
theorem B3053393 : Blo 1356997 3053393 := bstep (se 2 (by rfl) ⟨1145022, by rfl⟩ : syracuseStep 3053393 = 2290045) B2290045
theorem B2291537 : Blo 1356997 2291537 := bstep (se 2 (by rfl) ⟨859326, by rfl⟩ : syracuseStep 2291537 = 1718653) B1718653
theorem B1357651 : Blo 1356997 1357651 := bstep (se 1 (by rfl) ⟨1018238, by rfl⟩ : syracuseStep 1357651 = 2036477) B2036477
theorem B2037587 : Blo 1356997 2037587 := bstep (se 1 (by rfl) ⟨1528190, by rfl⟩ : syracuseStep 2037587 = 3056381) B3056381
theorem B3864419 : Blo 1356997 3864419 := bstep (se 1 (by rfl) ⟨2898314, by rfl⟩ : syracuseStep 3864419 = 5796629) B5796629
theorem B3053411 : Blo 1356997 3053411 := bstep (se 1 (by rfl) ⟨2290058, by rfl⟩ : syracuseStep 3053411 = 4580117) B4580117
theorem B1357667 : Blo 1356997 1357667 := bstep (se 1 (by rfl) ⟨1018250, by rfl⟩ : syracuseStep 1357667 = 2036501) B2036501
theorem B2037617 : Blo 1356997 2037617 := bstep (se 2 (by rfl) ⟨764106, by rfl⟩ : syracuseStep 2037617 = 1528213) B1528213
theorem B1357683 : Blo 1356997 1357683 := bstep (se 1 (by rfl) ⟨1018262, by rfl⟩ : syracuseStep 1357683 = 2036525) B2036525
theorem B1357699 : Blo 1356997 1357699 := bstep (se 1 (by rfl) ⟨1018274, by rfl⟩ : syracuseStep 1357699 = 2036549) B2036549
theorem B2037635 : Blo 1356997 2037635 := bstep (se 1 (by rfl) ⟨1528226, by rfl⟩ : syracuseStep 2037635 = 3056453) B3056453
theorem B2578321 : Blo 1356997 2578321 := bstep (se 2 (by rfl) ⟨966870, by rfl⟩ : syracuseStep 2578321 = 1933741) B1933741
theorem B1357715 : Blo 1356997 1357715 := bstep (se 1 (by rfl) ⟨1018286, by rfl⟩ : syracuseStep 1357715 = 2036573) B2036573
theorem B2037665 : Blo 1356997 2037665 := bstep (se 2 (by rfl) ⟨764124, by rfl⟩ : syracuseStep 2037665 = 1528249) B1528249
theorem B1357731 : Blo 1356997 1357731 := bstep (se 1 (by rfl) ⟨1018298, by rfl⟩ : syracuseStep 1357731 = 2036597) B2036597
theorem B1357747 : Blo 1356997 1357747 := bstep (se 1 (by rfl) ⟨1018310, by rfl⟩ : syracuseStep 1357747 = 2036621) B2036621
theorem B2037683 : Blo 1356997 2037683 := bstep (se 1 (by rfl) ⟨1528262, by rfl⟩ : syracuseStep 2037683 = 3056525) B3056525
theorem B1357763 : Blo 1356997 1357763 := bstep (se 1 (by rfl) ⟨1018322, by rfl⟩ : syracuseStep 1357763 = 2036645) B2036645
theorem B35739589 : Blo 1356997 35739589 := bstep (se 4 (by rfl) ⟨3350586, by rfl⟩ : syracuseStep 35739589 = 6701173) B6701173
theorem B2291665 : Blo 1356997 2291665 := bstep (se 2 (by rfl) ⟨859374, by rfl⟩ : syracuseStep 2291665 = 1718749) B1718749
theorem B2037713 : Blo 1356997 2037713 := bstep (se 2 (by rfl) ⟨764142, by rfl⟩ : syracuseStep 2037713 = 1528285) B1528285
theorem B1357779 : Blo 1356997 1357779 := bstep (se 1 (by rfl) ⟨1018334, by rfl⟩ : syracuseStep 1357779 = 2036669) B2036669
theorem B1357795 : Blo 1356997 1357795 := bstep (se 1 (by rfl) ⟨1018346, by rfl⟩ : syracuseStep 1357795 = 2036693) B2036693
theorem B2037731 : Blo 1356997 2037731 := bstep (se 1 (by rfl) ⟨1528298, by rfl⟩ : syracuseStep 2037731 = 3056597) B3056597
theorem B1357811 : Blo 1356997 1357811 := bstep (se 1 (by rfl) ⟨1018358, by rfl⟩ : syracuseStep 1357811 = 2036717) B2036717
theorem B2291699 : Blo 1356997 2291699 := bstep (se 1 (by rfl) ⟨1718774, by rfl⟩ : syracuseStep 2291699 = 3437549) B3437549
theorem B1357827 : Blo 1356997 1357827 := bstep (se 1 (by rfl) ⟨1018370, by rfl⟩ : syracuseStep 1357827 = 2036741) B2036741
theorem B1357843 : Blo 1356997 1357843 := bstep (se 1 (by rfl) ⟨1018382, by rfl⟩ : syracuseStep 1357843 = 2036765) B2036765
theorem B3864611 : Blo 1356997 3864611 := bstep (se 1 (by rfl) ⟨2898458, by rfl⟩ : syracuseStep 3864611 = 5796917) B5796917
theorem B1357859 : Blo 1356997 1357859 := bstep (se 1 (by rfl) ⟨1018394, by rfl⟩ : syracuseStep 1357859 = 2036789) B2036789
theorem B1357875 : Blo 1356997 1357875 := bstep (se 1 (by rfl) ⟨1018406, by rfl⟩ : syracuseStep 1357875 = 2036813) B2036813
theorem B1357891 : Blo 1356997 1357891 := bstep (se 1 (by rfl) ⟨1018418, by rfl⟩ : syracuseStep 1357891 = 2036837) B2036837
theorem B1357907 : Blo 1356997 1357907 := bstep (se 1 (by rfl) ⟨1018430, by rfl⟩ : syracuseStep 1357907 = 2036861) B2036861
theorem B1357923 : Blo 1356997 1357923 := bstep (se 1 (by rfl) ⟨1018442, by rfl⟩ : syracuseStep 1357923 = 2036885) B2036885
theorem B3053681 : Blo 1356997 3053681 := bstep (se 2 (by rfl) ⟨1145130, by rfl⟩ : syracuseStep 3053681 = 2290261) B2290261
theorem B1357939 : Blo 1356997 1357939 := bstep (se 1 (by rfl) ⟨1018454, by rfl⟩ : syracuseStep 1357939 = 2036909) B2036909
theorem B2291827 : Blo 1356997 2291827 := bstep (se 1 (by rfl) ⟨1718870, by rfl⟩ : syracuseStep 2291827 = 3437741) B3437741
theorem B3053699 : Blo 1356997 3053699 := bstep (se 1 (by rfl) ⟨2290274, by rfl⟩ : syracuseStep 3053699 = 4580549) B4580549
theorem B1357955 : Blo 1356997 1357955 := bstep (se 1 (by rfl) ⟨1018466, by rfl⟩ : syracuseStep 1357955 = 2036933) B2036933
theorem B1357971 : Blo 1356997 1357971 := bstep (se 1 (by rfl) ⟨1018478, by rfl⟩ : syracuseStep 1357971 = 2036957) B2036957
theorem B1718435 : Blo 1356997 1718435 := bstep (se 1 (by rfl) ⟨1288826, by rfl⟩ : syracuseStep 1718435 = 2577653) B2577653
theorem B1357987 : Blo 1356997 1357987 := bstep (se 1 (by rfl) ⟨1018490, by rfl⟩ : syracuseStep 1357987 = 2036981) B2036981
theorem B1358003 : Blo 1356997 1358003 := bstep (se 1 (by rfl) ⟨1018502, by rfl⟩ : syracuseStep 1358003 = 2037005) B2037005
theorem B1358019 : Blo 1356997 1358019 := bstep (se 1 (by rfl) ⟨1018514, by rfl⟩ : syracuseStep 1358019 = 2037029) B2037029
theorem B1358035 : Blo 1356997 1358035 := bstep (se 1 (by rfl) ⟨1018526, by rfl⟩ : syracuseStep 1358035 = 2037053) B2037053
theorem B1358051 : Blo 1356997 1358051 := bstep (se 1 (by rfl) ⟨1018538, by rfl⟩ : syracuseStep 1358051 = 2037077) B2037077
theorem B2447587 : Blo 1356997 2447587 := bstep (se 1 (by rfl) ⟨1835690, by rfl⟩ : syracuseStep 2447587 = 3671381) B3671381
theorem B1358067 : Blo 1356997 1358067 := bstep (se 1 (by rfl) ⟨1018550, by rfl⟩ : syracuseStep 1358067 = 2037101) B2037101
theorem B2291969 : Blo 1356997 2291969 := bstep (se 2 (by rfl) ⟨859488, by rfl⟩ : syracuseStep 2291969 = 1718977) B1718977
theorem B1358083 : Blo 1356997 1358083 := bstep (se 1 (by rfl) ⟨1018562, by rfl⟩ : syracuseStep 1358083 = 2037125) B2037125
theorem B1358099 : Blo 1356997 1358099 := bstep (se 1 (by rfl) ⟨1018574, by rfl⟩ : syracuseStep 1358099 = 2037149) B2037149
theorem B1358115 : Blo 1356997 1358115 := bstep (se 1 (by rfl) ⟨1018586, by rfl⟩ : syracuseStep 1358115 = 2037173) B2037173
theorem B1358131 : Blo 1356997 1358131 := bstep (se 1 (by rfl) ⟨1018598, by rfl⟩ : syracuseStep 1358131 = 2037197) B2037197
theorem B1358147 : Blo 1356997 1358147 := bstep (se 1 (by rfl) ⟨1018610, by rfl⟩ : syracuseStep 1358147 = 2037221) B2037221
theorem B1358163 : Blo 1356997 1358163 := bstep (se 1 (by rfl) ⟨1018622, by rfl⟩ : syracuseStep 1358163 = 2037245) B2037245
theorem B1358179 : Blo 1356997 1358179 := bstep (se 1 (by rfl) ⟨1018634, by rfl⟩ : syracuseStep 1358179 = 2037269) B2037269
theorem B1358195 : Blo 1356997 1358195 := bstep (se 1 (by rfl) ⟨1018646, by rfl⟩ : syracuseStep 1358195 = 2037293) B2037293
theorem B2292097 : Blo 1356997 2292097 := bstep (se 2 (by rfl) ⟨859536, by rfl⟩ : syracuseStep 2292097 = 1719073) B1719073
theorem B1358211 : Blo 1356997 1358211 := bstep (se 1 (by rfl) ⟨1018658, by rfl⟩ : syracuseStep 1358211 = 2037317) B2037317
theorem B3053969 : Blo 1356997 3053969 := bstep (se 2 (by rfl) ⟨1145238, by rfl⟩ : syracuseStep 3053969 = 2290477) B2290477
theorem B1358227 : Blo 1356997 1358227 := bstep (se 1 (by rfl) ⟨1018670, by rfl⟩ : syracuseStep 1358227 = 2037341) B2037341
theorem B3053987 : Blo 1356997 3053987 := bstep (se 1 (by rfl) ⟨2290490, by rfl⟩ : syracuseStep 3053987 = 4580981) B4580981
theorem B1358243 : Blo 1356997 1358243 := bstep (se 1 (by rfl) ⟨1018682, by rfl⟩ : syracuseStep 1358243 = 2037365) B2037365
theorem B2292131 : Blo 1356997 2292131 := bstep (se 1 (by rfl) ⟨1719098, by rfl⟩ : syracuseStep 2292131 = 3438197) B3438197
theorem B1358259 : Blo 1356997 1358259 := bstep (se 1 (by rfl) ⟨1018694, by rfl⟩ : syracuseStep 1358259 = 2037389) B2037389
theorem B1358275 : Blo 1356997 1358275 := bstep (se 1 (by rfl) ⟨1018706, by rfl⟩ : syracuseStep 1358275 = 2037413) B2037413
theorem B1358291 : Blo 1356997 1358291 := bstep (se 1 (by rfl) ⟨1018718, by rfl⟩ : syracuseStep 1358291 = 2037437) B2037437
theorem B7731683 : Blo 1356997 7731683 := bstep (se 1 (by rfl) ⟨5798762, by rfl⟩ : syracuseStep 7731683 = 11597525) B11597525
theorem B1358307 : Blo 1356997 1358307 := bstep (se 1 (by rfl) ⟨1018730, by rfl⟩ : syracuseStep 1358307 = 2037461) B2037461
theorem B1358323 : Blo 1356997 1358323 := bstep (se 1 (by rfl) ⟨1018742, by rfl⟩ : syracuseStep 1358323 = 2037485) B2037485
theorem B1358339 : Blo 1356997 1358339 := bstep (se 1 (by rfl) ⟨1018754, by rfl⟩ : syracuseStep 1358339 = 2037509) B2037509
theorem B1358355 : Blo 1356997 1358355 := bstep (se 1 (by rfl) ⟨1018766, by rfl⟩ : syracuseStep 1358355 = 2037533) B2037533
theorem B1358371 : Blo 1356997 1358371 := bstep (se 1 (by rfl) ⟨1018778, by rfl⟩ : syracuseStep 1358371 = 2037557) B2037557
theorem B2292259 : Blo 1356997 2292259 := bstep (se 1 (by rfl) ⟨1719194, by rfl⟩ : syracuseStep 2292259 = 3438389) B3438389
theorem B1358387 : Blo 1356997 1358387 := bstep (se 1 (by rfl) ⟨1018790, by rfl⟩ : syracuseStep 1358387 = 2037581) B2037581
theorem B1358403 : Blo 1356997 1358403 := bstep (se 1 (by rfl) ⟨1018802, by rfl⟩ : syracuseStep 1358403 = 2037605) B2037605
theorem B14678597 : Blo 1356997 14678597 := bstep (se 4 (by rfl) ⟨1376118, by rfl⟩ : syracuseStep 14678597 = 2752237) B2752237
theorem B1358419 : Blo 1356997 1358419 := bstep (se 1 (by rfl) ⟨1018814, by rfl⟩ : syracuseStep 1358419 = 2037629) B2037629
theorem B1358435 : Blo 1356997 1358435 := bstep (se 1 (by rfl) ⟨1018826, by rfl⟩ : syracuseStep 1358435 = 2037653) B2037653
theorem B1358451 : Blo 1356997 1358451 := bstep (se 1 (by rfl) ⟨1018838, by rfl⟩ : syracuseStep 1358451 = 2037677) B2037677
theorem B1358467 : Blo 1356997 1358467 := bstep (se 1 (by rfl) ⟨1018850, by rfl⟩ : syracuseStep 1358467 = 2037701) B2037701
theorem B1358483 : Blo 1356997 1358483 := bstep (se 1 (by rfl) ⟨1018862, by rfl⟩ : syracuseStep 1358483 = 2037725) B2037725
theorem B2898595 : Blo 1356997 2898595 := bstep (se 1 (by rfl) ⟨2173946, by rfl⟩ : syracuseStep 2898595 = 4347893) B4347893
theorem B6871715 : Blo 1356997 6871715 := bstep (se 1 (by rfl) ⟨5153786, by rfl⟩ : syracuseStep 6871715 = 10307573) B10307573
theorem B3054257 : Blo 1356997 3054257 := bstep (se 2 (by rfl) ⟨1145346, by rfl⟩ : syracuseStep 3054257 = 2290693) B2290693
theorem B2292401 : Blo 1356997 2292401 := bstep (se 2 (by rfl) ⟨859650, by rfl⟩ : syracuseStep 2292401 = 1719301) B1719301
theorem B3054275 : Blo 1356997 3054275 := bstep (se 1 (by rfl) ⟨2290706, by rfl⟩ : syracuseStep 3054275 = 4581413) B4581413
theorem B5798627 : Blo 1356997 5798627 := bstep (se 1 (by rfl) ⟨4348970, by rfl⟩ : syracuseStep 5798627 = 8697941) B8697941
theorem B10312433 : Blo 1356997 10312433 := bstep (se 2 (by rfl) ⟨3867162, by rfl⟩ : syracuseStep 10312433 = 7734325) B7734325
theorem B3668753 : Blo 1356997 3668753 := bstep (se 2 (by rfl) ⟨1375782, by rfl⟩ : syracuseStep 3668753 = 2751565) B2751565
theorem B3865421 : Blo 1356997 3865421 := bstep (se 3 (by rfl) ⟨724766, by rfl⟩ : syracuseStep 3865421 = 1449533) B1449533
theorem B1719139 : Blo 1356997 1719139 := bstep (se 1 (by rfl) ⟨1289354, by rfl⟩ : syracuseStep 1719139 = 2578709) B2578709
theorem B3668881 : Blo 1356997 3668881 := bstep (se 2 (by rfl) ⟨1375830, by rfl⟩ : syracuseStep 3668881 = 2751661) B2751661
theorem B1719235 : Blo 1356997 1719235 := bstep (se 1 (by rfl) ⟨1289426, by rfl⟩ : syracuseStep 1719235 = 2578853) B2578853
theorem B3054545 : Blo 1356997 3054545 := bstep (se 2 (by rfl) ⟨1145454, by rfl⟩ : syracuseStep 3054545 = 2290909) B2290909
theorem B3054563 : Blo 1356997 3054563 := bstep (se 1 (by rfl) ⟨2290922, by rfl⟩ : syracuseStep 3054563 = 4581845) B4581845
theorem B2898929 : Blo 1356997 2898929 := bstep (se 2 (by rfl) ⟨1087098, by rfl⟩ : syracuseStep 2898929 = 2174197) B2174197
theorem B3865603 : Blo 1356997 3865603 := bstep (se 1 (by rfl) ⟨2899202, by rfl⟩ : syracuseStep 3865603 = 5798405) B5798405
theorem B4709389 : Blo 1356997 4709389 := bstep (se 3 (by rfl) ⟨883010, by rfl⟩ : syracuseStep 4709389 = 1766021) B1766021
theorem B1547491 : Blo 1356997 1547491 := bstep (se 1 (by rfl) ⟨1160618, by rfl⟩ : syracuseStep 1547491 = 2321237) B2321237
theorem B3054833 : Blo 1356997 3054833 := bstep (se 2 (by rfl) ⟨1145562, by rfl⟩ : syracuseStep 3054833 = 2291125) B2291125
theorem B1932545 : Blo 1356997 1932545 := bstep (se 2 (by rfl) ⟨724704, by rfl⟩ : syracuseStep 1932545 = 1449409) B1449409
theorem B3054851 : Blo 1356997 3054851 := bstep (se 1 (by rfl) ⟨2291138, by rfl⟩ : syracuseStep 3054851 = 4582277) B4582277
theorem B4128077 : Blo 1356997 4128077 := bstep (se 3 (by rfl) ⟨774014, by rfl⟩ : syracuseStep 4128077 = 1548029) B1548029
theorem B11599301 : Blo 1356997 11599301 := bstep (se 4 (by rfl) ⟨1087434, by rfl⟩ : syracuseStep 11599301 = 2174869) B2174869
theorem B6872525 : Blo 1356997 6872525 := bstep (se 3 (by rfl) ⟨1288598, by rfl⟩ : syracuseStep 6872525 = 2577197) B2577197
theorem B7732685 : Blo 1356997 7732685 := bstep (se 3 (by rfl) ⟨1449878, by rfl⟩ : syracuseStep 7732685 = 2899757) B2899757
theorem B3866093 : Blo 1356997 3866093 := bstep (se 3 (by rfl) ⟨724892, by rfl⟩ : syracuseStep 3866093 = 1449785) B1449785
theorem B3055121 : Blo 1356997 3055121 := bstep (se 2 (by rfl) ⟨1145670, by rfl⟩ : syracuseStep 3055121 = 2291341) B2291341
theorem B3055139 : Blo 1356997 3055139 := bstep (se 1 (by rfl) ⟨2291354, by rfl⟩ : syracuseStep 3055139 = 4582709) B4582709
theorem B6192881 : Blo 1356997 6192881 := bstep (se 2 (by rfl) ⟨2322330, by rfl⟩ : syracuseStep 6192881 = 4644661) B4644661
theorem B1933075 : Blo 1356997 1933075 := bstep (se 1 (by rfl) ⟨1449806, by rfl⟩ : syracuseStep 1933075 = 2899613) B2899613
theorem B3055409 : Blo 1356997 3055409 := bstep (se 2 (by rfl) ⟨1145778, by rfl⟩ : syracuseStep 3055409 = 2291557) B2291557
theorem B3055427 : Blo 1356997 3055427 := bstep (se 1 (by rfl) ⟨2291570, by rfl⟩ : syracuseStep 3055427 = 4583141) B4583141
theorem B4407139 : Blo 1356997 4407139 := bstep (se 1 (by rfl) ⟨3305354, by rfl⟩ : syracuseStep 4407139 = 6610709) B6610709
theorem B7077773 : Blo 1356997 7077773 := bstep (se 3 (by rfl) ⟨1327082, by rfl⟩ : syracuseStep 7077773 = 2654165) B2654165
theorem B4349933 : Blo 1356997 4349933 := bstep (se 3 (by rfl) ⟨815612, by rfl⟩ : syracuseStep 4349933 = 1631225) B1631225
theorem B3096587 : Blo 1356997 3096587 := bstep (se 1 (by rfl) ⟨2322440, by rfl⟩ : syracuseStep 3096587 = 4644881) B4644881
theorem B1933399 : Blo 1356997 1933399 := bstep (se 1 (by rfl) ⟨1450049, by rfl⟩ : syracuseStep 1933399 = 2900099) B2900099
theorem B10305629 : Blo 1356997 10305629 := bstep (se 3 (by rfl) ⟨1932305, by rfl⟩ : syracuseStep 10305629 = 3864611) B3864611
theorem B3055769 : Blo 1356997 3055769 := bstep (se 2 (by rfl) ⟨1145913, by rfl⟩ : syracuseStep 3055769 = 2291827) B2291827
theorem B2064599 : Blo 1356997 2064599 := bstep (se 1 (by rfl) ⟨1548449, by rfl⟩ : syracuseStep 2064599 = 3096899) B3096899
theorem B3055859 : Blo 1356997 3055859 := bstep (se 1 (by rfl) ⟨2291894, by rfl⟩ : syracuseStep 3055859 = 4583789) B4583789
theorem B3055895 : Blo 1356997 3055895 := bstep (se 1 (by rfl) ⟨2291921, by rfl⟩ : syracuseStep 3055895 = 4583843) B4583843
theorem B1450391 : Blo 1356997 1450391 := bstep (se 1 (by rfl) ⟨1087793, by rfl⟩ : syracuseStep 1450391 = 2175587) B2175587
theorem B3056075 : Blo 1356997 3056075 := bstep (se 1 (by rfl) ⟨2292056, by rfl⟩ : syracuseStep 3056075 = 4584113) B4584113
theorem B2900441 : Blo 1356997 2900441 := bstep (se 2 (by rfl) ⟨1087665, by rfl⟩ : syracuseStep 2900441 = 2175331) B2175331
theorem B3056129 : Blo 1356997 3056129 := bstep (se 2 (by rfl) ⟨1146048, by rfl⟩ : syracuseStep 3056129 = 2292097) B2292097
theorem B7733825 : Blo 1356997 7733825 := bstep (se 2 (by rfl) ⟨2900184, by rfl⟩ : syracuseStep 7733825 = 5800369) B5800369
theorem B2613899 : Blo 1356997 2613899 := bstep (se 1 (by rfl) ⟨1960424, by rfl⟩ : syracuseStep 2613899 = 3920849) B3920849
theorem B5153453 : Blo 1356997 5153453 := bstep (se 3 (by rfl) ⟨966272, by rfl⟩ : syracuseStep 5153453 = 1932545) B1932545
theorem B3138227 : Blo 1356997 3138227 := bstep (se 1 (by rfl) ⟨2353670, by rfl⟩ : syracuseStep 3138227 = 4707341) B4707341
theorem B3670721 : Blo 1356997 3670721 := bstep (se 2 (by rfl) ⟨1376520, by rfl⟩ : syracuseStep 3670721 = 2753041) B2753041
theorem B5153483 : Blo 1356997 5153483 := bstep (se 1 (by rfl) ⟨3865112, by rfl⟩ : syracuseStep 5153483 = 7730225) B7730225
theorem B3056345 : Blo 1356997 3056345 := bstep (se 2 (by rfl) ⟨1146129, by rfl⟩ : syracuseStep 3056345 = 2292259) B2292259
theorem B19079981 : Blo 1356997 19079981 := bstep (se 3 (by rfl) ⟨3577496, by rfl⟩ : syracuseStep 19079981 = 7154993) B7154993
theorem B18834221 : Blo 1356997 18834221 := bstep (se 3 (by rfl) ⟨3531416, by rfl⟩ : syracuseStep 18834221 = 7062833) B7062833
theorem B3056435 : Blo 1356997 3056435 := bstep (se 1 (by rfl) ⟨2292326, by rfl⟩ : syracuseStep 3056435 = 4584653) B4584653
theorem B4580171 : Blo 1356997 4580171 := bstep (se 1 (by rfl) ⟨3435128, by rfl⟩ : syracuseStep 4580171 = 6870257) B6870257
theorem B3056471 : Blo 1356997 3056471 := bstep (se 1 (by rfl) ⟨2292353, by rfl⟩ : syracuseStep 3056471 = 4584707) B4584707
theorem B15459173 : Blo 1356997 15459173 := bstep (se 4 (by rfl) ⟨1449297, by rfl⟩ : syracuseStep 15459173 = 2898595) B2898595
theorem B1631191 : Blo 1356997 1631191 := bstep (se 1 (by rfl) ⟨1223393, by rfl⟩ : syracuseStep 1631191 = 2446787) B2446787
theorem B10732589 : Blo 1356997 10732589 := bstep (se 3 (by rfl) ⟨2012360, by rfl⟩ : syracuseStep 10732589 = 4024721) B4024721
theorem B11600941 : Blo 1356997 11600941 := bstep (se 3 (by rfl) ⟨2175176, by rfl⟩ : syracuseStep 11600941 = 4350353) B4350353
theorem B4580441 : Blo 1356997 4580441 := bstep (se 2 (by rfl) ⟨1717665, by rfl⟩ : syracuseStep 4580441 = 3435331) B3435331
theorem B1590391 : Blo 1356997 1590391 := bstep (se 1 (by rfl) ⟨1192793, by rfl⟩ : syracuseStep 1590391 = 2385587) B2385587
theorem B4891841 : Blo 1356997 4891841 := bstep (se 2 (by rfl) ⟨1834440, by rfl⟩ : syracuseStep 4891841 = 3668881) B3668881
theorem B5801291 : Blo 1356997 5801291 := bstep (se 1 (by rfl) ⟨4350968, by rfl⟩ : syracuseStep 5801291 = 8701937) B8701937
theorem B5154137 : Blo 1356997 5154137 := bstep (se 2 (by rfl) ⟨1932801, by rfl⟩ : syracuseStep 5154137 = 3865603) B3865603
theorem B39142925 : Blo 1356997 39142925 := bstep (se 3 (by rfl) ⟨7339298, by rfl⟩ : syracuseStep 39142925 = 14678597) B14678597
theorem B3868211 : Blo 1356997 3868211 := bstep (se 1 (by rfl) ⟨2901158, by rfl⟩ : syracuseStep 3868211 = 5802317) B5802317
theorem B8701505 : Blo 1356997 8701505 := bstep (se 2 (by rfl) ⟨3263064, by rfl⟩ : syracuseStep 8701505 = 6526129) B6526129
theorem B5154455 : Blo 1356997 5154455 := bstep (se 1 (by rfl) ⟨3865841, by rfl⟩ : syracuseStep 5154455 = 7731683) B7731683
theorem B4581143 : Blo 1356997 4581143 := bstep (se 1 (by rfl) ⟨3435857, by rfl⟩ : syracuseStep 4581143 = 6871715) B6871715
theorem B6874955 : Blo 1356997 6874955 := bstep (se 1 (by rfl) ⟨5156216, by rfl⟩ : syracuseStep 6874955 = 10312433) B10312433
theorem B2648065 : Blo 1356997 2648065 := bstep (se 2 (by rfl) ⟨993024, by rfl⟩ : syracuseStep 2648065 = 1986049) B1986049
theorem B6195217 : Blo 1356997 6195217 := bstep (se 2 (by rfl) ⟨2323206, by rfl⟩ : syracuseStep 6195217 = 4646413) B4646413
theorem B9783341 : Blo 1356997 9783341 := bstep (se 3 (by rfl) ⟨1834376, by rfl⟩ : syracuseStep 9783341 = 3668753) B3668753
theorem B4130995 : Blo 1356997 4130995 := bstep (se 1 (by rfl) ⟨3098246, by rfl⟩ : syracuseStep 4130995 = 6196493) B6196493
theorem B5507345 : Blo 1356997 5507345 := bstep (se 2 (by rfl) ⟨2065254, by rfl⟩ : syracuseStep 5507345 = 4130509) B4130509
theorem B4581683 : Blo 1356997 4581683 := bstep (se 1 (by rfl) ⟨3436262, by rfl⟩ : syracuseStep 4581683 = 6872525) B6872525
theorem B5155123 : Blo 1356997 5155123 := bstep (se 1 (by rfl) ⟨3866342, by rfl⟩ : syracuseStep 5155123 = 7732685) B7732685
theorem B11602277 : Blo 1356997 11602277 := bstep (se 4 (by rfl) ⟨1087713, by rfl⟩ : syracuseStep 11602277 = 2175427) B2175427
theorem B33499541 : Blo 1356997 33499541 := bstep (se 6 (by rfl) ⟨785145, by rfl⟩ : syracuseStep 33499541 = 1570291) B1570291
theorem B5876185 : Blo 1356997 5876185 := bstep (se 2 (by rfl) ⟨2203569, by rfl⟩ : syracuseStep 5876185 = 4407139) B4407139
theorem B4581953 : Blo 1356997 4581953 := bstep (se 2 (by rfl) ⟨1718232, by rfl⟩ : syracuseStep 4581953 = 3436465) B3436465
theorem B6523571 : Blo 1356997 6523571 := bstep (se 1 (by rfl) ⟨4892678, by rfl⟩ : syracuseStep 6523571 = 9785357) B9785357
theorem B5507929 : Blo 1356997 5507929 := bstep (se 2 (by rfl) ⟨2065473, by rfl⟩ : syracuseStep 5507929 = 4130947) B4130947
theorem B1526647 : Blo 1356997 1526647 := bstep (se 1 (by rfl) ⟨1144985, by rfl⟩ : syracuseStep 1526647 = 2289971) B2289971
theorem B3435443 : Blo 1356997 3435443 := bstep (se 1 (by rfl) ⟨2576582, by rfl⟩ : syracuseStep 3435443 = 5153165) B5153165
theorem B3263449 : Blo 1356997 3263449 := bstep (se 2 (by rfl) ⟨1223793, by rfl⟩ : syracuseStep 3263449 = 2447587) B2447587
theorem B1526827 : Blo 1356997 1526827 := bstep (se 1 (by rfl) ⟨1145120, by rfl⟩ : syracuseStep 1526827 = 2290241) B2290241
theorem B4582493 : Blo 1356997 4582493 := bstep (se 3 (by rfl) ⟨859217, by rfl⟩ : syracuseStep 4582493 = 1718435) B1718435
theorem B1526935 : Blo 1356997 1526935 := bstep (se 1 (by rfl) ⟨1145201, by rfl⟩ : syracuseStep 1526935 = 2290403) B2290403
theorem B2354329 : Blo 1356997 2354329 := bstep (se 2 (by rfl) ⟨882873, by rfl⟩ : syracuseStep 2354329 = 1765747) B1765747
theorem B6524225 : Blo 1356997 6524225 := bstep (se 2 (by rfl) ⟨2446584, by rfl⟩ : syracuseStep 6524225 = 4893169) B4893169
theorem B1527115 : Blo 1356997 1527115 := bstep (se 1 (by rfl) ⟨1145336, by rfl⟩ : syracuseStep 1527115 = 2290673) B2290673
theorem B1527223 : Blo 1356997 1527223 := bstep (se 1 (by rfl) ⟨1145417, by rfl⟩ : syracuseStep 1527223 = 2290835) B2290835
theorem B3435979 : Blo 1356997 3435979 := bstep (se 1 (by rfl) ⟨2576984, by rfl⟩ : syracuseStep 3435979 = 5153969) B5153969
theorem B5156369 : Blo 1356997 5156369 := bstep (se 2 (by rfl) ⟨1933638, by rfl⟩ : syracuseStep 5156369 = 3867277) B3867277
theorem B6876737 : Blo 1356997 6876737 := bstep (se 2 (by rfl) ⟨2578776, by rfl⟩ : syracuseStep 6876737 = 5157553) B5157553
theorem B3436121 : Blo 1356997 3436121 := bstep (se 2 (by rfl) ⟨1288545, by rfl⟩ : syracuseStep 3436121 = 2577091) B2577091
theorem B1527403 : Blo 1356997 1527403 := bstep (se 1 (by rfl) ⟨1145552, by rfl⟩ : syracuseStep 1527403 = 2291105) B2291105
theorem B9285299 : Blo 1356997 9285299 := bstep (se 1 (by rfl) ⟨6963974, by rfl⟩ : syracuseStep 9285299 = 13927949) B13927949
theorem B1527511 : Blo 1356997 1527511 := bstep (se 1 (by rfl) ⟨1145633, by rfl⟩ : syracuseStep 1527511 = 2291267) B2291267
theorem B2035595 : Blo 1356997 2035595 := bstep (se 1 (by rfl) ⟨1526696, by rfl⟩ : syracuseStep 2035595 = 3053393) B3053393
theorem B1527691 : Blo 1356997 1527691 := bstep (se 1 (by rfl) ⟨1145768, by rfl⟩ : syracuseStep 1527691 = 2291537) B2291537
theorem B4894609 : Blo 1356997 4894609 := bstep (se 2 (by rfl) ⟨1835478, by rfl⟩ : syracuseStep 4894609 = 3670957) B3670957
theorem B2576279 : Blo 1356997 2576279 := bstep (se 1 (by rfl) ⟨1932209, by rfl⟩ : syracuseStep 2576279 = 3864419) B3864419
theorem B2035607 : Blo 1356997 2035607 := bstep (se 1 (by rfl) ⟨1526705, by rfl⟩ : syracuseStep 2035607 = 3053411) B3053411
theorem B2035673 : Blo 1356997 2035673 := bstep (se 2 (by rfl) ⟨763377, by rfl⟩ : syracuseStep 2035673 = 1526755) B1526755
theorem B1527799 : Blo 1356997 1527799 := bstep (se 1 (by rfl) ⟨1145849, by rfl⟩ : syracuseStep 1527799 = 2291699) B2291699
theorem B6279185 : Blo 1356997 6279185 := bstep (se 2 (by rfl) ⟨2354694, by rfl⟩ : syracuseStep 6279185 = 4709389) B4709389
theorem B2035787 : Blo 1356997 2035787 := bstep (se 1 (by rfl) ⟨1526840, by rfl⟩ : syracuseStep 2035787 = 3053681) B3053681
theorem B2035799 : Blo 1356997 2035799 := bstep (se 1 (by rfl) ⟨1526849, by rfl⟩ : syracuseStep 2035799 = 3053699) B3053699
theorem B2035865 : Blo 1356997 2035865 := bstep (se 2 (by rfl) ⟨763449, by rfl⟩ : syracuseStep 2035865 = 1526899) B1526899
theorem B1527979 : Blo 1356997 1527979 := bstep (se 1 (by rfl) ⟨1145984, by rfl⟩ : syracuseStep 1527979 = 2291969) B2291969
theorem B4583627 : Blo 1356997 4583627 := bstep (se 1 (by rfl) ⟨3437720, by rfl⟩ : syracuseStep 4583627 = 6875441) B6875441
theorem B5157067 : Blo 1356997 5157067 := bstep (se 1 (by rfl) ⟨3867800, by rfl⟩ : syracuseStep 5157067 = 7735601) B7735601
theorem B2035979 : Blo 1356997 2035979 := bstep (se 1 (by rfl) ⟨1526984, by rfl⟩ : syracuseStep 2035979 = 3053969) B3053969
theorem B2035991 : Blo 1356997 2035991 := bstep (se 1 (by rfl) ⟨1526993, by rfl⟩ : syracuseStep 2035991 = 3053987) B3053987
theorem B1528087 : Blo 1356997 1528087 := bstep (se 1 (by rfl) ⟨1146065, by rfl⟩ : syracuseStep 1528087 = 2292131) B2292131
theorem B2036057 : Blo 1356997 2036057 := bstep (se 2 (by rfl) ⟨763521, by rfl⟩ : syracuseStep 2036057 = 1527043) B1527043
theorem B3436951 : Blo 1356997 3436951 := bstep (se 1 (by rfl) ⟨2577713, by rfl⟩ : syracuseStep 3436951 = 5155427) B5155427
theorem B11006387 : Blo 1356997 11006387 := bstep (se 1 (by rfl) ⟨8254790, by rfl⟩ : syracuseStep 11006387 = 16509581) B16509581
theorem B2036171 : Blo 1356997 2036171 := bstep (se 1 (by rfl) ⟨1527128, by rfl⟩ : syracuseStep 2036171 = 3054257) B3054257
theorem B1528267 : Blo 1356997 1528267 := bstep (se 1 (by rfl) ⟨1146200, by rfl⟩ : syracuseStep 1528267 = 2292401) B2292401
theorem B2036183 : Blo 1356997 2036183 := bstep (se 1 (by rfl) ⟨1527137, by rfl⟩ : syracuseStep 2036183 = 3054275) B3054275
theorem B4583897 : Blo 1356997 4583897 := bstep (se 2 (by rfl) ⟨1718961, by rfl⟩ : syracuseStep 4583897 = 3437923) B3437923
theorem B5157341 : Blo 1356997 5157341 := bstep (se 3 (by rfl) ⟨967001, by rfl⟩ : syracuseStep 5157341 = 1934003) B1934003
theorem B2290187 : Blo 1356997 2290187 := bstep (se 1 (by rfl) ⟨1717640, by rfl⟩ : syracuseStep 2290187 = 3435281) B3435281
theorem B2036249 : Blo 1356997 2036249 := bstep (se 2 (by rfl) ⟨763593, by rfl⟩ : syracuseStep 2036249 = 1527187) B1527187
theorem B2576947 : Blo 1356997 2576947 := bstep (se 1 (by rfl) ⟨1932710, by rfl⟩ : syracuseStep 2576947 = 3865421) B3865421
theorem B2290315 : Blo 1356997 2290315 := bstep (se 1 (by rfl) ⟨1717736, by rfl⟩ : syracuseStep 2290315 = 3435473) B3435473
theorem B2036363 : Blo 1356997 2036363 := bstep (se 1 (by rfl) ⟨1527272, by rfl⟩ : syracuseStep 2036363 = 3054545) B3054545
theorem B2036375 : Blo 1356997 2036375 := bstep (se 1 (by rfl) ⟨1527281, by rfl⟩ : syracuseStep 2036375 = 3054563) B3054563
theorem B2036441 : Blo 1356997 2036441 := bstep (se 2 (by rfl) ⟨763665, by rfl⟩ : syracuseStep 2036441 = 1527331) B1527331
theorem B9286417 : Blo 1356997 9286417 := bstep (se 2 (by rfl) ⟨3482406, by rfl⟩ : syracuseStep 9286417 = 6964813) B6964813
theorem B2290457 : Blo 1356997 2290457 := bstep (se 2 (by rfl) ⟨858921, by rfl⟩ : syracuseStep 2290457 = 1717843) B1717843
theorem B2036555 : Blo 1356997 2036555 := bstep (se 1 (by rfl) ⟨1527416, by rfl⟩ : syracuseStep 2036555 = 3054833) B3054833
theorem B3437387 : Blo 1356997 3437387 := bstep (se 1 (by rfl) ⟨2578040, by rfl⟩ : syracuseStep 3437387 = 5156081) B5156081
theorem B2036567 : Blo 1356997 2036567 := bstep (se 1 (by rfl) ⟨1527425, by rfl⟩ : syracuseStep 2036567 = 3054851) B3054851
theorem B2290585 : Blo 1356997 2290585 := bstep (se 2 (by rfl) ⟨858969, by rfl⟩ : syracuseStep 2290585 = 1717939) B1717939
theorem B2036633 : Blo 1356997 2036633 := bstep (se 2 (by rfl) ⟨763737, by rfl⟩ : syracuseStep 2036633 = 1527475) B1527475
theorem B2175959 : Blo 1356997 2175959 := bstep (se 1 (by rfl) ⟨1631969, by rfl⟩ : syracuseStep 2175959 = 3263939) B3263939
theorem B2577395 : Blo 1356997 2577395 := bstep (se 1 (by rfl) ⟨1933046, by rfl⟩ : syracuseStep 2577395 = 3866093) B3866093
theorem B2036747 : Blo 1356997 2036747 := bstep (se 1 (by rfl) ⟨1527560, by rfl⟩ : syracuseStep 2036747 = 3055121) B3055121
theorem B2036759 : Blo 1356997 2036759 := bstep (se 1 (by rfl) ⟨1527569, by rfl⟩ : syracuseStep 2036759 = 3055139) B3055139
theorem B2577433 : Blo 1356997 2577433 := bstep (se 2 (by rfl) ⟨966537, by rfl⟩ : syracuseStep 2577433 = 1933075) B1933075
theorem B5796953 : Blo 1356997 5796953 := bstep (se 2 (by rfl) ⟨2173857, by rfl⟩ : syracuseStep 5796953 = 4347715) B4347715
theorem B2036825 : Blo 1356997 2036825 := bstep (se 2 (by rfl) ⟨763809, by rfl⟩ : syracuseStep 2036825 = 1527619) B1527619
theorem B4584599 : Blo 1356997 4584599 := bstep (se 1 (by rfl) ⟨3438449, by rfl⟩ : syracuseStep 4584599 = 6876899) B6876899
theorem B5158039 : Blo 1356997 5158039 := bstep (se 1 (by rfl) ⟨3868529, by rfl⟩ : syracuseStep 5158039 = 7737059) B7737059
theorem B3437761 : Blo 1356997 3437761 := bstep (se 2 (by rfl) ⟨1289160, by rfl⟩ : syracuseStep 3437761 = 2578321) B2578321
theorem B1357003 : Blo 1356997 1357003 := bstep (se 1 (by rfl) ⟨1017752, by rfl⟩ : syracuseStep 1357003 = 2035505) B2035505
theorem B2036939 : Blo 1356997 2036939 := bstep (se 1 (by rfl) ⟨1527704, by rfl⟩ : syracuseStep 2036939 = 3055409) B3055409
theorem B1357015 : Blo 1356997 1357015 := bstep (se 1 (by rfl) ⟨1017761, by rfl⟩ : syracuseStep 1357015 = 2035523) B2035523
theorem B1717463 : Blo 1356997 1717463 := bstep (se 1 (by rfl) ⟨1288097, by rfl⟩ : syracuseStep 1717463 = 2576195) B2576195
theorem B2036951 : Blo 1356997 2036951 := bstep (se 1 (by rfl) ⟨1527713, by rfl⟩ : syracuseStep 2036951 = 3055427) B3055427
theorem B1357035 : Blo 1356997 1357035 := bstep (se 1 (by rfl) ⟨1017776, by rfl⟩ : syracuseStep 1357035 = 2035553) B2035553
theorem B1357047 : Blo 1356997 1357047 := bstep (se 1 (by rfl) ⟨1017785, by rfl⟩ : syracuseStep 1357047 = 2035571) B2035571
theorem B1357067 : Blo 1356997 1357067 := bstep (se 1 (by rfl) ⟨1017800, by rfl⟩ : syracuseStep 1357067 = 2035601) B2035601
theorem B1357079 : Blo 1356997 1357079 := bstep (se 1 (by rfl) ⟨1017809, by rfl⟩ : syracuseStep 1357079 = 2035619) B2035619
theorem B2037017 : Blo 1356997 2037017 := bstep (se 2 (by rfl) ⟨763881, by rfl⟩ : syracuseStep 2037017 = 1527763) B1527763
theorem B1357099 : Blo 1356997 1357099 := bstep (se 1 (by rfl) ⟨1017824, by rfl⟩ : syracuseStep 1357099 = 2035649) B2035649
theorem B7730477 : Blo 1356997 7730477 := bstep (se 3 (by rfl) ⟨1449464, by rfl⟩ : syracuseStep 7730477 = 2898929) B2898929
theorem B1357111 : Blo 1356997 1357111 := bstep (se 1 (by rfl) ⟨1017833, by rfl⟩ : syracuseStep 1357111 = 2035667) B2035667
theorem B1357131 : Blo 1356997 1357131 := bstep (se 1 (by rfl) ⟨1017848, by rfl⟩ : syracuseStep 1357131 = 2035697) B2035697
theorem B1357143 : Blo 1356997 1357143 := bstep (se 1 (by rfl) ⟨1017857, by rfl⟩ : syracuseStep 1357143 = 2035715) B2035715
theorem B1357163 : Blo 1356997 1357163 := bstep (se 1 (by rfl) ⟨1017872, by rfl⟩ : syracuseStep 1357163 = 2035745) B2035745
theorem B1357175 : Blo 1356997 1357175 := bstep (se 1 (by rfl) ⟨1017881, by rfl⟩ : syracuseStep 1357175 = 2035763) B2035763
theorem B1357195 : Blo 1356997 1357195 := bstep (se 1 (by rfl) ⟨1017896, by rfl⟩ : syracuseStep 1357195 = 2035793) B2035793
theorem B2037131 : Blo 1356997 2037131 := bstep (se 1 (by rfl) ⟨1527848, by rfl⟩ : syracuseStep 2037131 = 3055697) B3055697
theorem B1357207 : Blo 1356997 1357207 := bstep (se 1 (by rfl) ⟨1017905, by rfl⟩ : syracuseStep 1357207 = 2035811) B2035811
theorem B2037143 : Blo 1356997 2037143 := bstep (se 1 (by rfl) ⟨1527857, by rfl⟩ : syracuseStep 2037143 = 3055715) B3055715
theorem B1357227 : Blo 1356997 1357227 := bstep (se 1 (by rfl) ⟨1017920, by rfl⟩ : syracuseStep 1357227 = 2035841) B2035841
theorem B1357239 : Blo 1356997 1357239 := bstep (se 1 (by rfl) ⟨1017929, by rfl⟩ : syracuseStep 1357239 = 2035859) B2035859
theorem B1357259 : Blo 1356997 1357259 := bstep (se 1 (by rfl) ⟨1017944, by rfl⟩ : syracuseStep 1357259 = 2035889) B2035889
theorem B1357271 : Blo 1356997 1357271 := bstep (se 1 (by rfl) ⟨1017953, by rfl⟩ : syracuseStep 1357271 = 2035907) B2035907
theorem B2291159 : Blo 1356997 2291159 := bstep (se 1 (by rfl) ⟨1718369, by rfl⟩ : syracuseStep 2291159 = 3436739) B3436739
theorem B2577881 : Blo 1356997 2577881 := bstep (se 2 (by rfl) ⟨966705, by rfl⟩ : syracuseStep 2577881 = 1933411) B1933411
theorem B2037209 : Blo 1356997 2037209 := bstep (se 2 (by rfl) ⟨763953, by rfl⟩ : syracuseStep 2037209 = 1527907) B1527907
theorem B52917731 : Blo 1356997 52917731 := bstep (se 1 (by rfl) ⟨39688298, by rfl⟩ : syracuseStep 52917731 = 79376597) B79376597
theorem B1357291 : Blo 1356997 1357291 := bstep (se 1 (by rfl) ⟨1017968, by rfl⟩ : syracuseStep 1357291 = 2035937) B2035937
theorem B1357303 : Blo 1356997 1357303 := bstep (se 1 (by rfl) ⟨1017977, by rfl⟩ : syracuseStep 1357303 = 2035955) B2035955
theorem B1357323 : Blo 1356997 1357323 := bstep (se 1 (by rfl) ⟨1017992, by rfl⟩ : syracuseStep 1357323 = 2035985) B2035985
theorem B1357335 : Blo 1356997 1357335 := bstep (se 1 (by rfl) ⟨1018001, by rfl⟩ : syracuseStep 1357335 = 2036003) B2036003
theorem B1357355 : Blo 1356997 1357355 := bstep (se 1 (by rfl) ⟨1018016, by rfl⟩ : syracuseStep 1357355 = 2036033) B2036033
theorem B1357367 : Blo 1356997 1357367 := bstep (se 1 (by rfl) ⟨1018025, by rfl⟩ : syracuseStep 1357367 = 2036051) B2036051
theorem B1357387 : Blo 1356997 1357387 := bstep (se 1 (by rfl) ⟨1018040, by rfl⟩ : syracuseStep 1357387 = 2036081) B2036081
theorem B2037323 : Blo 1356997 2037323 := bstep (se 1 (by rfl) ⟨1527992, by rfl⟩ : syracuseStep 2037323 = 3055985) B3055985
theorem B1357399 : Blo 1356997 1357399 := bstep (se 1 (by rfl) ⟨1018049, by rfl⟩ : syracuseStep 1357399 = 2036099) B2036099
theorem B2291287 : Blo 1356997 2291287 := bstep (se 1 (by rfl) ⟨1718465, by rfl⟩ : syracuseStep 2291287 = 3436931) B3436931
theorem B2037335 : Blo 1356997 2037335 := bstep (se 1 (by rfl) ⟨1528001, by rfl⟩ : syracuseStep 2037335 = 3056003) B3056003
theorem B1357419 : Blo 1356997 1357419 := bstep (se 1 (by rfl) ⟨1018064, by rfl⟩ : syracuseStep 1357419 = 2036129) B2036129
theorem B1357431 : Blo 1356997 1357431 := bstep (se 1 (by rfl) ⟨1018073, by rfl⟩ : syracuseStep 1357431 = 2036147) B2036147
theorem B1357451 : Blo 1356997 1357451 := bstep (se 1 (by rfl) ⟨1018088, by rfl⟩ : syracuseStep 1357451 = 2036177) B2036177
theorem B1357463 : Blo 1356997 1357463 := bstep (se 1 (by rfl) ⟨1018097, by rfl⟩ : syracuseStep 1357463 = 2036195) B2036195
theorem B2037401 : Blo 1356997 2037401 := bstep (se 2 (by rfl) ⟨764025, by rfl⟩ : syracuseStep 2037401 = 1528051) B1528051
theorem B1357483 : Blo 1356997 1357483 := bstep (se 1 (by rfl) ⟨1018112, by rfl⟩ : syracuseStep 1357483 = 2036225) B2036225
theorem B1357495 : Blo 1356997 1357495 := bstep (se 1 (by rfl) ⟨1018121, by rfl⟩ : syracuseStep 1357495 = 2036243) B2036243
theorem B3053249 : Blo 1356997 3053249 := bstep (se 2 (by rfl) ⟨1144968, by rfl⟩ : syracuseStep 3053249 = 2289937) B2289937
theorem B1357515 : Blo 1356997 1357515 := bstep (se 1 (by rfl) ⟨1018136, by rfl⟩ : syracuseStep 1357515 = 2036273) B2036273
theorem B1357527 : Blo 1356997 1357527 := bstep (se 1 (by rfl) ⟨1018145, by rfl⟩ : syracuseStep 1357527 = 2036291) B2036291
theorem B1357547 : Blo 1356997 1357547 := bstep (se 1 (by rfl) ⟨1018160, by rfl⟩ : syracuseStep 1357547 = 2036321) B2036321
theorem B1357559 : Blo 1356997 1357559 := bstep (se 1 (by rfl) ⟨1018169, by rfl⟩ : syracuseStep 1357559 = 2036339) B2036339
theorem B1357579 : Blo 1356997 1357579 := bstep (se 1 (by rfl) ⟨1018184, by rfl⟩ : syracuseStep 1357579 = 2036369) B2036369
theorem B2037515 : Blo 1356997 2037515 := bstep (se 1 (by rfl) ⟨1528136, by rfl⟩ : syracuseStep 2037515 = 3056273) B3056273
theorem B1357591 : Blo 1356997 1357591 := bstep (se 1 (by rfl) ⟨1018193, by rfl⟩ : syracuseStep 1357591 = 2036387) B2036387
theorem B2037527 : Blo 1356997 2037527 := bstep (se 1 (by rfl) ⟨1528145, by rfl⟩ : syracuseStep 2037527 = 3056291) B3056291
theorem B3438359 : Blo 1356997 3438359 := bstep (se 1 (by rfl) ⟨2578769, by rfl⟩ : syracuseStep 3438359 = 5157539) B5157539
theorem B1357611 : Blo 1356997 1357611 := bstep (se 1 (by rfl) ⟨1018208, by rfl⟩ : syracuseStep 1357611 = 2036417) B2036417
theorem B1357623 : Blo 1356997 1357623 := bstep (se 1 (by rfl) ⟨1018217, by rfl⟩ : syracuseStep 1357623 = 2036435) B2036435
theorem B1357643 : Blo 1356997 1357643 := bstep (se 1 (by rfl) ⟨1018232, by rfl⟩ : syracuseStep 1357643 = 2036465) B2036465
theorem B1357655 : Blo 1356997 1357655 := bstep (se 1 (by rfl) ⟨1018241, by rfl⟩ : syracuseStep 1357655 = 2036483) B2036483
theorem B2037593 : Blo 1356997 2037593 := bstep (se 2 (by rfl) ⟨764097, by rfl⟩ : syracuseStep 2037593 = 1528195) B1528195
theorem B44046179 : Blo 1356997 44046179 := bstep (se 1 (by rfl) ⟨33034634, by rfl⟩ : syracuseStep 44046179 = 66069269) B66069269
theorem B1357675 : Blo 1356997 1357675 := bstep (se 1 (by rfl) ⟨1018256, by rfl⟩ : syracuseStep 1357675 = 2036513) B2036513
theorem B17872757 : Blo 1356997 17872757 := bstep (se 5 (by rfl) ⟨837785, by rfl⟩ : syracuseStep 17872757 = 1675571) B1675571
theorem B1357687 : Blo 1356997 1357687 := bstep (se 1 (by rfl) ⟨1018265, by rfl⟩ : syracuseStep 1357687 = 2036531) B2036531
theorem B2447219 : Blo 1356997 2447219 := bstep (se 1 (by rfl) ⟨1835414, by rfl⟩ : syracuseStep 2447219 = 3670829) B3670829
theorem B1357707 : Blo 1356997 1357707 := bstep (se 1 (by rfl) ⟨1018280, by rfl⟩ : syracuseStep 1357707 = 2036561) B2036561
theorem B1718167 : Blo 1356997 1718167 := bstep (se 1 (by rfl) ⟨1288625, by rfl⟩ : syracuseStep 1718167 = 2577251) B2577251
theorem B1357719 : Blo 1356997 1357719 := bstep (se 1 (by rfl) ⟨1018289, by rfl⟩ : syracuseStep 1357719 = 2036579) B2036579
theorem B3053465 : Blo 1356997 3053465 := bstep (se 2 (by rfl) ⟨1145049, by rfl⟩ : syracuseStep 3053465 = 2290099) B2290099
theorem B1357739 : Blo 1356997 1357739 := bstep (se 1 (by rfl) ⟨1018304, by rfl⟩ : syracuseStep 1357739 = 2036609) B2036609
theorem B1357751 : Blo 1356997 1357751 := bstep (se 1 (by rfl) ⟨1018313, by rfl⟩ : syracuseStep 1357751 = 2036627) B2036627
theorem B1357771 : Blo 1356997 1357771 := bstep (se 1 (by rfl) ⟨1018328, by rfl⟩ : syracuseStep 1357771 = 2036657) B2036657
theorem B2037707 : Blo 1356997 2037707 := bstep (se 1 (by rfl) ⟨1528280, by rfl⟩ : syracuseStep 2037707 = 3056561) B3056561
theorem B1357783 : Blo 1356997 1357783 := bstep (se 1 (by rfl) ⟨1018337, by rfl⟩ : syracuseStep 1357783 = 2036675) B2036675
theorem B2037719 : Blo 1356997 2037719 := bstep (se 1 (by rfl) ⟨1528289, by rfl⟩ : syracuseStep 2037719 = 3056579) B3056579
theorem B4962269 : Blo 1356997 4962269 := bstep (se 3 (by rfl) ⟨930425, by rfl⟩ : syracuseStep 4962269 = 1860851) B1860851
theorem B1357803 : Blo 1356997 1357803 := bstep (se 1 (by rfl) ⟨1018352, by rfl⟩ : syracuseStep 1357803 = 2036705) B2036705
theorem B3053555 : Blo 1356997 3053555 := bstep (se 1 (by rfl) ⟨2290166, by rfl⟩ : syracuseStep 3053555 = 4580333) B4580333
theorem B1357815 : Blo 1356997 1357815 := bstep (se 1 (by rfl) ⟨1018361, by rfl⟩ : syracuseStep 1357815 = 2036723) B2036723
theorem B1357835 : Blo 1356997 1357835 := bstep (se 1 (by rfl) ⟨1018376, by rfl⟩ : syracuseStep 1357835 = 2036753) B2036753
theorem B3053591 : Blo 1356997 3053591 := bstep (se 1 (by rfl) ⟨2290193, by rfl⟩ : syracuseStep 3053591 = 4580387) B4580387
theorem B1357847 : Blo 1356997 1357847 := bstep (se 1 (by rfl) ⟨1018385, by rfl⟩ : syracuseStep 1357847 = 2036771) B2036771
theorem B1357867 : Blo 1356997 1357867 := bstep (se 1 (by rfl) ⟨1018400, by rfl⟩ : syracuseStep 1357867 = 2036801) B2036801
theorem B1357879 : Blo 1356997 1357879 := bstep (se 1 (by rfl) ⟨1018409, by rfl⟩ : syracuseStep 1357879 = 2036819) B2036819
theorem B4773953 : Blo 1356997 4773953 := bstep (se 2 (by rfl) ⟨1790232, by rfl⟩ : syracuseStep 4773953 = 3580465) B3580465
theorem B1357899 : Blo 1356997 1357899 := bstep (se 1 (by rfl) ⟨1018424, by rfl⟩ : syracuseStep 1357899 = 2036849) B2036849
theorem B1357911 : Blo 1356997 1357911 := bstep (se 1 (by rfl) ⟨1018433, by rfl⟩ : syracuseStep 1357911 = 2036867) B2036867
theorem B1357931 : Blo 1356997 1357931 := bstep (se 1 (by rfl) ⟨1018448, by rfl⟩ : syracuseStep 1357931 = 2036897) B2036897
theorem B1357943 : Blo 1356997 1357943 := bstep (se 1 (by rfl) ⟨1018457, by rfl⟩ : syracuseStep 1357943 = 2036915) B2036915
theorem B1357963 : Blo 1356997 1357963 := bstep (se 1 (by rfl) ⟨1018472, by rfl⟩ : syracuseStep 1357963 = 2036945) B2036945
theorem B1357975 : Blo 1356997 1357975 := bstep (se 1 (by rfl) ⟨1018481, by rfl⟩ : syracuseStep 1357975 = 2036963) B2036963
theorem B1357995 : Blo 1356997 1357995 := bstep (se 1 (by rfl) ⟨1018496, by rfl⟩ : syracuseStep 1357995 = 2036993) B2036993
theorem B1358007 : Blo 1356997 1358007 := bstep (se 1 (by rfl) ⟨1018505, by rfl⟩ : syracuseStep 1358007 = 2037011) B2037011
theorem B2578625 : Blo 1356997 2578625 := bstep (se 2 (by rfl) ⟨966984, by rfl⟩ : syracuseStep 2578625 = 1933969) B1933969
theorem B3053771 : Blo 1356997 3053771 := bstep (se 1 (by rfl) ⟨2290328, by rfl⟩ : syracuseStep 3053771 = 4580657) B4580657
theorem B1358027 : Blo 1356997 1358027 := bstep (se 1 (by rfl) ⟨1018520, by rfl⟩ : syracuseStep 1358027 = 2037041) B2037041
theorem B2291915 : Blo 1356997 2291915 := bstep (se 1 (by rfl) ⟨1718936, by rfl⟩ : syracuseStep 2291915 = 3437873) B3437873
theorem B1358039 : Blo 1356997 1358039 := bstep (se 1 (by rfl) ⟨1018529, by rfl⟩ : syracuseStep 1358039 = 2037059) B2037059
theorem B1358059 : Blo 1356997 1358059 := bstep (se 1 (by rfl) ⟨1018544, by rfl⟩ : syracuseStep 1358059 = 2037089) B2037089
theorem B1358071 : Blo 1356997 1358071 := bstep (se 1 (by rfl) ⟨1018553, by rfl⟩ : syracuseStep 1358071 = 2037107) B2037107
theorem B3053825 : Blo 1356997 3053825 := bstep (se 2 (by rfl) ⟨1145184, by rfl⟩ : syracuseStep 3053825 = 2290369) B2290369
theorem B1358091 : Blo 1356997 1358091 := bstep (se 1 (by rfl) ⟨1018568, by rfl⟩ : syracuseStep 1358091 = 2037137) B2037137
theorem B1358103 : Blo 1356997 1358103 := bstep (se 1 (by rfl) ⟨1018577, by rfl⟩ : syracuseStep 1358103 = 2037155) B2037155
theorem B1358123 : Blo 1356997 1358123 := bstep (se 1 (by rfl) ⟨1018592, by rfl⟩ : syracuseStep 1358123 = 2037185) B2037185
theorem B1358135 : Blo 1356997 1358135 := bstep (se 1 (by rfl) ⟨1018601, by rfl⟩ : syracuseStep 1358135 = 2037203) B2037203
theorem B2611531 : Blo 1356997 2611531 := bstep (se 1 (by rfl) ⟨1958648, by rfl⟩ : syracuseStep 2611531 = 3917297) B3917297
theorem B1358155 : Blo 1356997 1358155 := bstep (se 1 (by rfl) ⟨1018616, by rfl⟩ : syracuseStep 1358155 = 2037233) B2037233
theorem B2292043 : Blo 1356997 2292043 := bstep (se 1 (by rfl) ⟨1719032, by rfl⟩ : syracuseStep 2292043 = 3438065) B3438065
theorem B1358167 : Blo 1356997 1358167 := bstep (se 1 (by rfl) ⟨1018625, by rfl⟩ : syracuseStep 1358167 = 2037251) B2037251
theorem B1358187 : Blo 1356997 1358187 := bstep (se 1 (by rfl) ⟨1018640, by rfl⟩ : syracuseStep 1358187 = 2037281) B2037281
theorem B1358199 : Blo 1356997 1358199 := bstep (se 1 (by rfl) ⟨1018649, by rfl⟩ : syracuseStep 1358199 = 2037299) B2037299
theorem B1489291 : Blo 1356997 1489291 := bstep (se 1 (by rfl) ⟨1116968, by rfl⟩ : syracuseStep 1489291 = 2233937) B2233937
theorem B1358219 : Blo 1356997 1358219 := bstep (se 1 (by rfl) ⟨1018664, by rfl⟩ : syracuseStep 1358219 = 2037329) B2037329
theorem B1358231 : Blo 1356997 1358231 := bstep (se 1 (by rfl) ⟨1018673, by rfl⟩ : syracuseStep 1358231 = 2037347) B2037347
theorem B1358251 : Blo 1356997 1358251 := bstep (se 1 (by rfl) ⟨1018688, by rfl⟩ : syracuseStep 1358251 = 2037377) B2037377
theorem B1358263 : Blo 1356997 1358263 := bstep (se 1 (by rfl) ⟨1018697, by rfl⟩ : syracuseStep 1358263 = 2037395) B2037395
theorem B1358283 : Blo 1356997 1358283 := bstep (se 1 (by rfl) ⟨1018712, by rfl⟩ : syracuseStep 1358283 = 2037425) B2037425
theorem B2578891 : Blo 1356997 2578891 := bstep (se 1 (by rfl) ⟨1934168, by rfl⟩ : syracuseStep 2578891 = 3868337) B3868337
theorem B1358295 : Blo 1356997 1358295 := bstep (se 1 (by rfl) ⟨1018721, by rfl⟩ : syracuseStep 1358295 = 2037443) B2037443
theorem B3054041 : Blo 1356997 3054041 := bstep (se 2 (by rfl) ⟨1145265, by rfl⟩ : syracuseStep 3054041 = 2290531) B2290531
theorem B2292185 : Blo 1356997 2292185 := bstep (se 2 (by rfl) ⟨859569, by rfl⟩ : syracuseStep 2292185 = 1719139) B1719139
theorem B1358315 : Blo 1356997 1358315 := bstep (se 1 (by rfl) ⟨1018736, by rfl⟩ : syracuseStep 1358315 = 2037473) B2037473
theorem B1358327 : Blo 1356997 1358327 := bstep (se 1 (by rfl) ⟨1018745, by rfl⟩ : syracuseStep 1358327 = 2037491) B2037491
theorem B1358347 : Blo 1356997 1358347 := bstep (se 1 (by rfl) ⟨1018760, by rfl⟩ : syracuseStep 1358347 = 2037521) B2037521
theorem B1358359 : Blo 1356997 1358359 := bstep (se 1 (by rfl) ⟨1018769, by rfl⟩ : syracuseStep 1358359 = 2037539) B2037539
theorem B1358379 : Blo 1356997 1358379 := bstep (se 1 (by rfl) ⟨1018784, by rfl⟩ : syracuseStep 1358379 = 2037569) B2037569
theorem B3054131 : Blo 1356997 3054131 := bstep (se 1 (by rfl) ⟨2290598, by rfl⟩ : syracuseStep 3054131 = 4581197) B4581197
theorem B1358391 : Blo 1356997 1358391 := bstep (se 1 (by rfl) ⟨1018793, by rfl⟩ : syracuseStep 1358391 = 2037587) B2037587
theorem B1358411 : Blo 1356997 1358411 := bstep (se 1 (by rfl) ⟨1018808, by rfl⟩ : syracuseStep 1358411 = 2037617) B2037617
theorem B3054167 : Blo 1356997 3054167 := bstep (se 1 (by rfl) ⟨2290625, by rfl⟩ : syracuseStep 3054167 = 4581251) B4581251
theorem B1358423 : Blo 1356997 1358423 := bstep (se 1 (by rfl) ⟨1018817, by rfl⟩ : syracuseStep 1358423 = 2037635) B2037635
theorem B2292313 : Blo 1356997 2292313 := bstep (se 2 (by rfl) ⟨859617, by rfl⟩ : syracuseStep 2292313 = 1719235) B1719235
theorem B1358443 : Blo 1356997 1358443 := bstep (se 1 (by rfl) ⟨1018832, by rfl⟩ : syracuseStep 1358443 = 2037665) B2037665
theorem B1358455 : Blo 1356997 1358455 := bstep (se 1 (by rfl) ⟨1018841, by rfl⟩ : syracuseStep 1358455 = 2037683) B2037683
theorem B1358475 : Blo 1356997 1358475 := bstep (se 1 (by rfl) ⟨1018856, by rfl⟩ : syracuseStep 1358475 = 2037713) B2037713
theorem B1358487 : Blo 1356997 1358487 := bstep (se 1 (by rfl) ⟨1018865, by rfl⟩ : syracuseStep 1358487 = 2037731) B2037731
theorem B4348637 : Blo 1356997 4348637 := bstep (se 3 (by rfl) ⟨815369, by rfl⟩ : syracuseStep 4348637 = 1630739) B1630739
theorem B3054347 : Blo 1356997 3054347 := bstep (se 1 (by rfl) ⟨2290760, by rfl⟩ : syracuseStep 3054347 = 4581521) B4581521
theorem B3054401 : Blo 1356997 3054401 := bstep (se 2 (by rfl) ⟨1145400, by rfl⟩ : syracuseStep 3054401 = 2290801) B2290801
theorem B18840437 : Blo 1356997 18840437 := bstep (se 5 (by rfl) ⟨883145, by rfl⟩ : syracuseStep 18840437 = 1766291) B1766291
theorem B2063321 : Blo 1356997 2063321 := bstep (se 2 (by rfl) ⟨773745, by rfl⟩ : syracuseStep 2063321 = 1547491) B1547491
theorem B3054617 : Blo 1356997 3054617 := bstep (se 2 (by rfl) ⟨1145481, by rfl⟩ : syracuseStep 3054617 = 2290963) B2290963
theorem B3054707 : Blo 1356997 3054707 := bstep (se 1 (by rfl) ⟨2291030, by rfl⟩ : syracuseStep 3054707 = 4582061) B4582061
theorem B3865751 : Blo 1356997 3865751 := bstep (se 1 (by rfl) ⟨2899313, by rfl⟩ : syracuseStep 3865751 = 5798627) B5798627
theorem B3054743 : Blo 1356997 3054743 := bstep (se 1 (by rfl) ⟨2291057, by rfl⟩ : syracuseStep 3054743 = 4582115) B4582115
theorem B3054923 : Blo 1356997 3054923 := bstep (se 1 (by rfl) ⟨2291192, by rfl⟩ : syracuseStep 3054923 = 4582385) B4582385
theorem B3054977 : Blo 1356997 3054977 := bstep (se 2 (by rfl) ⟨1145616, by rfl⟩ : syracuseStep 3054977 = 2291233) B2291233
theorem B15457715 : Blo 1356997 15457715 := bstep (se 1 (by rfl) ⟨11593286, by rfl⟩ : syracuseStep 15457715 = 23186573) B23186573
theorem B2752051 : Blo 1356997 2752051 := bstep (se 1 (by rfl) ⟨2064038, by rfl⟩ : syracuseStep 2752051 = 4128077) B4128077
theorem B3055193 : Blo 1356997 3055193 := bstep (se 2 (by rfl) ⟨1145697, by rfl⟩ : syracuseStep 3055193 = 2291395) B2291395
theorem B4349533 : Blo 1356997 4349533 := bstep (se 3 (by rfl) ⟨815537, by rfl⟩ : syracuseStep 4349533 = 1631075) B1631075
theorem B7732867 : Blo 1356997 7732867 := bstep (se 1 (by rfl) ⟨5799650, by rfl⟩ : syracuseStep 7732867 = 11599301) B11599301
theorem B3055283 : Blo 1356997 3055283 := bstep (se 1 (by rfl) ⟨2291462, by rfl⟩ : syracuseStep 3055283 = 4582925) B4582925
theorem B3055319 : Blo 1356997 3055319 := bstep (se 1 (by rfl) ⟨2291489, by rfl⟩ : syracuseStep 3055319 = 4582979) B4582979
theorem B6872849 : Blo 1356997 6872849 := bstep (se 2 (by rfl) ⟨2577318, by rfl⟩ : syracuseStep 6872849 = 5154637) B5154637
theorem B4128587 : Blo 1356997 4128587 := bstep (se 1 (by rfl) ⟨3096440, by rfl⟩ : syracuseStep 4128587 = 6192881) B6192881
theorem B2613131 : Blo 1356997 2613131 := bstep (se 1 (by rfl) ⟨1959848, by rfl⟩ : syracuseStep 2613131 = 3919697) B3919697
theorem B3055499 : Blo 1356997 3055499 := bstep (se 1 (by rfl) ⟨2291624, by rfl⟩ : syracuseStep 3055499 = 4583249) B4583249
theorem B47652785 : Blo 1356997 47652785 := bstep (se 2 (by rfl) ⟨17869794, by rfl⟩ : syracuseStep 47652785 = 35739589) B35739589
theorem B6873011 : Blo 1356997 6873011 := bstep (se 1 (by rfl) ⟨5154758, by rfl⟩ : syracuseStep 6873011 = 10309517) B10309517
theorem B4718515 : Blo 1356997 4718515 := bstep (se 1 (by rfl) ⟨3538886, by rfl⟩ : syracuseStep 4718515 = 7077773) B7077773
theorem B3055553 : Blo 1356997 3055553 := bstep (se 2 (by rfl) ⟨1145832, by rfl⟩ : syracuseStep 3055553 = 2291665) B2291665
theorem B2899955 : Blo 1356997 2899955 := bstep (se 1 (by rfl) ⟨2174966, by rfl⟩ : syracuseStep 2899955 = 4349933) B4349933
theorem B3530753 : Blo 1356997 3530753 := bstep (se 2 (by rfl) ⟨1324032, by rfl⟩ : syracuseStep 3530753 = 2648065) B2648065
theorem B4186123 : Blo 1356997 4186123 := bstep (se 1 (by rfl) ⟨3139592, by rfl⟩ : syracuseStep 4186123 = 6279185) B6279185
theorem B8257565 : Blo 1356997 8257565 := bstep (se 3 (by rfl) ⟨1548293, by rfl⟩ : syracuseStep 8257565 = 3096587) B3096587
theorem B3055751 : Blo 1356997 3055751 := bstep (se 1 (by rfl) ⟨2291813, by rfl⟩ : syracuseStep 3055751 = 4583627) B4583627
theorem B1376399 : Blo 1356997 1376399 := bstep (se 1 (by rfl) ⟨1032299, by rfl⟩ : syracuseStep 1376399 = 2064599) B2064599
theorem B1933627 : Blo 1356997 1933627 := bstep (se 1 (by rfl) ⟨1450220, by rfl⟩ : syracuseStep 1933627 = 2900441) B2900441
theorem B3055931 : Blo 1356997 3055931 := bstep (se 1 (by rfl) ⟨2291948, by rfl⟩ : syracuseStep 3055931 = 4583897) B4583897
theorem B6873497 : Blo 1356997 6873497 := bstep (se 2 (by rfl) ⟨2577561, by rfl⟩ : syracuseStep 6873497 = 5155123) B5155123
theorem B3482041 : Blo 1356997 3482041 := bstep (se 2 (by rfl) ⟨1305765, by rfl⟩ : syracuseStep 3482041 = 2611531) B2611531
theorem B3056057 : Blo 1356997 3056057 := bstep (se 2 (by rfl) ⟨1146021, by rfl⟩ : syracuseStep 3056057 = 2292043) B2292043
theorem B4579901 : Blo 1356997 4579901 := bstep (se 3 (by rfl) ⟨858731, by rfl⟩ : syracuseStep 4579901 = 1717463) B1717463
theorem B10306115 : Blo 1356997 10306115 := bstep (se 1 (by rfl) ⟨7729586, by rfl⟩ : syracuseStep 10306115 = 15459173) B15459173
theorem B1450639 : Blo 1356997 1450639 := bstep (se 1 (by rfl) ⟨1087979, by rfl⟩ : syracuseStep 1450639 = 2175959) B2175959
theorem B3056399 : Blo 1356997 3056399 := bstep (se 1 (by rfl) ⟨2292299, by rfl⟩ : syracuseStep 3056399 = 4584599) B4584599
theorem B3056417 : Blo 1356997 3056417 := bstep (se 2 (by rfl) ⟨1146156, by rfl⟩ : syracuseStep 3056417 = 2292313) B2292313
theorem B3261227 : Blo 1356997 3261227 := bstep (se 1 (by rfl) ⟨2445920, by rfl⟩ : syracuseStep 3261227 = 4891841) B4891841
theorem B5153651 : Blo 1356997 5153651 := bstep (se 1 (by rfl) ⟨3865238, by rfl⟩ : syracuseStep 5153651 = 7730477) B7730477
theorem B3867527 : Blo 1356997 3867527 := bstep (se 1 (by rfl) ⟨2900645, by rfl⟩ : syracuseStep 3867527 = 5801291) B5801291
theorem B5801003 : Blo 1356997 5801003 := bstep (se 1 (by rfl) ⟨4350752, by rfl⟩ : syracuseStep 5801003 = 8701505) B8701505
theorem B4351265 : Blo 1356997 4351265 := bstep (se 2 (by rfl) ⟨1631724, by rfl⟩ : syracuseStep 4351265 = 3263449) B3263449
theorem B6522227 : Blo 1356997 6522227 := bstep (se 1 (by rfl) ⟨4891670, by rfl⟩ : syracuseStep 6522227 = 9783341) B9783341
theorem B15467921 : Blo 1356997 15467921 := bstep (se 2 (by rfl) ⟨5800470, by rfl⟩ : syracuseStep 15467921 = 11600941) B11600941
theorem B3671563 : Blo 1356997 3671563 := bstep (se 1 (by rfl) ⟨2753672, by rfl⟩ : syracuseStep 3671563 = 5507345) B5507345
theorem B3139105 : Blo 1356997 3139105 := bstep (se 2 (by rfl) ⟨1177164, by rfl⟩ : syracuseStep 3139105 = 2354329) B2354329
theorem B7734851 : Blo 1356997 7734851 := bstep (se 1 (by rfl) ⟨5801138, by rfl⟩ : syracuseStep 7734851 = 11602277) B11602277
theorem B12560291 : Blo 1356997 12560291 := bstep (se 1 (by rfl) ⟨9420218, by rfl⟩ : syracuseStep 12560291 = 18840437) B18840437
theorem B4581305 : Blo 1356997 4581305 := bstep (se 2 (by rfl) ⟨1717989, by rfl⟩ : syracuseStep 4581305 = 3435979) B3435979
theorem B4581899 : Blo 1356997 4581899 := bstep (se 1 (by rfl) ⟨3436424, by rfl⟩ : syracuseStep 4581899 = 6872849) B6872849
theorem B13232717 : Blo 1356997 13232717 := bstep (se 3 (by rfl) ⟨2481134, by rfl⟩ : syracuseStep 13232717 = 4962269) B4962269
theorem B4582007 : Blo 1356997 4582007 := bstep (se 1 (by rfl) ⟨3436505, by rfl⟩ : syracuseStep 4582007 = 6873011) B6873011
theorem B8260289 : Blo 1356997 8260289 := bstep (se 2 (by rfl) ⟨3097608, by rfl⟩ : syracuseStep 8260289 = 6195217) B6195217
theorem B31771541 : Blo 1356997 31771541 := bstep (se 6 (by rfl) ⟨744645, by rfl⟩ : syracuseStep 31771541 = 1489291) B1489291
theorem B5507993 : Blo 1356997 5507993 := bstep (se 2 (by rfl) ⟨2065497, by rfl⟩ : syracuseStep 5507993 = 4130995) B4130995
theorem B6876089 : Blo 1356997 6876089 := bstep (se 2 (by rfl) ⟨2578533, by rfl⟩ : syracuseStep 6876089 = 5157067) B5157067
theorem B1526791 : Blo 1356997 1526791 := bstep (se 1 (by rfl) ⟨1145093, by rfl⟩ : syracuseStep 1526791 = 2290187) B2290187
theorem B5155883 : Blo 1356997 5155883 := bstep (se 1 (by rfl) ⟨3866912, by rfl⟩ : syracuseStep 5155883 = 7733825) B7733825
theorem B3435635 : Blo 1356997 3435635 := bstep (se 1 (by rfl) ⟨2576726, by rfl⟩ : syracuseStep 3435635 = 5153453) B5153453
theorem B2092151 : Blo 1356997 2092151 := bstep (se 1 (by rfl) ⟨1569113, by rfl⟩ : syracuseStep 2092151 = 3138227) B3138227
theorem B3435655 : Blo 1356997 3435655 := bstep (se 1 (by rfl) ⟨2576741, by rfl⟩ : syracuseStep 3435655 = 5153483) B5153483
theorem B1526971 : Blo 1356997 1526971 := bstep (se 1 (by rfl) ⟨1145228, by rfl⟩ : syracuseStep 1526971 = 2290457) B2290457
theorem B4582601 : Blo 1356997 4582601 := bstep (se 2 (by rfl) ⟨1718475, by rfl⟩ : syracuseStep 4582601 = 3436951) B3436951
theorem B7834913 : Blo 1356997 7834913 := bstep (se 2 (by rfl) ⟨2938092, by rfl⟩ : syracuseStep 7834913 = 5876185) B5876185
theorem B7155059 : Blo 1356997 7155059 := bstep (se 1 (by rfl) ⟨5366294, by rfl⟩ : syracuseStep 7155059 = 10732589) B10732589
theorem B3435929 : Blo 1356997 3435929 := bstep (se 2 (by rfl) ⟨1288473, by rfl⟩ : syracuseStep 3435929 = 2576947) B2576947
theorem B3436091 : Blo 1356997 3436091 := bstep (se 1 (by rfl) ⟨2577068, by rfl⟩ : syracuseStep 3436091 = 5154137) B5154137
theorem B1527439 : Blo 1356997 1527439 := bstep (se 1 (by rfl) ⟨1145579, by rfl⟩ : syracuseStep 1527439 = 2291159) B2291159
theorem B35278487 : Blo 1356997 35278487 := bstep (se 1 (by rfl) ⟨26458865, by rfl⟩ : syracuseStep 35278487 = 52917731) B52917731
theorem B26095283 : Blo 1356997 26095283 := bstep (se 1 (by rfl) ⟨19571462, by rfl⟩ : syracuseStep 26095283 = 39142925) B39142925
theorem B12381889 : Blo 1356997 12381889 := bstep (se 2 (by rfl) ⟨4643208, by rfl⟩ : syracuseStep 12381889 = 9286417) B9286417
theorem B3436303 : Blo 1356997 3436303 := bstep (se 1 (by rfl) ⟨2577227, by rfl⟩ : syracuseStep 3436303 = 5154455) B5154455
theorem B7343905 : Blo 1356997 7343905 := bstep (se 2 (by rfl) ⟨2753964, by rfl⟩ : syracuseStep 7343905 = 5507929) B5507929
theorem B2035499 : Blo 1356997 2035499 := bstep (se 1 (by rfl) ⟨1526624, by rfl⟩ : syracuseStep 2035499 = 3053249) B3053249
theorem B2035529 : Blo 1356997 2035529 := bstep (se 2 (by rfl) ⟨763323, by rfl⟩ : syracuseStep 2035529 = 1526647) B1526647
theorem B4583303 : Blo 1356997 4583303 := bstep (se 1 (by rfl) ⟨3437477, by rfl⟩ : syracuseStep 4583303 = 6874955) B6874955
theorem B29364119 : Blo 1356997 29364119 := bstep (se 1 (by rfl) ⟨22023089, by rfl⟩ : syracuseStep 29364119 = 44046179) B44046179
theorem B11915171 : Blo 1356997 11915171 := bstep (se 1 (by rfl) ⟨8936378, by rfl⟩ : syracuseStep 11915171 = 17872757) B17872757
theorem B2035643 : Blo 1356997 2035643 := bstep (se 1 (by rfl) ⟨1526732, by rfl⟩ : syracuseStep 2035643 = 3053465) B3053465
theorem B2174921 : Blo 1356997 2174921 := bstep (se 2 (by rfl) ⟨815595, by rfl⟩ : syracuseStep 2174921 = 1631191) B1631191
theorem B2035703 : Blo 1356997 2035703 := bstep (se 1 (by rfl) ⟨1526777, by rfl⟩ : syracuseStep 2035703 = 3053555) B3053555
theorem B2035727 : Blo 1356997 2035727 := bstep (se 1 (by rfl) ⟨1526795, by rfl⟩ : syracuseStep 2035727 = 3053591) B3053591
theorem B3436577 : Blo 1356997 3436577 := bstep (se 2 (by rfl) ⟨1288716, by rfl⟩ : syracuseStep 3436577 = 2577433) B2577433
theorem B3182635 : Blo 1356997 3182635 := bstep (se 1 (by rfl) ⟨2386976, by rfl⟩ : syracuseStep 3182635 = 4773953) B4773953
theorem B2035769 : Blo 1356997 2035769 := bstep (se 2 (by rfl) ⟨763413, by rfl⟩ : syracuseStep 2035769 = 1526827) B1526827
theorem B2035847 : Blo 1356997 2035847 := bstep (se 1 (by rfl) ⟨1526885, by rfl⟩ : syracuseStep 2035847 = 3053771) B3053771
theorem B1527943 : Blo 1356997 1527943 := bstep (se 1 (by rfl) ⟨1145957, by rfl⟩ : syracuseStep 1527943 = 2291915) B2291915
theorem B2035883 : Blo 1356997 2035883 := bstep (se 1 (by rfl) ⟨1526912, by rfl⟩ : syracuseStep 2035883 = 3053825) B3053825
theorem B2035913 : Blo 1356997 2035913 := bstep (se 2 (by rfl) ⟨763467, by rfl⟩ : syracuseStep 2035913 = 1526935) B1526935
theorem B6877385 : Blo 1356997 6877385 := bstep (se 2 (by rfl) ⟨2579019, by rfl⟩ : syracuseStep 6877385 = 5158039) B5158039
theorem B15470837 : Blo 1356997 15470837 := bstep (se 5 (by rfl) ⟨725195, by rfl⟩ : syracuseStep 15470837 = 1450391) B1450391
theorem B4583681 : Blo 1356997 4583681 := bstep (se 2 (by rfl) ⟨1718880, by rfl⟩ : syracuseStep 4583681 = 3437761) B3437761
theorem B2036027 : Blo 1356997 2036027 := bstep (se 1 (by rfl) ⟨1527020, by rfl⟩ : syracuseStep 2036027 = 3054041) B3054041
theorem B1528123 : Blo 1356997 1528123 := bstep (se 1 (by rfl) ⟨1146092, by rfl⟩ : syracuseStep 1528123 = 2292185) B2292185
theorem B2036087 : Blo 1356997 2036087 := bstep (se 1 (by rfl) ⟨1527065, by rfl⟩ : syracuseStep 2036087 = 3054131) B3054131
theorem B2036111 : Blo 1356997 2036111 := bstep (se 1 (by rfl) ⟨1527083, by rfl⟩ : syracuseStep 2036111 = 3054167) B3054167
theorem B2036153 : Blo 1356997 2036153 := bstep (se 2 (by rfl) ⟨763557, by rfl⟩ : syracuseStep 2036153 = 1527115) B1527115
theorem B2036231 : Blo 1356997 2036231 := bstep (se 1 (by rfl) ⟨1527173, by rfl⟩ : syracuseStep 2036231 = 3054347) B3054347
theorem B2036267 : Blo 1356997 2036267 := bstep (se 1 (by rfl) ⟨1527200, by rfl⟩ : syracuseStep 2036267 = 3054401) B3054401
theorem B2036297 : Blo 1356997 2036297 := bstep (se 2 (by rfl) ⟨763611, by rfl⟩ : syracuseStep 2036297 = 1527223) B1527223
theorem B2290295 : Blo 1356997 2290295 := bstep (se 1 (by rfl) ⟨1717721, by rfl⟩ : syracuseStep 2290295 = 3435443) B3435443
theorem B2036411 : Blo 1356997 2036411 := bstep (se 1 (by rfl) ⟨1527308, by rfl⟩ : syracuseStep 2036411 = 3054617) B3054617
theorem B2036471 : Blo 1356997 2036471 := bstep (se 1 (by rfl) ⟨1527353, by rfl⟩ : syracuseStep 2036471 = 3054707) B3054707
theorem B2577167 : Blo 1356997 2577167 := bstep (se 1 (by rfl) ⟨1932875, by rfl⟩ : syracuseStep 2577167 = 3865751) B3865751
theorem B2036495 : Blo 1356997 2036495 := bstep (se 1 (by rfl) ⟨1527371, by rfl⟩ : syracuseStep 2036495 = 3054743) B3054743
theorem B2036537 : Blo 1356997 2036537 := bstep (se 2 (by rfl) ⟨763701, by rfl⟩ : syracuseStep 2036537 = 1527403) B1527403
theorem B10310489 : Blo 1356997 10310489 := bstep (se 2 (by rfl) ⟨3866433, by rfl⟩ : syracuseStep 10310489 = 7732867) B7732867
theorem B2036615 : Blo 1356997 2036615 := bstep (se 1 (by rfl) ⟨1527461, by rfl⟩ : syracuseStep 2036615 = 3054923) B3054923
theorem B2036651 : Blo 1356997 2036651 := bstep (se 1 (by rfl) ⟨1527488, by rfl⟩ : syracuseStep 2036651 = 3054977) B3054977
theorem B2036681 : Blo 1356997 2036681 := bstep (se 2 (by rfl) ⟨763755, by rfl⟩ : syracuseStep 2036681 = 1527511) B1527511
theorem B6525917 : Blo 1356997 6525917 := bstep (se 3 (by rfl) ⟨1223609, by rfl⟩ : syracuseStep 6525917 = 2447219) B2447219
theorem B3437579 : Blo 1356997 3437579 := bstep (se 1 (by rfl) ⟨2578184, by rfl⟩ : syracuseStep 3437579 = 5156369) B5156369
theorem B4584491 : Blo 1356997 4584491 := bstep (se 1 (by rfl) ⟨3438368, by rfl⟩ : syracuseStep 4584491 = 6876737) B6876737
theorem B2290747 : Blo 1356997 2290747 := bstep (se 1 (by rfl) ⟨1718060, by rfl⟩ : syracuseStep 2290747 = 3436121) B3436121
theorem B2036795 : Blo 1356997 2036795 := bstep (se 1 (by rfl) ⟨1527596, by rfl⟩ : syracuseStep 2036795 = 3055193) B3055193
theorem B6190199 : Blo 1356997 6190199 := bstep (se 1 (by rfl) ⟨4642649, by rfl⟩ : syracuseStep 6190199 = 9285299) B9285299
theorem B2036855 : Blo 1356997 2036855 := bstep (se 1 (by rfl) ⟨1527641, by rfl⟩ : syracuseStep 2036855 = 3055283) B3055283
theorem B2036879 : Blo 1356997 2036879 := bstep (se 1 (by rfl) ⟨1527659, by rfl⟩ : syracuseStep 2036879 = 3055319) B3055319
theorem B2036921 : Blo 1356997 2036921 := bstep (se 2 (by rfl) ⟨763845, by rfl⟩ : syracuseStep 2036921 = 1527691) B1527691
theorem B6526145 : Blo 1356997 6526145 := bstep (se 2 (by rfl) ⟨2447304, by rfl⟩ : syracuseStep 6526145 = 4894609) B4894609
theorem B2290889 : Blo 1356997 2290889 := bstep (se 2 (by rfl) ⟨859083, by rfl⟩ : syracuseStep 2290889 = 1718167) B1718167
theorem B1357063 : Blo 1356997 1357063 := bstep (se 1 (by rfl) ⟨1017797, by rfl⟩ : syracuseStep 1357063 = 2035595) B2035595
theorem B1742087 : Blo 1356997 1742087 := bstep (se 1 (by rfl) ⟨1306565, by rfl⟩ : syracuseStep 1742087 = 2613131) B2613131
theorem B2036999 : Blo 1356997 2036999 := bstep (se 1 (by rfl) ⟨1527749, by rfl⟩ : syracuseStep 2036999 = 3055499) B3055499
theorem B1717519 : Blo 1356997 1717519 := bstep (se 1 (by rfl) ⟨1288139, by rfl⟩ : syracuseStep 1717519 = 2576279) B2576279
theorem B1357071 : Blo 1356997 1357071 := bstep (se 1 (by rfl) ⟨1017803, by rfl⟩ : syracuseStep 1357071 = 2035607) B2035607
theorem B2037035 : Blo 1356997 2037035 := bstep (se 1 (by rfl) ⟨1527776, by rfl⟩ : syracuseStep 2037035 = 3055553) B3055553
theorem B1357115 : Blo 1356997 1357115 := bstep (se 1 (by rfl) ⟨1017836, by rfl⟩ : syracuseStep 1357115 = 2035673) B2035673
theorem B2037065 : Blo 1356997 2037065 := bstep (se 2 (by rfl) ⟨763899, by rfl⟩ : syracuseStep 2037065 = 1527799) B1527799
theorem B1357191 : Blo 1356997 1357191 := bstep (se 1 (by rfl) ⟨1017893, by rfl⟩ : syracuseStep 1357191 = 2035787) B2035787
theorem B1357199 : Blo 1356997 1357199 := bstep (se 1 (by rfl) ⟨1017899, by rfl⟩ : syracuseStep 1357199 = 2035799) B2035799
theorem B6870419 : Blo 1356997 6870419 := bstep (se 1 (by rfl) ⟨5152814, by rfl⟩ : syracuseStep 6870419 = 10305629) B10305629
theorem B1357243 : Blo 1356997 1357243 := bstep (se 1 (by rfl) ⟨1017932, by rfl⟩ : syracuseStep 1357243 = 2035865) B2035865
theorem B2037179 : Blo 1356997 2037179 := bstep (se 1 (by rfl) ⟨1527884, by rfl⟩ : syracuseStep 2037179 = 3055769) B3055769
theorem B2037239 : Blo 1356997 2037239 := bstep (se 1 (by rfl) ⟨1527929, by rfl⟩ : syracuseStep 2037239 = 3055859) B3055859
theorem B1357319 : Blo 1356997 1357319 := bstep (se 1 (by rfl) ⟨1017989, by rfl⟩ : syracuseStep 1357319 = 2035979) B2035979
theorem B1357327 : Blo 1356997 1357327 := bstep (se 1 (by rfl) ⟨1017995, by rfl⟩ : syracuseStep 1357327 = 2035991) B2035991
theorem B2037263 : Blo 1356997 2037263 := bstep (se 1 (by rfl) ⟨1527947, by rfl⟩ : syracuseStep 2037263 = 3055895) B3055895
theorem B2037305 : Blo 1356997 2037305 := bstep (se 2 (by rfl) ⟨763989, by rfl⟩ : syracuseStep 2037305 = 1527979) B1527979
theorem B1357371 : Blo 1356997 1357371 := bstep (se 1 (by rfl) ⟨1018028, by rfl⟩ : syracuseStep 1357371 = 2036057) B2036057
theorem B7337591 : Blo 1356997 7337591 := bstep (se 1 (by rfl) ⟨5503193, by rfl⟩ : syracuseStep 7337591 = 11006387) B11006387
theorem B1357447 : Blo 1356997 1357447 := bstep (se 1 (by rfl) ⟨1018085, by rfl⟩ : syracuseStep 1357447 = 2036171) B2036171
theorem B2037383 : Blo 1356997 2037383 := bstep (se 1 (by rfl) ⟨1528037, by rfl⟩ : syracuseStep 2037383 = 3056075) B3056075
theorem B1357455 : Blo 1356997 1357455 := bstep (se 1 (by rfl) ⟨1018091, by rfl⟩ : syracuseStep 1357455 = 2036183) B2036183
theorem B3438227 : Blo 1356997 3438227 := bstep (se 1 (by rfl) ⟨2578670, by rfl⟩ : syracuseStep 3438227 = 5157341) B5157341
theorem B2037419 : Blo 1356997 2037419 := bstep (se 1 (by rfl) ⟨1528064, by rfl⟩ : syracuseStep 2037419 = 3056129) B3056129
theorem B1357499 : Blo 1356997 1357499 := bstep (se 1 (by rfl) ⟨1018124, by rfl⟩ : syracuseStep 1357499 = 2036249) B2036249
theorem B2037449 : Blo 1356997 2037449 := bstep (se 2 (by rfl) ⟨764043, by rfl⟩ : syracuseStep 2037449 = 1528087) B1528087
theorem B1357575 : Blo 1356997 1357575 := bstep (se 1 (by rfl) ⟨1018181, by rfl⟩ : syracuseStep 1357575 = 2036363) B2036363
theorem B1742599 : Blo 1356997 1742599 := bstep (se 1 (by rfl) ⟨1306949, by rfl⟩ : syracuseStep 1742599 = 2613899) B2613899
theorem B1357583 : Blo 1356997 1357583 := bstep (se 1 (by rfl) ⟨1018187, by rfl⟩ : syracuseStep 1357583 = 2036375) B2036375
theorem B10311461 : Blo 1356997 10311461 := bstep (se 4 (by rfl) ⟨966699, by rfl⟩ : syracuseStep 10311461 = 1933399) B1933399
theorem B2447147 : Blo 1356997 2447147 := bstep (se 1 (by rfl) ⟨1835360, by rfl⟩ : syracuseStep 2447147 = 3670721) B3670721
theorem B1357627 : Blo 1356997 1357627 := bstep (se 1 (by rfl) ⟨1018220, by rfl⟩ : syracuseStep 1357627 = 2036441) B2036441
theorem B2037563 : Blo 1356997 2037563 := bstep (se 1 (by rfl) ⟨1528172, by rfl⟩ : syracuseStep 2037563 = 3056345) B3056345
theorem B12719987 : Blo 1356997 12719987 := bstep (se 1 (by rfl) ⟨9539990, by rfl⟩ : syracuseStep 12719987 = 19079981) B19079981
theorem B12556147 : Blo 1356997 12556147 := bstep (se 1 (by rfl) ⟨9417110, by rfl⟩ : syracuseStep 12556147 = 18834221) B18834221
theorem B2037623 : Blo 1356997 2037623 := bstep (se 1 (by rfl) ⟨1528217, by rfl⟩ : syracuseStep 2037623 = 3056435) B3056435
theorem B3053447 : Blo 1356997 3053447 := bstep (se 1 (by rfl) ⟨2290085, by rfl⟩ : syracuseStep 3053447 = 4580171) B4580171
theorem B1357703 : Blo 1356997 1357703 := bstep (se 1 (by rfl) ⟨1018277, by rfl⟩ : syracuseStep 1357703 = 2036555) B2036555
theorem B2291591 : Blo 1356997 2291591 := bstep (se 1 (by rfl) ⟨1718693, by rfl⟩ : syracuseStep 2291591 = 3437387) B3437387
theorem B1357711 : Blo 1356997 1357711 := bstep (se 1 (by rfl) ⟨1018283, by rfl⟩ : syracuseStep 1357711 = 2036567) B2036567
theorem B2037647 : Blo 1356997 2037647 := bstep (se 1 (by rfl) ⟨1528235, by rfl⟩ : syracuseStep 2037647 = 3056471) B3056471
theorem B3438521 : Blo 1356997 3438521 := bstep (se 2 (by rfl) ⟨1289445, by rfl⟩ : syracuseStep 3438521 = 2578891) B2578891
theorem B2037689 : Blo 1356997 2037689 := bstep (se 2 (by rfl) ⟨764133, by rfl⟩ : syracuseStep 2037689 = 1528267) B1528267
theorem B1357755 : Blo 1356997 1357755 := bstep (se 1 (by rfl) ⟨1018316, by rfl⟩ : syracuseStep 1357755 = 2036633) B2036633
theorem B1718263 : Blo 1356997 1718263 := bstep (se 1 (by rfl) ⟨1288697, by rfl⟩ : syracuseStep 1718263 = 2577395) B2577395
theorem B1357831 : Blo 1356997 1357831 := bstep (se 1 (by rfl) ⟨1018373, by rfl⟩ : syracuseStep 1357831 = 2036747) B2036747
theorem B1357839 : Blo 1356997 1357839 := bstep (se 1 (by rfl) ⟨1018379, by rfl⟩ : syracuseStep 1357839 = 2036759) B2036759
theorem B3864635 : Blo 1356997 3864635 := bstep (se 1 (by rfl) ⟨2898476, by rfl⟩ : syracuseStep 3864635 = 5796953) B5796953
theorem B3053627 : Blo 1356997 3053627 := bstep (se 1 (by rfl) ⟨2290220, by rfl⟩ : syracuseStep 3053627 = 4580441) B4580441
theorem B1357883 : Blo 1356997 1357883 := bstep (se 1 (by rfl) ⟨1018412, by rfl⟩ : syracuseStep 1357883 = 2036825) B2036825
theorem B1357959 : Blo 1356997 1357959 := bstep (se 1 (by rfl) ⟨1018469, by rfl⟩ : syracuseStep 1357959 = 2036939) B2036939
theorem B1357967 : Blo 1356997 1357967 := bstep (se 1 (by rfl) ⟨1018475, by rfl⟩ : syracuseStep 1357967 = 2036951) B2036951
theorem B3053753 : Blo 1356997 3053753 := bstep (se 2 (by rfl) ⟨1145157, by rfl⟩ : syracuseStep 3053753 = 2290315) B2290315
theorem B1358011 : Blo 1356997 1358011 := bstep (se 1 (by rfl) ⟨1018508, by rfl⟩ : syracuseStep 1358011 = 2037017) B2037017
theorem B1358087 : Blo 1356997 1358087 := bstep (se 1 (by rfl) ⟨1018565, by rfl⟩ : syracuseStep 1358087 = 2037131) B2037131
theorem B1358095 : Blo 1356997 1358095 := bstep (se 1 (by rfl) ⟨1018571, by rfl⟩ : syracuseStep 1358095 = 2037143) B2037143
theorem B1718587 : Blo 1356997 1718587 := bstep (se 1 (by rfl) ⟨1288940, by rfl⟩ : syracuseStep 1718587 = 2577881) B2577881
theorem B1358139 : Blo 1356997 1358139 := bstep (se 1 (by rfl) ⟨1018604, by rfl⟩ : syracuseStep 1358139 = 2037209) B2037209
theorem B2578807 : Blo 1356997 2578807 := bstep (se 1 (by rfl) ⟨1934105, by rfl⟩ : syracuseStep 2578807 = 3868211) B3868211
theorem B1358215 : Blo 1356997 1358215 := bstep (se 1 (by rfl) ⟨1018661, by rfl⟩ : syracuseStep 1358215 = 2037323) B2037323
theorem B89332109 : Blo 1356997 89332109 := bstep (se 3 (by rfl) ⟨16749770, by rfl⟩ : syracuseStep 89332109 = 33499541) B33499541
theorem B1358223 : Blo 1356997 1358223 := bstep (se 1 (by rfl) ⟨1018667, by rfl⟩ : syracuseStep 1358223 = 2037335) B2037335
theorem B1358267 : Blo 1356997 1358267 := bstep (se 1 (by rfl) ⟨1018700, by rfl⟩ : syracuseStep 1358267 = 2037401) B2037401
theorem B1358343 : Blo 1356997 1358343 := bstep (se 1 (by rfl) ⟨1018757, by rfl⟩ : syracuseStep 1358343 = 2037515) B2037515
theorem B3054095 : Blo 1356997 3054095 := bstep (se 1 (by rfl) ⟨2290571, by rfl⟩ : syracuseStep 3054095 = 4581143) B4581143
theorem B1358351 : Blo 1356997 1358351 := bstep (se 1 (by rfl) ⟨1018763, by rfl⟩ : syracuseStep 1358351 = 2037527) B2037527
theorem B2292239 : Blo 1356997 2292239 := bstep (se 1 (by rfl) ⟨1719179, by rfl⟩ : syracuseStep 2292239 = 3438359) B3438359
theorem B3054113 : Blo 1356997 3054113 := bstep (se 2 (by rfl) ⟨1145292, by rfl⟩ : syracuseStep 3054113 = 2290585) B2290585
theorem B1358395 : Blo 1356997 1358395 := bstep (se 1 (by rfl) ⟨1018796, by rfl⟩ : syracuseStep 1358395 = 2037593) B2037593
theorem B1358471 : Blo 1356997 1358471 := bstep (se 1 (by rfl) ⟨1018853, by rfl⟩ : syracuseStep 1358471 = 2037707) B2037707
theorem B1358479 : Blo 1356997 1358479 := bstep (se 1 (by rfl) ⟨1018859, by rfl⟩ : syracuseStep 1358479 = 2037719) B2037719
theorem B1719083 : Blo 1356997 1719083 := bstep (se 1 (by rfl) ⟨1289312, by rfl⟩ : syracuseStep 1719083 = 2578625) B2578625
theorem B2120521 : Blo 1356997 2120521 := bstep (se 2 (by rfl) ⟨795195, by rfl⟩ : syracuseStep 2120521 = 1590391) B1590391
theorem B3054455 : Blo 1356997 3054455 := bstep (se 1 (by rfl) ⟨2290841, by rfl⟩ : syracuseStep 3054455 = 4581683) B4581683
theorem B3054635 : Blo 1356997 3054635 := bstep (se 1 (by rfl) ⟨2290976, by rfl⟩ : syracuseStep 3054635 = 4581953) B4581953
theorem B4349047 : Blo 1356997 4349047 := bstep (se 1 (by rfl) ⟨3261785, by rfl⟩ : syracuseStep 4349047 = 6523571) B6523571
theorem B2899091 : Blo 1356997 2899091 := bstep (se 1 (by rfl) ⟨2174318, by rfl⟩ : syracuseStep 2899091 = 4348637) B4348637
theorem B1375547 : Blo 1356997 1375547 := bstep (se 1 (by rfl) ⟨1031660, by rfl⟩ : syracuseStep 1375547 = 2063321) B2063321
theorem B3054995 : Blo 1356997 3054995 := bstep (se 1 (by rfl) ⟨2291246, by rfl⟩ : syracuseStep 3054995 = 4582493) B4582493
theorem B3669401 : Blo 1356997 3669401 := bstep (se 2 (by rfl) ⟨1376025, by rfl⟩ : syracuseStep 3669401 = 2752051) B2752051
theorem B3055049 : Blo 1356997 3055049 := bstep (se 2 (by rfl) ⟨1145643, by rfl⟩ : syracuseStep 3055049 = 2291287) B2291287
theorem B5799377 : Blo 1356997 5799377 := bstep (se 2 (by rfl) ⟨2174766, by rfl⟩ : syracuseStep 5799377 = 4349533) B4349533
theorem B4349483 : Blo 1356997 4349483 := bstep (se 1 (by rfl) ⟨3262112, by rfl⟩ : syracuseStep 4349483 = 6524225) B6524225
theorem B10305143 : Blo 1356997 10305143 := bstep (se 1 (by rfl) ⟨7728857, by rfl⟩ : syracuseStep 10305143 = 15457715) B15457715
theorem B2752391 : Blo 1356997 2752391 := bstep (se 1 (by rfl) ⟨2064293, by rfl⟩ : syracuseStep 2752391 = 4128587) B4128587
theorem B6291353 : Blo 1356997 6291353 := bstep (se 2 (by rfl) ⟨2359257, by rfl⟩ : syracuseStep 6291353 = 4718515) B4718515
theorem B31768523 : Blo 1356997 31768523 := bstep (se 1 (by rfl) ⟨23826392, by rfl⟩ : syracuseStep 31768523 = 47652785) B47652785
theorem B1933303 : Blo 1356997 1933303 := bstep (se 1 (by rfl) ⟨1449977, by rfl⟩ : syracuseStep 1933303 = 2899955) B2899955
theorem B4243513 : Blo 1356997 4243513 := bstep (se 2 (by rfl) ⟨1591317, by rfl⟩ : syracuseStep 4243513 = 3182635) B3182635
theorem B22020173 : Blo 1356997 22020173 := bstep (se 3 (by rfl) ⟨4128782, by rfl⟩ : syracuseStep 22020173 = 8257565) B8257565
theorem B10313891 : Blo 1356997 10313891 := bstep (se 1 (by rfl) ⟨7735418, by rfl⟩ : syracuseStep 10313891 = 15470837) B15470837
theorem B3055787 : Blo 1356997 3055787 := bstep (se 1 (by rfl) ⟨2291840, by rfl⟩ : syracuseStep 3055787 = 4583681) B4583681
theorem B3670397 : Blo 1356997 3670397 := bstep (se 3 (by rfl) ⟨688199, by rfl⟩ : syracuseStep 3670397 = 1376399) B1376399
theorem B6873659 : Blo 1356997 6873659 := bstep (se 1 (by rfl) ⟨5155244, by rfl⟩ : syracuseStep 6873659 = 10310489) B10310489
theorem B14672501 : Blo 1356997 14672501 := bstep (se 5 (by rfl) ⟨687773, by rfl⟩ : syracuseStep 14672501 = 1375547) B1375547
theorem B4350611 : Blo 1356997 4350611 := bstep (se 1 (by rfl) ⟨3262958, by rfl⟩ : syracuseStep 4350611 = 6525917) B6525917
theorem B4645565 : Blo 1356997 4645565 := bstep (se 3 (by rfl) ⟨871043, by rfl⟩ : syracuseStep 4645565 = 1742087) B1742087
theorem B3867335 : Blo 1356997 3867335 := bstep (se 1 (by rfl) ⟨2900501, by rfl⟩ : syracuseStep 3867335 = 5801003) B5801003
theorem B3056327 : Blo 1356997 3056327 := bstep (se 1 (by rfl) ⟨2292245, by rfl⟩ : syracuseStep 3056327 = 4584491) B4584491
theorem B4350763 : Blo 1356997 4350763 := bstep (se 1 (by rfl) ⟨3263072, by rfl⟩ : syracuseStep 4350763 = 6526145) B6526145
theorem B2900843 : Blo 1356997 2900843 := bstep (se 1 (by rfl) ⟨2175632, by rfl⟩ : syracuseStep 2900843 = 4351265) B4351265
theorem B4580279 : Blo 1356997 4580279 := bstep (se 1 (by rfl) ⟨3435209, by rfl⟩ : syracuseStep 4580279 = 6870419) B6870419
theorem B4891727 : Blo 1356997 4891727 := bstep (se 1 (by rfl) ⟨3668795, by rfl⟩ : syracuseStep 4891727 = 7337591) B7337591
theorem B2827361 : Blo 1356997 2827361 := bstep (se 2 (by rfl) ⟨1060260, by rfl⟩ : syracuseStep 2827361 = 2120521) B2120521
theorem B6874307 : Blo 1356997 6874307 := bstep (se 1 (by rfl) ⟨5155730, by rfl⟩ : syracuseStep 6874307 = 10311461) B10311461
theorem B1631431 : Blo 1356997 1631431 := bstep (se 1 (by rfl) ⟨1223573, by rfl⟩ : syracuseStep 1631431 = 2447147) B2447147
theorem B8479991 : Blo 1356997 8479991 := bstep (se 1 (by rfl) ⟨6359993, by rfl⟩ : syracuseStep 8479991 = 12719987) B12719987
theorem B8373527 : Blo 1356997 8373527 := bstep (se 1 (by rfl) ⟨6280145, by rfl⟩ : syracuseStep 8373527 = 12560291) B12560291
theorem B4580873 : Blo 1356997 4580873 := bstep (se 2 (by rfl) ⟨1717827, by rfl⟩ : syracuseStep 4580873 = 3435655) B3435655
theorem B5506859 : Blo 1356997 5506859 := bstep (se 1 (by rfl) ⟨4130144, by rfl⟩ : syracuseStep 5506859 = 8260289) B8260289
theorem B3671995 : Blo 1356997 3671995 := bstep (se 1 (by rfl) ⟨2753996, by rfl⟩ : syracuseStep 3671995 = 5507993) B5507993
theorem B1394767 : Blo 1356997 1394767 := bstep (se 1 (by rfl) ⟨1046075, by rfl⟩ : syracuseStep 1394767 = 2092151) B2092151
theorem B16509185 : Blo 1356997 16509185 := bstep (se 2 (by rfl) ⟨6190944, by rfl⟩ : syracuseStep 16509185 = 12381889) B12381889
theorem B4581737 : Blo 1356997 4581737 := bstep (se 2 (by rfl) ⟨1718151, by rfl⟩ : syracuseStep 4581737 = 3436303) B3436303
theorem B9791873 : Blo 1356997 9791873 := bstep (se 2 (by rfl) ⟨3671952, by rfl⟩ : syracuseStep 9791873 = 7343905) B7343905
theorem B21179015 : Blo 1356997 21179015 := bstep (se 1 (by rfl) ⟨15884261, by rfl⟩ : syracuseStep 21179015 = 31768523) B31768523
theorem B2353835 : Blo 1356997 2353835 := bstep (se 1 (by rfl) ⟨1765376, by rfl⟩ : syracuseStep 2353835 = 3530753) B3530753
theorem B89303957 : Blo 1356997 89303957 := bstep (se 6 (by rfl) ⟨2093061, by rfl⟩ : syracuseStep 89303957 = 4186123) B4186123
theorem B4582331 : Blo 1356997 4582331 := bstep (se 1 (by rfl) ⟨3436748, by rfl⟩ : syracuseStep 4582331 = 6873497) B6873497
theorem B1526863 : Blo 1356997 1526863 := bstep (se 1 (by rfl) ⟨1145147, by rfl⟩ : syracuseStep 1526863 = 2290295) B2290295
theorem B34786421 : Blo 1356997 34786421 := bstep (se 5 (by rfl) ⟨1630613, by rfl⟩ : syracuseStep 34786421 = 3261227) B3261227
theorem B3435767 : Blo 1356997 3435767 := bstep (se 1 (by rfl) ⟨2576825, by rfl⟩ : syracuseStep 3435767 = 5153651) B5153651
theorem B7736741 : Blo 1356997 7736741 := bstep (se 4 (by rfl) ⟨725319, by rfl⟩ : syracuseStep 7736741 = 1450639) B1450639
theorem B1527259 : Blo 1356997 1527259 := bstep (se 1 (by rfl) ⟨1145444, by rfl⟩ : syracuseStep 1527259 = 2290889) B2290889
theorem B5156567 : Blo 1356997 5156567 := bstep (se 1 (by rfl) ⟨3867425, by rfl⟩ : syracuseStep 5156567 = 7734851) B7734851
theorem B76320629 : Blo 1356997 76320629 := bstep (se 5 (by rfl) ⟨3577529, by rfl⟩ : syracuseStep 76320629 = 7155059) B7155059
theorem B2035631 : Blo 1356997 2035631 := bstep (se 1 (by rfl) ⟨1526723, by rfl⟩ : syracuseStep 2035631 = 3053447) B3053447
theorem B1527727 : Blo 1356997 1527727 := bstep (se 1 (by rfl) ⟨1145795, by rfl⟩ : syracuseStep 1527727 = 2291591) B2291591
theorem B2035721 : Blo 1356997 2035721 := bstep (se 2 (by rfl) ⟨763395, by rfl⟩ : syracuseStep 2035721 = 1526791) B1526791
theorem B9293861 : Blo 1356997 9293861 := bstep (se 4 (by rfl) ⟨871299, by rfl⟩ : syracuseStep 9293861 = 1742599) B1742599
theorem B2576423 : Blo 1356997 2576423 := bstep (se 1 (by rfl) ⟨1932317, by rfl⟩ : syracuseStep 2576423 = 3864635) B3864635
theorem B2035751 : Blo 1356997 2035751 := bstep (se 1 (by rfl) ⟨1526813, by rfl⟩ : syracuseStep 2035751 = 3053627) B3053627
theorem B2035835 : Blo 1356997 2035835 := bstep (se 1 (by rfl) ⟨1526876, by rfl⟩ : syracuseStep 2035835 = 3053753) B3053753
theorem B2035961 : Blo 1356997 2035961 := bstep (se 2 (by rfl) ⟨763485, by rfl⟩ : syracuseStep 2035961 = 1526971) B1526971
theorem B2036063 : Blo 1356997 2036063 := bstep (se 1 (by rfl) ⟨1527047, by rfl⟩ : syracuseStep 2036063 = 3054095) B3054095
theorem B1528159 : Blo 1356997 1528159 := bstep (se 1 (by rfl) ⟨1146119, by rfl⟩ : syracuseStep 1528159 = 2292239) B2292239
theorem B2290025 : Blo 1356997 2290025 := bstep (se 2 (by rfl) ⟨858759, by rfl⟩ : syracuseStep 2290025 = 1717519) B1717519
theorem B2036075 : Blo 1356997 2036075 := bstep (se 1 (by rfl) ⟨1527056, by rfl⟩ : syracuseStep 2036075 = 3054113) B3054113
theorem B2036303 : Blo 1356997 2036303 := bstep (se 1 (by rfl) ⟨1527227, by rfl⟩ : syracuseStep 2036303 = 3054455) B3054455
theorem B21181027 : Blo 1356997 21181027 := bstep (se 1 (by rfl) ⟨15885770, by rfl⟩ : syracuseStep 21181027 = 31771541) B31771541
theorem B4584059 : Blo 1356997 4584059 := bstep (se 1 (by rfl) ⟨3438044, by rfl⟩ : syracuseStep 4584059 = 6876089) B6876089
theorem B4895417 : Blo 1356997 4895417 := bstep (se 2 (by rfl) ⟨1835781, by rfl⟩ : syracuseStep 4895417 = 3671563) B3671563
theorem B2036423 : Blo 1356997 2036423 := bstep (se 1 (by rfl) ⟨1527317, by rfl⟩ : syracuseStep 2036423 = 3054635) B3054635
theorem B3437255 : Blo 1356997 3437255 := bstep (se 1 (by rfl) ⟨2577941, by rfl⟩ : syracuseStep 3437255 = 5155883) B5155883
theorem B2290423 : Blo 1356997 2290423 := bstep (se 1 (by rfl) ⟨1717817, by rfl⟩ : syracuseStep 2290423 = 3435635) B3435635
theorem B4584221 : Blo 1356997 4584221 := bstep (se 3 (by rfl) ⟨859541, by rfl⟩ : syracuseStep 4584221 = 1719083) B1719083
theorem B2036585 : Blo 1356997 2036585 := bstep (se 2 (by rfl) ⟨763719, by rfl⟩ : syracuseStep 2036585 = 1527439) B1527439
theorem B5223275 : Blo 1356997 5223275 := bstep (se 1 (by rfl) ⟨3917456, by rfl⟩ : syracuseStep 5223275 = 7834913) B7834913
theorem B2036663 : Blo 1356997 2036663 := bstep (se 1 (by rfl) ⟨1527497, by rfl⟩ : syracuseStep 2036663 = 3054995) B3054995
theorem B2290619 : Blo 1356997 2290619 := bstep (se 1 (by rfl) ⟨1717964, by rfl⟩ : syracuseStep 2290619 = 3435929) B3435929
theorem B2446267 : Blo 1356997 2446267 := bstep (se 1 (by rfl) ⟨1834700, by rfl⟩ : syracuseStep 2446267 = 3669401) B3669401
theorem B2036699 : Blo 1356997 2036699 := bstep (se 1 (by rfl) ⟨1527524, by rfl⟩ : syracuseStep 2036699 = 3055049) B3055049
theorem B2290727 : Blo 1356997 2290727 := bstep (se 1 (by rfl) ⟨1718045, by rfl⟩ : syracuseStep 2290727 = 3436091) B3436091
theorem B6870095 : Blo 1356997 6870095 := bstep (se 1 (by rfl) ⟨5152571, by rfl⟩ : syracuseStep 6870095 = 10305143) B10305143
theorem B17396855 : Blo 1356997 17396855 := bstep (se 1 (by rfl) ⟨13047641, by rfl⟩ : syracuseStep 17396855 = 26095283) B26095283
theorem B16741529 : Blo 1356997 16741529 := bstep (se 2 (by rfl) ⟨6278073, by rfl⟩ : syracuseStep 16741529 = 12556147) B12556147
theorem B1356999 : Blo 1356997 1356999 := bstep (se 1 (by rfl) ⟨1017749, by rfl⟩ : syracuseStep 1356999 = 2035499) B2035499
theorem B1357019 : Blo 1356997 1357019 := bstep (se 1 (by rfl) ⟨1017764, by rfl⟩ : syracuseStep 1357019 = 2035529) B2035529
theorem B19576079 : Blo 1356997 19576079 := bstep (se 1 (by rfl) ⟨14682059, by rfl⟩ : syracuseStep 19576079 = 29364119) B29364119
theorem B7943447 : Blo 1356997 7943447 := bstep (se 1 (by rfl) ⟨5957585, by rfl⟩ : syracuseStep 7943447 = 11915171) B11915171
theorem B1357095 : Blo 1356997 1357095 := bstep (se 1 (by rfl) ⟨1017821, by rfl⟩ : syracuseStep 1357095 = 2035643) B2035643
theorem B2291017 : Blo 1356997 2291017 := bstep (se 2 (by rfl) ⟨859131, by rfl⟩ : syracuseStep 2291017 = 1718263) B1718263
theorem B2577737 : Blo 1356997 2577737 := bstep (se 2 (by rfl) ⟨966651, by rfl⟩ : syracuseStep 2577737 = 1933303) B1933303
theorem B1357135 : Blo 1356997 1357135 := bstep (se 1 (by rfl) ⟨1017851, by rfl⟩ : syracuseStep 1357135 = 2035703) B2035703
theorem B1357151 : Blo 1356997 1357151 := bstep (se 1 (by rfl) ⟨1017863, by rfl⟩ : syracuseStep 1357151 = 2035727) B2035727
theorem B2291051 : Blo 1356997 2291051 := bstep (se 1 (by rfl) ⟨1718288, by rfl⟩ : syracuseStep 2291051 = 3436577) B3436577
theorem B1357179 : Blo 1356997 1357179 := bstep (se 1 (by rfl) ⟨1017884, by rfl⟩ : syracuseStep 1357179 = 2035769) B2035769
theorem B1357231 : Blo 1356997 1357231 := bstep (se 1 (by rfl) ⟨1017923, by rfl⟩ : syracuseStep 1357231 = 2035847) B2035847
theorem B2037167 : Blo 1356997 2037167 := bstep (se 1 (by rfl) ⟨1527875, by rfl⟩ : syracuseStep 2037167 = 3055751) B3055751
theorem B1357255 : Blo 1356997 1357255 := bstep (se 1 (by rfl) ⟨1017941, by rfl⟩ : syracuseStep 1357255 = 2035883) B2035883
theorem B1357275 : Blo 1356997 1357275 := bstep (se 1 (by rfl) ⟨1017956, by rfl⟩ : syracuseStep 1357275 = 2035913) B2035913
theorem B4584923 : Blo 1356997 4584923 := bstep (se 1 (by rfl) ⟨3438692, by rfl⟩ : syracuseStep 4584923 = 6877385) B6877385
theorem B2037257 : Blo 1356997 2037257 := bstep (se 2 (by rfl) ⟨763971, by rfl⟩ : syracuseStep 2037257 = 1527943) B1527943
theorem B1357351 : Blo 1356997 1357351 := bstep (se 1 (by rfl) ⟨1018013, by rfl⟩ : syracuseStep 1357351 = 2036027) B2036027
theorem B2037287 : Blo 1356997 2037287 := bstep (se 1 (by rfl) ⟨1527965, by rfl⟩ : syracuseStep 2037287 = 3055931) B3055931
theorem B1357391 : Blo 1356997 1357391 := bstep (se 1 (by rfl) ⟨1018043, by rfl⟩ : syracuseStep 1357391 = 2036087) B2036087
theorem B1357407 : Blo 1356997 1357407 := bstep (se 1 (by rfl) ⟨1018055, by rfl⟩ : syracuseStep 1357407 = 2036111) B2036111
theorem B1357435 : Blo 1356997 1357435 := bstep (se 1 (by rfl) ⟨1018076, by rfl⟩ : syracuseStep 1357435 = 2036153) B2036153
theorem B2037371 : Blo 1356997 2037371 := bstep (se 1 (by rfl) ⟨1528028, by rfl⟩ : syracuseStep 2037371 = 3056057) B3056057
theorem B1357487 : Blo 1356997 1357487 := bstep (se 1 (by rfl) ⟨1018115, by rfl⟩ : syracuseStep 1357487 = 2036231) B2036231
theorem B1357511 : Blo 1356997 1357511 := bstep (se 1 (by rfl) ⟨1018133, by rfl⟩ : syracuseStep 1357511 = 2036267) B2036267
theorem B3053267 : Blo 1356997 3053267 := bstep (se 1 (by rfl) ⟨2289950, by rfl⟩ : syracuseStep 3053267 = 4579901) B4579901
theorem B6870743 : Blo 1356997 6870743 := bstep (se 1 (by rfl) ⟨5153057, by rfl⟩ : syracuseStep 6870743 = 10306115) B10306115
theorem B1357531 : Blo 1356997 1357531 := bstep (se 1 (by rfl) ⟨1018148, by rfl⟩ : syracuseStep 1357531 = 2036297) B2036297
theorem B7730909 : Blo 1356997 7730909 := bstep (se 3 (by rfl) ⟨1449545, by rfl⟩ : syracuseStep 7730909 = 2899091) B2899091
theorem B2291449 : Blo 1356997 2291449 := bstep (se 2 (by rfl) ⟨859293, by rfl⟩ : syracuseStep 2291449 = 1718587) B1718587
theorem B2578169 : Blo 1356997 2578169 := bstep (se 2 (by rfl) ⟨966813, by rfl⟩ : syracuseStep 2578169 = 1933627) B1933627
theorem B2037497 : Blo 1356997 2037497 := bstep (se 2 (by rfl) ⟨764061, by rfl⟩ : syracuseStep 2037497 = 1528123) B1528123
theorem B1357607 : Blo 1356997 1357607 := bstep (se 1 (by rfl) ⟨1018205, by rfl⟩ : syracuseStep 1357607 = 2036411) B2036411
theorem B3438409 : Blo 1356997 3438409 := bstep (se 2 (by rfl) ⟨1289403, by rfl⟩ : syracuseStep 3438409 = 2578807) B2578807
theorem B1357647 : Blo 1356997 1357647 := bstep (se 1 (by rfl) ⟨1018235, by rfl⟩ : syracuseStep 1357647 = 2036471) B2036471
theorem B1718111 : Blo 1356997 1718111 := bstep (se 1 (by rfl) ⟨1288583, by rfl⟩ : syracuseStep 1718111 = 2577167) B2577167
theorem B1357663 : Blo 1356997 1357663 := bstep (se 1 (by rfl) ⟨1018247, by rfl⟩ : syracuseStep 1357663 = 2036495) B2036495
theorem B2037599 : Blo 1356997 2037599 := bstep (se 1 (by rfl) ⟨1528199, by rfl⟩ : syracuseStep 2037599 = 3056399) B3056399
theorem B2037611 : Blo 1356997 2037611 := bstep (se 1 (by rfl) ⟨1528208, by rfl⟩ : syracuseStep 2037611 = 3056417) B3056417
theorem B1357691 : Blo 1356997 1357691 := bstep (se 1 (by rfl) ⟨1018268, by rfl⟩ : syracuseStep 1357691 = 2036537) B2036537
theorem B4642721 : Blo 1356997 4642721 := bstep (se 2 (by rfl) ⟨1741020, by rfl⟩ : syracuseStep 4642721 = 3482041) B3482041
theorem B1357743 : Blo 1356997 1357743 := bstep (se 1 (by rfl) ⟨1018307, by rfl⟩ : syracuseStep 1357743 = 2036615) B2036615
theorem B1357767 : Blo 1356997 1357767 := bstep (se 1 (by rfl) ⟨1018325, by rfl⟩ : syracuseStep 1357767 = 2036651) B2036651
theorem B1357787 : Blo 1356997 1357787 := bstep (se 1 (by rfl) ⟨1018340, by rfl⟩ : syracuseStep 1357787 = 2036681) B2036681
theorem B2291719 : Blo 1356997 2291719 := bstep (se 1 (by rfl) ⟨1718789, by rfl⟩ : syracuseStep 2291719 = 3437579) B3437579
theorem B1357863 : Blo 1356997 1357863 := bstep (se 1 (by rfl) ⟨1018397, by rfl⟩ : syracuseStep 1357863 = 2036795) B2036795
theorem B4126799 : Blo 1356997 4126799 := bstep (se 1 (by rfl) ⟨3095099, by rfl⟩ : syracuseStep 4126799 = 6190199) B6190199
theorem B1357903 : Blo 1356997 1357903 := bstep (se 1 (by rfl) ⟨1018427, by rfl⟩ : syracuseStep 1357903 = 2036855) B2036855
theorem B1357919 : Blo 1356997 1357919 := bstep (se 1 (by rfl) ⟨1018439, by rfl⟩ : syracuseStep 1357919 = 2036879) B2036879
theorem B1357947 : Blo 1356997 1357947 := bstep (se 1 (by rfl) ⟨1018460, by rfl⟩ : syracuseStep 1357947 = 2036921) B2036921
theorem B1357999 : Blo 1356997 1357999 := bstep (se 1 (by rfl) ⟨1018499, by rfl⟩ : syracuseStep 1357999 = 2036999) B2036999
theorem B1358023 : Blo 1356997 1358023 := bstep (se 1 (by rfl) ⟨1018517, by rfl⟩ : syracuseStep 1358023 = 2037035) B2037035
theorem B1358043 : Blo 1356997 1358043 := bstep (se 1 (by rfl) ⟨1018532, by rfl⟩ : syracuseStep 1358043 = 2037065) B2037065
theorem B4348151 : Blo 1356997 4348151 := bstep (se 1 (by rfl) ⟨3261113, by rfl⟩ : syracuseStep 4348151 = 6522227) B6522227
theorem B10311947 : Blo 1356997 10311947 := bstep (se 1 (by rfl) ⟨7733960, by rfl⟩ : syracuseStep 10311947 = 15467921) B15467921
theorem B1358119 : Blo 1356997 1358119 := bstep (se 1 (by rfl) ⟨1018589, by rfl⟩ : syracuseStep 1358119 = 2037179) B2037179
theorem B1358159 : Blo 1356997 1358159 := bstep (se 1 (by rfl) ⟨1018619, by rfl⟩ : syracuseStep 1358159 = 2037239) B2037239
theorem B1358175 : Blo 1356997 1358175 := bstep (se 1 (by rfl) ⟨1018631, by rfl⟩ : syracuseStep 1358175 = 2037263) B2037263
theorem B1358203 : Blo 1356997 1358203 := bstep (se 1 (by rfl) ⟨1018652, by rfl⟩ : syracuseStep 1358203 = 2037305) B2037305
theorem B1358255 : Blo 1356997 1358255 := bstep (se 1 (by rfl) ⟨1018691, by rfl⟩ : syracuseStep 1358255 = 2037383) B2037383
theorem B2292151 : Blo 1356997 2292151 := bstep (se 1 (by rfl) ⟨1719113, by rfl⟩ : syracuseStep 2292151 = 3438227) B3438227
theorem B1358279 : Blo 1356997 1358279 := bstep (se 1 (by rfl) ⟨1018709, by rfl⟩ : syracuseStep 1358279 = 2037419) B2037419
theorem B1358299 : Blo 1356997 1358299 := bstep (se 1 (by rfl) ⟨1018724, by rfl⟩ : syracuseStep 1358299 = 2037449) B2037449
theorem B1358375 : Blo 1356997 1358375 := bstep (se 1 (by rfl) ⟨1018781, by rfl⟩ : syracuseStep 1358375 = 2037563) B2037563
theorem B15465005 : Blo 1356997 15465005 := bstep (se 3 (by rfl) ⟨2899688, by rfl⟩ : syracuseStep 15465005 = 5799377) B5799377
theorem B1358415 : Blo 1356997 1358415 := bstep (se 1 (by rfl) ⟨1018811, by rfl⟩ : syracuseStep 1358415 = 2037623) B2037623
theorem B1358431 : Blo 1356997 1358431 := bstep (se 1 (by rfl) ⟨1018823, by rfl⟩ : syracuseStep 1358431 = 2037647) B2037647
theorem B3054203 : Blo 1356997 3054203 := bstep (se 1 (by rfl) ⟨2290652, by rfl⟩ : syracuseStep 3054203 = 4581305) B4581305
theorem B2292347 : Blo 1356997 2292347 := bstep (se 1 (by rfl) ⟨1719260, by rfl⟩ : syracuseStep 2292347 = 3438521) B3438521
theorem B1358459 : Blo 1356997 1358459 := bstep (se 1 (by rfl) ⟨1018844, by rfl⟩ : syracuseStep 1358459 = 2037689) B2037689
theorem B3054329 : Blo 1356997 3054329 := bstep (se 2 (by rfl) ⟨1145373, by rfl⟩ : syracuseStep 3054329 = 2290747) B2290747
theorem B5798729 : Blo 1356997 5798729 := bstep (se 2 (by rfl) ⟨2174523, by rfl⟩ : syracuseStep 5798729 = 4349047) B4349047
theorem B1073724245 : Blo 1356997 1073724245 := bstep (se 9 (by rfl) ⟨3145676, by rfl⟩ : syracuseStep 1073724245 = 6291353) B6291353
theorem B59554739 : Blo 1356997 59554739 := bstep (se 1 (by rfl) ⟨44666054, by rfl⟩ : syracuseStep 59554739 = 89332109) B89332109
theorem B3054599 : Blo 1356997 3054599 := bstep (se 1 (by rfl) ⟨2290949, by rfl⟩ : syracuseStep 3054599 = 4581899) B4581899
theorem B8821811 : Blo 1356997 8821811 := bstep (se 1 (by rfl) ⟨6616358, by rfl⟩ : syracuseStep 8821811 = 13232717) B13232717
theorem B3054671 : Blo 1356997 3054671 := bstep (se 1 (by rfl) ⟨2291003, by rfl⟩ : syracuseStep 3054671 = 4582007) B4582007
theorem B4185473 : Blo 1356997 4185473 := bstep (se 2 (by rfl) ⟨1569552, by rfl⟩ : syracuseStep 4185473 = 3139105) B3139105
theorem B3055067 : Blo 1356997 3055067 := bstep (se 1 (by rfl) ⟨2291300, by rfl⟩ : syracuseStep 3055067 = 4582601) B4582601
theorem B7339709 : Blo 1356997 7339709 := bstep (se 3 (by rfl) ⟨1376195, by rfl⟩ : syracuseStep 7339709 = 2752391) B2752391
theorem B10313405 : Blo 1356997 10313405 := bstep (se 3 (by rfl) ⟨1933763, by rfl⟩ : syracuseStep 10313405 = 3867527) B3867527
theorem B2899655 : Blo 1356997 2899655 := bstep (se 1 (by rfl) ⟨2174741, by rfl⟩ : syracuseStep 2899655 = 4349483) B4349483
theorem B23518991 : Blo 1356997 23518991 := bstep (se 1 (by rfl) ⟨17639243, by rfl⟩ : syracuseStep 23518991 = 35278487) B35278487
theorem B3055535 : Blo 1356997 3055535 := bstep (se 1 (by rfl) ⟨2291651, by rfl⟩ : syracuseStep 3055535 = 4583303) B4583303
theorem B1449947 : Blo 1356997 1449947 := bstep (se 1 (by rfl) ⟨1087460, by rfl⟩ : syracuseStep 1449947 = 2174921) B2174921
theorem B3055625 : Blo 1356997 3055625 := bstep (se 2 (by rfl) ⟨1145859, by rfl⟩ : syracuseStep 3055625 = 2291719) B2291719
theorem B14680115 : Blo 1356997 14680115 := bstep (se 1 (by rfl) ⟨11010086, by rfl⟩ : syracuseStep 14680115 = 22020173) B22020173
theorem B1859689 : Blo 1356997 1859689 := bstep (se 2 (by rfl) ⟨697383, by rfl⟩ : syracuseStep 1859689 = 1394767) B1394767
theorem B9781667 : Blo 1356997 9781667 := bstep (se 1 (by rfl) ⟨7336250, by rfl⟩ : syracuseStep 9781667 = 14672501) B14672501
theorem B3056039 : Blo 1356997 3056039 := bstep (se 1 (by rfl) ⟨2292029, by rfl⟩ : syracuseStep 3056039 = 4584059) B4584059
theorem B2900407 : Blo 1356997 2900407 := bstep (se 1 (by rfl) ⟨2175305, by rfl⟩ : syracuseStep 2900407 = 4350611) B4350611
theorem B3097043 : Blo 1356997 3097043 := bstep (se 1 (by rfl) ⟨2322782, by rfl⟩ : syracuseStep 3097043 = 4645565) B4645565
theorem B3056147 : Blo 1356997 3056147 := bstep (se 1 (by rfl) ⟨2292110, by rfl⟩ : syracuseStep 3056147 = 4584221) B4584221
theorem B3482183 : Blo 1356997 3482183 := bstep (se 1 (by rfl) ⟨2611637, by rfl⟩ : syracuseStep 3482183 = 5223275) B5223275
theorem B1933895 : Blo 1356997 1933895 := bstep (se 1 (by rfl) ⟨1450421, by rfl⟩ : syracuseStep 1933895 = 2900843) B2900843
theorem B3056201 : Blo 1356997 3056201 := bstep (se 2 (by rfl) ⟨1146075, by rfl⟩ : syracuseStep 3056201 = 2292151) B2292151
theorem B4580063 : Blo 1356997 4580063 := bstep (se 1 (by rfl) ⟨3435047, by rfl⟩ : syracuseStep 4580063 = 6870095) B6870095
theorem B3261151 : Blo 1356997 3261151 := bstep (se 1 (by rfl) ⟨2445863, by rfl⟩ : syracuseStep 3261151 = 4891727) B4891727
theorem B1884907 : Blo 1356997 1884907 := bstep (se 1 (by rfl) ⟨1413680, by rfl⟩ : syracuseStep 1884907 = 2827361) B2827361
theorem B5653327 : Blo 1356997 5653327 := bstep (se 1 (by rfl) ⟨4239995, by rfl⟩ : syracuseStep 5653327 = 8479991) B8479991
theorem B13050719 : Blo 1356997 13050719 := bstep (se 1 (by rfl) ⟨9788039, by rfl⟩ : syracuseStep 13050719 = 19576079) B19576079
theorem B3056615 : Blo 1356997 3056615 := bstep (se 1 (by rfl) ⟨2292461, by rfl⟩ : syracuseStep 3056615 = 4584923) B4584923
theorem B8700965 : Blo 1356997 8700965 := bstep (se 4 (by rfl) ⟨815715, by rfl⟩ : syracuseStep 8700965 = 1631431) B1631431
theorem B4580495 : Blo 1356997 4580495 := bstep (se 1 (by rfl) ⟨3435371, by rfl⟩ : syracuseStep 4580495 = 6870743) B6870743
theorem B5153939 : Blo 1356997 5153939 := bstep (se 1 (by rfl) ⟨3865454, by rfl⟩ : syracuseStep 5153939 = 7730909) B7730909
theorem B3671239 : Blo 1356997 3671239 := bstep (se 1 (by rfl) ⟨2753429, by rfl⟩ : syracuseStep 3671239 = 5506859) B5506859
theorem B3261689 : Blo 1356997 3261689 := bstep (se 2 (by rfl) ⟨1223133, by rfl⟩ : syracuseStep 3261689 = 2446267) B2446267
theorem B6874631 : Blo 1356997 6874631 := bstep (se 1 (by rfl) ⟨5155973, by rfl⟩ : syracuseStep 6874631 = 10311947) B10311947
theorem B6875117 : Blo 1356997 6875117 := bstep (se 3 (by rfl) ⟨1289084, by rfl⟩ : syracuseStep 6875117 = 2578169) B2578169
theorem B4581629 : Blo 1356997 4581629 := bstep (se 3 (by rfl) ⟨859055, by rfl⟩ : syracuseStep 4581629 = 1718111) B1718111
theorem B4893139 : Blo 1356997 4893139 := bstep (se 1 (by rfl) ⟨3669854, by rfl⟩ : syracuseStep 4893139 = 7339709) B7339709
theorem B6875603 : Blo 1356997 6875603 := bstep (se 1 (by rfl) ⟨5156702, by rfl⟩ : syracuseStep 6875603 = 10313405) B10313405
theorem B6195907 : Blo 1356997 6195907 := bstep (se 1 (by rfl) ⟨4646930, by rfl⟩ : syracuseStep 6195907 = 9293861) B9293861
theorem B6875927 : Blo 1356997 6875927 := bstep (se 1 (by rfl) ⟨5156945, by rfl⟩ : syracuseStep 6875927 = 10313891) B10313891
theorem B11004797 : Blo 1356997 11004797 := bstep (se 3 (by rfl) ⟨2063399, by rfl⟩ : syracuseStep 11004797 = 4126799) B4126799
theorem B1526683 : Blo 1356997 1526683 := bstep (se 1 (by rfl) ⟨1145012, by rfl⟩ : syracuseStep 1526683 = 2290025) B2290025
theorem B4582439 : Blo 1356997 4582439 := bstep (se 1 (by rfl) ⟨3436829, by rfl⟩ : syracuseStep 4582439 = 6873659) B6873659
theorem B1527079 : Blo 1356997 1527079 := bstep (se 1 (by rfl) ⟨1145309, by rfl⟩ : syracuseStep 1527079 = 2290619) B2290619
theorem B1527151 : Blo 1356997 1527151 := bstep (se 1 (by rfl) ⟨1145363, by rfl⟩ : syracuseStep 1527151 = 2290727) B2290727
theorem B11161019 : Blo 1356997 11161019 := bstep (se 1 (by rfl) ⟨8370764, by rfl⟩ : syracuseStep 11161019 = 16741529) B16741529
theorem B4582871 : Blo 1356997 4582871 := bstep (se 1 (by rfl) ⟨3437153, by rfl⟩ : syracuseStep 4582871 = 6874307) B6874307
theorem B28241369 : Blo 1356997 28241369 := bstep (se 2 (by rfl) ⟨10590513, by rfl⟩ : syracuseStep 28241369 = 21181027) B21181027
theorem B5295631 : Blo 1356997 5295631 := bstep (se 1 (by rfl) ⟨3971723, by rfl⟩ : syracuseStep 5295631 = 7943447) B7943447
theorem B5582351 : Blo 1356997 5582351 := bstep (se 1 (by rfl) ⟨4186763, by rfl⟩ : syracuseStep 5582351 = 8373527) B8373527
theorem B1527367 : Blo 1356997 1527367 := bstep (se 1 (by rfl) ⟨1145525, by rfl⟩ : syracuseStep 1527367 = 2291051) B2291051
theorem B11161261 : Blo 1356997 11161261 := bstep (se 3 (by rfl) ⟨2092736, by rfl⟩ : syracuseStep 11161261 = 4185473) B4185473
theorem B2035511 : Blo 1356997 2035511 := bstep (se 1 (by rfl) ⟨1526633, by rfl⟩ : syracuseStep 2035511 = 3053267) B3053267
theorem B2035817 : Blo 1356997 2035817 := bstep (se 2 (by rfl) ⟨763431, by rfl⟩ : syracuseStep 2035817 = 1526863) B1526863
theorem B11006123 : Blo 1356997 11006123 := bstep (se 1 (by rfl) ⟨8254592, by rfl⟩ : syracuseStep 11006123 = 16509185) B16509185
theorem B23204069 : Blo 1356997 23204069 := bstep (se 4 (by rfl) ⟨2175381, by rfl⟩ : syracuseStep 23204069 = 4350763) B4350763
theorem B10310003 : Blo 1356997 10310003 := bstep (se 1 (by rfl) ⟨7732502, by rfl⟩ : syracuseStep 10310003 = 15465005) B15465005
theorem B2036135 : Blo 1356997 2036135 := bstep (se 1 (by rfl) ⟨1527101, by rfl⟩ : syracuseStep 2036135 = 3054203) B3054203
theorem B1528231 : Blo 1356997 1528231 := bstep (se 1 (by rfl) ⟨1146173, by rfl⟩ : syracuseStep 1528231 = 2292347) B2292347
theorem B14119343 : Blo 1356997 14119343 := bstep (se 1 (by rfl) ⟨10589507, by rfl⟩ : syracuseStep 14119343 = 21179015) B21179015
theorem B1569223 : Blo 1356997 1569223 := bstep (se 1 (by rfl) ⟨1176917, by rfl⟩ : syracuseStep 1569223 = 2353835) B2353835
theorem B13054445 : Blo 1356997 13054445 := bstep (se 3 (by rfl) ⟨2447708, by rfl⟩ : syracuseStep 13054445 = 4895417) B4895417
theorem B2036219 : Blo 1356997 2036219 := bstep (se 1 (by rfl) ⟨1527164, by rfl⟩ : syracuseStep 2036219 = 3054329) B3054329
theorem B59535971 : Blo 1356997 59535971 := bstep (se 1 (by rfl) ⟨44651978, by rfl⟩ : syracuseStep 59535971 = 89303957) B89303957
theorem B39703159 : Blo 1356997 39703159 := bstep (se 1 (by rfl) ⟨29777369, by rfl⟩ : syracuseStep 39703159 = 59554739) B59554739
theorem B2036345 : Blo 1356997 2036345 := bstep (se 2 (by rfl) ⟨763629, by rfl⟩ : syracuseStep 2036345 = 1527259) B1527259
theorem B2036399 : Blo 1356997 2036399 := bstep (se 1 (by rfl) ⟨1527299, by rfl⟩ : syracuseStep 2036399 = 3054599) B3054599
theorem B2036447 : Blo 1356997 2036447 := bstep (se 1 (by rfl) ⟨1527335, by rfl⟩ : syracuseStep 2036447 = 3054671) B3054671
theorem B2290511 : Blo 1356997 2290511 := bstep (se 1 (by rfl) ⟨1717883, by rfl⟩ : syracuseStep 2290511 = 3435767) B3435767
theorem B5157827 : Blo 1356997 5157827 := bstep (se 1 (by rfl) ⟨3868370, by rfl⟩ : syracuseStep 5157827 = 7736741) B7736741
theorem B2036711 : Blo 1356997 2036711 := bstep (se 1 (by rfl) ⟨1527533, by rfl⟩ : syracuseStep 2036711 = 3055067) B3055067
theorem B4584545 : Blo 1356997 4584545 := bstep (se 2 (by rfl) ⟨1719204, by rfl⟩ : syracuseStep 4584545 = 3438409) B3438409
theorem B3437711 : Blo 1356997 3437711 := bstep (se 1 (by rfl) ⟨2578283, by rfl⟩ : syracuseStep 3437711 = 5156567) B5156567
theorem B2036969 : Blo 1356997 2036969 := bstep (se 2 (by rfl) ⟨763863, by rfl⟩ : syracuseStep 2036969 = 1527727) B1527727
theorem B4895993 : Blo 1356997 4895993 := bstep (se 2 (by rfl) ⟨1835997, by rfl⟩ : syracuseStep 4895993 = 3671995) B3671995
theorem B1357087 : Blo 1356997 1357087 := bstep (se 1 (by rfl) ⟨1017815, by rfl⟩ : syracuseStep 1357087 = 2035631) B2035631
theorem B2037023 : Blo 1356997 2037023 := bstep (se 1 (by rfl) ⟨1527767, by rfl⟩ : syracuseStep 2037023 = 3055535) B3055535
theorem B1357147 : Blo 1356997 1357147 := bstep (se 1 (by rfl) ⟨1017860, by rfl⟩ : syracuseStep 1357147 = 2035721) B2035721
theorem B1717615 : Blo 1356997 1717615 := bstep (se 1 (by rfl) ⟨1288211, by rfl⟩ : syracuseStep 1717615 = 2576423) B2576423
theorem B1357167 : Blo 1356997 1357167 := bstep (se 1 (by rfl) ⟨1017875, by rfl⟩ : syracuseStep 1357167 = 2035751) B2035751
theorem B5658017 : Blo 1356997 5658017 := bstep (se 2 (by rfl) ⟨2121756, by rfl⟩ : syracuseStep 5658017 = 4243513) B4243513
theorem B1357223 : Blo 1356997 1357223 := bstep (se 1 (by rfl) ⟨1017917, by rfl⟩ : syracuseStep 1357223 = 2035835) B2035835
theorem B2037191 : Blo 1356997 2037191 := bstep (se 1 (by rfl) ⟨1527893, by rfl⟩ : syracuseStep 2037191 = 3055787) B3055787
theorem B23524829 : Blo 1356997 23524829 := bstep (se 3 (by rfl) ⟨4410905, by rfl⟩ : syracuseStep 23524829 = 8821811) B8821811
theorem B1357307 : Blo 1356997 1357307 := bstep (se 1 (by rfl) ⟨1017980, by rfl⟩ : syracuseStep 1357307 = 2035961) B2035961
theorem B1357375 : Blo 1356997 1357375 := bstep (se 1 (by rfl) ⟨1018031, by rfl⟩ : syracuseStep 1357375 = 2036063) B2036063
theorem B1357383 : Blo 1356997 1357383 := bstep (se 1 (by rfl) ⟨1018037, by rfl⟩ : syracuseStep 1357383 = 2036075) B2036075
theorem B2446931 : Blo 1356997 2446931 := bstep (se 1 (by rfl) ⟨1835198, by rfl⟩ : syracuseStep 2446931 = 3670397) B3670397
theorem B1357535 : Blo 1356997 1357535 := bstep (se 1 (by rfl) ⟨1018151, by rfl⟩ : syracuseStep 1357535 = 2036303) B2036303
theorem B2037545 : Blo 1356997 2037545 := bstep (se 2 (by rfl) ⟨764079, by rfl⟩ : syracuseStep 2037545 = 1528159) B1528159
theorem B1357615 : Blo 1356997 1357615 := bstep (se 1 (by rfl) ⟨1018211, by rfl⟩ : syracuseStep 1357615 = 2036423) B2036423
theorem B2291503 : Blo 1356997 2291503 := bstep (se 1 (by rfl) ⟨1718627, by rfl⟩ : syracuseStep 2291503 = 3437255) B3437255
theorem B2578223 : Blo 1356997 2578223 := bstep (se 1 (by rfl) ⟨1933667, by rfl⟩ : syracuseStep 2578223 = 3867335) B3867335
theorem B2037551 : Blo 1356997 2037551 := bstep (se 1 (by rfl) ⟨1528163, by rfl⟩ : syracuseStep 2037551 = 3056327) B3056327
theorem B1357723 : Blo 1356997 1357723 := bstep (se 1 (by rfl) ⟨1018292, by rfl⟩ : syracuseStep 1357723 = 2036585) B2036585
theorem B3053519 : Blo 1356997 3053519 := bstep (se 1 (by rfl) ⟨2290139, by rfl⟩ : syracuseStep 3053519 = 4580279) B4580279
theorem B1357775 : Blo 1356997 1357775 := bstep (se 1 (by rfl) ⟨1018331, by rfl⟩ : syracuseStep 1357775 = 2036663) B2036663
theorem B1357799 : Blo 1356997 1357799 := bstep (se 1 (by rfl) ⟨1018349, by rfl⟩ : syracuseStep 1357799 = 2036699) B2036699
theorem B11597903 : Blo 1356997 11597903 := bstep (se 1 (by rfl) ⟨8698427, by rfl⟩ : syracuseStep 11597903 = 17396855) B17396855
theorem B1718491 : Blo 1356997 1718491 := bstep (se 1 (by rfl) ⟨1288868, by rfl⟩ : syracuseStep 1718491 = 2577737) B2577737
theorem B1358111 : Blo 1356997 1358111 := bstep (se 1 (by rfl) ⟨1018583, by rfl⟩ : syracuseStep 1358111 = 2037167) B2037167
theorem B3053897 : Blo 1356997 3053897 := bstep (se 2 (by rfl) ⟨1145211, by rfl⟩ : syracuseStep 3053897 = 2290423) B2290423
theorem B3053915 : Blo 1356997 3053915 := bstep (se 1 (by rfl) ⟨2290436, by rfl⟩ : syracuseStep 3053915 = 4580873) B4580873
theorem B1358171 : Blo 1356997 1358171 := bstep (se 1 (by rfl) ⟨1018628, by rfl⟩ : syracuseStep 1358171 = 2037257) B2037257
theorem B1358191 : Blo 1356997 1358191 := bstep (se 1 (by rfl) ⟨1018643, by rfl⟩ : syracuseStep 1358191 = 2037287) B2037287
theorem B1358247 : Blo 1356997 1358247 := bstep (se 1 (by rfl) ⟨1018685, by rfl⟩ : syracuseStep 1358247 = 2037371) B2037371
theorem B1358331 : Blo 1356997 1358331 := bstep (se 1 (by rfl) ⟨1018748, by rfl⟩ : syracuseStep 1358331 = 2037497) B2037497
theorem B1358399 : Blo 1356997 1358399 := bstep (se 1 (by rfl) ⟨1018799, by rfl⟩ : syracuseStep 1358399 = 2037599) B2037599
theorem B1358407 : Blo 1356997 1358407 := bstep (se 1 (by rfl) ⟨1018805, by rfl⟩ : syracuseStep 1358407 = 2037611) B2037611
theorem B3095147 : Blo 1356997 3095147 := bstep (se 1 (by rfl) ⟨2321360, by rfl⟩ : syracuseStep 3095147 = 4642721) B4642721
theorem B2898767 : Blo 1356997 2898767 := bstep (se 1 (by rfl) ⟨2174075, by rfl⟩ : syracuseStep 2898767 = 4348151) B4348151
theorem B3054491 : Blo 1356997 3054491 := bstep (se 1 (by rfl) ⟨2290868, by rfl⟩ : syracuseStep 3054491 = 4581737) B4581737
theorem B6527915 : Blo 1356997 6527915 := bstep (se 1 (by rfl) ⟨4895936, by rfl⟩ : syracuseStep 6527915 = 9791873) B9791873
theorem B3054689 : Blo 1356997 3054689 := bstep (se 2 (by rfl) ⟨1145508, by rfl⟩ : syracuseStep 3054689 = 2291017) B2291017
theorem B3865819 : Blo 1356997 3865819 := bstep (se 1 (by rfl) ⟨2899364, by rfl⟩ : syracuseStep 3865819 = 5798729) B5798729
theorem B715816163 : Blo 1356997 715816163 := bstep (se 1 (by rfl) ⟨536862122, by rfl⟩ : syracuseStep 715816163 = 1073724245) B1073724245
theorem B3054887 : Blo 1356997 3054887 := bstep (se 1 (by rfl) ⟨2291165, by rfl⟩ : syracuseStep 3054887 = 4582331) B4582331
theorem B23190947 : Blo 1356997 23190947 := bstep (se 1 (by rfl) ⟨17393210, by rfl⟩ : syracuseStep 23190947 = 34786421) B34786421
theorem B3055265 : Blo 1356997 3055265 := bstep (se 2 (by rfl) ⟨1145724, by rfl⟩ : syracuseStep 3055265 = 2291449) B2291449
theorem B1933103 : Blo 1356997 1933103 := bstep (se 1 (by rfl) ⟨1449827, by rfl⟩ : syracuseStep 1933103 = 2899655) B2899655
theorem B15679327 : Blo 1356997 15679327 := bstep (se 1 (by rfl) ⟨11759495, by rfl⟩ : syracuseStep 15679327 = 23518991) B23518991
theorem B3866525 : Blo 1356997 3866525 := bstep (se 3 (by rfl) ⟨724973, by rfl⟩ : syracuseStep 3866525 = 1449947) B1449947
theorem B50880419 : Blo 1356997 50880419 := bstep (se 1 (by rfl) ⟨38160314, by rfl⟩ : syracuseStep 50880419 = 76320629) B76320629
theorem B6873335 : Blo 1356997 6873335 := bstep (se 1 (by rfl) ⟨5155001, by rfl⟩ : syracuseStep 6873335 = 10310003) B10310003
theorem B6521111 : Blo 1356997 6521111 := bstep (se 1 (by rfl) ⟨4890833, by rfl⟩ : syracuseStep 6521111 = 9781667) B9781667
theorem B9412895 : Blo 1356997 9412895 := bstep (se 1 (by rfl) ⟨7059671, by rfl⟩ : syracuseStep 9412895 = 14119343) B14119343
theorem B2064695 : Blo 1356997 2064695 := bstep (se 1 (by rfl) ⟨1548521, by rfl⟩ : syracuseStep 2064695 = 3097043) B3097043
theorem B39690647 : Blo 1356997 39690647 := bstep (se 1 (by rfl) ⟨29767985, by rfl⟩ : syracuseStep 39690647 = 59535971) B59535971
theorem B8700479 : Blo 1356997 8700479 := bstep (se 1 (by rfl) ⟨6525359, by rfl⟩ : syracuseStep 8700479 = 13050719) B13050719
theorem B3867209 : Blo 1356997 3867209 := bstep (se 2 (by rfl) ⟨1450203, by rfl⟩ : syracuseStep 3867209 = 2900407) B2900407
theorem B5800643 : Blo 1356997 5800643 := bstep (se 1 (by rfl) ⟨4350482, by rfl⟩ : syracuseStep 5800643 = 8700965) B8700965
theorem B3056363 : Blo 1356997 3056363 := bstep (se 1 (by rfl) ⟨2292272, by rfl⟩ : syracuseStep 3056363 = 4584545) B4584545
theorem B52937545 : Blo 1356997 52937545 := bstep (se 2 (by rfl) ⟨19851579, by rfl⟩ : syracuseStep 52937545 = 39703159) B39703159
theorem B1631287 : Blo 1356997 1631287 := bstep (se 1 (by rfl) ⟨1223465, by rfl⟩ : syracuseStep 1631287 = 2446931) B2446931
theorem B7537769 : Blo 1356997 7537769 := bstep (se 2 (by rfl) ⟨2826663, by rfl⟩ : syracuseStep 7537769 = 5653327) B5653327
theorem B14886269 : Blo 1356997 14886269 := bstep (se 3 (by rfl) ⟨2791175, by rfl⟩ : syracuseStep 14886269 = 5582351) B5582351
theorem B5154425 : Blo 1356997 5154425 := bstep (se 2 (by rfl) ⟨1932909, by rfl⟩ : syracuseStep 5154425 = 3865819) B3865819
theorem B4351943 : Blo 1356997 4351943 := bstep (se 1 (by rfl) ⟨3263957, by rfl⟩ : syracuseStep 4351943 = 6527915) B6527915
theorem B5154941 : Blo 1356997 5154941 := bstep (se 3 (by rfl) ⟨966551, by rfl⟩ : syracuseStep 5154941 = 1933103) B1933103
theorem B477210775 : Blo 1356997 477210775 := bstep (se 1 (by rfl) ⟨357908081, by rfl⟩ : syracuseStep 477210775 = 715816163) B715816163
theorem B15460631 : Blo 1356997 15460631 := bstep (se 1 (by rfl) ⟨11595473, by rfl⟩ : syracuseStep 15460631 = 23190947) B23190947
theorem B7440679 : Blo 1356997 7440679 := bstep (se 1 (by rfl) ⟨5580509, by rfl⟩ : syracuseStep 7440679 = 11161019) B11161019
theorem B18827579 : Blo 1356997 18827579 := bstep (se 1 (by rfl) ⟨14120684, by rfl⟩ : syracuseStep 18827579 = 28241369) B28241369
theorem B15469379 : Blo 1356997 15469379 := bstep (se 1 (by rfl) ⟨11602034, by rfl⟩ : syracuseStep 15469379 = 23204069) B23204069
theorem B8702963 : Blo 1356997 8702963 := bstep (se 1 (by rfl) ⟨6527222, by rfl⟩ : syracuseStep 8702963 = 13054445) B13054445
theorem B2321455 : Blo 1356997 2321455 := bstep (se 1 (by rfl) ⟨1741091, by rfl⟩ : syracuseStep 2321455 = 3482183) B3482183
theorem B1527007 : Blo 1356997 1527007 := bstep (se 1 (by rfl) ⟨1145255, by rfl⟩ : syracuseStep 1527007 = 2290511) B2290511
theorem B3435959 : Blo 1356997 3435959 := bstep (se 1 (by rfl) ⟨2576969, by rfl⟩ : syracuseStep 3435959 = 5153939) B5153939
theorem B2174459 : Blo 1356997 2174459 := bstep (se 1 (by rfl) ⟨1630844, by rfl⟩ : syracuseStep 2174459 = 3261689) B3261689
theorem B3263995 : Blo 1356997 3263995 := bstep (se 1 (by rfl) ⟨2447996, by rfl⟩ : syracuseStep 3263995 = 4895993) B4895993
theorem B8261209 : Blo 1356997 8261209 := bstep (se 2 (by rfl) ⟨3097953, by rfl⟩ : syracuseStep 8261209 = 6195907) B6195907
theorem B15683219 : Blo 1356997 15683219 := bstep (se 1 (by rfl) ⟨11762414, by rfl⟩ : syracuseStep 15683219 = 23524829) B23524829
theorem B4583087 : Blo 1356997 4583087 := bstep (se 1 (by rfl) ⟨3437315, by rfl⟩ : syracuseStep 4583087 = 6874631) B6874631
theorem B2035577 : Blo 1356997 2035577 := bstep (se 2 (by rfl) ⟨763341, by rfl⟩ : syracuseStep 2035577 = 1526683) B1526683
theorem B2035679 : Blo 1356997 2035679 := bstep (se 1 (by rfl) ⟨1526759, by rfl⟩ : syracuseStep 2035679 = 3053519) B3053519
theorem B4583411 : Blo 1356997 4583411 := bstep (se 1 (by rfl) ⟨3437558, by rfl⟩ : syracuseStep 4583411 = 6875117) B6875117
theorem B5157053 : Blo 1356997 5157053 := bstep (se 3 (by rfl) ⟨966947, by rfl⟩ : syracuseStep 5157053 = 1933895) B1933895
theorem B2035931 : Blo 1356997 2035931 := bstep (se 1 (by rfl) ⟨1526948, by rfl⟩ : syracuseStep 2035931 = 3053897) B3053897
theorem B2035943 : Blo 1356997 2035943 := bstep (se 1 (by rfl) ⟨1526957, by rfl⟩ : syracuseStep 2035943 = 3053915) B3053915
theorem B4894985 : Blo 1356997 4894985 := bstep (se 2 (by rfl) ⟨1835619, by rfl⟩ : syracuseStep 4894985 = 3671239) B3671239
theorem B4583735 : Blo 1356997 4583735 := bstep (se 1 (by rfl) ⟨3437801, by rfl⟩ : syracuseStep 4583735 = 6875603) B6875603
theorem B2036105 : Blo 1356997 2036105 := bstep (se 2 (by rfl) ⟨763539, by rfl⟩ : syracuseStep 2036105 = 1527079) B1527079
theorem B2290153 : Blo 1356997 2290153 := bstep (se 2 (by rfl) ⟨858807, by rfl⟩ : syracuseStep 2290153 = 1717615) B1717615
theorem B2036201 : Blo 1356997 2036201 := bstep (se 2 (by rfl) ⟨763575, by rfl⟩ : syracuseStep 2036201 = 1527151) B1527151
theorem B4583951 : Blo 1356997 4583951 := bstep (se 1 (by rfl) ⟨3437963, by rfl⟩ : syracuseStep 4583951 = 6875927) B6875927
theorem B7336531 : Blo 1356997 7336531 := bstep (se 1 (by rfl) ⟨5502398, by rfl⟩ : syracuseStep 7336531 = 11004797) B11004797
theorem B2036327 : Blo 1356997 2036327 := bstep (se 1 (by rfl) ⟨1527245, by rfl⟩ : syracuseStep 2036327 = 3054491) B3054491
theorem B2036459 : Blo 1356997 2036459 := bstep (se 1 (by rfl) ⟨1527344, by rfl⟩ : syracuseStep 2036459 = 3054689) B3054689
theorem B2036489 : Blo 1356997 2036489 := bstep (se 2 (by rfl) ⟨763683, by rfl⟩ : syracuseStep 2036489 = 1527367) B1527367
theorem B2036591 : Blo 1356997 2036591 := bstep (se 1 (by rfl) ⟨1527443, by rfl⟩ : syracuseStep 2036591 = 3054887) B3054887
theorem B14881681 : Blo 1356997 14881681 := bstep (se 2 (by rfl) ⟨5580630, by rfl⟩ : syracuseStep 14881681 = 11161261) B11161261
theorem B8369189 : Blo 1356997 8369189 := bstep (se 4 (by rfl) ⟨784611, by rfl⟩ : syracuseStep 8369189 = 1569223) B1569223
theorem B26096741 : Blo 1356997 26096741 := bstep (se 4 (by rfl) ⟨2446569, by rfl⟩ : syracuseStep 26096741 = 4893139) B4893139
theorem B2036843 : Blo 1356997 2036843 := bstep (se 1 (by rfl) ⟨1527632, by rfl⟩ : syracuseStep 2036843 = 3055265) B3055265
theorem B1357007 : Blo 1356997 1357007 := bstep (se 1 (by rfl) ⟨1017755, by rfl⟩ : syracuseStep 1357007 = 2035511) B2035511
theorem B2577683 : Blo 1356997 2577683 := bstep (se 1 (by rfl) ⟨1933262, by rfl⟩ : syracuseStep 2577683 = 3866525) B3866525
theorem B33920279 : Blo 1356997 33920279 := bstep (se 1 (by rfl) ⟨25440209, by rfl⟩ : syracuseStep 33920279 = 50880419) B50880419
theorem B2037083 : Blo 1356997 2037083 := bstep (se 1 (by rfl) ⟨1527812, by rfl⟩ : syracuseStep 2037083 = 3055625) B3055625
theorem B9786743 : Blo 1356997 9786743 := bstep (se 1 (by rfl) ⟨7340057, by rfl⟩ : syracuseStep 9786743 = 14680115) B14680115
theorem B1357211 : Blo 1356997 1357211 := bstep (se 1 (by rfl) ⟨1017908, by rfl⟩ : syracuseStep 1357211 = 2035817) B2035817
theorem B2479585 : Blo 1356997 2479585 := bstep (se 2 (by rfl) ⟨929844, by rfl⟩ : syracuseStep 2479585 = 1859689) B1859689
theorem B1357423 : Blo 1356997 1357423 := bstep (se 1 (by rfl) ⟨1018067, by rfl⟩ : syracuseStep 1357423 = 2036135) B2036135
theorem B2037359 : Blo 1356997 2037359 := bstep (se 1 (by rfl) ⟨1528019, by rfl⟩ : syracuseStep 2037359 = 3056039) B3056039
theorem B2291321 : Blo 1356997 2291321 := bstep (se 2 (by rfl) ⟨859245, by rfl⟩ : syracuseStep 2291321 = 1718491) B1718491
theorem B1357479 : Blo 1356997 1357479 := bstep (se 1 (by rfl) ⟨1018109, by rfl⟩ : syracuseStep 1357479 = 2036219) B2036219
theorem B2037431 : Blo 1356997 2037431 := bstep (se 1 (by rfl) ⟨1528073, by rfl⟩ : syracuseStep 2037431 = 3056147) B3056147
theorem B2037467 : Blo 1356997 2037467 := bstep (se 1 (by rfl) ⟨1528100, by rfl⟩ : syracuseStep 2037467 = 3056201) B3056201
theorem B1357563 : Blo 1356997 1357563 := bstep (se 1 (by rfl) ⟨1018172, by rfl⟩ : syracuseStep 1357563 = 2036345) B2036345
theorem B29349661 : Blo 1356997 29349661 := bstep (se 3 (by rfl) ⟨5503061, by rfl⟩ : syracuseStep 29349661 = 11006123) B11006123
theorem B1357599 : Blo 1356997 1357599 := bstep (se 1 (by rfl) ⟨1018199, by rfl⟩ : syracuseStep 1357599 = 2036399) B2036399
theorem B3053375 : Blo 1356997 3053375 := bstep (se 1 (by rfl) ⟨2290031, by rfl⟩ : syracuseStep 3053375 = 4580063) B4580063
theorem B1357631 : Blo 1356997 1357631 := bstep (se 1 (by rfl) ⟨1018223, by rfl⟩ : syracuseStep 1357631 = 2036447) B2036447
theorem B2037641 : Blo 1356997 2037641 := bstep (se 2 (by rfl) ⟨764115, by rfl⟩ : syracuseStep 2037641 = 1528231) B1528231
theorem B3438551 : Blo 1356997 3438551 := bstep (se 1 (by rfl) ⟨2578913, by rfl⟩ : syracuseStep 3438551 = 5157827) B5157827
theorem B1357807 : Blo 1356997 1357807 := bstep (se 1 (by rfl) ⟨1018355, by rfl⟩ : syracuseStep 1357807 = 2036711) B2036711
theorem B2037743 : Blo 1356997 2037743 := bstep (se 1 (by rfl) ⟨1528307, by rfl⟩ : syracuseStep 2037743 = 3056615) B3056615
theorem B3053663 : Blo 1356997 3053663 := bstep (se 1 (by rfl) ⟨2290247, by rfl⟩ : syracuseStep 3053663 = 4580495) B4580495
theorem B2291807 : Blo 1356997 2291807 := bstep (se 1 (by rfl) ⟨1718855, by rfl⟩ : syracuseStep 2291807 = 3437711) B3437711
theorem B1357979 : Blo 1356997 1357979 := bstep (se 1 (by rfl) ⟨1018484, by rfl⟩ : syracuseStep 1357979 = 2036969) B2036969
theorem B1358015 : Blo 1356997 1358015 := bstep (se 1 (by rfl) ⟨1018511, by rfl⟩ : syracuseStep 1358015 = 2037023) B2037023
theorem B4348201 : Blo 1356997 4348201 := bstep (se 2 (by rfl) ⟨1630575, by rfl⟩ : syracuseStep 4348201 = 3261151) B3261151
theorem B1358127 : Blo 1356997 1358127 := bstep (se 1 (by rfl) ⟨1018595, by rfl⟩ : syracuseStep 1358127 = 2037191) B2037191
theorem B2513209 : Blo 1356997 2513209 := bstep (se 2 (by rfl) ⟨942453, by rfl⟩ : syracuseStep 2513209 = 1884907) B1884907
theorem B15088045 : Blo 1356997 15088045 := bstep (se 3 (by rfl) ⟨2829008, by rfl⟩ : syracuseStep 15088045 = 5658017) B5658017
theorem B1358363 : Blo 1356997 1358363 := bstep (se 1 (by rfl) ⟨1018772, by rfl⟩ : syracuseStep 1358363 = 2037545) B2037545
theorem B1718815 : Blo 1356997 1718815 := bstep (se 1 (by rfl) ⟨1289111, by rfl⟩ : syracuseStep 1718815 = 2578223) B2578223
theorem B1358367 : Blo 1356997 1358367 := bstep (se 1 (by rfl) ⟨1018775, by rfl⟩ : syracuseStep 1358367 = 2037551) B2037551
theorem B7731935 : Blo 1356997 7731935 := bstep (se 1 (by rfl) ⟨5798951, by rfl⟩ : syracuseStep 7731935 = 11597903) B11597903
theorem B3054419 : Blo 1356997 3054419 := bstep (se 1 (by rfl) ⟨2290814, by rfl⟩ : syracuseStep 3054419 = 4581629) B4581629
theorem B2063431 : Blo 1356997 2063431 := bstep (se 1 (by rfl) ⟨1547573, by rfl⟩ : syracuseStep 2063431 = 3095147) B3095147
theorem B1932511 : Blo 1356997 1932511 := bstep (se 1 (by rfl) ⟨1449383, by rfl⟩ : syracuseStep 1932511 = 2898767) B2898767
theorem B7060841 : Blo 1356997 7060841 := bstep (se 2 (by rfl) ⟨2647815, by rfl⟩ : syracuseStep 7060841 = 5295631) B5295631
theorem B3054959 : Blo 1356997 3054959 := bstep (se 1 (by rfl) ⟨2291219, by rfl⟩ : syracuseStep 3054959 = 4582439) B4582439
theorem B3055247 : Blo 1356997 3055247 := bstep (se 1 (by rfl) ⟨2291435, by rfl⟩ : syracuseStep 3055247 = 4582871) B4582871
theorem B3055337 : Blo 1356997 3055337 := bstep (se 2 (by rfl) ⟨1145751, by rfl⟩ : syracuseStep 3055337 = 2291503) B2291503
theorem B20905769 : Blo 1356997 20905769 := bstep (se 2 (by rfl) ⟨7839663, by rfl⟩ : syracuseStep 20905769 = 15679327) B15679327
theorem B636281033 : Blo 1356997 636281033 := bstep (se 2 (by rfl) ⟨238605387, by rfl⟩ : syracuseStep 636281033 = 477210775) B477210775
theorem B3055823 : Blo 1356997 3055823 := bstep (se 1 (by rfl) ⟨2291867, by rfl⟩ : syracuseStep 3055823 = 4583735) B4583735
theorem B26460431 : Blo 1356997 26460431 := bstep (se 1 (by rfl) ⟨19845323, by rfl⟩ : syracuseStep 26460431 = 39690647) B39690647
theorem B3055967 : Blo 1356997 3055967 := bstep (se 1 (by rfl) ⟨2291975, by rfl⟩ : syracuseStep 3055967 = 4583951) B4583951
theorem B5800319 : Blo 1356997 5800319 := bstep (se 1 (by rfl) ⟨4350239, by rfl⟩ : syracuseStep 5800319 = 8700479) B8700479
theorem B3350945 : Blo 1356997 3350945 := bstep (se 2 (by rfl) ⟨1256604, by rfl⟩ : syracuseStep 3350945 = 2513209) B2513209
theorem B3867095 : Blo 1356997 3867095 := bstep (se 1 (by rfl) ⟨2900321, by rfl⟩ : syracuseStep 3867095 = 5800643) B5800643
theorem B5579459 : Blo 1356997 5579459 := bstep (se 1 (by rfl) ⟨4184594, by rfl⟩ : syracuseStep 5579459 = 8369189) B8369189
theorem B6873821 : Blo 1356997 6873821 := bstep (se 3 (by rfl) ⟨1288841, by rfl⟩ : syracuseStep 6873821 = 2577683) B2577683
theorem B25101053 : Blo 1356997 25101053 := bstep (se 3 (by rfl) ⟨4706447, by rfl⟩ : syracuseStep 25101053 = 9412895) B9412895
theorem B9782041 : Blo 1356997 9782041 := bstep (se 2 (by rfl) ⟨3668265, by rfl⟩ : syracuseStep 9782041 = 7336531) B7336531
theorem B5505853 : Blo 1356997 5505853 := bstep (se 3 (by rfl) ⟨1032347, by rfl⟩ : syracuseStep 5505853 = 2064695) B2064695
theorem B70583393 : Blo 1356997 70583393 := bstep (se 2 (by rfl) ⟨26468772, by rfl⟩ : syracuseStep 70583393 = 52937545) B52937545
theorem B19842241 : Blo 1356997 19842241 := bstep (se 2 (by rfl) ⟨7440840, by rfl⟩ : syracuseStep 19842241 = 14881681) B14881681
theorem B2901295 : Blo 1356997 2901295 := bstep (se 1 (by rfl) ⟨2175971, by rfl⟩ : syracuseStep 2901295 = 4351943) B4351943
theorem B10307087 : Blo 1356997 10307087 := bstep (se 1 (by rfl) ⟨7730315, by rfl⟩ : syracuseStep 10307087 = 15460631) B15460631
theorem B39683621 : Blo 1356997 39683621 := bstep (se 4 (by rfl) ⟨3720339, by rfl⟩ : syracuseStep 39683621 = 7440679) B7440679
theorem B5154623 : Blo 1356997 5154623 := bstep (se 1 (by rfl) ⟨3865967, by rfl⟩ : syracuseStep 5154623 = 7731935) B7731935
theorem B5801975 : Blo 1356997 5801975 := bstep (se 1 (by rfl) ⟨4351481, by rfl⟩ : syracuseStep 5801975 = 8702963) B8702963
theorem B10455479 : Blo 1356997 10455479 := bstep (se 1 (by rfl) ⟨7841609, by rfl⟩ : syracuseStep 10455479 = 15683219) B15683219
theorem B13937179 : Blo 1356997 13937179 := bstep (se 1 (by rfl) ⟨10452884, by rfl⟩ : syracuseStep 13937179 = 20905769) B20905769
theorem B4582223 : Blo 1356997 4582223 := bstep (se 1 (by rfl) ⟨3436667, by rfl⟩ : syracuseStep 4582223 = 6873335) B6873335
theorem B3263323 : Blo 1356997 3263323 := bstep (se 1 (by rfl) ⟨2447492, by rfl⟩ : syracuseStep 3263323 = 4894985) B4894985
theorem B44059781 : Blo 1356997 44059781 := bstep (se 4 (by rfl) ⟨4130604, by rfl⟩ : syracuseStep 44059781 = 8261209) B8261209
theorem B5025179 : Blo 1356997 5025179 := bstep (se 1 (by rfl) ⟨3768884, by rfl⟩ : syracuseStep 5025179 = 7537769) B7537769
theorem B22613519 : Blo 1356997 22613519 := bstep (se 1 (by rfl) ⟨16960139, by rfl⟩ : syracuseStep 22613519 = 33920279) B33920279
theorem B6524495 : Blo 1356997 6524495 := bstep (se 1 (by rfl) ⟨4893371, by rfl⟩ : syracuseStep 6524495 = 9786743) B9786743
theorem B9924179 : Blo 1356997 9924179 := bstep (se 1 (by rfl) ⟨7443134, by rfl⟩ : syracuseStep 9924179 = 14886269) B14886269
theorem B3436283 : Blo 1356997 3436283 := bstep (se 1 (by rfl) ⟨2577212, by rfl⟩ : syracuseStep 3436283 = 5154425) B5154425
theorem B1527547 : Blo 1356997 1527547 := bstep (se 1 (by rfl) ⟨1145660, by rfl⟩ : syracuseStep 1527547 = 2291321) B2291321
theorem B2035583 : Blo 1356997 2035583 := bstep (se 1 (by rfl) ⟨1526687, by rfl⟩ : syracuseStep 2035583 = 3053375) B3053375
theorem B2035775 : Blo 1356997 2035775 := bstep (se 1 (by rfl) ⟨1526831, by rfl⟩ : syracuseStep 2035775 = 3053663) B3053663
theorem B1527871 : Blo 1356997 1527871 := bstep (se 1 (by rfl) ⟨1145903, by rfl⟩ : syracuseStep 1527871 = 2291807) B2291807
theorem B2175049 : Blo 1356997 2175049 := bstep (se 2 (by rfl) ⟨815643, by rfl⟩ : syracuseStep 2175049 = 1631287) B1631287
theorem B3436627 : Blo 1356997 3436627 := bstep (se 1 (by rfl) ⟨2577470, by rfl⟩ : syracuseStep 3436627 = 5154941) B5154941
theorem B2576681 : Blo 1356997 2576681 := bstep (se 2 (by rfl) ⟨966255, by rfl⟩ : syracuseStep 2576681 = 1932511) B1932511
theorem B2036009 : Blo 1356997 2036009 := bstep (se 2 (by rfl) ⟨763503, by rfl⟩ : syracuseStep 2036009 = 1527007) B1527007
theorem B2036279 : Blo 1356997 2036279 := bstep (se 1 (by rfl) ⟨1527209, by rfl⟩ : syracuseStep 2036279 = 3054419) B3054419
theorem B3306113 : Blo 1356997 3306113 := bstep (se 2 (by rfl) ⟨1239792, by rfl⟩ : syracuseStep 3306113 = 2479585) B2479585
theorem B4707227 : Blo 1356997 4707227 := bstep (se 1 (by rfl) ⟨3530420, by rfl⟩ : syracuseStep 4707227 = 7060841) B7060841
theorem B2036639 : Blo 1356997 2036639 := bstep (se 1 (by rfl) ⟨1527479, by rfl⟩ : syracuseStep 2036639 = 3054959) B3054959
theorem B2290639 : Blo 1356997 2290639 := bstep (se 1 (by rfl) ⟨1717979, by rfl⟩ : syracuseStep 2290639 = 3435959) B3435959
theorem B2036831 : Blo 1356997 2036831 := bstep (se 1 (by rfl) ⟨1527623, by rfl⟩ : syracuseStep 2036831 = 3055247) B3055247
theorem B2036891 : Blo 1356997 2036891 := bstep (se 1 (by rfl) ⟨1527668, by rfl⟩ : syracuseStep 2036891 = 3055337) B3055337
theorem B3055607 : Blo 1356997 3055607 := bstep (se 1 (by rfl) ⟨2291705, by rfl⟩ : syracuseStep 3055607 = 4583411) B4583411
theorem B1357051 : Blo 1356997 1357051 := bstep (se 1 (by rfl) ⟨1017788, by rfl⟩ : syracuseStep 1357051 = 2035577) B2035577
theorem B1357119 : Blo 1356997 1357119 := bstep (se 1 (by rfl) ⟨1017839, by rfl⟩ : syracuseStep 1357119 = 2035679) B2035679
theorem B3438035 : Blo 1356997 3438035 := bstep (se 1 (by rfl) ⟨2578526, by rfl⟩ : syracuseStep 3438035 = 5157053) B5157053
theorem B1357287 : Blo 1356997 1357287 := bstep (se 1 (by rfl) ⟨1017965, by rfl⟩ : syracuseStep 1357287 = 2035931) B2035931
theorem B1357295 : Blo 1356997 1357295 := bstep (se 1 (by rfl) ⟨1017971, by rfl⟩ : syracuseStep 1357295 = 2035943) B2035943
theorem B4347407 : Blo 1356997 4347407 := bstep (se 1 (by rfl) ⟨3260555, by rfl⟩ : syracuseStep 4347407 = 6521111) B6521111
theorem B1357403 : Blo 1356997 1357403 := bstep (se 1 (by rfl) ⟨1018052, by rfl⟩ : syracuseStep 1357403 = 2036105) B2036105
theorem B1357467 : Blo 1356997 1357467 := bstep (se 1 (by rfl) ⟨1018100, by rfl⟩ : syracuseStep 1357467 = 2036201) B2036201
theorem B2578139 : Blo 1356997 2578139 := bstep (se 1 (by rfl) ⟨1933604, by rfl⟩ : syracuseStep 2578139 = 3867209) B3867209
theorem B5797601 : Blo 1356997 5797601 := bstep (se 2 (by rfl) ⟨2174100, by rfl⟩ : syracuseStep 5797601 = 4348201) B4348201
theorem B1357551 : Blo 1356997 1357551 := bstep (se 1 (by rfl) ⟨1018163, by rfl⟩ : syracuseStep 1357551 = 2036327) B2036327
theorem B1357639 : Blo 1356997 1357639 := bstep (se 1 (by rfl) ⟨1018229, by rfl⟩ : syracuseStep 1357639 = 2036459) B2036459
theorem B2037575 : Blo 1356997 2037575 := bstep (se 1 (by rfl) ⟨1528181, by rfl⟩ : syracuseStep 2037575 = 3056363) B3056363
theorem B1357659 : Blo 1356997 1357659 := bstep (se 1 (by rfl) ⟨1018244, by rfl⟩ : syracuseStep 1357659 = 2036489) B2036489
theorem B20117393 : Blo 1356997 20117393 := bstep (se 2 (by rfl) ⟨7544022, by rfl⟩ : syracuseStep 20117393 = 15088045) B15088045
theorem B1357727 : Blo 1356997 1357727 := bstep (se 1 (by rfl) ⟨1018295, by rfl⟩ : syracuseStep 1357727 = 2036591) B2036591
theorem B3053537 : Blo 1356997 3053537 := bstep (se 2 (by rfl) ⟨1145076, by rfl⟩ : syracuseStep 3053537 = 2290153) B2290153
theorem B2291753 : Blo 1356997 2291753 := bstep (se 2 (by rfl) ⟨859407, by rfl⟩ : syracuseStep 2291753 = 1718815) B1718815
theorem B17397827 : Blo 1356997 17397827 := bstep (se 1 (by rfl) ⟨13048370, by rfl⟩ : syracuseStep 17397827 = 26096741) B26096741
theorem B1357895 : Blo 1356997 1357895 := bstep (se 1 (by rfl) ⟨1018421, by rfl⟩ : syracuseStep 1357895 = 2036843) B2036843
theorem B50206877 : Blo 1356997 50206877 := bstep (se 3 (by rfl) ⟨9413789, by rfl⟩ : syracuseStep 50206877 = 18827579) B18827579
theorem B1358055 : Blo 1356997 1358055 := bstep (se 1 (by rfl) ⟨1018541, by rfl⟩ : syracuseStep 1358055 = 2037083) B2037083
theorem B1358239 : Blo 1356997 1358239 := bstep (se 1 (by rfl) ⟨1018679, by rfl⟩ : syracuseStep 1358239 = 2037359) B2037359
theorem B1358287 : Blo 1356997 1358287 := bstep (se 1 (by rfl) ⟨1018715, by rfl⟩ : syracuseStep 1358287 = 2037431) B2037431
theorem B1358311 : Blo 1356997 1358311 := bstep (se 1 (by rfl) ⟨1018733, by rfl⟩ : syracuseStep 1358311 = 2037467) B2037467
theorem B1358427 : Blo 1356997 1358427 := bstep (se 1 (by rfl) ⟨1018820, by rfl⟩ : syracuseStep 1358427 = 2037641) B2037641
theorem B2292367 : Blo 1356997 2292367 := bstep (se 1 (by rfl) ⟨1719275, by rfl⟩ : syracuseStep 2292367 = 3438551) B3438551
theorem B5798557 : Blo 1356997 5798557 := bstep (se 3 (by rfl) ⟨1087229, by rfl⟩ : syracuseStep 5798557 = 2174459) B2174459
theorem B1358495 : Blo 1356997 1358495 := bstep (se 1 (by rfl) ⟨1018871, by rfl⟩ : syracuseStep 1358495 = 2037743) B2037743
theorem B3095273 : Blo 1356997 3095273 := bstep (se 2 (by rfl) ⟨1160727, by rfl⟩ : syracuseStep 3095273 = 2321455) B2321455
theorem B2751241 : Blo 1356997 2751241 := bstep (se 2 (by rfl) ⟨1031715, by rfl⟩ : syracuseStep 2751241 = 2063431) B2063431
theorem B10312919 : Blo 1356997 10312919 := bstep (se 1 (by rfl) ⟨7734689, by rfl⟩ : syracuseStep 10312919 = 15469379) B15469379
theorem B39132881 : Blo 1356997 39132881 := bstep (se 2 (by rfl) ⟨14674830, by rfl⟩ : syracuseStep 39132881 = 29349661) B29349661
theorem B3055391 : Blo 1356997 3055391 := bstep (se 1 (by rfl) ⟨2291543, by rfl⟩ : syracuseStep 3055391 = 4583087) B4583087
theorem B17407973 : Blo 1356997 17407973 := bstep (se 4 (by rfl) ⟨1631997, by rfl⟩ : syracuseStep 17407973 = 3263995) B3263995
theorem B2900065 : Blo 1356997 2900065 := bstep (se 2 (by rfl) ⟨1087524, by rfl⟩ : syracuseStep 2900065 = 2175049) B2175049
theorem B3866879 : Blo 1356997 3866879 := bstep (se 1 (by rfl) ⟨2900159, by rfl⟩ : syracuseStep 3866879 = 5800319) B5800319
theorem B2204075 : Blo 1356997 2204075 := bstep (se 1 (by rfl) ⟨1653056, by rfl⟩ : syracuseStep 2204075 = 3306113) B3306113
theorem B3719639 : Blo 1356997 3719639 := bstep (se 1 (by rfl) ⟨2789729, by rfl⟩ : syracuseStep 3719639 = 5579459) B5579459
theorem B3138151 : Blo 1356997 3138151 := bstep (se 1 (by rfl) ⟨2353613, by rfl⟩ : syracuseStep 3138151 = 4707227) B4707227
theorem B47055595 : Blo 1356997 47055595 := bstep (se 1 (by rfl) ⟨35291696, by rfl⟩ : syracuseStep 47055595 = 70583393) B70583393
theorem B3056489 : Blo 1356997 3056489 := bstep (se 2 (by rfl) ⟨1146183, by rfl⟩ : syracuseStep 3056489 = 2292367) B2292367
theorem B13042721 : Blo 1356997 13042721 := bstep (se 2 (by rfl) ⟨4891020, by rfl⟩ : syracuseStep 13042721 = 9782041) B9782041
theorem B7341137 : Blo 1356997 7341137 := bstep (se 2 (by rfl) ⟨2752926, by rfl⟩ : syracuseStep 7341137 = 5505853) B5505853
theorem B4351097 : Blo 1356997 4351097 := bstep (se 2 (by rfl) ⟨1631661, by rfl⟩ : syracuseStep 4351097 = 3263323) B3263323
theorem B13411595 : Blo 1356997 13411595 := bstep (se 1 (by rfl) ⟨10058696, by rfl⟩ : syracuseStep 13411595 = 20117393) B20117393
theorem B3867983 : Blo 1356997 3867983 := bstep (se 1 (by rfl) ⟨2900987, by rfl⟩ : syracuseStep 3867983 = 5801975) B5801975
theorem B60302717 : Blo 1356997 60302717 := bstep (se 3 (by rfl) ⟨11306759, by rfl⟩ : syracuseStep 60302717 = 22613519) B22613519
theorem B3868393 : Blo 1356997 3868393 := bstep (se 2 (by rfl) ⟨1450647, by rfl⟩ : syracuseStep 3868393 = 2901295) B2901295
theorem B6875279 : Blo 1356997 6875279 := bstep (se 1 (by rfl) ⟨5156459, by rfl⟩ : syracuseStep 6875279 = 10312919) B10312919
theorem B4582169 : Blo 1356997 4582169 := bstep (se 2 (by rfl) ⟨1718313, by rfl⟩ : syracuseStep 4582169 = 3436627) B3436627
theorem B17640287 : Blo 1356997 17640287 := bstep (se 1 (by rfl) ⟨13230215, by rfl⟩ : syracuseStep 17640287 = 26460431) B26460431
theorem B4582547 : Blo 1356997 4582547 := bstep (se 1 (by rfl) ⟨3436910, by rfl⟩ : syracuseStep 4582547 = 6873821) B6873821
theorem B18582905 : Blo 1356997 18582905 := bstep (se 2 (by rfl) ⟨6968589, by rfl⟩ : syracuseStep 18582905 = 13937179) B13937179
theorem B26455747 : Blo 1356997 26455747 := bstep (se 1 (by rfl) ⟨19841810, by rfl⟩ : syracuseStep 26455747 = 39683621) B39683621
theorem B3436415 : Blo 1356997 3436415 := bstep (se 1 (by rfl) ⟨2577311, by rfl⟩ : syracuseStep 3436415 = 5154623) B5154623
theorem B2035691 : Blo 1356997 2035691 := bstep (se 1 (by rfl) ⟨1526768, by rfl⟩ : syracuseStep 2035691 = 3053537) B3053537
theorem B1527835 : Blo 1356997 1527835 := bstep (se 1 (by rfl) ⟨1145876, by rfl⟩ : syracuseStep 1527835 = 2291753) B2291753
theorem B26464477 : Blo 1356997 26464477 := bstep (se 3 (by rfl) ⟨4962089, by rfl⟩ : syracuseStep 26464477 = 9924179) B9924179
theorem B26456321 : Blo 1356997 26456321 := bstep (se 2 (by rfl) ⟨9921120, by rfl⟩ : syracuseStep 26456321 = 19842241) B19842241
theorem B8254061 : Blo 1356997 8254061 := bstep (se 3 (by rfl) ⟨1547636, by rfl⟩ : syracuseStep 8254061 = 3095273) B3095273
theorem B29373187 : Blo 1356997 29373187 := bstep (se 1 (by rfl) ⟨22029890, by rfl⟩ : syracuseStep 29373187 = 44059781) B44059781
theorem B2036729 : Blo 1356997 2036729 := bstep (se 2 (by rfl) ⟨763773, by rfl⟩ : syracuseStep 2036729 = 1527547) B1527547
theorem B26088587 : Blo 1356997 26088587 := bstep (se 1 (by rfl) ⟨19566440, by rfl⟩ : syracuseStep 26088587 = 39132881) B39132881
theorem B2290855 : Blo 1356997 2290855 := bstep (se 1 (by rfl) ⟨1718141, by rfl⟩ : syracuseStep 2290855 = 3436283) B3436283
theorem B2036927 : Blo 1356997 2036927 := bstep (se 1 (by rfl) ⟨1527695, by rfl⟩ : syracuseStep 2036927 = 3055391) B3055391
theorem B1357055 : Blo 1356997 1357055 := bstep (se 1 (by rfl) ⟨1017791, by rfl⟩ : syracuseStep 1357055 = 2035583) B2035583
theorem B11605315 : Blo 1356997 11605315 := bstep (se 1 (by rfl) ⟨8703986, by rfl⟩ : syracuseStep 11605315 = 17407973) B17407973
theorem B2037071 : Blo 1356997 2037071 := bstep (se 1 (by rfl) ⟨1527803, by rfl⟩ : syracuseStep 2037071 = 3055607) B3055607
theorem B1357183 : Blo 1356997 1357183 := bstep (se 1 (by rfl) ⟨1017887, by rfl⟩ : syracuseStep 1357183 = 2035775) B2035775
theorem B2037161 : Blo 1356997 2037161 := bstep (se 2 (by rfl) ⟨763935, by rfl⟩ : syracuseStep 2037161 = 1527871) B1527871
theorem B2037215 : Blo 1356997 2037215 := bstep (se 1 (by rfl) ⟨1527911, by rfl⟩ : syracuseStep 2037215 = 3055823) B3055823
theorem B1717787 : Blo 1356997 1717787 := bstep (se 1 (by rfl) ⟨1288340, by rfl⟩ : syracuseStep 1717787 = 2576681) B2576681
theorem B1357339 : Blo 1356997 1357339 := bstep (se 1 (by rfl) ⟨1018004, by rfl⟩ : syracuseStep 1357339 = 2036009) B2036009
theorem B2037311 : Blo 1356997 2037311 := bstep (se 1 (by rfl) ⟨1527983, by rfl⟩ : syracuseStep 2037311 = 3055967) B3055967
theorem B2233963 : Blo 1356997 2233963 := bstep (se 1 (by rfl) ⟨1675472, by rfl⟩ : syracuseStep 2233963 = 3350945) B3350945
theorem B2578063 : Blo 1356997 2578063 := bstep (se 1 (by rfl) ⟨1933547, by rfl⟩ : syracuseStep 2578063 = 3867095) B3867095
theorem B1357519 : Blo 1356997 1357519 := bstep (se 1 (by rfl) ⟨1018139, by rfl⟩ : syracuseStep 1357519 = 2036279) B2036279
theorem B16734035 : Blo 1356997 16734035 := bstep (se 1 (by rfl) ⟨12550526, by rfl⟩ : syracuseStep 16734035 = 25101053) B25101053
theorem B1357759 : Blo 1356997 1357759 := bstep (se 1 (by rfl) ⟨1018319, by rfl⟩ : syracuseStep 1357759 = 2036639) B2036639
theorem B1357887 : Blo 1356997 1357887 := bstep (se 1 (by rfl) ⟨1018415, by rfl⟩ : syracuseStep 1357887 = 2036831) B2036831
theorem B1357927 : Blo 1356997 1357927 := bstep (se 1 (by rfl) ⟨1018445, by rfl⟩ : syracuseStep 1357927 = 2036891) B2036891
theorem B7731409 : Blo 1356997 7731409 := bstep (se 2 (by rfl) ⟨2899278, by rfl⟩ : syracuseStep 7731409 = 5798557) B5798557
theorem B2292023 : Blo 1356997 2292023 := bstep (se 1 (by rfl) ⟨1719017, by rfl⟩ : syracuseStep 2292023 = 3438035) B3438035
theorem B2898271 : Blo 1356997 2898271 := bstep (se 1 (by rfl) ⟨2173703, by rfl⟩ : syracuseStep 2898271 = 4347407) B4347407
theorem B6871391 : Blo 1356997 6871391 := bstep (se 1 (by rfl) ⟨5153543, by rfl⟩ : syracuseStep 6871391 = 10307087) B10307087
theorem B3668321 : Blo 1356997 3668321 := bstep (se 2 (by rfl) ⟨1375620, by rfl⟩ : syracuseStep 3668321 = 2751241) B2751241
theorem B13400477 : Blo 1356997 13400477 := bstep (se 3 (by rfl) ⟨2512589, by rfl⟩ : syracuseStep 13400477 = 5025179) B5025179
theorem B1718759 : Blo 1356997 1718759 := bstep (se 1 (by rfl) ⟨1289069, by rfl⟩ : syracuseStep 1718759 = 2578139) B2578139
theorem B3865067 : Blo 1356997 3865067 := bstep (se 1 (by rfl) ⟨2898800, by rfl⟩ : syracuseStep 3865067 = 5797601) B5797601
theorem B1358383 : Blo 1356997 1358383 := bstep (se 1 (by rfl) ⟨1018787, by rfl⟩ : syracuseStep 1358383 = 2037575) B2037575
theorem B3054185 : Blo 1356997 3054185 := bstep (se 2 (by rfl) ⟨1145319, by rfl⟩ : syracuseStep 3054185 = 2290639) B2290639
theorem B11598551 : Blo 1356997 11598551 := bstep (se 1 (by rfl) ⟨8698913, by rfl⟩ : syracuseStep 11598551 = 17397827) B17397827
theorem B33471251 : Blo 1356997 33471251 := bstep (se 1 (by rfl) ⟨25103438, by rfl⟩ : syracuseStep 33471251 = 50206877) B50206877
theorem B6970319 : Blo 1356997 6970319 := bstep (se 1 (by rfl) ⟨5227739, by rfl⟩ : syracuseStep 6970319 = 10455479) B10455479
theorem B3054815 : Blo 1356997 3054815 := bstep (se 1 (by rfl) ⟨2291111, by rfl⟩ : syracuseStep 3054815 = 4582223) B4582223
theorem B6786997685 : Blo 1356997 6786997685 := bstep (se 5 (by rfl) ⟨318140516, by rfl⟩ : syracuseStep 6786997685 = 636281033) B636281033
theorem B4349663 : Blo 1356997 4349663 := bstep (se 1 (by rfl) ⟨3262247, by rfl⟩ : syracuseStep 4349663 = 6524495) B6524495
theorem B3866753 : Blo 1356997 3866753 := bstep (se 2 (by rfl) ⟨1450032, by rfl⟩ : syracuseStep 3866753 = 2900065) B2900065
theorem B17637547 : Blo 1356997 17637547 := bstep (se 1 (by rfl) ⟨13228160, by rfl⟩ : syracuseStep 17637547 = 26456321) B26456321
theorem B17392391 : Blo 1356997 17392391 := bstep (se 1 (by rfl) ⟨13044293, by rfl⟩ : syracuseStep 17392391 = 26088587) B26088587
theorem B49554413 : Blo 1356997 49554413 := bstep (se 3 (by rfl) ⟨9291452, by rfl⟩ : syracuseStep 49554413 = 18582905) B18582905
theorem B4580765 : Blo 1356997 4580765 := bstep (se 3 (by rfl) ⟨858893, by rfl⟩ : syracuseStep 4580765 = 1717787) B1717787
theorem B4580927 : Blo 1356997 4580927 := bstep (se 1 (by rfl) ⟨3435695, by rfl⟩ : syracuseStep 4580927 = 6871391) B6871391
theorem B4646879 : Blo 1356997 4646879 := bstep (se 1 (by rfl) ⟨3485159, by rfl⟩ : syracuseStep 4646879 = 6970319) B6970319
theorem B4524665123 : Blo 1356997 4524665123 := bstep (se 1 (by rfl) ⟨3393498842, by rfl⟩ : syracuseStep 4524665123 = 6786997685) B6786997685
theorem B10308545 : Blo 1356997 10308545 := bstep (se 2 (by rfl) ⟨3865704, by rfl⟩ : syracuseStep 10308545 = 7731409) B7731409
theorem B1469383 : Blo 1356997 1469383 := bstep (se 1 (by rfl) ⟨1102037, by rfl⟩ : syracuseStep 1469383 = 2204075) B2204075
theorem B35285969 : Blo 1356997 35285969 := bstep (se 2 (by rfl) ⟨13232238, by rfl⟩ : syracuseStep 35285969 = 26464477) B26464477
theorem B11602925 : Blo 1356997 11602925 := bstep (se 3 (by rfl) ⟨2175548, by rfl⟩ : syracuseStep 11602925 = 4351097) B4351097
theorem B11914469 : Blo 1356997 11914469 := bstep (se 4 (by rfl) ⟨1116981, by rfl⟩ : syracuseStep 11914469 = 2233963) B2233963
theorem B8695147 : Blo 1356997 8695147 := bstep (se 1 (by rfl) ⟨6521360, by rfl⟩ : syracuseStep 8695147 = 13042721) B13042721
theorem B4894091 : Blo 1356997 4894091 := bstep (se 1 (by rfl) ⟨3670568, by rfl⟩ : syracuseStep 4894091 = 7341137) B7341137
theorem B40201811 : Blo 1356997 40201811 := bstep (se 1 (by rfl) ⟨30151358, by rfl⟩ : syracuseStep 40201811 = 60302717) B60302717
theorem B4583357 : Blo 1356997 4583357 := bstep (se 3 (by rfl) ⟨859379, by rfl⟩ : syracuseStep 4583357 = 1718759) B1718759
theorem B4583519 : Blo 1356997 4583519 := bstep (se 1 (by rfl) ⟨3437639, by rfl⟩ : syracuseStep 4583519 = 6875279) B6875279
theorem B1528015 : Blo 1356997 1528015 := bstep (se 1 (by rfl) ⟨1146011, by rfl⟩ : syracuseStep 1528015 = 2292023) B2292023
theorem B2445547 : Blo 1356997 2445547 := bstep (se 1 (by rfl) ⟨1834160, by rfl⟩ : syracuseStep 2445547 = 3668321) B3668321
theorem B8933651 : Blo 1356997 8933651 := bstep (se 1 (by rfl) ⟨6700238, by rfl⟩ : syracuseStep 8933651 = 13400477) B13400477
theorem B2576711 : Blo 1356997 2576711 := bstep (se 1 (by rfl) ⟨1932533, by rfl⟩ : syracuseStep 2576711 = 3865067) B3865067
theorem B2036123 : Blo 1356997 2036123 := bstep (se 1 (by rfl) ⟨1527092, by rfl⟩ : syracuseStep 2036123 = 3054185) B3054185
theorem B11760191 : Blo 1356997 11760191 := bstep (se 1 (by rfl) ⟨8820143, by rfl⟩ : syracuseStep 11760191 = 17640287) B17640287
theorem B2036543 : Blo 1356997 2036543 := bstep (se 1 (by rfl) ⟨1527407, by rfl⟩ : syracuseStep 2036543 = 3054815) B3054815
theorem B3437417 : Blo 1356997 3437417 := bstep (se 2 (by rfl) ⟨1289031, by rfl⟩ : syracuseStep 3437417 = 2578063) B2578063
theorem B5157857 : Blo 1356997 5157857 := bstep (se 2 (by rfl) ⟨1934196, by rfl⟩ : syracuseStep 5157857 = 3868393) B3868393
theorem B2290943 : Blo 1356997 2290943 := bstep (se 1 (by rfl) ⟨1718207, by rfl⟩ : syracuseStep 2290943 = 3436415) B3436415
theorem B1357127 : Blo 1356997 1357127 := bstep (se 1 (by rfl) ⟨1017845, by rfl⟩ : syracuseStep 1357127 = 2035691) B2035691
theorem B2037113 : Blo 1356997 2037113 := bstep (se 2 (by rfl) ⟨763917, by rfl⟩ : syracuseStep 2037113 = 1527835) B1527835
theorem B2577919 : Blo 1356997 2577919 := bstep (se 1 (by rfl) ⟨1933439, by rfl⟩ : syracuseStep 2577919 = 3866879) B3866879
theorem B2479759 : Blo 1356997 2479759 := bstep (se 1 (by rfl) ⟨1859819, by rfl⟩ : syracuseStep 2479759 = 3719639) B3719639
theorem B5502707 : Blo 1356997 5502707 := bstep (se 1 (by rfl) ⟨4127030, by rfl⟩ : syracuseStep 5502707 = 8254061) B8254061
theorem B3864361 : Blo 1356997 3864361 := bstep (se 2 (by rfl) ⟨1449135, by rfl⟩ : syracuseStep 3864361 = 2898271) B2898271
theorem B2037659 : Blo 1356997 2037659 := bstep (se 1 (by rfl) ⟨1528244, by rfl⟩ : syracuseStep 2037659 = 3056489) B3056489
theorem B1357819 : Blo 1356997 1357819 := bstep (se 1 (by rfl) ⟨1018364, by rfl⟩ : syracuseStep 1357819 = 2036729) B2036729
theorem B35764253 : Blo 1356997 35764253 := bstep (se 3 (by rfl) ⟨6705797, by rfl⟩ : syracuseStep 35764253 = 13411595) B13411595
theorem B1357951 : Blo 1356997 1357951 := bstep (se 1 (by rfl) ⟨1018463, by rfl⟩ : syracuseStep 1357951 = 2036927) B2036927
theorem B4184201 : Blo 1356997 4184201 := bstep (se 2 (by rfl) ⟨1569075, by rfl⟩ : syracuseStep 4184201 = 3138151) B3138151
theorem B1358047 : Blo 1356997 1358047 := bstep (se 1 (by rfl) ⟨1018535, by rfl⟩ : syracuseStep 1358047 = 2037071) B2037071
theorem B2578655 : Blo 1356997 2578655 := bstep (se 1 (by rfl) ⟨1933991, by rfl⟩ : syracuseStep 2578655 = 3867983) B3867983
theorem B1358107 : Blo 1356997 1358107 := bstep (se 1 (by rfl) ⟨1018580, by rfl⟩ : syracuseStep 1358107 = 2037161) B2037161
theorem B62740793 : Blo 1356997 62740793 := bstep (se 2 (by rfl) ⟨23527797, by rfl⟩ : syracuseStep 62740793 = 47055595) B47055595
theorem B1358143 : Blo 1356997 1358143 := bstep (se 1 (by rfl) ⟨1018607, by rfl⟩ : syracuseStep 1358143 = 2037215) B2037215
theorem B39164249 : Blo 1356997 39164249 := bstep (se 2 (by rfl) ⟨14686593, by rfl⟩ : syracuseStep 39164249 = 29373187) B29373187
theorem B1358207 : Blo 1356997 1358207 := bstep (se 1 (by rfl) ⟨1018655, by rfl⟩ : syracuseStep 1358207 = 2037311) B2037311
theorem B11156023 : Blo 1356997 11156023 := bstep (se 1 (by rfl) ⟨8367017, by rfl⟩ : syracuseStep 11156023 = 16734035) B16734035
theorem B3054473 : Blo 1356997 3054473 := bstep (se 2 (by rfl) ⟨1145427, by rfl⟩ : syracuseStep 3054473 = 2290855) B2290855
theorem B15473753 : Blo 1356997 15473753 := bstep (se 2 (by rfl) ⟨5802657, by rfl⟩ : syracuseStep 15473753 = 11605315) B11605315
theorem B7732367 : Blo 1356997 7732367 := bstep (se 1 (by rfl) ⟨5799275, by rfl⟩ : syracuseStep 7732367 = 11598551) B11598551
theorem B22314167 : Blo 1356997 22314167 := bstep (se 1 (by rfl) ⟨16735625, by rfl⟩ : syracuseStep 22314167 = 33471251) B33471251
theorem B3054779 : Blo 1356997 3054779 := bstep (se 1 (by rfl) ⟨2291084, by rfl⟩ : syracuseStep 3054779 = 4582169) B4582169
theorem B3055031 : Blo 1356997 3055031 := bstep (se 1 (by rfl) ⟨2291273, by rfl⟩ : syracuseStep 3055031 = 4582547) B4582547
theorem B35274329 : Blo 1356997 35274329 := bstep (se 2 (by rfl) ⟨13227873, by rfl⟩ : syracuseStep 35274329 = 26455747) B26455747
theorem B2899775 : Blo 1356997 2899775 := bstep (se 1 (by rfl) ⟨2174831, by rfl⟩ : syracuseStep 2899775 = 4349663) B4349663
theorem B3055679 : Blo 1356997 3055679 := bstep (se 1 (by rfl) ⟨2291759, by rfl⟩ : syracuseStep 3055679 = 4583519) B4583519
theorem B5955767 : Blo 1356997 5955767 := bstep (se 1 (by rfl) ⟨4466825, by rfl⟩ : syracuseStep 5955767 = 8933651) B8933651
theorem B3260729 : Blo 1356997 3260729 := bstep (se 2 (by rfl) ⟨1222773, by rfl⟩ : syracuseStep 3260729 = 2445547) B2445547
theorem B11157869 : Blo 1356997 11157869 := bstep (se 3 (by rfl) ⟨2092100, by rfl⟩ : syracuseStep 11157869 = 4184201) B4184201
theorem B7840127 : Blo 1356997 7840127 := bstep (se 1 (by rfl) ⟨5880095, by rfl⟩ : syracuseStep 7840127 = 11760191) B11760191
theorem B3097919 : Blo 1356997 3097919 := bstep (se 1 (by rfl) ⟨2323439, by rfl⟩ : syracuseStep 3097919 = 4646879) B4646879
theorem B3016443415 : Blo 1356997 3016443415 := bstep (se 1 (by rfl) ⟨2262332561, by rfl⟩ : syracuseStep 3016443415 = 4524665123) B4524665123
theorem B26109499 : Blo 1356997 26109499 := bstep (se 1 (by rfl) ⟨19582124, by rfl⟩ : syracuseStep 26109499 = 39164249) B39164249
theorem B11593529 : Blo 1356997 11593529 := bstep (se 2 (by rfl) ⟨4347573, by rfl⟩ : syracuseStep 11593529 = 8695147) B8695147
theorem B7735283 : Blo 1356997 7735283 := bstep (se 1 (by rfl) ⟨5801462, by rfl⟩ : syracuseStep 7735283 = 11602925) B11602925
theorem B10315835 : Blo 1356997 10315835 := bstep (se 1 (by rfl) ⟨7736876, by rfl⟩ : syracuseStep 10315835 = 15473753) B15473753
theorem B5154911 : Blo 1356997 5154911 := bstep (se 1 (by rfl) ⟨3866183, by rfl⟩ : syracuseStep 5154911 = 7732367) B7732367
theorem B3262727 : Blo 1356997 3262727 := bstep (se 1 (by rfl) ⟨2447045, by rfl⟩ : syracuseStep 3262727 = 4894091) B4894091
theorem B94095917 : Blo 1356997 94095917 := bstep (se 3 (by rfl) ⟨17642984, by rfl⟩ : syracuseStep 94095917 = 35285969) B35285969
theorem B11594927 : Blo 1356997 11594927 := bstep (se 1 (by rfl) ⟨8696195, by rfl⟩ : syracuseStep 11594927 = 17392391) B17392391
theorem B6876413 : Blo 1356997 6876413 := bstep (se 3 (by rfl) ⟨1289327, by rfl⟩ : syracuseStep 6876413 = 2578655) B2578655
theorem B1527295 : Blo 1356997 1527295 := bstep (se 1 (by rfl) ⟨1145471, by rfl⟩ : syracuseStep 1527295 = 2290943) B2290943
theorem B23842835 : Blo 1356997 23842835 := bstep (se 1 (by rfl) ⟨17882126, by rfl⟩ : syracuseStep 23842835 = 35764253) B35764253
theorem B2036315 : Blo 1356997 2036315 := bstep (se 1 (by rfl) ⟨1527236, by rfl⟩ : syracuseStep 2036315 = 3054473) B3054473
theorem B3437225 : Blo 1356997 3437225 := bstep (se 2 (by rfl) ⟨1288959, by rfl⟩ : syracuseStep 3437225 = 2577919) B2577919
theorem B2036519 : Blo 1356997 2036519 := bstep (se 1 (by rfl) ⟨1527389, by rfl⟩ : syracuseStep 2036519 = 3054779) B3054779
theorem B7942979 : Blo 1356997 7942979 := bstep (se 1 (by rfl) ⟨5957234, by rfl⟩ : syracuseStep 7942979 = 11914469) B11914469
theorem B2036687 : Blo 1356997 2036687 := bstep (se 1 (by rfl) ⟨1527515, by rfl⟩ : syracuseStep 2036687 = 3055031) B3055031
theorem B7836709 : Blo 1356997 7836709 := bstep (se 4 (by rfl) ⟨734691, by rfl⟩ : syracuseStep 7836709 = 1469383) B1469383
theorem B26801207 : Blo 1356997 26801207 := bstep (se 1 (by rfl) ⟨20100905, by rfl⟩ : syracuseStep 26801207 = 40201811) B40201811
theorem B23516219 : Blo 1356997 23516219 := bstep (se 1 (by rfl) ⟨17637164, by rfl⟩ : syracuseStep 23516219 = 35274329) B35274329
theorem B2577835 : Blo 1356997 2577835 := bstep (se 1 (by rfl) ⟨1933376, by rfl⟩ : syracuseStep 2577835 = 3866753) B3866753
theorem B23516729 : Blo 1356997 23516729 := bstep (se 2 (by rfl) ⟨8818773, by rfl⟩ : syracuseStep 23516729 = 17637547) B17637547
theorem B1357415 : Blo 1356997 1357415 := bstep (se 1 (by rfl) ⟨1018061, by rfl⟩ : syracuseStep 1357415 = 2036123) B2036123
theorem B2037353 : Blo 1356997 2037353 := bstep (se 2 (by rfl) ⟨764007, by rfl⟩ : syracuseStep 2037353 = 1528015) B1528015
theorem B52901525 : Blo 1356997 52901525 := bstep (se 6 (by rfl) ⟨1239879, by rfl⟩ : syracuseStep 52901525 = 2479759) B2479759
theorem B1357695 : Blo 1356997 1357695 := bstep (se 1 (by rfl) ⟨1018271, by rfl⟩ : syracuseStep 1357695 = 2036543) B2036543
theorem B2291611 : Blo 1356997 2291611 := bstep (se 1 (by rfl) ⟨1718708, by rfl⟩ : syracuseStep 2291611 = 3437417) B3437417
theorem B3438571 : Blo 1356997 3438571 := bstep (se 1 (by rfl) ⟨2578928, by rfl⟩ : syracuseStep 3438571 = 5157857) B5157857
theorem B33036275 : Blo 1356997 33036275 := bstep (se 1 (by rfl) ⟨24777206, by rfl⟩ : syracuseStep 33036275 = 49554413) B49554413
theorem B14874697 : Blo 1356997 14874697 := bstep (se 2 (by rfl) ⟨5578011, by rfl⟩ : syracuseStep 14874697 = 11156023) B11156023
theorem B6871229 : Blo 1356997 6871229 := bstep (se 3 (by rfl) ⟨1288355, by rfl⟩ : syracuseStep 6871229 = 2576711) B2576711
theorem B1358075 : Blo 1356997 1358075 := bstep (se 1 (by rfl) ⟨1018556, by rfl⟩ : syracuseStep 1358075 = 2037113) B2037113
theorem B3053843 : Blo 1356997 3053843 := bstep (se 1 (by rfl) ⟨2290382, by rfl⟩ : syracuseStep 3053843 = 4580765) B4580765
theorem B3053951 : Blo 1356997 3053951 := bstep (se 1 (by rfl) ⟨2290463, by rfl⟩ : syracuseStep 3053951 = 4580927) B4580927
theorem B3668471 : Blo 1356997 3668471 := bstep (se 1 (by rfl) ⟨2751353, by rfl⟩ : syracuseStep 3668471 = 5502707) B5502707
theorem B1358439 : Blo 1356997 1358439 := bstep (se 1 (by rfl) ⟨1018829, by rfl⟩ : syracuseStep 1358439 = 2037659) B2037659
theorem B41827195 : Blo 1356997 41827195 := bstep (se 1 (by rfl) ⟨31370396, by rfl⟩ : syracuseStep 41827195 = 62740793) B62740793
theorem B6872363 : Blo 1356997 6872363 := bstep (se 1 (by rfl) ⟨5154272, by rfl⟩ : syracuseStep 6872363 = 10308545) B10308545
theorem B14876111 : Blo 1356997 14876111 := bstep (se 1 (by rfl) ⟨11157083, by rfl⟩ : syracuseStep 14876111 = 22314167) B22314167
theorem B5152481 : Blo 1356997 5152481 := bstep (se 2 (by rfl) ⟨1932180, by rfl⟩ : syracuseStep 5152481 = 3864361) B3864361
theorem B1933183 : Blo 1356997 1933183 := bstep (se 1 (by rfl) ⟨1449887, by rfl⟩ : syracuseStep 1933183 = 2899775) B2899775
theorem B3055571 : Blo 1356997 3055571 := bstep (se 1 (by rfl) ⟨2291678, by rfl⟩ : syracuseStep 3055571 = 4583357) B4583357
theorem B5226751 : Blo 1356997 5226751 := bstep (se 1 (by rfl) ⟨3920063, by rfl⟩ : syracuseStep 5226751 = 7840127) B7840127
theorem B79331717 : Blo 1356997 79331717 := bstep (se 4 (by rfl) ⟨7437348, by rfl⟩ : syracuseStep 79331717 = 14874697) B14874697
theorem B8700605 : Blo 1356997 8700605 := bstep (se 3 (by rfl) ⟨1631363, by rfl⟩ : syracuseStep 8700605 = 3262727) B3262727
theorem B17867471 : Blo 1356997 17867471 := bstep (se 1 (by rfl) ⟨13400603, by rfl⟩ : syracuseStep 17867471 = 26801207) B26801207
theorem B2065279 : Blo 1356997 2065279 := bstep (se 1 (by rfl) ⟨1548959, by rfl⟩ : syracuseStep 2065279 = 3097919) B3097919
theorem B29754317 : Blo 1356997 29754317 := bstep (se 3 (by rfl) ⟨5578934, by rfl⟩ : syracuseStep 29754317 = 11157869) B11157869
theorem B35267683 : Blo 1356997 35267683 := bstep (se 1 (by rfl) ⟨26450762, by rfl⟩ : syracuseStep 35267683 = 52901525) B52901525
theorem B4580819 : Blo 1356997 4580819 := bstep (se 1 (by rfl) ⟨3435614, by rfl⟩ : syracuseStep 4580819 = 6871229) B6871229
theorem B4581575 : Blo 1356997 4581575 := bstep (se 1 (by rfl) ⟨3436181, by rfl⟩ : syracuseStep 4581575 = 6872363) B6872363
theorem B3434987 : Blo 1356997 3434987 := bstep (se 1 (by rfl) ⟨2576240, by rfl⟩ : syracuseStep 3434987 = 5152481) B5152481
theorem B15895223 : Blo 1356997 15895223 := bstep (se 1 (by rfl) ⟨11921417, by rfl⟩ : syracuseStep 15895223 = 23842835) B23842835
theorem B2173819 : Blo 1356997 2173819 := bstep (se 1 (by rfl) ⟨1630364, by rfl⟩ : syracuseStep 2173819 = 3260729) B3260729
theorem B7729019 : Blo 1356997 7729019 := bstep (se 1 (by rfl) ⟨5796764, by rfl⟩ : syracuseStep 7729019 = 11593529) B11593529
theorem B5156855 : Blo 1356997 5156855 := bstep (se 1 (by rfl) ⟨3867641, by rfl⟩ : syracuseStep 5156855 = 7735283) B7735283
theorem B6877223 : Blo 1356997 6877223 := bstep (se 1 (by rfl) ⟨5157917, by rfl⟩ : syracuseStep 6877223 = 10315835) B10315835
theorem B10448945 : Blo 1356997 10448945 := bstep (se 2 (by rfl) ⟨3918354, by rfl⟩ : syracuseStep 10448945 = 7836709) B7836709
theorem B3436607 : Blo 1356997 3436607 := bstep (se 1 (by rfl) ⟨2577455, by rfl⟩ : syracuseStep 3436607 = 5154911) B5154911
theorem B2035895 : Blo 1356997 2035895 := bstep (se 1 (by rfl) ⟨1526921, by rfl⟩ : syracuseStep 2035895 = 3053843) B3053843
theorem B2035967 : Blo 1356997 2035967 := bstep (se 1 (by rfl) ⟨1526975, by rfl⟩ : syracuseStep 2035967 = 3053951) B3053951
theorem B2445647 : Blo 1356997 2445647 := bstep (se 1 (by rfl) ⟨1834235, by rfl⟩ : syracuseStep 2445647 = 3668471) B3668471
theorem B62730611 : Blo 1356997 62730611 := bstep (se 1 (by rfl) ⟨47047958, by rfl⟩ : syracuseStep 62730611 = 94095917) B94095917
theorem B3437113 : Blo 1356997 3437113 := bstep (se 2 (by rfl) ⟨1288917, by rfl⟩ : syracuseStep 3437113 = 2577835) B2577835
theorem B2036393 : Blo 1356997 2036393 := bstep (se 2 (by rfl) ⟨763647, by rfl⟩ : syracuseStep 2036393 = 1527295) B1527295
theorem B4021924553 : Blo 1356997 4021924553 := bstep (se 2 (by rfl) ⟨1508221707, by rfl⟩ : syracuseStep 4021924553 = 3016443415) B3016443415
theorem B34812665 : Blo 1356997 34812665 := bstep (se 2 (by rfl) ⟨13054749, by rfl⟩ : syracuseStep 34812665 = 26109499) B26109499
theorem B7729951 : Blo 1356997 7729951 := bstep (se 1 (by rfl) ⟨5797463, by rfl⟩ : syracuseStep 7729951 = 11594927) B11594927
theorem B4584275 : Blo 1356997 4584275 := bstep (se 1 (by rfl) ⟨3438206, by rfl⟩ : syracuseStep 4584275 = 6876413) B6876413
theorem B21181277 : Blo 1356997 21181277 := bstep (se 3 (by rfl) ⟨3971489, by rfl⟩ : syracuseStep 21181277 = 7942979) B7942979
theorem B9917407 : Blo 1356997 9917407 := bstep (se 1 (by rfl) ⟨7438055, by rfl⟩ : syracuseStep 9917407 = 14876111) B14876111
theorem B2577577 : Blo 1356997 2577577 := bstep (se 2 (by rfl) ⟨966591, by rfl⟩ : syracuseStep 2577577 = 1933183) B1933183
theorem B2037047 : Blo 1356997 2037047 := bstep (se 1 (by rfl) ⟨1527785, by rfl⟩ : syracuseStep 2037047 = 3055571) B3055571
theorem B4584761 : Blo 1356997 4584761 := bstep (se 2 (by rfl) ⟨1719285, by rfl⟩ : syracuseStep 4584761 = 3438571) B3438571
theorem B2037119 : Blo 1356997 2037119 := bstep (se 1 (by rfl) ⟨1527839, by rfl⟩ : syracuseStep 2037119 = 3055679) B3055679
theorem B3970511 : Blo 1356997 3970511 := bstep (se 1 (by rfl) ⟨2977883, by rfl⟩ : syracuseStep 3970511 = 5955767) B5955767
theorem B1357543 : Blo 1356997 1357543 := bstep (se 1 (by rfl) ⟨1018157, by rfl⟩ : syracuseStep 1357543 = 2036315) B2036315
theorem B2291483 : Blo 1356997 2291483 := bstep (se 1 (by rfl) ⟨1718612, by rfl⟩ : syracuseStep 2291483 = 3437225) B3437225
theorem B1357679 : Blo 1356997 1357679 := bstep (se 1 (by rfl) ⟨1018259, by rfl⟩ : syracuseStep 1357679 = 2036519) B2036519
theorem B1357791 : Blo 1356997 1357791 := bstep (se 1 (by rfl) ⟨1018343, by rfl⟩ : syracuseStep 1357791 = 2036687) B2036687
theorem B15677479 : Blo 1356997 15677479 := bstep (se 1 (by rfl) ⟨11758109, by rfl⟩ : syracuseStep 15677479 = 23516219) B23516219
theorem B15677819 : Blo 1356997 15677819 := bstep (se 1 (by rfl) ⟨11758364, by rfl⟩ : syracuseStep 15677819 = 23516729) B23516729
theorem B1358235 : Blo 1356997 1358235 := bstep (se 1 (by rfl) ⟨1018676, by rfl⟩ : syracuseStep 1358235 = 2037353) B2037353
theorem B55769593 : Blo 1356997 55769593 := bstep (se 2 (by rfl) ⟨20913597, by rfl⟩ : syracuseStep 55769593 = 41827195) B41827195
theorem B3055481 : Blo 1356997 3055481 := bstep (se 2 (by rfl) ⟨1145805, by rfl⟩ : syracuseStep 3055481 = 2291611) B2291611
theorem B88096733 : Blo 1356997 88096733 := bstep (se 3 (by rfl) ⟨16518137, by rfl⟩ : syracuseStep 88096733 = 33036275) B33036275
theorem B41820407 : Blo 1356997 41820407 := bstep (se 1 (by rfl) ⟨31365305, by rfl⟩ : syracuseStep 41820407 = 62730611) B62730611
theorem B52887811 : Blo 1356997 52887811 := bstep (se 1 (by rfl) ⟨39665858, by rfl⟩ : syracuseStep 52887811 = 79331717) B79331717
theorem B5800403 : Blo 1356997 5800403 := bstep (se 1 (by rfl) ⟨4350302, by rfl⟩ : syracuseStep 5800403 = 8700605) B8700605
theorem B2681283035 : Blo 1356997 2681283035 := bstep (se 1 (by rfl) ⟨2010962276, by rfl⟩ : syracuseStep 2681283035 = 4021924553) B4021924553
theorem B23208443 : Blo 1356997 23208443 := bstep (se 1 (by rfl) ⟨17406332, by rfl⟩ : syracuseStep 23208443 = 34812665) B34812665
theorem B3056183 : Blo 1356997 3056183 := bstep (se 1 (by rfl) ⟨2292137, by rfl⟩ : syracuseStep 3056183 = 4584275) B4584275
theorem B74359457 : Blo 1356997 74359457 := bstep (se 2 (by rfl) ⟨27884796, by rfl⟩ : syracuseStep 74359457 = 55769593) B55769593
theorem B3056507 : Blo 1356997 3056507 := bstep (se 1 (by rfl) ⟨2292380, by rfl⟩ : syracuseStep 3056507 = 4584761) B4584761
theorem B6521725 : Blo 1356997 6521725 := bstep (se 3 (by rfl) ⟨1222823, by rfl⟩ : syracuseStep 6521725 = 2445647) B2445647
theorem B2647007 : Blo 1356997 2647007 := bstep (se 1 (by rfl) ⟨1985255, by rfl⟩ : syracuseStep 2647007 = 3970511) B3970511
theorem B10306601 : Blo 1356997 10306601 := bstep (se 2 (by rfl) ⟨3864975, by rfl⟩ : syracuseStep 10306601 = 7729951) B7729951
theorem B2753705 : Blo 1356997 2753705 := bstep (se 2 (by rfl) ⟨1032639, by rfl⟩ : syracuseStep 2753705 = 2065279) B2065279
theorem B47023577 : Blo 1356997 47023577 := bstep (se 2 (by rfl) ⟨17633841, by rfl⟩ : syracuseStep 47023577 = 35267683) B35267683
theorem B58731155 : Blo 1356997 58731155 := bstep (se 1 (by rfl) ⟨44048366, by rfl⟩ : syracuseStep 58731155 = 88096733) B88096733
theorem B6965963 : Blo 1356997 6965963 := bstep (se 1 (by rfl) ⟨5224472, by rfl⟩ : syracuseStep 6965963 = 10448945) B10448945
theorem B19836211 : Blo 1356997 19836211 := bstep (se 1 (by rfl) ⟨14877158, by rfl⟩ : syracuseStep 19836211 = 29754317) B29754317
theorem B4582817 : Blo 1356997 4582817 := bstep (se 2 (by rfl) ⟨1718556, by rfl⟩ : syracuseStep 4582817 = 3437113) B3437113
theorem B1527655 : Blo 1356997 1527655 := bstep (se 1 (by rfl) ⟨1145741, by rfl⟩ : syracuseStep 1527655 = 2291483) B2291483
theorem B3436769 : Blo 1356997 3436769 := bstep (se 2 (by rfl) ⟨1288788, by rfl⟩ : syracuseStep 3436769 = 2577577) B2577577
theorem B2289991 : Blo 1356997 2289991 := bstep (se 1 (by rfl) ⟨1717493, by rfl⟩ : syracuseStep 2289991 = 3434987) B3434987
theorem B10596815 : Blo 1356997 10596815 := bstep (se 1 (by rfl) ⟨7947611, by rfl⟩ : syracuseStep 10596815 = 15895223) B15895223
theorem B52892837 : Blo 1356997 52892837 := bstep (se 4 (by rfl) ⟨4958703, by rfl⟩ : syracuseStep 52892837 = 9917407) B9917407
theorem B2036987 : Blo 1356997 2036987 := bstep (se 1 (by rfl) ⟨1527740, by rfl⟩ : syracuseStep 2036987 = 3055481) B3055481
theorem B3437903 : Blo 1356997 3437903 := bstep (se 1 (by rfl) ⟨2578427, by rfl⟩ : syracuseStep 3437903 = 5156855) B5156855
theorem B4584815 : Blo 1356997 4584815 := bstep (se 1 (by rfl) ⟨3438611, by rfl⟩ : syracuseStep 4584815 = 6877223) B6877223
theorem B2291071 : Blo 1356997 2291071 := bstep (se 1 (by rfl) ⟨1718303, by rfl⟩ : syracuseStep 2291071 = 3436607) B3436607
theorem B20903305 : Blo 1356997 20903305 := bstep (se 2 (by rfl) ⟨7838739, by rfl⟩ : syracuseStep 20903305 = 15677479) B15677479
theorem B1357263 : Blo 1356997 1357263 := bstep (se 1 (by rfl) ⟨1017947, by rfl⟩ : syracuseStep 1357263 = 2035895) B2035895
theorem B1357311 : Blo 1356997 1357311 := bstep (se 1 (by rfl) ⟨1017983, by rfl⟩ : syracuseStep 1357311 = 2035967) B2035967
theorem B6969001 : Blo 1356997 6969001 := bstep (se 2 (by rfl) ⟨2613375, by rfl⟩ : syracuseStep 6969001 = 5226751) B5226751
theorem B1357595 : Blo 1356997 1357595 := bstep (se 1 (by rfl) ⟨1018196, by rfl⟩ : syracuseStep 1357595 = 2036393) B2036393
theorem B14120851 : Blo 1356997 14120851 := bstep (se 1 (by rfl) ⟨10590638, by rfl⟩ : syracuseStep 14120851 = 21181277) B21181277
theorem B1358031 : Blo 1356997 1358031 := bstep (se 1 (by rfl) ⟨1018523, by rfl⟩ : syracuseStep 1358031 = 2037047) B2037047
theorem B1358079 : Blo 1356997 1358079 := bstep (se 1 (by rfl) ⟨1018559, by rfl⟩ : syracuseStep 1358079 = 2037119) B2037119
theorem B3053879 : Blo 1356997 3053879 := bstep (se 1 (by rfl) ⟨2290409, by rfl⟩ : syracuseStep 3053879 = 4580819) B4580819
theorem B2898425 : Blo 1356997 2898425 := bstep (se 2 (by rfl) ⟨1086909, by rfl⟩ : syracuseStep 2898425 = 2173819) B2173819
theorem B3054383 : Blo 1356997 3054383 := bstep (se 1 (by rfl) ⟨2290787, by rfl⟩ : syracuseStep 3054383 = 4581575) B4581575
theorem B10451879 : Blo 1356997 10451879 := bstep (se 1 (by rfl) ⟨7838909, by rfl⟩ : syracuseStep 10451879 = 15677819) B15677819
theorem B190586357 : Blo 1356997 190586357 := bstep (se 5 (by rfl) ⟨8933735, by rfl⟩ : syracuseStep 190586357 = 17867471) B17867471
theorem B5152679 : Blo 1356997 5152679 := bstep (se 1 (by rfl) ⟨3864509, by rfl⟩ : syracuseStep 5152679 = 7729019) B7729019
theorem B3866935 : Blo 1356997 3866935 := bstep (se 1 (by rfl) ⟨2900201, by rfl⟩ : syracuseStep 3866935 = 5800403) B5800403
theorem B70517081 : Blo 1356997 70517081 := bstep (se 2 (by rfl) ⟨26443905, by rfl⟩ : syracuseStep 70517081 = 52887811) B52887811
theorem B1835803 : Blo 1356997 1835803 := bstep (se 1 (by rfl) ⟨1376852, by rfl⟩ : syracuseStep 1835803 = 2753705) B2753705
theorem B3056543 : Blo 1356997 3056543 := bstep (se 1 (by rfl) ⟨2292407, by rfl⟩ : syracuseStep 3056543 = 4584815) B4584815
theorem B27871073 : Blo 1356997 27871073 := bstep (se 2 (by rfl) ⟨10451652, by rfl⟩ : syracuseStep 27871073 = 20903305) B20903305
theorem B9292001 : Blo 1356997 9292001 := bstep (se 2 (by rfl) ⟨3484500, by rfl⟩ : syracuseStep 9292001 = 6969001) B6969001
theorem B18827801 : Blo 1356997 18827801 := bstep (se 2 (by rfl) ⟨7060425, by rfl⟩ : syracuseStep 18827801 = 14120851) B14120851
theorem B3435119 : Blo 1356997 3435119 := bstep (se 1 (by rfl) ⟨2576339, by rfl⟩ : syracuseStep 3435119 = 5152679) B5152679
theorem B27880271 : Blo 1356997 27880271 := bstep (se 1 (by rfl) ⟨20910203, by rfl⟩ : syracuseStep 27880271 = 41820407) B41820407
theorem B7064543 : Blo 1356997 7064543 := bstep (se 1 (by rfl) ⟨5298407, by rfl⟩ : syracuseStep 7064543 = 10596815) B10596815
theorem B1787522023 : Blo 1356997 1787522023 := bstep (se 1 (by rfl) ⟨1340641517, by rfl⟩ : syracuseStep 1787522023 = 2681283035) B2681283035
theorem B49572971 : Blo 1356997 49572971 := bstep (se 1 (by rfl) ⟨37179728, by rfl⟩ : syracuseStep 49572971 = 74359457) B74359457
theorem B1764671 : Blo 1356997 1764671 := bstep (se 1 (by rfl) ⟨1323503, by rfl⟩ : syracuseStep 1764671 = 2647007) B2647007
theorem B35261891 : Blo 1356997 35261891 := bstep (se 1 (by rfl) ⟨26446418, by rfl⟩ : syracuseStep 35261891 = 52892837) B52892837
theorem B8695633 : Blo 1356997 8695633 := bstep (se 2 (by rfl) ⟨3260862, by rfl⟩ : syracuseStep 8695633 = 6521725) B6521725
theorem B2035919 : Blo 1356997 2035919 := bstep (se 1 (by rfl) ⟨1526939, by rfl⟩ : syracuseStep 2035919 = 3053879) B3053879
theorem B26448281 : Blo 1356997 26448281 := bstep (se 2 (by rfl) ⟨9918105, by rfl⟩ : syracuseStep 26448281 = 19836211) B19836211
theorem B39154103 : Blo 1356997 39154103 := bstep (se 1 (by rfl) ⟨29365577, by rfl⟩ : syracuseStep 39154103 = 58731155) B58731155
theorem B2036255 : Blo 1356997 2036255 := bstep (se 1 (by rfl) ⟨1527191, by rfl⟩ : syracuseStep 2036255 = 3054383) B3054383
theorem B6967919 : Blo 1356997 6967919 := bstep (se 1 (by rfl) ⟨5225939, by rfl⟩ : syracuseStep 6967919 = 10451879) B10451879
theorem B2036873 : Blo 1356997 2036873 := bstep (se 2 (by rfl) ⟨763827, by rfl⟩ : syracuseStep 2036873 = 1527655) B1527655
theorem B2291179 : Blo 1356997 2291179 := bstep (se 1 (by rfl) ⟨1718384, by rfl⟩ : syracuseStep 2291179 = 3436769) B3436769
theorem B15472295 : Blo 1356997 15472295 := bstep (se 1 (by rfl) ⟨11604221, by rfl⟩ : syracuseStep 15472295 = 23208443) B23208443
theorem B2037455 : Blo 1356997 2037455 := bstep (se 1 (by rfl) ⟨1528091, by rfl⟩ : syracuseStep 2037455 = 3056183) B3056183
theorem B3053321 : Blo 1356997 3053321 := bstep (se 2 (by rfl) ⟨1144995, by rfl⟩ : syracuseStep 3053321 = 2289991) B2289991
theorem B2037671 : Blo 1356997 2037671 := bstep (se 1 (by rfl) ⟨1528253, by rfl⟩ : syracuseStep 2037671 = 3056507) B3056507
theorem B6871067 : Blo 1356997 6871067 := bstep (se 1 (by rfl) ⟨5153300, by rfl⟩ : syracuseStep 6871067 = 10306601) B10306601
theorem B1357991 : Blo 1356997 1357991 := bstep (se 1 (by rfl) ⟨1018493, by rfl⟩ : syracuseStep 1357991 = 2036987) B2036987
theorem B2291935 : Blo 1356997 2291935 := bstep (se 1 (by rfl) ⟨1718951, by rfl⟩ : syracuseStep 2291935 = 3437903) B3437903
theorem B31349051 : Blo 1356997 31349051 := bstep (se 1 (by rfl) ⟨23511788, by rfl⟩ : syracuseStep 31349051 = 47023577) B47023577
theorem B1932283 : Blo 1356997 1932283 := bstep (se 1 (by rfl) ⟨1449212, by rfl⟩ : syracuseStep 1932283 = 2898425) B2898425
theorem B4643975 : Blo 1356997 4643975 := bstep (se 1 (by rfl) ⟨3482981, by rfl⟩ : syracuseStep 4643975 = 6965963) B6965963
theorem B3054761 : Blo 1356997 3054761 := bstep (se 2 (by rfl) ⟨1145535, by rfl⟩ : syracuseStep 3054761 = 2291071) B2291071
theorem B3055211 : Blo 1356997 3055211 := bstep (se 1 (by rfl) ⟨2291408, by rfl⟩ : syracuseStep 3055211 = 4582817) B4582817
theorem B127057571 : Blo 1356997 127057571 := bstep (se 1 (by rfl) ⟨95293178, by rfl⟩ : syracuseStep 127057571 = 190586357) B190586357
theorem B3055913 : Blo 1356997 3055913 := bstep (se 2 (by rfl) ⟨1145967, by rfl⟩ : syracuseStep 3055913 = 2291935) B2291935
theorem B4645279 : Blo 1356997 4645279 := bstep (se 1 (by rfl) ⟨3483959, by rfl⟩ : syracuseStep 4645279 = 6967919) B6967919
theorem B10314863 : Blo 1356997 10314863 := bstep (se 1 (by rfl) ⟨7736147, by rfl⟩ : syracuseStep 10314863 = 15472295) B15472295
theorem B18580715 : Blo 1356997 18580715 := bstep (se 1 (by rfl) ⟨13935536, by rfl⟩ : syracuseStep 18580715 = 27871073) B27871073
theorem B4580711 : Blo 1356997 4580711 := bstep (se 1 (by rfl) ⟨3435533, by rfl⟩ : syracuseStep 4580711 = 6871067) B6871067
theorem B9790949 : Blo 1356997 9790949 := bstep (se 4 (by rfl) ⟨917901, by rfl⟩ : syracuseStep 9790949 = 1835803) B1835803
theorem B20899367 : Blo 1356997 20899367 := bstep (se 1 (by rfl) ⟨15674525, by rfl⟩ : syracuseStep 20899367 = 31349051) B31349051
theorem B12551867 : Blo 1356997 12551867 := bstep (se 1 (by rfl) ⟨9413900, by rfl⟩ : syracuseStep 12551867 = 18827801) B18827801
theorem B33048647 : Blo 1356997 33048647 := bstep (se 1 (by rfl) ⟨24786485, by rfl⟩ : syracuseStep 33048647 = 49572971) B49572971
theorem B11594177 : Blo 1356997 11594177 := bstep (se 2 (by rfl) ⟨4347816, by rfl⟩ : syracuseStep 11594177 = 8695633) B8695633
theorem B9533450789 : Blo 1356997 9533450789 := bstep (se 4 (by rfl) ⟨893761011, by rfl⟩ : syracuseStep 9533450789 = 1787522023) B1787522023
theorem B17632187 : Blo 1356997 17632187 := bstep (se 1 (by rfl) ⟨13224140, by rfl⟩ : syracuseStep 17632187 = 26448281) B26448281
theorem B26102735 : Blo 1356997 26102735 := bstep (se 1 (by rfl) ⟨19577051, by rfl⟩ : syracuseStep 26102735 = 39154103) B39154103
theorem B5155913 : Blo 1356997 5155913 := bstep (se 2 (by rfl) ⟨1933467, by rfl⟩ : syracuseStep 5155913 = 3866935) B3866935
theorem B4705789 : Blo 1356997 4705789 := bstep (se 3 (by rfl) ⟨882335, by rfl⟩ : syracuseStep 4705789 = 1764671) B1764671
theorem B2035547 : Blo 1356997 2035547 := bstep (se 1 (by rfl) ⟨1526660, by rfl⟩ : syracuseStep 2035547 = 3053321) B3053321
theorem B2576377 : Blo 1356997 2576377 := bstep (se 2 (by rfl) ⟨966141, by rfl⟩ : syracuseStep 2576377 = 1932283) B1932283
theorem B2290079 : Blo 1356997 2290079 := bstep (se 1 (by rfl) ⟨1717559, by rfl⟩ : syracuseStep 2290079 = 3435119) B3435119
theorem B2036507 : Blo 1356997 2036507 := bstep (se 1 (by rfl) ⟨1527380, by rfl⟩ : syracuseStep 2036507 = 3054761) B3054761
theorem B23507927 : Blo 1356997 23507927 := bstep (se 1 (by rfl) ⟨17630945, by rfl⟩ : syracuseStep 23507927 = 35261891) B35261891
theorem B2036807 : Blo 1356997 2036807 := bstep (se 1 (by rfl) ⟨1527605, by rfl⟩ : syracuseStep 2036807 = 3055211) B3055211
theorem B18838781 : Blo 1356997 18838781 := bstep (se 3 (by rfl) ⟨3532271, by rfl⟩ : syracuseStep 18838781 = 7064543) B7064543
theorem B1357279 : Blo 1356997 1357279 := bstep (se 1 (by rfl) ⟨1017959, by rfl⟩ : syracuseStep 1357279 = 2035919) B2035919
theorem B47011387 : Blo 1356997 47011387 := bstep (se 1 (by rfl) ⟨35258540, by rfl⟩ : syracuseStep 47011387 = 70517081) B70517081
theorem B12383933 : Blo 1356997 12383933 := bstep (se 3 (by rfl) ⟨2321987, by rfl⟩ : syracuseStep 12383933 = 4643975) B4643975
theorem B1357503 : Blo 1356997 1357503 := bstep (se 1 (by rfl) ⟨1018127, by rfl⟩ : syracuseStep 1357503 = 2036255) B2036255
theorem B24778669 : Blo 1356997 24778669 := bstep (se 3 (by rfl) ⟨4646000, by rfl⟩ : syracuseStep 24778669 = 9292001) B9292001
theorem B2037695 : Blo 1356997 2037695 := bstep (se 1 (by rfl) ⟨1528271, by rfl⟩ : syracuseStep 2037695 = 3056543) B3056543
theorem B1357915 : Blo 1356997 1357915 := bstep (se 1 (by rfl) ⟨1018436, by rfl⟩ : syracuseStep 1357915 = 2036873) B2036873
theorem B1358303 : Blo 1356997 1358303 := bstep (se 1 (by rfl) ⟨1018727, by rfl⟩ : syracuseStep 1358303 = 2037455) B2037455
theorem B1358447 : Blo 1356997 1358447 := bstep (se 1 (by rfl) ⟨1018835, by rfl⟩ : syracuseStep 1358447 = 2037671) B2037671
theorem B18586847 : Blo 1356997 18586847 := bstep (se 1 (by rfl) ⟨13940135, by rfl⟩ : syracuseStep 18586847 = 27880271) B27880271
theorem B3054905 : Blo 1356997 3054905 := bstep (se 2 (by rfl) ⟨1145589, by rfl⟩ : syracuseStep 3054905 = 2291179) B2291179
theorem B84705047 : Blo 1356997 84705047 := bstep (se 1 (by rfl) ⟨63528785, by rfl⟩ : syracuseStep 84705047 = 127057571) B127057571
theorem B6193705 : Blo 1356997 6193705 := bstep (se 2 (by rfl) ⟨2322639, by rfl⟩ : syracuseStep 6193705 = 4645279) B4645279
theorem B15671951 : Blo 1356997 15671951 := bstep (se 1 (by rfl) ⟨11753963, by rfl⟩ : syracuseStep 15671951 = 23507927) B23507927
theorem B12387143 : Blo 1356997 12387143 := bstep (se 1 (by rfl) ⟨9290357, by rfl⟩ : syracuseStep 12387143 = 18580715) B18580715
theorem B12559187 : Blo 1356997 12559187 := bstep (se 1 (by rfl) ⟨9419390, by rfl⟩ : syracuseStep 12559187 = 18838781) B18838781
theorem B6355633859 : Blo 1356997 6355633859 := bstep (se 1 (by rfl) ⟨4766725394, by rfl⟩ : syracuseStep 6355633859 = 9533450789) B9533450789
theorem B33023821 : Blo 1356997 33023821 := bstep (se 3 (by rfl) ⟨6191966, by rfl⟩ : syracuseStep 33023821 = 12383933) B12383933
theorem B17401823 : Blo 1356997 17401823 := bstep (se 1 (by rfl) ⟨13051367, by rfl⟩ : syracuseStep 17401823 = 26102735) B26102735
theorem B56470031 : Blo 1356997 56470031 := bstep (se 1 (by rfl) ⟨42352523, by rfl⟩ : syracuseStep 56470031 = 84705047) B84705047
theorem B3435169 : Blo 1356997 3435169 := bstep (se 2 (by rfl) ⟨1288188, by rfl⟩ : syracuseStep 3435169 = 2576377) B2576377
theorem B1526719 : Blo 1356997 1526719 := bstep (se 1 (by rfl) ⟨1145039, by rfl⟩ : syracuseStep 1526719 = 2290079) B2290079
theorem B6876575 : Blo 1356997 6876575 := bstep (se 1 (by rfl) ⟨5157431, by rfl⟩ : syracuseStep 6876575 = 10314863) B10314863
theorem B8367911 : Blo 1356997 8367911 := bstep (se 1 (by rfl) ⟨6275933, by rfl⟩ : syracuseStep 8367911 = 12551867) B12551867
theorem B22032431 : Blo 1356997 22032431 := bstep (se 1 (by rfl) ⟨16524323, by rfl⟩ : syracuseStep 22032431 = 33048647) B33048647
theorem B7729451 : Blo 1356997 7729451 := bstep (se 1 (by rfl) ⟨5797088, by rfl⟩ : syracuseStep 7729451 = 11594177) B11594177
theorem B3437275 : Blo 1356997 3437275 := bstep (se 1 (by rfl) ⟨2577956, by rfl⟩ : syracuseStep 3437275 = 5155913) B5155913
theorem B62681849 : Blo 1356997 62681849 := bstep (se 2 (by rfl) ⟨23505693, by rfl⟩ : syracuseStep 62681849 = 47011387) B47011387
theorem B12391231 : Blo 1356997 12391231 := bstep (se 1 (by rfl) ⟨9293423, by rfl⟩ : syracuseStep 12391231 = 18586847) B18586847
theorem B2036603 : Blo 1356997 2036603 := bstep (se 1 (by rfl) ⟨1527452, by rfl⟩ : syracuseStep 2036603 = 3054905) B3054905
theorem B1357031 : Blo 1356997 1357031 := bstep (se 1 (by rfl) ⟨1017773, by rfl⟩ : syracuseStep 1357031 = 2035547) B2035547
theorem B2037275 : Blo 1356997 2037275 := bstep (se 1 (by rfl) ⟨1527956, by rfl⟩ : syracuseStep 2037275 = 3055913) B3055913
theorem B1357671 : Blo 1356997 1357671 := bstep (se 1 (by rfl) ⟨1018253, by rfl⟩ : syracuseStep 1357671 = 2036507) B2036507
theorem B1357871 : Blo 1356997 1357871 := bstep (se 1 (by rfl) ⟨1018403, by rfl⟩ : syracuseStep 1357871 = 2036807) B2036807
theorem B3053807 : Blo 1356997 3053807 := bstep (se 1 (by rfl) ⟨2290355, by rfl⟩ : syracuseStep 3053807 = 4580711) B4580711
theorem B6527299 : Blo 1356997 6527299 := bstep (se 1 (by rfl) ⟨4895474, by rfl⟩ : syracuseStep 6527299 = 9790949) B9790949
theorem B13932911 : Blo 1356997 13932911 := bstep (se 1 (by rfl) ⟨10449683, by rfl⟩ : syracuseStep 13932911 = 20899367) B20899367
theorem B1358463 : Blo 1356997 1358463 := bstep (se 1 (by rfl) ⟨1018847, by rfl⟩ : syracuseStep 1358463 = 2037695) B2037695
theorem B11754791 : Blo 1356997 11754791 := bstep (se 1 (by rfl) ⟨8816093, by rfl⟩ : syracuseStep 11754791 = 17632187) B17632187
theorem B6274385 : Blo 1356997 6274385 := bstep (se 2 (by rfl) ⟨2352894, by rfl⟩ : syracuseStep 6274385 = 4705789) B4705789
theorem B33038225 : Blo 1356997 33038225 := bstep (se 2 (by rfl) ⟨12389334, by rfl⟩ : syracuseStep 33038225 = 24778669) B24778669
theorem B14688287 : Blo 1356997 14688287 := bstep (se 1 (by rfl) ⟨11016215, by rfl⟩ : syracuseStep 14688287 = 22032431) B22032431
theorem B5152967 : Blo 1356997 5152967 := bstep (se 1 (by rfl) ⟨3864725, by rfl⟩ : syracuseStep 5152967 = 7729451) B7729451
theorem B41787899 : Blo 1356997 41787899 := bstep (se 1 (by rfl) ⟨31340924, by rfl⟩ : syracuseStep 41787899 = 62681849) B62681849
theorem B8258095 : Blo 1356997 8258095 := bstep (se 1 (by rfl) ⟨6193571, by rfl⟩ : syracuseStep 8258095 = 12387143) B12387143
theorem B8372791 : Blo 1356997 8372791 := bstep (se 1 (by rfl) ⟨6279593, by rfl⟩ : syracuseStep 8372791 = 12559187) B12559187
theorem B8258273 : Blo 1356997 8258273 := bstep (se 2 (by rfl) ⟨3096852, by rfl⟩ : syracuseStep 8258273 = 6193705) B6193705
theorem B4580225 : Blo 1356997 4580225 := bstep (se 2 (by rfl) ⟨1717584, by rfl⟩ : syracuseStep 4580225 = 3435169) B3435169
theorem B11601215 : Blo 1356997 11601215 := bstep (se 1 (by rfl) ⟨8700911, by rfl⟩ : syracuseStep 11601215 = 17401823) B17401823
theorem B8703065 : Blo 1356997 8703065 := bstep (se 2 (by rfl) ⟨3263649, by rfl⟩ : syracuseStep 8703065 = 6527299) B6527299
theorem B10447967 : Blo 1356997 10447967 := bstep (se 1 (by rfl) ⟨7835975, by rfl⟩ : syracuseStep 10447967 = 15671951) B15671951
theorem B4583033 : Blo 1356997 4583033 := bstep (se 2 (by rfl) ⟨1718637, by rfl⟩ : syracuseStep 4583033 = 3437275) B3437275
theorem B2035625 : Blo 1356997 2035625 := bstep (se 2 (by rfl) ⟨763359, by rfl⟩ : syracuseStep 2035625 = 1526719) B1526719
theorem B2035871 : Blo 1356997 2035871 := bstep (se 1 (by rfl) ⟨1526903, by rfl⟩ : syracuseStep 2035871 = 3053807) B3053807
theorem B37646687 : Blo 1356997 37646687 := bstep (se 1 (by rfl) ⟨28235015, by rfl⟩ : syracuseStep 37646687 = 56470031) B56470031
theorem B7836527 : Blo 1356997 7836527 := bstep (se 1 (by rfl) ⟨5877395, by rfl⟩ : syracuseStep 7836527 = 11754791) B11754791
theorem B4182923 : Blo 1356997 4182923 := bstep (se 1 (by rfl) ⟨3137192, by rfl⟩ : syracuseStep 4182923 = 6274385) B6274385
theorem B4584383 : Blo 1356997 4584383 := bstep (se 1 (by rfl) ⟨3438287, by rfl⟩ : syracuseStep 4584383 = 6876575) B6876575
theorem B22025483 : Blo 1356997 22025483 := bstep (se 1 (by rfl) ⟨16519112, by rfl⟩ : syracuseStep 22025483 = 33038225) B33038225
theorem B1357735 : Blo 1356997 1357735 := bstep (se 1 (by rfl) ⟨1018301, by rfl⟩ : syracuseStep 1357735 = 2036603) B2036603
theorem B1358183 : Blo 1356997 1358183 := bstep (se 1 (by rfl) ⟨1018637, by rfl⟩ : syracuseStep 1358183 = 2037275) B2037275
theorem B16521641 : Blo 1356997 16521641 := bstep (se 2 (by rfl) ⟨6195615, by rfl⟩ : syracuseStep 16521641 = 12391231) B12391231
theorem B4237089239 : Blo 1356997 4237089239 := bstep (se 1 (by rfl) ⟨3177816929, by rfl⟩ : syracuseStep 4237089239 = 6355633859) B6355633859
theorem B9288607 : Blo 1356997 9288607 := bstep (se 1 (by rfl) ⟨6966455, by rfl⟩ : syracuseStep 9288607 = 13932911) B13932911
theorem B44031761 : Blo 1356997 44031761 := bstep (se 2 (by rfl) ⟨16511910, by rfl⟩ : syracuseStep 44031761 = 33023821) B33023821
theorem B5578607 : Blo 1356997 5578607 := bstep (se 1 (by rfl) ⟨4183955, by rfl⟩ : syracuseStep 5578607 = 8367911) B8367911
theorem B44654885 : Blo 1356997 44654885 := bstep (se 4 (by rfl) ⟨4186395, by rfl⟩ : syracuseStep 44654885 = 8372791) B8372791
theorem B5505515 : Blo 1356997 5505515 := bstep (se 1 (by rfl) ⟨4129136, by rfl⟩ : syracuseStep 5505515 = 8258273) B8258273
theorem B3056255 : Blo 1356997 3056255 := bstep (se 1 (by rfl) ⟨2292191, by rfl⟩ : syracuseStep 3056255 = 4584383) B4584383
theorem B7734143 : Blo 1356997 7734143 := bstep (se 1 (by rfl) ⟨5800607, by rfl⟩ : syracuseStep 7734143 = 11601215) B11601215
theorem B2824726159 : Blo 1356997 2824726159 := bstep (se 1 (by rfl) ⟨2118544619, by rfl⟩ : syracuseStep 2824726159 = 4237089239) B4237089239
theorem B5802043 : Blo 1356997 5802043 := bstep (se 1 (by rfl) ⟨4351532, by rfl⟩ : syracuseStep 5802043 = 8703065) B8703065
theorem B6965311 : Blo 1356997 6965311 := bstep (se 1 (by rfl) ⟨5223983, by rfl⟩ : syracuseStep 6965311 = 10447967) B10447967
theorem B29354507 : Blo 1356997 29354507 := bstep (se 1 (by rfl) ⟨22015880, by rfl⟩ : syracuseStep 29354507 = 44031761) B44031761
theorem B9792191 : Blo 1356997 9792191 := bstep (se 1 (by rfl) ⟨7344143, by rfl⟩ : syracuseStep 9792191 = 14688287) B14688287
theorem B3435311 : Blo 1356997 3435311 := bstep (se 1 (by rfl) ⟨2576483, by rfl⟩ : syracuseStep 3435311 = 5152967) B5152967
theorem B44043173 : Blo 1356997 44043173 := bstep (se 4 (by rfl) ⟨4129047, by rfl⟩ : syracuseStep 44043173 = 8258095) B8258095
theorem B2788615 : Blo 1356997 2788615 := bstep (se 1 (by rfl) ⟨2091461, by rfl⟩ : syracuseStep 2788615 = 4182923) B4182923
theorem B14683655 : Blo 1356997 14683655 := bstep (se 1 (by rfl) ⟨11012741, by rfl⟩ : syracuseStep 14683655 = 22025483) B22025483
theorem B11014427 : Blo 1356997 11014427 := bstep (se 1 (by rfl) ⟨8260820, by rfl⟩ : syracuseStep 11014427 = 16521641) B16521641
theorem B1357083 : Blo 1356997 1357083 := bstep (se 1 (by rfl) ⟨1017812, by rfl⟩ : syracuseStep 1357083 = 2035625) B2035625
theorem B1357247 : Blo 1356997 1357247 := bstep (se 1 (by rfl) ⟨1017935, by rfl⟩ : syracuseStep 1357247 = 2035871) B2035871
theorem B27858599 : Blo 1356997 27858599 := bstep (se 1 (by rfl) ⟨20893949, by rfl⟩ : syracuseStep 27858599 = 41787899) B41787899
theorem B5224351 : Blo 1356997 5224351 := bstep (se 1 (by rfl) ⟨3918263, by rfl⟩ : syracuseStep 5224351 = 7836527) B7836527
theorem B3053483 : Blo 1356997 3053483 := bstep (se 1 (by rfl) ⟨2290112, by rfl⟩ : syracuseStep 3053483 = 4580225) B4580225
theorem B100391165 : Blo 1356997 100391165 := bstep (se 3 (by rfl) ⟨18823343, by rfl⟩ : syracuseStep 100391165 = 37646687) B37646687
theorem B12384809 : Blo 1356997 12384809 := bstep (se 2 (by rfl) ⟨4644303, by rfl⟩ : syracuseStep 12384809 = 9288607) B9288607
theorem B3055355 : Blo 1356997 3055355 := bstep (se 1 (by rfl) ⟨2291516, by rfl⟩ : syracuseStep 3055355 = 4583033) B4583033
theorem B3719071 : Blo 1356997 3719071 := bstep (se 1 (by rfl) ⟨2789303, by rfl⟩ : syracuseStep 3719071 = 5578607) B5578607
theorem B29769923 : Blo 1356997 29769923 := bstep (se 1 (by rfl) ⟨22327442, by rfl⟩ : syracuseStep 29769923 = 44654885) B44654885
theorem B3670343 : Blo 1356997 3670343 := bstep (se 1 (by rfl) ⟨2752757, by rfl⟩ : syracuseStep 3670343 = 5505515) B5505515
theorem B18572399 : Blo 1356997 18572399 := bstep (se 1 (by rfl) ⟨13929299, by rfl⟩ : syracuseStep 18572399 = 27858599) B27858599
theorem B29362115 : Blo 1356997 29362115 := bstep (se 1 (by rfl) ⟨22021586, by rfl⟩ : syracuseStep 29362115 = 44043173) B44043173
theorem B4958761 : Blo 1356997 4958761 := bstep (se 2 (by rfl) ⟨1859535, by rfl⟩ : syracuseStep 4958761 = 3719071) B3719071
theorem B6965801 : Blo 1356997 6965801 := bstep (se 2 (by rfl) ⟨2612175, by rfl⟩ : syracuseStep 6965801 = 5224351) B5224351
theorem B7736057 : Blo 1356997 7736057 := bstep (se 2 (by rfl) ⟨2901021, by rfl⟩ : syracuseStep 7736057 = 5802043) B5802043
theorem B5156095 : Blo 1356997 5156095 := bstep (se 1 (by rfl) ⟨3867071, by rfl⟩ : syracuseStep 5156095 = 7734143) B7734143
theorem B29371805 : Blo 1356997 29371805 := bstep (se 3 (by rfl) ⟨5507213, by rfl⟩ : syracuseStep 29371805 = 11014427) B11014427
theorem B2035655 : Blo 1356997 2035655 := bstep (se 1 (by rfl) ⟨1526741, by rfl⟩ : syracuseStep 2035655 = 3053483) B3053483
theorem B2290207 : Blo 1356997 2290207 := bstep (se 1 (by rfl) ⟨1717655, by rfl⟩ : syracuseStep 2290207 = 3435311) B3435311
theorem B3766301545 : Blo 1356997 3766301545 := bstep (se 2 (by rfl) ⟨1412363079, by rfl⟩ : syracuseStep 3766301545 = 2824726159) B2824726159
theorem B2036903 : Blo 1356997 2036903 := bstep (se 1 (by rfl) ⟨1527677, by rfl⟩ : syracuseStep 2036903 = 3055355) B3055355
theorem B9287081 : Blo 1356997 9287081 := bstep (se 2 (by rfl) ⟨3482655, by rfl⟩ : syracuseStep 9287081 = 6965311) B6965311
theorem B2037503 : Blo 1356997 2037503 := bstep (se 1 (by rfl) ⟨1528127, by rfl⟩ : syracuseStep 2037503 = 3056255) B3056255
theorem B66927443 : Blo 1356997 66927443 := bstep (se 1 (by rfl) ⟨50195582, by rfl⟩ : syracuseStep 66927443 = 100391165) B100391165
theorem B19569671 : Blo 1356997 19569671 := bstep (se 1 (by rfl) ⟨14677253, by rfl⟩ : syracuseStep 19569671 = 29354507) B29354507
theorem B3718153 : Blo 1356997 3718153 := bstep (se 2 (by rfl) ⟨1394307, by rfl⟩ : syracuseStep 3718153 = 2788615) B2788615
theorem B8256539 : Blo 1356997 8256539 := bstep (se 1 (by rfl) ⟨6192404, by rfl⟩ : syracuseStep 8256539 = 12384809) B12384809
theorem B6528127 : Blo 1356997 6528127 := bstep (se 1 (by rfl) ⟨4896095, by rfl⟩ : syracuseStep 6528127 = 9792191) B9792191
theorem B9789103 : Blo 1356997 9789103 := bstep (se 1 (by rfl) ⟨7341827, by rfl⟩ : syracuseStep 9789103 = 14683655) B14683655
theorem B6611681 : Blo 1356997 6611681 := bstep (se 2 (by rfl) ⟨2479380, by rfl⟩ : syracuseStep 6611681 = 4958761) B4958761
theorem B4957537 : Blo 1356997 4957537 := bstep (se 2 (by rfl) ⟨1859076, by rfl⟩ : syracuseStep 4957537 = 3718153) B3718153
theorem B6874793 : Blo 1356997 6874793 := bstep (se 2 (by rfl) ⟨2578047, by rfl⟩ : syracuseStep 6874793 = 5156095) B5156095
theorem B178473181 : Blo 1356997 178473181 := bstep (se 3 (by rfl) ⟨33463721, by rfl⟩ : syracuseStep 178473181 = 66927443) B66927443
theorem B13052137 : Blo 1356997 13052137 := bstep (se 2 (by rfl) ⟨4894551, by rfl⟩ : syracuseStep 13052137 = 9789103) B9789103
theorem B19581203 : Blo 1356997 19581203 := bstep (se 1 (by rfl) ⟨14685902, by rfl⟩ : syracuseStep 19581203 = 29371805) B29371805
theorem B12381599 : Blo 1356997 12381599 := bstep (se 1 (by rfl) ⟨9286199, by rfl⟩ : syracuseStep 12381599 = 18572399) B18572399
theorem B8704169 : Blo 1356997 8704169 := bstep (se 2 (by rfl) ⟨3264063, by rfl⟩ : syracuseStep 8704169 = 6528127) B6528127
theorem B5157371 : Blo 1356997 5157371 := bstep (se 1 (by rfl) ⟨3868028, by rfl⟩ : syracuseStep 5157371 = 7736057) B7736057
theorem B13046447 : Blo 1356997 13046447 := bstep (se 1 (by rfl) ⟨9784835, by rfl⟩ : syracuseStep 13046447 = 19569671) B19569671
theorem B1357103 : Blo 1356997 1357103 := bstep (se 1 (by rfl) ⟨1017827, by rfl⟩ : syracuseStep 1357103 = 2035655) B2035655
theorem B19846615 : Blo 1356997 19846615 := bstep (se 1 (by rfl) ⟨14884961, by rfl⟩ : syracuseStep 19846615 = 29769923) B29769923
theorem B2446895 : Blo 1356997 2446895 := bstep (se 1 (by rfl) ⟨1835171, by rfl⟩ : syracuseStep 2446895 = 3670343) B3670343
theorem B3053609 : Blo 1356997 3053609 := bstep (se 2 (by rfl) ⟨1145103, by rfl⟩ : syracuseStep 3053609 = 2290207) B2290207
theorem B1357935 : Blo 1356997 1357935 := bstep (se 1 (by rfl) ⟨1018451, by rfl⟩ : syracuseStep 1357935 = 2036903) B2036903
theorem B6191387 : Blo 1356997 6191387 := bstep (se 1 (by rfl) ⟨4643540, by rfl⟩ : syracuseStep 6191387 = 9287081) B9287081
theorem B5021735393 : Blo 1356997 5021735393 := bstep (se 2 (by rfl) ⟨1883150772, by rfl⟩ : syracuseStep 5021735393 = 3766301545) B3766301545
theorem B1358335 : Blo 1356997 1358335 := bstep (se 1 (by rfl) ⟨1018751, by rfl⟩ : syracuseStep 1358335 = 2037503) B2037503
theorem B4643867 : Blo 1356997 4643867 := bstep (se 1 (by rfl) ⟨3482900, by rfl⟩ : syracuseStep 4643867 = 6965801) B6965801
theorem B5504359 : Blo 1356997 5504359 := bstep (se 1 (by rfl) ⟨4128269, by rfl⟩ : syracuseStep 5504359 = 8256539) B8256539
theorem B78298973 : Blo 1356997 78298973 := bstep (se 3 (by rfl) ⟨14681057, by rfl⟩ : syracuseStep 78298973 = 29362115) B29362115
theorem B4407787 : Blo 1356997 4407787 := bstep (se 1 (by rfl) ⟨3305840, by rfl⟩ : syracuseStep 4407787 = 6611681) B6611681
theorem B1631263 : Blo 1356997 1631263 := bstep (se 1 (by rfl) ⟨1223447, by rfl⟩ : syracuseStep 1631263 = 2446895) B2446895
theorem B26462153 : Blo 1356997 26462153 := bstep (se 2 (by rfl) ⟨9923307, by rfl⟩ : syracuseStep 26462153 = 19846615) B19846615
theorem B5802779 : Blo 1356997 5802779 := bstep (se 1 (by rfl) ⟨4352084, by rfl⟩ : syracuseStep 5802779 = 8704169) B8704169
theorem B237964241 : Blo 1356997 237964241 := bstep (se 2 (by rfl) ⟨89236590, by rfl⟩ : syracuseStep 237964241 = 178473181) B178473181
theorem B17402849 : Blo 1356997 17402849 := bstep (se 2 (by rfl) ⟨6526068, by rfl⟩ : syracuseStep 17402849 = 13052137) B13052137
theorem B4583195 : Blo 1356997 4583195 := bstep (se 1 (by rfl) ⟨3437396, by rfl⟩ : syracuseStep 4583195 = 6874793) B6874793
theorem B2035739 : Blo 1356997 2035739 := bstep (se 1 (by rfl) ⟨1526804, by rfl⟩ : syracuseStep 2035739 = 3053609) B3053609
theorem B13054135 : Blo 1356997 13054135 := bstep (se 1 (by rfl) ⟨9790601, by rfl⟩ : syracuseStep 13054135 = 19581203) B19581203
theorem B8254399 : Blo 1356997 8254399 := bstep (se 1 (by rfl) ⟨6190799, by rfl⟩ : syracuseStep 8254399 = 12381599) B12381599
theorem B3438247 : Blo 1356997 3438247 := bstep (se 1 (by rfl) ⟨2578685, by rfl⟩ : syracuseStep 3438247 = 5157371) B5157371
theorem B8697631 : Blo 1356997 8697631 := bstep (se 1 (by rfl) ⟨6523223, by rfl⟩ : syracuseStep 8697631 = 13046447) B13046447
theorem B4127591 : Blo 1356997 4127591 := bstep (se 1 (by rfl) ⟨3095693, by rfl⟩ : syracuseStep 4127591 = 6191387) B6191387
theorem B3347823595 : Blo 1356997 3347823595 := bstep (se 1 (by rfl) ⟨2510867696, by rfl⟩ : syracuseStep 3347823595 = 5021735393) B5021735393
theorem B6610049 : Blo 1356997 6610049 := bstep (se 2 (by rfl) ⟨2478768, by rfl⟩ : syracuseStep 6610049 = 4957537) B4957537
theorem B7339145 : Blo 1356997 7339145 := bstep (se 2 (by rfl) ⟨2752179, by rfl⟩ : syracuseStep 7339145 = 5504359) B5504359
theorem B3095911 : Blo 1356997 3095911 := bstep (se 1 (by rfl) ⟨2321933, by rfl⟩ : syracuseStep 3095911 = 4643867) B4643867
theorem B52199315 : Blo 1356997 52199315 := bstep (se 1 (by rfl) ⟨39149486, by rfl⟩ : syracuseStep 52199315 = 78298973) B78298973
theorem B19571053 : Blo 1356997 19571053 := bstep (se 3 (by rfl) ⟨3669572, by rfl⟩ : syracuseStep 19571053 = 7339145) B7339145
theorem B4463764793 : Blo 1356997 4463764793 := bstep (se 2 (by rfl) ⟨1673911797, by rfl⟩ : syracuseStep 4463764793 = 3347823595) B3347823595
theorem B3868519 : Blo 1356997 3868519 := bstep (se 1 (by rfl) ⟨2901389, by rfl⟩ : syracuseStep 3868519 = 5802779) B5802779
theorem B11601899 : Blo 1356997 11601899 := bstep (se 1 (by rfl) ⟨8701424, by rfl⟩ : syracuseStep 11601899 = 17402849) B17402849
theorem B634571309 : Blo 1356997 634571309 := bstep (se 3 (by rfl) ⟨118982120, by rfl⟩ : syracuseStep 634571309 = 237964241) B237964241
theorem B5877049 : Blo 1356997 5877049 := bstep (se 2 (by rfl) ⟨2203893, by rfl⟩ : syracuseStep 5877049 = 4407787) B4407787
theorem B11005865 : Blo 1356997 11005865 := bstep (se 2 (by rfl) ⟨4127199, by rfl⟩ : syracuseStep 11005865 = 8254399) B8254399
theorem B2175017 : Blo 1356997 2175017 := bstep (se 2 (by rfl) ⟨815631, by rfl⟩ : syracuseStep 2175017 = 1631263) B1631263
theorem B4584329 : Blo 1356997 4584329 := bstep (se 2 (by rfl) ⟨1719123, by rfl⟩ : syracuseStep 4584329 = 3438247) B3438247
theorem B11596841 : Blo 1356997 11596841 := bstep (se 2 (by rfl) ⟨4348815, by rfl⟩ : syracuseStep 11596841 = 8697631) B8697631
theorem B1357159 : Blo 1356997 1357159 := bstep (se 1 (by rfl) ⟨1017869, by rfl⟩ : syracuseStep 1357159 = 2035739) B2035739
theorem B17405513 : Blo 1356997 17405513 := bstep (se 2 (by rfl) ⟨6527067, by rfl⟩ : syracuseStep 17405513 = 13054135) B13054135
theorem B4127881 : Blo 1356997 4127881 := bstep (se 2 (by rfl) ⟨1547955, by rfl⟩ : syracuseStep 4127881 = 3095911) B3095911
theorem B2751727 : Blo 1356997 2751727 := bstep (se 1 (by rfl) ⟨2063795, by rfl⟩ : syracuseStep 2751727 = 4127591) B4127591
theorem B4406699 : Blo 1356997 4406699 := bstep (se 1 (by rfl) ⟨3305024, by rfl⟩ : syracuseStep 4406699 = 6610049) B6610049
theorem B3055463 : Blo 1356997 3055463 := bstep (se 1 (by rfl) ⟨2291597, by rfl⟩ : syracuseStep 3055463 = 4583195) B4583195
theorem B70565741 : Blo 1356997 70565741 := bstep (se 3 (by rfl) ⟨13231076, by rfl⟩ : syracuseStep 70565741 = 26462153) B26462153
theorem B34799543 : Blo 1356997 34799543 := bstep (se 1 (by rfl) ⟨26099657, by rfl⟩ : syracuseStep 34799543 = 52199315) B52199315
theorem B5800045 : Blo 1356997 5800045 := bstep (se 3 (by rfl) ⟨1087508, by rfl⟩ : syracuseStep 5800045 = 2175017) B2175017
theorem B3056219 : Blo 1356997 3056219 := bstep (se 1 (by rfl) ⟨2292164, by rfl⟩ : syracuseStep 3056219 = 4584329) B4584329
theorem B2975843195 : Blo 1356997 2975843195 := bstep (se 1 (by rfl) ⟨2231882396, by rfl⟩ : syracuseStep 2975843195 = 4463764793) B4463764793
theorem B7734599 : Blo 1356997 7734599 := bstep (se 1 (by rfl) ⟨5800949, by rfl⟩ : syracuseStep 7734599 = 11601899) B11601899
theorem B26094737 : Blo 1356997 26094737 := bstep (se 2 (by rfl) ⟨9785526, by rfl⟩ : syracuseStep 26094737 = 19571053) B19571053
theorem B11603675 : Blo 1356997 11603675 := bstep (se 1 (by rfl) ⟨8702756, by rfl⟩ : syracuseStep 11603675 = 17405513) B17405513
theorem B423047539 : Blo 1356997 423047539 := bstep (se 1 (by rfl) ⟨317285654, by rfl⟩ : syracuseStep 423047539 = 634571309) B634571309
theorem B7836065 : Blo 1356997 7836065 := bstep (se 2 (by rfl) ⟨2938524, by rfl⟩ : syracuseStep 7836065 = 5877049) B5877049
theorem B2937799 : Blo 1356997 2937799 := bstep (se 1 (by rfl) ⟨2203349, by rfl⟩ : syracuseStep 2937799 = 4406699) B4406699
theorem B5158025 : Blo 1356997 5158025 := bstep (se 2 (by rfl) ⟨1934259, by rfl⟩ : syracuseStep 5158025 = 3868519) B3868519
theorem B2036975 : Blo 1356997 2036975 := bstep (se 1 (by rfl) ⟨1527731, by rfl⟩ : syracuseStep 2036975 = 3055463) B3055463
theorem B47043827 : Blo 1356997 47043827 := bstep (se 1 (by rfl) ⟨35282870, by rfl⟩ : syracuseStep 47043827 = 70565741) B70565741
theorem B7337243 : Blo 1356997 7337243 := bstep (se 1 (by rfl) ⟨5502932, by rfl⟩ : syracuseStep 7337243 = 11005865) B11005865
theorem B7731227 : Blo 1356997 7731227 := bstep (se 1 (by rfl) ⟨5798420, by rfl⟩ : syracuseStep 7731227 = 11596841) B11596841
theorem B5503841 : Blo 1356997 5503841 := bstep (se 2 (by rfl) ⟨2063940, by rfl⟩ : syracuseStep 5503841 = 4127881) B4127881
theorem B3668969 : Blo 1356997 3668969 := bstep (se 2 (by rfl) ⟨1375863, by rfl⟩ : syracuseStep 3668969 = 2751727) B2751727
theorem B23199695 : Blo 1356997 23199695 := bstep (se 1 (by rfl) ⟨17399771, by rfl⟩ : syracuseStep 23199695 = 34799543) B34799543
theorem B7733393 : Blo 1356997 7733393 := bstep (se 2 (by rfl) ⟨2900022, by rfl⟩ : syracuseStep 7733393 = 5800045) B5800045
theorem B5154151 : Blo 1356997 5154151 := bstep (se 1 (by rfl) ⟨3865613, by rfl⟩ : syracuseStep 5154151 = 7731227) B7731227
theorem B7735783 : Blo 1356997 7735783 := bstep (se 1 (by rfl) ⟨5801837, by rfl⟩ : syracuseStep 7735783 = 11603675) B11603675
theorem B564063385 : Blo 1356997 564063385 := bstep (se 2 (by rfl) ⟨211523769, by rfl⟩ : syracuseStep 564063385 = 423047539) B423047539
theorem B19565981 : Blo 1356997 19565981 := bstep (se 3 (by rfl) ⟨3668621, by rfl⟩ : syracuseStep 19565981 = 7337243) B7337243
theorem B31362551 : Blo 1356997 31362551 := bstep (se 1 (by rfl) ⟨23521913, by rfl⟩ : syracuseStep 31362551 = 47043827) B47043827
theorem B5156399 : Blo 1356997 5156399 := bstep (se 1 (by rfl) ⟨3867299, by rfl⟩ : syracuseStep 5156399 = 7734599) B7734599
theorem B2445979 : Blo 1356997 2445979 := bstep (se 1 (by rfl) ⟨1834484, by rfl⟩ : syracuseStep 2445979 = 3668969) B3668969
theorem B17396491 : Blo 1356997 17396491 := bstep (se 1 (by rfl) ⟨13047368, by rfl⟩ : syracuseStep 17396491 = 26094737) B26094737
theorem B15668261 : Blo 1356997 15668261 := bstep (se 4 (by rfl) ⟨1468899, by rfl⟩ : syracuseStep 15668261 = 2937799) B2937799
theorem B5224043 : Blo 1356997 5224043 := bstep (se 1 (by rfl) ⟨3918032, by rfl⟩ : syracuseStep 5224043 = 7836065) B7836065
theorem B2037479 : Blo 1356997 2037479 := bstep (se 1 (by rfl) ⟨1528109, by rfl⟩ : syracuseStep 2037479 = 3056219) B3056219
theorem B1983895463 : Blo 1356997 1983895463 := bstep (se 1 (by rfl) ⟨1487921597, by rfl⟩ : syracuseStep 1983895463 = 2975843195) B2975843195
theorem B3438683 : Blo 1356997 3438683 := bstep (se 1 (by rfl) ⟨2579012, by rfl⟩ : syracuseStep 3438683 = 5158025) B5158025
theorem B1357983 : Blo 1356997 1357983 := bstep (se 1 (by rfl) ⟨1018487, by rfl⟩ : syracuseStep 1357983 = 2036975) B2036975
theorem B3669227 : Blo 1356997 3669227 := bstep (se 1 (by rfl) ⟨2751920, by rfl⟩ : syracuseStep 3669227 = 5503841) B5503841
theorem B15466463 : Blo 1356997 15466463 := bstep (se 1 (by rfl) ⟨11599847, by rfl⟩ : syracuseStep 15466463 = 23199695) B23199695
theorem B10314377 : Blo 1356997 10314377 := bstep (se 2 (by rfl) ⟨3867891, by rfl⟩ : syracuseStep 10314377 = 7735783) B7735783
theorem B10445507 : Blo 1356997 10445507 := bstep (se 1 (by rfl) ⟨7834130, by rfl⟩ : syracuseStep 10445507 = 15668261) B15668261
theorem B3261305 : Blo 1356997 3261305 := bstep (se 2 (by rfl) ⟨1222989, by rfl⟩ : syracuseStep 3261305 = 2445979) B2445979
theorem B3482695 : Blo 1356997 3482695 := bstep (se 1 (by rfl) ⟨2612021, by rfl⟩ : syracuseStep 3482695 = 5224043) B5224043
theorem B752084513 : Blo 1356997 752084513 := bstep (se 2 (by rfl) ⟨282031692, by rfl⟩ : syracuseStep 752084513 = 564063385) B564063385
theorem B13043987 : Blo 1356997 13043987 := bstep (se 1 (by rfl) ⟨9782990, by rfl⟩ : syracuseStep 13043987 = 19565981) B19565981
theorem B20908367 : Blo 1356997 20908367 := bstep (se 1 (by rfl) ⟨15681275, by rfl⟩ : syracuseStep 20908367 = 31362551) B31362551
theorem B5290387901 : Blo 1356997 5290387901 := bstep (se 3 (by rfl) ⟨991947731, by rfl⟩ : syracuseStep 5290387901 = 1983895463) B1983895463
theorem B5155595 : Blo 1356997 5155595 := bstep (se 1 (by rfl) ⟨3866696, by rfl⟩ : syracuseStep 5155595 = 7733393) B7733393
theorem B23195321 : Blo 1356997 23195321 := bstep (se 2 (by rfl) ⟨8698245, by rfl⟩ : syracuseStep 23195321 = 17396491) B17396491
theorem B2446151 : Blo 1356997 2446151 := bstep (se 1 (by rfl) ⟨1834613, by rfl⟩ : syracuseStep 2446151 = 3669227) B3669227
theorem B3437599 : Blo 1356997 3437599 := bstep (se 1 (by rfl) ⟨2578199, by rfl⟩ : syracuseStep 3437599 = 5156399) B5156399
theorem B10310975 : Blo 1356997 10310975 := bstep (se 1 (by rfl) ⟨7733231, by rfl⟩ : syracuseStep 10310975 = 15466463) B15466463
theorem B1358319 : Blo 1356997 1358319 := bstep (se 1 (by rfl) ⟨1018739, by rfl⟩ : syracuseStep 1358319 = 2037479) B2037479
theorem B2292455 : Blo 1356997 2292455 := bstep (se 1 (by rfl) ⟨1719341, by rfl⟩ : syracuseStep 2292455 = 3438683) B3438683
theorem B6872201 : Blo 1356997 6872201 := bstep (se 2 (by rfl) ⟨2577075, by rfl⟩ : syracuseStep 6872201 = 5154151) B5154151
theorem B6963671 : Blo 1356997 6963671 := bstep (se 1 (by rfl) ⟨5222753, by rfl⟩ : syracuseStep 6963671 = 10445507) B10445507
theorem B26092277 : Blo 1356997 26092277 := bstep (se 5 (by rfl) ⟨1223075, by rfl⟩ : syracuseStep 26092277 = 2446151) B2446151
theorem B6873983 : Blo 1356997 6873983 := bstep (se 1 (by rfl) ⟨5155487, by rfl⟩ : syracuseStep 6873983 = 10310975) B10310975
theorem B4581467 : Blo 1356997 4581467 := bstep (se 1 (by rfl) ⟨3436100, by rfl⟩ : syracuseStep 4581467 = 6872201) B6872201
theorem B18574373 : Blo 1356997 18574373 := bstep (se 4 (by rfl) ⟨1741347, by rfl⟩ : syracuseStep 18574373 = 3482695) B3482695
theorem B6876251 : Blo 1356997 6876251 := bstep (se 1 (by rfl) ⟨5157188, by rfl⟩ : syracuseStep 6876251 = 10314377) B10314377
theorem B2174203 : Blo 1356997 2174203 := bstep (se 1 (by rfl) ⟨1630652, by rfl⟩ : syracuseStep 2174203 = 3261305) B3261305
theorem B4583465 : Blo 1356997 4583465 := bstep (se 2 (by rfl) ⟨1718799, by rfl⟩ : syracuseStep 4583465 = 3437599) B3437599
theorem B8695991 : Blo 1356997 8695991 := bstep (se 1 (by rfl) ⟨6521993, by rfl⟩ : syracuseStep 8695991 = 13043987) B13043987
theorem B13938911 : Blo 1356997 13938911 := bstep (se 1 (by rfl) ⟨10454183, by rfl⟩ : syracuseStep 13938911 = 20908367) B20908367
theorem B1528303 : Blo 1356997 1528303 := bstep (se 1 (by rfl) ⟨1146227, by rfl⟩ : syracuseStep 1528303 = 2292455) B2292455
theorem B3437063 : Blo 1356997 3437063 := bstep (se 1 (by rfl) ⟨2577797, by rfl⟩ : syracuseStep 3437063 = 5155595) B5155595
theorem B15463547 : Blo 1356997 15463547 := bstep (se 1 (by rfl) ⟨11597660, by rfl⟩ : syracuseStep 15463547 = 23195321) B23195321
theorem B501389675 : Blo 1356997 501389675 := bstep (se 1 (by rfl) ⟨376042256, by rfl⟩ : syracuseStep 501389675 = 752084513) B752084513
theorem B3526925267 : Blo 1356997 3526925267 := bstep (se 1 (by rfl) ⟨2645193950, by rfl⟩ : syracuseStep 3526925267 = 5290387901) B5290387901
theorem B3055643 : Blo 1356997 3055643 := bstep (se 1 (by rfl) ⟨2291732, by rfl⟩ : syracuseStep 3055643 = 4583465) B4583465
theorem B334259783 : Blo 1356997 334259783 := bstep (se 1 (by rfl) ⟨250694837, by rfl⟩ : syracuseStep 334259783 = 501389675) B501389675
theorem B9292607 : Blo 1356997 9292607 := bstep (se 1 (by rfl) ⟨6969455, by rfl⟩ : syracuseStep 9292607 = 13938911) B13938911
theorem B17394851 : Blo 1356997 17394851 := bstep (se 1 (by rfl) ⟨13046138, by rfl⟩ : syracuseStep 17394851 = 26092277) B26092277
theorem B4582655 : Blo 1356997 4582655 := bstep (se 1 (by rfl) ⟨3436991, by rfl⟩ : syracuseStep 4582655 = 6873983) B6873983
theorem B10309031 : Blo 1356997 10309031 := bstep (se 1 (by rfl) ⟨7731773, by rfl⟩ : syracuseStep 10309031 = 15463547) B15463547
theorem B12382915 : Blo 1356997 12382915 := bstep (se 1 (by rfl) ⟨9287186, by rfl⟩ : syracuseStep 12382915 = 18574373) B18574373
theorem B4584167 : Blo 1356997 4584167 := bstep (se 1 (by rfl) ⟨3438125, by rfl⟩ : syracuseStep 4584167 = 6876251) B6876251
theorem B5797327 : Blo 1356997 5797327 := bstep (se 1 (by rfl) ⟨4347995, by rfl⟩ : syracuseStep 5797327 = 8695991) B8695991
theorem B4642447 : Blo 1356997 4642447 := bstep (se 1 (by rfl) ⟨3481835, by rfl⟩ : syracuseStep 4642447 = 6963671) B6963671
theorem B2291375 : Blo 1356997 2291375 := bstep (se 1 (by rfl) ⟨1718531, by rfl⟩ : syracuseStep 2291375 = 3437063) B3437063
theorem B2037737 : Blo 1356997 2037737 := bstep (se 2 (by rfl) ⟨764151, by rfl⟩ : syracuseStep 2037737 = 1528303) B1528303
theorem B3054311 : Blo 1356997 3054311 := bstep (se 1 (by rfl) ⟨2290733, by rfl⟩ : syracuseStep 3054311 = 4581467) B4581467
theorem B2898937 : Blo 1356997 2898937 := bstep (se 2 (by rfl) ⟨1087101, by rfl⟩ : syracuseStep 2898937 = 2174203) B2174203
theorem B2351283511 : Blo 1356997 2351283511 := bstep (se 1 (by rfl) ⟨1763462633, by rfl⟩ : syracuseStep 2351283511 = 3526925267) B3526925267
theorem B3056111 : Blo 1356997 3056111 := bstep (se 1 (by rfl) ⟨2292083, by rfl⟩ : syracuseStep 3056111 = 4584167) B4584167
theorem B222839855 : Blo 1356997 222839855 := bstep (se 1 (by rfl) ⟨167129891, by rfl⟩ : syracuseStep 222839855 = 334259783) B334259783
theorem B6195071 : Blo 1356997 6195071 := bstep (se 1 (by rfl) ⟨4646303, by rfl⟩ : syracuseStep 6195071 = 9292607) B9292607
theorem B16510553 : Blo 1356997 16510553 := bstep (se 2 (by rfl) ⟨6191457, by rfl⟩ : syracuseStep 16510553 = 12382915) B12382915
theorem B1527583 : Blo 1356997 1527583 := bstep (se 1 (by rfl) ⟨1145687, by rfl⟩ : syracuseStep 1527583 = 2291375) B2291375
theorem B2036207 : Blo 1356997 2036207 := bstep (se 1 (by rfl) ⟨1527155, by rfl⟩ : syracuseStep 2036207 = 3054311) B3054311
theorem B7729769 : Blo 1356997 7729769 := bstep (se 2 (by rfl) ⟨2898663, by rfl⟩ : syracuseStep 7729769 = 5797327) B5797327
theorem B11596567 : Blo 1356997 11596567 := bstep (se 1 (by rfl) ⟨8697425, by rfl⟩ : syracuseStep 11596567 = 17394851) B17394851
theorem B6189929 : Blo 1356997 6189929 := bstep (se 2 (by rfl) ⟨2321223, by rfl⟩ : syracuseStep 6189929 = 4642447) B4642447
theorem B2037095 : Blo 1356997 2037095 := bstep (se 1 (by rfl) ⟨1527821, by rfl⟩ : syracuseStep 2037095 = 3055643) B3055643
theorem B1358491 : Blo 1356997 1358491 := bstep (se 1 (by rfl) ⟨1018868, by rfl⟩ : syracuseStep 1358491 = 2037737) B2037737
theorem B3865249 : Blo 1356997 3865249 := bstep (se 2 (by rfl) ⟨1449468, by rfl⟩ : syracuseStep 3865249 = 2898937) B2898937
theorem B3135044681 : Blo 1356997 3135044681 := bstep (se 2 (by rfl) ⟨1175641755, by rfl⟩ : syracuseStep 3135044681 = 2351283511) B2351283511
theorem B3055103 : Blo 1356997 3055103 := bstep (se 1 (by rfl) ⟨2291327, by rfl⟩ : syracuseStep 3055103 = 4582655) B4582655
theorem B6872687 : Blo 1356997 6872687 := bstep (se 1 (by rfl) ⟨5154515, by rfl⟩ : syracuseStep 6872687 = 10309031) B10309031
theorem B5153179 : Blo 1356997 5153179 := bstep (se 1 (by rfl) ⟨3864884, by rfl⟩ : syracuseStep 5153179 = 7729769) B7729769
theorem B5153665 : Blo 1356997 5153665 := bstep (se 2 (by rfl) ⟨1932624, by rfl⟩ : syracuseStep 5153665 = 3865249) B3865249
theorem B4130047 : Blo 1356997 4130047 := bstep (se 1 (by rfl) ⟨3097535, by rfl⟩ : syracuseStep 4130047 = 6195071) B6195071
theorem B4581791 : Blo 1356997 4581791 := bstep (se 1 (by rfl) ⟨3436343, by rfl⟩ : syracuseStep 4581791 = 6872687) B6872687
theorem B15462089 : Blo 1356997 15462089 := bstep (se 2 (by rfl) ⟨5798283, by rfl⟩ : syracuseStep 15462089 = 11596567) B11596567
theorem B2090029787 : Blo 1356997 2090029787 := bstep (se 1 (by rfl) ⟨1567522340, by rfl⟩ : syracuseStep 2090029787 = 3135044681) B3135044681
theorem B2036735 : Blo 1356997 2036735 := bstep (se 1 (by rfl) ⟨1527551, by rfl⟩ : syracuseStep 2036735 = 3055103) B3055103
theorem B2036777 : Blo 1356997 2036777 := bstep (se 2 (by rfl) ⟨763791, by rfl⟩ : syracuseStep 2036777 = 1527583) B1527583
theorem B11007035 : Blo 1356997 11007035 := bstep (se 1 (by rfl) ⟨8255276, by rfl⟩ : syracuseStep 11007035 = 16510553) B16510553
theorem B1357471 : Blo 1356997 1357471 := bstep (se 1 (by rfl) ⟨1018103, by rfl⟩ : syracuseStep 1357471 = 2036207) B2036207
theorem B2037407 : Blo 1356997 2037407 := bstep (se 1 (by rfl) ⟨1528055, by rfl⟩ : syracuseStep 2037407 = 3056111) B3056111
theorem B4126619 : Blo 1356997 4126619 := bstep (se 1 (by rfl) ⟨3094964, by rfl⟩ : syracuseStep 4126619 = 6189929) B6189929
theorem B148559903 : Blo 1356997 148559903 := bstep (se 1 (by rfl) ⟨111419927, by rfl⟩ : syracuseStep 148559903 = 222839855) B222839855
theorem B1358063 : Blo 1356997 1358063 := bstep (se 1 (by rfl) ⟨1018547, by rfl⟩ : syracuseStep 1358063 = 2037095) B2037095
theorem B1393353191 : Blo 1356997 1393353191 := bstep (se 1 (by rfl) ⟨1045014893, by rfl⟩ : syracuseStep 1393353191 = 2090029787) B2090029787
theorem B10308059 : Blo 1356997 10308059 := bstep (se 1 (by rfl) ⟨7731044, by rfl⟩ : syracuseStep 10308059 = 15462089) B15462089
theorem B6870905 : Blo 1356997 6870905 := bstep (se 2 (by rfl) ⟨2576589, by rfl⟩ : syracuseStep 6870905 = 5153179) B5153179
theorem B1357823 : Blo 1356997 1357823 := bstep (se 1 (by rfl) ⟨1018367, by rfl⟩ : syracuseStep 1357823 = 2036735) B2036735
theorem B1357851 : Blo 1356997 1357851 := bstep (se 1 (by rfl) ⟨1018388, by rfl⟩ : syracuseStep 1357851 = 2036777) B2036777
theorem B7338023 : Blo 1356997 7338023 := bstep (se 1 (by rfl) ⟨5503517, by rfl⟩ : syracuseStep 7338023 = 11007035) B11007035
theorem B1358271 : Blo 1356997 1358271 := bstep (se 1 (by rfl) ⟨1018703, by rfl⟩ : syracuseStep 1358271 = 2037407) B2037407
theorem B6871553 : Blo 1356997 6871553 := bstep (se 2 (by rfl) ⟨2576832, by rfl⟩ : syracuseStep 6871553 = 5153665) B5153665
theorem B2751079 : Blo 1356997 2751079 := bstep (se 1 (by rfl) ⟨2063309, by rfl⟩ : syracuseStep 2751079 = 4126619) B4126619
theorem B22026917 : Blo 1356997 22026917 := bstep (se 4 (by rfl) ⟨2065023, by rfl⟩ : syracuseStep 22026917 = 4130047) B4130047
theorem B99039935 : Blo 1356997 99039935 := bstep (se 1 (by rfl) ⟨74279951, by rfl⟩ : syracuseStep 99039935 = 148559903) B148559903
theorem B3054527 : Blo 1356997 3054527 := bstep (se 1 (by rfl) ⟨2290895, by rfl⟩ : syracuseStep 3054527 = 4581791) B4581791
theorem B4580603 : Blo 1356997 4580603 := bstep (se 1 (by rfl) ⟨3435452, by rfl⟩ : syracuseStep 4580603 = 6870905) B6870905
theorem B4892015 : Blo 1356997 4892015 := bstep (se 1 (by rfl) ⟨3669011, by rfl⟩ : syracuseStep 4892015 = 7338023) B7338023
theorem B4581035 : Blo 1356997 4581035 := bstep (se 1 (by rfl) ⟨3435776, by rfl⟩ : syracuseStep 4581035 = 6871553) B6871553
theorem B928902127 : Blo 1356997 928902127 := bstep (se 1 (by rfl) ⟨696676595, by rfl⟩ : syracuseStep 928902127 = 1393353191) B1393353191
theorem B14684611 : Blo 1356997 14684611 := bstep (se 1 (by rfl) ⟨11013458, by rfl⟩ : syracuseStep 14684611 = 22026917) B22026917
theorem B2036351 : Blo 1356997 2036351 := bstep (se 1 (by rfl) ⟨1527263, by rfl⟩ : syracuseStep 2036351 = 3054527) B3054527
theorem B3668105 : Blo 1356997 3668105 := bstep (se 2 (by rfl) ⟨1375539, by rfl⟩ : syracuseStep 3668105 = 2751079) B2751079
theorem B6872039 : Blo 1356997 6872039 := bstep (se 1 (by rfl) ⟨5154029, by rfl⟩ : syracuseStep 6872039 = 10308059) B10308059
theorem B66026623 : Blo 1356997 66026623 := bstep (se 1 (by rfl) ⟨49519967, by rfl⟩ : syracuseStep 66026623 = 99039935) B99039935
theorem B19579481 : Blo 1356997 19579481 := bstep (se 2 (by rfl) ⟨7342305, by rfl⟩ : syracuseStep 19579481 = 14684611) B14684611
theorem B4581359 : Blo 1356997 4581359 := bstep (se 1 (by rfl) ⟨3436019, by rfl⟩ : syracuseStep 4581359 = 6872039) B6872039
theorem B13045373 : Blo 1356997 13045373 := bstep (se 3 (by rfl) ⟨2446007, by rfl⟩ : syracuseStep 13045373 = 4892015) B4892015
theorem B1238536169 : Blo 1356997 1238536169 := bstep (se 2 (by rfl) ⟨464451063, by rfl⟩ : syracuseStep 1238536169 = 928902127) B928902127
theorem B2445403 : Blo 1356997 2445403 := bstep (se 1 (by rfl) ⟨1834052, by rfl⟩ : syracuseStep 2445403 = 3668105) B3668105
theorem B88035497 : Blo 1356997 88035497 := bstep (se 2 (by rfl) ⟨33013311, by rfl⟩ : syracuseStep 88035497 = 66026623) B66026623
theorem B1357567 : Blo 1356997 1357567 := bstep (se 1 (by rfl) ⟨1018175, by rfl⟩ : syracuseStep 1357567 = 2036351) B2036351
theorem B3053735 : Blo 1356997 3053735 := bstep (se 1 (by rfl) ⟨2290301, by rfl⟩ : syracuseStep 3053735 = 4580603) B4580603
theorem B3054023 : Blo 1356997 3054023 := bstep (se 1 (by rfl) ⟨2290517, by rfl⟩ : syracuseStep 3054023 = 4581035) B4581035
theorem B3260537 : Blo 1356997 3260537 := bstep (se 2 (by rfl) ⟨1222701, by rfl⟩ : syracuseStep 3260537 = 2445403) B2445403
theorem B825690779 : Blo 1356997 825690779 := bstep (se 1 (by rfl) ⟨619268084, by rfl⟩ : syracuseStep 825690779 = 1238536169) B1238536169
theorem B58690331 : Blo 1356997 58690331 := bstep (se 1 (by rfl) ⟨44017748, by rfl⟩ : syracuseStep 58690331 = 88035497) B88035497
theorem B13052987 : Blo 1356997 13052987 := bstep (se 1 (by rfl) ⟨9789740, by rfl⟩ : syracuseStep 13052987 = 19579481) B19579481
theorem B2035823 : Blo 1356997 2035823 := bstep (se 1 (by rfl) ⟨1526867, by rfl⟩ : syracuseStep 2035823 = 3053735) B3053735
theorem B2036015 : Blo 1356997 2036015 := bstep (se 1 (by rfl) ⟨1527011, by rfl⟩ : syracuseStep 2036015 = 3054023) B3054023
theorem B8696915 : Blo 1356997 8696915 := bstep (se 1 (by rfl) ⟨6522686, by rfl⟩ : syracuseStep 8696915 = 13045373) B13045373
theorem B3054239 : Blo 1356997 3054239 := bstep (se 1 (by rfl) ⟨2290679, by rfl⟩ : syracuseStep 3054239 = 4581359) B4581359
theorem B39126887 : Blo 1356997 39126887 := bstep (se 1 (by rfl) ⟨29345165, by rfl⟩ : syracuseStep 39126887 = 58690331) B58690331
theorem B8701991 : Blo 1356997 8701991 := bstep (se 1 (by rfl) ⟨6526493, by rfl⟩ : syracuseStep 8701991 = 13052987) B13052987
theorem B2173691 : Blo 1356997 2173691 := bstep (se 1 (by rfl) ⟨1630268, by rfl⟩ : syracuseStep 2173691 = 3260537) B3260537
theorem B2036159 : Blo 1356997 2036159 := bstep (se 1 (by rfl) ⟨1527119, by rfl⟩ : syracuseStep 2036159 = 3054239) B3054239
theorem B1357215 : Blo 1356997 1357215 := bstep (se 1 (by rfl) ⟨1017911, by rfl⟩ : syracuseStep 1357215 = 2035823) B2035823
theorem B1357343 : Blo 1356997 1357343 := bstep (se 1 (by rfl) ⟨1018007, by rfl⟩ : syracuseStep 1357343 = 2036015) B2036015
theorem B5797943 : Blo 1356997 5797943 := bstep (se 1 (by rfl) ⟨4348457, by rfl⟩ : syracuseStep 5797943 = 8696915) B8696915
theorem B550460519 : Blo 1356997 550460519 := bstep (se 1 (by rfl) ⟨412845389, by rfl⟩ : syracuseStep 550460519 = 825690779) B825690779
theorem B26084591 : Blo 1356997 26084591 := bstep (se 1 (by rfl) ⟨19563443, by rfl⟩ : syracuseStep 26084591 = 39126887) B39126887
theorem B5801327 : Blo 1356997 5801327 := bstep (se 1 (by rfl) ⟨4350995, by rfl⟩ : syracuseStep 5801327 = 8701991) B8701991
theorem B366973679 : Blo 1356997 366973679 := bstep (se 1 (by rfl) ⟨275230259, by rfl⟩ : syracuseStep 366973679 = 550460519) B550460519
theorem B1357439 : Blo 1356997 1357439 := bstep (se 1 (by rfl) ⟨1018079, by rfl⟩ : syracuseStep 1357439 = 2036159) B2036159
theorem B3865295 : Blo 1356997 3865295 := bstep (se 1 (by rfl) ⟨2898971, by rfl⟩ : syracuseStep 3865295 = 5797943) B5797943
theorem B1449127 : Blo 1356997 1449127 := bstep (se 1 (by rfl) ⟨1086845, by rfl⟩ : syracuseStep 1449127 = 2173691) B2173691
theorem B3867551 : Blo 1356997 3867551 := bstep (se 1 (by rfl) ⟨2900663, by rfl⟩ : syracuseStep 3867551 = 5801327) B5801327
theorem B2576863 : Blo 1356997 2576863 := bstep (se 1 (by rfl) ⟨1932647, by rfl⟩ : syracuseStep 2576863 = 3865295) B3865295
theorem B978596477 : Blo 1356997 978596477 := bstep (se 3 (by rfl) ⟨183486839, by rfl⟩ : syracuseStep 978596477 = 366973679) B366973679
theorem B17389727 : Blo 1356997 17389727 := bstep (se 1 (by rfl) ⟨13042295, by rfl⟩ : syracuseStep 17389727 = 26084591) B26084591
theorem B1932169 : Blo 1356997 1932169 := bstep (se 2 (by rfl) ⟨724563, by rfl⟩ : syracuseStep 1932169 = 1449127) B1449127
theorem B11593151 : Blo 1356997 11593151 := bstep (se 1 (by rfl) ⟨8694863, by rfl⟩ : syracuseStep 11593151 = 17389727) B17389727
theorem B652397651 : Blo 1356997 652397651 := bstep (se 1 (by rfl) ⟨489298238, by rfl⟩ : syracuseStep 652397651 = 978596477) B978596477
theorem B3435817 : Blo 1356997 3435817 := bstep (se 2 (by rfl) ⟨1288431, by rfl⟩ : syracuseStep 3435817 = 2576863) B2576863
theorem B2576225 : Blo 1356997 2576225 := bstep (se 2 (by rfl) ⟨966084, by rfl⟩ : syracuseStep 2576225 = 1932169) B1932169
theorem B2578367 : Blo 1356997 2578367 := bstep (se 1 (by rfl) ⟨1933775, by rfl⟩ : syracuseStep 2578367 = 3867551) B3867551
theorem B4581089 : Blo 1356997 4581089 := bstep (se 2 (by rfl) ⟨1717908, by rfl⟩ : syracuseStep 4581089 = 3435817) B3435817
theorem B434931767 : Blo 1356997 434931767 := bstep (se 1 (by rfl) ⟨326198825, by rfl⟩ : syracuseStep 434931767 = 652397651) B652397651
theorem B7728767 : Blo 1356997 7728767 := bstep (se 1 (by rfl) ⟨5796575, by rfl⟩ : syracuseStep 7728767 = 11593151) B11593151
theorem B6869933 : Blo 1356997 6869933 := bstep (se 3 (by rfl) ⟨1288112, by rfl⟩ : syracuseStep 6869933 = 2576225) B2576225
theorem B1718911 : Blo 1356997 1718911 := bstep (se 1 (by rfl) ⟨1289183, by rfl⟩ : syracuseStep 1718911 = 2578367) B2578367
theorem B4579955 : Blo 1356997 4579955 := bstep (se 1 (by rfl) ⟨3434966, by rfl⟩ : syracuseStep 4579955 = 6869933) B6869933
theorem B2291881 : Blo 1356997 2291881 := bstep (se 2 (by rfl) ⟨859455, by rfl⟩ : syracuseStep 2291881 = 1718911) B1718911
theorem B3054059 : Blo 1356997 3054059 := bstep (se 1 (by rfl) ⟨2290544, by rfl⟩ : syracuseStep 3054059 = 4581089) B4581089
theorem B289954511 : Blo 1356997 289954511 := bstep (se 1 (by rfl) ⟨217465883, by rfl⟩ : syracuseStep 289954511 = 434931767) B434931767
theorem B5152511 : Blo 1356997 5152511 := bstep (se 1 (by rfl) ⟨3864383, by rfl⟩ : syracuseStep 5152511 = 7728767) B7728767
theorem B3055841 : Blo 1356997 3055841 := bstep (se 2 (by rfl) ⟨1145940, by rfl⟩ : syracuseStep 3055841 = 2291881) B2291881
theorem B3435007 : Blo 1356997 3435007 := bstep (se 1 (by rfl) ⟨2576255, by rfl⟩ : syracuseStep 3435007 = 5152511) B5152511
theorem B2036039 : Blo 1356997 2036039 := bstep (se 1 (by rfl) ⟨1527029, by rfl⟩ : syracuseStep 2036039 = 3054059) B3054059
theorem B193303007 : Blo 1356997 193303007 := bstep (se 1 (by rfl) ⟨144977255, by rfl⟩ : syracuseStep 193303007 = 289954511) B289954511
theorem B3053303 : Blo 1356997 3053303 := bstep (se 1 (by rfl) ⟨2289977, by rfl⟩ : syracuseStep 3053303 = 4579955) B4579955
theorem B128868671 : Blo 1356997 128868671 := bstep (se 1 (by rfl) ⟨96651503, by rfl⟩ : syracuseStep 128868671 = 193303007) B193303007
theorem B4580009 : Blo 1356997 4580009 := bstep (se 2 (by rfl) ⟨1717503, by rfl⟩ : syracuseStep 4580009 = 3435007) B3435007
theorem B2035535 : Blo 1356997 2035535 := bstep (se 1 (by rfl) ⟨1526651, by rfl⟩ : syracuseStep 2035535 = 3053303) B3053303
theorem B2037227 : Blo 1356997 2037227 := bstep (se 1 (by rfl) ⟨1527920, by rfl⟩ : syracuseStep 2037227 = 3055841) B3055841
theorem B1357359 : Blo 1356997 1357359 := bstep (se 1 (by rfl) ⟨1018019, by rfl⟩ : syracuseStep 1357359 = 2036039) B2036039
theorem B343649789 : Blo 1356997 343649789 := bstep (se 3 (by rfl) ⟨64434335, by rfl⟩ : syracuseStep 343649789 = 128868671) B128868671
theorem B1357023 : Blo 1356997 1357023 := bstep (se 1 (by rfl) ⟨1017767, by rfl⟩ : syracuseStep 1357023 = 2035535) B2035535
theorem B3053339 : Blo 1356997 3053339 := bstep (se 1 (by rfl) ⟨2290004, by rfl⟩ : syracuseStep 3053339 = 4580009) B4580009
theorem B1358151 : Blo 1356997 1358151 := bstep (se 1 (by rfl) ⟨1018613, by rfl⟩ : syracuseStep 1358151 = 2037227) B2037227
theorem B229099859 : Blo 1356997 229099859 := bstep (se 1 (by rfl) ⟨171824894, by rfl⟩ : syracuseStep 229099859 = 343649789) B343649789
theorem B2035559 : Blo 1356997 2035559 := bstep (se 1 (by rfl) ⟨1526669, by rfl⟩ : syracuseStep 2035559 = 3053339) B3053339
theorem B152733239 : Blo 1356997 152733239 := bstep (se 1 (by rfl) ⟨114549929, by rfl⟩ : syracuseStep 152733239 = 229099859) B229099859
theorem B1357039 : Blo 1356997 1357039 := bstep (se 1 (by rfl) ⟨1017779, by rfl⟩ : syracuseStep 1357039 = 2035559) B2035559
theorem B101822159 : Blo 1356997 101822159 := bstep (se 1 (by rfl) ⟨76366619, by rfl⟩ : syracuseStep 101822159 = 152733239) B152733239
theorem B67881439 : Blo 1356997 67881439 := bstep (se 1 (by rfl) ⟨50911079, by rfl⟩ : syracuseStep 67881439 = 101822159) B101822159
theorem B90508585 : Blo 1356997 90508585 := bstep (se 2 (by rfl) ⟨33940719, by rfl⟩ : syracuseStep 90508585 = 67881439) B67881439
theorem B120678113 : Blo 1356997 120678113 := bstep (se 2 (by rfl) ⟨45254292, by rfl⟩ : syracuseStep 120678113 = 90508585) B90508585
theorem B80452075 : Blo 1356997 80452075 := bstep (se 1 (by rfl) ⟨60339056, by rfl⟩ : syracuseStep 80452075 = 120678113) B120678113
theorem B107269433 : Blo 1356997 107269433 := bstep (se 2 (by rfl) ⟨40226037, by rfl⟩ : syracuseStep 107269433 = 80452075) B80452075
theorem B71512955 : Blo 1356997 71512955 := bstep (se 1 (by rfl) ⟨53634716, by rfl⟩ : syracuseStep 71512955 = 107269433) B107269433
theorem B47675303 : Blo 1356997 47675303 := bstep (se 1 (by rfl) ⟨35756477, by rfl⟩ : syracuseStep 47675303 = 71512955) B71512955
theorem B31783535 : Blo 1356997 31783535 := bstep (se 1 (by rfl) ⟨23837651, by rfl⟩ : syracuseStep 31783535 = 47675303) B47675303
theorem B21189023 : Blo 1356997 21189023 := bstep (se 1 (by rfl) ⟨15891767, by rfl⟩ : syracuseStep 21189023 = 31783535) B31783535
theorem B14126015 : Blo 1356997 14126015 := bstep (se 1 (by rfl) ⟨10594511, by rfl⟩ : syracuseStep 14126015 = 21189023) B21189023
theorem B9417343 : Blo 1356997 9417343 := bstep (se 1 (by rfl) ⟨7063007, by rfl⟩ : syracuseStep 9417343 = 14126015) B14126015
theorem B12556457 : Blo 1356997 12556457 := bstep (se 2 (by rfl) ⟨4708671, by rfl⟩ : syracuseStep 12556457 = 9417343) B9417343
theorem B8370971 : Blo 1356997 8370971 := bstep (se 1 (by rfl) ⟨6278228, by rfl⟩ : syracuseStep 8370971 = 12556457) B12556457
theorem B5580647 : Blo 1356997 5580647 := bstep (se 1 (by rfl) ⟨4185485, by rfl⟩ : syracuseStep 5580647 = 8370971) B8370971
theorem B3720431 : Blo 1356997 3720431 := bstep (se 1 (by rfl) ⟨2790323, by rfl⟩ : syracuseStep 3720431 = 5580647) B5580647
theorem B9921149 : Blo 1356997 9921149 := bstep (se 3 (by rfl) ⟨1860215, by rfl⟩ : syracuseStep 9921149 = 3720431) B3720431
theorem B6614099 : Blo 1356997 6614099 := bstep (se 1 (by rfl) ⟨4960574, by rfl⟩ : syracuseStep 6614099 = 9921149) B9921149
theorem B4409399 : Blo 1356997 4409399 := bstep (se 1 (by rfl) ⟨3307049, by rfl⟩ : syracuseStep 4409399 = 6614099) B6614099
theorem B2939599 : Blo 1356997 2939599 := bstep (se 1 (by rfl) ⟨2204699, by rfl⟩ : syracuseStep 2939599 = 4409399) B4409399
theorem B3919465 : Blo 1356997 3919465 := bstep (se 2 (by rfl) ⟨1469799, by rfl⟩ : syracuseStep 3919465 = 2939599) B2939599
theorem B5225953 : Blo 1356997 5225953 := bstep (se 2 (by rfl) ⟨1959732, by rfl⟩ : syracuseStep 5225953 = 3919465) B3919465
theorem B6967937 : Blo 1356997 6967937 := bstep (se 2 (by rfl) ⟨2612976, by rfl⟩ : syracuseStep 6967937 = 5225953) B5225953
theorem B4645291 : Blo 1356997 4645291 := bstep (se 1 (by rfl) ⟨3483968, by rfl⟩ : syracuseStep 4645291 = 6967937) B6967937
theorem B6193721 : Blo 1356997 6193721 := bstep (se 2 (by rfl) ⟨2322645, by rfl⟩ : syracuseStep 6193721 = 4645291) B4645291
theorem B4129147 : Blo 1356997 4129147 := bstep (se 1 (by rfl) ⟨3096860, by rfl⟩ : syracuseStep 4129147 = 6193721) B6193721
theorem B5505529 : Blo 1356997 5505529 := bstep (se 2 (by rfl) ⟨2064573, by rfl⟩ : syracuseStep 5505529 = 4129147) B4129147
theorem B7340705 : Blo 1356997 7340705 := bstep (se 2 (by rfl) ⟨2752764, by rfl⟩ : syracuseStep 7340705 = 5505529) B5505529
theorem B4893803 : Blo 1356997 4893803 := bstep (se 1 (by rfl) ⟨3670352, by rfl⟩ : syracuseStep 4893803 = 7340705) B7340705
theorem B3262535 : Blo 1356997 3262535 := bstep (se 1 (by rfl) ⟨2446901, by rfl⟩ : syracuseStep 3262535 = 4893803) B4893803
theorem B2175023 : Blo 1356997 2175023 := bstep (se 1 (by rfl) ⟨1631267, by rfl⟩ : syracuseStep 2175023 = 3262535) B3262535
theorem B5800061 : Blo 1356997 5800061 := bstep (se 3 (by rfl) ⟨1087511, by rfl⟩ : syracuseStep 5800061 = 2175023) B2175023
theorem B3866707 : Blo 1356997 3866707 := bstep (se 1 (by rfl) ⟨2900030, by rfl⟩ : syracuseStep 3866707 = 5800061) B5800061
theorem B5155609 : Blo 1356997 5155609 := bstep (se 2 (by rfl) ⟨1933353, by rfl⟩ : syracuseStep 5155609 = 3866707) B3866707
theorem B6874145 : Blo 1356997 6874145 := bstep (se 2 (by rfl) ⟨2577804, by rfl⟩ : syracuseStep 6874145 = 5155609) B5155609
theorem B4582763 : Blo 1356997 4582763 := bstep (se 1 (by rfl) ⟨3437072, by rfl⟩ : syracuseStep 4582763 = 6874145) B6874145
theorem B3055175 : Blo 1356997 3055175 := bstep (se 1 (by rfl) ⟨2291381, by rfl⟩ : syracuseStep 3055175 = 4582763) B4582763
theorem B2036783 : Blo 1356997 2036783 := bstep (se 1 (by rfl) ⟨1527587, by rfl⟩ : syracuseStep 2036783 = 3055175) B3055175
theorem B1357855 : Blo 1356997 1357855 := bstep (se 1 (by rfl) ⟨1018391, by rfl⟩ : syracuseStep 1357855 = 2036783) B2036783

theorem C0 (j : ℕ) (h1 : 339249 ≤ j) (h2 : j ≤ 339623) : Blo 1356997 (4 * j + 3) := by
  interval_cases j
  · exact B1356999
  · exact B1357003
  · exact B1357007
  · exact B1357011
  · exact B1357015
  · exact B1357019
  · exact B1357023
  · exact B1357027
  · exact B1357031
  · exact B1357035
  · exact B1357039
  · exact B1357043
  · exact B1357047
  · exact B1357051
  · exact B1357055
  · exact B1357059
  · exact B1357063
  · exact B1357067
  · exact B1357071
  · exact B1357075
  · exact B1357079
  · exact B1357083
  · exact B1357087
  · exact B1357091
  · exact B1357095
  · exact B1357099
  · exact B1357103
  · exact B1357107
  · exact B1357111
  · exact B1357115
  · exact B1357119
  · exact B1357123
  · exact B1357127
  · exact B1357131
  · exact B1357135
  · exact B1357139
  · exact B1357143
  · exact B1357147
  · exact B1357151
  · exact B1357155
  · exact B1357159
  · exact B1357163
  · exact B1357167
  · exact B1357171
  · exact B1357175
  · exact B1357179
  · exact B1357183
  · exact B1357187
  · exact B1357191
  · exact B1357195
  · exact B1357199
  · exact B1357203
  · exact B1357207
  · exact B1357211
  · exact B1357215
  · exact B1357219
  · exact B1357223
  · exact B1357227
  · exact B1357231
  · exact B1357235
  · exact B1357239
  · exact B1357243
  · exact B1357247
  · exact B1357251
  · exact B1357255
  · exact B1357259
  · exact B1357263
  · exact B1357267
  · exact B1357271
  · exact B1357275
  · exact B1357279
  · exact B1357283
  · exact B1357287
  · exact B1357291
  · exact B1357295
  · exact B1357299
  · exact B1357303
  · exact B1357307
  · exact B1357311
  · exact B1357315
  · exact B1357319
  · exact B1357323
  · exact B1357327
  · exact B1357331
  · exact B1357335
  · exact B1357339
  · exact B1357343
  · exact B1357347
  · exact B1357351
  · exact B1357355
  · exact B1357359
  · exact B1357363
  · exact B1357367
  · exact B1357371
  · exact B1357375
  · exact B1357379
  · exact B1357383
  · exact B1357387
  · exact B1357391
  · exact B1357395
  · exact B1357399
  · exact B1357403
  · exact B1357407
  · exact B1357411
  · exact B1357415
  · exact B1357419
  · exact B1357423
  · exact B1357427
  · exact B1357431
  · exact B1357435
  · exact B1357439
  · exact B1357443
  · exact B1357447
  · exact B1357451
  · exact B1357455
  · exact B1357459
  · exact B1357463
  · exact B1357467
  · exact B1357471
  · exact B1357475
  · exact B1357479
  · exact B1357483
  · exact B1357487
  · exact B1357491
  · exact B1357495
  · exact B1357499
  · exact B1357503
  · exact B1357507
  · exact B1357511
  · exact B1357515
  · exact B1357519
  · exact B1357523
  · exact B1357527
  · exact B1357531
  · exact B1357535
  · exact B1357539
  · exact B1357543
  · exact B1357547
  · exact B1357551
  · exact B1357555
  · exact B1357559
  · exact B1357563
  · exact B1357567
  · exact B1357571
  · exact B1357575
  · exact B1357579
  · exact B1357583
  · exact B1357587
  · exact B1357591
  · exact B1357595
  · exact B1357599
  · exact B1357603
  · exact B1357607
  · exact B1357611
  · exact B1357615
  · exact B1357619
  · exact B1357623
  · exact B1357627
  · exact B1357631
  · exact B1357635
  · exact B1357639
  · exact B1357643
  · exact B1357647
  · exact B1357651
  · exact B1357655
  · exact B1357659
  · exact B1357663
  · exact B1357667
  · exact B1357671
  · exact B1357675
  · exact B1357679
  · exact B1357683
  · exact B1357687
  · exact B1357691
  · exact B1357695
  · exact B1357699
  · exact B1357703
  · exact B1357707
  · exact B1357711
  · exact B1357715
  · exact B1357719
  · exact B1357723
  · exact B1357727
  · exact B1357731
  · exact B1357735
  · exact B1357739
  · exact B1357743
  · exact B1357747
  · exact B1357751
  · exact B1357755
  · exact B1357759
  · exact B1357763
  · exact B1357767
  · exact B1357771
  · exact B1357775
  · exact B1357779
  · exact B1357783
  · exact B1357787
  · exact B1357791
  · exact B1357795
  · exact B1357799
  · exact B1357803
  · exact B1357807
  · exact B1357811
  · exact B1357815
  · exact B1357819
  · exact B1357823
  · exact B1357827
  · exact B1357831
  · exact B1357835
  · exact B1357839
  · exact B1357843
  · exact B1357847
  · exact B1357851
  · exact B1357855
  · exact B1357859
  · exact B1357863
  · exact B1357867
  · exact B1357871
  · exact B1357875
  · exact B1357879
  · exact B1357883
  · exact B1357887
  · exact B1357891
  · exact B1357895
  · exact B1357899
  · exact B1357903
  · exact B1357907
  · exact B1357911
  · exact B1357915
  · exact B1357919
  · exact B1357923
  · exact B1357927
  · exact B1357931
  · exact B1357935
  · exact B1357939
  · exact B1357943
  · exact B1357947
  · exact B1357951
  · exact B1357955
  · exact B1357959
  · exact B1357963
  · exact B1357967
  · exact B1357971
  · exact B1357975
  · exact B1357979
  · exact B1357983
  · exact B1357987
  · exact B1357991
  · exact B1357995
  · exact B1357999
  · exact B1358003
  · exact B1358007
  · exact B1358011
  · exact B1358015
  · exact B1358019
  · exact B1358023
  · exact B1358027
  · exact B1358031
  · exact B1358035
  · exact B1358039
  · exact B1358043
  · exact B1358047
  · exact B1358051
  · exact B1358055
  · exact B1358059
  · exact B1358063
  · exact B1358067
  · exact B1358071
  · exact B1358075
  · exact B1358079
  · exact B1358083
  · exact B1358087
  · exact B1358091
  · exact B1358095
  · exact B1358099
  · exact B1358103
  · exact B1358107
  · exact B1358111
  · exact B1358115
  · exact B1358119
  · exact B1358123
  · exact B1358127
  · exact B1358131
  · exact B1358135
  · exact B1358139
  · exact B1358143
  · exact B1358147
  · exact B1358151
  · exact B1358155
  · exact B1358159
  · exact B1358163
  · exact B1358167
  · exact B1358171
  · exact B1358175
  · exact B1358179
  · exact B1358183
  · exact B1358187
  · exact B1358191
  · exact B1358195
  · exact B1358199
  · exact B1358203
  · exact B1358207
  · exact B1358211
  · exact B1358215
  · exact B1358219
  · exact B1358223
  · exact B1358227
  · exact B1358231
  · exact B1358235
  · exact B1358239
  · exact B1358243
  · exact B1358247
  · exact B1358251
  · exact B1358255
  · exact B1358259
  · exact B1358263
  · exact B1358267
  · exact B1358271
  · exact B1358275
  · exact B1358279
  · exact B1358283
  · exact B1358287
  · exact B1358291
  · exact B1358295
  · exact B1358299
  · exact B1358303
  · exact B1358307
  · exact B1358311
  · exact B1358315
  · exact B1358319
  · exact B1358323
  · exact B1358327
  · exact B1358331
  · exact B1358335
  · exact B1358339
  · exact B1358343
  · exact B1358347
  · exact B1358351
  · exact B1358355
  · exact B1358359
  · exact B1358363
  · exact B1358367
  · exact B1358371
  · exact B1358375
  · exact B1358379
  · exact B1358383
  · exact B1358387
  · exact B1358391
  · exact B1358395
  · exact B1358399
  · exact B1358403
  · exact B1358407
  · exact B1358411
  · exact B1358415
  · exact B1358419
  · exact B1358423
  · exact B1358427
  · exact B1358431
  · exact B1358435
  · exact B1358439
  · exact B1358443
  · exact B1358447
  · exact B1358451
  · exact B1358455
  · exact B1358459
  · exact B1358463
  · exact B1358467
  · exact B1358471
  · exact B1358475
  · exact B1358479
  · exact B1358483
  · exact B1358487
  · exact B1358491
  · exact B1358495

theorem solution (m : ℕ) (hlo : 1356997 ≤ m) (hhi : m ≤ 1358497) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 339249 ≤ j := by omega
    have hj2 : j ≤ 339623 := by omega
    have hb : Blo 1356997 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
