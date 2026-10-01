-- Prove2me | solution 1 for syracuse_descends_range_2137435_2139435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:13.493564+00:00
-- url     : https://prove2.me/submissions/0a4afb04-b07b-4e4a-a511-673286a9cb1f

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

theorem B4057789 : Blo 2137435 4057789 := bbase (se 3 (by rfl) ⟨760835, by rfl⟩ : syracuseStep 4057789 = 1521671) (by norm_num)
theorem B5410385 : Blo 2137435 5410385 := bstep (se 2 (by rfl) ⟨2028894, by rfl⟩ : syracuseStep 5410385 = 4057789) B4057789
theorem B3606923 : Blo 2137435 3606923 := bstep (se 1 (by rfl) ⟨2705192, by rfl⟩ : syracuseStep 3606923 = 5410385) B5410385
theorem B2404615 : Blo 2137435 2404615 := bstep (se 1 (by rfl) ⟨1803461, by rfl⟩ : syracuseStep 2404615 = 3606923) B3606923
theorem B3206153 : Blo 2137435 3206153 := bstep (se 2 (by rfl) ⟨1202307, by rfl⟩ : syracuseStep 3206153 = 2404615) B2404615
theorem B2137435 : Blo 2137435 2137435 := bstep (se 1 (by rfl) ⟨1603076, by rfl⟩ : syracuseStep 2137435 = 3206153) B3206153
theorem B10820789 : Blo 2137435 10820789 := bbase (se 5 (by rfl) ⟨507224, by rfl⟩ : syracuseStep 10820789 = 1014449) (by norm_num)
theorem B7213859 : Blo 2137435 7213859 := bstep (se 1 (by rfl) ⟨5410394, by rfl⟩ : syracuseStep 7213859 = 10820789) B10820789
theorem B4809239 : Blo 2137435 4809239 := bstep (se 1 (by rfl) ⟨3606929, by rfl⟩ : syracuseStep 4809239 = 7213859) B7213859
theorem B3206159 : Blo 2137435 3206159 := bstep (se 1 (by rfl) ⟨2404619, by rfl⟩ : syracuseStep 3206159 = 4809239) B4809239
theorem B2137439 : Blo 2137435 2137439 := bstep (se 1 (by rfl) ⟨1603079, by rfl⟩ : syracuseStep 2137439 = 3206159) B3206159
theorem B3206165 : Blo 2137435 3206165 := bbase (se 6 (by rfl) ⟨75144, by rfl⟩ : syracuseStep 3206165 = 150289) (by norm_num)
theorem B2137443 : Blo 2137435 2137443 := bstep (se 1 (by rfl) ⟨1603082, by rfl⟩ : syracuseStep 2137443 = 3206165) B3206165
theorem B9254645 : Blo 2137435 9254645 := bbase (se 5 (by rfl) ⟨433811, by rfl⟩ : syracuseStep 9254645 = 867623) (by norm_num)
theorem B6169763 : Blo 2137435 6169763 := bstep (se 1 (by rfl) ⟨4627322, by rfl⟩ : syracuseStep 6169763 = 9254645) B9254645
theorem B4113175 : Blo 2137435 4113175 := bstep (se 1 (by rfl) ⟨3084881, by rfl⟩ : syracuseStep 4113175 = 6169763) B6169763
theorem B5484233 : Blo 2137435 5484233 := bstep (se 2 (by rfl) ⟨2056587, by rfl⟩ : syracuseStep 5484233 = 4113175) B4113175
theorem B14624621 : Blo 2137435 14624621 := bstep (se 3 (by rfl) ⟨2742116, by rfl⟩ : syracuseStep 14624621 = 5484233) B5484233
theorem B9749747 : Blo 2137435 9749747 := bstep (se 1 (by rfl) ⟨7312310, by rfl⟩ : syracuseStep 9749747 = 14624621) B14624621
theorem B6499831 : Blo 2137435 6499831 := bstep (se 1 (by rfl) ⟨4874873, by rfl⟩ : syracuseStep 6499831 = 9749747) B9749747
theorem B8666441 : Blo 2137435 8666441 := bstep (se 2 (by rfl) ⟨3249915, by rfl⟩ : syracuseStep 8666441 = 6499831) B6499831
theorem B5777627 : Blo 2137435 5777627 := bstep (se 1 (by rfl) ⟨4333220, by rfl⟩ : syracuseStep 5777627 = 8666441) B8666441
theorem B15407005 : Blo 2137435 15407005 := bstep (se 3 (by rfl) ⟨2888813, by rfl⟩ : syracuseStep 15407005 = 5777627) B5777627
theorem B20542673 : Blo 2137435 20542673 := bstep (se 2 (by rfl) ⟨7703502, by rfl⟩ : syracuseStep 20542673 = 15407005) B15407005
theorem B13695115 : Blo 2137435 13695115 := bstep (se 1 (by rfl) ⟨10271336, by rfl⟩ : syracuseStep 13695115 = 20542673) B20542673
theorem B18260153 : Blo 2137435 18260153 := bstep (se 2 (by rfl) ⟨6847557, by rfl⟩ : syracuseStep 18260153 = 13695115) B13695115
theorem B12173435 : Blo 2137435 12173435 := bstep (se 1 (by rfl) ⟨9130076, by rfl⟩ : syracuseStep 12173435 = 18260153) B18260153
theorem B8115623 : Blo 2137435 8115623 := bstep (se 1 (by rfl) ⟨6086717, by rfl⟩ : syracuseStep 8115623 = 12173435) B12173435
theorem B5410415 : Blo 2137435 5410415 := bstep (se 1 (by rfl) ⟨4057811, by rfl⟩ : syracuseStep 5410415 = 8115623) B8115623
theorem B3606943 : Blo 2137435 3606943 := bstep (se 1 (by rfl) ⟨2705207, by rfl⟩ : syracuseStep 3606943 = 5410415) B5410415
theorem B4809257 : Blo 2137435 4809257 := bstep (se 2 (by rfl) ⟨1803471, by rfl⟩ : syracuseStep 4809257 = 3606943) B3606943
theorem B3206171 : Blo 2137435 3206171 := bstep (se 1 (by rfl) ⟨2404628, by rfl⟩ : syracuseStep 3206171 = 4809257) B4809257
theorem B2137447 : Blo 2137435 2137447 := bstep (se 1 (by rfl) ⟨1603085, by rfl⟩ : syracuseStep 2137447 = 3206171) B3206171
theorem B2404633 : Blo 2137435 2404633 := bbase (se 2 (by rfl) ⟨901737, by rfl⟩ : syracuseStep 2404633 = 1803475) (by norm_num)
theorem B3206177 : Blo 2137435 3206177 := bstep (se 2 (by rfl) ⟨1202316, by rfl⟩ : syracuseStep 3206177 = 2404633) B2404633
theorem B2137451 : Blo 2137435 2137451 := bstep (se 1 (by rfl) ⟨1603088, by rfl⟩ : syracuseStep 2137451 = 3206177) B3206177
theorem B8115653 : Blo 2137435 8115653 := bbase (se 4 (by rfl) ⟨760842, by rfl⟩ : syracuseStep 8115653 = 1521685) (by norm_num)
theorem B5410435 : Blo 2137435 5410435 := bstep (se 1 (by rfl) ⟨4057826, by rfl⟩ : syracuseStep 5410435 = 8115653) B8115653
theorem B7213913 : Blo 2137435 7213913 := bstep (se 2 (by rfl) ⟨2705217, by rfl⟩ : syracuseStep 7213913 = 5410435) B5410435
theorem B4809275 : Blo 2137435 4809275 := bstep (se 1 (by rfl) ⟨3606956, by rfl⟩ : syracuseStep 4809275 = 7213913) B7213913
theorem B3206183 : Blo 2137435 3206183 := bstep (se 1 (by rfl) ⟨2404637, by rfl⟩ : syracuseStep 3206183 = 4809275) B4809275
theorem B2137455 : Blo 2137435 2137455 := bstep (se 1 (by rfl) ⟨1603091, by rfl⟩ : syracuseStep 2137455 = 3206183) B3206183
theorem B3206189 : Blo 2137435 3206189 := bbase (se 3 (by rfl) ⟨601160, by rfl⟩ : syracuseStep 3206189 = 1202321) (by norm_num)
theorem B2137459 : Blo 2137435 2137459 := bstep (se 1 (by rfl) ⟨1603094, by rfl⟩ : syracuseStep 2137459 = 3206189) B3206189
theorem B4809293 : Blo 2137435 4809293 := bbase (se 3 (by rfl) ⟨901742, by rfl⟩ : syracuseStep 4809293 = 1803485) (by norm_num)
theorem B3206195 : Blo 2137435 3206195 := bstep (se 1 (by rfl) ⟨2404646, by rfl⟩ : syracuseStep 3206195 = 4809293) B4809293
theorem B2137463 : Blo 2137435 2137463 := bstep (se 1 (by rfl) ⟨1603097, by rfl⟩ : syracuseStep 2137463 = 3206195) B3206195
theorem B2705233 : Blo 2137435 2705233 := bbase (se 2 (by rfl) ⟨1014462, by rfl⟩ : syracuseStep 2705233 = 2028925) (by norm_num)
theorem B3606977 : Blo 2137435 3606977 := bstep (se 2 (by rfl) ⟨1352616, by rfl⟩ : syracuseStep 3606977 = 2705233) B2705233
theorem B2404651 : Blo 2137435 2404651 := bstep (se 1 (by rfl) ⟨1803488, by rfl⟩ : syracuseStep 2404651 = 3606977) B3606977
theorem B3206201 : Blo 2137435 3206201 := bstep (se 2 (by rfl) ⟨1202325, by rfl⟩ : syracuseStep 3206201 = 2404651) B2404651
theorem B2137467 : Blo 2137435 2137467 := bstep (se 1 (by rfl) ⟨1603100, by rfl⟩ : syracuseStep 2137467 = 3206201) B3206201
theorem B2437465 : Blo 2137435 2437465 := bbase (se 2 (by rfl) ⟨914049, by rfl⟩ : syracuseStep 2437465 = 1828099) (by norm_num)
theorem B3249953 : Blo 2137435 3249953 := bstep (se 2 (by rfl) ⟨1218732, by rfl⟩ : syracuseStep 3249953 = 2437465) B2437465
theorem B2166635 : Blo 2137435 2166635 := bstep (se 1 (by rfl) ⟨1624976, by rfl⟩ : syracuseStep 2166635 = 3249953) B3249953
theorem B5777693 : Blo 2137435 5777693 := bstep (se 3 (by rfl) ⟨1083317, by rfl⟩ : syracuseStep 5777693 = 2166635) B2166635
theorem B3851795 : Blo 2137435 3851795 := bstep (se 1 (by rfl) ⟨2888846, by rfl⟩ : syracuseStep 3851795 = 5777693) B5777693
theorem B2567863 : Blo 2137435 2567863 := bstep (se 1 (by rfl) ⟨1925897, by rfl⟩ : syracuseStep 2567863 = 3851795) B3851795
theorem B3423817 : Blo 2137435 3423817 := bstep (se 2 (by rfl) ⟨1283931, by rfl⟩ : syracuseStep 3423817 = 2567863) B2567863
theorem B4565089 : Blo 2137435 4565089 := bstep (se 2 (by rfl) ⟨1711908, by rfl⟩ : syracuseStep 4565089 = 3423817) B3423817
theorem B24347141 : Blo 2137435 24347141 := bstep (se 4 (by rfl) ⟨2282544, by rfl⟩ : syracuseStep 24347141 = 4565089) B4565089
theorem B16231427 : Blo 2137435 16231427 := bstep (se 1 (by rfl) ⟨12173570, by rfl⟩ : syracuseStep 16231427 = 24347141) B24347141
theorem B10820951 : Blo 2137435 10820951 := bstep (se 1 (by rfl) ⟨8115713, by rfl⟩ : syracuseStep 10820951 = 16231427) B16231427
theorem B7213967 : Blo 2137435 7213967 := bstep (se 1 (by rfl) ⟨5410475, by rfl⟩ : syracuseStep 7213967 = 10820951) B10820951
theorem B4809311 : Blo 2137435 4809311 := bstep (se 1 (by rfl) ⟨3606983, by rfl⟩ : syracuseStep 4809311 = 7213967) B7213967
theorem B3206207 : Blo 2137435 3206207 := bstep (se 1 (by rfl) ⟨2404655, by rfl⟩ : syracuseStep 3206207 = 4809311) B4809311
theorem B2137471 : Blo 2137435 2137471 := bstep (se 1 (by rfl) ⟨1603103, by rfl⟩ : syracuseStep 2137471 = 3206207) B3206207
theorem B3206213 : Blo 2137435 3206213 := bbase (se 4 (by rfl) ⟨300582, by rfl⟩ : syracuseStep 3206213 = 601165) (by norm_num)
theorem B2137475 : Blo 2137435 2137475 := bstep (se 1 (by rfl) ⟨1603106, by rfl⟩ : syracuseStep 2137475 = 3206213) B3206213
theorem B3606997 : Blo 2137435 3606997 := bbase (se 7 (by rfl) ⟨42269, by rfl⟩ : syracuseStep 3606997 = 84539) (by norm_num)
theorem B4809329 : Blo 2137435 4809329 := bstep (se 2 (by rfl) ⟨1803498, by rfl⟩ : syracuseStep 4809329 = 3606997) B3606997
theorem B3206219 : Blo 2137435 3206219 := bstep (se 1 (by rfl) ⟨2404664, by rfl⟩ : syracuseStep 3206219 = 4809329) B4809329
theorem B2137479 : Blo 2137435 2137479 := bstep (se 1 (by rfl) ⟨1603109, by rfl⟩ : syracuseStep 2137479 = 3206219) B3206219
theorem B2404669 : Blo 2137435 2404669 := bbase (se 3 (by rfl) ⟨450875, by rfl⟩ : syracuseStep 2404669 = 901751) (by norm_num)
theorem B3206225 : Blo 2137435 3206225 := bstep (se 2 (by rfl) ⟨1202334, by rfl⟩ : syracuseStep 3206225 = 2404669) B2404669
theorem B2137483 : Blo 2137435 2137483 := bstep (se 1 (by rfl) ⟨1603112, by rfl⟩ : syracuseStep 2137483 = 3206225) B3206225
theorem B7214021 : Blo 2137435 7214021 := bbase (se 4 (by rfl) ⟨676314, by rfl⟩ : syracuseStep 7214021 = 1352629) (by norm_num)
theorem B4809347 : Blo 2137435 4809347 := bstep (se 1 (by rfl) ⟨3607010, by rfl⟩ : syracuseStep 4809347 = 7214021) B7214021
theorem B3206231 : Blo 2137435 3206231 := bstep (se 1 (by rfl) ⟨2404673, by rfl⟩ : syracuseStep 3206231 = 4809347) B4809347
theorem B2137487 : Blo 2137435 2137487 := bstep (se 1 (by rfl) ⟨1603115, by rfl⟩ : syracuseStep 2137487 = 3206231) B3206231
theorem B3206237 : Blo 2137435 3206237 := bbase (se 3 (by rfl) ⟨601169, by rfl⟩ : syracuseStep 3206237 = 1202339) (by norm_num)
theorem B2137491 : Blo 2137435 2137491 := bstep (se 1 (by rfl) ⟨1603118, by rfl⟩ : syracuseStep 2137491 = 3206237) B3206237
theorem B4809365 : Blo 2137435 4809365 := bbase (se 6 (by rfl) ⟨112719, by rfl⟩ : syracuseStep 4809365 = 225439) (by norm_num)
theorem B3206243 : Blo 2137435 3206243 := bstep (se 1 (by rfl) ⟨2404682, by rfl⟩ : syracuseStep 3206243 = 4809365) B4809365
theorem B2137495 : Blo 2137435 2137495 := bstep (se 1 (by rfl) ⟨1603121, by rfl⟩ : syracuseStep 2137495 = 3206243) B3206243
theorem B2888885 : Blo 2137435 2888885 := bbase (se 5 (by rfl) ⟨135416, by rfl⟩ : syracuseStep 2888885 = 270833) (by norm_num)
theorem B7703693 : Blo 2137435 7703693 := bstep (se 3 (by rfl) ⟨1444442, by rfl⟩ : syracuseStep 7703693 = 2888885) B2888885
theorem B5135795 : Blo 2137435 5135795 := bstep (se 1 (by rfl) ⟨3851846, by rfl⟩ : syracuseStep 5135795 = 7703693) B7703693
theorem B3423863 : Blo 2137435 3423863 := bstep (se 1 (by rfl) ⟨2567897, by rfl⟩ : syracuseStep 3423863 = 5135795) B5135795
theorem B2282575 : Blo 2137435 2282575 := bstep (se 1 (by rfl) ⟨1711931, by rfl⟩ : syracuseStep 2282575 = 3423863) B3423863
theorem B3043433 : Blo 2137435 3043433 := bstep (se 2 (by rfl) ⟨1141287, by rfl⟩ : syracuseStep 3043433 = 2282575) B2282575
theorem B8115821 : Blo 2137435 8115821 := bstep (se 3 (by rfl) ⟨1521716, by rfl⟩ : syracuseStep 8115821 = 3043433) B3043433
theorem B5410547 : Blo 2137435 5410547 := bstep (se 1 (by rfl) ⟨4057910, by rfl⟩ : syracuseStep 5410547 = 8115821) B8115821
theorem B3607031 : Blo 2137435 3607031 := bstep (se 1 (by rfl) ⟨2705273, by rfl⟩ : syracuseStep 3607031 = 5410547) B5410547
theorem B2404687 : Blo 2137435 2404687 := bstep (se 1 (by rfl) ⟨1803515, by rfl⟩ : syracuseStep 2404687 = 3607031) B3607031
theorem B3206249 : Blo 2137435 3206249 := bstep (se 2 (by rfl) ⟨1202343, by rfl⟩ : syracuseStep 3206249 = 2404687) B2404687
theorem B2137499 : Blo 2137435 2137499 := bstep (se 1 (by rfl) ⟨1603124, by rfl⟩ : syracuseStep 2137499 = 3206249) B3206249
theorem B10271605 : Blo 2137435 10271605 := bbase (se 5 (by rfl) ⟨481481, by rfl⟩ : syracuseStep 10271605 = 962963) (by norm_num)
theorem B13695473 : Blo 2137435 13695473 := bstep (se 2 (by rfl) ⟨5135802, by rfl⟩ : syracuseStep 13695473 = 10271605) B10271605
theorem B9130315 : Blo 2137435 9130315 := bstep (se 1 (by rfl) ⟨6847736, by rfl⟩ : syracuseStep 9130315 = 13695473) B13695473
theorem B12173753 : Blo 2137435 12173753 := bstep (se 2 (by rfl) ⟨4565157, by rfl⟩ : syracuseStep 12173753 = 9130315) B9130315
theorem B8115835 : Blo 2137435 8115835 := bstep (se 1 (by rfl) ⟨6086876, by rfl⟩ : syracuseStep 8115835 = 12173753) B12173753
theorem B10821113 : Blo 2137435 10821113 := bstep (se 2 (by rfl) ⟨4057917, by rfl⟩ : syracuseStep 10821113 = 8115835) B8115835
theorem B7214075 : Blo 2137435 7214075 := bstep (se 1 (by rfl) ⟨5410556, by rfl⟩ : syracuseStep 7214075 = 10821113) B10821113
theorem B4809383 : Blo 2137435 4809383 := bstep (se 1 (by rfl) ⟨3607037, by rfl⟩ : syracuseStep 4809383 = 7214075) B7214075
theorem B3206255 : Blo 2137435 3206255 := bstep (se 1 (by rfl) ⟨2404691, by rfl⟩ : syracuseStep 3206255 = 4809383) B4809383
theorem B2137503 : Blo 2137435 2137503 := bstep (se 1 (by rfl) ⟨1603127, by rfl⟩ : syracuseStep 2137503 = 3206255) B3206255
theorem B3206261 : Blo 2137435 3206261 := bbase (se 5 (by rfl) ⟨150293, by rfl⟩ : syracuseStep 3206261 = 300587) (by norm_num)
theorem B2137507 : Blo 2137435 2137507 := bstep (se 1 (by rfl) ⟨1603130, by rfl⟩ : syracuseStep 2137507 = 3206261) B3206261
theorem B4057933 : Blo 2137435 4057933 := bbase (se 3 (by rfl) ⟨760862, by rfl⟩ : syracuseStep 4057933 = 1521725) (by norm_num)
theorem B5410577 : Blo 2137435 5410577 := bstep (se 2 (by rfl) ⟨2028966, by rfl⟩ : syracuseStep 5410577 = 4057933) B4057933
theorem B3607051 : Blo 2137435 3607051 := bstep (se 1 (by rfl) ⟨2705288, by rfl⟩ : syracuseStep 3607051 = 5410577) B5410577
theorem B4809401 : Blo 2137435 4809401 := bstep (se 2 (by rfl) ⟨1803525, by rfl⟩ : syracuseStep 4809401 = 3607051) B3607051
theorem B3206267 : Blo 2137435 3206267 := bstep (se 1 (by rfl) ⟨2404700, by rfl⟩ : syracuseStep 3206267 = 4809401) B4809401
theorem B2137511 : Blo 2137435 2137511 := bstep (se 1 (by rfl) ⟨1603133, by rfl⟩ : syracuseStep 2137511 = 3206267) B3206267
theorem B2404705 : Blo 2137435 2404705 := bbase (se 2 (by rfl) ⟨901764, by rfl⟩ : syracuseStep 2404705 = 1803529) (by norm_num)
theorem B3206273 : Blo 2137435 3206273 := bstep (se 2 (by rfl) ⟨1202352, by rfl⟩ : syracuseStep 3206273 = 2404705) B2404705
theorem B2137515 : Blo 2137435 2137515 := bstep (se 1 (by rfl) ⟨1603136, by rfl⟩ : syracuseStep 2137515 = 3206273) B3206273
theorem B5410597 : Blo 2137435 5410597 := bbase (se 4 (by rfl) ⟨507243, by rfl⟩ : syracuseStep 5410597 = 1014487) (by norm_num)
theorem B7214129 : Blo 2137435 7214129 := bstep (se 2 (by rfl) ⟨2705298, by rfl⟩ : syracuseStep 7214129 = 5410597) B5410597
theorem B4809419 : Blo 2137435 4809419 := bstep (se 1 (by rfl) ⟨3607064, by rfl⟩ : syracuseStep 4809419 = 7214129) B7214129
theorem B3206279 : Blo 2137435 3206279 := bstep (se 1 (by rfl) ⟨2404709, by rfl⟩ : syracuseStep 3206279 = 4809419) B4809419
theorem B2137519 : Blo 2137435 2137519 := bstep (se 1 (by rfl) ⟨1603139, by rfl⟩ : syracuseStep 2137519 = 3206279) B3206279
theorem B3206285 : Blo 2137435 3206285 := bbase (se 3 (by rfl) ⟨601178, by rfl⟩ : syracuseStep 3206285 = 1202357) (by norm_num)
theorem B2137523 : Blo 2137435 2137523 := bstep (se 1 (by rfl) ⟨1603142, by rfl⟩ : syracuseStep 2137523 = 3206285) B3206285
theorem B4809437 : Blo 2137435 4809437 := bbase (se 3 (by rfl) ⟨901769, by rfl⟩ : syracuseStep 4809437 = 1803539) (by norm_num)
theorem B3206291 : Blo 2137435 3206291 := bstep (se 1 (by rfl) ⟨2404718, by rfl⟩ : syracuseStep 3206291 = 4809437) B4809437
theorem B2137527 : Blo 2137435 2137527 := bstep (se 1 (by rfl) ⟨1603145, by rfl⟩ : syracuseStep 2137527 = 3206291) B3206291
theorem B3607085 : Blo 2137435 3607085 := bbase (se 3 (by rfl) ⟨676328, by rfl⟩ : syracuseStep 3607085 = 1352657) (by norm_num)
theorem B2404723 : Blo 2137435 2404723 := bstep (se 1 (by rfl) ⟨1803542, by rfl⟩ : syracuseStep 2404723 = 3607085) B3607085
theorem B3206297 : Blo 2137435 3206297 := bstep (se 2 (by rfl) ⟨1202361, by rfl⟩ : syracuseStep 3206297 = 2404723) B2404723
theorem B2137531 : Blo 2137435 2137531 := bstep (se 1 (by rfl) ⟨1603148, by rfl⟩ : syracuseStep 2137531 = 3206297) B3206297
theorem B2742229 : Blo 2137435 2742229 := bbase (se 7 (by rfl) ⟨32135, by rfl⟩ : syracuseStep 2742229 = 64271) (by norm_num)
theorem B3656305 : Blo 2137435 3656305 := bstep (se 2 (by rfl) ⟨1371114, by rfl⟩ : syracuseStep 3656305 = 2742229) B2742229
theorem B4875073 : Blo 2137435 4875073 := bstep (se 2 (by rfl) ⟨1828152, by rfl⟩ : syracuseStep 4875073 = 3656305) B3656305
theorem B26000389 : Blo 2137435 26000389 := bstep (se 4 (by rfl) ⟨2437536, by rfl⟩ : syracuseStep 26000389 = 4875073) B4875073
theorem B34667185 : Blo 2137435 34667185 := bstep (se 2 (by rfl) ⟨13000194, by rfl⟩ : syracuseStep 34667185 = 26000389) B26000389
theorem B46222913 : Blo 2137435 46222913 := bstep (se 2 (by rfl) ⟨17333592, by rfl⟩ : syracuseStep 46222913 = 34667185) B34667185
theorem B30815275 : Blo 2137435 30815275 := bstep (se 1 (by rfl) ⟨23111456, by rfl⟩ : syracuseStep 30815275 = 46222913) B46222913
theorem B41087033 : Blo 2137435 41087033 := bstep (se 2 (by rfl) ⟨15407637, by rfl⟩ : syracuseStep 41087033 = 30815275) B30815275
theorem B27391355 : Blo 2137435 27391355 := bstep (se 1 (by rfl) ⟨20543516, by rfl⟩ : syracuseStep 27391355 = 41087033) B41087033
theorem B18260903 : Blo 2137435 18260903 := bstep (se 1 (by rfl) ⟨13695677, by rfl⟩ : syracuseStep 18260903 = 27391355) B27391355
theorem B12173935 : Blo 2137435 12173935 := bstep (se 1 (by rfl) ⟨9130451, by rfl⟩ : syracuseStep 12173935 = 18260903) B18260903
theorem B16231913 : Blo 2137435 16231913 := bstep (se 2 (by rfl) ⟨6086967, by rfl⟩ : syracuseStep 16231913 = 12173935) B12173935
theorem B10821275 : Blo 2137435 10821275 := bstep (se 1 (by rfl) ⟨8115956, by rfl⟩ : syracuseStep 10821275 = 16231913) B16231913
theorem B7214183 : Blo 2137435 7214183 := bstep (se 1 (by rfl) ⟨5410637, by rfl⟩ : syracuseStep 7214183 = 10821275) B10821275
theorem B4809455 : Blo 2137435 4809455 := bstep (se 1 (by rfl) ⟨3607091, by rfl⟩ : syracuseStep 4809455 = 7214183) B7214183
theorem B3206303 : Blo 2137435 3206303 := bstep (se 1 (by rfl) ⟨2404727, by rfl⟩ : syracuseStep 3206303 = 4809455) B4809455
theorem B2137535 : Blo 2137435 2137535 := bstep (se 1 (by rfl) ⟨1603151, by rfl⟩ : syracuseStep 2137535 = 3206303) B3206303
theorem B3206309 : Blo 2137435 3206309 := bbase (se 4 (by rfl) ⟨300591, by rfl⟩ : syracuseStep 3206309 = 601183) (by norm_num)
theorem B2137539 : Blo 2137435 2137539 := bstep (se 1 (by rfl) ⟨1603154, by rfl⟩ : syracuseStep 2137539 = 3206309) B3206309
theorem B2705329 : Blo 2137435 2705329 := bbase (se 2 (by rfl) ⟨1014498, by rfl⟩ : syracuseStep 2705329 = 2028997) (by norm_num)
theorem B3607105 : Blo 2137435 3607105 := bstep (se 2 (by rfl) ⟨1352664, by rfl⟩ : syracuseStep 3607105 = 2705329) B2705329
theorem B4809473 : Blo 2137435 4809473 := bstep (se 2 (by rfl) ⟨1803552, by rfl⟩ : syracuseStep 4809473 = 3607105) B3607105
theorem B3206315 : Blo 2137435 3206315 := bstep (se 1 (by rfl) ⟨2404736, by rfl⟩ : syracuseStep 3206315 = 4809473) B4809473
theorem B2137543 : Blo 2137435 2137543 := bstep (se 1 (by rfl) ⟨1603157, by rfl⟩ : syracuseStep 2137543 = 3206315) B3206315
theorem B2404741 : Blo 2137435 2404741 := bbase (se 4 (by rfl) ⟨225444, by rfl⟩ : syracuseStep 2404741 = 450889) (by norm_num)
theorem B3206321 : Blo 2137435 3206321 := bstep (se 2 (by rfl) ⟨1202370, by rfl⟩ : syracuseStep 3206321 = 2404741) B2404741
theorem B2137547 : Blo 2137435 2137547 := bstep (se 1 (by rfl) ⟨1603160, by rfl⟩ : syracuseStep 2137547 = 3206321) B3206321
theorem B4565261 : Blo 2137435 4565261 := bbase (se 3 (by rfl) ⟨855986, by rfl⟩ : syracuseStep 4565261 = 1711973) (by norm_num)
theorem B3043507 : Blo 2137435 3043507 := bstep (se 1 (by rfl) ⟨2282630, by rfl⟩ : syracuseStep 3043507 = 4565261) B4565261
theorem B4058009 : Blo 2137435 4058009 := bstep (se 2 (by rfl) ⟨1521753, by rfl⟩ : syracuseStep 4058009 = 3043507) B3043507
theorem B2705339 : Blo 2137435 2705339 := bstep (se 1 (by rfl) ⟨2029004, by rfl⟩ : syracuseStep 2705339 = 4058009) B4058009
theorem B7214237 : Blo 2137435 7214237 := bstep (se 3 (by rfl) ⟨1352669, by rfl⟩ : syracuseStep 7214237 = 2705339) B2705339
theorem B4809491 : Blo 2137435 4809491 := bstep (se 1 (by rfl) ⟨3607118, by rfl⟩ : syracuseStep 4809491 = 7214237) B7214237
theorem B3206327 : Blo 2137435 3206327 := bstep (se 1 (by rfl) ⟨2404745, by rfl⟩ : syracuseStep 3206327 = 4809491) B4809491
theorem B2137551 : Blo 2137435 2137551 := bstep (se 1 (by rfl) ⟨1603163, by rfl⟩ : syracuseStep 2137551 = 3206327) B3206327
theorem B3206333 : Blo 2137435 3206333 := bbase (se 3 (by rfl) ⟨601187, by rfl⟩ : syracuseStep 3206333 = 1202375) (by norm_num)
theorem B2137555 : Blo 2137435 2137555 := bstep (se 1 (by rfl) ⟨1603166, by rfl⟩ : syracuseStep 2137555 = 3206333) B3206333
theorem B4809509 : Blo 2137435 4809509 := bbase (se 4 (by rfl) ⟨450891, by rfl⟩ : syracuseStep 4809509 = 901783) (by norm_num)
theorem B3206339 : Blo 2137435 3206339 := bstep (se 1 (by rfl) ⟨2404754, by rfl⟩ : syracuseStep 3206339 = 4809509) B4809509
theorem B2137559 : Blo 2137435 2137559 := bstep (se 1 (by rfl) ⟨1603169, by rfl⟩ : syracuseStep 2137559 = 3206339) B3206339
theorem B5410709 : Blo 2137435 5410709 := bbase (se 6 (by rfl) ⟨126813, by rfl⟩ : syracuseStep 5410709 = 253627) (by norm_num)
theorem B3607139 : Blo 2137435 3607139 := bstep (se 1 (by rfl) ⟨2705354, by rfl⟩ : syracuseStep 3607139 = 5410709) B5410709
theorem B2404759 : Blo 2137435 2404759 := bstep (se 1 (by rfl) ⟨1803569, by rfl⟩ : syracuseStep 2404759 = 3607139) B3607139
theorem B3206345 : Blo 2137435 3206345 := bstep (se 2 (by rfl) ⟨1202379, by rfl⟩ : syracuseStep 3206345 = 2404759) B2404759
theorem B2137563 : Blo 2137435 2137563 := bstep (se 1 (by rfl) ⟨1603172, by rfl⟩ : syracuseStep 2137563 = 3206345) B3206345
theorem B5135957 : Blo 2137435 5135957 := bbase (se 8 (by rfl) ⟨30093, by rfl⟩ : syracuseStep 5135957 = 60187) (by norm_num)
theorem B3423971 : Blo 2137435 3423971 := bstep (se 1 (by rfl) ⟨2567978, by rfl⟩ : syracuseStep 3423971 = 5135957) B5135957
theorem B9130589 : Blo 2137435 9130589 := bstep (se 3 (by rfl) ⟨1711985, by rfl⟩ : syracuseStep 9130589 = 3423971) B3423971
theorem B6087059 : Blo 2137435 6087059 := bstep (se 1 (by rfl) ⟨4565294, by rfl⟩ : syracuseStep 6087059 = 9130589) B9130589
theorem B4058039 : Blo 2137435 4058039 := bstep (se 1 (by rfl) ⟨3043529, by rfl⟩ : syracuseStep 4058039 = 6087059) B6087059
theorem B10821437 : Blo 2137435 10821437 := bstep (se 3 (by rfl) ⟨2029019, by rfl⟩ : syracuseStep 10821437 = 4058039) B4058039
theorem B7214291 : Blo 2137435 7214291 := bstep (se 1 (by rfl) ⟨5410718, by rfl⟩ : syracuseStep 7214291 = 10821437) B10821437
theorem B4809527 : Blo 2137435 4809527 := bstep (se 1 (by rfl) ⟨3607145, by rfl⟩ : syracuseStep 4809527 = 7214291) B7214291
theorem B3206351 : Blo 2137435 3206351 := bstep (se 1 (by rfl) ⟨2404763, by rfl⟩ : syracuseStep 3206351 = 4809527) B4809527
theorem B2137567 : Blo 2137435 2137567 := bstep (se 1 (by rfl) ⟨1603175, by rfl⟩ : syracuseStep 2137567 = 3206351) B3206351
theorem B3206357 : Blo 2137435 3206357 := bbase (se 7 (by rfl) ⟨37574, by rfl⟩ : syracuseStep 3206357 = 75149) (by norm_num)
theorem B2137571 : Blo 2137435 2137571 := bstep (se 1 (by rfl) ⟨1603178, by rfl⟩ : syracuseStep 2137571 = 3206357) B3206357
theorem B3043541 : Blo 2137435 3043541 := bbase (se 7 (by rfl) ⟨35666, by rfl⟩ : syracuseStep 3043541 = 71333) (by norm_num)
theorem B8116109 : Blo 2137435 8116109 := bstep (se 3 (by rfl) ⟨1521770, by rfl⟩ : syracuseStep 8116109 = 3043541) B3043541
theorem B5410739 : Blo 2137435 5410739 := bstep (se 1 (by rfl) ⟨4058054, by rfl⟩ : syracuseStep 5410739 = 8116109) B8116109
theorem B3607159 : Blo 2137435 3607159 := bstep (se 1 (by rfl) ⟨2705369, by rfl⟩ : syracuseStep 3607159 = 5410739) B5410739
theorem B4809545 : Blo 2137435 4809545 := bstep (se 2 (by rfl) ⟨1803579, by rfl⟩ : syracuseStep 4809545 = 3607159) B3607159
theorem B3206363 : Blo 2137435 3206363 := bstep (se 1 (by rfl) ⟨2404772, by rfl⟩ : syracuseStep 3206363 = 4809545) B4809545
theorem B2137575 : Blo 2137435 2137575 := bstep (se 1 (by rfl) ⟨1603181, by rfl⟩ : syracuseStep 2137575 = 3206363) B3206363
theorem B2404777 : Blo 2137435 2404777 := bbase (se 2 (by rfl) ⟨901791, by rfl⟩ : syracuseStep 2404777 = 1803583) (by norm_num)
theorem B3206369 : Blo 2137435 3206369 := bstep (se 2 (by rfl) ⟨1202388, by rfl⟩ : syracuseStep 3206369 = 2404777) B2404777
theorem B2137579 : Blo 2137435 2137579 := bstep (se 1 (by rfl) ⟨1603184, by rfl⟩ : syracuseStep 2137579 = 3206369) B3206369
theorem B6500245 : Blo 2137435 6500245 := bbase (se 6 (by rfl) ⟨152349, by rfl⟩ : syracuseStep 6500245 = 304699) (by norm_num)
theorem B8666993 : Blo 2137435 8666993 := bstep (se 2 (by rfl) ⟨3250122, by rfl⟩ : syracuseStep 8666993 = 6500245) B6500245
theorem B5777995 : Blo 2137435 5777995 := bstep (se 1 (by rfl) ⟨4333496, by rfl⟩ : syracuseStep 5777995 = 8666993) B8666993
theorem B7703993 : Blo 2137435 7703993 := bstep (se 2 (by rfl) ⟨2888997, by rfl⟩ : syracuseStep 7703993 = 5777995) B5777995
theorem B5135995 : Blo 2137435 5135995 := bstep (se 1 (by rfl) ⟨3851996, by rfl⟩ : syracuseStep 5135995 = 7703993) B7703993
theorem B6847993 : Blo 2137435 6847993 := bstep (se 2 (by rfl) ⟨2567997, by rfl⟩ : syracuseStep 6847993 = 5135995) B5135995
theorem B9130657 : Blo 2137435 9130657 := bstep (se 2 (by rfl) ⟨3423996, by rfl⟩ : syracuseStep 9130657 = 6847993) B6847993
theorem B12174209 : Blo 2137435 12174209 := bstep (se 2 (by rfl) ⟨4565328, by rfl⟩ : syracuseStep 12174209 = 9130657) B9130657
theorem B8116139 : Blo 2137435 8116139 := bstep (se 1 (by rfl) ⟨6087104, by rfl⟩ : syracuseStep 8116139 = 12174209) B12174209
theorem B5410759 : Blo 2137435 5410759 := bstep (se 1 (by rfl) ⟨4058069, by rfl⟩ : syracuseStep 5410759 = 8116139) B8116139
theorem B7214345 : Blo 2137435 7214345 := bstep (se 2 (by rfl) ⟨2705379, by rfl⟩ : syracuseStep 7214345 = 5410759) B5410759
theorem B4809563 : Blo 2137435 4809563 := bstep (se 1 (by rfl) ⟨3607172, by rfl⟩ : syracuseStep 4809563 = 7214345) B7214345
theorem B3206375 : Blo 2137435 3206375 := bstep (se 1 (by rfl) ⟨2404781, by rfl⟩ : syracuseStep 3206375 = 4809563) B4809563
theorem B2137583 : Blo 2137435 2137583 := bstep (se 1 (by rfl) ⟨1603187, by rfl⟩ : syracuseStep 2137583 = 3206375) B3206375
theorem B3206381 : Blo 2137435 3206381 := bbase (se 3 (by rfl) ⟨601196, by rfl⟩ : syracuseStep 3206381 = 1202393) (by norm_num)
theorem B2137587 : Blo 2137435 2137587 := bstep (se 1 (by rfl) ⟨1603190, by rfl⟩ : syracuseStep 2137587 = 3206381) B3206381
theorem B4809581 : Blo 2137435 4809581 := bbase (se 3 (by rfl) ⟨901796, by rfl⟩ : syracuseStep 4809581 = 1803593) (by norm_num)
theorem B3206387 : Blo 2137435 3206387 := bstep (se 1 (by rfl) ⟨2404790, by rfl⟩ : syracuseStep 3206387 = 4809581) B4809581
theorem B2137591 : Blo 2137435 2137591 := bstep (se 1 (by rfl) ⟨1603193, by rfl⟩ : syracuseStep 2137591 = 3206387) B3206387
theorem B4058093 : Blo 2137435 4058093 := bbase (se 3 (by rfl) ⟨760892, by rfl⟩ : syracuseStep 4058093 = 1521785) (by norm_num)
theorem B2705395 : Blo 2137435 2705395 := bstep (se 1 (by rfl) ⟨2029046, by rfl⟩ : syracuseStep 2705395 = 4058093) B4058093
theorem B3607193 : Blo 2137435 3607193 := bstep (se 2 (by rfl) ⟨1352697, by rfl⟩ : syracuseStep 3607193 = 2705395) B2705395
theorem B2404795 : Blo 2137435 2404795 := bstep (se 1 (by rfl) ⟨1803596, by rfl⟩ : syracuseStep 2404795 = 3607193) B3607193
theorem B3206393 : Blo 2137435 3206393 := bstep (se 2 (by rfl) ⟨1202397, by rfl⟩ : syracuseStep 3206393 = 2404795) B2404795
theorem B2137595 : Blo 2137435 2137595 := bstep (se 1 (by rfl) ⟨1603196, by rfl⟩ : syracuseStep 2137595 = 3206393) B3206393
theorem B5778037 : Blo 2137435 5778037 := bbase (se 5 (by rfl) ⟨270845, by rfl⟩ : syracuseStep 5778037 = 541691) (by norm_num)
theorem B30816197 : Blo 2137435 30816197 := bstep (se 4 (by rfl) ⟨2889018, by rfl⟩ : syracuseStep 30816197 = 5778037) B5778037
theorem B20544131 : Blo 2137435 20544131 := bstep (se 1 (by rfl) ⟨15408098, by rfl⟩ : syracuseStep 20544131 = 30816197) B30816197
theorem B54784349 : Blo 2137435 54784349 := bstep (se 3 (by rfl) ⟨10272065, by rfl⟩ : syracuseStep 54784349 = 20544131) B20544131
theorem B36522899 : Blo 2137435 36522899 := bstep (se 1 (by rfl) ⟨27392174, by rfl⟩ : syracuseStep 36522899 = 54784349) B54784349
theorem B24348599 : Blo 2137435 24348599 := bstep (se 1 (by rfl) ⟨18261449, by rfl⟩ : syracuseStep 24348599 = 36522899) B36522899
theorem B16232399 : Blo 2137435 16232399 := bstep (se 1 (by rfl) ⟨12174299, by rfl⟩ : syracuseStep 16232399 = 24348599) B24348599
theorem B10821599 : Blo 2137435 10821599 := bstep (se 1 (by rfl) ⟨8116199, by rfl⟩ : syracuseStep 10821599 = 16232399) B16232399
theorem B7214399 : Blo 2137435 7214399 := bstep (se 1 (by rfl) ⟨5410799, by rfl⟩ : syracuseStep 7214399 = 10821599) B10821599
theorem B4809599 : Blo 2137435 4809599 := bstep (se 1 (by rfl) ⟨3607199, by rfl⟩ : syracuseStep 4809599 = 7214399) B7214399
theorem B3206399 : Blo 2137435 3206399 := bstep (se 1 (by rfl) ⟨2404799, by rfl⟩ : syracuseStep 3206399 = 4809599) B4809599
theorem B2137599 : Blo 2137435 2137599 := bstep (se 1 (by rfl) ⟨1603199, by rfl⟩ : syracuseStep 2137599 = 3206399) B3206399
theorem B3206405 : Blo 2137435 3206405 := bbase (se 4 (by rfl) ⟨300600, by rfl⟩ : syracuseStep 3206405 = 601201) (by norm_num)
theorem B2137603 : Blo 2137435 2137603 := bstep (se 1 (by rfl) ⟨1603202, by rfl⟩ : syracuseStep 2137603 = 3206405) B3206405
theorem B3607213 : Blo 2137435 3607213 := bbase (se 3 (by rfl) ⟨676352, by rfl⟩ : syracuseStep 3607213 = 1352705) (by norm_num)
theorem B4809617 : Blo 2137435 4809617 := bstep (se 2 (by rfl) ⟨1803606, by rfl⟩ : syracuseStep 4809617 = 3607213) B3607213
theorem B3206411 : Blo 2137435 3206411 := bstep (se 1 (by rfl) ⟨2404808, by rfl⟩ : syracuseStep 3206411 = 4809617) B4809617
theorem B2137607 : Blo 2137435 2137607 := bstep (se 1 (by rfl) ⟨1603205, by rfl⟩ : syracuseStep 2137607 = 3206411) B3206411
theorem B2404813 : Blo 2137435 2404813 := bbase (se 3 (by rfl) ⟨450902, by rfl⟩ : syracuseStep 2404813 = 901805) (by norm_num)
theorem B3206417 : Blo 2137435 3206417 := bstep (se 2 (by rfl) ⟨1202406, by rfl⟩ : syracuseStep 3206417 = 2404813) B2404813
theorem B2137611 : Blo 2137435 2137611 := bstep (se 1 (by rfl) ⟨1603208, by rfl⟩ : syracuseStep 2137611 = 3206417) B3206417
theorem B7214453 : Blo 2137435 7214453 := bbase (se 5 (by rfl) ⟨338177, by rfl⟩ : syracuseStep 7214453 = 676355) (by norm_num)
theorem B4809635 : Blo 2137435 4809635 := bstep (se 1 (by rfl) ⟨3607226, by rfl⟩ : syracuseStep 4809635 = 7214453) B7214453
theorem B3206423 : Blo 2137435 3206423 := bstep (se 1 (by rfl) ⟨2404817, by rfl⟩ : syracuseStep 3206423 = 4809635) B4809635
theorem B2137615 : Blo 2137435 2137615 := bstep (se 1 (by rfl) ⟨1603211, by rfl⟩ : syracuseStep 2137615 = 3206423) B3206423
theorem B3206429 : Blo 2137435 3206429 := bbase (se 3 (by rfl) ⟨601205, by rfl⟩ : syracuseStep 3206429 = 1202411) (by norm_num)
theorem B2137619 : Blo 2137435 2137619 := bstep (se 1 (by rfl) ⟨1603214, by rfl⟩ : syracuseStep 2137619 = 3206429) B3206429
theorem B4809653 : Blo 2137435 4809653 := bbase (se 5 (by rfl) ⟨225452, by rfl⟩ : syracuseStep 4809653 = 450905) (by norm_num)
theorem B3206435 : Blo 2137435 3206435 := bstep (se 1 (by rfl) ⟨2404826, by rfl⟩ : syracuseStep 3206435 = 4809653) B4809653
theorem B2137623 : Blo 2137435 2137623 := bstep (se 1 (by rfl) ⟨1603217, by rfl⟩ : syracuseStep 2137623 = 3206435) B3206435
theorem B2166793 : Blo 2137435 2166793 := bbase (se 2 (by rfl) ⟨812547, by rfl⟩ : syracuseStep 2166793 = 1625095) (by norm_num)
theorem B11556229 : Blo 2137435 11556229 := bstep (se 4 (by rfl) ⟨1083396, by rfl⟩ : syracuseStep 11556229 = 2166793) B2166793
theorem B15408305 : Blo 2137435 15408305 := bstep (se 2 (by rfl) ⟨5778114, by rfl⟩ : syracuseStep 15408305 = 11556229) B11556229
theorem B10272203 : Blo 2137435 10272203 := bstep (se 1 (by rfl) ⟨7704152, by rfl⟩ : syracuseStep 10272203 = 15408305) B15408305
theorem B6848135 : Blo 2137435 6848135 := bstep (se 1 (by rfl) ⟨5136101, by rfl⟩ : syracuseStep 6848135 = 10272203) B10272203
theorem B4565423 : Blo 2137435 4565423 := bstep (se 1 (by rfl) ⟨3424067, by rfl⟩ : syracuseStep 4565423 = 6848135) B6848135
theorem B12174461 : Blo 2137435 12174461 := bstep (se 3 (by rfl) ⟨2282711, by rfl⟩ : syracuseStep 12174461 = 4565423) B4565423
theorem B8116307 : Blo 2137435 8116307 := bstep (se 1 (by rfl) ⟨6087230, by rfl⟩ : syracuseStep 8116307 = 12174461) B12174461
theorem B5410871 : Blo 2137435 5410871 := bstep (se 1 (by rfl) ⟨4058153, by rfl⟩ : syracuseStep 5410871 = 8116307) B8116307
theorem B3607247 : Blo 2137435 3607247 := bstep (se 1 (by rfl) ⟨2705435, by rfl⟩ : syracuseStep 3607247 = 5410871) B5410871
theorem B2404831 : Blo 2137435 2404831 := bstep (se 1 (by rfl) ⟨1803623, by rfl⟩ : syracuseStep 2404831 = 3607247) B3607247
theorem B3206441 : Blo 2137435 3206441 := bstep (se 2 (by rfl) ⟨1202415, by rfl⟩ : syracuseStep 3206441 = 2404831) B2404831
theorem B2137627 : Blo 2137435 2137627 := bstep (se 1 (by rfl) ⟨1603220, by rfl⟩ : syracuseStep 2137627 = 3206441) B3206441
theorem B2166797 : Blo 2137435 2166797 := bbase (se 3 (by rfl) ⟨406274, by rfl⟩ : syracuseStep 2166797 = 812549) (by norm_num)
theorem B5778125 : Blo 2137435 5778125 := bstep (se 3 (by rfl) ⟨1083398, by rfl⟩ : syracuseStep 5778125 = 2166797) B2166797
theorem B3852083 : Blo 2137435 3852083 := bstep (se 1 (by rfl) ⟨2889062, by rfl⟩ : syracuseStep 3852083 = 5778125) B5778125
theorem B10272221 : Blo 2137435 10272221 := bstep (se 3 (by rfl) ⟨1926041, by rfl⟩ : syracuseStep 10272221 = 3852083) B3852083
theorem B6848147 : Blo 2137435 6848147 := bstep (se 1 (by rfl) ⟨5136110, by rfl⟩ : syracuseStep 6848147 = 10272221) B10272221
theorem B4565431 : Blo 2137435 4565431 := bstep (se 1 (by rfl) ⟨3424073, by rfl⟩ : syracuseStep 4565431 = 6848147) B6848147
theorem B6087241 : Blo 2137435 6087241 := bstep (se 2 (by rfl) ⟨2282715, by rfl⟩ : syracuseStep 6087241 = 4565431) B4565431
theorem B8116321 : Blo 2137435 8116321 := bstep (se 2 (by rfl) ⟨3043620, by rfl⟩ : syracuseStep 8116321 = 6087241) B6087241
theorem B10821761 : Blo 2137435 10821761 := bstep (se 2 (by rfl) ⟨4058160, by rfl⟩ : syracuseStep 10821761 = 8116321) B8116321
theorem B7214507 : Blo 2137435 7214507 := bstep (se 1 (by rfl) ⟨5410880, by rfl⟩ : syracuseStep 7214507 = 10821761) B10821761
theorem B4809671 : Blo 2137435 4809671 := bstep (se 1 (by rfl) ⟨3607253, by rfl⟩ : syracuseStep 4809671 = 7214507) B7214507
theorem B3206447 : Blo 2137435 3206447 := bstep (se 1 (by rfl) ⟨2404835, by rfl⟩ : syracuseStep 3206447 = 4809671) B4809671
theorem B2137631 : Blo 2137435 2137631 := bstep (se 1 (by rfl) ⟨1603223, by rfl⟩ : syracuseStep 2137631 = 3206447) B3206447
theorem B3206453 : Blo 2137435 3206453 := bbase (se 5 (by rfl) ⟨150302, by rfl⟩ : syracuseStep 3206453 = 300605) (by norm_num)
theorem B2137635 : Blo 2137435 2137635 := bstep (se 1 (by rfl) ⟨1603226, by rfl⟩ : syracuseStep 2137635 = 3206453) B3206453
theorem B5410901 : Blo 2137435 5410901 := bbase (se 8 (by rfl) ⟨31704, by rfl⟩ : syracuseStep 5410901 = 63409) (by norm_num)
theorem B3607267 : Blo 2137435 3607267 := bstep (se 1 (by rfl) ⟨2705450, by rfl⟩ : syracuseStep 3607267 = 5410901) B5410901
theorem B4809689 : Blo 2137435 4809689 := bstep (se 2 (by rfl) ⟨1803633, by rfl⟩ : syracuseStep 4809689 = 3607267) B3607267
theorem B3206459 : Blo 2137435 3206459 := bstep (se 1 (by rfl) ⟨2404844, by rfl⟩ : syracuseStep 3206459 = 4809689) B4809689
theorem B2137639 : Blo 2137435 2137639 := bstep (se 1 (by rfl) ⟨1603229, by rfl⟩ : syracuseStep 2137639 = 3206459) B3206459
theorem B2404849 : Blo 2137435 2404849 := bbase (se 2 (by rfl) ⟨901818, by rfl⟩ : syracuseStep 2404849 = 1803637) (by norm_num)
theorem B3206465 : Blo 2137435 3206465 := bstep (se 2 (by rfl) ⟨1202424, by rfl⟩ : syracuseStep 3206465 = 2404849) B2404849
theorem B2137643 : Blo 2137435 2137643 := bstep (se 1 (by rfl) ⟨1603232, by rfl⟩ : syracuseStep 2137643 = 3206465) B3206465
theorem B5136149 : Blo 2137435 5136149 := bbase (se 6 (by rfl) ⟨120378, by rfl⟩ : syracuseStep 5136149 = 240757) (by norm_num)
theorem B13696397 : Blo 2137435 13696397 := bstep (se 3 (by rfl) ⟨2568074, by rfl⟩ : syracuseStep 13696397 = 5136149) B5136149
theorem B9130931 : Blo 2137435 9130931 := bstep (se 1 (by rfl) ⟨6848198, by rfl⟩ : syracuseStep 9130931 = 13696397) B13696397
theorem B6087287 : Blo 2137435 6087287 := bstep (se 1 (by rfl) ⟨4565465, by rfl⟩ : syracuseStep 6087287 = 9130931) B9130931
theorem B4058191 : Blo 2137435 4058191 := bstep (se 1 (by rfl) ⟨3043643, by rfl⟩ : syracuseStep 4058191 = 6087287) B6087287
theorem B5410921 : Blo 2137435 5410921 := bstep (se 2 (by rfl) ⟨2029095, by rfl⟩ : syracuseStep 5410921 = 4058191) B4058191
theorem B7214561 : Blo 2137435 7214561 := bstep (se 2 (by rfl) ⟨2705460, by rfl⟩ : syracuseStep 7214561 = 5410921) B5410921
theorem B4809707 : Blo 2137435 4809707 := bstep (se 1 (by rfl) ⟨3607280, by rfl⟩ : syracuseStep 4809707 = 7214561) B7214561
theorem B3206471 : Blo 2137435 3206471 := bstep (se 1 (by rfl) ⟨2404853, by rfl⟩ : syracuseStep 3206471 = 4809707) B4809707
theorem B2137647 : Blo 2137435 2137647 := bstep (se 1 (by rfl) ⟨1603235, by rfl⟩ : syracuseStep 2137647 = 3206471) B3206471
theorem B3206477 : Blo 2137435 3206477 := bbase (se 3 (by rfl) ⟨601214, by rfl⟩ : syracuseStep 3206477 = 1202429) (by norm_num)
theorem B2137651 : Blo 2137435 2137651 := bstep (se 1 (by rfl) ⟨1603238, by rfl⟩ : syracuseStep 2137651 = 3206477) B3206477
theorem B4809725 : Blo 2137435 4809725 := bbase (se 3 (by rfl) ⟨901823, by rfl⟩ : syracuseStep 4809725 = 1803647) (by norm_num)
theorem B3206483 : Blo 2137435 3206483 := bstep (se 1 (by rfl) ⟨2404862, by rfl⟩ : syracuseStep 3206483 = 4809725) B4809725
theorem B2137655 : Blo 2137435 2137655 := bstep (se 1 (by rfl) ⟨1603241, by rfl⟩ : syracuseStep 2137655 = 3206483) B3206483
theorem B3607301 : Blo 2137435 3607301 := bbase (se 4 (by rfl) ⟨338184, by rfl⟩ : syracuseStep 3607301 = 676369) (by norm_num)
theorem B2404867 : Blo 2137435 2404867 := bstep (se 1 (by rfl) ⟨1803650, by rfl⟩ : syracuseStep 2404867 = 3607301) B3607301
theorem B3206489 : Blo 2137435 3206489 := bstep (se 2 (by rfl) ⟨1202433, by rfl⟩ : syracuseStep 3206489 = 2404867) B2404867
theorem B2137659 : Blo 2137435 2137659 := bstep (se 1 (by rfl) ⟨1603244, by rfl⟩ : syracuseStep 2137659 = 3206489) B3206489
theorem B16232885 : Blo 2137435 16232885 := bbase (se 5 (by rfl) ⟨760916, by rfl⟩ : syracuseStep 16232885 = 1521833) (by norm_num)
theorem B10821923 : Blo 2137435 10821923 := bstep (se 1 (by rfl) ⟨8116442, by rfl⟩ : syracuseStep 10821923 = 16232885) B16232885
theorem B7214615 : Blo 2137435 7214615 := bstep (se 1 (by rfl) ⟨5410961, by rfl⟩ : syracuseStep 7214615 = 10821923) B10821923
theorem B4809743 : Blo 2137435 4809743 := bstep (se 1 (by rfl) ⟨3607307, by rfl⟩ : syracuseStep 4809743 = 7214615) B7214615
theorem B3206495 : Blo 2137435 3206495 := bstep (se 1 (by rfl) ⟨2404871, by rfl⟩ : syracuseStep 3206495 = 4809743) B4809743
theorem B2137663 : Blo 2137435 2137663 := bstep (se 1 (by rfl) ⟨1603247, by rfl⟩ : syracuseStep 2137663 = 3206495) B3206495
theorem B3206501 : Blo 2137435 3206501 := bbase (se 4 (by rfl) ⟨300609, by rfl⟩ : syracuseStep 3206501 = 601219) (by norm_num)
theorem B2137667 : Blo 2137435 2137667 := bstep (se 1 (by rfl) ⟨1603250, by rfl⟩ : syracuseStep 2137667 = 3206501) B3206501
theorem B4058237 : Blo 2137435 4058237 := bbase (se 3 (by rfl) ⟨760919, by rfl⟩ : syracuseStep 4058237 = 1521839) (by norm_num)
theorem B2705491 : Blo 2137435 2705491 := bstep (se 1 (by rfl) ⟨2029118, by rfl⟩ : syracuseStep 2705491 = 4058237) B4058237
theorem B3607321 : Blo 2137435 3607321 := bstep (se 2 (by rfl) ⟨1352745, by rfl⟩ : syracuseStep 3607321 = 2705491) B2705491
theorem B4809761 : Blo 2137435 4809761 := bstep (se 2 (by rfl) ⟨1803660, by rfl⟩ : syracuseStep 4809761 = 3607321) B3607321
theorem B3206507 : Blo 2137435 3206507 := bstep (se 1 (by rfl) ⟨2404880, by rfl⟩ : syracuseStep 3206507 = 4809761) B4809761
theorem B2137671 : Blo 2137435 2137671 := bstep (se 1 (by rfl) ⟨1603253, by rfl⟩ : syracuseStep 2137671 = 3206507) B3206507
theorem B2404885 : Blo 2137435 2404885 := bbase (se 6 (by rfl) ⟨56364, by rfl⟩ : syracuseStep 2404885 = 112729) (by norm_num)
theorem B3206513 : Blo 2137435 3206513 := bstep (se 2 (by rfl) ⟨1202442, by rfl⟩ : syracuseStep 3206513 = 2404885) B2404885
theorem B2137675 : Blo 2137435 2137675 := bstep (se 1 (by rfl) ⟨1603256, by rfl⟩ : syracuseStep 2137675 = 3206513) B3206513
theorem B2705501 : Blo 2137435 2705501 := bbase (se 3 (by rfl) ⟨507281, by rfl⟩ : syracuseStep 2705501 = 1014563) (by norm_num)
theorem B7214669 : Blo 2137435 7214669 := bstep (se 3 (by rfl) ⟨1352750, by rfl⟩ : syracuseStep 7214669 = 2705501) B2705501
theorem B4809779 : Blo 2137435 4809779 := bstep (se 1 (by rfl) ⟨3607334, by rfl⟩ : syracuseStep 4809779 = 7214669) B7214669
theorem B3206519 : Blo 2137435 3206519 := bstep (se 1 (by rfl) ⟨2404889, by rfl⟩ : syracuseStep 3206519 = 4809779) B4809779
theorem B2137679 : Blo 2137435 2137679 := bstep (se 1 (by rfl) ⟨1603259, by rfl⟩ : syracuseStep 2137679 = 3206519) B3206519
theorem B3206525 : Blo 2137435 3206525 := bbase (se 3 (by rfl) ⟨601223, by rfl⟩ : syracuseStep 3206525 = 1202447) (by norm_num)
theorem B2137683 : Blo 2137435 2137683 := bstep (se 1 (by rfl) ⟨1603262, by rfl⟩ : syracuseStep 2137683 = 3206525) B3206525
theorem B4809797 : Blo 2137435 4809797 := bbase (se 4 (by rfl) ⟨450918, by rfl⟩ : syracuseStep 4809797 = 901837) (by norm_num)
theorem B3206531 : Blo 2137435 3206531 := bstep (se 1 (by rfl) ⟨2404898, by rfl⟩ : syracuseStep 3206531 = 4809797) B4809797
theorem B2137687 : Blo 2137435 2137687 := bstep (se 1 (by rfl) ⟨1603265, by rfl⟩ : syracuseStep 2137687 = 3206531) B3206531
theorem B6087413 : Blo 2137435 6087413 := bbase (se 5 (by rfl) ⟨285347, by rfl⟩ : syracuseStep 6087413 = 570695) (by norm_num)
theorem B4058275 : Blo 2137435 4058275 := bstep (se 1 (by rfl) ⟨3043706, by rfl⟩ : syracuseStep 4058275 = 6087413) B6087413
theorem B5411033 : Blo 2137435 5411033 := bstep (se 2 (by rfl) ⟨2029137, by rfl⟩ : syracuseStep 5411033 = 4058275) B4058275
theorem B3607355 : Blo 2137435 3607355 := bstep (se 1 (by rfl) ⟨2705516, by rfl⟩ : syracuseStep 3607355 = 5411033) B5411033
theorem B2404903 : Blo 2137435 2404903 := bstep (se 1 (by rfl) ⟨1803677, by rfl⟩ : syracuseStep 2404903 = 3607355) B3607355
theorem B3206537 : Blo 2137435 3206537 := bstep (se 2 (by rfl) ⟨1202451, by rfl⟩ : syracuseStep 3206537 = 2404903) B2404903
theorem B2137691 : Blo 2137435 2137691 := bstep (se 1 (by rfl) ⟨1603268, by rfl⟩ : syracuseStep 2137691 = 3206537) B3206537
theorem B10822085 : Blo 2137435 10822085 := bbase (se 4 (by rfl) ⟨1014570, by rfl⟩ : syracuseStep 10822085 = 2029141) (by norm_num)
theorem B7214723 : Blo 2137435 7214723 := bstep (se 1 (by rfl) ⟨5411042, by rfl⟩ : syracuseStep 7214723 = 10822085) B10822085
theorem B4809815 : Blo 2137435 4809815 := bstep (se 1 (by rfl) ⟨3607361, by rfl⟩ : syracuseStep 4809815 = 7214723) B7214723
theorem B3206543 : Blo 2137435 3206543 := bstep (se 1 (by rfl) ⟨2404907, by rfl⟩ : syracuseStep 3206543 = 4809815) B4809815
theorem B2137695 : Blo 2137435 2137695 := bstep (se 1 (by rfl) ⟨1603271, by rfl⟩ : syracuseStep 2137695 = 3206543) B3206543
theorem B3206549 : Blo 2137435 3206549 := bbase (se 6 (by rfl) ⟨75153, by rfl⟩ : syracuseStep 3206549 = 150307) (by norm_num)
theorem B2137699 : Blo 2137435 2137699 := bstep (se 1 (by rfl) ⟨1603274, by rfl⟩ : syracuseStep 2137699 = 3206549) B3206549
theorem B3424189 : Blo 2137435 3424189 := bbase (se 3 (by rfl) ⟨642035, by rfl⟩ : syracuseStep 3424189 = 1284071) (by norm_num)
theorem B4565585 : Blo 2137435 4565585 := bstep (se 2 (by rfl) ⟨1712094, by rfl⟩ : syracuseStep 4565585 = 3424189) B3424189
theorem B12174893 : Blo 2137435 12174893 := bstep (se 3 (by rfl) ⟨2282792, by rfl⟩ : syracuseStep 12174893 = 4565585) B4565585
theorem B8116595 : Blo 2137435 8116595 := bstep (se 1 (by rfl) ⟨6087446, by rfl⟩ : syracuseStep 8116595 = 12174893) B12174893
theorem B5411063 : Blo 2137435 5411063 := bstep (se 1 (by rfl) ⟨4058297, by rfl⟩ : syracuseStep 5411063 = 8116595) B8116595
theorem B3607375 : Blo 2137435 3607375 := bstep (se 1 (by rfl) ⟨2705531, by rfl⟩ : syracuseStep 3607375 = 5411063) B5411063
theorem B4809833 : Blo 2137435 4809833 := bstep (se 2 (by rfl) ⟨1803687, by rfl⟩ : syracuseStep 4809833 = 3607375) B3607375
theorem B3206555 : Blo 2137435 3206555 := bstep (se 1 (by rfl) ⟨2404916, by rfl⟩ : syracuseStep 3206555 = 4809833) B4809833
theorem B2137703 : Blo 2137435 2137703 := bstep (se 1 (by rfl) ⟨1603277, by rfl⟩ : syracuseStep 2137703 = 3206555) B3206555
theorem B2404921 : Blo 2137435 2404921 := bbase (se 2 (by rfl) ⟨901845, by rfl⟩ : syracuseStep 2404921 = 1803691) (by norm_num)
theorem B3206561 : Blo 2137435 3206561 := bstep (se 2 (by rfl) ⟨1202460, by rfl⟩ : syracuseStep 3206561 = 2404921) B2404921
theorem B2137707 : Blo 2137435 2137707 := bstep (se 1 (by rfl) ⟨1603280, by rfl⟩ : syracuseStep 2137707 = 3206561) B3206561
theorem B2282801 : Blo 2137435 2282801 := bbase (se 2 (by rfl) ⟨856050, by rfl⟩ : syracuseStep 2282801 = 1712101) (by norm_num)
theorem B6087469 : Blo 2137435 6087469 := bstep (se 3 (by rfl) ⟨1141400, by rfl⟩ : syracuseStep 6087469 = 2282801) B2282801
theorem B8116625 : Blo 2137435 8116625 := bstep (se 2 (by rfl) ⟨3043734, by rfl⟩ : syracuseStep 8116625 = 6087469) B6087469
theorem B5411083 : Blo 2137435 5411083 := bstep (se 1 (by rfl) ⟨4058312, by rfl⟩ : syracuseStep 5411083 = 8116625) B8116625
theorem B7214777 : Blo 2137435 7214777 := bstep (se 2 (by rfl) ⟨2705541, by rfl⟩ : syracuseStep 7214777 = 5411083) B5411083
theorem B4809851 : Blo 2137435 4809851 := bstep (se 1 (by rfl) ⟨3607388, by rfl⟩ : syracuseStep 4809851 = 7214777) B7214777
theorem B3206567 : Blo 2137435 3206567 := bstep (se 1 (by rfl) ⟨2404925, by rfl⟩ : syracuseStep 3206567 = 4809851) B4809851
theorem B2137711 : Blo 2137435 2137711 := bstep (se 1 (by rfl) ⟨1603283, by rfl⟩ : syracuseStep 2137711 = 3206567) B3206567
theorem B3206573 : Blo 2137435 3206573 := bbase (se 3 (by rfl) ⟨601232, by rfl⟩ : syracuseStep 3206573 = 1202465) (by norm_num)
theorem B2137715 : Blo 2137435 2137715 := bstep (se 1 (by rfl) ⟨1603286, by rfl⟩ : syracuseStep 2137715 = 3206573) B3206573
theorem B4809869 : Blo 2137435 4809869 := bbase (se 3 (by rfl) ⟨901850, by rfl⟩ : syracuseStep 4809869 = 1803701) (by norm_num)
theorem B3206579 : Blo 2137435 3206579 := bstep (se 1 (by rfl) ⟨2404934, by rfl⟩ : syracuseStep 3206579 = 4809869) B4809869
theorem B2137719 : Blo 2137435 2137719 := bstep (se 1 (by rfl) ⟨1603289, by rfl⟩ : syracuseStep 2137719 = 3206579) B3206579
theorem B2705557 : Blo 2137435 2705557 := bbase (se 6 (by rfl) ⟨63411, by rfl⟩ : syracuseStep 2705557 = 126823) (by norm_num)
theorem B3607409 : Blo 2137435 3607409 := bstep (se 2 (by rfl) ⟨1352778, by rfl⟩ : syracuseStep 3607409 = 2705557) B2705557
theorem B2404939 : Blo 2137435 2404939 := bstep (se 1 (by rfl) ⟨1803704, by rfl⟩ : syracuseStep 2404939 = 3607409) B3607409
theorem B3206585 : Blo 2137435 3206585 := bstep (se 2 (by rfl) ⟨1202469, by rfl⟩ : syracuseStep 3206585 = 2404939) B2404939
theorem B2137723 : Blo 2137435 2137723 := bstep (se 1 (by rfl) ⟨1603292, by rfl⟩ : syracuseStep 2137723 = 3206585) B3206585
theorem B3085285 : Blo 2137435 3085285 := bbase (se 4 (by rfl) ⟨289245, by rfl⟩ : syracuseStep 3085285 = 578491) (by norm_num)
theorem B4113713 : Blo 2137435 4113713 := bstep (se 2 (by rfl) ⟨1542642, by rfl⟩ : syracuseStep 4113713 = 3085285) B3085285
theorem B10969901 : Blo 2137435 10969901 := bstep (se 3 (by rfl) ⟨2056856, by rfl⟩ : syracuseStep 10969901 = 4113713) B4113713
theorem B7313267 : Blo 2137435 7313267 := bstep (se 1 (by rfl) ⟨5484950, by rfl⟩ : syracuseStep 7313267 = 10969901) B10969901
theorem B19502045 : Blo 2137435 19502045 := bstep (se 3 (by rfl) ⟨3656633, by rfl⟩ : syracuseStep 19502045 = 7313267) B7313267
theorem B13001363 : Blo 2137435 13001363 := bstep (se 1 (by rfl) ⟨9751022, by rfl⟩ : syracuseStep 13001363 = 19502045) B19502045
theorem B8667575 : Blo 2137435 8667575 := bstep (se 1 (by rfl) ⟨6500681, by rfl⟩ : syracuseStep 8667575 = 13001363) B13001363
theorem B5778383 : Blo 2137435 5778383 := bstep (se 1 (by rfl) ⟨4333787, by rfl⟩ : syracuseStep 5778383 = 8667575) B8667575
theorem B61636085 : Blo 2137435 61636085 := bstep (se 5 (by rfl) ⟨2889191, by rfl⟩ : syracuseStep 61636085 = 5778383) B5778383
theorem B41090723 : Blo 2137435 41090723 := bstep (se 1 (by rfl) ⟨30818042, by rfl⟩ : syracuseStep 41090723 = 61636085) B61636085
theorem B27393815 : Blo 2137435 27393815 := bstep (se 1 (by rfl) ⟨20545361, by rfl⟩ : syracuseStep 27393815 = 41090723) B41090723
theorem B18262543 : Blo 2137435 18262543 := bstep (se 1 (by rfl) ⟨13696907, by rfl⟩ : syracuseStep 18262543 = 27393815) B27393815
theorem B24350057 : Blo 2137435 24350057 := bstep (se 2 (by rfl) ⟨9131271, by rfl⟩ : syracuseStep 24350057 = 18262543) B18262543
theorem B16233371 : Blo 2137435 16233371 := bstep (se 1 (by rfl) ⟨12175028, by rfl⟩ : syracuseStep 16233371 = 24350057) B24350057
theorem B10822247 : Blo 2137435 10822247 := bstep (se 1 (by rfl) ⟨8116685, by rfl⟩ : syracuseStep 10822247 = 16233371) B16233371
theorem B7214831 : Blo 2137435 7214831 := bstep (se 1 (by rfl) ⟨5411123, by rfl⟩ : syracuseStep 7214831 = 10822247) B10822247
theorem B4809887 : Blo 2137435 4809887 := bstep (se 1 (by rfl) ⟨3607415, by rfl⟩ : syracuseStep 4809887 = 7214831) B7214831
theorem B3206591 : Blo 2137435 3206591 := bstep (se 1 (by rfl) ⟨2404943, by rfl⟩ : syracuseStep 3206591 = 4809887) B4809887
theorem B2137727 : Blo 2137435 2137727 := bstep (se 1 (by rfl) ⟨1603295, by rfl⟩ : syracuseStep 2137727 = 3206591) B3206591
theorem B3206597 : Blo 2137435 3206597 := bbase (se 4 (by rfl) ⟨300618, by rfl⟩ : syracuseStep 3206597 = 601237) (by norm_num)
theorem B2137731 : Blo 2137435 2137731 := bstep (se 1 (by rfl) ⟨1603298, by rfl⟩ : syracuseStep 2137731 = 3206597) B3206597
theorem B3607429 : Blo 2137435 3607429 := bbase (se 4 (by rfl) ⟨338196, by rfl⟩ : syracuseStep 3607429 = 676393) (by norm_num)
theorem B4809905 : Blo 2137435 4809905 := bstep (se 2 (by rfl) ⟨1803714, by rfl⟩ : syracuseStep 4809905 = 3607429) B3607429
theorem B3206603 : Blo 2137435 3206603 := bstep (se 1 (by rfl) ⟨2404952, by rfl⟩ : syracuseStep 3206603 = 4809905) B4809905
theorem B2137735 : Blo 2137435 2137735 := bstep (se 1 (by rfl) ⟨1603301, by rfl⟩ : syracuseStep 2137735 = 3206603) B3206603
theorem B2404957 : Blo 2137435 2404957 := bbase (se 3 (by rfl) ⟨450929, by rfl⟩ : syracuseStep 2404957 = 901859) (by norm_num)
theorem B3206609 : Blo 2137435 3206609 := bstep (se 2 (by rfl) ⟨1202478, by rfl⟩ : syracuseStep 3206609 = 2404957) B2404957
theorem B2137739 : Blo 2137435 2137739 := bstep (se 1 (by rfl) ⟨1603304, by rfl⟩ : syracuseStep 2137739 = 3206609) B3206609
theorem B7214885 : Blo 2137435 7214885 := bbase (se 4 (by rfl) ⟨676395, by rfl⟩ : syracuseStep 7214885 = 1352791) (by norm_num)
theorem B4809923 : Blo 2137435 4809923 := bstep (se 1 (by rfl) ⟨3607442, by rfl⟩ : syracuseStep 4809923 = 7214885) B7214885
theorem B3206615 : Blo 2137435 3206615 := bstep (se 1 (by rfl) ⟨2404961, by rfl⟩ : syracuseStep 3206615 = 4809923) B4809923
theorem B2137743 : Blo 2137435 2137743 := bstep (se 1 (by rfl) ⟨1603307, by rfl⟩ : syracuseStep 2137743 = 3206615) B3206615
theorem B3206621 : Blo 2137435 3206621 := bbase (se 3 (by rfl) ⟨601241, by rfl⟩ : syracuseStep 3206621 = 1202483) (by norm_num)
theorem B2137747 : Blo 2137435 2137747 := bstep (se 1 (by rfl) ⟨1603310, by rfl⟩ : syracuseStep 2137747 = 3206621) B3206621
theorem B4809941 : Blo 2137435 4809941 := bbase (se 7 (by rfl) ⟨56366, by rfl⟩ : syracuseStep 4809941 = 112733) (by norm_num)
theorem B3206627 : Blo 2137435 3206627 := bstep (se 1 (by rfl) ⟨2404970, by rfl⟩ : syracuseStep 3206627 = 4809941) B4809941
theorem B2137751 : Blo 2137435 2137751 := bstep (se 1 (by rfl) ⟨1603313, by rfl⟩ : syracuseStep 2137751 = 3206627) B3206627
theorem B2437789 : Blo 2137435 2437789 := bbase (se 3 (by rfl) ⟨457085, by rfl⟩ : syracuseStep 2437789 = 914171) (by norm_num)
theorem B3250385 : Blo 2137435 3250385 := bstep (se 2 (by rfl) ⟨1218894, by rfl⟩ : syracuseStep 3250385 = 2437789) B2437789
theorem B2166923 : Blo 2137435 2166923 := bstep (se 1 (by rfl) ⟨1625192, by rfl⟩ : syracuseStep 2166923 = 3250385) B3250385
theorem B5778461 : Blo 2137435 5778461 := bstep (se 3 (by rfl) ⟨1083461, by rfl⟩ : syracuseStep 5778461 = 2166923) B2166923
theorem B3852307 : Blo 2137435 3852307 := bstep (se 1 (by rfl) ⟨2889230, by rfl⟩ : syracuseStep 3852307 = 5778461) B5778461
theorem B5136409 : Blo 2137435 5136409 := bstep (se 2 (by rfl) ⟨1926153, by rfl⟩ : syracuseStep 5136409 = 3852307) B3852307
theorem B6848545 : Blo 2137435 6848545 := bstep (se 2 (by rfl) ⟨2568204, by rfl⟩ : syracuseStep 6848545 = 5136409) B5136409
theorem B9131393 : Blo 2137435 9131393 := bstep (se 2 (by rfl) ⟨3424272, by rfl⟩ : syracuseStep 9131393 = 6848545) B6848545
theorem B6087595 : Blo 2137435 6087595 := bstep (se 1 (by rfl) ⟨4565696, by rfl⟩ : syracuseStep 6087595 = 9131393) B9131393
theorem B8116793 : Blo 2137435 8116793 := bstep (se 2 (by rfl) ⟨3043797, by rfl⟩ : syracuseStep 8116793 = 6087595) B6087595
theorem B5411195 : Blo 2137435 5411195 := bstep (se 1 (by rfl) ⟨4058396, by rfl⟩ : syracuseStep 5411195 = 8116793) B8116793
theorem B3607463 : Blo 2137435 3607463 := bstep (se 1 (by rfl) ⟨2705597, by rfl⟩ : syracuseStep 3607463 = 5411195) B5411195
theorem B2404975 : Blo 2137435 2404975 := bstep (se 1 (by rfl) ⟨1803731, by rfl⟩ : syracuseStep 2404975 = 3607463) B3607463
theorem B3206633 : Blo 2137435 3206633 := bstep (se 2 (by rfl) ⟨1202487, by rfl⟩ : syracuseStep 3206633 = 2404975) B2404975
theorem B2137755 : Blo 2137435 2137755 := bstep (se 1 (by rfl) ⟨1603316, by rfl⟩ : syracuseStep 2137755 = 3206633) B3206633
theorem B4333853 : Blo 2137435 4333853 := bbase (se 3 (by rfl) ⟨812597, by rfl⟩ : syracuseStep 4333853 = 1625195) (by norm_num)
theorem B2889235 : Blo 2137435 2889235 := bstep (se 1 (by rfl) ⟨2166926, by rfl⟩ : syracuseStep 2889235 = 4333853) B4333853
theorem B15409253 : Blo 2137435 15409253 := bstep (se 4 (by rfl) ⟨1444617, by rfl⟩ : syracuseStep 15409253 = 2889235) B2889235
theorem B10272835 : Blo 2137435 10272835 := bstep (se 1 (by rfl) ⟨7704626, by rfl⟩ : syracuseStep 10272835 = 15409253) B15409253
theorem B13697113 : Blo 2137435 13697113 := bstep (se 2 (by rfl) ⟨5136417, by rfl⟩ : syracuseStep 13697113 = 10272835) B10272835
theorem B18262817 : Blo 2137435 18262817 := bstep (se 2 (by rfl) ⟨6848556, by rfl⟩ : syracuseStep 18262817 = 13697113) B13697113
theorem B12175211 : Blo 2137435 12175211 := bstep (se 1 (by rfl) ⟨9131408, by rfl⟩ : syracuseStep 12175211 = 18262817) B18262817
theorem B8116807 : Blo 2137435 8116807 := bstep (se 1 (by rfl) ⟨6087605, by rfl⟩ : syracuseStep 8116807 = 12175211) B12175211
theorem B10822409 : Blo 2137435 10822409 := bstep (se 2 (by rfl) ⟨4058403, by rfl⟩ : syracuseStep 10822409 = 8116807) B8116807
theorem B7214939 : Blo 2137435 7214939 := bstep (se 1 (by rfl) ⟨5411204, by rfl⟩ : syracuseStep 7214939 = 10822409) B10822409
theorem B4809959 : Blo 2137435 4809959 := bstep (se 1 (by rfl) ⟨3607469, by rfl⟩ : syracuseStep 4809959 = 7214939) B7214939
theorem B3206639 : Blo 2137435 3206639 := bstep (se 1 (by rfl) ⟨2404979, by rfl⟩ : syracuseStep 3206639 = 4809959) B4809959
theorem B2137759 : Blo 2137435 2137759 := bstep (se 1 (by rfl) ⟨1603319, by rfl⟩ : syracuseStep 2137759 = 3206639) B3206639
theorem B3206645 : Blo 2137435 3206645 := bbase (se 5 (by rfl) ⟨150311, by rfl⟩ : syracuseStep 3206645 = 300623) (by norm_num)
theorem B2137763 : Blo 2137435 2137763 := bstep (se 1 (by rfl) ⟨1603322, by rfl⟩ : syracuseStep 2137763 = 3206645) B3206645
theorem B2282861 : Blo 2137435 2282861 := bbase (se 3 (by rfl) ⟨428036, by rfl⟩ : syracuseStep 2282861 = 856073) (by norm_num)
theorem B6087629 : Blo 2137435 6087629 := bstep (se 3 (by rfl) ⟨1141430, by rfl⟩ : syracuseStep 6087629 = 2282861) B2282861
theorem B4058419 : Blo 2137435 4058419 := bstep (se 1 (by rfl) ⟨3043814, by rfl⟩ : syracuseStep 4058419 = 6087629) B6087629
theorem B5411225 : Blo 2137435 5411225 := bstep (se 2 (by rfl) ⟨2029209, by rfl⟩ : syracuseStep 5411225 = 4058419) B4058419
theorem B3607483 : Blo 2137435 3607483 := bstep (se 1 (by rfl) ⟨2705612, by rfl⟩ : syracuseStep 3607483 = 5411225) B5411225
theorem B4809977 : Blo 2137435 4809977 := bstep (se 2 (by rfl) ⟨1803741, by rfl⟩ : syracuseStep 4809977 = 3607483) B3607483
theorem B3206651 : Blo 2137435 3206651 := bstep (se 1 (by rfl) ⟨2404988, by rfl⟩ : syracuseStep 3206651 = 4809977) B4809977
theorem B2137767 : Blo 2137435 2137767 := bstep (se 1 (by rfl) ⟨1603325, by rfl⟩ : syracuseStep 2137767 = 3206651) B3206651
theorem B2404993 : Blo 2137435 2404993 := bbase (se 2 (by rfl) ⟨901872, by rfl⟩ : syracuseStep 2404993 = 1803745) (by norm_num)
theorem B3206657 : Blo 2137435 3206657 := bstep (se 2 (by rfl) ⟨1202496, by rfl⟩ : syracuseStep 3206657 = 2404993) B2404993
theorem B2137771 : Blo 2137435 2137771 := bstep (se 1 (by rfl) ⟨1603328, by rfl⟩ : syracuseStep 2137771 = 3206657) B3206657
theorem B5411245 : Blo 2137435 5411245 := bbase (se 3 (by rfl) ⟨1014608, by rfl⟩ : syracuseStep 5411245 = 2029217) (by norm_num)
theorem B7214993 : Blo 2137435 7214993 := bstep (se 2 (by rfl) ⟨2705622, by rfl⟩ : syracuseStep 7214993 = 5411245) B5411245
theorem B4809995 : Blo 2137435 4809995 := bstep (se 1 (by rfl) ⟨3607496, by rfl⟩ : syracuseStep 4809995 = 7214993) B7214993
theorem B3206663 : Blo 2137435 3206663 := bstep (se 1 (by rfl) ⟨2404997, by rfl⟩ : syracuseStep 3206663 = 4809995) B4809995
theorem B2137775 : Blo 2137435 2137775 := bstep (se 1 (by rfl) ⟨1603331, by rfl⟩ : syracuseStep 2137775 = 3206663) B3206663
theorem B3206669 : Blo 2137435 3206669 := bbase (se 3 (by rfl) ⟨601250, by rfl⟩ : syracuseStep 3206669 = 1202501) (by norm_num)
theorem B2137779 : Blo 2137435 2137779 := bstep (se 1 (by rfl) ⟨1603334, by rfl⟩ : syracuseStep 2137779 = 3206669) B3206669
theorem B4810013 : Blo 2137435 4810013 := bbase (se 3 (by rfl) ⟨901877, by rfl⟩ : syracuseStep 4810013 = 1803755) (by norm_num)
theorem B3206675 : Blo 2137435 3206675 := bstep (se 1 (by rfl) ⟨2405006, by rfl⟩ : syracuseStep 3206675 = 4810013) B4810013
theorem B2137783 : Blo 2137435 2137783 := bstep (se 1 (by rfl) ⟨1603337, by rfl⟩ : syracuseStep 2137783 = 3206675) B3206675
theorem B3607517 : Blo 2137435 3607517 := bbase (se 3 (by rfl) ⟨676409, by rfl⟩ : syracuseStep 3607517 = 1352819) (by norm_num)
theorem B2405011 : Blo 2137435 2405011 := bstep (se 1 (by rfl) ⟨1803758, by rfl⟩ : syracuseStep 2405011 = 3607517) B3607517
theorem B3206681 : Blo 2137435 3206681 := bstep (se 2 (by rfl) ⟨1202505, by rfl⟩ : syracuseStep 3206681 = 2405011) B2405011
theorem B2137787 : Blo 2137435 2137787 := bstep (se 1 (by rfl) ⟨1603340, by rfl⟩ : syracuseStep 2137787 = 3206681) B3206681
theorem B5485117 : Blo 2137435 5485117 := bbase (se 3 (by rfl) ⟨1028459, by rfl⟩ : syracuseStep 5485117 = 2056919) (by norm_num)
theorem B7313489 : Blo 2137435 7313489 := bstep (se 2 (by rfl) ⟨2742558, by rfl⟩ : syracuseStep 7313489 = 5485117) B5485117
theorem B4875659 : Blo 2137435 4875659 := bstep (se 1 (by rfl) ⟨3656744, by rfl⟩ : syracuseStep 4875659 = 7313489) B7313489
theorem B3250439 : Blo 2137435 3250439 := bstep (se 1 (by rfl) ⟨2437829, by rfl⟩ : syracuseStep 3250439 = 4875659) B4875659
theorem B2166959 : Blo 2137435 2166959 := bstep (se 1 (by rfl) ⟨1625219, by rfl⟩ : syracuseStep 2166959 = 3250439) B3250439
theorem B5778557 : Blo 2137435 5778557 := bstep (se 3 (by rfl) ⟨1083479, by rfl⟩ : syracuseStep 5778557 = 2166959) B2166959
theorem B3852371 : Blo 2137435 3852371 := bstep (se 1 (by rfl) ⟨2889278, by rfl⟩ : syracuseStep 3852371 = 5778557) B5778557
theorem B10272989 : Blo 2137435 10272989 := bstep (se 3 (by rfl) ⟨1926185, by rfl⟩ : syracuseStep 10272989 = 3852371) B3852371
theorem B6848659 : Blo 2137435 6848659 := bstep (se 1 (by rfl) ⟨5136494, by rfl⟩ : syracuseStep 6848659 = 10272989) B10272989
theorem B9131545 : Blo 2137435 9131545 := bstep (se 2 (by rfl) ⟨3424329, by rfl⟩ : syracuseStep 9131545 = 6848659) B6848659
theorem B12175393 : Blo 2137435 12175393 := bstep (se 2 (by rfl) ⟨4565772, by rfl⟩ : syracuseStep 12175393 = 9131545) B9131545
theorem B16233857 : Blo 2137435 16233857 := bstep (se 2 (by rfl) ⟨6087696, by rfl⟩ : syracuseStep 16233857 = 12175393) B12175393
theorem B10822571 : Blo 2137435 10822571 := bstep (se 1 (by rfl) ⟨8116928, by rfl⟩ : syracuseStep 10822571 = 16233857) B16233857
theorem B7215047 : Blo 2137435 7215047 := bstep (se 1 (by rfl) ⟨5411285, by rfl⟩ : syracuseStep 7215047 = 10822571) B10822571
theorem B4810031 : Blo 2137435 4810031 := bstep (se 1 (by rfl) ⟨3607523, by rfl⟩ : syracuseStep 4810031 = 7215047) B7215047
theorem B3206687 : Blo 2137435 3206687 := bstep (se 1 (by rfl) ⟨2405015, by rfl⟩ : syracuseStep 3206687 = 4810031) B4810031
theorem B2137791 : Blo 2137435 2137791 := bstep (se 1 (by rfl) ⟨1603343, by rfl⟩ : syracuseStep 2137791 = 3206687) B3206687
theorem B3206693 : Blo 2137435 3206693 := bbase (se 4 (by rfl) ⟨300627, by rfl⟩ : syracuseStep 3206693 = 601255) (by norm_num)
theorem B2137795 : Blo 2137435 2137795 := bstep (se 1 (by rfl) ⟨1603346, by rfl⟩ : syracuseStep 2137795 = 3206693) B3206693
theorem B2705653 : Blo 2137435 2705653 := bbase (se 5 (by rfl) ⟨126827, by rfl⟩ : syracuseStep 2705653 = 253655) (by norm_num)
theorem B3607537 : Blo 2137435 3607537 := bstep (se 2 (by rfl) ⟨1352826, by rfl⟩ : syracuseStep 3607537 = 2705653) B2705653
theorem B4810049 : Blo 2137435 4810049 := bstep (se 2 (by rfl) ⟨1803768, by rfl⟩ : syracuseStep 4810049 = 3607537) B3607537
theorem B3206699 : Blo 2137435 3206699 := bstep (se 1 (by rfl) ⟨2405024, by rfl⟩ : syracuseStep 3206699 = 4810049) B4810049
theorem B2137799 : Blo 2137435 2137799 := bstep (se 1 (by rfl) ⟨1603349, by rfl⟩ : syracuseStep 2137799 = 3206699) B3206699
theorem B2405029 : Blo 2137435 2405029 := bbase (se 4 (by rfl) ⟨225471, by rfl⟩ : syracuseStep 2405029 = 450943) (by norm_num)
theorem B3206705 : Blo 2137435 3206705 := bstep (se 2 (by rfl) ⟨1202514, by rfl⟩ : syracuseStep 3206705 = 2405029) B2405029
theorem B2137803 : Blo 2137435 2137803 := bstep (se 1 (by rfl) ⟨1603352, by rfl⟩ : syracuseStep 2137803 = 3206705) B3206705
theorem B3471077 : Blo 2137435 3471077 := bbase (se 4 (by rfl) ⟨325413, by rfl⟩ : syracuseStep 3471077 = 650827) (by norm_num)
theorem B2314051 : Blo 2137435 2314051 := bstep (se 1 (by rfl) ⟨1735538, by rfl⟩ : syracuseStep 2314051 = 3471077) B3471077
theorem B12341605 : Blo 2137435 12341605 := bstep (se 4 (by rfl) ⟨1157025, by rfl⟩ : syracuseStep 12341605 = 2314051) B2314051
theorem B16455473 : Blo 2137435 16455473 := bstep (se 2 (by rfl) ⟨6170802, by rfl⟩ : syracuseStep 16455473 = 12341605) B12341605
theorem B10970315 : Blo 2137435 10970315 := bstep (se 1 (by rfl) ⟨8227736, by rfl⟩ : syracuseStep 10970315 = 16455473) B16455473
theorem B7313543 : Blo 2137435 7313543 := bstep (se 1 (by rfl) ⟨5485157, by rfl⟩ : syracuseStep 7313543 = 10970315) B10970315
theorem B4875695 : Blo 2137435 4875695 := bstep (se 1 (by rfl) ⟨3656771, by rfl⟩ : syracuseStep 4875695 = 7313543) B7313543
theorem B3250463 : Blo 2137435 3250463 := bstep (se 1 (by rfl) ⟨2437847, by rfl⟩ : syracuseStep 3250463 = 4875695) B4875695
theorem B8667901 : Blo 2137435 8667901 := bstep (se 3 (by rfl) ⟨1625231, by rfl⟩ : syracuseStep 8667901 = 3250463) B3250463
theorem B46228805 : Blo 2137435 46228805 := bstep (se 4 (by rfl) ⟨4333950, by rfl⟩ : syracuseStep 46228805 = 8667901) B8667901
theorem B30819203 : Blo 2137435 30819203 := bstep (se 1 (by rfl) ⟨23114402, by rfl⟩ : syracuseStep 30819203 = 46228805) B46228805
theorem B20546135 : Blo 2137435 20546135 := bstep (se 1 (by rfl) ⟨15409601, by rfl⟩ : syracuseStep 20546135 = 30819203) B30819203
theorem B13697423 : Blo 2137435 13697423 := bstep (se 1 (by rfl) ⟨10273067, by rfl⟩ : syracuseStep 13697423 = 20546135) B20546135
theorem B9131615 : Blo 2137435 9131615 := bstep (se 1 (by rfl) ⟨6848711, by rfl⟩ : syracuseStep 9131615 = 13697423) B13697423
theorem B6087743 : Blo 2137435 6087743 := bstep (se 1 (by rfl) ⟨4565807, by rfl⟩ : syracuseStep 6087743 = 9131615) B9131615
theorem B4058495 : Blo 2137435 4058495 := bstep (se 1 (by rfl) ⟨3043871, by rfl⟩ : syracuseStep 4058495 = 6087743) B6087743
theorem B2705663 : Blo 2137435 2705663 := bstep (se 1 (by rfl) ⟨2029247, by rfl⟩ : syracuseStep 2705663 = 4058495) B4058495
theorem B7215101 : Blo 2137435 7215101 := bstep (se 3 (by rfl) ⟨1352831, by rfl⟩ : syracuseStep 7215101 = 2705663) B2705663
theorem B4810067 : Blo 2137435 4810067 := bstep (se 1 (by rfl) ⟨3607550, by rfl⟩ : syracuseStep 4810067 = 7215101) B7215101
theorem B3206711 : Blo 2137435 3206711 := bstep (se 1 (by rfl) ⟨2405033, by rfl⟩ : syracuseStep 3206711 = 4810067) B4810067
theorem B2137807 : Blo 2137435 2137807 := bstep (se 1 (by rfl) ⟨1603355, by rfl⟩ : syracuseStep 2137807 = 3206711) B3206711
theorem B3206717 : Blo 2137435 3206717 := bbase (se 3 (by rfl) ⟨601259, by rfl⟩ : syracuseStep 3206717 = 1202519) (by norm_num)
theorem B2137811 : Blo 2137435 2137811 := bstep (se 1 (by rfl) ⟨1603358, by rfl⟩ : syracuseStep 2137811 = 3206717) B3206717
theorem B4810085 : Blo 2137435 4810085 := bbase (se 4 (by rfl) ⟨450945, by rfl⟩ : syracuseStep 4810085 = 901891) (by norm_num)
theorem B3206723 : Blo 2137435 3206723 := bstep (se 1 (by rfl) ⟨2405042, by rfl⟩ : syracuseStep 3206723 = 4810085) B4810085
theorem B2137815 : Blo 2137435 2137815 := bstep (se 1 (by rfl) ⟨1603361, by rfl⟩ : syracuseStep 2137815 = 3206723) B3206723
theorem B5411357 : Blo 2137435 5411357 := bbase (se 3 (by rfl) ⟨1014629, by rfl⟩ : syracuseStep 5411357 = 2029259) (by norm_num)
theorem B3607571 : Blo 2137435 3607571 := bstep (se 1 (by rfl) ⟨2705678, by rfl⟩ : syracuseStep 3607571 = 5411357) B5411357
theorem B2405047 : Blo 2137435 2405047 := bstep (se 1 (by rfl) ⟨1803785, by rfl⟩ : syracuseStep 2405047 = 3607571) B3607571
theorem B3206729 : Blo 2137435 3206729 := bstep (se 2 (by rfl) ⟨1202523, by rfl⟩ : syracuseStep 3206729 = 2405047) B2405047
theorem B2137819 : Blo 2137435 2137819 := bstep (se 1 (by rfl) ⟨1603364, by rfl⟩ : syracuseStep 2137819 = 3206729) B3206729
theorem B4058525 : Blo 2137435 4058525 := bbase (se 3 (by rfl) ⟨760973, by rfl⟩ : syracuseStep 4058525 = 1521947) (by norm_num)
theorem B10822733 : Blo 2137435 10822733 := bstep (se 3 (by rfl) ⟨2029262, by rfl⟩ : syracuseStep 10822733 = 4058525) B4058525
theorem B7215155 : Blo 2137435 7215155 := bstep (se 1 (by rfl) ⟨5411366, by rfl⟩ : syracuseStep 7215155 = 10822733) B10822733
theorem B4810103 : Blo 2137435 4810103 := bstep (se 1 (by rfl) ⟨3607577, by rfl⟩ : syracuseStep 4810103 = 7215155) B7215155
theorem B3206735 : Blo 2137435 3206735 := bstep (se 1 (by rfl) ⟨2405051, by rfl⟩ : syracuseStep 3206735 = 4810103) B4810103
theorem B2137823 : Blo 2137435 2137823 := bstep (se 1 (by rfl) ⟨1603367, by rfl⟩ : syracuseStep 2137823 = 3206735) B3206735
theorem B3206741 : Blo 2137435 3206741 := bbase (se 8 (by rfl) ⟨18789, by rfl⟩ : syracuseStep 3206741 = 37579) (by norm_num)
theorem B2137827 : Blo 2137435 2137827 := bstep (se 1 (by rfl) ⟨1603370, by rfl⟩ : syracuseStep 2137827 = 3206741) B3206741
theorem B9131717 : Blo 2137435 9131717 := bbase (se 4 (by rfl) ⟨856098, by rfl⟩ : syracuseStep 9131717 = 1712197) (by norm_num)
theorem B6087811 : Blo 2137435 6087811 := bstep (se 1 (by rfl) ⟨4565858, by rfl⟩ : syracuseStep 6087811 = 9131717) B9131717
theorem B8117081 : Blo 2137435 8117081 := bstep (se 2 (by rfl) ⟨3043905, by rfl⟩ : syracuseStep 8117081 = 6087811) B6087811
theorem B5411387 : Blo 2137435 5411387 := bstep (se 1 (by rfl) ⟨4058540, by rfl⟩ : syracuseStep 5411387 = 8117081) B8117081
theorem B3607591 : Blo 2137435 3607591 := bstep (se 1 (by rfl) ⟨2705693, by rfl⟩ : syracuseStep 3607591 = 5411387) B5411387
theorem B4810121 : Blo 2137435 4810121 := bstep (se 2 (by rfl) ⟨1803795, by rfl⟩ : syracuseStep 4810121 = 3607591) B3607591
theorem B3206747 : Blo 2137435 3206747 := bstep (se 1 (by rfl) ⟨2405060, by rfl⟩ : syracuseStep 3206747 = 4810121) B4810121
theorem B2137831 : Blo 2137435 2137831 := bstep (se 1 (by rfl) ⟨1603373, by rfl⟩ : syracuseStep 2137831 = 3206747) B3206747
theorem B2405065 : Blo 2137435 2405065 := bbase (se 2 (by rfl) ⟨901899, by rfl⟩ : syracuseStep 2405065 = 1803799) (by norm_num)
theorem B3206753 : Blo 2137435 3206753 := bstep (se 2 (by rfl) ⟨1202532, by rfl⟩ : syracuseStep 3206753 = 2405065) B2405065
theorem B2137835 : Blo 2137435 2137835 := bstep (se 1 (by rfl) ⟨1603376, by rfl⟩ : syracuseStep 2137835 = 3206753) B3206753
theorem B2568305 : Blo 2137435 2568305 := bbase (se 2 (by rfl) ⟨963114, by rfl⟩ : syracuseStep 2568305 = 1926229) (by norm_num)
theorem B6848813 : Blo 2137435 6848813 := bstep (se 3 (by rfl) ⟨1284152, by rfl⟩ : syracuseStep 6848813 = 2568305) B2568305
theorem B18263501 : Blo 2137435 18263501 := bstep (se 3 (by rfl) ⟨3424406, by rfl⟩ : syracuseStep 18263501 = 6848813) B6848813
theorem B12175667 : Blo 2137435 12175667 := bstep (se 1 (by rfl) ⟨9131750, by rfl⟩ : syracuseStep 12175667 = 18263501) B18263501
theorem B8117111 : Blo 2137435 8117111 := bstep (se 1 (by rfl) ⟨6087833, by rfl⟩ : syracuseStep 8117111 = 12175667) B12175667
theorem B5411407 : Blo 2137435 5411407 := bstep (se 1 (by rfl) ⟨4058555, by rfl⟩ : syracuseStep 5411407 = 8117111) B8117111
theorem B7215209 : Blo 2137435 7215209 := bstep (se 2 (by rfl) ⟨2705703, by rfl⟩ : syracuseStep 7215209 = 5411407) B5411407
theorem B4810139 : Blo 2137435 4810139 := bstep (se 1 (by rfl) ⟨3607604, by rfl⟩ : syracuseStep 4810139 = 7215209) B7215209
theorem B3206759 : Blo 2137435 3206759 := bstep (se 1 (by rfl) ⟨2405069, by rfl⟩ : syracuseStep 3206759 = 4810139) B4810139
theorem B2137839 : Blo 2137435 2137839 := bstep (se 1 (by rfl) ⟨1603379, by rfl⟩ : syracuseStep 2137839 = 3206759) B3206759
theorem B3206765 : Blo 2137435 3206765 := bbase (se 3 (by rfl) ⟨601268, by rfl⟩ : syracuseStep 3206765 = 1202537) (by norm_num)
theorem B2137843 : Blo 2137435 2137843 := bstep (se 1 (by rfl) ⟨1603382, by rfl⟩ : syracuseStep 2137843 = 3206765) B3206765
theorem B4810157 : Blo 2137435 4810157 := bbase (se 3 (by rfl) ⟨901904, by rfl⟩ : syracuseStep 4810157 = 1803809) (by norm_num)
theorem B3206771 : Blo 2137435 3206771 := bstep (se 1 (by rfl) ⟨2405078, by rfl⟩ : syracuseStep 3206771 = 4810157) B4810157
theorem B2137847 : Blo 2137435 2137847 := bstep (se 1 (by rfl) ⟨1603385, by rfl⟩ : syracuseStep 2137847 = 3206771) B3206771
theorem B2167021 : Blo 2137435 2167021 := bbase (se 3 (by rfl) ⟨406316, by rfl⟩ : syracuseStep 2167021 = 812633) (by norm_num)
theorem B2889361 : Blo 2137435 2889361 := bstep (se 2 (by rfl) ⟨1083510, by rfl⟩ : syracuseStep 2889361 = 2167021) B2167021
theorem B3852481 : Blo 2137435 3852481 := bstep (se 2 (by rfl) ⟨1444680, by rfl⟩ : syracuseStep 3852481 = 2889361) B2889361
theorem B5136641 : Blo 2137435 5136641 := bstep (se 2 (by rfl) ⟨1926240, by rfl⟩ : syracuseStep 5136641 = 3852481) B3852481
theorem B3424427 : Blo 2137435 3424427 := bstep (se 1 (by rfl) ⟨2568320, by rfl⟩ : syracuseStep 3424427 = 5136641) B5136641
theorem B2282951 : Blo 2137435 2282951 := bstep (se 1 (by rfl) ⟨1712213, by rfl⟩ : syracuseStep 2282951 = 3424427) B3424427
theorem B6087869 : Blo 2137435 6087869 := bstep (se 3 (by rfl) ⟨1141475, by rfl⟩ : syracuseStep 6087869 = 2282951) B2282951
theorem B4058579 : Blo 2137435 4058579 := bstep (se 1 (by rfl) ⟨3043934, by rfl⟩ : syracuseStep 4058579 = 6087869) B6087869
theorem B2705719 : Blo 2137435 2705719 := bstep (se 1 (by rfl) ⟨2029289, by rfl⟩ : syracuseStep 2705719 = 4058579) B4058579
theorem B3607625 : Blo 2137435 3607625 := bstep (se 2 (by rfl) ⟨1352859, by rfl⟩ : syracuseStep 3607625 = 2705719) B2705719
theorem B2405083 : Blo 2137435 2405083 := bstep (se 1 (by rfl) ⟨1803812, by rfl⟩ : syracuseStep 2405083 = 3607625) B3607625
theorem B3206777 : Blo 2137435 3206777 := bstep (se 2 (by rfl) ⟨1202541, by rfl⟩ : syracuseStep 3206777 = 2405083) B2405083
theorem B2137851 : Blo 2137435 2137851 := bstep (se 1 (by rfl) ⟨1603388, by rfl⟩ : syracuseStep 2137851 = 3206777) B3206777
theorem B9510709 : Blo 2137435 9510709 := bbase (se 5 (by rfl) ⟨445814, by rfl⟩ : syracuseStep 9510709 = 891629) (by norm_num)
theorem B12680945 : Blo 2137435 12680945 := bstep (se 2 (by rfl) ⟨4755354, by rfl⟩ : syracuseStep 12680945 = 9510709) B9510709
theorem B8453963 : Blo 2137435 8453963 := bstep (se 1 (by rfl) ⟨6340472, by rfl⟩ : syracuseStep 8453963 = 12680945) B12680945
theorem B5635975 : Blo 2137435 5635975 := bstep (se 1 (by rfl) ⟨4226981, by rfl⟩ : syracuseStep 5635975 = 8453963) B8453963
theorem B7514633 : Blo 2137435 7514633 := bstep (se 2 (by rfl) ⟨2817987, by rfl⟩ : syracuseStep 7514633 = 5635975) B5635975
theorem B20039021 : Blo 2137435 20039021 := bstep (se 3 (by rfl) ⟨3757316, by rfl⟩ : syracuseStep 20039021 = 7514633) B7514633
theorem B13359347 : Blo 2137435 13359347 := bstep (se 1 (by rfl) ⟨10019510, by rfl⟩ : syracuseStep 13359347 = 20039021) B20039021
theorem B8906231 : Blo 2137435 8906231 := bstep (se 1 (by rfl) ⟨6679673, by rfl⟩ : syracuseStep 8906231 = 13359347) B13359347
theorem B23749949 : Blo 2137435 23749949 := bstep (se 3 (by rfl) ⟨4453115, by rfl⟩ : syracuseStep 23749949 = 8906231) B8906231
theorem B63333197 : Blo 2137435 63333197 := bstep (se 3 (by rfl) ⟨11874974, by rfl⟩ : syracuseStep 63333197 = 23749949) B23749949
theorem B42222131 : Blo 2137435 42222131 := bstep (se 1 (by rfl) ⟨31666598, by rfl⟩ : syracuseStep 42222131 = 63333197) B63333197
theorem B28148087 : Blo 2137435 28148087 := bstep (se 1 (by rfl) ⟨21111065, by rfl⟩ : syracuseStep 28148087 = 42222131) B42222131
theorem B18765391 : Blo 2137435 18765391 := bstep (se 1 (by rfl) ⟨14074043, by rfl⟩ : syracuseStep 18765391 = 28148087) B28148087
theorem B25020521 : Blo 2137435 25020521 := bstep (se 2 (by rfl) ⟨9382695, by rfl⟩ : syracuseStep 25020521 = 18765391) B18765391
theorem B16680347 : Blo 2137435 16680347 := bstep (se 1 (by rfl) ⟨12510260, by rfl⟩ : syracuseStep 16680347 = 25020521) B25020521
theorem B11120231 : Blo 2137435 11120231 := bstep (se 1 (by rfl) ⟨8340173, by rfl⟩ : syracuseStep 11120231 = 16680347) B16680347
theorem B7413487 : Blo 2137435 7413487 := bstep (se 1 (by rfl) ⟨5560115, by rfl⟩ : syracuseStep 7413487 = 11120231) B11120231
theorem B39538597 : Blo 2137435 39538597 := bstep (se 4 (by rfl) ⟨3706743, by rfl⟩ : syracuseStep 39538597 = 7413487) B7413487
theorem B52718129 : Blo 2137435 52718129 := bstep (se 2 (by rfl) ⟨19769298, by rfl⟩ : syracuseStep 52718129 = 39538597) B39538597
theorem B35145419 : Blo 2137435 35145419 := bstep (se 1 (by rfl) ⟨26359064, by rfl⟩ : syracuseStep 35145419 = 52718129) B52718129
theorem B374884469 : Blo 2137435 374884469 := bstep (se 5 (by rfl) ⟨17572709, by rfl⟩ : syracuseStep 374884469 = 35145419) B35145419
theorem B249922979 : Blo 2137435 249922979 := bstep (se 1 (by rfl) ⟨187442234, by rfl⟩ : syracuseStep 249922979 = 374884469) B374884469
theorem B166615319 : Blo 2137435 166615319 := bstep (se 1 (by rfl) ⟨124961489, by rfl⟩ : syracuseStep 166615319 = 249922979) B249922979
theorem B444307517 : Blo 2137435 444307517 := bstep (se 3 (by rfl) ⟨83307659, by rfl⟩ : syracuseStep 444307517 = 166615319) B166615319
theorem B296205011 : Blo 2137435 296205011 := bstep (se 1 (by rfl) ⟨222153758, by rfl⟩ : syracuseStep 296205011 = 444307517) B444307517
theorem B197470007 : Blo 2137435 197470007 := bstep (se 1 (by rfl) ⟨148102505, by rfl⟩ : syracuseStep 197470007 = 296205011) B296205011
theorem B131646671 : Blo 2137435 131646671 := bstep (se 1 (by rfl) ⟨98735003, by rfl⟩ : syracuseStep 131646671 = 197470007) B197470007
theorem B87764447 : Blo 2137435 87764447 := bstep (se 1 (by rfl) ⟨65823335, by rfl⟩ : syracuseStep 87764447 = 131646671) B131646671
theorem B58509631 : Blo 2137435 58509631 := bstep (se 1 (by rfl) ⟨43882223, by rfl⟩ : syracuseStep 58509631 = 87764447) B87764447
theorem B312051365 : Blo 2137435 312051365 := bstep (se 4 (by rfl) ⟨29254815, by rfl⟩ : syracuseStep 312051365 = 58509631) B58509631
theorem B208034243 : Blo 2137435 208034243 := bstep (se 1 (by rfl) ⟨156025682, by rfl⟩ : syracuseStep 208034243 = 312051365) B312051365
theorem B138689495 : Blo 2137435 138689495 := bstep (se 1 (by rfl) ⟨104017121, by rfl⟩ : syracuseStep 138689495 = 208034243) B208034243
theorem B92459663 : Blo 2137435 92459663 := bstep (se 1 (by rfl) ⟨69344747, by rfl⟩ : syracuseStep 92459663 = 138689495) B138689495
theorem B61639775 : Blo 2137435 61639775 := bstep (se 1 (by rfl) ⟨46229831, by rfl⟩ : syracuseStep 61639775 = 92459663) B92459663
theorem B41093183 : Blo 2137435 41093183 := bstep (se 1 (by rfl) ⟨30819887, by rfl⟩ : syracuseStep 41093183 = 61639775) B61639775
theorem B27395455 : Blo 2137435 27395455 := bstep (se 1 (by rfl) ⟨20546591, by rfl⟩ : syracuseStep 27395455 = 41093183) B41093183
theorem B36527273 : Blo 2137435 36527273 := bstep (se 2 (by rfl) ⟨13697727, by rfl⟩ : syracuseStep 36527273 = 27395455) B27395455
theorem B24351515 : Blo 2137435 24351515 := bstep (se 1 (by rfl) ⟨18263636, by rfl⟩ : syracuseStep 24351515 = 36527273) B36527273
theorem B16234343 : Blo 2137435 16234343 := bstep (se 1 (by rfl) ⟨12175757, by rfl⟩ : syracuseStep 16234343 = 24351515) B24351515
theorem B10822895 : Blo 2137435 10822895 := bstep (se 1 (by rfl) ⟨8117171, by rfl⟩ : syracuseStep 10822895 = 16234343) B16234343
theorem B7215263 : Blo 2137435 7215263 := bstep (se 1 (by rfl) ⟨5411447, by rfl⟩ : syracuseStep 7215263 = 10822895) B10822895
theorem B4810175 : Blo 2137435 4810175 := bstep (se 1 (by rfl) ⟨3607631, by rfl⟩ : syracuseStep 4810175 = 7215263) B7215263
theorem B3206783 : Blo 2137435 3206783 := bstep (se 1 (by rfl) ⟨2405087, by rfl⟩ : syracuseStep 3206783 = 4810175) B4810175
theorem B2137855 : Blo 2137435 2137855 := bstep (se 1 (by rfl) ⟨1603391, by rfl⟩ : syracuseStep 2137855 = 3206783) B3206783
theorem B3206789 : Blo 2137435 3206789 := bbase (se 4 (by rfl) ⟨300636, by rfl⟩ : syracuseStep 3206789 = 601273) (by norm_num)
theorem B2137859 : Blo 2137435 2137859 := bstep (se 1 (by rfl) ⟨1603394, by rfl⟩ : syracuseStep 2137859 = 3206789) B3206789
theorem B3607645 : Blo 2137435 3607645 := bbase (se 3 (by rfl) ⟨676433, by rfl⟩ : syracuseStep 3607645 = 1352867) (by norm_num)
theorem B4810193 : Blo 2137435 4810193 := bstep (se 2 (by rfl) ⟨1803822, by rfl⟩ : syracuseStep 4810193 = 3607645) B3607645
theorem B3206795 : Blo 2137435 3206795 := bstep (se 1 (by rfl) ⟨2405096, by rfl⟩ : syracuseStep 3206795 = 4810193) B4810193
theorem B2137863 : Blo 2137435 2137863 := bstep (se 1 (by rfl) ⟨1603397, by rfl⟩ : syracuseStep 2137863 = 3206795) B3206795
theorem B2405101 : Blo 2137435 2405101 := bbase (se 3 (by rfl) ⟨450956, by rfl⟩ : syracuseStep 2405101 = 901913) (by norm_num)
theorem B3206801 : Blo 2137435 3206801 := bstep (se 2 (by rfl) ⟨1202550, by rfl⟩ : syracuseStep 3206801 = 2405101) B2405101
theorem B2137867 : Blo 2137435 2137867 := bstep (se 1 (by rfl) ⟨1603400, by rfl⟩ : syracuseStep 2137867 = 3206801) B3206801
theorem B7215317 : Blo 2137435 7215317 := bbase (se 7 (by rfl) ⟨84554, by rfl⟩ : syracuseStep 7215317 = 169109) (by norm_num)
theorem B4810211 : Blo 2137435 4810211 := bstep (se 1 (by rfl) ⟨3607658, by rfl⟩ : syracuseStep 4810211 = 7215317) B7215317
theorem B3206807 : Blo 2137435 3206807 := bstep (se 1 (by rfl) ⟨2405105, by rfl⟩ : syracuseStep 3206807 = 4810211) B4810211
theorem B2137871 : Blo 2137435 2137871 := bstep (se 1 (by rfl) ⟨1603403, by rfl⟩ : syracuseStep 2137871 = 3206807) B3206807
theorem B3206813 : Blo 2137435 3206813 := bbase (se 3 (by rfl) ⟨601277, by rfl⟩ : syracuseStep 3206813 = 1202555) (by norm_num)
theorem B2137875 : Blo 2137435 2137875 := bstep (se 1 (by rfl) ⟨1603406, by rfl⟩ : syracuseStep 2137875 = 3206813) B3206813
theorem B4810229 : Blo 2137435 4810229 := bbase (se 5 (by rfl) ⟨225479, by rfl⟩ : syracuseStep 4810229 = 450959) (by norm_num)
theorem B3206819 : Blo 2137435 3206819 := bstep (se 1 (by rfl) ⟨2405114, by rfl⟩ : syracuseStep 3206819 = 4810229) B4810229
theorem B2137879 : Blo 2137435 2137879 := bstep (se 1 (by rfl) ⟨1603409, by rfl⟩ : syracuseStep 2137879 = 3206819) B3206819
theorem B17572949 : Blo 2137435 17572949 := bbase (se 8 (by rfl) ⟨102966, by rfl⟩ : syracuseStep 17572949 = 205933) (by norm_num)
theorem B11715299 : Blo 2137435 11715299 := bstep (se 1 (by rfl) ⟨8786474, by rfl⟩ : syracuseStep 11715299 = 17572949) B17572949
theorem B7810199 : Blo 2137435 7810199 := bstep (se 1 (by rfl) ⟨5857649, by rfl⟩ : syracuseStep 7810199 = 11715299) B11715299
theorem B5206799 : Blo 2137435 5206799 := bstep (se 1 (by rfl) ⟨3905099, by rfl⟩ : syracuseStep 5206799 = 7810199) B7810199
theorem B13884797 : Blo 2137435 13884797 := bstep (se 3 (by rfl) ⟨2603399, by rfl⟩ : syracuseStep 13884797 = 5206799) B5206799
theorem B9256531 : Blo 2137435 9256531 := bstep (se 1 (by rfl) ⟨6942398, by rfl⟩ : syracuseStep 9256531 = 13884797) B13884797
theorem B12342041 : Blo 2137435 12342041 := bstep (se 2 (by rfl) ⟨4628265, by rfl⟩ : syracuseStep 12342041 = 9256531) B9256531
theorem B8228027 : Blo 2137435 8228027 := bstep (se 1 (by rfl) ⟨6171020, by rfl⟩ : syracuseStep 8228027 = 12342041) B12342041
theorem B21941405 : Blo 2137435 21941405 := bstep (se 3 (by rfl) ⟨4114013, by rfl⟩ : syracuseStep 21941405 = 8228027) B8228027
theorem B14627603 : Blo 2137435 14627603 := bstep (se 1 (by rfl) ⟨10970702, by rfl⟩ : syracuseStep 14627603 = 21941405) B21941405
theorem B9751735 : Blo 2137435 9751735 := bstep (se 1 (by rfl) ⟨7313801, by rfl⟩ : syracuseStep 9751735 = 14627603) B14627603
theorem B52009253 : Blo 2137435 52009253 := bstep (se 4 (by rfl) ⟨4875867, by rfl⟩ : syracuseStep 52009253 = 9751735) B9751735
theorem B34672835 : Blo 2137435 34672835 := bstep (se 1 (by rfl) ⟨26004626, by rfl⟩ : syracuseStep 34672835 = 52009253) B52009253
theorem B23115223 : Blo 2137435 23115223 := bstep (se 1 (by rfl) ⟨17336417, by rfl⟩ : syracuseStep 23115223 = 34672835) B34672835
theorem B30820297 : Blo 2137435 30820297 := bstep (se 2 (by rfl) ⟨11557611, by rfl⟩ : syracuseStep 30820297 = 23115223) B23115223
theorem B41093729 : Blo 2137435 41093729 := bstep (se 2 (by rfl) ⟨15410148, by rfl⟩ : syracuseStep 41093729 = 30820297) B30820297
theorem B27395819 : Blo 2137435 27395819 := bstep (se 1 (by rfl) ⟨20546864, by rfl⟩ : syracuseStep 27395819 = 41093729) B41093729
theorem B18263879 : Blo 2137435 18263879 := bstep (se 1 (by rfl) ⟨13697909, by rfl⟩ : syracuseStep 18263879 = 27395819) B27395819
theorem B12175919 : Blo 2137435 12175919 := bstep (se 1 (by rfl) ⟨9131939, by rfl⟩ : syracuseStep 12175919 = 18263879) B18263879
theorem B8117279 : Blo 2137435 8117279 := bstep (se 1 (by rfl) ⟨6087959, by rfl⟩ : syracuseStep 8117279 = 12175919) B12175919
theorem B5411519 : Blo 2137435 5411519 := bstep (se 1 (by rfl) ⟨4058639, by rfl⟩ : syracuseStep 5411519 = 8117279) B8117279
theorem B3607679 : Blo 2137435 3607679 := bstep (se 1 (by rfl) ⟨2705759, by rfl⟩ : syracuseStep 3607679 = 5411519) B5411519
theorem B2405119 : Blo 2137435 2405119 := bstep (se 1 (by rfl) ⟨1803839, by rfl⟩ : syracuseStep 2405119 = 3607679) B3607679
theorem B3206825 : Blo 2137435 3206825 := bstep (se 2 (by rfl) ⟨1202559, by rfl⟩ : syracuseStep 3206825 = 2405119) B2405119
theorem B2137883 : Blo 2137435 2137883 := bstep (se 1 (by rfl) ⟨1603412, by rfl⟩ : syracuseStep 2137883 = 3206825) B3206825
theorem B2282989 : Blo 2137435 2282989 := bbase (se 3 (by rfl) ⟨428060, by rfl⟩ : syracuseStep 2282989 = 856121) (by norm_num)
theorem B3043985 : Blo 2137435 3043985 := bstep (se 2 (by rfl) ⟨1141494, by rfl⟩ : syracuseStep 3043985 = 2282989) B2282989
theorem B8117293 : Blo 2137435 8117293 := bstep (se 3 (by rfl) ⟨1521992, by rfl⟩ : syracuseStep 8117293 = 3043985) B3043985
theorem B10823057 : Blo 2137435 10823057 := bstep (se 2 (by rfl) ⟨4058646, by rfl⟩ : syracuseStep 10823057 = 8117293) B8117293
theorem B7215371 : Blo 2137435 7215371 := bstep (se 1 (by rfl) ⟨5411528, by rfl⟩ : syracuseStep 7215371 = 10823057) B10823057
theorem B4810247 : Blo 2137435 4810247 := bstep (se 1 (by rfl) ⟨3607685, by rfl⟩ : syracuseStep 4810247 = 7215371) B7215371
theorem B3206831 : Blo 2137435 3206831 := bstep (se 1 (by rfl) ⟨2405123, by rfl⟩ : syracuseStep 3206831 = 4810247) B4810247
theorem B2137887 : Blo 2137435 2137887 := bstep (se 1 (by rfl) ⟨1603415, by rfl⟩ : syracuseStep 2137887 = 3206831) B3206831
theorem B3206837 : Blo 2137435 3206837 := bbase (se 5 (by rfl) ⟨150320, by rfl⟩ : syracuseStep 3206837 = 300641) (by norm_num)
theorem B2137891 : Blo 2137435 2137891 := bstep (se 1 (by rfl) ⟨1603418, by rfl⟩ : syracuseStep 2137891 = 3206837) B3206837
theorem B5411549 : Blo 2137435 5411549 := bbase (se 3 (by rfl) ⟨1014665, by rfl⟩ : syracuseStep 5411549 = 2029331) (by norm_num)
theorem B3607699 : Blo 2137435 3607699 := bstep (se 1 (by rfl) ⟨2705774, by rfl⟩ : syracuseStep 3607699 = 5411549) B5411549
theorem B4810265 : Blo 2137435 4810265 := bstep (se 2 (by rfl) ⟨1803849, by rfl⟩ : syracuseStep 4810265 = 3607699) B3607699
theorem B3206843 : Blo 2137435 3206843 := bstep (se 1 (by rfl) ⟨2405132, by rfl⟩ : syracuseStep 3206843 = 4810265) B4810265
theorem B2137895 : Blo 2137435 2137895 := bstep (se 1 (by rfl) ⟨1603421, by rfl⟩ : syracuseStep 2137895 = 3206843) B3206843
theorem B2405137 : Blo 2137435 2405137 := bbase (se 2 (by rfl) ⟨901926, by rfl⟩ : syracuseStep 2405137 = 1803853) (by norm_num)
theorem B3206849 : Blo 2137435 3206849 := bstep (se 2 (by rfl) ⟨1202568, by rfl⟩ : syracuseStep 3206849 = 2405137) B2405137
theorem B2137899 : Blo 2137435 2137899 := bstep (se 1 (by rfl) ⟨1603424, by rfl⟩ : syracuseStep 2137899 = 3206849) B3206849
theorem B4058677 : Blo 2137435 4058677 := bbase (se 5 (by rfl) ⟨190250, by rfl⟩ : syracuseStep 4058677 = 380501) (by norm_num)
theorem B5411569 : Blo 2137435 5411569 := bstep (se 2 (by rfl) ⟨2029338, by rfl⟩ : syracuseStep 5411569 = 4058677) B4058677
theorem B7215425 : Blo 2137435 7215425 := bstep (se 2 (by rfl) ⟨2705784, by rfl⟩ : syracuseStep 7215425 = 5411569) B5411569
theorem B4810283 : Blo 2137435 4810283 := bstep (se 1 (by rfl) ⟨3607712, by rfl⟩ : syracuseStep 4810283 = 7215425) B7215425
theorem B3206855 : Blo 2137435 3206855 := bstep (se 1 (by rfl) ⟨2405141, by rfl⟩ : syracuseStep 3206855 = 4810283) B4810283
theorem B2137903 : Blo 2137435 2137903 := bstep (se 1 (by rfl) ⟨1603427, by rfl⟩ : syracuseStep 2137903 = 3206855) B3206855
theorem B3206861 : Blo 2137435 3206861 := bbase (se 3 (by rfl) ⟨601286, by rfl⟩ : syracuseStep 3206861 = 1202573) (by norm_num)
theorem B2137907 : Blo 2137435 2137907 := bstep (se 1 (by rfl) ⟨1603430, by rfl⟩ : syracuseStep 2137907 = 3206861) B3206861
theorem B4810301 : Blo 2137435 4810301 := bbase (se 3 (by rfl) ⟨901931, by rfl⟩ : syracuseStep 4810301 = 1803863) (by norm_num)
theorem B3206867 : Blo 2137435 3206867 := bstep (se 1 (by rfl) ⟨2405150, by rfl⟩ : syracuseStep 3206867 = 4810301) B4810301
theorem B2137911 : Blo 2137435 2137911 := bstep (se 1 (by rfl) ⟨1603433, by rfl⟩ : syracuseStep 2137911 = 3206867) B3206867
theorem B3607733 : Blo 2137435 3607733 := bbase (se 5 (by rfl) ⟨169112, by rfl⟩ : syracuseStep 3607733 = 338225) (by norm_num)
theorem B2405155 : Blo 2137435 2405155 := bstep (se 1 (by rfl) ⟨1803866, by rfl⟩ : syracuseStep 2405155 = 3607733) B3607733
theorem B3206873 : Blo 2137435 3206873 := bstep (se 2 (by rfl) ⟨1202577, by rfl⟩ : syracuseStep 3206873 = 2405155) B2405155
theorem B2137915 : Blo 2137435 2137915 := bstep (se 1 (by rfl) ⟨1603436, by rfl⟩ : syracuseStep 2137915 = 3206873) B3206873
theorem B7705205 : Blo 2137435 7705205 := bbase (se 5 (by rfl) ⟨361181, by rfl⟩ : syracuseStep 7705205 = 722363) (by norm_num)
theorem B5136803 : Blo 2137435 5136803 := bstep (se 1 (by rfl) ⟨3852602, by rfl⟩ : syracuseStep 5136803 = 7705205) B7705205
theorem B3424535 : Blo 2137435 3424535 := bstep (se 1 (by rfl) ⟨2568401, by rfl⟩ : syracuseStep 3424535 = 5136803) B5136803
theorem B2283023 : Blo 2137435 2283023 := bstep (se 1 (by rfl) ⟨1712267, by rfl⟩ : syracuseStep 2283023 = 3424535) B3424535
theorem B6088061 : Blo 2137435 6088061 := bstep (se 3 (by rfl) ⟨1141511, by rfl⟩ : syracuseStep 6088061 = 2283023) B2283023
theorem B16234829 : Blo 2137435 16234829 := bstep (se 3 (by rfl) ⟨3044030, by rfl⟩ : syracuseStep 16234829 = 6088061) B6088061
theorem B10823219 : Blo 2137435 10823219 := bstep (se 1 (by rfl) ⟨8117414, by rfl⟩ : syracuseStep 10823219 = 16234829) B16234829
theorem B7215479 : Blo 2137435 7215479 := bstep (se 1 (by rfl) ⟨5411609, by rfl⟩ : syracuseStep 7215479 = 10823219) B10823219
theorem B4810319 : Blo 2137435 4810319 := bstep (se 1 (by rfl) ⟨3607739, by rfl⟩ : syracuseStep 4810319 = 7215479) B7215479
theorem B3206879 : Blo 2137435 3206879 := bstep (se 1 (by rfl) ⟨2405159, by rfl⟩ : syracuseStep 3206879 = 4810319) B4810319
theorem B2137919 : Blo 2137435 2137919 := bstep (se 1 (by rfl) ⟨1603439, by rfl⟩ : syracuseStep 2137919 = 3206879) B3206879
theorem B3206885 : Blo 2137435 3206885 := bbase (se 4 (by rfl) ⟨300645, by rfl⟩ : syracuseStep 3206885 = 601291) (by norm_num)
theorem B2137923 : Blo 2137435 2137923 := bstep (se 1 (by rfl) ⟨1603442, by rfl⟩ : syracuseStep 2137923 = 3206885) B3206885
theorem B6088085 : Blo 2137435 6088085 := bbase (se 6 (by rfl) ⟨142689, by rfl⟩ : syracuseStep 6088085 = 285379) (by norm_num)
theorem B4058723 : Blo 2137435 4058723 := bstep (se 1 (by rfl) ⟨3044042, by rfl⟩ : syracuseStep 4058723 = 6088085) B6088085
theorem B2705815 : Blo 2137435 2705815 := bstep (se 1 (by rfl) ⟨2029361, by rfl⟩ : syracuseStep 2705815 = 4058723) B4058723
theorem B3607753 : Blo 2137435 3607753 := bstep (se 2 (by rfl) ⟨1352907, by rfl⟩ : syracuseStep 3607753 = 2705815) B2705815
theorem B4810337 : Blo 2137435 4810337 := bstep (se 2 (by rfl) ⟨1803876, by rfl⟩ : syracuseStep 4810337 = 3607753) B3607753
theorem B3206891 : Blo 2137435 3206891 := bstep (se 1 (by rfl) ⟨2405168, by rfl⟩ : syracuseStep 3206891 = 4810337) B4810337
theorem B2137927 : Blo 2137435 2137927 := bstep (se 1 (by rfl) ⟨1603445, by rfl⟩ : syracuseStep 2137927 = 3206891) B3206891
theorem B2405173 : Blo 2137435 2405173 := bbase (se 5 (by rfl) ⟨112742, by rfl⟩ : syracuseStep 2405173 = 225485) (by norm_num)
theorem B3206897 : Blo 2137435 3206897 := bstep (se 2 (by rfl) ⟨1202586, by rfl⟩ : syracuseStep 3206897 = 2405173) B2405173
theorem B2137931 : Blo 2137435 2137931 := bstep (se 1 (by rfl) ⟨1603448, by rfl⟩ : syracuseStep 2137931 = 3206897) B3206897
theorem B2705825 : Blo 2137435 2705825 := bbase (se 2 (by rfl) ⟨1014684, by rfl⟩ : syracuseStep 2705825 = 2029369) (by norm_num)
theorem B7215533 : Blo 2137435 7215533 := bstep (se 3 (by rfl) ⟨1352912, by rfl⟩ : syracuseStep 7215533 = 2705825) B2705825
theorem B4810355 : Blo 2137435 4810355 := bstep (se 1 (by rfl) ⟨3607766, by rfl⟩ : syracuseStep 4810355 = 7215533) B7215533
theorem B3206903 : Blo 2137435 3206903 := bstep (se 1 (by rfl) ⟨2405177, by rfl⟩ : syracuseStep 3206903 = 4810355) B4810355
theorem B2137935 : Blo 2137435 2137935 := bstep (se 1 (by rfl) ⟨1603451, by rfl⟩ : syracuseStep 2137935 = 3206903) B3206903
theorem B3206909 : Blo 2137435 3206909 := bbase (se 3 (by rfl) ⟨601295, by rfl⟩ : syracuseStep 3206909 = 1202591) (by norm_num)
theorem B2137939 : Blo 2137435 2137939 := bstep (se 1 (by rfl) ⟨1603454, by rfl⟩ : syracuseStep 2137939 = 3206909) B3206909
theorem B4810373 : Blo 2137435 4810373 := bbase (se 4 (by rfl) ⟨450972, by rfl⟩ : syracuseStep 4810373 = 901945) (by norm_num)
theorem B3206915 : Blo 2137435 3206915 := bstep (se 1 (by rfl) ⟨2405186, by rfl⟩ : syracuseStep 3206915 = 4810373) B4810373
theorem B2137943 : Blo 2137435 2137943 := bstep (se 1 (by rfl) ⟨1603457, by rfl⟩ : syracuseStep 2137943 = 3206915) B3206915
theorem B2196685 : Blo 2137435 2196685 := bbase (se 3 (by rfl) ⟨411878, by rfl⟩ : syracuseStep 2196685 = 823757) (by norm_num)
theorem B11715653 : Blo 2137435 11715653 := bstep (se 4 (by rfl) ⟨1098342, by rfl⟩ : syracuseStep 11715653 = 2196685) B2196685
theorem B7810435 : Blo 2137435 7810435 := bstep (se 1 (by rfl) ⟨5857826, by rfl⟩ : syracuseStep 7810435 = 11715653) B11715653
theorem B41655653 : Blo 2137435 41655653 := bstep (se 4 (by rfl) ⟨3905217, by rfl⟩ : syracuseStep 41655653 = 7810435) B7810435
theorem B27770435 : Blo 2137435 27770435 := bstep (se 1 (by rfl) ⟨20827826, by rfl⟩ : syracuseStep 27770435 = 41655653) B41655653
theorem B18513623 : Blo 2137435 18513623 := bstep (se 1 (by rfl) ⟨13885217, by rfl⟩ : syracuseStep 18513623 = 27770435) B27770435
theorem B12342415 : Blo 2137435 12342415 := bstep (se 1 (by rfl) ⟨9256811, by rfl⟩ : syracuseStep 12342415 = 18513623) B18513623
theorem B16456553 : Blo 2137435 16456553 := bstep (se 2 (by rfl) ⟨6171207, by rfl⟩ : syracuseStep 16456553 = 12342415) B12342415
theorem B10971035 : Blo 2137435 10971035 := bstep (se 1 (by rfl) ⟨8228276, by rfl⟩ : syracuseStep 10971035 = 16456553) B16456553
theorem B7314023 : Blo 2137435 7314023 := bstep (se 1 (by rfl) ⟨5485517, by rfl⟩ : syracuseStep 7314023 = 10971035) B10971035
theorem B19504061 : Blo 2137435 19504061 := bstep (se 3 (by rfl) ⟨3657011, by rfl⟩ : syracuseStep 19504061 = 7314023) B7314023
theorem B13002707 : Blo 2137435 13002707 := bstep (se 1 (by rfl) ⟨9752030, by rfl⟩ : syracuseStep 13002707 = 19504061) B19504061
theorem B8668471 : Blo 2137435 8668471 := bstep (se 1 (by rfl) ⟨6501353, by rfl⟩ : syracuseStep 8668471 = 13002707) B13002707
theorem B11557961 : Blo 2137435 11557961 := bstep (se 2 (by rfl) ⟨4334235, by rfl⟩ : syracuseStep 11557961 = 8668471) B8668471
theorem B7705307 : Blo 2137435 7705307 := bstep (se 1 (by rfl) ⟨5778980, by rfl⟩ : syracuseStep 7705307 = 11557961) B11557961
theorem B5136871 : Blo 2137435 5136871 := bstep (se 1 (by rfl) ⟨3852653, by rfl⟩ : syracuseStep 5136871 = 7705307) B7705307
theorem B6849161 : Blo 2137435 6849161 := bstep (se 2 (by rfl) ⟨2568435, by rfl⟩ : syracuseStep 6849161 = 5136871) B5136871
theorem B4566107 : Blo 2137435 4566107 := bstep (se 1 (by rfl) ⟨3424580, by rfl⟩ : syracuseStep 4566107 = 6849161) B6849161
theorem B3044071 : Blo 2137435 3044071 := bstep (se 1 (by rfl) ⟨2283053, by rfl⟩ : syracuseStep 3044071 = 4566107) B4566107
theorem B4058761 : Blo 2137435 4058761 := bstep (se 2 (by rfl) ⟨1522035, by rfl⟩ : syracuseStep 4058761 = 3044071) B3044071
theorem B5411681 : Blo 2137435 5411681 := bstep (se 2 (by rfl) ⟨2029380, by rfl⟩ : syracuseStep 5411681 = 4058761) B4058761
theorem B3607787 : Blo 2137435 3607787 := bstep (se 1 (by rfl) ⟨2705840, by rfl⟩ : syracuseStep 3607787 = 5411681) B5411681
theorem B2405191 : Blo 2137435 2405191 := bstep (se 1 (by rfl) ⟨1803893, by rfl⟩ : syracuseStep 2405191 = 3607787) B3607787
theorem B3206921 : Blo 2137435 3206921 := bstep (se 2 (by rfl) ⟨1202595, by rfl⟩ : syracuseStep 3206921 = 2405191) B2405191
theorem B2137947 : Blo 2137435 2137947 := bstep (se 1 (by rfl) ⟨1603460, by rfl⟩ : syracuseStep 2137947 = 3206921) B3206921
theorem B10823381 : Blo 2137435 10823381 := bbase (se 7 (by rfl) ⟨126836, by rfl⟩ : syracuseStep 10823381 = 253673) (by norm_num)
theorem B7215587 : Blo 2137435 7215587 := bstep (se 1 (by rfl) ⟨5411690, by rfl⟩ : syracuseStep 7215587 = 10823381) B10823381
theorem B4810391 : Blo 2137435 4810391 := bstep (se 1 (by rfl) ⟨3607793, by rfl⟩ : syracuseStep 4810391 = 7215587) B7215587
theorem B3206927 : Blo 2137435 3206927 := bstep (se 1 (by rfl) ⟨2405195, by rfl⟩ : syracuseStep 3206927 = 4810391) B4810391
theorem B2137951 : Blo 2137435 2137951 := bstep (se 1 (by rfl) ⟨1603463, by rfl⟩ : syracuseStep 2137951 = 3206927) B3206927
theorem B3206933 : Blo 2137435 3206933 := bbase (se 6 (by rfl) ⟨75162, by rfl⟩ : syracuseStep 3206933 = 150325) (by norm_num)
theorem B2137955 : Blo 2137435 2137955 := bstep (se 1 (by rfl) ⟨1603466, by rfl⟩ : syracuseStep 2137955 = 3206933) B3206933
theorem B2742773 : Blo 2137435 2742773 := bbase (se 5 (by rfl) ⟨128567, by rfl⟩ : syracuseStep 2742773 = 257135) (by norm_num)
theorem B7314061 : Blo 2137435 7314061 := bstep (se 3 (by rfl) ⟨1371386, by rfl⟩ : syracuseStep 7314061 = 2742773) B2742773
theorem B9752081 : Blo 2137435 9752081 := bstep (se 2 (by rfl) ⟨3657030, by rfl⟩ : syracuseStep 9752081 = 7314061) B7314061
theorem B26005549 : Blo 2137435 26005549 := bstep (se 3 (by rfl) ⟨4876040, by rfl⟩ : syracuseStep 26005549 = 9752081) B9752081
theorem B34674065 : Blo 2137435 34674065 := bstep (se 2 (by rfl) ⟨13002774, by rfl⟩ : syracuseStep 34674065 = 26005549) B26005549
theorem B23116043 : Blo 2137435 23116043 := bstep (se 1 (by rfl) ⟨17337032, by rfl⟩ : syracuseStep 23116043 = 34674065) B34674065
theorem B61642781 : Blo 2137435 61642781 := bstep (se 3 (by rfl) ⟨11558021, by rfl⟩ : syracuseStep 61642781 = 23116043) B23116043
theorem B41095187 : Blo 2137435 41095187 := bstep (se 1 (by rfl) ⟨30821390, by rfl⟩ : syracuseStep 41095187 = 61642781) B61642781
theorem B27396791 : Blo 2137435 27396791 := bstep (se 1 (by rfl) ⟨20547593, by rfl⟩ : syracuseStep 27396791 = 41095187) B41095187
theorem B18264527 : Blo 2137435 18264527 := bstep (se 1 (by rfl) ⟨13698395, by rfl⟩ : syracuseStep 18264527 = 27396791) B27396791
theorem B12176351 : Blo 2137435 12176351 := bstep (se 1 (by rfl) ⟨9132263, by rfl⟩ : syracuseStep 12176351 = 18264527) B18264527
theorem B8117567 : Blo 2137435 8117567 := bstep (se 1 (by rfl) ⟨6088175, by rfl⟩ : syracuseStep 8117567 = 12176351) B12176351
theorem B5411711 : Blo 2137435 5411711 := bstep (se 1 (by rfl) ⟨4058783, by rfl⟩ : syracuseStep 5411711 = 8117567) B8117567
theorem B3607807 : Blo 2137435 3607807 := bstep (se 1 (by rfl) ⟨2705855, by rfl⟩ : syracuseStep 3607807 = 5411711) B5411711
theorem B4810409 : Blo 2137435 4810409 := bstep (se 2 (by rfl) ⟨1803903, by rfl⟩ : syracuseStep 4810409 = 3607807) B3607807
theorem B3206939 : Blo 2137435 3206939 := bstep (se 1 (by rfl) ⟨2405204, by rfl⟩ : syracuseStep 3206939 = 4810409) B4810409
theorem B2137959 : Blo 2137435 2137959 := bstep (se 1 (by rfl) ⟨1603469, by rfl⟩ : syracuseStep 2137959 = 3206939) B3206939
theorem B2405209 : Blo 2137435 2405209 := bbase (se 2 (by rfl) ⟨901953, by rfl⟩ : syracuseStep 2405209 = 1803907) (by norm_num)
theorem B3206945 : Blo 2137435 3206945 := bstep (se 2 (by rfl) ⟨1202604, by rfl⟩ : syracuseStep 3206945 = 2405209) B2405209
theorem B2137963 : Blo 2137435 2137963 := bstep (se 1 (by rfl) ⟨1603472, by rfl⟩ : syracuseStep 2137963 = 3206945) B3206945
theorem B4566149 : Blo 2137435 4566149 := bbase (se 4 (by rfl) ⟨428076, by rfl⟩ : syracuseStep 4566149 = 856153) (by norm_num)
theorem B3044099 : Blo 2137435 3044099 := bstep (se 1 (by rfl) ⟨2283074, by rfl⟩ : syracuseStep 3044099 = 4566149) B4566149
theorem B8117597 : Blo 2137435 8117597 := bstep (se 3 (by rfl) ⟨1522049, by rfl⟩ : syracuseStep 8117597 = 3044099) B3044099
theorem B5411731 : Blo 2137435 5411731 := bstep (se 1 (by rfl) ⟨4058798, by rfl⟩ : syracuseStep 5411731 = 8117597) B8117597
theorem B7215641 : Blo 2137435 7215641 := bstep (se 2 (by rfl) ⟨2705865, by rfl⟩ : syracuseStep 7215641 = 5411731) B5411731
theorem B4810427 : Blo 2137435 4810427 := bstep (se 1 (by rfl) ⟨3607820, by rfl⟩ : syracuseStep 4810427 = 7215641) B7215641
theorem B3206951 : Blo 2137435 3206951 := bstep (se 1 (by rfl) ⟨2405213, by rfl⟩ : syracuseStep 3206951 = 4810427) B4810427
theorem B2137967 : Blo 2137435 2137967 := bstep (se 1 (by rfl) ⟨1603475, by rfl⟩ : syracuseStep 2137967 = 3206951) B3206951
theorem B3206957 : Blo 2137435 3206957 := bbase (se 3 (by rfl) ⟨601304, by rfl⟩ : syracuseStep 3206957 = 1202609) (by norm_num)
theorem B2137971 : Blo 2137435 2137971 := bstep (se 1 (by rfl) ⟨1603478, by rfl⟩ : syracuseStep 2137971 = 3206957) B3206957
theorem B4810445 : Blo 2137435 4810445 := bbase (se 3 (by rfl) ⟨901958, by rfl⟩ : syracuseStep 4810445 = 1803917) (by norm_num)
theorem B3206963 : Blo 2137435 3206963 := bstep (se 1 (by rfl) ⟨2405222, by rfl⟩ : syracuseStep 3206963 = 4810445) B4810445
theorem B2137975 : Blo 2137435 2137975 := bstep (se 1 (by rfl) ⟨1603481, by rfl⟩ : syracuseStep 2137975 = 3206963) B3206963
theorem B2705881 : Blo 2137435 2705881 := bbase (se 2 (by rfl) ⟨1014705, by rfl⟩ : syracuseStep 2705881 = 2029411) (by norm_num)
theorem B3607841 : Blo 2137435 3607841 := bstep (se 2 (by rfl) ⟨1352940, by rfl⟩ : syracuseStep 3607841 = 2705881) B2705881
theorem B2405227 : Blo 2137435 2405227 := bstep (se 1 (by rfl) ⟨1803920, by rfl⟩ : syracuseStep 2405227 = 3607841) B3607841
theorem B3206969 : Blo 2137435 3206969 := bstep (se 2 (by rfl) ⟨1202613, by rfl⟩ : syracuseStep 3206969 = 2405227) B2405227
theorem B2137979 : Blo 2137435 2137979 := bstep (se 1 (by rfl) ⟨1603484, by rfl⟩ : syracuseStep 2137979 = 3206969) B3206969
theorem B3424637 : Blo 2137435 3424637 := bbase (se 3 (by rfl) ⟨642119, by rfl⟩ : syracuseStep 3424637 = 1284239) (by norm_num)
theorem B9132365 : Blo 2137435 9132365 := bstep (se 3 (by rfl) ⟨1712318, by rfl⟩ : syracuseStep 9132365 = 3424637) B3424637
theorem B24352973 : Blo 2137435 24352973 := bstep (se 3 (by rfl) ⟨4566182, by rfl⟩ : syracuseStep 24352973 = 9132365) B9132365
theorem B16235315 : Blo 2137435 16235315 := bstep (se 1 (by rfl) ⟨12176486, by rfl⟩ : syracuseStep 16235315 = 24352973) B24352973
theorem B10823543 : Blo 2137435 10823543 := bstep (se 1 (by rfl) ⟨8117657, by rfl⟩ : syracuseStep 10823543 = 16235315) B16235315
theorem B7215695 : Blo 2137435 7215695 := bstep (se 1 (by rfl) ⟨5411771, by rfl⟩ : syracuseStep 7215695 = 10823543) B10823543
theorem B4810463 : Blo 2137435 4810463 := bstep (se 1 (by rfl) ⟨3607847, by rfl⟩ : syracuseStep 4810463 = 7215695) B7215695
theorem B3206975 : Blo 2137435 3206975 := bstep (se 1 (by rfl) ⟨2405231, by rfl⟩ : syracuseStep 3206975 = 4810463) B4810463
theorem B2137983 : Blo 2137435 2137983 := bstep (se 1 (by rfl) ⟨1603487, by rfl⟩ : syracuseStep 2137983 = 3206975) B3206975
theorem B3206981 : Blo 2137435 3206981 := bbase (se 4 (by rfl) ⟨300654, by rfl⟩ : syracuseStep 3206981 = 601309) (by norm_num)
theorem B2137987 : Blo 2137435 2137987 := bstep (se 1 (by rfl) ⟨1603490, by rfl⟩ : syracuseStep 2137987 = 3206981) B3206981
theorem B3607861 : Blo 2137435 3607861 := bbase (se 5 (by rfl) ⟨169118, by rfl⟩ : syracuseStep 3607861 = 338237) (by norm_num)
theorem B4810481 : Blo 2137435 4810481 := bstep (se 2 (by rfl) ⟨1803930, by rfl⟩ : syracuseStep 4810481 = 3607861) B3607861
theorem B3206987 : Blo 2137435 3206987 := bstep (se 1 (by rfl) ⟨2405240, by rfl⟩ : syracuseStep 3206987 = 4810481) B4810481
theorem B2137991 : Blo 2137435 2137991 := bstep (se 1 (by rfl) ⟨1603493, by rfl⟩ : syracuseStep 2137991 = 3206987) B3206987
theorem B2405245 : Blo 2137435 2405245 := bbase (se 3 (by rfl) ⟨450983, by rfl⟩ : syracuseStep 2405245 = 901967) (by norm_num)
theorem B3206993 : Blo 2137435 3206993 := bstep (se 2 (by rfl) ⟨1202622, by rfl⟩ : syracuseStep 3206993 = 2405245) B2405245
theorem B2137995 : Blo 2137435 2137995 := bstep (se 1 (by rfl) ⟨1603496, by rfl⟩ : syracuseStep 2137995 = 3206993) B3206993
theorem B7215749 : Blo 2137435 7215749 := bbase (se 4 (by rfl) ⟨676476, by rfl⟩ : syracuseStep 7215749 = 1352953) (by norm_num)
theorem B4810499 : Blo 2137435 4810499 := bstep (se 1 (by rfl) ⟨3607874, by rfl⟩ : syracuseStep 4810499 = 7215749) B7215749
theorem B3206999 : Blo 2137435 3206999 := bstep (se 1 (by rfl) ⟨2405249, by rfl⟩ : syracuseStep 3206999 = 4810499) B4810499
theorem B2137999 : Blo 2137435 2137999 := bstep (se 1 (by rfl) ⟨1603499, by rfl⟩ : syracuseStep 2137999 = 3206999) B3206999
theorem B3207005 : Blo 2137435 3207005 := bbase (se 3 (by rfl) ⟨601313, by rfl⟩ : syracuseStep 3207005 = 1202627) (by norm_num)
theorem B2138003 : Blo 2137435 2138003 := bstep (se 1 (by rfl) ⟨1603502, by rfl⟩ : syracuseStep 2138003 = 3207005) B3207005
theorem B4810517 : Blo 2137435 4810517 := bbase (se 6 (by rfl) ⟨112746, by rfl⟩ : syracuseStep 4810517 = 225493) (by norm_num)
theorem B3207011 : Blo 2137435 3207011 := bstep (se 1 (by rfl) ⟨2405258, by rfl⟩ : syracuseStep 3207011 = 4810517) B4810517
theorem B2138007 : Blo 2137435 2138007 := bstep (se 1 (by rfl) ⟨1603505, by rfl⟩ : syracuseStep 2138007 = 3207011) B3207011
theorem B8117765 : Blo 2137435 8117765 := bbase (se 4 (by rfl) ⟨761040, by rfl⟩ : syracuseStep 8117765 = 1522081) (by norm_num)
theorem B5411843 : Blo 2137435 5411843 := bstep (se 1 (by rfl) ⟨4058882, by rfl⟩ : syracuseStep 5411843 = 8117765) B8117765
theorem B3607895 : Blo 2137435 3607895 := bstep (se 1 (by rfl) ⟨2705921, by rfl⟩ : syracuseStep 3607895 = 5411843) B5411843
theorem B2405263 : Blo 2137435 2405263 := bstep (se 1 (by rfl) ⟨1803947, by rfl⟩ : syracuseStep 2405263 = 3607895) B3607895
theorem B3207017 : Blo 2137435 3207017 := bstep (se 2 (by rfl) ⟨1202631, by rfl⟩ : syracuseStep 3207017 = 2405263) B2405263
theorem B2138011 : Blo 2137435 2138011 := bstep (se 1 (by rfl) ⟨1603508, by rfl⟩ : syracuseStep 2138011 = 3207017) B3207017
theorem B2603561 : Blo 2137435 2603561 := bbase (se 2 (by rfl) ⟨976335, by rfl⟩ : syracuseStep 2603561 = 1952671) (by norm_num)
theorem B6942829 : Blo 2137435 6942829 := bstep (se 3 (by rfl) ⟨1301780, by rfl⟩ : syracuseStep 6942829 = 2603561) B2603561
theorem B9257105 : Blo 2137435 9257105 := bstep (se 2 (by rfl) ⟨3471414, by rfl⟩ : syracuseStep 9257105 = 6942829) B6942829
theorem B6171403 : Blo 2137435 6171403 := bstep (se 1 (by rfl) ⟨4628552, by rfl⟩ : syracuseStep 6171403 = 9257105) B9257105
theorem B8228537 : Blo 2137435 8228537 := bstep (se 2 (by rfl) ⟨3085701, by rfl⟩ : syracuseStep 8228537 = 6171403) B6171403
theorem B5485691 : Blo 2137435 5485691 := bstep (se 1 (by rfl) ⟨4114268, by rfl⟩ : syracuseStep 5485691 = 8228537) B8228537
theorem B14628509 : Blo 2137435 14628509 := bstep (se 3 (by rfl) ⟨2742845, by rfl⟩ : syracuseStep 14628509 = 5485691) B5485691
theorem B9752339 : Blo 2137435 9752339 := bstep (se 1 (by rfl) ⟨7314254, by rfl⟩ : syracuseStep 9752339 = 14628509) B14628509
theorem B6501559 : Blo 2137435 6501559 := bstep (se 1 (by rfl) ⟨4876169, by rfl⟩ : syracuseStep 6501559 = 9752339) B9752339
theorem B8668745 : Blo 2137435 8668745 := bstep (se 2 (by rfl) ⟨3250779, by rfl⟩ : syracuseStep 8668745 = 6501559) B6501559
theorem B5779163 : Blo 2137435 5779163 := bstep (se 1 (by rfl) ⟨4334372, by rfl⟩ : syracuseStep 5779163 = 8668745) B8668745
theorem B3852775 : Blo 2137435 3852775 := bstep (se 1 (by rfl) ⟨2889581, by rfl⟩ : syracuseStep 3852775 = 5779163) B5779163
theorem B5137033 : Blo 2137435 5137033 := bstep (se 2 (by rfl) ⟨1926387, by rfl⟩ : syracuseStep 5137033 = 3852775) B3852775
theorem B6849377 : Blo 2137435 6849377 := bstep (se 2 (by rfl) ⟨2568516, by rfl⟩ : syracuseStep 6849377 = 5137033) B5137033
theorem B4566251 : Blo 2137435 4566251 := bstep (se 1 (by rfl) ⟨3424688, by rfl⟩ : syracuseStep 4566251 = 6849377) B6849377
theorem B12176669 : Blo 2137435 12176669 := bstep (se 3 (by rfl) ⟨2283125, by rfl⟩ : syracuseStep 12176669 = 4566251) B4566251
theorem B8117779 : Blo 2137435 8117779 := bstep (se 1 (by rfl) ⟨6088334, by rfl⟩ : syracuseStep 8117779 = 12176669) B12176669
theorem B10823705 : Blo 2137435 10823705 := bstep (se 2 (by rfl) ⟨4058889, by rfl⟩ : syracuseStep 10823705 = 8117779) B8117779
theorem B7215803 : Blo 2137435 7215803 := bstep (se 1 (by rfl) ⟨5411852, by rfl⟩ : syracuseStep 7215803 = 10823705) B10823705
theorem B4810535 : Blo 2137435 4810535 := bstep (se 1 (by rfl) ⟨3607901, by rfl⟩ : syracuseStep 4810535 = 7215803) B7215803
theorem B3207023 : Blo 2137435 3207023 := bstep (se 1 (by rfl) ⟨2405267, by rfl⟩ : syracuseStep 3207023 = 4810535) B4810535
theorem B2138015 : Blo 2137435 2138015 := bstep (se 1 (by rfl) ⟨1603511, by rfl⟩ : syracuseStep 2138015 = 3207023) B3207023
theorem B3207029 : Blo 2137435 3207029 := bbase (se 5 (by rfl) ⟨150329, by rfl⟩ : syracuseStep 3207029 = 300659) (by norm_num)
theorem B2138019 : Blo 2137435 2138019 := bstep (se 1 (by rfl) ⟨1603514, by rfl⟩ : syracuseStep 2138019 = 3207029) B3207029
theorem B4566269 : Blo 2137435 4566269 := bbase (se 3 (by rfl) ⟨856175, by rfl⟩ : syracuseStep 4566269 = 1712351) (by norm_num)
theorem B3044179 : Blo 2137435 3044179 := bstep (se 1 (by rfl) ⟨2283134, by rfl⟩ : syracuseStep 3044179 = 4566269) B4566269
theorem B4058905 : Blo 2137435 4058905 := bstep (se 2 (by rfl) ⟨1522089, by rfl⟩ : syracuseStep 4058905 = 3044179) B3044179
theorem B5411873 : Blo 2137435 5411873 := bstep (se 2 (by rfl) ⟨2029452, by rfl⟩ : syracuseStep 5411873 = 4058905) B4058905
theorem B3607915 : Blo 2137435 3607915 := bstep (se 1 (by rfl) ⟨2705936, by rfl⟩ : syracuseStep 3607915 = 5411873) B5411873
theorem B4810553 : Blo 2137435 4810553 := bstep (se 2 (by rfl) ⟨1803957, by rfl⟩ : syracuseStep 4810553 = 3607915) B3607915
theorem B3207035 : Blo 2137435 3207035 := bstep (se 1 (by rfl) ⟨2405276, by rfl⟩ : syracuseStep 3207035 = 4810553) B4810553
theorem B2138023 : Blo 2137435 2138023 := bstep (se 1 (by rfl) ⟨1603517, by rfl⟩ : syracuseStep 2138023 = 3207035) B3207035
theorem B2405281 : Blo 2137435 2405281 := bbase (se 2 (by rfl) ⟨901980, by rfl⟩ : syracuseStep 2405281 = 1803961) (by norm_num)
theorem B3207041 : Blo 2137435 3207041 := bstep (se 2 (by rfl) ⟨1202640, by rfl⟩ : syracuseStep 3207041 = 2405281) B2405281
theorem B2138027 : Blo 2137435 2138027 := bstep (se 1 (by rfl) ⟨1603520, by rfl⟩ : syracuseStep 2138027 = 3207041) B3207041
theorem B5411893 : Blo 2137435 5411893 := bbase (se 5 (by rfl) ⟨253682, by rfl⟩ : syracuseStep 5411893 = 507365) (by norm_num)
theorem B7215857 : Blo 2137435 7215857 := bstep (se 2 (by rfl) ⟨2705946, by rfl⟩ : syracuseStep 7215857 = 5411893) B5411893
theorem B4810571 : Blo 2137435 4810571 := bstep (se 1 (by rfl) ⟨3607928, by rfl⟩ : syracuseStep 4810571 = 7215857) B7215857
theorem B3207047 : Blo 2137435 3207047 := bstep (se 1 (by rfl) ⟨2405285, by rfl⟩ : syracuseStep 3207047 = 4810571) B4810571
theorem B2138031 : Blo 2137435 2138031 := bstep (se 1 (by rfl) ⟨1603523, by rfl⟩ : syracuseStep 2138031 = 3207047) B3207047
theorem B3207053 : Blo 2137435 3207053 := bbase (se 3 (by rfl) ⟨601322, by rfl⟩ : syracuseStep 3207053 = 1202645) (by norm_num)
theorem B2138035 : Blo 2137435 2138035 := bstep (se 1 (by rfl) ⟨1603526, by rfl⟩ : syracuseStep 2138035 = 3207053) B3207053
theorem B4810589 : Blo 2137435 4810589 := bbase (se 3 (by rfl) ⟨901985, by rfl⟩ : syracuseStep 4810589 = 1803971) (by norm_num)
theorem B3207059 : Blo 2137435 3207059 := bstep (se 1 (by rfl) ⟨2405294, by rfl⟩ : syracuseStep 3207059 = 4810589) B4810589
theorem B2138039 : Blo 2137435 2138039 := bstep (se 1 (by rfl) ⟨1603529, by rfl⟩ : syracuseStep 2138039 = 3207059) B3207059
theorem B3607949 : Blo 2137435 3607949 := bbase (se 3 (by rfl) ⟨676490, by rfl⟩ : syracuseStep 3607949 = 1352981) (by norm_num)
theorem B2405299 : Blo 2137435 2405299 := bstep (se 1 (by rfl) ⟨1803974, by rfl⟩ : syracuseStep 2405299 = 3607949) B3607949
theorem B3207065 : Blo 2137435 3207065 := bstep (se 2 (by rfl) ⟨1202649, by rfl⟩ : syracuseStep 3207065 = 2405299) B2405299
theorem B2138043 : Blo 2137435 2138043 := bstep (se 1 (by rfl) ⟨1603532, by rfl⟩ : syracuseStep 2138043 = 3207065) B3207065
theorem B14628725 : Blo 2137435 14628725 := bbase (se 5 (by rfl) ⟨685721, by rfl⟩ : syracuseStep 14628725 = 1371443) (by norm_num)
theorem B9752483 : Blo 2137435 9752483 := bstep (se 1 (by rfl) ⟨7314362, by rfl⟩ : syracuseStep 9752483 = 14628725) B14628725
theorem B6501655 : Blo 2137435 6501655 := bstep (se 1 (by rfl) ⟨4876241, by rfl⟩ : syracuseStep 6501655 = 9752483) B9752483
theorem B8668873 : Blo 2137435 8668873 := bstep (se 2 (by rfl) ⟨3250827, by rfl⟩ : syracuseStep 8668873 = 6501655) B6501655
theorem B11558497 : Blo 2137435 11558497 := bstep (se 2 (by rfl) ⟨4334436, by rfl⟩ : syracuseStep 11558497 = 8668873) B8668873
theorem B15411329 : Blo 2137435 15411329 := bstep (se 2 (by rfl) ⟨5779248, by rfl⟩ : syracuseStep 15411329 = 11558497) B11558497
theorem B10274219 : Blo 2137435 10274219 := bstep (se 1 (by rfl) ⟨7705664, by rfl⟩ : syracuseStep 10274219 = 15411329) B15411329
theorem B6849479 : Blo 2137435 6849479 := bstep (se 1 (by rfl) ⟨5137109, by rfl⟩ : syracuseStep 6849479 = 10274219) B10274219
theorem B18265277 : Blo 2137435 18265277 := bstep (se 3 (by rfl) ⟨3424739, by rfl⟩ : syracuseStep 18265277 = 6849479) B6849479
theorem B12176851 : Blo 2137435 12176851 := bstep (se 1 (by rfl) ⟨9132638, by rfl⟩ : syracuseStep 12176851 = 18265277) B18265277
theorem B16235801 : Blo 2137435 16235801 := bstep (se 2 (by rfl) ⟨6088425, by rfl⟩ : syracuseStep 16235801 = 12176851) B12176851
theorem B10823867 : Blo 2137435 10823867 := bstep (se 1 (by rfl) ⟨8117900, by rfl⟩ : syracuseStep 10823867 = 16235801) B16235801
theorem B7215911 : Blo 2137435 7215911 := bstep (se 1 (by rfl) ⟨5411933, by rfl⟩ : syracuseStep 7215911 = 10823867) B10823867
theorem B4810607 : Blo 2137435 4810607 := bstep (se 1 (by rfl) ⟨3607955, by rfl⟩ : syracuseStep 4810607 = 7215911) B7215911
theorem B3207071 : Blo 2137435 3207071 := bstep (se 1 (by rfl) ⟨2405303, by rfl⟩ : syracuseStep 3207071 = 4810607) B4810607
theorem B2138047 : Blo 2137435 2138047 := bstep (se 1 (by rfl) ⟨1603535, by rfl⟩ : syracuseStep 2138047 = 3207071) B3207071
theorem B3207077 : Blo 2137435 3207077 := bbase (se 4 (by rfl) ⟨300663, by rfl⟩ : syracuseStep 3207077 = 601327) (by norm_num)
theorem B2138051 : Blo 2137435 2138051 := bstep (se 1 (by rfl) ⟨1603538, by rfl⟩ : syracuseStep 2138051 = 3207077) B3207077
theorem B2705977 : Blo 2137435 2705977 := bbase (se 2 (by rfl) ⟨1014741, by rfl⟩ : syracuseStep 2705977 = 2029483) (by norm_num)
theorem B3607969 : Blo 2137435 3607969 := bstep (se 2 (by rfl) ⟨1352988, by rfl⟩ : syracuseStep 3607969 = 2705977) B2705977
theorem B4810625 : Blo 2137435 4810625 := bstep (se 2 (by rfl) ⟨1803984, by rfl⟩ : syracuseStep 4810625 = 3607969) B3607969
theorem B3207083 : Blo 2137435 3207083 := bstep (se 1 (by rfl) ⟨2405312, by rfl⟩ : syracuseStep 3207083 = 4810625) B4810625
theorem B2138055 : Blo 2137435 2138055 := bstep (se 1 (by rfl) ⟨1603541, by rfl⟩ : syracuseStep 2138055 = 3207083) B3207083
theorem B2405317 : Blo 2137435 2405317 := bbase (se 4 (by rfl) ⟨225498, by rfl⟩ : syracuseStep 2405317 = 450997) (by norm_num)
theorem B3207089 : Blo 2137435 3207089 := bstep (se 2 (by rfl) ⟨1202658, by rfl⟩ : syracuseStep 3207089 = 2405317) B2405317
theorem B2138059 : Blo 2137435 2138059 := bstep (se 1 (by rfl) ⟨1603544, by rfl⟩ : syracuseStep 2138059 = 3207089) B3207089
theorem B4058981 : Blo 2137435 4058981 := bbase (se 4 (by rfl) ⟨380529, by rfl⟩ : syracuseStep 4058981 = 761059) (by norm_num)
theorem B2705987 : Blo 2137435 2705987 := bstep (se 1 (by rfl) ⟨2029490, by rfl⟩ : syracuseStep 2705987 = 4058981) B4058981
theorem B7215965 : Blo 2137435 7215965 := bstep (se 3 (by rfl) ⟨1352993, by rfl⟩ : syracuseStep 7215965 = 2705987) B2705987
theorem B4810643 : Blo 2137435 4810643 := bstep (se 1 (by rfl) ⟨3607982, by rfl⟩ : syracuseStep 4810643 = 7215965) B7215965
theorem B3207095 : Blo 2137435 3207095 := bstep (se 1 (by rfl) ⟨2405321, by rfl⟩ : syracuseStep 3207095 = 4810643) B4810643
theorem B2138063 : Blo 2137435 2138063 := bstep (se 1 (by rfl) ⟨1603547, by rfl⟩ : syracuseStep 2138063 = 3207095) B3207095
theorem B3207101 : Blo 2137435 3207101 := bbase (se 3 (by rfl) ⟨601331, by rfl⟩ : syracuseStep 3207101 = 1202663) (by norm_num)
theorem B2138067 : Blo 2137435 2138067 := bstep (se 1 (by rfl) ⟨1603550, by rfl⟩ : syracuseStep 2138067 = 3207101) B3207101
theorem B4810661 : Blo 2137435 4810661 := bbase (se 4 (by rfl) ⟨450999, by rfl⟩ : syracuseStep 4810661 = 901999) (by norm_num)
theorem B3207107 : Blo 2137435 3207107 := bstep (se 1 (by rfl) ⟨2405330, by rfl⟩ : syracuseStep 3207107 = 4810661) B4810661
theorem B2138071 : Blo 2137435 2138071 := bstep (se 1 (by rfl) ⟨1603553, by rfl⟩ : syracuseStep 2138071 = 3207107) B3207107
theorem B5412005 : Blo 2137435 5412005 := bbase (se 4 (by rfl) ⟨507375, by rfl⟩ : syracuseStep 5412005 = 1014751) (by norm_num)
theorem B3608003 : Blo 2137435 3608003 := bstep (se 1 (by rfl) ⟨2706002, by rfl⟩ : syracuseStep 3608003 = 5412005) B5412005
theorem B2405335 : Blo 2137435 2405335 := bstep (se 1 (by rfl) ⟨1804001, by rfl⟩ : syracuseStep 2405335 = 3608003) B3608003
theorem B3207113 : Blo 2137435 3207113 := bstep (se 2 (by rfl) ⟨1202667, by rfl⟩ : syracuseStep 3207113 = 2405335) B2405335
theorem B2138075 : Blo 2137435 2138075 := bstep (se 1 (by rfl) ⟨1603556, by rfl⟩ : syracuseStep 2138075 = 3207113) B3207113
theorem B6088517 : Blo 2137435 6088517 := bbase (se 4 (by rfl) ⟨570798, by rfl⟩ : syracuseStep 6088517 = 1141597) (by norm_num)
theorem B4059011 : Blo 2137435 4059011 := bstep (se 1 (by rfl) ⟨3044258, by rfl⟩ : syracuseStep 4059011 = 6088517) B6088517
theorem B10824029 : Blo 2137435 10824029 := bstep (se 3 (by rfl) ⟨2029505, by rfl⟩ : syracuseStep 10824029 = 4059011) B4059011
theorem B7216019 : Blo 2137435 7216019 := bstep (se 1 (by rfl) ⟨5412014, by rfl⟩ : syracuseStep 7216019 = 10824029) B10824029
theorem B4810679 : Blo 2137435 4810679 := bstep (se 1 (by rfl) ⟨3608009, by rfl⟩ : syracuseStep 4810679 = 7216019) B7216019
theorem B3207119 : Blo 2137435 3207119 := bstep (se 1 (by rfl) ⟨2405339, by rfl⟩ : syracuseStep 3207119 = 4810679) B4810679
theorem B2138079 : Blo 2137435 2138079 := bstep (se 1 (by rfl) ⟨1603559, by rfl⟩ : syracuseStep 2138079 = 3207119) B3207119
theorem B3207125 : Blo 2137435 3207125 := bbase (se 7 (by rfl) ⟨37583, by rfl⟩ : syracuseStep 3207125 = 75167) (by norm_num)
theorem B2138083 : Blo 2137435 2138083 := bstep (se 1 (by rfl) ⟨1603562, by rfl⟩ : syracuseStep 2138083 = 3207125) B3207125
theorem B8118053 : Blo 2137435 8118053 := bbase (se 4 (by rfl) ⟨761067, by rfl⟩ : syracuseStep 8118053 = 1522135) (by norm_num)
theorem B5412035 : Blo 2137435 5412035 := bstep (se 1 (by rfl) ⟨4059026, by rfl⟩ : syracuseStep 5412035 = 8118053) B8118053
theorem B3608023 : Blo 2137435 3608023 := bstep (se 1 (by rfl) ⟨2706017, by rfl⟩ : syracuseStep 3608023 = 5412035) B5412035
theorem B4810697 : Blo 2137435 4810697 := bstep (se 2 (by rfl) ⟨1804011, by rfl⟩ : syracuseStep 4810697 = 3608023) B3608023
theorem B3207131 : Blo 2137435 3207131 := bstep (se 1 (by rfl) ⟨2405348, by rfl⟩ : syracuseStep 3207131 = 4810697) B4810697
theorem B2138087 : Blo 2137435 2138087 := bstep (se 1 (by rfl) ⟨1603565, by rfl⟩ : syracuseStep 2138087 = 3207131) B3207131
theorem B2405353 : Blo 2137435 2405353 := bbase (se 2 (by rfl) ⟨902007, by rfl⟩ : syracuseStep 2405353 = 1804015) (by norm_num)
theorem B3207137 : Blo 2137435 3207137 := bstep (se 2 (by rfl) ⟨1202676, by rfl⟩ : syracuseStep 3207137 = 2405353) B2405353
theorem B2138091 : Blo 2137435 2138091 := bstep (se 1 (by rfl) ⟨1603568, by rfl⟩ : syracuseStep 2138091 = 3207137) B3207137
theorem B2568613 : Blo 2137435 2568613 := bbase (se 4 (by rfl) ⟨240807, by rfl⟩ : syracuseStep 2568613 = 481615) (by norm_num)
theorem B3424817 : Blo 2137435 3424817 := bstep (se 2 (by rfl) ⟨1284306, by rfl⟩ : syracuseStep 3424817 = 2568613) B2568613
theorem B2283211 : Blo 2137435 2283211 := bstep (se 1 (by rfl) ⟨1712408, by rfl⟩ : syracuseStep 2283211 = 3424817) B3424817
theorem B12177125 : Blo 2137435 12177125 := bstep (se 4 (by rfl) ⟨1141605, by rfl⟩ : syracuseStep 12177125 = 2283211) B2283211
theorem B8118083 : Blo 2137435 8118083 := bstep (se 1 (by rfl) ⟨6088562, by rfl⟩ : syracuseStep 8118083 = 12177125) B12177125
theorem B5412055 : Blo 2137435 5412055 := bstep (se 1 (by rfl) ⟨4059041, by rfl⟩ : syracuseStep 5412055 = 8118083) B8118083
theorem B7216073 : Blo 2137435 7216073 := bstep (se 2 (by rfl) ⟨2706027, by rfl⟩ : syracuseStep 7216073 = 5412055) B5412055
theorem B4810715 : Blo 2137435 4810715 := bstep (se 1 (by rfl) ⟨3608036, by rfl⟩ : syracuseStep 4810715 = 7216073) B7216073
theorem B3207143 : Blo 2137435 3207143 := bstep (se 1 (by rfl) ⟨2405357, by rfl⟩ : syracuseStep 3207143 = 4810715) B4810715
theorem B2138095 : Blo 2137435 2138095 := bstep (se 1 (by rfl) ⟨1603571, by rfl⟩ : syracuseStep 2138095 = 3207143) B3207143
theorem B3207149 : Blo 2137435 3207149 := bbase (se 3 (by rfl) ⟨601340, by rfl⟩ : syracuseStep 3207149 = 1202681) (by norm_num)
theorem B2138099 : Blo 2137435 2138099 := bstep (se 1 (by rfl) ⟨1603574, by rfl⟩ : syracuseStep 2138099 = 3207149) B3207149
theorem B4810733 : Blo 2137435 4810733 := bbase (se 3 (by rfl) ⟨902012, by rfl⟩ : syracuseStep 4810733 = 1804025) (by norm_num)
theorem B3207155 : Blo 2137435 3207155 := bstep (se 1 (by rfl) ⟨2405366, by rfl⟩ : syracuseStep 3207155 = 4810733) B4810733
theorem B2138103 : Blo 2137435 2138103 := bstep (se 1 (by rfl) ⟨1603577, by rfl⟩ : syracuseStep 2138103 = 3207155) B3207155
theorem B3424837 : Blo 2137435 3424837 := bbase (se 4 (by rfl) ⟨321078, by rfl⟩ : syracuseStep 3424837 = 642157) (by norm_num)
theorem B4566449 : Blo 2137435 4566449 := bstep (se 2 (by rfl) ⟨1712418, by rfl⟩ : syracuseStep 4566449 = 3424837) B3424837
theorem B3044299 : Blo 2137435 3044299 := bstep (se 1 (by rfl) ⟨2283224, by rfl⟩ : syracuseStep 3044299 = 4566449) B4566449
theorem B4059065 : Blo 2137435 4059065 := bstep (se 2 (by rfl) ⟨1522149, by rfl⟩ : syracuseStep 4059065 = 3044299) B3044299
theorem B2706043 : Blo 2137435 2706043 := bstep (se 1 (by rfl) ⟨2029532, by rfl⟩ : syracuseStep 2706043 = 4059065) B4059065
theorem B3608057 : Blo 2137435 3608057 := bstep (se 2 (by rfl) ⟨1353021, by rfl⟩ : syracuseStep 3608057 = 2706043) B2706043
theorem B2405371 : Blo 2137435 2405371 := bstep (se 1 (by rfl) ⟨1804028, by rfl⟩ : syracuseStep 2405371 = 3608057) B3608057
theorem B3207161 : Blo 2137435 3207161 := bstep (se 2 (by rfl) ⟨1202685, by rfl⟩ : syracuseStep 3207161 = 2405371) B2405371
theorem B2138107 : Blo 2137435 2138107 := bstep (se 1 (by rfl) ⟨1603580, by rfl⟩ : syracuseStep 2138107 = 3207161) B3207161
theorem B2603677 : Blo 2137435 2603677 := bbase (se 3 (by rfl) ⟨488189, by rfl⟩ : syracuseStep 2603677 = 976379) (by norm_num)
theorem B3471569 : Blo 2137435 3471569 := bstep (se 2 (by rfl) ⟨1301838, by rfl⟩ : syracuseStep 3471569 = 2603677) B2603677
theorem B2314379 : Blo 2137435 2314379 := bstep (se 1 (by rfl) ⟨1735784, by rfl⟩ : syracuseStep 2314379 = 3471569) B3471569
theorem B6171677 : Blo 2137435 6171677 := bstep (se 3 (by rfl) ⟨1157189, by rfl⟩ : syracuseStep 6171677 = 2314379) B2314379
theorem B4114451 : Blo 2137435 4114451 := bstep (se 1 (by rfl) ⟨3085838, by rfl⟩ : syracuseStep 4114451 = 6171677) B6171677
theorem B702199637 : Blo 2137435 702199637 := bstep (se 9 (by rfl) ⟨2057225, by rfl⟩ : syracuseStep 702199637 = 4114451) B4114451
theorem B468133091 : Blo 2137435 468133091 := bstep (se 1 (by rfl) ⟨351099818, by rfl⟩ : syracuseStep 468133091 = 702199637) B702199637
theorem B312088727 : Blo 2137435 312088727 := bstep (se 1 (by rfl) ⟨234066545, by rfl⟩ : syracuseStep 312088727 = 468133091) B468133091
theorem B208059151 : Blo 2137435 208059151 := bstep (se 1 (by rfl) ⟨156044363, by rfl⟩ : syracuseStep 208059151 = 312088727) B312088727
theorem B277412201 : Blo 2137435 277412201 := bstep (se 2 (by rfl) ⟨104029575, by rfl⟩ : syracuseStep 277412201 = 208059151) B208059151
theorem B184941467 : Blo 2137435 184941467 := bstep (se 1 (by rfl) ⟨138706100, by rfl⟩ : syracuseStep 184941467 = 277412201) B277412201
theorem B123294311 : Blo 2137435 123294311 := bstep (se 1 (by rfl) ⟨92470733, by rfl⟩ : syracuseStep 123294311 = 184941467) B184941467
theorem B82196207 : Blo 2137435 82196207 := bstep (se 1 (by rfl) ⟨61647155, by rfl⟩ : syracuseStep 82196207 = 123294311) B123294311
theorem B54797471 : Blo 2137435 54797471 := bstep (se 1 (by rfl) ⟨41098103, by rfl⟩ : syracuseStep 54797471 = 82196207) B82196207
theorem B36531647 : Blo 2137435 36531647 := bstep (se 1 (by rfl) ⟨27398735, by rfl⟩ : syracuseStep 36531647 = 54797471) B54797471
theorem B24354431 : Blo 2137435 24354431 := bstep (se 1 (by rfl) ⟨18265823, by rfl⟩ : syracuseStep 24354431 = 36531647) B36531647
theorem B16236287 : Blo 2137435 16236287 := bstep (se 1 (by rfl) ⟨12177215, by rfl⟩ : syracuseStep 16236287 = 24354431) B24354431
theorem B10824191 : Blo 2137435 10824191 := bstep (se 1 (by rfl) ⟨8118143, by rfl⟩ : syracuseStep 10824191 = 16236287) B16236287
theorem B7216127 : Blo 2137435 7216127 := bstep (se 1 (by rfl) ⟨5412095, by rfl⟩ : syracuseStep 7216127 = 10824191) B10824191
theorem B4810751 : Blo 2137435 4810751 := bstep (se 1 (by rfl) ⟨3608063, by rfl⟩ : syracuseStep 4810751 = 7216127) B7216127
theorem B3207167 : Blo 2137435 3207167 := bstep (se 1 (by rfl) ⟨2405375, by rfl⟩ : syracuseStep 3207167 = 4810751) B4810751
theorem B2138111 : Blo 2137435 2138111 := bstep (se 1 (by rfl) ⟨1603583, by rfl⟩ : syracuseStep 2138111 = 3207167) B3207167
theorem B3207173 : Blo 2137435 3207173 := bbase (se 4 (by rfl) ⟨300672, by rfl⟩ : syracuseStep 3207173 = 601345) (by norm_num)
theorem B2138115 : Blo 2137435 2138115 := bstep (se 1 (by rfl) ⟨1603586, by rfl⟩ : syracuseStep 2138115 = 3207173) B3207173
theorem B3608077 : Blo 2137435 3608077 := bbase (se 3 (by rfl) ⟨676514, by rfl⟩ : syracuseStep 3608077 = 1353029) (by norm_num)
theorem B4810769 : Blo 2137435 4810769 := bstep (se 2 (by rfl) ⟨1804038, by rfl⟩ : syracuseStep 4810769 = 3608077) B3608077
theorem B3207179 : Blo 2137435 3207179 := bstep (se 1 (by rfl) ⟨2405384, by rfl⟩ : syracuseStep 3207179 = 4810769) B4810769
theorem B2138119 : Blo 2137435 2138119 := bstep (se 1 (by rfl) ⟨1603589, by rfl⟩ : syracuseStep 2138119 = 3207179) B3207179
theorem B2405389 : Blo 2137435 2405389 := bbase (se 3 (by rfl) ⟨451010, by rfl⟩ : syracuseStep 2405389 = 902021) (by norm_num)
theorem B3207185 : Blo 2137435 3207185 := bstep (se 2 (by rfl) ⟨1202694, by rfl⟩ : syracuseStep 3207185 = 2405389) B2405389
theorem B2138123 : Blo 2137435 2138123 := bstep (se 1 (by rfl) ⟨1603592, by rfl⟩ : syracuseStep 2138123 = 3207185) B3207185
theorem B7216181 : Blo 2137435 7216181 := bbase (se 5 (by rfl) ⟨338258, by rfl⟩ : syracuseStep 7216181 = 676517) (by norm_num)
theorem B4810787 : Blo 2137435 4810787 := bstep (se 1 (by rfl) ⟨3608090, by rfl⟩ : syracuseStep 4810787 = 7216181) B7216181
theorem B3207191 : Blo 2137435 3207191 := bstep (se 1 (by rfl) ⟨2405393, by rfl⟩ : syracuseStep 3207191 = 4810787) B4810787
theorem B2138127 : Blo 2137435 2138127 := bstep (se 1 (by rfl) ⟨1603595, by rfl⟩ : syracuseStep 2138127 = 3207191) B3207191
theorem B3207197 : Blo 2137435 3207197 := bbase (se 3 (by rfl) ⟨601349, by rfl⟩ : syracuseStep 3207197 = 1202699) (by norm_num)
theorem B2138131 : Blo 2137435 2138131 := bstep (se 1 (by rfl) ⟨1603598, by rfl⟩ : syracuseStep 2138131 = 3207197) B3207197
theorem B4810805 : Blo 2137435 4810805 := bbase (se 5 (by rfl) ⟨225506, by rfl⟩ : syracuseStep 4810805 = 451013) (by norm_num)
theorem B3207203 : Blo 2137435 3207203 := bstep (se 1 (by rfl) ⟨2405402, by rfl⟩ : syracuseStep 3207203 = 4810805) B4810805
theorem B2138135 : Blo 2137435 2138135 := bstep (se 1 (by rfl) ⟨1603601, by rfl⟩ : syracuseStep 2138135 = 3207203) B3207203
theorem B8341285 : Blo 2137435 8341285 := bbase (se 4 (by rfl) ⟨781995, by rfl⟩ : syracuseStep 8341285 = 1563991) (by norm_num)
theorem B11121713 : Blo 2137435 11121713 := bstep (se 2 (by rfl) ⟨4170642, by rfl⟩ : syracuseStep 11121713 = 8341285) B8341285
theorem B7414475 : Blo 2137435 7414475 := bstep (se 1 (by rfl) ⟨5560856, by rfl⟩ : syracuseStep 7414475 = 11121713) B11121713
theorem B19771933 : Blo 2137435 19771933 := bstep (se 3 (by rfl) ⟨3707237, by rfl⟩ : syracuseStep 19771933 = 7414475) B7414475
theorem B26362577 : Blo 2137435 26362577 := bstep (se 2 (by rfl) ⟨9885966, by rfl⟩ : syracuseStep 26362577 = 19771933) B19771933
theorem B17575051 : Blo 2137435 17575051 := bstep (se 1 (by rfl) ⟨13181288, by rfl⟩ : syracuseStep 17575051 = 26362577) B26362577
theorem B23433401 : Blo 2137435 23433401 := bstep (se 2 (by rfl) ⟨8787525, by rfl⟩ : syracuseStep 23433401 = 17575051) B17575051
theorem B15622267 : Blo 2137435 15622267 := bstep (se 1 (by rfl) ⟨11716700, by rfl⟩ : syracuseStep 15622267 = 23433401) B23433401
theorem B20829689 : Blo 2137435 20829689 := bstep (se 2 (by rfl) ⟨7811133, by rfl⟩ : syracuseStep 20829689 = 15622267) B15622267
theorem B13886459 : Blo 2137435 13886459 := bstep (se 1 (by rfl) ⟨10414844, by rfl⟩ : syracuseStep 13886459 = 20829689) B20829689
theorem B148122229 : Blo 2137435 148122229 := bstep (se 5 (by rfl) ⟨6943229, by rfl⟩ : syracuseStep 148122229 = 13886459) B13886459
theorem B197496305 : Blo 2137435 197496305 := bstep (se 2 (by rfl) ⟨74061114, by rfl⟩ : syracuseStep 197496305 = 148122229) B148122229
theorem B131664203 : Blo 2137435 131664203 := bstep (se 1 (by rfl) ⟨98748152, by rfl⟩ : syracuseStep 131664203 = 197496305) B197496305
theorem B87776135 : Blo 2137435 87776135 := bstep (se 1 (by rfl) ⟨65832101, by rfl⟩ : syracuseStep 87776135 = 131664203) B131664203
theorem B58517423 : Blo 2137435 58517423 := bstep (se 1 (by rfl) ⟨43888067, by rfl⟩ : syracuseStep 58517423 = 87776135) B87776135
theorem B39011615 : Blo 2137435 39011615 := bstep (se 1 (by rfl) ⟨29258711, by rfl⟩ : syracuseStep 39011615 = 58517423) B58517423
theorem B26007743 : Blo 2137435 26007743 := bstep (se 1 (by rfl) ⟨19505807, by rfl⟩ : syracuseStep 26007743 = 39011615) B39011615
theorem B17338495 : Blo 2137435 17338495 := bstep (se 1 (by rfl) ⟨13003871, by rfl⟩ : syracuseStep 17338495 = 26007743) B26007743
theorem B23117993 : Blo 2137435 23117993 := bstep (se 2 (by rfl) ⟨8669247, by rfl⟩ : syracuseStep 23117993 = 17338495) B17338495
theorem B15411995 : Blo 2137435 15411995 := bstep (se 1 (by rfl) ⟨11558996, by rfl⟩ : syracuseStep 15411995 = 23117993) B23117993
theorem B10274663 : Blo 2137435 10274663 := bstep (se 1 (by rfl) ⟨7705997, by rfl⟩ : syracuseStep 10274663 = 15411995) B15411995
theorem B6849775 : Blo 2137435 6849775 := bstep (se 1 (by rfl) ⟨5137331, by rfl⟩ : syracuseStep 6849775 = 10274663) B10274663
theorem B9133033 : Blo 2137435 9133033 := bstep (se 2 (by rfl) ⟨3424887, by rfl⟩ : syracuseStep 9133033 = 6849775) B6849775
theorem B12177377 : Blo 2137435 12177377 := bstep (se 2 (by rfl) ⟨4566516, by rfl⟩ : syracuseStep 12177377 = 9133033) B9133033
theorem B8118251 : Blo 2137435 8118251 := bstep (se 1 (by rfl) ⟨6088688, by rfl⟩ : syracuseStep 8118251 = 12177377) B12177377
theorem B5412167 : Blo 2137435 5412167 := bstep (se 1 (by rfl) ⟨4059125, by rfl⟩ : syracuseStep 5412167 = 8118251) B8118251
theorem B3608111 : Blo 2137435 3608111 := bstep (se 1 (by rfl) ⟨2706083, by rfl⟩ : syracuseStep 3608111 = 5412167) B5412167
theorem B2405407 : Blo 2137435 2405407 := bstep (se 1 (by rfl) ⟨1804055, by rfl⟩ : syracuseStep 2405407 = 3608111) B3608111
theorem B3207209 : Blo 2137435 3207209 := bstep (se 2 (by rfl) ⟨1202703, by rfl⟩ : syracuseStep 3207209 = 2405407) B2405407
theorem B2138139 : Blo 2137435 2138139 := bstep (se 1 (by rfl) ⟨1603604, by rfl⟩ : syracuseStep 2138139 = 3207209) B3207209
theorem B10972037 : Blo 2137435 10972037 := bbase (se 4 (by rfl) ⟨1028628, by rfl⟩ : syracuseStep 10972037 = 2057257) (by norm_num)
theorem B29258765 : Blo 2137435 29258765 := bstep (se 3 (by rfl) ⟨5486018, by rfl⟩ : syracuseStep 29258765 = 10972037) B10972037
theorem B19505843 : Blo 2137435 19505843 := bstep (se 1 (by rfl) ⟨14629382, by rfl⟩ : syracuseStep 19505843 = 29258765) B29258765
theorem B13003895 : Blo 2137435 13003895 := bstep (se 1 (by rfl) ⟨9752921, by rfl⟩ : syracuseStep 13003895 = 19505843) B19505843
theorem B8669263 : Blo 2137435 8669263 := bstep (se 1 (by rfl) ⟨6501947, by rfl⟩ : syracuseStep 8669263 = 13003895) B13003895
theorem B11559017 : Blo 2137435 11559017 := bstep (se 2 (by rfl) ⟨4334631, by rfl⟩ : syracuseStep 11559017 = 8669263) B8669263
theorem B7706011 : Blo 2137435 7706011 := bstep (se 1 (by rfl) ⟨5779508, by rfl⟩ : syracuseStep 7706011 = 11559017) B11559017
theorem B10274681 : Blo 2137435 10274681 := bstep (se 2 (by rfl) ⟨3853005, by rfl⟩ : syracuseStep 10274681 = 7706011) B7706011
theorem B6849787 : Blo 2137435 6849787 := bstep (se 1 (by rfl) ⟨5137340, by rfl⟩ : syracuseStep 6849787 = 10274681) B10274681
theorem B9133049 : Blo 2137435 9133049 := bstep (se 2 (by rfl) ⟨3424893, by rfl⟩ : syracuseStep 9133049 = 6849787) B6849787
theorem B6088699 : Blo 2137435 6088699 := bstep (se 1 (by rfl) ⟨4566524, by rfl⟩ : syracuseStep 6088699 = 9133049) B9133049
theorem B8118265 : Blo 2137435 8118265 := bstep (se 2 (by rfl) ⟨3044349, by rfl⟩ : syracuseStep 8118265 = 6088699) B6088699
theorem B10824353 : Blo 2137435 10824353 := bstep (se 2 (by rfl) ⟨4059132, by rfl⟩ : syracuseStep 10824353 = 8118265) B8118265
theorem B7216235 : Blo 2137435 7216235 := bstep (se 1 (by rfl) ⟨5412176, by rfl⟩ : syracuseStep 7216235 = 10824353) B10824353
theorem B4810823 : Blo 2137435 4810823 := bstep (se 1 (by rfl) ⟨3608117, by rfl⟩ : syracuseStep 4810823 = 7216235) B7216235
theorem B3207215 : Blo 2137435 3207215 := bstep (se 1 (by rfl) ⟨2405411, by rfl⟩ : syracuseStep 3207215 = 4810823) B4810823
theorem B2138143 : Blo 2137435 2138143 := bstep (se 1 (by rfl) ⟨1603607, by rfl⟩ : syracuseStep 2138143 = 3207215) B3207215
theorem B3207221 : Blo 2137435 3207221 := bbase (se 5 (by rfl) ⟨150338, by rfl⟩ : syracuseStep 3207221 = 300677) (by norm_num)
theorem B2138147 : Blo 2137435 2138147 := bstep (se 1 (by rfl) ⟨1603610, by rfl⟩ : syracuseStep 2138147 = 3207221) B3207221
theorem B5412197 : Blo 2137435 5412197 := bbase (se 4 (by rfl) ⟨507393, by rfl⟩ : syracuseStep 5412197 = 1014787) (by norm_num)
theorem B3608131 : Blo 2137435 3608131 := bstep (se 1 (by rfl) ⟨2706098, by rfl⟩ : syracuseStep 3608131 = 5412197) B5412197
theorem B4810841 : Blo 2137435 4810841 := bstep (se 2 (by rfl) ⟨1804065, by rfl⟩ : syracuseStep 4810841 = 3608131) B3608131
theorem B3207227 : Blo 2137435 3207227 := bstep (se 1 (by rfl) ⟨2405420, by rfl⟩ : syracuseStep 3207227 = 4810841) B4810841
theorem B2138151 : Blo 2137435 2138151 := bstep (se 1 (by rfl) ⟨1603613, by rfl⟩ : syracuseStep 2138151 = 3207227) B3207227
theorem B2405425 : Blo 2137435 2405425 := bbase (se 2 (by rfl) ⟨902034, by rfl⟩ : syracuseStep 2405425 = 1804069) (by norm_num)
theorem B3207233 : Blo 2137435 3207233 := bstep (se 2 (by rfl) ⟨1202712, by rfl⟩ : syracuseStep 3207233 = 2405425) B2405425
theorem B2138155 : Blo 2137435 2138155 := bstep (se 1 (by rfl) ⟨1603616, by rfl⟩ : syracuseStep 2138155 = 3207233) B3207233
theorem B14629493 : Blo 2137435 14629493 := bbase (se 5 (by rfl) ⟨685757, by rfl⟩ : syracuseStep 14629493 = 1371515) (by norm_num)
theorem B9752995 : Blo 2137435 9752995 := bstep (se 1 (by rfl) ⟨7314746, by rfl⟩ : syracuseStep 9752995 = 14629493) B14629493
theorem B13003993 : Blo 2137435 13003993 := bstep (se 2 (by rfl) ⟨4876497, by rfl⟩ : syracuseStep 13003993 = 9752995) B9752995
theorem B17338657 : Blo 2137435 17338657 := bstep (se 2 (by rfl) ⟨6501996, by rfl⟩ : syracuseStep 17338657 = 13003993) B13003993
theorem B23118209 : Blo 2137435 23118209 := bstep (se 2 (by rfl) ⟨8669328, by rfl⟩ : syracuseStep 23118209 = 17338657) B17338657
theorem B15412139 : Blo 2137435 15412139 := bstep (se 1 (by rfl) ⟨11559104, by rfl⟩ : syracuseStep 15412139 = 23118209) B23118209
theorem B10274759 : Blo 2137435 10274759 := bstep (se 1 (by rfl) ⟨7706069, by rfl⟩ : syracuseStep 10274759 = 15412139) B15412139
theorem B6849839 : Blo 2137435 6849839 := bstep (se 1 (by rfl) ⟨5137379, by rfl⟩ : syracuseStep 6849839 = 10274759) B10274759
theorem B4566559 : Blo 2137435 4566559 := bstep (se 1 (by rfl) ⟨3424919, by rfl⟩ : syracuseStep 4566559 = 6849839) B6849839
theorem B6088745 : Blo 2137435 6088745 := bstep (se 2 (by rfl) ⟨2283279, by rfl⟩ : syracuseStep 6088745 = 4566559) B4566559
theorem B4059163 : Blo 2137435 4059163 := bstep (se 1 (by rfl) ⟨3044372, by rfl⟩ : syracuseStep 4059163 = 6088745) B6088745
theorem B5412217 : Blo 2137435 5412217 := bstep (se 2 (by rfl) ⟨2029581, by rfl⟩ : syracuseStep 5412217 = 4059163) B4059163
theorem B7216289 : Blo 2137435 7216289 := bstep (se 2 (by rfl) ⟨2706108, by rfl⟩ : syracuseStep 7216289 = 5412217) B5412217
theorem B4810859 : Blo 2137435 4810859 := bstep (se 1 (by rfl) ⟨3608144, by rfl⟩ : syracuseStep 4810859 = 7216289) B7216289
theorem B3207239 : Blo 2137435 3207239 := bstep (se 1 (by rfl) ⟨2405429, by rfl⟩ : syracuseStep 3207239 = 4810859) B4810859
theorem B2138159 : Blo 2137435 2138159 := bstep (se 1 (by rfl) ⟨1603619, by rfl⟩ : syracuseStep 2138159 = 3207239) B3207239
theorem B3207245 : Blo 2137435 3207245 := bbase (se 3 (by rfl) ⟨601358, by rfl⟩ : syracuseStep 3207245 = 1202717) (by norm_num)
theorem B2138163 : Blo 2137435 2138163 := bstep (se 1 (by rfl) ⟨1603622, by rfl⟩ : syracuseStep 2138163 = 3207245) B3207245
theorem B4810877 : Blo 2137435 4810877 := bbase (se 3 (by rfl) ⟨902039, by rfl⟩ : syracuseStep 4810877 = 1804079) (by norm_num)
theorem B3207251 : Blo 2137435 3207251 := bstep (se 1 (by rfl) ⟨2405438, by rfl⟩ : syracuseStep 3207251 = 4810877) B4810877
theorem B2138167 : Blo 2137435 2138167 := bstep (se 1 (by rfl) ⟨1603625, by rfl⟩ : syracuseStep 2138167 = 3207251) B3207251
theorem B3608165 : Blo 2137435 3608165 := bbase (se 4 (by rfl) ⟨338265, by rfl⟩ : syracuseStep 3608165 = 676531) (by norm_num)
theorem B2405443 : Blo 2137435 2405443 := bstep (se 1 (by rfl) ⟨1804082, by rfl⟩ : syracuseStep 2405443 = 3608165) B3608165
theorem B3207257 : Blo 2137435 3207257 := bstep (se 2 (by rfl) ⟨1202721, by rfl⟩ : syracuseStep 3207257 = 2405443) B2405443
theorem B2138171 : Blo 2137435 2138171 := bstep (se 1 (by rfl) ⟨1603628, by rfl⟩ : syracuseStep 2138171 = 3207257) B3207257
theorem B2568709 : Blo 2137435 2568709 := bbase (se 4 (by rfl) ⟨240816, by rfl⟩ : syracuseStep 2568709 = 481633) (by norm_num)
theorem B3424945 : Blo 2137435 3424945 := bstep (se 2 (by rfl) ⟨1284354, by rfl⟩ : syracuseStep 3424945 = 2568709) B2568709
theorem B4566593 : Blo 2137435 4566593 := bstep (se 2 (by rfl) ⟨1712472, by rfl⟩ : syracuseStep 4566593 = 3424945) B3424945
theorem B3044395 : Blo 2137435 3044395 := bstep (se 1 (by rfl) ⟨2283296, by rfl⟩ : syracuseStep 3044395 = 4566593) B4566593
theorem B16236773 : Blo 2137435 16236773 := bstep (se 4 (by rfl) ⟨1522197, by rfl⟩ : syracuseStep 16236773 = 3044395) B3044395
theorem B10824515 : Blo 2137435 10824515 := bstep (se 1 (by rfl) ⟨8118386, by rfl⟩ : syracuseStep 10824515 = 16236773) B16236773
theorem B7216343 : Blo 2137435 7216343 := bstep (se 1 (by rfl) ⟨5412257, by rfl⟩ : syracuseStep 7216343 = 10824515) B10824515
theorem B4810895 : Blo 2137435 4810895 := bstep (se 1 (by rfl) ⟨3608171, by rfl⟩ : syracuseStep 4810895 = 7216343) B7216343
theorem B3207263 : Blo 2137435 3207263 := bstep (se 1 (by rfl) ⟨2405447, by rfl⟩ : syracuseStep 3207263 = 4810895) B4810895
theorem B2138175 : Blo 2137435 2138175 := bstep (se 1 (by rfl) ⟨1603631, by rfl⟩ : syracuseStep 2138175 = 3207263) B3207263
theorem B3207269 : Blo 2137435 3207269 := bbase (se 4 (by rfl) ⟨300681, by rfl⟩ : syracuseStep 3207269 = 601363) (by norm_num)
theorem B2138179 : Blo 2137435 2138179 := bstep (se 1 (by rfl) ⟨1603634, by rfl⟩ : syracuseStep 2138179 = 3207269) B3207269
theorem B8669429 : Blo 2137435 8669429 := bbase (se 5 (by rfl) ⟨406379, by rfl⟩ : syracuseStep 8669429 = 812759) (by norm_num)
theorem B5779619 : Blo 2137435 5779619 := bstep (se 1 (by rfl) ⟨4334714, by rfl⟩ : syracuseStep 5779619 = 8669429) B8669429
theorem B3853079 : Blo 2137435 3853079 := bstep (se 1 (by rfl) ⟨2889809, by rfl⟩ : syracuseStep 3853079 = 5779619) B5779619
theorem B2568719 : Blo 2137435 2568719 := bstep (se 1 (by rfl) ⟨1926539, by rfl⟩ : syracuseStep 2568719 = 3853079) B3853079
theorem B6849917 : Blo 2137435 6849917 := bstep (se 3 (by rfl) ⟨1284359, by rfl⟩ : syracuseStep 6849917 = 2568719) B2568719
theorem B4566611 : Blo 2137435 4566611 := bstep (se 1 (by rfl) ⟨3424958, by rfl⟩ : syracuseStep 4566611 = 6849917) B6849917
theorem B3044407 : Blo 2137435 3044407 := bstep (se 1 (by rfl) ⟨2283305, by rfl⟩ : syracuseStep 3044407 = 4566611) B4566611
theorem B4059209 : Blo 2137435 4059209 := bstep (se 2 (by rfl) ⟨1522203, by rfl⟩ : syracuseStep 4059209 = 3044407) B3044407
theorem B2706139 : Blo 2137435 2706139 := bstep (se 1 (by rfl) ⟨2029604, by rfl⟩ : syracuseStep 2706139 = 4059209) B4059209
theorem B3608185 : Blo 2137435 3608185 := bstep (se 2 (by rfl) ⟨1353069, by rfl⟩ : syracuseStep 3608185 = 2706139) B2706139
theorem B4810913 : Blo 2137435 4810913 := bstep (se 2 (by rfl) ⟨1804092, by rfl⟩ : syracuseStep 4810913 = 3608185) B3608185
theorem B3207275 : Blo 2137435 3207275 := bstep (se 1 (by rfl) ⟨2405456, by rfl⟩ : syracuseStep 3207275 = 4810913) B4810913
theorem B2138183 : Blo 2137435 2138183 := bstep (se 1 (by rfl) ⟨1603637, by rfl⟩ : syracuseStep 2138183 = 3207275) B3207275
theorem B2405461 : Blo 2137435 2405461 := bbase (se 8 (by rfl) ⟨14094, by rfl⟩ : syracuseStep 2405461 = 28189) (by norm_num)
theorem B3207281 : Blo 2137435 3207281 := bstep (se 2 (by rfl) ⟨1202730, by rfl⟩ : syracuseStep 3207281 = 2405461) B2405461
theorem B2138187 : Blo 2137435 2138187 := bstep (se 1 (by rfl) ⟨1603640, by rfl⟩ : syracuseStep 2138187 = 3207281) B3207281
theorem B2706149 : Blo 2137435 2706149 := bbase (se 4 (by rfl) ⟨253701, by rfl⟩ : syracuseStep 2706149 = 507403) (by norm_num)
theorem B7216397 : Blo 2137435 7216397 := bstep (se 3 (by rfl) ⟨1353074, by rfl⟩ : syracuseStep 7216397 = 2706149) B2706149
theorem B4810931 : Blo 2137435 4810931 := bstep (se 1 (by rfl) ⟨3608198, by rfl⟩ : syracuseStep 4810931 = 7216397) B7216397
theorem B3207287 : Blo 2137435 3207287 := bstep (se 1 (by rfl) ⟨2405465, by rfl⟩ : syracuseStep 3207287 = 4810931) B4810931
theorem B2138191 : Blo 2137435 2138191 := bstep (se 1 (by rfl) ⟨1603643, by rfl⟩ : syracuseStep 2138191 = 3207287) B3207287
theorem B3207293 : Blo 2137435 3207293 := bbase (se 3 (by rfl) ⟨601367, by rfl⟩ : syracuseStep 3207293 = 1202735) (by norm_num)
theorem B2138195 : Blo 2137435 2138195 := bstep (se 1 (by rfl) ⟨1603646, by rfl⟩ : syracuseStep 2138195 = 3207293) B3207293
theorem B4810949 : Blo 2137435 4810949 := bbase (se 4 (by rfl) ⟨451026, by rfl⟩ : syracuseStep 4810949 = 902053) (by norm_num)
theorem B3207299 : Blo 2137435 3207299 := bstep (se 1 (by rfl) ⟨2405474, by rfl⟩ : syracuseStep 3207299 = 4810949) B4810949
theorem B2138199 : Blo 2137435 2138199 := bstep (se 1 (by rfl) ⟨1603649, by rfl⟩ : syracuseStep 2138199 = 3207299) B3207299
theorem B5486173 : Blo 2137435 5486173 := bbase (se 3 (by rfl) ⟨1028657, by rfl⟩ : syracuseStep 5486173 = 2057315) (by norm_num)
theorem B29259589 : Blo 2137435 29259589 := bstep (se 4 (by rfl) ⟨2743086, by rfl⟩ : syracuseStep 29259589 = 5486173) B5486173
theorem B39012785 : Blo 2137435 39012785 := bstep (se 2 (by rfl) ⟨14629794, by rfl⟩ : syracuseStep 39012785 = 29259589) B29259589
theorem B26008523 : Blo 2137435 26008523 := bstep (se 1 (by rfl) ⟨19506392, by rfl⟩ : syracuseStep 26008523 = 39012785) B39012785
theorem B17339015 : Blo 2137435 17339015 := bstep (se 1 (by rfl) ⟨13004261, by rfl⟩ : syracuseStep 17339015 = 26008523) B26008523
theorem B11559343 : Blo 2137435 11559343 := bstep (se 1 (by rfl) ⟨8669507, by rfl⟩ : syracuseStep 11559343 = 17339015) B17339015
theorem B15412457 : Blo 2137435 15412457 := bstep (se 2 (by rfl) ⟨5779671, by rfl⟩ : syracuseStep 15412457 = 11559343) B11559343
theorem B10274971 : Blo 2137435 10274971 := bstep (se 1 (by rfl) ⟨7706228, by rfl⟩ : syracuseStep 10274971 = 15412457) B15412457
theorem B13699961 : Blo 2137435 13699961 := bstep (se 2 (by rfl) ⟨5137485, by rfl⟩ : syracuseStep 13699961 = 10274971) B10274971
theorem B9133307 : Blo 2137435 9133307 := bstep (se 1 (by rfl) ⟨6849980, by rfl⟩ : syracuseStep 9133307 = 13699961) B13699961
theorem B6088871 : Blo 2137435 6088871 := bstep (se 1 (by rfl) ⟨4566653, by rfl⟩ : syracuseStep 6088871 = 9133307) B9133307
theorem B4059247 : Blo 2137435 4059247 := bstep (se 1 (by rfl) ⟨3044435, by rfl⟩ : syracuseStep 4059247 = 6088871) B6088871
theorem B5412329 : Blo 2137435 5412329 := bstep (se 2 (by rfl) ⟨2029623, by rfl⟩ : syracuseStep 5412329 = 4059247) B4059247
theorem B3608219 : Blo 2137435 3608219 := bstep (se 1 (by rfl) ⟨2706164, by rfl⟩ : syracuseStep 3608219 = 5412329) B5412329
theorem B2405479 : Blo 2137435 2405479 := bstep (se 1 (by rfl) ⟨1804109, by rfl⟩ : syracuseStep 2405479 = 3608219) B3608219
theorem B3207305 : Blo 2137435 3207305 := bstep (se 2 (by rfl) ⟨1202739, by rfl⟩ : syracuseStep 3207305 = 2405479) B2405479
theorem B2138203 : Blo 2137435 2138203 := bstep (se 1 (by rfl) ⟨1603652, by rfl⟩ : syracuseStep 2138203 = 3207305) B3207305
theorem B10824677 : Blo 2137435 10824677 := bbase (se 4 (by rfl) ⟨1014813, by rfl⟩ : syracuseStep 10824677 = 2029627) (by norm_num)
theorem B7216451 : Blo 2137435 7216451 := bstep (se 1 (by rfl) ⟨5412338, by rfl⟩ : syracuseStep 7216451 = 10824677) B10824677
theorem B4810967 : Blo 2137435 4810967 := bstep (se 1 (by rfl) ⟨3608225, by rfl⟩ : syracuseStep 4810967 = 7216451) B7216451
theorem B3207311 : Blo 2137435 3207311 := bstep (se 1 (by rfl) ⟨2405483, by rfl⟩ : syracuseStep 3207311 = 4810967) B4810967
theorem B2138207 : Blo 2137435 2138207 := bstep (se 1 (by rfl) ⟨1603655, by rfl⟩ : syracuseStep 2138207 = 3207311) B3207311
theorem B3207317 : Blo 2137435 3207317 := bbase (se 6 (by rfl) ⟨75171, by rfl⟩ : syracuseStep 3207317 = 150343) (by norm_num)
theorem B2138211 : Blo 2137435 2138211 := bstep (se 1 (by rfl) ⟨1603658, by rfl⟩ : syracuseStep 2138211 = 3207317) B3207317
theorem B2568757 : Blo 2137435 2568757 := bbase (se 5 (by rfl) ⟨120410, by rfl⟩ : syracuseStep 2568757 = 240821) (by norm_num)
theorem B3425009 : Blo 2137435 3425009 := bstep (se 2 (by rfl) ⟨1284378, by rfl⟩ : syracuseStep 3425009 = 2568757) B2568757
theorem B9133357 : Blo 2137435 9133357 := bstep (se 3 (by rfl) ⟨1712504, by rfl⟩ : syracuseStep 9133357 = 3425009) B3425009
theorem B12177809 : Blo 2137435 12177809 := bstep (se 2 (by rfl) ⟨4566678, by rfl⟩ : syracuseStep 12177809 = 9133357) B9133357
theorem B8118539 : Blo 2137435 8118539 := bstep (se 1 (by rfl) ⟨6088904, by rfl⟩ : syracuseStep 8118539 = 12177809) B12177809
theorem B5412359 : Blo 2137435 5412359 := bstep (se 1 (by rfl) ⟨4059269, by rfl⟩ : syracuseStep 5412359 = 8118539) B8118539
theorem B3608239 : Blo 2137435 3608239 := bstep (se 1 (by rfl) ⟨2706179, by rfl⟩ : syracuseStep 3608239 = 5412359) B5412359
theorem B4810985 : Blo 2137435 4810985 := bstep (se 2 (by rfl) ⟨1804119, by rfl⟩ : syracuseStep 4810985 = 3608239) B3608239
theorem B3207323 : Blo 2137435 3207323 := bstep (se 1 (by rfl) ⟨2405492, by rfl⟩ : syracuseStep 3207323 = 4810985) B4810985
theorem B2138215 : Blo 2137435 2138215 := bstep (se 1 (by rfl) ⟨1603661, by rfl⟩ : syracuseStep 2138215 = 3207323) B3207323
theorem B2405497 : Blo 2137435 2405497 := bbase (se 2 (by rfl) ⟨902061, by rfl⟩ : syracuseStep 2405497 = 1804123) (by norm_num)
theorem B3207329 : Blo 2137435 3207329 := bstep (se 2 (by rfl) ⟨1202748, by rfl⟩ : syracuseStep 3207329 = 2405497) B2405497
theorem B2138219 : Blo 2137435 2138219 := bstep (se 1 (by rfl) ⟨1603664, by rfl⟩ : syracuseStep 2138219 = 3207329) B3207329
theorem B7314965 : Blo 2137435 7314965 := bbase (se 6 (by rfl) ⟨171444, by rfl⟩ : syracuseStep 7314965 = 342889) (by norm_num)
theorem B4876643 : Blo 2137435 4876643 := bstep (se 1 (by rfl) ⟨3657482, by rfl⟩ : syracuseStep 4876643 = 7314965) B7314965
theorem B13004381 : Blo 2137435 13004381 := bstep (se 3 (by rfl) ⟨2438321, by rfl⟩ : syracuseStep 13004381 = 4876643) B4876643
theorem B8669587 : Blo 2137435 8669587 := bstep (se 1 (by rfl) ⟨6502190, by rfl⟩ : syracuseStep 8669587 = 13004381) B13004381
theorem B11559449 : Blo 2137435 11559449 := bstep (se 2 (by rfl) ⟨4334793, by rfl⟩ : syracuseStep 11559449 = 8669587) B8669587
theorem B30825197 : Blo 2137435 30825197 := bstep (se 3 (by rfl) ⟨5779724, by rfl⟩ : syracuseStep 30825197 = 11559449) B11559449
theorem B20550131 : Blo 2137435 20550131 := bstep (se 1 (by rfl) ⟨15412598, by rfl⟩ : syracuseStep 20550131 = 30825197) B30825197
theorem B13700087 : Blo 2137435 13700087 := bstep (se 1 (by rfl) ⟨10275065, by rfl⟩ : syracuseStep 13700087 = 20550131) B20550131
theorem B9133391 : Blo 2137435 9133391 := bstep (se 1 (by rfl) ⟨6850043, by rfl⟩ : syracuseStep 9133391 = 13700087) B13700087
theorem B6088927 : Blo 2137435 6088927 := bstep (se 1 (by rfl) ⟨4566695, by rfl⟩ : syracuseStep 6088927 = 9133391) B9133391
theorem B8118569 : Blo 2137435 8118569 := bstep (se 2 (by rfl) ⟨3044463, by rfl⟩ : syracuseStep 8118569 = 6088927) B6088927
theorem B5412379 : Blo 2137435 5412379 := bstep (se 1 (by rfl) ⟨4059284, by rfl⟩ : syracuseStep 5412379 = 8118569) B8118569
theorem B7216505 : Blo 2137435 7216505 := bstep (se 2 (by rfl) ⟨2706189, by rfl⟩ : syracuseStep 7216505 = 5412379) B5412379
theorem B4811003 : Blo 2137435 4811003 := bstep (se 1 (by rfl) ⟨3608252, by rfl⟩ : syracuseStep 4811003 = 7216505) B7216505
theorem B3207335 : Blo 2137435 3207335 := bstep (se 1 (by rfl) ⟨2405501, by rfl⟩ : syracuseStep 3207335 = 4811003) B4811003
theorem B2138223 : Blo 2137435 2138223 := bstep (se 1 (by rfl) ⟨1603667, by rfl⟩ : syracuseStep 2138223 = 3207335) B3207335
theorem B3207341 : Blo 2137435 3207341 := bbase (se 3 (by rfl) ⟨601376, by rfl⟩ : syracuseStep 3207341 = 1202753) (by norm_num)
theorem B2138227 : Blo 2137435 2138227 := bstep (se 1 (by rfl) ⟨1603670, by rfl⟩ : syracuseStep 2138227 = 3207341) B3207341
theorem B4811021 : Blo 2137435 4811021 := bbase (se 3 (by rfl) ⟨902066, by rfl⟩ : syracuseStep 4811021 = 1804133) (by norm_num)
theorem B3207347 : Blo 2137435 3207347 := bstep (se 1 (by rfl) ⟨2405510, by rfl⟩ : syracuseStep 3207347 = 4811021) B4811021
theorem B2138231 : Blo 2137435 2138231 := bstep (se 1 (by rfl) ⟨1603673, by rfl⟩ : syracuseStep 2138231 = 3207347) B3207347
theorem B2706205 : Blo 2137435 2706205 := bbase (se 3 (by rfl) ⟨507413, by rfl⟩ : syracuseStep 2706205 = 1014827) (by norm_num)
theorem B3608273 : Blo 2137435 3608273 := bstep (se 2 (by rfl) ⟨1353102, by rfl⟩ : syracuseStep 3608273 = 2706205) B2706205
theorem B2405515 : Blo 2137435 2405515 := bstep (se 1 (by rfl) ⟨1804136, by rfl⟩ : syracuseStep 2405515 = 3608273) B3608273
theorem B3207353 : Blo 2137435 3207353 := bstep (se 2 (by rfl) ⟨1202757, by rfl⟩ : syracuseStep 3207353 = 2405515) B2405515
theorem B2138235 : Blo 2137435 2138235 := bstep (se 1 (by rfl) ⟨1603676, by rfl⟩ : syracuseStep 2138235 = 3207353) B3207353
theorem B7706357 : Blo 2137435 7706357 := bbase (se 5 (by rfl) ⟨361235, by rfl⟩ : syracuseStep 7706357 = 722471) (by norm_num)
theorem B5137571 : Blo 2137435 5137571 := bstep (se 1 (by rfl) ⟨3853178, by rfl⟩ : syracuseStep 5137571 = 7706357) B7706357
theorem B3425047 : Blo 2137435 3425047 := bstep (se 1 (by rfl) ⟨2568785, by rfl⟩ : syracuseStep 3425047 = 5137571) B5137571
theorem B18266917 : Blo 2137435 18266917 := bstep (se 4 (by rfl) ⟨1712523, by rfl⟩ : syracuseStep 18266917 = 3425047) B3425047
theorem B24355889 : Blo 2137435 24355889 := bstep (se 2 (by rfl) ⟨9133458, by rfl⟩ : syracuseStep 24355889 = 18266917) B18266917
theorem B16237259 : Blo 2137435 16237259 := bstep (se 1 (by rfl) ⟨12177944, by rfl⟩ : syracuseStep 16237259 = 24355889) B24355889
theorem B10824839 : Blo 2137435 10824839 := bstep (se 1 (by rfl) ⟨8118629, by rfl⟩ : syracuseStep 10824839 = 16237259) B16237259
theorem B7216559 : Blo 2137435 7216559 := bstep (se 1 (by rfl) ⟨5412419, by rfl⟩ : syracuseStep 7216559 = 10824839) B10824839
theorem B4811039 : Blo 2137435 4811039 := bstep (se 1 (by rfl) ⟨3608279, by rfl⟩ : syracuseStep 4811039 = 7216559) B7216559
theorem B3207359 : Blo 2137435 3207359 := bstep (se 1 (by rfl) ⟨2405519, by rfl⟩ : syracuseStep 3207359 = 4811039) B4811039
theorem B2138239 : Blo 2137435 2138239 := bstep (se 1 (by rfl) ⟨1603679, by rfl⟩ : syracuseStep 2138239 = 3207359) B3207359
theorem B3207365 : Blo 2137435 3207365 := bbase (se 4 (by rfl) ⟨300690, by rfl⟩ : syracuseStep 3207365 = 601381) (by norm_num)
theorem B2138243 : Blo 2137435 2138243 := bstep (se 1 (by rfl) ⟨1603682, by rfl⟩ : syracuseStep 2138243 = 3207365) B3207365
theorem B3608293 : Blo 2137435 3608293 := bbase (se 4 (by rfl) ⟨338277, by rfl⟩ : syracuseStep 3608293 = 676555) (by norm_num)
theorem B4811057 : Blo 2137435 4811057 := bstep (se 2 (by rfl) ⟨1804146, by rfl⟩ : syracuseStep 4811057 = 3608293) B3608293
theorem B3207371 : Blo 2137435 3207371 := bstep (se 1 (by rfl) ⟨2405528, by rfl⟩ : syracuseStep 3207371 = 4811057) B4811057
theorem B2138247 : Blo 2137435 2138247 := bstep (se 1 (by rfl) ⟨1603685, by rfl⟩ : syracuseStep 2138247 = 3207371) B3207371
theorem B2405533 : Blo 2137435 2405533 := bbase (se 3 (by rfl) ⟨451037, by rfl⟩ : syracuseStep 2405533 = 902075) (by norm_num)
theorem B3207377 : Blo 2137435 3207377 := bstep (se 2 (by rfl) ⟨1202766, by rfl⟩ : syracuseStep 3207377 = 2405533) B2405533
theorem B2138251 : Blo 2137435 2138251 := bstep (se 1 (by rfl) ⟨1603688, by rfl⟩ : syracuseStep 2138251 = 3207377) B3207377
theorem B7216613 : Blo 2137435 7216613 := bbase (se 4 (by rfl) ⟨676557, by rfl⟩ : syracuseStep 7216613 = 1353115) (by norm_num)
theorem B4811075 : Blo 2137435 4811075 := bstep (se 1 (by rfl) ⟨3608306, by rfl⟩ : syracuseStep 4811075 = 7216613) B7216613
theorem B3207383 : Blo 2137435 3207383 := bstep (se 1 (by rfl) ⟨2405537, by rfl⟩ : syracuseStep 3207383 = 4811075) B4811075
theorem B2138255 : Blo 2137435 2138255 := bstep (se 1 (by rfl) ⟨1603691, by rfl⟩ : syracuseStep 2138255 = 3207383) B3207383
theorem B3207389 : Blo 2137435 3207389 := bbase (se 3 (by rfl) ⟨601385, by rfl⟩ : syracuseStep 3207389 = 1202771) (by norm_num)
theorem B2138259 : Blo 2137435 2138259 := bstep (se 1 (by rfl) ⟨1603694, by rfl⟩ : syracuseStep 2138259 = 3207389) B3207389
theorem B4811093 : Blo 2137435 4811093 := bbase (se 10 (by rfl) ⟨7047, by rfl⟩ : syracuseStep 4811093 = 14095) (by norm_num)
theorem B3207395 : Blo 2137435 3207395 := bstep (se 1 (by rfl) ⟨2405546, by rfl⟩ : syracuseStep 3207395 = 4811093) B4811093
theorem B2138263 : Blo 2137435 2138263 := bstep (se 1 (by rfl) ⟨1603697, by rfl⟩ : syracuseStep 2138263 = 3207395) B3207395
theorem B3425093 : Blo 2137435 3425093 := bbase (se 4 (by rfl) ⟨321102, by rfl⟩ : syracuseStep 3425093 = 642205) (by norm_num)
theorem B2283395 : Blo 2137435 2283395 := bstep (se 1 (by rfl) ⟨1712546, by rfl⟩ : syracuseStep 2283395 = 3425093) B3425093
theorem B6089053 : Blo 2137435 6089053 := bstep (se 3 (by rfl) ⟨1141697, by rfl⟩ : syracuseStep 6089053 = 2283395) B2283395
theorem B8118737 : Blo 2137435 8118737 := bstep (se 2 (by rfl) ⟨3044526, by rfl⟩ : syracuseStep 8118737 = 6089053) B6089053
theorem B5412491 : Blo 2137435 5412491 := bstep (se 1 (by rfl) ⟨4059368, by rfl⟩ : syracuseStep 5412491 = 8118737) B8118737
theorem B3608327 : Blo 2137435 3608327 := bstep (se 1 (by rfl) ⟨2706245, by rfl⟩ : syracuseStep 3608327 = 5412491) B5412491
theorem B2405551 : Blo 2137435 2405551 := bstep (se 1 (by rfl) ⟨1804163, by rfl⟩ : syracuseStep 2405551 = 3608327) B3608327
theorem B3207401 : Blo 2137435 3207401 := bstep (se 2 (by rfl) ⟨1202775, by rfl⟩ : syracuseStep 3207401 = 2405551) B2405551
theorem B2138267 : Blo 2137435 2138267 := bstep (se 1 (by rfl) ⟨1603700, by rfl⟩ : syracuseStep 2138267 = 3207401) B3207401
theorem B13182101 : Blo 2137435 13182101 := bbase (se 6 (by rfl) ⟨308955, by rfl⟩ : syracuseStep 13182101 = 617911) (by norm_num)
theorem B8788067 : Blo 2137435 8788067 := bstep (se 1 (by rfl) ⟨6591050, by rfl⟩ : syracuseStep 8788067 = 13182101) B13182101
theorem B5858711 : Blo 2137435 5858711 := bstep (se 1 (by rfl) ⟨4394033, by rfl⟩ : syracuseStep 5858711 = 8788067) B8788067
theorem B3905807 : Blo 2137435 3905807 := bstep (se 1 (by rfl) ⟨2929355, by rfl⟩ : syracuseStep 3905807 = 5858711) B5858711
theorem B10415485 : Blo 2137435 10415485 := bstep (se 3 (by rfl) ⟨1952903, by rfl⟩ : syracuseStep 10415485 = 3905807) B3905807
theorem B55549253 : Blo 2137435 55549253 := bstep (se 4 (by rfl) ⟨5207742, by rfl⟩ : syracuseStep 55549253 = 10415485) B10415485
theorem B148131341 : Blo 2137435 148131341 := bstep (se 3 (by rfl) ⟨27774626, by rfl⟩ : syracuseStep 148131341 = 55549253) B55549253
theorem B98754227 : Blo 2137435 98754227 := bstep (se 1 (by rfl) ⟨74065670, by rfl⟩ : syracuseStep 98754227 = 148131341) B148131341
theorem B65836151 : Blo 2137435 65836151 := bstep (se 1 (by rfl) ⟨49377113, by rfl⟩ : syracuseStep 65836151 = 98754227) B98754227
theorem B43890767 : Blo 2137435 43890767 := bstep (se 1 (by rfl) ⟨32918075, by rfl⟩ : syracuseStep 43890767 = 65836151) B65836151
theorem B29260511 : Blo 2137435 29260511 := bstep (se 1 (by rfl) ⟨21945383, by rfl⟩ : syracuseStep 29260511 = 43890767) B43890767
theorem B19507007 : Blo 2137435 19507007 := bstep (se 1 (by rfl) ⟨14630255, by rfl⟩ : syracuseStep 19507007 = 29260511) B29260511
theorem B52018685 : Blo 2137435 52018685 := bstep (se 3 (by rfl) ⟨9753503, by rfl⟩ : syracuseStep 52018685 = 19507007) B19507007
theorem B34679123 : Blo 2137435 34679123 := bstep (se 1 (by rfl) ⟨26009342, by rfl⟩ : syracuseStep 34679123 = 52018685) B52018685
theorem B23119415 : Blo 2137435 23119415 := bstep (se 1 (by rfl) ⟨17339561, by rfl⟩ : syracuseStep 23119415 = 34679123) B34679123
theorem B15412943 : Blo 2137435 15412943 := bstep (se 1 (by rfl) ⟨11559707, by rfl⟩ : syracuseStep 15412943 = 23119415) B23119415
theorem B41101181 : Blo 2137435 41101181 := bstep (se 3 (by rfl) ⟨7706471, by rfl⟩ : syracuseStep 41101181 = 15412943) B15412943
theorem B27400787 : Blo 2137435 27400787 := bstep (se 1 (by rfl) ⟨20550590, by rfl⟩ : syracuseStep 27400787 = 41101181) B41101181
theorem B18267191 : Blo 2137435 18267191 := bstep (se 1 (by rfl) ⟨13700393, by rfl⟩ : syracuseStep 18267191 = 27400787) B27400787
theorem B12178127 : Blo 2137435 12178127 := bstep (se 1 (by rfl) ⟨9133595, by rfl⟩ : syracuseStep 12178127 = 18267191) B18267191
theorem B8118751 : Blo 2137435 8118751 := bstep (se 1 (by rfl) ⟨6089063, by rfl⟩ : syracuseStep 8118751 = 12178127) B12178127
theorem B10825001 : Blo 2137435 10825001 := bstep (se 2 (by rfl) ⟨4059375, by rfl⟩ : syracuseStep 10825001 = 8118751) B8118751
theorem B7216667 : Blo 2137435 7216667 := bstep (se 1 (by rfl) ⟨5412500, by rfl⟩ : syracuseStep 7216667 = 10825001) B10825001
theorem B4811111 : Blo 2137435 4811111 := bstep (se 1 (by rfl) ⟨3608333, by rfl⟩ : syracuseStep 4811111 = 7216667) B7216667
theorem B3207407 : Blo 2137435 3207407 := bstep (se 1 (by rfl) ⟨2405555, by rfl⟩ : syracuseStep 3207407 = 4811111) B4811111
theorem B2138271 : Blo 2137435 2138271 := bstep (se 1 (by rfl) ⟨1603703, by rfl⟩ : syracuseStep 2138271 = 3207407) B3207407
theorem B3207413 : Blo 2137435 3207413 := bbase (se 5 (by rfl) ⟨150347, by rfl⟩ : syracuseStep 3207413 = 300695) (by norm_num)
theorem B2138275 : Blo 2137435 2138275 := bstep (se 1 (by rfl) ⟨1603706, by rfl⟩ : syracuseStep 2138275 = 3207413) B3207413
theorem B7315157 : Blo 2137435 7315157 := bbase (se 7 (by rfl) ⟨85724, by rfl⟩ : syracuseStep 7315157 = 171449) (by norm_num)
theorem B4876771 : Blo 2137435 4876771 := bstep (se 1 (by rfl) ⟨3657578, by rfl⟩ : syracuseStep 4876771 = 7315157) B7315157
theorem B6502361 : Blo 2137435 6502361 := bstep (se 2 (by rfl) ⟨2438385, by rfl⟩ : syracuseStep 6502361 = 4876771) B4876771
theorem B69358517 : Blo 2137435 69358517 := bstep (se 5 (by rfl) ⟨3251180, by rfl⟩ : syracuseStep 69358517 = 6502361) B6502361
theorem B46239011 : Blo 2137435 46239011 := bstep (se 1 (by rfl) ⟨34679258, by rfl⟩ : syracuseStep 46239011 = 69358517) B69358517
theorem B30826007 : Blo 2137435 30826007 := bstep (se 1 (by rfl) ⟨23119505, by rfl⟩ : syracuseStep 30826007 = 46239011) B46239011
theorem B20550671 : Blo 2137435 20550671 := bstep (se 1 (by rfl) ⟨15413003, by rfl⟩ : syracuseStep 20550671 = 30826007) B30826007
theorem B13700447 : Blo 2137435 13700447 := bstep (se 1 (by rfl) ⟨10275335, by rfl⟩ : syracuseStep 13700447 = 20550671) B20550671
theorem B9133631 : Blo 2137435 9133631 := bstep (se 1 (by rfl) ⟨6850223, by rfl⟩ : syracuseStep 9133631 = 13700447) B13700447
theorem B6089087 : Blo 2137435 6089087 := bstep (se 1 (by rfl) ⟨4566815, by rfl⟩ : syracuseStep 6089087 = 9133631) B9133631
theorem B4059391 : Blo 2137435 4059391 := bstep (se 1 (by rfl) ⟨3044543, by rfl⟩ : syracuseStep 4059391 = 6089087) B6089087
theorem B5412521 : Blo 2137435 5412521 := bstep (se 2 (by rfl) ⟨2029695, by rfl⟩ : syracuseStep 5412521 = 4059391) B4059391
theorem B3608347 : Blo 2137435 3608347 := bstep (se 1 (by rfl) ⟨2706260, by rfl⟩ : syracuseStep 3608347 = 5412521) B5412521
theorem B4811129 : Blo 2137435 4811129 := bstep (se 2 (by rfl) ⟨1804173, by rfl⟩ : syracuseStep 4811129 = 3608347) B3608347
theorem B3207419 : Blo 2137435 3207419 := bstep (se 1 (by rfl) ⟨2405564, by rfl⟩ : syracuseStep 3207419 = 4811129) B4811129
theorem B2138279 : Blo 2137435 2138279 := bstep (se 1 (by rfl) ⟨1603709, by rfl⟩ : syracuseStep 2138279 = 3207419) B3207419
theorem B2405569 : Blo 2137435 2405569 := bbase (se 2 (by rfl) ⟨902088, by rfl⟩ : syracuseStep 2405569 = 1804177) (by norm_num)
theorem B3207425 : Blo 2137435 3207425 := bstep (se 2 (by rfl) ⟨1202784, by rfl⟩ : syracuseStep 3207425 = 2405569) B2405569
theorem B2138283 : Blo 2137435 2138283 := bstep (se 1 (by rfl) ⟨1603712, by rfl⟩ : syracuseStep 2138283 = 3207425) B3207425
theorem B5412541 : Blo 2137435 5412541 := bbase (se 3 (by rfl) ⟨1014851, by rfl⟩ : syracuseStep 5412541 = 2029703) (by norm_num)
theorem B7216721 : Blo 2137435 7216721 := bstep (se 2 (by rfl) ⟨2706270, by rfl⟩ : syracuseStep 7216721 = 5412541) B5412541
theorem B4811147 : Blo 2137435 4811147 := bstep (se 1 (by rfl) ⟨3608360, by rfl⟩ : syracuseStep 4811147 = 7216721) B7216721
theorem B3207431 : Blo 2137435 3207431 := bstep (se 1 (by rfl) ⟨2405573, by rfl⟩ : syracuseStep 3207431 = 4811147) B4811147
theorem B2138287 : Blo 2137435 2138287 := bstep (se 1 (by rfl) ⟨1603715, by rfl⟩ : syracuseStep 2138287 = 3207431) B3207431
theorem B3207437 : Blo 2137435 3207437 := bbase (se 3 (by rfl) ⟨601394, by rfl⟩ : syracuseStep 3207437 = 1202789) (by norm_num)
theorem B2138291 : Blo 2137435 2138291 := bstep (se 1 (by rfl) ⟨1603718, by rfl⟩ : syracuseStep 2138291 = 3207437) B3207437
theorem B4811165 : Blo 2137435 4811165 := bbase (se 3 (by rfl) ⟨902093, by rfl⟩ : syracuseStep 4811165 = 1804187) (by norm_num)
theorem B3207443 : Blo 2137435 3207443 := bstep (se 1 (by rfl) ⟨2405582, by rfl⟩ : syracuseStep 3207443 = 4811165) B4811165
theorem B2138295 : Blo 2137435 2138295 := bstep (se 1 (by rfl) ⟨1603721, by rfl⟩ : syracuseStep 2138295 = 3207443) B3207443
theorem B3608381 : Blo 2137435 3608381 := bbase (se 3 (by rfl) ⟨676571, by rfl⟩ : syracuseStep 3608381 = 1353143) (by norm_num)
theorem B2405587 : Blo 2137435 2405587 := bstep (se 1 (by rfl) ⟨1804190, by rfl⟩ : syracuseStep 2405587 = 3608381) B3608381
theorem B3207449 : Blo 2137435 3207449 := bstep (se 2 (by rfl) ⟨1202793, by rfl⟩ : syracuseStep 3207449 = 2405587) B2405587
theorem B2138299 : Blo 2137435 2138299 := bstep (se 1 (by rfl) ⟨1603724, by rfl⟩ : syracuseStep 2138299 = 3207449) B3207449
theorem B2283433 : Blo 2137435 2283433 := bbase (se 2 (by rfl) ⟨856287, by rfl⟩ : syracuseStep 2283433 = 1712575) (by norm_num)
theorem B12178309 : Blo 2137435 12178309 := bstep (se 4 (by rfl) ⟨1141716, by rfl⟩ : syracuseStep 12178309 = 2283433) B2283433
theorem B16237745 : Blo 2137435 16237745 := bstep (se 2 (by rfl) ⟨6089154, by rfl⟩ : syracuseStep 16237745 = 12178309) B12178309
theorem B10825163 : Blo 2137435 10825163 := bstep (se 1 (by rfl) ⟨8118872, by rfl⟩ : syracuseStep 10825163 = 16237745) B16237745
theorem B7216775 : Blo 2137435 7216775 := bstep (se 1 (by rfl) ⟨5412581, by rfl⟩ : syracuseStep 7216775 = 10825163) B10825163
theorem B4811183 : Blo 2137435 4811183 := bstep (se 1 (by rfl) ⟨3608387, by rfl⟩ : syracuseStep 4811183 = 7216775) B7216775
theorem B3207455 : Blo 2137435 3207455 := bstep (se 1 (by rfl) ⟨2405591, by rfl⟩ : syracuseStep 3207455 = 4811183) B4811183
theorem B2138303 : Blo 2137435 2138303 := bstep (se 1 (by rfl) ⟨1603727, by rfl⟩ : syracuseStep 2138303 = 3207455) B3207455
theorem B3207461 : Blo 2137435 3207461 := bbase (se 4 (by rfl) ⟨300699, by rfl⟩ : syracuseStep 3207461 = 601399) (by norm_num)
theorem B2138307 : Blo 2137435 2138307 := bstep (se 1 (by rfl) ⟨1603730, by rfl⟩ : syracuseStep 2138307 = 3207461) B3207461
theorem B2706301 : Blo 2137435 2706301 := bbase (se 3 (by rfl) ⟨507431, by rfl⟩ : syracuseStep 2706301 = 1014863) (by norm_num)
theorem B3608401 : Blo 2137435 3608401 := bstep (se 2 (by rfl) ⟨1353150, by rfl⟩ : syracuseStep 3608401 = 2706301) B2706301
theorem B4811201 : Blo 2137435 4811201 := bstep (se 2 (by rfl) ⟨1804200, by rfl⟩ : syracuseStep 4811201 = 3608401) B3608401
theorem B3207467 : Blo 2137435 3207467 := bstep (se 1 (by rfl) ⟨2405600, by rfl⟩ : syracuseStep 3207467 = 4811201) B4811201
theorem B2138311 : Blo 2137435 2138311 := bstep (se 1 (by rfl) ⟨1603733, by rfl⟩ : syracuseStep 2138311 = 3207467) B3207467
theorem B2405605 : Blo 2137435 2405605 := bbase (se 4 (by rfl) ⟨225525, by rfl⟩ : syracuseStep 2405605 = 451051) (by norm_num)
theorem B3207473 : Blo 2137435 3207473 := bstep (se 2 (by rfl) ⟨1202802, by rfl⟩ : syracuseStep 3207473 = 2405605) B2405605
theorem B2138315 : Blo 2137435 2138315 := bstep (se 1 (by rfl) ⟨1603736, by rfl⟩ : syracuseStep 2138315 = 3207473) B3207473
theorem B4566901 : Blo 2137435 4566901 := bbase (se 5 (by rfl) ⟨214073, by rfl⟩ : syracuseStep 4566901 = 428147) (by norm_num)
theorem B6089201 : Blo 2137435 6089201 := bstep (se 2 (by rfl) ⟨2283450, by rfl⟩ : syracuseStep 6089201 = 4566901) B4566901
theorem B4059467 : Blo 2137435 4059467 := bstep (se 1 (by rfl) ⟨3044600, by rfl⟩ : syracuseStep 4059467 = 6089201) B6089201
theorem B2706311 : Blo 2137435 2706311 := bstep (se 1 (by rfl) ⟨2029733, by rfl⟩ : syracuseStep 2706311 = 4059467) B4059467
theorem B7216829 : Blo 2137435 7216829 := bstep (se 3 (by rfl) ⟨1353155, by rfl⟩ : syracuseStep 7216829 = 2706311) B2706311
theorem B4811219 : Blo 2137435 4811219 := bstep (se 1 (by rfl) ⟨3608414, by rfl⟩ : syracuseStep 4811219 = 7216829) B7216829
theorem B3207479 : Blo 2137435 3207479 := bstep (se 1 (by rfl) ⟨2405609, by rfl⟩ : syracuseStep 3207479 = 4811219) B4811219
theorem B2138319 : Blo 2137435 2138319 := bstep (se 1 (by rfl) ⟨1603739, by rfl⟩ : syracuseStep 2138319 = 3207479) B3207479
theorem B3207485 : Blo 2137435 3207485 := bbase (se 3 (by rfl) ⟨601403, by rfl⟩ : syracuseStep 3207485 = 1202807) (by norm_num)
theorem B2138323 : Blo 2137435 2138323 := bstep (se 1 (by rfl) ⟨1603742, by rfl⟩ : syracuseStep 2138323 = 3207485) B3207485
theorem B4811237 : Blo 2137435 4811237 := bbase (se 4 (by rfl) ⟨451053, by rfl⟩ : syracuseStep 4811237 = 902107) (by norm_num)
theorem B3207491 : Blo 2137435 3207491 := bstep (se 1 (by rfl) ⟨2405618, by rfl⟩ : syracuseStep 3207491 = 4811237) B4811237
theorem B2138327 : Blo 2137435 2138327 := bstep (se 1 (by rfl) ⟨1603745, by rfl⟩ : syracuseStep 2138327 = 3207491) B3207491
theorem B5412653 : Blo 2137435 5412653 := bbase (se 3 (by rfl) ⟨1014872, by rfl⟩ : syracuseStep 5412653 = 2029745) (by norm_num)
theorem B3608435 : Blo 2137435 3608435 := bstep (se 1 (by rfl) ⟨2706326, by rfl⟩ : syracuseStep 3608435 = 5412653) B5412653
theorem B2405623 : Blo 2137435 2405623 := bstep (se 1 (by rfl) ⟨1804217, by rfl⟩ : syracuseStep 2405623 = 3608435) B3608435
theorem B3207497 : Blo 2137435 3207497 := bstep (se 2 (by rfl) ⟨1202811, by rfl⟩ : syracuseStep 3207497 = 2405623) B2405623
theorem B2138331 : Blo 2137435 2138331 := bstep (se 1 (by rfl) ⟨1603748, by rfl⟩ : syracuseStep 2138331 = 3207497) B3207497
theorem B10275605 : Blo 2137435 10275605 := bbase (se 6 (by rfl) ⟨240834, by rfl⟩ : syracuseStep 10275605 = 481669) (by norm_num)
theorem B6850403 : Blo 2137435 6850403 := bstep (se 1 (by rfl) ⟨5137802, by rfl⟩ : syracuseStep 6850403 = 10275605) B10275605
theorem B4566935 : Blo 2137435 4566935 := bstep (se 1 (by rfl) ⟨3425201, by rfl⟩ : syracuseStep 4566935 = 6850403) B6850403
theorem B3044623 : Blo 2137435 3044623 := bstep (se 1 (by rfl) ⟨2283467, by rfl⟩ : syracuseStep 3044623 = 4566935) B4566935
theorem B4059497 : Blo 2137435 4059497 := bstep (se 2 (by rfl) ⟨1522311, by rfl⟩ : syracuseStep 4059497 = 3044623) B3044623
theorem B10825325 : Blo 2137435 10825325 := bstep (se 3 (by rfl) ⟨2029748, by rfl⟩ : syracuseStep 10825325 = 4059497) B4059497
theorem B7216883 : Blo 2137435 7216883 := bstep (se 1 (by rfl) ⟨5412662, by rfl⟩ : syracuseStep 7216883 = 10825325) B10825325
theorem B4811255 : Blo 2137435 4811255 := bstep (se 1 (by rfl) ⟨3608441, by rfl⟩ : syracuseStep 4811255 = 7216883) B7216883
theorem B3207503 : Blo 2137435 3207503 := bstep (se 1 (by rfl) ⟨2405627, by rfl⟩ : syracuseStep 3207503 = 4811255) B4811255
theorem B2138335 : Blo 2137435 2138335 := bstep (se 1 (by rfl) ⟨1603751, by rfl⟩ : syracuseStep 2138335 = 3207503) B3207503
theorem B3207509 : Blo 2137435 3207509 := bbase (se 10 (by rfl) ⟨4698, by rfl⟩ : syracuseStep 3207509 = 9397) (by norm_num)
theorem B2138339 : Blo 2137435 2138339 := bstep (se 1 (by rfl) ⟨1603754, by rfl⟩ : syracuseStep 2138339 = 3207509) B3207509
theorem B6089269 : Blo 2137435 6089269 := bbase (se 5 (by rfl) ⟨285434, by rfl⟩ : syracuseStep 6089269 = 570869) (by norm_num)
theorem B8119025 : Blo 2137435 8119025 := bstep (se 2 (by rfl) ⟨3044634, by rfl⟩ : syracuseStep 8119025 = 6089269) B6089269
theorem B5412683 : Blo 2137435 5412683 := bstep (se 1 (by rfl) ⟨4059512, by rfl⟩ : syracuseStep 5412683 = 8119025) B8119025
theorem B3608455 : Blo 2137435 3608455 := bstep (se 1 (by rfl) ⟨2706341, by rfl⟩ : syracuseStep 3608455 = 5412683) B5412683
theorem B4811273 : Blo 2137435 4811273 := bstep (se 2 (by rfl) ⟨1804227, by rfl⟩ : syracuseStep 4811273 = 3608455) B3608455
theorem B3207515 : Blo 2137435 3207515 := bstep (se 1 (by rfl) ⟨2405636, by rfl⟩ : syracuseStep 3207515 = 4811273) B4811273
theorem B2138343 : Blo 2137435 2138343 := bstep (se 1 (by rfl) ⟨1603757, by rfl⟩ : syracuseStep 2138343 = 3207515) B3207515
theorem B2405641 : Blo 2137435 2405641 := bbase (se 2 (by rfl) ⟨902115, by rfl⟩ : syracuseStep 2405641 = 1804231) (by norm_num)
theorem B3207521 : Blo 2137435 3207521 := bstep (se 2 (by rfl) ⟨1202820, by rfl⟩ : syracuseStep 3207521 = 2405641) B2405641
theorem B2138347 : Blo 2137435 2138347 := bstep (se 1 (by rfl) ⟨1603760, by rfl⟩ : syracuseStep 2138347 = 3207521) B3207521
theorem B27401813 : Blo 2137435 27401813 := bbase (se 8 (by rfl) ⟨160557, by rfl⟩ : syracuseStep 27401813 = 321115) (by norm_num)
theorem B18267875 : Blo 2137435 18267875 := bstep (se 1 (by rfl) ⟨13700906, by rfl⟩ : syracuseStep 18267875 = 27401813) B27401813
theorem B12178583 : Blo 2137435 12178583 := bstep (se 1 (by rfl) ⟨9133937, by rfl⟩ : syracuseStep 12178583 = 18267875) B18267875
theorem B8119055 : Blo 2137435 8119055 := bstep (se 1 (by rfl) ⟨6089291, by rfl⟩ : syracuseStep 8119055 = 12178583) B12178583
theorem B5412703 : Blo 2137435 5412703 := bstep (se 1 (by rfl) ⟨4059527, by rfl⟩ : syracuseStep 5412703 = 8119055) B8119055
theorem B7216937 : Blo 2137435 7216937 := bstep (se 2 (by rfl) ⟨2706351, by rfl⟩ : syracuseStep 7216937 = 5412703) B5412703
theorem B4811291 : Blo 2137435 4811291 := bstep (se 1 (by rfl) ⟨3608468, by rfl⟩ : syracuseStep 4811291 = 7216937) B7216937
theorem B3207527 : Blo 2137435 3207527 := bstep (se 1 (by rfl) ⟨2405645, by rfl⟩ : syracuseStep 3207527 = 4811291) B4811291
theorem B2138351 : Blo 2137435 2138351 := bstep (se 1 (by rfl) ⟨1603763, by rfl⟩ : syracuseStep 2138351 = 3207527) B3207527
theorem B3207533 : Blo 2137435 3207533 := bbase (se 3 (by rfl) ⟨601412, by rfl⟩ : syracuseStep 3207533 = 1202825) (by norm_num)
theorem B2138355 : Blo 2137435 2138355 := bstep (se 1 (by rfl) ⟨1603766, by rfl⟩ : syracuseStep 2138355 = 3207533) B3207533
theorem B4811309 : Blo 2137435 4811309 := bbase (se 3 (by rfl) ⟨902120, by rfl⟩ : syracuseStep 4811309 = 1804241) (by norm_num)
theorem B3207539 : Blo 2137435 3207539 := bstep (se 1 (by rfl) ⟨2405654, by rfl⟩ : syracuseStep 3207539 = 4811309) B4811309
theorem B2138359 : Blo 2137435 2138359 := bstep (se 1 (by rfl) ⟨1603769, by rfl⟩ : syracuseStep 2138359 = 3207539) B3207539
theorem B7315445 : Blo 2137435 7315445 := bbase (se 5 (by rfl) ⟨342911, by rfl⟩ : syracuseStep 7315445 = 685823) (by norm_num)
theorem B19507853 : Blo 2137435 19507853 := bstep (se 3 (by rfl) ⟨3657722, by rfl⟩ : syracuseStep 19507853 = 7315445) B7315445
theorem B13005235 : Blo 2137435 13005235 := bstep (se 1 (by rfl) ⟨9753926, by rfl⟩ : syracuseStep 13005235 = 19507853) B19507853
theorem B17340313 : Blo 2137435 17340313 := bstep (se 2 (by rfl) ⟨6502617, by rfl⟩ : syracuseStep 17340313 = 13005235) B13005235
theorem B23120417 : Blo 2137435 23120417 := bstep (se 2 (by rfl) ⟨8670156, by rfl⟩ : syracuseStep 23120417 = 17340313) B17340313
theorem B15413611 : Blo 2137435 15413611 := bstep (se 1 (by rfl) ⟨11560208, by rfl⟩ : syracuseStep 15413611 = 23120417) B23120417
theorem B20551481 : Blo 2137435 20551481 := bstep (se 2 (by rfl) ⟨7706805, by rfl⟩ : syracuseStep 20551481 = 15413611) B15413611
theorem B13700987 : Blo 2137435 13700987 := bstep (se 1 (by rfl) ⟨10275740, by rfl⟩ : syracuseStep 13700987 = 20551481) B20551481
theorem B9133991 : Blo 2137435 9133991 := bstep (se 1 (by rfl) ⟨6850493, by rfl⟩ : syracuseStep 9133991 = 13700987) B13700987
theorem B6089327 : Blo 2137435 6089327 := bstep (se 1 (by rfl) ⟨4566995, by rfl⟩ : syracuseStep 6089327 = 9133991) B9133991
theorem B4059551 : Blo 2137435 4059551 := bstep (se 1 (by rfl) ⟨3044663, by rfl⟩ : syracuseStep 4059551 = 6089327) B6089327
theorem B2706367 : Blo 2137435 2706367 := bstep (se 1 (by rfl) ⟨2029775, by rfl⟩ : syracuseStep 2706367 = 4059551) B4059551
theorem B3608489 : Blo 2137435 3608489 := bstep (se 2 (by rfl) ⟨1353183, by rfl⟩ : syracuseStep 3608489 = 2706367) B2706367
theorem B2405659 : Blo 2137435 2405659 := bstep (se 1 (by rfl) ⟨1804244, by rfl⟩ : syracuseStep 2405659 = 3608489) B3608489
theorem B3207545 : Blo 2137435 3207545 := bstep (se 2 (by rfl) ⟨1202829, by rfl⟩ : syracuseStep 3207545 = 2405659) B2405659
theorem B2138363 : Blo 2137435 2138363 := bstep (se 1 (by rfl) ⟨1603772, by rfl⟩ : syracuseStep 2138363 = 3207545) B3207545
theorem B36536021 : Blo 2137435 36536021 := bbase (se 7 (by rfl) ⟨428156, by rfl⟩ : syracuseStep 36536021 = 856313) (by norm_num)
theorem B24357347 : Blo 2137435 24357347 := bstep (se 1 (by rfl) ⟨18268010, by rfl⟩ : syracuseStep 24357347 = 36536021) B36536021
theorem B16238231 : Blo 2137435 16238231 := bstep (se 1 (by rfl) ⟨12178673, by rfl⟩ : syracuseStep 16238231 = 24357347) B24357347
theorem B10825487 : Blo 2137435 10825487 := bstep (se 1 (by rfl) ⟨8119115, by rfl⟩ : syracuseStep 10825487 = 16238231) B16238231
theorem B7216991 : Blo 2137435 7216991 := bstep (se 1 (by rfl) ⟨5412743, by rfl⟩ : syracuseStep 7216991 = 10825487) B10825487
theorem B4811327 : Blo 2137435 4811327 := bstep (se 1 (by rfl) ⟨3608495, by rfl⟩ : syracuseStep 4811327 = 7216991) B7216991
theorem B3207551 : Blo 2137435 3207551 := bstep (se 1 (by rfl) ⟨2405663, by rfl⟩ : syracuseStep 3207551 = 4811327) B4811327
theorem B2138367 : Blo 2137435 2138367 := bstep (se 1 (by rfl) ⟨1603775, by rfl⟩ : syracuseStep 2138367 = 3207551) B3207551
theorem B3207557 : Blo 2137435 3207557 := bbase (se 4 (by rfl) ⟨300708, by rfl⟩ : syracuseStep 3207557 = 601417) (by norm_num)
theorem B2138371 : Blo 2137435 2138371 := bstep (se 1 (by rfl) ⟨1603778, by rfl⟩ : syracuseStep 2138371 = 3207557) B3207557
theorem B3608509 : Blo 2137435 3608509 := bbase (se 3 (by rfl) ⟨676595, by rfl⟩ : syracuseStep 3608509 = 1353191) (by norm_num)
theorem B4811345 : Blo 2137435 4811345 := bstep (se 2 (by rfl) ⟨1804254, by rfl⟩ : syracuseStep 4811345 = 3608509) B3608509
theorem B3207563 : Blo 2137435 3207563 := bstep (se 1 (by rfl) ⟨2405672, by rfl⟩ : syracuseStep 3207563 = 4811345) B4811345
theorem B2138375 : Blo 2137435 2138375 := bstep (se 1 (by rfl) ⟨1603781, by rfl⟩ : syracuseStep 2138375 = 3207563) B3207563
theorem B2405677 : Blo 2137435 2405677 := bbase (se 3 (by rfl) ⟨451064, by rfl⟩ : syracuseStep 2405677 = 902129) (by norm_num)
theorem B3207569 : Blo 2137435 3207569 := bstep (se 2 (by rfl) ⟨1202838, by rfl⟩ : syracuseStep 3207569 = 2405677) B2405677
theorem B2138379 : Blo 2137435 2138379 := bstep (se 1 (by rfl) ⟨1603784, by rfl⟩ : syracuseStep 2138379 = 3207569) B3207569
theorem B7217045 : Blo 2137435 7217045 := bbase (se 6 (by rfl) ⟨169149, by rfl⟩ : syracuseStep 7217045 = 338299) (by norm_num)
theorem B4811363 : Blo 2137435 4811363 := bstep (se 1 (by rfl) ⟨3608522, by rfl⟩ : syracuseStep 4811363 = 7217045) B7217045
theorem B3207575 : Blo 2137435 3207575 := bstep (se 1 (by rfl) ⟨2405681, by rfl⟩ : syracuseStep 3207575 = 4811363) B4811363
theorem B2138383 : Blo 2137435 2138383 := bstep (se 1 (by rfl) ⟨1603787, by rfl⟩ : syracuseStep 2138383 = 3207575) B3207575
theorem B3207581 : Blo 2137435 3207581 := bbase (se 3 (by rfl) ⟨601421, by rfl⟩ : syracuseStep 3207581 = 1202843) (by norm_num)
theorem B2138387 : Blo 2137435 2138387 := bstep (se 1 (by rfl) ⟨1603790, by rfl⟩ : syracuseStep 2138387 = 3207581) B3207581
theorem B4811381 : Blo 2137435 4811381 := bbase (se 5 (by rfl) ⟨225533, by rfl⟩ : syracuseStep 4811381 = 451067) (by norm_num)
theorem B3207587 : Blo 2137435 3207587 := bstep (se 1 (by rfl) ⟨2405690, by rfl⟩ : syracuseStep 3207587 = 4811381) B4811381
theorem B2138391 : Blo 2137435 2138391 := bstep (se 1 (by rfl) ⟨1603793, by rfl⟩ : syracuseStep 2138391 = 3207587) B3207587
theorem B10275893 : Blo 2137435 10275893 := bbase (se 5 (by rfl) ⟨481682, by rfl⟩ : syracuseStep 10275893 = 963365) (by norm_num)
theorem B6850595 : Blo 2137435 6850595 := bstep (se 1 (by rfl) ⟨5137946, by rfl⟩ : syracuseStep 6850595 = 10275893) B10275893
theorem B18268253 : Blo 2137435 18268253 := bstep (se 3 (by rfl) ⟨3425297, by rfl⟩ : syracuseStep 18268253 = 6850595) B6850595
theorem B12178835 : Blo 2137435 12178835 := bstep (se 1 (by rfl) ⟨9134126, by rfl⟩ : syracuseStep 12178835 = 18268253) B18268253
theorem B8119223 : Blo 2137435 8119223 := bstep (se 1 (by rfl) ⟨6089417, by rfl⟩ : syracuseStep 8119223 = 12178835) B12178835
theorem B5412815 : Blo 2137435 5412815 := bstep (se 1 (by rfl) ⟨4059611, by rfl⟩ : syracuseStep 5412815 = 8119223) B8119223
theorem B3608543 : Blo 2137435 3608543 := bstep (se 1 (by rfl) ⟨2706407, by rfl⟩ : syracuseStep 3608543 = 5412815) B5412815
theorem B2405695 : Blo 2137435 2405695 := bstep (se 1 (by rfl) ⟨1804271, by rfl⟩ : syracuseStep 2405695 = 3608543) B3608543
theorem B3207593 : Blo 2137435 3207593 := bstep (se 2 (by rfl) ⟨1202847, by rfl⟩ : syracuseStep 3207593 = 2405695) B2405695
theorem B2138395 : Blo 2137435 2138395 := bstep (se 1 (by rfl) ⟨1603796, by rfl⟩ : syracuseStep 2138395 = 3207593) B3207593
theorem B8119237 : Blo 2137435 8119237 := bbase (se 4 (by rfl) ⟨761178, by rfl⟩ : syracuseStep 8119237 = 1522357) (by norm_num)
theorem B10825649 : Blo 2137435 10825649 := bstep (se 2 (by rfl) ⟨4059618, by rfl⟩ : syracuseStep 10825649 = 8119237) B8119237
theorem B7217099 : Blo 2137435 7217099 := bstep (se 1 (by rfl) ⟨5412824, by rfl⟩ : syracuseStep 7217099 = 10825649) B10825649
theorem B4811399 : Blo 2137435 4811399 := bstep (se 1 (by rfl) ⟨3608549, by rfl⟩ : syracuseStep 4811399 = 7217099) B7217099
theorem B3207599 : Blo 2137435 3207599 := bstep (se 1 (by rfl) ⟨2405699, by rfl⟩ : syracuseStep 3207599 = 4811399) B4811399
theorem B2138399 : Blo 2137435 2138399 := bstep (se 1 (by rfl) ⟨1603799, by rfl⟩ : syracuseStep 2138399 = 3207599) B3207599
theorem B3207605 : Blo 2137435 3207605 := bbase (se 5 (by rfl) ⟨150356, by rfl⟩ : syracuseStep 3207605 = 300713) (by norm_num)
theorem B2138403 : Blo 2137435 2138403 := bstep (se 1 (by rfl) ⟨1603802, by rfl⟩ : syracuseStep 2138403 = 3207605) B3207605
theorem B5412845 : Blo 2137435 5412845 := bbase (se 3 (by rfl) ⟨1014908, by rfl⟩ : syracuseStep 5412845 = 2029817) (by norm_num)
theorem B3608563 : Blo 2137435 3608563 := bstep (se 1 (by rfl) ⟨2706422, by rfl⟩ : syracuseStep 3608563 = 5412845) B5412845
theorem B4811417 : Blo 2137435 4811417 := bstep (se 2 (by rfl) ⟨1804281, by rfl⟩ : syracuseStep 4811417 = 3608563) B3608563
theorem B3207611 : Blo 2137435 3207611 := bstep (se 1 (by rfl) ⟨2405708, by rfl⟩ : syracuseStep 3207611 = 4811417) B4811417
theorem B2138407 : Blo 2137435 2138407 := bstep (se 1 (by rfl) ⟨1603805, by rfl⟩ : syracuseStep 2138407 = 3207611) B3207611
theorem B2405713 : Blo 2137435 2405713 := bbase (se 2 (by rfl) ⟨902142, by rfl⟩ : syracuseStep 2405713 = 1804285) (by norm_num)
theorem B3207617 : Blo 2137435 3207617 := bstep (se 2 (by rfl) ⟨1202856, by rfl⟩ : syracuseStep 3207617 = 2405713) B2405713
theorem B2138411 : Blo 2137435 2138411 := bstep (se 1 (by rfl) ⟨1603808, by rfl⟩ : syracuseStep 2138411 = 3207617) B3207617
theorem B2283553 : Blo 2137435 2283553 := bbase (se 2 (by rfl) ⟨856332, by rfl⟩ : syracuseStep 2283553 = 1712665) (by norm_num)
theorem B3044737 : Blo 2137435 3044737 := bstep (se 2 (by rfl) ⟨1141776, by rfl⟩ : syracuseStep 3044737 = 2283553) B2283553
theorem B4059649 : Blo 2137435 4059649 := bstep (se 2 (by rfl) ⟨1522368, by rfl⟩ : syracuseStep 4059649 = 3044737) B3044737
theorem B5412865 : Blo 2137435 5412865 := bstep (se 2 (by rfl) ⟨2029824, by rfl⟩ : syracuseStep 5412865 = 4059649) B4059649
theorem B7217153 : Blo 2137435 7217153 := bstep (se 2 (by rfl) ⟨2706432, by rfl⟩ : syracuseStep 7217153 = 5412865) B5412865
theorem B4811435 : Blo 2137435 4811435 := bstep (se 1 (by rfl) ⟨3608576, by rfl⟩ : syracuseStep 4811435 = 7217153) B7217153
theorem B3207623 : Blo 2137435 3207623 := bstep (se 1 (by rfl) ⟨2405717, by rfl⟩ : syracuseStep 3207623 = 4811435) B4811435
theorem B2138415 : Blo 2137435 2138415 := bstep (se 1 (by rfl) ⟨1603811, by rfl⟩ : syracuseStep 2138415 = 3207623) B3207623
theorem B3207629 : Blo 2137435 3207629 := bbase (se 3 (by rfl) ⟨601430, by rfl⟩ : syracuseStep 3207629 = 1202861) (by norm_num)
theorem B2138419 : Blo 2137435 2138419 := bstep (se 1 (by rfl) ⟨1603814, by rfl⟩ : syracuseStep 2138419 = 3207629) B3207629
theorem B4811453 : Blo 2137435 4811453 := bbase (se 3 (by rfl) ⟨902147, by rfl⟩ : syracuseStep 4811453 = 1804295) (by norm_num)
theorem B3207635 : Blo 2137435 3207635 := bstep (se 1 (by rfl) ⟨2405726, by rfl⟩ : syracuseStep 3207635 = 4811453) B4811453
theorem B2138423 : Blo 2137435 2138423 := bstep (se 1 (by rfl) ⟨1603817, by rfl⟩ : syracuseStep 2138423 = 3207635) B3207635
theorem B3608597 : Blo 2137435 3608597 := bbase (se 6 (by rfl) ⟨84576, by rfl⟩ : syracuseStep 3608597 = 169153) (by norm_num)
theorem B2405731 : Blo 2137435 2405731 := bstep (se 1 (by rfl) ⟨1804298, by rfl⟩ : syracuseStep 2405731 = 3608597) B3608597
theorem B3207641 : Blo 2137435 3207641 := bstep (se 2 (by rfl) ⟨1202865, by rfl⟩ : syracuseStep 3207641 = 2405731) B2405731
theorem B2138427 : Blo 2137435 2138427 := bstep (se 1 (by rfl) ⟨1603820, by rfl⟩ : syracuseStep 2138427 = 3207641) B3207641
theorem B12345205 : Blo 2137435 12345205 := bbase (se 5 (by rfl) ⟨578681, by rfl⟩ : syracuseStep 12345205 = 1157363) (by norm_num)
theorem B16460273 : Blo 2137435 16460273 := bstep (se 2 (by rfl) ⟨6172602, by rfl⟩ : syracuseStep 16460273 = 12345205) B12345205
theorem B10973515 : Blo 2137435 10973515 := bstep (se 1 (by rfl) ⟨8230136, by rfl⟩ : syracuseStep 10973515 = 16460273) B16460273
theorem B14631353 : Blo 2137435 14631353 := bstep (se 2 (by rfl) ⟨5486757, by rfl⟩ : syracuseStep 14631353 = 10973515) B10973515
theorem B9754235 : Blo 2137435 9754235 := bstep (se 1 (by rfl) ⟨7315676, by rfl⟩ : syracuseStep 9754235 = 14631353) B14631353
theorem B6502823 : Blo 2137435 6502823 := bstep (se 1 (by rfl) ⟨4877117, by rfl⟩ : syracuseStep 6502823 = 9754235) B9754235
theorem B4335215 : Blo 2137435 4335215 := bstep (se 1 (by rfl) ⟨3251411, by rfl⟩ : syracuseStep 4335215 = 6502823) B6502823
theorem B11560573 : Blo 2137435 11560573 := bstep (se 3 (by rfl) ⟨2167607, by rfl⟩ : syracuseStep 11560573 = 4335215) B4335215
theorem B15414097 : Blo 2137435 15414097 := bstep (se 2 (by rfl) ⟨5780286, by rfl⟩ : syracuseStep 15414097 = 11560573) B11560573
theorem B20552129 : Blo 2137435 20552129 := bstep (se 2 (by rfl) ⟨7707048, by rfl⟩ : syracuseStep 20552129 = 15414097) B15414097
theorem B13701419 : Blo 2137435 13701419 := bstep (se 1 (by rfl) ⟨10276064, by rfl⟩ : syracuseStep 13701419 = 20552129) B20552129
theorem B9134279 : Blo 2137435 9134279 := bstep (se 1 (by rfl) ⟨6850709, by rfl⟩ : syracuseStep 9134279 = 13701419) B13701419
theorem B6089519 : Blo 2137435 6089519 := bstep (se 1 (by rfl) ⟨4567139, by rfl⟩ : syracuseStep 6089519 = 9134279) B9134279
theorem B16238717 : Blo 2137435 16238717 := bstep (se 3 (by rfl) ⟨3044759, by rfl⟩ : syracuseStep 16238717 = 6089519) B6089519
theorem B10825811 : Blo 2137435 10825811 := bstep (se 1 (by rfl) ⟨8119358, by rfl⟩ : syracuseStep 10825811 = 16238717) B16238717
theorem B7217207 : Blo 2137435 7217207 := bstep (se 1 (by rfl) ⟨5412905, by rfl⟩ : syracuseStep 7217207 = 10825811) B10825811
theorem B4811471 : Blo 2137435 4811471 := bstep (se 1 (by rfl) ⟨3608603, by rfl⟩ : syracuseStep 4811471 = 7217207) B7217207
theorem B3207647 : Blo 2137435 3207647 := bstep (se 1 (by rfl) ⟨2405735, by rfl⟩ : syracuseStep 3207647 = 4811471) B4811471
theorem B2138431 : Blo 2137435 2138431 := bstep (se 1 (by rfl) ⟨1603823, by rfl⟩ : syracuseStep 2138431 = 3207647) B3207647
theorem B3207653 : Blo 2137435 3207653 := bbase (se 4 (by rfl) ⟨300717, by rfl⟩ : syracuseStep 3207653 = 601435) (by norm_num)
theorem B2138435 : Blo 2137435 2138435 := bstep (se 1 (by rfl) ⟨1603826, by rfl⟩ : syracuseStep 2138435 = 3207653) B3207653
theorem B4576709 : Blo 2137435 4576709 := bbase (se 4 (by rfl) ⟨429066, by rfl⟩ : syracuseStep 4576709 = 858133) (by norm_num)
theorem B12204557 : Blo 2137435 12204557 := bstep (se 3 (by rfl) ⟨2288354, by rfl⟩ : syracuseStep 12204557 = 4576709) B4576709
theorem B8136371 : Blo 2137435 8136371 := bstep (se 1 (by rfl) ⟨6102278, by rfl⟩ : syracuseStep 8136371 = 12204557) B12204557
theorem B21696989 : Blo 2137435 21696989 := bstep (se 3 (by rfl) ⟨4068185, by rfl⟩ : syracuseStep 21696989 = 8136371) B8136371
theorem B57858637 : Blo 2137435 57858637 := bstep (se 3 (by rfl) ⟨10848494, by rfl⟩ : syracuseStep 57858637 = 21696989) B21696989
theorem B77144849 : Blo 2137435 77144849 := bstep (se 2 (by rfl) ⟨28929318, by rfl⟩ : syracuseStep 77144849 = 57858637) B57858637
theorem B51429899 : Blo 2137435 51429899 := bstep (se 1 (by rfl) ⟨38572424, by rfl⟩ : syracuseStep 51429899 = 77144849) B77144849
theorem B34286599 : Blo 2137435 34286599 := bstep (se 1 (by rfl) ⟨25714949, by rfl⟩ : syracuseStep 34286599 = 51429899) B51429899
theorem B11703159125 : Blo 2137435 11703159125 := bstep (se 10 (by rfl) ⟨17143299, by rfl⟩ : syracuseStep 11703159125 = 34286599) B34286599
theorem B7802106083 : Blo 2137435 7802106083 := bstep (se 1 (by rfl) ⟨5851579562, by rfl⟩ : syracuseStep 7802106083 = 11703159125) B11703159125
theorem B5201404055 : Blo 2137435 5201404055 := bstep (se 1 (by rfl) ⟨3901053041, by rfl⟩ : syracuseStep 5201404055 = 7802106083) B7802106083
theorem B3467602703 : Blo 2137435 3467602703 := bstep (se 1 (by rfl) ⟨2600702027, by rfl⟩ : syracuseStep 3467602703 = 5201404055) B5201404055
theorem B2311735135 : Blo 2137435 2311735135 := bstep (se 1 (by rfl) ⟨1733801351, by rfl⟩ : syracuseStep 2311735135 = 3467602703) B3467602703
theorem B3082313513 : Blo 2137435 3082313513 := bstep (se 2 (by rfl) ⟨1155867567, by rfl⟩ : syracuseStep 3082313513 = 2311735135) B2311735135
theorem B2054875675 : Blo 2137435 2054875675 := bstep (se 1 (by rfl) ⟨1541156756, by rfl⟩ : syracuseStep 2054875675 = 3082313513) B3082313513
theorem B2739834233 : Blo 2137435 2739834233 := bstep (se 2 (by rfl) ⟨1027437837, by rfl⟩ : syracuseStep 2739834233 = 2054875675) B2054875675
theorem B1826556155 : Blo 2137435 1826556155 := bstep (se 1 (by rfl) ⟨1369917116, by rfl⟩ : syracuseStep 1826556155 = 2739834233) B2739834233
theorem B1217704103 : Blo 2137435 1217704103 := bstep (se 1 (by rfl) ⟨913278077, by rfl⟩ : syracuseStep 1217704103 = 1826556155) B1826556155
theorem B811802735 : Blo 2137435 811802735 := bstep (se 1 (by rfl) ⟨608852051, by rfl⟩ : syracuseStep 811802735 = 1217704103) B1217704103
theorem B541201823 : Blo 2137435 541201823 := bstep (se 1 (by rfl) ⟨405901367, by rfl⟩ : syracuseStep 541201823 = 811802735) B811802735
theorem B360801215 : Blo 2137435 360801215 := bstep (se 1 (by rfl) ⟨270600911, by rfl⟩ : syracuseStep 360801215 = 541201823) B541201823
theorem B240534143 : Blo 2137435 240534143 := bstep (se 1 (by rfl) ⟨180400607, by rfl⟩ : syracuseStep 240534143 = 360801215) B360801215
theorem B160356095 : Blo 2137435 160356095 := bstep (se 1 (by rfl) ⟨120267071, by rfl⟩ : syracuseStep 160356095 = 240534143) B240534143
theorem B106904063 : Blo 2137435 106904063 := bstep (se 1 (by rfl) ⟨80178047, by rfl⟩ : syracuseStep 106904063 = 160356095) B160356095
theorem B285077501 : Blo 2137435 285077501 := bstep (se 3 (by rfl) ⟨53452031, by rfl⟩ : syracuseStep 285077501 = 106904063) B106904063
theorem B190051667 : Blo 2137435 190051667 := bstep (se 1 (by rfl) ⟨142538750, by rfl⟩ : syracuseStep 190051667 = 285077501) B285077501
theorem B126701111 : Blo 2137435 126701111 := bstep (se 1 (by rfl) ⟨95025833, by rfl⟩ : syracuseStep 126701111 = 190051667) B190051667
theorem B84467407 : Blo 2137435 84467407 := bstep (se 1 (by rfl) ⟨63350555, by rfl⟩ : syracuseStep 84467407 = 126701111) B126701111
theorem B112623209 : Blo 2137435 112623209 := bstep (se 2 (by rfl) ⟨42233703, by rfl⟩ : syracuseStep 112623209 = 84467407) B84467407
theorem B75082139 : Blo 2137435 75082139 := bstep (se 1 (by rfl) ⟨56311604, by rfl⟩ : syracuseStep 75082139 = 112623209) B112623209
theorem B50054759 : Blo 2137435 50054759 := bstep (se 1 (by rfl) ⟨37541069, by rfl⟩ : syracuseStep 50054759 = 75082139) B75082139
theorem B33369839 : Blo 2137435 33369839 := bstep (se 1 (by rfl) ⟨25027379, by rfl⟩ : syracuseStep 33369839 = 50054759) B50054759
theorem B22246559 : Blo 2137435 22246559 := bstep (se 1 (by rfl) ⟨16684919, by rfl⟩ : syracuseStep 22246559 = 33369839) B33369839
theorem B14831039 : Blo 2137435 14831039 := bstep (se 1 (by rfl) ⟨11123279, by rfl⟩ : syracuseStep 14831039 = 22246559) B22246559
theorem B9887359 : Blo 2137435 9887359 := bstep (se 1 (by rfl) ⟨7415519, by rfl⟩ : syracuseStep 9887359 = 14831039) B14831039
theorem B13183145 : Blo 2137435 13183145 := bstep (se 2 (by rfl) ⟨4943679, by rfl⟩ : syracuseStep 13183145 = 9887359) B9887359
theorem B8788763 : Blo 2137435 8788763 := bstep (se 1 (by rfl) ⟨6591572, by rfl⟩ : syracuseStep 8788763 = 13183145) B13183145
theorem B5859175 : Blo 2137435 5859175 := bstep (se 1 (by rfl) ⟨4394381, by rfl⟩ : syracuseStep 5859175 = 8788763) B8788763
theorem B7812233 : Blo 2137435 7812233 := bstep (se 2 (by rfl) ⟨2929587, by rfl⟩ : syracuseStep 7812233 = 5859175) B5859175
theorem B5208155 : Blo 2137435 5208155 := bstep (se 1 (by rfl) ⟨3906116, by rfl⟩ : syracuseStep 5208155 = 7812233) B7812233
theorem B3472103 : Blo 2137435 3472103 := bstep (se 1 (by rfl) ⟨2604077, by rfl⟩ : syracuseStep 3472103 = 5208155) B5208155
theorem B9258941 : Blo 2137435 9258941 := bstep (se 3 (by rfl) ⟨1736051, by rfl⟩ : syracuseStep 9258941 = 3472103) B3472103
theorem B6172627 : Blo 2137435 6172627 := bstep (se 1 (by rfl) ⟨4629470, by rfl⟩ : syracuseStep 6172627 = 9258941) B9258941
theorem B8230169 : Blo 2137435 8230169 := bstep (se 2 (by rfl) ⟨3086313, by rfl⟩ : syracuseStep 8230169 = 6172627) B6172627
theorem B5486779 : Blo 2137435 5486779 := bstep (se 1 (by rfl) ⟨4115084, by rfl⟩ : syracuseStep 5486779 = 8230169) B8230169
theorem B7315705 : Blo 2137435 7315705 := bstep (se 2 (by rfl) ⟨2743389, by rfl⟩ : syracuseStep 7315705 = 5486779) B5486779
theorem B9754273 : Blo 2137435 9754273 := bstep (se 2 (by rfl) ⟨3657852, by rfl⟩ : syracuseStep 9754273 = 7315705) B7315705
theorem B13005697 : Blo 2137435 13005697 := bstep (se 2 (by rfl) ⟨4877136, by rfl⟩ : syracuseStep 13005697 = 9754273) B9754273
theorem B17340929 : Blo 2137435 17340929 := bstep (se 2 (by rfl) ⟨6502848, by rfl⟩ : syracuseStep 17340929 = 13005697) B13005697
theorem B11560619 : Blo 2137435 11560619 := bstep (se 1 (by rfl) ⟨8670464, by rfl⟩ : syracuseStep 11560619 = 17340929) B17340929
theorem B7707079 : Blo 2137435 7707079 := bstep (se 1 (by rfl) ⟨5780309, by rfl⟩ : syracuseStep 7707079 = 11560619) B11560619
theorem B10276105 : Blo 2137435 10276105 := bstep (se 2 (by rfl) ⟨3853539, by rfl⟩ : syracuseStep 10276105 = 7707079) B7707079
theorem B13701473 : Blo 2137435 13701473 := bstep (se 2 (by rfl) ⟨5138052, by rfl⟩ : syracuseStep 13701473 = 10276105) B10276105
theorem B9134315 : Blo 2137435 9134315 := bstep (se 1 (by rfl) ⟨6850736, by rfl⟩ : syracuseStep 9134315 = 13701473) B13701473
theorem B6089543 : Blo 2137435 6089543 := bstep (se 1 (by rfl) ⟨4567157, by rfl⟩ : syracuseStep 6089543 = 9134315) B9134315
theorem B4059695 : Blo 2137435 4059695 := bstep (se 1 (by rfl) ⟨3044771, by rfl⟩ : syracuseStep 4059695 = 6089543) B6089543
theorem B2706463 : Blo 2137435 2706463 := bstep (se 1 (by rfl) ⟨2029847, by rfl⟩ : syracuseStep 2706463 = 4059695) B4059695
theorem B3608617 : Blo 2137435 3608617 := bstep (se 2 (by rfl) ⟨1353231, by rfl⟩ : syracuseStep 3608617 = 2706463) B2706463
theorem B4811489 : Blo 2137435 4811489 := bstep (se 2 (by rfl) ⟨1804308, by rfl⟩ : syracuseStep 4811489 = 3608617) B3608617
theorem B3207659 : Blo 2137435 3207659 := bstep (se 1 (by rfl) ⟨2405744, by rfl⟩ : syracuseStep 3207659 = 4811489) B4811489
theorem B2138439 : Blo 2137435 2138439 := bstep (se 1 (by rfl) ⟨1603829, by rfl⟩ : syracuseStep 2138439 = 3207659) B3207659
theorem B2405749 : Blo 2137435 2405749 := bbase (se 5 (by rfl) ⟨112769, by rfl⟩ : syracuseStep 2405749 = 225539) (by norm_num)
theorem B3207665 : Blo 2137435 3207665 := bstep (se 2 (by rfl) ⟨1202874, by rfl⟩ : syracuseStep 3207665 = 2405749) B2405749
theorem B2138443 : Blo 2137435 2138443 := bstep (se 1 (by rfl) ⟨1603832, by rfl⟩ : syracuseStep 2138443 = 3207665) B3207665
theorem B2706473 : Blo 2137435 2706473 := bbase (se 2 (by rfl) ⟨1014927, by rfl⟩ : syracuseStep 2706473 = 2029855) (by norm_num)
theorem B7217261 : Blo 2137435 7217261 := bstep (se 3 (by rfl) ⟨1353236, by rfl⟩ : syracuseStep 7217261 = 2706473) B2706473
theorem B4811507 : Blo 2137435 4811507 := bstep (se 1 (by rfl) ⟨3608630, by rfl⟩ : syracuseStep 4811507 = 7217261) B7217261
theorem B3207671 : Blo 2137435 3207671 := bstep (se 1 (by rfl) ⟨2405753, by rfl⟩ : syracuseStep 3207671 = 4811507) B4811507
theorem B2138447 : Blo 2137435 2138447 := bstep (se 1 (by rfl) ⟨1603835, by rfl⟩ : syracuseStep 2138447 = 3207671) B3207671
theorem B3207677 : Blo 2137435 3207677 := bbase (se 3 (by rfl) ⟨601439, by rfl⟩ : syracuseStep 3207677 = 1202879) (by norm_num)
theorem B2138451 : Blo 2137435 2138451 := bstep (se 1 (by rfl) ⟨1603838, by rfl⟩ : syracuseStep 2138451 = 3207677) B3207677
theorem B4811525 : Blo 2137435 4811525 := bbase (se 4 (by rfl) ⟨451080, by rfl⟩ : syracuseStep 4811525 = 902161) (by norm_num)
theorem B3207683 : Blo 2137435 3207683 := bstep (se 1 (by rfl) ⟨2405762, by rfl⟩ : syracuseStep 3207683 = 4811525) B4811525
theorem B2138455 : Blo 2137435 2138455 := bstep (se 1 (by rfl) ⟨1603841, by rfl⟩ : syracuseStep 2138455 = 3207683) B3207683
theorem B4059733 : Blo 2137435 4059733 := bbase (se 8 (by rfl) ⟨23787, by rfl⟩ : syracuseStep 4059733 = 47575) (by norm_num)
theorem B5412977 : Blo 2137435 5412977 := bstep (se 2 (by rfl) ⟨2029866, by rfl⟩ : syracuseStep 5412977 = 4059733) B4059733
theorem B3608651 : Blo 2137435 3608651 := bstep (se 1 (by rfl) ⟨2706488, by rfl⟩ : syracuseStep 3608651 = 5412977) B5412977
theorem B2405767 : Blo 2137435 2405767 := bstep (se 1 (by rfl) ⟨1804325, by rfl⟩ : syracuseStep 2405767 = 3608651) B3608651
theorem B3207689 : Blo 2137435 3207689 := bstep (se 2 (by rfl) ⟨1202883, by rfl⟩ : syracuseStep 3207689 = 2405767) B2405767
theorem B2138459 : Blo 2137435 2138459 := bstep (se 1 (by rfl) ⟨1603844, by rfl⟩ : syracuseStep 2138459 = 3207689) B3207689
theorem B10825973 : Blo 2137435 10825973 := bbase (se 5 (by rfl) ⟨507467, by rfl⟩ : syracuseStep 10825973 = 1014935) (by norm_num)
theorem B7217315 : Blo 2137435 7217315 := bstep (se 1 (by rfl) ⟨5412986, by rfl⟩ : syracuseStep 7217315 = 10825973) B10825973
theorem B4811543 : Blo 2137435 4811543 := bstep (se 1 (by rfl) ⟨3608657, by rfl⟩ : syracuseStep 4811543 = 7217315) B7217315
theorem B3207695 : Blo 2137435 3207695 := bstep (se 1 (by rfl) ⟨2405771, by rfl⟩ : syracuseStep 3207695 = 4811543) B4811543
theorem B2138463 : Blo 2137435 2138463 := bstep (se 1 (by rfl) ⟨1603847, by rfl⟩ : syracuseStep 2138463 = 3207695) B3207695
theorem B3207701 : Blo 2137435 3207701 := bbase (se 6 (by rfl) ⟨75180, by rfl⟩ : syracuseStep 3207701 = 150361) (by norm_num)
theorem B2138467 : Blo 2137435 2138467 := bstep (se 1 (by rfl) ⟨1603850, by rfl⟩ : syracuseStep 2138467 = 3207701) B3207701
theorem B3853597 : Blo 2137435 3853597 := bbase (se 3 (by rfl) ⟨722549, by rfl⟩ : syracuseStep 3853597 = 1445099) (by norm_num)
theorem B5138129 : Blo 2137435 5138129 := bstep (se 2 (by rfl) ⟨1926798, by rfl⟩ : syracuseStep 5138129 = 3853597) B3853597
theorem B3425419 : Blo 2137435 3425419 := bstep (se 1 (by rfl) ⟨2569064, by rfl⟩ : syracuseStep 3425419 = 5138129) B5138129
theorem B18268901 : Blo 2137435 18268901 := bstep (se 4 (by rfl) ⟨1712709, by rfl⟩ : syracuseStep 18268901 = 3425419) B3425419
theorem B12179267 : Blo 2137435 12179267 := bstep (se 1 (by rfl) ⟨9134450, by rfl⟩ : syracuseStep 12179267 = 18268901) B18268901
theorem B8119511 : Blo 2137435 8119511 := bstep (se 1 (by rfl) ⟨6089633, by rfl⟩ : syracuseStep 8119511 = 12179267) B12179267
theorem B5413007 : Blo 2137435 5413007 := bstep (se 1 (by rfl) ⟨4059755, by rfl⟩ : syracuseStep 5413007 = 8119511) B8119511
theorem B3608671 : Blo 2137435 3608671 := bstep (se 1 (by rfl) ⟨2706503, by rfl⟩ : syracuseStep 3608671 = 5413007) B5413007
theorem B4811561 : Blo 2137435 4811561 := bstep (se 2 (by rfl) ⟨1804335, by rfl⟩ : syracuseStep 4811561 = 3608671) B3608671
theorem B3207707 : Blo 2137435 3207707 := bstep (se 1 (by rfl) ⟨2405780, by rfl⟩ : syracuseStep 3207707 = 4811561) B4811561
theorem B2138471 : Blo 2137435 2138471 := bstep (se 1 (by rfl) ⟨1603853, by rfl⟩ : syracuseStep 2138471 = 3207707) B3207707
theorem B2405785 : Blo 2137435 2405785 := bbase (se 2 (by rfl) ⟨902169, by rfl⟩ : syracuseStep 2405785 = 1804339) (by norm_num)
theorem B3207713 : Blo 2137435 3207713 := bstep (se 2 (by rfl) ⟨1202892, by rfl⟩ : syracuseStep 3207713 = 2405785) B2405785
theorem B2138475 : Blo 2137435 2138475 := bstep (se 1 (by rfl) ⟨1603856, by rfl⟩ : syracuseStep 2138475 = 3207713) B3207713
theorem B8119541 : Blo 2137435 8119541 := bbase (se 5 (by rfl) ⟨380603, by rfl⟩ : syracuseStep 8119541 = 761207) (by norm_num)
theorem B5413027 : Blo 2137435 5413027 := bstep (se 1 (by rfl) ⟨4059770, by rfl⟩ : syracuseStep 5413027 = 8119541) B8119541
theorem B7217369 : Blo 2137435 7217369 := bstep (se 2 (by rfl) ⟨2706513, by rfl⟩ : syracuseStep 7217369 = 5413027) B5413027
theorem B4811579 : Blo 2137435 4811579 := bstep (se 1 (by rfl) ⟨3608684, by rfl⟩ : syracuseStep 4811579 = 7217369) B7217369
theorem B3207719 : Blo 2137435 3207719 := bstep (se 1 (by rfl) ⟨2405789, by rfl⟩ : syracuseStep 3207719 = 4811579) B4811579
theorem B2138479 : Blo 2137435 2138479 := bstep (se 1 (by rfl) ⟨1603859, by rfl⟩ : syracuseStep 2138479 = 3207719) B3207719
theorem B3207725 : Blo 2137435 3207725 := bbase (se 3 (by rfl) ⟨601448, by rfl⟩ : syracuseStep 3207725 = 1202897) (by norm_num)
theorem B2138483 : Blo 2137435 2138483 := bstep (se 1 (by rfl) ⟨1603862, by rfl⟩ : syracuseStep 2138483 = 3207725) B3207725
theorem B4811597 : Blo 2137435 4811597 := bbase (se 3 (by rfl) ⟨902174, by rfl⟩ : syracuseStep 4811597 = 1804349) (by norm_num)
theorem B3207731 : Blo 2137435 3207731 := bstep (se 1 (by rfl) ⟨2405798, by rfl⟩ : syracuseStep 3207731 = 4811597) B4811597
theorem B2138487 : Blo 2137435 2138487 := bstep (se 1 (by rfl) ⟨1603865, by rfl⟩ : syracuseStep 2138487 = 3207731) B3207731
theorem B2706529 : Blo 2137435 2706529 := bbase (se 2 (by rfl) ⟨1014948, by rfl⟩ : syracuseStep 2706529 = 2029897) (by norm_num)
theorem B3608705 : Blo 2137435 3608705 := bstep (se 2 (by rfl) ⟨1353264, by rfl⟩ : syracuseStep 3608705 = 2706529) B2706529
theorem B2405803 : Blo 2137435 2405803 := bstep (se 1 (by rfl) ⟨1804352, by rfl⟩ : syracuseStep 2405803 = 3608705) B3608705
theorem B3207737 : Blo 2137435 3207737 := bstep (se 2 (by rfl) ⟨1202901, by rfl⟩ : syracuseStep 3207737 = 2405803) B2405803
theorem B2138491 : Blo 2137435 2138491 := bstep (se 1 (by rfl) ⟨1603868, by rfl⟩ : syracuseStep 2138491 = 3207737) B3207737
theorem B24358805 : Blo 2137435 24358805 := bbase (se 6 (by rfl) ⟨570909, by rfl⟩ : syracuseStep 24358805 = 1141819) (by norm_num)
theorem B16239203 : Blo 2137435 16239203 := bstep (se 1 (by rfl) ⟨12179402, by rfl⟩ : syracuseStep 16239203 = 24358805) B24358805
theorem B10826135 : Blo 2137435 10826135 := bstep (se 1 (by rfl) ⟨8119601, by rfl⟩ : syracuseStep 10826135 = 16239203) B16239203
theorem B7217423 : Blo 2137435 7217423 := bstep (se 1 (by rfl) ⟨5413067, by rfl⟩ : syracuseStep 7217423 = 10826135) B10826135
theorem B4811615 : Blo 2137435 4811615 := bstep (se 1 (by rfl) ⟨3608711, by rfl⟩ : syracuseStep 4811615 = 7217423) B7217423
theorem B3207743 : Blo 2137435 3207743 := bstep (se 1 (by rfl) ⟨2405807, by rfl⟩ : syracuseStep 3207743 = 4811615) B4811615
theorem B2138495 : Blo 2137435 2138495 := bstep (se 1 (by rfl) ⟨1603871, by rfl⟩ : syracuseStep 2138495 = 3207743) B3207743
theorem B3207749 : Blo 2137435 3207749 := bbase (se 4 (by rfl) ⟨300726, by rfl⟩ : syracuseStep 3207749 = 601453) (by norm_num)
theorem B2138499 : Blo 2137435 2138499 := bstep (se 1 (by rfl) ⟨1603874, by rfl⟩ : syracuseStep 2138499 = 3207749) B3207749
theorem B3608725 : Blo 2137435 3608725 := bbase (se 6 (by rfl) ⟨84579, by rfl⟩ : syracuseStep 3608725 = 169159) (by norm_num)
theorem B4811633 : Blo 2137435 4811633 := bstep (se 2 (by rfl) ⟨1804362, by rfl⟩ : syracuseStep 4811633 = 3608725) B3608725
theorem B3207755 : Blo 2137435 3207755 := bstep (se 1 (by rfl) ⟨2405816, by rfl⟩ : syracuseStep 3207755 = 4811633) B4811633
theorem B2138503 : Blo 2137435 2138503 := bstep (se 1 (by rfl) ⟨1603877, by rfl⟩ : syracuseStep 2138503 = 3207755) B3207755
theorem B2405821 : Blo 2137435 2405821 := bbase (se 3 (by rfl) ⟨451091, by rfl⟩ : syracuseStep 2405821 = 902183) (by norm_num)
theorem B3207761 : Blo 2137435 3207761 := bstep (se 2 (by rfl) ⟨1202910, by rfl⟩ : syracuseStep 3207761 = 2405821) B2405821
theorem B2138507 : Blo 2137435 2138507 := bstep (se 1 (by rfl) ⟨1603880, by rfl⟩ : syracuseStep 2138507 = 3207761) B3207761
theorem B7217477 : Blo 2137435 7217477 := bbase (se 4 (by rfl) ⟨676638, by rfl⟩ : syracuseStep 7217477 = 1353277) (by norm_num)
theorem B4811651 : Blo 2137435 4811651 := bstep (se 1 (by rfl) ⟨3608738, by rfl⟩ : syracuseStep 4811651 = 7217477) B7217477
theorem B3207767 : Blo 2137435 3207767 := bstep (se 1 (by rfl) ⟨2405825, by rfl⟩ : syracuseStep 3207767 = 4811651) B4811651
theorem B2138511 : Blo 2137435 2138511 := bstep (se 1 (by rfl) ⟨1603883, by rfl⟩ : syracuseStep 2138511 = 3207767) B3207767
theorem B3207773 : Blo 2137435 3207773 := bbase (se 3 (by rfl) ⟨601457, by rfl⟩ : syracuseStep 3207773 = 1202915) (by norm_num)
theorem B2138515 : Blo 2137435 2138515 := bstep (se 1 (by rfl) ⟨1603886, by rfl⟩ : syracuseStep 2138515 = 3207773) B3207773
theorem B4811669 : Blo 2137435 4811669 := bbase (se 6 (by rfl) ⟨112773, by rfl⟩ : syracuseStep 4811669 = 225547) (by norm_num)
theorem B3207779 : Blo 2137435 3207779 := bstep (se 1 (by rfl) ⟨2405834, by rfl⟩ : syracuseStep 3207779 = 4811669) B4811669
theorem B2138519 : Blo 2137435 2138519 := bstep (se 1 (by rfl) ⟨1603889, by rfl⟩ : syracuseStep 2138519 = 3207779) B3207779
theorem B3657997 : Blo 2137435 3657997 := bbase (se 3 (by rfl) ⟨685874, by rfl⟩ : syracuseStep 3657997 = 1371749) (by norm_num)
theorem B4877329 : Blo 2137435 4877329 := bstep (se 2 (by rfl) ⟨1828998, by rfl⟩ : syracuseStep 4877329 = 3657997) B3657997
theorem B6503105 : Blo 2137435 6503105 := bstep (se 2 (by rfl) ⟨2438664, by rfl⟩ : syracuseStep 6503105 = 4877329) B4877329
theorem B17341613 : Blo 2137435 17341613 := bstep (se 3 (by rfl) ⟨3251552, by rfl⟩ : syracuseStep 17341613 = 6503105) B6503105
theorem B11561075 : Blo 2137435 11561075 := bstep (se 1 (by rfl) ⟨8670806, by rfl⟩ : syracuseStep 11561075 = 17341613) B17341613
theorem B7707383 : Blo 2137435 7707383 := bstep (se 1 (by rfl) ⟨5780537, by rfl⟩ : syracuseStep 7707383 = 11561075) B11561075
theorem B5138255 : Blo 2137435 5138255 := bstep (se 1 (by rfl) ⟨3853691, by rfl⟩ : syracuseStep 5138255 = 7707383) B7707383
theorem B3425503 : Blo 2137435 3425503 := bstep (se 1 (by rfl) ⟨2569127, by rfl⟩ : syracuseStep 3425503 = 5138255) B5138255
theorem B4567337 : Blo 2137435 4567337 := bstep (se 2 (by rfl) ⟨1712751, by rfl⟩ : syracuseStep 4567337 = 3425503) B3425503
theorem B3044891 : Blo 2137435 3044891 := bstep (se 1 (by rfl) ⟨2283668, by rfl⟩ : syracuseStep 3044891 = 4567337) B4567337
theorem B8119709 : Blo 2137435 8119709 := bstep (se 3 (by rfl) ⟨1522445, by rfl⟩ : syracuseStep 8119709 = 3044891) B3044891
theorem B5413139 : Blo 2137435 5413139 := bstep (se 1 (by rfl) ⟨4059854, by rfl⟩ : syracuseStep 5413139 = 8119709) B8119709
theorem B3608759 : Blo 2137435 3608759 := bstep (se 1 (by rfl) ⟨2706569, by rfl⟩ : syracuseStep 3608759 = 5413139) B5413139
theorem B2405839 : Blo 2137435 2405839 := bstep (se 1 (by rfl) ⟨1804379, by rfl⟩ : syracuseStep 2405839 = 3608759) B3608759
theorem B3207785 : Blo 2137435 3207785 := bstep (se 2 (by rfl) ⟨1202919, by rfl⟩ : syracuseStep 3207785 = 2405839) B2405839
theorem B2138523 : Blo 2137435 2138523 := bstep (se 1 (by rfl) ⟨1603892, by rfl⟩ : syracuseStep 2138523 = 3207785) B3207785
theorem B2167705 : Blo 2137435 2167705 := bbase (se 2 (by rfl) ⟨812889, by rfl⟩ : syracuseStep 2167705 = 1625779) (by norm_num)
theorem B11561093 : Blo 2137435 11561093 := bstep (se 4 (by rfl) ⟨1083852, by rfl⟩ : syracuseStep 11561093 = 2167705) B2167705
theorem B7707395 : Blo 2137435 7707395 := bstep (se 1 (by rfl) ⟨5780546, by rfl⟩ : syracuseStep 7707395 = 11561093) B11561093
theorem B5138263 : Blo 2137435 5138263 := bstep (se 1 (by rfl) ⟨3853697, by rfl⟩ : syracuseStep 5138263 = 7707395) B7707395
theorem B6851017 : Blo 2137435 6851017 := bstep (se 2 (by rfl) ⟨2569131, by rfl⟩ : syracuseStep 6851017 = 5138263) B5138263
theorem B9134689 : Blo 2137435 9134689 := bstep (se 2 (by rfl) ⟨3425508, by rfl⟩ : syracuseStep 9134689 = 6851017) B6851017
theorem B12179585 : Blo 2137435 12179585 := bstep (se 2 (by rfl) ⟨4567344, by rfl⟩ : syracuseStep 12179585 = 9134689) B9134689
theorem B8119723 : Blo 2137435 8119723 := bstep (se 1 (by rfl) ⟨6089792, by rfl⟩ : syracuseStep 8119723 = 12179585) B12179585
theorem B10826297 : Blo 2137435 10826297 := bstep (se 2 (by rfl) ⟨4059861, by rfl⟩ : syracuseStep 10826297 = 8119723) B8119723
theorem B7217531 : Blo 2137435 7217531 := bstep (se 1 (by rfl) ⟨5413148, by rfl⟩ : syracuseStep 7217531 = 10826297) B10826297
theorem B4811687 : Blo 2137435 4811687 := bstep (se 1 (by rfl) ⟨3608765, by rfl⟩ : syracuseStep 4811687 = 7217531) B7217531
theorem B3207791 : Blo 2137435 3207791 := bstep (se 1 (by rfl) ⟨2405843, by rfl⟩ : syracuseStep 3207791 = 4811687) B4811687
theorem B2138527 : Blo 2137435 2138527 := bstep (se 1 (by rfl) ⟨1603895, by rfl⟩ : syracuseStep 2138527 = 3207791) B3207791
theorem B3207797 : Blo 2137435 3207797 := bbase (se 5 (by rfl) ⟨150365, by rfl⟩ : syracuseStep 3207797 = 300731) (by norm_num)
theorem B2138531 : Blo 2137435 2138531 := bstep (se 1 (by rfl) ⟨1603898, by rfl⟩ : syracuseStep 2138531 = 3207797) B3207797
theorem B4059877 : Blo 2137435 4059877 := bbase (se 4 (by rfl) ⟨380613, by rfl⟩ : syracuseStep 4059877 = 761227) (by norm_num)
theorem B5413169 : Blo 2137435 5413169 := bstep (se 2 (by rfl) ⟨2029938, by rfl⟩ : syracuseStep 5413169 = 4059877) B4059877
theorem B3608779 : Blo 2137435 3608779 := bstep (se 1 (by rfl) ⟨2706584, by rfl⟩ : syracuseStep 3608779 = 5413169) B5413169
theorem B4811705 : Blo 2137435 4811705 := bstep (se 2 (by rfl) ⟨1804389, by rfl⟩ : syracuseStep 4811705 = 3608779) B3608779
theorem B3207803 : Blo 2137435 3207803 := bstep (se 1 (by rfl) ⟨2405852, by rfl⟩ : syracuseStep 3207803 = 4811705) B4811705
theorem B2138535 : Blo 2137435 2138535 := bstep (se 1 (by rfl) ⟨1603901, by rfl⟩ : syracuseStep 2138535 = 3207803) B3207803
theorem B2405857 : Blo 2137435 2405857 := bbase (se 2 (by rfl) ⟨902196, by rfl⟩ : syracuseStep 2405857 = 1804393) (by norm_num)
theorem B3207809 : Blo 2137435 3207809 := bstep (se 2 (by rfl) ⟨1202928, by rfl⟩ : syracuseStep 3207809 = 2405857) B2405857
theorem B2138539 : Blo 2137435 2138539 := bstep (se 1 (by rfl) ⟨1603904, by rfl⟩ : syracuseStep 2138539 = 3207809) B3207809
theorem B5413189 : Blo 2137435 5413189 := bbase (se 4 (by rfl) ⟨507486, by rfl⟩ : syracuseStep 5413189 = 1014973) (by norm_num)
theorem B7217585 : Blo 2137435 7217585 := bstep (se 2 (by rfl) ⟨2706594, by rfl⟩ : syracuseStep 7217585 = 5413189) B5413189
theorem B4811723 : Blo 2137435 4811723 := bstep (se 1 (by rfl) ⟨3608792, by rfl⟩ : syracuseStep 4811723 = 7217585) B7217585
theorem B3207815 : Blo 2137435 3207815 := bstep (se 1 (by rfl) ⟨2405861, by rfl⟩ : syracuseStep 3207815 = 4811723) B4811723
theorem B2138543 : Blo 2137435 2138543 := bstep (se 1 (by rfl) ⟨1603907, by rfl⟩ : syracuseStep 2138543 = 3207815) B3207815
theorem B3207821 : Blo 2137435 3207821 := bbase (se 3 (by rfl) ⟨601466, by rfl⟩ : syracuseStep 3207821 = 1202933) (by norm_num)
theorem B2138547 : Blo 2137435 2138547 := bstep (se 1 (by rfl) ⟨1603910, by rfl⟩ : syracuseStep 2138547 = 3207821) B3207821
theorem B4811741 : Blo 2137435 4811741 := bbase (se 3 (by rfl) ⟨902201, by rfl⟩ : syracuseStep 4811741 = 1804403) (by norm_num)
theorem B3207827 : Blo 2137435 3207827 := bstep (se 1 (by rfl) ⟨2405870, by rfl⟩ : syracuseStep 3207827 = 4811741) B4811741
theorem B2138551 : Blo 2137435 2138551 := bstep (se 1 (by rfl) ⟨1603913, by rfl⟩ : syracuseStep 2138551 = 3207827) B3207827
theorem B3608813 : Blo 2137435 3608813 := bbase (se 3 (by rfl) ⟨676652, by rfl⟩ : syracuseStep 3608813 = 1353305) (by norm_num)
theorem B2405875 : Blo 2137435 2405875 := bstep (se 1 (by rfl) ⟨1804406, by rfl⟩ : syracuseStep 2405875 = 3608813) B3608813
theorem B3207833 : Blo 2137435 3207833 := bstep (se 2 (by rfl) ⟨1202937, by rfl⟩ : syracuseStep 3207833 = 2405875) B2405875
theorem B2138555 : Blo 2137435 2138555 := bstep (se 1 (by rfl) ⟨1603916, by rfl⟩ : syracuseStep 2138555 = 3207833) B3207833
theorem B5487085 : Blo 2137435 5487085 := bbase (se 3 (by rfl) ⟨1028828, by rfl⟩ : syracuseStep 5487085 = 2057657) (by norm_num)
theorem B29264453 : Blo 2137435 29264453 := bstep (se 4 (by rfl) ⟨2743542, by rfl⟩ : syracuseStep 29264453 = 5487085) B5487085
theorem B19509635 : Blo 2137435 19509635 := bstep (se 1 (by rfl) ⟨14632226, by rfl⟩ : syracuseStep 19509635 = 29264453) B29264453
theorem B13006423 : Blo 2137435 13006423 := bstep (se 1 (by rfl) ⟨9754817, by rfl⟩ : syracuseStep 13006423 = 19509635) B19509635
theorem B17341897 : Blo 2137435 17341897 := bstep (se 2 (by rfl) ⟨6503211, by rfl⟩ : syracuseStep 17341897 = 13006423) B13006423
theorem B23122529 : Blo 2137435 23122529 := bstep (se 2 (by rfl) ⟨8670948, by rfl⟩ : syracuseStep 23122529 = 17341897) B17341897
theorem B15415019 : Blo 2137435 15415019 := bstep (se 1 (by rfl) ⟨11561264, by rfl⟩ : syracuseStep 15415019 = 23122529) B23122529
theorem B10276679 : Blo 2137435 10276679 := bstep (se 1 (by rfl) ⟨7707509, by rfl⟩ : syracuseStep 10276679 = 15415019) B15415019
theorem B27404477 : Blo 2137435 27404477 := bstep (se 3 (by rfl) ⟨5138339, by rfl⟩ : syracuseStep 27404477 = 10276679) B10276679
theorem B18269651 : Blo 2137435 18269651 := bstep (se 1 (by rfl) ⟨13702238, by rfl⟩ : syracuseStep 18269651 = 27404477) B27404477
theorem B12179767 : Blo 2137435 12179767 := bstep (se 1 (by rfl) ⟨9134825, by rfl⟩ : syracuseStep 12179767 = 18269651) B18269651
theorem B16239689 : Blo 2137435 16239689 := bstep (se 2 (by rfl) ⟨6089883, by rfl⟩ : syracuseStep 16239689 = 12179767) B12179767
theorem B10826459 : Blo 2137435 10826459 := bstep (se 1 (by rfl) ⟨8119844, by rfl⟩ : syracuseStep 10826459 = 16239689) B16239689
theorem B7217639 : Blo 2137435 7217639 := bstep (se 1 (by rfl) ⟨5413229, by rfl⟩ : syracuseStep 7217639 = 10826459) B10826459
theorem B4811759 : Blo 2137435 4811759 := bstep (se 1 (by rfl) ⟨3608819, by rfl⟩ : syracuseStep 4811759 = 7217639) B7217639
theorem B3207839 : Blo 2137435 3207839 := bstep (se 1 (by rfl) ⟨2405879, by rfl⟩ : syracuseStep 3207839 = 4811759) B4811759
theorem B2138559 : Blo 2137435 2138559 := bstep (se 1 (by rfl) ⟨1603919, by rfl⟩ : syracuseStep 2138559 = 3207839) B3207839
theorem B3207845 : Blo 2137435 3207845 := bbase (se 4 (by rfl) ⟨300735, by rfl⟩ : syracuseStep 3207845 = 601471) (by norm_num)
theorem B2138563 : Blo 2137435 2138563 := bstep (se 1 (by rfl) ⟨1603922, by rfl⟩ : syracuseStep 2138563 = 3207845) B3207845
theorem B2706625 : Blo 2137435 2706625 := bbase (se 2 (by rfl) ⟨1014984, by rfl⟩ : syracuseStep 2706625 = 2029969) (by norm_num)
theorem B3608833 : Blo 2137435 3608833 := bstep (se 2 (by rfl) ⟨1353312, by rfl⟩ : syracuseStep 3608833 = 2706625) B2706625
theorem B4811777 : Blo 2137435 4811777 := bstep (se 2 (by rfl) ⟨1804416, by rfl⟩ : syracuseStep 4811777 = 3608833) B3608833
theorem B3207851 : Blo 2137435 3207851 := bstep (se 1 (by rfl) ⟨2405888, by rfl⟩ : syracuseStep 3207851 = 4811777) B4811777
theorem B2138567 : Blo 2137435 2138567 := bstep (se 1 (by rfl) ⟨1603925, by rfl⟩ : syracuseStep 2138567 = 3207851) B3207851
theorem B2405893 : Blo 2137435 2405893 := bbase (se 4 (by rfl) ⟨225552, by rfl⟩ : syracuseStep 2405893 = 451105) (by norm_num)
theorem B3207857 : Blo 2137435 3207857 := bstep (se 2 (by rfl) ⟨1202946, by rfl⟩ : syracuseStep 3207857 = 2405893) B2405893
theorem B2138571 : Blo 2137435 2138571 := bstep (se 1 (by rfl) ⟨1603928, by rfl⟩ : syracuseStep 2138571 = 3207857) B3207857
theorem B3044965 : Blo 2137435 3044965 := bbase (se 4 (by rfl) ⟨285465, by rfl⟩ : syracuseStep 3044965 = 570931) (by norm_num)
theorem B4059953 : Blo 2137435 4059953 := bstep (se 2 (by rfl) ⟨1522482, by rfl⟩ : syracuseStep 4059953 = 3044965) B3044965
theorem B2706635 : Blo 2137435 2706635 := bstep (se 1 (by rfl) ⟨2029976, by rfl⟩ : syracuseStep 2706635 = 4059953) B4059953
theorem B7217693 : Blo 2137435 7217693 := bstep (se 3 (by rfl) ⟨1353317, by rfl⟩ : syracuseStep 7217693 = 2706635) B2706635
theorem B4811795 : Blo 2137435 4811795 := bstep (se 1 (by rfl) ⟨3608846, by rfl⟩ : syracuseStep 4811795 = 7217693) B7217693
theorem B3207863 : Blo 2137435 3207863 := bstep (se 1 (by rfl) ⟨2405897, by rfl⟩ : syracuseStep 3207863 = 4811795) B4811795
theorem B2138575 : Blo 2137435 2138575 := bstep (se 1 (by rfl) ⟨1603931, by rfl⟩ : syracuseStep 2138575 = 3207863) B3207863
theorem B3207869 : Blo 2137435 3207869 := bbase (se 3 (by rfl) ⟨601475, by rfl⟩ : syracuseStep 3207869 = 1202951) (by norm_num)
theorem B2138579 : Blo 2137435 2138579 := bstep (se 1 (by rfl) ⟨1603934, by rfl⟩ : syracuseStep 2138579 = 3207869) B3207869
theorem B4811813 : Blo 2137435 4811813 := bbase (se 4 (by rfl) ⟨451107, by rfl⟩ : syracuseStep 4811813 = 902215) (by norm_num)
theorem B3207875 : Blo 2137435 3207875 := bstep (se 1 (by rfl) ⟨2405906, by rfl⟩ : syracuseStep 3207875 = 4811813) B4811813
theorem B2138583 : Blo 2137435 2138583 := bstep (se 1 (by rfl) ⟨1603937, by rfl⟩ : syracuseStep 2138583 = 3207875) B3207875
theorem B5413301 : Blo 2137435 5413301 := bbase (se 5 (by rfl) ⟨253748, by rfl⟩ : syracuseStep 5413301 = 507497) (by norm_num)
theorem B3608867 : Blo 2137435 3608867 := bstep (se 1 (by rfl) ⟨2706650, by rfl⟩ : syracuseStep 3608867 = 5413301) B5413301
theorem B2405911 : Blo 2137435 2405911 := bstep (se 1 (by rfl) ⟨1804433, by rfl⟩ : syracuseStep 2405911 = 3608867) B3608867
theorem B3207881 : Blo 2137435 3207881 := bstep (se 2 (by rfl) ⟨1202955, by rfl⟩ : syracuseStep 3207881 = 2405911) B2405911
theorem B2138587 : Blo 2137435 2138587 := bstep (se 1 (by rfl) ⟨1603940, by rfl⟩ : syracuseStep 2138587 = 3207881) B3207881
theorem B3853813 : Blo 2137435 3853813 := bbase (se 5 (by rfl) ⟨180647, by rfl⟩ : syracuseStep 3853813 = 361295) (by norm_num)
theorem B5138417 : Blo 2137435 5138417 := bstep (se 2 (by rfl) ⟨1926906, by rfl⟩ : syracuseStep 5138417 = 3853813) B3853813
theorem B13702445 : Blo 2137435 13702445 := bstep (se 3 (by rfl) ⟨2569208, by rfl⟩ : syracuseStep 13702445 = 5138417) B5138417
theorem B9134963 : Blo 2137435 9134963 := bstep (se 1 (by rfl) ⟨6851222, by rfl⟩ : syracuseStep 9134963 = 13702445) B13702445
theorem B6089975 : Blo 2137435 6089975 := bstep (se 1 (by rfl) ⟨4567481, by rfl⟩ : syracuseStep 6089975 = 9134963) B9134963
theorem B4059983 : Blo 2137435 4059983 := bstep (se 1 (by rfl) ⟨3044987, by rfl⟩ : syracuseStep 4059983 = 6089975) B6089975
theorem B10826621 : Blo 2137435 10826621 := bstep (se 3 (by rfl) ⟨2029991, by rfl⟩ : syracuseStep 10826621 = 4059983) B4059983
theorem B7217747 : Blo 2137435 7217747 := bstep (se 1 (by rfl) ⟨5413310, by rfl⟩ : syracuseStep 7217747 = 10826621) B10826621
theorem B4811831 : Blo 2137435 4811831 := bstep (se 1 (by rfl) ⟨3608873, by rfl⟩ : syracuseStep 4811831 = 7217747) B7217747
theorem B3207887 : Blo 2137435 3207887 := bstep (se 1 (by rfl) ⟨2405915, by rfl⟩ : syracuseStep 3207887 = 4811831) B4811831
theorem B2138591 : Blo 2137435 2138591 := bstep (se 1 (by rfl) ⟨1603943, by rfl⟩ : syracuseStep 2138591 = 3207887) B3207887
theorem B3207893 : Blo 2137435 3207893 := bbase (se 7 (by rfl) ⟨37592, by rfl⟩ : syracuseStep 3207893 = 75185) (by norm_num)
theorem B2138595 : Blo 2137435 2138595 := bstep (se 1 (by rfl) ⟨1603946, by rfl⟩ : syracuseStep 2138595 = 3207893) B3207893
theorem B5138437 : Blo 2137435 5138437 := bbase (se 4 (by rfl) ⟨481728, by rfl⟩ : syracuseStep 5138437 = 963457) (by norm_num)
theorem B6851249 : Blo 2137435 6851249 := bstep (se 2 (by rfl) ⟨2569218, by rfl⟩ : syracuseStep 6851249 = 5138437) B5138437
theorem B4567499 : Blo 2137435 4567499 := bstep (se 1 (by rfl) ⟨3425624, by rfl⟩ : syracuseStep 4567499 = 6851249) B6851249
theorem B3044999 : Blo 2137435 3044999 := bstep (se 1 (by rfl) ⟨2283749, by rfl⟩ : syracuseStep 3044999 = 4567499) B4567499
theorem B8119997 : Blo 2137435 8119997 := bstep (se 3 (by rfl) ⟨1522499, by rfl⟩ : syracuseStep 8119997 = 3044999) B3044999
theorem B5413331 : Blo 2137435 5413331 := bstep (se 1 (by rfl) ⟨4059998, by rfl⟩ : syracuseStep 5413331 = 8119997) B8119997
theorem B3608887 : Blo 2137435 3608887 := bstep (se 1 (by rfl) ⟨2706665, by rfl⟩ : syracuseStep 3608887 = 5413331) B5413331
theorem B4811849 : Blo 2137435 4811849 := bstep (se 2 (by rfl) ⟨1804443, by rfl⟩ : syracuseStep 4811849 = 3608887) B3608887
theorem B3207899 : Blo 2137435 3207899 := bstep (se 1 (by rfl) ⟨2405924, by rfl⟩ : syracuseStep 3207899 = 4811849) B4811849
theorem B2138599 : Blo 2137435 2138599 := bstep (se 1 (by rfl) ⟨1603949, by rfl⟩ : syracuseStep 2138599 = 3207899) B3207899
theorem B2405929 : Blo 2137435 2405929 := bbase (se 2 (by rfl) ⟨902223, by rfl⟩ : syracuseStep 2405929 = 1804447) (by norm_num)
theorem B3207905 : Blo 2137435 3207905 := bstep (se 2 (by rfl) ⟨1202964, by rfl⟩ : syracuseStep 3207905 = 2405929) B2405929
theorem B2138603 : Blo 2137435 2138603 := bstep (se 1 (by rfl) ⟨1603952, by rfl⟩ : syracuseStep 2138603 = 3207905) B3207905
theorem B11561525 : Blo 2137435 11561525 := bbase (se 5 (by rfl) ⟨541946, by rfl⟩ : syracuseStep 11561525 = 1083893) (by norm_num)
theorem B7707683 : Blo 2137435 7707683 := bstep (se 1 (by rfl) ⟨5780762, by rfl⟩ : syracuseStep 7707683 = 11561525) B11561525
theorem B20553821 : Blo 2137435 20553821 := bstep (se 3 (by rfl) ⟨3853841, by rfl⟩ : syracuseStep 20553821 = 7707683) B7707683
theorem B13702547 : Blo 2137435 13702547 := bstep (se 1 (by rfl) ⟨10276910, by rfl⟩ : syracuseStep 13702547 = 20553821) B20553821
theorem B9135031 : Blo 2137435 9135031 := bstep (se 1 (by rfl) ⟨6851273, by rfl⟩ : syracuseStep 9135031 = 13702547) B13702547
theorem B12180041 : Blo 2137435 12180041 := bstep (se 2 (by rfl) ⟨4567515, by rfl⟩ : syracuseStep 12180041 = 9135031) B9135031
theorem B8120027 : Blo 2137435 8120027 := bstep (se 1 (by rfl) ⟨6090020, by rfl⟩ : syracuseStep 8120027 = 12180041) B12180041
theorem B5413351 : Blo 2137435 5413351 := bstep (se 1 (by rfl) ⟨4060013, by rfl⟩ : syracuseStep 5413351 = 8120027) B8120027
theorem B7217801 : Blo 2137435 7217801 := bstep (se 2 (by rfl) ⟨2706675, by rfl⟩ : syracuseStep 7217801 = 5413351) B5413351
theorem B4811867 : Blo 2137435 4811867 := bstep (se 1 (by rfl) ⟨3608900, by rfl⟩ : syracuseStep 4811867 = 7217801) B7217801
theorem B3207911 : Blo 2137435 3207911 := bstep (se 1 (by rfl) ⟨2405933, by rfl⟩ : syracuseStep 3207911 = 4811867) B4811867
theorem B2138607 : Blo 2137435 2138607 := bstep (se 1 (by rfl) ⟨1603955, by rfl⟩ : syracuseStep 2138607 = 3207911) B3207911
theorem B3207917 : Blo 2137435 3207917 := bbase (se 3 (by rfl) ⟨601484, by rfl⟩ : syracuseStep 3207917 = 1202969) (by norm_num)
theorem B2138611 : Blo 2137435 2138611 := bstep (se 1 (by rfl) ⟨1603958, by rfl⟩ : syracuseStep 2138611 = 3207917) B3207917
theorem B4811885 : Blo 2137435 4811885 := bbase (se 3 (by rfl) ⟨902228, by rfl⟩ : syracuseStep 4811885 = 1804457) (by norm_num)
theorem B3207923 : Blo 2137435 3207923 := bstep (se 1 (by rfl) ⟨2405942, by rfl⟩ : syracuseStep 3207923 = 4811885) B4811885
theorem B2138615 : Blo 2137435 2138615 := bstep (se 1 (by rfl) ⟨1603961, by rfl⟩ : syracuseStep 2138615 = 3207923) B3207923
theorem B4060037 : Blo 2137435 4060037 := bbase (se 4 (by rfl) ⟨380628, by rfl⟩ : syracuseStep 4060037 = 761257) (by norm_num)
theorem B2706691 : Blo 2137435 2706691 := bstep (se 1 (by rfl) ⟨2030018, by rfl⟩ : syracuseStep 2706691 = 4060037) B4060037
theorem B3608921 : Blo 2137435 3608921 := bstep (se 2 (by rfl) ⟨1353345, by rfl⟩ : syracuseStep 3608921 = 2706691) B2706691
theorem B2405947 : Blo 2137435 2405947 := bstep (se 1 (by rfl) ⟨1804460, by rfl⟩ : syracuseStep 2405947 = 3608921) B3608921
theorem B3207929 : Blo 2137435 3207929 := bstep (se 2 (by rfl) ⟨1202973, by rfl⟩ : syracuseStep 3207929 = 2405947) B2405947
theorem B2138619 : Blo 2137435 2138619 := bstep (se 1 (by rfl) ⟨1603964, by rfl⟩ : syracuseStep 2138619 = 3207929) B3207929
theorem B9259733 : Blo 2137435 9259733 := bbase (se 7 (by rfl) ⟨108512, by rfl⟩ : syracuseStep 9259733 = 217025) (by norm_num)
theorem B6173155 : Blo 2137435 6173155 := bstep (se 1 (by rfl) ⟨4629866, by rfl⟩ : syracuseStep 6173155 = 9259733) B9259733
theorem B8230873 : Blo 2137435 8230873 := bstep (se 2 (by rfl) ⟨3086577, by rfl⟩ : syracuseStep 8230873 = 6173155) B6173155
theorem B10974497 : Blo 2137435 10974497 := bstep (se 2 (by rfl) ⟨4115436, by rfl⟩ : syracuseStep 10974497 = 8230873) B8230873
theorem B117061301 : Blo 2137435 117061301 := bstep (se 5 (by rfl) ⟨5487248, by rfl⟩ : syracuseStep 117061301 = 10974497) B10974497
theorem B78040867 : Blo 2137435 78040867 := bstep (se 1 (by rfl) ⟨58530650, by rfl⟩ : syracuseStep 78040867 = 117061301) B117061301
theorem B104054489 : Blo 2137435 104054489 := bstep (se 2 (by rfl) ⟨39020433, by rfl⟩ : syracuseStep 104054489 = 78040867) B78040867
theorem B69369659 : Blo 2137435 69369659 := bstep (se 1 (by rfl) ⟨52027244, by rfl⟩ : syracuseStep 69369659 = 104054489) B104054489
theorem B46246439 : Blo 2137435 46246439 := bstep (se 1 (by rfl) ⟨34684829, by rfl⟩ : syracuseStep 46246439 = 69369659) B69369659
theorem B30830959 : Blo 2137435 30830959 := bstep (se 1 (by rfl) ⟨23123219, by rfl⟩ : syracuseStep 30830959 = 46246439) B46246439
theorem B41107945 : Blo 2137435 41107945 := bstep (se 2 (by rfl) ⟨15415479, by rfl⟩ : syracuseStep 41107945 = 30830959) B30830959
theorem B54810593 : Blo 2137435 54810593 := bstep (se 2 (by rfl) ⟨20553972, by rfl⟩ : syracuseStep 54810593 = 41107945) B41107945
theorem B36540395 : Blo 2137435 36540395 := bstep (se 1 (by rfl) ⟨27405296, by rfl⟩ : syracuseStep 36540395 = 54810593) B54810593
theorem B24360263 : Blo 2137435 24360263 := bstep (se 1 (by rfl) ⟨18270197, by rfl⟩ : syracuseStep 24360263 = 36540395) B36540395
theorem B16240175 : Blo 2137435 16240175 := bstep (se 1 (by rfl) ⟨12180131, by rfl⟩ : syracuseStep 16240175 = 24360263) B24360263
theorem B10826783 : Blo 2137435 10826783 := bstep (se 1 (by rfl) ⟨8120087, by rfl⟩ : syracuseStep 10826783 = 16240175) B16240175
theorem B7217855 : Blo 2137435 7217855 := bstep (se 1 (by rfl) ⟨5413391, by rfl⟩ : syracuseStep 7217855 = 10826783) B10826783
theorem B4811903 : Blo 2137435 4811903 := bstep (se 1 (by rfl) ⟨3608927, by rfl⟩ : syracuseStep 4811903 = 7217855) B7217855
theorem B3207935 : Blo 2137435 3207935 := bstep (se 1 (by rfl) ⟨2405951, by rfl⟩ : syracuseStep 3207935 = 4811903) B4811903
theorem B2138623 : Blo 2137435 2138623 := bstep (se 1 (by rfl) ⟨1603967, by rfl⟩ : syracuseStep 2138623 = 3207935) B3207935
theorem B3207941 : Blo 2137435 3207941 := bbase (se 4 (by rfl) ⟨300744, by rfl⟩ : syracuseStep 3207941 = 601489) (by norm_num)
theorem B2138627 : Blo 2137435 2138627 := bstep (se 1 (by rfl) ⟨1603970, by rfl⟩ : syracuseStep 2138627 = 3207941) B3207941
theorem B3608941 : Blo 2137435 3608941 := bbase (se 3 (by rfl) ⟨676676, by rfl⟩ : syracuseStep 3608941 = 1353353) (by norm_num)
theorem B4811921 : Blo 2137435 4811921 := bstep (se 2 (by rfl) ⟨1804470, by rfl⟩ : syracuseStep 4811921 = 3608941) B3608941
theorem B3207947 : Blo 2137435 3207947 := bstep (se 1 (by rfl) ⟨2405960, by rfl⟩ : syracuseStep 3207947 = 4811921) B4811921
theorem B2138631 : Blo 2137435 2138631 := bstep (se 1 (by rfl) ⟨1603973, by rfl⟩ : syracuseStep 2138631 = 3207947) B3207947
theorem B2405965 : Blo 2137435 2405965 := bbase (se 3 (by rfl) ⟨451118, by rfl⟩ : syracuseStep 2405965 = 902237) (by norm_num)
theorem B3207953 : Blo 2137435 3207953 := bstep (se 2 (by rfl) ⟨1202982, by rfl⟩ : syracuseStep 3207953 = 2405965) B2405965
theorem B2138635 : Blo 2137435 2138635 := bstep (se 1 (by rfl) ⟨1603976, by rfl⟩ : syracuseStep 2138635 = 3207953) B3207953
theorem B7217909 : Blo 2137435 7217909 := bbase (se 5 (by rfl) ⟨338339, by rfl⟩ : syracuseStep 7217909 = 676679) (by norm_num)
theorem B4811939 : Blo 2137435 4811939 := bstep (se 1 (by rfl) ⟨3608954, by rfl⟩ : syracuseStep 4811939 = 7217909) B7217909
theorem B3207959 : Blo 2137435 3207959 := bstep (se 1 (by rfl) ⟨2405969, by rfl⟩ : syracuseStep 3207959 = 4811939) B4811939
theorem B2138639 : Blo 2137435 2138639 := bstep (se 1 (by rfl) ⟨1603979, by rfl⟩ : syracuseStep 2138639 = 3207959) B3207959
theorem B3207965 : Blo 2137435 3207965 := bbase (se 3 (by rfl) ⟨601493, by rfl⟩ : syracuseStep 3207965 = 1202987) (by norm_num)
theorem B2138643 : Blo 2137435 2138643 := bstep (se 1 (by rfl) ⟨1603982, by rfl⟩ : syracuseStep 2138643 = 3207965) B3207965
theorem B4811957 : Blo 2137435 4811957 := bbase (se 5 (by rfl) ⟨225560, by rfl⟩ : syracuseStep 4811957 = 451121) (by norm_num)
theorem B3207971 : Blo 2137435 3207971 := bstep (se 1 (by rfl) ⟨2405978, by rfl⟩ : syracuseStep 3207971 = 4811957) B4811957
theorem B2138647 : Blo 2137435 2138647 := bstep (se 1 (by rfl) ⟨1603985, by rfl⟩ : syracuseStep 2138647 = 3207971) B3207971
theorem B2283805 : Blo 2137435 2283805 := bbase (se 3 (by rfl) ⟨428213, by rfl⟩ : syracuseStep 2283805 = 856427) (by norm_num)
theorem B12180293 : Blo 2137435 12180293 := bstep (se 4 (by rfl) ⟨1141902, by rfl⟩ : syracuseStep 12180293 = 2283805) B2283805
theorem B8120195 : Blo 2137435 8120195 := bstep (se 1 (by rfl) ⟨6090146, by rfl⟩ : syracuseStep 8120195 = 12180293) B12180293
theorem B5413463 : Blo 2137435 5413463 := bstep (se 1 (by rfl) ⟨4060097, by rfl⟩ : syracuseStep 5413463 = 8120195) B8120195
theorem B3608975 : Blo 2137435 3608975 := bstep (se 1 (by rfl) ⟨2706731, by rfl⟩ : syracuseStep 3608975 = 5413463) B5413463
theorem B2405983 : Blo 2137435 2405983 := bstep (se 1 (by rfl) ⟨1804487, by rfl⟩ : syracuseStep 2405983 = 3608975) B3608975
theorem B3207977 : Blo 2137435 3207977 := bstep (se 2 (by rfl) ⟨1202991, by rfl⟩ : syracuseStep 3207977 = 2405983) B2405983
theorem B2138651 : Blo 2137435 2138651 := bstep (se 1 (by rfl) ⟨1603988, by rfl⟩ : syracuseStep 2138651 = 3207977) B3207977
theorem B2283809 : Blo 2137435 2283809 := bbase (se 2 (by rfl) ⟨856428, by rfl⟩ : syracuseStep 2283809 = 1712857) (by norm_num)
theorem B6090157 : Blo 2137435 6090157 := bstep (se 3 (by rfl) ⟨1141904, by rfl⟩ : syracuseStep 6090157 = 2283809) B2283809
theorem B8120209 : Blo 2137435 8120209 := bstep (se 2 (by rfl) ⟨3045078, by rfl⟩ : syracuseStep 8120209 = 6090157) B6090157
theorem B10826945 : Blo 2137435 10826945 := bstep (se 2 (by rfl) ⟨4060104, by rfl⟩ : syracuseStep 10826945 = 8120209) B8120209
theorem B7217963 : Blo 2137435 7217963 := bstep (se 1 (by rfl) ⟨5413472, by rfl⟩ : syracuseStep 7217963 = 10826945) B10826945
theorem B4811975 : Blo 2137435 4811975 := bstep (se 1 (by rfl) ⟨3608981, by rfl⟩ : syracuseStep 4811975 = 7217963) B7217963
theorem B3207983 : Blo 2137435 3207983 := bstep (se 1 (by rfl) ⟨2405987, by rfl⟩ : syracuseStep 3207983 = 4811975) B4811975
theorem B2138655 : Blo 2137435 2138655 := bstep (se 1 (by rfl) ⟨1603991, by rfl⟩ : syracuseStep 2138655 = 3207983) B3207983
theorem B3207989 : Blo 2137435 3207989 := bbase (se 5 (by rfl) ⟨150374, by rfl⟩ : syracuseStep 3207989 = 300749) (by norm_num)
theorem B2138659 : Blo 2137435 2138659 := bstep (se 1 (by rfl) ⟨1603994, by rfl⟩ : syracuseStep 2138659 = 3207989) B3207989
theorem B5413493 : Blo 2137435 5413493 := bbase (se 5 (by rfl) ⟨253757, by rfl⟩ : syracuseStep 5413493 = 507515) (by norm_num)
theorem B3608995 : Blo 2137435 3608995 := bstep (se 1 (by rfl) ⟨2706746, by rfl⟩ : syracuseStep 3608995 = 5413493) B5413493
theorem B4811993 : Blo 2137435 4811993 := bstep (se 2 (by rfl) ⟨1804497, by rfl⟩ : syracuseStep 4811993 = 3608995) B3608995
theorem B3207995 : Blo 2137435 3207995 := bstep (se 1 (by rfl) ⟨2405996, by rfl⟩ : syracuseStep 3207995 = 4811993) B4811993
theorem B2138663 : Blo 2137435 2138663 := bstep (se 1 (by rfl) ⟨1603997, by rfl⟩ : syracuseStep 2138663 = 3207995) B3207995
theorem B2406001 : Blo 2137435 2406001 := bbase (se 2 (by rfl) ⟨902250, by rfl⟩ : syracuseStep 2406001 = 1804501) (by norm_num)
theorem B3208001 : Blo 2137435 3208001 := bstep (se 2 (by rfl) ⟨1203000, by rfl⟩ : syracuseStep 3208001 = 2406001) B2406001
theorem B2138667 : Blo 2137435 2138667 := bstep (se 1 (by rfl) ⟨1604000, by rfl⟩ : syracuseStep 2138667 = 3208001) B3208001
theorem B15415829 : Blo 2137435 15415829 := bbase (se 6 (by rfl) ⟨361308, by rfl⟩ : syracuseStep 15415829 = 722617) (by norm_num)
theorem B10277219 : Blo 2137435 10277219 := bstep (se 1 (by rfl) ⟨7707914, by rfl⟩ : syracuseStep 10277219 = 15415829) B15415829
theorem B6851479 : Blo 2137435 6851479 := bstep (se 1 (by rfl) ⟨5138609, by rfl⟩ : syracuseStep 6851479 = 10277219) B10277219
theorem B9135305 : Blo 2137435 9135305 := bstep (se 2 (by rfl) ⟨3425739, by rfl⟩ : syracuseStep 9135305 = 6851479) B6851479
theorem B6090203 : Blo 2137435 6090203 := bstep (se 1 (by rfl) ⟨4567652, by rfl⟩ : syracuseStep 6090203 = 9135305) B9135305
theorem B4060135 : Blo 2137435 4060135 := bstep (se 1 (by rfl) ⟨3045101, by rfl⟩ : syracuseStep 4060135 = 6090203) B6090203
theorem B5413513 : Blo 2137435 5413513 := bstep (se 2 (by rfl) ⟨2030067, by rfl⟩ : syracuseStep 5413513 = 4060135) B4060135
theorem B7218017 : Blo 2137435 7218017 := bstep (se 2 (by rfl) ⟨2706756, by rfl⟩ : syracuseStep 7218017 = 5413513) B5413513
theorem B4812011 : Blo 2137435 4812011 := bstep (se 1 (by rfl) ⟨3609008, by rfl⟩ : syracuseStep 4812011 = 7218017) B7218017
theorem B3208007 : Blo 2137435 3208007 := bstep (se 1 (by rfl) ⟨2406005, by rfl⟩ : syracuseStep 3208007 = 4812011) B4812011
theorem B2138671 : Blo 2137435 2138671 := bstep (se 1 (by rfl) ⟨1604003, by rfl⟩ : syracuseStep 2138671 = 3208007) B3208007
theorem B3208013 : Blo 2137435 3208013 := bbase (se 3 (by rfl) ⟨601502, by rfl⟩ : syracuseStep 3208013 = 1203005) (by norm_num)
theorem B2138675 : Blo 2137435 2138675 := bstep (se 1 (by rfl) ⟨1604006, by rfl⟩ : syracuseStep 2138675 = 3208013) B3208013
theorem B4812029 : Blo 2137435 4812029 := bbase (se 3 (by rfl) ⟨902255, by rfl⟩ : syracuseStep 4812029 = 1804511) (by norm_num)
theorem B3208019 : Blo 2137435 3208019 := bstep (se 1 (by rfl) ⟨2406014, by rfl⟩ : syracuseStep 3208019 = 4812029) B4812029
theorem B2138679 : Blo 2137435 2138679 := bstep (se 1 (by rfl) ⟨1604009, by rfl⟩ : syracuseStep 2138679 = 3208019) B3208019
theorem B3609029 : Blo 2137435 3609029 := bbase (se 4 (by rfl) ⟨338346, by rfl⟩ : syracuseStep 3609029 = 676693) (by norm_num)
theorem B2406019 : Blo 2137435 2406019 := bstep (se 1 (by rfl) ⟨1804514, by rfl⟩ : syracuseStep 2406019 = 3609029) B3609029
theorem B3208025 : Blo 2137435 3208025 := bstep (se 2 (by rfl) ⟨1203009, by rfl⟩ : syracuseStep 3208025 = 2406019) B2406019
theorem B2138683 : Blo 2137435 2138683 := bstep (se 1 (by rfl) ⟨1604012, by rfl⟩ : syracuseStep 2138683 = 3208025) B3208025
theorem B16240661 : Blo 2137435 16240661 := bbase (se 6 (by rfl) ⟨380640, by rfl⟩ : syracuseStep 16240661 = 761281) (by norm_num)
theorem B10827107 : Blo 2137435 10827107 := bstep (se 1 (by rfl) ⟨8120330, by rfl⟩ : syracuseStep 10827107 = 16240661) B16240661
theorem B7218071 : Blo 2137435 7218071 := bstep (se 1 (by rfl) ⟨5413553, by rfl⟩ : syracuseStep 7218071 = 10827107) B10827107
theorem B4812047 : Blo 2137435 4812047 := bstep (se 1 (by rfl) ⟨3609035, by rfl⟩ : syracuseStep 4812047 = 7218071) B7218071
theorem B3208031 : Blo 2137435 3208031 := bstep (se 1 (by rfl) ⟨2406023, by rfl⟩ : syracuseStep 3208031 = 4812047) B4812047
theorem B2138687 : Blo 2137435 2138687 := bstep (se 1 (by rfl) ⟨1604015, by rfl⟩ : syracuseStep 2138687 = 3208031) B3208031
theorem B3208037 : Blo 2137435 3208037 := bbase (se 4 (by rfl) ⟨300753, by rfl⟩ : syracuseStep 3208037 = 601507) (by norm_num)
theorem B2138691 : Blo 2137435 2138691 := bstep (se 1 (by rfl) ⟨1604018, by rfl⟩ : syracuseStep 2138691 = 3208037) B3208037
theorem B4060181 : Blo 2137435 4060181 := bbase (se 6 (by rfl) ⟨95160, by rfl⟩ : syracuseStep 4060181 = 190321) (by norm_num)
theorem B2706787 : Blo 2137435 2706787 := bstep (se 1 (by rfl) ⟨2030090, by rfl⟩ : syracuseStep 2706787 = 4060181) B4060181
theorem B3609049 : Blo 2137435 3609049 := bstep (se 2 (by rfl) ⟨1353393, by rfl⟩ : syracuseStep 3609049 = 2706787) B2706787
theorem B4812065 : Blo 2137435 4812065 := bstep (se 2 (by rfl) ⟨1804524, by rfl⟩ : syracuseStep 4812065 = 3609049) B3609049
theorem B3208043 : Blo 2137435 3208043 := bstep (se 1 (by rfl) ⟨2406032, by rfl⟩ : syracuseStep 3208043 = 4812065) B4812065
theorem B2138695 : Blo 2137435 2138695 := bstep (se 1 (by rfl) ⟨1604021, by rfl⟩ : syracuseStep 2138695 = 3208043) B3208043
theorem B2406037 : Blo 2137435 2406037 := bbase (se 6 (by rfl) ⟨56391, by rfl⟩ : syracuseStep 2406037 = 112783) (by norm_num)
theorem B3208049 : Blo 2137435 3208049 := bstep (se 2 (by rfl) ⟨1203018, by rfl⟩ : syracuseStep 3208049 = 2406037) B2406037
theorem B2138699 : Blo 2137435 2138699 := bstep (se 1 (by rfl) ⟨1604024, by rfl⟩ : syracuseStep 2138699 = 3208049) B3208049
theorem B2706797 : Blo 2137435 2706797 := bbase (se 3 (by rfl) ⟨507524, by rfl⟩ : syracuseStep 2706797 = 1015049) (by norm_num)
theorem B7218125 : Blo 2137435 7218125 := bstep (se 3 (by rfl) ⟨1353398, by rfl⟩ : syracuseStep 7218125 = 2706797) B2706797
theorem B4812083 : Blo 2137435 4812083 := bstep (se 1 (by rfl) ⟨3609062, by rfl⟩ : syracuseStep 4812083 = 7218125) B7218125
theorem B3208055 : Blo 2137435 3208055 := bstep (se 1 (by rfl) ⟨2406041, by rfl⟩ : syracuseStep 3208055 = 4812083) B4812083
theorem B2138703 : Blo 2137435 2138703 := bstep (se 1 (by rfl) ⟨1604027, by rfl⟩ : syracuseStep 2138703 = 3208055) B3208055
theorem B3208061 : Blo 2137435 3208061 := bbase (se 3 (by rfl) ⟨601511, by rfl⟩ : syracuseStep 3208061 = 1203023) (by norm_num)
theorem B2138707 : Blo 2137435 2138707 := bstep (se 1 (by rfl) ⟨1604030, by rfl⟩ : syracuseStep 2138707 = 3208061) B3208061
theorem B4812101 : Blo 2137435 4812101 := bbase (se 4 (by rfl) ⟨451134, by rfl⟩ : syracuseStep 4812101 = 902269) (by norm_num)
theorem B3208067 : Blo 2137435 3208067 := bstep (se 1 (by rfl) ⟨2406050, by rfl⟩ : syracuseStep 3208067 = 4812101) B4812101
theorem B2138711 : Blo 2137435 2138711 := bstep (se 1 (by rfl) ⟨1604033, by rfl⟩ : syracuseStep 2138711 = 3208067) B3208067
theorem B6851621 : Blo 2137435 6851621 := bbase (se 4 (by rfl) ⟨642339, by rfl⟩ : syracuseStep 6851621 = 1284679) (by norm_num)
theorem B4567747 : Blo 2137435 4567747 := bstep (se 1 (by rfl) ⟨3425810, by rfl⟩ : syracuseStep 4567747 = 6851621) B6851621
theorem B6090329 : Blo 2137435 6090329 := bstep (se 2 (by rfl) ⟨2283873, by rfl⟩ : syracuseStep 6090329 = 4567747) B4567747
theorem B4060219 : Blo 2137435 4060219 := bstep (se 1 (by rfl) ⟨3045164, by rfl⟩ : syracuseStep 4060219 = 6090329) B6090329
theorem B5413625 : Blo 2137435 5413625 := bstep (se 2 (by rfl) ⟨2030109, by rfl⟩ : syracuseStep 5413625 = 4060219) B4060219
theorem B3609083 : Blo 2137435 3609083 := bstep (se 1 (by rfl) ⟨2706812, by rfl⟩ : syracuseStep 3609083 = 5413625) B5413625
theorem B2406055 : Blo 2137435 2406055 := bstep (se 1 (by rfl) ⟨1804541, by rfl⟩ : syracuseStep 2406055 = 3609083) B3609083
theorem B3208073 : Blo 2137435 3208073 := bstep (se 2 (by rfl) ⟨1203027, by rfl⟩ : syracuseStep 3208073 = 2406055) B2406055
theorem B2138715 : Blo 2137435 2138715 := bstep (se 1 (by rfl) ⟨1604036, by rfl⟩ : syracuseStep 2138715 = 3208073) B3208073
theorem B10827269 : Blo 2137435 10827269 := bbase (se 4 (by rfl) ⟨1015056, by rfl⟩ : syracuseStep 10827269 = 2030113) (by norm_num)
theorem B7218179 : Blo 2137435 7218179 := bstep (se 1 (by rfl) ⟨5413634, by rfl⟩ : syracuseStep 7218179 = 10827269) B10827269
theorem B4812119 : Blo 2137435 4812119 := bstep (se 1 (by rfl) ⟨3609089, by rfl⟩ : syracuseStep 4812119 = 7218179) B7218179
theorem B3208079 : Blo 2137435 3208079 := bstep (se 1 (by rfl) ⟨2406059, by rfl⟩ : syracuseStep 3208079 = 4812119) B4812119
theorem B2138719 : Blo 2137435 2138719 := bstep (se 1 (by rfl) ⟨1604039, by rfl⟩ : syracuseStep 2138719 = 3208079) B3208079
theorem B3208085 : Blo 2137435 3208085 := bbase (se 6 (by rfl) ⟨75189, by rfl⟩ : syracuseStep 3208085 = 150379) (by norm_num)
theorem B2138723 : Blo 2137435 2138723 := bstep (se 1 (by rfl) ⟨1604042, by rfl⟩ : syracuseStep 2138723 = 3208085) B3208085
theorem B12180725 : Blo 2137435 12180725 := bbase (se 5 (by rfl) ⟨570971, by rfl⟩ : syracuseStep 12180725 = 1141943) (by norm_num)
theorem B8120483 : Blo 2137435 8120483 := bstep (se 1 (by rfl) ⟨6090362, by rfl⟩ : syracuseStep 8120483 = 12180725) B12180725
theorem B5413655 : Blo 2137435 5413655 := bstep (se 1 (by rfl) ⟨4060241, by rfl⟩ : syracuseStep 5413655 = 8120483) B8120483
theorem B3609103 : Blo 2137435 3609103 := bstep (se 1 (by rfl) ⟨2706827, by rfl⟩ : syracuseStep 3609103 = 5413655) B5413655
theorem B4812137 : Blo 2137435 4812137 := bstep (se 2 (by rfl) ⟨1804551, by rfl⟩ : syracuseStep 4812137 = 3609103) B3609103
theorem B3208091 : Blo 2137435 3208091 := bstep (se 1 (by rfl) ⟨2406068, by rfl⟩ : syracuseStep 3208091 = 4812137) B4812137
theorem B2138727 : Blo 2137435 2138727 := bstep (se 1 (by rfl) ⟨1604045, by rfl⟩ : syracuseStep 2138727 = 3208091) B3208091
theorem B2406073 : Blo 2137435 2406073 := bbase (se 2 (by rfl) ⟨902277, by rfl⟩ : syracuseStep 2406073 = 1804555) (by norm_num)
theorem B3208097 : Blo 2137435 3208097 := bstep (se 2 (by rfl) ⟨1203036, by rfl⟩ : syracuseStep 3208097 = 2406073) B2406073
theorem B2138731 : Blo 2137435 2138731 := bstep (se 1 (by rfl) ⟨1604048, by rfl⟩ : syracuseStep 2138731 = 3208097) B3208097
theorem B4567789 : Blo 2137435 4567789 := bbase (se 3 (by rfl) ⟨856460, by rfl⟩ : syracuseStep 4567789 = 1712921) (by norm_num)
theorem B6090385 : Blo 2137435 6090385 := bstep (se 2 (by rfl) ⟨2283894, by rfl⟩ : syracuseStep 6090385 = 4567789) B4567789
theorem B8120513 : Blo 2137435 8120513 := bstep (se 2 (by rfl) ⟨3045192, by rfl⟩ : syracuseStep 8120513 = 6090385) B6090385
theorem B5413675 : Blo 2137435 5413675 := bstep (se 1 (by rfl) ⟨4060256, by rfl⟩ : syracuseStep 5413675 = 8120513) B8120513
theorem B7218233 : Blo 2137435 7218233 := bstep (se 2 (by rfl) ⟨2706837, by rfl⟩ : syracuseStep 7218233 = 5413675) B5413675
theorem B4812155 : Blo 2137435 4812155 := bstep (se 1 (by rfl) ⟨3609116, by rfl⟩ : syracuseStep 4812155 = 7218233) B7218233
theorem B3208103 : Blo 2137435 3208103 := bstep (se 1 (by rfl) ⟨2406077, by rfl⟩ : syracuseStep 3208103 = 4812155) B4812155
theorem B2138735 : Blo 2137435 2138735 := bstep (se 1 (by rfl) ⟨1604051, by rfl⟩ : syracuseStep 2138735 = 3208103) B3208103
theorem B3208109 : Blo 2137435 3208109 := bbase (se 3 (by rfl) ⟨601520, by rfl⟩ : syracuseStep 3208109 = 1203041) (by norm_num)
theorem B2138739 : Blo 2137435 2138739 := bstep (se 1 (by rfl) ⟨1604054, by rfl⟩ : syracuseStep 2138739 = 3208109) B3208109
theorem B4812173 : Blo 2137435 4812173 := bbase (se 3 (by rfl) ⟨902282, by rfl⟩ : syracuseStep 4812173 = 1804565) (by norm_num)
theorem B3208115 : Blo 2137435 3208115 := bstep (se 1 (by rfl) ⟨2406086, by rfl⟩ : syracuseStep 3208115 = 4812173) B4812173
theorem B2138743 : Blo 2137435 2138743 := bstep (se 1 (by rfl) ⟨1604057, by rfl⟩ : syracuseStep 2138743 = 3208115) B3208115
theorem B2706853 : Blo 2137435 2706853 := bbase (se 4 (by rfl) ⟨253767, by rfl⟩ : syracuseStep 2706853 = 507535) (by norm_num)
theorem B3609137 : Blo 2137435 3609137 := bstep (se 2 (by rfl) ⟨1353426, by rfl⟩ : syracuseStep 3609137 = 2706853) B2706853
theorem B2406091 : Blo 2137435 2406091 := bstep (se 1 (by rfl) ⟨1804568, by rfl⟩ : syracuseStep 2406091 = 3609137) B3609137
theorem B3208121 : Blo 2137435 3208121 := bstep (se 2 (by rfl) ⟨1203045, by rfl⟩ : syracuseStep 3208121 = 2406091) B2406091
theorem B2138747 : Blo 2137435 2138747 := bstep (se 1 (by rfl) ⟨1604060, by rfl⟩ : syracuseStep 2138747 = 3208121) B3208121
theorem B3171565 : Blo 2137435 3171565 := bbase (se 3 (by rfl) ⟨594668, by rfl⟩ : syracuseStep 3171565 = 1189337) (by norm_num)
theorem B16915013 : Blo 2137435 16915013 := bstep (se 4 (by rfl) ⟨1585782, by rfl⟩ : syracuseStep 16915013 = 3171565) B3171565
theorem B11276675 : Blo 2137435 11276675 := bstep (se 1 (by rfl) ⟨8457506, by rfl⟩ : syracuseStep 11276675 = 16915013) B16915013
theorem B7517783 : Blo 2137435 7517783 := bstep (se 1 (by rfl) ⟨5638337, by rfl⟩ : syracuseStep 7517783 = 11276675) B11276675
theorem B20047421 : Blo 2137435 20047421 := bstep (se 3 (by rfl) ⟨3758891, by rfl⟩ : syracuseStep 20047421 = 7517783) B7517783
theorem B13364947 : Blo 2137435 13364947 := bstep (se 1 (by rfl) ⟨10023710, by rfl⟩ : syracuseStep 13364947 = 20047421) B20047421
theorem B17819929 : Blo 2137435 17819929 := bstep (se 2 (by rfl) ⟨6682473, by rfl⟩ : syracuseStep 17819929 = 13364947) B13364947
theorem B23759905 : Blo 2137435 23759905 := bstep (se 2 (by rfl) ⟨8909964, by rfl⟩ : syracuseStep 23759905 = 17819929) B17819929
theorem B31679873 : Blo 2137435 31679873 := bstep (se 2 (by rfl) ⟨11879952, by rfl⟩ : syracuseStep 31679873 = 23759905) B23759905
theorem B21119915 : Blo 2137435 21119915 := bstep (se 1 (by rfl) ⟨15839936, by rfl⟩ : syracuseStep 21119915 = 31679873) B31679873
theorem B14079943 : Blo 2137435 14079943 := bstep (se 1 (by rfl) ⟨10559957, by rfl⟩ : syracuseStep 14079943 = 21119915) B21119915
theorem B75093029 : Blo 2137435 75093029 := bstep (se 4 (by rfl) ⟨7039971, by rfl⟩ : syracuseStep 75093029 = 14079943) B14079943
theorem B50062019 : Blo 2137435 50062019 := bstep (se 1 (by rfl) ⟨37546514, by rfl⟩ : syracuseStep 50062019 = 75093029) B75093029
theorem B533994869 : Blo 2137435 533994869 := bstep (se 5 (by rfl) ⟨25031009, by rfl⟩ : syracuseStep 533994869 = 50062019) B50062019
theorem B1423986317 : Blo 2137435 1423986317 := bstep (se 3 (by rfl) ⟨266997434, by rfl⟩ : syracuseStep 1423986317 = 533994869) B533994869
theorem B949324211 : Blo 2137435 949324211 := bstep (se 1 (by rfl) ⟨711993158, by rfl⟩ : syracuseStep 949324211 = 1423986317) B1423986317
theorem B632882807 : Blo 2137435 632882807 := bstep (se 1 (by rfl) ⟨474662105, by rfl⟩ : syracuseStep 632882807 = 949324211) B949324211
theorem B421921871 : Blo 2137435 421921871 := bstep (se 1 (by rfl) ⟨316441403, by rfl⟩ : syracuseStep 421921871 = 632882807) B632882807
theorem B281281247 : Blo 2137435 281281247 := bstep (se 1 (by rfl) ⟨210960935, by rfl⟩ : syracuseStep 281281247 = 421921871) B421921871
theorem B187520831 : Blo 2137435 187520831 := bstep (se 1 (by rfl) ⟨140640623, by rfl⟩ : syracuseStep 187520831 = 281281247) B281281247
theorem B125013887 : Blo 2137435 125013887 := bstep (se 1 (by rfl) ⟨93760415, by rfl⟩ : syracuseStep 125013887 = 187520831) B187520831
theorem B83342591 : Blo 2137435 83342591 := bstep (se 1 (by rfl) ⟨62506943, by rfl⟩ : syracuseStep 83342591 = 125013887) B125013887
theorem B55561727 : Blo 2137435 55561727 := bstep (se 1 (by rfl) ⟨41671295, by rfl⟩ : syracuseStep 55561727 = 83342591) B83342591
theorem B37041151 : Blo 2137435 37041151 := bstep (se 1 (by rfl) ⟨27780863, by rfl⟩ : syracuseStep 37041151 = 55561727) B55561727
theorem B49388201 : Blo 2137435 49388201 := bstep (se 2 (by rfl) ⟨18520575, by rfl⟩ : syracuseStep 49388201 = 37041151) B37041151
theorem B32925467 : Blo 2137435 32925467 := bstep (se 1 (by rfl) ⟨24694100, by rfl⟩ : syracuseStep 32925467 = 49388201) B49388201
theorem B21950311 : Blo 2137435 21950311 := bstep (se 1 (by rfl) ⟨16462733, by rfl⟩ : syracuseStep 21950311 = 32925467) B32925467
theorem B29267081 : Blo 2137435 29267081 := bstep (se 2 (by rfl) ⟨10975155, by rfl⟩ : syracuseStep 29267081 = 21950311) B21950311
theorem B19511387 : Blo 2137435 19511387 := bstep (se 1 (by rfl) ⟨14633540, by rfl⟩ : syracuseStep 19511387 = 29267081) B29267081
theorem B13007591 : Blo 2137435 13007591 := bstep (se 1 (by rfl) ⟨9755693, by rfl⟩ : syracuseStep 13007591 = 19511387) B19511387
theorem B8671727 : Blo 2137435 8671727 := bstep (se 1 (by rfl) ⟨6503795, by rfl⟩ : syracuseStep 8671727 = 13007591) B13007591
theorem B5781151 : Blo 2137435 5781151 := bstep (se 1 (by rfl) ⟨4335863, by rfl⟩ : syracuseStep 5781151 = 8671727) B8671727
theorem B30832805 : Blo 2137435 30832805 := bstep (se 4 (by rfl) ⟨2890575, by rfl⟩ : syracuseStep 30832805 = 5781151) B5781151
theorem B20555203 : Blo 2137435 20555203 := bstep (se 1 (by rfl) ⟨15416402, by rfl⟩ : syracuseStep 20555203 = 30832805) B30832805
theorem B27406937 : Blo 2137435 27406937 := bstep (se 2 (by rfl) ⟨10277601, by rfl⟩ : syracuseStep 27406937 = 20555203) B20555203
theorem B18271291 : Blo 2137435 18271291 := bstep (se 1 (by rfl) ⟨13703468, by rfl⟩ : syracuseStep 18271291 = 27406937) B27406937
theorem B24361721 : Blo 2137435 24361721 := bstep (se 2 (by rfl) ⟨9135645, by rfl⟩ : syracuseStep 24361721 = 18271291) B18271291
theorem B16241147 : Blo 2137435 16241147 := bstep (se 1 (by rfl) ⟨12180860, by rfl⟩ : syracuseStep 16241147 = 24361721) B24361721
theorem B10827431 : Blo 2137435 10827431 := bstep (se 1 (by rfl) ⟨8120573, by rfl⟩ : syracuseStep 10827431 = 16241147) B16241147
theorem B7218287 : Blo 2137435 7218287 := bstep (se 1 (by rfl) ⟨5413715, by rfl⟩ : syracuseStep 7218287 = 10827431) B10827431
theorem B4812191 : Blo 2137435 4812191 := bstep (se 1 (by rfl) ⟨3609143, by rfl⟩ : syracuseStep 4812191 = 7218287) B7218287
theorem B3208127 : Blo 2137435 3208127 := bstep (se 1 (by rfl) ⟨2406095, by rfl⟩ : syracuseStep 3208127 = 4812191) B4812191
theorem B2138751 : Blo 2137435 2138751 := bstep (se 1 (by rfl) ⟨1604063, by rfl⟩ : syracuseStep 2138751 = 3208127) B3208127
theorem B3208133 : Blo 2137435 3208133 := bbase (se 4 (by rfl) ⟨300762, by rfl⟩ : syracuseStep 3208133 = 601525) (by norm_num)
theorem B2138755 : Blo 2137435 2138755 := bstep (se 1 (by rfl) ⟨1604066, by rfl⟩ : syracuseStep 2138755 = 3208133) B3208133
theorem B3609157 : Blo 2137435 3609157 := bbase (se 4 (by rfl) ⟨338358, by rfl⟩ : syracuseStep 3609157 = 676717) (by norm_num)
theorem B4812209 : Blo 2137435 4812209 := bstep (se 2 (by rfl) ⟨1804578, by rfl⟩ : syracuseStep 4812209 = 3609157) B3609157
theorem B3208139 : Blo 2137435 3208139 := bstep (se 1 (by rfl) ⟨2406104, by rfl⟩ : syracuseStep 3208139 = 4812209) B4812209
theorem B2138759 : Blo 2137435 2138759 := bstep (se 1 (by rfl) ⟨1604069, by rfl⟩ : syracuseStep 2138759 = 3208139) B3208139
theorem B2406109 : Blo 2137435 2406109 := bbase (se 3 (by rfl) ⟨451145, by rfl⟩ : syracuseStep 2406109 = 902291) (by norm_num)
theorem B3208145 : Blo 2137435 3208145 := bstep (se 2 (by rfl) ⟨1203054, by rfl⟩ : syracuseStep 3208145 = 2406109) B2406109
theorem B2138763 : Blo 2137435 2138763 := bstep (se 1 (by rfl) ⟨1604072, by rfl⟩ : syracuseStep 2138763 = 3208145) B3208145
theorem B7218341 : Blo 2137435 7218341 := bbase (se 4 (by rfl) ⟨676719, by rfl⟩ : syracuseStep 7218341 = 1353439) (by norm_num)
theorem B4812227 : Blo 2137435 4812227 := bstep (se 1 (by rfl) ⟨3609170, by rfl⟩ : syracuseStep 4812227 = 7218341) B7218341
theorem B3208151 : Blo 2137435 3208151 := bstep (se 1 (by rfl) ⟨2406113, by rfl⟩ : syracuseStep 3208151 = 4812227) B4812227
theorem B2138767 : Blo 2137435 2138767 := bstep (se 1 (by rfl) ⟨1604075, by rfl⟩ : syracuseStep 2138767 = 3208151) B3208151
theorem B3208157 : Blo 2137435 3208157 := bbase (se 3 (by rfl) ⟨601529, by rfl⟩ : syracuseStep 3208157 = 1203059) (by norm_num)
theorem B2138771 : Blo 2137435 2138771 := bstep (se 1 (by rfl) ⟨1604078, by rfl⟩ : syracuseStep 2138771 = 3208157) B3208157
theorem B4812245 : Blo 2137435 4812245 := bbase (se 7 (by rfl) ⟨56393, by rfl⟩ : syracuseStep 4812245 = 112787) (by norm_num)
theorem B3208163 : Blo 2137435 3208163 := bstep (se 1 (by rfl) ⟨2406122, by rfl⟩ : syracuseStep 3208163 = 4812245) B4812245
theorem B2138775 : Blo 2137435 2138775 := bstep (se 1 (by rfl) ⟨1604081, by rfl⟩ : syracuseStep 2138775 = 3208163) B3208163
theorem B20555477 : Blo 2137435 20555477 := bbase (se 7 (by rfl) ⟨240884, by rfl⟩ : syracuseStep 20555477 = 481769) (by norm_num)
theorem B13703651 : Blo 2137435 13703651 := bstep (se 1 (by rfl) ⟨10277738, by rfl⟩ : syracuseStep 13703651 = 20555477) B20555477
theorem B9135767 : Blo 2137435 9135767 := bstep (se 1 (by rfl) ⟨6851825, by rfl⟩ : syracuseStep 9135767 = 13703651) B13703651
theorem B6090511 : Blo 2137435 6090511 := bstep (se 1 (by rfl) ⟨4567883, by rfl⟩ : syracuseStep 6090511 = 9135767) B9135767
theorem B8120681 : Blo 2137435 8120681 := bstep (se 2 (by rfl) ⟨3045255, by rfl⟩ : syracuseStep 8120681 = 6090511) B6090511
theorem B5413787 : Blo 2137435 5413787 := bstep (se 1 (by rfl) ⟨4060340, by rfl⟩ : syracuseStep 5413787 = 8120681) B8120681
theorem B3609191 : Blo 2137435 3609191 := bstep (se 1 (by rfl) ⟨2706893, by rfl⟩ : syracuseStep 3609191 = 5413787) B5413787
theorem B2406127 : Blo 2137435 2406127 := bstep (se 1 (by rfl) ⟨1804595, by rfl⟩ : syracuseStep 2406127 = 3609191) B3609191
theorem B3208169 : Blo 2137435 3208169 := bstep (se 2 (by rfl) ⟨1203063, by rfl⟩ : syracuseStep 3208169 = 2406127) B2406127
theorem B2138779 : Blo 2137435 2138779 := bstep (se 1 (by rfl) ⟨1604084, by rfl⟩ : syracuseStep 2138779 = 3208169) B3208169
theorem B6173621 : Blo 2137435 6173621 := bbase (se 5 (by rfl) ⟨289388, by rfl⟩ : syracuseStep 6173621 = 578777) (by norm_num)
theorem B4115747 : Blo 2137435 4115747 := bstep (se 1 (by rfl) ⟨3086810, by rfl⟩ : syracuseStep 4115747 = 6173621) B6173621
theorem B2743831 : Blo 2137435 2743831 := bstep (se 1 (by rfl) ⟨2057873, by rfl⟩ : syracuseStep 2743831 = 4115747) B4115747
theorem B3658441 : Blo 2137435 3658441 := bstep (se 2 (by rfl) ⟨1371915, by rfl⟩ : syracuseStep 3658441 = 2743831) B2743831
theorem B4877921 : Blo 2137435 4877921 := bstep (se 2 (by rfl) ⟨1829220, by rfl⟩ : syracuseStep 4877921 = 3658441) B3658441
theorem B13007789 : Blo 2137435 13007789 := bstep (se 3 (by rfl) ⟨2438960, by rfl⟩ : syracuseStep 13007789 = 4877921) B4877921
theorem B8671859 : Blo 2137435 8671859 := bstep (se 1 (by rfl) ⟨6503894, by rfl⟩ : syracuseStep 8671859 = 13007789) B13007789
theorem B5781239 : Blo 2137435 5781239 := bstep (se 1 (by rfl) ⟨4335929, by rfl⟩ : syracuseStep 5781239 = 8671859) B8671859
theorem B3854159 : Blo 2137435 3854159 := bstep (se 1 (by rfl) ⟨2890619, by rfl⟩ : syracuseStep 3854159 = 5781239) B5781239
theorem B2569439 : Blo 2137435 2569439 := bstep (se 1 (by rfl) ⟨1927079, by rfl⟩ : syracuseStep 2569439 = 3854159) B3854159
theorem B6851837 : Blo 2137435 6851837 := bstep (se 3 (by rfl) ⟨1284719, by rfl⟩ : syracuseStep 6851837 = 2569439) B2569439
theorem B18271565 : Blo 2137435 18271565 := bstep (se 3 (by rfl) ⟨3425918, by rfl⟩ : syracuseStep 18271565 = 6851837) B6851837
theorem B12181043 : Blo 2137435 12181043 := bstep (se 1 (by rfl) ⟨9135782, by rfl⟩ : syracuseStep 12181043 = 18271565) B18271565
theorem B8120695 : Blo 2137435 8120695 := bstep (se 1 (by rfl) ⟨6090521, by rfl⟩ : syracuseStep 8120695 = 12181043) B12181043
theorem B10827593 : Blo 2137435 10827593 := bstep (se 2 (by rfl) ⟨4060347, by rfl⟩ : syracuseStep 10827593 = 8120695) B8120695
theorem B7218395 : Blo 2137435 7218395 := bstep (se 1 (by rfl) ⟨5413796, by rfl⟩ : syracuseStep 7218395 = 10827593) B10827593
theorem B4812263 : Blo 2137435 4812263 := bstep (se 1 (by rfl) ⟨3609197, by rfl⟩ : syracuseStep 4812263 = 7218395) B7218395
theorem B3208175 : Blo 2137435 3208175 := bstep (se 1 (by rfl) ⟨2406131, by rfl⟩ : syracuseStep 3208175 = 4812263) B4812263
theorem B2138783 : Blo 2137435 2138783 := bstep (se 1 (by rfl) ⟨1604087, by rfl⟩ : syracuseStep 2138783 = 3208175) B3208175
theorem B3208181 : Blo 2137435 3208181 := bbase (se 5 (by rfl) ⟨150383, by rfl⟩ : syracuseStep 3208181 = 300767) (by norm_num)
theorem B2138787 : Blo 2137435 2138787 := bstep (se 1 (by rfl) ⟨1604090, by rfl⟩ : syracuseStep 2138787 = 3208181) B3208181
theorem B4567909 : Blo 2137435 4567909 := bbase (se 4 (by rfl) ⟨428241, by rfl⟩ : syracuseStep 4567909 = 856483) (by norm_num)
theorem B6090545 : Blo 2137435 6090545 := bstep (se 2 (by rfl) ⟨2283954, by rfl⟩ : syracuseStep 6090545 = 4567909) B4567909
theorem B4060363 : Blo 2137435 4060363 := bstep (se 1 (by rfl) ⟨3045272, by rfl⟩ : syracuseStep 4060363 = 6090545) B6090545
theorem B5413817 : Blo 2137435 5413817 := bstep (se 2 (by rfl) ⟨2030181, by rfl⟩ : syracuseStep 5413817 = 4060363) B4060363
theorem B3609211 : Blo 2137435 3609211 := bstep (se 1 (by rfl) ⟨2706908, by rfl⟩ : syracuseStep 3609211 = 5413817) B5413817
theorem B4812281 : Blo 2137435 4812281 := bstep (se 2 (by rfl) ⟨1804605, by rfl⟩ : syracuseStep 4812281 = 3609211) B3609211
theorem B3208187 : Blo 2137435 3208187 := bstep (se 1 (by rfl) ⟨2406140, by rfl⟩ : syracuseStep 3208187 = 4812281) B4812281
theorem B2138791 : Blo 2137435 2138791 := bstep (se 1 (by rfl) ⟨1604093, by rfl⟩ : syracuseStep 2138791 = 3208187) B3208187
theorem B2406145 : Blo 2137435 2406145 := bbase (se 2 (by rfl) ⟨902304, by rfl⟩ : syracuseStep 2406145 = 1804609) (by norm_num)
theorem B3208193 : Blo 2137435 3208193 := bstep (se 2 (by rfl) ⟨1203072, by rfl⟩ : syracuseStep 3208193 = 2406145) B2406145
theorem B2138795 : Blo 2137435 2138795 := bstep (se 1 (by rfl) ⟨1604096, by rfl⟩ : syracuseStep 2138795 = 3208193) B3208193
theorem B5413837 : Blo 2137435 5413837 := bbase (se 3 (by rfl) ⟨1015094, by rfl⟩ : syracuseStep 5413837 = 2030189) (by norm_num)
theorem B7218449 : Blo 2137435 7218449 := bstep (se 2 (by rfl) ⟨2706918, by rfl⟩ : syracuseStep 7218449 = 5413837) B5413837
theorem B4812299 : Blo 2137435 4812299 := bstep (se 1 (by rfl) ⟨3609224, by rfl⟩ : syracuseStep 4812299 = 7218449) B7218449
theorem B3208199 : Blo 2137435 3208199 := bstep (se 1 (by rfl) ⟨2406149, by rfl⟩ : syracuseStep 3208199 = 4812299) B4812299
theorem B2138799 : Blo 2137435 2138799 := bstep (se 1 (by rfl) ⟨1604099, by rfl⟩ : syracuseStep 2138799 = 3208199) B3208199
theorem B3208205 : Blo 2137435 3208205 := bbase (se 3 (by rfl) ⟨601538, by rfl⟩ : syracuseStep 3208205 = 1203077) (by norm_num)
theorem B2138803 : Blo 2137435 2138803 := bstep (se 1 (by rfl) ⟨1604102, by rfl⟩ : syracuseStep 2138803 = 3208205) B3208205
theorem B4812317 : Blo 2137435 4812317 := bbase (se 3 (by rfl) ⟨902309, by rfl⟩ : syracuseStep 4812317 = 1804619) (by norm_num)
theorem B3208211 : Blo 2137435 3208211 := bstep (se 1 (by rfl) ⟨2406158, by rfl⟩ : syracuseStep 3208211 = 4812317) B4812317
theorem B2138807 : Blo 2137435 2138807 := bstep (se 1 (by rfl) ⟨1604105, by rfl⟩ : syracuseStep 2138807 = 3208211) B3208211
theorem B3609245 : Blo 2137435 3609245 := bbase (se 3 (by rfl) ⟨676733, by rfl⟩ : syracuseStep 3609245 = 1353467) (by norm_num)
theorem B2406163 : Blo 2137435 2406163 := bstep (se 1 (by rfl) ⟨1804622, by rfl⟩ : syracuseStep 2406163 = 3609245) B3609245
theorem B3208217 : Blo 2137435 3208217 := bstep (se 2 (by rfl) ⟨1203081, by rfl⟩ : syracuseStep 3208217 = 2406163) B2406163
theorem B2138811 : Blo 2137435 2138811 := bstep (se 1 (by rfl) ⟨1604108, by rfl⟩ : syracuseStep 2138811 = 3208217) B3208217
theorem B9889093 : Blo 2137435 9889093 := bbase (se 4 (by rfl) ⟨927102, by rfl⟩ : syracuseStep 9889093 = 1854205) (by norm_num)
theorem B52741829 : Blo 2137435 52741829 := bstep (se 4 (by rfl) ⟨4944546, by rfl⟩ : syracuseStep 52741829 = 9889093) B9889093
theorem B35161219 : Blo 2137435 35161219 := bstep (se 1 (by rfl) ⟨26370914, by rfl⟩ : syracuseStep 35161219 = 52741829) B52741829
theorem B46881625 : Blo 2137435 46881625 := bstep (se 2 (by rfl) ⟨17580609, by rfl⟩ : syracuseStep 46881625 = 35161219) B35161219
theorem B62508833 : Blo 2137435 62508833 := bstep (se 2 (by rfl) ⟨23440812, by rfl⟩ : syracuseStep 62508833 = 46881625) B46881625
theorem B41672555 : Blo 2137435 41672555 := bstep (se 1 (by rfl) ⟨31254416, by rfl⟩ : syracuseStep 41672555 = 62508833) B62508833
theorem B27781703 : Blo 2137435 27781703 := bstep (se 1 (by rfl) ⟨20836277, by rfl⟩ : syracuseStep 27781703 = 41672555) B41672555
theorem B18521135 : Blo 2137435 18521135 := bstep (se 1 (by rfl) ⟨13890851, by rfl⟩ : syracuseStep 18521135 = 27781703) B27781703
theorem B12347423 : Blo 2137435 12347423 := bstep (se 1 (by rfl) ⟨9260567, by rfl⟩ : syracuseStep 12347423 = 18521135) B18521135
theorem B8231615 : Blo 2137435 8231615 := bstep (se 1 (by rfl) ⟨6173711, by rfl⟩ : syracuseStep 8231615 = 12347423) B12347423
theorem B5487743 : Blo 2137435 5487743 := bstep (se 1 (by rfl) ⟨4115807, by rfl⟩ : syracuseStep 5487743 = 8231615) B8231615
theorem B3658495 : Blo 2137435 3658495 := bstep (se 1 (by rfl) ⟨2743871, by rfl⟩ : syracuseStep 3658495 = 5487743) B5487743
theorem B4877993 : Blo 2137435 4877993 := bstep (se 2 (by rfl) ⟨1829247, by rfl⟩ : syracuseStep 4877993 = 3658495) B3658495
theorem B3251995 : Blo 2137435 3251995 := bstep (se 1 (by rfl) ⟨2438996, by rfl⟩ : syracuseStep 3251995 = 4877993) B4877993
theorem B17343973 : Blo 2137435 17343973 := bstep (se 4 (by rfl) ⟨1625997, by rfl⟩ : syracuseStep 17343973 = 3251995) B3251995
theorem B23125297 : Blo 2137435 23125297 := bstep (se 2 (by rfl) ⟨8671986, by rfl⟩ : syracuseStep 23125297 = 17343973) B17343973
theorem B30833729 : Blo 2137435 30833729 := bstep (se 2 (by rfl) ⟨11562648, by rfl⟩ : syracuseStep 30833729 = 23125297) B23125297
theorem B20555819 : Blo 2137435 20555819 := bstep (se 1 (by rfl) ⟨15416864, by rfl⟩ : syracuseStep 20555819 = 30833729) B30833729
theorem B13703879 : Blo 2137435 13703879 := bstep (se 1 (by rfl) ⟨10277909, by rfl⟩ : syracuseStep 13703879 = 20555819) B20555819
theorem B9135919 : Blo 2137435 9135919 := bstep (se 1 (by rfl) ⟨6851939, by rfl⟩ : syracuseStep 9135919 = 13703879) B13703879
theorem B12181225 : Blo 2137435 12181225 := bstep (se 2 (by rfl) ⟨4567959, by rfl⟩ : syracuseStep 12181225 = 9135919) B9135919
theorem B16241633 : Blo 2137435 16241633 := bstep (se 2 (by rfl) ⟨6090612, by rfl⟩ : syracuseStep 16241633 = 12181225) B12181225
theorem B10827755 : Blo 2137435 10827755 := bstep (se 1 (by rfl) ⟨8120816, by rfl⟩ : syracuseStep 10827755 = 16241633) B16241633
theorem B7218503 : Blo 2137435 7218503 := bstep (se 1 (by rfl) ⟨5413877, by rfl⟩ : syracuseStep 7218503 = 10827755) B10827755
theorem B4812335 : Blo 2137435 4812335 := bstep (se 1 (by rfl) ⟨3609251, by rfl⟩ : syracuseStep 4812335 = 7218503) B7218503
theorem B3208223 : Blo 2137435 3208223 := bstep (se 1 (by rfl) ⟨2406167, by rfl⟩ : syracuseStep 3208223 = 4812335) B4812335
theorem B2138815 : Blo 2137435 2138815 := bstep (se 1 (by rfl) ⟨1604111, by rfl⟩ : syracuseStep 2138815 = 3208223) B3208223
theorem B3208229 : Blo 2137435 3208229 := bbase (se 4 (by rfl) ⟨300771, by rfl⟩ : syracuseStep 3208229 = 601543) (by norm_num)
theorem B2138819 : Blo 2137435 2138819 := bstep (se 1 (by rfl) ⟨1604114, by rfl⟩ : syracuseStep 2138819 = 3208229) B3208229
theorem B2706949 : Blo 2137435 2706949 := bbase (se 4 (by rfl) ⟨253776, by rfl⟩ : syracuseStep 2706949 = 507553) (by norm_num)
theorem B3609265 : Blo 2137435 3609265 := bstep (se 2 (by rfl) ⟨1353474, by rfl⟩ : syracuseStep 3609265 = 2706949) B2706949
theorem B4812353 : Blo 2137435 4812353 := bstep (se 2 (by rfl) ⟨1804632, by rfl⟩ : syracuseStep 4812353 = 3609265) B3609265
theorem B3208235 : Blo 2137435 3208235 := bstep (se 1 (by rfl) ⟨2406176, by rfl⟩ : syracuseStep 3208235 = 4812353) B4812353
theorem B2138823 : Blo 2137435 2138823 := bstep (se 1 (by rfl) ⟨1604117, by rfl⟩ : syracuseStep 2138823 = 3208235) B3208235
theorem B2406181 : Blo 2137435 2406181 := bbase (se 4 (by rfl) ⟨225579, by rfl⟩ : syracuseStep 2406181 = 451159) (by norm_num)
theorem B3208241 : Blo 2137435 3208241 := bstep (se 2 (by rfl) ⟨1203090, by rfl⟩ : syracuseStep 3208241 = 2406181) B2406181
theorem B2138827 : Blo 2137435 2138827 := bstep (se 1 (by rfl) ⟨1604120, by rfl⟩ : syracuseStep 2138827 = 3208241) B3208241
theorem B9135989 : Blo 2137435 9135989 := bbase (se 5 (by rfl) ⟨428249, by rfl⟩ : syracuseStep 9135989 = 856499) (by norm_num)
theorem B6090659 : Blo 2137435 6090659 := bstep (se 1 (by rfl) ⟨4567994, by rfl⟩ : syracuseStep 6090659 = 9135989) B9135989
theorem B4060439 : Blo 2137435 4060439 := bstep (se 1 (by rfl) ⟨3045329, by rfl⟩ : syracuseStep 4060439 = 6090659) B6090659
theorem B2706959 : Blo 2137435 2706959 := bstep (se 1 (by rfl) ⟨2030219, by rfl⟩ : syracuseStep 2706959 = 4060439) B4060439
theorem B7218557 : Blo 2137435 7218557 := bstep (se 3 (by rfl) ⟨1353479, by rfl⟩ : syracuseStep 7218557 = 2706959) B2706959
theorem B4812371 : Blo 2137435 4812371 := bstep (se 1 (by rfl) ⟨3609278, by rfl⟩ : syracuseStep 4812371 = 7218557) B7218557
theorem B3208247 : Blo 2137435 3208247 := bstep (se 1 (by rfl) ⟨2406185, by rfl⟩ : syracuseStep 3208247 = 4812371) B4812371
theorem B2138831 : Blo 2137435 2138831 := bstep (se 1 (by rfl) ⟨1604123, by rfl⟩ : syracuseStep 2138831 = 3208247) B3208247
theorem B3208253 : Blo 2137435 3208253 := bbase (se 3 (by rfl) ⟨601547, by rfl⟩ : syracuseStep 3208253 = 1203095) (by norm_num)
theorem B2138835 : Blo 2137435 2138835 := bstep (se 1 (by rfl) ⟨1604126, by rfl⟩ : syracuseStep 2138835 = 3208253) B3208253
theorem B4812389 : Blo 2137435 4812389 := bbase (se 4 (by rfl) ⟨451161, by rfl⟩ : syracuseStep 4812389 = 902323) (by norm_num)
theorem B3208259 : Blo 2137435 3208259 := bstep (se 1 (by rfl) ⟨2406194, by rfl⟩ : syracuseStep 3208259 = 4812389) B4812389
theorem B2138839 : Blo 2137435 2138839 := bstep (se 1 (by rfl) ⟨1604129, by rfl⟩ : syracuseStep 2138839 = 3208259) B3208259
theorem B5413949 : Blo 2137435 5413949 := bbase (se 3 (by rfl) ⟨1015115, by rfl⟩ : syracuseStep 5413949 = 2030231) (by norm_num)
theorem B3609299 : Blo 2137435 3609299 := bstep (se 1 (by rfl) ⟨2706974, by rfl⟩ : syracuseStep 3609299 = 5413949) B5413949
theorem B2406199 : Blo 2137435 2406199 := bstep (se 1 (by rfl) ⟨1804649, by rfl⟩ : syracuseStep 2406199 = 3609299) B3609299
theorem B3208265 : Blo 2137435 3208265 := bstep (se 2 (by rfl) ⟨1203099, by rfl⟩ : syracuseStep 3208265 = 2406199) B2406199
theorem B2138843 : Blo 2137435 2138843 := bstep (se 1 (by rfl) ⟨1604132, by rfl⟩ : syracuseStep 2138843 = 3208265) B3208265
theorem B4060469 : Blo 2137435 4060469 := bbase (se 5 (by rfl) ⟨190334, by rfl⟩ : syracuseStep 4060469 = 380669) (by norm_num)
theorem B10827917 : Blo 2137435 10827917 := bstep (se 3 (by rfl) ⟨2030234, by rfl⟩ : syracuseStep 10827917 = 4060469) B4060469
theorem B7218611 : Blo 2137435 7218611 := bstep (se 1 (by rfl) ⟨5413958, by rfl⟩ : syracuseStep 7218611 = 10827917) B10827917
theorem B4812407 : Blo 2137435 4812407 := bstep (se 1 (by rfl) ⟨3609305, by rfl⟩ : syracuseStep 4812407 = 7218611) B7218611
theorem B3208271 : Blo 2137435 3208271 := bstep (se 1 (by rfl) ⟨2406203, by rfl⟩ : syracuseStep 3208271 = 4812407) B4812407
theorem B2138847 : Blo 2137435 2138847 := bstep (se 1 (by rfl) ⟨1604135, by rfl⟩ : syracuseStep 2138847 = 3208271) B3208271
theorem B3208277 : Blo 2137435 3208277 := bbase (se 8 (by rfl) ⟨18798, by rfl⟩ : syracuseStep 3208277 = 37597) (by norm_num)
theorem B2138851 : Blo 2137435 2138851 := bstep (se 1 (by rfl) ⟨1604138, by rfl⟩ : syracuseStep 2138851 = 3208277) B3208277
theorem B4878085 : Blo 2137435 4878085 := bbase (se 4 (by rfl) ⟨457320, by rfl⟩ : syracuseStep 4878085 = 914641) (by norm_num)
theorem B6504113 : Blo 2137435 6504113 := bstep (se 2 (by rfl) ⟨2439042, by rfl⟩ : syracuseStep 6504113 = 4878085) B4878085
theorem B4336075 : Blo 2137435 4336075 := bstep (se 1 (by rfl) ⟨3252056, by rfl⟩ : syracuseStep 4336075 = 6504113) B6504113
theorem B23125733 : Blo 2137435 23125733 := bstep (se 4 (by rfl) ⟨2168037, by rfl⟩ : syracuseStep 23125733 = 4336075) B4336075
theorem B15417155 : Blo 2137435 15417155 := bstep (se 1 (by rfl) ⟨11562866, by rfl⟩ : syracuseStep 15417155 = 23125733) B23125733
theorem B10278103 : Blo 2137435 10278103 := bstep (se 1 (by rfl) ⟨7708577, by rfl⟩ : syracuseStep 10278103 = 15417155) B15417155
theorem B13704137 : Blo 2137435 13704137 := bstep (se 2 (by rfl) ⟨5139051, by rfl⟩ : syracuseStep 13704137 = 10278103) B10278103
theorem B9136091 : Blo 2137435 9136091 := bstep (se 1 (by rfl) ⟨6852068, by rfl⟩ : syracuseStep 9136091 = 13704137) B13704137
theorem B6090727 : Blo 2137435 6090727 := bstep (se 1 (by rfl) ⟨4568045, by rfl⟩ : syracuseStep 6090727 = 9136091) B9136091
theorem B8120969 : Blo 2137435 8120969 := bstep (se 2 (by rfl) ⟨3045363, by rfl⟩ : syracuseStep 8120969 = 6090727) B6090727
theorem B5413979 : Blo 2137435 5413979 := bstep (se 1 (by rfl) ⟨4060484, by rfl⟩ : syracuseStep 5413979 = 8120969) B8120969
theorem B3609319 : Blo 2137435 3609319 := bstep (se 1 (by rfl) ⟨2706989, by rfl⟩ : syracuseStep 3609319 = 5413979) B5413979
theorem B4812425 : Blo 2137435 4812425 := bstep (se 2 (by rfl) ⟨1804659, by rfl⟩ : syracuseStep 4812425 = 3609319) B3609319
theorem B3208283 : Blo 2137435 3208283 := bstep (se 1 (by rfl) ⟨2406212, by rfl⟩ : syracuseStep 3208283 = 4812425) B4812425
theorem B2138855 : Blo 2137435 2138855 := bstep (se 1 (by rfl) ⟨1604141, by rfl⟩ : syracuseStep 2138855 = 3208283) B3208283
theorem B2406217 : Blo 2137435 2406217 := bbase (se 2 (by rfl) ⟨902331, by rfl⟩ : syracuseStep 2406217 = 1804663) (by norm_num)
theorem B3208289 : Blo 2137435 3208289 := bstep (se 2 (by rfl) ⟨1203108, by rfl⟩ : syracuseStep 3208289 = 2406217) B2406217
theorem B2138859 : Blo 2137435 2138859 := bstep (se 1 (by rfl) ⟨1604144, by rfl⟩ : syracuseStep 2138859 = 3208289) B3208289
theorem B2604593 : Blo 2137435 2604593 := bbase (se 2 (by rfl) ⟨976722, by rfl⟩ : syracuseStep 2604593 = 1953445) (by norm_num)
theorem B6945581 : Blo 2137435 6945581 := bstep (se 3 (by rfl) ⟨1302296, by rfl⟩ : syracuseStep 6945581 = 2604593) B2604593
theorem B4630387 : Blo 2137435 4630387 := bstep (se 1 (by rfl) ⟨3472790, by rfl⟩ : syracuseStep 4630387 = 6945581) B6945581
theorem B6173849 : Blo 2137435 6173849 := bstep (se 2 (by rfl) ⟨2315193, by rfl⟩ : syracuseStep 6173849 = 4630387) B4630387
theorem B4115899 : Blo 2137435 4115899 := bstep (se 1 (by rfl) ⟨3086924, by rfl⟩ : syracuseStep 4115899 = 6173849) B6173849
theorem B21951461 : Blo 2137435 21951461 := bstep (se 4 (by rfl) ⟨2057949, by rfl⟩ : syracuseStep 21951461 = 4115899) B4115899
theorem B14634307 : Blo 2137435 14634307 := bstep (se 1 (by rfl) ⟨10975730, by rfl⟩ : syracuseStep 14634307 = 21951461) B21951461
theorem B19512409 : Blo 2137435 19512409 := bstep (se 2 (by rfl) ⟨7317153, by rfl⟩ : syracuseStep 19512409 = 14634307) B14634307
theorem B26016545 : Blo 2137435 26016545 := bstep (se 2 (by rfl) ⟨9756204, by rfl⟩ : syracuseStep 26016545 = 19512409) B19512409
theorem B17344363 : Blo 2137435 17344363 := bstep (se 1 (by rfl) ⟨13008272, by rfl⟩ : syracuseStep 17344363 = 26016545) B26016545
theorem B23125817 : Blo 2137435 23125817 := bstep (se 2 (by rfl) ⟨8672181, by rfl⟩ : syracuseStep 23125817 = 17344363) B17344363
theorem B15417211 : Blo 2137435 15417211 := bstep (se 1 (by rfl) ⟨11562908, by rfl⟩ : syracuseStep 15417211 = 23125817) B23125817
theorem B20556281 : Blo 2137435 20556281 := bstep (se 2 (by rfl) ⟨7708605, by rfl⟩ : syracuseStep 20556281 = 15417211) B15417211
theorem B13704187 : Blo 2137435 13704187 := bstep (se 1 (by rfl) ⟨10278140, by rfl⟩ : syracuseStep 13704187 = 20556281) B20556281
theorem B18272249 : Blo 2137435 18272249 := bstep (se 2 (by rfl) ⟨6852093, by rfl⟩ : syracuseStep 18272249 = 13704187) B13704187
theorem B12181499 : Blo 2137435 12181499 := bstep (se 1 (by rfl) ⟨9136124, by rfl⟩ : syracuseStep 12181499 = 18272249) B18272249
theorem B8120999 : Blo 2137435 8120999 := bstep (se 1 (by rfl) ⟨6090749, by rfl⟩ : syracuseStep 8120999 = 12181499) B12181499
theorem B5413999 : Blo 2137435 5413999 := bstep (se 1 (by rfl) ⟨4060499, by rfl⟩ : syracuseStep 5413999 = 8120999) B8120999
theorem B7218665 : Blo 2137435 7218665 := bstep (se 2 (by rfl) ⟨2706999, by rfl⟩ : syracuseStep 7218665 = 5413999) B5413999
theorem B4812443 : Blo 2137435 4812443 := bstep (se 1 (by rfl) ⟨3609332, by rfl⟩ : syracuseStep 4812443 = 7218665) B7218665
theorem B3208295 : Blo 2137435 3208295 := bstep (se 1 (by rfl) ⟨2406221, by rfl⟩ : syracuseStep 3208295 = 4812443) B4812443
theorem B2138863 : Blo 2137435 2138863 := bstep (se 1 (by rfl) ⟨1604147, by rfl⟩ : syracuseStep 2138863 = 3208295) B3208295
theorem B3208301 : Blo 2137435 3208301 := bbase (se 3 (by rfl) ⟨601556, by rfl⟩ : syracuseStep 3208301 = 1203113) (by norm_num)
theorem B2138867 : Blo 2137435 2138867 := bstep (se 1 (by rfl) ⟨1604150, by rfl⟩ : syracuseStep 2138867 = 3208301) B3208301
theorem B4812461 : Blo 2137435 4812461 := bbase (se 3 (by rfl) ⟨902336, by rfl⟩ : syracuseStep 4812461 = 1804673) (by norm_num)
theorem B3208307 : Blo 2137435 3208307 := bstep (se 1 (by rfl) ⟨2406230, by rfl⟩ : syracuseStep 3208307 = 4812461) B4812461
theorem B2138871 : Blo 2137435 2138871 := bstep (se 1 (by rfl) ⟨1604153, by rfl⟩ : syracuseStep 2138871 = 3208307) B3208307
theorem B5139101 : Blo 2137435 5139101 := bbase (se 3 (by rfl) ⟨963581, by rfl⟩ : syracuseStep 5139101 = 1927163) (by norm_num)
theorem B3426067 : Blo 2137435 3426067 := bstep (se 1 (by rfl) ⟨2569550, by rfl⟩ : syracuseStep 3426067 = 5139101) B5139101
theorem B4568089 : Blo 2137435 4568089 := bstep (se 2 (by rfl) ⟨1713033, by rfl⟩ : syracuseStep 4568089 = 3426067) B3426067
theorem B6090785 : Blo 2137435 6090785 := bstep (se 2 (by rfl) ⟨2284044, by rfl⟩ : syracuseStep 6090785 = 4568089) B4568089
theorem B4060523 : Blo 2137435 4060523 := bstep (se 1 (by rfl) ⟨3045392, by rfl⟩ : syracuseStep 4060523 = 6090785) B6090785
theorem B2707015 : Blo 2137435 2707015 := bstep (se 1 (by rfl) ⟨2030261, by rfl⟩ : syracuseStep 2707015 = 4060523) B4060523
theorem B3609353 : Blo 2137435 3609353 := bstep (se 2 (by rfl) ⟨1353507, by rfl⟩ : syracuseStep 3609353 = 2707015) B2707015
theorem B2406235 : Blo 2137435 2406235 := bstep (se 1 (by rfl) ⟨1804676, by rfl⟩ : syracuseStep 2406235 = 3609353) B3609353
theorem B3208313 : Blo 2137435 3208313 := bstep (se 2 (by rfl) ⟨1203117, by rfl⟩ : syracuseStep 3208313 = 2406235) B2406235
theorem B2138875 : Blo 2137435 2138875 := bstep (se 1 (by rfl) ⟨1604156, by rfl⟩ : syracuseStep 2138875 = 3208313) B3208313
theorem B8231861 : Blo 2137435 8231861 := bbase (se 5 (by rfl) ⟨385868, by rfl⟩ : syracuseStep 8231861 = 771737) (by norm_num)
theorem B5487907 : Blo 2137435 5487907 := bstep (se 1 (by rfl) ⟨4115930, by rfl⟩ : syracuseStep 5487907 = 8231861) B8231861
theorem B7317209 : Blo 2137435 7317209 := bstep (se 2 (by rfl) ⟨2743953, by rfl⟩ : syracuseStep 7317209 = 5487907) B5487907
theorem B4878139 : Blo 2137435 4878139 := bstep (se 1 (by rfl) ⟨3658604, by rfl⟩ : syracuseStep 4878139 = 7317209) B7317209
theorem B6504185 : Blo 2137435 6504185 := bstep (se 2 (by rfl) ⟨2439069, by rfl⟩ : syracuseStep 6504185 = 4878139) B4878139
theorem B4336123 : Blo 2137435 4336123 := bstep (se 1 (by rfl) ⟨3252092, by rfl⟩ : syracuseStep 4336123 = 6504185) B6504185
theorem B5781497 : Blo 2137435 5781497 := bstep (se 2 (by rfl) ⟨2168061, by rfl⟩ : syracuseStep 5781497 = 4336123) B4336123
theorem B15417325 : Blo 2137435 15417325 := bstep (se 3 (by rfl) ⟨2890748, by rfl⟩ : syracuseStep 15417325 = 5781497) B5781497
theorem B20556433 : Blo 2137435 20556433 := bstep (se 2 (by rfl) ⟨7708662, by rfl⟩ : syracuseStep 20556433 = 15417325) B15417325
theorem B27408577 : Blo 2137435 27408577 := bstep (se 2 (by rfl) ⟨10278216, by rfl⟩ : syracuseStep 27408577 = 20556433) B20556433
theorem B36544769 : Blo 2137435 36544769 := bstep (se 2 (by rfl) ⟨13704288, by rfl⟩ : syracuseStep 36544769 = 27408577) B27408577
theorem B24363179 : Blo 2137435 24363179 := bstep (se 1 (by rfl) ⟨18272384, by rfl⟩ : syracuseStep 24363179 = 36544769) B36544769
theorem B16242119 : Blo 2137435 16242119 := bstep (se 1 (by rfl) ⟨12181589, by rfl⟩ : syracuseStep 16242119 = 24363179) B24363179
theorem B10828079 : Blo 2137435 10828079 := bstep (se 1 (by rfl) ⟨8121059, by rfl⟩ : syracuseStep 10828079 = 16242119) B16242119
theorem B7218719 : Blo 2137435 7218719 := bstep (se 1 (by rfl) ⟨5414039, by rfl⟩ : syracuseStep 7218719 = 10828079) B10828079
theorem B4812479 : Blo 2137435 4812479 := bstep (se 1 (by rfl) ⟨3609359, by rfl⟩ : syracuseStep 4812479 = 7218719) B7218719
theorem B3208319 : Blo 2137435 3208319 := bstep (se 1 (by rfl) ⟨2406239, by rfl⟩ : syracuseStep 3208319 = 4812479) B4812479
theorem B2138879 : Blo 2137435 2138879 := bstep (se 1 (by rfl) ⟨1604159, by rfl⟩ : syracuseStep 2138879 = 3208319) B3208319
theorem B3208325 : Blo 2137435 3208325 := bbase (se 4 (by rfl) ⟨300780, by rfl⟩ : syracuseStep 3208325 = 601561) (by norm_num)
theorem B2138883 : Blo 2137435 2138883 := bstep (se 1 (by rfl) ⟨1604162, by rfl⟩ : syracuseStep 2138883 = 3208325) B3208325
theorem B3609373 : Blo 2137435 3609373 := bbase (se 3 (by rfl) ⟨676757, by rfl⟩ : syracuseStep 3609373 = 1353515) (by norm_num)
theorem B4812497 : Blo 2137435 4812497 := bstep (se 2 (by rfl) ⟨1804686, by rfl⟩ : syracuseStep 4812497 = 3609373) B3609373
theorem B3208331 : Blo 2137435 3208331 := bstep (se 1 (by rfl) ⟨2406248, by rfl⟩ : syracuseStep 3208331 = 4812497) B4812497
theorem B2138887 : Blo 2137435 2138887 := bstep (se 1 (by rfl) ⟨1604165, by rfl⟩ : syracuseStep 2138887 = 3208331) B3208331
theorem B2406253 : Blo 2137435 2406253 := bbase (se 3 (by rfl) ⟨451172, by rfl⟩ : syracuseStep 2406253 = 902345) (by norm_num)
theorem B3208337 : Blo 2137435 3208337 := bstep (se 2 (by rfl) ⟨1203126, by rfl⟩ : syracuseStep 3208337 = 2406253) B2406253
theorem B2138891 : Blo 2137435 2138891 := bstep (se 1 (by rfl) ⟨1604168, by rfl⟩ : syracuseStep 2138891 = 3208337) B3208337
theorem B7218773 : Blo 2137435 7218773 := bbase (se 8 (by rfl) ⟨42297, by rfl⟩ : syracuseStep 7218773 = 84595) (by norm_num)
theorem B4812515 : Blo 2137435 4812515 := bstep (se 1 (by rfl) ⟨3609386, by rfl⟩ : syracuseStep 4812515 = 7218773) B7218773
theorem B3208343 : Blo 2137435 3208343 := bstep (se 1 (by rfl) ⟨2406257, by rfl⟩ : syracuseStep 3208343 = 4812515) B4812515
theorem B2138895 : Blo 2137435 2138895 := bstep (se 1 (by rfl) ⟨1604171, by rfl⟩ : syracuseStep 2138895 = 3208343) B3208343
theorem B3208349 : Blo 2137435 3208349 := bbase (se 3 (by rfl) ⟨601565, by rfl⟩ : syracuseStep 3208349 = 1203131) (by norm_num)
theorem B2138899 : Blo 2137435 2138899 := bstep (se 1 (by rfl) ⟨1604174, by rfl⟩ : syracuseStep 2138899 = 3208349) B3208349
theorem B4812533 : Blo 2137435 4812533 := bbase (se 5 (by rfl) ⟨225587, by rfl⟩ : syracuseStep 4812533 = 451175) (by norm_num)
theorem B3208355 : Blo 2137435 3208355 := bstep (se 1 (by rfl) ⟨2406266, by rfl⟩ : syracuseStep 3208355 = 4812533) B4812533
theorem B2138903 : Blo 2137435 2138903 := bstep (se 1 (by rfl) ⟨1604177, by rfl⟩ : syracuseStep 2138903 = 3208355) B3208355
theorem B4336181 : Blo 2137435 4336181 := bbase (se 5 (by rfl) ⟨203258, by rfl⟩ : syracuseStep 4336181 = 406517) (by norm_num)
theorem B2890787 : Blo 2137435 2890787 := bstep (se 1 (by rfl) ⟨2168090, by rfl⟩ : syracuseStep 2890787 = 4336181) B4336181
theorem B7708765 : Blo 2137435 7708765 := bstep (se 3 (by rfl) ⟨1445393, by rfl⟩ : syracuseStep 7708765 = 2890787) B2890787
theorem B10278353 : Blo 2137435 10278353 := bstep (se 2 (by rfl) ⟨3854382, by rfl⟩ : syracuseStep 10278353 = 7708765) B7708765
theorem B27408941 : Blo 2137435 27408941 := bstep (se 3 (by rfl) ⟨5139176, by rfl⟩ : syracuseStep 27408941 = 10278353) B10278353
theorem B18272627 : Blo 2137435 18272627 := bstep (se 1 (by rfl) ⟨13704470, by rfl⟩ : syracuseStep 18272627 = 27408941) B27408941
theorem B12181751 : Blo 2137435 12181751 := bstep (se 1 (by rfl) ⟨9136313, by rfl⟩ : syracuseStep 12181751 = 18272627) B18272627
theorem B8121167 : Blo 2137435 8121167 := bstep (se 1 (by rfl) ⟨6090875, by rfl⟩ : syracuseStep 8121167 = 12181751) B12181751
theorem B5414111 : Blo 2137435 5414111 := bstep (se 1 (by rfl) ⟨4060583, by rfl⟩ : syracuseStep 5414111 = 8121167) B8121167
theorem B3609407 : Blo 2137435 3609407 := bstep (se 1 (by rfl) ⟨2707055, by rfl⟩ : syracuseStep 3609407 = 5414111) B5414111
theorem B2406271 : Blo 2137435 2406271 := bstep (se 1 (by rfl) ⟨1804703, by rfl⟩ : syracuseStep 2406271 = 3609407) B3609407
theorem B3208361 : Blo 2137435 3208361 := bstep (se 2 (by rfl) ⟨1203135, by rfl⟩ : syracuseStep 3208361 = 2406271) B2406271
theorem B2138907 : Blo 2137435 2138907 := bstep (se 1 (by rfl) ⟨1604180, by rfl⟩ : syracuseStep 2138907 = 3208361) B3208361
theorem B4568165 : Blo 2137435 4568165 := bbase (se 4 (by rfl) ⟨428265, by rfl⟩ : syracuseStep 4568165 = 856531) (by norm_num)
theorem B3045443 : Blo 2137435 3045443 := bstep (se 1 (by rfl) ⟨2284082, by rfl⟩ : syracuseStep 3045443 = 4568165) B4568165
theorem B8121181 : Blo 2137435 8121181 := bstep (se 3 (by rfl) ⟨1522721, by rfl⟩ : syracuseStep 8121181 = 3045443) B3045443
theorem B10828241 : Blo 2137435 10828241 := bstep (se 2 (by rfl) ⟨4060590, by rfl⟩ : syracuseStep 10828241 = 8121181) B8121181
theorem B7218827 : Blo 2137435 7218827 := bstep (se 1 (by rfl) ⟨5414120, by rfl⟩ : syracuseStep 7218827 = 10828241) B10828241
theorem B4812551 : Blo 2137435 4812551 := bstep (se 1 (by rfl) ⟨3609413, by rfl⟩ : syracuseStep 4812551 = 7218827) B7218827
theorem B3208367 : Blo 2137435 3208367 := bstep (se 1 (by rfl) ⟨2406275, by rfl⟩ : syracuseStep 3208367 = 4812551) B4812551
theorem B2138911 : Blo 2137435 2138911 := bstep (se 1 (by rfl) ⟨1604183, by rfl⟩ : syracuseStep 2138911 = 3208367) B3208367
theorem B3208373 : Blo 2137435 3208373 := bbase (se 5 (by rfl) ⟨150392, by rfl⟩ : syracuseStep 3208373 = 300785) (by norm_num)
theorem B2138915 : Blo 2137435 2138915 := bstep (se 1 (by rfl) ⟨1604186, by rfl⟩ : syracuseStep 2138915 = 3208373) B3208373
theorem B5414141 : Blo 2137435 5414141 := bbase (se 3 (by rfl) ⟨1015151, by rfl⟩ : syracuseStep 5414141 = 2030303) (by norm_num)
theorem B3609427 : Blo 2137435 3609427 := bstep (se 1 (by rfl) ⟨2707070, by rfl⟩ : syracuseStep 3609427 = 5414141) B5414141
theorem B4812569 : Blo 2137435 4812569 := bstep (se 2 (by rfl) ⟨1804713, by rfl⟩ : syracuseStep 4812569 = 3609427) B3609427
theorem B3208379 : Blo 2137435 3208379 := bstep (se 1 (by rfl) ⟨2406284, by rfl⟩ : syracuseStep 3208379 = 4812569) B4812569
theorem B2138919 : Blo 2137435 2138919 := bstep (se 1 (by rfl) ⟨1604189, by rfl⟩ : syracuseStep 2138919 = 3208379) B3208379
theorem B2406289 : Blo 2137435 2406289 := bbase (se 2 (by rfl) ⟨902358, by rfl⟩ : syracuseStep 2406289 = 1804717) (by norm_num)
theorem B3208385 : Blo 2137435 3208385 := bstep (se 2 (by rfl) ⟨1203144, by rfl⟩ : syracuseStep 3208385 = 2406289) B2406289
theorem B2138923 : Blo 2137435 2138923 := bstep (se 1 (by rfl) ⟨1604192, by rfl⟩ : syracuseStep 2138923 = 3208385) B3208385
theorem B4060621 : Blo 2137435 4060621 := bbase (se 3 (by rfl) ⟨761366, by rfl⟩ : syracuseStep 4060621 = 1522733) (by norm_num)
theorem B5414161 : Blo 2137435 5414161 := bstep (se 2 (by rfl) ⟨2030310, by rfl⟩ : syracuseStep 5414161 = 4060621) B4060621
theorem B7218881 : Blo 2137435 7218881 := bstep (se 2 (by rfl) ⟨2707080, by rfl⟩ : syracuseStep 7218881 = 5414161) B5414161
theorem B4812587 : Blo 2137435 4812587 := bstep (se 1 (by rfl) ⟨3609440, by rfl⟩ : syracuseStep 4812587 = 7218881) B7218881
theorem B3208391 : Blo 2137435 3208391 := bstep (se 1 (by rfl) ⟨2406293, by rfl⟩ : syracuseStep 3208391 = 4812587) B4812587
theorem B2138927 : Blo 2137435 2138927 := bstep (se 1 (by rfl) ⟨1604195, by rfl⟩ : syracuseStep 2138927 = 3208391) B3208391
theorem B3208397 : Blo 2137435 3208397 := bbase (se 3 (by rfl) ⟨601574, by rfl⟩ : syracuseStep 3208397 = 1203149) (by norm_num)
theorem B2138931 : Blo 2137435 2138931 := bstep (se 1 (by rfl) ⟨1604198, by rfl⟩ : syracuseStep 2138931 = 3208397) B3208397
theorem B4812605 : Blo 2137435 4812605 := bbase (se 3 (by rfl) ⟨902363, by rfl⟩ : syracuseStep 4812605 = 1804727) (by norm_num)
theorem B3208403 : Blo 2137435 3208403 := bstep (se 1 (by rfl) ⟨2406302, by rfl⟩ : syracuseStep 3208403 = 4812605) B4812605
theorem B2138935 : Blo 2137435 2138935 := bstep (se 1 (by rfl) ⟨1604201, by rfl⟩ : syracuseStep 2138935 = 3208403) B3208403
theorem B3609461 : Blo 2137435 3609461 := bbase (se 5 (by rfl) ⟨169193, by rfl⟩ : syracuseStep 3609461 = 338387) (by norm_num)
theorem B2406307 : Blo 2137435 2406307 := bstep (se 1 (by rfl) ⟨1804730, by rfl⟩ : syracuseStep 2406307 = 3609461) B3609461
theorem B3208409 : Blo 2137435 3208409 := bstep (se 2 (by rfl) ⟨1203153, by rfl⟩ : syracuseStep 3208409 = 2406307) B2406307
theorem B2138939 : Blo 2137435 2138939 := bstep (se 1 (by rfl) ⟨1604204, by rfl⟩ : syracuseStep 2138939 = 3208409) B3208409
theorem B5209381 : Blo 2137435 5209381 := bbase (se 4 (by rfl) ⟨488379, by rfl⟩ : syracuseStep 5209381 = 976759) (by norm_num)
theorem B6945841 : Blo 2137435 6945841 := bstep (se 2 (by rfl) ⟨2604690, by rfl⟩ : syracuseStep 6945841 = 5209381) B5209381
theorem B37044485 : Blo 2137435 37044485 := bstep (se 4 (by rfl) ⟨3472920, by rfl⟩ : syracuseStep 37044485 = 6945841) B6945841
theorem B24696323 : Blo 2137435 24696323 := bstep (se 1 (by rfl) ⟨18522242, by rfl⟩ : syracuseStep 24696323 = 37044485) B37044485
theorem B16464215 : Blo 2137435 16464215 := bstep (se 1 (by rfl) ⟨12348161, by rfl⟩ : syracuseStep 16464215 = 24696323) B24696323
theorem B10976143 : Blo 2137435 10976143 := bstep (se 1 (by rfl) ⟨8232107, by rfl⟩ : syracuseStep 10976143 = 16464215) B16464215
theorem B14634857 : Blo 2137435 14634857 := bstep (se 2 (by rfl) ⟨5488071, by rfl⟩ : syracuseStep 14634857 = 10976143) B10976143
theorem B39026285 : Blo 2137435 39026285 := bstep (se 3 (by rfl) ⟨7317428, by rfl⟩ : syracuseStep 39026285 = 14634857) B14634857
theorem B26017523 : Blo 2137435 26017523 := bstep (se 1 (by rfl) ⟨19513142, by rfl⟩ : syracuseStep 26017523 = 39026285) B39026285
theorem B17345015 : Blo 2137435 17345015 := bstep (se 1 (by rfl) ⟨13008761, by rfl⟩ : syracuseStep 17345015 = 26017523) B26017523
theorem B11563343 : Blo 2137435 11563343 := bstep (se 1 (by rfl) ⟨8672507, by rfl⟩ : syracuseStep 11563343 = 17345015) B17345015
theorem B7708895 : Blo 2137435 7708895 := bstep (se 1 (by rfl) ⟨5781671, by rfl⟩ : syracuseStep 7708895 = 11563343) B11563343
theorem B5139263 : Blo 2137435 5139263 := bstep (se 1 (by rfl) ⟨3854447, by rfl⟩ : syracuseStep 5139263 = 7708895) B7708895
theorem B3426175 : Blo 2137435 3426175 := bstep (se 1 (by rfl) ⟨2569631, by rfl⟩ : syracuseStep 3426175 = 5139263) B5139263
theorem B4568233 : Blo 2137435 4568233 := bstep (se 2 (by rfl) ⟨1713087, by rfl⟩ : syracuseStep 4568233 = 3426175) B3426175
theorem B6090977 : Blo 2137435 6090977 := bstep (se 2 (by rfl) ⟨2284116, by rfl⟩ : syracuseStep 6090977 = 4568233) B4568233
theorem B16242605 : Blo 2137435 16242605 := bstep (se 3 (by rfl) ⟨3045488, by rfl⟩ : syracuseStep 16242605 = 6090977) B6090977
theorem B10828403 : Blo 2137435 10828403 := bstep (se 1 (by rfl) ⟨8121302, by rfl⟩ : syracuseStep 10828403 = 16242605) B16242605
theorem B7218935 : Blo 2137435 7218935 := bstep (se 1 (by rfl) ⟨5414201, by rfl⟩ : syracuseStep 7218935 = 10828403) B10828403
theorem B4812623 : Blo 2137435 4812623 := bstep (se 1 (by rfl) ⟨3609467, by rfl⟩ : syracuseStep 4812623 = 7218935) B7218935
theorem B3208415 : Blo 2137435 3208415 := bstep (se 1 (by rfl) ⟨2406311, by rfl⟩ : syracuseStep 3208415 = 4812623) B4812623
theorem B2138943 : Blo 2137435 2138943 := bstep (se 1 (by rfl) ⟨1604207, by rfl⟩ : syracuseStep 2138943 = 3208415) B3208415
theorem B3208421 : Blo 2137435 3208421 := bbase (se 4 (by rfl) ⟨300789, by rfl⟩ : syracuseStep 3208421 = 601579) (by norm_num)
theorem B2138947 : Blo 2137435 2138947 := bstep (se 1 (by rfl) ⟨1604210, by rfl⟩ : syracuseStep 2138947 = 3208421) B3208421
theorem B8790869 : Blo 2137435 8790869 := bbase (se 9 (by rfl) ⟨25754, by rfl⟩ : syracuseStep 8790869 = 51509) (by norm_num)
theorem B23442317 : Blo 2137435 23442317 := bstep (se 3 (by rfl) ⟨4395434, by rfl⟩ : syracuseStep 23442317 = 8790869) B8790869
theorem B15628211 : Blo 2137435 15628211 := bstep (se 1 (by rfl) ⟨11721158, by rfl⟩ : syracuseStep 15628211 = 23442317) B23442317
theorem B10418807 : Blo 2137435 10418807 := bstep (se 1 (by rfl) ⟨7814105, by rfl⟩ : syracuseStep 10418807 = 15628211) B15628211
theorem B6945871 : Blo 2137435 6945871 := bstep (se 1 (by rfl) ⟨5209403, by rfl⟩ : syracuseStep 6945871 = 10418807) B10418807
theorem B9261161 : Blo 2137435 9261161 := bstep (se 2 (by rfl) ⟨3472935, by rfl⟩ : syracuseStep 9261161 = 6945871) B6945871
theorem B6174107 : Blo 2137435 6174107 := bstep (se 1 (by rfl) ⟨4630580, by rfl⟩ : syracuseStep 6174107 = 9261161) B9261161
theorem B4116071 : Blo 2137435 4116071 := bstep (se 1 (by rfl) ⟨3087053, by rfl⟩ : syracuseStep 4116071 = 6174107) B6174107
theorem B2744047 : Blo 2137435 2744047 := bstep (se 1 (by rfl) ⟨2058035, by rfl⟩ : syracuseStep 2744047 = 4116071) B4116071
theorem B14634917 : Blo 2137435 14634917 := bstep (se 4 (by rfl) ⟨1372023, by rfl⟩ : syracuseStep 14634917 = 2744047) B2744047
theorem B9756611 : Blo 2137435 9756611 := bstep (se 1 (by rfl) ⟨7317458, by rfl⟩ : syracuseStep 9756611 = 14634917) B14634917
theorem B6504407 : Blo 2137435 6504407 := bstep (se 1 (by rfl) ⟨4878305, by rfl⟩ : syracuseStep 6504407 = 9756611) B9756611
theorem B4336271 : Blo 2137435 4336271 := bstep (se 1 (by rfl) ⟨3252203, by rfl⟩ : syracuseStep 4336271 = 6504407) B6504407
theorem B2890847 : Blo 2137435 2890847 := bstep (se 1 (by rfl) ⟨2168135, by rfl⟩ : syracuseStep 2890847 = 4336271) B4336271
theorem B7708925 : Blo 2137435 7708925 := bstep (se 3 (by rfl) ⟨1445423, by rfl⟩ : syracuseStep 7708925 = 2890847) B2890847
theorem B5139283 : Blo 2137435 5139283 := bstep (se 1 (by rfl) ⟨3854462, by rfl⟩ : syracuseStep 5139283 = 7708925) B7708925
theorem B6852377 : Blo 2137435 6852377 := bstep (se 2 (by rfl) ⟨2569641, by rfl⟩ : syracuseStep 6852377 = 5139283) B5139283
theorem B4568251 : Blo 2137435 4568251 := bstep (se 1 (by rfl) ⟨3426188, by rfl⟩ : syracuseStep 4568251 = 6852377) B6852377
theorem B6091001 : Blo 2137435 6091001 := bstep (se 2 (by rfl) ⟨2284125, by rfl⟩ : syracuseStep 6091001 = 4568251) B4568251
theorem B4060667 : Blo 2137435 4060667 := bstep (se 1 (by rfl) ⟨3045500, by rfl⟩ : syracuseStep 4060667 = 6091001) B6091001
theorem B2707111 : Blo 2137435 2707111 := bstep (se 1 (by rfl) ⟨2030333, by rfl⟩ : syracuseStep 2707111 = 4060667) B4060667
theorem B3609481 : Blo 2137435 3609481 := bstep (se 2 (by rfl) ⟨1353555, by rfl⟩ : syracuseStep 3609481 = 2707111) B2707111
theorem B4812641 : Blo 2137435 4812641 := bstep (se 2 (by rfl) ⟨1804740, by rfl⟩ : syracuseStep 4812641 = 3609481) B3609481
theorem B3208427 : Blo 2137435 3208427 := bstep (se 1 (by rfl) ⟨2406320, by rfl⟩ : syracuseStep 3208427 = 4812641) B4812641
theorem B2138951 : Blo 2137435 2138951 := bstep (se 1 (by rfl) ⟨1604213, by rfl⟩ : syracuseStep 2138951 = 3208427) B3208427
theorem B2406325 : Blo 2137435 2406325 := bbase (se 5 (by rfl) ⟨112796, by rfl⟩ : syracuseStep 2406325 = 225593) (by norm_num)
theorem B3208433 : Blo 2137435 3208433 := bstep (se 2 (by rfl) ⟨1203162, by rfl⟩ : syracuseStep 3208433 = 2406325) B2406325
theorem B2138955 : Blo 2137435 2138955 := bstep (se 1 (by rfl) ⟨1604216, by rfl⟩ : syracuseStep 2138955 = 3208433) B3208433
theorem B2707121 : Blo 2137435 2707121 := bbase (se 2 (by rfl) ⟨1015170, by rfl⟩ : syracuseStep 2707121 = 2030341) (by norm_num)
theorem B7218989 : Blo 2137435 7218989 := bstep (se 3 (by rfl) ⟨1353560, by rfl⟩ : syracuseStep 7218989 = 2707121) B2707121
theorem B4812659 : Blo 2137435 4812659 := bstep (se 1 (by rfl) ⟨3609494, by rfl⟩ : syracuseStep 4812659 = 7218989) B7218989
theorem B3208439 : Blo 2137435 3208439 := bstep (se 1 (by rfl) ⟨2406329, by rfl⟩ : syracuseStep 3208439 = 4812659) B4812659
theorem B2138959 : Blo 2137435 2138959 := bstep (se 1 (by rfl) ⟨1604219, by rfl⟩ : syracuseStep 2138959 = 3208439) B3208439
theorem B3208445 : Blo 2137435 3208445 := bbase (se 3 (by rfl) ⟨601583, by rfl⟩ : syracuseStep 3208445 = 1203167) (by norm_num)
theorem B2138963 : Blo 2137435 2138963 := bstep (se 1 (by rfl) ⟨1604222, by rfl⟩ : syracuseStep 2138963 = 3208445) B3208445
theorem B4812677 : Blo 2137435 4812677 := bbase (se 4 (by rfl) ⟨451188, by rfl⟩ : syracuseStep 4812677 = 902377) (by norm_num)
theorem B3208451 : Blo 2137435 3208451 := bstep (se 1 (by rfl) ⟨2406338, by rfl⟩ : syracuseStep 3208451 = 4812677) B4812677
theorem B2138967 : Blo 2137435 2138967 := bstep (se 1 (by rfl) ⟨1604225, by rfl⟩ : syracuseStep 2138967 = 3208451) B3208451
theorem B3426221 : Blo 2137435 3426221 := bbase (se 3 (by rfl) ⟨642416, by rfl⟩ : syracuseStep 3426221 = 1284833) (by norm_num)
theorem B2284147 : Blo 2137435 2284147 := bstep (se 1 (by rfl) ⟨1713110, by rfl⟩ : syracuseStep 2284147 = 3426221) B3426221
theorem B3045529 : Blo 2137435 3045529 := bstep (se 2 (by rfl) ⟨1142073, by rfl⟩ : syracuseStep 3045529 = 2284147) B2284147
theorem B4060705 : Blo 2137435 4060705 := bstep (se 2 (by rfl) ⟨1522764, by rfl⟩ : syracuseStep 4060705 = 3045529) B3045529
theorem B5414273 : Blo 2137435 5414273 := bstep (se 2 (by rfl) ⟨2030352, by rfl⟩ : syracuseStep 5414273 = 4060705) B4060705
theorem B3609515 : Blo 2137435 3609515 := bstep (se 1 (by rfl) ⟨2707136, by rfl⟩ : syracuseStep 3609515 = 5414273) B5414273
theorem B2406343 : Blo 2137435 2406343 := bstep (se 1 (by rfl) ⟨1804757, by rfl⟩ : syracuseStep 2406343 = 3609515) B3609515
theorem B3208457 : Blo 2137435 3208457 := bstep (se 2 (by rfl) ⟨1203171, by rfl⟩ : syracuseStep 3208457 = 2406343) B2406343
theorem B2138971 : Blo 2137435 2138971 := bstep (se 1 (by rfl) ⟨1604228, by rfl⟩ : syracuseStep 2138971 = 3208457) B3208457
theorem B10828565 : Blo 2137435 10828565 := bbase (se 6 (by rfl) ⟨253794, by rfl⟩ : syracuseStep 10828565 = 507589) (by norm_num)
theorem B7219043 : Blo 2137435 7219043 := bstep (se 1 (by rfl) ⟨5414282, by rfl⟩ : syracuseStep 7219043 = 10828565) B10828565
theorem B4812695 : Blo 2137435 4812695 := bstep (se 1 (by rfl) ⟨3609521, by rfl⟩ : syracuseStep 4812695 = 7219043) B7219043
theorem B3208463 : Blo 2137435 3208463 := bstep (se 1 (by rfl) ⟨2406347, by rfl⟩ : syracuseStep 3208463 = 4812695) B4812695
theorem B2138975 : Blo 2137435 2138975 := bstep (se 1 (by rfl) ⟨1604231, by rfl⟩ : syracuseStep 2138975 = 3208463) B3208463
theorem B3208469 : Blo 2137435 3208469 := bbase (se 6 (by rfl) ⟨75198, by rfl⟩ : syracuseStep 3208469 = 150397) (by norm_num)
theorem B2138979 : Blo 2137435 2138979 := bstep (se 1 (by rfl) ⟨1604234, by rfl⟩ : syracuseStep 2138979 = 3208469) B3208469
theorem B26018005 : Blo 2137435 26018005 := bbase (se 7 (by rfl) ⟨304898, by rfl⟩ : syracuseStep 26018005 = 609797) (by norm_num)
theorem B34690673 : Blo 2137435 34690673 := bstep (se 2 (by rfl) ⟨13009002, by rfl⟩ : syracuseStep 34690673 = 26018005) B26018005
theorem B23127115 : Blo 2137435 23127115 := bstep (se 1 (by rfl) ⟨17345336, by rfl⟩ : syracuseStep 23127115 = 34690673) B34690673
theorem B30836153 : Blo 2137435 30836153 := bstep (se 2 (by rfl) ⟨11563557, by rfl⟩ : syracuseStep 30836153 = 23127115) B23127115
theorem B20557435 : Blo 2137435 20557435 := bstep (se 1 (by rfl) ⟨15418076, by rfl⟩ : syracuseStep 20557435 = 30836153) B30836153
theorem B27409913 : Blo 2137435 27409913 := bstep (se 2 (by rfl) ⟨10278717, by rfl⟩ : syracuseStep 27409913 = 20557435) B20557435
theorem B18273275 : Blo 2137435 18273275 := bstep (se 1 (by rfl) ⟨13704956, by rfl⟩ : syracuseStep 18273275 = 27409913) B27409913
theorem B12182183 : Blo 2137435 12182183 := bstep (se 1 (by rfl) ⟨9136637, by rfl⟩ : syracuseStep 12182183 = 18273275) B18273275
theorem B8121455 : Blo 2137435 8121455 := bstep (se 1 (by rfl) ⟨6091091, by rfl⟩ : syracuseStep 8121455 = 12182183) B12182183
theorem B5414303 : Blo 2137435 5414303 := bstep (se 1 (by rfl) ⟨4060727, by rfl⟩ : syracuseStep 5414303 = 8121455) B8121455
theorem B3609535 : Blo 2137435 3609535 := bstep (se 1 (by rfl) ⟨2707151, by rfl⟩ : syracuseStep 3609535 = 5414303) B5414303
theorem B4812713 : Blo 2137435 4812713 := bstep (se 2 (by rfl) ⟨1804767, by rfl⟩ : syracuseStep 4812713 = 3609535) B3609535
theorem B3208475 : Blo 2137435 3208475 := bstep (se 1 (by rfl) ⟨2406356, by rfl⟩ : syracuseStep 3208475 = 4812713) B4812713
theorem B2138983 : Blo 2137435 2138983 := bstep (se 1 (by rfl) ⟨1604237, by rfl⟩ : syracuseStep 2138983 = 3208475) B3208475
theorem B2406361 : Blo 2137435 2406361 := bbase (se 2 (by rfl) ⟨902385, by rfl⟩ : syracuseStep 2406361 = 1804771) (by norm_num)
theorem B3208481 : Blo 2137435 3208481 := bstep (se 2 (by rfl) ⟨1203180, by rfl⟩ : syracuseStep 3208481 = 2406361) B2406361
theorem B2138987 : Blo 2137435 2138987 := bstep (se 1 (by rfl) ⟨1604240, by rfl⟩ : syracuseStep 2138987 = 3208481) B3208481
theorem B3045557 : Blo 2137435 3045557 := bbase (se 5 (by rfl) ⟨142760, by rfl⟩ : syracuseStep 3045557 = 285521) (by norm_num)
theorem B8121485 : Blo 2137435 8121485 := bstep (se 3 (by rfl) ⟨1522778, by rfl⟩ : syracuseStep 8121485 = 3045557) B3045557
theorem B5414323 : Blo 2137435 5414323 := bstep (se 1 (by rfl) ⟨4060742, by rfl⟩ : syracuseStep 5414323 = 8121485) B8121485
theorem B7219097 : Blo 2137435 7219097 := bstep (se 2 (by rfl) ⟨2707161, by rfl⟩ : syracuseStep 7219097 = 5414323) B5414323
theorem B4812731 : Blo 2137435 4812731 := bstep (se 1 (by rfl) ⟨3609548, by rfl⟩ : syracuseStep 4812731 = 7219097) B7219097
theorem B3208487 : Blo 2137435 3208487 := bstep (se 1 (by rfl) ⟨2406365, by rfl⟩ : syracuseStep 3208487 = 4812731) B4812731
theorem B2138991 : Blo 2137435 2138991 := bstep (se 1 (by rfl) ⟨1604243, by rfl⟩ : syracuseStep 2138991 = 3208487) B3208487
theorem B3208493 : Blo 2137435 3208493 := bbase (se 3 (by rfl) ⟨601592, by rfl⟩ : syracuseStep 3208493 = 1203185) (by norm_num)
theorem B2138995 : Blo 2137435 2138995 := bstep (se 1 (by rfl) ⟨1604246, by rfl⟩ : syracuseStep 2138995 = 3208493) B3208493
theorem B4812749 : Blo 2137435 4812749 := bbase (se 3 (by rfl) ⟨902390, by rfl⟩ : syracuseStep 4812749 = 1804781) (by norm_num)
theorem B3208499 : Blo 2137435 3208499 := bstep (se 1 (by rfl) ⟨2406374, by rfl⟩ : syracuseStep 3208499 = 4812749) B4812749
theorem B2138999 : Blo 2137435 2138999 := bstep (se 1 (by rfl) ⟨1604249, by rfl⟩ : syracuseStep 2138999 = 3208499) B3208499
theorem B2707177 : Blo 2137435 2707177 := bbase (se 2 (by rfl) ⟨1015191, by rfl⟩ : syracuseStep 2707177 = 2030383) (by norm_num)
theorem B3609569 : Blo 2137435 3609569 := bstep (se 2 (by rfl) ⟨1353588, by rfl⟩ : syracuseStep 3609569 = 2707177) B2707177
theorem B2406379 : Blo 2137435 2406379 := bstep (se 1 (by rfl) ⟨1804784, by rfl⟩ : syracuseStep 2406379 = 3609569) B3609569
theorem B3208505 : Blo 2137435 3208505 := bstep (se 2 (by rfl) ⟨1203189, by rfl⟩ : syracuseStep 3208505 = 2406379) B2406379
theorem B2139003 : Blo 2137435 2139003 := bstep (se 1 (by rfl) ⟨1604252, by rfl⟩ : syracuseStep 2139003 = 3208505) B3208505
theorem B13705109 : Blo 2137435 13705109 := bbase (se 6 (by rfl) ⟨321213, by rfl⟩ : syracuseStep 13705109 = 642427) (by norm_num)
theorem B9136739 : Blo 2137435 9136739 := bstep (se 1 (by rfl) ⟨6852554, by rfl⟩ : syracuseStep 9136739 = 13705109) B13705109
theorem B24364637 : Blo 2137435 24364637 := bstep (se 3 (by rfl) ⟨4568369, by rfl⟩ : syracuseStep 24364637 = 9136739) B9136739
theorem B16243091 : Blo 2137435 16243091 := bstep (se 1 (by rfl) ⟨12182318, by rfl⟩ : syracuseStep 16243091 = 24364637) B24364637
theorem B10828727 : Blo 2137435 10828727 := bstep (se 1 (by rfl) ⟨8121545, by rfl⟩ : syracuseStep 10828727 = 16243091) B16243091
theorem B7219151 : Blo 2137435 7219151 := bstep (se 1 (by rfl) ⟨5414363, by rfl⟩ : syracuseStep 7219151 = 10828727) B10828727
theorem B4812767 : Blo 2137435 4812767 := bstep (se 1 (by rfl) ⟨3609575, by rfl⟩ : syracuseStep 4812767 = 7219151) B7219151
theorem B3208511 : Blo 2137435 3208511 := bstep (se 1 (by rfl) ⟨2406383, by rfl⟩ : syracuseStep 3208511 = 4812767) B4812767
theorem B2139007 : Blo 2137435 2139007 := bstep (se 1 (by rfl) ⟨1604255, by rfl⟩ : syracuseStep 2139007 = 3208511) B3208511
theorem B3208517 : Blo 2137435 3208517 := bbase (se 4 (by rfl) ⟨300798, by rfl⟩ : syracuseStep 3208517 = 601597) (by norm_num)
theorem B2139011 : Blo 2137435 2139011 := bstep (se 1 (by rfl) ⟨1604258, by rfl⟩ : syracuseStep 2139011 = 3208517) B3208517
theorem B3609589 : Blo 2137435 3609589 := bbase (se 5 (by rfl) ⟨169199, by rfl⟩ : syracuseStep 3609589 = 338399) (by norm_num)
theorem B4812785 : Blo 2137435 4812785 := bstep (se 2 (by rfl) ⟨1804794, by rfl⟩ : syracuseStep 4812785 = 3609589) B3609589
theorem B3208523 : Blo 2137435 3208523 := bstep (se 1 (by rfl) ⟨2406392, by rfl⟩ : syracuseStep 3208523 = 4812785) B4812785
theorem B2139015 : Blo 2137435 2139015 := bstep (se 1 (by rfl) ⟨1604261, by rfl⟩ : syracuseStep 2139015 = 3208523) B3208523
theorem B2406397 : Blo 2137435 2406397 := bbase (se 3 (by rfl) ⟨451199, by rfl⟩ : syracuseStep 2406397 = 902399) (by norm_num)
theorem B3208529 : Blo 2137435 3208529 := bstep (se 2 (by rfl) ⟨1203198, by rfl⟩ : syracuseStep 3208529 = 2406397) B2406397
theorem B2139019 : Blo 2137435 2139019 := bstep (se 1 (by rfl) ⟨1604264, by rfl⟩ : syracuseStep 2139019 = 3208529) B3208529
theorem B7219205 : Blo 2137435 7219205 := bbase (se 4 (by rfl) ⟨676800, by rfl⟩ : syracuseStep 7219205 = 1353601) (by norm_num)
theorem B4812803 : Blo 2137435 4812803 := bstep (se 1 (by rfl) ⟨3609602, by rfl⟩ : syracuseStep 4812803 = 7219205) B7219205
theorem B3208535 : Blo 2137435 3208535 := bstep (se 1 (by rfl) ⟨2406401, by rfl⟩ : syracuseStep 3208535 = 4812803) B4812803
theorem B2139023 : Blo 2137435 2139023 := bstep (se 1 (by rfl) ⟨1604267, by rfl⟩ : syracuseStep 2139023 = 3208535) B3208535
theorem B3208541 : Blo 2137435 3208541 := bbase (se 3 (by rfl) ⟨601601, by rfl⟩ : syracuseStep 3208541 = 1203203) (by norm_num)
theorem B2139027 : Blo 2137435 2139027 := bstep (se 1 (by rfl) ⟨1604270, by rfl⟩ : syracuseStep 2139027 = 3208541) B3208541
theorem B4812821 : Blo 2137435 4812821 := bbase (se 6 (by rfl) ⟨112800, by rfl⟩ : syracuseStep 4812821 = 225601) (by norm_num)
theorem B3208547 : Blo 2137435 3208547 := bstep (se 1 (by rfl) ⟨2406410, by rfl⟩ : syracuseStep 3208547 = 4812821) B4812821
theorem B2139031 : Blo 2137435 2139031 := bstep (se 1 (by rfl) ⟨1604273, by rfl⟩ : syracuseStep 2139031 = 3208547) B3208547
theorem B8121653 : Blo 2137435 8121653 := bbase (se 5 (by rfl) ⟨380702, by rfl⟩ : syracuseStep 8121653 = 761405) (by norm_num)
theorem B5414435 : Blo 2137435 5414435 := bstep (se 1 (by rfl) ⟨4060826, by rfl⟩ : syracuseStep 5414435 = 8121653) B8121653
theorem B3609623 : Blo 2137435 3609623 := bstep (se 1 (by rfl) ⟨2707217, by rfl⟩ : syracuseStep 3609623 = 5414435) B5414435
theorem B2406415 : Blo 2137435 2406415 := bstep (se 1 (by rfl) ⟨1804811, by rfl⟩ : syracuseStep 2406415 = 3609623) B3609623
theorem B3208553 : Blo 2137435 3208553 := bstep (se 2 (by rfl) ⟨1203207, by rfl⟩ : syracuseStep 3208553 = 2406415) B2406415
theorem B2139035 : Blo 2137435 2139035 := bstep (se 1 (by rfl) ⟨1604276, by rfl⟩ : syracuseStep 2139035 = 3208553) B3208553
theorem B3854621 : Blo 2137435 3854621 := bbase (se 3 (by rfl) ⟨722741, by rfl⟩ : syracuseStep 3854621 = 1445483) (by norm_num)
theorem B2569747 : Blo 2137435 2569747 := bstep (se 1 (by rfl) ⟨1927310, by rfl⟩ : syracuseStep 2569747 = 3854621) B3854621
theorem B3426329 : Blo 2137435 3426329 := bstep (se 2 (by rfl) ⟨1284873, by rfl⟩ : syracuseStep 3426329 = 2569747) B2569747
theorem B2284219 : Blo 2137435 2284219 := bstep (se 1 (by rfl) ⟨1713164, by rfl⟩ : syracuseStep 2284219 = 3426329) B3426329
theorem B12182501 : Blo 2137435 12182501 := bstep (se 4 (by rfl) ⟨1142109, by rfl⟩ : syracuseStep 12182501 = 2284219) B2284219
theorem B8121667 : Blo 2137435 8121667 := bstep (se 1 (by rfl) ⟨6091250, by rfl⟩ : syracuseStep 8121667 = 12182501) B12182501
theorem B10828889 : Blo 2137435 10828889 := bstep (se 2 (by rfl) ⟨4060833, by rfl⟩ : syracuseStep 10828889 = 8121667) B8121667
theorem B7219259 : Blo 2137435 7219259 := bstep (se 1 (by rfl) ⟨5414444, by rfl⟩ : syracuseStep 7219259 = 10828889) B10828889
theorem B4812839 : Blo 2137435 4812839 := bstep (se 1 (by rfl) ⟨3609629, by rfl⟩ : syracuseStep 4812839 = 7219259) B7219259
theorem B3208559 : Blo 2137435 3208559 := bstep (se 1 (by rfl) ⟨2406419, by rfl⟩ : syracuseStep 3208559 = 4812839) B4812839
theorem B2139039 : Blo 2137435 2139039 := bstep (se 1 (by rfl) ⟨1604279, by rfl⟩ : syracuseStep 2139039 = 3208559) B3208559
theorem B3208565 : Blo 2137435 3208565 := bbase (se 5 (by rfl) ⟨150401, by rfl⟩ : syracuseStep 3208565 = 300803) (by norm_num)
theorem B2139043 : Blo 2137435 2139043 := bstep (se 1 (by rfl) ⟨1604282, by rfl⟩ : syracuseStep 2139043 = 3208565) B3208565
theorem B3045637 : Blo 2137435 3045637 := bbase (se 4 (by rfl) ⟨285528, by rfl⟩ : syracuseStep 3045637 = 571057) (by norm_num)
theorem B4060849 : Blo 2137435 4060849 := bstep (se 2 (by rfl) ⟨1522818, by rfl⟩ : syracuseStep 4060849 = 3045637) B3045637
theorem B5414465 : Blo 2137435 5414465 := bstep (se 2 (by rfl) ⟨2030424, by rfl⟩ : syracuseStep 5414465 = 4060849) B4060849
theorem B3609643 : Blo 2137435 3609643 := bstep (se 1 (by rfl) ⟨2707232, by rfl⟩ : syracuseStep 3609643 = 5414465) B5414465
theorem B4812857 : Blo 2137435 4812857 := bstep (se 2 (by rfl) ⟨1804821, by rfl⟩ : syracuseStep 4812857 = 3609643) B3609643
theorem B3208571 : Blo 2137435 3208571 := bstep (se 1 (by rfl) ⟨2406428, by rfl⟩ : syracuseStep 3208571 = 4812857) B4812857
theorem B2139047 : Blo 2137435 2139047 := bstep (se 1 (by rfl) ⟨1604285, by rfl⟩ : syracuseStep 2139047 = 3208571) B3208571
theorem B2406433 : Blo 2137435 2406433 := bbase (se 2 (by rfl) ⟨902412, by rfl⟩ : syracuseStep 2406433 = 1804825) (by norm_num)
theorem B3208577 : Blo 2137435 3208577 := bstep (se 2 (by rfl) ⟨1203216, by rfl⟩ : syracuseStep 3208577 = 2406433) B2406433
theorem B2139051 : Blo 2137435 2139051 := bstep (se 1 (by rfl) ⟨1604288, by rfl⟩ : syracuseStep 2139051 = 3208577) B3208577
theorem B5414485 : Blo 2137435 5414485 := bbase (se 8 (by rfl) ⟨31725, by rfl⟩ : syracuseStep 5414485 = 63451) (by norm_num)
theorem B7219313 : Blo 2137435 7219313 := bstep (se 2 (by rfl) ⟨2707242, by rfl⟩ : syracuseStep 7219313 = 5414485) B5414485
theorem B4812875 : Blo 2137435 4812875 := bstep (se 1 (by rfl) ⟨3609656, by rfl⟩ : syracuseStep 4812875 = 7219313) B7219313
theorem B3208583 : Blo 2137435 3208583 := bstep (se 1 (by rfl) ⟨2406437, by rfl⟩ : syracuseStep 3208583 = 4812875) B4812875
theorem B2139055 : Blo 2137435 2139055 := bstep (se 1 (by rfl) ⟨1604291, by rfl⟩ : syracuseStep 2139055 = 3208583) B3208583
theorem B3208589 : Blo 2137435 3208589 := bbase (se 3 (by rfl) ⟨601610, by rfl⟩ : syracuseStep 3208589 = 1203221) (by norm_num)
theorem B2139059 : Blo 2137435 2139059 := bstep (se 1 (by rfl) ⟨1604294, by rfl⟩ : syracuseStep 2139059 = 3208589) B3208589
theorem B4812893 : Blo 2137435 4812893 := bbase (se 3 (by rfl) ⟨902417, by rfl⟩ : syracuseStep 4812893 = 1804835) (by norm_num)
theorem B3208595 : Blo 2137435 3208595 := bstep (se 1 (by rfl) ⟨2406446, by rfl⟩ : syracuseStep 3208595 = 4812893) B4812893
theorem B2139063 : Blo 2137435 2139063 := bstep (se 1 (by rfl) ⟨1604297, by rfl⟩ : syracuseStep 2139063 = 3208595) B3208595
theorem B3609677 : Blo 2137435 3609677 := bbase (se 3 (by rfl) ⟨676814, by rfl⟩ : syracuseStep 3609677 = 1353629) (by norm_num)
theorem B2406451 : Blo 2137435 2406451 := bstep (se 1 (by rfl) ⟨1804838, by rfl⟩ : syracuseStep 2406451 = 3609677) B3609677
theorem B3208601 : Blo 2137435 3208601 := bstep (se 2 (by rfl) ⟨1203225, by rfl⟩ : syracuseStep 3208601 = 2406451) B2406451
theorem B2139067 : Blo 2137435 2139067 := bstep (se 1 (by rfl) ⟨1604300, by rfl⟩ : syracuseStep 2139067 = 3208601) B3208601
theorem B4630837 : Blo 2137435 4630837 := bbase (se 5 (by rfl) ⟨217070, by rfl⟩ : syracuseStep 4630837 = 434141) (by norm_num)
theorem B6174449 : Blo 2137435 6174449 := bstep (se 2 (by rfl) ⟨2315418, by rfl⟩ : syracuseStep 6174449 = 4630837) B4630837
theorem B4116299 : Blo 2137435 4116299 := bstep (se 1 (by rfl) ⟨3087224, by rfl⟩ : syracuseStep 4116299 = 6174449) B6174449
theorem B10976797 : Blo 2137435 10976797 := bstep (se 3 (by rfl) ⟨2058149, by rfl⟩ : syracuseStep 10976797 = 4116299) B4116299
theorem B14635729 : Blo 2137435 14635729 := bstep (se 2 (by rfl) ⟨5488398, by rfl⟩ : syracuseStep 14635729 = 10976797) B10976797
theorem B19514305 : Blo 2137435 19514305 := bstep (se 2 (by rfl) ⟨7317864, by rfl⟩ : syracuseStep 19514305 = 14635729) B14635729
theorem B26019073 : Blo 2137435 26019073 := bstep (se 2 (by rfl) ⟨9757152, by rfl⟩ : syracuseStep 26019073 = 19514305) B19514305
theorem B34692097 : Blo 2137435 34692097 := bstep (se 2 (by rfl) ⟨13009536, by rfl⟩ : syracuseStep 34692097 = 26019073) B26019073
theorem B46256129 : Blo 2137435 46256129 := bstep (se 2 (by rfl) ⟨17346048, by rfl⟩ : syracuseStep 46256129 = 34692097) B34692097
theorem B30837419 : Blo 2137435 30837419 := bstep (se 1 (by rfl) ⟨23128064, by rfl⟩ : syracuseStep 30837419 = 46256129) B46256129
theorem B20558279 : Blo 2137435 20558279 := bstep (se 1 (by rfl) ⟨15418709, by rfl⟩ : syracuseStep 20558279 = 30837419) B30837419
theorem B13705519 : Blo 2137435 13705519 := bstep (se 1 (by rfl) ⟨10279139, by rfl⟩ : syracuseStep 13705519 = 20558279) B20558279
theorem B18274025 : Blo 2137435 18274025 := bstep (se 2 (by rfl) ⟨6852759, by rfl⟩ : syracuseStep 18274025 = 13705519) B13705519
theorem B12182683 : Blo 2137435 12182683 := bstep (se 1 (by rfl) ⟨9137012, by rfl⟩ : syracuseStep 12182683 = 18274025) B18274025
theorem B16243577 : Blo 2137435 16243577 := bstep (se 2 (by rfl) ⟨6091341, by rfl⟩ : syracuseStep 16243577 = 12182683) B12182683
theorem B10829051 : Blo 2137435 10829051 := bstep (se 1 (by rfl) ⟨8121788, by rfl⟩ : syracuseStep 10829051 = 16243577) B16243577
theorem B7219367 : Blo 2137435 7219367 := bstep (se 1 (by rfl) ⟨5414525, by rfl⟩ : syracuseStep 7219367 = 10829051) B10829051
theorem B4812911 : Blo 2137435 4812911 := bstep (se 1 (by rfl) ⟨3609683, by rfl⟩ : syracuseStep 4812911 = 7219367) B7219367
theorem B3208607 : Blo 2137435 3208607 := bstep (se 1 (by rfl) ⟨2406455, by rfl⟩ : syracuseStep 3208607 = 4812911) B4812911
theorem B2139071 : Blo 2137435 2139071 := bstep (se 1 (by rfl) ⟨1604303, by rfl⟩ : syracuseStep 2139071 = 3208607) B3208607
theorem B3208613 : Blo 2137435 3208613 := bbase (se 4 (by rfl) ⟨300807, by rfl⟩ : syracuseStep 3208613 = 601615) (by norm_num)
theorem B2139075 : Blo 2137435 2139075 := bstep (se 1 (by rfl) ⟨1604306, by rfl⟩ : syracuseStep 2139075 = 3208613) B3208613
theorem B2707273 : Blo 2137435 2707273 := bbase (se 2 (by rfl) ⟨1015227, by rfl⟩ : syracuseStep 2707273 = 2030455) (by norm_num)
theorem B3609697 : Blo 2137435 3609697 := bstep (se 2 (by rfl) ⟨1353636, by rfl⟩ : syracuseStep 3609697 = 2707273) B2707273
theorem B4812929 : Blo 2137435 4812929 := bstep (se 2 (by rfl) ⟨1804848, by rfl⟩ : syracuseStep 4812929 = 3609697) B3609697
theorem B3208619 : Blo 2137435 3208619 := bstep (se 1 (by rfl) ⟨2406464, by rfl⟩ : syracuseStep 3208619 = 4812929) B4812929
theorem B2139079 : Blo 2137435 2139079 := bstep (se 1 (by rfl) ⟨1604309, by rfl⟩ : syracuseStep 2139079 = 3208619) B3208619
theorem B2406469 : Blo 2137435 2406469 := bbase (se 4 (by rfl) ⟨225606, by rfl⟩ : syracuseStep 2406469 = 451213) (by norm_num)
theorem B3208625 : Blo 2137435 3208625 := bstep (se 2 (by rfl) ⟨1203234, by rfl⟩ : syracuseStep 3208625 = 2406469) B2406469
theorem B2139083 : Blo 2137435 2139083 := bstep (se 1 (by rfl) ⟨1604312, by rfl⟩ : syracuseStep 2139083 = 3208625) B3208625
theorem B4060925 : Blo 2137435 4060925 := bbase (se 3 (by rfl) ⟨761423, by rfl⟩ : syracuseStep 4060925 = 1522847) (by norm_num)
theorem B2707283 : Blo 2137435 2707283 := bstep (se 1 (by rfl) ⟨2030462, by rfl⟩ : syracuseStep 2707283 = 4060925) B4060925
theorem B7219421 : Blo 2137435 7219421 := bstep (se 3 (by rfl) ⟨1353641, by rfl⟩ : syracuseStep 7219421 = 2707283) B2707283
theorem B4812947 : Blo 2137435 4812947 := bstep (se 1 (by rfl) ⟨3609710, by rfl⟩ : syracuseStep 4812947 = 7219421) B7219421
theorem B3208631 : Blo 2137435 3208631 := bstep (se 1 (by rfl) ⟨2406473, by rfl⟩ : syracuseStep 3208631 = 4812947) B4812947
theorem B2139087 : Blo 2137435 2139087 := bstep (se 1 (by rfl) ⟨1604315, by rfl⟩ : syracuseStep 2139087 = 3208631) B3208631
theorem B3208637 : Blo 2137435 3208637 := bbase (se 3 (by rfl) ⟨601619, by rfl⟩ : syracuseStep 3208637 = 1203239) (by norm_num)
theorem B2139091 : Blo 2137435 2139091 := bstep (se 1 (by rfl) ⟨1604318, by rfl⟩ : syracuseStep 2139091 = 3208637) B3208637
theorem B4812965 : Blo 2137435 4812965 := bbase (se 4 (by rfl) ⟨451215, by rfl⟩ : syracuseStep 4812965 = 902431) (by norm_num)
theorem B3208643 : Blo 2137435 3208643 := bstep (se 1 (by rfl) ⟨2406482, by rfl⟩ : syracuseStep 3208643 = 4812965) B4812965
theorem B2139095 : Blo 2137435 2139095 := bstep (se 1 (by rfl) ⟨1604321, by rfl⟩ : syracuseStep 2139095 = 3208643) B3208643
theorem B5414597 : Blo 2137435 5414597 := bbase (se 4 (by rfl) ⟨507618, by rfl⟩ : syracuseStep 5414597 = 1015237) (by norm_num)
theorem B3609731 : Blo 2137435 3609731 := bstep (se 1 (by rfl) ⟨2707298, by rfl⟩ : syracuseStep 3609731 = 5414597) B5414597
theorem B2406487 : Blo 2137435 2406487 := bstep (se 1 (by rfl) ⟨1804865, by rfl⟩ : syracuseStep 2406487 = 3609731) B3609731
theorem B3208649 : Blo 2137435 3208649 := bstep (se 2 (by rfl) ⟨1203243, by rfl⟩ : syracuseStep 3208649 = 2406487) B2406487
theorem B2139099 : Blo 2137435 2139099 := bstep (se 1 (by rfl) ⟨1604324, by rfl⟩ : syracuseStep 2139099 = 3208649) B3208649
theorem B21123413 : Blo 2137435 21123413 := bbase (se 10 (by rfl) ⟨30942, by rfl⟩ : syracuseStep 21123413 = 61885) (by norm_num)
theorem B14082275 : Blo 2137435 14082275 := bstep (se 1 (by rfl) ⟨10561706, by rfl⟩ : syracuseStep 14082275 = 21123413) B21123413
theorem B9388183 : Blo 2137435 9388183 := bstep (se 1 (by rfl) ⟨7041137, by rfl⟩ : syracuseStep 9388183 = 14082275) B14082275
theorem B12517577 : Blo 2137435 12517577 := bstep (se 2 (by rfl) ⟨4694091, by rfl⟩ : syracuseStep 12517577 = 9388183) B9388183
theorem B8345051 : Blo 2137435 8345051 := bstep (se 1 (by rfl) ⟨6258788, by rfl⟩ : syracuseStep 8345051 = 12517577) B12517577
theorem B5563367 : Blo 2137435 5563367 := bstep (se 1 (by rfl) ⟨4172525, by rfl⟩ : syracuseStep 5563367 = 8345051) B8345051
theorem B3708911 : Blo 2137435 3708911 := bstep (se 1 (by rfl) ⟨2781683, by rfl⟩ : syracuseStep 3708911 = 5563367) B5563367
theorem B2472607 : Blo 2137435 2472607 := bstep (se 1 (by rfl) ⟨1854455, by rfl⟩ : syracuseStep 2472607 = 3708911) B3708911
theorem B3296809 : Blo 2137435 3296809 := bstep (se 2 (by rfl) ⟨1236303, by rfl⟩ : syracuseStep 3296809 = 2472607) B2472607
theorem B4395745 : Blo 2137435 4395745 := bstep (se 2 (by rfl) ⟨1648404, by rfl⟩ : syracuseStep 4395745 = 3296809) B3296809
theorem B5860993 : Blo 2137435 5860993 := bstep (se 2 (by rfl) ⟨2197872, by rfl⟩ : syracuseStep 5860993 = 4395745) B4395745
theorem B7814657 : Blo 2137435 7814657 := bstep (se 2 (by rfl) ⟨2930496, by rfl⟩ : syracuseStep 7814657 = 5860993) B5860993
theorem B5209771 : Blo 2137435 5209771 := bstep (se 1 (by rfl) ⟨3907328, by rfl⟩ : syracuseStep 5209771 = 7814657) B7814657
theorem B6946361 : Blo 2137435 6946361 := bstep (se 2 (by rfl) ⟨2604885, by rfl⟩ : syracuseStep 6946361 = 5209771) B5209771
theorem B4630907 : Blo 2137435 4630907 := bstep (se 1 (by rfl) ⟨3473180, by rfl⟩ : syracuseStep 4630907 = 6946361) B6946361
theorem B3087271 : Blo 2137435 3087271 := bstep (se 1 (by rfl) ⟨2315453, by rfl⟩ : syracuseStep 3087271 = 4630907) B4630907
theorem B16465445 : Blo 2137435 16465445 := bstep (se 4 (by rfl) ⟨1543635, by rfl⟩ : syracuseStep 16465445 = 3087271) B3087271
theorem B10976963 : Blo 2137435 10976963 := bstep (se 1 (by rfl) ⟨8232722, by rfl⟩ : syracuseStep 10976963 = 16465445) B16465445
theorem B117087605 : Blo 2137435 117087605 := bstep (se 5 (by rfl) ⟨5488481, by rfl⟩ : syracuseStep 117087605 = 10976963) B10976963
theorem B78058403 : Blo 2137435 78058403 := bstep (se 1 (by rfl) ⟨58543802, by rfl⟩ : syracuseStep 78058403 = 117087605) B117087605
theorem B52038935 : Blo 2137435 52038935 := bstep (se 1 (by rfl) ⟨39029201, by rfl⟩ : syracuseStep 52038935 = 78058403) B78058403
theorem B34692623 : Blo 2137435 34692623 := bstep (se 1 (by rfl) ⟨26019467, by rfl⟩ : syracuseStep 34692623 = 52038935) B52038935
theorem B23128415 : Blo 2137435 23128415 := bstep (se 1 (by rfl) ⟨17346311, by rfl⟩ : syracuseStep 23128415 = 34692623) B34692623
theorem B15418943 : Blo 2137435 15418943 := bstep (se 1 (by rfl) ⟨11564207, by rfl⟩ : syracuseStep 15418943 = 23128415) B23128415
theorem B10279295 : Blo 2137435 10279295 := bstep (se 1 (by rfl) ⟨7709471, by rfl⟩ : syracuseStep 10279295 = 15418943) B15418943
theorem B6852863 : Blo 2137435 6852863 := bstep (se 1 (by rfl) ⟨5139647, by rfl⟩ : syracuseStep 6852863 = 10279295) B10279295
theorem B4568575 : Blo 2137435 4568575 := bstep (se 1 (by rfl) ⟨3426431, by rfl⟩ : syracuseStep 4568575 = 6852863) B6852863
theorem B6091433 : Blo 2137435 6091433 := bstep (se 2 (by rfl) ⟨2284287, by rfl⟩ : syracuseStep 6091433 = 4568575) B4568575
theorem B4060955 : Blo 2137435 4060955 := bstep (se 1 (by rfl) ⟨3045716, by rfl⟩ : syracuseStep 4060955 = 6091433) B6091433
theorem B10829213 : Blo 2137435 10829213 := bstep (se 3 (by rfl) ⟨2030477, by rfl⟩ : syracuseStep 10829213 = 4060955) B4060955
theorem B7219475 : Blo 2137435 7219475 := bstep (se 1 (by rfl) ⟨5414606, by rfl⟩ : syracuseStep 7219475 = 10829213) B10829213
theorem B4812983 : Blo 2137435 4812983 := bstep (se 1 (by rfl) ⟨3609737, by rfl⟩ : syracuseStep 4812983 = 7219475) B7219475
theorem B3208655 : Blo 2137435 3208655 := bstep (se 1 (by rfl) ⟨2406491, by rfl⟩ : syracuseStep 3208655 = 4812983) B4812983
theorem B2139103 : Blo 2137435 2139103 := bstep (se 1 (by rfl) ⟨1604327, by rfl⟩ : syracuseStep 2139103 = 3208655) B3208655
theorem B3208661 : Blo 2137435 3208661 := bbase (se 7 (by rfl) ⟨37601, by rfl⟩ : syracuseStep 3208661 = 75203) (by norm_num)
theorem B2139107 : Blo 2137435 2139107 := bstep (se 1 (by rfl) ⟨1604330, by rfl⟩ : syracuseStep 2139107 = 3208661) B3208661
theorem B8121941 : Blo 2137435 8121941 := bbase (se 8 (by rfl) ⟨47589, by rfl⟩ : syracuseStep 8121941 = 95179) (by norm_num)
theorem B5414627 : Blo 2137435 5414627 := bstep (se 1 (by rfl) ⟨4060970, by rfl⟩ : syracuseStep 5414627 = 8121941) B8121941
theorem B3609751 : Blo 2137435 3609751 := bstep (se 1 (by rfl) ⟨2707313, by rfl⟩ : syracuseStep 3609751 = 5414627) B5414627
theorem B4813001 : Blo 2137435 4813001 := bstep (se 2 (by rfl) ⟨1804875, by rfl⟩ : syracuseStep 4813001 = 3609751) B3609751
theorem B3208667 : Blo 2137435 3208667 := bstep (se 1 (by rfl) ⟨2406500, by rfl⟩ : syracuseStep 3208667 = 4813001) B4813001
theorem B2139111 : Blo 2137435 2139111 := bstep (se 1 (by rfl) ⟨1604333, by rfl⟩ : syracuseStep 2139111 = 3208667) B3208667
theorem B2406505 : Blo 2137435 2406505 := bbase (se 2 (by rfl) ⟨902439, by rfl⟩ : syracuseStep 2406505 = 1804879) (by norm_num)
theorem B3208673 : Blo 2137435 3208673 := bstep (se 2 (by rfl) ⟨1203252, by rfl⟩ : syracuseStep 3208673 = 2406505) B2406505
theorem B2139115 : Blo 2137435 2139115 := bstep (se 1 (by rfl) ⟨1604336, by rfl⟩ : syracuseStep 2139115 = 3208673) B3208673
theorem B3854765 : Blo 2137435 3854765 := bbase (se 3 (by rfl) ⟨722768, by rfl⟩ : syracuseStep 3854765 = 1445537) (by norm_num)
theorem B2569843 : Blo 2137435 2569843 := bstep (se 1 (by rfl) ⟨1927382, by rfl⟩ : syracuseStep 2569843 = 3854765) B3854765
theorem B3426457 : Blo 2137435 3426457 := bstep (se 2 (by rfl) ⟨1284921, by rfl⟩ : syracuseStep 3426457 = 2569843) B2569843
theorem B4568609 : Blo 2137435 4568609 := bstep (se 2 (by rfl) ⟨1713228, by rfl⟩ : syracuseStep 4568609 = 3426457) B3426457
theorem B12182957 : Blo 2137435 12182957 := bstep (se 3 (by rfl) ⟨2284304, by rfl⟩ : syracuseStep 12182957 = 4568609) B4568609
theorem B8121971 : Blo 2137435 8121971 := bstep (se 1 (by rfl) ⟨6091478, by rfl⟩ : syracuseStep 8121971 = 12182957) B12182957
theorem B5414647 : Blo 2137435 5414647 := bstep (se 1 (by rfl) ⟨4060985, by rfl⟩ : syracuseStep 5414647 = 8121971) B8121971
theorem B7219529 : Blo 2137435 7219529 := bstep (se 2 (by rfl) ⟨2707323, by rfl⟩ : syracuseStep 7219529 = 5414647) B5414647
theorem B4813019 : Blo 2137435 4813019 := bstep (se 1 (by rfl) ⟨3609764, by rfl⟩ : syracuseStep 4813019 = 7219529) B7219529
theorem B3208679 : Blo 2137435 3208679 := bstep (se 1 (by rfl) ⟨2406509, by rfl⟩ : syracuseStep 3208679 = 4813019) B4813019
theorem B2139119 : Blo 2137435 2139119 := bstep (se 1 (by rfl) ⟨1604339, by rfl⟩ : syracuseStep 2139119 = 3208679) B3208679
theorem B3208685 : Blo 2137435 3208685 := bbase (se 3 (by rfl) ⟨601628, by rfl⟩ : syracuseStep 3208685 = 1203257) (by norm_num)
theorem B2139123 : Blo 2137435 2139123 := bstep (se 1 (by rfl) ⟨1604342, by rfl⟩ : syracuseStep 2139123 = 3208685) B3208685
theorem B4813037 : Blo 2137435 4813037 := bbase (se 3 (by rfl) ⟨902444, by rfl⟩ : syracuseStep 4813037 = 1804889) (by norm_num)
theorem B3208691 : Blo 2137435 3208691 := bstep (se 1 (by rfl) ⟨2406518, by rfl⟩ : syracuseStep 3208691 = 4813037) B4813037
theorem B2139127 : Blo 2137435 2139127 := bstep (se 1 (by rfl) ⟨1604345, by rfl⟩ : syracuseStep 2139127 = 3208691) B3208691
theorem B3045757 : Blo 2137435 3045757 := bbase (se 3 (by rfl) ⟨571079, by rfl⟩ : syracuseStep 3045757 = 1142159) (by norm_num)
theorem B4061009 : Blo 2137435 4061009 := bstep (se 2 (by rfl) ⟨1522878, by rfl⟩ : syracuseStep 4061009 = 3045757) B3045757
theorem B2707339 : Blo 2137435 2707339 := bstep (se 1 (by rfl) ⟨2030504, by rfl⟩ : syracuseStep 2707339 = 4061009) B4061009
theorem B3609785 : Blo 2137435 3609785 := bstep (se 2 (by rfl) ⟨1353669, by rfl⟩ : syracuseStep 3609785 = 2707339) B2707339
theorem B2406523 : Blo 2137435 2406523 := bstep (se 1 (by rfl) ⟨1804892, by rfl⟩ : syracuseStep 2406523 = 3609785) B3609785
theorem B3208697 : Blo 2137435 3208697 := bstep (se 2 (by rfl) ⟨1203261, by rfl⟩ : syracuseStep 3208697 = 2406523) B2406523
theorem B2139131 : Blo 2137435 2139131 := bstep (se 1 (by rfl) ⟨1604348, by rfl⟩ : syracuseStep 2139131 = 3208697) B3208697
theorem B2168321 : Blo 2137435 2168321 := bbase (se 2 (by rfl) ⟨813120, by rfl⟩ : syracuseStep 2168321 = 1626241) (by norm_num)
theorem B5782189 : Blo 2137435 5782189 := bstep (se 3 (by rfl) ⟨1084160, by rfl⟩ : syracuseStep 5782189 = 2168321) B2168321
theorem B7709585 : Blo 2137435 7709585 := bstep (se 2 (by rfl) ⟨2891094, by rfl⟩ : syracuseStep 7709585 = 5782189) B5782189
theorem B82235573 : Blo 2137435 82235573 := bstep (se 5 (by rfl) ⟨3854792, by rfl⟩ : syracuseStep 82235573 = 7709585) B7709585
theorem B54823715 : Blo 2137435 54823715 := bstep (se 1 (by rfl) ⟨41117786, by rfl⟩ : syracuseStep 54823715 = 82235573) B82235573
theorem B36549143 : Blo 2137435 36549143 := bstep (se 1 (by rfl) ⟨27411857, by rfl⟩ : syracuseStep 36549143 = 54823715) B54823715
theorem B24366095 : Blo 2137435 24366095 := bstep (se 1 (by rfl) ⟨18274571, by rfl⟩ : syracuseStep 24366095 = 36549143) B36549143
theorem B16244063 : Blo 2137435 16244063 := bstep (se 1 (by rfl) ⟨12183047, by rfl⟩ : syracuseStep 16244063 = 24366095) B24366095
theorem B10829375 : Blo 2137435 10829375 := bstep (se 1 (by rfl) ⟨8122031, by rfl⟩ : syracuseStep 10829375 = 16244063) B16244063
theorem B7219583 : Blo 2137435 7219583 := bstep (se 1 (by rfl) ⟨5414687, by rfl⟩ : syracuseStep 7219583 = 10829375) B10829375
theorem B4813055 : Blo 2137435 4813055 := bstep (se 1 (by rfl) ⟨3609791, by rfl⟩ : syracuseStep 4813055 = 7219583) B7219583
theorem B3208703 : Blo 2137435 3208703 := bstep (se 1 (by rfl) ⟨2406527, by rfl⟩ : syracuseStep 3208703 = 4813055) B4813055
theorem B2139135 : Blo 2137435 2139135 := bstep (se 1 (by rfl) ⟨1604351, by rfl⟩ : syracuseStep 2139135 = 3208703) B3208703
theorem B3208709 : Blo 2137435 3208709 := bbase (se 4 (by rfl) ⟨300816, by rfl⟩ : syracuseStep 3208709 = 601633) (by norm_num)
theorem B2139139 : Blo 2137435 2139139 := bstep (se 1 (by rfl) ⟨1604354, by rfl⟩ : syracuseStep 2139139 = 3208709) B3208709
theorem B3609805 : Blo 2137435 3609805 := bbase (se 3 (by rfl) ⟨676838, by rfl⟩ : syracuseStep 3609805 = 1353677) (by norm_num)
theorem B4813073 : Blo 2137435 4813073 := bstep (se 2 (by rfl) ⟨1804902, by rfl⟩ : syracuseStep 4813073 = 3609805) B3609805
theorem B3208715 : Blo 2137435 3208715 := bstep (se 1 (by rfl) ⟨2406536, by rfl⟩ : syracuseStep 3208715 = 4813073) B4813073
theorem B2139143 : Blo 2137435 2139143 := bstep (se 1 (by rfl) ⟨1604357, by rfl⟩ : syracuseStep 2139143 = 3208715) B3208715
theorem B2406541 : Blo 2137435 2406541 := bbase (se 3 (by rfl) ⟨451226, by rfl⟩ : syracuseStep 2406541 = 902453) (by norm_num)
theorem B3208721 : Blo 2137435 3208721 := bstep (se 2 (by rfl) ⟨1203270, by rfl⟩ : syracuseStep 3208721 = 2406541) B2406541
theorem B2139147 : Blo 2137435 2139147 := bstep (se 1 (by rfl) ⟨1604360, by rfl⟩ : syracuseStep 2139147 = 3208721) B3208721
theorem B7219637 : Blo 2137435 7219637 := bbase (se 5 (by rfl) ⟨338420, by rfl⟩ : syracuseStep 7219637 = 676841) (by norm_num)
theorem B4813091 : Blo 2137435 4813091 := bstep (se 1 (by rfl) ⟨3609818, by rfl⟩ : syracuseStep 4813091 = 7219637) B7219637
theorem B3208727 : Blo 2137435 3208727 := bstep (se 1 (by rfl) ⟨2406545, by rfl⟩ : syracuseStep 3208727 = 4813091) B4813091
theorem B2139151 : Blo 2137435 2139151 := bstep (se 1 (by rfl) ⟨1604363, by rfl⟩ : syracuseStep 2139151 = 3208727) B3208727
theorem B3208733 : Blo 2137435 3208733 := bbase (se 3 (by rfl) ⟨601637, by rfl⟩ : syracuseStep 3208733 = 1203275) (by norm_num)
theorem B2139155 : Blo 2137435 2139155 := bstep (se 1 (by rfl) ⟨1604366, by rfl⟩ : syracuseStep 2139155 = 3208733) B3208733
theorem B4813109 : Blo 2137435 4813109 := bbase (se 5 (by rfl) ⟨225614, by rfl⟩ : syracuseStep 4813109 = 451229) (by norm_num)
theorem B3208739 : Blo 2137435 3208739 := bstep (se 1 (by rfl) ⟨2406554, by rfl⟩ : syracuseStep 3208739 = 4813109) B4813109
theorem B2139159 : Blo 2137435 2139159 := bstep (se 1 (by rfl) ⟨1604369, by rfl⟩ : syracuseStep 2139159 = 3208739) B3208739
theorem B4694221 : Blo 2137435 4694221 := bbase (se 3 (by rfl) ⟨880166, by rfl⟩ : syracuseStep 4694221 = 1760333) (by norm_num)
theorem B6258961 : Blo 2137435 6258961 := bstep (se 2 (by rfl) ⟨2347110, by rfl⟩ : syracuseStep 6258961 = 4694221) B4694221
theorem B8345281 : Blo 2137435 8345281 := bstep (se 2 (by rfl) ⟨3129480, by rfl⟩ : syracuseStep 8345281 = 6258961) B6258961
theorem B11127041 : Blo 2137435 11127041 := bstep (se 2 (by rfl) ⟨4172640, by rfl⟩ : syracuseStep 11127041 = 8345281) B8345281
theorem B7418027 : Blo 2137435 7418027 := bstep (se 1 (by rfl) ⟨5563520, by rfl⟩ : syracuseStep 7418027 = 11127041) B11127041
theorem B19781405 : Blo 2137435 19781405 := bstep (se 3 (by rfl) ⟨3709013, by rfl⟩ : syracuseStep 19781405 = 7418027) B7418027
theorem B13187603 : Blo 2137435 13187603 := bstep (se 1 (by rfl) ⟨9890702, by rfl⟩ : syracuseStep 13187603 = 19781405) B19781405
theorem B8791735 : Blo 2137435 8791735 := bstep (se 1 (by rfl) ⟨6593801, by rfl⟩ : syracuseStep 8791735 = 13187603) B13187603
theorem B11722313 : Blo 2137435 11722313 := bstep (se 2 (by rfl) ⟨4395867, by rfl⟩ : syracuseStep 11722313 = 8791735) B8791735
theorem B7814875 : Blo 2137435 7814875 := bstep (se 1 (by rfl) ⟨5861156, by rfl⟩ : syracuseStep 7814875 = 11722313) B11722313
theorem B10419833 : Blo 2137435 10419833 := bstep (se 2 (by rfl) ⟨3907437, by rfl⟩ : syracuseStep 10419833 = 7814875) B7814875
theorem B6946555 : Blo 2137435 6946555 := bstep (se 1 (by rfl) ⟨5209916, by rfl⟩ : syracuseStep 6946555 = 10419833) B10419833
theorem B9262073 : Blo 2137435 9262073 := bstep (se 2 (by rfl) ⟨3473277, by rfl⟩ : syracuseStep 9262073 = 6946555) B6946555
theorem B6174715 : Blo 2137435 6174715 := bstep (se 1 (by rfl) ⟨4631036, by rfl⟩ : syracuseStep 6174715 = 9262073) B9262073
theorem B8232953 : Blo 2137435 8232953 := bstep (se 2 (by rfl) ⟨3087357, by rfl⟩ : syracuseStep 8232953 = 6174715) B6174715
theorem B87818165 : Blo 2137435 87818165 := bstep (se 5 (by rfl) ⟨4116476, by rfl⟩ : syracuseStep 87818165 = 8232953) B8232953
theorem B58545443 : Blo 2137435 58545443 := bstep (se 1 (by rfl) ⟨43909082, by rfl⟩ : syracuseStep 58545443 = 87818165) B87818165
theorem B156121181 : Blo 2137435 156121181 := bstep (se 3 (by rfl) ⟨29272721, by rfl⟩ : syracuseStep 156121181 = 58545443) B58545443
theorem B104080787 : Blo 2137435 104080787 := bstep (se 1 (by rfl) ⟨78060590, by rfl⟩ : syracuseStep 104080787 = 156121181) B156121181
theorem B69387191 : Blo 2137435 69387191 := bstep (se 1 (by rfl) ⟨52040393, by rfl⟩ : syracuseStep 69387191 = 104080787) B104080787
theorem B46258127 : Blo 2137435 46258127 := bstep (se 1 (by rfl) ⟨34693595, by rfl⟩ : syracuseStep 46258127 = 69387191) B69387191
theorem B30838751 : Blo 2137435 30838751 := bstep (se 1 (by rfl) ⟨23129063, by rfl⟩ : syracuseStep 30838751 = 46258127) B46258127
theorem B20559167 : Blo 2137435 20559167 := bstep (se 1 (by rfl) ⟨15419375, by rfl⟩ : syracuseStep 20559167 = 30838751) B30838751
theorem B13706111 : Blo 2137435 13706111 := bstep (se 1 (by rfl) ⟨10279583, by rfl⟩ : syracuseStep 13706111 = 20559167) B20559167
theorem B9137407 : Blo 2137435 9137407 := bstep (se 1 (by rfl) ⟨6853055, by rfl⟩ : syracuseStep 9137407 = 13706111) B13706111
theorem B12183209 : Blo 2137435 12183209 := bstep (se 2 (by rfl) ⟨4568703, by rfl⟩ : syracuseStep 12183209 = 9137407) B9137407
theorem B8122139 : Blo 2137435 8122139 := bstep (se 1 (by rfl) ⟨6091604, by rfl⟩ : syracuseStep 8122139 = 12183209) B12183209
theorem B5414759 : Blo 2137435 5414759 := bstep (se 1 (by rfl) ⟨4061069, by rfl⟩ : syracuseStep 5414759 = 8122139) B8122139
theorem B3609839 : Blo 2137435 3609839 := bstep (se 1 (by rfl) ⟨2707379, by rfl⟩ : syracuseStep 3609839 = 5414759) B5414759
theorem B2406559 : Blo 2137435 2406559 := bstep (se 1 (by rfl) ⟨1804919, by rfl⟩ : syracuseStep 2406559 = 3609839) B3609839
theorem B3208745 : Blo 2137435 3208745 := bstep (se 2 (by rfl) ⟨1203279, by rfl⟩ : syracuseStep 3208745 = 2406559) B2406559
theorem B2139163 : Blo 2137435 2139163 := bstep (se 1 (by rfl) ⟨1604372, by rfl⟩ : syracuseStep 2139163 = 3208745) B3208745
theorem B30838805 : Blo 2137435 30838805 := bbase (se 6 (by rfl) ⟨722784, by rfl⟩ : syracuseStep 30838805 = 1445569) (by norm_num)
theorem B20559203 : Blo 2137435 20559203 := bstep (se 1 (by rfl) ⟨15419402, by rfl⟩ : syracuseStep 20559203 = 30838805) B30838805
theorem B13706135 : Blo 2137435 13706135 := bstep (se 1 (by rfl) ⟨10279601, by rfl⟩ : syracuseStep 13706135 = 20559203) B20559203
theorem B9137423 : Blo 2137435 9137423 := bstep (se 1 (by rfl) ⟨6853067, by rfl⟩ : syracuseStep 9137423 = 13706135) B13706135
theorem B6091615 : Blo 2137435 6091615 := bstep (se 1 (by rfl) ⟨4568711, by rfl⟩ : syracuseStep 6091615 = 9137423) B9137423
theorem B8122153 : Blo 2137435 8122153 := bstep (se 2 (by rfl) ⟨3045807, by rfl⟩ : syracuseStep 8122153 = 6091615) B6091615
theorem B10829537 : Blo 2137435 10829537 := bstep (se 2 (by rfl) ⟨4061076, by rfl⟩ : syracuseStep 10829537 = 8122153) B8122153
theorem B7219691 : Blo 2137435 7219691 := bstep (se 1 (by rfl) ⟨5414768, by rfl⟩ : syracuseStep 7219691 = 10829537) B10829537
theorem B4813127 : Blo 2137435 4813127 := bstep (se 1 (by rfl) ⟨3609845, by rfl⟩ : syracuseStep 4813127 = 7219691) B7219691
theorem B3208751 : Blo 2137435 3208751 := bstep (se 1 (by rfl) ⟨2406563, by rfl⟩ : syracuseStep 3208751 = 4813127) B4813127
theorem B2139167 : Blo 2137435 2139167 := bstep (se 1 (by rfl) ⟨1604375, by rfl⟩ : syracuseStep 2139167 = 3208751) B3208751
theorem B3208757 : Blo 2137435 3208757 := bbase (se 5 (by rfl) ⟨150410, by rfl⟩ : syracuseStep 3208757 = 300821) (by norm_num)
theorem B2139171 : Blo 2137435 2139171 := bstep (se 1 (by rfl) ⟨1604378, by rfl⟩ : syracuseStep 2139171 = 3208757) B3208757
theorem B5414789 : Blo 2137435 5414789 := bbase (se 4 (by rfl) ⟨507636, by rfl⟩ : syracuseStep 5414789 = 1015273) (by norm_num)
theorem B3609859 : Blo 2137435 3609859 := bstep (se 1 (by rfl) ⟨2707394, by rfl⟩ : syracuseStep 3609859 = 5414789) B5414789
theorem B4813145 : Blo 2137435 4813145 := bstep (se 2 (by rfl) ⟨1804929, by rfl⟩ : syracuseStep 4813145 = 3609859) B3609859
theorem B3208763 : Blo 2137435 3208763 := bstep (se 1 (by rfl) ⟨2406572, by rfl⟩ : syracuseStep 3208763 = 4813145) B4813145
theorem B2139175 : Blo 2137435 2139175 := bstep (se 1 (by rfl) ⟨1604381, by rfl⟩ : syracuseStep 2139175 = 3208763) B3208763
theorem B2406577 : Blo 2137435 2406577 := bbase (se 2 (by rfl) ⟨902466, by rfl⟩ : syracuseStep 2406577 = 1804933) (by norm_num)
theorem B3208769 : Blo 2137435 3208769 := bstep (se 2 (by rfl) ⟨1203288, by rfl⟩ : syracuseStep 3208769 = 2406577) B2406577
theorem B2139179 : Blo 2137435 2139179 := bstep (se 1 (by rfl) ⟨1604384, by rfl⟩ : syracuseStep 2139179 = 3208769) B3208769
theorem B2284373 : Blo 2137435 2284373 := bbase (se 9 (by rfl) ⟨6692, by rfl⟩ : syracuseStep 2284373 = 13385) (by norm_num)
theorem B6091661 : Blo 2137435 6091661 := bstep (se 3 (by rfl) ⟨1142186, by rfl⟩ : syracuseStep 6091661 = 2284373) B2284373
theorem B4061107 : Blo 2137435 4061107 := bstep (se 1 (by rfl) ⟨3045830, by rfl⟩ : syracuseStep 4061107 = 6091661) B6091661
theorem B5414809 : Blo 2137435 5414809 := bstep (se 2 (by rfl) ⟨2030553, by rfl⟩ : syracuseStep 5414809 = 4061107) B4061107
theorem B7219745 : Blo 2137435 7219745 := bstep (se 2 (by rfl) ⟨2707404, by rfl⟩ : syracuseStep 7219745 = 5414809) B5414809
theorem B4813163 : Blo 2137435 4813163 := bstep (se 1 (by rfl) ⟨3609872, by rfl⟩ : syracuseStep 4813163 = 7219745) B7219745
theorem B3208775 : Blo 2137435 3208775 := bstep (se 1 (by rfl) ⟨2406581, by rfl⟩ : syracuseStep 3208775 = 4813163) B4813163
theorem B2139183 : Blo 2137435 2139183 := bstep (se 1 (by rfl) ⟨1604387, by rfl⟩ : syracuseStep 2139183 = 3208775) B3208775
theorem B3208781 : Blo 2137435 3208781 := bbase (se 3 (by rfl) ⟨601646, by rfl⟩ : syracuseStep 3208781 = 1203293) (by norm_num)
theorem B2139187 : Blo 2137435 2139187 := bstep (se 1 (by rfl) ⟨1604390, by rfl⟩ : syracuseStep 2139187 = 3208781) B3208781
theorem B4813181 : Blo 2137435 4813181 := bbase (se 3 (by rfl) ⟨902471, by rfl⟩ : syracuseStep 4813181 = 1804943) (by norm_num)
theorem B3208787 : Blo 2137435 3208787 := bstep (se 1 (by rfl) ⟨2406590, by rfl⟩ : syracuseStep 3208787 = 4813181) B4813181
theorem B2139191 : Blo 2137435 2139191 := bstep (se 1 (by rfl) ⟨1604393, by rfl⟩ : syracuseStep 2139191 = 3208787) B3208787
theorem B3609893 : Blo 2137435 3609893 := bbase (se 4 (by rfl) ⟨338427, by rfl⟩ : syracuseStep 3609893 = 676855) (by norm_num)
theorem B2406595 : Blo 2137435 2406595 := bstep (se 1 (by rfl) ⟨1804946, by rfl⟩ : syracuseStep 2406595 = 3609893) B3609893
theorem B3208793 : Blo 2137435 3208793 := bstep (se 2 (by rfl) ⟨1203297, by rfl⟩ : syracuseStep 3208793 = 2406595) B2406595
theorem B2139195 : Blo 2137435 2139195 := bstep (se 1 (by rfl) ⟨1604396, by rfl⟩ : syracuseStep 2139195 = 3208793) B3208793
theorem B3045853 : Blo 2137435 3045853 := bbase (se 3 (by rfl) ⟨571097, by rfl⟩ : syracuseStep 3045853 = 1142195) (by norm_num)
theorem B16244549 : Blo 2137435 16244549 := bstep (se 4 (by rfl) ⟨1522926, by rfl⟩ : syracuseStep 16244549 = 3045853) B3045853
theorem B10829699 : Blo 2137435 10829699 := bstep (se 1 (by rfl) ⟨8122274, by rfl⟩ : syracuseStep 10829699 = 16244549) B16244549
theorem B7219799 : Blo 2137435 7219799 := bstep (se 1 (by rfl) ⟨5414849, by rfl⟩ : syracuseStep 7219799 = 10829699) B10829699
theorem B4813199 : Blo 2137435 4813199 := bstep (se 1 (by rfl) ⟨3609899, by rfl⟩ : syracuseStep 4813199 = 7219799) B7219799
theorem B3208799 : Blo 2137435 3208799 := bstep (se 1 (by rfl) ⟨2406599, by rfl⟩ : syracuseStep 3208799 = 4813199) B4813199
theorem B2139199 : Blo 2137435 2139199 := bstep (se 1 (by rfl) ⟨1604399, by rfl⟩ : syracuseStep 2139199 = 3208799) B3208799
theorem B3208805 : Blo 2137435 3208805 := bbase (se 4 (by rfl) ⟨300825, by rfl⟩ : syracuseStep 3208805 = 601651) (by norm_num)
theorem B2139203 : Blo 2137435 2139203 := bstep (se 1 (by rfl) ⟨1604402, by rfl⟩ : syracuseStep 2139203 = 3208805) B3208805
theorem B2439445 : Blo 2137435 2439445 := bbase (se 6 (by rfl) ⟨57174, by rfl⟩ : syracuseStep 2439445 = 114349) (by norm_num)
theorem B3252593 : Blo 2137435 3252593 := bstep (se 2 (by rfl) ⟨1219722, by rfl⟩ : syracuseStep 3252593 = 2439445) B2439445
theorem B8673581 : Blo 2137435 8673581 := bstep (se 3 (by rfl) ⟨1626296, by rfl⟩ : syracuseStep 8673581 = 3252593) B3252593
theorem B5782387 : Blo 2137435 5782387 := bstep (se 1 (by rfl) ⟨4336790, by rfl⟩ : syracuseStep 5782387 = 8673581) B8673581
theorem B7709849 : Blo 2137435 7709849 := bstep (se 2 (by rfl) ⟨2891193, by rfl⟩ : syracuseStep 7709849 = 5782387) B5782387
theorem B5139899 : Blo 2137435 5139899 := bstep (se 1 (by rfl) ⟨3854924, by rfl⟩ : syracuseStep 5139899 = 7709849) B7709849
theorem B3426599 : Blo 2137435 3426599 := bstep (se 1 (by rfl) ⟨2569949, by rfl⟩ : syracuseStep 3426599 = 5139899) B5139899
theorem B2284399 : Blo 2137435 2284399 := bstep (se 1 (by rfl) ⟨1713299, by rfl⟩ : syracuseStep 2284399 = 3426599) B3426599
theorem B3045865 : Blo 2137435 3045865 := bstep (se 2 (by rfl) ⟨1142199, by rfl⟩ : syracuseStep 3045865 = 2284399) B2284399
theorem B4061153 : Blo 2137435 4061153 := bstep (se 2 (by rfl) ⟨1522932, by rfl⟩ : syracuseStep 4061153 = 3045865) B3045865
theorem B2707435 : Blo 2137435 2707435 := bstep (se 1 (by rfl) ⟨2030576, by rfl⟩ : syracuseStep 2707435 = 4061153) B4061153
theorem B3609913 : Blo 2137435 3609913 := bstep (se 2 (by rfl) ⟨1353717, by rfl⟩ : syracuseStep 3609913 = 2707435) B2707435
theorem B4813217 : Blo 2137435 4813217 := bstep (se 2 (by rfl) ⟨1804956, by rfl⟩ : syracuseStep 4813217 = 3609913) B3609913
theorem B3208811 : Blo 2137435 3208811 := bstep (se 1 (by rfl) ⟨2406608, by rfl⟩ : syracuseStep 3208811 = 4813217) B4813217
theorem B2139207 : Blo 2137435 2139207 := bstep (se 1 (by rfl) ⟨1604405, by rfl⟩ : syracuseStep 2139207 = 3208811) B3208811
theorem B2406613 : Blo 2137435 2406613 := bbase (se 7 (by rfl) ⟨28202, by rfl⟩ : syracuseStep 2406613 = 56405) (by norm_num)
theorem B3208817 : Blo 2137435 3208817 := bstep (se 2 (by rfl) ⟨1203306, by rfl⟩ : syracuseStep 3208817 = 2406613) B2406613
theorem B2139211 : Blo 2137435 2139211 := bstep (se 1 (by rfl) ⟨1604408, by rfl⟩ : syracuseStep 2139211 = 3208817) B3208817
theorem B2707445 : Blo 2137435 2707445 := bbase (se 5 (by rfl) ⟨126911, by rfl⟩ : syracuseStep 2707445 = 253823) (by norm_num)
theorem B7219853 : Blo 2137435 7219853 := bstep (se 3 (by rfl) ⟨1353722, by rfl⟩ : syracuseStep 7219853 = 2707445) B2707445
theorem B4813235 : Blo 2137435 4813235 := bstep (se 1 (by rfl) ⟨3609926, by rfl⟩ : syracuseStep 4813235 = 7219853) B7219853
theorem B3208823 : Blo 2137435 3208823 := bstep (se 1 (by rfl) ⟨2406617, by rfl⟩ : syracuseStep 3208823 = 4813235) B4813235
theorem B2139215 : Blo 2137435 2139215 := bstep (se 1 (by rfl) ⟨1604411, by rfl⟩ : syracuseStep 2139215 = 3208823) B3208823
theorem B3208829 : Blo 2137435 3208829 := bbase (se 3 (by rfl) ⟨601655, by rfl⟩ : syracuseStep 3208829 = 1203311) (by norm_num)
theorem B2139219 : Blo 2137435 2139219 := bstep (se 1 (by rfl) ⟨1604414, by rfl⟩ : syracuseStep 2139219 = 3208829) B3208829
theorem B4813253 : Blo 2137435 4813253 := bbase (se 4 (by rfl) ⟨451242, by rfl⟩ : syracuseStep 4813253 = 902485) (by norm_num)
theorem B3208835 : Blo 2137435 3208835 := bstep (se 1 (by rfl) ⟨2406626, by rfl⟩ : syracuseStep 3208835 = 4813253) B4813253
theorem B2139223 : Blo 2137435 2139223 := bstep (se 1 (by rfl) ⟨1604417, by rfl⟩ : syracuseStep 2139223 = 3208835) B3208835
theorem B2569973 : Blo 2137435 2569973 := bbase (se 5 (by rfl) ⟨120467, by rfl⟩ : syracuseStep 2569973 = 240935) (by norm_num)
theorem B6853261 : Blo 2137435 6853261 := bstep (se 3 (by rfl) ⟨1284986, by rfl⟩ : syracuseStep 6853261 = 2569973) B2569973
theorem B9137681 : Blo 2137435 9137681 := bstep (se 2 (by rfl) ⟨3426630, by rfl⟩ : syracuseStep 9137681 = 6853261) B6853261
theorem B6091787 : Blo 2137435 6091787 := bstep (se 1 (by rfl) ⟨4568840, by rfl⟩ : syracuseStep 6091787 = 9137681) B9137681
theorem B4061191 : Blo 2137435 4061191 := bstep (se 1 (by rfl) ⟨3045893, by rfl⟩ : syracuseStep 4061191 = 6091787) B6091787
theorem B5414921 : Blo 2137435 5414921 := bstep (se 2 (by rfl) ⟨2030595, by rfl⟩ : syracuseStep 5414921 = 4061191) B4061191
theorem B3609947 : Blo 2137435 3609947 := bstep (se 1 (by rfl) ⟨2707460, by rfl⟩ : syracuseStep 3609947 = 5414921) B5414921
theorem B2406631 : Blo 2137435 2406631 := bstep (se 1 (by rfl) ⟨1804973, by rfl⟩ : syracuseStep 2406631 = 3609947) B3609947
theorem B3208841 : Blo 2137435 3208841 := bstep (se 2 (by rfl) ⟨1203315, by rfl⟩ : syracuseStep 3208841 = 2406631) B2406631
theorem B2139227 : Blo 2137435 2139227 := bstep (se 1 (by rfl) ⟨1604420, by rfl⟩ : syracuseStep 2139227 = 3208841) B3208841
theorem B10829861 : Blo 2137435 10829861 := bbase (se 4 (by rfl) ⟨1015299, by rfl⟩ : syracuseStep 10829861 = 2030599) (by norm_num)
theorem B7219907 : Blo 2137435 7219907 := bstep (se 1 (by rfl) ⟨5414930, by rfl⟩ : syracuseStep 7219907 = 10829861) B10829861
theorem B4813271 : Blo 2137435 4813271 := bstep (se 1 (by rfl) ⟨3609953, by rfl⟩ : syracuseStep 4813271 = 7219907) B7219907
theorem B3208847 : Blo 2137435 3208847 := bstep (se 1 (by rfl) ⟨2406635, by rfl⟩ : syracuseStep 3208847 = 4813271) B4813271
theorem B2139231 : Blo 2137435 2139231 := bstep (se 1 (by rfl) ⟨1604423, by rfl⟩ : syracuseStep 2139231 = 3208847) B3208847
theorem B3208853 : Blo 2137435 3208853 := bbase (se 6 (by rfl) ⟨75207, by rfl⟩ : syracuseStep 3208853 = 150415) (by norm_num)
theorem B2139235 : Blo 2137435 2139235 := bstep (se 1 (by rfl) ⟨1604426, by rfl⟩ : syracuseStep 2139235 = 3208853) B3208853
theorem B3854981 : Blo 2137435 3854981 := bbase (se 4 (by rfl) ⟨361404, by rfl⟩ : syracuseStep 3854981 = 722809) (by norm_num)
theorem B2569987 : Blo 2137435 2569987 := bstep (se 1 (by rfl) ⟨1927490, by rfl⟩ : syracuseStep 2569987 = 3854981) B3854981
theorem B13706597 : Blo 2137435 13706597 := bstep (se 4 (by rfl) ⟨1284993, by rfl⟩ : syracuseStep 13706597 = 2569987) B2569987
theorem B9137731 : Blo 2137435 9137731 := bstep (se 1 (by rfl) ⟨6853298, by rfl⟩ : syracuseStep 9137731 = 13706597) B13706597
theorem B12183641 : Blo 2137435 12183641 := bstep (se 2 (by rfl) ⟨4568865, by rfl⟩ : syracuseStep 12183641 = 9137731) B9137731
theorem B8122427 : Blo 2137435 8122427 := bstep (se 1 (by rfl) ⟨6091820, by rfl⟩ : syracuseStep 8122427 = 12183641) B12183641
theorem B5414951 : Blo 2137435 5414951 := bstep (se 1 (by rfl) ⟨4061213, by rfl⟩ : syracuseStep 5414951 = 8122427) B8122427
theorem B3609967 : Blo 2137435 3609967 := bstep (se 1 (by rfl) ⟨2707475, by rfl⟩ : syracuseStep 3609967 = 5414951) B5414951
theorem B4813289 : Blo 2137435 4813289 := bstep (se 2 (by rfl) ⟨1804983, by rfl⟩ : syracuseStep 4813289 = 3609967) B3609967
theorem B3208859 : Blo 2137435 3208859 := bstep (se 1 (by rfl) ⟨2406644, by rfl⟩ : syracuseStep 3208859 = 4813289) B4813289
theorem B2139239 : Blo 2137435 2139239 := bstep (se 1 (by rfl) ⟨1604429, by rfl⟩ : syracuseStep 2139239 = 3208859) B3208859
theorem B2406649 : Blo 2137435 2406649 := bbase (se 2 (by rfl) ⟨902493, by rfl⟩ : syracuseStep 2406649 = 1804987) (by norm_num)
theorem B3208865 : Blo 2137435 3208865 := bstep (se 2 (by rfl) ⟨1203324, by rfl⟩ : syracuseStep 3208865 = 2406649) B2406649
theorem B2139243 : Blo 2137435 2139243 := bstep (se 1 (by rfl) ⟨1604432, by rfl⟩ : syracuseStep 2139243 = 3208865) B3208865
theorem B9137765 : Blo 2137435 9137765 := bbase (se 4 (by rfl) ⟨856665, by rfl⟩ : syracuseStep 9137765 = 1713331) (by norm_num)
theorem B6091843 : Blo 2137435 6091843 := bstep (se 1 (by rfl) ⟨4568882, by rfl⟩ : syracuseStep 6091843 = 9137765) B9137765
theorem B8122457 : Blo 2137435 8122457 := bstep (se 2 (by rfl) ⟨3045921, by rfl⟩ : syracuseStep 8122457 = 6091843) B6091843
theorem B5414971 : Blo 2137435 5414971 := bstep (se 1 (by rfl) ⟨4061228, by rfl⟩ : syracuseStep 5414971 = 8122457) B8122457
theorem B7219961 : Blo 2137435 7219961 := bstep (se 2 (by rfl) ⟨2707485, by rfl⟩ : syracuseStep 7219961 = 5414971) B5414971
theorem B4813307 : Blo 2137435 4813307 := bstep (se 1 (by rfl) ⟨3609980, by rfl⟩ : syracuseStep 4813307 = 7219961) B7219961
theorem B3208871 : Blo 2137435 3208871 := bstep (se 1 (by rfl) ⟨2406653, by rfl⟩ : syracuseStep 3208871 = 4813307) B4813307
theorem B2139247 : Blo 2137435 2139247 := bstep (se 1 (by rfl) ⟨1604435, by rfl⟩ : syracuseStep 2139247 = 3208871) B3208871
theorem B3208877 : Blo 2137435 3208877 := bbase (se 3 (by rfl) ⟨601664, by rfl⟩ : syracuseStep 3208877 = 1203329) (by norm_num)
theorem B2139251 : Blo 2137435 2139251 := bstep (se 1 (by rfl) ⟨1604438, by rfl⟩ : syracuseStep 2139251 = 3208877) B3208877
theorem B4813325 : Blo 2137435 4813325 := bbase (se 3 (by rfl) ⟨902498, by rfl⟩ : syracuseStep 4813325 = 1804997) (by norm_num)
theorem B3208883 : Blo 2137435 3208883 := bstep (se 1 (by rfl) ⟨2406662, by rfl⟩ : syracuseStep 3208883 = 4813325) B4813325
theorem B2139255 : Blo 2137435 2139255 := bstep (se 1 (by rfl) ⟨1604441, by rfl⟩ : syracuseStep 2139255 = 3208883) B3208883
theorem B2707501 : Blo 2137435 2707501 := bbase (se 3 (by rfl) ⟨507656, by rfl⟩ : syracuseStep 2707501 = 1015313) (by norm_num)
theorem B3610001 : Blo 2137435 3610001 := bstep (se 2 (by rfl) ⟨1353750, by rfl⟩ : syracuseStep 3610001 = 2707501) B2707501
theorem B2406667 : Blo 2137435 2406667 := bstep (se 1 (by rfl) ⟨1805000, by rfl⟩ : syracuseStep 2406667 = 3610001) B3610001
theorem B3208889 : Blo 2137435 3208889 := bstep (se 2 (by rfl) ⟨1203333, by rfl⟩ : syracuseStep 3208889 = 2406667) B2406667
theorem B2139259 : Blo 2137435 2139259 := bstep (se 1 (by rfl) ⟨1604444, by rfl⟩ : syracuseStep 2139259 = 3208889) B3208889
theorem B3659261 : Blo 2137435 3659261 := bbase (se 3 (by rfl) ⟨686111, by rfl⟩ : syracuseStep 3659261 = 1372223) (by norm_num)
theorem B39032117 : Blo 2137435 39032117 := bstep (se 5 (by rfl) ⟨1829630, by rfl⟩ : syracuseStep 39032117 = 3659261) B3659261
theorem B26021411 : Blo 2137435 26021411 := bstep (se 1 (by rfl) ⟨19516058, by rfl⟩ : syracuseStep 26021411 = 39032117) B39032117
theorem B17347607 : Blo 2137435 17347607 := bstep (se 1 (by rfl) ⟨13010705, by rfl⟩ : syracuseStep 17347607 = 26021411) B26021411
theorem B11565071 : Blo 2137435 11565071 := bstep (se 1 (by rfl) ⟨8673803, by rfl⟩ : syracuseStep 11565071 = 17347607) B17347607
theorem B7710047 : Blo 2137435 7710047 := bstep (se 1 (by rfl) ⟨5782535, by rfl⟩ : syracuseStep 7710047 = 11565071) B11565071
theorem B5140031 : Blo 2137435 5140031 := bstep (se 1 (by rfl) ⟨3855023, by rfl⟩ : syracuseStep 5140031 = 7710047) B7710047
theorem B13706749 : Blo 2137435 13706749 := bstep (se 3 (by rfl) ⟨2570015, by rfl⟩ : syracuseStep 13706749 = 5140031) B5140031
theorem B18275665 : Blo 2137435 18275665 := bstep (se 2 (by rfl) ⟨6853374, by rfl⟩ : syracuseStep 18275665 = 13706749) B13706749
theorem B24367553 : Blo 2137435 24367553 := bstep (se 2 (by rfl) ⟨9137832, by rfl⟩ : syracuseStep 24367553 = 18275665) B18275665
theorem B16245035 : Blo 2137435 16245035 := bstep (se 1 (by rfl) ⟨12183776, by rfl⟩ : syracuseStep 16245035 = 24367553) B24367553
theorem B10830023 : Blo 2137435 10830023 := bstep (se 1 (by rfl) ⟨8122517, by rfl⟩ : syracuseStep 10830023 = 16245035) B16245035
theorem B7220015 : Blo 2137435 7220015 := bstep (se 1 (by rfl) ⟨5415011, by rfl⟩ : syracuseStep 7220015 = 10830023) B10830023
theorem B4813343 : Blo 2137435 4813343 := bstep (se 1 (by rfl) ⟨3610007, by rfl⟩ : syracuseStep 4813343 = 7220015) B7220015
theorem B3208895 : Blo 2137435 3208895 := bstep (se 1 (by rfl) ⟨2406671, by rfl⟩ : syracuseStep 3208895 = 4813343) B4813343
theorem B2139263 : Blo 2137435 2139263 := bstep (se 1 (by rfl) ⟨1604447, by rfl⟩ : syracuseStep 2139263 = 3208895) B3208895
theorem B3208901 : Blo 2137435 3208901 := bbase (se 4 (by rfl) ⟨300834, by rfl⟩ : syracuseStep 3208901 = 601669) (by norm_num)
theorem B2139267 : Blo 2137435 2139267 := bstep (se 1 (by rfl) ⟨1604450, by rfl⟩ : syracuseStep 2139267 = 3208901) B3208901
theorem B3610021 : Blo 2137435 3610021 := bbase (se 4 (by rfl) ⟨338439, by rfl⟩ : syracuseStep 3610021 = 676879) (by norm_num)
theorem B4813361 : Blo 2137435 4813361 := bstep (se 2 (by rfl) ⟨1805010, by rfl⟩ : syracuseStep 4813361 = 3610021) B3610021
theorem B3208907 : Blo 2137435 3208907 := bstep (se 1 (by rfl) ⟨2406680, by rfl⟩ : syracuseStep 3208907 = 4813361) B4813361
theorem B2139271 : Blo 2137435 2139271 := bstep (se 1 (by rfl) ⟨1604453, by rfl⟩ : syracuseStep 2139271 = 3208907) B3208907
theorem B2406685 : Blo 2137435 2406685 := bbase (se 3 (by rfl) ⟨451253, by rfl⟩ : syracuseStep 2406685 = 902507) (by norm_num)
theorem B3208913 : Blo 2137435 3208913 := bstep (se 2 (by rfl) ⟨1203342, by rfl⟩ : syracuseStep 3208913 = 2406685) B2406685
theorem B2139275 : Blo 2137435 2139275 := bstep (se 1 (by rfl) ⟨1604456, by rfl⟩ : syracuseStep 2139275 = 3208913) B3208913
theorem B7220069 : Blo 2137435 7220069 := bbase (se 4 (by rfl) ⟨676881, by rfl⟩ : syracuseStep 7220069 = 1353763) (by norm_num)
theorem B4813379 : Blo 2137435 4813379 := bstep (se 1 (by rfl) ⟨3610034, by rfl⟩ : syracuseStep 4813379 = 7220069) B7220069
theorem B3208919 : Blo 2137435 3208919 := bstep (se 1 (by rfl) ⟨2406689, by rfl⟩ : syracuseStep 3208919 = 4813379) B4813379
theorem B2139279 : Blo 2137435 2139279 := bstep (se 1 (by rfl) ⟨1604459, by rfl⟩ : syracuseStep 2139279 = 3208919) B3208919
theorem B3208925 : Blo 2137435 3208925 := bbase (se 3 (by rfl) ⟨601673, by rfl⟩ : syracuseStep 3208925 = 1203347) (by norm_num)
theorem B2139283 : Blo 2137435 2139283 := bstep (se 1 (by rfl) ⟨1604462, by rfl⟩ : syracuseStep 2139283 = 3208925) B3208925
theorem B4813397 : Blo 2137435 4813397 := bbase (se 8 (by rfl) ⟨28203, by rfl⟩ : syracuseStep 4813397 = 56407) (by norm_num)
theorem B3208931 : Blo 2137435 3208931 := bstep (se 1 (by rfl) ⟨2406698, by rfl⟩ : syracuseStep 3208931 = 4813397) B4813397
theorem B2139287 : Blo 2137435 2139287 := bstep (se 1 (by rfl) ⟨1604465, by rfl⟩ : syracuseStep 2139287 = 3208931) B3208931
theorem B3426733 : Blo 2137435 3426733 := bbase (se 3 (by rfl) ⟨642512, by rfl⟩ : syracuseStep 3426733 = 1285025) (by norm_num)
theorem B4568977 : Blo 2137435 4568977 := bstep (se 2 (by rfl) ⟨1713366, by rfl⟩ : syracuseStep 4568977 = 3426733) B3426733
theorem B6091969 : Blo 2137435 6091969 := bstep (se 2 (by rfl) ⟨2284488, by rfl⟩ : syracuseStep 6091969 = 4568977) B4568977
theorem B8122625 : Blo 2137435 8122625 := bstep (se 2 (by rfl) ⟨3045984, by rfl⟩ : syracuseStep 8122625 = 6091969) B6091969
theorem B5415083 : Blo 2137435 5415083 := bstep (se 1 (by rfl) ⟨4061312, by rfl⟩ : syracuseStep 5415083 = 8122625) B8122625
theorem B3610055 : Blo 2137435 3610055 := bstep (se 1 (by rfl) ⟨2707541, by rfl⟩ : syracuseStep 3610055 = 5415083) B5415083
theorem B2406703 : Blo 2137435 2406703 := bstep (se 1 (by rfl) ⟨1805027, by rfl⟩ : syracuseStep 2406703 = 3610055) B3610055
theorem B3208937 : Blo 2137435 3208937 := bstep (se 2 (by rfl) ⟨1203351, by rfl⟩ : syracuseStep 3208937 = 2406703) B2406703
theorem B2139291 : Blo 2137435 2139291 := bstep (se 1 (by rfl) ⟨1604468, by rfl⟩ : syracuseStep 2139291 = 3208937) B3208937
theorem B27413909 : Blo 2137435 27413909 := bbase (se 6 (by rfl) ⟨642513, by rfl⟩ : syracuseStep 27413909 = 1285027) (by norm_num)
theorem B18275939 : Blo 2137435 18275939 := bstep (se 1 (by rfl) ⟨13706954, by rfl⟩ : syracuseStep 18275939 = 27413909) B27413909
theorem B12183959 : Blo 2137435 12183959 := bstep (se 1 (by rfl) ⟨9137969, by rfl⟩ : syracuseStep 12183959 = 18275939) B18275939
theorem B8122639 : Blo 2137435 8122639 := bstep (se 1 (by rfl) ⟨6091979, by rfl⟩ : syracuseStep 8122639 = 12183959) B12183959
theorem B10830185 : Blo 2137435 10830185 := bstep (se 2 (by rfl) ⟨4061319, by rfl⟩ : syracuseStep 10830185 = 8122639) B8122639
theorem B7220123 : Blo 2137435 7220123 := bstep (se 1 (by rfl) ⟨5415092, by rfl⟩ : syracuseStep 7220123 = 10830185) B10830185
theorem B4813415 : Blo 2137435 4813415 := bstep (se 1 (by rfl) ⟨3610061, by rfl⟩ : syracuseStep 4813415 = 7220123) B7220123
theorem B3208943 : Blo 2137435 3208943 := bstep (se 1 (by rfl) ⟨2406707, by rfl⟩ : syracuseStep 3208943 = 4813415) B4813415
theorem B2139295 : Blo 2137435 2139295 := bstep (se 1 (by rfl) ⟨1604471, by rfl⟩ : syracuseStep 2139295 = 3208943) B3208943
theorem B3208949 : Blo 2137435 3208949 := bbase (se 5 (by rfl) ⟨150419, by rfl⟩ : syracuseStep 3208949 = 300839) (by norm_num)
theorem B2139299 : Blo 2137435 2139299 := bstep (se 1 (by rfl) ⟨1604474, by rfl⟩ : syracuseStep 2139299 = 3208949) B3208949
theorem B9138005 : Blo 2137435 9138005 := bbase (se 9 (by rfl) ⟨26771, by rfl⟩ : syracuseStep 9138005 = 53543) (by norm_num)
theorem B6092003 : Blo 2137435 6092003 := bstep (se 1 (by rfl) ⟨4569002, by rfl⟩ : syracuseStep 6092003 = 9138005) B9138005
theorem B4061335 : Blo 2137435 4061335 := bstep (se 1 (by rfl) ⟨3046001, by rfl⟩ : syracuseStep 4061335 = 6092003) B6092003
theorem B5415113 : Blo 2137435 5415113 := bstep (se 2 (by rfl) ⟨2030667, by rfl⟩ : syracuseStep 5415113 = 4061335) B4061335
theorem B3610075 : Blo 2137435 3610075 := bstep (se 1 (by rfl) ⟨2707556, by rfl⟩ : syracuseStep 3610075 = 5415113) B5415113
theorem B4813433 : Blo 2137435 4813433 := bstep (se 2 (by rfl) ⟨1805037, by rfl⟩ : syracuseStep 4813433 = 3610075) B3610075
theorem B3208955 : Blo 2137435 3208955 := bstep (se 1 (by rfl) ⟨2406716, by rfl⟩ : syracuseStep 3208955 = 4813433) B4813433
theorem B2139303 : Blo 2137435 2139303 := bstep (se 1 (by rfl) ⟨1604477, by rfl⟩ : syracuseStep 2139303 = 3208955) B3208955
theorem B2406721 : Blo 2137435 2406721 := bbase (se 2 (by rfl) ⟨902520, by rfl⟩ : syracuseStep 2406721 = 1805041) (by norm_num)
theorem B3208961 : Blo 2137435 3208961 := bstep (se 2 (by rfl) ⟨1203360, by rfl⟩ : syracuseStep 3208961 = 2406721) B2406721
theorem B2139307 : Blo 2137435 2139307 := bstep (se 1 (by rfl) ⟨1604480, by rfl⟩ : syracuseStep 2139307 = 3208961) B3208961
theorem B5415133 : Blo 2137435 5415133 := bbase (se 3 (by rfl) ⟨1015337, by rfl⟩ : syracuseStep 5415133 = 2030675) (by norm_num)
theorem B7220177 : Blo 2137435 7220177 := bstep (se 2 (by rfl) ⟨2707566, by rfl⟩ : syracuseStep 7220177 = 5415133) B5415133
theorem B4813451 : Blo 2137435 4813451 := bstep (se 1 (by rfl) ⟨3610088, by rfl⟩ : syracuseStep 4813451 = 7220177) B7220177
theorem B3208967 : Blo 2137435 3208967 := bstep (se 1 (by rfl) ⟨2406725, by rfl⟩ : syracuseStep 3208967 = 4813451) B4813451
theorem B2139311 : Blo 2137435 2139311 := bstep (se 1 (by rfl) ⟨1604483, by rfl⟩ : syracuseStep 2139311 = 3208967) B3208967
theorem B3208973 : Blo 2137435 3208973 := bbase (se 3 (by rfl) ⟨601682, by rfl⟩ : syracuseStep 3208973 = 1203365) (by norm_num)
theorem B2139315 : Blo 2137435 2139315 := bstep (se 1 (by rfl) ⟨1604486, by rfl⟩ : syracuseStep 2139315 = 3208973) B3208973
theorem B4813469 : Blo 2137435 4813469 := bbase (se 3 (by rfl) ⟨902525, by rfl⟩ : syracuseStep 4813469 = 1805051) (by norm_num)
theorem B3208979 : Blo 2137435 3208979 := bstep (se 1 (by rfl) ⟨2406734, by rfl⟩ : syracuseStep 3208979 = 4813469) B4813469
theorem B2139319 : Blo 2137435 2139319 := bstep (se 1 (by rfl) ⟨1604489, by rfl⟩ : syracuseStep 2139319 = 3208979) B3208979
theorem B3610109 : Blo 2137435 3610109 := bbase (se 3 (by rfl) ⟨676895, by rfl⟩ : syracuseStep 3610109 = 1353791) (by norm_num)
theorem B2406739 : Blo 2137435 2406739 := bstep (se 1 (by rfl) ⟨1805054, by rfl⟩ : syracuseStep 2406739 = 3610109) B3610109
theorem B3208985 : Blo 2137435 3208985 := bstep (se 2 (by rfl) ⟨1203369, by rfl⟩ : syracuseStep 3208985 = 2406739) B2406739
theorem B2139323 : Blo 2137435 2139323 := bstep (se 1 (by rfl) ⟨1604492, by rfl⟩ : syracuseStep 2139323 = 3208985) B3208985
theorem B4569053 : Blo 2137435 4569053 := bbase (se 3 (by rfl) ⟨856697, by rfl⟩ : syracuseStep 4569053 = 1713395) (by norm_num)
theorem B12184141 : Blo 2137435 12184141 := bstep (se 3 (by rfl) ⟨2284526, by rfl⟩ : syracuseStep 12184141 = 4569053) B4569053
theorem B16245521 : Blo 2137435 16245521 := bstep (se 2 (by rfl) ⟨6092070, by rfl⟩ : syracuseStep 16245521 = 12184141) B12184141
theorem B10830347 : Blo 2137435 10830347 := bstep (se 1 (by rfl) ⟨8122760, by rfl⟩ : syracuseStep 10830347 = 16245521) B16245521
theorem B7220231 : Blo 2137435 7220231 := bstep (se 1 (by rfl) ⟨5415173, by rfl⟩ : syracuseStep 7220231 = 10830347) B10830347
theorem B4813487 : Blo 2137435 4813487 := bstep (se 1 (by rfl) ⟨3610115, by rfl⟩ : syracuseStep 4813487 = 7220231) B7220231
theorem B3208991 : Blo 2137435 3208991 := bstep (se 1 (by rfl) ⟨2406743, by rfl⟩ : syracuseStep 3208991 = 4813487) B4813487
theorem B2139327 : Blo 2137435 2139327 := bstep (se 1 (by rfl) ⟨1604495, by rfl⟩ : syracuseStep 2139327 = 3208991) B3208991
theorem B3208997 : Blo 2137435 3208997 := bbase (se 4 (by rfl) ⟨300843, by rfl⟩ : syracuseStep 3208997 = 601687) (by norm_num)
theorem B2139331 : Blo 2137435 2139331 := bstep (se 1 (by rfl) ⟨1604498, by rfl⟩ : syracuseStep 2139331 = 3208997) B3208997
theorem B2707597 : Blo 2137435 2707597 := bbase (se 3 (by rfl) ⟨507674, by rfl⟩ : syracuseStep 2707597 = 1015349) (by norm_num)
theorem B3610129 : Blo 2137435 3610129 := bstep (se 2 (by rfl) ⟨1353798, by rfl⟩ : syracuseStep 3610129 = 2707597) B2707597
theorem B4813505 : Blo 2137435 4813505 := bstep (se 2 (by rfl) ⟨1805064, by rfl⟩ : syracuseStep 4813505 = 3610129) B3610129
theorem B3209003 : Blo 2137435 3209003 := bstep (se 1 (by rfl) ⟨2406752, by rfl⟩ : syracuseStep 3209003 = 4813505) B4813505
theorem B2139335 : Blo 2137435 2139335 := bstep (se 1 (by rfl) ⟨1604501, by rfl⟩ : syracuseStep 2139335 = 3209003) B3209003
theorem B2406757 : Blo 2137435 2406757 := bbase (se 4 (by rfl) ⟨225633, by rfl⟩ : syracuseStep 2406757 = 451267) (by norm_num)
theorem B3209009 : Blo 2137435 3209009 := bstep (se 2 (by rfl) ⟨1203378, by rfl⟩ : syracuseStep 3209009 = 2406757) B2406757
theorem B2139339 : Blo 2137435 2139339 := bstep (se 1 (by rfl) ⟨1604504, by rfl⟩ : syracuseStep 2139339 = 3209009) B3209009
theorem B6092117 : Blo 2137435 6092117 := bbase (se 13 (by rfl) ⟨1115, by rfl⟩ : syracuseStep 6092117 = 2231) (by norm_num)
theorem B4061411 : Blo 2137435 4061411 := bstep (se 1 (by rfl) ⟨3046058, by rfl⟩ : syracuseStep 4061411 = 6092117) B6092117
theorem B2707607 : Blo 2137435 2707607 := bstep (se 1 (by rfl) ⟨2030705, by rfl⟩ : syracuseStep 2707607 = 4061411) B4061411
theorem B7220285 : Blo 2137435 7220285 := bstep (se 3 (by rfl) ⟨1353803, by rfl⟩ : syracuseStep 7220285 = 2707607) B2707607
theorem B4813523 : Blo 2137435 4813523 := bstep (se 1 (by rfl) ⟨3610142, by rfl⟩ : syracuseStep 4813523 = 7220285) B7220285
theorem B3209015 : Blo 2137435 3209015 := bstep (se 1 (by rfl) ⟨2406761, by rfl⟩ : syracuseStep 3209015 = 4813523) B4813523
theorem B2139343 : Blo 2137435 2139343 := bstep (se 1 (by rfl) ⟨1604507, by rfl⟩ : syracuseStep 2139343 = 3209015) B3209015
theorem B3209021 : Blo 2137435 3209021 := bbase (se 3 (by rfl) ⟨601691, by rfl⟩ : syracuseStep 3209021 = 1203383) (by norm_num)
theorem B2139347 : Blo 2137435 2139347 := bstep (se 1 (by rfl) ⟨1604510, by rfl⟩ : syracuseStep 2139347 = 3209021) B3209021
theorem B4813541 : Blo 2137435 4813541 := bbase (se 4 (by rfl) ⟨451269, by rfl⟩ : syracuseStep 4813541 = 902539) (by norm_num)
theorem B3209027 : Blo 2137435 3209027 := bstep (se 1 (by rfl) ⟨2406770, by rfl⟩ : syracuseStep 3209027 = 4813541) B4813541
theorem B2139351 : Blo 2137435 2139351 := bstep (se 1 (by rfl) ⟨1604513, by rfl⟩ : syracuseStep 2139351 = 3209027) B3209027
theorem B5415245 : Blo 2137435 5415245 := bbase (se 3 (by rfl) ⟨1015358, by rfl⟩ : syracuseStep 5415245 = 2030717) (by norm_num)
theorem B3610163 : Blo 2137435 3610163 := bstep (se 1 (by rfl) ⟨2707622, by rfl⟩ : syracuseStep 3610163 = 5415245) B5415245
theorem B2406775 : Blo 2137435 2406775 := bstep (se 1 (by rfl) ⟨1805081, by rfl⟩ : syracuseStep 2406775 = 3610163) B3610163
theorem B3209033 : Blo 2137435 3209033 := bstep (se 2 (by rfl) ⟨1203387, by rfl⟩ : syracuseStep 3209033 = 2406775) B2406775
theorem B2139355 : Blo 2137435 2139355 := bstep (se 1 (by rfl) ⟨1604516, by rfl⟩ : syracuseStep 2139355 = 3209033) B3209033
theorem B2284561 : Blo 2137435 2284561 := bbase (se 2 (by rfl) ⟨856710, by rfl⟩ : syracuseStep 2284561 = 1713421) (by norm_num)
theorem B3046081 : Blo 2137435 3046081 := bstep (se 2 (by rfl) ⟨1142280, by rfl⟩ : syracuseStep 3046081 = 2284561) B2284561
theorem B4061441 : Blo 2137435 4061441 := bstep (se 2 (by rfl) ⟨1523040, by rfl⟩ : syracuseStep 4061441 = 3046081) B3046081
theorem B10830509 : Blo 2137435 10830509 := bstep (se 3 (by rfl) ⟨2030720, by rfl⟩ : syracuseStep 10830509 = 4061441) B4061441
theorem B7220339 : Blo 2137435 7220339 := bstep (se 1 (by rfl) ⟨5415254, by rfl⟩ : syracuseStep 7220339 = 10830509) B10830509
theorem B4813559 : Blo 2137435 4813559 := bstep (se 1 (by rfl) ⟨3610169, by rfl⟩ : syracuseStep 4813559 = 7220339) B7220339
theorem B3209039 : Blo 2137435 3209039 := bstep (se 1 (by rfl) ⟨2406779, by rfl⟩ : syracuseStep 3209039 = 4813559) B4813559
theorem B2139359 : Blo 2137435 2139359 := bstep (se 1 (by rfl) ⟨1604519, by rfl⟩ : syracuseStep 2139359 = 3209039) B3209039
theorem B3209045 : Blo 2137435 3209045 := bbase (se 9 (by rfl) ⟨9401, by rfl⟩ : syracuseStep 3209045 = 18803) (by norm_num)
theorem B2139363 : Blo 2137435 2139363 := bstep (se 1 (by rfl) ⟨1604522, by rfl⟩ : syracuseStep 2139363 = 3209045) B3209045
theorem B2570141 : Blo 2137435 2570141 := bbase (se 3 (by rfl) ⟨481901, by rfl⟩ : syracuseStep 2570141 = 963803) (by norm_num)
theorem B6853709 : Blo 2137435 6853709 := bstep (se 3 (by rfl) ⟨1285070, by rfl⟩ : syracuseStep 6853709 = 2570141) B2570141
theorem B4569139 : Blo 2137435 4569139 := bstep (se 1 (by rfl) ⟨3426854, by rfl⟩ : syracuseStep 4569139 = 6853709) B6853709
theorem B6092185 : Blo 2137435 6092185 := bstep (se 2 (by rfl) ⟨2284569, by rfl⟩ : syracuseStep 6092185 = 4569139) B4569139
theorem B8122913 : Blo 2137435 8122913 := bstep (se 2 (by rfl) ⟨3046092, by rfl⟩ : syracuseStep 8122913 = 6092185) B6092185
theorem B5415275 : Blo 2137435 5415275 := bstep (se 1 (by rfl) ⟨4061456, by rfl⟩ : syracuseStep 5415275 = 8122913) B8122913
theorem B3610183 : Blo 2137435 3610183 := bstep (se 1 (by rfl) ⟨2707637, by rfl⟩ : syracuseStep 3610183 = 5415275) B5415275
theorem B4813577 : Blo 2137435 4813577 := bstep (se 2 (by rfl) ⟨1805091, by rfl⟩ : syracuseStep 4813577 = 3610183) B3610183
theorem B3209051 : Blo 2137435 3209051 := bstep (se 1 (by rfl) ⟨2406788, by rfl⟩ : syracuseStep 3209051 = 4813577) B4813577
theorem B2139367 : Blo 2137435 2139367 := bstep (se 1 (by rfl) ⟨1604525, by rfl⟩ : syracuseStep 2139367 = 3209051) B3209051
theorem B2406793 : Blo 2137435 2406793 := bbase (se 2 (by rfl) ⟨902547, by rfl⟩ : syracuseStep 2406793 = 1805095) (by norm_num)
theorem B3209057 : Blo 2137435 3209057 := bstep (se 2 (by rfl) ⟨1203396, by rfl⟩ : syracuseStep 3209057 = 2406793) B2406793
theorem B2139371 : Blo 2137435 2139371 := bstep (se 1 (by rfl) ⟨1604528, by rfl⟩ : syracuseStep 2139371 = 3209057) B3209057
theorem B2605217 : Blo 2137435 2605217 := bbase (se 2 (by rfl) ⟨976956, by rfl⟩ : syracuseStep 2605217 = 1953913) (by norm_num)
theorem B6947245 : Blo 2137435 6947245 := bstep (se 3 (by rfl) ⟨1302608, by rfl⟩ : syracuseStep 6947245 = 2605217) B2605217
theorem B9262993 : Blo 2137435 9262993 := bstep (se 2 (by rfl) ⟨3473622, by rfl⟩ : syracuseStep 9262993 = 6947245) B6947245
theorem B12350657 : Blo 2137435 12350657 := bstep (se 2 (by rfl) ⟨4631496, by rfl⟩ : syracuseStep 12350657 = 9262993) B9262993
theorem B8233771 : Blo 2137435 8233771 := bstep (se 1 (by rfl) ⟨6175328, by rfl⟩ : syracuseStep 8233771 = 12350657) B12350657
theorem B10978361 : Blo 2137435 10978361 := bstep (se 2 (by rfl) ⟨4116885, by rfl⟩ : syracuseStep 10978361 = 8233771) B8233771
theorem B7318907 : Blo 2137435 7318907 := bstep (se 1 (by rfl) ⟨5489180, by rfl⟩ : syracuseStep 7318907 = 10978361) B10978361
theorem B4879271 : Blo 2137435 4879271 := bstep (se 1 (by rfl) ⟨3659453, by rfl⟩ : syracuseStep 4879271 = 7318907) B7318907
theorem B3252847 : Blo 2137435 3252847 := bstep (se 1 (by rfl) ⟨2439635, by rfl⟩ : syracuseStep 3252847 = 4879271) B4879271
theorem B4337129 : Blo 2137435 4337129 := bstep (se 2 (by rfl) ⟨1626423, by rfl⟩ : syracuseStep 4337129 = 3252847) B3252847
theorem B2891419 : Blo 2137435 2891419 := bstep (se 1 (by rfl) ⟨2168564, by rfl⟩ : syracuseStep 2891419 = 4337129) B4337129
theorem B61683605 : Blo 2137435 61683605 := bstep (se 6 (by rfl) ⟨1445709, by rfl⟩ : syracuseStep 61683605 = 2891419) B2891419
theorem B41122403 : Blo 2137435 41122403 := bstep (se 1 (by rfl) ⟨30841802, by rfl⟩ : syracuseStep 41122403 = 61683605) B61683605
theorem B27414935 : Blo 2137435 27414935 := bstep (se 1 (by rfl) ⟨20561201, by rfl⟩ : syracuseStep 27414935 = 41122403) B41122403
theorem B18276623 : Blo 2137435 18276623 := bstep (se 1 (by rfl) ⟨13707467, by rfl⟩ : syracuseStep 18276623 = 27414935) B27414935
theorem B12184415 : Blo 2137435 12184415 := bstep (se 1 (by rfl) ⟨9138311, by rfl⟩ : syracuseStep 12184415 = 18276623) B18276623
theorem B8122943 : Blo 2137435 8122943 := bstep (se 1 (by rfl) ⟨6092207, by rfl⟩ : syracuseStep 8122943 = 12184415) B12184415
theorem B5415295 : Blo 2137435 5415295 := bstep (se 1 (by rfl) ⟨4061471, by rfl⟩ : syracuseStep 5415295 = 8122943) B8122943
theorem B7220393 : Blo 2137435 7220393 := bstep (se 2 (by rfl) ⟨2707647, by rfl⟩ : syracuseStep 7220393 = 5415295) B5415295
theorem B4813595 : Blo 2137435 4813595 := bstep (se 1 (by rfl) ⟨3610196, by rfl⟩ : syracuseStep 4813595 = 7220393) B7220393
theorem B3209063 : Blo 2137435 3209063 := bstep (se 1 (by rfl) ⟨2406797, by rfl⟩ : syracuseStep 3209063 = 4813595) B4813595
theorem B2139375 : Blo 2137435 2139375 := bstep (se 1 (by rfl) ⟨1604531, by rfl⟩ : syracuseStep 2139375 = 3209063) B3209063
theorem B3209069 : Blo 2137435 3209069 := bbase (se 3 (by rfl) ⟨601700, by rfl⟩ : syracuseStep 3209069 = 1203401) (by norm_num)
theorem B2139379 : Blo 2137435 2139379 := bstep (se 1 (by rfl) ⟨1604534, by rfl⟩ : syracuseStep 2139379 = 3209069) B3209069
theorem B4813613 : Blo 2137435 4813613 := bbase (se 3 (by rfl) ⟨902552, by rfl⟩ : syracuseStep 4813613 = 1805105) (by norm_num)
theorem B3209075 : Blo 2137435 3209075 := bstep (se 1 (by rfl) ⟨2406806, by rfl⟩ : syracuseStep 3209075 = 4813613) B4813613
theorem B2139383 : Blo 2137435 2139383 := bstep (se 1 (by rfl) ⟨1604537, by rfl⟩ : syracuseStep 2139383 = 3209075) B3209075
theorem B6505733 : Blo 2137435 6505733 := bbase (se 4 (by rfl) ⟨609912, by rfl⟩ : syracuseStep 6505733 = 1219825) (by norm_num)
theorem B4337155 : Blo 2137435 4337155 := bstep (se 1 (by rfl) ⟨3252866, by rfl⟩ : syracuseStep 4337155 = 6505733) B6505733
theorem B5782873 : Blo 2137435 5782873 := bstep (se 2 (by rfl) ⟨2168577, by rfl⟩ : syracuseStep 5782873 = 4337155) B4337155
theorem B7710497 : Blo 2137435 7710497 := bstep (se 2 (by rfl) ⟨2891436, by rfl⟩ : syracuseStep 7710497 = 5782873) B5782873
theorem B5140331 : Blo 2137435 5140331 := bstep (se 1 (by rfl) ⟨3855248, by rfl⟩ : syracuseStep 5140331 = 7710497) B7710497
theorem B3426887 : Blo 2137435 3426887 := bstep (se 1 (by rfl) ⟨2570165, by rfl⟩ : syracuseStep 3426887 = 5140331) B5140331
theorem B9138365 : Blo 2137435 9138365 := bstep (se 3 (by rfl) ⟨1713443, by rfl⟩ : syracuseStep 9138365 = 3426887) B3426887
theorem B6092243 : Blo 2137435 6092243 := bstep (se 1 (by rfl) ⟨4569182, by rfl⟩ : syracuseStep 6092243 = 9138365) B9138365
theorem B4061495 : Blo 2137435 4061495 := bstep (se 1 (by rfl) ⟨3046121, by rfl⟩ : syracuseStep 4061495 = 6092243) B6092243
theorem B2707663 : Blo 2137435 2707663 := bstep (se 1 (by rfl) ⟨2030747, by rfl⟩ : syracuseStep 2707663 = 4061495) B4061495
theorem B3610217 : Blo 2137435 3610217 := bstep (se 2 (by rfl) ⟨1353831, by rfl⟩ : syracuseStep 3610217 = 2707663) B2707663
theorem B2406811 : Blo 2137435 2406811 := bstep (se 1 (by rfl) ⟨1805108, by rfl⟩ : syracuseStep 2406811 = 3610217) B3610217
theorem B3209081 : Blo 2137435 3209081 := bstep (se 2 (by rfl) ⟨1203405, by rfl⟩ : syracuseStep 3209081 = 2406811) B2406811
theorem B2139387 : Blo 2137435 2139387 := bstep (se 1 (by rfl) ⟨1604540, by rfl⟩ : syracuseStep 2139387 = 3209081) B3209081
theorem B10280677 : Blo 2137435 10280677 := bbase (se 4 (by rfl) ⟨963813, by rfl⟩ : syracuseStep 10280677 = 1927627) (by norm_num)
theorem B13707569 : Blo 2137435 13707569 := bstep (se 2 (by rfl) ⟨5140338, by rfl⟩ : syracuseStep 13707569 = 10280677) B10280677
theorem B36553517 : Blo 2137435 36553517 := bstep (se 3 (by rfl) ⟨6853784, by rfl⟩ : syracuseStep 36553517 = 13707569) B13707569
theorem B24369011 : Blo 2137435 24369011 := bstep (se 1 (by rfl) ⟨18276758, by rfl⟩ : syracuseStep 24369011 = 36553517) B36553517
theorem B16246007 : Blo 2137435 16246007 := bstep (se 1 (by rfl) ⟨12184505, by rfl⟩ : syracuseStep 16246007 = 24369011) B24369011
theorem B10830671 : Blo 2137435 10830671 := bstep (se 1 (by rfl) ⟨8123003, by rfl⟩ : syracuseStep 10830671 = 16246007) B16246007
theorem B7220447 : Blo 2137435 7220447 := bstep (se 1 (by rfl) ⟨5415335, by rfl⟩ : syracuseStep 7220447 = 10830671) B10830671
theorem B4813631 : Blo 2137435 4813631 := bstep (se 1 (by rfl) ⟨3610223, by rfl⟩ : syracuseStep 4813631 = 7220447) B7220447
theorem B3209087 : Blo 2137435 3209087 := bstep (se 1 (by rfl) ⟨2406815, by rfl⟩ : syracuseStep 3209087 = 4813631) B4813631
theorem B2139391 : Blo 2137435 2139391 := bstep (se 1 (by rfl) ⟨1604543, by rfl⟩ : syracuseStep 2139391 = 3209087) B3209087
theorem B3209093 : Blo 2137435 3209093 := bbase (se 4 (by rfl) ⟨300852, by rfl⟩ : syracuseStep 3209093 = 601705) (by norm_num)
theorem B2139395 : Blo 2137435 2139395 := bstep (se 1 (by rfl) ⟨1604546, by rfl⟩ : syracuseStep 2139395 = 3209093) B3209093
theorem B3610237 : Blo 2137435 3610237 := bbase (se 3 (by rfl) ⟨676919, by rfl⟩ : syracuseStep 3610237 = 1353839) (by norm_num)
theorem B4813649 : Blo 2137435 4813649 := bstep (se 2 (by rfl) ⟨1805118, by rfl⟩ : syracuseStep 4813649 = 3610237) B3610237
theorem B3209099 : Blo 2137435 3209099 := bstep (se 1 (by rfl) ⟨2406824, by rfl⟩ : syracuseStep 3209099 = 4813649) B4813649
theorem B2139399 : Blo 2137435 2139399 := bstep (se 1 (by rfl) ⟨1604549, by rfl⟩ : syracuseStep 2139399 = 3209099) B3209099
theorem B2406829 : Blo 2137435 2406829 := bbase (se 3 (by rfl) ⟨451280, by rfl⟩ : syracuseStep 2406829 = 902561) (by norm_num)
theorem B3209105 : Blo 2137435 3209105 := bstep (se 2 (by rfl) ⟨1203414, by rfl⟩ : syracuseStep 3209105 = 2406829) B2406829
theorem B2139403 : Blo 2137435 2139403 := bstep (se 1 (by rfl) ⟨1604552, by rfl⟩ : syracuseStep 2139403 = 3209105) B3209105
theorem B7220501 : Blo 2137435 7220501 := bbase (se 6 (by rfl) ⟨169230, by rfl⟩ : syracuseStep 7220501 = 338461) (by norm_num)
theorem B4813667 : Blo 2137435 4813667 := bstep (se 1 (by rfl) ⟨3610250, by rfl⟩ : syracuseStep 4813667 = 7220501) B7220501
theorem B3209111 : Blo 2137435 3209111 := bstep (se 1 (by rfl) ⟨2406833, by rfl⟩ : syracuseStep 3209111 = 4813667) B4813667
theorem B2139407 : Blo 2137435 2139407 := bstep (se 1 (by rfl) ⟨1604555, by rfl⟩ : syracuseStep 2139407 = 3209111) B3209111
theorem B3209117 : Blo 2137435 3209117 := bbase (se 3 (by rfl) ⟨601709, by rfl⟩ : syracuseStep 3209117 = 1203419) (by norm_num)
theorem B2139411 : Blo 2137435 2139411 := bstep (se 1 (by rfl) ⟨1604558, by rfl⟩ : syracuseStep 2139411 = 3209117) B3209117
theorem B4813685 : Blo 2137435 4813685 := bbase (se 5 (by rfl) ⟨225641, by rfl⟩ : syracuseStep 4813685 = 451283) (by norm_num)
theorem B3209123 : Blo 2137435 3209123 := bstep (se 1 (by rfl) ⟨2406842, by rfl⟩ : syracuseStep 3209123 = 4813685) B4813685
theorem B2139415 : Blo 2137435 2139415 := bstep (se 1 (by rfl) ⟨1604561, by rfl⟩ : syracuseStep 2139415 = 3209123) B3209123
theorem B2198197 : Blo 2137435 2198197 := bbase (se 5 (by rfl) ⟨103040, by rfl⟩ : syracuseStep 2198197 = 206081) (by norm_num)
theorem B11723717 : Blo 2137435 11723717 := bstep (se 4 (by rfl) ⟨1099098, by rfl⟩ : syracuseStep 11723717 = 2198197) B2198197
theorem B7815811 : Blo 2137435 7815811 := bstep (se 1 (by rfl) ⟨5861858, by rfl⟩ : syracuseStep 7815811 = 11723717) B11723717
theorem B10421081 : Blo 2137435 10421081 := bstep (se 2 (by rfl) ⟨3907905, by rfl⟩ : syracuseStep 10421081 = 7815811) B7815811
theorem B6947387 : Blo 2137435 6947387 := bstep (se 1 (by rfl) ⟨5210540, by rfl⟩ : syracuseStep 6947387 = 10421081) B10421081
theorem B4631591 : Blo 2137435 4631591 := bstep (se 1 (by rfl) ⟨3473693, by rfl⟩ : syracuseStep 4631591 = 6947387) B6947387
theorem B3087727 : Blo 2137435 3087727 := bstep (se 1 (by rfl) ⟨2315795, by rfl⟩ : syracuseStep 3087727 = 4631591) B4631591
theorem B16467877 : Blo 2137435 16467877 := bstep (se 4 (by rfl) ⟨1543863, by rfl⟩ : syracuseStep 16467877 = 3087727) B3087727
theorem B21957169 : Blo 2137435 21957169 := bstep (se 2 (by rfl) ⟨8233938, by rfl⟩ : syracuseStep 21957169 = 16467877) B16467877
theorem B29276225 : Blo 2137435 29276225 := bstep (se 2 (by rfl) ⟨10978584, by rfl⟩ : syracuseStep 29276225 = 21957169) B21957169
theorem B19517483 : Blo 2137435 19517483 := bstep (se 1 (by rfl) ⟨14638112, by rfl⟩ : syracuseStep 19517483 = 29276225) B29276225
theorem B52046621 : Blo 2137435 52046621 := bstep (se 3 (by rfl) ⟨9758741, by rfl⟩ : syracuseStep 52046621 = 19517483) B19517483
theorem B34697747 : Blo 2137435 34697747 := bstep (se 1 (by rfl) ⟨26023310, by rfl⟩ : syracuseStep 34697747 = 52046621) B52046621
theorem B23131831 : Blo 2137435 23131831 := bstep (se 1 (by rfl) ⟨17348873, by rfl⟩ : syracuseStep 23131831 = 34697747) B34697747
theorem B30842441 : Blo 2137435 30842441 := bstep (se 2 (by rfl) ⟨11565915, by rfl⟩ : syracuseStep 30842441 = 23131831) B23131831
theorem B20561627 : Blo 2137435 20561627 := bstep (se 1 (by rfl) ⟨15421220, by rfl⟩ : syracuseStep 20561627 = 30842441) B30842441
theorem B13707751 : Blo 2137435 13707751 := bstep (se 1 (by rfl) ⟨10280813, by rfl⟩ : syracuseStep 13707751 = 20561627) B20561627
theorem B18277001 : Blo 2137435 18277001 := bstep (se 2 (by rfl) ⟨6853875, by rfl⟩ : syracuseStep 18277001 = 13707751) B13707751
theorem B12184667 : Blo 2137435 12184667 := bstep (se 1 (by rfl) ⟨9138500, by rfl⟩ : syracuseStep 12184667 = 18277001) B18277001
theorem B8123111 : Blo 2137435 8123111 := bstep (se 1 (by rfl) ⟨6092333, by rfl⟩ : syracuseStep 8123111 = 12184667) B12184667
theorem B5415407 : Blo 2137435 5415407 := bstep (se 1 (by rfl) ⟨4061555, by rfl⟩ : syracuseStep 5415407 = 8123111) B8123111
theorem B3610271 : Blo 2137435 3610271 := bstep (se 1 (by rfl) ⟨2707703, by rfl⟩ : syracuseStep 3610271 = 5415407) B5415407
theorem B2406847 : Blo 2137435 2406847 := bstep (se 1 (by rfl) ⟨1805135, by rfl⟩ : syracuseStep 2406847 = 3610271) B3610271
theorem B3209129 : Blo 2137435 3209129 := bstep (se 2 (by rfl) ⟨1203423, by rfl⟩ : syracuseStep 3209129 = 2406847) B2406847
theorem B2139419 : Blo 2137435 2139419 := bstep (se 1 (by rfl) ⟨1604564, by rfl⟩ : syracuseStep 2139419 = 3209129) B3209129
theorem B8123125 : Blo 2137435 8123125 := bbase (se 5 (by rfl) ⟨380771, by rfl⟩ : syracuseStep 8123125 = 761543) (by norm_num)
theorem B10830833 : Blo 2137435 10830833 := bstep (se 2 (by rfl) ⟨4061562, by rfl⟩ : syracuseStep 10830833 = 8123125) B8123125
theorem B7220555 : Blo 2137435 7220555 := bstep (se 1 (by rfl) ⟨5415416, by rfl⟩ : syracuseStep 7220555 = 10830833) B10830833
theorem B4813703 : Blo 2137435 4813703 := bstep (se 1 (by rfl) ⟨3610277, by rfl⟩ : syracuseStep 4813703 = 7220555) B7220555
theorem B3209135 : Blo 2137435 3209135 := bstep (se 1 (by rfl) ⟨2406851, by rfl⟩ : syracuseStep 3209135 = 4813703) B4813703
theorem B2139423 : Blo 2137435 2139423 := bstep (se 1 (by rfl) ⟨1604567, by rfl⟩ : syracuseStep 2139423 = 3209135) B3209135
theorem B3209141 : Blo 2137435 3209141 := bbase (se 5 (by rfl) ⟨150428, by rfl⟩ : syracuseStep 3209141 = 300857) (by norm_num)
theorem B2139427 : Blo 2137435 2139427 := bstep (se 1 (by rfl) ⟨1604570, by rfl⟩ : syracuseStep 2139427 = 3209141) B3209141
theorem B5415437 : Blo 2137435 5415437 := bbase (se 3 (by rfl) ⟨1015394, by rfl⟩ : syracuseStep 5415437 = 2030789) (by norm_num)
theorem B3610291 : Blo 2137435 3610291 := bstep (se 1 (by rfl) ⟨2707718, by rfl⟩ : syracuseStep 3610291 = 5415437) B5415437
theorem B4813721 : Blo 2137435 4813721 := bstep (se 2 (by rfl) ⟨1805145, by rfl⟩ : syracuseStep 4813721 = 3610291) B3610291
theorem B3209147 : Blo 2137435 3209147 := bstep (se 1 (by rfl) ⟨2406860, by rfl⟩ : syracuseStep 3209147 = 4813721) B4813721
theorem B2139431 : Blo 2137435 2139431 := bstep (se 1 (by rfl) ⟨1604573, by rfl⟩ : syracuseStep 2139431 = 3209147) B3209147
theorem B2406865 : Blo 2137435 2406865 := bbase (se 2 (by rfl) ⟨902574, by rfl⟩ : syracuseStep 2406865 = 1805149) (by norm_num)
theorem B3209153 : Blo 2137435 3209153 := bstep (se 2 (by rfl) ⟨1203432, by rfl⟩ : syracuseStep 3209153 = 2406865) B2406865
theorem B2139435 : Blo 2137435 2139435 := bstep (se 1 (by rfl) ⟨1604576, by rfl⟩ : syracuseStep 2139435 = 3209153) B3209153
theorem C0 (j : ℕ) (h1 : 534358 ≤ j) (h2 : j ≤ 534858) : Blo 2137435 (4 * j + 3) := by
  interval_cases j
  · exact B2137435
  · exact B2137439
  · exact B2137443
  · exact B2137447
  · exact B2137451
  · exact B2137455
  · exact B2137459
  · exact B2137463
  · exact B2137467
  · exact B2137471
  · exact B2137475
  · exact B2137479
  · exact B2137483
  · exact B2137487
  · exact B2137491
  · exact B2137495
  · exact B2137499
  · exact B2137503
  · exact B2137507
  · exact B2137511
  · exact B2137515
  · exact B2137519
  · exact B2137523
  · exact B2137527
  · exact B2137531
  · exact B2137535
  · exact B2137539
  · exact B2137543
  · exact B2137547
  · exact B2137551
  · exact B2137555
  · exact B2137559
  · exact B2137563
  · exact B2137567
  · exact B2137571
  · exact B2137575
  · exact B2137579
  · exact B2137583
  · exact B2137587
  · exact B2137591
  · exact B2137595
  · exact B2137599
  · exact B2137603
  · exact B2137607
  · exact B2137611
  · exact B2137615
  · exact B2137619
  · exact B2137623
  · exact B2137627
  · exact B2137631
  · exact B2137635
  · exact B2137639
  · exact B2137643
  · exact B2137647
  · exact B2137651
  · exact B2137655
  · exact B2137659
  · exact B2137663
  · exact B2137667
  · exact B2137671
  · exact B2137675
  · exact B2137679
  · exact B2137683
  · exact B2137687
  · exact B2137691
  · exact B2137695
  · exact B2137699
  · exact B2137703
  · exact B2137707
  · exact B2137711
  · exact B2137715
  · exact B2137719
  · exact B2137723
  · exact B2137727
  · exact B2137731
  · exact B2137735
  · exact B2137739
  · exact B2137743
  · exact B2137747
  · exact B2137751
  · exact B2137755
  · exact B2137759
  · exact B2137763
  · exact B2137767
  · exact B2137771
  · exact B2137775
  · exact B2137779
  · exact B2137783
  · exact B2137787
  · exact B2137791
  · exact B2137795
  · exact B2137799
  · exact B2137803
  · exact B2137807
  · exact B2137811
  · exact B2137815
  · exact B2137819
  · exact B2137823
  · exact B2137827
  · exact B2137831
  · exact B2137835
  · exact B2137839
  · exact B2137843
  · exact B2137847
  · exact B2137851
  · exact B2137855
  · exact B2137859
  · exact B2137863
  · exact B2137867
  · exact B2137871
  · exact B2137875
  · exact B2137879
  · exact B2137883
  · exact B2137887
  · exact B2137891
  · exact B2137895
  · exact B2137899
  · exact B2137903
  · exact B2137907
  · exact B2137911
  · exact B2137915
  · exact B2137919
  · exact B2137923
  · exact B2137927
  · exact B2137931
  · exact B2137935
  · exact B2137939
  · exact B2137943
  · exact B2137947
  · exact B2137951
  · exact B2137955
  · exact B2137959
  · exact B2137963
  · exact B2137967
  · exact B2137971
  · exact B2137975
  · exact B2137979
  · exact B2137983
  · exact B2137987
  · exact B2137991
  · exact B2137995
  · exact B2137999
  · exact B2138003
  · exact B2138007
  · exact B2138011
  · exact B2138015
  · exact B2138019
  · exact B2138023
  · exact B2138027
  · exact B2138031
  · exact B2138035
  · exact B2138039
  · exact B2138043
  · exact B2138047
  · exact B2138051
  · exact B2138055
  · exact B2138059
  · exact B2138063
  · exact B2138067
  · exact B2138071
  · exact B2138075
  · exact B2138079
  · exact B2138083
  · exact B2138087
  · exact B2138091
  · exact B2138095
  · exact B2138099
  · exact B2138103
  · exact B2138107
  · exact B2138111
  · exact B2138115
  · exact B2138119
  · exact B2138123
  · exact B2138127
  · exact B2138131
  · exact B2138135
  · exact B2138139
  · exact B2138143
  · exact B2138147
  · exact B2138151
  · exact B2138155
  · exact B2138159
  · exact B2138163
  · exact B2138167
  · exact B2138171
  · exact B2138175
  · exact B2138179
  · exact B2138183
  · exact B2138187
  · exact B2138191
  · exact B2138195
  · exact B2138199
  · exact B2138203
  · exact B2138207
  · exact B2138211
  · exact B2138215
  · exact B2138219
  · exact B2138223
  · exact B2138227
  · exact B2138231
  · exact B2138235
  · exact B2138239
  · exact B2138243
  · exact B2138247
  · exact B2138251
  · exact B2138255
  · exact B2138259
  · exact B2138263
  · exact B2138267
  · exact B2138271
  · exact B2138275
  · exact B2138279
  · exact B2138283
  · exact B2138287
  · exact B2138291
  · exact B2138295
  · exact B2138299
  · exact B2138303
  · exact B2138307
  · exact B2138311
  · exact B2138315
  · exact B2138319
  · exact B2138323
  · exact B2138327
  · exact B2138331
  · exact B2138335
  · exact B2138339
  · exact B2138343
  · exact B2138347
  · exact B2138351
  · exact B2138355
  · exact B2138359
  · exact B2138363
  · exact B2138367
  · exact B2138371
  · exact B2138375
  · exact B2138379
  · exact B2138383
  · exact B2138387
  · exact B2138391
  · exact B2138395
  · exact B2138399
  · exact B2138403
  · exact B2138407
  · exact B2138411
  · exact B2138415
  · exact B2138419
  · exact B2138423
  · exact B2138427
  · exact B2138431
  · exact B2138435
  · exact B2138439
  · exact B2138443
  · exact B2138447
  · exact B2138451
  · exact B2138455
  · exact B2138459
  · exact B2138463
  · exact B2138467
  · exact B2138471
  · exact B2138475
  · exact B2138479
  · exact B2138483
  · exact B2138487
  · exact B2138491
  · exact B2138495
  · exact B2138499
  · exact B2138503
  · exact B2138507
  · exact B2138511
  · exact B2138515
  · exact B2138519
  · exact B2138523
  · exact B2138527
  · exact B2138531
  · exact B2138535
  · exact B2138539
  · exact B2138543
  · exact B2138547
  · exact B2138551
  · exact B2138555
  · exact B2138559
  · exact B2138563
  · exact B2138567
  · exact B2138571
  · exact B2138575
  · exact B2138579
  · exact B2138583
  · exact B2138587
  · exact B2138591
  · exact B2138595
  · exact B2138599
  · exact B2138603
  · exact B2138607
  · exact B2138611
  · exact B2138615
  · exact B2138619
  · exact B2138623
  · exact B2138627
  · exact B2138631
  · exact B2138635
  · exact B2138639
  · exact B2138643
  · exact B2138647
  · exact B2138651
  · exact B2138655
  · exact B2138659
  · exact B2138663
  · exact B2138667
  · exact B2138671
  · exact B2138675
  · exact B2138679
  · exact B2138683
  · exact B2138687
  · exact B2138691
  · exact B2138695
  · exact B2138699
  · exact B2138703
  · exact B2138707
  · exact B2138711
  · exact B2138715
  · exact B2138719
  · exact B2138723
  · exact B2138727
  · exact B2138731
  · exact B2138735
  · exact B2138739
  · exact B2138743
  · exact B2138747
  · exact B2138751
  · exact B2138755
  · exact B2138759
  · exact B2138763
  · exact B2138767
  · exact B2138771
  · exact B2138775
  · exact B2138779
  · exact B2138783
  · exact B2138787
  · exact B2138791
  · exact B2138795
  · exact B2138799
  · exact B2138803
  · exact B2138807
  · exact B2138811
  · exact B2138815
  · exact B2138819
  · exact B2138823
  · exact B2138827
  · exact B2138831
  · exact B2138835
  · exact B2138839
  · exact B2138843
  · exact B2138847
  · exact B2138851
  · exact B2138855
  · exact B2138859
  · exact B2138863
  · exact B2138867
  · exact B2138871
  · exact B2138875
  · exact B2138879
  · exact B2138883
  · exact B2138887
  · exact B2138891
  · exact B2138895
  · exact B2138899
  · exact B2138903
  · exact B2138907
  · exact B2138911
  · exact B2138915
  · exact B2138919
  · exact B2138923
  · exact B2138927
  · exact B2138931
  · exact B2138935
  · exact B2138939
  · exact B2138943
  · exact B2138947
  · exact B2138951
  · exact B2138955
  · exact B2138959
  · exact B2138963
  · exact B2138967
  · exact B2138971
  · exact B2138975
  · exact B2138979
  · exact B2138983
  · exact B2138987
  · exact B2138991
  · exact B2138995
  · exact B2138999
  · exact B2139003
  · exact B2139007
  · exact B2139011
  · exact B2139015
  · exact B2139019
  · exact B2139023
  · exact B2139027
  · exact B2139031
  · exact B2139035
  · exact B2139039
  · exact B2139043
  · exact B2139047
  · exact B2139051
  · exact B2139055
  · exact B2139059
  · exact B2139063
  · exact B2139067
  · exact B2139071
  · exact B2139075
  · exact B2139079
  · exact B2139083
  · exact B2139087
  · exact B2139091
  · exact B2139095
  · exact B2139099
  · exact B2139103
  · exact B2139107
  · exact B2139111
  · exact B2139115
  · exact B2139119
  · exact B2139123
  · exact B2139127
  · exact B2139131
  · exact B2139135
  · exact B2139139
  · exact B2139143
  · exact B2139147
  · exact B2139151
  · exact B2139155
  · exact B2139159
  · exact B2139163
  · exact B2139167
  · exact B2139171
  · exact B2139175
  · exact B2139179
  · exact B2139183
  · exact B2139187
  · exact B2139191
  · exact B2139195
  · exact B2139199
  · exact B2139203
  · exact B2139207
  · exact B2139211
  · exact B2139215
  · exact B2139219
  · exact B2139223
  · exact B2139227
  · exact B2139231
  · exact B2139235
  · exact B2139239
  · exact B2139243
  · exact B2139247
  · exact B2139251
  · exact B2139255
  · exact B2139259
  · exact B2139263
  · exact B2139267
  · exact B2139271
  · exact B2139275
  · exact B2139279
  · exact B2139283
  · exact B2139287
  · exact B2139291
  · exact B2139295
  · exact B2139299
  · exact B2139303
  · exact B2139307
  · exact B2139311
  · exact B2139315
  · exact B2139319
  · exact B2139323
  · exact B2139327
  · exact B2139331
  · exact B2139335
  · exact B2139339
  · exact B2139343
  · exact B2139347
  · exact B2139351
  · exact B2139355
  · exact B2139359
  · exact B2139363
  · exact B2139367
  · exact B2139371
  · exact B2139375
  · exact B2139379
  · exact B2139383
  · exact B2139387
  · exact B2139391
  · exact B2139395
  · exact B2139399
  · exact B2139403
  · exact B2139407
  · exact B2139411
  · exact B2139415
  · exact B2139419
  · exact B2139423
  · exact B2139427
  · exact B2139431
  · exact B2139435
theorem solution (m : ℕ) (hlo : 2137435 ≤ m) (hhi : m ≤ 2139435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 534358 ≤ j := by omega
    have hj2 : j ≤ 534858 := by omega
    have hb : Blo 2137435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
