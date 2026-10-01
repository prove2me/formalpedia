-- Prove2me | solution 1 for syracuse_descends_range_2195435_2197435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:12.784092+00:00
-- url     : https://prove2.me/submissions/7b638ec3-0163-475b-ba44-791063d9dc44

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

theorem B2469865 : Blo 2195435 2469865 := bbase (se 2 (by rfl) ⟨926199, by rfl⟩ : syracuseStep 2469865 = 1852399) (by norm_num)
theorem B3293153 : Blo 2195435 3293153 := bstep (se 2 (by rfl) ⟨1234932, by rfl⟩ : syracuseStep 3293153 = 2469865) B2469865
theorem B2195435 : Blo 2195435 2195435 := bstep (se 1 (by rfl) ⟨1646576, by rfl⟩ : syracuseStep 2195435 = 3293153) B3293153
theorem B5075453 : Blo 2195435 5075453 := bbase (se 3 (by rfl) ⟨951647, by rfl⟩ : syracuseStep 5075453 = 1903295) (by norm_num)
theorem B3383635 : Blo 2195435 3383635 := bstep (se 1 (by rfl) ⟨2537726, by rfl⟩ : syracuseStep 3383635 = 5075453) B5075453
theorem B4511513 : Blo 2195435 4511513 := bstep (se 2 (by rfl) ⟨1691817, by rfl⟩ : syracuseStep 4511513 = 3383635) B3383635
theorem B3007675 : Blo 2195435 3007675 := bstep (se 1 (by rfl) ⟨2255756, by rfl⟩ : syracuseStep 3007675 = 4511513) B4511513
theorem B4010233 : Blo 2195435 4010233 := bstep (se 2 (by rfl) ⟨1503837, by rfl⟩ : syracuseStep 4010233 = 3007675) B3007675
theorem B5346977 : Blo 2195435 5346977 := bstep (se 2 (by rfl) ⟨2005116, by rfl⟩ : syracuseStep 5346977 = 4010233) B4010233
theorem B14258605 : Blo 2195435 14258605 := bstep (se 3 (by rfl) ⟨2673488, by rfl⟩ : syracuseStep 14258605 = 5346977) B5346977
theorem B19011473 : Blo 2195435 19011473 := bstep (se 2 (by rfl) ⟨7129302, by rfl⟩ : syracuseStep 19011473 = 14258605) B14258605
theorem B12674315 : Blo 2195435 12674315 := bstep (se 1 (by rfl) ⟨9505736, by rfl⟩ : syracuseStep 12674315 = 19011473) B19011473
theorem B8449543 : Blo 2195435 8449543 := bstep (se 1 (by rfl) ⟨6337157, by rfl⟩ : syracuseStep 8449543 = 12674315) B12674315
theorem B11266057 : Blo 2195435 11266057 := bstep (se 2 (by rfl) ⟨4224771, by rfl⟩ : syracuseStep 11266057 = 8449543) B8449543
theorem B60085637 : Blo 2195435 60085637 := bstep (se 4 (by rfl) ⟨5633028, by rfl⟩ : syracuseStep 60085637 = 11266057) B11266057
theorem B40057091 : Blo 2195435 40057091 := bstep (se 1 (by rfl) ⟨30042818, by rfl⟩ : syracuseStep 40057091 = 60085637) B60085637
theorem B26704727 : Blo 2195435 26704727 := bstep (se 1 (by rfl) ⟨20028545, by rfl⟩ : syracuseStep 26704727 = 40057091) B40057091
theorem B17803151 : Blo 2195435 17803151 := bstep (se 1 (by rfl) ⟨13352363, by rfl⟩ : syracuseStep 17803151 = 26704727) B26704727
theorem B11868767 : Blo 2195435 11868767 := bstep (se 1 (by rfl) ⟨8901575, by rfl⟩ : syracuseStep 11868767 = 17803151) B17803151
theorem B7912511 : Blo 2195435 7912511 := bstep (se 1 (by rfl) ⟨5934383, by rfl⟩ : syracuseStep 7912511 = 11868767) B11868767
theorem B5275007 : Blo 2195435 5275007 := bstep (se 1 (by rfl) ⟨3956255, by rfl⟩ : syracuseStep 5275007 = 7912511) B7912511
theorem B3516671 : Blo 2195435 3516671 := bstep (se 1 (by rfl) ⟨2637503, by rfl⟩ : syracuseStep 3516671 = 5275007) B5275007
theorem B2344447 : Blo 2195435 2344447 := bstep (se 1 (by rfl) ⟨1758335, by rfl⟩ : syracuseStep 2344447 = 3516671) B3516671
theorem B12503717 : Blo 2195435 12503717 := bstep (se 4 (by rfl) ⟨1172223, by rfl⟩ : syracuseStep 12503717 = 2344447) B2344447
theorem B8335811 : Blo 2195435 8335811 := bstep (se 1 (by rfl) ⟨6251858, by rfl⟩ : syracuseStep 8335811 = 12503717) B12503717
theorem B5557207 : Blo 2195435 5557207 := bstep (se 1 (by rfl) ⟨4167905, by rfl⟩ : syracuseStep 5557207 = 8335811) B8335811
theorem B7409609 : Blo 2195435 7409609 := bstep (se 2 (by rfl) ⟨2778603, by rfl⟩ : syracuseStep 7409609 = 5557207) B5557207
theorem B4939739 : Blo 2195435 4939739 := bstep (se 1 (by rfl) ⟨3704804, by rfl⟩ : syracuseStep 4939739 = 7409609) B7409609
theorem B3293159 : Blo 2195435 3293159 := bstep (se 1 (by rfl) ⟨2469869, by rfl⟩ : syracuseStep 3293159 = 4939739) B4939739
theorem B2195439 : Blo 2195435 2195439 := bstep (se 1 (by rfl) ⟨1646579, by rfl⟩ : syracuseStep 2195439 = 3293159) B3293159
theorem B3293165 : Blo 2195435 3293165 := bbase (se 3 (by rfl) ⟨617468, by rfl⟩ : syracuseStep 3293165 = 1234937) (by norm_num)
theorem B2195443 : Blo 2195435 2195443 := bstep (se 1 (by rfl) ⟨1646582, by rfl⟩ : syracuseStep 2195443 = 3293165) B3293165
theorem B4939757 : Blo 2195435 4939757 := bbase (se 3 (by rfl) ⟨926204, by rfl⟩ : syracuseStep 4939757 = 1852409) (by norm_num)
theorem B3293171 : Blo 2195435 3293171 := bstep (se 1 (by rfl) ⟨2469878, by rfl⟩ : syracuseStep 3293171 = 4939757) B4939757
theorem B2195447 : Blo 2195435 2195447 := bstep (se 1 (by rfl) ⟨1646585, by rfl⟩ : syracuseStep 2195447 = 3293171) B3293171
theorem B5275037 : Blo 2195435 5275037 := bbase (se 3 (by rfl) ⟨989069, by rfl⟩ : syracuseStep 5275037 = 1978139) (by norm_num)
theorem B3516691 : Blo 2195435 3516691 := bstep (se 1 (by rfl) ⟨2637518, by rfl⟩ : syracuseStep 3516691 = 5275037) B5275037
theorem B4688921 : Blo 2195435 4688921 := bstep (se 2 (by rfl) ⟨1758345, by rfl⟩ : syracuseStep 4688921 = 3516691) B3516691
theorem B3125947 : Blo 2195435 3125947 := bstep (se 1 (by rfl) ⟨2344460, by rfl⟩ : syracuseStep 3125947 = 4688921) B4688921
theorem B4167929 : Blo 2195435 4167929 := bstep (se 2 (by rfl) ⟨1562973, by rfl⟩ : syracuseStep 4167929 = 3125947) B3125947
theorem B2778619 : Blo 2195435 2778619 := bstep (se 1 (by rfl) ⟨2083964, by rfl⟩ : syracuseStep 2778619 = 4167929) B4167929
theorem B3704825 : Blo 2195435 3704825 := bstep (se 2 (by rfl) ⟨1389309, by rfl⟩ : syracuseStep 3704825 = 2778619) B2778619
theorem B2469883 : Blo 2195435 2469883 := bstep (se 1 (by rfl) ⟨1852412, by rfl⟩ : syracuseStep 2469883 = 3704825) B3704825
theorem B3293177 : Blo 2195435 3293177 := bstep (se 2 (by rfl) ⟨1234941, by rfl⟩ : syracuseStep 3293177 = 2469883) B2469883
theorem B2195451 : Blo 2195435 2195451 := bstep (se 1 (by rfl) ⟨1646588, by rfl⟩ : syracuseStep 2195451 = 3293177) B3293177
theorem B640917845 : Blo 2195435 640917845 := bbase (se 10 (by rfl) ⟨938844, by rfl⟩ : syracuseStep 640917845 = 1877689) (by norm_num)
theorem B427278563 : Blo 2195435 427278563 := bstep (se 1 (by rfl) ⟨320458922, by rfl⟩ : syracuseStep 427278563 = 640917845) B640917845
theorem B284852375 : Blo 2195435 284852375 := bstep (se 1 (by rfl) ⟨213639281, by rfl⟩ : syracuseStep 284852375 = 427278563) B427278563
theorem B189901583 : Blo 2195435 189901583 := bstep (se 1 (by rfl) ⟨142426187, by rfl⟩ : syracuseStep 189901583 = 284852375) B284852375
theorem B126601055 : Blo 2195435 126601055 := bstep (se 1 (by rfl) ⟨94950791, by rfl⟩ : syracuseStep 126601055 = 189901583) B189901583
theorem B84400703 : Blo 2195435 84400703 := bstep (se 1 (by rfl) ⟨63300527, by rfl⟩ : syracuseStep 84400703 = 126601055) B126601055
theorem B56267135 : Blo 2195435 56267135 := bstep (se 1 (by rfl) ⟨42200351, by rfl⟩ : syracuseStep 56267135 = 84400703) B84400703
theorem B37511423 : Blo 2195435 37511423 := bstep (se 1 (by rfl) ⟨28133567, by rfl⟩ : syracuseStep 37511423 = 56267135) B56267135
theorem B25007615 : Blo 2195435 25007615 := bstep (se 1 (by rfl) ⟨18755711, by rfl⟩ : syracuseStep 25007615 = 37511423) B37511423
theorem B16671743 : Blo 2195435 16671743 := bstep (se 1 (by rfl) ⟨12503807, by rfl⟩ : syracuseStep 16671743 = 25007615) B25007615
theorem B11114495 : Blo 2195435 11114495 := bstep (se 1 (by rfl) ⟨8335871, by rfl⟩ : syracuseStep 11114495 = 16671743) B16671743
theorem B7409663 : Blo 2195435 7409663 := bstep (se 1 (by rfl) ⟨5557247, by rfl⟩ : syracuseStep 7409663 = 11114495) B11114495
theorem B4939775 : Blo 2195435 4939775 := bstep (se 1 (by rfl) ⟨3704831, by rfl⟩ : syracuseStep 4939775 = 7409663) B7409663
theorem B3293183 : Blo 2195435 3293183 := bstep (se 1 (by rfl) ⟨2469887, by rfl⟩ : syracuseStep 3293183 = 4939775) B4939775
theorem B2195455 : Blo 2195435 2195455 := bstep (se 1 (by rfl) ⟨1646591, by rfl⟩ : syracuseStep 2195455 = 3293183) B3293183
theorem B3293189 : Blo 2195435 3293189 := bbase (se 4 (by rfl) ⟨308736, by rfl⟩ : syracuseStep 3293189 = 617473) (by norm_num)
theorem B2195459 : Blo 2195435 2195459 := bstep (se 1 (by rfl) ⟨1646594, by rfl⟩ : syracuseStep 2195459 = 3293189) B3293189
theorem B3704845 : Blo 2195435 3704845 := bbase (se 3 (by rfl) ⟨694658, by rfl⟩ : syracuseStep 3704845 = 1389317) (by norm_num)
theorem B4939793 : Blo 2195435 4939793 := bstep (se 2 (by rfl) ⟨1852422, by rfl⟩ : syracuseStep 4939793 = 3704845) B3704845
theorem B3293195 : Blo 2195435 3293195 := bstep (se 1 (by rfl) ⟨2469896, by rfl⟩ : syracuseStep 3293195 = 4939793) B4939793
theorem B2195463 : Blo 2195435 2195463 := bstep (se 1 (by rfl) ⟨1646597, by rfl⟩ : syracuseStep 2195463 = 3293195) B3293195
theorem B2469901 : Blo 2195435 2469901 := bbase (se 3 (by rfl) ⟨463106, by rfl⟩ : syracuseStep 2469901 = 926213) (by norm_num)
theorem B3293201 : Blo 2195435 3293201 := bstep (se 2 (by rfl) ⟨1234950, by rfl⟩ : syracuseStep 3293201 = 2469901) B2469901
theorem B2195467 : Blo 2195435 2195467 := bstep (se 1 (by rfl) ⟨1646600, by rfl⟩ : syracuseStep 2195467 = 3293201) B3293201
theorem B7409717 : Blo 2195435 7409717 := bbase (se 5 (by rfl) ⟨347330, by rfl⟩ : syracuseStep 7409717 = 694661) (by norm_num)
theorem B4939811 : Blo 2195435 4939811 := bstep (se 1 (by rfl) ⟨3704858, by rfl⟩ : syracuseStep 4939811 = 7409717) B7409717
theorem B3293207 : Blo 2195435 3293207 := bstep (se 1 (by rfl) ⟨2469905, by rfl⟩ : syracuseStep 3293207 = 4939811) B4939811
theorem B2195471 : Blo 2195435 2195471 := bstep (se 1 (by rfl) ⟨1646603, by rfl⟩ : syracuseStep 2195471 = 3293207) B3293207
theorem B3293213 : Blo 2195435 3293213 := bbase (se 3 (by rfl) ⟨617477, by rfl⟩ : syracuseStep 3293213 = 1234955) (by norm_num)
theorem B2195475 : Blo 2195435 2195475 := bstep (se 1 (by rfl) ⟨1646606, by rfl⟩ : syracuseStep 2195475 = 3293213) B3293213
theorem B4939829 : Blo 2195435 4939829 := bbase (se 5 (by rfl) ⟨231554, by rfl⟩ : syracuseStep 4939829 = 463109) (by norm_num)
theorem B3293219 : Blo 2195435 3293219 := bstep (se 1 (by rfl) ⟨2469914, by rfl⟩ : syracuseStep 3293219 = 4939829) B4939829
theorem B2195479 : Blo 2195435 2195479 := bstep (se 1 (by rfl) ⟨1646609, by rfl⟩ : syracuseStep 2195479 = 3293219) B3293219
theorem B4450877 : Blo 2195435 4450877 := bbase (se 3 (by rfl) ⟨834539, by rfl⟩ : syracuseStep 4450877 = 1669079) (by norm_num)
theorem B2967251 : Blo 2195435 2967251 := bstep (se 1 (by rfl) ⟨2225438, by rfl⟩ : syracuseStep 2967251 = 4450877) B4450877
theorem B7912669 : Blo 2195435 7912669 := bstep (se 3 (by rfl) ⟨1483625, by rfl⟩ : syracuseStep 7912669 = 2967251) B2967251
theorem B10550225 : Blo 2195435 10550225 := bstep (se 2 (by rfl) ⟨3956334, by rfl⟩ : syracuseStep 10550225 = 7912669) B7912669
theorem B7033483 : Blo 2195435 7033483 := bstep (se 1 (by rfl) ⟨5275112, by rfl⟩ : syracuseStep 7033483 = 10550225) B10550225
theorem B9377977 : Blo 2195435 9377977 := bstep (se 2 (by rfl) ⟨3516741, by rfl⟩ : syracuseStep 9377977 = 7033483) B7033483
theorem B12503969 : Blo 2195435 12503969 := bstep (se 2 (by rfl) ⟨4688988, by rfl⟩ : syracuseStep 12503969 = 9377977) B9377977
theorem B8335979 : Blo 2195435 8335979 := bstep (se 1 (by rfl) ⟨6251984, by rfl⟩ : syracuseStep 8335979 = 12503969) B12503969
theorem B5557319 : Blo 2195435 5557319 := bstep (se 1 (by rfl) ⟨4167989, by rfl⟩ : syracuseStep 5557319 = 8335979) B8335979
theorem B3704879 : Blo 2195435 3704879 := bstep (se 1 (by rfl) ⟨2778659, by rfl⟩ : syracuseStep 3704879 = 5557319) B5557319
theorem B2469919 : Blo 2195435 2469919 := bstep (se 1 (by rfl) ⟨1852439, by rfl⟩ : syracuseStep 2469919 = 3704879) B3704879
theorem B3293225 : Blo 2195435 3293225 := bstep (se 2 (by rfl) ⟨1234959, by rfl⟩ : syracuseStep 3293225 = 2469919) B2469919
theorem B2195483 : Blo 2195435 2195483 := bstep (se 1 (by rfl) ⟨1646612, by rfl⟩ : syracuseStep 2195483 = 3293225) B3293225
theorem B15825365 : Blo 2195435 15825365 := bbase (se 7 (by rfl) ⟨185453, by rfl⟩ : syracuseStep 15825365 = 370907) (by norm_num)
theorem B10550243 : Blo 2195435 10550243 := bstep (se 1 (by rfl) ⟨7912682, by rfl⟩ : syracuseStep 10550243 = 15825365) B15825365
theorem B7033495 : Blo 2195435 7033495 := bstep (se 1 (by rfl) ⟨5275121, by rfl⟩ : syracuseStep 7033495 = 10550243) B10550243
theorem B9377993 : Blo 2195435 9377993 := bstep (se 2 (by rfl) ⟨3516747, by rfl⟩ : syracuseStep 9377993 = 7033495) B7033495
theorem B6251995 : Blo 2195435 6251995 := bstep (se 1 (by rfl) ⟨4688996, by rfl⟩ : syracuseStep 6251995 = 9377993) B9377993
theorem B8335993 : Blo 2195435 8335993 := bstep (se 2 (by rfl) ⟨3125997, by rfl⟩ : syracuseStep 8335993 = 6251995) B6251995
theorem B11114657 : Blo 2195435 11114657 := bstep (se 2 (by rfl) ⟨4167996, by rfl⟩ : syracuseStep 11114657 = 8335993) B8335993
theorem B7409771 : Blo 2195435 7409771 := bstep (se 1 (by rfl) ⟨5557328, by rfl⟩ : syracuseStep 7409771 = 11114657) B11114657
theorem B4939847 : Blo 2195435 4939847 := bstep (se 1 (by rfl) ⟨3704885, by rfl⟩ : syracuseStep 4939847 = 7409771) B7409771
theorem B3293231 : Blo 2195435 3293231 := bstep (se 1 (by rfl) ⟨2469923, by rfl⟩ : syracuseStep 3293231 = 4939847) B4939847
theorem B2195487 : Blo 2195435 2195487 := bstep (se 1 (by rfl) ⟨1646615, by rfl⟩ : syracuseStep 2195487 = 3293231) B3293231
theorem B3293237 : Blo 2195435 3293237 := bbase (se 5 (by rfl) ⟨154370, by rfl⟩ : syracuseStep 3293237 = 308741) (by norm_num)
theorem B2195491 : Blo 2195435 2195491 := bstep (se 1 (by rfl) ⟨1646618, by rfl⟩ : syracuseStep 2195491 = 3293237) B3293237
theorem B5557349 : Blo 2195435 5557349 := bbase (se 4 (by rfl) ⟨521001, by rfl⟩ : syracuseStep 5557349 = 1042003) (by norm_num)
theorem B3704899 : Blo 2195435 3704899 := bstep (se 1 (by rfl) ⟨2778674, by rfl⟩ : syracuseStep 3704899 = 5557349) B5557349
theorem B4939865 : Blo 2195435 4939865 := bstep (se 2 (by rfl) ⟨1852449, by rfl⟩ : syracuseStep 4939865 = 3704899) B3704899
theorem B3293243 : Blo 2195435 3293243 := bstep (se 1 (by rfl) ⟨2469932, by rfl⟩ : syracuseStep 3293243 = 4939865) B4939865
theorem B2195495 : Blo 2195435 2195495 := bstep (se 1 (by rfl) ⟨1646621, by rfl⟩ : syracuseStep 2195495 = 3293243) B3293243
theorem B2469937 : Blo 2195435 2469937 := bbase (se 2 (by rfl) ⟨926226, by rfl⟩ : syracuseStep 2469937 = 1852453) (by norm_num)
theorem B3293249 : Blo 2195435 3293249 := bstep (se 2 (by rfl) ⟨1234968, by rfl⟩ : syracuseStep 3293249 = 2469937) B2469937
theorem B2195499 : Blo 2195435 2195499 := bstep (se 1 (by rfl) ⟨1646624, by rfl⟩ : syracuseStep 2195499 = 3293249) B3293249
theorem B7912741 : Blo 2195435 7912741 := bbase (se 4 (by rfl) ⟨741819, by rfl⟩ : syracuseStep 7912741 = 1483639) (by norm_num)
theorem B10550321 : Blo 2195435 10550321 := bstep (se 2 (by rfl) ⟨3956370, by rfl⟩ : syracuseStep 10550321 = 7912741) B7912741
theorem B7033547 : Blo 2195435 7033547 := bstep (se 1 (by rfl) ⟨5275160, by rfl⟩ : syracuseStep 7033547 = 10550321) B10550321
theorem B4689031 : Blo 2195435 4689031 := bstep (se 1 (by rfl) ⟨3516773, by rfl⟩ : syracuseStep 4689031 = 7033547) B7033547
theorem B6252041 : Blo 2195435 6252041 := bstep (se 2 (by rfl) ⟨2344515, by rfl⟩ : syracuseStep 6252041 = 4689031) B4689031
theorem B4168027 : Blo 2195435 4168027 := bstep (se 1 (by rfl) ⟨3126020, by rfl⟩ : syracuseStep 4168027 = 6252041) B6252041
theorem B5557369 : Blo 2195435 5557369 := bstep (se 2 (by rfl) ⟨2084013, by rfl⟩ : syracuseStep 5557369 = 4168027) B4168027
theorem B7409825 : Blo 2195435 7409825 := bstep (se 2 (by rfl) ⟨2778684, by rfl⟩ : syracuseStep 7409825 = 5557369) B5557369
theorem B4939883 : Blo 2195435 4939883 := bstep (se 1 (by rfl) ⟨3704912, by rfl⟩ : syracuseStep 4939883 = 7409825) B7409825
theorem B3293255 : Blo 2195435 3293255 := bstep (se 1 (by rfl) ⟨2469941, by rfl⟩ : syracuseStep 3293255 = 4939883) B4939883
theorem B2195503 : Blo 2195435 2195503 := bstep (se 1 (by rfl) ⟨1646627, by rfl⟩ : syracuseStep 2195503 = 3293255) B3293255
theorem B3293261 : Blo 2195435 3293261 := bbase (se 3 (by rfl) ⟨617486, by rfl⟩ : syracuseStep 3293261 = 1234973) (by norm_num)
theorem B2195507 : Blo 2195435 2195507 := bstep (se 1 (by rfl) ⟨1646630, by rfl⟩ : syracuseStep 2195507 = 3293261) B3293261
theorem B4939901 : Blo 2195435 4939901 := bbase (se 3 (by rfl) ⟨926231, by rfl⟩ : syracuseStep 4939901 = 1852463) (by norm_num)
theorem B3293267 : Blo 2195435 3293267 := bstep (se 1 (by rfl) ⟨2469950, by rfl⟩ : syracuseStep 3293267 = 4939901) B4939901
theorem B2195511 : Blo 2195435 2195511 := bstep (se 1 (by rfl) ⟨1646633, by rfl⟩ : syracuseStep 2195511 = 3293267) B3293267
theorem B3704933 : Blo 2195435 3704933 := bbase (se 4 (by rfl) ⟨347337, by rfl⟩ : syracuseStep 3704933 = 694675) (by norm_num)
theorem B2469955 : Blo 2195435 2469955 := bstep (se 1 (by rfl) ⟨1852466, by rfl⟩ : syracuseStep 2469955 = 3704933) B3704933
theorem B3293273 : Blo 2195435 3293273 := bstep (se 2 (by rfl) ⟨1234977, by rfl⟩ : syracuseStep 3293273 = 2469955) B2469955
theorem B2195515 : Blo 2195435 2195515 := bstep (se 1 (by rfl) ⟨1646636, by rfl⟩ : syracuseStep 2195515 = 3293273) B3293273
theorem B2816617 : Blo 2195435 2816617 := bbase (se 2 (by rfl) ⟨1056231, by rfl⟩ : syracuseStep 2816617 = 2112463) (by norm_num)
theorem B3755489 : Blo 2195435 3755489 := bstep (se 2 (by rfl) ⟨1408308, by rfl⟩ : syracuseStep 3755489 = 2816617) B2816617
theorem B40058549 : Blo 2195435 40058549 := bstep (se 5 (by rfl) ⟨1877744, by rfl⟩ : syracuseStep 40058549 = 3755489) B3755489
theorem B26705699 : Blo 2195435 26705699 := bstep (se 1 (by rfl) ⟨20029274, by rfl⟩ : syracuseStep 26705699 = 40058549) B40058549
theorem B17803799 : Blo 2195435 17803799 := bstep (se 1 (by rfl) ⟨13352849, by rfl⟩ : syracuseStep 17803799 = 26705699) B26705699
theorem B11869199 : Blo 2195435 11869199 := bstep (se 1 (by rfl) ⟨8901899, by rfl⟩ : syracuseStep 11869199 = 17803799) B17803799
theorem B7912799 : Blo 2195435 7912799 := bstep (se 1 (by rfl) ⟨5934599, by rfl⟩ : syracuseStep 7912799 = 11869199) B11869199
theorem B5275199 : Blo 2195435 5275199 := bstep (se 1 (by rfl) ⟨3956399, by rfl⟩ : syracuseStep 5275199 = 7912799) B7912799
theorem B3516799 : Blo 2195435 3516799 := bstep (se 1 (by rfl) ⟨2637599, by rfl⟩ : syracuseStep 3516799 = 5275199) B5275199
theorem B4689065 : Blo 2195435 4689065 := bstep (se 2 (by rfl) ⟨1758399, by rfl⟩ : syracuseStep 4689065 = 3516799) B3516799
theorem B3126043 : Blo 2195435 3126043 := bstep (se 1 (by rfl) ⟨2344532, by rfl⟩ : syracuseStep 3126043 = 4689065) B4689065
theorem B16672229 : Blo 2195435 16672229 := bstep (se 4 (by rfl) ⟨1563021, by rfl⟩ : syracuseStep 16672229 = 3126043) B3126043
theorem B11114819 : Blo 2195435 11114819 := bstep (se 1 (by rfl) ⟨8336114, by rfl⟩ : syracuseStep 11114819 = 16672229) B16672229
theorem B7409879 : Blo 2195435 7409879 := bstep (se 1 (by rfl) ⟨5557409, by rfl⟩ : syracuseStep 7409879 = 11114819) B11114819
theorem B4939919 : Blo 2195435 4939919 := bstep (se 1 (by rfl) ⟨3704939, by rfl⟩ : syracuseStep 4939919 = 7409879) B7409879
theorem B3293279 : Blo 2195435 3293279 := bstep (se 1 (by rfl) ⟨2469959, by rfl⟩ : syracuseStep 3293279 = 4939919) B4939919
theorem B2195519 : Blo 2195435 2195519 := bstep (se 1 (by rfl) ⟨1646639, by rfl⟩ : syracuseStep 2195519 = 3293279) B3293279
theorem B3293285 : Blo 2195435 3293285 := bbase (se 4 (by rfl) ⟨308745, by rfl⟩ : syracuseStep 3293285 = 617491) (by norm_num)
theorem B2195523 : Blo 2195435 2195523 := bstep (se 1 (by rfl) ⟨1646642, by rfl⟩ : syracuseStep 2195523 = 3293285) B3293285
theorem B10014677 : Blo 2195435 10014677 := bbase (se 7 (by rfl) ⟨117359, by rfl⟩ : syracuseStep 10014677 = 234719) (by norm_num)
theorem B6676451 : Blo 2195435 6676451 := bstep (se 1 (by rfl) ⟨5007338, by rfl⟩ : syracuseStep 6676451 = 10014677) B10014677
theorem B4450967 : Blo 2195435 4450967 := bstep (se 1 (by rfl) ⟨3338225, by rfl⟩ : syracuseStep 4450967 = 6676451) B6676451
theorem B2967311 : Blo 2195435 2967311 := bstep (se 1 (by rfl) ⟨2225483, by rfl⟩ : syracuseStep 2967311 = 4450967) B4450967
theorem B7912829 : Blo 2195435 7912829 := bstep (se 3 (by rfl) ⟨1483655, by rfl⟩ : syracuseStep 7912829 = 2967311) B2967311
theorem B5275219 : Blo 2195435 5275219 := bstep (se 1 (by rfl) ⟨3956414, by rfl⟩ : syracuseStep 5275219 = 7912829) B7912829
theorem B7033625 : Blo 2195435 7033625 := bstep (se 2 (by rfl) ⟨2637609, by rfl⟩ : syracuseStep 7033625 = 5275219) B5275219
theorem B4689083 : Blo 2195435 4689083 := bstep (se 1 (by rfl) ⟨3516812, by rfl⟩ : syracuseStep 4689083 = 7033625) B7033625
theorem B3126055 : Blo 2195435 3126055 := bstep (se 1 (by rfl) ⟨2344541, by rfl⟩ : syracuseStep 3126055 = 4689083) B4689083
theorem B4168073 : Blo 2195435 4168073 := bstep (se 2 (by rfl) ⟨1563027, by rfl⟩ : syracuseStep 4168073 = 3126055) B3126055
theorem B2778715 : Blo 2195435 2778715 := bstep (se 1 (by rfl) ⟨2084036, by rfl⟩ : syracuseStep 2778715 = 4168073) B4168073
theorem B3704953 : Blo 2195435 3704953 := bstep (se 2 (by rfl) ⟨1389357, by rfl⟩ : syracuseStep 3704953 = 2778715) B2778715
theorem B4939937 : Blo 2195435 4939937 := bstep (se 2 (by rfl) ⟨1852476, by rfl⟩ : syracuseStep 4939937 = 3704953) B3704953
theorem B3293291 : Blo 2195435 3293291 := bstep (se 1 (by rfl) ⟨2469968, by rfl⟩ : syracuseStep 3293291 = 4939937) B4939937
theorem B2195527 : Blo 2195435 2195527 := bstep (se 1 (by rfl) ⟨1646645, by rfl⟩ : syracuseStep 2195527 = 3293291) B3293291
theorem B2469973 : Blo 2195435 2469973 := bbase (se 8 (by rfl) ⟨14472, by rfl⟩ : syracuseStep 2469973 = 28945) (by norm_num)
theorem B3293297 : Blo 2195435 3293297 := bstep (se 2 (by rfl) ⟨1234986, by rfl⟩ : syracuseStep 3293297 = 2469973) B2469973
theorem B2195531 : Blo 2195435 2195531 := bstep (se 1 (by rfl) ⟨1646648, by rfl⟩ : syracuseStep 2195531 = 3293297) B3293297
theorem B2778725 : Blo 2195435 2778725 := bbase (se 4 (by rfl) ⟨260505, by rfl⟩ : syracuseStep 2778725 = 521011) (by norm_num)
theorem B7409933 : Blo 2195435 7409933 := bstep (se 3 (by rfl) ⟨1389362, by rfl⟩ : syracuseStep 7409933 = 2778725) B2778725
theorem B4939955 : Blo 2195435 4939955 := bstep (se 1 (by rfl) ⟨3704966, by rfl⟩ : syracuseStep 4939955 = 7409933) B7409933
theorem B3293303 : Blo 2195435 3293303 := bstep (se 1 (by rfl) ⟨2469977, by rfl⟩ : syracuseStep 3293303 = 4939955) B4939955
theorem B2195535 : Blo 2195435 2195535 := bstep (se 1 (by rfl) ⟨1646651, by rfl⟩ : syracuseStep 2195535 = 3293303) B3293303
theorem B3293309 : Blo 2195435 3293309 := bbase (se 3 (by rfl) ⟨617495, by rfl⟩ : syracuseStep 3293309 = 1234991) (by norm_num)
theorem B2195539 : Blo 2195435 2195539 := bstep (se 1 (by rfl) ⟨1646654, by rfl⟩ : syracuseStep 2195539 = 3293309) B3293309
theorem B4939973 : Blo 2195435 4939973 := bbase (se 4 (by rfl) ⟨463122, by rfl⟩ : syracuseStep 4939973 = 926245) (by norm_num)
theorem B3293315 : Blo 2195435 3293315 := bstep (se 1 (by rfl) ⟨2469986, by rfl⟩ : syracuseStep 3293315 = 4939973) B4939973
theorem B2195543 : Blo 2195435 2195543 := bstep (se 1 (by rfl) ⟨1646657, by rfl⟩ : syracuseStep 2195543 = 3293315) B3293315
theorem B10550533 : Blo 2195435 10550533 := bbase (se 4 (by rfl) ⟨989112, by rfl⟩ : syracuseStep 10550533 = 1978225) (by norm_num)
theorem B14067377 : Blo 2195435 14067377 := bstep (se 2 (by rfl) ⟨5275266, by rfl⟩ : syracuseStep 14067377 = 10550533) B10550533
theorem B9378251 : Blo 2195435 9378251 := bstep (se 1 (by rfl) ⟨7033688, by rfl⟩ : syracuseStep 9378251 = 14067377) B14067377
theorem B6252167 : Blo 2195435 6252167 := bstep (se 1 (by rfl) ⟨4689125, by rfl⟩ : syracuseStep 6252167 = 9378251) B9378251
theorem B4168111 : Blo 2195435 4168111 := bstep (se 1 (by rfl) ⟨3126083, by rfl⟩ : syracuseStep 4168111 = 6252167) B6252167
theorem B5557481 : Blo 2195435 5557481 := bstep (se 2 (by rfl) ⟨2084055, by rfl⟩ : syracuseStep 5557481 = 4168111) B4168111
theorem B3704987 : Blo 2195435 3704987 := bstep (se 1 (by rfl) ⟨2778740, by rfl⟩ : syracuseStep 3704987 = 5557481) B5557481
theorem B2469991 : Blo 2195435 2469991 := bstep (se 1 (by rfl) ⟨1852493, by rfl⟩ : syracuseStep 2469991 = 3704987) B3704987
theorem B3293321 : Blo 2195435 3293321 := bstep (se 2 (by rfl) ⟨1234995, by rfl⟩ : syracuseStep 3293321 = 2469991) B2469991
theorem B2195547 : Blo 2195435 2195547 := bstep (se 1 (by rfl) ⟨1646660, by rfl⟩ : syracuseStep 2195547 = 3293321) B3293321
theorem B11114981 : Blo 2195435 11114981 := bbase (se 4 (by rfl) ⟨1042029, by rfl⟩ : syracuseStep 11114981 = 2084059) (by norm_num)
theorem B7409987 : Blo 2195435 7409987 := bstep (se 1 (by rfl) ⟨5557490, by rfl⟩ : syracuseStep 7409987 = 11114981) B11114981
theorem B4939991 : Blo 2195435 4939991 := bstep (se 1 (by rfl) ⟨3704993, by rfl⟩ : syracuseStep 4939991 = 7409987) B7409987
theorem B3293327 : Blo 2195435 3293327 := bstep (se 1 (by rfl) ⟨2469995, by rfl⟩ : syracuseStep 3293327 = 4939991) B4939991
theorem B2195551 : Blo 2195435 2195551 := bstep (se 1 (by rfl) ⟨1646663, by rfl⟩ : syracuseStep 2195551 = 3293327) B3293327
theorem B3293333 : Blo 2195435 3293333 := bbase (se 6 (by rfl) ⟨77187, by rfl⟩ : syracuseStep 3293333 = 154375) (by norm_num)
theorem B2195555 : Blo 2195435 2195555 := bstep (se 1 (by rfl) ⟨1646666, by rfl⟩ : syracuseStep 2195555 = 3293333) B3293333
theorem B11420389 : Blo 2195435 11420389 := bbase (se 4 (by rfl) ⟨1070661, by rfl⟩ : syracuseStep 11420389 = 2141323) (by norm_num)
theorem B15227185 : Blo 2195435 15227185 := bstep (se 2 (by rfl) ⟨5710194, by rfl⟩ : syracuseStep 15227185 = 11420389) B11420389
theorem B20302913 : Blo 2195435 20302913 := bstep (se 2 (by rfl) ⟨7613592, by rfl⟩ : syracuseStep 20302913 = 15227185) B15227185
theorem B13535275 : Blo 2195435 13535275 := bstep (se 1 (by rfl) ⟨10151456, by rfl⟩ : syracuseStep 13535275 = 20302913) B20302913
theorem B18047033 : Blo 2195435 18047033 := bstep (se 2 (by rfl) ⟨6767637, by rfl⟩ : syracuseStep 18047033 = 13535275) B13535275
theorem B12031355 : Blo 2195435 12031355 := bstep (se 1 (by rfl) ⟨9023516, by rfl⟩ : syracuseStep 12031355 = 18047033) B18047033
theorem B32083613 : Blo 2195435 32083613 := bstep (se 3 (by rfl) ⟨6015677, by rfl⟩ : syracuseStep 32083613 = 12031355) B12031355
theorem B21389075 : Blo 2195435 21389075 := bstep (se 1 (by rfl) ⟨16041806, by rfl⟩ : syracuseStep 21389075 = 32083613) B32083613
theorem B14259383 : Blo 2195435 14259383 := bstep (se 1 (by rfl) ⟨10694537, by rfl⟩ : syracuseStep 14259383 = 21389075) B21389075
theorem B9506255 : Blo 2195435 9506255 := bstep (se 1 (by rfl) ⟨7129691, by rfl⟩ : syracuseStep 9506255 = 14259383) B14259383
theorem B25350013 : Blo 2195435 25350013 := bstep (se 3 (by rfl) ⟨4753127, by rfl⟩ : syracuseStep 25350013 = 9506255) B9506255
theorem B33800017 : Blo 2195435 33800017 := bstep (se 2 (by rfl) ⟨12675006, by rfl⟩ : syracuseStep 33800017 = 25350013) B25350013
theorem B45066689 : Blo 2195435 45066689 := bstep (se 2 (by rfl) ⟨16900008, by rfl⟩ : syracuseStep 45066689 = 33800017) B33800017
theorem B30044459 : Blo 2195435 30044459 := bstep (se 1 (by rfl) ⟨22533344, by rfl⟩ : syracuseStep 30044459 = 45066689) B45066689
theorem B20029639 : Blo 2195435 20029639 := bstep (se 1 (by rfl) ⟨15022229, by rfl⟩ : syracuseStep 20029639 = 30044459) B30044459
theorem B26706185 : Blo 2195435 26706185 := bstep (se 2 (by rfl) ⟨10014819, by rfl⟩ : syracuseStep 26706185 = 20029639) B20029639
theorem B17804123 : Blo 2195435 17804123 := bstep (se 1 (by rfl) ⟨13353092, by rfl⟩ : syracuseStep 17804123 = 26706185) B26706185
theorem B11869415 : Blo 2195435 11869415 := bstep (se 1 (by rfl) ⟨8902061, by rfl⟩ : syracuseStep 11869415 = 17804123) B17804123
theorem B7912943 : Blo 2195435 7912943 := bstep (se 1 (by rfl) ⟨5934707, by rfl⟩ : syracuseStep 7912943 = 11869415) B11869415
theorem B5275295 : Blo 2195435 5275295 := bstep (se 1 (by rfl) ⟨3956471, by rfl⟩ : syracuseStep 5275295 = 7912943) B7912943
theorem B3516863 : Blo 2195435 3516863 := bstep (se 1 (by rfl) ⟨2637647, by rfl⟩ : syracuseStep 3516863 = 5275295) B5275295
theorem B9378301 : Blo 2195435 9378301 := bstep (se 3 (by rfl) ⟨1758431, by rfl⟩ : syracuseStep 9378301 = 3516863) B3516863
theorem B12504401 : Blo 2195435 12504401 := bstep (se 2 (by rfl) ⟨4689150, by rfl⟩ : syracuseStep 12504401 = 9378301) B9378301
theorem B8336267 : Blo 2195435 8336267 := bstep (se 1 (by rfl) ⟨6252200, by rfl⟩ : syracuseStep 8336267 = 12504401) B12504401
theorem B5557511 : Blo 2195435 5557511 := bstep (se 1 (by rfl) ⟨4168133, by rfl⟩ : syracuseStep 5557511 = 8336267) B8336267
theorem B3705007 : Blo 2195435 3705007 := bstep (se 1 (by rfl) ⟨2778755, by rfl⟩ : syracuseStep 3705007 = 5557511) B5557511
theorem B4940009 : Blo 2195435 4940009 := bstep (se 2 (by rfl) ⟨1852503, by rfl⟩ : syracuseStep 4940009 = 3705007) B3705007
theorem B3293339 : Blo 2195435 3293339 := bstep (se 1 (by rfl) ⟨2470004, by rfl⟩ : syracuseStep 3293339 = 4940009) B4940009
theorem B2195559 : Blo 2195435 2195559 := bstep (se 1 (by rfl) ⟨1646669, by rfl⟩ : syracuseStep 2195559 = 3293339) B3293339
theorem B2470009 : Blo 2195435 2470009 := bbase (se 2 (by rfl) ⟨926253, by rfl⟩ : syracuseStep 2470009 = 1852507) (by norm_num)
theorem B3293345 : Blo 2195435 3293345 := bstep (se 2 (by rfl) ⟨1235004, by rfl⟩ : syracuseStep 3293345 = 2470009) B2470009
theorem B2195563 : Blo 2195435 2195563 := bstep (se 1 (by rfl) ⟨1646672, by rfl⟩ : syracuseStep 2195563 = 3293345) B3293345
theorem B7511141 : Blo 2195435 7511141 := bbase (se 4 (by rfl) ⟨704169, by rfl⟩ : syracuseStep 7511141 = 1408339) (by norm_num)
theorem B5007427 : Blo 2195435 5007427 := bstep (se 1 (by rfl) ⟨3755570, by rfl⟩ : syracuseStep 5007427 = 7511141) B7511141
theorem B26706277 : Blo 2195435 26706277 := bstep (se 4 (by rfl) ⟨2503713, by rfl⟩ : syracuseStep 26706277 = 5007427) B5007427
theorem B35608369 : Blo 2195435 35608369 := bstep (se 2 (by rfl) ⟨13353138, by rfl⟩ : syracuseStep 35608369 = 26706277) B26706277
theorem B47477825 : Blo 2195435 47477825 := bstep (se 2 (by rfl) ⟨17804184, by rfl⟩ : syracuseStep 47477825 = 35608369) B35608369
theorem B31651883 : Blo 2195435 31651883 := bstep (se 1 (by rfl) ⟨23738912, by rfl⟩ : syracuseStep 31651883 = 47477825) B47477825
theorem B21101255 : Blo 2195435 21101255 := bstep (se 1 (by rfl) ⟨15825941, by rfl⟩ : syracuseStep 21101255 = 31651883) B31651883
theorem B14067503 : Blo 2195435 14067503 := bstep (se 1 (by rfl) ⟨10550627, by rfl⟩ : syracuseStep 14067503 = 21101255) B21101255
theorem B9378335 : Blo 2195435 9378335 := bstep (se 1 (by rfl) ⟨7033751, by rfl⟩ : syracuseStep 9378335 = 14067503) B14067503
theorem B6252223 : Blo 2195435 6252223 := bstep (se 1 (by rfl) ⟨4689167, by rfl⟩ : syracuseStep 6252223 = 9378335) B9378335
theorem B8336297 : Blo 2195435 8336297 := bstep (se 2 (by rfl) ⟨3126111, by rfl⟩ : syracuseStep 8336297 = 6252223) B6252223
theorem B5557531 : Blo 2195435 5557531 := bstep (se 1 (by rfl) ⟨4168148, by rfl⟩ : syracuseStep 5557531 = 8336297) B8336297
theorem B7410041 : Blo 2195435 7410041 := bstep (se 2 (by rfl) ⟨2778765, by rfl⟩ : syracuseStep 7410041 = 5557531) B5557531
theorem B4940027 : Blo 2195435 4940027 := bstep (se 1 (by rfl) ⟨3705020, by rfl⟩ : syracuseStep 4940027 = 7410041) B7410041
theorem B3293351 : Blo 2195435 3293351 := bstep (se 1 (by rfl) ⟨2470013, by rfl⟩ : syracuseStep 3293351 = 4940027) B4940027
theorem B2195567 : Blo 2195435 2195567 := bstep (se 1 (by rfl) ⟨1646675, by rfl⟩ : syracuseStep 2195567 = 3293351) B3293351
theorem B3293357 : Blo 2195435 3293357 := bbase (se 3 (by rfl) ⟨617504, by rfl⟩ : syracuseStep 3293357 = 1235009) (by norm_num)
theorem B2195571 : Blo 2195435 2195571 := bstep (se 1 (by rfl) ⟨1646678, by rfl⟩ : syracuseStep 2195571 = 3293357) B3293357
theorem B4940045 : Blo 2195435 4940045 := bbase (se 3 (by rfl) ⟨926258, by rfl⟩ : syracuseStep 4940045 = 1852517) (by norm_num)
theorem B3293363 : Blo 2195435 3293363 := bstep (se 1 (by rfl) ⟨2470022, by rfl⟩ : syracuseStep 3293363 = 4940045) B4940045
theorem B2195575 : Blo 2195435 2195575 := bstep (se 1 (by rfl) ⟨1646681, by rfl⟩ : syracuseStep 2195575 = 3293363) B3293363
theorem B2778781 : Blo 2195435 2778781 := bbase (se 3 (by rfl) ⟨521021, by rfl⟩ : syracuseStep 2778781 = 1042043) (by norm_num)
theorem B3705041 : Blo 2195435 3705041 := bstep (se 2 (by rfl) ⟨1389390, by rfl⟩ : syracuseStep 3705041 = 2778781) B2778781
theorem B2470027 : Blo 2195435 2470027 := bstep (se 1 (by rfl) ⟨1852520, by rfl⟩ : syracuseStep 2470027 = 3705041) B3705041
theorem B3293369 : Blo 2195435 3293369 := bstep (se 2 (by rfl) ⟨1235013, by rfl⟩ : syracuseStep 3293369 = 2470027) B2470027
theorem B2195579 : Blo 2195435 2195579 := bstep (se 1 (by rfl) ⟨1646684, by rfl⟩ : syracuseStep 2195579 = 3293369) B3293369
theorem B3516901 : Blo 2195435 3516901 := bbase (se 4 (by rfl) ⟨329709, by rfl⟩ : syracuseStep 3516901 = 659419) (by norm_num)
theorem B18756805 : Blo 2195435 18756805 := bstep (se 4 (by rfl) ⟨1758450, by rfl⟩ : syracuseStep 18756805 = 3516901) B3516901
theorem B25009073 : Blo 2195435 25009073 := bstep (se 2 (by rfl) ⟨9378402, by rfl⟩ : syracuseStep 25009073 = 18756805) B18756805
theorem B16672715 : Blo 2195435 16672715 := bstep (se 1 (by rfl) ⟨12504536, by rfl⟩ : syracuseStep 16672715 = 25009073) B25009073
theorem B11115143 : Blo 2195435 11115143 := bstep (se 1 (by rfl) ⟨8336357, by rfl⟩ : syracuseStep 11115143 = 16672715) B16672715
theorem B7410095 : Blo 2195435 7410095 := bstep (se 1 (by rfl) ⟨5557571, by rfl⟩ : syracuseStep 7410095 = 11115143) B11115143
theorem B4940063 : Blo 2195435 4940063 := bstep (se 1 (by rfl) ⟨3705047, by rfl⟩ : syracuseStep 4940063 = 7410095) B7410095
theorem B3293375 : Blo 2195435 3293375 := bstep (se 1 (by rfl) ⟨2470031, by rfl⟩ : syracuseStep 3293375 = 4940063) B4940063
theorem B2195583 : Blo 2195435 2195583 := bstep (se 1 (by rfl) ⟨1646687, by rfl⟩ : syracuseStep 2195583 = 3293375) B3293375
theorem B3293381 : Blo 2195435 3293381 := bbase (se 4 (by rfl) ⟨308754, by rfl⟩ : syracuseStep 3293381 = 617509) (by norm_num)
theorem B2195587 : Blo 2195435 2195587 := bstep (se 1 (by rfl) ⟨1646690, by rfl⟩ : syracuseStep 2195587 = 3293381) B3293381
theorem B3705061 : Blo 2195435 3705061 := bbase (se 4 (by rfl) ⟨347349, by rfl⟩ : syracuseStep 3705061 = 694699) (by norm_num)
theorem B4940081 : Blo 2195435 4940081 := bstep (se 2 (by rfl) ⟨1852530, by rfl⟩ : syracuseStep 4940081 = 3705061) B3705061
theorem B3293387 : Blo 2195435 3293387 := bstep (se 1 (by rfl) ⟨2470040, by rfl⟩ : syracuseStep 3293387 = 4940081) B4940081
theorem B2195591 : Blo 2195435 2195591 := bstep (se 1 (by rfl) ⟨1646693, by rfl⟩ : syracuseStep 2195591 = 3293387) B3293387
theorem B2470045 : Blo 2195435 2470045 := bbase (se 3 (by rfl) ⟨463133, by rfl⟩ : syracuseStep 2470045 = 926267) (by norm_num)
theorem B3293393 : Blo 2195435 3293393 := bstep (se 2 (by rfl) ⟨1235022, by rfl⟩ : syracuseStep 3293393 = 2470045) B2470045
theorem B2195595 : Blo 2195435 2195595 := bstep (se 1 (by rfl) ⟨1646696, by rfl⟩ : syracuseStep 2195595 = 3293393) B3293393
theorem B7410149 : Blo 2195435 7410149 := bbase (se 4 (by rfl) ⟨694701, by rfl⟩ : syracuseStep 7410149 = 1389403) (by norm_num)
theorem B4940099 : Blo 2195435 4940099 := bstep (se 1 (by rfl) ⟨3705074, by rfl⟩ : syracuseStep 4940099 = 7410149) B7410149
theorem B3293399 : Blo 2195435 3293399 := bstep (se 1 (by rfl) ⟨2470049, by rfl⟩ : syracuseStep 3293399 = 4940099) B4940099
theorem B2195599 : Blo 2195435 2195599 := bstep (se 1 (by rfl) ⟨1646699, by rfl⟩ : syracuseStep 2195599 = 3293399) B3293399
theorem B3293405 : Blo 2195435 3293405 := bbase (se 3 (by rfl) ⟨617513, by rfl⟩ : syracuseStep 3293405 = 1235027) (by norm_num)
theorem B2195603 : Blo 2195435 2195603 := bstep (se 1 (by rfl) ⟨1646702, by rfl⟩ : syracuseStep 2195603 = 3293405) B3293405
theorem B4940117 : Blo 2195435 4940117 := bbase (se 10 (by rfl) ⟨7236, by rfl⟩ : syracuseStep 4940117 = 14473) (by norm_num)
theorem B3293411 : Blo 2195435 3293411 := bstep (se 1 (by rfl) ⟨2470058, by rfl⟩ : syracuseStep 3293411 = 4940117) B4940117
theorem B2195607 : Blo 2195435 2195607 := bstep (se 1 (by rfl) ⟨1646705, by rfl⟩ : syracuseStep 2195607 = 3293411) B3293411
theorem B5275421 : Blo 2195435 5275421 := bbase (se 3 (by rfl) ⟨989141, by rfl⟩ : syracuseStep 5275421 = 1978283) (by norm_num)
theorem B3516947 : Blo 2195435 3516947 := bstep (se 1 (by rfl) ⟨2637710, by rfl⟩ : syracuseStep 3516947 = 5275421) B5275421
theorem B2344631 : Blo 2195435 2344631 := bstep (se 1 (by rfl) ⟨1758473, by rfl⟩ : syracuseStep 2344631 = 3516947) B3516947
theorem B6252349 : Blo 2195435 6252349 := bstep (se 3 (by rfl) ⟨1172315, by rfl⟩ : syracuseStep 6252349 = 2344631) B2344631
theorem B8336465 : Blo 2195435 8336465 := bstep (se 2 (by rfl) ⟨3126174, by rfl⟩ : syracuseStep 8336465 = 6252349) B6252349
theorem B5557643 : Blo 2195435 5557643 := bstep (se 1 (by rfl) ⟨4168232, by rfl⟩ : syracuseStep 5557643 = 8336465) B8336465
theorem B3705095 : Blo 2195435 3705095 := bstep (se 1 (by rfl) ⟨2778821, by rfl⟩ : syracuseStep 3705095 = 5557643) B5557643
theorem B2470063 : Blo 2195435 2470063 := bstep (se 1 (by rfl) ⟨1852547, by rfl⟩ : syracuseStep 2470063 = 3705095) B3705095
theorem B3293417 : Blo 2195435 3293417 := bstep (se 2 (by rfl) ⟨1235031, by rfl⟩ : syracuseStep 3293417 = 2470063) B2470063
theorem B2195611 : Blo 2195435 2195611 := bstep (se 1 (by rfl) ⟨1646708, by rfl⟩ : syracuseStep 2195611 = 3293417) B3293417
theorem B5347405 : Blo 2195435 5347405 := bbase (se 3 (by rfl) ⟨1002638, by rfl⟩ : syracuseStep 5347405 = 2005277) (by norm_num)
theorem B7129873 : Blo 2195435 7129873 := bstep (se 2 (by rfl) ⟨2673702, by rfl⟩ : syracuseStep 7129873 = 5347405) B5347405
theorem B9506497 : Blo 2195435 9506497 := bstep (se 2 (by rfl) ⟨3564936, by rfl⟩ : syracuseStep 9506497 = 7129873) B7129873
theorem B12675329 : Blo 2195435 12675329 := bstep (se 2 (by rfl) ⟨4753248, by rfl⟩ : syracuseStep 12675329 = 9506497) B9506497
theorem B8450219 : Blo 2195435 8450219 := bstep (se 1 (by rfl) ⟨6337664, by rfl⟩ : syracuseStep 8450219 = 12675329) B12675329
theorem B5633479 : Blo 2195435 5633479 := bstep (se 1 (by rfl) ⟨4225109, by rfl⟩ : syracuseStep 5633479 = 8450219) B8450219
theorem B7511305 : Blo 2195435 7511305 := bstep (se 2 (by rfl) ⟨2816739, by rfl⟩ : syracuseStep 7511305 = 5633479) B5633479
theorem B10015073 : Blo 2195435 10015073 := bstep (se 2 (by rfl) ⟨3755652, by rfl⟩ : syracuseStep 10015073 = 7511305) B7511305
theorem B6676715 : Blo 2195435 6676715 := bstep (se 1 (by rfl) ⟨5007536, by rfl⟩ : syracuseStep 6676715 = 10015073) B10015073
theorem B17804573 : Blo 2195435 17804573 := bstep (se 3 (by rfl) ⟨3338357, by rfl⟩ : syracuseStep 17804573 = 6676715) B6676715
theorem B11869715 : Blo 2195435 11869715 := bstep (se 1 (by rfl) ⟨8902286, by rfl⟩ : syracuseStep 11869715 = 17804573) B17804573
theorem B7913143 : Blo 2195435 7913143 := bstep (se 1 (by rfl) ⟨5934857, by rfl⟩ : syracuseStep 7913143 = 11869715) B11869715
theorem B42203429 : Blo 2195435 42203429 := bstep (se 4 (by rfl) ⟨3956571, by rfl⟩ : syracuseStep 42203429 = 7913143) B7913143
theorem B28135619 : Blo 2195435 28135619 := bstep (se 1 (by rfl) ⟨21101714, by rfl⟩ : syracuseStep 28135619 = 42203429) B42203429
theorem B18757079 : Blo 2195435 18757079 := bstep (se 1 (by rfl) ⟨14067809, by rfl⟩ : syracuseStep 18757079 = 28135619) B28135619
theorem B12504719 : Blo 2195435 12504719 := bstep (se 1 (by rfl) ⟨9378539, by rfl⟩ : syracuseStep 12504719 = 18757079) B18757079
theorem B8336479 : Blo 2195435 8336479 := bstep (se 1 (by rfl) ⟨6252359, by rfl⟩ : syracuseStep 8336479 = 12504719) B12504719
theorem B11115305 : Blo 2195435 11115305 := bstep (se 2 (by rfl) ⟨4168239, by rfl⟩ : syracuseStep 11115305 = 8336479) B8336479
theorem B7410203 : Blo 2195435 7410203 := bstep (se 1 (by rfl) ⟨5557652, by rfl⟩ : syracuseStep 7410203 = 11115305) B11115305
theorem B4940135 : Blo 2195435 4940135 := bstep (se 1 (by rfl) ⟨3705101, by rfl⟩ : syracuseStep 4940135 = 7410203) B7410203
theorem B3293423 : Blo 2195435 3293423 := bstep (se 1 (by rfl) ⟨2470067, by rfl⟩ : syracuseStep 3293423 = 4940135) B4940135
theorem B2195615 : Blo 2195435 2195615 := bstep (se 1 (by rfl) ⟨1646711, by rfl⟩ : syracuseStep 2195615 = 3293423) B3293423
theorem B3293429 : Blo 2195435 3293429 := bbase (se 5 (by rfl) ⟨154379, by rfl⟩ : syracuseStep 3293429 = 308759) (by norm_num)
theorem B2195619 : Blo 2195435 2195619 := bstep (se 1 (by rfl) ⟨1646714, by rfl⟩ : syracuseStep 2195619 = 3293429) B3293429
theorem B31652693 : Blo 2195435 31652693 := bbase (se 9 (by rfl) ⟨92732, by rfl⟩ : syracuseStep 31652693 = 185465) (by norm_num)
theorem B21101795 : Blo 2195435 21101795 := bstep (se 1 (by rfl) ⟨15826346, by rfl⟩ : syracuseStep 21101795 = 31652693) B31652693
theorem B14067863 : Blo 2195435 14067863 := bstep (se 1 (by rfl) ⟨10550897, by rfl⟩ : syracuseStep 14067863 = 21101795) B21101795
theorem B9378575 : Blo 2195435 9378575 := bstep (se 1 (by rfl) ⟨7033931, by rfl⟩ : syracuseStep 9378575 = 14067863) B14067863
theorem B6252383 : Blo 2195435 6252383 := bstep (se 1 (by rfl) ⟨4689287, by rfl⟩ : syracuseStep 6252383 = 9378575) B9378575
theorem B4168255 : Blo 2195435 4168255 := bstep (se 1 (by rfl) ⟨3126191, by rfl⟩ : syracuseStep 4168255 = 6252383) B6252383
theorem B5557673 : Blo 2195435 5557673 := bstep (se 2 (by rfl) ⟨2084127, by rfl⟩ : syracuseStep 5557673 = 4168255) B4168255
theorem B3705115 : Blo 2195435 3705115 := bstep (se 1 (by rfl) ⟨2778836, by rfl⟩ : syracuseStep 3705115 = 5557673) B5557673
theorem B4940153 : Blo 2195435 4940153 := bstep (se 2 (by rfl) ⟨1852557, by rfl⟩ : syracuseStep 4940153 = 3705115) B3705115
theorem B3293435 : Blo 2195435 3293435 := bstep (se 1 (by rfl) ⟨2470076, by rfl⟩ : syracuseStep 3293435 = 4940153) B4940153
theorem B2195623 : Blo 2195435 2195623 := bstep (se 1 (by rfl) ⟨1646717, by rfl⟩ : syracuseStep 2195623 = 3293435) B3293435
theorem B2470081 : Blo 2195435 2470081 := bbase (se 2 (by rfl) ⟨926280, by rfl⟩ : syracuseStep 2470081 = 1852561) (by norm_num)
theorem B3293441 : Blo 2195435 3293441 := bstep (se 2 (by rfl) ⟨1235040, by rfl⟩ : syracuseStep 3293441 = 2470081) B2470081
theorem B2195627 : Blo 2195435 2195627 := bstep (se 1 (by rfl) ⟨1646720, by rfl⟩ : syracuseStep 2195627 = 3293441) B3293441
theorem B5557693 : Blo 2195435 5557693 := bbase (se 3 (by rfl) ⟨1042067, by rfl⟩ : syracuseStep 5557693 = 2084135) (by norm_num)
theorem B7410257 : Blo 2195435 7410257 := bstep (se 2 (by rfl) ⟨2778846, by rfl⟩ : syracuseStep 7410257 = 5557693) B5557693
theorem B4940171 : Blo 2195435 4940171 := bstep (se 1 (by rfl) ⟨3705128, by rfl⟩ : syracuseStep 4940171 = 7410257) B7410257
theorem B3293447 : Blo 2195435 3293447 := bstep (se 1 (by rfl) ⟨2470085, by rfl⟩ : syracuseStep 3293447 = 4940171) B4940171
theorem B2195631 : Blo 2195435 2195631 := bstep (se 1 (by rfl) ⟨1646723, by rfl⟩ : syracuseStep 2195631 = 3293447) B3293447
theorem B3293453 : Blo 2195435 3293453 := bbase (se 3 (by rfl) ⟨617522, by rfl⟩ : syracuseStep 3293453 = 1235045) (by norm_num)
theorem B2195635 : Blo 2195435 2195635 := bstep (se 1 (by rfl) ⟨1646726, by rfl⟩ : syracuseStep 2195635 = 3293453) B3293453
theorem B4940189 : Blo 2195435 4940189 := bbase (se 3 (by rfl) ⟨926285, by rfl⟩ : syracuseStep 4940189 = 1852571) (by norm_num)
theorem B3293459 : Blo 2195435 3293459 := bstep (se 1 (by rfl) ⟨2470094, by rfl⟩ : syracuseStep 3293459 = 4940189) B4940189
theorem B2195639 : Blo 2195435 2195639 := bstep (se 1 (by rfl) ⟨1646729, by rfl⟩ : syracuseStep 2195639 = 3293459) B3293459
theorem B3705149 : Blo 2195435 3705149 := bbase (se 3 (by rfl) ⟨694715, by rfl⟩ : syracuseStep 3705149 = 1389431) (by norm_num)
theorem B2470099 : Blo 2195435 2470099 := bstep (se 1 (by rfl) ⟨1852574, by rfl⟩ : syracuseStep 2470099 = 3705149) B3705149
theorem B3293465 : Blo 2195435 3293465 := bstep (se 2 (by rfl) ⟨1235049, by rfl⟩ : syracuseStep 3293465 = 2470099) B2470099
theorem B2195643 : Blo 2195435 2195643 := bstep (se 1 (by rfl) ⟨1646732, by rfl⟩ : syracuseStep 2195643 = 3293465) B3293465
theorem B2344669 : Blo 2195435 2344669 := bbase (se 3 (by rfl) ⟨439625, by rfl⟩ : syracuseStep 2344669 = 879251) (by norm_num)
theorem B12504901 : Blo 2195435 12504901 := bstep (se 4 (by rfl) ⟨1172334, by rfl⟩ : syracuseStep 12504901 = 2344669) B2344669
theorem B16673201 : Blo 2195435 16673201 := bstep (se 2 (by rfl) ⟨6252450, by rfl⟩ : syracuseStep 16673201 = 12504901) B12504901
theorem B11115467 : Blo 2195435 11115467 := bstep (se 1 (by rfl) ⟨8336600, by rfl⟩ : syracuseStep 11115467 = 16673201) B16673201
theorem B7410311 : Blo 2195435 7410311 := bstep (se 1 (by rfl) ⟨5557733, by rfl⟩ : syracuseStep 7410311 = 11115467) B11115467
theorem B4940207 : Blo 2195435 4940207 := bstep (se 1 (by rfl) ⟨3705155, by rfl⟩ : syracuseStep 4940207 = 7410311) B7410311
theorem B3293471 : Blo 2195435 3293471 := bstep (se 1 (by rfl) ⟨2470103, by rfl⟩ : syracuseStep 3293471 = 4940207) B4940207
theorem B2195647 : Blo 2195435 2195647 := bstep (se 1 (by rfl) ⟨1646735, by rfl⟩ : syracuseStep 2195647 = 3293471) B3293471
theorem B3293477 : Blo 2195435 3293477 := bbase (se 4 (by rfl) ⟨308763, by rfl⟩ : syracuseStep 3293477 = 617527) (by norm_num)
theorem B2195651 : Blo 2195435 2195651 := bstep (se 1 (by rfl) ⟨1646738, by rfl⟩ : syracuseStep 2195651 = 3293477) B3293477
theorem B2778877 : Blo 2195435 2778877 := bbase (se 3 (by rfl) ⟨521039, by rfl⟩ : syracuseStep 2778877 = 1042079) (by norm_num)
theorem B3705169 : Blo 2195435 3705169 := bstep (se 2 (by rfl) ⟨1389438, by rfl⟩ : syracuseStep 3705169 = 2778877) B2778877
theorem B4940225 : Blo 2195435 4940225 := bstep (se 2 (by rfl) ⟨1852584, by rfl⟩ : syracuseStep 4940225 = 3705169) B3705169
theorem B3293483 : Blo 2195435 3293483 := bstep (se 1 (by rfl) ⟨2470112, by rfl⟩ : syracuseStep 3293483 = 4940225) B4940225
theorem B2195655 : Blo 2195435 2195655 := bstep (se 1 (by rfl) ⟨1646741, by rfl⟩ : syracuseStep 2195655 = 3293483) B3293483
theorem B2470117 : Blo 2195435 2470117 := bbase (se 4 (by rfl) ⟨231573, by rfl⟩ : syracuseStep 2470117 = 463147) (by norm_num)
theorem B3293489 : Blo 2195435 3293489 := bstep (se 2 (by rfl) ⟨1235058, by rfl⟩ : syracuseStep 3293489 = 2470117) B2470117
theorem B2195659 : Blo 2195435 2195659 := bstep (se 1 (by rfl) ⟨1646744, by rfl⟩ : syracuseStep 2195659 = 3293489) B3293489
theorem B4689373 : Blo 2195435 4689373 := bbase (se 3 (by rfl) ⟨879257, by rfl⟩ : syracuseStep 4689373 = 1758515) (by norm_num)
theorem B6252497 : Blo 2195435 6252497 := bstep (se 2 (by rfl) ⟨2344686, by rfl⟩ : syracuseStep 6252497 = 4689373) B4689373
theorem B4168331 : Blo 2195435 4168331 := bstep (se 1 (by rfl) ⟨3126248, by rfl⟩ : syracuseStep 4168331 = 6252497) B6252497
theorem B2778887 : Blo 2195435 2778887 := bstep (se 1 (by rfl) ⟨2084165, by rfl⟩ : syracuseStep 2778887 = 4168331) B4168331
theorem B7410365 : Blo 2195435 7410365 := bstep (se 3 (by rfl) ⟨1389443, by rfl⟩ : syracuseStep 7410365 = 2778887) B2778887
theorem B4940243 : Blo 2195435 4940243 := bstep (se 1 (by rfl) ⟨3705182, by rfl⟩ : syracuseStep 4940243 = 7410365) B7410365
theorem B3293495 : Blo 2195435 3293495 := bstep (se 1 (by rfl) ⟨2470121, by rfl⟩ : syracuseStep 3293495 = 4940243) B4940243
theorem B2195663 : Blo 2195435 2195663 := bstep (se 1 (by rfl) ⟨1646747, by rfl⟩ : syracuseStep 2195663 = 3293495) B3293495
theorem B3293501 : Blo 2195435 3293501 := bbase (se 3 (by rfl) ⟨617531, by rfl⟩ : syracuseStep 3293501 = 1235063) (by norm_num)
theorem B2195667 : Blo 2195435 2195667 := bstep (se 1 (by rfl) ⟨1646750, by rfl⟩ : syracuseStep 2195667 = 3293501) B3293501
theorem B4940261 : Blo 2195435 4940261 := bbase (se 4 (by rfl) ⟨463149, by rfl⟩ : syracuseStep 4940261 = 926299) (by norm_num)
theorem B3293507 : Blo 2195435 3293507 := bstep (se 1 (by rfl) ⟨2470130, by rfl⟩ : syracuseStep 3293507 = 4940261) B4940261
theorem B2195671 : Blo 2195435 2195671 := bstep (se 1 (by rfl) ⟨1646753, by rfl⟩ : syracuseStep 2195671 = 3293507) B3293507
theorem B5557805 : Blo 2195435 5557805 := bbase (se 3 (by rfl) ⟨1042088, by rfl⟩ : syracuseStep 5557805 = 2084177) (by norm_num)
theorem B3705203 : Blo 2195435 3705203 := bstep (se 1 (by rfl) ⟨2778902, by rfl⟩ : syracuseStep 3705203 = 5557805) B5557805
theorem B2470135 : Blo 2195435 2470135 := bstep (se 1 (by rfl) ⟨1852601, by rfl⟩ : syracuseStep 2470135 = 3705203) B3705203
theorem B3293513 : Blo 2195435 3293513 := bstep (se 2 (by rfl) ⟨1235067, by rfl⟩ : syracuseStep 3293513 = 2470135) B2470135
theorem B2195675 : Blo 2195435 2195675 := bstep (se 1 (by rfl) ⟨1646756, by rfl⟩ : syracuseStep 2195675 = 3293513) B3293513
theorem B3807005 : Blo 2195435 3807005 := bbase (se 3 (by rfl) ⟨713813, by rfl⟩ : syracuseStep 3807005 = 1427627) (by norm_num)
theorem B10152013 : Blo 2195435 10152013 := bstep (se 3 (by rfl) ⟨1903502, by rfl⟩ : syracuseStep 10152013 = 3807005) B3807005
theorem B13536017 : Blo 2195435 13536017 := bstep (se 2 (by rfl) ⟨5076006, by rfl⟩ : syracuseStep 13536017 = 10152013) B10152013
theorem B9024011 : Blo 2195435 9024011 := bstep (se 1 (by rfl) ⟨6768008, by rfl⟩ : syracuseStep 9024011 = 13536017) B13536017
theorem B6016007 : Blo 2195435 6016007 := bstep (se 1 (by rfl) ⟨4512005, by rfl⟩ : syracuseStep 6016007 = 9024011) B9024011
theorem B4010671 : Blo 2195435 4010671 := bstep (se 1 (by rfl) ⟨3008003, by rfl⟩ : syracuseStep 4010671 = 6016007) B6016007
theorem B5347561 : Blo 2195435 5347561 := bstep (se 2 (by rfl) ⟨2005335, by rfl⟩ : syracuseStep 5347561 = 4010671) B4010671
theorem B7130081 : Blo 2195435 7130081 := bstep (se 2 (by rfl) ⟨2673780, by rfl⟩ : syracuseStep 7130081 = 5347561) B5347561
theorem B4753387 : Blo 2195435 4753387 := bstep (se 1 (by rfl) ⟨3565040, by rfl⟩ : syracuseStep 4753387 = 7130081) B7130081
theorem B25351397 : Blo 2195435 25351397 := bstep (se 4 (by rfl) ⟨2376693, by rfl⟩ : syracuseStep 25351397 = 4753387) B4753387
theorem B16900931 : Blo 2195435 16900931 := bstep (se 1 (by rfl) ⟨12675698, by rfl⟩ : syracuseStep 16900931 = 25351397) B25351397
theorem B45069149 : Blo 2195435 45069149 := bstep (se 3 (by rfl) ⟨8450465, by rfl⟩ : syracuseStep 45069149 = 16900931) B16900931
theorem B120184397 : Blo 2195435 120184397 := bstep (se 3 (by rfl) ⟨22534574, by rfl⟩ : syracuseStep 120184397 = 45069149) B45069149
theorem B80122931 : Blo 2195435 80122931 := bstep (se 1 (by rfl) ⟨60092198, by rfl⟩ : syracuseStep 80122931 = 120184397) B120184397
theorem B53415287 : Blo 2195435 53415287 := bstep (se 1 (by rfl) ⟨40061465, by rfl⟩ : syracuseStep 53415287 = 80122931) B80122931
theorem B35610191 : Blo 2195435 35610191 := bstep (se 1 (by rfl) ⟨26707643, by rfl⟩ : syracuseStep 35610191 = 53415287) B53415287
theorem B23740127 : Blo 2195435 23740127 := bstep (se 1 (by rfl) ⟨17805095, by rfl⟩ : syracuseStep 23740127 = 35610191) B35610191
theorem B15826751 : Blo 2195435 15826751 := bstep (se 1 (by rfl) ⟨11870063, by rfl⟩ : syracuseStep 15826751 = 23740127) B23740127
theorem B10551167 : Blo 2195435 10551167 := bstep (se 1 (by rfl) ⟨7913375, by rfl⟩ : syracuseStep 10551167 = 15826751) B15826751
theorem B7034111 : Blo 2195435 7034111 := bstep (se 1 (by rfl) ⟨5275583, by rfl⟩ : syracuseStep 7034111 = 10551167) B10551167
theorem B4689407 : Blo 2195435 4689407 := bstep (se 1 (by rfl) ⟨3517055, by rfl⟩ : syracuseStep 4689407 = 7034111) B7034111
theorem B3126271 : Blo 2195435 3126271 := bstep (se 1 (by rfl) ⟨2344703, by rfl⟩ : syracuseStep 3126271 = 4689407) B4689407
theorem B4168361 : Blo 2195435 4168361 := bstep (se 2 (by rfl) ⟨1563135, by rfl⟩ : syracuseStep 4168361 = 3126271) B3126271
theorem B11115629 : Blo 2195435 11115629 := bstep (se 3 (by rfl) ⟨2084180, by rfl⟩ : syracuseStep 11115629 = 4168361) B4168361
theorem B7410419 : Blo 2195435 7410419 := bstep (se 1 (by rfl) ⟨5557814, by rfl⟩ : syracuseStep 7410419 = 11115629) B11115629
theorem B4940279 : Blo 2195435 4940279 := bstep (se 1 (by rfl) ⟨3705209, by rfl⟩ : syracuseStep 4940279 = 7410419) B7410419
theorem B3293519 : Blo 2195435 3293519 := bstep (se 1 (by rfl) ⟨2470139, by rfl⟩ : syracuseStep 3293519 = 4940279) B4940279
theorem B2195679 : Blo 2195435 2195679 := bstep (se 1 (by rfl) ⟨1646759, by rfl⟩ : syracuseStep 2195679 = 3293519) B3293519
theorem B3293525 : Blo 2195435 3293525 := bbase (se 10 (by rfl) ⟨4824, by rfl⟩ : syracuseStep 3293525 = 9649) (by norm_num)
theorem B2195683 : Blo 2195435 2195683 := bstep (se 1 (by rfl) ⟨1646762, by rfl⟩ : syracuseStep 2195683 = 3293525) B3293525
theorem B6252565 : Blo 2195435 6252565 := bbase (se 6 (by rfl) ⟨146544, by rfl⟩ : syracuseStep 6252565 = 293089) (by norm_num)
theorem B8336753 : Blo 2195435 8336753 := bstep (se 2 (by rfl) ⟨3126282, by rfl⟩ : syracuseStep 8336753 = 6252565) B6252565
theorem B5557835 : Blo 2195435 5557835 := bstep (se 1 (by rfl) ⟨4168376, by rfl⟩ : syracuseStep 5557835 = 8336753) B8336753
theorem B3705223 : Blo 2195435 3705223 := bstep (se 1 (by rfl) ⟨2778917, by rfl⟩ : syracuseStep 3705223 = 5557835) B5557835
theorem B4940297 : Blo 2195435 4940297 := bstep (se 2 (by rfl) ⟨1852611, by rfl⟩ : syracuseStep 4940297 = 3705223) B3705223
theorem B3293531 : Blo 2195435 3293531 := bstep (se 1 (by rfl) ⟨2470148, by rfl⟩ : syracuseStep 3293531 = 4940297) B4940297
theorem B2195687 : Blo 2195435 2195687 := bstep (se 1 (by rfl) ⟨1646765, by rfl⟩ : syracuseStep 2195687 = 3293531) B3293531
theorem B2470153 : Blo 2195435 2470153 := bbase (se 2 (by rfl) ⟨926307, by rfl⟩ : syracuseStep 2470153 = 1852615) (by norm_num)
theorem B3293537 : Blo 2195435 3293537 := bstep (se 2 (by rfl) ⟨1235076, by rfl⟩ : syracuseStep 3293537 = 2470153) B2470153
theorem B2195691 : Blo 2195435 2195691 := bstep (se 1 (by rfl) ⟨1646768, by rfl⟩ : syracuseStep 2195691 = 3293537) B3293537
theorem B5275621 : Blo 2195435 5275621 := bbase (se 4 (by rfl) ⟨494589, by rfl⟩ : syracuseStep 5275621 = 989179) (by norm_num)
theorem B28136645 : Blo 2195435 28136645 := bstep (se 4 (by rfl) ⟨2637810, by rfl⟩ : syracuseStep 28136645 = 5275621) B5275621
theorem B18757763 : Blo 2195435 18757763 := bstep (se 1 (by rfl) ⟨14068322, by rfl⟩ : syracuseStep 18757763 = 28136645) B28136645
theorem B12505175 : Blo 2195435 12505175 := bstep (se 1 (by rfl) ⟨9378881, by rfl⟩ : syracuseStep 12505175 = 18757763) B18757763
theorem B8336783 : Blo 2195435 8336783 := bstep (se 1 (by rfl) ⟨6252587, by rfl⟩ : syracuseStep 8336783 = 12505175) B12505175
theorem B5557855 : Blo 2195435 5557855 := bstep (se 1 (by rfl) ⟨4168391, by rfl⟩ : syracuseStep 5557855 = 8336783) B8336783
theorem B7410473 : Blo 2195435 7410473 := bstep (se 2 (by rfl) ⟨2778927, by rfl⟩ : syracuseStep 7410473 = 5557855) B5557855
theorem B4940315 : Blo 2195435 4940315 := bstep (se 1 (by rfl) ⟨3705236, by rfl⟩ : syracuseStep 4940315 = 7410473) B7410473
theorem B3293543 : Blo 2195435 3293543 := bstep (se 1 (by rfl) ⟨2470157, by rfl⟩ : syracuseStep 3293543 = 4940315) B4940315
theorem B2195695 : Blo 2195435 2195695 := bstep (se 1 (by rfl) ⟨1646771, by rfl⟩ : syracuseStep 2195695 = 3293543) B3293543
theorem B3293549 : Blo 2195435 3293549 := bbase (se 3 (by rfl) ⟨617540, by rfl⟩ : syracuseStep 3293549 = 1235081) (by norm_num)
theorem B2195699 : Blo 2195435 2195699 := bstep (se 1 (by rfl) ⟨1646774, by rfl⟩ : syracuseStep 2195699 = 3293549) B3293549
theorem B4940333 : Blo 2195435 4940333 := bbase (se 3 (by rfl) ⟨926312, by rfl⟩ : syracuseStep 4940333 = 1852625) (by norm_num)
theorem B3293555 : Blo 2195435 3293555 := bstep (se 1 (by rfl) ⟨2470166, by rfl⟩ : syracuseStep 3293555 = 4940333) B4940333
theorem B2195703 : Blo 2195435 2195703 := bstep (se 1 (by rfl) ⟨1646777, by rfl⟩ : syracuseStep 2195703 = 3293555) B3293555
theorem B7913477 : Blo 2195435 7913477 := bbase (se 4 (by rfl) ⟨741888, by rfl⟩ : syracuseStep 7913477 = 1483777) (by norm_num)
theorem B21102605 : Blo 2195435 21102605 := bstep (se 3 (by rfl) ⟨3956738, by rfl⟩ : syracuseStep 21102605 = 7913477) B7913477
theorem B14068403 : Blo 2195435 14068403 := bstep (se 1 (by rfl) ⟨10551302, by rfl⟩ : syracuseStep 14068403 = 21102605) B21102605
theorem B9378935 : Blo 2195435 9378935 := bstep (se 1 (by rfl) ⟨7034201, by rfl⟩ : syracuseStep 9378935 = 14068403) B14068403
theorem B6252623 : Blo 2195435 6252623 := bstep (se 1 (by rfl) ⟨4689467, by rfl⟩ : syracuseStep 6252623 = 9378935) B9378935
theorem B4168415 : Blo 2195435 4168415 := bstep (se 1 (by rfl) ⟨3126311, by rfl⟩ : syracuseStep 4168415 = 6252623) B6252623
theorem B2778943 : Blo 2195435 2778943 := bstep (se 1 (by rfl) ⟨2084207, by rfl⟩ : syracuseStep 2778943 = 4168415) B4168415
theorem B3705257 : Blo 2195435 3705257 := bstep (se 2 (by rfl) ⟨1389471, by rfl⟩ : syracuseStep 3705257 = 2778943) B2778943
theorem B2470171 : Blo 2195435 2470171 := bstep (se 1 (by rfl) ⟨1852628, by rfl⟩ : syracuseStep 2470171 = 3705257) B3705257
theorem B3293561 : Blo 2195435 3293561 := bstep (se 2 (by rfl) ⟨1235085, by rfl⟩ : syracuseStep 3293561 = 2470171) B2470171
theorem B2195707 : Blo 2195435 2195707 := bstep (se 1 (by rfl) ⟨1646780, by rfl⟩ : syracuseStep 2195707 = 3293561) B3293561
theorem B37515797 : Blo 2195435 37515797 := bbase (se 6 (by rfl) ⟨879276, by rfl⟩ : syracuseStep 37515797 = 1758553) (by norm_num)
theorem B25010531 : Blo 2195435 25010531 := bstep (se 1 (by rfl) ⟨18757898, by rfl⟩ : syracuseStep 25010531 = 37515797) B37515797
theorem B16673687 : Blo 2195435 16673687 := bstep (se 1 (by rfl) ⟨12505265, by rfl⟩ : syracuseStep 16673687 = 25010531) B25010531
theorem B11115791 : Blo 2195435 11115791 := bstep (se 1 (by rfl) ⟨8336843, by rfl⟩ : syracuseStep 11115791 = 16673687) B16673687
theorem B7410527 : Blo 2195435 7410527 := bstep (se 1 (by rfl) ⟨5557895, by rfl⟩ : syracuseStep 7410527 = 11115791) B11115791
theorem B4940351 : Blo 2195435 4940351 := bstep (se 1 (by rfl) ⟨3705263, by rfl⟩ : syracuseStep 4940351 = 7410527) B7410527
theorem B3293567 : Blo 2195435 3293567 := bstep (se 1 (by rfl) ⟨2470175, by rfl⟩ : syracuseStep 3293567 = 4940351) B4940351
theorem B2195711 : Blo 2195435 2195711 := bstep (se 1 (by rfl) ⟨1646783, by rfl⟩ : syracuseStep 2195711 = 3293567) B3293567
theorem B3293573 : Blo 2195435 3293573 := bbase (se 4 (by rfl) ⟨308772, by rfl⟩ : syracuseStep 3293573 = 617545) (by norm_num)
theorem B2195715 : Blo 2195435 2195715 := bstep (se 1 (by rfl) ⟨1646786, by rfl⟩ : syracuseStep 2195715 = 3293573) B3293573
theorem B3705277 : Blo 2195435 3705277 := bbase (se 3 (by rfl) ⟨694739, by rfl⟩ : syracuseStep 3705277 = 1389479) (by norm_num)
theorem B4940369 : Blo 2195435 4940369 := bstep (se 2 (by rfl) ⟨1852638, by rfl⟩ : syracuseStep 4940369 = 3705277) B3705277
theorem B3293579 : Blo 2195435 3293579 := bstep (se 1 (by rfl) ⟨2470184, by rfl⟩ : syracuseStep 3293579 = 4940369) B4940369
theorem B2195719 : Blo 2195435 2195719 := bstep (se 1 (by rfl) ⟨1646789, by rfl⟩ : syracuseStep 2195719 = 3293579) B3293579
theorem B2470189 : Blo 2195435 2470189 := bbase (se 3 (by rfl) ⟨463160, by rfl⟩ : syracuseStep 2470189 = 926321) (by norm_num)
theorem B3293585 : Blo 2195435 3293585 := bstep (se 2 (by rfl) ⟨1235094, by rfl⟩ : syracuseStep 3293585 = 2470189) B2470189
theorem B2195723 : Blo 2195435 2195723 := bstep (se 1 (by rfl) ⟨1646792, by rfl⟩ : syracuseStep 2195723 = 3293585) B3293585
theorem B7410581 : Blo 2195435 7410581 := bbase (se 6 (by rfl) ⟨173685, by rfl⟩ : syracuseStep 7410581 = 347371) (by norm_num)
theorem B4940387 : Blo 2195435 4940387 := bstep (se 1 (by rfl) ⟨3705290, by rfl⟩ : syracuseStep 4940387 = 7410581) B7410581
theorem B3293591 : Blo 2195435 3293591 := bstep (se 1 (by rfl) ⟨2470193, by rfl⟩ : syracuseStep 3293591 = 4940387) B4940387
theorem B2195727 : Blo 2195435 2195727 := bstep (se 1 (by rfl) ⟨1646795, by rfl⟩ : syracuseStep 2195727 = 3293591) B3293591
theorem B3293597 : Blo 2195435 3293597 := bbase (se 3 (by rfl) ⟨617549, by rfl⟩ : syracuseStep 3293597 = 1235099) (by norm_num)
theorem B2195731 : Blo 2195435 2195731 := bstep (se 1 (by rfl) ⟨1646798, by rfl⟩ : syracuseStep 2195731 = 3293597) B3293597
theorem B4940405 : Blo 2195435 4940405 := bbase (se 5 (by rfl) ⟨231581, by rfl⟩ : syracuseStep 4940405 = 463163) (by norm_num)
theorem B3293603 : Blo 2195435 3293603 := bstep (se 1 (by rfl) ⟨2470202, by rfl⟩ : syracuseStep 3293603 = 4940405) B4940405
theorem B2195735 : Blo 2195435 2195735 := bstep (se 1 (by rfl) ⟨1646801, by rfl⟩ : syracuseStep 2195735 = 3293603) B3293603
theorem B10695413 : Blo 2195435 10695413 := bbase (se 5 (by rfl) ⟨501347, by rfl⟩ : syracuseStep 10695413 = 1002695) (by norm_num)
theorem B7130275 : Blo 2195435 7130275 := bstep (se 1 (by rfl) ⟨5347706, by rfl⟩ : syracuseStep 7130275 = 10695413) B10695413
theorem B38028133 : Blo 2195435 38028133 := bstep (se 4 (by rfl) ⟨3565137, by rfl⟩ : syracuseStep 38028133 = 7130275) B7130275
theorem B202816709 : Blo 2195435 202816709 := bstep (se 4 (by rfl) ⟨19014066, by rfl⟩ : syracuseStep 202816709 = 38028133) B38028133
theorem B135211139 : Blo 2195435 135211139 := bstep (se 1 (by rfl) ⟨101408354, by rfl⟩ : syracuseStep 135211139 = 202816709) B202816709
theorem B90140759 : Blo 2195435 90140759 := bstep (se 1 (by rfl) ⟨67605569, by rfl⟩ : syracuseStep 90140759 = 135211139) B135211139
theorem B60093839 : Blo 2195435 60093839 := bstep (se 1 (by rfl) ⟨45070379, by rfl⟩ : syracuseStep 60093839 = 90140759) B90140759
theorem B40062559 : Blo 2195435 40062559 := bstep (se 1 (by rfl) ⟨30046919, by rfl⟩ : syracuseStep 40062559 = 60093839) B60093839
theorem B53416745 : Blo 2195435 53416745 := bstep (se 2 (by rfl) ⟨20031279, by rfl⟩ : syracuseStep 53416745 = 40062559) B40062559
theorem B35611163 : Blo 2195435 35611163 := bstep (se 1 (by rfl) ⟨26708372, by rfl⟩ : syracuseStep 35611163 = 53416745) B53416745
theorem B23740775 : Blo 2195435 23740775 := bstep (se 1 (by rfl) ⟨17805581, by rfl⟩ : syracuseStep 23740775 = 35611163) B35611163
theorem B15827183 : Blo 2195435 15827183 := bstep (se 1 (by rfl) ⟨11870387, by rfl⟩ : syracuseStep 15827183 = 23740775) B23740775
theorem B10551455 : Blo 2195435 10551455 := bstep (se 1 (by rfl) ⟨7913591, by rfl⟩ : syracuseStep 10551455 = 15827183) B15827183
theorem B7034303 : Blo 2195435 7034303 := bstep (se 1 (by rfl) ⟨5275727, by rfl⟩ : syracuseStep 7034303 = 10551455) B10551455
theorem B18758141 : Blo 2195435 18758141 := bstep (se 3 (by rfl) ⟨3517151, by rfl⟩ : syracuseStep 18758141 = 7034303) B7034303
theorem B12505427 : Blo 2195435 12505427 := bstep (se 1 (by rfl) ⟨9379070, by rfl⟩ : syracuseStep 12505427 = 18758141) B18758141
theorem B8336951 : Blo 2195435 8336951 := bstep (se 1 (by rfl) ⟨6252713, by rfl⟩ : syracuseStep 8336951 = 12505427) B12505427
theorem B5557967 : Blo 2195435 5557967 := bstep (se 1 (by rfl) ⟨4168475, by rfl⟩ : syracuseStep 5557967 = 8336951) B8336951
theorem B3705311 : Blo 2195435 3705311 := bstep (se 1 (by rfl) ⟨2778983, by rfl⟩ : syracuseStep 3705311 = 5557967) B5557967
theorem B2470207 : Blo 2195435 2470207 := bstep (se 1 (by rfl) ⟨1852655, by rfl⟩ : syracuseStep 2470207 = 3705311) B3705311
theorem B3293609 : Blo 2195435 3293609 := bstep (se 2 (by rfl) ⟨1235103, by rfl⟩ : syracuseStep 3293609 = 2470207) B2470207
theorem B2195739 : Blo 2195435 2195739 := bstep (se 1 (by rfl) ⟨1646804, by rfl⟩ : syracuseStep 2195739 = 3293609) B3293609
theorem B8336965 : Blo 2195435 8336965 := bbase (se 4 (by rfl) ⟨781590, by rfl⟩ : syracuseStep 8336965 = 1563181) (by norm_num)
theorem B11115953 : Blo 2195435 11115953 := bstep (se 2 (by rfl) ⟨4168482, by rfl⟩ : syracuseStep 11115953 = 8336965) B8336965
theorem B7410635 : Blo 2195435 7410635 := bstep (se 1 (by rfl) ⟨5557976, by rfl⟩ : syracuseStep 7410635 = 11115953) B11115953
theorem B4940423 : Blo 2195435 4940423 := bstep (se 1 (by rfl) ⟨3705317, by rfl⟩ : syracuseStep 4940423 = 7410635) B7410635
theorem B3293615 : Blo 2195435 3293615 := bstep (se 1 (by rfl) ⟨2470211, by rfl⟩ : syracuseStep 3293615 = 4940423) B4940423
theorem B2195743 : Blo 2195435 2195743 := bstep (se 1 (by rfl) ⟨1646807, by rfl⟩ : syracuseStep 2195743 = 3293615) B3293615
theorem B3293621 : Blo 2195435 3293621 := bbase (se 5 (by rfl) ⟨154388, by rfl⟩ : syracuseStep 3293621 = 308777) (by norm_num)
theorem B2195747 : Blo 2195435 2195747 := bstep (se 1 (by rfl) ⟨1646810, by rfl⟩ : syracuseStep 2195747 = 3293621) B3293621
theorem B5557997 : Blo 2195435 5557997 := bbase (se 3 (by rfl) ⟨1042124, by rfl⟩ : syracuseStep 5557997 = 2084249) (by norm_num)
theorem B3705331 : Blo 2195435 3705331 := bstep (se 1 (by rfl) ⟨2778998, by rfl⟩ : syracuseStep 3705331 = 5557997) B5557997
theorem B4940441 : Blo 2195435 4940441 := bstep (se 2 (by rfl) ⟨1852665, by rfl⟩ : syracuseStep 4940441 = 3705331) B3705331
theorem B3293627 : Blo 2195435 3293627 := bstep (se 1 (by rfl) ⟨2470220, by rfl⟩ : syracuseStep 3293627 = 4940441) B4940441
theorem B2195751 : Blo 2195435 2195751 := bstep (se 1 (by rfl) ⟨1646813, by rfl⟩ : syracuseStep 2195751 = 3293627) B3293627
theorem B2470225 : Blo 2195435 2470225 := bbase (se 2 (by rfl) ⟨926334, by rfl⟩ : syracuseStep 2470225 = 1852669) (by norm_num)
theorem B3293633 : Blo 2195435 3293633 := bstep (se 2 (by rfl) ⟨1235112, by rfl⟩ : syracuseStep 3293633 = 2470225) B2470225
theorem B2195755 : Blo 2195435 2195755 := bstep (se 1 (by rfl) ⟨1646816, by rfl⟩ : syracuseStep 2195755 = 3293633) B3293633
theorem B2344789 : Blo 2195435 2344789 := bbase (se 9 (by rfl) ⟨6869, by rfl⟩ : syracuseStep 2344789 = 13739) (by norm_num)
theorem B3126385 : Blo 2195435 3126385 := bstep (se 2 (by rfl) ⟨1172394, by rfl⟩ : syracuseStep 3126385 = 2344789) B2344789
theorem B4168513 : Blo 2195435 4168513 := bstep (se 2 (by rfl) ⟨1563192, by rfl⟩ : syracuseStep 4168513 = 3126385) B3126385
theorem B5558017 : Blo 2195435 5558017 := bstep (se 2 (by rfl) ⟨2084256, by rfl⟩ : syracuseStep 5558017 = 4168513) B4168513
theorem B7410689 : Blo 2195435 7410689 := bstep (se 2 (by rfl) ⟨2779008, by rfl⟩ : syracuseStep 7410689 = 5558017) B5558017
theorem B4940459 : Blo 2195435 4940459 := bstep (se 1 (by rfl) ⟨3705344, by rfl⟩ : syracuseStep 4940459 = 7410689) B7410689
theorem B3293639 : Blo 2195435 3293639 := bstep (se 1 (by rfl) ⟨2470229, by rfl⟩ : syracuseStep 3293639 = 4940459) B4940459
theorem B2195759 : Blo 2195435 2195759 := bstep (se 1 (by rfl) ⟨1646819, by rfl⟩ : syracuseStep 2195759 = 3293639) B3293639
theorem B3293645 : Blo 2195435 3293645 := bbase (se 3 (by rfl) ⟨617558, by rfl⟩ : syracuseStep 3293645 = 1235117) (by norm_num)
theorem B2195763 : Blo 2195435 2195763 := bstep (se 1 (by rfl) ⟨1646822, by rfl⟩ : syracuseStep 2195763 = 3293645) B3293645
theorem B4940477 : Blo 2195435 4940477 := bbase (se 3 (by rfl) ⟨926339, by rfl⟩ : syracuseStep 4940477 = 1852679) (by norm_num)
theorem B3293651 : Blo 2195435 3293651 := bstep (se 1 (by rfl) ⟨2470238, by rfl⟩ : syracuseStep 3293651 = 4940477) B4940477
theorem B2195767 : Blo 2195435 2195767 := bstep (se 1 (by rfl) ⟨1646825, by rfl⟩ : syracuseStep 2195767 = 3293651) B3293651
theorem B3705365 : Blo 2195435 3705365 := bbase (se 6 (by rfl) ⟨86844, by rfl⟩ : syracuseStep 3705365 = 173689) (by norm_num)
theorem B2470243 : Blo 2195435 2470243 := bstep (se 1 (by rfl) ⟨1852682, by rfl⟩ : syracuseStep 2470243 = 3705365) B3705365
theorem B3293657 : Blo 2195435 3293657 := bstep (se 2 (by rfl) ⟨1235121, by rfl⟩ : syracuseStep 3293657 = 2470243) B2470243
theorem B2195771 : Blo 2195435 2195771 := bstep (se 1 (by rfl) ⟨1646828, by rfl⟩ : syracuseStep 2195771 = 3293657) B3293657
theorem B21103253 : Blo 2195435 21103253 := bbase (se 6 (by rfl) ⟨494607, by rfl⟩ : syracuseStep 21103253 = 989215) (by norm_num)
theorem B14068835 : Blo 2195435 14068835 := bstep (se 1 (by rfl) ⟨10551626, by rfl⟩ : syracuseStep 14068835 = 21103253) B21103253
theorem B9379223 : Blo 2195435 9379223 := bstep (se 1 (by rfl) ⟨7034417, by rfl⟩ : syracuseStep 9379223 = 14068835) B14068835
theorem B6252815 : Blo 2195435 6252815 := bstep (se 1 (by rfl) ⟨4689611, by rfl⟩ : syracuseStep 6252815 = 9379223) B9379223
theorem B16674173 : Blo 2195435 16674173 := bstep (se 3 (by rfl) ⟨3126407, by rfl⟩ : syracuseStep 16674173 = 6252815) B6252815
theorem B11116115 : Blo 2195435 11116115 := bstep (se 1 (by rfl) ⟨8337086, by rfl⟩ : syracuseStep 11116115 = 16674173) B16674173
theorem B7410743 : Blo 2195435 7410743 := bstep (se 1 (by rfl) ⟨5558057, by rfl⟩ : syracuseStep 7410743 = 11116115) B11116115
theorem B4940495 : Blo 2195435 4940495 := bstep (se 1 (by rfl) ⟨3705371, by rfl⟩ : syracuseStep 4940495 = 7410743) B7410743
theorem B3293663 : Blo 2195435 3293663 := bstep (se 1 (by rfl) ⟨2470247, by rfl⟩ : syracuseStep 3293663 = 4940495) B4940495
theorem B2195775 : Blo 2195435 2195775 := bstep (se 1 (by rfl) ⟨1646831, by rfl⟩ : syracuseStep 2195775 = 3293663) B3293663
theorem B3293669 : Blo 2195435 3293669 := bbase (se 4 (by rfl) ⟨308781, by rfl⟩ : syracuseStep 3293669 = 617563) (by norm_num)
theorem B2195779 : Blo 2195435 2195779 := bstep (se 1 (by rfl) ⟨1646834, by rfl⟩ : syracuseStep 2195779 = 3293669) B3293669
theorem B4451485 : Blo 2195435 4451485 := bbase (se 3 (by rfl) ⟨834653, by rfl⟩ : syracuseStep 4451485 = 1669307) (by norm_num)
theorem B5935313 : Blo 2195435 5935313 := bstep (se 2 (by rfl) ⟨2225742, by rfl⟩ : syracuseStep 5935313 = 4451485) B4451485
theorem B15827501 : Blo 2195435 15827501 := bstep (se 3 (by rfl) ⟨2967656, by rfl⟩ : syracuseStep 15827501 = 5935313) B5935313
theorem B10551667 : Blo 2195435 10551667 := bstep (se 1 (by rfl) ⟨7913750, by rfl⟩ : syracuseStep 10551667 = 15827501) B15827501
theorem B14068889 : Blo 2195435 14068889 := bstep (se 2 (by rfl) ⟨5275833, by rfl⟩ : syracuseStep 14068889 = 10551667) B10551667
theorem B9379259 : Blo 2195435 9379259 := bstep (se 1 (by rfl) ⟨7034444, by rfl⟩ : syracuseStep 9379259 = 14068889) B14068889
theorem B6252839 : Blo 2195435 6252839 := bstep (se 1 (by rfl) ⟨4689629, by rfl⟩ : syracuseStep 6252839 = 9379259) B9379259
theorem B4168559 : Blo 2195435 4168559 := bstep (se 1 (by rfl) ⟨3126419, by rfl⟩ : syracuseStep 4168559 = 6252839) B6252839
theorem B2779039 : Blo 2195435 2779039 := bstep (se 1 (by rfl) ⟨2084279, by rfl⟩ : syracuseStep 2779039 = 4168559) B4168559
theorem B3705385 : Blo 2195435 3705385 := bstep (se 2 (by rfl) ⟨1389519, by rfl⟩ : syracuseStep 3705385 = 2779039) B2779039
theorem B4940513 : Blo 2195435 4940513 := bstep (se 2 (by rfl) ⟨1852692, by rfl⟩ : syracuseStep 4940513 = 3705385) B3705385
theorem B3293675 : Blo 2195435 3293675 := bstep (se 1 (by rfl) ⟨2470256, by rfl⟩ : syracuseStep 3293675 = 4940513) B4940513
theorem B2195783 : Blo 2195435 2195783 := bstep (se 1 (by rfl) ⟨1646837, by rfl⟩ : syracuseStep 2195783 = 3293675) B3293675
theorem B2470261 : Blo 2195435 2470261 := bbase (se 5 (by rfl) ⟨115793, by rfl⟩ : syracuseStep 2470261 = 231587) (by norm_num)
theorem B3293681 : Blo 2195435 3293681 := bstep (se 2 (by rfl) ⟨1235130, by rfl⟩ : syracuseStep 3293681 = 2470261) B2470261
theorem B2195787 : Blo 2195435 2195787 := bstep (se 1 (by rfl) ⟨1646840, by rfl⟩ : syracuseStep 2195787 = 3293681) B3293681
theorem B2779049 : Blo 2195435 2779049 := bbase (se 2 (by rfl) ⟨1042143, by rfl⟩ : syracuseStep 2779049 = 2084287) (by norm_num)
theorem B7410797 : Blo 2195435 7410797 := bstep (se 3 (by rfl) ⟨1389524, by rfl⟩ : syracuseStep 7410797 = 2779049) B2779049
theorem B4940531 : Blo 2195435 4940531 := bstep (se 1 (by rfl) ⟨3705398, by rfl⟩ : syracuseStep 4940531 = 7410797) B7410797
theorem B3293687 : Blo 2195435 3293687 := bstep (se 1 (by rfl) ⟨2470265, by rfl⟩ : syracuseStep 3293687 = 4940531) B4940531
theorem B2195791 : Blo 2195435 2195791 := bstep (se 1 (by rfl) ⟨1646843, by rfl⟩ : syracuseStep 2195791 = 3293687) B3293687
theorem B3293693 : Blo 2195435 3293693 := bbase (se 3 (by rfl) ⟨617567, by rfl⟩ : syracuseStep 3293693 = 1235135) (by norm_num)
theorem B2195795 : Blo 2195435 2195795 := bstep (se 1 (by rfl) ⟨1646846, by rfl⟩ : syracuseStep 2195795 = 3293693) B3293693
theorem B4940549 : Blo 2195435 4940549 := bbase (se 4 (by rfl) ⟨463176, by rfl⟩ : syracuseStep 4940549 = 926353) (by norm_num)
theorem B3293699 : Blo 2195435 3293699 := bstep (se 1 (by rfl) ⟨2470274, by rfl⟩ : syracuseStep 3293699 = 4940549) B4940549
theorem B2195799 : Blo 2195435 2195799 := bstep (se 1 (by rfl) ⟨1646849, by rfl⟩ : syracuseStep 2195799 = 3293699) B3293699
theorem B4168597 : Blo 2195435 4168597 := bbase (se 6 (by rfl) ⟨97701, by rfl⟩ : syracuseStep 4168597 = 195403) (by norm_num)
theorem B5558129 : Blo 2195435 5558129 := bstep (se 2 (by rfl) ⟨2084298, by rfl⟩ : syracuseStep 5558129 = 4168597) B4168597
theorem B3705419 : Blo 2195435 3705419 := bstep (se 1 (by rfl) ⟨2779064, by rfl⟩ : syracuseStep 3705419 = 5558129) B5558129
theorem B2470279 : Blo 2195435 2470279 := bstep (se 1 (by rfl) ⟨1852709, by rfl⟩ : syracuseStep 2470279 = 3705419) B3705419
theorem B3293705 : Blo 2195435 3293705 := bstep (se 2 (by rfl) ⟨1235139, by rfl⟩ : syracuseStep 3293705 = 2470279) B2470279
theorem B2195803 : Blo 2195435 2195803 := bstep (se 1 (by rfl) ⟨1646852, by rfl⟩ : syracuseStep 2195803 = 3293705) B3293705
theorem B11116277 : Blo 2195435 11116277 := bbase (se 5 (by rfl) ⟨521075, by rfl⟩ : syracuseStep 11116277 = 1042151) (by norm_num)
theorem B7410851 : Blo 2195435 7410851 := bstep (se 1 (by rfl) ⟨5558138, by rfl⟩ : syracuseStep 7410851 = 11116277) B11116277
theorem B4940567 : Blo 2195435 4940567 := bstep (se 1 (by rfl) ⟨3705425, by rfl⟩ : syracuseStep 4940567 = 7410851) B7410851
theorem B3293711 : Blo 2195435 3293711 := bstep (se 1 (by rfl) ⟨2470283, by rfl⟩ : syracuseStep 3293711 = 4940567) B4940567
theorem B2195807 : Blo 2195435 2195807 := bstep (se 1 (by rfl) ⟨1646855, by rfl⟩ : syracuseStep 2195807 = 3293711) B3293711
theorem B3293717 : Blo 2195435 3293717 := bbase (se 6 (by rfl) ⟨77196, by rfl⟩ : syracuseStep 3293717 = 154393) (by norm_num)
theorem B2195811 : Blo 2195435 2195811 := bstep (se 1 (by rfl) ⟨1646858, by rfl⟩ : syracuseStep 2195811 = 3293717) B3293717
theorem B3956933 : Blo 2195435 3956933 := bbase (se 4 (by rfl) ⟨370962, by rfl⟩ : syracuseStep 3956933 = 741925) (by norm_num)
theorem B2637955 : Blo 2195435 2637955 := bstep (se 1 (by rfl) ⟨1978466, by rfl⟩ : syracuseStep 2637955 = 3956933) B3956933
theorem B3517273 : Blo 2195435 3517273 := bstep (se 2 (by rfl) ⟨1318977, by rfl⟩ : syracuseStep 3517273 = 2637955) B2637955
theorem B18758789 : Blo 2195435 18758789 := bstep (se 4 (by rfl) ⟨1758636, by rfl⟩ : syracuseStep 18758789 = 3517273) B3517273
theorem B12505859 : Blo 2195435 12505859 := bstep (se 1 (by rfl) ⟨9379394, by rfl⟩ : syracuseStep 12505859 = 18758789) B18758789
theorem B8337239 : Blo 2195435 8337239 := bstep (se 1 (by rfl) ⟨6252929, by rfl⟩ : syracuseStep 8337239 = 12505859) B12505859
theorem B5558159 : Blo 2195435 5558159 := bstep (se 1 (by rfl) ⟨4168619, by rfl⟩ : syracuseStep 5558159 = 8337239) B8337239
theorem B3705439 : Blo 2195435 3705439 := bstep (se 1 (by rfl) ⟨2779079, by rfl⟩ : syracuseStep 3705439 = 5558159) B5558159
theorem B4940585 : Blo 2195435 4940585 := bstep (se 2 (by rfl) ⟨1852719, by rfl⟩ : syracuseStep 4940585 = 3705439) B3705439
theorem B3293723 : Blo 2195435 3293723 := bstep (se 1 (by rfl) ⟨2470292, by rfl⟩ : syracuseStep 3293723 = 4940585) B4940585
theorem B2195815 : Blo 2195435 2195815 := bstep (se 1 (by rfl) ⟨1646861, by rfl⟩ : syracuseStep 2195815 = 3293723) B3293723
theorem B2470297 : Blo 2195435 2470297 := bbase (se 2 (by rfl) ⟨926361, by rfl⟩ : syracuseStep 2470297 = 1852723) (by norm_num)
theorem B3293729 : Blo 2195435 3293729 := bstep (se 2 (by rfl) ⟨1235148, by rfl⟩ : syracuseStep 3293729 = 2470297) B2470297
theorem B2195819 : Blo 2195435 2195819 := bstep (se 1 (by rfl) ⟨1646864, by rfl⟩ : syracuseStep 2195819 = 3293729) B3293729
theorem B8337269 : Blo 2195435 8337269 := bbase (se 5 (by rfl) ⟨390809, by rfl⟩ : syracuseStep 8337269 = 781619) (by norm_num)
theorem B5558179 : Blo 2195435 5558179 := bstep (se 1 (by rfl) ⟨4168634, by rfl⟩ : syracuseStep 5558179 = 8337269) B8337269
theorem B7410905 : Blo 2195435 7410905 := bstep (se 2 (by rfl) ⟨2779089, by rfl⟩ : syracuseStep 7410905 = 5558179) B5558179
theorem B4940603 : Blo 2195435 4940603 := bstep (se 1 (by rfl) ⟨3705452, by rfl⟩ : syracuseStep 4940603 = 7410905) B7410905
theorem B3293735 : Blo 2195435 3293735 := bstep (se 1 (by rfl) ⟨2470301, by rfl⟩ : syracuseStep 3293735 = 4940603) B4940603
theorem B2195823 : Blo 2195435 2195823 := bstep (se 1 (by rfl) ⟨1646867, by rfl⟩ : syracuseStep 2195823 = 3293735) B3293735
theorem B3293741 : Blo 2195435 3293741 := bbase (se 3 (by rfl) ⟨617576, by rfl⟩ : syracuseStep 3293741 = 1235153) (by norm_num)
theorem B2195827 : Blo 2195435 2195827 := bstep (se 1 (by rfl) ⟨1646870, by rfl⟩ : syracuseStep 2195827 = 3293741) B3293741
theorem B4940621 : Blo 2195435 4940621 := bbase (se 3 (by rfl) ⟨926366, by rfl⟩ : syracuseStep 4940621 = 1852733) (by norm_num)
theorem B3293747 : Blo 2195435 3293747 := bstep (se 1 (by rfl) ⟨2470310, by rfl⟩ : syracuseStep 3293747 = 4940621) B4940621
theorem B2195831 : Blo 2195435 2195831 := bstep (se 1 (by rfl) ⟨1646873, by rfl⟩ : syracuseStep 2195831 = 3293747) B3293747
theorem B2779105 : Blo 2195435 2779105 := bbase (se 2 (by rfl) ⟨1042164, by rfl⟩ : syracuseStep 2779105 = 2084329) (by norm_num)
theorem B3705473 : Blo 2195435 3705473 := bstep (se 2 (by rfl) ⟨1389552, by rfl⟩ : syracuseStep 3705473 = 2779105) B2779105
theorem B2470315 : Blo 2195435 2470315 := bstep (se 1 (by rfl) ⟨1852736, by rfl⟩ : syracuseStep 2470315 = 3705473) B3705473
theorem B3293753 : Blo 2195435 3293753 := bstep (se 2 (by rfl) ⟨1235157, by rfl⟩ : syracuseStep 3293753 = 2470315) B2470315
theorem B2195835 : Blo 2195435 2195835 := bstep (se 1 (by rfl) ⟨1646876, by rfl⟩ : syracuseStep 2195835 = 3293753) B3293753
theorem B25011989 : Blo 2195435 25011989 := bbase (se 6 (by rfl) ⟨586218, by rfl⟩ : syracuseStep 25011989 = 1172437) (by norm_num)
theorem B16674659 : Blo 2195435 16674659 := bstep (se 1 (by rfl) ⟨12505994, by rfl⟩ : syracuseStep 16674659 = 25011989) B25011989
theorem B11116439 : Blo 2195435 11116439 := bstep (se 1 (by rfl) ⟨8337329, by rfl⟩ : syracuseStep 11116439 = 16674659) B16674659
theorem B7410959 : Blo 2195435 7410959 := bstep (se 1 (by rfl) ⟨5558219, by rfl⟩ : syracuseStep 7410959 = 11116439) B11116439
theorem B4940639 : Blo 2195435 4940639 := bstep (se 1 (by rfl) ⟨3705479, by rfl⟩ : syracuseStep 4940639 = 7410959) B7410959
theorem B3293759 : Blo 2195435 3293759 := bstep (se 1 (by rfl) ⟨2470319, by rfl⟩ : syracuseStep 3293759 = 4940639) B4940639
theorem B2195839 : Blo 2195435 2195839 := bstep (se 1 (by rfl) ⟨1646879, by rfl⟩ : syracuseStep 2195839 = 3293759) B3293759
theorem B3293765 : Blo 2195435 3293765 := bbase (se 4 (by rfl) ⟨308790, by rfl⟩ : syracuseStep 3293765 = 617581) (by norm_num)
theorem B2195843 : Blo 2195435 2195843 := bstep (se 1 (by rfl) ⟨1646882, by rfl⟩ : syracuseStep 2195843 = 3293765) B3293765
theorem B3705493 : Blo 2195435 3705493 := bbase (se 6 (by rfl) ⟨86847, by rfl⟩ : syracuseStep 3705493 = 173695) (by norm_num)
theorem B4940657 : Blo 2195435 4940657 := bstep (se 2 (by rfl) ⟨1852746, by rfl⟩ : syracuseStep 4940657 = 3705493) B3705493
theorem B3293771 : Blo 2195435 3293771 := bstep (se 1 (by rfl) ⟨2470328, by rfl⟩ : syracuseStep 3293771 = 4940657) B4940657
theorem B2195847 : Blo 2195435 2195847 := bstep (se 1 (by rfl) ⟨1646885, by rfl⟩ : syracuseStep 2195847 = 3293771) B3293771
theorem B2470333 : Blo 2195435 2470333 := bbase (se 3 (by rfl) ⟨463187, by rfl⟩ : syracuseStep 2470333 = 926375) (by norm_num)
theorem B3293777 : Blo 2195435 3293777 := bstep (se 2 (by rfl) ⟨1235166, by rfl⟩ : syracuseStep 3293777 = 2470333) B2470333
theorem B2195851 : Blo 2195435 2195851 := bstep (se 1 (by rfl) ⟨1646888, by rfl⟩ : syracuseStep 2195851 = 3293777) B3293777
theorem B7411013 : Blo 2195435 7411013 := bbase (se 4 (by rfl) ⟨694782, by rfl⟩ : syracuseStep 7411013 = 1389565) (by norm_num)
theorem B4940675 : Blo 2195435 4940675 := bstep (se 1 (by rfl) ⟨3705506, by rfl⟩ : syracuseStep 4940675 = 7411013) B7411013
theorem B3293783 : Blo 2195435 3293783 := bstep (se 1 (by rfl) ⟨2470337, by rfl⟩ : syracuseStep 3293783 = 4940675) B4940675
theorem B2195855 : Blo 2195435 2195855 := bstep (se 1 (by rfl) ⟨1646891, by rfl⟩ : syracuseStep 2195855 = 3293783) B3293783
theorem B3293789 : Blo 2195435 3293789 := bbase (se 3 (by rfl) ⟨617585, by rfl⟩ : syracuseStep 3293789 = 1235171) (by norm_num)
theorem B2195859 : Blo 2195435 2195859 := bstep (se 1 (by rfl) ⟨1646894, by rfl⟩ : syracuseStep 2195859 = 3293789) B3293789
theorem B4940693 : Blo 2195435 4940693 := bbase (se 6 (by rfl) ⟨115797, by rfl⟩ : syracuseStep 4940693 = 231595) (by norm_num)
theorem B3293795 : Blo 2195435 3293795 := bstep (se 1 (by rfl) ⟨2470346, by rfl⟩ : syracuseStep 3293795 = 4940693) B4940693
theorem B2195863 : Blo 2195435 2195863 := bstep (se 1 (by rfl) ⟨1646897, by rfl⟩ : syracuseStep 2195863 = 3293795) B3293795
theorem B3517357 : Blo 2195435 3517357 := bbase (se 3 (by rfl) ⟨659504, by rfl⟩ : syracuseStep 3517357 = 1319009) (by norm_num)
theorem B4689809 : Blo 2195435 4689809 := bstep (se 2 (by rfl) ⟨1758678, by rfl⟩ : syracuseStep 4689809 = 3517357) B3517357
theorem B3126539 : Blo 2195435 3126539 := bstep (se 1 (by rfl) ⟨2344904, by rfl⟩ : syracuseStep 3126539 = 4689809) B4689809
theorem B8337437 : Blo 2195435 8337437 := bstep (se 3 (by rfl) ⟨1563269, by rfl⟩ : syracuseStep 8337437 = 3126539) B3126539
theorem B5558291 : Blo 2195435 5558291 := bstep (se 1 (by rfl) ⟨4168718, by rfl⟩ : syracuseStep 5558291 = 8337437) B8337437
theorem B3705527 : Blo 2195435 3705527 := bstep (se 1 (by rfl) ⟨2779145, by rfl⟩ : syracuseStep 3705527 = 5558291) B5558291
theorem B2470351 : Blo 2195435 2470351 := bstep (se 1 (by rfl) ⟨1852763, by rfl⟩ : syracuseStep 2470351 = 3705527) B3705527
theorem B3293801 : Blo 2195435 3293801 := bstep (se 2 (by rfl) ⟨1235175, by rfl⟩ : syracuseStep 3293801 = 2470351) B2470351
theorem B2195867 : Blo 2195435 2195867 := bstep (se 1 (by rfl) ⟨1646900, by rfl⟩ : syracuseStep 2195867 = 3293801) B3293801
theorem B7034725 : Blo 2195435 7034725 := bbase (se 4 (by rfl) ⟨659505, by rfl⟩ : syracuseStep 7034725 = 1319011) (by norm_num)
theorem B9379633 : Blo 2195435 9379633 := bstep (se 2 (by rfl) ⟨3517362, by rfl⟩ : syracuseStep 9379633 = 7034725) B7034725
theorem B12506177 : Blo 2195435 12506177 := bstep (se 2 (by rfl) ⟨4689816, by rfl⟩ : syracuseStep 12506177 = 9379633) B9379633
theorem B8337451 : Blo 2195435 8337451 := bstep (se 1 (by rfl) ⟨6253088, by rfl⟩ : syracuseStep 8337451 = 12506177) B12506177
theorem B11116601 : Blo 2195435 11116601 := bstep (se 2 (by rfl) ⟨4168725, by rfl⟩ : syracuseStep 11116601 = 8337451) B8337451
theorem B7411067 : Blo 2195435 7411067 := bstep (se 1 (by rfl) ⟨5558300, by rfl⟩ : syracuseStep 7411067 = 11116601) B11116601
theorem B4940711 : Blo 2195435 4940711 := bstep (se 1 (by rfl) ⟨3705533, by rfl⟩ : syracuseStep 4940711 = 7411067) B7411067
theorem B3293807 : Blo 2195435 3293807 := bstep (se 1 (by rfl) ⟨2470355, by rfl⟩ : syracuseStep 3293807 = 4940711) B4940711
theorem B2195871 : Blo 2195435 2195871 := bstep (se 1 (by rfl) ⟨1646903, by rfl⟩ : syracuseStep 2195871 = 3293807) B3293807
theorem B3293813 : Blo 2195435 3293813 := bbase (se 5 (by rfl) ⟨154397, by rfl⟩ : syracuseStep 3293813 = 308795) (by norm_num)
theorem B2195875 : Blo 2195435 2195875 := bstep (se 1 (by rfl) ⟨1646906, by rfl⟩ : syracuseStep 2195875 = 3293813) B3293813
theorem B4168741 : Blo 2195435 4168741 := bbase (se 4 (by rfl) ⟨390819, by rfl⟩ : syracuseStep 4168741 = 781639) (by norm_num)
theorem B5558321 : Blo 2195435 5558321 := bstep (se 2 (by rfl) ⟨2084370, by rfl⟩ : syracuseStep 5558321 = 4168741) B4168741
theorem B3705547 : Blo 2195435 3705547 := bstep (se 1 (by rfl) ⟨2779160, by rfl⟩ : syracuseStep 3705547 = 5558321) B5558321
theorem B4940729 : Blo 2195435 4940729 := bstep (se 2 (by rfl) ⟨1852773, by rfl⟩ : syracuseStep 4940729 = 3705547) B3705547
theorem B3293819 : Blo 2195435 3293819 := bstep (se 1 (by rfl) ⟨2470364, by rfl⟩ : syracuseStep 3293819 = 4940729) B4940729
theorem B2195879 : Blo 2195435 2195879 := bstep (se 1 (by rfl) ⟨1646909, by rfl⟩ : syracuseStep 2195879 = 3293819) B3293819
theorem B2470369 : Blo 2195435 2470369 := bbase (se 2 (by rfl) ⟨926388, by rfl⟩ : syracuseStep 2470369 = 1852777) (by norm_num)
theorem B3293825 : Blo 2195435 3293825 := bstep (se 2 (by rfl) ⟨1235184, by rfl⟩ : syracuseStep 3293825 = 2470369) B2470369
theorem B2195883 : Blo 2195435 2195883 := bstep (se 1 (by rfl) ⟨1646912, by rfl⟩ : syracuseStep 2195883 = 3293825) B3293825
theorem B5558341 : Blo 2195435 5558341 := bbase (se 4 (by rfl) ⟨521094, by rfl⟩ : syracuseStep 5558341 = 1042189) (by norm_num)
theorem B7411121 : Blo 2195435 7411121 := bstep (se 2 (by rfl) ⟨2779170, by rfl⟩ : syracuseStep 7411121 = 5558341) B5558341
theorem B4940747 : Blo 2195435 4940747 := bstep (se 1 (by rfl) ⟨3705560, by rfl⟩ : syracuseStep 4940747 = 7411121) B7411121
theorem B3293831 : Blo 2195435 3293831 := bstep (se 1 (by rfl) ⟨2470373, by rfl⟩ : syracuseStep 3293831 = 4940747) B4940747
theorem B2195887 : Blo 2195435 2195887 := bstep (se 1 (by rfl) ⟨1646915, by rfl⟩ : syracuseStep 2195887 = 3293831) B3293831
theorem B3293837 : Blo 2195435 3293837 := bbase (se 3 (by rfl) ⟨617594, by rfl⟩ : syracuseStep 3293837 = 1235189) (by norm_num)
theorem B2195891 : Blo 2195435 2195891 := bstep (se 1 (by rfl) ⟨1646918, by rfl⟩ : syracuseStep 2195891 = 3293837) B3293837
theorem B4940765 : Blo 2195435 4940765 := bbase (se 3 (by rfl) ⟨926393, by rfl⟩ : syracuseStep 4940765 = 1852787) (by norm_num)
theorem B3293843 : Blo 2195435 3293843 := bstep (se 1 (by rfl) ⟨2470382, by rfl⟩ : syracuseStep 3293843 = 4940765) B4940765
theorem B2195895 : Blo 2195435 2195895 := bstep (se 1 (by rfl) ⟨1646921, by rfl⟩ : syracuseStep 2195895 = 3293843) B3293843
theorem B3705581 : Blo 2195435 3705581 := bbase (se 3 (by rfl) ⟨694796, by rfl⟩ : syracuseStep 3705581 = 1389593) (by norm_num)
theorem B2470387 : Blo 2195435 2470387 := bstep (se 1 (by rfl) ⟨1852790, by rfl⟩ : syracuseStep 2470387 = 3705581) B3705581
theorem B3293849 : Blo 2195435 3293849 := bstep (se 2 (by rfl) ⟨1235193, by rfl⟩ : syracuseStep 3293849 = 2470387) B2470387
theorem B2195899 : Blo 2195435 2195899 := bstep (se 1 (by rfl) ⟨1646924, by rfl⟩ : syracuseStep 2195899 = 3293849) B3293849
theorem B7914181 : Blo 2195435 7914181 := bbase (se 4 (by rfl) ⟨741954, by rfl⟩ : syracuseStep 7914181 = 1483909) (by norm_num)
theorem B10552241 : Blo 2195435 10552241 := bstep (se 2 (by rfl) ⟨3957090, by rfl⟩ : syracuseStep 10552241 = 7914181) B7914181
theorem B28139309 : Blo 2195435 28139309 := bstep (se 3 (by rfl) ⟨5276120, by rfl⟩ : syracuseStep 28139309 = 10552241) B10552241
theorem B18759539 : Blo 2195435 18759539 := bstep (se 1 (by rfl) ⟨14069654, by rfl⟩ : syracuseStep 18759539 = 28139309) B28139309
theorem B12506359 : Blo 2195435 12506359 := bstep (se 1 (by rfl) ⟨9379769, by rfl⟩ : syracuseStep 12506359 = 18759539) B18759539
theorem B16675145 : Blo 2195435 16675145 := bstep (se 2 (by rfl) ⟨6253179, by rfl⟩ : syracuseStep 16675145 = 12506359) B12506359
theorem B11116763 : Blo 2195435 11116763 := bstep (se 1 (by rfl) ⟨8337572, by rfl⟩ : syracuseStep 11116763 = 16675145) B16675145
theorem B7411175 : Blo 2195435 7411175 := bstep (se 1 (by rfl) ⟨5558381, by rfl⟩ : syracuseStep 7411175 = 11116763) B11116763
theorem B4940783 : Blo 2195435 4940783 := bstep (se 1 (by rfl) ⟨3705587, by rfl⟩ : syracuseStep 4940783 = 7411175) B7411175
theorem B3293855 : Blo 2195435 3293855 := bstep (se 1 (by rfl) ⟨2470391, by rfl⟩ : syracuseStep 3293855 = 4940783) B4940783
theorem B2195903 : Blo 2195435 2195903 := bstep (se 1 (by rfl) ⟨1646927, by rfl⟩ : syracuseStep 2195903 = 3293855) B3293855
theorem B3293861 : Blo 2195435 3293861 := bbase (se 4 (by rfl) ⟨308799, by rfl⟩ : syracuseStep 3293861 = 617599) (by norm_num)
theorem B2195907 : Blo 2195435 2195907 := bstep (se 1 (by rfl) ⟨1646930, by rfl⟩ : syracuseStep 2195907 = 3293861) B3293861
theorem B2779201 : Blo 2195435 2779201 := bbase (se 2 (by rfl) ⟨1042200, by rfl⟩ : syracuseStep 2779201 = 2084401) (by norm_num)
theorem B3705601 : Blo 2195435 3705601 := bstep (se 2 (by rfl) ⟨1389600, by rfl⟩ : syracuseStep 3705601 = 2779201) B2779201
theorem B4940801 : Blo 2195435 4940801 := bstep (se 2 (by rfl) ⟨1852800, by rfl⟩ : syracuseStep 4940801 = 3705601) B3705601
theorem B3293867 : Blo 2195435 3293867 := bstep (se 1 (by rfl) ⟨2470400, by rfl⟩ : syracuseStep 3293867 = 4940801) B4940801
theorem B2195911 : Blo 2195435 2195911 := bstep (se 1 (by rfl) ⟨1646933, by rfl⟩ : syracuseStep 2195911 = 3293867) B3293867
theorem B2470405 : Blo 2195435 2470405 := bbase (se 4 (by rfl) ⟨231600, by rfl⟩ : syracuseStep 2470405 = 463201) (by norm_num)
theorem B3293873 : Blo 2195435 3293873 := bstep (se 2 (by rfl) ⟨1235202, by rfl⟩ : syracuseStep 3293873 = 2470405) B2470405
theorem B2195915 : Blo 2195435 2195915 := bstep (se 1 (by rfl) ⟨1646936, by rfl⟩ : syracuseStep 2195915 = 3293873) B3293873
theorem B3126613 : Blo 2195435 3126613 := bbase (se 13 (by rfl) ⟨572, by rfl⟩ : syracuseStep 3126613 = 1145) (by norm_num)
theorem B4168817 : Blo 2195435 4168817 := bstep (se 2 (by rfl) ⟨1563306, by rfl⟩ : syracuseStep 4168817 = 3126613) B3126613
theorem B2779211 : Blo 2195435 2779211 := bstep (se 1 (by rfl) ⟨2084408, by rfl⟩ : syracuseStep 2779211 = 4168817) B4168817
theorem B7411229 : Blo 2195435 7411229 := bstep (se 3 (by rfl) ⟨1389605, by rfl⟩ : syracuseStep 7411229 = 2779211) B2779211
theorem B4940819 : Blo 2195435 4940819 := bstep (se 1 (by rfl) ⟨3705614, by rfl⟩ : syracuseStep 4940819 = 7411229) B7411229
theorem B3293879 : Blo 2195435 3293879 := bstep (se 1 (by rfl) ⟨2470409, by rfl⟩ : syracuseStep 3293879 = 4940819) B4940819
theorem B2195919 : Blo 2195435 2195919 := bstep (se 1 (by rfl) ⟨1646939, by rfl⟩ : syracuseStep 2195919 = 3293879) B3293879
theorem B3293885 : Blo 2195435 3293885 := bbase (se 3 (by rfl) ⟨617603, by rfl⟩ : syracuseStep 3293885 = 1235207) (by norm_num)
theorem B2195923 : Blo 2195435 2195923 := bstep (se 1 (by rfl) ⟨1646942, by rfl⟩ : syracuseStep 2195923 = 3293885) B3293885
theorem B4940837 : Blo 2195435 4940837 := bbase (se 4 (by rfl) ⟨463203, by rfl⟩ : syracuseStep 4940837 = 926407) (by norm_num)
theorem B3293891 : Blo 2195435 3293891 := bstep (se 1 (by rfl) ⟨2470418, by rfl⟩ : syracuseStep 3293891 = 4940837) B4940837
theorem B2195927 : Blo 2195435 2195927 := bstep (se 1 (by rfl) ⟨1646945, by rfl⟩ : syracuseStep 2195927 = 3293891) B3293891
theorem B5558453 : Blo 2195435 5558453 := bbase (se 5 (by rfl) ⟨260552, by rfl⟩ : syracuseStep 5558453 = 521105) (by norm_num)
theorem B3705635 : Blo 2195435 3705635 := bstep (se 1 (by rfl) ⟨2779226, by rfl⟩ : syracuseStep 3705635 = 5558453) B5558453
theorem B2470423 : Blo 2195435 2470423 := bstep (se 1 (by rfl) ⟨1852817, by rfl⟩ : syracuseStep 2470423 = 3705635) B3705635
theorem B3293897 : Blo 2195435 3293897 := bstep (se 2 (by rfl) ⟨1235211, by rfl⟩ : syracuseStep 3293897 = 2470423) B2470423
theorem B2195931 : Blo 2195435 2195931 := bstep (se 1 (by rfl) ⟨1646948, by rfl⟩ : syracuseStep 2195931 = 3293897) B3293897
theorem B3957149 : Blo 2195435 3957149 := bbase (se 3 (by rfl) ⟨741965, by rfl⟩ : syracuseStep 3957149 = 1483931) (by norm_num)
theorem B2638099 : Blo 2195435 2638099 := bstep (se 1 (by rfl) ⟨1978574, by rfl⟩ : syracuseStep 2638099 = 3957149) B3957149
theorem B14069861 : Blo 2195435 14069861 := bstep (se 4 (by rfl) ⟨1319049, by rfl⟩ : syracuseStep 14069861 = 2638099) B2638099
theorem B9379907 : Blo 2195435 9379907 := bstep (se 1 (by rfl) ⟨7034930, by rfl⟩ : syracuseStep 9379907 = 14069861) B14069861
theorem B6253271 : Blo 2195435 6253271 := bstep (se 1 (by rfl) ⟨4689953, by rfl⟩ : syracuseStep 6253271 = 9379907) B9379907
theorem B4168847 : Blo 2195435 4168847 := bstep (se 1 (by rfl) ⟨3126635, by rfl⟩ : syracuseStep 4168847 = 6253271) B6253271
theorem B11116925 : Blo 2195435 11116925 := bstep (se 3 (by rfl) ⟨2084423, by rfl⟩ : syracuseStep 11116925 = 4168847) B4168847
theorem B7411283 : Blo 2195435 7411283 := bstep (se 1 (by rfl) ⟨5558462, by rfl⟩ : syracuseStep 7411283 = 11116925) B11116925
theorem B4940855 : Blo 2195435 4940855 := bstep (se 1 (by rfl) ⟨3705641, by rfl⟩ : syracuseStep 4940855 = 7411283) B7411283
theorem B3293903 : Blo 2195435 3293903 := bstep (se 1 (by rfl) ⟨2470427, by rfl⟩ : syracuseStep 3293903 = 4940855) B4940855
theorem B2195935 : Blo 2195435 2195935 := bstep (se 1 (by rfl) ⟨1646951, by rfl⟩ : syracuseStep 2195935 = 3293903) B3293903
theorem B3293909 : Blo 2195435 3293909 := bbase (se 7 (by rfl) ⟨38600, by rfl⟩ : syracuseStep 3293909 = 77201) (by norm_num)
theorem B2195939 : Blo 2195435 2195939 := bstep (se 1 (by rfl) ⟨1646954, by rfl⟩ : syracuseStep 2195939 = 3293909) B3293909
theorem B2638109 : Blo 2195435 2638109 := bbase (se 3 (by rfl) ⟨494645, by rfl⟩ : syracuseStep 2638109 = 989291) (by norm_num)
theorem B7034957 : Blo 2195435 7034957 := bstep (se 3 (by rfl) ⟨1319054, by rfl⟩ : syracuseStep 7034957 = 2638109) B2638109
theorem B4689971 : Blo 2195435 4689971 := bstep (se 1 (by rfl) ⟨3517478, by rfl⟩ : syracuseStep 4689971 = 7034957) B7034957
theorem B3126647 : Blo 2195435 3126647 := bstep (se 1 (by rfl) ⟨2344985, by rfl⟩ : syracuseStep 3126647 = 4689971) B4689971
theorem B8337725 : Blo 2195435 8337725 := bstep (se 3 (by rfl) ⟨1563323, by rfl⟩ : syracuseStep 8337725 = 3126647) B3126647
theorem B5558483 : Blo 2195435 5558483 := bstep (se 1 (by rfl) ⟨4168862, by rfl⟩ : syracuseStep 5558483 = 8337725) B8337725
theorem B3705655 : Blo 2195435 3705655 := bstep (se 1 (by rfl) ⟨2779241, by rfl⟩ : syracuseStep 3705655 = 5558483) B5558483
theorem B4940873 : Blo 2195435 4940873 := bstep (se 2 (by rfl) ⟨1852827, by rfl⟩ : syracuseStep 4940873 = 3705655) B3705655
theorem B3293915 : Blo 2195435 3293915 := bstep (se 1 (by rfl) ⟨2470436, by rfl⟩ : syracuseStep 3293915 = 4940873) B4940873
theorem B2195943 : Blo 2195435 2195943 := bstep (se 1 (by rfl) ⟨1646957, by rfl⟩ : syracuseStep 2195943 = 3293915) B3293915
theorem B2470441 : Blo 2195435 2470441 := bbase (se 2 (by rfl) ⟨926415, by rfl⟩ : syracuseStep 2470441 = 1852831) (by norm_num)
theorem B3293921 : Blo 2195435 3293921 := bstep (se 2 (by rfl) ⟨1235220, by rfl⟩ : syracuseStep 3293921 = 2470441) B2470441
theorem B2195947 : Blo 2195435 2195947 := bstep (se 1 (by rfl) ⟨1646960, by rfl⟩ : syracuseStep 2195947 = 3293921) B3293921
theorem B3338869 : Blo 2195435 3338869 := bbase (se 5 (by rfl) ⟨156509, by rfl⟩ : syracuseStep 3338869 = 313019) (by norm_num)
theorem B4451825 : Blo 2195435 4451825 := bstep (se 2 (by rfl) ⟨1669434, by rfl⟩ : syracuseStep 4451825 = 3338869) B3338869
theorem B2967883 : Blo 2195435 2967883 := bstep (se 1 (by rfl) ⟨2225912, by rfl⟩ : syracuseStep 2967883 = 4451825) B4451825
theorem B15828709 : Blo 2195435 15828709 := bstep (se 4 (by rfl) ⟨1483941, by rfl⟩ : syracuseStep 15828709 = 2967883) B2967883
theorem B21104945 : Blo 2195435 21104945 := bstep (se 2 (by rfl) ⟨7914354, by rfl⟩ : syracuseStep 21104945 = 15828709) B15828709
theorem B14069963 : Blo 2195435 14069963 := bstep (se 1 (by rfl) ⟨10552472, by rfl⟩ : syracuseStep 14069963 = 21104945) B21104945
theorem B9379975 : Blo 2195435 9379975 := bstep (se 1 (by rfl) ⟨7034981, by rfl⟩ : syracuseStep 9379975 = 14069963) B14069963
theorem B12506633 : Blo 2195435 12506633 := bstep (se 2 (by rfl) ⟨4689987, by rfl⟩ : syracuseStep 12506633 = 9379975) B9379975
theorem B8337755 : Blo 2195435 8337755 := bstep (se 1 (by rfl) ⟨6253316, by rfl⟩ : syracuseStep 8337755 = 12506633) B12506633
theorem B5558503 : Blo 2195435 5558503 := bstep (se 1 (by rfl) ⟨4168877, by rfl⟩ : syracuseStep 5558503 = 8337755) B8337755
theorem B7411337 : Blo 2195435 7411337 := bstep (se 2 (by rfl) ⟨2779251, by rfl⟩ : syracuseStep 7411337 = 5558503) B5558503
theorem B4940891 : Blo 2195435 4940891 := bstep (se 1 (by rfl) ⟨3705668, by rfl⟩ : syracuseStep 4940891 = 7411337) B7411337
theorem B3293927 : Blo 2195435 3293927 := bstep (se 1 (by rfl) ⟨2470445, by rfl⟩ : syracuseStep 3293927 = 4940891) B4940891
theorem B2195951 : Blo 2195435 2195951 := bstep (se 1 (by rfl) ⟨1646963, by rfl⟩ : syracuseStep 2195951 = 3293927) B3293927
theorem B3293933 : Blo 2195435 3293933 := bbase (se 3 (by rfl) ⟨617612, by rfl⟩ : syracuseStep 3293933 = 1235225) (by norm_num)
theorem B2195955 : Blo 2195435 2195955 := bstep (se 1 (by rfl) ⟨1646966, by rfl⟩ : syracuseStep 2195955 = 3293933) B3293933
theorem B4940909 : Blo 2195435 4940909 := bbase (se 3 (by rfl) ⟨926420, by rfl⟩ : syracuseStep 4940909 = 1852841) (by norm_num)
theorem B3293939 : Blo 2195435 3293939 := bstep (se 1 (by rfl) ⟨2470454, by rfl⟩ : syracuseStep 3293939 = 4940909) B4940909
theorem B2195959 : Blo 2195435 2195959 := bstep (se 1 (by rfl) ⟨1646969, by rfl⟩ : syracuseStep 2195959 = 3293939) B3293939
theorem B4168901 : Blo 2195435 4168901 := bbase (se 4 (by rfl) ⟨390834, by rfl⟩ : syracuseStep 4168901 = 781669) (by norm_num)
theorem B2779267 : Blo 2195435 2779267 := bstep (se 1 (by rfl) ⟨2084450, by rfl⟩ : syracuseStep 2779267 = 4168901) B4168901
theorem B3705689 : Blo 2195435 3705689 := bstep (se 2 (by rfl) ⟨1389633, by rfl⟩ : syracuseStep 3705689 = 2779267) B2779267
theorem B2470459 : Blo 2195435 2470459 := bstep (se 1 (by rfl) ⟨1852844, by rfl⟩ : syracuseStep 2470459 = 3705689) B3705689
theorem B3293945 : Blo 2195435 3293945 := bstep (se 2 (by rfl) ⟨1235229, by rfl⟩ : syracuseStep 3293945 = 2470459) B2470459
theorem B2195963 : Blo 2195435 2195963 := bstep (se 1 (by rfl) ⟨1646972, by rfl⟩ : syracuseStep 2195963 = 3293945) B3293945
theorem B2409437 : Blo 2195435 2409437 := bbase (se 3 (by rfl) ⟨451769, by rfl⟩ : syracuseStep 2409437 = 903539) (by norm_num)
theorem B6425165 : Blo 2195435 6425165 := bstep (se 3 (by rfl) ⟨1204718, by rfl⟩ : syracuseStep 6425165 = 2409437) B2409437
theorem B4283443 : Blo 2195435 4283443 := bstep (se 1 (by rfl) ⟨3212582, by rfl⟩ : syracuseStep 4283443 = 6425165) B6425165
theorem B5711257 : Blo 2195435 5711257 := bstep (se 2 (by rfl) ⟨2141721, by rfl⟩ : syracuseStep 5711257 = 4283443) B4283443
theorem B7615009 : Blo 2195435 7615009 := bstep (se 2 (by rfl) ⟨2855628, by rfl⟩ : syracuseStep 7615009 = 5711257) B5711257
theorem B10153345 : Blo 2195435 10153345 := bstep (se 2 (by rfl) ⟨3807504, by rfl⟩ : syracuseStep 10153345 = 7615009) B7615009
theorem B13537793 : Blo 2195435 13537793 := bstep (se 2 (by rfl) ⟨5076672, by rfl⟩ : syracuseStep 13537793 = 10153345) B10153345
theorem B9025195 : Blo 2195435 9025195 := bstep (se 1 (by rfl) ⟨6768896, by rfl⟩ : syracuseStep 9025195 = 13537793) B13537793
theorem B12033593 : Blo 2195435 12033593 := bstep (se 2 (by rfl) ⟨4512597, by rfl⟩ : syracuseStep 12033593 = 9025195) B9025195
theorem B8022395 : Blo 2195435 8022395 := bstep (se 1 (by rfl) ⟨6016796, by rfl⟩ : syracuseStep 8022395 = 12033593) B12033593
theorem B5348263 : Blo 2195435 5348263 := bstep (se 1 (by rfl) ⟨4011197, by rfl⟩ : syracuseStep 5348263 = 8022395) B8022395
theorem B7131017 : Blo 2195435 7131017 := bstep (se 2 (by rfl) ⟨2674131, by rfl⟩ : syracuseStep 7131017 = 5348263) B5348263
theorem B4754011 : Blo 2195435 4754011 := bstep (se 1 (by rfl) ⟨3565508, by rfl⟩ : syracuseStep 4754011 = 7131017) B7131017
theorem B6338681 : Blo 2195435 6338681 := bstep (se 2 (by rfl) ⟨2377005, by rfl⟩ : syracuseStep 6338681 = 4754011) B4754011
theorem B4225787 : Blo 2195435 4225787 := bstep (se 1 (by rfl) ⟨3169340, by rfl⟩ : syracuseStep 4225787 = 6338681) B6338681
theorem B2817191 : Blo 2195435 2817191 := bstep (se 1 (by rfl) ⟨2112893, by rfl⟩ : syracuseStep 2817191 = 4225787) B4225787
theorem B7512509 : Blo 2195435 7512509 := bstep (se 3 (by rfl) ⟨1408595, by rfl⟩ : syracuseStep 7512509 = 2817191) B2817191
theorem B5008339 : Blo 2195435 5008339 := bstep (se 1 (by rfl) ⟨3756254, by rfl⟩ : syracuseStep 5008339 = 7512509) B7512509
theorem B6677785 : Blo 2195435 6677785 := bstep (se 2 (by rfl) ⟨2504169, by rfl⟩ : syracuseStep 6677785 = 5008339) B5008339
theorem B8903713 : Blo 2195435 8903713 := bstep (se 2 (by rfl) ⟨3338892, by rfl⟩ : syracuseStep 8903713 = 6677785) B6677785
theorem B11871617 : Blo 2195435 11871617 := bstep (se 2 (by rfl) ⟨4451856, by rfl⟩ : syracuseStep 11871617 = 8903713) B8903713
theorem B31657645 : Blo 2195435 31657645 := bstep (se 3 (by rfl) ⟨5935808, by rfl⟩ : syracuseStep 31657645 = 11871617) B11871617
theorem B42210193 : Blo 2195435 42210193 := bstep (se 2 (by rfl) ⟨15828822, by rfl⟩ : syracuseStep 42210193 = 31657645) B31657645
theorem B56280257 : Blo 2195435 56280257 := bstep (se 2 (by rfl) ⟨21105096, by rfl⟩ : syracuseStep 56280257 = 42210193) B42210193
theorem B37520171 : Blo 2195435 37520171 := bstep (se 1 (by rfl) ⟨28140128, by rfl⟩ : syracuseStep 37520171 = 56280257) B56280257
theorem B25013447 : Blo 2195435 25013447 := bstep (se 1 (by rfl) ⟨18760085, by rfl⟩ : syracuseStep 25013447 = 37520171) B37520171
theorem B16675631 : Blo 2195435 16675631 := bstep (se 1 (by rfl) ⟨12506723, by rfl⟩ : syracuseStep 16675631 = 25013447) B25013447
theorem B11117087 : Blo 2195435 11117087 := bstep (se 1 (by rfl) ⟨8337815, by rfl⟩ : syracuseStep 11117087 = 16675631) B16675631
theorem B7411391 : Blo 2195435 7411391 := bstep (se 1 (by rfl) ⟨5558543, by rfl⟩ : syracuseStep 7411391 = 11117087) B11117087
theorem B4940927 : Blo 2195435 4940927 := bstep (se 1 (by rfl) ⟨3705695, by rfl⟩ : syracuseStep 4940927 = 7411391) B7411391
theorem B3293951 : Blo 2195435 3293951 := bstep (se 1 (by rfl) ⟨2470463, by rfl⟩ : syracuseStep 3293951 = 4940927) B4940927
theorem B2195967 : Blo 2195435 2195967 := bstep (se 1 (by rfl) ⟨1646975, by rfl⟩ : syracuseStep 2195967 = 3293951) B3293951
theorem B3293957 : Blo 2195435 3293957 := bbase (se 4 (by rfl) ⟨308808, by rfl⟩ : syracuseStep 3293957 = 617617) (by norm_num)
theorem B2195971 : Blo 2195435 2195971 := bstep (se 1 (by rfl) ⟨1646978, by rfl⟩ : syracuseStep 2195971 = 3293957) B3293957
theorem B3705709 : Blo 2195435 3705709 := bbase (se 3 (by rfl) ⟨694820, by rfl⟩ : syracuseStep 3705709 = 1389641) (by norm_num)
theorem B4940945 : Blo 2195435 4940945 := bstep (se 2 (by rfl) ⟨1852854, by rfl⟩ : syracuseStep 4940945 = 3705709) B3705709
theorem B3293963 : Blo 2195435 3293963 := bstep (se 1 (by rfl) ⟨2470472, by rfl⟩ : syracuseStep 3293963 = 4940945) B4940945
theorem B2195975 : Blo 2195435 2195975 := bstep (se 1 (by rfl) ⟨1646981, by rfl⟩ : syracuseStep 2195975 = 3293963) B3293963
theorem B2470477 : Blo 2195435 2470477 := bbase (se 3 (by rfl) ⟨463214, by rfl⟩ : syracuseStep 2470477 = 926429) (by norm_num)
theorem B3293969 : Blo 2195435 3293969 := bstep (se 2 (by rfl) ⟨1235238, by rfl⟩ : syracuseStep 3293969 = 2470477) B2470477
theorem B2195979 : Blo 2195435 2195979 := bstep (se 1 (by rfl) ⟨1646984, by rfl⟩ : syracuseStep 2195979 = 3293969) B3293969
theorem B7411445 : Blo 2195435 7411445 := bbase (se 5 (by rfl) ⟨347411, by rfl⟩ : syracuseStep 7411445 = 694823) (by norm_num)
theorem B4940963 : Blo 2195435 4940963 := bstep (se 1 (by rfl) ⟨3705722, by rfl⟩ : syracuseStep 4940963 = 7411445) B7411445
theorem B3293975 : Blo 2195435 3293975 := bstep (se 1 (by rfl) ⟨2470481, by rfl⟩ : syracuseStep 3293975 = 4940963) B4940963
theorem B2195983 : Blo 2195435 2195983 := bstep (se 1 (by rfl) ⟨1646987, by rfl⟩ : syracuseStep 2195983 = 3293975) B3293975
theorem B3293981 : Blo 2195435 3293981 := bbase (se 3 (by rfl) ⟨617621, by rfl⟩ : syracuseStep 3293981 = 1235243) (by norm_num)
theorem B2195987 : Blo 2195435 2195987 := bstep (se 1 (by rfl) ⟨1646990, by rfl⟩ : syracuseStep 2195987 = 3293981) B3293981
theorem B4940981 : Blo 2195435 4940981 := bbase (se 5 (by rfl) ⟨231608, by rfl⟩ : syracuseStep 4940981 = 463217) (by norm_num)
theorem B3293987 : Blo 2195435 3293987 := bstep (se 1 (by rfl) ⟨2470490, by rfl⟩ : syracuseStep 3293987 = 4940981) B4940981
theorem B2195991 : Blo 2195435 2195991 := bstep (se 1 (by rfl) ⟨1646993, by rfl⟩ : syracuseStep 2195991 = 3293987) B3293987
theorem B2345041 : Blo 2195435 2345041 := bbase (se 2 (by rfl) ⟨879390, by rfl⟩ : syracuseStep 2345041 = 1758781) (by norm_num)
theorem B12506885 : Blo 2195435 12506885 := bstep (se 4 (by rfl) ⟨1172520, by rfl⟩ : syracuseStep 12506885 = 2345041) B2345041
theorem B8337923 : Blo 2195435 8337923 := bstep (se 1 (by rfl) ⟨6253442, by rfl⟩ : syracuseStep 8337923 = 12506885) B12506885
theorem B5558615 : Blo 2195435 5558615 := bstep (se 1 (by rfl) ⟨4168961, by rfl⟩ : syracuseStep 5558615 = 8337923) B8337923
theorem B3705743 : Blo 2195435 3705743 := bstep (se 1 (by rfl) ⟨2779307, by rfl⟩ : syracuseStep 3705743 = 5558615) B5558615
theorem B2470495 : Blo 2195435 2470495 := bstep (se 1 (by rfl) ⟨1852871, by rfl⟩ : syracuseStep 2470495 = 3705743) B3705743
theorem B3293993 : Blo 2195435 3293993 := bstep (se 2 (by rfl) ⟨1235247, by rfl⟩ : syracuseStep 3293993 = 2470495) B2470495
theorem B2195995 : Blo 2195435 2195995 := bstep (se 1 (by rfl) ⟨1646996, by rfl⟩ : syracuseStep 2195995 = 3293993) B3293993
theorem B2345045 : Blo 2195435 2345045 := bbase (se 8 (by rfl) ⟨13740, by rfl⟩ : syracuseStep 2345045 = 27481) (by norm_num)
theorem B6253453 : Blo 2195435 6253453 := bstep (se 3 (by rfl) ⟨1172522, by rfl⟩ : syracuseStep 6253453 = 2345045) B2345045
theorem B8337937 : Blo 2195435 8337937 := bstep (se 2 (by rfl) ⟨3126726, by rfl⟩ : syracuseStep 8337937 = 6253453) B6253453
theorem B11117249 : Blo 2195435 11117249 := bstep (se 2 (by rfl) ⟨4168968, by rfl⟩ : syracuseStep 11117249 = 8337937) B8337937
theorem B7411499 : Blo 2195435 7411499 := bstep (se 1 (by rfl) ⟨5558624, by rfl⟩ : syracuseStep 7411499 = 11117249) B11117249
theorem B4940999 : Blo 2195435 4940999 := bstep (se 1 (by rfl) ⟨3705749, by rfl⟩ : syracuseStep 4940999 = 7411499) B7411499
theorem B3293999 : Blo 2195435 3293999 := bstep (se 1 (by rfl) ⟨2470499, by rfl⟩ : syracuseStep 3293999 = 4940999) B4940999
theorem B2195999 : Blo 2195435 2195999 := bstep (se 1 (by rfl) ⟨1646999, by rfl⟩ : syracuseStep 2195999 = 3293999) B3293999
theorem B3294005 : Blo 2195435 3294005 := bbase (se 5 (by rfl) ⟨154406, by rfl⟩ : syracuseStep 3294005 = 308813) (by norm_num)
theorem B2196003 : Blo 2195435 2196003 := bstep (se 1 (by rfl) ⟨1647002, by rfl⟩ : syracuseStep 2196003 = 3294005) B3294005
theorem B5558645 : Blo 2195435 5558645 := bbase (se 5 (by rfl) ⟨260561, by rfl⟩ : syracuseStep 5558645 = 521123) (by norm_num)
theorem B3705763 : Blo 2195435 3705763 := bstep (se 1 (by rfl) ⟨2779322, by rfl⟩ : syracuseStep 3705763 = 5558645) B5558645
theorem B4941017 : Blo 2195435 4941017 := bstep (se 2 (by rfl) ⟨1852881, by rfl⟩ : syracuseStep 4941017 = 3705763) B3705763
theorem B3294011 : Blo 2195435 3294011 := bstep (se 1 (by rfl) ⟨2470508, by rfl⟩ : syracuseStep 3294011 = 4941017) B4941017
theorem B2196007 : Blo 2195435 2196007 := bstep (se 1 (by rfl) ⟨1647005, by rfl⟩ : syracuseStep 2196007 = 3294011) B3294011
theorem B2470513 : Blo 2195435 2470513 := bbase (se 2 (by rfl) ⟨926442, by rfl⟩ : syracuseStep 2470513 = 1852885) (by norm_num)
theorem B3294017 : Blo 2195435 3294017 := bstep (se 2 (by rfl) ⟨1235256, by rfl⟩ : syracuseStep 3294017 = 2470513) B2470513
theorem B2196011 : Blo 2195435 2196011 := bstep (se 1 (by rfl) ⟨1647008, by rfl⟩ : syracuseStep 2196011 = 3294017) B3294017
theorem B3957293 : Blo 2195435 3957293 := bbase (se 3 (by rfl) ⟨741992, by rfl⟩ : syracuseStep 3957293 = 1483985) (by norm_num)
theorem B10552781 : Blo 2195435 10552781 := bstep (se 3 (by rfl) ⟨1978646, by rfl⟩ : syracuseStep 10552781 = 3957293) B3957293
theorem B7035187 : Blo 2195435 7035187 := bstep (se 1 (by rfl) ⟨5276390, by rfl⟩ : syracuseStep 7035187 = 10552781) B10552781
theorem B9380249 : Blo 2195435 9380249 := bstep (se 2 (by rfl) ⟨3517593, by rfl⟩ : syracuseStep 9380249 = 7035187) B7035187
theorem B6253499 : Blo 2195435 6253499 := bstep (se 1 (by rfl) ⟨4690124, by rfl⟩ : syracuseStep 6253499 = 9380249) B9380249
theorem B4168999 : Blo 2195435 4168999 := bstep (se 1 (by rfl) ⟨3126749, by rfl⟩ : syracuseStep 4168999 = 6253499) B6253499
theorem B5558665 : Blo 2195435 5558665 := bstep (se 2 (by rfl) ⟨2084499, by rfl⟩ : syracuseStep 5558665 = 4168999) B4168999
theorem B7411553 : Blo 2195435 7411553 := bstep (se 2 (by rfl) ⟨2779332, by rfl⟩ : syracuseStep 7411553 = 5558665) B5558665
theorem B4941035 : Blo 2195435 4941035 := bstep (se 1 (by rfl) ⟨3705776, by rfl⟩ : syracuseStep 4941035 = 7411553) B7411553
theorem B3294023 : Blo 2195435 3294023 := bstep (se 1 (by rfl) ⟨2470517, by rfl⟩ : syracuseStep 3294023 = 4941035) B4941035
theorem B2196015 : Blo 2195435 2196015 := bstep (se 1 (by rfl) ⟨1647011, by rfl⟩ : syracuseStep 2196015 = 3294023) B3294023
theorem B3294029 : Blo 2195435 3294029 := bbase (se 3 (by rfl) ⟨617630, by rfl⟩ : syracuseStep 3294029 = 1235261) (by norm_num)
theorem B2196019 : Blo 2195435 2196019 := bstep (se 1 (by rfl) ⟨1647014, by rfl⟩ : syracuseStep 2196019 = 3294029) B3294029
theorem B4941053 : Blo 2195435 4941053 := bbase (se 3 (by rfl) ⟨926447, by rfl⟩ : syracuseStep 4941053 = 1852895) (by norm_num)
theorem B3294035 : Blo 2195435 3294035 := bstep (se 1 (by rfl) ⟨2470526, by rfl⟩ : syracuseStep 3294035 = 4941053) B4941053
theorem B2196023 : Blo 2195435 2196023 := bstep (se 1 (by rfl) ⟨1647017, by rfl⟩ : syracuseStep 2196023 = 3294035) B3294035
theorem B3705797 : Blo 2195435 3705797 := bbase (se 4 (by rfl) ⟨347418, by rfl⟩ : syracuseStep 3705797 = 694837) (by norm_num)
theorem B2470531 : Blo 2195435 2470531 := bstep (se 1 (by rfl) ⟨1852898, by rfl⟩ : syracuseStep 2470531 = 3705797) B3705797
theorem B3294041 : Blo 2195435 3294041 := bstep (se 2 (by rfl) ⟨1235265, by rfl⟩ : syracuseStep 3294041 = 2470531) B2470531
theorem B2196027 : Blo 2195435 2196027 := bstep (se 1 (by rfl) ⟨1647020, by rfl⟩ : syracuseStep 2196027 = 3294041) B3294041
theorem B16676117 : Blo 2195435 16676117 := bbase (se 6 (by rfl) ⟨390846, by rfl⟩ : syracuseStep 16676117 = 781693) (by norm_num)
theorem B11117411 : Blo 2195435 11117411 := bstep (se 1 (by rfl) ⟨8338058, by rfl⟩ : syracuseStep 11117411 = 16676117) B16676117
theorem B7411607 : Blo 2195435 7411607 := bstep (se 1 (by rfl) ⟨5558705, by rfl⟩ : syracuseStep 7411607 = 11117411) B11117411
theorem B4941071 : Blo 2195435 4941071 := bstep (se 1 (by rfl) ⟨3705803, by rfl⟩ : syracuseStep 4941071 = 7411607) B7411607
theorem B3294047 : Blo 2195435 3294047 := bstep (se 1 (by rfl) ⟨2470535, by rfl⟩ : syracuseStep 3294047 = 4941071) B4941071
theorem B2196031 : Blo 2195435 2196031 := bstep (se 1 (by rfl) ⟨1647023, by rfl⟩ : syracuseStep 2196031 = 3294047) B3294047
theorem B3294053 : Blo 2195435 3294053 := bbase (se 4 (by rfl) ⟨308817, by rfl⟩ : syracuseStep 3294053 = 617635) (by norm_num)
theorem B2196035 : Blo 2195435 2196035 := bstep (se 1 (by rfl) ⟨1647026, by rfl⟩ : syracuseStep 2196035 = 3294053) B3294053
theorem B4169045 : Blo 2195435 4169045 := bbase (se 11 (by rfl) ⟨3053, by rfl⟩ : syracuseStep 4169045 = 6107) (by norm_num)
theorem B2779363 : Blo 2195435 2779363 := bstep (se 1 (by rfl) ⟨2084522, by rfl⟩ : syracuseStep 2779363 = 4169045) B4169045
theorem B3705817 : Blo 2195435 3705817 := bstep (se 2 (by rfl) ⟨1389681, by rfl⟩ : syracuseStep 3705817 = 2779363) B2779363
theorem B4941089 : Blo 2195435 4941089 := bstep (se 2 (by rfl) ⟨1852908, by rfl⟩ : syracuseStep 4941089 = 3705817) B3705817
theorem B3294059 : Blo 2195435 3294059 := bstep (se 1 (by rfl) ⟨2470544, by rfl⟩ : syracuseStep 3294059 = 4941089) B4941089
theorem B2196039 : Blo 2195435 2196039 := bstep (se 1 (by rfl) ⟨1647029, by rfl⟩ : syracuseStep 2196039 = 3294059) B3294059
theorem B2470549 : Blo 2195435 2470549 := bbase (se 6 (by rfl) ⟨57903, by rfl⟩ : syracuseStep 2470549 = 115807) (by norm_num)
theorem B3294065 : Blo 2195435 3294065 := bstep (se 2 (by rfl) ⟨1235274, by rfl⟩ : syracuseStep 3294065 = 2470549) B2470549
theorem B2196043 : Blo 2195435 2196043 := bstep (se 1 (by rfl) ⟨1647032, by rfl⟩ : syracuseStep 2196043 = 3294065) B3294065
theorem B2779373 : Blo 2195435 2779373 := bbase (se 3 (by rfl) ⟨521132, by rfl⟩ : syracuseStep 2779373 = 1042265) (by norm_num)
theorem B7411661 : Blo 2195435 7411661 := bstep (se 3 (by rfl) ⟨1389686, by rfl⟩ : syracuseStep 7411661 = 2779373) B2779373
theorem B4941107 : Blo 2195435 4941107 := bstep (se 1 (by rfl) ⟨3705830, by rfl⟩ : syracuseStep 4941107 = 7411661) B7411661
theorem B3294071 : Blo 2195435 3294071 := bstep (se 1 (by rfl) ⟨2470553, by rfl⟩ : syracuseStep 3294071 = 4941107) B4941107
theorem B2196047 : Blo 2195435 2196047 := bstep (se 1 (by rfl) ⟨1647035, by rfl⟩ : syracuseStep 2196047 = 3294071) B3294071
theorem B3294077 : Blo 2195435 3294077 := bbase (se 3 (by rfl) ⟨617639, by rfl⟩ : syracuseStep 3294077 = 1235279) (by norm_num)
theorem B2196051 : Blo 2195435 2196051 := bstep (se 1 (by rfl) ⟨1647038, by rfl⟩ : syracuseStep 2196051 = 3294077) B3294077
theorem B4941125 : Blo 2195435 4941125 := bbase (se 4 (by rfl) ⟨463230, by rfl⟩ : syracuseStep 4941125 = 926461) (by norm_num)
theorem B3294083 : Blo 2195435 3294083 := bstep (se 1 (by rfl) ⟨2470562, by rfl⟩ : syracuseStep 3294083 = 4941125) B4941125
theorem B2196055 : Blo 2195435 2196055 := bstep (se 1 (by rfl) ⟨1647041, by rfl⟩ : syracuseStep 2196055 = 3294083) B3294083
theorem B3957373 : Blo 2195435 3957373 := bbase (se 3 (by rfl) ⟨742007, by rfl⟩ : syracuseStep 3957373 = 1484015) (by norm_num)
theorem B5276497 : Blo 2195435 5276497 := bstep (se 2 (by rfl) ⟨1978686, by rfl⟩ : syracuseStep 5276497 = 3957373) B3957373
theorem B7035329 : Blo 2195435 7035329 := bstep (se 2 (by rfl) ⟨2638248, by rfl⟩ : syracuseStep 7035329 = 5276497) B5276497
theorem B4690219 : Blo 2195435 4690219 := bstep (se 1 (by rfl) ⟨3517664, by rfl⟩ : syracuseStep 4690219 = 7035329) B7035329
theorem B6253625 : Blo 2195435 6253625 := bstep (se 2 (by rfl) ⟨2345109, by rfl⟩ : syracuseStep 6253625 = 4690219) B4690219
theorem B4169083 : Blo 2195435 4169083 := bstep (se 1 (by rfl) ⟨3126812, by rfl⟩ : syracuseStep 4169083 = 6253625) B6253625
theorem B5558777 : Blo 2195435 5558777 := bstep (se 2 (by rfl) ⟨2084541, by rfl⟩ : syracuseStep 5558777 = 4169083) B4169083
theorem B3705851 : Blo 2195435 3705851 := bstep (se 1 (by rfl) ⟨2779388, by rfl⟩ : syracuseStep 3705851 = 5558777) B5558777
theorem B2470567 : Blo 2195435 2470567 := bstep (se 1 (by rfl) ⟨1852925, by rfl⟩ : syracuseStep 2470567 = 3705851) B3705851
theorem B3294089 : Blo 2195435 3294089 := bstep (se 2 (by rfl) ⟨1235283, by rfl⟩ : syracuseStep 3294089 = 2470567) B2470567
theorem B2196059 : Blo 2195435 2196059 := bstep (se 1 (by rfl) ⟨1647044, by rfl⟩ : syracuseStep 2196059 = 3294089) B3294089
theorem B11117573 : Blo 2195435 11117573 := bbase (se 4 (by rfl) ⟨1042272, by rfl⟩ : syracuseStep 11117573 = 2084545) (by norm_num)
theorem B7411715 : Blo 2195435 7411715 := bstep (se 1 (by rfl) ⟨5558786, by rfl⟩ : syracuseStep 7411715 = 11117573) B11117573
theorem B4941143 : Blo 2195435 4941143 := bstep (se 1 (by rfl) ⟨3705857, by rfl⟩ : syracuseStep 4941143 = 7411715) B7411715
theorem B3294095 : Blo 2195435 3294095 := bstep (se 1 (by rfl) ⟨2470571, by rfl⟩ : syracuseStep 3294095 = 4941143) B4941143
theorem B2196063 : Blo 2195435 2196063 := bstep (se 1 (by rfl) ⟨1647047, by rfl⟩ : syracuseStep 2196063 = 3294095) B3294095
theorem B3294101 : Blo 2195435 3294101 := bbase (se 6 (by rfl) ⟨77205, by rfl⟩ : syracuseStep 3294101 = 154411) (by norm_num)
theorem B2196067 : Blo 2195435 2196067 := bstep (se 1 (by rfl) ⟨1647050, by rfl⟩ : syracuseStep 2196067 = 3294101) B3294101
theorem B12507317 : Blo 2195435 12507317 := bbase (se 5 (by rfl) ⟨586280, by rfl⟩ : syracuseStep 12507317 = 1172561) (by norm_num)
theorem B8338211 : Blo 2195435 8338211 := bstep (se 1 (by rfl) ⟨6253658, by rfl⟩ : syracuseStep 8338211 = 12507317) B12507317
theorem B5558807 : Blo 2195435 5558807 := bstep (se 1 (by rfl) ⟨4169105, by rfl⟩ : syracuseStep 5558807 = 8338211) B8338211
theorem B3705871 : Blo 2195435 3705871 := bstep (se 1 (by rfl) ⟨2779403, by rfl⟩ : syracuseStep 3705871 = 5558807) B5558807
theorem B4941161 : Blo 2195435 4941161 := bstep (se 2 (by rfl) ⟨1852935, by rfl⟩ : syracuseStep 4941161 = 3705871) B3705871
theorem B3294107 : Blo 2195435 3294107 := bstep (se 1 (by rfl) ⟨2470580, by rfl⟩ : syracuseStep 3294107 = 4941161) B4941161
theorem B2196071 : Blo 2195435 2196071 := bstep (se 1 (by rfl) ⟨1647053, by rfl⟩ : syracuseStep 2196071 = 3294107) B3294107
theorem B2470585 : Blo 2195435 2470585 := bbase (se 2 (by rfl) ⟨926469, by rfl⟩ : syracuseStep 2470585 = 1852939) (by norm_num)
theorem B3294113 : Blo 2195435 3294113 := bstep (se 2 (by rfl) ⟨1235292, by rfl⟩ : syracuseStep 3294113 = 2470585) B2470585
theorem B2196075 : Blo 2195435 2196075 := bstep (se 1 (by rfl) ⟨1647056, by rfl⟩ : syracuseStep 2196075 = 3294113) B3294113
theorem B4690261 : Blo 2195435 4690261 := bbase (se 10 (by rfl) ⟨6870, by rfl⟩ : syracuseStep 4690261 = 13741) (by norm_num)
theorem B6253681 : Blo 2195435 6253681 := bstep (se 2 (by rfl) ⟨2345130, by rfl⟩ : syracuseStep 6253681 = 4690261) B4690261
theorem B8338241 : Blo 2195435 8338241 := bstep (se 2 (by rfl) ⟨3126840, by rfl⟩ : syracuseStep 8338241 = 6253681) B6253681
theorem B5558827 : Blo 2195435 5558827 := bstep (se 1 (by rfl) ⟨4169120, by rfl⟩ : syracuseStep 5558827 = 8338241) B8338241
theorem B7411769 : Blo 2195435 7411769 := bstep (se 2 (by rfl) ⟨2779413, by rfl⟩ : syracuseStep 7411769 = 5558827) B5558827
theorem B4941179 : Blo 2195435 4941179 := bstep (se 1 (by rfl) ⟨3705884, by rfl⟩ : syracuseStep 4941179 = 7411769) B7411769
theorem B3294119 : Blo 2195435 3294119 := bstep (se 1 (by rfl) ⟨2470589, by rfl⟩ : syracuseStep 3294119 = 4941179) B4941179
theorem B2196079 : Blo 2195435 2196079 := bstep (se 1 (by rfl) ⟨1647059, by rfl⟩ : syracuseStep 2196079 = 3294119) B3294119
theorem B3294125 : Blo 2195435 3294125 := bbase (se 3 (by rfl) ⟨617648, by rfl⟩ : syracuseStep 3294125 = 1235297) (by norm_num)
theorem B2196083 : Blo 2195435 2196083 := bstep (se 1 (by rfl) ⟨1647062, by rfl⟩ : syracuseStep 2196083 = 3294125) B3294125
theorem B4941197 : Blo 2195435 4941197 := bbase (se 3 (by rfl) ⟨926474, by rfl⟩ : syracuseStep 4941197 = 1852949) (by norm_num)
theorem B3294131 : Blo 2195435 3294131 := bstep (se 1 (by rfl) ⟨2470598, by rfl⟩ : syracuseStep 3294131 = 4941197) B4941197
theorem B2196087 : Blo 2195435 2196087 := bstep (se 1 (by rfl) ⟨1647065, by rfl⟩ : syracuseStep 2196087 = 3294131) B3294131
theorem B2779429 : Blo 2195435 2779429 := bbase (se 4 (by rfl) ⟨260571, by rfl⟩ : syracuseStep 2779429 = 521143) (by norm_num)
theorem B3705905 : Blo 2195435 3705905 := bstep (se 2 (by rfl) ⟨1389714, by rfl⟩ : syracuseStep 3705905 = 2779429) B2779429
theorem B2470603 : Blo 2195435 2470603 := bstep (se 1 (by rfl) ⟨1852952, by rfl⟩ : syracuseStep 2470603 = 3705905) B3705905
theorem B3294137 : Blo 2195435 3294137 := bstep (se 2 (by rfl) ⟨1235301, by rfl⟩ : syracuseStep 3294137 = 2470603) B2470603
theorem B2196091 : Blo 2195435 2196091 := bstep (se 1 (by rfl) ⟨1647068, by rfl⟩ : syracuseStep 2196091 = 3294137) B3294137
theorem B47489237 : Blo 2195435 47489237 := bbase (se 7 (by rfl) ⟨556514, by rfl⟩ : syracuseStep 47489237 = 1113029) (by norm_num)
theorem B31659491 : Blo 2195435 31659491 := bstep (se 1 (by rfl) ⟨23744618, by rfl⟩ : syracuseStep 31659491 = 47489237) B47489237
theorem B21106327 : Blo 2195435 21106327 := bstep (se 1 (by rfl) ⟨15829745, by rfl⟩ : syracuseStep 21106327 = 31659491) B31659491
theorem B28141769 : Blo 2195435 28141769 := bstep (se 2 (by rfl) ⟨10553163, by rfl⟩ : syracuseStep 28141769 = 21106327) B21106327
theorem B18761179 : Blo 2195435 18761179 := bstep (se 1 (by rfl) ⟨14070884, by rfl⟩ : syracuseStep 18761179 = 28141769) B28141769
theorem B25014905 : Blo 2195435 25014905 := bstep (se 2 (by rfl) ⟨9380589, by rfl⟩ : syracuseStep 25014905 = 18761179) B18761179
theorem B16676603 : Blo 2195435 16676603 := bstep (se 1 (by rfl) ⟨12507452, by rfl⟩ : syracuseStep 16676603 = 25014905) B25014905
theorem B11117735 : Blo 2195435 11117735 := bstep (se 1 (by rfl) ⟨8338301, by rfl⟩ : syracuseStep 11117735 = 16676603) B16676603
theorem B7411823 : Blo 2195435 7411823 := bstep (se 1 (by rfl) ⟨5558867, by rfl⟩ : syracuseStep 7411823 = 11117735) B11117735
theorem B4941215 : Blo 2195435 4941215 := bstep (se 1 (by rfl) ⟨3705911, by rfl⟩ : syracuseStep 4941215 = 7411823) B7411823
theorem B3294143 : Blo 2195435 3294143 := bstep (se 1 (by rfl) ⟨2470607, by rfl⟩ : syracuseStep 3294143 = 4941215) B4941215
theorem B2196095 : Blo 2195435 2196095 := bstep (se 1 (by rfl) ⟨1647071, by rfl⟩ : syracuseStep 2196095 = 3294143) B3294143
theorem B3294149 : Blo 2195435 3294149 := bbase (se 4 (by rfl) ⟨308826, by rfl⟩ : syracuseStep 3294149 = 617653) (by norm_num)
theorem B2196099 : Blo 2195435 2196099 := bstep (se 1 (by rfl) ⟨1647074, by rfl⟩ : syracuseStep 2196099 = 3294149) B3294149
theorem B3705925 : Blo 2195435 3705925 := bbase (se 4 (by rfl) ⟨347430, by rfl⟩ : syracuseStep 3705925 = 694861) (by norm_num)
theorem B4941233 : Blo 2195435 4941233 := bstep (se 2 (by rfl) ⟨1852962, by rfl⟩ : syracuseStep 4941233 = 3705925) B3705925
theorem B3294155 : Blo 2195435 3294155 := bstep (se 1 (by rfl) ⟨2470616, by rfl⟩ : syracuseStep 3294155 = 4941233) B4941233
theorem B2196103 : Blo 2195435 2196103 := bstep (se 1 (by rfl) ⟨1647077, by rfl⟩ : syracuseStep 2196103 = 3294155) B3294155
theorem B2470621 : Blo 2195435 2470621 := bbase (se 3 (by rfl) ⟨463241, by rfl⟩ : syracuseStep 2470621 = 926483) (by norm_num)
theorem B3294161 : Blo 2195435 3294161 := bstep (se 2 (by rfl) ⟨1235310, by rfl⟩ : syracuseStep 3294161 = 2470621) B2470621
theorem B2196107 : Blo 2195435 2196107 := bstep (se 1 (by rfl) ⟨1647080, by rfl⟩ : syracuseStep 2196107 = 3294161) B3294161
theorem B7411877 : Blo 2195435 7411877 := bbase (se 4 (by rfl) ⟨694863, by rfl⟩ : syracuseStep 7411877 = 1389727) (by norm_num)
theorem B4941251 : Blo 2195435 4941251 := bstep (se 1 (by rfl) ⟨3705938, by rfl⟩ : syracuseStep 4941251 = 7411877) B7411877
theorem B3294167 : Blo 2195435 3294167 := bstep (se 1 (by rfl) ⟨2470625, by rfl⟩ : syracuseStep 3294167 = 4941251) B4941251
theorem B2196111 : Blo 2195435 2196111 := bstep (se 1 (by rfl) ⟨1647083, by rfl⟩ : syracuseStep 2196111 = 3294167) B3294167
theorem B3294173 : Blo 2195435 3294173 := bbase (se 3 (by rfl) ⟨617657, by rfl⟩ : syracuseStep 3294173 = 1235315) (by norm_num)
theorem B2196115 : Blo 2195435 2196115 := bstep (se 1 (by rfl) ⟨1647086, by rfl⟩ : syracuseStep 2196115 = 3294173) B3294173
theorem B4941269 : Blo 2195435 4941269 := bbase (se 7 (by rfl) ⟨57905, by rfl⟩ : syracuseStep 4941269 = 115811) (by norm_num)
theorem B3294179 : Blo 2195435 3294179 := bstep (se 1 (by rfl) ⟨2470634, by rfl⟩ : syracuseStep 3294179 = 4941269) B4941269
theorem B2196119 : Blo 2195435 2196119 := bstep (se 1 (by rfl) ⟨1647089, by rfl⟩ : syracuseStep 2196119 = 3294179) B3294179
theorem B4819213 : Blo 2195435 4819213 := bbase (se 3 (by rfl) ⟨903602, by rfl⟩ : syracuseStep 4819213 = 1807205) (by norm_num)
theorem B25702469 : Blo 2195435 25702469 := bstep (se 4 (by rfl) ⟨2409606, by rfl⟩ : syracuseStep 25702469 = 4819213) B4819213
theorem B17134979 : Blo 2195435 17134979 := bstep (se 1 (by rfl) ⟨12851234, by rfl⟩ : syracuseStep 17134979 = 25702469) B25702469
theorem B182773109 : Blo 2195435 182773109 := bstep (se 5 (by rfl) ⟨8567489, by rfl⟩ : syracuseStep 182773109 = 17134979) B17134979
theorem B487394957 : Blo 2195435 487394957 := bstep (se 3 (by rfl) ⟨91386554, by rfl⟩ : syracuseStep 487394957 = 182773109) B182773109
theorem B324929971 : Blo 2195435 324929971 := bstep (se 1 (by rfl) ⟨243697478, by rfl⟩ : syracuseStep 324929971 = 487394957) B487394957
theorem B433239961 : Blo 2195435 433239961 := bstep (se 2 (by rfl) ⟨162464985, by rfl⟩ : syracuseStep 433239961 = 324929971) B324929971
theorem B577653281 : Blo 2195435 577653281 := bstep (se 2 (by rfl) ⟨216619980, by rfl⟩ : syracuseStep 577653281 = 433239961) B433239961
theorem B385102187 : Blo 2195435 385102187 := bstep (se 1 (by rfl) ⟨288826640, by rfl⟩ : syracuseStep 385102187 = 577653281) B577653281
theorem B256734791 : Blo 2195435 256734791 := bstep (se 1 (by rfl) ⟨192551093, by rfl⟩ : syracuseStep 256734791 = 385102187) B385102187
theorem B171156527 : Blo 2195435 171156527 := bstep (se 1 (by rfl) ⟨128367395, by rfl⟩ : syracuseStep 171156527 = 256734791) B256734791
theorem B114104351 : Blo 2195435 114104351 := bstep (se 1 (by rfl) ⟨85578263, by rfl⟩ : syracuseStep 114104351 = 171156527) B171156527
theorem B76069567 : Blo 2195435 76069567 := bstep (se 1 (by rfl) ⟨57052175, by rfl⟩ : syracuseStep 76069567 = 114104351) B114104351
theorem B101426089 : Blo 2195435 101426089 := bstep (se 2 (by rfl) ⟨38034783, by rfl⟩ : syracuseStep 101426089 = 76069567) B76069567
theorem B135234785 : Blo 2195435 135234785 := bstep (se 2 (by rfl) ⟨50713044, by rfl⟩ : syracuseStep 135234785 = 101426089) B101426089
theorem B90156523 : Blo 2195435 90156523 := bstep (se 1 (by rfl) ⟨67617392, by rfl⟩ : syracuseStep 90156523 = 135234785) B135234785
theorem B120208697 : Blo 2195435 120208697 := bstep (se 2 (by rfl) ⟨45078261, by rfl⟩ : syracuseStep 120208697 = 90156523) B90156523
theorem B80139131 : Blo 2195435 80139131 := bstep (se 1 (by rfl) ⟨60104348, by rfl⟩ : syracuseStep 80139131 = 120208697) B120208697
theorem B53426087 : Blo 2195435 53426087 := bstep (se 1 (by rfl) ⟨40069565, by rfl⟩ : syracuseStep 53426087 = 80139131) B80139131
theorem B35617391 : Blo 2195435 35617391 := bstep (se 1 (by rfl) ⟨26713043, by rfl⟩ : syracuseStep 35617391 = 53426087) B53426087
theorem B23744927 : Blo 2195435 23744927 := bstep (se 1 (by rfl) ⟨17808695, by rfl⟩ : syracuseStep 23744927 = 35617391) B35617391
theorem B15829951 : Blo 2195435 15829951 := bstep (se 1 (by rfl) ⟨11872463, by rfl⟩ : syracuseStep 15829951 = 23744927) B23744927
theorem B21106601 : Blo 2195435 21106601 := bstep (se 2 (by rfl) ⟨7914975, by rfl⟩ : syracuseStep 21106601 = 15829951) B15829951
theorem B14071067 : Blo 2195435 14071067 := bstep (se 1 (by rfl) ⟨10553300, by rfl⟩ : syracuseStep 14071067 = 21106601) B21106601
theorem B9380711 : Blo 2195435 9380711 := bstep (se 1 (by rfl) ⟨7035533, by rfl⟩ : syracuseStep 9380711 = 14071067) B14071067
theorem B6253807 : Blo 2195435 6253807 := bstep (se 1 (by rfl) ⟨4690355, by rfl⟩ : syracuseStep 6253807 = 9380711) B9380711
theorem B8338409 : Blo 2195435 8338409 := bstep (se 2 (by rfl) ⟨3126903, by rfl⟩ : syracuseStep 8338409 = 6253807) B6253807
theorem B5558939 : Blo 2195435 5558939 := bstep (se 1 (by rfl) ⟨4169204, by rfl⟩ : syracuseStep 5558939 = 8338409) B8338409
theorem B3705959 : Blo 2195435 3705959 := bstep (se 1 (by rfl) ⟨2779469, by rfl⟩ : syracuseStep 3705959 = 5558939) B5558939
theorem B2470639 : Blo 2195435 2470639 := bstep (se 1 (by rfl) ⟨1852979, by rfl⟩ : syracuseStep 2470639 = 3705959) B3705959
theorem B3294185 : Blo 2195435 3294185 := bstep (se 2 (by rfl) ⟨1235319, by rfl⟩ : syracuseStep 3294185 = 2470639) B2470639
theorem B2196123 : Blo 2195435 2196123 := bstep (se 1 (by rfl) ⟨1647092, by rfl⟩ : syracuseStep 2196123 = 3294185) B3294185
theorem B2504353 : Blo 2195435 2504353 := bbase (se 2 (by rfl) ⟨939132, by rfl⟩ : syracuseStep 2504353 = 1878265) (by norm_num)
theorem B3339137 : Blo 2195435 3339137 := bstep (se 2 (by rfl) ⟨1252176, by rfl⟩ : syracuseStep 3339137 = 2504353) B2504353
theorem B2226091 : Blo 2195435 2226091 := bstep (se 1 (by rfl) ⟨1669568, by rfl⟩ : syracuseStep 2226091 = 3339137) B3339137
theorem B2968121 : Blo 2195435 2968121 := bstep (se 2 (by rfl) ⟨1113045, by rfl⟩ : syracuseStep 2968121 = 2226091) B2226091
theorem B7914989 : Blo 2195435 7914989 := bstep (se 3 (by rfl) ⟨1484060, by rfl⟩ : syracuseStep 7914989 = 2968121) B2968121
theorem B5276659 : Blo 2195435 5276659 := bstep (se 1 (by rfl) ⟨3957494, by rfl⟩ : syracuseStep 5276659 = 7914989) B7914989
theorem B7035545 : Blo 2195435 7035545 := bstep (se 2 (by rfl) ⟨2638329, by rfl⟩ : syracuseStep 7035545 = 5276659) B5276659
theorem B18761453 : Blo 2195435 18761453 := bstep (se 3 (by rfl) ⟨3517772, by rfl⟩ : syracuseStep 18761453 = 7035545) B7035545
theorem B12507635 : Blo 2195435 12507635 := bstep (se 1 (by rfl) ⟨9380726, by rfl⟩ : syracuseStep 12507635 = 18761453) B18761453
theorem B8338423 : Blo 2195435 8338423 := bstep (se 1 (by rfl) ⟨6253817, by rfl⟩ : syracuseStep 8338423 = 12507635) B12507635
theorem B11117897 : Blo 2195435 11117897 := bstep (se 2 (by rfl) ⟨4169211, by rfl⟩ : syracuseStep 11117897 = 8338423) B8338423
theorem B7411931 : Blo 2195435 7411931 := bstep (se 1 (by rfl) ⟨5558948, by rfl⟩ : syracuseStep 7411931 = 11117897) B11117897
theorem B4941287 : Blo 2195435 4941287 := bstep (se 1 (by rfl) ⟨3705965, by rfl⟩ : syracuseStep 4941287 = 7411931) B7411931
theorem B3294191 : Blo 2195435 3294191 := bstep (se 1 (by rfl) ⟨2470643, by rfl⟩ : syracuseStep 3294191 = 4941287) B4941287
theorem B2196127 : Blo 2195435 2196127 := bstep (se 1 (by rfl) ⟨1647095, by rfl⟩ : syracuseStep 2196127 = 3294191) B3294191
theorem B3294197 : Blo 2195435 3294197 := bbase (se 5 (by rfl) ⟨154415, by rfl⟩ : syracuseStep 3294197 = 308831) (by norm_num)
theorem B2196131 : Blo 2195435 2196131 := bstep (se 1 (by rfl) ⟨1647098, by rfl⟩ : syracuseStep 2196131 = 3294197) B3294197
theorem B4690381 : Blo 2195435 4690381 := bbase (se 3 (by rfl) ⟨879446, by rfl⟩ : syracuseStep 4690381 = 1758893) (by norm_num)
theorem B6253841 : Blo 2195435 6253841 := bstep (se 2 (by rfl) ⟨2345190, by rfl⟩ : syracuseStep 6253841 = 4690381) B4690381
theorem B4169227 : Blo 2195435 4169227 := bstep (se 1 (by rfl) ⟨3126920, by rfl⟩ : syracuseStep 4169227 = 6253841) B6253841
theorem B5558969 : Blo 2195435 5558969 := bstep (se 2 (by rfl) ⟨2084613, by rfl⟩ : syracuseStep 5558969 = 4169227) B4169227
theorem B3705979 : Blo 2195435 3705979 := bstep (se 1 (by rfl) ⟨2779484, by rfl⟩ : syracuseStep 3705979 = 5558969) B5558969
theorem B4941305 : Blo 2195435 4941305 := bstep (se 2 (by rfl) ⟨1852989, by rfl⟩ : syracuseStep 4941305 = 3705979) B3705979
theorem B3294203 : Blo 2195435 3294203 := bstep (se 1 (by rfl) ⟨2470652, by rfl⟩ : syracuseStep 3294203 = 4941305) B4941305
theorem B2196135 : Blo 2195435 2196135 := bstep (se 1 (by rfl) ⟨1647101, by rfl⟩ : syracuseStep 2196135 = 3294203) B3294203
theorem B2470657 : Blo 2195435 2470657 := bbase (se 2 (by rfl) ⟨926496, by rfl⟩ : syracuseStep 2470657 = 1852993) (by norm_num)
theorem B3294209 : Blo 2195435 3294209 := bstep (se 2 (by rfl) ⟨1235328, by rfl⟩ : syracuseStep 3294209 = 2470657) B2470657
theorem B2196139 : Blo 2195435 2196139 := bstep (se 1 (by rfl) ⟨1647104, by rfl⟩ : syracuseStep 2196139 = 3294209) B3294209
theorem B5558989 : Blo 2195435 5558989 := bbase (se 3 (by rfl) ⟨1042310, by rfl⟩ : syracuseStep 5558989 = 2084621) (by norm_num)
theorem B7411985 : Blo 2195435 7411985 := bstep (se 2 (by rfl) ⟨2779494, by rfl⟩ : syracuseStep 7411985 = 5558989) B5558989
theorem B4941323 : Blo 2195435 4941323 := bstep (se 1 (by rfl) ⟨3705992, by rfl⟩ : syracuseStep 4941323 = 7411985) B7411985
theorem B3294215 : Blo 2195435 3294215 := bstep (se 1 (by rfl) ⟨2470661, by rfl⟩ : syracuseStep 3294215 = 4941323) B4941323
theorem B2196143 : Blo 2195435 2196143 := bstep (se 1 (by rfl) ⟨1647107, by rfl⟩ : syracuseStep 2196143 = 3294215) B3294215
theorem B3294221 : Blo 2195435 3294221 := bbase (se 3 (by rfl) ⟨617666, by rfl⟩ : syracuseStep 3294221 = 1235333) (by norm_num)
theorem B2196147 : Blo 2195435 2196147 := bstep (se 1 (by rfl) ⟨1647110, by rfl⟩ : syracuseStep 2196147 = 3294221) B3294221
theorem B4941341 : Blo 2195435 4941341 := bbase (se 3 (by rfl) ⟨926501, by rfl⟩ : syracuseStep 4941341 = 1853003) (by norm_num)
theorem B3294227 : Blo 2195435 3294227 := bstep (se 1 (by rfl) ⟨2470670, by rfl⟩ : syracuseStep 3294227 = 4941341) B4941341
theorem B2196151 : Blo 2195435 2196151 := bstep (se 1 (by rfl) ⟨1647113, by rfl⟩ : syracuseStep 2196151 = 3294227) B3294227
theorem B3706013 : Blo 2195435 3706013 := bbase (se 3 (by rfl) ⟨694877, by rfl⟩ : syracuseStep 3706013 = 1389755) (by norm_num)
theorem B2470675 : Blo 2195435 2470675 := bstep (se 1 (by rfl) ⟨1853006, by rfl⟩ : syracuseStep 2470675 = 3706013) B3706013
theorem B3294233 : Blo 2195435 3294233 := bstep (se 2 (by rfl) ⟨1235337, by rfl⟩ : syracuseStep 3294233 = 2470675) B2470675
theorem B2196155 : Blo 2195435 2196155 := bstep (se 1 (by rfl) ⟨1647116, by rfl⟩ : syracuseStep 2196155 = 3294233) B3294233
theorem B9149125 : Blo 2195435 9149125 := bbase (se 4 (by rfl) ⟨857730, by rfl⟩ : syracuseStep 9149125 = 1715461) (by norm_num)
theorem B12198833 : Blo 2195435 12198833 := bstep (se 2 (by rfl) ⟨4574562, by rfl⟩ : syracuseStep 12198833 = 9149125) B9149125
theorem B8132555 : Blo 2195435 8132555 := bstep (se 1 (by rfl) ⟨6099416, by rfl⟩ : syracuseStep 8132555 = 12198833) B12198833
theorem B5421703 : Blo 2195435 5421703 := bstep (se 1 (by rfl) ⟨4066277, by rfl⟩ : syracuseStep 5421703 = 8132555) B8132555
theorem B7228937 : Blo 2195435 7228937 := bstep (se 2 (by rfl) ⟨2710851, by rfl⟩ : syracuseStep 7228937 = 5421703) B5421703
theorem B19277165 : Blo 2195435 19277165 := bstep (se 3 (by rfl) ⟨3614468, by rfl⟩ : syracuseStep 19277165 = 7228937) B7228937
theorem B12851443 : Blo 2195435 12851443 := bstep (se 1 (by rfl) ⟨9638582, by rfl⟩ : syracuseStep 12851443 = 19277165) B19277165
theorem B68541029 : Blo 2195435 68541029 := bstep (se 4 (by rfl) ⟨6425721, by rfl⟩ : syracuseStep 68541029 = 12851443) B12851443
theorem B45694019 : Blo 2195435 45694019 := bstep (se 1 (by rfl) ⟨34270514, by rfl⟩ : syracuseStep 45694019 = 68541029) B68541029
theorem B30462679 : Blo 2195435 30462679 := bstep (se 1 (by rfl) ⟨22847009, by rfl⟩ : syracuseStep 30462679 = 45694019) B45694019
theorem B40616905 : Blo 2195435 40616905 := bstep (se 2 (by rfl) ⟨15231339, by rfl⟩ : syracuseStep 40616905 = 30462679) B30462679
theorem B54155873 : Blo 2195435 54155873 := bstep (se 2 (by rfl) ⟨20308452, by rfl⟩ : syracuseStep 54155873 = 40616905) B40616905
theorem B36103915 : Blo 2195435 36103915 := bstep (se 1 (by rfl) ⟨27077936, by rfl⟩ : syracuseStep 36103915 = 54155873) B54155873
theorem B48138553 : Blo 2195435 48138553 := bstep (se 2 (by rfl) ⟨18051957, by rfl⟩ : syracuseStep 48138553 = 36103915) B36103915
theorem B64184737 : Blo 2195435 64184737 := bstep (se 2 (by rfl) ⟨24069276, by rfl⟩ : syracuseStep 64184737 = 48138553) B48138553
theorem B85579649 : Blo 2195435 85579649 := bstep (se 2 (by rfl) ⟨32092368, by rfl⟩ : syracuseStep 85579649 = 64184737) B64184737
theorem B57053099 : Blo 2195435 57053099 := bstep (se 1 (by rfl) ⟨42789824, by rfl⟩ : syracuseStep 57053099 = 85579649) B85579649
theorem B38035399 : Blo 2195435 38035399 := bstep (se 1 (by rfl) ⟨28526549, by rfl⟩ : syracuseStep 38035399 = 57053099) B57053099
theorem B50713865 : Blo 2195435 50713865 := bstep (se 2 (by rfl) ⟨19017699, by rfl⟩ : syracuseStep 50713865 = 38035399) B38035399
theorem B33809243 : Blo 2195435 33809243 := bstep (se 1 (by rfl) ⟨25356932, by rfl⟩ : syracuseStep 33809243 = 50713865) B50713865
theorem B360631925 : Blo 2195435 360631925 := bstep (se 5 (by rfl) ⟨16904621, by rfl⟩ : syracuseStep 360631925 = 33809243) B33809243
theorem B240421283 : Blo 2195435 240421283 := bstep (se 1 (by rfl) ⟨180315962, by rfl⟩ : syracuseStep 240421283 = 360631925) B360631925
theorem B160280855 : Blo 2195435 160280855 := bstep (se 1 (by rfl) ⟨120210641, by rfl⟩ : syracuseStep 160280855 = 240421283) B240421283
theorem B106853903 : Blo 2195435 106853903 := bstep (se 1 (by rfl) ⟨80140427, by rfl⟩ : syracuseStep 106853903 = 160280855) B160280855
theorem B71235935 : Blo 2195435 71235935 := bstep (se 1 (by rfl) ⟨53426951, by rfl⟩ : syracuseStep 71235935 = 106853903) B106853903
theorem B47490623 : Blo 2195435 47490623 := bstep (se 1 (by rfl) ⟨35617967, by rfl⟩ : syracuseStep 47490623 = 71235935) B71235935
theorem B31660415 : Blo 2195435 31660415 := bstep (se 1 (by rfl) ⟨23745311, by rfl⟩ : syracuseStep 31660415 = 47490623) B47490623
theorem B21106943 : Blo 2195435 21106943 := bstep (se 1 (by rfl) ⟨15830207, by rfl⟩ : syracuseStep 21106943 = 31660415) B31660415
theorem B14071295 : Blo 2195435 14071295 := bstep (se 1 (by rfl) ⟨10553471, by rfl⟩ : syracuseStep 14071295 = 21106943) B21106943
theorem B9380863 : Blo 2195435 9380863 := bstep (se 1 (by rfl) ⟨7035647, by rfl⟩ : syracuseStep 9380863 = 14071295) B14071295
theorem B12507817 : Blo 2195435 12507817 := bstep (se 2 (by rfl) ⟨4690431, by rfl⟩ : syracuseStep 12507817 = 9380863) B9380863
theorem B16677089 : Blo 2195435 16677089 := bstep (se 2 (by rfl) ⟨6253908, by rfl⟩ : syracuseStep 16677089 = 12507817) B12507817
theorem B11118059 : Blo 2195435 11118059 := bstep (se 1 (by rfl) ⟨8338544, by rfl⟩ : syracuseStep 11118059 = 16677089) B16677089
theorem B7412039 : Blo 2195435 7412039 := bstep (se 1 (by rfl) ⟨5559029, by rfl⟩ : syracuseStep 7412039 = 11118059) B11118059
theorem B4941359 : Blo 2195435 4941359 := bstep (se 1 (by rfl) ⟨3706019, by rfl⟩ : syracuseStep 4941359 = 7412039) B7412039
theorem B3294239 : Blo 2195435 3294239 := bstep (se 1 (by rfl) ⟨2470679, by rfl⟩ : syracuseStep 3294239 = 4941359) B4941359
theorem B2196159 : Blo 2195435 2196159 := bstep (se 1 (by rfl) ⟨1647119, by rfl⟩ : syracuseStep 2196159 = 3294239) B3294239
theorem B3294245 : Blo 2195435 3294245 := bbase (se 4 (by rfl) ⟨308835, by rfl⟩ : syracuseStep 3294245 = 617671) (by norm_num)
theorem B2196163 : Blo 2195435 2196163 := bstep (se 1 (by rfl) ⟨1647122, by rfl⟩ : syracuseStep 2196163 = 3294245) B3294245
theorem B2779525 : Blo 2195435 2779525 := bbase (se 4 (by rfl) ⟨260580, by rfl⟩ : syracuseStep 2779525 = 521161) (by norm_num)
theorem B3706033 : Blo 2195435 3706033 := bstep (se 2 (by rfl) ⟨1389762, by rfl⟩ : syracuseStep 3706033 = 2779525) B2779525
theorem B4941377 : Blo 2195435 4941377 := bstep (se 2 (by rfl) ⟨1853016, by rfl⟩ : syracuseStep 4941377 = 3706033) B3706033
theorem B3294251 : Blo 2195435 3294251 := bstep (se 1 (by rfl) ⟨2470688, by rfl⟩ : syracuseStep 3294251 = 4941377) B4941377
theorem B2196167 : Blo 2195435 2196167 := bstep (se 1 (by rfl) ⟨1647125, by rfl⟩ : syracuseStep 2196167 = 3294251) B3294251
theorem B2470693 : Blo 2195435 2470693 := bbase (se 4 (by rfl) ⟨231627, by rfl⟩ : syracuseStep 2470693 = 463255) (by norm_num)
theorem B3294257 : Blo 2195435 3294257 := bstep (se 2 (by rfl) ⟨1235346, by rfl⟩ : syracuseStep 3294257 = 2470693) B2470693
theorem B2196171 : Blo 2195435 2196171 := bstep (se 1 (by rfl) ⟨1647128, by rfl⟩ : syracuseStep 2196171 = 3294257) B3294257
theorem B9380933 : Blo 2195435 9380933 := bbase (se 4 (by rfl) ⟨879462, by rfl⟩ : syracuseStep 9380933 = 1758925) (by norm_num)
theorem B6253955 : Blo 2195435 6253955 := bstep (se 1 (by rfl) ⟨4690466, by rfl⟩ : syracuseStep 6253955 = 9380933) B9380933
theorem B4169303 : Blo 2195435 4169303 := bstep (se 1 (by rfl) ⟨3126977, by rfl⟩ : syracuseStep 4169303 = 6253955) B6253955
theorem B2779535 : Blo 2195435 2779535 := bstep (se 1 (by rfl) ⟨2084651, by rfl⟩ : syracuseStep 2779535 = 4169303) B4169303
theorem B7412093 : Blo 2195435 7412093 := bstep (se 3 (by rfl) ⟨1389767, by rfl⟩ : syracuseStep 7412093 = 2779535) B2779535
theorem B4941395 : Blo 2195435 4941395 := bstep (se 1 (by rfl) ⟨3706046, by rfl⟩ : syracuseStep 4941395 = 7412093) B7412093
theorem B3294263 : Blo 2195435 3294263 := bstep (se 1 (by rfl) ⟨2470697, by rfl⟩ : syracuseStep 3294263 = 4941395) B4941395
theorem B2196175 : Blo 2195435 2196175 := bstep (se 1 (by rfl) ⟨1647131, by rfl⟩ : syracuseStep 2196175 = 3294263) B3294263
theorem B3294269 : Blo 2195435 3294269 := bbase (se 3 (by rfl) ⟨617675, by rfl⟩ : syracuseStep 3294269 = 1235351) (by norm_num)
theorem B2196179 : Blo 2195435 2196179 := bstep (se 1 (by rfl) ⟨1647134, by rfl⟩ : syracuseStep 2196179 = 3294269) B3294269
theorem B4941413 : Blo 2195435 4941413 := bbase (se 4 (by rfl) ⟨463257, by rfl⟩ : syracuseStep 4941413 = 926515) (by norm_num)
theorem B3294275 : Blo 2195435 3294275 := bstep (se 1 (by rfl) ⟨2470706, by rfl⟩ : syracuseStep 3294275 = 4941413) B4941413
theorem B2196183 : Blo 2195435 2196183 := bstep (se 1 (by rfl) ⟨1647137, by rfl⟩ : syracuseStep 2196183 = 3294275) B3294275
theorem B5559101 : Blo 2195435 5559101 := bbase (se 3 (by rfl) ⟨1042331, by rfl⟩ : syracuseStep 5559101 = 2084663) (by norm_num)
theorem B3706067 : Blo 2195435 3706067 := bstep (se 1 (by rfl) ⟨2779550, by rfl⟩ : syracuseStep 3706067 = 5559101) B5559101
theorem B2470711 : Blo 2195435 2470711 := bstep (se 1 (by rfl) ⟨1853033, by rfl⟩ : syracuseStep 2470711 = 3706067) B3706067
theorem B3294281 : Blo 2195435 3294281 := bstep (se 2 (by rfl) ⟨1235355, by rfl⟩ : syracuseStep 3294281 = 2470711) B2470711
theorem B2196187 : Blo 2195435 2196187 := bstep (se 1 (by rfl) ⟨1647140, by rfl⟩ : syracuseStep 2196187 = 3294281) B3294281
theorem B4169333 : Blo 2195435 4169333 := bbase (se 5 (by rfl) ⟨195437, by rfl⟩ : syracuseStep 4169333 = 390875) (by norm_num)
theorem B11118221 : Blo 2195435 11118221 := bstep (se 3 (by rfl) ⟨2084666, by rfl⟩ : syracuseStep 11118221 = 4169333) B4169333
theorem B7412147 : Blo 2195435 7412147 := bstep (se 1 (by rfl) ⟨5559110, by rfl⟩ : syracuseStep 7412147 = 11118221) B11118221
theorem B4941431 : Blo 2195435 4941431 := bstep (se 1 (by rfl) ⟨3706073, by rfl⟩ : syracuseStep 4941431 = 7412147) B7412147
theorem B3294287 : Blo 2195435 3294287 := bstep (se 1 (by rfl) ⟨2470715, by rfl⟩ : syracuseStep 3294287 = 4941431) B4941431
theorem B2196191 : Blo 2195435 2196191 := bstep (se 1 (by rfl) ⟨1647143, by rfl⟩ : syracuseStep 2196191 = 3294287) B3294287
theorem B3294293 : Blo 2195435 3294293 := bbase (se 8 (by rfl) ⟨19302, by rfl⟩ : syracuseStep 3294293 = 38605) (by norm_num)
theorem B2196195 : Blo 2195435 2196195 := bstep (se 1 (by rfl) ⟨1647146, by rfl⟩ : syracuseStep 2196195 = 3294293) B3294293
theorem B5936437 : Blo 2195435 5936437 := bbase (se 5 (by rfl) ⟨278270, by rfl⟩ : syracuseStep 5936437 = 556541) (by norm_num)
theorem B7915249 : Blo 2195435 7915249 := bstep (se 2 (by rfl) ⟨2968218, by rfl⟩ : syracuseStep 7915249 = 5936437) B5936437
theorem B10553665 : Blo 2195435 10553665 := bstep (se 2 (by rfl) ⟨3957624, by rfl⟩ : syracuseStep 10553665 = 7915249) B7915249
theorem B14071553 : Blo 2195435 14071553 := bstep (se 2 (by rfl) ⟨5276832, by rfl⟩ : syracuseStep 14071553 = 10553665) B10553665
theorem B9381035 : Blo 2195435 9381035 := bstep (se 1 (by rfl) ⟨7035776, by rfl⟩ : syracuseStep 9381035 = 14071553) B14071553
theorem B6254023 : Blo 2195435 6254023 := bstep (se 1 (by rfl) ⟨4690517, by rfl⟩ : syracuseStep 6254023 = 9381035) B9381035
theorem B8338697 : Blo 2195435 8338697 := bstep (se 2 (by rfl) ⟨3127011, by rfl⟩ : syracuseStep 8338697 = 6254023) B6254023
theorem B5559131 : Blo 2195435 5559131 := bstep (se 1 (by rfl) ⟨4169348, by rfl⟩ : syracuseStep 5559131 = 8338697) B8338697
theorem B3706087 : Blo 2195435 3706087 := bstep (se 1 (by rfl) ⟨2779565, by rfl⟩ : syracuseStep 3706087 = 5559131) B5559131
theorem B4941449 : Blo 2195435 4941449 := bstep (se 2 (by rfl) ⟨1853043, by rfl⟩ : syracuseStep 4941449 = 3706087) B3706087
theorem B3294299 : Blo 2195435 3294299 := bstep (se 1 (by rfl) ⟨2470724, by rfl⟩ : syracuseStep 3294299 = 4941449) B4941449
theorem B2196199 : Blo 2195435 2196199 := bstep (se 1 (by rfl) ⟨1647149, by rfl⟩ : syracuseStep 2196199 = 3294299) B3294299
theorem B2470729 : Blo 2195435 2470729 := bbase (se 2 (by rfl) ⟨926523, by rfl⟩ : syracuseStep 2470729 = 1853047) (by norm_num)
theorem B3294305 : Blo 2195435 3294305 := bstep (se 2 (by rfl) ⟨1235364, by rfl⟩ : syracuseStep 3294305 = 2470729) B2470729
theorem B2196203 : Blo 2195435 2196203 := bstep (se 1 (by rfl) ⟨1647152, by rfl⟩ : syracuseStep 2196203 = 3294305) B3294305
theorem B2968229 : Blo 2195435 2968229 := bbase (se 4 (by rfl) ⟨278271, by rfl⟩ : syracuseStep 2968229 = 556543) (by norm_num)
theorem B7915277 : Blo 2195435 7915277 := bstep (se 3 (by rfl) ⟨1484114, by rfl⟩ : syracuseStep 7915277 = 2968229) B2968229
theorem B21107405 : Blo 2195435 21107405 := bstep (se 3 (by rfl) ⟨3957638, by rfl⟩ : syracuseStep 21107405 = 7915277) B7915277
theorem B14071603 : Blo 2195435 14071603 := bstep (se 1 (by rfl) ⟨10553702, by rfl⟩ : syracuseStep 14071603 = 21107405) B21107405
theorem B18762137 : Blo 2195435 18762137 := bstep (se 2 (by rfl) ⟨7035801, by rfl⟩ : syracuseStep 18762137 = 14071603) B14071603
theorem B12508091 : Blo 2195435 12508091 := bstep (se 1 (by rfl) ⟨9381068, by rfl⟩ : syracuseStep 12508091 = 18762137) B18762137
theorem B8338727 : Blo 2195435 8338727 := bstep (se 1 (by rfl) ⟨6254045, by rfl⟩ : syracuseStep 8338727 = 12508091) B12508091
theorem B5559151 : Blo 2195435 5559151 := bstep (se 1 (by rfl) ⟨4169363, by rfl⟩ : syracuseStep 5559151 = 8338727) B8338727
theorem B7412201 : Blo 2195435 7412201 := bstep (se 2 (by rfl) ⟨2779575, by rfl⟩ : syracuseStep 7412201 = 5559151) B5559151
theorem B4941467 : Blo 2195435 4941467 := bstep (se 1 (by rfl) ⟨3706100, by rfl⟩ : syracuseStep 4941467 = 7412201) B7412201
theorem B3294311 : Blo 2195435 3294311 := bstep (se 1 (by rfl) ⟨2470733, by rfl⟩ : syracuseStep 3294311 = 4941467) B4941467
theorem B2196207 : Blo 2195435 2196207 := bstep (se 1 (by rfl) ⟨1647155, by rfl⟩ : syracuseStep 2196207 = 3294311) B3294311
theorem B3294317 : Blo 2195435 3294317 := bbase (se 3 (by rfl) ⟨617684, by rfl⟩ : syracuseStep 3294317 = 1235369) (by norm_num)
theorem B2196211 : Blo 2195435 2196211 := bstep (se 1 (by rfl) ⟨1647158, by rfl⟩ : syracuseStep 2196211 = 3294317) B3294317
theorem B4941485 : Blo 2195435 4941485 := bbase (se 3 (by rfl) ⟨926528, by rfl⟩ : syracuseStep 4941485 = 1853057) (by norm_num)
theorem B3294323 : Blo 2195435 3294323 := bstep (se 1 (by rfl) ⟨2470742, by rfl⟩ : syracuseStep 3294323 = 4941485) B4941485
theorem B2196215 : Blo 2195435 2196215 := bstep (se 1 (by rfl) ⟨1647161, by rfl⟩ : syracuseStep 2196215 = 3294323) B3294323
theorem B2638441 : Blo 2195435 2638441 := bbase (se 2 (by rfl) ⟨989415, by rfl⟩ : syracuseStep 2638441 = 1978831) (by norm_num)
theorem B3517921 : Blo 2195435 3517921 := bstep (se 2 (by rfl) ⟨1319220, by rfl⟩ : syracuseStep 3517921 = 2638441) B2638441
theorem B4690561 : Blo 2195435 4690561 := bstep (se 2 (by rfl) ⟨1758960, by rfl⟩ : syracuseStep 4690561 = 3517921) B3517921
theorem B6254081 : Blo 2195435 6254081 := bstep (se 2 (by rfl) ⟨2345280, by rfl⟩ : syracuseStep 6254081 = 4690561) B4690561
theorem B4169387 : Blo 2195435 4169387 := bstep (se 1 (by rfl) ⟨3127040, by rfl⟩ : syracuseStep 4169387 = 6254081) B6254081
theorem B2779591 : Blo 2195435 2779591 := bstep (se 1 (by rfl) ⟨2084693, by rfl⟩ : syracuseStep 2779591 = 4169387) B4169387
theorem B3706121 : Blo 2195435 3706121 := bstep (se 2 (by rfl) ⟨1389795, by rfl⟩ : syracuseStep 3706121 = 2779591) B2779591
theorem B2470747 : Blo 2195435 2470747 := bstep (se 1 (by rfl) ⟨1853060, by rfl⟩ : syracuseStep 2470747 = 3706121) B3706121
theorem B3294329 : Blo 2195435 3294329 := bstep (se 2 (by rfl) ⟨1235373, by rfl⟩ : syracuseStep 3294329 = 2470747) B2470747
theorem B2196219 : Blo 2195435 2196219 := bstep (se 1 (by rfl) ⟨1647164, by rfl⟩ : syracuseStep 2196219 = 3294329) B3294329
theorem B5936501 : Blo 2195435 5936501 := bbase (se 5 (by rfl) ⟨278273, by rfl⟩ : syracuseStep 5936501 = 556547) (by norm_num)
theorem B3957667 : Blo 2195435 3957667 := bstep (se 1 (by rfl) ⟨2968250, by rfl⟩ : syracuseStep 3957667 = 5936501) B5936501
theorem B21107557 : Blo 2195435 21107557 := bstep (se 4 (by rfl) ⟨1978833, by rfl⟩ : syracuseStep 21107557 = 3957667) B3957667
theorem B28143409 : Blo 2195435 28143409 := bstep (se 2 (by rfl) ⟨10553778, by rfl⟩ : syracuseStep 28143409 = 21107557) B21107557
theorem B37524545 : Blo 2195435 37524545 := bstep (se 2 (by rfl) ⟨14071704, by rfl⟩ : syracuseStep 37524545 = 28143409) B28143409
theorem B25016363 : Blo 2195435 25016363 := bstep (se 1 (by rfl) ⟨18762272, by rfl⟩ : syracuseStep 25016363 = 37524545) B37524545
theorem B16677575 : Blo 2195435 16677575 := bstep (se 1 (by rfl) ⟨12508181, by rfl⟩ : syracuseStep 16677575 = 25016363) B25016363
theorem B11118383 : Blo 2195435 11118383 := bstep (se 1 (by rfl) ⟨8338787, by rfl⟩ : syracuseStep 11118383 = 16677575) B16677575
theorem B7412255 : Blo 2195435 7412255 := bstep (se 1 (by rfl) ⟨5559191, by rfl⟩ : syracuseStep 7412255 = 11118383) B11118383
theorem B4941503 : Blo 2195435 4941503 := bstep (se 1 (by rfl) ⟨3706127, by rfl⟩ : syracuseStep 4941503 = 7412255) B7412255
theorem B3294335 : Blo 2195435 3294335 := bstep (se 1 (by rfl) ⟨2470751, by rfl⟩ : syracuseStep 3294335 = 4941503) B4941503
theorem B2196223 : Blo 2195435 2196223 := bstep (se 1 (by rfl) ⟨1647167, by rfl⟩ : syracuseStep 2196223 = 3294335) B3294335
theorem B3294341 : Blo 2195435 3294341 := bbase (se 4 (by rfl) ⟨308844, by rfl⟩ : syracuseStep 3294341 = 617689) (by norm_num)
theorem B2196227 : Blo 2195435 2196227 := bstep (se 1 (by rfl) ⟨1647170, by rfl⟩ : syracuseStep 2196227 = 3294341) B3294341
theorem B3706141 : Blo 2195435 3706141 := bbase (se 3 (by rfl) ⟨694901, by rfl⟩ : syracuseStep 3706141 = 1389803) (by norm_num)
theorem B4941521 : Blo 2195435 4941521 := bstep (se 2 (by rfl) ⟨1853070, by rfl⟩ : syracuseStep 4941521 = 3706141) B3706141
theorem B3294347 : Blo 2195435 3294347 := bstep (se 1 (by rfl) ⟨2470760, by rfl⟩ : syracuseStep 3294347 = 4941521) B4941521
theorem B2196231 : Blo 2195435 2196231 := bstep (se 1 (by rfl) ⟨1647173, by rfl⟩ : syracuseStep 2196231 = 3294347) B3294347
theorem B2470765 : Blo 2195435 2470765 := bbase (se 3 (by rfl) ⟨463268, by rfl⟩ : syracuseStep 2470765 = 926537) (by norm_num)
theorem B3294353 : Blo 2195435 3294353 := bstep (se 2 (by rfl) ⟨1235382, by rfl⟩ : syracuseStep 3294353 = 2470765) B2470765
theorem B2196235 : Blo 2195435 2196235 := bstep (se 1 (by rfl) ⟨1647176, by rfl⟩ : syracuseStep 2196235 = 3294353) B3294353
theorem B7412309 : Blo 2195435 7412309 := bbase (se 8 (by rfl) ⟨43431, by rfl⟩ : syracuseStep 7412309 = 86863) (by norm_num)
theorem B4941539 : Blo 2195435 4941539 := bstep (se 1 (by rfl) ⟨3706154, by rfl⟩ : syracuseStep 4941539 = 7412309) B7412309
theorem B3294359 : Blo 2195435 3294359 := bstep (se 1 (by rfl) ⟨2470769, by rfl⟩ : syracuseStep 3294359 = 4941539) B4941539
theorem B2196239 : Blo 2195435 2196239 := bstep (se 1 (by rfl) ⟨1647179, by rfl⟩ : syracuseStep 2196239 = 3294359) B3294359
theorem B3294365 : Blo 2195435 3294365 := bbase (se 3 (by rfl) ⟨617693, by rfl⟩ : syracuseStep 3294365 = 1235387) (by norm_num)
theorem B2196243 : Blo 2195435 2196243 := bstep (se 1 (by rfl) ⟨1647182, by rfl⟩ : syracuseStep 2196243 = 3294365) B3294365
theorem B4941557 : Blo 2195435 4941557 := bbase (se 5 (by rfl) ⟨231635, by rfl⟩ : syracuseStep 4941557 = 463271) (by norm_num)
theorem B3294371 : Blo 2195435 3294371 := bstep (se 1 (by rfl) ⟨2470778, by rfl⟩ : syracuseStep 3294371 = 4941557) B4941557
theorem B2196247 : Blo 2195435 2196247 := bstep (se 1 (by rfl) ⟨1647185, by rfl⟩ : syracuseStep 2196247 = 3294371) B3294371
theorem B3339325 : Blo 2195435 3339325 := bbase (se 3 (by rfl) ⟨626123, by rfl⟩ : syracuseStep 3339325 = 1252247) (by norm_num)
theorem B17809733 : Blo 2195435 17809733 := bstep (se 4 (by rfl) ⟨1669662, by rfl⟩ : syracuseStep 17809733 = 3339325) B3339325
theorem B11873155 : Blo 2195435 11873155 := bstep (se 1 (by rfl) ⟨8904866, by rfl⟩ : syracuseStep 11873155 = 17809733) B17809733
theorem B15830873 : Blo 2195435 15830873 := bstep (se 2 (by rfl) ⟨5936577, by rfl⟩ : syracuseStep 15830873 = 11873155) B11873155
theorem B10553915 : Blo 2195435 10553915 := bstep (se 1 (by rfl) ⟨7915436, by rfl⟩ : syracuseStep 10553915 = 15830873) B15830873
theorem B28143773 : Blo 2195435 28143773 := bstep (se 3 (by rfl) ⟨5276957, by rfl⟩ : syracuseStep 28143773 = 10553915) B10553915
theorem B18762515 : Blo 2195435 18762515 := bstep (se 1 (by rfl) ⟨14071886, by rfl⟩ : syracuseStep 18762515 = 28143773) B28143773
theorem B12508343 : Blo 2195435 12508343 := bstep (se 1 (by rfl) ⟨9381257, by rfl⟩ : syracuseStep 12508343 = 18762515) B18762515
theorem B8338895 : Blo 2195435 8338895 := bstep (se 1 (by rfl) ⟨6254171, by rfl⟩ : syracuseStep 8338895 = 12508343) B12508343
theorem B5559263 : Blo 2195435 5559263 := bstep (se 1 (by rfl) ⟨4169447, by rfl⟩ : syracuseStep 5559263 = 8338895) B8338895
theorem B3706175 : Blo 2195435 3706175 := bstep (se 1 (by rfl) ⟨2779631, by rfl⟩ : syracuseStep 3706175 = 5559263) B5559263
theorem B2470783 : Blo 2195435 2470783 := bstep (se 1 (by rfl) ⟨1853087, by rfl⟩ : syracuseStep 2470783 = 3706175) B3706175
theorem B3294377 : Blo 2195435 3294377 := bstep (se 2 (by rfl) ⟨1235391, by rfl⟩ : syracuseStep 3294377 = 2470783) B2470783
theorem B2196251 : Blo 2195435 2196251 := bstep (se 1 (by rfl) ⟨1647188, by rfl⟩ : syracuseStep 2196251 = 3294377) B3294377
theorem B4690637 : Blo 2195435 4690637 := bbase (se 3 (by rfl) ⟨879494, by rfl⟩ : syracuseStep 4690637 = 1758989) (by norm_num)
theorem B3127091 : Blo 2195435 3127091 := bstep (se 1 (by rfl) ⟨2345318, by rfl⟩ : syracuseStep 3127091 = 4690637) B4690637
theorem B8338909 : Blo 2195435 8338909 := bstep (se 3 (by rfl) ⟨1563545, by rfl⟩ : syracuseStep 8338909 = 3127091) B3127091
theorem B11118545 : Blo 2195435 11118545 := bstep (se 2 (by rfl) ⟨4169454, by rfl⟩ : syracuseStep 11118545 = 8338909) B8338909
theorem B7412363 : Blo 2195435 7412363 := bstep (se 1 (by rfl) ⟨5559272, by rfl⟩ : syracuseStep 7412363 = 11118545) B11118545
theorem B4941575 : Blo 2195435 4941575 := bstep (se 1 (by rfl) ⟨3706181, by rfl⟩ : syracuseStep 4941575 = 7412363) B7412363
theorem B3294383 : Blo 2195435 3294383 := bstep (se 1 (by rfl) ⟨2470787, by rfl⟩ : syracuseStep 3294383 = 4941575) B4941575
theorem B2196255 : Blo 2195435 2196255 := bstep (se 1 (by rfl) ⟨1647191, by rfl⟩ : syracuseStep 2196255 = 3294383) B3294383
theorem B3294389 : Blo 2195435 3294389 := bbase (se 5 (by rfl) ⟨154424, by rfl⟩ : syracuseStep 3294389 = 308849) (by norm_num)
theorem B2196259 : Blo 2195435 2196259 := bstep (se 1 (by rfl) ⟨1647194, by rfl⟩ : syracuseStep 2196259 = 3294389) B3294389
theorem B5559293 : Blo 2195435 5559293 := bbase (se 3 (by rfl) ⟨1042367, by rfl⟩ : syracuseStep 5559293 = 2084735) (by norm_num)
theorem B3706195 : Blo 2195435 3706195 := bstep (se 1 (by rfl) ⟨2779646, by rfl⟩ : syracuseStep 3706195 = 5559293) B5559293
theorem B4941593 : Blo 2195435 4941593 := bstep (se 2 (by rfl) ⟨1853097, by rfl⟩ : syracuseStep 4941593 = 3706195) B3706195
theorem B3294395 : Blo 2195435 3294395 := bstep (se 1 (by rfl) ⟨2470796, by rfl⟩ : syracuseStep 3294395 = 4941593) B4941593
theorem B2196263 : Blo 2195435 2196263 := bstep (se 1 (by rfl) ⟨1647197, by rfl⟩ : syracuseStep 2196263 = 3294395) B3294395
theorem B2470801 : Blo 2195435 2470801 := bbase (se 2 (by rfl) ⟨926550, by rfl⟩ : syracuseStep 2470801 = 1853101) (by norm_num)
theorem B3294401 : Blo 2195435 3294401 := bstep (se 2 (by rfl) ⟨1235400, by rfl⟩ : syracuseStep 3294401 = 2470801) B2470801
theorem B2196267 : Blo 2195435 2196267 := bstep (se 1 (by rfl) ⟨1647200, by rfl⟩ : syracuseStep 2196267 = 3294401) B3294401
theorem B4169485 : Blo 2195435 4169485 := bbase (se 3 (by rfl) ⟨781778, by rfl⟩ : syracuseStep 4169485 = 1563557) (by norm_num)
theorem B5559313 : Blo 2195435 5559313 := bstep (se 2 (by rfl) ⟨2084742, by rfl⟩ : syracuseStep 5559313 = 4169485) B4169485
theorem B7412417 : Blo 2195435 7412417 := bstep (se 2 (by rfl) ⟨2779656, by rfl⟩ : syracuseStep 7412417 = 5559313) B5559313
theorem B4941611 : Blo 2195435 4941611 := bstep (se 1 (by rfl) ⟨3706208, by rfl⟩ : syracuseStep 4941611 = 7412417) B7412417
theorem B3294407 : Blo 2195435 3294407 := bstep (se 1 (by rfl) ⟨2470805, by rfl⟩ : syracuseStep 3294407 = 4941611) B4941611
theorem B2196271 : Blo 2195435 2196271 := bstep (se 1 (by rfl) ⟨1647203, by rfl⟩ : syracuseStep 2196271 = 3294407) B3294407
theorem B3294413 : Blo 2195435 3294413 := bbase (se 3 (by rfl) ⟨617702, by rfl⟩ : syracuseStep 3294413 = 1235405) (by norm_num)
theorem B2196275 : Blo 2195435 2196275 := bstep (se 1 (by rfl) ⟨1647206, by rfl⟩ : syracuseStep 2196275 = 3294413) B3294413
theorem B4941629 : Blo 2195435 4941629 := bbase (se 3 (by rfl) ⟨926555, by rfl⟩ : syracuseStep 4941629 = 1853111) (by norm_num)
theorem B3294419 : Blo 2195435 3294419 := bstep (se 1 (by rfl) ⟨2470814, by rfl⟩ : syracuseStep 3294419 = 4941629) B4941629
theorem B2196279 : Blo 2195435 2196279 := bstep (se 1 (by rfl) ⟨1647209, by rfl⟩ : syracuseStep 2196279 = 3294419) B3294419
theorem B3706229 : Blo 2195435 3706229 := bbase (se 5 (by rfl) ⟨173729, by rfl⟩ : syracuseStep 3706229 = 347459) (by norm_num)
theorem B2470819 : Blo 2195435 2470819 := bstep (se 1 (by rfl) ⟨1853114, by rfl⟩ : syracuseStep 2470819 = 3706229) B3706229
theorem B3294425 : Blo 2195435 3294425 := bstep (se 2 (by rfl) ⟨1235409, by rfl⟩ : syracuseStep 3294425 = 2470819) B2470819
theorem B2196283 : Blo 2195435 2196283 := bstep (se 1 (by rfl) ⟨1647212, by rfl⟩ : syracuseStep 2196283 = 3294425) B3294425
theorem B3518029 : Blo 2195435 3518029 := bbase (se 3 (by rfl) ⟨659630, by rfl⟩ : syracuseStep 3518029 = 1319261) (by norm_num)
theorem B4690705 : Blo 2195435 4690705 := bstep (se 2 (by rfl) ⟨1759014, by rfl⟩ : syracuseStep 4690705 = 3518029) B3518029
theorem B6254273 : Blo 2195435 6254273 := bstep (se 2 (by rfl) ⟨2345352, by rfl⟩ : syracuseStep 6254273 = 4690705) B4690705
theorem B16678061 : Blo 2195435 16678061 := bstep (se 3 (by rfl) ⟨3127136, by rfl⟩ : syracuseStep 16678061 = 6254273) B6254273
theorem B11118707 : Blo 2195435 11118707 := bstep (se 1 (by rfl) ⟨8339030, by rfl⟩ : syracuseStep 11118707 = 16678061) B16678061
theorem B7412471 : Blo 2195435 7412471 := bstep (se 1 (by rfl) ⟨5559353, by rfl⟩ : syracuseStep 7412471 = 11118707) B11118707
theorem B4941647 : Blo 2195435 4941647 := bstep (se 1 (by rfl) ⟨3706235, by rfl⟩ : syracuseStep 4941647 = 7412471) B7412471
theorem B3294431 : Blo 2195435 3294431 := bstep (se 1 (by rfl) ⟨2470823, by rfl⟩ : syracuseStep 3294431 = 4941647) B4941647
theorem B2196287 : Blo 2195435 2196287 := bstep (se 1 (by rfl) ⟨1647215, by rfl⟩ : syracuseStep 2196287 = 3294431) B3294431
theorem B3294437 : Blo 2195435 3294437 := bbase (se 4 (by rfl) ⟨308853, by rfl⟩ : syracuseStep 3294437 = 617707) (by norm_num)
theorem B2196291 : Blo 2195435 2196291 := bstep (se 1 (by rfl) ⟨1647218, by rfl⟩ : syracuseStep 2196291 = 3294437) B3294437
theorem B7036085 : Blo 2195435 7036085 := bbase (se 5 (by rfl) ⟨329816, by rfl⟩ : syracuseStep 7036085 = 659633) (by norm_num)
theorem B4690723 : Blo 2195435 4690723 := bstep (se 1 (by rfl) ⟨3518042, by rfl⟩ : syracuseStep 4690723 = 7036085) B7036085
theorem B6254297 : Blo 2195435 6254297 := bstep (se 2 (by rfl) ⟨2345361, by rfl⟩ : syracuseStep 6254297 = 4690723) B4690723
theorem B4169531 : Blo 2195435 4169531 := bstep (se 1 (by rfl) ⟨3127148, by rfl⟩ : syracuseStep 4169531 = 6254297) B6254297
theorem B2779687 : Blo 2195435 2779687 := bstep (se 1 (by rfl) ⟨2084765, by rfl⟩ : syracuseStep 2779687 = 4169531) B4169531
theorem B3706249 : Blo 2195435 3706249 := bstep (se 2 (by rfl) ⟨1389843, by rfl⟩ : syracuseStep 3706249 = 2779687) B2779687
theorem B4941665 : Blo 2195435 4941665 := bstep (se 2 (by rfl) ⟨1853124, by rfl⟩ : syracuseStep 4941665 = 3706249) B3706249
theorem B3294443 : Blo 2195435 3294443 := bstep (se 1 (by rfl) ⟨2470832, by rfl⟩ : syracuseStep 3294443 = 4941665) B4941665
theorem B2196295 : Blo 2195435 2196295 := bstep (se 1 (by rfl) ⟨1647221, by rfl⟩ : syracuseStep 2196295 = 3294443) B3294443
theorem B2470837 : Blo 2195435 2470837 := bbase (se 5 (by rfl) ⟨115820, by rfl⟩ : syracuseStep 2470837 = 231641) (by norm_num)
theorem B3294449 : Blo 2195435 3294449 := bstep (se 2 (by rfl) ⟨1235418, by rfl⟩ : syracuseStep 3294449 = 2470837) B2470837
theorem B2196299 : Blo 2195435 2196299 := bstep (se 1 (by rfl) ⟨1647224, by rfl⟩ : syracuseStep 2196299 = 3294449) B3294449
theorem B2779697 : Blo 2195435 2779697 := bbase (se 2 (by rfl) ⟨1042386, by rfl⟩ : syracuseStep 2779697 = 2084773) (by norm_num)
theorem B7412525 : Blo 2195435 7412525 := bstep (se 3 (by rfl) ⟨1389848, by rfl⟩ : syracuseStep 7412525 = 2779697) B2779697
theorem B4941683 : Blo 2195435 4941683 := bstep (se 1 (by rfl) ⟨3706262, by rfl⟩ : syracuseStep 4941683 = 7412525) B7412525
theorem B3294455 : Blo 2195435 3294455 := bstep (se 1 (by rfl) ⟨2470841, by rfl⟩ : syracuseStep 3294455 = 4941683) B4941683
theorem B2196303 : Blo 2195435 2196303 := bstep (se 1 (by rfl) ⟨1647227, by rfl⟩ : syracuseStep 2196303 = 3294455) B3294455
theorem B3294461 : Blo 2195435 3294461 := bbase (se 3 (by rfl) ⟨617711, by rfl⟩ : syracuseStep 3294461 = 1235423) (by norm_num)
theorem B2196307 : Blo 2195435 2196307 := bstep (se 1 (by rfl) ⟨1647230, by rfl⟩ : syracuseStep 2196307 = 3294461) B3294461
theorem B4941701 : Blo 2195435 4941701 := bbase (se 4 (by rfl) ⟨463284, by rfl⟩ : syracuseStep 4941701 = 926569) (by norm_num)
theorem B3294467 : Blo 2195435 3294467 := bstep (se 1 (by rfl) ⟨2470850, by rfl⟩ : syracuseStep 3294467 = 4941701) B4941701
theorem B2196311 : Blo 2195435 2196311 := bstep (se 1 (by rfl) ⟨1647233, by rfl⟩ : syracuseStep 2196311 = 3294467) B3294467
theorem B4452565 : Blo 2195435 4452565 := bbase (se 7 (by rfl) ⟨52178, by rfl⟩ : syracuseStep 4452565 = 104357) (by norm_num)
theorem B5936753 : Blo 2195435 5936753 := bstep (se 2 (by rfl) ⟨2226282, by rfl⟩ : syracuseStep 5936753 = 4452565) B4452565
theorem B3957835 : Blo 2195435 3957835 := bstep (se 1 (by rfl) ⟨2968376, by rfl⟩ : syracuseStep 3957835 = 5936753) B5936753
theorem B5277113 : Blo 2195435 5277113 := bstep (se 2 (by rfl) ⟨1978917, by rfl⟩ : syracuseStep 5277113 = 3957835) B3957835
theorem B3518075 : Blo 2195435 3518075 := bstep (se 1 (by rfl) ⟨2638556, by rfl⟩ : syracuseStep 3518075 = 5277113) B5277113
theorem B2345383 : Blo 2195435 2345383 := bstep (se 1 (by rfl) ⟨1759037, by rfl⟩ : syracuseStep 2345383 = 3518075) B3518075
theorem B3127177 : Blo 2195435 3127177 := bstep (se 2 (by rfl) ⟨1172691, by rfl⟩ : syracuseStep 3127177 = 2345383) B2345383
theorem B4169569 : Blo 2195435 4169569 := bstep (se 2 (by rfl) ⟨1563588, by rfl⟩ : syracuseStep 4169569 = 3127177) B3127177
theorem B5559425 : Blo 2195435 5559425 := bstep (se 2 (by rfl) ⟨2084784, by rfl⟩ : syracuseStep 5559425 = 4169569) B4169569
theorem B3706283 : Blo 2195435 3706283 := bstep (se 1 (by rfl) ⟨2779712, by rfl⟩ : syracuseStep 3706283 = 5559425) B5559425
theorem B2470855 : Blo 2195435 2470855 := bstep (se 1 (by rfl) ⟨1853141, by rfl⟩ : syracuseStep 2470855 = 3706283) B3706283
theorem B3294473 : Blo 2195435 3294473 := bstep (se 2 (by rfl) ⟨1235427, by rfl⟩ : syracuseStep 3294473 = 2470855) B2470855
theorem B2196315 : Blo 2195435 2196315 := bstep (se 1 (by rfl) ⟨1647236, by rfl⟩ : syracuseStep 2196315 = 3294473) B3294473
theorem B11118869 : Blo 2195435 11118869 := bbase (se 6 (by rfl) ⟨260598, by rfl⟩ : syracuseStep 11118869 = 521197) (by norm_num)
theorem B7412579 : Blo 2195435 7412579 := bstep (se 1 (by rfl) ⟨5559434, by rfl⟩ : syracuseStep 7412579 = 11118869) B11118869
theorem B4941719 : Blo 2195435 4941719 := bstep (se 1 (by rfl) ⟨3706289, by rfl⟩ : syracuseStep 4941719 = 7412579) B7412579
theorem B3294479 : Blo 2195435 3294479 := bstep (se 1 (by rfl) ⟨2470859, by rfl⟩ : syracuseStep 3294479 = 4941719) B4941719
theorem B2196319 : Blo 2195435 2196319 := bstep (se 1 (by rfl) ⟨1647239, by rfl⟩ : syracuseStep 2196319 = 3294479) B3294479
theorem B3294485 : Blo 2195435 3294485 := bbase (se 6 (by rfl) ⟨77214, by rfl⟩ : syracuseStep 3294485 = 154429) (by norm_num)
theorem B2196323 : Blo 2195435 2196323 := bstep (se 1 (by rfl) ⟨1647242, by rfl⟩ : syracuseStep 2196323 = 3294485) B3294485
theorem B10698277 : Blo 2195435 10698277 := bbase (se 4 (by rfl) ⟨1002963, by rfl⟩ : syracuseStep 10698277 = 2005927) (by norm_num)
theorem B14264369 : Blo 2195435 14264369 := bstep (se 2 (by rfl) ⟨5349138, by rfl⟩ : syracuseStep 14264369 = 10698277) B10698277
theorem B9509579 : Blo 2195435 9509579 := bstep (se 1 (by rfl) ⟨7132184, by rfl⟩ : syracuseStep 9509579 = 14264369) B14264369
theorem B6339719 : Blo 2195435 6339719 := bstep (se 1 (by rfl) ⟨4754789, by rfl⟩ : syracuseStep 6339719 = 9509579) B9509579
theorem B16905917 : Blo 2195435 16905917 := bstep (se 3 (by rfl) ⟨3169859, by rfl⟩ : syracuseStep 16905917 = 6339719) B6339719
theorem B11270611 : Blo 2195435 11270611 := bstep (se 1 (by rfl) ⟨8452958, by rfl⟩ : syracuseStep 11270611 = 16905917) B16905917
theorem B15027481 : Blo 2195435 15027481 := bstep (se 2 (by rfl) ⟨5635305, by rfl⟩ : syracuseStep 15027481 = 11270611) B11270611
theorem B20036641 : Blo 2195435 20036641 := bstep (se 2 (by rfl) ⟨7513740, by rfl⟩ : syracuseStep 20036641 = 15027481) B15027481
theorem B26715521 : Blo 2195435 26715521 := bstep (se 2 (by rfl) ⟨10018320, by rfl⟩ : syracuseStep 26715521 = 20036641) B20036641
theorem B71241389 : Blo 2195435 71241389 := bstep (se 3 (by rfl) ⟨13357760, by rfl⟩ : syracuseStep 71241389 = 26715521) B26715521
theorem B47494259 : Blo 2195435 47494259 := bstep (se 1 (by rfl) ⟨35620694, by rfl⟩ : syracuseStep 47494259 = 71241389) B71241389
theorem B31662839 : Blo 2195435 31662839 := bstep (se 1 (by rfl) ⟨23747129, by rfl⟩ : syracuseStep 31662839 = 47494259) B47494259
theorem B21108559 : Blo 2195435 21108559 := bstep (se 1 (by rfl) ⟨15831419, by rfl⟩ : syracuseStep 21108559 = 31662839) B31662839
theorem B28144745 : Blo 2195435 28144745 := bstep (se 2 (by rfl) ⟨10554279, by rfl⟩ : syracuseStep 28144745 = 21108559) B21108559
theorem B18763163 : Blo 2195435 18763163 := bstep (se 1 (by rfl) ⟨14072372, by rfl⟩ : syracuseStep 18763163 = 28144745) B28144745
theorem B12508775 : Blo 2195435 12508775 := bstep (se 1 (by rfl) ⟨9381581, by rfl⟩ : syracuseStep 12508775 = 18763163) B18763163
theorem B8339183 : Blo 2195435 8339183 := bstep (se 1 (by rfl) ⟨6254387, by rfl⟩ : syracuseStep 8339183 = 12508775) B12508775
theorem B5559455 : Blo 2195435 5559455 := bstep (se 1 (by rfl) ⟨4169591, by rfl⟩ : syracuseStep 5559455 = 8339183) B8339183
theorem B3706303 : Blo 2195435 3706303 := bstep (se 1 (by rfl) ⟨2779727, by rfl⟩ : syracuseStep 3706303 = 5559455) B5559455
theorem B4941737 : Blo 2195435 4941737 := bstep (se 2 (by rfl) ⟨1853151, by rfl⟩ : syracuseStep 4941737 = 3706303) B3706303
theorem B3294491 : Blo 2195435 3294491 := bstep (se 1 (by rfl) ⟨2470868, by rfl⟩ : syracuseStep 3294491 = 4941737) B4941737
theorem B2196327 : Blo 2195435 2196327 := bstep (se 1 (by rfl) ⟨1647245, by rfl⟩ : syracuseStep 2196327 = 3294491) B3294491
theorem B2470873 : Blo 2195435 2470873 := bbase (se 2 (by rfl) ⟨926577, by rfl⟩ : syracuseStep 2470873 = 1853155) (by norm_num)
theorem B3294497 : Blo 2195435 3294497 := bstep (se 2 (by rfl) ⟨1235436, by rfl⟩ : syracuseStep 3294497 = 2470873) B2470873
theorem B2196331 : Blo 2195435 2196331 := bstep (se 1 (by rfl) ⟨1647248, by rfl⟩ : syracuseStep 2196331 = 3294497) B3294497
theorem B3127205 : Blo 2195435 3127205 := bbase (se 4 (by rfl) ⟨293175, by rfl⟩ : syracuseStep 3127205 = 586351) (by norm_num)
theorem B8339213 : Blo 2195435 8339213 := bstep (se 3 (by rfl) ⟨1563602, by rfl⟩ : syracuseStep 8339213 = 3127205) B3127205
theorem B5559475 : Blo 2195435 5559475 := bstep (se 1 (by rfl) ⟨4169606, by rfl⟩ : syracuseStep 5559475 = 8339213) B8339213
theorem B7412633 : Blo 2195435 7412633 := bstep (se 2 (by rfl) ⟨2779737, by rfl⟩ : syracuseStep 7412633 = 5559475) B5559475
theorem B4941755 : Blo 2195435 4941755 := bstep (se 1 (by rfl) ⟨3706316, by rfl⟩ : syracuseStep 4941755 = 7412633) B7412633
theorem B3294503 : Blo 2195435 3294503 := bstep (se 1 (by rfl) ⟨2470877, by rfl⟩ : syracuseStep 3294503 = 4941755) B4941755
theorem B2196335 : Blo 2195435 2196335 := bstep (se 1 (by rfl) ⟨1647251, by rfl⟩ : syracuseStep 2196335 = 3294503) B3294503
theorem B3294509 : Blo 2195435 3294509 := bbase (se 3 (by rfl) ⟨617720, by rfl⟩ : syracuseStep 3294509 = 1235441) (by norm_num)
theorem B2196339 : Blo 2195435 2196339 := bstep (se 1 (by rfl) ⟨1647254, by rfl⟩ : syracuseStep 2196339 = 3294509) B3294509
theorem B4941773 : Blo 2195435 4941773 := bbase (se 3 (by rfl) ⟨926582, by rfl⟩ : syracuseStep 4941773 = 1853165) (by norm_num)
theorem B3294515 : Blo 2195435 3294515 := bstep (se 1 (by rfl) ⟨2470886, by rfl⟩ : syracuseStep 3294515 = 4941773) B4941773
theorem B2196343 : Blo 2195435 2196343 := bstep (se 1 (by rfl) ⟨1647257, by rfl⟩ : syracuseStep 2196343 = 3294515) B3294515
theorem B2779753 : Blo 2195435 2779753 := bbase (se 2 (by rfl) ⟨1042407, by rfl⟩ : syracuseStep 2779753 = 2084815) (by norm_num)
theorem B3706337 : Blo 2195435 3706337 := bstep (se 2 (by rfl) ⟨1389876, by rfl⟩ : syracuseStep 3706337 = 2779753) B2779753
theorem B2470891 : Blo 2195435 2470891 := bstep (se 1 (by rfl) ⟨1853168, by rfl⟩ : syracuseStep 2470891 = 3706337) B3706337
theorem B3294521 : Blo 2195435 3294521 := bstep (se 2 (by rfl) ⟨1235445, by rfl⟩ : syracuseStep 3294521 = 2470891) B2470891
theorem B2196347 : Blo 2195435 2196347 := bstep (se 1 (by rfl) ⟨1647260, by rfl⟩ : syracuseStep 2196347 = 3294521) B3294521
theorem B5277197 : Blo 2195435 5277197 := bbase (se 3 (by rfl) ⟨989474, by rfl⟩ : syracuseStep 5277197 = 1978949) (by norm_num)
theorem B14072525 : Blo 2195435 14072525 := bstep (se 3 (by rfl) ⟨2638598, by rfl⟩ : syracuseStep 14072525 = 5277197) B5277197
theorem B9381683 : Blo 2195435 9381683 := bstep (se 1 (by rfl) ⟨7036262, by rfl⟩ : syracuseStep 9381683 = 14072525) B14072525
theorem B25017821 : Blo 2195435 25017821 := bstep (se 3 (by rfl) ⟨4690841, by rfl⟩ : syracuseStep 25017821 = 9381683) B9381683
theorem B16678547 : Blo 2195435 16678547 := bstep (se 1 (by rfl) ⟨12508910, by rfl⟩ : syracuseStep 16678547 = 25017821) B25017821
theorem B11119031 : Blo 2195435 11119031 := bstep (se 1 (by rfl) ⟨8339273, by rfl⟩ : syracuseStep 11119031 = 16678547) B16678547
theorem B7412687 : Blo 2195435 7412687 := bstep (se 1 (by rfl) ⟨5559515, by rfl⟩ : syracuseStep 7412687 = 11119031) B11119031
theorem B4941791 : Blo 2195435 4941791 := bstep (se 1 (by rfl) ⟨3706343, by rfl⟩ : syracuseStep 4941791 = 7412687) B7412687
theorem B3294527 : Blo 2195435 3294527 := bstep (se 1 (by rfl) ⟨2470895, by rfl⟩ : syracuseStep 3294527 = 4941791) B4941791
theorem B2196351 : Blo 2195435 2196351 := bstep (se 1 (by rfl) ⟨1647263, by rfl⟩ : syracuseStep 2196351 = 3294527) B3294527
theorem B3294533 : Blo 2195435 3294533 := bbase (se 4 (by rfl) ⟨308862, by rfl⟩ : syracuseStep 3294533 = 617725) (by norm_num)
theorem B2196355 : Blo 2195435 2196355 := bstep (se 1 (by rfl) ⟨1647266, by rfl⟩ : syracuseStep 2196355 = 3294533) B3294533
theorem B3706357 : Blo 2195435 3706357 := bbase (se 5 (by rfl) ⟨173735, by rfl⟩ : syracuseStep 3706357 = 347471) (by norm_num)
theorem B4941809 : Blo 2195435 4941809 := bstep (se 2 (by rfl) ⟨1853178, by rfl⟩ : syracuseStep 4941809 = 3706357) B3706357
theorem B3294539 : Blo 2195435 3294539 := bstep (se 1 (by rfl) ⟨2470904, by rfl⟩ : syracuseStep 3294539 = 4941809) B4941809
theorem B2196359 : Blo 2195435 2196359 := bstep (se 1 (by rfl) ⟨1647269, by rfl⟩ : syracuseStep 2196359 = 3294539) B3294539
theorem B2470909 : Blo 2195435 2470909 := bbase (se 3 (by rfl) ⟨463295, by rfl⟩ : syracuseStep 2470909 = 926591) (by norm_num)
theorem B3294545 : Blo 2195435 3294545 := bstep (se 2 (by rfl) ⟨1235454, by rfl⟩ : syracuseStep 3294545 = 2470909) B2470909
theorem B2196363 : Blo 2195435 2196363 := bstep (se 1 (by rfl) ⟨1647272, by rfl⟩ : syracuseStep 2196363 = 3294545) B3294545
theorem B7412741 : Blo 2195435 7412741 := bbase (se 4 (by rfl) ⟨694944, by rfl⟩ : syracuseStep 7412741 = 1389889) (by norm_num)
theorem B4941827 : Blo 2195435 4941827 := bstep (se 1 (by rfl) ⟨3706370, by rfl⟩ : syracuseStep 4941827 = 7412741) B7412741
theorem B3294551 : Blo 2195435 3294551 := bstep (se 1 (by rfl) ⟨2470913, by rfl⟩ : syracuseStep 3294551 = 4941827) B4941827
theorem B2196367 : Blo 2195435 2196367 := bstep (se 1 (by rfl) ⟨1647275, by rfl⟩ : syracuseStep 2196367 = 3294551) B3294551
theorem B3294557 : Blo 2195435 3294557 := bbase (se 3 (by rfl) ⟨617729, by rfl⟩ : syracuseStep 3294557 = 1235459) (by norm_num)
theorem B2196371 : Blo 2195435 2196371 := bstep (se 1 (by rfl) ⟨1647278, by rfl⟩ : syracuseStep 2196371 = 3294557) B3294557
theorem B4941845 : Blo 2195435 4941845 := bbase (se 6 (by rfl) ⟨115824, by rfl⟩ : syracuseStep 4941845 = 231649) (by norm_num)
theorem B3294563 : Blo 2195435 3294563 := bstep (se 1 (by rfl) ⟨2470922, by rfl⟩ : syracuseStep 3294563 = 4941845) B4941845
theorem B2196375 : Blo 2195435 2196375 := bstep (se 1 (by rfl) ⟨1647281, by rfl⟩ : syracuseStep 2196375 = 3294563) B3294563
theorem B8339381 : Blo 2195435 8339381 := bbase (se 5 (by rfl) ⟨390908, by rfl⟩ : syracuseStep 8339381 = 781817) (by norm_num)
theorem B5559587 : Blo 2195435 5559587 := bstep (se 1 (by rfl) ⟨4169690, by rfl⟩ : syracuseStep 5559587 = 8339381) B8339381
theorem B3706391 : Blo 2195435 3706391 := bstep (se 1 (by rfl) ⟨2779793, by rfl⟩ : syracuseStep 3706391 = 5559587) B5559587
theorem B2470927 : Blo 2195435 2470927 := bstep (se 1 (by rfl) ⟨1853195, by rfl⟩ : syracuseStep 2470927 = 3706391) B3706391
theorem B3294569 : Blo 2195435 3294569 := bstep (se 2 (by rfl) ⟨1235463, by rfl⟩ : syracuseStep 3294569 = 2470927) B2470927
theorem B2196379 : Blo 2195435 2196379 := bstep (se 1 (by rfl) ⟨1647284, by rfl⟩ : syracuseStep 2196379 = 3294569) B3294569
theorem B5349277 : Blo 2195435 5349277 := bbase (se 3 (by rfl) ⟨1002989, by rfl⟩ : syracuseStep 5349277 = 2005979) (by norm_num)
theorem B7132369 : Blo 2195435 7132369 := bstep (se 2 (by rfl) ⟨2674638, by rfl⟩ : syracuseStep 7132369 = 5349277) B5349277
theorem B9509825 : Blo 2195435 9509825 := bstep (se 2 (by rfl) ⟨3566184, by rfl⟩ : syracuseStep 9509825 = 7132369) B7132369
theorem B6339883 : Blo 2195435 6339883 := bstep (se 1 (by rfl) ⟨4754912, by rfl⟩ : syracuseStep 6339883 = 9509825) B9509825
theorem B8453177 : Blo 2195435 8453177 := bstep (se 2 (by rfl) ⟨3169941, by rfl⟩ : syracuseStep 8453177 = 6339883) B6339883
theorem B5635451 : Blo 2195435 5635451 := bstep (se 1 (by rfl) ⟨4226588, by rfl⟩ : syracuseStep 5635451 = 8453177) B8453177
theorem B15027869 : Blo 2195435 15027869 := bstep (se 3 (by rfl) ⟨2817725, by rfl⟩ : syracuseStep 15027869 = 5635451) B5635451
theorem B10018579 : Blo 2195435 10018579 := bstep (se 1 (by rfl) ⟨7513934, by rfl⟩ : syracuseStep 10018579 = 15027869) B15027869
theorem B13358105 : Blo 2195435 13358105 := bstep (se 2 (by rfl) ⟨5009289, by rfl⟩ : syracuseStep 13358105 = 10018579) B10018579
theorem B8905403 : Blo 2195435 8905403 := bstep (se 1 (by rfl) ⟨6679052, by rfl⟩ : syracuseStep 8905403 = 13358105) B13358105
theorem B5936935 : Blo 2195435 5936935 := bstep (se 1 (by rfl) ⟨4452701, by rfl⟩ : syracuseStep 5936935 = 8905403) B8905403
theorem B7915913 : Blo 2195435 7915913 := bstep (se 2 (by rfl) ⟨2968467, by rfl⟩ : syracuseStep 7915913 = 5936935) B5936935
theorem B5277275 : Blo 2195435 5277275 := bstep (se 1 (by rfl) ⟨3957956, by rfl⟩ : syracuseStep 5277275 = 7915913) B7915913
theorem B3518183 : Blo 2195435 3518183 := bstep (se 1 (by rfl) ⟨2638637, by rfl⟩ : syracuseStep 3518183 = 5277275) B5277275
theorem B2345455 : Blo 2195435 2345455 := bstep (se 1 (by rfl) ⟨1759091, by rfl⟩ : syracuseStep 2345455 = 3518183) B3518183
theorem B12509093 : Blo 2195435 12509093 := bstep (se 4 (by rfl) ⟨1172727, by rfl⟩ : syracuseStep 12509093 = 2345455) B2345455
theorem B8339395 : Blo 2195435 8339395 := bstep (se 1 (by rfl) ⟨6254546, by rfl⟩ : syracuseStep 8339395 = 12509093) B12509093
theorem B11119193 : Blo 2195435 11119193 := bstep (se 2 (by rfl) ⟨4169697, by rfl⟩ : syracuseStep 11119193 = 8339395) B8339395
theorem B7412795 : Blo 2195435 7412795 := bstep (se 1 (by rfl) ⟨5559596, by rfl⟩ : syracuseStep 7412795 = 11119193) B11119193
theorem B4941863 : Blo 2195435 4941863 := bstep (se 1 (by rfl) ⟨3706397, by rfl⟩ : syracuseStep 4941863 = 7412795) B7412795
theorem B3294575 : Blo 2195435 3294575 := bstep (se 1 (by rfl) ⟨2470931, by rfl⟩ : syracuseStep 3294575 = 4941863) B4941863
theorem B2196383 : Blo 2195435 2196383 := bstep (se 1 (by rfl) ⟨1647287, by rfl⟩ : syracuseStep 2196383 = 3294575) B3294575
theorem B3294581 : Blo 2195435 3294581 := bbase (se 5 (by rfl) ⟨154433, by rfl⟩ : syracuseStep 3294581 = 308867) (by norm_num)
theorem B2196387 : Blo 2195435 2196387 := bstep (se 1 (by rfl) ⟨1647290, by rfl⟩ : syracuseStep 2196387 = 3294581) B3294581
theorem B3127285 : Blo 2195435 3127285 := bbase (se 5 (by rfl) ⟨146591, by rfl⟩ : syracuseStep 3127285 = 293183) (by norm_num)
theorem B4169713 : Blo 2195435 4169713 := bstep (se 2 (by rfl) ⟨1563642, by rfl⟩ : syracuseStep 4169713 = 3127285) B3127285
theorem B5559617 : Blo 2195435 5559617 := bstep (se 2 (by rfl) ⟨2084856, by rfl⟩ : syracuseStep 5559617 = 4169713) B4169713
theorem B3706411 : Blo 2195435 3706411 := bstep (se 1 (by rfl) ⟨2779808, by rfl⟩ : syracuseStep 3706411 = 5559617) B5559617
theorem B4941881 : Blo 2195435 4941881 := bstep (se 2 (by rfl) ⟨1853205, by rfl⟩ : syracuseStep 4941881 = 3706411) B3706411
theorem B3294587 : Blo 2195435 3294587 := bstep (se 1 (by rfl) ⟨2470940, by rfl⟩ : syracuseStep 3294587 = 4941881) B4941881
theorem B2196391 : Blo 2195435 2196391 := bstep (se 1 (by rfl) ⟨1647293, by rfl⟩ : syracuseStep 2196391 = 3294587) B3294587
theorem B2470945 : Blo 2195435 2470945 := bbase (se 2 (by rfl) ⟨926604, by rfl⟩ : syracuseStep 2470945 = 1853209) (by norm_num)
theorem B3294593 : Blo 2195435 3294593 := bstep (se 2 (by rfl) ⟨1235472, by rfl⟩ : syracuseStep 3294593 = 2470945) B2470945
theorem B2196395 : Blo 2195435 2196395 := bstep (se 1 (by rfl) ⟨1647296, by rfl⟩ : syracuseStep 2196395 = 3294593) B3294593
theorem B5559637 : Blo 2195435 5559637 := bbase (se 15 (by rfl) ⟨254, by rfl⟩ : syracuseStep 5559637 = 509) (by norm_num)
theorem B7412849 : Blo 2195435 7412849 := bstep (se 2 (by rfl) ⟨2779818, by rfl⟩ : syracuseStep 7412849 = 5559637) B5559637
theorem B4941899 : Blo 2195435 4941899 := bstep (se 1 (by rfl) ⟨3706424, by rfl⟩ : syracuseStep 4941899 = 7412849) B7412849
theorem B3294599 : Blo 2195435 3294599 := bstep (se 1 (by rfl) ⟨2470949, by rfl⟩ : syracuseStep 3294599 = 4941899) B4941899
theorem B2196399 : Blo 2195435 2196399 := bstep (se 1 (by rfl) ⟨1647299, by rfl⟩ : syracuseStep 2196399 = 3294599) B3294599
theorem B3294605 : Blo 2195435 3294605 := bbase (se 3 (by rfl) ⟨617738, by rfl⟩ : syracuseStep 3294605 = 1235477) (by norm_num)
theorem B2196403 : Blo 2195435 2196403 := bstep (se 1 (by rfl) ⟨1647302, by rfl⟩ : syracuseStep 2196403 = 3294605) B3294605
theorem B4941917 : Blo 2195435 4941917 := bbase (se 3 (by rfl) ⟨926609, by rfl⟩ : syracuseStep 4941917 = 1853219) (by norm_num)
theorem B3294611 : Blo 2195435 3294611 := bstep (se 1 (by rfl) ⟨2470958, by rfl⟩ : syracuseStep 3294611 = 4941917) B4941917
theorem B2196407 : Blo 2195435 2196407 := bstep (se 1 (by rfl) ⟨1647305, by rfl⟩ : syracuseStep 2196407 = 3294611) B3294611
theorem B3706445 : Blo 2195435 3706445 := bbase (se 3 (by rfl) ⟨694958, by rfl⟩ : syracuseStep 3706445 = 1389917) (by norm_num)
theorem B2470963 : Blo 2195435 2470963 := bstep (se 1 (by rfl) ⟨1853222, by rfl⟩ : syracuseStep 2470963 = 3706445) B3706445
theorem B3294617 : Blo 2195435 3294617 := bstep (se 2 (by rfl) ⟨1235481, by rfl⟩ : syracuseStep 3294617 = 2470963) B2470963
theorem B2196411 : Blo 2195435 2196411 := bstep (se 1 (by rfl) ⟨1647308, by rfl⟩ : syracuseStep 2196411 = 3294617) B3294617
theorem B8568629 : Blo 2195435 8568629 := bbase (se 5 (by rfl) ⟨401654, by rfl⟩ : syracuseStep 8568629 = 803309) (by norm_num)
theorem B5712419 : Blo 2195435 5712419 := bstep (se 1 (by rfl) ⟨4284314, by rfl⟩ : syracuseStep 5712419 = 8568629) B8568629
theorem B3808279 : Blo 2195435 3808279 := bstep (se 1 (by rfl) ⟨2856209, by rfl⟩ : syracuseStep 3808279 = 5712419) B5712419
theorem B20310821 : Blo 2195435 20310821 := bstep (se 4 (by rfl) ⟨1904139, by rfl⟩ : syracuseStep 20310821 = 3808279) B3808279
theorem B13540547 : Blo 2195435 13540547 := bstep (se 1 (by rfl) ⟨10155410, by rfl⟩ : syracuseStep 13540547 = 20310821) B20310821
theorem B36108125 : Blo 2195435 36108125 := bstep (se 3 (by rfl) ⟨6770273, by rfl⟩ : syracuseStep 36108125 = 13540547) B13540547
theorem B24072083 : Blo 2195435 24072083 := bstep (se 1 (by rfl) ⟨18054062, by rfl⟩ : syracuseStep 24072083 = 36108125) B36108125
theorem B16048055 : Blo 2195435 16048055 := bstep (se 1 (by rfl) ⟨12036041, by rfl⟩ : syracuseStep 16048055 = 24072083) B24072083
theorem B10698703 : Blo 2195435 10698703 := bstep (se 1 (by rfl) ⟨8024027, by rfl⟩ : syracuseStep 10698703 = 16048055) B16048055
theorem B57059749 : Blo 2195435 57059749 := bstep (se 4 (by rfl) ⟨5349351, by rfl⟩ : syracuseStep 57059749 = 10698703) B10698703
theorem B76079665 : Blo 2195435 76079665 := bstep (se 2 (by rfl) ⟨28529874, by rfl⟩ : syracuseStep 76079665 = 57059749) B57059749
theorem B101439553 : Blo 2195435 101439553 := bstep (se 2 (by rfl) ⟨38039832, by rfl⟩ : syracuseStep 101439553 = 76079665) B76079665
theorem B135252737 : Blo 2195435 135252737 := bstep (se 2 (by rfl) ⟨50719776, by rfl⟩ : syracuseStep 135252737 = 101439553) B101439553
theorem B90168491 : Blo 2195435 90168491 := bstep (se 1 (by rfl) ⟨67626368, by rfl⟩ : syracuseStep 90168491 = 135252737) B135252737
theorem B60112327 : Blo 2195435 60112327 := bstep (se 1 (by rfl) ⟨45084245, by rfl⟩ : syracuseStep 60112327 = 90168491) B90168491
theorem B80149769 : Blo 2195435 80149769 := bstep (se 2 (by rfl) ⟨30056163, by rfl⟩ : syracuseStep 80149769 = 60112327) B60112327
theorem B53433179 : Blo 2195435 53433179 := bstep (se 1 (by rfl) ⟨40074884, by rfl⟩ : syracuseStep 53433179 = 80149769) B80149769
theorem B35622119 : Blo 2195435 35622119 := bstep (se 1 (by rfl) ⟨26716589, by rfl⟩ : syracuseStep 35622119 = 53433179) B53433179
theorem B23748079 : Blo 2195435 23748079 := bstep (se 1 (by rfl) ⟨17811059, by rfl⟩ : syracuseStep 23748079 = 35622119) B35622119
theorem B31664105 : Blo 2195435 31664105 := bstep (se 2 (by rfl) ⟨11874039, by rfl⟩ : syracuseStep 31664105 = 23748079) B23748079
theorem B21109403 : Blo 2195435 21109403 := bstep (se 1 (by rfl) ⟨15832052, by rfl⟩ : syracuseStep 21109403 = 31664105) B31664105
theorem B14072935 : Blo 2195435 14072935 := bstep (se 1 (by rfl) ⟨10554701, by rfl⟩ : syracuseStep 14072935 = 21109403) B21109403
theorem B18763913 : Blo 2195435 18763913 := bstep (se 2 (by rfl) ⟨7036467, by rfl⟩ : syracuseStep 18763913 = 14072935) B14072935
theorem B12509275 : Blo 2195435 12509275 := bstep (se 1 (by rfl) ⟨9381956, by rfl⟩ : syracuseStep 12509275 = 18763913) B18763913
theorem B16679033 : Blo 2195435 16679033 := bstep (se 2 (by rfl) ⟨6254637, by rfl⟩ : syracuseStep 16679033 = 12509275) B12509275
theorem B11119355 : Blo 2195435 11119355 := bstep (se 1 (by rfl) ⟨8339516, by rfl⟩ : syracuseStep 11119355 = 16679033) B16679033
theorem B7412903 : Blo 2195435 7412903 := bstep (se 1 (by rfl) ⟨5559677, by rfl⟩ : syracuseStep 7412903 = 11119355) B11119355
theorem B4941935 : Blo 2195435 4941935 := bstep (se 1 (by rfl) ⟨3706451, by rfl⟩ : syracuseStep 4941935 = 7412903) B7412903
theorem B3294623 : Blo 2195435 3294623 := bstep (se 1 (by rfl) ⟨2470967, by rfl⟩ : syracuseStep 3294623 = 4941935) B4941935
theorem B2196415 : Blo 2195435 2196415 := bstep (se 1 (by rfl) ⟨1647311, by rfl⟩ : syracuseStep 2196415 = 3294623) B3294623
theorem B3294629 : Blo 2195435 3294629 := bbase (se 4 (by rfl) ⟨308871, by rfl⟩ : syracuseStep 3294629 = 617743) (by norm_num)
theorem B2196419 : Blo 2195435 2196419 := bstep (se 1 (by rfl) ⟨1647314, by rfl⟩ : syracuseStep 2196419 = 3294629) B3294629
theorem B2779849 : Blo 2195435 2779849 := bbase (se 2 (by rfl) ⟨1042443, by rfl⟩ : syracuseStep 2779849 = 2084887) (by norm_num)
theorem B3706465 : Blo 2195435 3706465 := bstep (se 2 (by rfl) ⟨1389924, by rfl⟩ : syracuseStep 3706465 = 2779849) B2779849
theorem B4941953 : Blo 2195435 4941953 := bstep (se 2 (by rfl) ⟨1853232, by rfl⟩ : syracuseStep 4941953 = 3706465) B3706465
theorem B3294635 : Blo 2195435 3294635 := bstep (se 1 (by rfl) ⟨2470976, by rfl⟩ : syracuseStep 3294635 = 4941953) B4941953
theorem B2196423 : Blo 2195435 2196423 := bstep (se 1 (by rfl) ⟨1647317, by rfl⟩ : syracuseStep 2196423 = 3294635) B3294635
theorem B2470981 : Blo 2195435 2470981 := bbase (se 4 (by rfl) ⟨231654, by rfl⟩ : syracuseStep 2470981 = 463309) (by norm_num)
theorem B3294641 : Blo 2195435 3294641 := bstep (se 2 (by rfl) ⟨1235490, by rfl⟩ : syracuseStep 3294641 = 2470981) B2470981
theorem B2196427 : Blo 2195435 2196427 := bstep (se 1 (by rfl) ⟨1647320, by rfl⟩ : syracuseStep 2196427 = 3294641) B3294641
theorem B4169789 : Blo 2195435 4169789 := bbase (se 3 (by rfl) ⟨781835, by rfl⟩ : syracuseStep 4169789 = 1563671) (by norm_num)
theorem B2779859 : Blo 2195435 2779859 := bstep (se 1 (by rfl) ⟨2084894, by rfl⟩ : syracuseStep 2779859 = 4169789) B4169789
theorem B7412957 : Blo 2195435 7412957 := bstep (se 3 (by rfl) ⟨1389929, by rfl⟩ : syracuseStep 7412957 = 2779859) B2779859
theorem B4941971 : Blo 2195435 4941971 := bstep (se 1 (by rfl) ⟨3706478, by rfl⟩ : syracuseStep 4941971 = 7412957) B7412957
theorem B3294647 : Blo 2195435 3294647 := bstep (se 1 (by rfl) ⟨2470985, by rfl⟩ : syracuseStep 3294647 = 4941971) B4941971
theorem B2196431 : Blo 2195435 2196431 := bstep (se 1 (by rfl) ⟨1647323, by rfl⟩ : syracuseStep 2196431 = 3294647) B3294647
theorem B3294653 : Blo 2195435 3294653 := bbase (se 3 (by rfl) ⟨617747, by rfl⟩ : syracuseStep 3294653 = 1235495) (by norm_num)
theorem B2196435 : Blo 2195435 2196435 := bstep (se 1 (by rfl) ⟨1647326, by rfl⟩ : syracuseStep 2196435 = 3294653) B3294653
theorem B4941989 : Blo 2195435 4941989 := bbase (se 4 (by rfl) ⟨463311, by rfl⟩ : syracuseStep 4941989 = 926623) (by norm_num)
theorem B3294659 : Blo 2195435 3294659 := bstep (se 1 (by rfl) ⟨2470994, by rfl⟩ : syracuseStep 3294659 = 4941989) B4941989
theorem B2196439 : Blo 2195435 2196439 := bstep (se 1 (by rfl) ⟨1647329, by rfl⟩ : syracuseStep 2196439 = 3294659) B3294659
theorem B5559749 : Blo 2195435 5559749 := bbase (se 4 (by rfl) ⟨521226, by rfl⟩ : syracuseStep 5559749 = 1042453) (by norm_num)
theorem B3706499 : Blo 2195435 3706499 := bstep (se 1 (by rfl) ⟨2779874, by rfl⟩ : syracuseStep 3706499 = 5559749) B5559749
theorem B2470999 : Blo 2195435 2470999 := bstep (se 1 (by rfl) ⟨1853249, by rfl⟩ : syracuseStep 2470999 = 3706499) B3706499
theorem B3294665 : Blo 2195435 3294665 := bstep (se 2 (by rfl) ⟨1235499, by rfl⟩ : syracuseStep 3294665 = 2470999) B2470999
theorem B2196443 : Blo 2195435 2196443 := bstep (se 1 (by rfl) ⟨1647332, by rfl⟩ : syracuseStep 2196443 = 3294665) B3294665
theorem B5077781 : Blo 2195435 5077781 := bbase (se 6 (by rfl) ⟨119010, by rfl⟩ : syracuseStep 5077781 = 238021) (by norm_num)
theorem B3385187 : Blo 2195435 3385187 := bstep (se 1 (by rfl) ⟨2538890, by rfl⟩ : syracuseStep 3385187 = 5077781) B5077781
theorem B36108661 : Blo 2195435 36108661 := bstep (se 5 (by rfl) ⟨1692593, by rfl⟩ : syracuseStep 36108661 = 3385187) B3385187
theorem B48144881 : Blo 2195435 48144881 := bstep (se 2 (by rfl) ⟨18054330, by rfl⟩ : syracuseStep 48144881 = 36108661) B36108661
theorem B32096587 : Blo 2195435 32096587 := bstep (se 1 (by rfl) ⟨24072440, by rfl⟩ : syracuseStep 32096587 = 48144881) B48144881
theorem B42795449 : Blo 2195435 42795449 := bstep (se 2 (by rfl) ⟨16048293, by rfl⟩ : syracuseStep 42795449 = 32096587) B32096587
theorem B28530299 : Blo 2195435 28530299 := bstep (se 1 (by rfl) ⟨21397724, by rfl⟩ : syracuseStep 28530299 = 42795449) B42795449
theorem B19020199 : Blo 2195435 19020199 := bstep (se 1 (by rfl) ⟨14265149, by rfl⟩ : syracuseStep 19020199 = 28530299) B28530299
theorem B25360265 : Blo 2195435 25360265 := bstep (se 2 (by rfl) ⟨9510099, by rfl⟩ : syracuseStep 25360265 = 19020199) B19020199
theorem B16906843 : Blo 2195435 16906843 := bstep (se 1 (by rfl) ⟨12680132, by rfl⟩ : syracuseStep 16906843 = 25360265) B25360265
theorem B22542457 : Blo 2195435 22542457 := bstep (se 2 (by rfl) ⟨8453421, by rfl⟩ : syracuseStep 22542457 = 16906843) B16906843
theorem B30056609 : Blo 2195435 30056609 := bstep (se 2 (by rfl) ⟨11271228, by rfl⟩ : syracuseStep 30056609 = 22542457) B22542457
theorem B20037739 : Blo 2195435 20037739 := bstep (se 1 (by rfl) ⟨15028304, by rfl⟩ : syracuseStep 20037739 = 30056609) B30056609
theorem B26716985 : Blo 2195435 26716985 := bstep (se 2 (by rfl) ⟨10018869, by rfl⟩ : syracuseStep 26716985 = 20037739) B20037739
theorem B17811323 : Blo 2195435 17811323 := bstep (se 1 (by rfl) ⟨13358492, by rfl⟩ : syracuseStep 17811323 = 26716985) B26716985
theorem B11874215 : Blo 2195435 11874215 := bstep (se 1 (by rfl) ⟨8905661, by rfl⟩ : syracuseStep 11874215 = 17811323) B17811323
theorem B7916143 : Blo 2195435 7916143 := bstep (se 1 (by rfl) ⟨5937107, by rfl⟩ : syracuseStep 7916143 = 11874215) B11874215
theorem B10554857 : Blo 2195435 10554857 := bstep (se 2 (by rfl) ⟨3958071, by rfl⟩ : syracuseStep 10554857 = 7916143) B7916143
theorem B7036571 : Blo 2195435 7036571 := bstep (se 1 (by rfl) ⟨5277428, by rfl⟩ : syracuseStep 7036571 = 10554857) B10554857
theorem B4691047 : Blo 2195435 4691047 := bstep (se 1 (by rfl) ⟨3518285, by rfl⟩ : syracuseStep 4691047 = 7036571) B7036571
theorem B6254729 : Blo 2195435 6254729 := bstep (se 2 (by rfl) ⟨2345523, by rfl⟩ : syracuseStep 6254729 = 4691047) B4691047
theorem B4169819 : Blo 2195435 4169819 := bstep (se 1 (by rfl) ⟨3127364, by rfl⟩ : syracuseStep 4169819 = 6254729) B6254729
theorem B11119517 : Blo 2195435 11119517 := bstep (se 3 (by rfl) ⟨2084909, by rfl⟩ : syracuseStep 11119517 = 4169819) B4169819
theorem B7413011 : Blo 2195435 7413011 := bstep (se 1 (by rfl) ⟨5559758, by rfl⟩ : syracuseStep 7413011 = 11119517) B11119517
theorem B4942007 : Blo 2195435 4942007 := bstep (se 1 (by rfl) ⟨3706505, by rfl⟩ : syracuseStep 4942007 = 7413011) B7413011
theorem B3294671 : Blo 2195435 3294671 := bstep (se 1 (by rfl) ⟨2471003, by rfl⟩ : syracuseStep 3294671 = 4942007) B4942007
theorem B2196447 : Blo 2195435 2196447 := bstep (se 1 (by rfl) ⟨1647335, by rfl⟩ : syracuseStep 2196447 = 3294671) B3294671
theorem B3294677 : Blo 2195435 3294677 := bbase (se 7 (by rfl) ⟨38609, by rfl⟩ : syracuseStep 3294677 = 77219) (by norm_num)
theorem B2196451 : Blo 2195435 2196451 := bstep (se 1 (by rfl) ⟨1647338, by rfl⟩ : syracuseStep 2196451 = 3294677) B3294677
theorem B8339669 : Blo 2195435 8339669 := bbase (se 7 (by rfl) ⟨97730, by rfl⟩ : syracuseStep 8339669 = 195461) (by norm_num)
theorem B5559779 : Blo 2195435 5559779 := bstep (se 1 (by rfl) ⟨4169834, by rfl⟩ : syracuseStep 5559779 = 8339669) B8339669
theorem B3706519 : Blo 2195435 3706519 := bstep (se 1 (by rfl) ⟨2779889, by rfl⟩ : syracuseStep 3706519 = 5559779) B5559779
theorem B4942025 : Blo 2195435 4942025 := bstep (se 2 (by rfl) ⟨1853259, by rfl⟩ : syracuseStep 4942025 = 3706519) B3706519
theorem B3294683 : Blo 2195435 3294683 := bstep (se 1 (by rfl) ⟨2471012, by rfl⟩ : syracuseStep 3294683 = 4942025) B4942025
theorem B2196455 : Blo 2195435 2196455 := bstep (se 1 (by rfl) ⟨1647341, by rfl⟩ : syracuseStep 2196455 = 3294683) B3294683
theorem B2471017 : Blo 2195435 2471017 := bbase (se 2 (by rfl) ⟨926631, by rfl⟩ : syracuseStep 2471017 = 1853263) (by norm_num)
theorem B3294689 : Blo 2195435 3294689 := bstep (se 2 (by rfl) ⟨1235508, by rfl⟩ : syracuseStep 3294689 = 2471017) B2471017
theorem B2196459 : Blo 2195435 2196459 := bstep (se 1 (by rfl) ⟨1647344, by rfl⟩ : syracuseStep 2196459 = 3294689) B3294689
theorem B7720645 : Blo 2195435 7720645 := bbase (se 4 (by rfl) ⟨723810, by rfl⟩ : syracuseStep 7720645 = 1447621) (by norm_num)
theorem B10294193 : Blo 2195435 10294193 := bstep (se 2 (by rfl) ⟨3860322, by rfl⟩ : syracuseStep 10294193 = 7720645) B7720645
theorem B6862795 : Blo 2195435 6862795 := bstep (se 1 (by rfl) ⟨5147096, by rfl⟩ : syracuseStep 6862795 = 10294193) B10294193
theorem B36601573 : Blo 2195435 36601573 := bstep (se 4 (by rfl) ⟨3431397, by rfl⟩ : syracuseStep 36601573 = 6862795) B6862795
theorem B48802097 : Blo 2195435 48802097 := bstep (se 2 (by rfl) ⟨18300786, by rfl⟩ : syracuseStep 48802097 = 36601573) B36601573
theorem B32534731 : Blo 2195435 32534731 := bstep (se 1 (by rfl) ⟨24401048, by rfl⟩ : syracuseStep 32534731 = 48802097) B48802097
theorem B43379641 : Blo 2195435 43379641 := bstep (se 2 (by rfl) ⟨16267365, by rfl⟩ : syracuseStep 43379641 = 32534731) B32534731
theorem B57839521 : Blo 2195435 57839521 := bstep (se 2 (by rfl) ⟨21689820, by rfl⟩ : syracuseStep 57839521 = 43379641) B43379641
theorem B77119361 : Blo 2195435 77119361 := bstep (se 2 (by rfl) ⟨28919760, by rfl⟩ : syracuseStep 77119361 = 57839521) B57839521
theorem B51412907 : Blo 2195435 51412907 := bstep (se 1 (by rfl) ⟨38559680, by rfl⟩ : syracuseStep 51412907 = 77119361) B77119361
theorem B137101085 : Blo 2195435 137101085 := bstep (se 3 (by rfl) ⟨25706453, by rfl⟩ : syracuseStep 137101085 = 51412907) B51412907
theorem B91400723 : Blo 2195435 91400723 := bstep (se 1 (by rfl) ⟨68550542, by rfl⟩ : syracuseStep 91400723 = 137101085) B137101085
theorem B60933815 : Blo 2195435 60933815 := bstep (se 1 (by rfl) ⟨45700361, by rfl⟩ : syracuseStep 60933815 = 91400723) B91400723
theorem B40622543 : Blo 2195435 40622543 := bstep (se 1 (by rfl) ⟨30466907, by rfl⟩ : syracuseStep 40622543 = 60933815) B60933815
theorem B27081695 : Blo 2195435 27081695 := bstep (se 1 (by rfl) ⟨20311271, by rfl⟩ : syracuseStep 27081695 = 40622543) B40622543
theorem B18054463 : Blo 2195435 18054463 := bstep (se 1 (by rfl) ⟨13540847, by rfl⟩ : syracuseStep 18054463 = 27081695) B27081695
theorem B24072617 : Blo 2195435 24072617 := bstep (se 2 (by rfl) ⟨9027231, by rfl⟩ : syracuseStep 24072617 = 18054463) B18054463
theorem B16048411 : Blo 2195435 16048411 := bstep (se 1 (by rfl) ⟨12036308, by rfl⟩ : syracuseStep 16048411 = 24072617) B24072617
theorem B342366101 : Blo 2195435 342366101 := bstep (se 6 (by rfl) ⟨8024205, by rfl⟩ : syracuseStep 342366101 = 16048411) B16048411
theorem B228244067 : Blo 2195435 228244067 := bstep (se 1 (by rfl) ⟨171183050, by rfl⟩ : syracuseStep 228244067 = 342366101) B342366101
theorem B152162711 : Blo 2195435 152162711 := bstep (se 1 (by rfl) ⟨114122033, by rfl⟩ : syracuseStep 152162711 = 228244067) B228244067
theorem B101441807 : Blo 2195435 101441807 := bstep (se 1 (by rfl) ⟨76081355, by rfl⟩ : syracuseStep 101441807 = 152162711) B152162711
theorem B67627871 : Blo 2195435 67627871 := bstep (se 1 (by rfl) ⟨50720903, by rfl⟩ : syracuseStep 67627871 = 101441807) B101441807
theorem B45085247 : Blo 2195435 45085247 := bstep (se 1 (by rfl) ⟨33813935, by rfl⟩ : syracuseStep 45085247 = 67627871) B67627871
theorem B30056831 : Blo 2195435 30056831 := bstep (se 1 (by rfl) ⟨22542623, by rfl⟩ : syracuseStep 30056831 = 45085247) B45085247
theorem B20037887 : Blo 2195435 20037887 := bstep (se 1 (by rfl) ⟨15028415, by rfl⟩ : syracuseStep 20037887 = 30056831) B30056831
theorem B13358591 : Blo 2195435 13358591 := bstep (se 1 (by rfl) ⟨10018943, by rfl⟩ : syracuseStep 13358591 = 20037887) B20037887
theorem B8905727 : Blo 2195435 8905727 := bstep (se 1 (by rfl) ⟨6679295, by rfl⟩ : syracuseStep 8905727 = 13358591) B13358591
theorem B5937151 : Blo 2195435 5937151 := bstep (se 1 (by rfl) ⟨4452863, by rfl⟩ : syracuseStep 5937151 = 8905727) B8905727
theorem B7916201 : Blo 2195435 7916201 := bstep (se 2 (by rfl) ⟨2968575, by rfl⟩ : syracuseStep 7916201 = 5937151) B5937151
theorem B5277467 : Blo 2195435 5277467 := bstep (se 1 (by rfl) ⟨3958100, by rfl⟩ : syracuseStep 5277467 = 7916201) B7916201
theorem B3518311 : Blo 2195435 3518311 := bstep (se 1 (by rfl) ⟨2638733, by rfl⟩ : syracuseStep 3518311 = 5277467) B5277467
theorem B4691081 : Blo 2195435 4691081 := bstep (se 2 (by rfl) ⟨1759155, by rfl⟩ : syracuseStep 4691081 = 3518311) B3518311
theorem B12509549 : Blo 2195435 12509549 := bstep (se 3 (by rfl) ⟨2345540, by rfl⟩ : syracuseStep 12509549 = 4691081) B4691081
theorem B8339699 : Blo 2195435 8339699 := bstep (se 1 (by rfl) ⟨6254774, by rfl⟩ : syracuseStep 8339699 = 12509549) B12509549
theorem B5559799 : Blo 2195435 5559799 := bstep (se 1 (by rfl) ⟨4169849, by rfl⟩ : syracuseStep 5559799 = 8339699) B8339699
theorem B7413065 : Blo 2195435 7413065 := bstep (se 2 (by rfl) ⟨2779899, by rfl⟩ : syracuseStep 7413065 = 5559799) B5559799
theorem B4942043 : Blo 2195435 4942043 := bstep (se 1 (by rfl) ⟨3706532, by rfl⟩ : syracuseStep 4942043 = 7413065) B7413065
theorem B3294695 : Blo 2195435 3294695 := bstep (se 1 (by rfl) ⟨2471021, by rfl⟩ : syracuseStep 3294695 = 4942043) B4942043
theorem B2196463 : Blo 2195435 2196463 := bstep (se 1 (by rfl) ⟨1647347, by rfl⟩ : syracuseStep 2196463 = 3294695) B3294695
theorem B3294701 : Blo 2195435 3294701 := bbase (se 3 (by rfl) ⟨617756, by rfl⟩ : syracuseStep 3294701 = 1235513) (by norm_num)
theorem B2196467 : Blo 2195435 2196467 := bstep (se 1 (by rfl) ⟨1647350, by rfl⟩ : syracuseStep 2196467 = 3294701) B3294701
theorem B4942061 : Blo 2195435 4942061 := bbase (se 3 (by rfl) ⟨926636, by rfl⟩ : syracuseStep 4942061 = 1853273) (by norm_num)
theorem B3294707 : Blo 2195435 3294707 := bstep (se 1 (by rfl) ⟨2471030, by rfl⟩ : syracuseStep 3294707 = 4942061) B4942061
theorem B2196471 : Blo 2195435 2196471 := bstep (se 1 (by rfl) ⟨1647353, by rfl⟩ : syracuseStep 2196471 = 3294707) B3294707
theorem B3127405 : Blo 2195435 3127405 := bbase (se 3 (by rfl) ⟨586388, by rfl⟩ : syracuseStep 3127405 = 1172777) (by norm_num)
theorem B4169873 : Blo 2195435 4169873 := bstep (se 2 (by rfl) ⟨1563702, by rfl⟩ : syracuseStep 4169873 = 3127405) B3127405
theorem B2779915 : Blo 2195435 2779915 := bstep (se 1 (by rfl) ⟨2084936, by rfl⟩ : syracuseStep 2779915 = 4169873) B4169873
theorem B3706553 : Blo 2195435 3706553 := bstep (se 2 (by rfl) ⟨1389957, by rfl⟩ : syracuseStep 3706553 = 2779915) B2779915
theorem B2471035 : Blo 2195435 2471035 := bstep (se 1 (by rfl) ⟨1853276, by rfl⟩ : syracuseStep 2471035 = 3706553) B3706553
theorem B3294713 : Blo 2195435 3294713 := bstep (se 2 (by rfl) ⟨1235517, by rfl⟩ : syracuseStep 3294713 = 2471035) B2471035
theorem B2196475 : Blo 2195435 2196475 := bstep (se 1 (by rfl) ⟨1647356, by rfl⟩ : syracuseStep 2196475 = 3294713) B3294713
theorem B7514261 : Blo 2195435 7514261 := bbase (se 6 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 7514261 = 352231) (by norm_num)
theorem B5009507 : Blo 2195435 5009507 := bstep (se 1 (by rfl) ⟨3757130, by rfl⟩ : syracuseStep 5009507 = 7514261) B7514261
theorem B3339671 : Blo 2195435 3339671 := bstep (se 1 (by rfl) ⟨2504753, by rfl⟩ : syracuseStep 3339671 = 5009507) B5009507
theorem B8905789 : Blo 2195435 8905789 := bstep (se 3 (by rfl) ⟨1669835, by rfl⟩ : syracuseStep 8905789 = 3339671) B3339671
theorem B11874385 : Blo 2195435 11874385 := bstep (se 2 (by rfl) ⟨4452894, by rfl⟩ : syracuseStep 11874385 = 8905789) B8905789
theorem B15832513 : Blo 2195435 15832513 := bstep (se 2 (by rfl) ⟨5937192, by rfl⟩ : syracuseStep 15832513 = 11874385) B11874385
theorem B84440069 : Blo 2195435 84440069 := bstep (se 4 (by rfl) ⟨7916256, by rfl⟩ : syracuseStep 84440069 = 15832513) B15832513
theorem B56293379 : Blo 2195435 56293379 := bstep (se 1 (by rfl) ⟨42220034, by rfl⟩ : syracuseStep 56293379 = 84440069) B84440069
theorem B37528919 : Blo 2195435 37528919 := bstep (se 1 (by rfl) ⟨28146689, by rfl⟩ : syracuseStep 37528919 = 56293379) B56293379
theorem B25019279 : Blo 2195435 25019279 := bstep (se 1 (by rfl) ⟨18764459, by rfl⟩ : syracuseStep 25019279 = 37528919) B37528919
theorem B16679519 : Blo 2195435 16679519 := bstep (se 1 (by rfl) ⟨12509639, by rfl⟩ : syracuseStep 16679519 = 25019279) B25019279
theorem B11119679 : Blo 2195435 11119679 := bstep (se 1 (by rfl) ⟨8339759, by rfl⟩ : syracuseStep 11119679 = 16679519) B16679519
theorem B7413119 : Blo 2195435 7413119 := bstep (se 1 (by rfl) ⟨5559839, by rfl⟩ : syracuseStep 7413119 = 11119679) B11119679
theorem B4942079 : Blo 2195435 4942079 := bstep (se 1 (by rfl) ⟨3706559, by rfl⟩ : syracuseStep 4942079 = 7413119) B7413119
theorem B3294719 : Blo 2195435 3294719 := bstep (se 1 (by rfl) ⟨2471039, by rfl⟩ : syracuseStep 3294719 = 4942079) B4942079
theorem B2196479 : Blo 2195435 2196479 := bstep (se 1 (by rfl) ⟨1647359, by rfl⟩ : syracuseStep 2196479 = 3294719) B3294719
theorem B3294725 : Blo 2195435 3294725 := bbase (se 4 (by rfl) ⟨308880, by rfl⟩ : syracuseStep 3294725 = 617761) (by norm_num)
theorem B2196483 : Blo 2195435 2196483 := bstep (se 1 (by rfl) ⟨1647362, by rfl⟩ : syracuseStep 2196483 = 3294725) B3294725
theorem B3706573 : Blo 2195435 3706573 := bbase (se 3 (by rfl) ⟨694982, by rfl⟩ : syracuseStep 3706573 = 1389965) (by norm_num)
theorem B4942097 : Blo 2195435 4942097 := bstep (se 2 (by rfl) ⟨1853286, by rfl⟩ : syracuseStep 4942097 = 3706573) B3706573
theorem B3294731 : Blo 2195435 3294731 := bstep (se 1 (by rfl) ⟨2471048, by rfl⟩ : syracuseStep 3294731 = 4942097) B4942097
theorem B2196487 : Blo 2195435 2196487 := bstep (se 1 (by rfl) ⟨1647365, by rfl⟩ : syracuseStep 2196487 = 3294731) B3294731
theorem B2471053 : Blo 2195435 2471053 := bbase (se 3 (by rfl) ⟨463322, by rfl⟩ : syracuseStep 2471053 = 926645) (by norm_num)
theorem B3294737 : Blo 2195435 3294737 := bstep (se 2 (by rfl) ⟨1235526, by rfl⟩ : syracuseStep 3294737 = 2471053) B2471053
theorem B2196491 : Blo 2195435 2196491 := bstep (se 1 (by rfl) ⟨1647368, by rfl⟩ : syracuseStep 2196491 = 3294737) B3294737
theorem B7413173 : Blo 2195435 7413173 := bbase (se 5 (by rfl) ⟨347492, by rfl⟩ : syracuseStep 7413173 = 694985) (by norm_num)
theorem B4942115 : Blo 2195435 4942115 := bstep (se 1 (by rfl) ⟨3706586, by rfl⟩ : syracuseStep 4942115 = 7413173) B7413173
theorem B3294743 : Blo 2195435 3294743 := bstep (se 1 (by rfl) ⟨2471057, by rfl⟩ : syracuseStep 3294743 = 4942115) B4942115
theorem B2196495 : Blo 2195435 2196495 := bstep (se 1 (by rfl) ⟨1647371, by rfl⟩ : syracuseStep 2196495 = 3294743) B3294743
theorem B3294749 : Blo 2195435 3294749 := bbase (se 3 (by rfl) ⟨617765, by rfl⟩ : syracuseStep 3294749 = 1235531) (by norm_num)
theorem B2196499 : Blo 2195435 2196499 := bstep (se 1 (by rfl) ⟨1647374, by rfl⟩ : syracuseStep 2196499 = 3294749) B3294749
theorem B4942133 : Blo 2195435 4942133 := bbase (se 5 (by rfl) ⟨231662, by rfl⟩ : syracuseStep 4942133 = 463325) (by norm_num)
theorem B3294755 : Blo 2195435 3294755 := bstep (se 1 (by rfl) ⟨2471066, by rfl⟩ : syracuseStep 3294755 = 4942133) B4942133
theorem B2196503 : Blo 2195435 2196503 := bstep (se 1 (by rfl) ⟨1647377, by rfl⟩ : syracuseStep 2196503 = 3294755) B3294755
theorem B2256853 : Blo 2195435 2256853 := bbase (se 7 (by rfl) ⟨26447, by rfl⟩ : syracuseStep 2256853 = 52895) (by norm_num)
theorem B48146197 : Blo 2195435 48146197 := bstep (se 6 (by rfl) ⟨1128426, by rfl⟩ : syracuseStep 48146197 = 2256853) B2256853
theorem B64194929 : Blo 2195435 64194929 := bstep (se 2 (by rfl) ⟨24073098, by rfl⟩ : syracuseStep 64194929 = 48146197) B48146197
theorem B42796619 : Blo 2195435 42796619 := bstep (se 1 (by rfl) ⟨32097464, by rfl⟩ : syracuseStep 42796619 = 64194929) B64194929
theorem B28531079 : Blo 2195435 28531079 := bstep (se 1 (by rfl) ⟨21398309, by rfl⟩ : syracuseStep 28531079 = 42796619) B42796619
theorem B19020719 : Blo 2195435 19020719 := bstep (se 1 (by rfl) ⟨14265539, by rfl⟩ : syracuseStep 19020719 = 28531079) B28531079
theorem B12680479 : Blo 2195435 12680479 := bstep (se 1 (by rfl) ⟨9510359, by rfl⟩ : syracuseStep 12680479 = 19020719) B19020719
theorem B16907305 : Blo 2195435 16907305 := bstep (se 2 (by rfl) ⟨6340239, by rfl⟩ : syracuseStep 16907305 = 12680479) B12680479
theorem B22543073 : Blo 2195435 22543073 := bstep (se 2 (by rfl) ⟨8453652, by rfl⟩ : syracuseStep 22543073 = 16907305) B16907305
theorem B15028715 : Blo 2195435 15028715 := bstep (se 1 (by rfl) ⟨11271536, by rfl⟩ : syracuseStep 15028715 = 22543073) B22543073
theorem B10019143 : Blo 2195435 10019143 := bstep (se 1 (by rfl) ⟨7514357, by rfl⟩ : syracuseStep 10019143 = 15028715) B15028715
theorem B13358857 : Blo 2195435 13358857 := bstep (se 2 (by rfl) ⟨5009571, by rfl⟩ : syracuseStep 13358857 = 10019143) B10019143
theorem B17811809 : Blo 2195435 17811809 := bstep (se 2 (by rfl) ⟨6679428, by rfl⟩ : syracuseStep 17811809 = 13358857) B13358857
theorem B11874539 : Blo 2195435 11874539 := bstep (se 1 (by rfl) ⟨8905904, by rfl⟩ : syracuseStep 11874539 = 17811809) B17811809
theorem B31665437 : Blo 2195435 31665437 := bstep (se 3 (by rfl) ⟨5937269, by rfl⟩ : syracuseStep 31665437 = 11874539) B11874539
theorem B21110291 : Blo 2195435 21110291 := bstep (se 1 (by rfl) ⟨15832718, by rfl⟩ : syracuseStep 21110291 = 31665437) B31665437
theorem B14073527 : Blo 2195435 14073527 := bstep (se 1 (by rfl) ⟨10555145, by rfl⟩ : syracuseStep 14073527 = 21110291) B21110291
theorem B9382351 : Blo 2195435 9382351 := bstep (se 1 (by rfl) ⟨7036763, by rfl⟩ : syracuseStep 9382351 = 14073527) B14073527
theorem B12509801 : Blo 2195435 12509801 := bstep (se 2 (by rfl) ⟨4691175, by rfl⟩ : syracuseStep 12509801 = 9382351) B9382351
theorem B8339867 : Blo 2195435 8339867 := bstep (se 1 (by rfl) ⟨6254900, by rfl⟩ : syracuseStep 8339867 = 12509801) B12509801
theorem B5559911 : Blo 2195435 5559911 := bstep (se 1 (by rfl) ⟨4169933, by rfl⟩ : syracuseStep 5559911 = 8339867) B8339867
theorem B3706607 : Blo 2195435 3706607 := bstep (se 1 (by rfl) ⟨2779955, by rfl⟩ : syracuseStep 3706607 = 5559911) B5559911
theorem B2471071 : Blo 2195435 2471071 := bstep (se 1 (by rfl) ⟨1853303, by rfl⟩ : syracuseStep 2471071 = 3706607) B3706607
theorem B3294761 : Blo 2195435 3294761 := bstep (se 2 (by rfl) ⟨1235535, by rfl⟩ : syracuseStep 3294761 = 2471071) B2471071
theorem B2196507 : Blo 2195435 2196507 := bstep (se 1 (by rfl) ⟨1647380, by rfl⟩ : syracuseStep 2196507 = 3294761) B3294761
theorem B2674793 : Blo 2195435 2674793 := bbase (se 2 (by rfl) ⟨1003047, by rfl⟩ : syracuseStep 2674793 = 2006095) (by norm_num)
theorem B7132781 : Blo 2195435 7132781 := bstep (se 3 (by rfl) ⟨1337396, by rfl⟩ : syracuseStep 7132781 = 2674793) B2674793
theorem B19020749 : Blo 2195435 19020749 := bstep (se 3 (by rfl) ⟨3566390, by rfl⟩ : syracuseStep 19020749 = 7132781) B7132781
theorem B202887989 : Blo 2195435 202887989 := bstep (se 5 (by rfl) ⟨9510374, by rfl⟩ : syracuseStep 202887989 = 19020749) B19020749
theorem B135258659 : Blo 2195435 135258659 := bstep (se 1 (by rfl) ⟨101443994, by rfl⟩ : syracuseStep 135258659 = 202887989) B202887989
theorem B90172439 : Blo 2195435 90172439 := bstep (se 1 (by rfl) ⟨67629329, by rfl⟩ : syracuseStep 90172439 = 135258659) B135258659
theorem B60114959 : Blo 2195435 60114959 := bstep (se 1 (by rfl) ⟨45086219, by rfl⟩ : syracuseStep 60114959 = 90172439) B90172439
theorem B40076639 : Blo 2195435 40076639 := bstep (se 1 (by rfl) ⟨30057479, by rfl⟩ : syracuseStep 40076639 = 60114959) B60114959
theorem B26717759 : Blo 2195435 26717759 := bstep (se 1 (by rfl) ⟨20038319, by rfl⟩ : syracuseStep 26717759 = 40076639) B40076639
theorem B17811839 : Blo 2195435 17811839 := bstep (se 1 (by rfl) ⟨13358879, by rfl⟩ : syracuseStep 17811839 = 26717759) B26717759
theorem B47498237 : Blo 2195435 47498237 := bstep (se 3 (by rfl) ⟨8905919, by rfl⟩ : syracuseStep 47498237 = 17811839) B17811839
theorem B31665491 : Blo 2195435 31665491 := bstep (se 1 (by rfl) ⟨23749118, by rfl⟩ : syracuseStep 31665491 = 47498237) B47498237
theorem B21110327 : Blo 2195435 21110327 := bstep (se 1 (by rfl) ⟨15832745, by rfl⟩ : syracuseStep 21110327 = 31665491) B31665491
theorem B14073551 : Blo 2195435 14073551 := bstep (se 1 (by rfl) ⟨10555163, by rfl⟩ : syracuseStep 14073551 = 21110327) B21110327
theorem B9382367 : Blo 2195435 9382367 := bstep (se 1 (by rfl) ⟨7036775, by rfl⟩ : syracuseStep 9382367 = 14073551) B14073551
theorem B6254911 : Blo 2195435 6254911 := bstep (se 1 (by rfl) ⟨4691183, by rfl⟩ : syracuseStep 6254911 = 9382367) B9382367
theorem B8339881 : Blo 2195435 8339881 := bstep (se 2 (by rfl) ⟨3127455, by rfl⟩ : syracuseStep 8339881 = 6254911) B6254911
theorem B11119841 : Blo 2195435 11119841 := bstep (se 2 (by rfl) ⟨4169940, by rfl⟩ : syracuseStep 11119841 = 8339881) B8339881
theorem B7413227 : Blo 2195435 7413227 := bstep (se 1 (by rfl) ⟨5559920, by rfl⟩ : syracuseStep 7413227 = 11119841) B11119841
theorem B4942151 : Blo 2195435 4942151 := bstep (se 1 (by rfl) ⟨3706613, by rfl⟩ : syracuseStep 4942151 = 7413227) B7413227
theorem B3294767 : Blo 2195435 3294767 := bstep (se 1 (by rfl) ⟨2471075, by rfl⟩ : syracuseStep 3294767 = 4942151) B4942151
theorem B2196511 : Blo 2195435 2196511 := bstep (se 1 (by rfl) ⟨1647383, by rfl⟩ : syracuseStep 2196511 = 3294767) B3294767
theorem B3294773 : Blo 2195435 3294773 := bbase (se 5 (by rfl) ⟨154442, by rfl⟩ : syracuseStep 3294773 = 308885) (by norm_num)
theorem B2196515 : Blo 2195435 2196515 := bstep (se 1 (by rfl) ⟨1647386, by rfl⟩ : syracuseStep 2196515 = 3294773) B3294773
theorem B5559941 : Blo 2195435 5559941 := bbase (se 4 (by rfl) ⟨521244, by rfl⟩ : syracuseStep 5559941 = 1042489) (by norm_num)
theorem B3706627 : Blo 2195435 3706627 := bstep (se 1 (by rfl) ⟨2779970, by rfl⟩ : syracuseStep 3706627 = 5559941) B5559941
theorem B4942169 : Blo 2195435 4942169 := bstep (se 2 (by rfl) ⟨1853313, by rfl⟩ : syracuseStep 4942169 = 3706627) B3706627
theorem B3294779 : Blo 2195435 3294779 := bstep (se 1 (by rfl) ⟨2471084, by rfl⟩ : syracuseStep 3294779 = 4942169) B4942169
theorem B2196519 : Blo 2195435 2196519 := bstep (se 1 (by rfl) ⟨1647389, by rfl⟩ : syracuseStep 2196519 = 3294779) B3294779
theorem B2471089 : Blo 2195435 2471089 := bbase (se 2 (by rfl) ⟨926658, by rfl⟩ : syracuseStep 2471089 = 1853317) (by norm_num)
theorem B3294785 : Blo 2195435 3294785 := bstep (se 2 (by rfl) ⟨1235544, by rfl⟩ : syracuseStep 3294785 = 2471089) B2471089
theorem B2196523 : Blo 2195435 2196523 := bstep (se 1 (by rfl) ⟨1647392, by rfl⟩ : syracuseStep 2196523 = 3294785) B3294785
theorem B2345609 : Blo 2195435 2345609 := bbase (se 2 (by rfl) ⟨879603, by rfl⟩ : syracuseStep 2345609 = 1759207) (by norm_num)
theorem B6254957 : Blo 2195435 6254957 := bstep (se 3 (by rfl) ⟨1172804, by rfl⟩ : syracuseStep 6254957 = 2345609) B2345609
theorem B4169971 : Blo 2195435 4169971 := bstep (se 1 (by rfl) ⟨3127478, by rfl⟩ : syracuseStep 4169971 = 6254957) B6254957
theorem B5559961 : Blo 2195435 5559961 := bstep (se 2 (by rfl) ⟨2084985, by rfl⟩ : syracuseStep 5559961 = 4169971) B4169971
theorem B7413281 : Blo 2195435 7413281 := bstep (se 2 (by rfl) ⟨2779980, by rfl⟩ : syracuseStep 7413281 = 5559961) B5559961
theorem B4942187 : Blo 2195435 4942187 := bstep (se 1 (by rfl) ⟨3706640, by rfl⟩ : syracuseStep 4942187 = 7413281) B7413281
theorem B3294791 : Blo 2195435 3294791 := bstep (se 1 (by rfl) ⟨2471093, by rfl⟩ : syracuseStep 3294791 = 4942187) B4942187
theorem B2196527 : Blo 2195435 2196527 := bstep (se 1 (by rfl) ⟨1647395, by rfl⟩ : syracuseStep 2196527 = 3294791) B3294791
theorem B3294797 : Blo 2195435 3294797 := bbase (se 3 (by rfl) ⟨617774, by rfl⟩ : syracuseStep 3294797 = 1235549) (by norm_num)
theorem B2196531 : Blo 2195435 2196531 := bstep (se 1 (by rfl) ⟨1647398, by rfl⟩ : syracuseStep 2196531 = 3294797) B3294797
theorem B4942205 : Blo 2195435 4942205 := bbase (se 3 (by rfl) ⟨926663, by rfl⟩ : syracuseStep 4942205 = 1853327) (by norm_num)
theorem B3294803 : Blo 2195435 3294803 := bstep (se 1 (by rfl) ⟨2471102, by rfl⟩ : syracuseStep 3294803 = 4942205) B4942205
theorem B2196535 : Blo 2195435 2196535 := bstep (se 1 (by rfl) ⟨1647401, by rfl⟩ : syracuseStep 2196535 = 3294803) B3294803
theorem B3706661 : Blo 2195435 3706661 := bbase (se 4 (by rfl) ⟨347499, by rfl⟩ : syracuseStep 3706661 = 694999) (by norm_num)
theorem B2471107 : Blo 2195435 2471107 := bstep (se 1 (by rfl) ⟨1853330, by rfl⟩ : syracuseStep 2471107 = 3706661) B3706661
theorem B3294809 : Blo 2195435 3294809 := bstep (se 2 (by rfl) ⟨1235553, by rfl⟩ : syracuseStep 3294809 = 2471107) B2471107
theorem B2196539 : Blo 2195435 2196539 := bstep (se 1 (by rfl) ⟨1647404, by rfl⟩ : syracuseStep 2196539 = 3294809) B3294809
theorem B3127501 : Blo 2195435 3127501 := bbase (se 3 (by rfl) ⟨586406, by rfl⟩ : syracuseStep 3127501 = 1172813) (by norm_num)
theorem B16680005 : Blo 2195435 16680005 := bstep (se 4 (by rfl) ⟨1563750, by rfl⟩ : syracuseStep 16680005 = 3127501) B3127501
theorem B11120003 : Blo 2195435 11120003 := bstep (se 1 (by rfl) ⟨8340002, by rfl⟩ : syracuseStep 11120003 = 16680005) B16680005
theorem B7413335 : Blo 2195435 7413335 := bstep (se 1 (by rfl) ⟨5560001, by rfl⟩ : syracuseStep 7413335 = 11120003) B11120003
theorem B4942223 : Blo 2195435 4942223 := bstep (se 1 (by rfl) ⟨3706667, by rfl⟩ : syracuseStep 4942223 = 7413335) B7413335
theorem B3294815 : Blo 2195435 3294815 := bstep (se 1 (by rfl) ⟨2471111, by rfl⟩ : syracuseStep 3294815 = 4942223) B4942223
theorem B2196543 : Blo 2195435 2196543 := bstep (se 1 (by rfl) ⟨1647407, by rfl⟩ : syracuseStep 2196543 = 3294815) B3294815
theorem B3294821 : Blo 2195435 3294821 := bbase (se 4 (by rfl) ⟨308889, by rfl⟩ : syracuseStep 3294821 = 617779) (by norm_num)
theorem B2196547 : Blo 2195435 2196547 := bstep (se 1 (by rfl) ⟨1647410, by rfl⟩ : syracuseStep 2196547 = 3294821) B3294821
theorem B3518453 : Blo 2195435 3518453 := bbase (se 5 (by rfl) ⟨164927, by rfl⟩ : syracuseStep 3518453 = 329855) (by norm_num)
theorem B2345635 : Blo 2195435 2345635 := bstep (se 1 (by rfl) ⟨1759226, by rfl⟩ : syracuseStep 2345635 = 3518453) B3518453
theorem B3127513 : Blo 2195435 3127513 := bstep (se 2 (by rfl) ⟨1172817, by rfl⟩ : syracuseStep 3127513 = 2345635) B2345635
theorem B4170017 : Blo 2195435 4170017 := bstep (se 2 (by rfl) ⟨1563756, by rfl⟩ : syracuseStep 4170017 = 3127513) B3127513
theorem B2780011 : Blo 2195435 2780011 := bstep (se 1 (by rfl) ⟨2085008, by rfl⟩ : syracuseStep 2780011 = 4170017) B4170017
theorem B3706681 : Blo 2195435 3706681 := bstep (se 2 (by rfl) ⟨1390005, by rfl⟩ : syracuseStep 3706681 = 2780011) B2780011
theorem B4942241 : Blo 2195435 4942241 := bstep (se 2 (by rfl) ⟨1853340, by rfl⟩ : syracuseStep 4942241 = 3706681) B3706681
theorem B3294827 : Blo 2195435 3294827 := bstep (se 1 (by rfl) ⟨2471120, by rfl⟩ : syracuseStep 3294827 = 4942241) B4942241
theorem B2196551 : Blo 2195435 2196551 := bstep (se 1 (by rfl) ⟨1647413, by rfl⟩ : syracuseStep 2196551 = 3294827) B3294827
theorem B2471125 : Blo 2195435 2471125 := bbase (se 7 (by rfl) ⟨28958, by rfl⟩ : syracuseStep 2471125 = 57917) (by norm_num)
theorem B3294833 : Blo 2195435 3294833 := bstep (se 2 (by rfl) ⟨1235562, by rfl⟩ : syracuseStep 3294833 = 2471125) B2471125
theorem B2196555 : Blo 2195435 2196555 := bstep (se 1 (by rfl) ⟨1647416, by rfl⟩ : syracuseStep 2196555 = 3294833) B3294833
theorem B2780021 : Blo 2195435 2780021 := bbase (se 5 (by rfl) ⟨130313, by rfl⟩ : syracuseStep 2780021 = 260627) (by norm_num)
theorem B7413389 : Blo 2195435 7413389 := bstep (se 3 (by rfl) ⟨1390010, by rfl⟩ : syracuseStep 7413389 = 2780021) B2780021
theorem B4942259 : Blo 2195435 4942259 := bstep (se 1 (by rfl) ⟨3706694, by rfl⟩ : syracuseStep 4942259 = 7413389) B7413389
theorem B3294839 : Blo 2195435 3294839 := bstep (se 1 (by rfl) ⟨2471129, by rfl⟩ : syracuseStep 3294839 = 4942259) B4942259
theorem B2196559 : Blo 2195435 2196559 := bstep (se 1 (by rfl) ⟨1647419, by rfl⟩ : syracuseStep 2196559 = 3294839) B3294839
theorem B3294845 : Blo 2195435 3294845 := bbase (se 3 (by rfl) ⟨617783, by rfl⟩ : syracuseStep 3294845 = 1235567) (by norm_num)
theorem B2196563 : Blo 2195435 2196563 := bstep (se 1 (by rfl) ⟨1647422, by rfl⟩ : syracuseStep 2196563 = 3294845) B3294845
theorem B4942277 : Blo 2195435 4942277 := bbase (se 4 (by rfl) ⟨463338, by rfl⟩ : syracuseStep 4942277 = 926677) (by norm_num)
theorem B3294851 : Blo 2195435 3294851 := bstep (se 1 (by rfl) ⟨2471138, by rfl⟩ : syracuseStep 3294851 = 4942277) B4942277
theorem B2196567 : Blo 2195435 2196567 := bstep (se 1 (by rfl) ⟨1647425, by rfl⟩ : syracuseStep 2196567 = 3294851) B3294851
theorem B22543733 : Blo 2195435 22543733 := bbase (se 5 (by rfl) ⟨1056737, by rfl⟩ : syracuseStep 22543733 = 2113475) (by norm_num)
theorem B15029155 : Blo 2195435 15029155 := bstep (se 1 (by rfl) ⟨11271866, by rfl⟩ : syracuseStep 15029155 = 22543733) B22543733
theorem B20038873 : Blo 2195435 20038873 := bstep (se 2 (by rfl) ⟨7514577, by rfl⟩ : syracuseStep 20038873 = 15029155) B15029155
theorem B26718497 : Blo 2195435 26718497 := bstep (se 2 (by rfl) ⟨10019436, by rfl⟩ : syracuseStep 26718497 = 20038873) B20038873
theorem B17812331 : Blo 2195435 17812331 := bstep (se 1 (by rfl) ⟨13359248, by rfl⟩ : syracuseStep 17812331 = 26718497) B26718497
theorem B11874887 : Blo 2195435 11874887 := bstep (se 1 (by rfl) ⟨8906165, by rfl⟩ : syracuseStep 11874887 = 17812331) B17812331
theorem B7916591 : Blo 2195435 7916591 := bstep (se 1 (by rfl) ⟨5937443, by rfl⟩ : syracuseStep 7916591 = 11874887) B11874887
theorem B5277727 : Blo 2195435 5277727 := bstep (se 1 (by rfl) ⟨3958295, by rfl⟩ : syracuseStep 5277727 = 7916591) B7916591
theorem B7036969 : Blo 2195435 7036969 := bstep (se 2 (by rfl) ⟨2638863, by rfl⟩ : syracuseStep 7036969 = 5277727) B5277727
theorem B9382625 : Blo 2195435 9382625 := bstep (se 2 (by rfl) ⟨3518484, by rfl⟩ : syracuseStep 9382625 = 7036969) B7036969
theorem B6255083 : Blo 2195435 6255083 := bstep (se 1 (by rfl) ⟨4691312, by rfl⟩ : syracuseStep 6255083 = 9382625) B9382625
theorem B4170055 : Blo 2195435 4170055 := bstep (se 1 (by rfl) ⟨3127541, by rfl⟩ : syracuseStep 4170055 = 6255083) B6255083
theorem B5560073 : Blo 2195435 5560073 := bstep (se 2 (by rfl) ⟨2085027, by rfl⟩ : syracuseStep 5560073 = 4170055) B4170055
theorem B3706715 : Blo 2195435 3706715 := bstep (se 1 (by rfl) ⟨2780036, by rfl⟩ : syracuseStep 3706715 = 5560073) B5560073
theorem B2471143 : Blo 2195435 2471143 := bstep (se 1 (by rfl) ⟨1853357, by rfl⟩ : syracuseStep 2471143 = 3706715) B3706715
theorem B3294857 : Blo 2195435 3294857 := bstep (se 2 (by rfl) ⟨1235571, by rfl⟩ : syracuseStep 3294857 = 2471143) B2471143
theorem B2196571 : Blo 2195435 2196571 := bstep (se 1 (by rfl) ⟨1647428, by rfl⟩ : syracuseStep 2196571 = 3294857) B3294857
theorem B11120165 : Blo 2195435 11120165 := bbase (se 4 (by rfl) ⟨1042515, by rfl⟩ : syracuseStep 11120165 = 2085031) (by norm_num)
theorem B7413443 : Blo 2195435 7413443 := bstep (se 1 (by rfl) ⟨5560082, by rfl⟩ : syracuseStep 7413443 = 11120165) B11120165
theorem B4942295 : Blo 2195435 4942295 := bstep (se 1 (by rfl) ⟨3706721, by rfl⟩ : syracuseStep 4942295 = 7413443) B7413443
theorem B3294863 : Blo 2195435 3294863 := bstep (se 1 (by rfl) ⟨2471147, by rfl⟩ : syracuseStep 3294863 = 4942295) B4942295
theorem B2196575 : Blo 2195435 2196575 := bstep (se 1 (by rfl) ⟨1647431, by rfl⟩ : syracuseStep 2196575 = 3294863) B3294863
theorem B3294869 : Blo 2195435 3294869 := bbase (se 6 (by rfl) ⟨77223, by rfl⟩ : syracuseStep 3294869 = 154447) (by norm_num)
theorem B2196579 : Blo 2195435 2196579 := bstep (se 1 (by rfl) ⟨1647434, by rfl⟩ : syracuseStep 2196579 = 3294869) B3294869
theorem B8906213 : Blo 2195435 8906213 := bbase (se 4 (by rfl) ⟨834957, by rfl⟩ : syracuseStep 8906213 = 1669915) (by norm_num)
theorem B5937475 : Blo 2195435 5937475 := bstep (se 1 (by rfl) ⟨4453106, by rfl⟩ : syracuseStep 5937475 = 8906213) B8906213
theorem B7916633 : Blo 2195435 7916633 := bstep (se 2 (by rfl) ⟨2968737, by rfl⟩ : syracuseStep 7916633 = 5937475) B5937475
theorem B5277755 : Blo 2195435 5277755 := bstep (se 1 (by rfl) ⟨3958316, by rfl⟩ : syracuseStep 5277755 = 7916633) B7916633
theorem B14074013 : Blo 2195435 14074013 := bstep (se 3 (by rfl) ⟨2638877, by rfl⟩ : syracuseStep 14074013 = 5277755) B5277755
theorem B9382675 : Blo 2195435 9382675 := bstep (se 1 (by rfl) ⟨7037006, by rfl⟩ : syracuseStep 9382675 = 14074013) B14074013
theorem B12510233 : Blo 2195435 12510233 := bstep (se 2 (by rfl) ⟨4691337, by rfl⟩ : syracuseStep 12510233 = 9382675) B9382675
theorem B8340155 : Blo 2195435 8340155 := bstep (se 1 (by rfl) ⟨6255116, by rfl⟩ : syracuseStep 8340155 = 12510233) B12510233
theorem B5560103 : Blo 2195435 5560103 := bstep (se 1 (by rfl) ⟨4170077, by rfl⟩ : syracuseStep 5560103 = 8340155) B8340155
theorem B3706735 : Blo 2195435 3706735 := bstep (se 1 (by rfl) ⟨2780051, by rfl⟩ : syracuseStep 3706735 = 5560103) B5560103
theorem B4942313 : Blo 2195435 4942313 := bstep (se 2 (by rfl) ⟨1853367, by rfl⟩ : syracuseStep 4942313 = 3706735) B3706735
theorem B3294875 : Blo 2195435 3294875 := bstep (se 1 (by rfl) ⟨2471156, by rfl⟩ : syracuseStep 3294875 = 4942313) B4942313
theorem B2196583 : Blo 2195435 2196583 := bstep (se 1 (by rfl) ⟨1647437, by rfl⟩ : syracuseStep 2196583 = 3294875) B3294875
theorem B2471161 : Blo 2195435 2471161 := bbase (se 2 (by rfl) ⟨926685, by rfl⟩ : syracuseStep 2471161 = 1853371) (by norm_num)
theorem B3294881 : Blo 2195435 3294881 := bstep (se 2 (by rfl) ⟨1235580, by rfl⟩ : syracuseStep 3294881 = 2471161) B2471161
theorem B2196587 : Blo 2195435 2196587 := bstep (se 1 (by rfl) ⟨1647440, by rfl⟩ : syracuseStep 2196587 = 3294881) B3294881
theorem B9382709 : Blo 2195435 9382709 := bbase (se 5 (by rfl) ⟨439814, by rfl⟩ : syracuseStep 9382709 = 879629) (by norm_num)
theorem B6255139 : Blo 2195435 6255139 := bstep (se 1 (by rfl) ⟨4691354, by rfl⟩ : syracuseStep 6255139 = 9382709) B9382709
theorem B8340185 : Blo 2195435 8340185 := bstep (se 2 (by rfl) ⟨3127569, by rfl⟩ : syracuseStep 8340185 = 6255139) B6255139
theorem B5560123 : Blo 2195435 5560123 := bstep (se 1 (by rfl) ⟨4170092, by rfl⟩ : syracuseStep 5560123 = 8340185) B8340185
theorem B7413497 : Blo 2195435 7413497 := bstep (se 2 (by rfl) ⟨2780061, by rfl⟩ : syracuseStep 7413497 = 5560123) B5560123
theorem B4942331 : Blo 2195435 4942331 := bstep (se 1 (by rfl) ⟨3706748, by rfl⟩ : syracuseStep 4942331 = 7413497) B7413497
theorem B3294887 : Blo 2195435 3294887 := bstep (se 1 (by rfl) ⟨2471165, by rfl⟩ : syracuseStep 3294887 = 4942331) B4942331
theorem B2196591 : Blo 2195435 2196591 := bstep (se 1 (by rfl) ⟨1647443, by rfl⟩ : syracuseStep 2196591 = 3294887) B3294887
theorem B3294893 : Blo 2195435 3294893 := bbase (se 3 (by rfl) ⟨617792, by rfl⟩ : syracuseStep 3294893 = 1235585) (by norm_num)
theorem B2196595 : Blo 2195435 2196595 := bstep (se 1 (by rfl) ⟨1647446, by rfl⟩ : syracuseStep 2196595 = 3294893) B3294893
theorem B4942349 : Blo 2195435 4942349 := bbase (se 3 (by rfl) ⟨926690, by rfl⟩ : syracuseStep 4942349 = 1853381) (by norm_num)
theorem B3294899 : Blo 2195435 3294899 := bstep (se 1 (by rfl) ⟨2471174, by rfl⟩ : syracuseStep 3294899 = 4942349) B4942349
theorem B2196599 : Blo 2195435 2196599 := bstep (se 1 (by rfl) ⟨1647449, by rfl⟩ : syracuseStep 2196599 = 3294899) B3294899
theorem B2780077 : Blo 2195435 2780077 := bbase (se 3 (by rfl) ⟨521264, by rfl⟩ : syracuseStep 2780077 = 1042529) (by norm_num)
theorem B3706769 : Blo 2195435 3706769 := bstep (se 2 (by rfl) ⟨1390038, by rfl⟩ : syracuseStep 3706769 = 2780077) B2780077
theorem B2471179 : Blo 2195435 2471179 := bstep (se 1 (by rfl) ⟨1853384, by rfl⟩ : syracuseStep 2471179 = 3706769) B3706769
theorem B3294905 : Blo 2195435 3294905 := bstep (se 2 (by rfl) ⟨1235589, by rfl⟩ : syracuseStep 3294905 = 2471179) B2471179
theorem B2196603 : Blo 2195435 2196603 := bstep (se 1 (by rfl) ⟨1647452, by rfl⟩ : syracuseStep 2196603 = 3294905) B3294905
theorem B14074165 : Blo 2195435 14074165 := bbase (se 5 (by rfl) ⟨659726, by rfl⟩ : syracuseStep 14074165 = 1319453) (by norm_num)
theorem B18765553 : Blo 2195435 18765553 := bstep (se 2 (by rfl) ⟨7037082, by rfl⟩ : syracuseStep 18765553 = 14074165) B14074165
theorem B25020737 : Blo 2195435 25020737 := bstep (se 2 (by rfl) ⟨9382776, by rfl⟩ : syracuseStep 25020737 = 18765553) B18765553
theorem B16680491 : Blo 2195435 16680491 := bstep (se 1 (by rfl) ⟨12510368, by rfl⟩ : syracuseStep 16680491 = 25020737) B25020737
theorem B11120327 : Blo 2195435 11120327 := bstep (se 1 (by rfl) ⟨8340245, by rfl⟩ : syracuseStep 11120327 = 16680491) B16680491
theorem B7413551 : Blo 2195435 7413551 := bstep (se 1 (by rfl) ⟨5560163, by rfl⟩ : syracuseStep 7413551 = 11120327) B11120327
theorem B4942367 : Blo 2195435 4942367 := bstep (se 1 (by rfl) ⟨3706775, by rfl⟩ : syracuseStep 4942367 = 7413551) B7413551
theorem B3294911 : Blo 2195435 3294911 := bstep (se 1 (by rfl) ⟨2471183, by rfl⟩ : syracuseStep 3294911 = 4942367) B4942367
theorem B2196607 : Blo 2195435 2196607 := bstep (se 1 (by rfl) ⟨1647455, by rfl⟩ : syracuseStep 2196607 = 3294911) B3294911
theorem B3294917 : Blo 2195435 3294917 := bbase (se 4 (by rfl) ⟨308898, by rfl⟩ : syracuseStep 3294917 = 617797) (by norm_num)
theorem B2196611 : Blo 2195435 2196611 := bstep (se 1 (by rfl) ⟨1647458, by rfl⟩ : syracuseStep 2196611 = 3294917) B3294917
theorem B3706789 : Blo 2195435 3706789 := bbase (se 4 (by rfl) ⟨347511, by rfl⟩ : syracuseStep 3706789 = 695023) (by norm_num)
theorem B4942385 : Blo 2195435 4942385 := bstep (se 2 (by rfl) ⟨1853394, by rfl⟩ : syracuseStep 4942385 = 3706789) B3706789
theorem B3294923 : Blo 2195435 3294923 := bstep (se 1 (by rfl) ⟨2471192, by rfl⟩ : syracuseStep 3294923 = 4942385) B4942385
theorem B2196615 : Blo 2195435 2196615 := bstep (se 1 (by rfl) ⟨1647461, by rfl⟩ : syracuseStep 2196615 = 3294923) B3294923
theorem B2471197 : Blo 2195435 2471197 := bbase (se 3 (by rfl) ⟨463349, by rfl⟩ : syracuseStep 2471197 = 926699) (by norm_num)
theorem B3294929 : Blo 2195435 3294929 := bstep (se 2 (by rfl) ⟨1235598, by rfl⟩ : syracuseStep 3294929 = 2471197) B2471197
theorem B2196619 : Blo 2195435 2196619 := bstep (se 1 (by rfl) ⟨1647464, by rfl⟩ : syracuseStep 2196619 = 3294929) B3294929
theorem B7413605 : Blo 2195435 7413605 := bbase (se 4 (by rfl) ⟨695025, by rfl⟩ : syracuseStep 7413605 = 1390051) (by norm_num)
theorem B4942403 : Blo 2195435 4942403 := bstep (se 1 (by rfl) ⟨3706802, by rfl⟩ : syracuseStep 4942403 = 7413605) B7413605
theorem B3294935 : Blo 2195435 3294935 := bstep (se 1 (by rfl) ⟨2471201, by rfl⟩ : syracuseStep 3294935 = 4942403) B4942403
theorem B2196623 : Blo 2195435 2196623 := bstep (se 1 (by rfl) ⟨1647467, by rfl⟩ : syracuseStep 2196623 = 3294935) B3294935
theorem B3294941 : Blo 2195435 3294941 := bbase (se 3 (by rfl) ⟨617801, by rfl⟩ : syracuseStep 3294941 = 1235603) (by norm_num)
theorem B2196627 : Blo 2195435 2196627 := bstep (se 1 (by rfl) ⟨1647470, by rfl⟩ : syracuseStep 2196627 = 3294941) B3294941
theorem B4942421 : Blo 2195435 4942421 := bbase (se 8 (by rfl) ⟨28959, by rfl⟩ : syracuseStep 4942421 = 57919) (by norm_num)
theorem B3294947 : Blo 2195435 3294947 := bstep (se 1 (by rfl) ⟨2471210, by rfl⟩ : syracuseStep 3294947 = 4942421) B4942421
theorem B2196631 : Blo 2195435 2196631 := bstep (se 1 (by rfl) ⟨1647473, by rfl⟩ : syracuseStep 2196631 = 3294947) B3294947
theorem B4453213 : Blo 2195435 4453213 := bbase (se 3 (by rfl) ⟨834977, by rfl⟩ : syracuseStep 4453213 = 1669955) (by norm_num)
theorem B5937617 : Blo 2195435 5937617 := bstep (se 2 (by rfl) ⟨2226606, by rfl⟩ : syracuseStep 5937617 = 4453213) B4453213
theorem B3958411 : Blo 2195435 3958411 := bstep (se 1 (by rfl) ⟨2968808, by rfl⟩ : syracuseStep 3958411 = 5937617) B5937617
theorem B5277881 : Blo 2195435 5277881 := bstep (se 2 (by rfl) ⟨1979205, by rfl⟩ : syracuseStep 5277881 = 3958411) B3958411
theorem B3518587 : Blo 2195435 3518587 := bstep (se 1 (by rfl) ⟨2638940, by rfl⟩ : syracuseStep 3518587 = 5277881) B5277881
theorem B4691449 : Blo 2195435 4691449 := bstep (se 2 (by rfl) ⟨1759293, by rfl⟩ : syracuseStep 4691449 = 3518587) B3518587
theorem B6255265 : Blo 2195435 6255265 := bstep (se 2 (by rfl) ⟨2345724, by rfl⟩ : syracuseStep 6255265 = 4691449) B4691449
theorem B8340353 : Blo 2195435 8340353 := bstep (se 2 (by rfl) ⟨3127632, by rfl⟩ : syracuseStep 8340353 = 6255265) B6255265
theorem B5560235 : Blo 2195435 5560235 := bstep (se 1 (by rfl) ⟨4170176, by rfl⟩ : syracuseStep 5560235 = 8340353) B8340353
theorem B3706823 : Blo 2195435 3706823 := bstep (se 1 (by rfl) ⟨2780117, by rfl⟩ : syracuseStep 3706823 = 5560235) B5560235
theorem B2471215 : Blo 2195435 2471215 := bstep (se 1 (by rfl) ⟨1853411, by rfl⟩ : syracuseStep 2471215 = 3706823) B3706823
theorem B3294953 : Blo 2195435 3294953 := bstep (se 2 (by rfl) ⟨1235607, by rfl⟩ : syracuseStep 3294953 = 2471215) B2471215
theorem B2196635 : Blo 2195435 2196635 := bstep (se 1 (by rfl) ⟨1647476, by rfl⟩ : syracuseStep 2196635 = 3294953) B3294953
theorem B2968813 : Blo 2195435 2968813 := bbase (se 3 (by rfl) ⟨556652, by rfl⟩ : syracuseStep 2968813 = 1113305) (by norm_num)
theorem B3958417 : Blo 2195435 3958417 := bstep (se 2 (by rfl) ⟨1484406, by rfl⟩ : syracuseStep 3958417 = 2968813) B2968813
theorem B5277889 : Blo 2195435 5277889 := bstep (se 2 (by rfl) ⟨1979208, by rfl⟩ : syracuseStep 5277889 = 3958417) B3958417
theorem B28148741 : Blo 2195435 28148741 := bstep (se 4 (by rfl) ⟨2638944, by rfl⟩ : syracuseStep 28148741 = 5277889) B5277889
theorem B18765827 : Blo 2195435 18765827 := bstep (se 1 (by rfl) ⟨14074370, by rfl⟩ : syracuseStep 18765827 = 28148741) B28148741
theorem B12510551 : Blo 2195435 12510551 := bstep (se 1 (by rfl) ⟨9382913, by rfl⟩ : syracuseStep 12510551 = 18765827) B18765827
theorem B8340367 : Blo 2195435 8340367 := bstep (se 1 (by rfl) ⟨6255275, by rfl⟩ : syracuseStep 8340367 = 12510551) B12510551
theorem B11120489 : Blo 2195435 11120489 := bstep (se 2 (by rfl) ⟨4170183, by rfl⟩ : syracuseStep 11120489 = 8340367) B8340367
theorem B7413659 : Blo 2195435 7413659 := bstep (se 1 (by rfl) ⟨5560244, by rfl⟩ : syracuseStep 7413659 = 11120489) B11120489
theorem B4942439 : Blo 2195435 4942439 := bstep (se 1 (by rfl) ⟨3706829, by rfl⟩ : syracuseStep 4942439 = 7413659) B7413659
theorem B3294959 : Blo 2195435 3294959 := bstep (se 1 (by rfl) ⟨2471219, by rfl⟩ : syracuseStep 3294959 = 4942439) B4942439
theorem B2196639 : Blo 2195435 2196639 := bstep (se 1 (by rfl) ⟨1647479, by rfl⟩ : syracuseStep 2196639 = 3294959) B3294959
theorem B3294965 : Blo 2195435 3294965 := bbase (se 5 (by rfl) ⟨154451, by rfl⟩ : syracuseStep 3294965 = 308903) (by norm_num)
theorem B2196643 : Blo 2195435 2196643 := bstep (se 1 (by rfl) ⟨1647482, by rfl⟩ : syracuseStep 2196643 = 3294965) B3294965
theorem B9382949 : Blo 2195435 9382949 := bbase (se 4 (by rfl) ⟨879651, by rfl⟩ : syracuseStep 9382949 = 1759303) (by norm_num)
theorem B6255299 : Blo 2195435 6255299 := bstep (se 1 (by rfl) ⟨4691474, by rfl⟩ : syracuseStep 6255299 = 9382949) B9382949
theorem B4170199 : Blo 2195435 4170199 := bstep (se 1 (by rfl) ⟨3127649, by rfl⟩ : syracuseStep 4170199 = 6255299) B6255299
theorem B5560265 : Blo 2195435 5560265 := bstep (se 2 (by rfl) ⟨2085099, by rfl⟩ : syracuseStep 5560265 = 4170199) B4170199
theorem B3706843 : Blo 2195435 3706843 := bstep (se 1 (by rfl) ⟨2780132, by rfl⟩ : syracuseStep 3706843 = 5560265) B5560265
theorem B4942457 : Blo 2195435 4942457 := bstep (se 2 (by rfl) ⟨1853421, by rfl⟩ : syracuseStep 4942457 = 3706843) B3706843
theorem B3294971 : Blo 2195435 3294971 := bstep (se 1 (by rfl) ⟨2471228, by rfl⟩ : syracuseStep 3294971 = 4942457) B4942457
theorem B2196647 : Blo 2195435 2196647 := bstep (se 1 (by rfl) ⟨1647485, by rfl⟩ : syracuseStep 2196647 = 3294971) B3294971
theorem B2471233 : Blo 2195435 2471233 := bbase (se 2 (by rfl) ⟨926712, by rfl⟩ : syracuseStep 2471233 = 1853425) (by norm_num)
theorem B3294977 : Blo 2195435 3294977 := bstep (se 2 (by rfl) ⟨1235616, by rfl⟩ : syracuseStep 3294977 = 2471233) B2471233
theorem B2196651 : Blo 2195435 2196651 := bstep (se 1 (by rfl) ⟨1647488, by rfl⟩ : syracuseStep 2196651 = 3294977) B3294977
theorem B5560285 : Blo 2195435 5560285 := bbase (se 3 (by rfl) ⟨1042553, by rfl⟩ : syracuseStep 5560285 = 2085107) (by norm_num)
theorem B7413713 : Blo 2195435 7413713 := bstep (se 2 (by rfl) ⟨2780142, by rfl⟩ : syracuseStep 7413713 = 5560285) B5560285
theorem B4942475 : Blo 2195435 4942475 := bstep (se 1 (by rfl) ⟨3706856, by rfl⟩ : syracuseStep 4942475 = 7413713) B7413713
theorem B3294983 : Blo 2195435 3294983 := bstep (se 1 (by rfl) ⟨2471237, by rfl⟩ : syracuseStep 3294983 = 4942475) B4942475
theorem B2196655 : Blo 2195435 2196655 := bstep (se 1 (by rfl) ⟨1647491, by rfl⟩ : syracuseStep 2196655 = 3294983) B3294983
theorem B3294989 : Blo 2195435 3294989 := bbase (se 3 (by rfl) ⟨617810, by rfl⟩ : syracuseStep 3294989 = 1235621) (by norm_num)
theorem B2196659 : Blo 2195435 2196659 := bstep (se 1 (by rfl) ⟨1647494, by rfl⟩ : syracuseStep 2196659 = 3294989) B3294989
theorem B4942493 : Blo 2195435 4942493 := bbase (se 3 (by rfl) ⟨926717, by rfl⟩ : syracuseStep 4942493 = 1853435) (by norm_num)
theorem B3294995 : Blo 2195435 3294995 := bstep (se 1 (by rfl) ⟨2471246, by rfl⟩ : syracuseStep 3294995 = 4942493) B4942493
theorem B2196663 : Blo 2195435 2196663 := bstep (se 1 (by rfl) ⟨1647497, by rfl⟩ : syracuseStep 2196663 = 3294995) B3294995
theorem B3706877 : Blo 2195435 3706877 := bbase (se 3 (by rfl) ⟨695039, by rfl⟩ : syracuseStep 3706877 = 1390079) (by norm_num)
theorem B2471251 : Blo 2195435 2471251 := bstep (se 1 (by rfl) ⟨1853438, by rfl⟩ : syracuseStep 2471251 = 3706877) B3706877
theorem B3295001 : Blo 2195435 3295001 := bstep (se 2 (by rfl) ⟨1235625, by rfl⟩ : syracuseStep 3295001 = 2471251) B2471251
theorem B2196667 : Blo 2195435 2196667 := bstep (se 1 (by rfl) ⟨1647500, by rfl⟩ : syracuseStep 2196667 = 3295001) B3295001
theorem B4691525 : Blo 2195435 4691525 := bbase (se 4 (by rfl) ⟨439830, by rfl⟩ : syracuseStep 4691525 = 879661) (by norm_num)
theorem B12510733 : Blo 2195435 12510733 := bstep (se 3 (by rfl) ⟨2345762, by rfl⟩ : syracuseStep 12510733 = 4691525) B4691525
theorem B16680977 : Blo 2195435 16680977 := bstep (se 2 (by rfl) ⟨6255366, by rfl⟩ : syracuseStep 16680977 = 12510733) B12510733
theorem B11120651 : Blo 2195435 11120651 := bstep (se 1 (by rfl) ⟨8340488, by rfl⟩ : syracuseStep 11120651 = 16680977) B16680977
theorem B7413767 : Blo 2195435 7413767 := bstep (se 1 (by rfl) ⟨5560325, by rfl⟩ : syracuseStep 7413767 = 11120651) B11120651
theorem B4942511 : Blo 2195435 4942511 := bstep (se 1 (by rfl) ⟨3706883, by rfl⟩ : syracuseStep 4942511 = 7413767) B7413767
theorem B3295007 : Blo 2195435 3295007 := bstep (se 1 (by rfl) ⟨2471255, by rfl⟩ : syracuseStep 3295007 = 4942511) B4942511
theorem B2196671 : Blo 2195435 2196671 := bstep (se 1 (by rfl) ⟨1647503, by rfl⟩ : syracuseStep 2196671 = 3295007) B3295007
theorem B3295013 : Blo 2195435 3295013 := bbase (se 4 (by rfl) ⟨308907, by rfl⟩ : syracuseStep 3295013 = 617815) (by norm_num)
theorem B2196675 : Blo 2195435 2196675 := bstep (se 1 (by rfl) ⟨1647506, by rfl⟩ : syracuseStep 2196675 = 3295013) B3295013
theorem B2780173 : Blo 2195435 2780173 := bbase (se 3 (by rfl) ⟨521282, by rfl⟩ : syracuseStep 2780173 = 1042565) (by norm_num)
theorem B3706897 : Blo 2195435 3706897 := bstep (se 2 (by rfl) ⟨1390086, by rfl⟩ : syracuseStep 3706897 = 2780173) B2780173
theorem B4942529 : Blo 2195435 4942529 := bstep (se 2 (by rfl) ⟨1853448, by rfl⟩ : syracuseStep 4942529 = 3706897) B3706897
theorem B3295019 : Blo 2195435 3295019 := bstep (se 1 (by rfl) ⟨2471264, by rfl⟩ : syracuseStep 3295019 = 4942529) B4942529
theorem B2196679 : Blo 2195435 2196679 := bstep (se 1 (by rfl) ⟨1647509, by rfl⟩ : syracuseStep 2196679 = 3295019) B3295019
theorem B2471269 : Blo 2195435 2471269 := bbase (se 4 (by rfl) ⟨231681, by rfl⟩ : syracuseStep 2471269 = 463363) (by norm_num)
theorem B3295025 : Blo 2195435 3295025 := bstep (se 2 (by rfl) ⟨1235634, by rfl⟩ : syracuseStep 3295025 = 2471269) B2471269
theorem B2196683 : Blo 2195435 2196683 := bstep (se 1 (by rfl) ⟨1647512, by rfl⟩ : syracuseStep 2196683 = 3295025) B3295025
theorem B6255413 : Blo 2195435 6255413 := bbase (se 5 (by rfl) ⟨293222, by rfl⟩ : syracuseStep 6255413 = 586445) (by norm_num)
theorem B4170275 : Blo 2195435 4170275 := bstep (se 1 (by rfl) ⟨3127706, by rfl⟩ : syracuseStep 4170275 = 6255413) B6255413
theorem B2780183 : Blo 2195435 2780183 := bstep (se 1 (by rfl) ⟨2085137, by rfl⟩ : syracuseStep 2780183 = 4170275) B4170275
theorem B7413821 : Blo 2195435 7413821 := bstep (se 3 (by rfl) ⟨1390091, by rfl⟩ : syracuseStep 7413821 = 2780183) B2780183
theorem B4942547 : Blo 2195435 4942547 := bstep (se 1 (by rfl) ⟨3706910, by rfl⟩ : syracuseStep 4942547 = 7413821) B7413821
theorem B3295031 : Blo 2195435 3295031 := bstep (se 1 (by rfl) ⟨2471273, by rfl⟩ : syracuseStep 3295031 = 4942547) B4942547
theorem B2196687 : Blo 2195435 2196687 := bstep (se 1 (by rfl) ⟨1647515, by rfl⟩ : syracuseStep 2196687 = 3295031) B3295031
theorem B3295037 : Blo 2195435 3295037 := bbase (se 3 (by rfl) ⟨617819, by rfl⟩ : syracuseStep 3295037 = 1235639) (by norm_num)
theorem B2196691 : Blo 2195435 2196691 := bstep (se 1 (by rfl) ⟨1647518, by rfl⟩ : syracuseStep 2196691 = 3295037) B3295037
theorem B4942565 : Blo 2195435 4942565 := bbase (se 4 (by rfl) ⟨463365, by rfl⟩ : syracuseStep 4942565 = 926731) (by norm_num)
theorem B3295043 : Blo 2195435 3295043 := bstep (se 1 (by rfl) ⟨2471282, by rfl⟩ : syracuseStep 3295043 = 4942565) B4942565
theorem B2196695 : Blo 2195435 2196695 := bstep (se 1 (by rfl) ⟨1647521, by rfl⟩ : syracuseStep 2196695 = 3295043) B3295043
theorem B5560397 : Blo 2195435 5560397 := bbase (se 3 (by rfl) ⟨1042574, by rfl⟩ : syracuseStep 5560397 = 2085149) (by norm_num)
theorem B3706931 : Blo 2195435 3706931 := bstep (se 1 (by rfl) ⟨2780198, by rfl⟩ : syracuseStep 3706931 = 5560397) B5560397
theorem B2471287 : Blo 2195435 2471287 := bstep (se 1 (by rfl) ⟨1853465, by rfl⟩ : syracuseStep 2471287 = 3706931) B3706931
theorem B3295049 : Blo 2195435 3295049 := bstep (se 2 (by rfl) ⟨1235643, by rfl⟩ : syracuseStep 3295049 = 2471287) B2471287
theorem B2196699 : Blo 2195435 2196699 := bstep (se 1 (by rfl) ⟨1647524, by rfl⟩ : syracuseStep 2196699 = 3295049) B3295049
theorem B2345797 : Blo 2195435 2345797 := bbase (se 4 (by rfl) ⟨219918, by rfl⟩ : syracuseStep 2345797 = 439837) (by norm_num)
theorem B3127729 : Blo 2195435 3127729 := bstep (se 2 (by rfl) ⟨1172898, by rfl⟩ : syracuseStep 3127729 = 2345797) B2345797
theorem B4170305 : Blo 2195435 4170305 := bstep (se 2 (by rfl) ⟨1563864, by rfl⟩ : syracuseStep 4170305 = 3127729) B3127729
theorem B11120813 : Blo 2195435 11120813 := bstep (se 3 (by rfl) ⟨2085152, by rfl⟩ : syracuseStep 11120813 = 4170305) B4170305
theorem B7413875 : Blo 2195435 7413875 := bstep (se 1 (by rfl) ⟨5560406, by rfl⟩ : syracuseStep 7413875 = 11120813) B11120813
theorem B4942583 : Blo 2195435 4942583 := bstep (se 1 (by rfl) ⟨3706937, by rfl⟩ : syracuseStep 4942583 = 7413875) B7413875
theorem B3295055 : Blo 2195435 3295055 := bstep (se 1 (by rfl) ⟨2471291, by rfl⟩ : syracuseStep 3295055 = 4942583) B4942583
theorem B2196703 : Blo 2195435 2196703 := bstep (se 1 (by rfl) ⟨1647527, by rfl⟩ : syracuseStep 2196703 = 3295055) B3295055
theorem B3295061 : Blo 2195435 3295061 := bbase (se 9 (by rfl) ⟨9653, by rfl⟩ : syracuseStep 3295061 = 19307) (by norm_num)
theorem B2196707 : Blo 2195435 2196707 := bstep (se 1 (by rfl) ⟨1647530, by rfl⟩ : syracuseStep 2196707 = 3295061) B3295061
theorem B20040149 : Blo 2195435 20040149 := bbase (se 7 (by rfl) ⟨234845, by rfl⟩ : syracuseStep 20040149 = 469691) (by norm_num)
theorem B13360099 : Blo 2195435 13360099 := bstep (se 1 (by rfl) ⟨10020074, by rfl⟩ : syracuseStep 13360099 = 20040149) B20040149
theorem B17813465 : Blo 2195435 17813465 := bstep (se 2 (by rfl) ⟨6680049, by rfl⟩ : syracuseStep 17813465 = 13360099) B13360099
theorem B11875643 : Blo 2195435 11875643 := bstep (se 1 (by rfl) ⟨8906732, by rfl⟩ : syracuseStep 11875643 = 17813465) B17813465
theorem B7917095 : Blo 2195435 7917095 := bstep (se 1 (by rfl) ⟨5937821, by rfl⟩ : syracuseStep 7917095 = 11875643) B11875643
theorem B5278063 : Blo 2195435 5278063 := bstep (se 1 (by rfl) ⟨3958547, by rfl⟩ : syracuseStep 5278063 = 7917095) B7917095
theorem B7037417 : Blo 2195435 7037417 := bstep (se 2 (by rfl) ⟨2639031, by rfl⟩ : syracuseStep 7037417 = 5278063) B5278063
theorem B4691611 : Blo 2195435 4691611 := bstep (se 1 (by rfl) ⟨3518708, by rfl⟩ : syracuseStep 4691611 = 7037417) B7037417
theorem B6255481 : Blo 2195435 6255481 := bstep (se 2 (by rfl) ⟨2345805, by rfl⟩ : syracuseStep 6255481 = 4691611) B4691611
theorem B8340641 : Blo 2195435 8340641 := bstep (se 2 (by rfl) ⟨3127740, by rfl⟩ : syracuseStep 8340641 = 6255481) B6255481
theorem B5560427 : Blo 2195435 5560427 := bstep (se 1 (by rfl) ⟨4170320, by rfl⟩ : syracuseStep 5560427 = 8340641) B8340641
theorem B3706951 : Blo 2195435 3706951 := bstep (se 1 (by rfl) ⟨2780213, by rfl⟩ : syracuseStep 3706951 = 5560427) B5560427
theorem B4942601 : Blo 2195435 4942601 := bstep (se 2 (by rfl) ⟨1853475, by rfl⟩ : syracuseStep 4942601 = 3706951) B3706951
theorem B3295067 : Blo 2195435 3295067 := bstep (se 1 (by rfl) ⟨2471300, by rfl⟩ : syracuseStep 3295067 = 4942601) B4942601
theorem B2196711 : Blo 2195435 2196711 := bstep (se 1 (by rfl) ⟨1647533, by rfl⟩ : syracuseStep 2196711 = 3295067) B3295067
theorem B2471305 : Blo 2195435 2471305 := bbase (se 2 (by rfl) ⟨926739, by rfl⟩ : syracuseStep 2471305 = 1853479) (by norm_num)
theorem B3295073 : Blo 2195435 3295073 := bstep (se 2 (by rfl) ⟨1235652, by rfl⟩ : syracuseStep 3295073 = 2471305) B2471305
theorem B2196715 : Blo 2195435 2196715 := bstep (se 1 (by rfl) ⟨1647536, by rfl⟩ : syracuseStep 2196715 = 3295073) B3295073
theorem B17813525 : Blo 2195435 17813525 := bbase (se 6 (by rfl) ⟨417504, by rfl⟩ : syracuseStep 17813525 = 835009) (by norm_num)
theorem B47502733 : Blo 2195435 47502733 := bstep (se 3 (by rfl) ⟨8906762, by rfl⟩ : syracuseStep 47502733 = 17813525) B17813525
theorem B63336977 : Blo 2195435 63336977 := bstep (se 2 (by rfl) ⟨23751366, by rfl⟩ : syracuseStep 63336977 = 47502733) B47502733
theorem B42224651 : Blo 2195435 42224651 := bstep (se 1 (by rfl) ⟨31668488, by rfl⟩ : syracuseStep 42224651 = 63336977) B63336977
theorem B28149767 : Blo 2195435 28149767 := bstep (se 1 (by rfl) ⟨21112325, by rfl⟩ : syracuseStep 28149767 = 42224651) B42224651
theorem B18766511 : Blo 2195435 18766511 := bstep (se 1 (by rfl) ⟨14074883, by rfl⟩ : syracuseStep 18766511 = 28149767) B28149767
theorem B12511007 : Blo 2195435 12511007 := bstep (se 1 (by rfl) ⟨9383255, by rfl⟩ : syracuseStep 12511007 = 18766511) B18766511
theorem B8340671 : Blo 2195435 8340671 := bstep (se 1 (by rfl) ⟨6255503, by rfl⟩ : syracuseStep 8340671 = 12511007) B12511007
theorem B5560447 : Blo 2195435 5560447 := bstep (se 1 (by rfl) ⟨4170335, by rfl⟩ : syracuseStep 5560447 = 8340671) B8340671
theorem B7413929 : Blo 2195435 7413929 := bstep (se 2 (by rfl) ⟨2780223, by rfl⟩ : syracuseStep 7413929 = 5560447) B5560447
theorem B4942619 : Blo 2195435 4942619 := bstep (se 1 (by rfl) ⟨3706964, by rfl⟩ : syracuseStep 4942619 = 7413929) B7413929
theorem B3295079 : Blo 2195435 3295079 := bstep (se 1 (by rfl) ⟨2471309, by rfl⟩ : syracuseStep 3295079 = 4942619) B4942619
theorem B2196719 : Blo 2195435 2196719 := bstep (se 1 (by rfl) ⟨1647539, by rfl⟩ : syracuseStep 2196719 = 3295079) B3295079
theorem B3295085 : Blo 2195435 3295085 := bbase (se 3 (by rfl) ⟨617828, by rfl⟩ : syracuseStep 3295085 = 1235657) (by norm_num)
theorem B2196723 : Blo 2195435 2196723 := bstep (se 1 (by rfl) ⟨1647542, by rfl⟩ : syracuseStep 2196723 = 3295085) B3295085
theorem B4942637 : Blo 2195435 4942637 := bbase (se 3 (by rfl) ⟨926744, by rfl⟩ : syracuseStep 4942637 = 1853489) (by norm_num)
theorem B3295091 : Blo 2195435 3295091 := bstep (se 1 (by rfl) ⟨2471318, by rfl⟩ : syracuseStep 3295091 = 4942637) B4942637
theorem B2196727 : Blo 2195435 2196727 := bstep (se 1 (by rfl) ⟨1647545, by rfl⟩ : syracuseStep 2196727 = 3295091) B3295091
theorem B3518741 : Blo 2195435 3518741 := bbase (se 6 (by rfl) ⟨82470, by rfl⟩ : syracuseStep 3518741 = 164941) (by norm_num)
theorem B9383309 : Blo 2195435 9383309 := bstep (se 3 (by rfl) ⟨1759370, by rfl⟩ : syracuseStep 9383309 = 3518741) B3518741
theorem B6255539 : Blo 2195435 6255539 := bstep (se 1 (by rfl) ⟨4691654, by rfl⟩ : syracuseStep 6255539 = 9383309) B9383309
theorem B4170359 : Blo 2195435 4170359 := bstep (se 1 (by rfl) ⟨3127769, by rfl⟩ : syracuseStep 4170359 = 6255539) B6255539
theorem B2780239 : Blo 2195435 2780239 := bstep (se 1 (by rfl) ⟨2085179, by rfl⟩ : syracuseStep 2780239 = 4170359) B4170359
theorem B3706985 : Blo 2195435 3706985 := bstep (se 2 (by rfl) ⟨1390119, by rfl⟩ : syracuseStep 3706985 = 2780239) B2780239
theorem B2471323 : Blo 2195435 2471323 := bstep (se 1 (by rfl) ⟨1853492, by rfl⟩ : syracuseStep 2471323 = 3706985) B3706985
theorem B3295097 : Blo 2195435 3295097 := bstep (se 2 (by rfl) ⟨1235661, by rfl⟩ : syracuseStep 3295097 = 2471323) B2471323
theorem B2196731 : Blo 2195435 2196731 := bstep (se 1 (by rfl) ⟨1647548, by rfl⟩ : syracuseStep 2196731 = 3295097) B3295097
theorem B10020181 : Blo 2195435 10020181 := bbase (se 12 (by rfl) ⟨3669, by rfl⟩ : syracuseStep 10020181 = 7339) (by norm_num)
theorem B13360241 : Blo 2195435 13360241 := bstep (se 2 (by rfl) ⟨5010090, by rfl⟩ : syracuseStep 13360241 = 10020181) B10020181
theorem B35627309 : Blo 2195435 35627309 := bstep (se 3 (by rfl) ⟨6680120, by rfl⟩ : syracuseStep 35627309 = 13360241) B13360241
theorem B23751539 : Blo 2195435 23751539 := bstep (se 1 (by rfl) ⟨17813654, by rfl⟩ : syracuseStep 23751539 = 35627309) B35627309
theorem B15834359 : Blo 2195435 15834359 := bstep (se 1 (by rfl) ⟨11875769, by rfl⟩ : syracuseStep 15834359 = 23751539) B23751539
theorem B10556239 : Blo 2195435 10556239 := bstep (se 1 (by rfl) ⟨7917179, by rfl⟩ : syracuseStep 10556239 = 15834359) B15834359
theorem B14074985 : Blo 2195435 14074985 := bstep (se 2 (by rfl) ⟨5278119, by rfl⟩ : syracuseStep 14074985 = 10556239) B10556239
theorem B37533293 : Blo 2195435 37533293 := bstep (se 3 (by rfl) ⟨7037492, by rfl⟩ : syracuseStep 37533293 = 14074985) B14074985
theorem B25022195 : Blo 2195435 25022195 := bstep (se 1 (by rfl) ⟨18766646, by rfl⟩ : syracuseStep 25022195 = 37533293) B37533293
theorem B16681463 : Blo 2195435 16681463 := bstep (se 1 (by rfl) ⟨12511097, by rfl⟩ : syracuseStep 16681463 = 25022195) B25022195
theorem B11120975 : Blo 2195435 11120975 := bstep (se 1 (by rfl) ⟨8340731, by rfl⟩ : syracuseStep 11120975 = 16681463) B16681463
theorem B7413983 : Blo 2195435 7413983 := bstep (se 1 (by rfl) ⟨5560487, by rfl⟩ : syracuseStep 7413983 = 11120975) B11120975
theorem B4942655 : Blo 2195435 4942655 := bstep (se 1 (by rfl) ⟨3706991, by rfl⟩ : syracuseStep 4942655 = 7413983) B7413983
theorem B3295103 : Blo 2195435 3295103 := bstep (se 1 (by rfl) ⟨2471327, by rfl⟩ : syracuseStep 3295103 = 4942655) B4942655
theorem B2196735 : Blo 2195435 2196735 := bstep (se 1 (by rfl) ⟨1647551, by rfl⟩ : syracuseStep 2196735 = 3295103) B3295103
theorem B3295109 : Blo 2195435 3295109 := bbase (se 4 (by rfl) ⟨308916, by rfl⟩ : syracuseStep 3295109 = 617833) (by norm_num)
theorem B2196739 : Blo 2195435 2196739 := bstep (se 1 (by rfl) ⟨1647554, by rfl⟩ : syracuseStep 2196739 = 3295109) B3295109
theorem B3707005 : Blo 2195435 3707005 := bbase (se 3 (by rfl) ⟨695063, by rfl⟩ : syracuseStep 3707005 = 1390127) (by norm_num)
theorem B4942673 : Blo 2195435 4942673 := bstep (se 2 (by rfl) ⟨1853502, by rfl⟩ : syracuseStep 4942673 = 3707005) B3707005
theorem B3295115 : Blo 2195435 3295115 := bstep (se 1 (by rfl) ⟨2471336, by rfl⟩ : syracuseStep 3295115 = 4942673) B4942673
theorem B2196743 : Blo 2195435 2196743 := bstep (se 1 (by rfl) ⟨1647557, by rfl⟩ : syracuseStep 2196743 = 3295115) B3295115
theorem B2471341 : Blo 2195435 2471341 := bbase (se 3 (by rfl) ⟨463376, by rfl⟩ : syracuseStep 2471341 = 926753) (by norm_num)
theorem B3295121 : Blo 2195435 3295121 := bstep (se 2 (by rfl) ⟨1235670, by rfl⟩ : syracuseStep 3295121 = 2471341) B2471341
theorem B2196747 : Blo 2195435 2196747 := bstep (se 1 (by rfl) ⟨1647560, by rfl⟩ : syracuseStep 2196747 = 3295121) B3295121
theorem B7414037 : Blo 2195435 7414037 := bbase (se 6 (by rfl) ⟨173766, by rfl⟩ : syracuseStep 7414037 = 347533) (by norm_num)
theorem B4942691 : Blo 2195435 4942691 := bstep (se 1 (by rfl) ⟨3707018, by rfl⟩ : syracuseStep 4942691 = 7414037) B7414037
theorem B3295127 : Blo 2195435 3295127 := bstep (se 1 (by rfl) ⟨2471345, by rfl⟩ : syracuseStep 3295127 = 4942691) B4942691
theorem B2196751 : Blo 2195435 2196751 := bstep (se 1 (by rfl) ⟨1647563, by rfl⟩ : syracuseStep 2196751 = 3295127) B3295127
theorem B3295133 : Blo 2195435 3295133 := bbase (se 3 (by rfl) ⟨617837, by rfl⟩ : syracuseStep 3295133 = 1235675) (by norm_num)
theorem B2196755 : Blo 2195435 2196755 := bstep (se 1 (by rfl) ⟨1647566, by rfl⟩ : syracuseStep 2196755 = 3295133) B3295133
theorem B4942709 : Blo 2195435 4942709 := bbase (se 5 (by rfl) ⟨231689, by rfl⟩ : syracuseStep 4942709 = 463379) (by norm_num)
theorem B3295139 : Blo 2195435 3295139 := bstep (se 1 (by rfl) ⟨2471354, by rfl⟩ : syracuseStep 3295139 = 4942709) B4942709
theorem B2196759 : Blo 2195435 2196759 := bstep (se 1 (by rfl) ⟨1647569, by rfl⟩ : syracuseStep 2196759 = 3295139) B3295139
theorem B2675101 : Blo 2195435 2675101 := bbase (se 3 (by rfl) ⟨501581, by rfl⟩ : syracuseStep 2675101 = 1003163) (by norm_num)
theorem B3566801 : Blo 2195435 3566801 := bstep (se 2 (by rfl) ⟨1337550, by rfl⟩ : syracuseStep 3566801 = 2675101) B2675101
theorem B9511469 : Blo 2195435 9511469 := bstep (se 3 (by rfl) ⟨1783400, by rfl⟩ : syracuseStep 9511469 = 3566801) B3566801
theorem B6340979 : Blo 2195435 6340979 := bstep (se 1 (by rfl) ⟨4755734, by rfl⟩ : syracuseStep 6340979 = 9511469) B9511469
theorem B4227319 : Blo 2195435 4227319 := bstep (se 1 (by rfl) ⟨3170489, by rfl⟩ : syracuseStep 4227319 = 6340979) B6340979
theorem B5636425 : Blo 2195435 5636425 := bstep (se 2 (by rfl) ⟨2113659, by rfl⟩ : syracuseStep 5636425 = 4227319) B4227319
theorem B7515233 : Blo 2195435 7515233 := bstep (se 2 (by rfl) ⟨2818212, by rfl⟩ : syracuseStep 7515233 = 5636425) B5636425
theorem B5010155 : Blo 2195435 5010155 := bstep (se 1 (by rfl) ⟨3757616, by rfl⟩ : syracuseStep 5010155 = 7515233) B7515233
theorem B53441653 : Blo 2195435 53441653 := bstep (se 5 (by rfl) ⟨2505077, by rfl⟩ : syracuseStep 53441653 = 5010155) B5010155
theorem B71255537 : Blo 2195435 71255537 := bstep (se 2 (by rfl) ⟨26720826, by rfl⟩ : syracuseStep 71255537 = 53441653) B53441653
theorem B47503691 : Blo 2195435 47503691 := bstep (se 1 (by rfl) ⟨35627768, by rfl⟩ : syracuseStep 47503691 = 71255537) B71255537
theorem B31669127 : Blo 2195435 31669127 := bstep (se 1 (by rfl) ⟨23751845, by rfl⟩ : syracuseStep 31669127 = 47503691) B47503691
theorem B21112751 : Blo 2195435 21112751 := bstep (se 1 (by rfl) ⟨15834563, by rfl⟩ : syracuseStep 21112751 = 31669127) B31669127
theorem B14075167 : Blo 2195435 14075167 := bstep (se 1 (by rfl) ⟨10556375, by rfl⟩ : syracuseStep 14075167 = 21112751) B21112751
theorem B18766889 : Blo 2195435 18766889 := bstep (se 2 (by rfl) ⟨7037583, by rfl⟩ : syracuseStep 18766889 = 14075167) B14075167
theorem B12511259 : Blo 2195435 12511259 := bstep (se 1 (by rfl) ⟨9383444, by rfl⟩ : syracuseStep 12511259 = 18766889) B18766889
theorem B8340839 : Blo 2195435 8340839 := bstep (se 1 (by rfl) ⟨6255629, by rfl⟩ : syracuseStep 8340839 = 12511259) B12511259
theorem B5560559 : Blo 2195435 5560559 := bstep (se 1 (by rfl) ⟨4170419, by rfl⟩ : syracuseStep 5560559 = 8340839) B8340839
theorem B3707039 : Blo 2195435 3707039 := bstep (se 1 (by rfl) ⟨2780279, by rfl⟩ : syracuseStep 3707039 = 5560559) B5560559
theorem B2471359 : Blo 2195435 2471359 := bstep (se 1 (by rfl) ⟨1853519, by rfl⟩ : syracuseStep 2471359 = 3707039) B3707039
theorem B3295145 : Blo 2195435 3295145 := bstep (se 2 (by rfl) ⟨1235679, by rfl⟩ : syracuseStep 3295145 = 2471359) B2471359
theorem B2196763 : Blo 2195435 2196763 := bstep (se 1 (by rfl) ⟨1647572, by rfl⟩ : syracuseStep 2196763 = 3295145) B3295145
theorem B8340853 : Blo 2195435 8340853 := bbase (se 5 (by rfl) ⟨390977, by rfl⟩ : syracuseStep 8340853 = 781955) (by norm_num)
theorem B11121137 : Blo 2195435 11121137 := bstep (se 2 (by rfl) ⟨4170426, by rfl⟩ : syracuseStep 11121137 = 8340853) B8340853
theorem B7414091 : Blo 2195435 7414091 := bstep (se 1 (by rfl) ⟨5560568, by rfl⟩ : syracuseStep 7414091 = 11121137) B11121137
theorem B4942727 : Blo 2195435 4942727 := bstep (se 1 (by rfl) ⟨3707045, by rfl⟩ : syracuseStep 4942727 = 7414091) B7414091
theorem B3295151 : Blo 2195435 3295151 := bstep (se 1 (by rfl) ⟨2471363, by rfl⟩ : syracuseStep 3295151 = 4942727) B4942727
theorem B2196767 : Blo 2195435 2196767 := bstep (se 1 (by rfl) ⟨1647575, by rfl⟩ : syracuseStep 2196767 = 3295151) B3295151
theorem B3295157 : Blo 2195435 3295157 := bbase (se 5 (by rfl) ⟨154460, by rfl⟩ : syracuseStep 3295157 = 308921) (by norm_num)
theorem B2196771 : Blo 2195435 2196771 := bstep (se 1 (by rfl) ⟨1647578, by rfl⟩ : syracuseStep 2196771 = 3295157) B3295157
theorem B5560589 : Blo 2195435 5560589 := bbase (se 3 (by rfl) ⟨1042610, by rfl⟩ : syracuseStep 5560589 = 2085221) (by norm_num)
theorem B3707059 : Blo 2195435 3707059 := bstep (se 1 (by rfl) ⟨2780294, by rfl⟩ : syracuseStep 3707059 = 5560589) B5560589
theorem B4942745 : Blo 2195435 4942745 := bstep (se 2 (by rfl) ⟨1853529, by rfl⟩ : syracuseStep 4942745 = 3707059) B3707059
theorem B3295163 : Blo 2195435 3295163 := bstep (se 1 (by rfl) ⟨2471372, by rfl⟩ : syracuseStep 3295163 = 4942745) B4942745
theorem B2196775 : Blo 2195435 2196775 := bstep (se 1 (by rfl) ⟨1647581, by rfl⟩ : syracuseStep 2196775 = 3295163) B3295163
theorem B2471377 : Blo 2195435 2471377 := bbase (se 2 (by rfl) ⟨926766, by rfl⟩ : syracuseStep 2471377 = 1853533) (by norm_num)
theorem B3295169 : Blo 2195435 3295169 := bstep (se 2 (by rfl) ⟨1235688, by rfl⟩ : syracuseStep 3295169 = 2471377) B2471377
theorem B2196779 : Blo 2195435 2196779 := bstep (se 1 (by rfl) ⟨1647584, by rfl⟩ : syracuseStep 2196779 = 3295169) B3295169
theorem B4691765 : Blo 2195435 4691765 := bbase (se 5 (by rfl) ⟨219926, by rfl⟩ : syracuseStep 4691765 = 439853) (by norm_num)
theorem B3127843 : Blo 2195435 3127843 := bstep (se 1 (by rfl) ⟨2345882, by rfl⟩ : syracuseStep 3127843 = 4691765) B4691765
theorem B4170457 : Blo 2195435 4170457 := bstep (se 2 (by rfl) ⟨1563921, by rfl⟩ : syracuseStep 4170457 = 3127843) B3127843
theorem B5560609 : Blo 2195435 5560609 := bstep (se 2 (by rfl) ⟨2085228, by rfl⟩ : syracuseStep 5560609 = 4170457) B4170457
theorem B7414145 : Blo 2195435 7414145 := bstep (se 2 (by rfl) ⟨2780304, by rfl⟩ : syracuseStep 7414145 = 5560609) B5560609
theorem B4942763 : Blo 2195435 4942763 := bstep (se 1 (by rfl) ⟨3707072, by rfl⟩ : syracuseStep 4942763 = 7414145) B7414145
theorem B3295175 : Blo 2195435 3295175 := bstep (se 1 (by rfl) ⟨2471381, by rfl⟩ : syracuseStep 3295175 = 4942763) B4942763
theorem B2196783 : Blo 2195435 2196783 := bstep (se 1 (by rfl) ⟨1647587, by rfl⟩ : syracuseStep 2196783 = 3295175) B3295175
theorem B3295181 : Blo 2195435 3295181 := bbase (se 3 (by rfl) ⟨617846, by rfl⟩ : syracuseStep 3295181 = 1235693) (by norm_num)
theorem B2196787 : Blo 2195435 2196787 := bstep (se 1 (by rfl) ⟨1647590, by rfl⟩ : syracuseStep 2196787 = 3295181) B3295181
theorem B4942781 : Blo 2195435 4942781 := bbase (se 3 (by rfl) ⟨926771, by rfl⟩ : syracuseStep 4942781 = 1853543) (by norm_num)
theorem B3295187 : Blo 2195435 3295187 := bstep (se 1 (by rfl) ⟨2471390, by rfl⟩ : syracuseStep 3295187 = 4942781) B4942781
theorem B2196791 : Blo 2195435 2196791 := bstep (se 1 (by rfl) ⟨1647593, by rfl⟩ : syracuseStep 2196791 = 3295187) B3295187
theorem B3707093 : Blo 2195435 3707093 := bbase (se 7 (by rfl) ⟨43442, by rfl⟩ : syracuseStep 3707093 = 86885) (by norm_num)
theorem B2471395 : Blo 2195435 2471395 := bstep (se 1 (by rfl) ⟨1853546, by rfl⟩ : syracuseStep 2471395 = 3707093) B3707093
theorem B3295193 : Blo 2195435 3295193 := bstep (se 2 (by rfl) ⟨1235697, by rfl⟩ : syracuseStep 3295193 = 2471395) B2471395
theorem B2196795 : Blo 2195435 2196795 := bstep (se 1 (by rfl) ⟨1647596, by rfl⟩ : syracuseStep 2196795 = 3295193) B3295193
theorem B2639137 : Blo 2195435 2639137 := bbase (se 2 (by rfl) ⟨989676, by rfl⟩ : syracuseStep 2639137 = 1979353) (by norm_num)
theorem B3518849 : Blo 2195435 3518849 := bstep (se 2 (by rfl) ⟨1319568, by rfl⟩ : syracuseStep 3518849 = 2639137) B2639137
theorem B9383597 : Blo 2195435 9383597 := bstep (se 3 (by rfl) ⟨1759424, by rfl⟩ : syracuseStep 9383597 = 3518849) B3518849
theorem B6255731 : Blo 2195435 6255731 := bstep (se 1 (by rfl) ⟨4691798, by rfl⟩ : syracuseStep 6255731 = 9383597) B9383597
theorem B16681949 : Blo 2195435 16681949 := bstep (se 3 (by rfl) ⟨3127865, by rfl⟩ : syracuseStep 16681949 = 6255731) B6255731
theorem B11121299 : Blo 2195435 11121299 := bstep (se 1 (by rfl) ⟨8340974, by rfl⟩ : syracuseStep 11121299 = 16681949) B16681949
theorem B7414199 : Blo 2195435 7414199 := bstep (se 1 (by rfl) ⟨5560649, by rfl⟩ : syracuseStep 7414199 = 11121299) B11121299
theorem B4942799 : Blo 2195435 4942799 := bstep (se 1 (by rfl) ⟨3707099, by rfl⟩ : syracuseStep 4942799 = 7414199) B7414199
theorem B3295199 : Blo 2195435 3295199 := bstep (se 1 (by rfl) ⟨2471399, by rfl⟩ : syracuseStep 3295199 = 4942799) B4942799
theorem B2196799 : Blo 2195435 2196799 := bstep (se 1 (by rfl) ⟨1647599, by rfl⟩ : syracuseStep 2196799 = 3295199) B3295199
theorem B3295205 : Blo 2195435 3295205 := bbase (se 4 (by rfl) ⟨308925, by rfl⟩ : syracuseStep 3295205 = 617851) (by norm_num)
theorem B2196803 : Blo 2195435 2196803 := bstep (se 1 (by rfl) ⟨1647602, by rfl⟩ : syracuseStep 2196803 = 3295205) B3295205
theorem B2226781 : Blo 2195435 2226781 := bbase (se 3 (by rfl) ⟨417521, by rfl⟩ : syracuseStep 2226781 = 835043) (by norm_num)
theorem B2969041 : Blo 2195435 2969041 := bstep (se 2 (by rfl) ⟨1113390, by rfl⟩ : syracuseStep 2969041 = 2226781) B2226781
theorem B3958721 : Blo 2195435 3958721 := bstep (se 2 (by rfl) ⟨1484520, by rfl⟩ : syracuseStep 3958721 = 2969041) B2969041
theorem B2639147 : Blo 2195435 2639147 := bstep (se 1 (by rfl) ⟨1979360, by rfl⟩ : syracuseStep 2639147 = 3958721) B3958721
theorem B7037725 : Blo 2195435 7037725 := bstep (se 3 (by rfl) ⟨1319573, by rfl⟩ : syracuseStep 7037725 = 2639147) B2639147
theorem B9383633 : Blo 2195435 9383633 := bstep (se 2 (by rfl) ⟨3518862, by rfl⟩ : syracuseStep 9383633 = 7037725) B7037725
theorem B6255755 : Blo 2195435 6255755 := bstep (se 1 (by rfl) ⟨4691816, by rfl⟩ : syracuseStep 6255755 = 9383633) B9383633
theorem B4170503 : Blo 2195435 4170503 := bstep (se 1 (by rfl) ⟨3127877, by rfl⟩ : syracuseStep 4170503 = 6255755) B6255755
theorem B2780335 : Blo 2195435 2780335 := bstep (se 1 (by rfl) ⟨2085251, by rfl⟩ : syracuseStep 2780335 = 4170503) B4170503
theorem B3707113 : Blo 2195435 3707113 := bstep (se 2 (by rfl) ⟨1390167, by rfl⟩ : syracuseStep 3707113 = 2780335) B2780335
theorem B4942817 : Blo 2195435 4942817 := bstep (se 2 (by rfl) ⟨1853556, by rfl⟩ : syracuseStep 4942817 = 3707113) B3707113
theorem B3295211 : Blo 2195435 3295211 := bstep (se 1 (by rfl) ⟨2471408, by rfl⟩ : syracuseStep 3295211 = 4942817) B4942817
theorem B2196807 : Blo 2195435 2196807 := bstep (se 1 (by rfl) ⟨1647605, by rfl⟩ : syracuseStep 2196807 = 3295211) B3295211
theorem B2471413 : Blo 2195435 2471413 := bbase (se 5 (by rfl) ⟨115847, by rfl⟩ : syracuseStep 2471413 = 231695) (by norm_num)
theorem B3295217 : Blo 2195435 3295217 := bstep (se 2 (by rfl) ⟨1235706, by rfl⟩ : syracuseStep 3295217 = 2471413) B2471413
theorem B2196811 : Blo 2195435 2196811 := bstep (se 1 (by rfl) ⟨1647608, by rfl⟩ : syracuseStep 2196811 = 3295217) B3295217
theorem B2780345 : Blo 2195435 2780345 := bbase (se 2 (by rfl) ⟨1042629, by rfl⟩ : syracuseStep 2780345 = 2085259) (by norm_num)
theorem B7414253 : Blo 2195435 7414253 := bstep (se 3 (by rfl) ⟨1390172, by rfl⟩ : syracuseStep 7414253 = 2780345) B2780345
theorem B4942835 : Blo 2195435 4942835 := bstep (se 1 (by rfl) ⟨3707126, by rfl⟩ : syracuseStep 4942835 = 7414253) B7414253
theorem B3295223 : Blo 2195435 3295223 := bstep (se 1 (by rfl) ⟨2471417, by rfl⟩ : syracuseStep 3295223 = 4942835) B4942835
theorem B2196815 : Blo 2195435 2196815 := bstep (se 1 (by rfl) ⟨1647611, by rfl⟩ : syracuseStep 2196815 = 3295223) B3295223
theorem B3295229 : Blo 2195435 3295229 := bbase (se 3 (by rfl) ⟨617855, by rfl⟩ : syracuseStep 3295229 = 1235711) (by norm_num)
theorem B2196819 : Blo 2195435 2196819 := bstep (se 1 (by rfl) ⟨1647614, by rfl⟩ : syracuseStep 2196819 = 3295229) B3295229
theorem B4942853 : Blo 2195435 4942853 := bbase (se 4 (by rfl) ⟨463392, by rfl⟩ : syracuseStep 4942853 = 926785) (by norm_num)
theorem B3295235 : Blo 2195435 3295235 := bstep (se 1 (by rfl) ⟨2471426, by rfl⟩ : syracuseStep 3295235 = 4942853) B4942853
theorem B2196823 : Blo 2195435 2196823 := bstep (se 1 (by rfl) ⟨1647617, by rfl⟩ : syracuseStep 2196823 = 3295235) B3295235
theorem B4170541 : Blo 2195435 4170541 := bbase (se 3 (by rfl) ⟨781976, by rfl⟩ : syracuseStep 4170541 = 1563953) (by norm_num)
theorem B5560721 : Blo 2195435 5560721 := bstep (se 2 (by rfl) ⟨2085270, by rfl⟩ : syracuseStep 5560721 = 4170541) B4170541
theorem B3707147 : Blo 2195435 3707147 := bstep (se 1 (by rfl) ⟨2780360, by rfl⟩ : syracuseStep 3707147 = 5560721) B5560721
theorem B2471431 : Blo 2195435 2471431 := bstep (se 1 (by rfl) ⟨1853573, by rfl⟩ : syracuseStep 2471431 = 3707147) B3707147
theorem B3295241 : Blo 2195435 3295241 := bstep (se 2 (by rfl) ⟨1235715, by rfl⟩ : syracuseStep 3295241 = 2471431) B2471431
theorem B2196827 : Blo 2195435 2196827 := bstep (se 1 (by rfl) ⟨1647620, by rfl⟩ : syracuseStep 2196827 = 3295241) B3295241
theorem B11121461 : Blo 2195435 11121461 := bbase (se 5 (by rfl) ⟨521318, by rfl⟩ : syracuseStep 11121461 = 1042637) (by norm_num)
theorem B7414307 : Blo 2195435 7414307 := bstep (se 1 (by rfl) ⟨5560730, by rfl⟩ : syracuseStep 7414307 = 11121461) B11121461
theorem B4942871 : Blo 2195435 4942871 := bstep (se 1 (by rfl) ⟨3707153, by rfl⟩ : syracuseStep 4942871 = 7414307) B7414307
theorem B3295247 : Blo 2195435 3295247 := bstep (se 1 (by rfl) ⟨2471435, by rfl⟩ : syracuseStep 3295247 = 4942871) B4942871
theorem B2196831 : Blo 2195435 2196831 := bstep (se 1 (by rfl) ⟨1647623, by rfl⟩ : syracuseStep 2196831 = 3295247) B3295247
theorem B3295253 : Blo 2195435 3295253 := bbase (se 6 (by rfl) ⟨77232, by rfl⟩ : syracuseStep 3295253 = 154465) (by norm_num)
theorem B2196835 : Blo 2195435 2196835 := bstep (se 1 (by rfl) ⟨1647626, by rfl⟩ : syracuseStep 2196835 = 3295253) B3295253
theorem B2639185 : Blo 2195435 2639185 := bbase (se 2 (by rfl) ⟨989694, by rfl⟩ : syracuseStep 2639185 = 1979389) (by norm_num)
theorem B14075653 : Blo 2195435 14075653 := bstep (se 4 (by rfl) ⟨1319592, by rfl⟩ : syracuseStep 14075653 = 2639185) B2639185
theorem B18767537 : Blo 2195435 18767537 := bstep (se 2 (by rfl) ⟨7037826, by rfl⟩ : syracuseStep 18767537 = 14075653) B14075653
theorem B12511691 : Blo 2195435 12511691 := bstep (se 1 (by rfl) ⟨9383768, by rfl⟩ : syracuseStep 12511691 = 18767537) B18767537
theorem B8341127 : Blo 2195435 8341127 := bstep (se 1 (by rfl) ⟨6255845, by rfl⟩ : syracuseStep 8341127 = 12511691) B12511691
theorem B5560751 : Blo 2195435 5560751 := bstep (se 1 (by rfl) ⟨4170563, by rfl⟩ : syracuseStep 5560751 = 8341127) B8341127
theorem B3707167 : Blo 2195435 3707167 := bstep (se 1 (by rfl) ⟨2780375, by rfl⟩ : syracuseStep 3707167 = 5560751) B5560751
theorem B4942889 : Blo 2195435 4942889 := bstep (se 2 (by rfl) ⟨1853583, by rfl⟩ : syracuseStep 4942889 = 3707167) B3707167
theorem B3295259 : Blo 2195435 3295259 := bstep (se 1 (by rfl) ⟨2471444, by rfl⟩ : syracuseStep 3295259 = 4942889) B4942889
theorem B2196839 : Blo 2195435 2196839 := bstep (se 1 (by rfl) ⟨1647629, by rfl⟩ : syracuseStep 2196839 = 3295259) B3295259
theorem B2471449 : Blo 2195435 2471449 := bbase (se 2 (by rfl) ⟨926793, by rfl⟩ : syracuseStep 2471449 = 1853587) (by norm_num)
theorem B3295265 : Blo 2195435 3295265 := bstep (se 2 (by rfl) ⟨1235724, by rfl⟩ : syracuseStep 3295265 = 2471449) B2471449
theorem B2196843 : Blo 2195435 2196843 := bstep (se 1 (by rfl) ⟨1647632, by rfl⟩ : syracuseStep 2196843 = 3295265) B3295265
theorem B8341157 : Blo 2195435 8341157 := bbase (se 4 (by rfl) ⟨781983, by rfl⟩ : syracuseStep 8341157 = 1563967) (by norm_num)
theorem B5560771 : Blo 2195435 5560771 := bstep (se 1 (by rfl) ⟨4170578, by rfl⟩ : syracuseStep 5560771 = 8341157) B8341157
theorem B7414361 : Blo 2195435 7414361 := bstep (se 2 (by rfl) ⟨2780385, by rfl⟩ : syracuseStep 7414361 = 5560771) B5560771
theorem B4942907 : Blo 2195435 4942907 := bstep (se 1 (by rfl) ⟨3707180, by rfl⟩ : syracuseStep 4942907 = 7414361) B7414361
theorem B3295271 : Blo 2195435 3295271 := bstep (se 1 (by rfl) ⟨2471453, by rfl⟩ : syracuseStep 3295271 = 4942907) B4942907
theorem B2196847 : Blo 2195435 2196847 := bstep (se 1 (by rfl) ⟨1647635, by rfl⟩ : syracuseStep 2196847 = 3295271) B3295271
theorem B3295277 : Blo 2195435 3295277 := bbase (se 3 (by rfl) ⟨617864, by rfl⟩ : syracuseStep 3295277 = 1235729) (by norm_num)
theorem B2196851 : Blo 2195435 2196851 := bstep (se 1 (by rfl) ⟨1647638, by rfl⟩ : syracuseStep 2196851 = 3295277) B3295277
theorem B4942925 : Blo 2195435 4942925 := bbase (se 3 (by rfl) ⟨926798, by rfl⟩ : syracuseStep 4942925 = 1853597) (by norm_num)
theorem B3295283 : Blo 2195435 3295283 := bstep (se 1 (by rfl) ⟨2471462, by rfl⟩ : syracuseStep 3295283 = 4942925) B4942925
theorem B2196855 : Blo 2195435 2196855 := bstep (se 1 (by rfl) ⟨1647641, by rfl⟩ : syracuseStep 2196855 = 3295283) B3295283
theorem B2780401 : Blo 2195435 2780401 := bbase (se 2 (by rfl) ⟨1042650, by rfl⟩ : syracuseStep 2780401 = 2085301) (by norm_num)
theorem B3707201 : Blo 2195435 3707201 := bstep (se 2 (by rfl) ⟨1390200, by rfl⟩ : syracuseStep 3707201 = 2780401) B2780401
theorem B2471467 : Blo 2195435 2471467 := bstep (se 1 (by rfl) ⟨1853600, by rfl⟩ : syracuseStep 2471467 = 3707201) B3707201
theorem B3295289 : Blo 2195435 3295289 := bstep (se 2 (by rfl) ⟨1235733, by rfl⟩ : syracuseStep 3295289 = 2471467) B2471467
theorem B2196859 : Blo 2195435 2196859 := bstep (se 1 (by rfl) ⟨1647644, by rfl⟩ : syracuseStep 2196859 = 3295289) B3295289
theorem B5350445 : Blo 2195435 5350445 := bbase (se 3 (by rfl) ⟨1003208, by rfl⟩ : syracuseStep 5350445 = 2006417) (by norm_num)
theorem B3566963 : Blo 2195435 3566963 := bstep (se 1 (by rfl) ⟨2675222, by rfl⟩ : syracuseStep 3566963 = 5350445) B5350445
theorem B9511901 : Blo 2195435 9511901 := bstep (se 3 (by rfl) ⟨1783481, by rfl⟩ : syracuseStep 9511901 = 3566963) B3566963
theorem B6341267 : Blo 2195435 6341267 := bstep (se 1 (by rfl) ⟨4755950, by rfl⟩ : syracuseStep 6341267 = 9511901) B9511901
theorem B16910045 : Blo 2195435 16910045 := bstep (se 3 (by rfl) ⟨3170633, by rfl⟩ : syracuseStep 16910045 = 6341267) B6341267
theorem B11273363 : Blo 2195435 11273363 := bstep (se 1 (by rfl) ⟨8455022, by rfl⟩ : syracuseStep 11273363 = 16910045) B16910045
theorem B7515575 : Blo 2195435 7515575 := bstep (se 1 (by rfl) ⟨5636681, by rfl⟩ : syracuseStep 7515575 = 11273363) B11273363
theorem B5010383 : Blo 2195435 5010383 := bstep (se 1 (by rfl) ⟨3757787, by rfl⟩ : syracuseStep 5010383 = 7515575) B7515575
theorem B13361021 : Blo 2195435 13361021 := bstep (se 3 (by rfl) ⟨2505191, by rfl⟩ : syracuseStep 13361021 = 5010383) B5010383
theorem B8907347 : Blo 2195435 8907347 := bstep (se 1 (by rfl) ⟨6680510, by rfl⟩ : syracuseStep 8907347 = 13361021) B13361021
theorem B23752925 : Blo 2195435 23752925 := bstep (se 3 (by rfl) ⟨4453673, by rfl⟩ : syracuseStep 23752925 = 8907347) B8907347
theorem B15835283 : Blo 2195435 15835283 := bstep (se 1 (by rfl) ⟨11876462, by rfl⟩ : syracuseStep 15835283 = 23752925) B23752925
theorem B10556855 : Blo 2195435 10556855 := bstep (se 1 (by rfl) ⟨7917641, by rfl⟩ : syracuseStep 10556855 = 15835283) B15835283
theorem B7037903 : Blo 2195435 7037903 := bstep (se 1 (by rfl) ⟨5278427, by rfl⟩ : syracuseStep 7037903 = 10556855) B10556855
theorem B4691935 : Blo 2195435 4691935 := bstep (se 1 (by rfl) ⟨3518951, by rfl⟩ : syracuseStep 4691935 = 7037903) B7037903
theorem B25023653 : Blo 2195435 25023653 := bstep (se 4 (by rfl) ⟨2345967, by rfl⟩ : syracuseStep 25023653 = 4691935) B4691935
theorem B16682435 : Blo 2195435 16682435 := bstep (se 1 (by rfl) ⟨12511826, by rfl⟩ : syracuseStep 16682435 = 25023653) B25023653
theorem B11121623 : Blo 2195435 11121623 := bstep (se 1 (by rfl) ⟨8341217, by rfl⟩ : syracuseStep 11121623 = 16682435) B16682435
theorem B7414415 : Blo 2195435 7414415 := bstep (se 1 (by rfl) ⟨5560811, by rfl⟩ : syracuseStep 7414415 = 11121623) B11121623
theorem B4942943 : Blo 2195435 4942943 := bstep (se 1 (by rfl) ⟨3707207, by rfl⟩ : syracuseStep 4942943 = 7414415) B7414415
theorem B3295295 : Blo 2195435 3295295 := bstep (se 1 (by rfl) ⟨2471471, by rfl⟩ : syracuseStep 3295295 = 4942943) B4942943
theorem B2196863 : Blo 2195435 2196863 := bstep (se 1 (by rfl) ⟨1647647, by rfl⟩ : syracuseStep 2196863 = 3295295) B3295295
theorem B3295301 : Blo 2195435 3295301 := bbase (se 4 (by rfl) ⟨308934, by rfl⟩ : syracuseStep 3295301 = 617869) (by norm_num)
theorem B2196867 : Blo 2195435 2196867 := bstep (se 1 (by rfl) ⟨1647650, by rfl⟩ : syracuseStep 2196867 = 3295301) B3295301
theorem B3707221 : Blo 2195435 3707221 := bbase (se 10 (by rfl) ⟨5430, by rfl⟩ : syracuseStep 3707221 = 10861) (by norm_num)
theorem B4942961 : Blo 2195435 4942961 := bstep (se 2 (by rfl) ⟨1853610, by rfl⟩ : syracuseStep 4942961 = 3707221) B3707221
theorem B3295307 : Blo 2195435 3295307 := bstep (se 1 (by rfl) ⟨2471480, by rfl⟩ : syracuseStep 3295307 = 4942961) B4942961
theorem B2196871 : Blo 2195435 2196871 := bstep (se 1 (by rfl) ⟨1647653, by rfl⟩ : syracuseStep 2196871 = 3295307) B3295307
theorem B2471485 : Blo 2195435 2471485 := bbase (se 3 (by rfl) ⟨463403, by rfl⟩ : syracuseStep 2471485 = 926807) (by norm_num)
theorem B3295313 : Blo 2195435 3295313 := bstep (se 2 (by rfl) ⟨1235742, by rfl⟩ : syracuseStep 3295313 = 2471485) B2471485
theorem B2196875 : Blo 2195435 2196875 := bstep (se 1 (by rfl) ⟨1647656, by rfl⟩ : syracuseStep 2196875 = 3295313) B3295313
theorem B7414469 : Blo 2195435 7414469 := bbase (se 4 (by rfl) ⟨695106, by rfl⟩ : syracuseStep 7414469 = 1390213) (by norm_num)
theorem B4942979 : Blo 2195435 4942979 := bstep (se 1 (by rfl) ⟨3707234, by rfl⟩ : syracuseStep 4942979 = 7414469) B7414469
theorem B3295319 : Blo 2195435 3295319 := bstep (se 1 (by rfl) ⟨2471489, by rfl⟩ : syracuseStep 3295319 = 4942979) B4942979
theorem B2196879 : Blo 2195435 2196879 := bstep (se 1 (by rfl) ⟨1647659, by rfl⟩ : syracuseStep 2196879 = 3295319) B3295319
theorem B3295325 : Blo 2195435 3295325 := bbase (se 3 (by rfl) ⟨617873, by rfl⟩ : syracuseStep 3295325 = 1235747) (by norm_num)
theorem B2196883 : Blo 2195435 2196883 := bstep (se 1 (by rfl) ⟨1647662, by rfl⟩ : syracuseStep 2196883 = 3295325) B3295325
theorem B4942997 : Blo 2195435 4942997 := bbase (se 6 (by rfl) ⟨115851, by rfl⟩ : syracuseStep 4942997 = 231703) (by norm_num)
theorem B3295331 : Blo 2195435 3295331 := bstep (se 1 (by rfl) ⟨2471498, by rfl⟩ : syracuseStep 3295331 = 4942997) B4942997
theorem B2196887 : Blo 2195435 2196887 := bstep (se 1 (by rfl) ⟨1647665, by rfl⟩ : syracuseStep 2196887 = 3295331) B3295331
theorem B3127997 : Blo 2195435 3127997 := bbase (se 3 (by rfl) ⟨586499, by rfl⟩ : syracuseStep 3127997 = 1172999) (by norm_num)
theorem B8341325 : Blo 2195435 8341325 := bstep (se 3 (by rfl) ⟨1563998, by rfl⟩ : syracuseStep 8341325 = 3127997) B3127997
theorem B5560883 : Blo 2195435 5560883 := bstep (se 1 (by rfl) ⟨4170662, by rfl⟩ : syracuseStep 5560883 = 8341325) B8341325
theorem B3707255 : Blo 2195435 3707255 := bstep (se 1 (by rfl) ⟨2780441, by rfl⟩ : syracuseStep 3707255 = 5560883) B5560883
theorem B2471503 : Blo 2195435 2471503 := bstep (se 1 (by rfl) ⟨1853627, by rfl⟩ : syracuseStep 2471503 = 3707255) B3707255
theorem B3295337 : Blo 2195435 3295337 := bstep (se 2 (by rfl) ⟨1235751, by rfl⟩ : syracuseStep 3295337 = 2471503) B2471503
theorem B2196891 : Blo 2195435 2196891 := bstep (se 1 (by rfl) ⟨1647668, by rfl⟩ : syracuseStep 2196891 = 3295337) B3295337
theorem B5713669 : Blo 2195435 5713669 := bbase (se 4 (by rfl) ⟨535656, by rfl⟩ : syracuseStep 5713669 = 1071313) (by norm_num)
theorem B7618225 : Blo 2195435 7618225 := bstep (se 2 (by rfl) ⟨2856834, by rfl⟩ : syracuseStep 7618225 = 5713669) B5713669
theorem B10157633 : Blo 2195435 10157633 := bstep (se 2 (by rfl) ⟨3809112, by rfl⟩ : syracuseStep 10157633 = 7618225) B7618225
theorem B6771755 : Blo 2195435 6771755 := bstep (se 1 (by rfl) ⟨5078816, by rfl⟩ : syracuseStep 6771755 = 10157633) B10157633
theorem B4514503 : Blo 2195435 4514503 := bstep (se 1 (by rfl) ⟨3385877, by rfl⟩ : syracuseStep 4514503 = 6771755) B6771755
theorem B6019337 : Blo 2195435 6019337 := bstep (se 2 (by rfl) ⟨2257251, by rfl⟩ : syracuseStep 6019337 = 4514503) B4514503
theorem B4012891 : Blo 2195435 4012891 := bstep (se 1 (by rfl) ⟨3009668, by rfl⟩ : syracuseStep 4012891 = 6019337) B6019337
theorem B21402085 : Blo 2195435 21402085 := bstep (se 4 (by rfl) ⟨2006445, by rfl⟩ : syracuseStep 21402085 = 4012891) B4012891
theorem B28536113 : Blo 2195435 28536113 := bstep (se 2 (by rfl) ⟨10701042, by rfl⟩ : syracuseStep 28536113 = 21402085) B21402085
theorem B19024075 : Blo 2195435 19024075 := bstep (se 1 (by rfl) ⟨14268056, by rfl⟩ : syracuseStep 19024075 = 28536113) B28536113
theorem B101461733 : Blo 2195435 101461733 := bstep (se 4 (by rfl) ⟨9512037, by rfl⟩ : syracuseStep 101461733 = 19024075) B19024075
theorem B67641155 : Blo 2195435 67641155 := bstep (se 1 (by rfl) ⟨50730866, by rfl⟩ : syracuseStep 67641155 = 101461733) B101461733
theorem B45094103 : Blo 2195435 45094103 := bstep (se 1 (by rfl) ⟨33820577, by rfl⟩ : syracuseStep 45094103 = 67641155) B67641155
theorem B30062735 : Blo 2195435 30062735 := bstep (se 1 (by rfl) ⟨22547051, by rfl⟩ : syracuseStep 30062735 = 45094103) B45094103
theorem B20041823 : Blo 2195435 20041823 := bstep (se 1 (by rfl) ⟨15031367, by rfl⟩ : syracuseStep 20041823 = 30062735) B30062735
theorem B13361215 : Blo 2195435 13361215 := bstep (se 1 (by rfl) ⟨10020911, by rfl⟩ : syracuseStep 13361215 = 20041823) B20041823
theorem B17814953 : Blo 2195435 17814953 := bstep (se 2 (by rfl) ⟨6680607, by rfl⟩ : syracuseStep 17814953 = 13361215) B13361215
theorem B11876635 : Blo 2195435 11876635 := bstep (se 1 (by rfl) ⟨8907476, by rfl⟩ : syracuseStep 11876635 = 17814953) B17814953
theorem B15835513 : Blo 2195435 15835513 := bstep (se 2 (by rfl) ⟨5938317, by rfl⟩ : syracuseStep 15835513 = 11876635) B11876635
theorem B21114017 : Blo 2195435 21114017 := bstep (se 2 (by rfl) ⟨7917756, by rfl⟩ : syracuseStep 21114017 = 15835513) B15835513
theorem B14076011 : Blo 2195435 14076011 := bstep (se 1 (by rfl) ⟨10557008, by rfl⟩ : syracuseStep 14076011 = 21114017) B21114017
theorem B9384007 : Blo 2195435 9384007 := bstep (se 1 (by rfl) ⟨7038005, by rfl⟩ : syracuseStep 9384007 = 14076011) B14076011
theorem B12512009 : Blo 2195435 12512009 := bstep (se 2 (by rfl) ⟨4692003, by rfl⟩ : syracuseStep 12512009 = 9384007) B9384007
theorem B8341339 : Blo 2195435 8341339 := bstep (se 1 (by rfl) ⟨6256004, by rfl⟩ : syracuseStep 8341339 = 12512009) B12512009
theorem B11121785 : Blo 2195435 11121785 := bstep (se 2 (by rfl) ⟨4170669, by rfl⟩ : syracuseStep 11121785 = 8341339) B8341339
theorem B7414523 : Blo 2195435 7414523 := bstep (se 1 (by rfl) ⟨5560892, by rfl⟩ : syracuseStep 7414523 = 11121785) B11121785
theorem B4943015 : Blo 2195435 4943015 := bstep (se 1 (by rfl) ⟨3707261, by rfl⟩ : syracuseStep 4943015 = 7414523) B7414523
theorem B3295343 : Blo 2195435 3295343 := bstep (se 1 (by rfl) ⟨2471507, by rfl⟩ : syracuseStep 3295343 = 4943015) B4943015
theorem B2196895 : Blo 2195435 2196895 := bstep (se 1 (by rfl) ⟨1647671, by rfl⟩ : syracuseStep 2196895 = 3295343) B3295343
theorem B3295349 : Blo 2195435 3295349 := bbase (se 5 (by rfl) ⟨154469, by rfl⟩ : syracuseStep 3295349 = 308939) (by norm_num)
theorem B2196899 : Blo 2195435 2196899 := bstep (se 1 (by rfl) ⟨1647674, by rfl⟩ : syracuseStep 2196899 = 3295349) B3295349
theorem B4170685 : Blo 2195435 4170685 := bbase (se 3 (by rfl) ⟨782003, by rfl⟩ : syracuseStep 4170685 = 1564007) (by norm_num)
theorem B5560913 : Blo 2195435 5560913 := bstep (se 2 (by rfl) ⟨2085342, by rfl⟩ : syracuseStep 5560913 = 4170685) B4170685
theorem B3707275 : Blo 2195435 3707275 := bstep (se 1 (by rfl) ⟨2780456, by rfl⟩ : syracuseStep 3707275 = 5560913) B5560913
theorem B4943033 : Blo 2195435 4943033 := bstep (se 2 (by rfl) ⟨1853637, by rfl⟩ : syracuseStep 4943033 = 3707275) B3707275
theorem B3295355 : Blo 2195435 3295355 := bstep (se 1 (by rfl) ⟨2471516, by rfl⟩ : syracuseStep 3295355 = 4943033) B4943033
theorem B2196903 : Blo 2195435 2196903 := bstep (se 1 (by rfl) ⟨1647677, by rfl⟩ : syracuseStep 2196903 = 3295355) B3295355
theorem B2471521 : Blo 2195435 2471521 := bbase (se 2 (by rfl) ⟨926820, by rfl⟩ : syracuseStep 2471521 = 1853641) (by norm_num)
theorem B3295361 : Blo 2195435 3295361 := bstep (se 2 (by rfl) ⟨1235760, by rfl⟩ : syracuseStep 3295361 = 2471521) B2471521
theorem B2196907 : Blo 2195435 2196907 := bstep (se 1 (by rfl) ⟨1647680, by rfl⟩ : syracuseStep 2196907 = 3295361) B3295361
theorem B5560933 : Blo 2195435 5560933 := bbase (se 4 (by rfl) ⟨521337, by rfl⟩ : syracuseStep 5560933 = 1042675) (by norm_num)
theorem B7414577 : Blo 2195435 7414577 := bstep (se 2 (by rfl) ⟨2780466, by rfl⟩ : syracuseStep 7414577 = 5560933) B5560933
theorem B4943051 : Blo 2195435 4943051 := bstep (se 1 (by rfl) ⟨3707288, by rfl⟩ : syracuseStep 4943051 = 7414577) B7414577
theorem B3295367 : Blo 2195435 3295367 := bstep (se 1 (by rfl) ⟨2471525, by rfl⟩ : syracuseStep 3295367 = 4943051) B4943051
theorem B2196911 : Blo 2195435 2196911 := bstep (se 1 (by rfl) ⟨1647683, by rfl⟩ : syracuseStep 2196911 = 3295367) B3295367
theorem B3295373 : Blo 2195435 3295373 := bbase (se 3 (by rfl) ⟨617882, by rfl⟩ : syracuseStep 3295373 = 1235765) (by norm_num)
theorem B2196915 : Blo 2195435 2196915 := bstep (se 1 (by rfl) ⟨1647686, by rfl⟩ : syracuseStep 2196915 = 3295373) B3295373
theorem B4943069 : Blo 2195435 4943069 := bbase (se 3 (by rfl) ⟨926825, by rfl⟩ : syracuseStep 4943069 = 1853651) (by norm_num)
theorem B3295379 : Blo 2195435 3295379 := bstep (se 1 (by rfl) ⟨2471534, by rfl⟩ : syracuseStep 3295379 = 4943069) B4943069
theorem B2196919 : Blo 2195435 2196919 := bstep (se 1 (by rfl) ⟨1647689, by rfl⟩ : syracuseStep 2196919 = 3295379) B3295379
theorem B3707309 : Blo 2195435 3707309 := bbase (se 3 (by rfl) ⟨695120, by rfl⟩ : syracuseStep 3707309 = 1390241) (by norm_num)
theorem B2471539 : Blo 2195435 2471539 := bstep (se 1 (by rfl) ⟨1853654, by rfl⟩ : syracuseStep 2471539 = 3707309) B3707309
theorem B3295385 : Blo 2195435 3295385 := bstep (se 2 (by rfl) ⟨1235769, by rfl⟩ : syracuseStep 3295385 = 2471539) B2471539
theorem B2196923 : Blo 2195435 2196923 := bstep (se 1 (by rfl) ⟨1647692, by rfl⟩ : syracuseStep 2196923 = 3295385) B3295385
theorem B2410489 : Blo 2195435 2410489 := bbase (se 2 (by rfl) ⟨903933, by rfl⟩ : syracuseStep 2410489 = 1807867) (by norm_num)
theorem B3213985 : Blo 2195435 3213985 := bstep (se 2 (by rfl) ⟨1205244, by rfl⟩ : syracuseStep 3213985 = 2410489) B2410489
theorem B4285313 : Blo 2195435 4285313 := bstep (se 2 (by rfl) ⟨1606992, by rfl⟩ : syracuseStep 4285313 = 3213985) B3213985
theorem B2856875 : Blo 2195435 2856875 := bstep (se 1 (by rfl) ⟨2142656, by rfl⟩ : syracuseStep 2856875 = 4285313) B4285313
theorem B30473333 : Blo 2195435 30473333 := bstep (se 5 (by rfl) ⟨1428437, by rfl⟩ : syracuseStep 30473333 = 2856875) B2856875
theorem B20315555 : Blo 2195435 20315555 := bstep (se 1 (by rfl) ⟨15236666, by rfl⟩ : syracuseStep 20315555 = 30473333) B30473333
theorem B13543703 : Blo 2195435 13543703 := bstep (se 1 (by rfl) ⟨10157777, by rfl⟩ : syracuseStep 13543703 = 20315555) B20315555
theorem B9029135 : Blo 2195435 9029135 := bstep (se 1 (by rfl) ⟨6771851, by rfl⟩ : syracuseStep 9029135 = 13543703) B13543703
theorem B24077693 : Blo 2195435 24077693 := bstep (se 3 (by rfl) ⟨4514567, by rfl⟩ : syracuseStep 24077693 = 9029135) B9029135
theorem B64207181 : Blo 2195435 64207181 := bstep (se 3 (by rfl) ⟨12038846, by rfl⟩ : syracuseStep 64207181 = 24077693) B24077693
theorem B42804787 : Blo 2195435 42804787 := bstep (se 1 (by rfl) ⟨32103590, by rfl⟩ : syracuseStep 42804787 = 64207181) B64207181
theorem B57073049 : Blo 2195435 57073049 := bstep (se 2 (by rfl) ⟨21402393, by rfl⟩ : syracuseStep 57073049 = 42804787) B42804787
theorem B38048699 : Blo 2195435 38048699 := bstep (se 1 (by rfl) ⟨28536524, by rfl⟩ : syracuseStep 38048699 = 57073049) B57073049
theorem B25365799 : Blo 2195435 25365799 := bstep (se 1 (by rfl) ⟨19024349, by rfl⟩ : syracuseStep 25365799 = 38048699) B38048699
theorem B33821065 : Blo 2195435 33821065 := bstep (se 2 (by rfl) ⟨12682899, by rfl⟩ : syracuseStep 33821065 = 25365799) B25365799
theorem B45094753 : Blo 2195435 45094753 := bstep (se 2 (by rfl) ⟨16910532, by rfl⟩ : syracuseStep 45094753 = 33821065) B33821065
theorem B60126337 : Blo 2195435 60126337 := bstep (se 2 (by rfl) ⟨22547376, by rfl⟩ : syracuseStep 60126337 = 45094753) B45094753
theorem B80168449 : Blo 2195435 80168449 := bstep (se 2 (by rfl) ⟨30063168, by rfl⟩ : syracuseStep 80168449 = 60126337) B60126337
theorem B106891265 : Blo 2195435 106891265 := bstep (se 2 (by rfl) ⟨40084224, by rfl⟩ : syracuseStep 106891265 = 80168449) B80168449
theorem B71260843 : Blo 2195435 71260843 := bstep (se 1 (by rfl) ⟨53445632, by rfl⟩ : syracuseStep 71260843 = 106891265) B106891265
theorem B95014457 : Blo 2195435 95014457 := bstep (se 2 (by rfl) ⟨35630421, by rfl⟩ : syracuseStep 95014457 = 71260843) B71260843
theorem B63342971 : Blo 2195435 63342971 := bstep (se 1 (by rfl) ⟨47507228, by rfl⟩ : syracuseStep 63342971 = 95014457) B95014457
theorem B42228647 : Blo 2195435 42228647 := bstep (se 1 (by rfl) ⟨31671485, by rfl⟩ : syracuseStep 42228647 = 63342971) B63342971
theorem B28152431 : Blo 2195435 28152431 := bstep (se 1 (by rfl) ⟨21114323, by rfl⟩ : syracuseStep 28152431 = 42228647) B42228647
theorem B18768287 : Blo 2195435 18768287 := bstep (se 1 (by rfl) ⟨14076215, by rfl⟩ : syracuseStep 18768287 = 28152431) B28152431
theorem B12512191 : Blo 2195435 12512191 := bstep (se 1 (by rfl) ⟨9384143, by rfl⟩ : syracuseStep 12512191 = 18768287) B18768287
theorem B16682921 : Blo 2195435 16682921 := bstep (se 2 (by rfl) ⟨6256095, by rfl⟩ : syracuseStep 16682921 = 12512191) B12512191
theorem B11121947 : Blo 2195435 11121947 := bstep (se 1 (by rfl) ⟨8341460, by rfl⟩ : syracuseStep 11121947 = 16682921) B16682921
theorem B7414631 : Blo 2195435 7414631 := bstep (se 1 (by rfl) ⟨5560973, by rfl⟩ : syracuseStep 7414631 = 11121947) B11121947
theorem B4943087 : Blo 2195435 4943087 := bstep (se 1 (by rfl) ⟨3707315, by rfl⟩ : syracuseStep 4943087 = 7414631) B7414631
theorem B3295391 : Blo 2195435 3295391 := bstep (se 1 (by rfl) ⟨2471543, by rfl⟩ : syracuseStep 3295391 = 4943087) B4943087
theorem B2196927 : Blo 2195435 2196927 := bstep (se 1 (by rfl) ⟨1647695, by rfl⟩ : syracuseStep 2196927 = 3295391) B3295391
theorem B3295397 : Blo 2195435 3295397 := bbase (se 4 (by rfl) ⟨308943, by rfl⟩ : syracuseStep 3295397 = 617887) (by norm_num)
theorem B2196931 : Blo 2195435 2196931 := bstep (se 1 (by rfl) ⟨1647698, by rfl⟩ : syracuseStep 2196931 = 3295397) B3295397
theorem B2780497 : Blo 2195435 2780497 := bbase (se 2 (by rfl) ⟨1042686, by rfl⟩ : syracuseStep 2780497 = 2085373) (by norm_num)
theorem B3707329 : Blo 2195435 3707329 := bstep (se 2 (by rfl) ⟨1390248, by rfl⟩ : syracuseStep 3707329 = 2780497) B2780497
theorem B4943105 : Blo 2195435 4943105 := bstep (se 2 (by rfl) ⟨1853664, by rfl⟩ : syracuseStep 4943105 = 3707329) B3707329
theorem B3295403 : Blo 2195435 3295403 := bstep (se 1 (by rfl) ⟨2471552, by rfl⟩ : syracuseStep 3295403 = 4943105) B4943105
theorem B2196935 : Blo 2195435 2196935 := bstep (se 1 (by rfl) ⟨1647701, by rfl⟩ : syracuseStep 2196935 = 3295403) B3295403
theorem B2471557 : Blo 2195435 2471557 := bbase (se 4 (by rfl) ⟨231708, by rfl⟩ : syracuseStep 2471557 = 463417) (by norm_num)
theorem B3295409 : Blo 2195435 3295409 := bstep (se 2 (by rfl) ⟨1235778, by rfl⟩ : syracuseStep 3295409 = 2471557) B2471557
theorem B2196939 : Blo 2195435 2196939 := bstep (se 1 (by rfl) ⟨1647704, by rfl⟩ : syracuseStep 2196939 = 3295409) B3295409
theorem B5278621 : Blo 2195435 5278621 := bbase (se 3 (by rfl) ⟨989741, by rfl⟩ : syracuseStep 5278621 = 1979483) (by norm_num)
theorem B7038161 : Blo 2195435 7038161 := bstep (se 2 (by rfl) ⟨2639310, by rfl⟩ : syracuseStep 7038161 = 5278621) B5278621
theorem B4692107 : Blo 2195435 4692107 := bstep (se 1 (by rfl) ⟨3519080, by rfl⟩ : syracuseStep 4692107 = 7038161) B7038161
theorem B3128071 : Blo 2195435 3128071 := bstep (se 1 (by rfl) ⟨2346053, by rfl⟩ : syracuseStep 3128071 = 4692107) B4692107
theorem B4170761 : Blo 2195435 4170761 := bstep (se 2 (by rfl) ⟨1564035, by rfl⟩ : syracuseStep 4170761 = 3128071) B3128071
theorem B2780507 : Blo 2195435 2780507 := bstep (se 1 (by rfl) ⟨2085380, by rfl⟩ : syracuseStep 2780507 = 4170761) B4170761
theorem B7414685 : Blo 2195435 7414685 := bstep (se 3 (by rfl) ⟨1390253, by rfl⟩ : syracuseStep 7414685 = 2780507) B2780507
theorem B4943123 : Blo 2195435 4943123 := bstep (se 1 (by rfl) ⟨3707342, by rfl⟩ : syracuseStep 4943123 = 7414685) B7414685
theorem B3295415 : Blo 2195435 3295415 := bstep (se 1 (by rfl) ⟨2471561, by rfl⟩ : syracuseStep 3295415 = 4943123) B4943123
theorem B2196943 : Blo 2195435 2196943 := bstep (se 1 (by rfl) ⟨1647707, by rfl⟩ : syracuseStep 2196943 = 3295415) B3295415
theorem B3295421 : Blo 2195435 3295421 := bbase (se 3 (by rfl) ⟨617891, by rfl⟩ : syracuseStep 3295421 = 1235783) (by norm_num)
theorem B2196947 : Blo 2195435 2196947 := bstep (se 1 (by rfl) ⟨1647710, by rfl⟩ : syracuseStep 2196947 = 3295421) B3295421
theorem B4943141 : Blo 2195435 4943141 := bbase (se 4 (by rfl) ⟨463419, by rfl⟩ : syracuseStep 4943141 = 926839) (by norm_num)
theorem B3295427 : Blo 2195435 3295427 := bstep (se 1 (by rfl) ⟨2471570, by rfl⟩ : syracuseStep 3295427 = 4943141) B4943141
theorem B2196951 : Blo 2195435 2196951 := bstep (se 1 (by rfl) ⟨1647713, by rfl⟩ : syracuseStep 2196951 = 3295427) B3295427
theorem B5561045 : Blo 2195435 5561045 := bbase (se 7 (by rfl) ⟨65168, by rfl⟩ : syracuseStep 5561045 = 130337) (by norm_num)
theorem B3707363 : Blo 2195435 3707363 := bstep (se 1 (by rfl) ⟨2780522, by rfl⟩ : syracuseStep 3707363 = 5561045) B5561045
theorem B2471575 : Blo 2195435 2471575 := bstep (se 1 (by rfl) ⟨1853681, by rfl⟩ : syracuseStep 2471575 = 3707363) B3707363
theorem B3295433 : Blo 2195435 3295433 := bstep (se 2 (by rfl) ⟨1235787, by rfl⟩ : syracuseStep 3295433 = 2471575) B2471575
theorem B2196955 : Blo 2195435 2196955 := bstep (se 1 (by rfl) ⟨1647716, by rfl⟩ : syracuseStep 2196955 = 3295433) B3295433
theorem B10557317 : Blo 2195435 10557317 := bbase (se 4 (by rfl) ⟨989748, by rfl⟩ : syracuseStep 10557317 = 1979497) (by norm_num)
theorem B7038211 : Blo 2195435 7038211 := bstep (se 1 (by rfl) ⟨5278658, by rfl⟩ : syracuseStep 7038211 = 10557317) B10557317
theorem B9384281 : Blo 2195435 9384281 := bstep (se 2 (by rfl) ⟨3519105, by rfl⟩ : syracuseStep 9384281 = 7038211) B7038211
theorem B6256187 : Blo 2195435 6256187 := bstep (se 1 (by rfl) ⟨4692140, by rfl⟩ : syracuseStep 6256187 = 9384281) B9384281
theorem B4170791 : Blo 2195435 4170791 := bstep (se 1 (by rfl) ⟨3128093, by rfl⟩ : syracuseStep 4170791 = 6256187) B6256187
theorem B11122109 : Blo 2195435 11122109 := bstep (se 3 (by rfl) ⟨2085395, by rfl⟩ : syracuseStep 11122109 = 4170791) B4170791
theorem B7414739 : Blo 2195435 7414739 := bstep (se 1 (by rfl) ⟨5561054, by rfl⟩ : syracuseStep 7414739 = 11122109) B11122109
theorem B4943159 : Blo 2195435 4943159 := bstep (se 1 (by rfl) ⟨3707369, by rfl⟩ : syracuseStep 4943159 = 7414739) B7414739
theorem B3295439 : Blo 2195435 3295439 := bstep (se 1 (by rfl) ⟨2471579, by rfl⟩ : syracuseStep 3295439 = 4943159) B4943159
theorem B2196959 : Blo 2195435 2196959 := bstep (se 1 (by rfl) ⟨1647719, by rfl⟩ : syracuseStep 2196959 = 3295439) B3295439
theorem B3295445 : Blo 2195435 3295445 := bbase (se 7 (by rfl) ⟨38618, by rfl⟩ : syracuseStep 3295445 = 77237) (by norm_num)
theorem B2196963 : Blo 2195435 2196963 := bstep (se 1 (by rfl) ⟨1647722, by rfl⟩ : syracuseStep 2196963 = 3295445) B3295445
theorem B5713861 : Blo 2195435 5713861 := bbase (se 4 (by rfl) ⟨535674, by rfl⟩ : syracuseStep 5713861 = 1071349) (by norm_num)
theorem B7618481 : Blo 2195435 7618481 := bstep (se 2 (by rfl) ⟨2856930, by rfl⟩ : syracuseStep 7618481 = 5713861) B5713861
theorem B5078987 : Blo 2195435 5078987 := bstep (se 1 (by rfl) ⟨3809240, by rfl⟩ : syracuseStep 5078987 = 7618481) B7618481
theorem B3385991 : Blo 2195435 3385991 := bstep (se 1 (by rfl) ⟨2539493, by rfl⟩ : syracuseStep 3385991 = 5078987) B5078987
theorem B2257327 : Blo 2195435 2257327 := bstep (se 1 (by rfl) ⟨1692995, by rfl⟩ : syracuseStep 2257327 = 3385991) B3385991
theorem B12039077 : Blo 2195435 12039077 := bstep (se 4 (by rfl) ⟨1128663, by rfl⟩ : syracuseStep 12039077 = 2257327) B2257327
theorem B8026051 : Blo 2195435 8026051 := bstep (se 1 (by rfl) ⟨6019538, by rfl⟩ : syracuseStep 8026051 = 12039077) B12039077
theorem B10701401 : Blo 2195435 10701401 := bstep (se 2 (by rfl) ⟨4013025, by rfl⟩ : syracuseStep 10701401 = 8026051) B8026051
theorem B28537069 : Blo 2195435 28537069 := bstep (se 3 (by rfl) ⟨5350700, by rfl⟩ : syracuseStep 28537069 = 10701401) B10701401
theorem B38049425 : Blo 2195435 38049425 := bstep (se 2 (by rfl) ⟨14268534, by rfl⟩ : syracuseStep 38049425 = 28537069) B28537069
theorem B25366283 : Blo 2195435 25366283 := bstep (se 1 (by rfl) ⟨19024712, by rfl⟩ : syracuseStep 25366283 = 38049425) B38049425
theorem B16910855 : Blo 2195435 16910855 := bstep (se 1 (by rfl) ⟨12683141, by rfl⟩ : syracuseStep 16910855 = 25366283) B25366283
theorem B11273903 : Blo 2195435 11273903 := bstep (se 1 (by rfl) ⟨8455427, by rfl⟩ : syracuseStep 11273903 = 16910855) B16910855
theorem B7515935 : Blo 2195435 7515935 := bstep (se 1 (by rfl) ⟨5636951, by rfl⟩ : syracuseStep 7515935 = 11273903) B11273903
theorem B5010623 : Blo 2195435 5010623 := bstep (se 1 (by rfl) ⟨3757967, by rfl⟩ : syracuseStep 5010623 = 7515935) B7515935
theorem B3340415 : Blo 2195435 3340415 := bstep (se 1 (by rfl) ⟨2505311, by rfl⟩ : syracuseStep 3340415 = 5010623) B5010623
theorem B2226943 : Blo 2195435 2226943 := bstep (se 1 (by rfl) ⟨1670207, by rfl⟩ : syracuseStep 2226943 = 3340415) B3340415
theorem B11877029 : Blo 2195435 11877029 := bstep (se 4 (by rfl) ⟨1113471, by rfl⟩ : syracuseStep 11877029 = 2226943) B2226943
theorem B7918019 : Blo 2195435 7918019 := bstep (se 1 (by rfl) ⟨5938514, by rfl⟩ : syracuseStep 7918019 = 11877029) B11877029
theorem B5278679 : Blo 2195435 5278679 := bstep (se 1 (by rfl) ⟨3959009, by rfl⟩ : syracuseStep 5278679 = 7918019) B7918019
theorem B3519119 : Blo 2195435 3519119 := bstep (se 1 (by rfl) ⟨2639339, by rfl⟩ : syracuseStep 3519119 = 5278679) B5278679
theorem B2346079 : Blo 2195435 2346079 := bstep (se 1 (by rfl) ⟨1759559, by rfl⟩ : syracuseStep 2346079 = 3519119) B3519119
theorem B3128105 : Blo 2195435 3128105 := bstep (se 2 (by rfl) ⟨1173039, by rfl⟩ : syracuseStep 3128105 = 2346079) B2346079
theorem B8341613 : Blo 2195435 8341613 := bstep (se 3 (by rfl) ⟨1564052, by rfl⟩ : syracuseStep 8341613 = 3128105) B3128105
theorem B5561075 : Blo 2195435 5561075 := bstep (se 1 (by rfl) ⟨4170806, by rfl⟩ : syracuseStep 5561075 = 8341613) B8341613
theorem B3707383 : Blo 2195435 3707383 := bstep (se 1 (by rfl) ⟨2780537, by rfl⟩ : syracuseStep 3707383 = 5561075) B5561075
theorem B4943177 : Blo 2195435 4943177 := bstep (se 2 (by rfl) ⟨1853691, by rfl⟩ : syracuseStep 4943177 = 3707383) B3707383
theorem B3295451 : Blo 2195435 3295451 := bstep (se 1 (by rfl) ⟨2471588, by rfl⟩ : syracuseStep 3295451 = 4943177) B4943177
theorem B2196967 : Blo 2195435 2196967 := bstep (se 1 (by rfl) ⟨1647725, by rfl⟩ : syracuseStep 2196967 = 3295451) B3295451
theorem B2471593 : Blo 2195435 2471593 := bbase (se 2 (by rfl) ⟨926847, by rfl⟩ : syracuseStep 2471593 = 1853695) (by norm_num)
theorem B3295457 : Blo 2195435 3295457 := bstep (se 2 (by rfl) ⟨1235796, by rfl⟩ : syracuseStep 3295457 = 2471593) B2471593
theorem B2196971 : Blo 2195435 2196971 := bstep (se 1 (by rfl) ⟨1647728, by rfl⟩ : syracuseStep 2196971 = 3295457) B3295457
theorem B2539501 : Blo 2195435 2539501 := bbase (se 3 (by rfl) ⟨476156, by rfl⟩ : syracuseStep 2539501 = 952313) (by norm_num)
theorem B13544005 : Blo 2195435 13544005 := bstep (se 4 (by rfl) ⟨1269750, by rfl⟩ : syracuseStep 13544005 = 2539501) B2539501
theorem B18058673 : Blo 2195435 18058673 := bstep (se 2 (by rfl) ⟨6772002, by rfl⟩ : syracuseStep 18058673 = 13544005) B13544005
theorem B12039115 : Blo 2195435 12039115 := bstep (se 1 (by rfl) ⟨9029336, by rfl⟩ : syracuseStep 12039115 = 18058673) B18058673
theorem B16052153 : Blo 2195435 16052153 := bstep (se 2 (by rfl) ⟨6019557, by rfl⟩ : syracuseStep 16052153 = 12039115) B12039115
theorem B42805741 : Blo 2195435 42805741 := bstep (se 3 (by rfl) ⟨8026076, by rfl⟩ : syracuseStep 42805741 = 16052153) B16052153
theorem B57074321 : Blo 2195435 57074321 := bstep (se 2 (by rfl) ⟨21402870, by rfl⟩ : syracuseStep 57074321 = 42805741) B42805741
theorem B38049547 : Blo 2195435 38049547 := bstep (se 1 (by rfl) ⟨28537160, by rfl⟩ : syracuseStep 38049547 = 57074321) B57074321
theorem B50732729 : Blo 2195435 50732729 := bstep (se 2 (by rfl) ⟨19024773, by rfl⟩ : syracuseStep 50732729 = 38049547) B38049547
theorem B33821819 : Blo 2195435 33821819 := bstep (se 1 (by rfl) ⟨25366364, by rfl⟩ : syracuseStep 33821819 = 50732729) B50732729
theorem B22547879 : Blo 2195435 22547879 := bstep (se 1 (by rfl) ⟨16910909, by rfl⟩ : syracuseStep 22547879 = 33821819) B33821819
theorem B15031919 : Blo 2195435 15031919 := bstep (se 1 (by rfl) ⟨11273939, by rfl⟩ : syracuseStep 15031919 = 22547879) B22547879
theorem B10021279 : Blo 2195435 10021279 := bstep (se 1 (by rfl) ⟨7515959, by rfl⟩ : syracuseStep 10021279 = 15031919) B15031919
theorem B13361705 : Blo 2195435 13361705 := bstep (se 2 (by rfl) ⟨5010639, by rfl⟩ : syracuseStep 13361705 = 10021279) B10021279
theorem B8907803 : Blo 2195435 8907803 := bstep (se 1 (by rfl) ⟨6680852, by rfl⟩ : syracuseStep 8907803 = 13361705) B13361705
theorem B5938535 : Blo 2195435 5938535 := bstep (se 1 (by rfl) ⟨4453901, by rfl⟩ : syracuseStep 5938535 = 8907803) B8907803
theorem B3959023 : Blo 2195435 3959023 := bstep (se 1 (by rfl) ⟨2969267, by rfl⟩ : syracuseStep 3959023 = 5938535) B5938535
theorem B5278697 : Blo 2195435 5278697 := bstep (se 2 (by rfl) ⟨1979511, by rfl⟩ : syracuseStep 5278697 = 3959023) B3959023
theorem B3519131 : Blo 2195435 3519131 := bstep (se 1 (by rfl) ⟨2639348, by rfl⟩ : syracuseStep 3519131 = 5278697) B5278697
theorem B9384349 : Blo 2195435 9384349 := bstep (se 3 (by rfl) ⟨1759565, by rfl⟩ : syracuseStep 9384349 = 3519131) B3519131
theorem B12512465 : Blo 2195435 12512465 := bstep (se 2 (by rfl) ⟨4692174, by rfl⟩ : syracuseStep 12512465 = 9384349) B9384349
theorem B8341643 : Blo 2195435 8341643 := bstep (se 1 (by rfl) ⟨6256232, by rfl⟩ : syracuseStep 8341643 = 12512465) B12512465
theorem B5561095 : Blo 2195435 5561095 := bstep (se 1 (by rfl) ⟨4170821, by rfl⟩ : syracuseStep 5561095 = 8341643) B8341643
theorem B7414793 : Blo 2195435 7414793 := bstep (se 2 (by rfl) ⟨2780547, by rfl⟩ : syracuseStep 7414793 = 5561095) B5561095
theorem B4943195 : Blo 2195435 4943195 := bstep (se 1 (by rfl) ⟨3707396, by rfl⟩ : syracuseStep 4943195 = 7414793) B7414793
theorem B3295463 : Blo 2195435 3295463 := bstep (se 1 (by rfl) ⟨2471597, by rfl⟩ : syracuseStep 3295463 = 4943195) B4943195
theorem B2196975 : Blo 2195435 2196975 := bstep (se 1 (by rfl) ⟨1647731, by rfl⟩ : syracuseStep 2196975 = 3295463) B3295463
theorem B3295469 : Blo 2195435 3295469 := bbase (se 3 (by rfl) ⟨617900, by rfl⟩ : syracuseStep 3295469 = 1235801) (by norm_num)
theorem B2196979 : Blo 2195435 2196979 := bstep (se 1 (by rfl) ⟨1647734, by rfl⟩ : syracuseStep 2196979 = 3295469) B3295469
theorem B4943213 : Blo 2195435 4943213 := bbase (se 3 (by rfl) ⟨926852, by rfl⟩ : syracuseStep 4943213 = 1853705) (by norm_num)
theorem B3295475 : Blo 2195435 3295475 := bstep (se 1 (by rfl) ⟨2471606, by rfl⟩ : syracuseStep 3295475 = 4943213) B4943213
theorem B2196983 : Blo 2195435 2196983 := bstep (se 1 (by rfl) ⟨1647737, by rfl⟩ : syracuseStep 2196983 = 3295475) B3295475
theorem B4170845 : Blo 2195435 4170845 := bbase (se 3 (by rfl) ⟨782033, by rfl⟩ : syracuseStep 4170845 = 1564067) (by norm_num)
theorem B2780563 : Blo 2195435 2780563 := bstep (se 1 (by rfl) ⟨2085422, by rfl⟩ : syracuseStep 2780563 = 4170845) B4170845
theorem B3707417 : Blo 2195435 3707417 := bstep (se 2 (by rfl) ⟨1390281, by rfl⟩ : syracuseStep 3707417 = 2780563) B2780563
theorem B2471611 : Blo 2195435 2471611 := bstep (se 1 (by rfl) ⟨1853708, by rfl⟩ : syracuseStep 2471611 = 3707417) B3707417
theorem B3295481 : Blo 2195435 3295481 := bstep (se 2 (by rfl) ⟨1235805, by rfl⟩ : syracuseStep 3295481 = 2471611) B2471611
theorem B2196987 : Blo 2195435 2196987 := bstep (se 1 (by rfl) ⟨1647740, by rfl⟩ : syracuseStep 2196987 = 3295481) B3295481
theorem B4453933 : Blo 2195435 4453933 := bbase (se 3 (by rfl) ⟨835112, by rfl⟩ : syracuseStep 4453933 = 1670225) (by norm_num)
theorem B5938577 : Blo 2195435 5938577 := bstep (se 2 (by rfl) ⟨2226966, by rfl⟩ : syracuseStep 5938577 = 4453933) B4453933
theorem B3959051 : Blo 2195435 3959051 := bstep (se 1 (by rfl) ⟨2969288, by rfl⟩ : syracuseStep 3959051 = 5938577) B5938577
theorem B10557469 : Blo 2195435 10557469 := bstep (se 3 (by rfl) ⟨1979525, by rfl⟩ : syracuseStep 10557469 = 3959051) B3959051
theorem B56306501 : Blo 2195435 56306501 := bstep (se 4 (by rfl) ⟨5278734, by rfl⟩ : syracuseStep 56306501 = 10557469) B10557469
theorem B37537667 : Blo 2195435 37537667 := bstep (se 1 (by rfl) ⟨28153250, by rfl⟩ : syracuseStep 37537667 = 56306501) B56306501
theorem B25025111 : Blo 2195435 25025111 := bstep (se 1 (by rfl) ⟨18768833, by rfl⟩ : syracuseStep 25025111 = 37537667) B37537667
theorem B16683407 : Blo 2195435 16683407 := bstep (se 1 (by rfl) ⟨12512555, by rfl⟩ : syracuseStep 16683407 = 25025111) B25025111
theorem B11122271 : Blo 2195435 11122271 := bstep (se 1 (by rfl) ⟨8341703, by rfl⟩ : syracuseStep 11122271 = 16683407) B16683407
theorem B7414847 : Blo 2195435 7414847 := bstep (se 1 (by rfl) ⟨5561135, by rfl⟩ : syracuseStep 7414847 = 11122271) B11122271
theorem B4943231 : Blo 2195435 4943231 := bstep (se 1 (by rfl) ⟨3707423, by rfl⟩ : syracuseStep 4943231 = 7414847) B7414847
theorem B3295487 : Blo 2195435 3295487 := bstep (se 1 (by rfl) ⟨2471615, by rfl⟩ : syracuseStep 3295487 = 4943231) B4943231
theorem B2196991 : Blo 2195435 2196991 := bstep (se 1 (by rfl) ⟨1647743, by rfl⟩ : syracuseStep 2196991 = 3295487) B3295487
theorem B3295493 : Blo 2195435 3295493 := bbase (se 4 (by rfl) ⟨308952, by rfl⟩ : syracuseStep 3295493 = 617905) (by norm_num)
theorem B2196995 : Blo 2195435 2196995 := bstep (se 1 (by rfl) ⟨1647746, by rfl⟩ : syracuseStep 2196995 = 3295493) B3295493
theorem B3707437 : Blo 2195435 3707437 := bbase (se 3 (by rfl) ⟨695144, by rfl⟩ : syracuseStep 3707437 = 1390289) (by norm_num)
theorem B4943249 : Blo 2195435 4943249 := bstep (se 2 (by rfl) ⟨1853718, by rfl⟩ : syracuseStep 4943249 = 3707437) B3707437
theorem B3295499 : Blo 2195435 3295499 := bstep (se 1 (by rfl) ⟨2471624, by rfl⟩ : syracuseStep 3295499 = 4943249) B4943249
theorem B2196999 : Blo 2195435 2196999 := bstep (se 1 (by rfl) ⟨1647749, by rfl⟩ : syracuseStep 2196999 = 3295499) B3295499
theorem B2471629 : Blo 2195435 2471629 := bbase (se 3 (by rfl) ⟨463430, by rfl⟩ : syracuseStep 2471629 = 926861) (by norm_num)
theorem B3295505 : Blo 2195435 3295505 := bstep (se 2 (by rfl) ⟨1235814, by rfl⟩ : syracuseStep 3295505 = 2471629) B2471629
theorem B2197003 : Blo 2195435 2197003 := bstep (se 1 (by rfl) ⟨1647752, by rfl⟩ : syracuseStep 2197003 = 3295505) B3295505
theorem B7414901 : Blo 2195435 7414901 := bbase (se 5 (by rfl) ⟨347573, by rfl⟩ : syracuseStep 7414901 = 695147) (by norm_num)
theorem B4943267 : Blo 2195435 4943267 := bstep (se 1 (by rfl) ⟨3707450, by rfl⟩ : syracuseStep 4943267 = 7414901) B7414901
theorem B3295511 : Blo 2195435 3295511 := bstep (se 1 (by rfl) ⟨2471633, by rfl⟩ : syracuseStep 3295511 = 4943267) B4943267
theorem B2197007 : Blo 2195435 2197007 := bstep (se 1 (by rfl) ⟨1647755, by rfl⟩ : syracuseStep 2197007 = 3295511) B3295511
theorem B3295517 : Blo 2195435 3295517 := bbase (se 3 (by rfl) ⟨617909, by rfl⟩ : syracuseStep 3295517 = 1235819) (by norm_num)
theorem B2197011 : Blo 2195435 2197011 := bstep (se 1 (by rfl) ⟨1647758, by rfl⟩ : syracuseStep 2197011 = 3295517) B3295517
theorem B4943285 : Blo 2195435 4943285 := bbase (se 5 (by rfl) ⟨231716, by rfl⟩ : syracuseStep 4943285 = 463433) (by norm_num)
theorem B3295523 : Blo 2195435 3295523 := bstep (se 1 (by rfl) ⟨2471642, by rfl⟩ : syracuseStep 3295523 = 4943285) B4943285
theorem B2197015 : Blo 2195435 2197015 := bstep (se 1 (by rfl) ⟨1647761, by rfl⟩ : syracuseStep 2197015 = 3295523) B3295523
theorem B4692269 : Blo 2195435 4692269 := bbase (se 3 (by rfl) ⟨879800, by rfl⟩ : syracuseStep 4692269 = 1759601) (by norm_num)
theorem B12512717 : Blo 2195435 12512717 := bstep (se 3 (by rfl) ⟨2346134, by rfl⟩ : syracuseStep 12512717 = 4692269) B4692269
theorem B8341811 : Blo 2195435 8341811 := bstep (se 1 (by rfl) ⟨6256358, by rfl⟩ : syracuseStep 8341811 = 12512717) B12512717
theorem B5561207 : Blo 2195435 5561207 := bstep (se 1 (by rfl) ⟨4170905, by rfl⟩ : syracuseStep 5561207 = 8341811) B8341811
theorem B3707471 : Blo 2195435 3707471 := bstep (se 1 (by rfl) ⟨2780603, by rfl⟩ : syracuseStep 3707471 = 5561207) B5561207
theorem B2471647 : Blo 2195435 2471647 := bstep (se 1 (by rfl) ⟨1853735, by rfl⟩ : syracuseStep 2471647 = 3707471) B3707471
theorem B3295529 : Blo 2195435 3295529 := bstep (se 2 (by rfl) ⟨1235823, by rfl⟩ : syracuseStep 3295529 = 2471647) B2471647
theorem B2197019 : Blo 2195435 2197019 := bstep (se 1 (by rfl) ⟨1647764, by rfl⟩ : syracuseStep 2197019 = 3295529) B3295529
theorem B4692277 : Blo 2195435 4692277 := bbase (se 5 (by rfl) ⟨219950, by rfl⟩ : syracuseStep 4692277 = 439901) (by norm_num)
theorem B6256369 : Blo 2195435 6256369 := bstep (se 2 (by rfl) ⟨2346138, by rfl⟩ : syracuseStep 6256369 = 4692277) B4692277
theorem B8341825 : Blo 2195435 8341825 := bstep (se 2 (by rfl) ⟨3128184, by rfl⟩ : syracuseStep 8341825 = 6256369) B6256369
theorem B11122433 : Blo 2195435 11122433 := bstep (se 2 (by rfl) ⟨4170912, by rfl⟩ : syracuseStep 11122433 = 8341825) B8341825
theorem B7414955 : Blo 2195435 7414955 := bstep (se 1 (by rfl) ⟨5561216, by rfl⟩ : syracuseStep 7414955 = 11122433) B11122433
theorem B4943303 : Blo 2195435 4943303 := bstep (se 1 (by rfl) ⟨3707477, by rfl⟩ : syracuseStep 4943303 = 7414955) B7414955
theorem B3295535 : Blo 2195435 3295535 := bstep (se 1 (by rfl) ⟨2471651, by rfl⟩ : syracuseStep 3295535 = 4943303) B4943303
theorem B2197023 : Blo 2195435 2197023 := bstep (se 1 (by rfl) ⟨1647767, by rfl⟩ : syracuseStep 2197023 = 3295535) B3295535
theorem B3295541 : Blo 2195435 3295541 := bbase (se 5 (by rfl) ⟨154478, by rfl⟩ : syracuseStep 3295541 = 308957) (by norm_num)
theorem B2197027 : Blo 2195435 2197027 := bstep (se 1 (by rfl) ⟨1647770, by rfl⟩ : syracuseStep 2197027 = 3295541) B3295541
theorem B5561237 : Blo 2195435 5561237 := bbase (se 6 (by rfl) ⟨130341, by rfl⟩ : syracuseStep 5561237 = 260683) (by norm_num)
theorem B3707491 : Blo 2195435 3707491 := bstep (se 1 (by rfl) ⟨2780618, by rfl⟩ : syracuseStep 3707491 = 5561237) B5561237
theorem B4943321 : Blo 2195435 4943321 := bstep (se 2 (by rfl) ⟨1853745, by rfl⟩ : syracuseStep 4943321 = 3707491) B3707491
theorem B3295547 : Blo 2195435 3295547 := bstep (se 1 (by rfl) ⟨2471660, by rfl⟩ : syracuseStep 3295547 = 4943321) B4943321
theorem B2197031 : Blo 2195435 2197031 := bstep (se 1 (by rfl) ⟨1647773, by rfl⟩ : syracuseStep 2197031 = 3295547) B3295547
theorem B2471665 : Blo 2195435 2471665 := bbase (se 2 (by rfl) ⟨926874, by rfl⟩ : syracuseStep 2471665 = 1853749) (by norm_num)
theorem B3295553 : Blo 2195435 3295553 := bstep (se 2 (by rfl) ⟨1235832, by rfl⟩ : syracuseStep 3295553 = 2471665) B2471665
theorem B2197035 : Blo 2195435 2197035 := bstep (se 1 (by rfl) ⟨1647776, by rfl⟩ : syracuseStep 2197035 = 3295553) B3295553
theorem B4756333 : Blo 2195435 4756333 := bbase (se 3 (by rfl) ⟨891812, by rfl⟩ : syracuseStep 4756333 = 1783625) (by norm_num)
theorem B6341777 : Blo 2195435 6341777 := bstep (se 2 (by rfl) ⟨2378166, by rfl⟩ : syracuseStep 6341777 = 4756333) B4756333
theorem B4227851 : Blo 2195435 4227851 := bstep (se 1 (by rfl) ⟨3170888, by rfl⟩ : syracuseStep 4227851 = 6341777) B6341777
theorem B2818567 : Blo 2195435 2818567 := bstep (se 1 (by rfl) ⟨2113925, by rfl⟩ : syracuseStep 2818567 = 4227851) B4227851
theorem B3758089 : Blo 2195435 3758089 := bstep (se 2 (by rfl) ⟨1409283, by rfl⟩ : syracuseStep 3758089 = 2818567) B2818567
theorem B5010785 : Blo 2195435 5010785 := bstep (se 2 (by rfl) ⟨1879044, by rfl⟩ : syracuseStep 5010785 = 3758089) B3758089
theorem B3340523 : Blo 2195435 3340523 := bstep (se 1 (by rfl) ⟨2505392, by rfl⟩ : syracuseStep 3340523 = 5010785) B5010785
theorem B8908061 : Blo 2195435 8908061 := bstep (se 3 (by rfl) ⟨1670261, by rfl⟩ : syracuseStep 8908061 = 3340523) B3340523
theorem B23754829 : Blo 2195435 23754829 := bstep (se 3 (by rfl) ⟨4454030, by rfl⟩ : syracuseStep 23754829 = 8908061) B8908061
theorem B31673105 : Blo 2195435 31673105 := bstep (se 2 (by rfl) ⟨11877414, by rfl⟩ : syracuseStep 31673105 = 23754829) B23754829
theorem B21115403 : Blo 2195435 21115403 := bstep (se 1 (by rfl) ⟨15836552, by rfl⟩ : syracuseStep 21115403 = 31673105) B31673105
theorem B14076935 : Blo 2195435 14076935 := bstep (se 1 (by rfl) ⟨10557701, by rfl⟩ : syracuseStep 14076935 = 21115403) B21115403
theorem B9384623 : Blo 2195435 9384623 := bstep (se 1 (by rfl) ⟨7038467, by rfl⟩ : syracuseStep 9384623 = 14076935) B14076935
theorem B6256415 : Blo 2195435 6256415 := bstep (se 1 (by rfl) ⟨4692311, by rfl⟩ : syracuseStep 6256415 = 9384623) B9384623
theorem B4170943 : Blo 2195435 4170943 := bstep (se 1 (by rfl) ⟨3128207, by rfl⟩ : syracuseStep 4170943 = 6256415) B6256415
theorem B5561257 : Blo 2195435 5561257 := bstep (se 2 (by rfl) ⟨2085471, by rfl⟩ : syracuseStep 5561257 = 4170943) B4170943
theorem B7415009 : Blo 2195435 7415009 := bstep (se 2 (by rfl) ⟨2780628, by rfl⟩ : syracuseStep 7415009 = 5561257) B5561257
theorem B4943339 : Blo 2195435 4943339 := bstep (se 1 (by rfl) ⟨3707504, by rfl⟩ : syracuseStep 4943339 = 7415009) B7415009
theorem B3295559 : Blo 2195435 3295559 := bstep (se 1 (by rfl) ⟨2471669, by rfl⟩ : syracuseStep 3295559 = 4943339) B4943339
theorem B2197039 : Blo 2195435 2197039 := bstep (se 1 (by rfl) ⟨1647779, by rfl⟩ : syracuseStep 2197039 = 3295559) B3295559
theorem B3295565 : Blo 2195435 3295565 := bbase (se 3 (by rfl) ⟨617918, by rfl⟩ : syracuseStep 3295565 = 1235837) (by norm_num)
theorem B2197043 : Blo 2195435 2197043 := bstep (se 1 (by rfl) ⟨1647782, by rfl⟩ : syracuseStep 2197043 = 3295565) B3295565
theorem B4943357 : Blo 2195435 4943357 := bbase (se 3 (by rfl) ⟨926879, by rfl⟩ : syracuseStep 4943357 = 1853759) (by norm_num)
theorem B3295571 : Blo 2195435 3295571 := bstep (se 1 (by rfl) ⟨2471678, by rfl⟩ : syracuseStep 3295571 = 4943357) B4943357
theorem B2197047 : Blo 2195435 2197047 := bstep (se 1 (by rfl) ⟨1647785, by rfl⟩ : syracuseStep 2197047 = 3295571) B3295571
theorem B3707525 : Blo 2195435 3707525 := bbase (se 4 (by rfl) ⟨347580, by rfl⟩ : syracuseStep 3707525 = 695161) (by norm_num)
theorem B2471683 : Blo 2195435 2471683 := bstep (se 1 (by rfl) ⟨1853762, by rfl⟩ : syracuseStep 2471683 = 3707525) B3707525
theorem B3295577 : Blo 2195435 3295577 := bstep (se 2 (by rfl) ⟨1235841, by rfl⟩ : syracuseStep 3295577 = 2471683) B2471683
theorem B2197051 : Blo 2195435 2197051 := bstep (se 1 (by rfl) ⟨1647788, by rfl⟩ : syracuseStep 2197051 = 3295577) B3295577
theorem B16683893 : Blo 2195435 16683893 := bbase (se 5 (by rfl) ⟨782057, by rfl⟩ : syracuseStep 16683893 = 1564115) (by norm_num)
theorem B11122595 : Blo 2195435 11122595 := bstep (se 1 (by rfl) ⟨8341946, by rfl⟩ : syracuseStep 11122595 = 16683893) B16683893
theorem B7415063 : Blo 2195435 7415063 := bstep (se 1 (by rfl) ⟨5561297, by rfl⟩ : syracuseStep 7415063 = 11122595) B11122595
theorem B4943375 : Blo 2195435 4943375 := bstep (se 1 (by rfl) ⟨3707531, by rfl⟩ : syracuseStep 4943375 = 7415063) B7415063
theorem B3295583 : Blo 2195435 3295583 := bstep (se 1 (by rfl) ⟨2471687, by rfl⟩ : syracuseStep 3295583 = 4943375) B4943375
theorem B2197055 : Blo 2195435 2197055 := bstep (se 1 (by rfl) ⟨1647791, by rfl⟩ : syracuseStep 2197055 = 3295583) B3295583
theorem B3295589 : Blo 2195435 3295589 := bbase (se 4 (by rfl) ⟨308961, by rfl⟩ : syracuseStep 3295589 = 617923) (by norm_num)
theorem B2197059 : Blo 2195435 2197059 := bstep (se 1 (by rfl) ⟨1647794, by rfl⟩ : syracuseStep 2197059 = 3295589) B3295589
theorem B4170989 : Blo 2195435 4170989 := bbase (se 3 (by rfl) ⟨782060, by rfl⟩ : syracuseStep 4170989 = 1564121) (by norm_num)
theorem B2780659 : Blo 2195435 2780659 := bstep (se 1 (by rfl) ⟨2085494, by rfl⟩ : syracuseStep 2780659 = 4170989) B4170989
theorem B3707545 : Blo 2195435 3707545 := bstep (se 2 (by rfl) ⟨1390329, by rfl⟩ : syracuseStep 3707545 = 2780659) B2780659
theorem B4943393 : Blo 2195435 4943393 := bstep (se 2 (by rfl) ⟨1853772, by rfl⟩ : syracuseStep 4943393 = 3707545) B3707545
theorem B3295595 : Blo 2195435 3295595 := bstep (se 1 (by rfl) ⟨2471696, by rfl⟩ : syracuseStep 3295595 = 4943393) B4943393
theorem B2197063 : Blo 2195435 2197063 := bstep (se 1 (by rfl) ⟨1647797, by rfl⟩ : syracuseStep 2197063 = 3295595) B3295595
theorem B2471701 : Blo 2195435 2471701 := bbase (se 6 (by rfl) ⟨57930, by rfl⟩ : syracuseStep 2471701 = 115861) (by norm_num)
theorem B3295601 : Blo 2195435 3295601 := bstep (se 2 (by rfl) ⟨1235850, by rfl⟩ : syracuseStep 3295601 = 2471701) B2471701
theorem B2197067 : Blo 2195435 2197067 := bstep (se 1 (by rfl) ⟨1647800, by rfl⟩ : syracuseStep 2197067 = 3295601) B3295601
theorem B2780669 : Blo 2195435 2780669 := bbase (se 3 (by rfl) ⟨521375, by rfl⟩ : syracuseStep 2780669 = 1042751) (by norm_num)
theorem B7415117 : Blo 2195435 7415117 := bstep (se 3 (by rfl) ⟨1390334, by rfl⟩ : syracuseStep 7415117 = 2780669) B2780669
theorem B4943411 : Blo 2195435 4943411 := bstep (se 1 (by rfl) ⟨3707558, by rfl⟩ : syracuseStep 4943411 = 7415117) B7415117
theorem B3295607 : Blo 2195435 3295607 := bstep (se 1 (by rfl) ⟨2471705, by rfl⟩ : syracuseStep 3295607 = 4943411) B4943411
theorem B2197071 : Blo 2195435 2197071 := bstep (se 1 (by rfl) ⟨1647803, by rfl⟩ : syracuseStep 2197071 = 3295607) B3295607
theorem B3295613 : Blo 2195435 3295613 := bbase (se 3 (by rfl) ⟨617927, by rfl⟩ : syracuseStep 3295613 = 1235855) (by norm_num)
theorem B2197075 : Blo 2195435 2197075 := bstep (se 1 (by rfl) ⟨1647806, by rfl⟩ : syracuseStep 2197075 = 3295613) B3295613
theorem B4943429 : Blo 2195435 4943429 := bbase (se 4 (by rfl) ⟨463446, by rfl⟩ : syracuseStep 4943429 = 926893) (by norm_num)
theorem B3295619 : Blo 2195435 3295619 := bstep (se 1 (by rfl) ⟨2471714, by rfl⟩ : syracuseStep 3295619 = 4943429) B4943429
theorem B2197079 : Blo 2195435 2197079 := bstep (se 1 (by rfl) ⟨1647809, by rfl⟩ : syracuseStep 2197079 = 3295619) B3295619
theorem B2227061 : Blo 2195435 2227061 := bbase (se 5 (by rfl) ⟨104393, by rfl⟩ : syracuseStep 2227061 = 208787) (by norm_num)
theorem B5938829 : Blo 2195435 5938829 := bstep (se 3 (by rfl) ⟨1113530, by rfl⟩ : syracuseStep 5938829 = 2227061) B2227061
theorem B3959219 : Blo 2195435 3959219 := bstep (se 1 (by rfl) ⟨2969414, by rfl⟩ : syracuseStep 3959219 = 5938829) B5938829
theorem B2639479 : Blo 2195435 2639479 := bstep (se 1 (by rfl) ⟨1979609, by rfl⟩ : syracuseStep 2639479 = 3959219) B3959219
theorem B3519305 : Blo 2195435 3519305 := bstep (se 2 (by rfl) ⟨1319739, by rfl⟩ : syracuseStep 3519305 = 2639479) B2639479
theorem B2346203 : Blo 2195435 2346203 := bstep (se 1 (by rfl) ⟨1759652, by rfl⟩ : syracuseStep 2346203 = 3519305) B3519305
theorem B6256541 : Blo 2195435 6256541 := bstep (se 3 (by rfl) ⟨1173101, by rfl⟩ : syracuseStep 6256541 = 2346203) B2346203
theorem B4171027 : Blo 2195435 4171027 := bstep (se 1 (by rfl) ⟨3128270, by rfl⟩ : syracuseStep 4171027 = 6256541) B6256541
theorem B5561369 : Blo 2195435 5561369 := bstep (se 2 (by rfl) ⟨2085513, by rfl⟩ : syracuseStep 5561369 = 4171027) B4171027
theorem B3707579 : Blo 2195435 3707579 := bstep (se 1 (by rfl) ⟨2780684, by rfl⟩ : syracuseStep 3707579 = 5561369) B5561369
theorem B2471719 : Blo 2195435 2471719 := bstep (se 1 (by rfl) ⟨1853789, by rfl⟩ : syracuseStep 2471719 = 3707579) B3707579
theorem B3295625 : Blo 2195435 3295625 := bstep (se 2 (by rfl) ⟨1235859, by rfl⟩ : syracuseStep 3295625 = 2471719) B2471719
theorem B2197083 : Blo 2195435 2197083 := bstep (se 1 (by rfl) ⟨1647812, by rfl⟩ : syracuseStep 2197083 = 3295625) B3295625
theorem B11122757 : Blo 2195435 11122757 := bbase (se 4 (by rfl) ⟨1042758, by rfl⟩ : syracuseStep 11122757 = 2085517) (by norm_num)
theorem B7415171 : Blo 2195435 7415171 := bstep (se 1 (by rfl) ⟨5561378, by rfl⟩ : syracuseStep 7415171 = 11122757) B11122757
theorem B4943447 : Blo 2195435 4943447 := bstep (se 1 (by rfl) ⟨3707585, by rfl⟩ : syracuseStep 4943447 = 7415171) B7415171
theorem B3295631 : Blo 2195435 3295631 := bstep (se 1 (by rfl) ⟨2471723, by rfl⟩ : syracuseStep 3295631 = 4943447) B4943447
theorem B2197087 : Blo 2195435 2197087 := bstep (se 1 (by rfl) ⟨1647815, by rfl⟩ : syracuseStep 2197087 = 3295631) B3295631
theorem B3295637 : Blo 2195435 3295637 := bbase (se 6 (by rfl) ⟨77241, by rfl⟩ : syracuseStep 3295637 = 154483) (by norm_num)
theorem B2197091 : Blo 2195435 2197091 := bstep (se 1 (by rfl) ⟨1647818, by rfl⟩ : syracuseStep 2197091 = 3295637) B3295637
theorem B3567341 : Blo 2195435 3567341 := bbase (se 3 (by rfl) ⟨668876, by rfl⟩ : syracuseStep 3567341 = 1337753) (by norm_num)
theorem B9512909 : Blo 2195435 9512909 := bstep (se 3 (by rfl) ⟨1783670, by rfl⟩ : syracuseStep 9512909 = 3567341) B3567341
theorem B6341939 : Blo 2195435 6341939 := bstep (se 1 (by rfl) ⟨4756454, by rfl⟩ : syracuseStep 6341939 = 9512909) B9512909
theorem B4227959 : Blo 2195435 4227959 := bstep (se 1 (by rfl) ⟨3170969, by rfl⟩ : syracuseStep 4227959 = 6341939) B6341939
theorem B2818639 : Blo 2195435 2818639 := bstep (se 1 (by rfl) ⟨2113979, by rfl⟩ : syracuseStep 2818639 = 4227959) B4227959
theorem B3758185 : Blo 2195435 3758185 := bstep (se 2 (by rfl) ⟨1409319, by rfl⟩ : syracuseStep 3758185 = 2818639) B2818639
theorem B5010913 : Blo 2195435 5010913 := bstep (se 2 (by rfl) ⟨1879092, by rfl⟩ : syracuseStep 5010913 = 3758185) B3758185
theorem B6681217 : Blo 2195435 6681217 := bstep (se 2 (by rfl) ⟨2505456, by rfl⟩ : syracuseStep 6681217 = 5010913) B5010913
theorem B8908289 : Blo 2195435 8908289 := bstep (se 2 (by rfl) ⟨3340608, by rfl⟩ : syracuseStep 8908289 = 6681217) B6681217
theorem B5938859 : Blo 2195435 5938859 := bstep (se 1 (by rfl) ⟨4454144, by rfl⟩ : syracuseStep 5938859 = 8908289) B8908289
theorem B15836957 : Blo 2195435 15836957 := bstep (se 3 (by rfl) ⟨2969429, by rfl⟩ : syracuseStep 15836957 = 5938859) B5938859
theorem B10557971 : Blo 2195435 10557971 := bstep (se 1 (by rfl) ⟨7918478, by rfl⟩ : syracuseStep 10557971 = 15836957) B15836957
theorem B7038647 : Blo 2195435 7038647 := bstep (se 1 (by rfl) ⟨5278985, by rfl⟩ : syracuseStep 7038647 = 10557971) B10557971
theorem B4692431 : Blo 2195435 4692431 := bstep (se 1 (by rfl) ⟨3519323, by rfl⟩ : syracuseStep 4692431 = 7038647) B7038647
theorem B12513149 : Blo 2195435 12513149 := bstep (se 3 (by rfl) ⟨2346215, by rfl⟩ : syracuseStep 12513149 = 4692431) B4692431
theorem B8342099 : Blo 2195435 8342099 := bstep (se 1 (by rfl) ⟨6256574, by rfl⟩ : syracuseStep 8342099 = 12513149) B12513149
theorem B5561399 : Blo 2195435 5561399 := bstep (se 1 (by rfl) ⟨4171049, by rfl⟩ : syracuseStep 5561399 = 8342099) B8342099
theorem B3707599 : Blo 2195435 3707599 := bstep (se 1 (by rfl) ⟨2780699, by rfl⟩ : syracuseStep 3707599 = 5561399) B5561399
theorem B4943465 : Blo 2195435 4943465 := bstep (se 2 (by rfl) ⟨1853799, by rfl⟩ : syracuseStep 4943465 = 3707599) B3707599
theorem B3295643 : Blo 2195435 3295643 := bstep (se 1 (by rfl) ⟨2471732, by rfl⟩ : syracuseStep 3295643 = 4943465) B4943465
theorem B2197095 : Blo 2195435 2197095 := bstep (se 1 (by rfl) ⟨1647821, by rfl⟩ : syracuseStep 2197095 = 3295643) B3295643
theorem B2471737 : Blo 2195435 2471737 := bbase (se 2 (by rfl) ⟨926901, by rfl⟩ : syracuseStep 2471737 = 1853803) (by norm_num)
theorem B3295649 : Blo 2195435 3295649 := bstep (se 2 (by rfl) ⟨1235868, by rfl⟩ : syracuseStep 3295649 = 2471737) B2471737
theorem B2197099 : Blo 2195435 2197099 := bstep (se 1 (by rfl) ⟨1647824, by rfl⟩ : syracuseStep 2197099 = 3295649) B3295649
theorem B6256597 : Blo 2195435 6256597 := bbase (se 7 (by rfl) ⟨73319, by rfl⟩ : syracuseStep 6256597 = 146639) (by norm_num)
theorem B8342129 : Blo 2195435 8342129 := bstep (se 2 (by rfl) ⟨3128298, by rfl⟩ : syracuseStep 8342129 = 6256597) B6256597
theorem B5561419 : Blo 2195435 5561419 := bstep (se 1 (by rfl) ⟨4171064, by rfl⟩ : syracuseStep 5561419 = 8342129) B8342129
theorem B7415225 : Blo 2195435 7415225 := bstep (se 2 (by rfl) ⟨2780709, by rfl⟩ : syracuseStep 7415225 = 5561419) B5561419
theorem B4943483 : Blo 2195435 4943483 := bstep (se 1 (by rfl) ⟨3707612, by rfl⟩ : syracuseStep 4943483 = 7415225) B7415225
theorem B3295655 : Blo 2195435 3295655 := bstep (se 1 (by rfl) ⟨2471741, by rfl⟩ : syracuseStep 3295655 = 4943483) B4943483
theorem B2197103 : Blo 2195435 2197103 := bstep (se 1 (by rfl) ⟨1647827, by rfl⟩ : syracuseStep 2197103 = 3295655) B3295655
theorem B3295661 : Blo 2195435 3295661 := bbase (se 3 (by rfl) ⟨617936, by rfl⟩ : syracuseStep 3295661 = 1235873) (by norm_num)
theorem B2197107 : Blo 2195435 2197107 := bstep (se 1 (by rfl) ⟨1647830, by rfl⟩ : syracuseStep 2197107 = 3295661) B3295661
theorem B4943501 : Blo 2195435 4943501 := bbase (se 3 (by rfl) ⟨926906, by rfl⟩ : syracuseStep 4943501 = 1853813) (by norm_num)
theorem B3295667 : Blo 2195435 3295667 := bstep (se 1 (by rfl) ⟨2471750, by rfl⟩ : syracuseStep 3295667 = 4943501) B4943501
theorem B2197111 : Blo 2195435 2197111 := bstep (se 1 (by rfl) ⟨1647833, by rfl⟩ : syracuseStep 2197111 = 3295667) B3295667
theorem B2780725 : Blo 2195435 2780725 := bbase (se 5 (by rfl) ⟨130346, by rfl⟩ : syracuseStep 2780725 = 260693) (by norm_num)
theorem B3707633 : Blo 2195435 3707633 := bstep (se 2 (by rfl) ⟨1390362, by rfl⟩ : syracuseStep 3707633 = 2780725) B2780725
theorem B2471755 : Blo 2195435 2471755 := bstep (se 1 (by rfl) ⟨1853816, by rfl⟩ : syracuseStep 2471755 = 3707633) B3707633
theorem B3295673 : Blo 2195435 3295673 := bstep (se 2 (by rfl) ⟨1235877, by rfl⟩ : syracuseStep 3295673 = 2471755) B2471755
theorem B2197115 : Blo 2195435 2197115 := bstep (se 1 (by rfl) ⟨1647836, by rfl⟩ : syracuseStep 2197115 = 3295673) B3295673
theorem B11877845 : Blo 2195435 11877845 := bbase (se 7 (by rfl) ⟨139193, by rfl⟩ : syracuseStep 11877845 = 278387) (by norm_num)
theorem B31674253 : Blo 2195435 31674253 := bstep (se 3 (by rfl) ⟨5938922, by rfl⟩ : syracuseStep 31674253 = 11877845) B11877845
theorem B42232337 : Blo 2195435 42232337 := bstep (se 2 (by rfl) ⟨15837126, by rfl⟩ : syracuseStep 42232337 = 31674253) B31674253
theorem B28154891 : Blo 2195435 28154891 := bstep (se 1 (by rfl) ⟨21116168, by rfl⟩ : syracuseStep 28154891 = 42232337) B42232337
theorem B18769927 : Blo 2195435 18769927 := bstep (se 1 (by rfl) ⟨14077445, by rfl⟩ : syracuseStep 18769927 = 28154891) B28154891
theorem B25026569 : Blo 2195435 25026569 := bstep (se 2 (by rfl) ⟨9384963, by rfl⟩ : syracuseStep 25026569 = 18769927) B18769927
theorem B16684379 : Blo 2195435 16684379 := bstep (se 1 (by rfl) ⟨12513284, by rfl⟩ : syracuseStep 16684379 = 25026569) B25026569
theorem B11122919 : Blo 2195435 11122919 := bstep (se 1 (by rfl) ⟨8342189, by rfl⟩ : syracuseStep 11122919 = 16684379) B16684379
theorem B7415279 : Blo 2195435 7415279 := bstep (se 1 (by rfl) ⟨5561459, by rfl⟩ : syracuseStep 7415279 = 11122919) B11122919
theorem B4943519 : Blo 2195435 4943519 := bstep (se 1 (by rfl) ⟨3707639, by rfl⟩ : syracuseStep 4943519 = 7415279) B7415279
theorem B3295679 : Blo 2195435 3295679 := bstep (se 1 (by rfl) ⟨2471759, by rfl⟩ : syracuseStep 3295679 = 4943519) B4943519
theorem B2197119 : Blo 2195435 2197119 := bstep (se 1 (by rfl) ⟨1647839, by rfl⟩ : syracuseStep 2197119 = 3295679) B3295679
theorem B3295685 : Blo 2195435 3295685 := bbase (se 4 (by rfl) ⟨308970, by rfl⟩ : syracuseStep 3295685 = 617941) (by norm_num)
theorem B2197123 : Blo 2195435 2197123 := bstep (se 1 (by rfl) ⟨1647842, by rfl⟩ : syracuseStep 2197123 = 3295685) B3295685
theorem B3707653 : Blo 2195435 3707653 := bbase (se 4 (by rfl) ⟨347592, by rfl⟩ : syracuseStep 3707653 = 695185) (by norm_num)
theorem B4943537 : Blo 2195435 4943537 := bstep (se 2 (by rfl) ⟨1853826, by rfl⟩ : syracuseStep 4943537 = 3707653) B3707653
theorem B3295691 : Blo 2195435 3295691 := bstep (se 1 (by rfl) ⟨2471768, by rfl⟩ : syracuseStep 3295691 = 4943537) B4943537
theorem B2197127 : Blo 2195435 2197127 := bstep (se 1 (by rfl) ⟨1647845, by rfl⟩ : syracuseStep 2197127 = 3295691) B3295691
theorem B2471773 : Blo 2195435 2471773 := bbase (se 3 (by rfl) ⟨463457, by rfl⟩ : syracuseStep 2471773 = 926915) (by norm_num)
theorem B3295697 : Blo 2195435 3295697 := bstep (se 2 (by rfl) ⟨1235886, by rfl⟩ : syracuseStep 3295697 = 2471773) B2471773
theorem B2197131 : Blo 2195435 2197131 := bstep (se 1 (by rfl) ⟨1647848, by rfl⟩ : syracuseStep 2197131 = 3295697) B3295697
theorem B7415333 : Blo 2195435 7415333 := bbase (se 4 (by rfl) ⟨695187, by rfl⟩ : syracuseStep 7415333 = 1390375) (by norm_num)
theorem B4943555 : Blo 2195435 4943555 := bstep (se 1 (by rfl) ⟨3707666, by rfl⟩ : syracuseStep 4943555 = 7415333) B7415333
theorem B3295703 : Blo 2195435 3295703 := bstep (se 1 (by rfl) ⟨2471777, by rfl⟩ : syracuseStep 3295703 = 4943555) B4943555
theorem B2197135 : Blo 2195435 2197135 := bstep (se 1 (by rfl) ⟨1647851, by rfl⟩ : syracuseStep 2197135 = 3295703) B3295703
theorem B3295709 : Blo 2195435 3295709 := bbase (se 3 (by rfl) ⟨617945, by rfl⟩ : syracuseStep 3295709 = 1235891) (by norm_num)
theorem B2197139 : Blo 2195435 2197139 := bstep (se 1 (by rfl) ⟨1647854, by rfl⟩ : syracuseStep 2197139 = 3295709) B3295709
theorem B4943573 : Blo 2195435 4943573 := bbase (se 7 (by rfl) ⟨57932, by rfl⟩ : syracuseStep 4943573 = 115865) (by norm_num)
theorem B3295715 : Blo 2195435 3295715 := bstep (se 1 (by rfl) ⟨2471786, by rfl⟩ : syracuseStep 3295715 = 4943573) B4943573
theorem B2197143 : Blo 2195435 2197143 := bstep (se 1 (by rfl) ⟨1647857, by rfl⟩ : syracuseStep 2197143 = 3295715) B3295715
theorem B8908501 : Blo 2195435 8908501 := bbase (se 7 (by rfl) ⟨104396, by rfl⟩ : syracuseStep 8908501 = 208793) (by norm_num)
theorem B11878001 : Blo 2195435 11878001 := bstep (se 2 (by rfl) ⟨4454250, by rfl⟩ : syracuseStep 11878001 = 8908501) B8908501
theorem B7918667 : Blo 2195435 7918667 := bstep (se 1 (by rfl) ⟨5939000, by rfl⟩ : syracuseStep 7918667 = 11878001) B11878001
theorem B5279111 : Blo 2195435 5279111 := bstep (se 1 (by rfl) ⟨3959333, by rfl⟩ : syracuseStep 5279111 = 7918667) B7918667
theorem B3519407 : Blo 2195435 3519407 := bstep (se 1 (by rfl) ⟨2639555, by rfl⟩ : syracuseStep 3519407 = 5279111) B5279111
theorem B9385085 : Blo 2195435 9385085 := bstep (se 3 (by rfl) ⟨1759703, by rfl⟩ : syracuseStep 9385085 = 3519407) B3519407
theorem B6256723 : Blo 2195435 6256723 := bstep (se 1 (by rfl) ⟨4692542, by rfl⟩ : syracuseStep 6256723 = 9385085) B9385085
theorem B8342297 : Blo 2195435 8342297 := bstep (se 2 (by rfl) ⟨3128361, by rfl⟩ : syracuseStep 8342297 = 6256723) B6256723
theorem B5561531 : Blo 2195435 5561531 := bstep (se 1 (by rfl) ⟨4171148, by rfl⟩ : syracuseStep 5561531 = 8342297) B8342297
theorem B3707687 : Blo 2195435 3707687 := bstep (se 1 (by rfl) ⟨2780765, by rfl⟩ : syracuseStep 3707687 = 5561531) B5561531
theorem B2471791 : Blo 2195435 2471791 := bstep (se 1 (by rfl) ⟨1853843, by rfl⟩ : syracuseStep 2471791 = 3707687) B3707687
theorem B3295721 : Blo 2195435 3295721 := bstep (se 2 (by rfl) ⟨1235895, by rfl⟩ : syracuseStep 3295721 = 2471791) B2471791
theorem B2197147 : Blo 2195435 2197147 := bstep (se 1 (by rfl) ⟨1647860, by rfl⟩ : syracuseStep 2197147 = 3295721) B3295721
theorem B3340693 : Blo 2195435 3340693 := bbase (se 6 (by rfl) ⟨78297, by rfl⟩ : syracuseStep 3340693 = 156595) (by norm_num)
theorem B17817029 : Blo 2195435 17817029 := bstep (se 4 (by rfl) ⟨1670346, by rfl⟩ : syracuseStep 17817029 = 3340693) B3340693
theorem B11878019 : Blo 2195435 11878019 := bstep (se 1 (by rfl) ⟨8908514, by rfl⟩ : syracuseStep 11878019 = 17817029) B17817029
theorem B7918679 : Blo 2195435 7918679 := bstep (se 1 (by rfl) ⟨5939009, by rfl⟩ : syracuseStep 7918679 = 11878019) B11878019
theorem B21116477 : Blo 2195435 21116477 := bstep (se 3 (by rfl) ⟨3959339, by rfl⟩ : syracuseStep 21116477 = 7918679) B7918679
theorem B14077651 : Blo 2195435 14077651 := bstep (se 1 (by rfl) ⟨10558238, by rfl⟩ : syracuseStep 14077651 = 21116477) B21116477
theorem B18770201 : Blo 2195435 18770201 := bstep (se 2 (by rfl) ⟨7038825, by rfl⟩ : syracuseStep 18770201 = 14077651) B14077651
theorem B12513467 : Blo 2195435 12513467 := bstep (se 1 (by rfl) ⟨9385100, by rfl⟩ : syracuseStep 12513467 = 18770201) B18770201
theorem B8342311 : Blo 2195435 8342311 := bstep (se 1 (by rfl) ⟨6256733, by rfl⟩ : syracuseStep 8342311 = 12513467) B12513467
theorem B11123081 : Blo 2195435 11123081 := bstep (se 2 (by rfl) ⟨4171155, by rfl⟩ : syracuseStep 11123081 = 8342311) B8342311
theorem B7415387 : Blo 2195435 7415387 := bstep (se 1 (by rfl) ⟨5561540, by rfl⟩ : syracuseStep 7415387 = 11123081) B11123081
theorem B4943591 : Blo 2195435 4943591 := bstep (se 1 (by rfl) ⟨3707693, by rfl⟩ : syracuseStep 4943591 = 7415387) B7415387
theorem B3295727 : Blo 2195435 3295727 := bstep (se 1 (by rfl) ⟨2471795, by rfl⟩ : syracuseStep 3295727 = 4943591) B4943591
theorem B2197151 : Blo 2195435 2197151 := bstep (se 1 (by rfl) ⟨1647863, by rfl⟩ : syracuseStep 2197151 = 3295727) B3295727
theorem B3295733 : Blo 2195435 3295733 := bbase (se 5 (by rfl) ⟨154487, by rfl⟩ : syracuseStep 3295733 = 308975) (by norm_num)
theorem B2197155 : Blo 2195435 2197155 := bstep (se 1 (by rfl) ⟨1647866, by rfl⟩ : syracuseStep 2197155 = 3295733) B3295733
theorem B6256757 : Blo 2195435 6256757 := bbase (se 5 (by rfl) ⟨293285, by rfl⟩ : syracuseStep 6256757 = 586571) (by norm_num)
theorem B4171171 : Blo 2195435 4171171 := bstep (se 1 (by rfl) ⟨3128378, by rfl⟩ : syracuseStep 4171171 = 6256757) B6256757
theorem B5561561 : Blo 2195435 5561561 := bstep (se 2 (by rfl) ⟨2085585, by rfl⟩ : syracuseStep 5561561 = 4171171) B4171171
theorem B3707707 : Blo 2195435 3707707 := bstep (se 1 (by rfl) ⟨2780780, by rfl⟩ : syracuseStep 3707707 = 5561561) B5561561
theorem B4943609 : Blo 2195435 4943609 := bstep (se 2 (by rfl) ⟨1853853, by rfl⟩ : syracuseStep 4943609 = 3707707) B3707707
theorem B3295739 : Blo 2195435 3295739 := bstep (se 1 (by rfl) ⟨2471804, by rfl⟩ : syracuseStep 3295739 = 4943609) B4943609
theorem B2197159 : Blo 2195435 2197159 := bstep (se 1 (by rfl) ⟨1647869, by rfl⟩ : syracuseStep 2197159 = 3295739) B3295739
theorem B2471809 : Blo 2195435 2471809 := bbase (se 2 (by rfl) ⟨926928, by rfl⟩ : syracuseStep 2471809 = 1853857) (by norm_num)
theorem B3295745 : Blo 2195435 3295745 := bstep (se 2 (by rfl) ⟨1235904, by rfl⟩ : syracuseStep 3295745 = 2471809) B2471809
theorem B2197163 : Blo 2195435 2197163 := bstep (se 1 (by rfl) ⟨1647872, by rfl⟩ : syracuseStep 2197163 = 3295745) B3295745
theorem B5561581 : Blo 2195435 5561581 := bbase (se 3 (by rfl) ⟨1042796, by rfl⟩ : syracuseStep 5561581 = 2085593) (by norm_num)
theorem B7415441 : Blo 2195435 7415441 := bstep (se 2 (by rfl) ⟨2780790, by rfl⟩ : syracuseStep 7415441 = 5561581) B5561581
theorem B4943627 : Blo 2195435 4943627 := bstep (se 1 (by rfl) ⟨3707720, by rfl⟩ : syracuseStep 4943627 = 7415441) B7415441
theorem B3295751 : Blo 2195435 3295751 := bstep (se 1 (by rfl) ⟨2471813, by rfl⟩ : syracuseStep 3295751 = 4943627) B4943627
theorem B2197167 : Blo 2195435 2197167 := bstep (se 1 (by rfl) ⟨1647875, by rfl⟩ : syracuseStep 2197167 = 3295751) B3295751
theorem B3295757 : Blo 2195435 3295757 := bbase (se 3 (by rfl) ⟨617954, by rfl⟩ : syracuseStep 3295757 = 1235909) (by norm_num)
theorem B2197171 : Blo 2195435 2197171 := bstep (se 1 (by rfl) ⟨1647878, by rfl⟩ : syracuseStep 2197171 = 3295757) B3295757
theorem B4943645 : Blo 2195435 4943645 := bbase (se 3 (by rfl) ⟨926933, by rfl⟩ : syracuseStep 4943645 = 1853867) (by norm_num)
theorem B3295763 : Blo 2195435 3295763 := bstep (se 1 (by rfl) ⟨2471822, by rfl⟩ : syracuseStep 3295763 = 4943645) B4943645
theorem B2197175 : Blo 2195435 2197175 := bstep (se 1 (by rfl) ⟨1647881, by rfl⟩ : syracuseStep 2197175 = 3295763) B3295763
theorem B3707741 : Blo 2195435 3707741 := bbase (se 3 (by rfl) ⟨695201, by rfl⟩ : syracuseStep 3707741 = 1390403) (by norm_num)
theorem B2471827 : Blo 2195435 2471827 := bstep (se 1 (by rfl) ⟨1853870, by rfl⟩ : syracuseStep 2471827 = 3707741) B3707741
theorem B3295769 : Blo 2195435 3295769 := bstep (se 2 (by rfl) ⟨1235913, by rfl⟩ : syracuseStep 3295769 = 2471827) B2471827
theorem B2197179 : Blo 2195435 2197179 := bstep (se 1 (by rfl) ⟨1647884, by rfl⟩ : syracuseStep 2197179 = 3295769) B3295769
theorem B9385237 : Blo 2195435 9385237 := bbase (se 6 (by rfl) ⟨219966, by rfl⟩ : syracuseStep 9385237 = 439933) (by norm_num)
theorem B12513649 : Blo 2195435 12513649 := bstep (se 2 (by rfl) ⟨4692618, by rfl⟩ : syracuseStep 12513649 = 9385237) B9385237
theorem B16684865 : Blo 2195435 16684865 := bstep (se 2 (by rfl) ⟨6256824, by rfl⟩ : syracuseStep 16684865 = 12513649) B12513649
theorem B11123243 : Blo 2195435 11123243 := bstep (se 1 (by rfl) ⟨8342432, by rfl⟩ : syracuseStep 11123243 = 16684865) B16684865
theorem B7415495 : Blo 2195435 7415495 := bstep (se 1 (by rfl) ⟨5561621, by rfl⟩ : syracuseStep 7415495 = 11123243) B11123243
theorem B4943663 : Blo 2195435 4943663 := bstep (se 1 (by rfl) ⟨3707747, by rfl⟩ : syracuseStep 4943663 = 7415495) B7415495
theorem B3295775 : Blo 2195435 3295775 := bstep (se 1 (by rfl) ⟨2471831, by rfl⟩ : syracuseStep 3295775 = 4943663) B4943663
theorem B2197183 : Blo 2195435 2197183 := bstep (se 1 (by rfl) ⟨1647887, by rfl⟩ : syracuseStep 2197183 = 3295775) B3295775
theorem B3295781 : Blo 2195435 3295781 := bbase (se 4 (by rfl) ⟨308979, by rfl⟩ : syracuseStep 3295781 = 617959) (by norm_num)
theorem B2197187 : Blo 2195435 2197187 := bstep (se 1 (by rfl) ⟨1647890, by rfl⟩ : syracuseStep 2197187 = 3295781) B3295781
theorem B2780821 : Blo 2195435 2780821 := bbase (se 6 (by rfl) ⟨65175, by rfl⟩ : syracuseStep 2780821 = 130351) (by norm_num)
theorem B3707761 : Blo 2195435 3707761 := bstep (se 2 (by rfl) ⟨1390410, by rfl⟩ : syracuseStep 3707761 = 2780821) B2780821
theorem B4943681 : Blo 2195435 4943681 := bstep (se 2 (by rfl) ⟨1853880, by rfl⟩ : syracuseStep 4943681 = 3707761) B3707761
theorem B3295787 : Blo 2195435 3295787 := bstep (se 1 (by rfl) ⟨2471840, by rfl⟩ : syracuseStep 3295787 = 4943681) B4943681
theorem B2197191 : Blo 2195435 2197191 := bstep (se 1 (by rfl) ⟨1647893, by rfl⟩ : syracuseStep 2197191 = 3295787) B3295787
theorem B2471845 : Blo 2195435 2471845 := bbase (se 4 (by rfl) ⟨231735, by rfl⟩ : syracuseStep 2471845 = 463471) (by norm_num)
theorem B3295793 : Blo 2195435 3295793 := bstep (se 2 (by rfl) ⟨1235922, by rfl⟩ : syracuseStep 3295793 = 2471845) B2471845
theorem B2197195 : Blo 2195435 2197195 := bstep (se 1 (by rfl) ⟨1647896, by rfl⟩ : syracuseStep 2197195 = 3295793) B3295793
theorem B2257565 : Blo 2195435 2257565 := bbase (se 3 (by rfl) ⟨423293, by rfl⟩ : syracuseStep 2257565 = 846587) (by norm_num)
theorem B6020173 : Blo 2195435 6020173 := bstep (se 3 (by rfl) ⟨1128782, by rfl⟩ : syracuseStep 6020173 = 2257565) B2257565
theorem B32107589 : Blo 2195435 32107589 := bstep (se 4 (by rfl) ⟨3010086, by rfl⟩ : syracuseStep 32107589 = 6020173) B6020173
theorem B21405059 : Blo 2195435 21405059 := bstep (se 1 (by rfl) ⟨16053794, by rfl⟩ : syracuseStep 21405059 = 32107589) B32107589
theorem B14270039 : Blo 2195435 14270039 := bstep (se 1 (by rfl) ⟨10702529, by rfl⟩ : syracuseStep 14270039 = 21405059) B21405059
theorem B9513359 : Blo 2195435 9513359 := bstep (se 1 (by rfl) ⟨7135019, by rfl⟩ : syracuseStep 9513359 = 14270039) B14270039
theorem B6342239 : Blo 2195435 6342239 := bstep (se 1 (by rfl) ⟨4756679, by rfl⟩ : syracuseStep 6342239 = 9513359) B9513359
theorem B4228159 : Blo 2195435 4228159 := bstep (se 1 (by rfl) ⟨3171119, by rfl⟩ : syracuseStep 4228159 = 6342239) B6342239
theorem B5637545 : Blo 2195435 5637545 := bstep (se 2 (by rfl) ⟨2114079, by rfl⟩ : syracuseStep 5637545 = 4228159) B4228159
theorem B3758363 : Blo 2195435 3758363 := bstep (se 1 (by rfl) ⟨2818772, by rfl⟩ : syracuseStep 3758363 = 5637545) B5637545
theorem B2505575 : Blo 2195435 2505575 := bstep (se 1 (by rfl) ⟨1879181, by rfl⟩ : syracuseStep 2505575 = 3758363) B3758363
theorem B6681533 : Blo 2195435 6681533 := bstep (se 3 (by rfl) ⟨1252787, by rfl⟩ : syracuseStep 6681533 = 2505575) B2505575
theorem B17817421 : Blo 2195435 17817421 := bstep (se 3 (by rfl) ⟨3340766, by rfl⟩ : syracuseStep 17817421 = 6681533) B6681533
theorem B23756561 : Blo 2195435 23756561 := bstep (se 2 (by rfl) ⟨8908710, by rfl⟩ : syracuseStep 23756561 = 17817421) B17817421
theorem B15837707 : Blo 2195435 15837707 := bstep (se 1 (by rfl) ⟨11878280, by rfl⟩ : syracuseStep 15837707 = 23756561) B23756561
theorem B10558471 : Blo 2195435 10558471 := bstep (se 1 (by rfl) ⟨7918853, by rfl⟩ : syracuseStep 10558471 = 15837707) B15837707
theorem B14077961 : Blo 2195435 14077961 := bstep (se 2 (by rfl) ⟨5279235, by rfl⟩ : syracuseStep 14077961 = 10558471) B10558471
theorem B9385307 : Blo 2195435 9385307 := bstep (se 1 (by rfl) ⟨7038980, by rfl⟩ : syracuseStep 9385307 = 14077961) B14077961
theorem B6256871 : Blo 2195435 6256871 := bstep (se 1 (by rfl) ⟨4692653, by rfl⟩ : syracuseStep 6256871 = 9385307) B9385307
theorem B4171247 : Blo 2195435 4171247 := bstep (se 1 (by rfl) ⟨3128435, by rfl⟩ : syracuseStep 4171247 = 6256871) B6256871
theorem B2780831 : Blo 2195435 2780831 := bstep (se 1 (by rfl) ⟨2085623, by rfl⟩ : syracuseStep 2780831 = 4171247) B4171247
theorem B7415549 : Blo 2195435 7415549 := bstep (se 3 (by rfl) ⟨1390415, by rfl⟩ : syracuseStep 7415549 = 2780831) B2780831
theorem B4943699 : Blo 2195435 4943699 := bstep (se 1 (by rfl) ⟨3707774, by rfl⟩ : syracuseStep 4943699 = 7415549) B7415549
theorem B3295799 : Blo 2195435 3295799 := bstep (se 1 (by rfl) ⟨2471849, by rfl⟩ : syracuseStep 3295799 = 4943699) B4943699
theorem B2197199 : Blo 2195435 2197199 := bstep (se 1 (by rfl) ⟨1647899, by rfl⟩ : syracuseStep 2197199 = 3295799) B3295799
theorem B3295805 : Blo 2195435 3295805 := bbase (se 3 (by rfl) ⟨617963, by rfl⟩ : syracuseStep 3295805 = 1235927) (by norm_num)
theorem B2197203 : Blo 2195435 2197203 := bstep (se 1 (by rfl) ⟨1647902, by rfl⟩ : syracuseStep 2197203 = 3295805) B3295805
theorem B4943717 : Blo 2195435 4943717 := bbase (se 4 (by rfl) ⟨463473, by rfl⟩ : syracuseStep 4943717 = 926947) (by norm_num)
theorem B3295811 : Blo 2195435 3295811 := bstep (se 1 (by rfl) ⟨2471858, by rfl⟩ : syracuseStep 3295811 = 4943717) B4943717
theorem B2197207 : Blo 2195435 2197207 := bstep (se 1 (by rfl) ⟨1647905, by rfl⟩ : syracuseStep 2197207 = 3295811) B3295811
theorem B5561693 : Blo 2195435 5561693 := bbase (se 3 (by rfl) ⟨1042817, by rfl⟩ : syracuseStep 5561693 = 2085635) (by norm_num)
theorem B3707795 : Blo 2195435 3707795 := bstep (se 1 (by rfl) ⟨2780846, by rfl⟩ : syracuseStep 3707795 = 5561693) B5561693
theorem B2471863 : Blo 2195435 2471863 := bstep (se 1 (by rfl) ⟨1853897, by rfl⟩ : syracuseStep 2471863 = 3707795) B3707795
theorem B3295817 : Blo 2195435 3295817 := bstep (se 2 (by rfl) ⟨1235931, by rfl⟩ : syracuseStep 3295817 = 2471863) B2471863
theorem B2197211 : Blo 2195435 2197211 := bstep (se 1 (by rfl) ⟨1647908, by rfl⟩ : syracuseStep 2197211 = 3295817) B3295817
theorem B4171277 : Blo 2195435 4171277 := bbase (se 3 (by rfl) ⟨782114, by rfl⟩ : syracuseStep 4171277 = 1564229) (by norm_num)
theorem B11123405 : Blo 2195435 11123405 := bstep (se 3 (by rfl) ⟨2085638, by rfl⟩ : syracuseStep 11123405 = 4171277) B4171277
theorem B7415603 : Blo 2195435 7415603 := bstep (se 1 (by rfl) ⟨5561702, by rfl⟩ : syracuseStep 7415603 = 11123405) B11123405
theorem B4943735 : Blo 2195435 4943735 := bstep (se 1 (by rfl) ⟨3707801, by rfl⟩ : syracuseStep 4943735 = 7415603) B7415603
theorem B3295823 : Blo 2195435 3295823 := bstep (se 1 (by rfl) ⟨2471867, by rfl⟩ : syracuseStep 3295823 = 4943735) B4943735
theorem B2197215 : Blo 2195435 2197215 := bstep (se 1 (by rfl) ⟨1647911, by rfl⟩ : syracuseStep 2197215 = 3295823) B3295823
theorem B3295829 : Blo 2195435 3295829 := bbase (se 8 (by rfl) ⟨19311, by rfl⟩ : syracuseStep 3295829 = 38623) (by norm_num)
theorem B2197219 : Blo 2195435 2197219 := bstep (se 1 (by rfl) ⟨1647914, by rfl⟩ : syracuseStep 2197219 = 3295829) B3295829
theorem B5279293 : Blo 2195435 5279293 := bbase (se 3 (by rfl) ⟨989867, by rfl⟩ : syracuseStep 5279293 = 1979735) (by norm_num)
theorem B7039057 : Blo 2195435 7039057 := bstep (se 2 (by rfl) ⟨2639646, by rfl⟩ : syracuseStep 7039057 = 5279293) B5279293
theorem B9385409 : Blo 2195435 9385409 := bstep (se 2 (by rfl) ⟨3519528, by rfl⟩ : syracuseStep 9385409 = 7039057) B7039057
theorem B6256939 : Blo 2195435 6256939 := bstep (se 1 (by rfl) ⟨4692704, by rfl⟩ : syracuseStep 6256939 = 9385409) B9385409
theorem B8342585 : Blo 2195435 8342585 := bstep (se 2 (by rfl) ⟨3128469, by rfl⟩ : syracuseStep 8342585 = 6256939) B6256939
theorem B5561723 : Blo 2195435 5561723 := bstep (se 1 (by rfl) ⟨4171292, by rfl⟩ : syracuseStep 5561723 = 8342585) B8342585
theorem B3707815 : Blo 2195435 3707815 := bstep (se 1 (by rfl) ⟨2780861, by rfl⟩ : syracuseStep 3707815 = 5561723) B5561723
theorem B4943753 : Blo 2195435 4943753 := bstep (se 2 (by rfl) ⟨1853907, by rfl⟩ : syracuseStep 4943753 = 3707815) B3707815
theorem B3295835 : Blo 2195435 3295835 := bstep (se 1 (by rfl) ⟨2471876, by rfl⟩ : syracuseStep 3295835 = 4943753) B4943753
theorem B2197223 : Blo 2195435 2197223 := bstep (se 1 (by rfl) ⟨1647917, by rfl⟩ : syracuseStep 2197223 = 3295835) B3295835
theorem B2471881 : Blo 2195435 2471881 := bbase (se 2 (by rfl) ⟨926955, by rfl⟩ : syracuseStep 2471881 = 1853911) (by norm_num)
theorem B3295841 : Blo 2195435 3295841 := bstep (se 2 (by rfl) ⟨1235940, by rfl⟩ : syracuseStep 3295841 = 2471881) B2471881
theorem B2197227 : Blo 2195435 2197227 := bstep (se 1 (by rfl) ⟨1647920, by rfl⟩ : syracuseStep 2197227 = 3295841) B3295841
theorem B3519541 : Blo 2195435 3519541 := bbase (se 5 (by rfl) ⟨164978, by rfl⟩ : syracuseStep 3519541 = 329957) (by norm_num)
theorem B18770885 : Blo 2195435 18770885 := bstep (se 4 (by rfl) ⟨1759770, by rfl⟩ : syracuseStep 18770885 = 3519541) B3519541
theorem B12513923 : Blo 2195435 12513923 := bstep (se 1 (by rfl) ⟨9385442, by rfl⟩ : syracuseStep 12513923 = 18770885) B18770885
theorem B8342615 : Blo 2195435 8342615 := bstep (se 1 (by rfl) ⟨6256961, by rfl⟩ : syracuseStep 8342615 = 12513923) B12513923
theorem B5561743 : Blo 2195435 5561743 := bstep (se 1 (by rfl) ⟨4171307, by rfl⟩ : syracuseStep 5561743 = 8342615) B8342615
theorem B7415657 : Blo 2195435 7415657 := bstep (se 2 (by rfl) ⟨2780871, by rfl⟩ : syracuseStep 7415657 = 5561743) B5561743
theorem B4943771 : Blo 2195435 4943771 := bstep (se 1 (by rfl) ⟨3707828, by rfl⟩ : syracuseStep 4943771 = 7415657) B7415657
theorem B3295847 : Blo 2195435 3295847 := bstep (se 1 (by rfl) ⟨2471885, by rfl⟩ : syracuseStep 3295847 = 4943771) B4943771
theorem B2197231 : Blo 2195435 2197231 := bstep (se 1 (by rfl) ⟨1647923, by rfl⟩ : syracuseStep 2197231 = 3295847) B3295847
theorem B3295853 : Blo 2195435 3295853 := bbase (se 3 (by rfl) ⟨617972, by rfl⟩ : syracuseStep 3295853 = 1235945) (by norm_num)
theorem B2197235 : Blo 2195435 2197235 := bstep (se 1 (by rfl) ⟨1647926, by rfl⟩ : syracuseStep 2197235 = 3295853) B3295853
theorem B4943789 : Blo 2195435 4943789 := bbase (se 3 (by rfl) ⟨926960, by rfl⟩ : syracuseStep 4943789 = 1853921) (by norm_num)
theorem B3295859 : Blo 2195435 3295859 := bstep (se 1 (by rfl) ⟨2471894, by rfl⟩ : syracuseStep 3295859 = 4943789) B4943789
theorem B2197239 : Blo 2195435 2197239 := bstep (se 1 (by rfl) ⟨1647929, by rfl⟩ : syracuseStep 2197239 = 3295859) B3295859
theorem B6256997 : Blo 2195435 6256997 := bbase (se 4 (by rfl) ⟨586593, by rfl⟩ : syracuseStep 6256997 = 1173187) (by norm_num)
theorem B4171331 : Blo 2195435 4171331 := bstep (se 1 (by rfl) ⟨3128498, by rfl⟩ : syracuseStep 4171331 = 6256997) B6256997
theorem B2780887 : Blo 2195435 2780887 := bstep (se 1 (by rfl) ⟨2085665, by rfl⟩ : syracuseStep 2780887 = 4171331) B4171331
theorem B3707849 : Blo 2195435 3707849 := bstep (se 2 (by rfl) ⟨1390443, by rfl⟩ : syracuseStep 3707849 = 2780887) B2780887
theorem B2471899 : Blo 2195435 2471899 := bstep (se 1 (by rfl) ⟨1853924, by rfl⟩ : syracuseStep 2471899 = 3707849) B3707849
theorem B3295865 : Blo 2195435 3295865 := bstep (se 2 (by rfl) ⟨1235949, by rfl⟩ : syracuseStep 3295865 = 2471899) B2471899
theorem B2197243 : Blo 2195435 2197243 := bstep (se 1 (by rfl) ⟨1647932, by rfl⟩ : syracuseStep 2197243 = 3295865) B3295865
theorem B10702757 : Blo 2195435 10702757 := bbase (se 4 (by rfl) ⟨1003383, by rfl⟩ : syracuseStep 10702757 = 2006767) (by norm_num)
theorem B7135171 : Blo 2195435 7135171 := bstep (se 1 (by rfl) ⟨5351378, by rfl⟩ : syracuseStep 7135171 = 10702757) B10702757
theorem B38054245 : Blo 2195435 38054245 := bstep (se 4 (by rfl) ⟨3567585, by rfl⟩ : syracuseStep 38054245 = 7135171) B7135171
theorem B50738993 : Blo 2195435 50738993 := bstep (se 2 (by rfl) ⟨19027122, by rfl⟩ : syracuseStep 50738993 = 38054245) B38054245
theorem B33825995 : Blo 2195435 33825995 := bstep (se 1 (by rfl) ⟨25369496, by rfl⟩ : syracuseStep 33825995 = 50738993) B50738993
theorem B22550663 : Blo 2195435 22550663 := bstep (se 1 (by rfl) ⟨16912997, by rfl⟩ : syracuseStep 22550663 = 33825995) B33825995
theorem B15033775 : Blo 2195435 15033775 := bstep (se 1 (by rfl) ⟨11275331, by rfl⟩ : syracuseStep 15033775 = 22550663) B22550663
theorem B20045033 : Blo 2195435 20045033 := bstep (se 2 (by rfl) ⟨7516887, by rfl⟩ : syracuseStep 20045033 = 15033775) B15033775
theorem B13363355 : Blo 2195435 13363355 := bstep (se 1 (by rfl) ⟨10022516, by rfl⟩ : syracuseStep 13363355 = 20045033) B20045033
theorem B8908903 : Blo 2195435 8908903 := bstep (se 1 (by rfl) ⟨6681677, by rfl⟩ : syracuseStep 8908903 = 13363355) B13363355
theorem B11878537 : Blo 2195435 11878537 := bstep (se 2 (by rfl) ⟨4454451, by rfl⟩ : syracuseStep 11878537 = 8908903) B8908903
theorem B15838049 : Blo 2195435 15838049 := bstep (se 2 (by rfl) ⟨5939268, by rfl⟩ : syracuseStep 15838049 = 11878537) B11878537
theorem B42234797 : Blo 2195435 42234797 := bstep (se 3 (by rfl) ⟨7919024, by rfl⟩ : syracuseStep 42234797 = 15838049) B15838049
theorem B28156531 : Blo 2195435 28156531 := bstep (se 1 (by rfl) ⟨21117398, by rfl⟩ : syracuseStep 28156531 = 42234797) B42234797
theorem B37542041 : Blo 2195435 37542041 := bstep (se 2 (by rfl) ⟨14078265, by rfl⟩ : syracuseStep 37542041 = 28156531) B28156531
theorem B25028027 : Blo 2195435 25028027 := bstep (se 1 (by rfl) ⟨18771020, by rfl⟩ : syracuseStep 25028027 = 37542041) B37542041
theorem B16685351 : Blo 2195435 16685351 := bstep (se 1 (by rfl) ⟨12514013, by rfl⟩ : syracuseStep 16685351 = 25028027) B25028027
theorem B11123567 : Blo 2195435 11123567 := bstep (se 1 (by rfl) ⟨8342675, by rfl⟩ : syracuseStep 11123567 = 16685351) B16685351
theorem B7415711 : Blo 2195435 7415711 := bstep (se 1 (by rfl) ⟨5561783, by rfl⟩ : syracuseStep 7415711 = 11123567) B11123567
theorem B4943807 : Blo 2195435 4943807 := bstep (se 1 (by rfl) ⟨3707855, by rfl⟩ : syracuseStep 4943807 = 7415711) B7415711
theorem B3295871 : Blo 2195435 3295871 := bstep (se 1 (by rfl) ⟨2471903, by rfl⟩ : syracuseStep 3295871 = 4943807) B4943807
theorem B2197247 : Blo 2195435 2197247 := bstep (se 1 (by rfl) ⟨1647935, by rfl⟩ : syracuseStep 2197247 = 3295871) B3295871
theorem B3295877 : Blo 2195435 3295877 := bbase (se 4 (by rfl) ⟨308988, by rfl⟩ : syracuseStep 3295877 = 617977) (by norm_num)
theorem B2197251 : Blo 2195435 2197251 := bstep (se 1 (by rfl) ⟨1647938, by rfl⟩ : syracuseStep 2197251 = 3295877) B3295877
theorem B3707869 : Blo 2195435 3707869 := bbase (se 3 (by rfl) ⟨695225, by rfl⟩ : syracuseStep 3707869 = 1390451) (by norm_num)
theorem B4943825 : Blo 2195435 4943825 := bstep (se 2 (by rfl) ⟨1853934, by rfl⟩ : syracuseStep 4943825 = 3707869) B3707869
theorem B3295883 : Blo 2195435 3295883 := bstep (se 1 (by rfl) ⟨2471912, by rfl⟩ : syracuseStep 3295883 = 4943825) B4943825
theorem B2197255 : Blo 2195435 2197255 := bstep (se 1 (by rfl) ⟨1647941, by rfl⟩ : syracuseStep 2197255 = 3295883) B3295883
theorem B2471917 : Blo 2195435 2471917 := bbase (se 3 (by rfl) ⟨463484, by rfl⟩ : syracuseStep 2471917 = 926969) (by norm_num)
theorem B3295889 : Blo 2195435 3295889 := bstep (se 2 (by rfl) ⟨1235958, by rfl⟩ : syracuseStep 3295889 = 2471917) B2471917
theorem B2197259 : Blo 2195435 2197259 := bstep (se 1 (by rfl) ⟨1647944, by rfl⟩ : syracuseStep 2197259 = 3295889) B3295889
theorem B7415765 : Blo 2195435 7415765 := bbase (se 7 (by rfl) ⟨86903, by rfl⟩ : syracuseStep 7415765 = 173807) (by norm_num)
theorem B4943843 : Blo 2195435 4943843 := bstep (se 1 (by rfl) ⟨3707882, by rfl⟩ : syracuseStep 4943843 = 7415765) B7415765
theorem B3295895 : Blo 2195435 3295895 := bstep (se 1 (by rfl) ⟨2471921, by rfl⟩ : syracuseStep 3295895 = 4943843) B4943843
theorem B2197263 : Blo 2195435 2197263 := bstep (se 1 (by rfl) ⟨1647947, by rfl⟩ : syracuseStep 2197263 = 3295895) B3295895
theorem B3295901 : Blo 2195435 3295901 := bbase (se 3 (by rfl) ⟨617981, by rfl⟩ : syracuseStep 3295901 = 1235963) (by norm_num)
theorem B2197267 : Blo 2195435 2197267 := bstep (se 1 (by rfl) ⟨1647950, by rfl⟩ : syracuseStep 2197267 = 3295901) B3295901
theorem B4943861 : Blo 2195435 4943861 := bbase (se 5 (by rfl) ⟨231743, by rfl⟩ : syracuseStep 4943861 = 463487) (by norm_num)
theorem B3295907 : Blo 2195435 3295907 := bstep (se 1 (by rfl) ⟨2471930, by rfl⟩ : syracuseStep 3295907 = 4943861) B4943861
theorem B2197271 : Blo 2195435 2197271 := bstep (se 1 (by rfl) ⟨1647953, by rfl⟩ : syracuseStep 2197271 = 3295907) B3295907
theorem B2712229 : Blo 2195435 2712229 := bbase (se 4 (by rfl) ⟨254271, by rfl⟩ : syracuseStep 2712229 = 508543) (by norm_num)
theorem B14465221 : Blo 2195435 14465221 := bstep (se 4 (by rfl) ⟨1356114, by rfl⟩ : syracuseStep 14465221 = 2712229) B2712229
theorem B77147845 : Blo 2195435 77147845 := bstep (se 4 (by rfl) ⟨7232610, by rfl⟩ : syracuseStep 77147845 = 14465221) B14465221
theorem B411455173 : Blo 2195435 411455173 := bstep (se 4 (by rfl) ⟨38573922, by rfl⟩ : syracuseStep 411455173 = 77147845) B77147845
theorem B548606897 : Blo 2195435 548606897 := bstep (se 2 (by rfl) ⟨205727586, by rfl⟩ : syracuseStep 548606897 = 411455173) B411455173
theorem B365737931 : Blo 2195435 365737931 := bstep (se 1 (by rfl) ⟨274303448, by rfl⟩ : syracuseStep 365737931 = 548606897) B548606897
theorem B243825287 : Blo 2195435 243825287 := bstep (se 1 (by rfl) ⟨182868965, by rfl⟩ : syracuseStep 243825287 = 365737931) B365737931
theorem B650200765 : Blo 2195435 650200765 := bstep (se 3 (by rfl) ⟨121912643, by rfl⟩ : syracuseStep 650200765 = 243825287) B243825287
theorem B866934353 : Blo 2195435 866934353 := bstep (se 2 (by rfl) ⟨325100382, by rfl⟩ : syracuseStep 866934353 = 650200765) B650200765
theorem B577956235 : Blo 2195435 577956235 := bstep (se 1 (by rfl) ⟨433467176, by rfl⟩ : syracuseStep 577956235 = 866934353) B866934353
theorem B770608313 : Blo 2195435 770608313 := bstep (se 2 (by rfl) ⟨288978117, by rfl⟩ : syracuseStep 770608313 = 577956235) B577956235
theorem B513738875 : Blo 2195435 513738875 := bstep (se 1 (by rfl) ⟨385304156, by rfl⟩ : syracuseStep 513738875 = 770608313) B770608313
theorem B342492583 : Blo 2195435 342492583 := bstep (se 1 (by rfl) ⟨256869437, by rfl⟩ : syracuseStep 342492583 = 513738875) B513738875
theorem B456656777 : Blo 2195435 456656777 := bstep (se 2 (by rfl) ⟨171246291, by rfl⟩ : syracuseStep 456656777 = 342492583) B342492583
theorem B304437851 : Blo 2195435 304437851 := bstep (se 1 (by rfl) ⟨228328388, by rfl⟩ : syracuseStep 304437851 = 456656777) B456656777
theorem B202958567 : Blo 2195435 202958567 := bstep (se 1 (by rfl) ⟨152218925, by rfl⟩ : syracuseStep 202958567 = 304437851) B304437851
theorem B135305711 : Blo 2195435 135305711 := bstep (se 1 (by rfl) ⟨101479283, by rfl⟩ : syracuseStep 135305711 = 202958567) B202958567
theorem B90203807 : Blo 2195435 90203807 := bstep (se 1 (by rfl) ⟨67652855, by rfl⟩ : syracuseStep 90203807 = 135305711) B135305711
theorem B60135871 : Blo 2195435 60135871 := bstep (se 1 (by rfl) ⟨45101903, by rfl⟩ : syracuseStep 60135871 = 90203807) B90203807
theorem B80181161 : Blo 2195435 80181161 := bstep (se 2 (by rfl) ⟨30067935, by rfl⟩ : syracuseStep 80181161 = 60135871) B60135871
theorem B53454107 : Blo 2195435 53454107 := bstep (se 1 (by rfl) ⟨40090580, by rfl⟩ : syracuseStep 53454107 = 80181161) B80181161
theorem B142544285 : Blo 2195435 142544285 := bstep (se 3 (by rfl) ⟨26727053, by rfl⟩ : syracuseStep 142544285 = 53454107) B53454107
theorem B95029523 : Blo 2195435 95029523 := bstep (se 1 (by rfl) ⟨71272142, by rfl⟩ : syracuseStep 95029523 = 142544285) B142544285
theorem B63353015 : Blo 2195435 63353015 := bstep (se 1 (by rfl) ⟨47514761, by rfl⟩ : syracuseStep 63353015 = 95029523) B95029523
theorem B42235343 : Blo 2195435 42235343 := bstep (se 1 (by rfl) ⟨31676507, by rfl⟩ : syracuseStep 42235343 = 63353015) B63353015
theorem B28156895 : Blo 2195435 28156895 := bstep (se 1 (by rfl) ⟨21117671, by rfl⟩ : syracuseStep 28156895 = 42235343) B42235343
theorem B18771263 : Blo 2195435 18771263 := bstep (se 1 (by rfl) ⟨14078447, by rfl⟩ : syracuseStep 18771263 = 28156895) B28156895
theorem B12514175 : Blo 2195435 12514175 := bstep (se 1 (by rfl) ⟨9385631, by rfl⟩ : syracuseStep 12514175 = 18771263) B18771263
theorem B8342783 : Blo 2195435 8342783 := bstep (se 1 (by rfl) ⟨6257087, by rfl⟩ : syracuseStep 8342783 = 12514175) B12514175
theorem B5561855 : Blo 2195435 5561855 := bstep (se 1 (by rfl) ⟨4171391, by rfl⟩ : syracuseStep 5561855 = 8342783) B8342783
theorem B3707903 : Blo 2195435 3707903 := bstep (se 1 (by rfl) ⟨2780927, by rfl⟩ : syracuseStep 3707903 = 5561855) B5561855
theorem B2471935 : Blo 2195435 2471935 := bstep (se 1 (by rfl) ⟨1853951, by rfl⟩ : syracuseStep 2471935 = 3707903) B3707903
theorem B3295913 : Blo 2195435 3295913 := bstep (se 2 (by rfl) ⟨1235967, by rfl⟩ : syracuseStep 3295913 = 2471935) B2471935
theorem B2197275 : Blo 2195435 2197275 := bstep (se 1 (by rfl) ⟨1647956, by rfl⟩ : syracuseStep 2197275 = 3295913) B3295913
theorem B3128549 : Blo 2195435 3128549 := bbase (se 4 (by rfl) ⟨293301, by rfl⟩ : syracuseStep 3128549 = 586603) (by norm_num)
theorem B8342797 : Blo 2195435 8342797 := bstep (se 3 (by rfl) ⟨1564274, by rfl⟩ : syracuseStep 8342797 = 3128549) B3128549
theorem B11123729 : Blo 2195435 11123729 := bstep (se 2 (by rfl) ⟨4171398, by rfl⟩ : syracuseStep 11123729 = 8342797) B8342797
theorem B7415819 : Blo 2195435 7415819 := bstep (se 1 (by rfl) ⟨5561864, by rfl⟩ : syracuseStep 7415819 = 11123729) B11123729
theorem B4943879 : Blo 2195435 4943879 := bstep (se 1 (by rfl) ⟨3707909, by rfl⟩ : syracuseStep 4943879 = 7415819) B7415819
theorem B3295919 : Blo 2195435 3295919 := bstep (se 1 (by rfl) ⟨2471939, by rfl⟩ : syracuseStep 3295919 = 4943879) B4943879
theorem B2197279 : Blo 2195435 2197279 := bstep (se 1 (by rfl) ⟨1647959, by rfl⟩ : syracuseStep 2197279 = 3295919) B3295919
theorem B3295925 : Blo 2195435 3295925 := bbase (se 5 (by rfl) ⟨154496, by rfl⟩ : syracuseStep 3295925 = 308993) (by norm_num)
theorem B2197283 : Blo 2195435 2197283 := bstep (se 1 (by rfl) ⟨1647962, by rfl⟩ : syracuseStep 2197283 = 3295925) B3295925
theorem B5561885 : Blo 2195435 5561885 := bbase (se 3 (by rfl) ⟨1042853, by rfl⟩ : syracuseStep 5561885 = 2085707) (by norm_num)
theorem B3707923 : Blo 2195435 3707923 := bstep (se 1 (by rfl) ⟨2780942, by rfl⟩ : syracuseStep 3707923 = 5561885) B5561885
theorem B4943897 : Blo 2195435 4943897 := bstep (se 2 (by rfl) ⟨1853961, by rfl⟩ : syracuseStep 4943897 = 3707923) B3707923
theorem B3295931 : Blo 2195435 3295931 := bstep (se 1 (by rfl) ⟨2471948, by rfl⟩ : syracuseStep 3295931 = 4943897) B4943897
theorem B2197287 : Blo 2195435 2197287 := bstep (se 1 (by rfl) ⟨1647965, by rfl⟩ : syracuseStep 2197287 = 3295931) B3295931
theorem B2471953 : Blo 2195435 2471953 := bbase (se 2 (by rfl) ⟨926982, by rfl⟩ : syracuseStep 2471953 = 1853965) (by norm_num)
theorem B3295937 : Blo 2195435 3295937 := bstep (se 2 (by rfl) ⟨1235976, by rfl⟩ : syracuseStep 3295937 = 2471953) B2471953
theorem B2197291 : Blo 2195435 2197291 := bstep (se 1 (by rfl) ⟨1647968, by rfl⟩ : syracuseStep 2197291 = 3295937) B3295937
theorem B4171429 : Blo 2195435 4171429 := bbase (se 4 (by rfl) ⟨391071, by rfl⟩ : syracuseStep 4171429 = 782143) (by norm_num)
theorem B5561905 : Blo 2195435 5561905 := bstep (se 2 (by rfl) ⟨2085714, by rfl⟩ : syracuseStep 5561905 = 4171429) B4171429
theorem B7415873 : Blo 2195435 7415873 := bstep (se 2 (by rfl) ⟨2780952, by rfl⟩ : syracuseStep 7415873 = 5561905) B5561905
theorem B4943915 : Blo 2195435 4943915 := bstep (se 1 (by rfl) ⟨3707936, by rfl⟩ : syracuseStep 4943915 = 7415873) B7415873
theorem B3295943 : Blo 2195435 3295943 := bstep (se 1 (by rfl) ⟨2471957, by rfl⟩ : syracuseStep 3295943 = 4943915) B4943915
theorem B2197295 : Blo 2195435 2197295 := bstep (se 1 (by rfl) ⟨1647971, by rfl⟩ : syracuseStep 2197295 = 3295943) B3295943
theorem B3295949 : Blo 2195435 3295949 := bbase (se 3 (by rfl) ⟨617990, by rfl⟩ : syracuseStep 3295949 = 1235981) (by norm_num)
theorem B2197299 : Blo 2195435 2197299 := bstep (se 1 (by rfl) ⟨1647974, by rfl⟩ : syracuseStep 2197299 = 3295949) B3295949
theorem B4943933 : Blo 2195435 4943933 := bbase (se 3 (by rfl) ⟨926987, by rfl⟩ : syracuseStep 4943933 = 1853975) (by norm_num)
theorem B3295955 : Blo 2195435 3295955 := bstep (se 1 (by rfl) ⟨2471966, by rfl⟩ : syracuseStep 3295955 = 4943933) B4943933
theorem B2197303 : Blo 2195435 2197303 := bstep (se 1 (by rfl) ⟨1647977, by rfl⟩ : syracuseStep 2197303 = 3295955) B3295955
theorem B3707957 : Blo 2195435 3707957 := bbase (se 5 (by rfl) ⟨173810, by rfl⟩ : syracuseStep 3707957 = 347621) (by norm_num)
theorem B2471971 : Blo 2195435 2471971 := bstep (se 1 (by rfl) ⟨1853978, by rfl⟩ : syracuseStep 2471971 = 3707957) B3707957
theorem B3295961 : Blo 2195435 3295961 := bstep (se 2 (by rfl) ⟨1235985, by rfl⟩ : syracuseStep 3295961 = 2471971) B2471971
theorem B2197307 : Blo 2195435 2197307 := bstep (se 1 (by rfl) ⟨1647980, by rfl⟩ : syracuseStep 2197307 = 3295961) B3295961
theorem B6257189 : Blo 2195435 6257189 := bbase (se 4 (by rfl) ⟨586611, by rfl⟩ : syracuseStep 6257189 = 1173223) (by norm_num)
theorem B16685837 : Blo 2195435 16685837 := bstep (se 3 (by rfl) ⟨3128594, by rfl⟩ : syracuseStep 16685837 = 6257189) B6257189
theorem B11123891 : Blo 2195435 11123891 := bstep (se 1 (by rfl) ⟨8342918, by rfl⟩ : syracuseStep 11123891 = 16685837) B16685837
theorem B7415927 : Blo 2195435 7415927 := bstep (se 1 (by rfl) ⟨5561945, by rfl⟩ : syracuseStep 7415927 = 11123891) B11123891
theorem B4943951 : Blo 2195435 4943951 := bstep (se 1 (by rfl) ⟨3707963, by rfl⟩ : syracuseStep 4943951 = 7415927) B7415927
theorem B3295967 : Blo 2195435 3295967 := bstep (se 1 (by rfl) ⟨2471975, by rfl⟩ : syracuseStep 3295967 = 4943951) B4943951
theorem B2197311 : Blo 2195435 2197311 := bstep (se 1 (by rfl) ⟨1647983, by rfl⟩ : syracuseStep 2197311 = 3295967) B3295967
theorem B3295973 : Blo 2195435 3295973 := bbase (se 4 (by rfl) ⟨308997, by rfl⟩ : syracuseStep 3295973 = 617995) (by norm_num)
theorem B2197315 : Blo 2195435 2197315 := bstep (se 1 (by rfl) ⟨1647986, by rfl⟩ : syracuseStep 2197315 = 3295973) B3295973
theorem B5279525 : Blo 2195435 5279525 := bbase (se 4 (by rfl) ⟨494955, by rfl⟩ : syracuseStep 5279525 = 989911) (by norm_num)
theorem B3519683 : Blo 2195435 3519683 := bstep (se 1 (by rfl) ⟨2639762, by rfl⟩ : syracuseStep 3519683 = 5279525) B5279525
theorem B2346455 : Blo 2195435 2346455 := bstep (se 1 (by rfl) ⟨1759841, by rfl⟩ : syracuseStep 2346455 = 3519683) B3519683
theorem B6257213 : Blo 2195435 6257213 := bstep (se 3 (by rfl) ⟨1173227, by rfl⟩ : syracuseStep 6257213 = 2346455) B2346455
theorem B4171475 : Blo 2195435 4171475 := bstep (se 1 (by rfl) ⟨3128606, by rfl⟩ : syracuseStep 4171475 = 6257213) B6257213
theorem B2780983 : Blo 2195435 2780983 := bstep (se 1 (by rfl) ⟨2085737, by rfl⟩ : syracuseStep 2780983 = 4171475) B4171475
theorem B3707977 : Blo 2195435 3707977 := bstep (se 2 (by rfl) ⟨1390491, by rfl⟩ : syracuseStep 3707977 = 2780983) B2780983
theorem B4943969 : Blo 2195435 4943969 := bstep (se 2 (by rfl) ⟨1853988, by rfl⟩ : syracuseStep 4943969 = 3707977) B3707977
theorem B3295979 : Blo 2195435 3295979 := bstep (se 1 (by rfl) ⟨2471984, by rfl⟩ : syracuseStep 3295979 = 4943969) B4943969
theorem B2197319 : Blo 2195435 2197319 := bstep (se 1 (by rfl) ⟨1647989, by rfl⟩ : syracuseStep 2197319 = 3295979) B3295979
theorem B2471989 : Blo 2195435 2471989 := bbase (se 5 (by rfl) ⟨115874, by rfl⟩ : syracuseStep 2471989 = 231749) (by norm_num)
theorem B3295985 : Blo 2195435 3295985 := bstep (se 2 (by rfl) ⟨1235994, by rfl⟩ : syracuseStep 3295985 = 2471989) B2471989
theorem B2197323 : Blo 2195435 2197323 := bstep (se 1 (by rfl) ⟨1647992, by rfl⟩ : syracuseStep 2197323 = 3295985) B3295985
theorem B2780993 : Blo 2195435 2780993 := bbase (se 2 (by rfl) ⟨1042872, by rfl⟩ : syracuseStep 2780993 = 2085745) (by norm_num)
theorem B7415981 : Blo 2195435 7415981 := bstep (se 3 (by rfl) ⟨1390496, by rfl⟩ : syracuseStep 7415981 = 2780993) B2780993
theorem B4943987 : Blo 2195435 4943987 := bstep (se 1 (by rfl) ⟨3707990, by rfl⟩ : syracuseStep 4943987 = 7415981) B7415981
theorem B3295991 : Blo 2195435 3295991 := bstep (se 1 (by rfl) ⟨2471993, by rfl⟩ : syracuseStep 3295991 = 4943987) B4943987
theorem B2197327 : Blo 2195435 2197327 := bstep (se 1 (by rfl) ⟨1647995, by rfl⟩ : syracuseStep 2197327 = 3295991) B3295991
theorem B3295997 : Blo 2195435 3295997 := bbase (se 3 (by rfl) ⟨617999, by rfl⟩ : syracuseStep 3295997 = 1235999) (by norm_num)
theorem B2197331 : Blo 2195435 2197331 := bstep (se 1 (by rfl) ⟨1647998, by rfl⟩ : syracuseStep 2197331 = 3295997) B3295997
theorem B4944005 : Blo 2195435 4944005 := bbase (se 4 (by rfl) ⟨463500, by rfl⟩ : syracuseStep 4944005 = 927001) (by norm_num)
theorem B3296003 : Blo 2195435 3296003 := bstep (se 1 (by rfl) ⟨2472002, by rfl⟩ : syracuseStep 3296003 = 4944005) B4944005
theorem B2197335 : Blo 2195435 2197335 := bstep (se 1 (by rfl) ⟨1648001, by rfl⟩ : syracuseStep 2197335 = 3296003) B3296003
theorem B5279573 : Blo 2195435 5279573 := bbase (se 9 (by rfl) ⟨15467, by rfl⟩ : syracuseStep 5279573 = 30935) (by norm_num)
theorem B3519715 : Blo 2195435 3519715 := bstep (se 1 (by rfl) ⟨2639786, by rfl⟩ : syracuseStep 3519715 = 5279573) B5279573
theorem B4692953 : Blo 2195435 4692953 := bstep (se 2 (by rfl) ⟨1759857, by rfl⟩ : syracuseStep 4692953 = 3519715) B3519715
theorem B3128635 : Blo 2195435 3128635 := bstep (se 1 (by rfl) ⟨2346476, by rfl⟩ : syracuseStep 3128635 = 4692953) B4692953
theorem B4171513 : Blo 2195435 4171513 := bstep (se 2 (by rfl) ⟨1564317, by rfl⟩ : syracuseStep 4171513 = 3128635) B3128635
theorem B5562017 : Blo 2195435 5562017 := bstep (se 2 (by rfl) ⟨2085756, by rfl⟩ : syracuseStep 5562017 = 4171513) B4171513
theorem B3708011 : Blo 2195435 3708011 := bstep (se 1 (by rfl) ⟨2781008, by rfl⟩ : syracuseStep 3708011 = 5562017) B5562017
theorem B2472007 : Blo 2195435 2472007 := bstep (se 1 (by rfl) ⟨1854005, by rfl⟩ : syracuseStep 2472007 = 3708011) B3708011
theorem B3296009 : Blo 2195435 3296009 := bstep (se 2 (by rfl) ⟨1236003, by rfl⟩ : syracuseStep 3296009 = 2472007) B2472007
theorem B2197339 : Blo 2195435 2197339 := bstep (se 1 (by rfl) ⟨1648004, by rfl⟩ : syracuseStep 2197339 = 3296009) B3296009
theorem B11124053 : Blo 2195435 11124053 := bbase (se 11 (by rfl) ⟨8147, by rfl⟩ : syracuseStep 11124053 = 16295) (by norm_num)
theorem B7416035 : Blo 2195435 7416035 := bstep (se 1 (by rfl) ⟨5562026, by rfl⟩ : syracuseStep 7416035 = 11124053) B11124053
theorem B4944023 : Blo 2195435 4944023 := bstep (se 1 (by rfl) ⟨3708017, by rfl⟩ : syracuseStep 4944023 = 7416035) B7416035
theorem B3296015 : Blo 2195435 3296015 := bstep (se 1 (by rfl) ⟨2472011, by rfl⟩ : syracuseStep 3296015 = 4944023) B4944023
theorem B2197343 : Blo 2195435 2197343 := bstep (se 1 (by rfl) ⟨1648007, by rfl⟩ : syracuseStep 2197343 = 3296015) B3296015
theorem B3296021 : Blo 2195435 3296021 := bbase (se 6 (by rfl) ⟨77250, by rfl⟩ : syracuseStep 3296021 = 154501) (by norm_num)
theorem B2197347 : Blo 2195435 2197347 := bstep (se 1 (by rfl) ⟨1648010, by rfl⟩ : syracuseStep 2197347 = 3296021) B3296021
theorem B4403893 : Blo 2195435 4403893 := bbase (se 5 (by rfl) ⟨206432, by rfl⟩ : syracuseStep 4403893 = 412865) (by norm_num)
theorem B5871857 : Blo 2195435 5871857 := bstep (se 2 (by rfl) ⟨2201946, by rfl⟩ : syracuseStep 5871857 = 4403893) B4403893
theorem B15658285 : Blo 2195435 15658285 := bstep (se 3 (by rfl) ⟨2935928, by rfl⟩ : syracuseStep 15658285 = 5871857) B5871857
theorem B20877713 : Blo 2195435 20877713 := bstep (se 2 (by rfl) ⟨7829142, by rfl⟩ : syracuseStep 20877713 = 15658285) B15658285
theorem B13918475 : Blo 2195435 13918475 := bstep (se 1 (by rfl) ⟨10438856, by rfl⟩ : syracuseStep 13918475 = 20877713) B20877713
theorem B9278983 : Blo 2195435 9278983 := bstep (se 1 (by rfl) ⟨6959237, by rfl⟩ : syracuseStep 9278983 = 13918475) B13918475
theorem B12371977 : Blo 2195435 12371977 := bstep (se 2 (by rfl) ⟨4639491, by rfl⟩ : syracuseStep 12371977 = 9278983) B9278983
theorem B16495969 : Blo 2195435 16495969 := bstep (se 2 (by rfl) ⟨6185988, by rfl⟩ : syracuseStep 16495969 = 12371977) B12371977
theorem B21994625 : Blo 2195435 21994625 := bstep (se 2 (by rfl) ⟨8247984, by rfl⟩ : syracuseStep 21994625 = 16495969) B16495969
theorem B58652333 : Blo 2195435 58652333 := bstep (se 3 (by rfl) ⟨10997312, by rfl⟩ : syracuseStep 58652333 = 21994625) B21994625
theorem B39101555 : Blo 2195435 39101555 := bstep (se 1 (by rfl) ⟨29326166, by rfl⟩ : syracuseStep 39101555 = 58652333) B58652333
theorem B26067703 : Blo 2195435 26067703 := bstep (se 1 (by rfl) ⟨19550777, by rfl⟩ : syracuseStep 26067703 = 39101555) B39101555
theorem B34756937 : Blo 2195435 34756937 := bstep (se 2 (by rfl) ⟨13033851, by rfl⟩ : syracuseStep 34756937 = 26067703) B26067703
theorem B23171291 : Blo 2195435 23171291 := bstep (se 1 (by rfl) ⟨17378468, by rfl⟩ : syracuseStep 23171291 = 34756937) B34756937
theorem B15447527 : Blo 2195435 15447527 := bstep (se 1 (by rfl) ⟨11585645, by rfl⟩ : syracuseStep 15447527 = 23171291) B23171291
theorem B10298351 : Blo 2195435 10298351 := bstep (se 1 (by rfl) ⟨7723763, by rfl⟩ : syracuseStep 10298351 = 15447527) B15447527
theorem B27462269 : Blo 2195435 27462269 := bstep (se 3 (by rfl) ⟨5149175, by rfl⟩ : syracuseStep 27462269 = 10298351) B10298351
theorem B18308179 : Blo 2195435 18308179 := bstep (se 1 (by rfl) ⟨13731134, by rfl⟩ : syracuseStep 18308179 = 27462269) B27462269
theorem B24410905 : Blo 2195435 24410905 := bstep (se 2 (by rfl) ⟨9154089, by rfl⟩ : syracuseStep 24410905 = 18308179) B18308179
theorem B520765973 : Blo 2195435 520765973 := bstep (se 6 (by rfl) ⟨12205452, by rfl⟩ : syracuseStep 520765973 = 24410905) B24410905
theorem B347177315 : Blo 2195435 347177315 := bstep (se 1 (by rfl) ⟨260382986, by rfl⟩ : syracuseStep 347177315 = 520765973) B520765973
theorem B231451543 : Blo 2195435 231451543 := bstep (se 1 (by rfl) ⟨173588657, by rfl⟩ : syracuseStep 231451543 = 347177315) B347177315
theorem B308602057 : Blo 2195435 308602057 := bstep (se 2 (by rfl) ⟨115725771, by rfl⟩ : syracuseStep 308602057 = 231451543) B231451543
theorem B411469409 : Blo 2195435 411469409 := bstep (se 2 (by rfl) ⟨154301028, by rfl⟩ : syracuseStep 411469409 = 308602057) B308602057
theorem B274312939 : Blo 2195435 274312939 := bstep (se 1 (by rfl) ⟨205734704, by rfl⟩ : syracuseStep 274312939 = 411469409) B411469409
theorem B365750585 : Blo 2195435 365750585 := bstep (se 2 (by rfl) ⟨137156469, by rfl⟩ : syracuseStep 365750585 = 274312939) B274312939
theorem B243833723 : Blo 2195435 243833723 := bstep (se 1 (by rfl) ⟨182875292, by rfl⟩ : syracuseStep 243833723 = 365750585) B365750585
theorem B162555815 : Blo 2195435 162555815 := bstep (se 1 (by rfl) ⟨121916861, by rfl⟩ : syracuseStep 162555815 = 243833723) B243833723
theorem B108370543 : Blo 2195435 108370543 := bstep (se 1 (by rfl) ⟨81277907, by rfl⟩ : syracuseStep 108370543 = 162555815) B162555815
theorem B144494057 : Blo 2195435 144494057 := bstep (se 2 (by rfl) ⟨54185271, by rfl⟩ : syracuseStep 144494057 = 108370543) B108370543
theorem B385317485 : Blo 2195435 385317485 := bstep (se 3 (by rfl) ⟨72247028, by rfl⟩ : syracuseStep 385317485 = 144494057) B144494057
theorem B256878323 : Blo 2195435 256878323 := bstep (se 1 (by rfl) ⟨192658742, by rfl⟩ : syracuseStep 256878323 = 385317485) B385317485
theorem B171252215 : Blo 2195435 171252215 := bstep (se 1 (by rfl) ⟨128439161, by rfl⟩ : syracuseStep 171252215 = 256878323) B256878323
theorem B114168143 : Blo 2195435 114168143 := bstep (se 1 (by rfl) ⟨85626107, by rfl⟩ : syracuseStep 114168143 = 171252215) B171252215
theorem B76112095 : Blo 2195435 76112095 := bstep (se 1 (by rfl) ⟨57084071, by rfl⟩ : syracuseStep 76112095 = 114168143) B114168143
theorem B101482793 : Blo 2195435 101482793 := bstep (se 2 (by rfl) ⟨38056047, by rfl⟩ : syracuseStep 101482793 = 76112095) B76112095
theorem B67655195 : Blo 2195435 67655195 := bstep (se 1 (by rfl) ⟨50741396, by rfl⟩ : syracuseStep 67655195 = 101482793) B101482793
theorem B45103463 : Blo 2195435 45103463 := bstep (se 1 (by rfl) ⟨33827597, by rfl⟩ : syracuseStep 45103463 = 67655195) B67655195
theorem B30068975 : Blo 2195435 30068975 := bstep (se 1 (by rfl) ⟨22551731, by rfl⟩ : syracuseStep 30068975 = 45103463) B45103463
theorem B20045983 : Blo 2195435 20045983 := bstep (se 1 (by rfl) ⟨15034487, by rfl⟩ : syracuseStep 20045983 = 30068975) B30068975
theorem B26727977 : Blo 2195435 26727977 := bstep (se 2 (by rfl) ⟨10022991, by rfl⟩ : syracuseStep 26727977 = 20045983) B20045983
theorem B17818651 : Blo 2195435 17818651 := bstep (se 1 (by rfl) ⟨13363988, by rfl⟩ : syracuseStep 17818651 = 26727977) B26727977
theorem B23758201 : Blo 2195435 23758201 := bstep (se 2 (by rfl) ⟨8909325, by rfl⟩ : syracuseStep 23758201 = 17818651) B17818651
theorem B31677601 : Blo 2195435 31677601 := bstep (se 2 (by rfl) ⟨11879100, by rfl⟩ : syracuseStep 31677601 = 23758201) B23758201
theorem B42236801 : Blo 2195435 42236801 := bstep (se 2 (by rfl) ⟨15838800, by rfl⟩ : syracuseStep 42236801 = 31677601) B31677601
theorem B28157867 : Blo 2195435 28157867 := bstep (se 1 (by rfl) ⟨21118400, by rfl⟩ : syracuseStep 28157867 = 42236801) B42236801
theorem B18771911 : Blo 2195435 18771911 := bstep (se 1 (by rfl) ⟨14078933, by rfl⟩ : syracuseStep 18771911 = 28157867) B28157867
theorem B12514607 : Blo 2195435 12514607 := bstep (se 1 (by rfl) ⟨9385955, by rfl⟩ : syracuseStep 12514607 = 18771911) B18771911
theorem B8343071 : Blo 2195435 8343071 := bstep (se 1 (by rfl) ⟨6257303, by rfl⟩ : syracuseStep 8343071 = 12514607) B12514607
theorem B5562047 : Blo 2195435 5562047 := bstep (se 1 (by rfl) ⟨4171535, by rfl⟩ : syracuseStep 5562047 = 8343071) B8343071
theorem B3708031 : Blo 2195435 3708031 := bstep (se 1 (by rfl) ⟨2781023, by rfl⟩ : syracuseStep 3708031 = 5562047) B5562047
theorem B4944041 : Blo 2195435 4944041 := bstep (se 2 (by rfl) ⟨1854015, by rfl⟩ : syracuseStep 4944041 = 3708031) B3708031
theorem B3296027 : Blo 2195435 3296027 := bstep (se 1 (by rfl) ⟨2472020, by rfl⟩ : syracuseStep 3296027 = 4944041) B4944041
theorem B2197351 : Blo 2195435 2197351 := bstep (se 1 (by rfl) ⟨1648013, by rfl⟩ : syracuseStep 2197351 = 3296027) B3296027
theorem B2472025 : Blo 2195435 2472025 := bbase (se 2 (by rfl) ⟨927009, by rfl⟩ : syracuseStep 2472025 = 1854019) (by norm_num)
theorem B3296033 : Blo 2195435 3296033 := bstep (se 2 (by rfl) ⟨1236012, by rfl⟩ : syracuseStep 3296033 = 2472025) B2472025
theorem B2197355 : Blo 2195435 2197355 := bstep (se 1 (by rfl) ⟨1648016, by rfl⟩ : syracuseStep 2197355 = 3296033) B3296033
theorem B7039493 : Blo 2195435 7039493 := bbase (se 4 (by rfl) ⟨659952, by rfl⟩ : syracuseStep 7039493 = 1319905) (by norm_num)
theorem B4692995 : Blo 2195435 4692995 := bstep (se 1 (by rfl) ⟨3519746, by rfl⟩ : syracuseStep 4692995 = 7039493) B7039493
theorem B3128663 : Blo 2195435 3128663 := bstep (se 1 (by rfl) ⟨2346497, by rfl⟩ : syracuseStep 3128663 = 4692995) B4692995
theorem B8343101 : Blo 2195435 8343101 := bstep (se 3 (by rfl) ⟨1564331, by rfl⟩ : syracuseStep 8343101 = 3128663) B3128663
theorem B5562067 : Blo 2195435 5562067 := bstep (se 1 (by rfl) ⟨4171550, by rfl⟩ : syracuseStep 5562067 = 8343101) B8343101
theorem B7416089 : Blo 2195435 7416089 := bstep (se 2 (by rfl) ⟨2781033, by rfl⟩ : syracuseStep 7416089 = 5562067) B5562067
theorem B4944059 : Blo 2195435 4944059 := bstep (se 1 (by rfl) ⟨3708044, by rfl⟩ : syracuseStep 4944059 = 7416089) B7416089
theorem B3296039 : Blo 2195435 3296039 := bstep (se 1 (by rfl) ⟨2472029, by rfl⟩ : syracuseStep 3296039 = 4944059) B4944059
theorem B2197359 : Blo 2195435 2197359 := bstep (se 1 (by rfl) ⟨1648019, by rfl⟩ : syracuseStep 2197359 = 3296039) B3296039
theorem B3296045 : Blo 2195435 3296045 := bbase (se 3 (by rfl) ⟨618008, by rfl⟩ : syracuseStep 3296045 = 1236017) (by norm_num)
theorem B2197363 : Blo 2195435 2197363 := bstep (se 1 (by rfl) ⟨1648022, by rfl⟩ : syracuseStep 2197363 = 3296045) B3296045
theorem B4944077 : Blo 2195435 4944077 := bbase (se 3 (by rfl) ⟨927014, by rfl⟩ : syracuseStep 4944077 = 1854029) (by norm_num)
theorem B3296051 : Blo 2195435 3296051 := bstep (se 1 (by rfl) ⟨2472038, by rfl⟩ : syracuseStep 3296051 = 4944077) B4944077
theorem B2197367 : Blo 2195435 2197367 := bstep (se 1 (by rfl) ⟨1648025, by rfl⟩ : syracuseStep 2197367 = 3296051) B3296051
theorem B2781049 : Blo 2195435 2781049 := bbase (se 2 (by rfl) ⟨1042893, by rfl⟩ : syracuseStep 2781049 = 2085787) (by norm_num)
theorem B3708065 : Blo 2195435 3708065 := bstep (se 2 (by rfl) ⟨1390524, by rfl⟩ : syracuseStep 3708065 = 2781049) B2781049
theorem B2472043 : Blo 2195435 2472043 := bstep (se 1 (by rfl) ⟨1854032, by rfl⟩ : syracuseStep 2472043 = 3708065) B3708065
theorem B3296057 : Blo 2195435 3296057 := bstep (se 2 (by rfl) ⟨1236021, by rfl⟩ : syracuseStep 3296057 = 2472043) B2472043
theorem B2197371 : Blo 2195435 2197371 := bstep (se 1 (by rfl) ⟨1648028, by rfl⟩ : syracuseStep 2197371 = 3296057) B3296057
theorem B4286189 : Blo 2195435 4286189 := bbase (se 3 (by rfl) ⟨803660, by rfl⟩ : syracuseStep 4286189 = 1607321) (by norm_num)
theorem B2857459 : Blo 2195435 2857459 := bstep (se 1 (by rfl) ⟨2143094, by rfl⟩ : syracuseStep 2857459 = 4286189) B4286189
theorem B3809945 : Blo 2195435 3809945 := bstep (se 2 (by rfl) ⟨1428729, by rfl⟩ : syracuseStep 3809945 = 2857459) B2857459
theorem B2539963 : Blo 2195435 2539963 := bstep (se 1 (by rfl) ⟨1904972, by rfl⟩ : syracuseStep 2539963 = 3809945) B3809945
theorem B3386617 : Blo 2195435 3386617 := bstep (se 2 (by rfl) ⟨1269981, by rfl⟩ : syracuseStep 3386617 = 2539963) B2539963
theorem B18061957 : Blo 2195435 18061957 := bstep (se 4 (by rfl) ⟨1693308, by rfl⟩ : syracuseStep 18061957 = 3386617) B3386617
theorem B24082609 : Blo 2195435 24082609 := bstep (se 2 (by rfl) ⟨9030978, by rfl⟩ : syracuseStep 24082609 = 18061957) B18061957
theorem B32110145 : Blo 2195435 32110145 := bstep (se 2 (by rfl) ⟨12041304, by rfl⟩ : syracuseStep 32110145 = 24082609) B24082609
theorem B21406763 : Blo 2195435 21406763 := bstep (se 1 (by rfl) ⟨16055072, by rfl⟩ : syracuseStep 21406763 = 32110145) B32110145
theorem B14271175 : Blo 2195435 14271175 := bstep (se 1 (by rfl) ⟨10703381, by rfl⟩ : syracuseStep 14271175 = 21406763) B21406763
theorem B19028233 : Blo 2195435 19028233 := bstep (se 2 (by rfl) ⟨7135587, by rfl⟩ : syracuseStep 19028233 = 14271175) B14271175
theorem B25370977 : Blo 2195435 25370977 := bstep (se 2 (by rfl) ⟨9514116, by rfl⟩ : syracuseStep 25370977 = 19028233) B19028233
theorem B33827969 : Blo 2195435 33827969 := bstep (se 2 (by rfl) ⟨12685488, by rfl⟩ : syracuseStep 33827969 = 25370977) B25370977
theorem B22551979 : Blo 2195435 22551979 := bstep (se 1 (by rfl) ⟨16913984, by rfl⟩ : syracuseStep 22551979 = 33827969) B33827969
theorem B30069305 : Blo 2195435 30069305 := bstep (se 2 (by rfl) ⟨11275989, by rfl⟩ : syracuseStep 30069305 = 22551979) B22551979
theorem B20046203 : Blo 2195435 20046203 := bstep (se 1 (by rfl) ⟨15034652, by rfl⟩ : syracuseStep 20046203 = 30069305) B30069305
theorem B13364135 : Blo 2195435 13364135 := bstep (se 1 (by rfl) ⟨10023101, by rfl⟩ : syracuseStep 13364135 = 20046203) B20046203
theorem B8909423 : Blo 2195435 8909423 := bstep (se 1 (by rfl) ⟨6682067, by rfl⟩ : syracuseStep 8909423 = 13364135) B13364135
theorem B5939615 : Blo 2195435 5939615 := bstep (se 1 (by rfl) ⟨4454711, by rfl⟩ : syracuseStep 5939615 = 8909423) B8909423
theorem B15838973 : Blo 2195435 15838973 := bstep (se 3 (by rfl) ⟨2969807, by rfl⟩ : syracuseStep 15838973 = 5939615) B5939615
theorem B10559315 : Blo 2195435 10559315 := bstep (se 1 (by rfl) ⟨7919486, by rfl⟩ : syracuseStep 10559315 = 15838973) B15838973
theorem B7039543 : Blo 2195435 7039543 := bstep (se 1 (by rfl) ⟨5279657, by rfl⟩ : syracuseStep 7039543 = 10559315) B10559315
theorem B9386057 : Blo 2195435 9386057 := bstep (se 2 (by rfl) ⟨3519771, by rfl⟩ : syracuseStep 9386057 = 7039543) B7039543
theorem B25029485 : Blo 2195435 25029485 := bstep (se 3 (by rfl) ⟨4693028, by rfl⟩ : syracuseStep 25029485 = 9386057) B9386057
theorem B16686323 : Blo 2195435 16686323 := bstep (se 1 (by rfl) ⟨12514742, by rfl⟩ : syracuseStep 16686323 = 25029485) B25029485
theorem B11124215 : Blo 2195435 11124215 := bstep (se 1 (by rfl) ⟨8343161, by rfl⟩ : syracuseStep 11124215 = 16686323) B16686323
theorem B7416143 : Blo 2195435 7416143 := bstep (se 1 (by rfl) ⟨5562107, by rfl⟩ : syracuseStep 7416143 = 11124215) B11124215
theorem B4944095 : Blo 2195435 4944095 := bstep (se 1 (by rfl) ⟨3708071, by rfl⟩ : syracuseStep 4944095 = 7416143) B7416143
theorem B3296063 : Blo 2195435 3296063 := bstep (se 1 (by rfl) ⟨2472047, by rfl⟩ : syracuseStep 3296063 = 4944095) B4944095
theorem B2197375 : Blo 2195435 2197375 := bstep (se 1 (by rfl) ⟨1648031, by rfl⟩ : syracuseStep 2197375 = 3296063) B3296063
theorem B3296069 : Blo 2195435 3296069 := bbase (se 4 (by rfl) ⟨309006, by rfl⟩ : syracuseStep 3296069 = 618013) (by norm_num)
theorem B2197379 : Blo 2195435 2197379 := bstep (se 1 (by rfl) ⟨1648034, by rfl⟩ : syracuseStep 2197379 = 3296069) B3296069
theorem B3708085 : Blo 2195435 3708085 := bbase (se 5 (by rfl) ⟨173816, by rfl⟩ : syracuseStep 3708085 = 347633) (by norm_num)
theorem B4944113 : Blo 2195435 4944113 := bstep (se 2 (by rfl) ⟨1854042, by rfl⟩ : syracuseStep 4944113 = 3708085) B3708085
theorem B3296075 : Blo 2195435 3296075 := bstep (se 1 (by rfl) ⟨2472056, by rfl⟩ : syracuseStep 3296075 = 4944113) B4944113
theorem B2197383 : Blo 2195435 2197383 := bstep (se 1 (by rfl) ⟨1648037, by rfl⟩ : syracuseStep 2197383 = 3296075) B3296075
theorem B2472061 : Blo 2195435 2472061 := bbase (se 3 (by rfl) ⟨463511, by rfl⟩ : syracuseStep 2472061 = 927023) (by norm_num)
theorem B3296081 : Blo 2195435 3296081 := bstep (se 2 (by rfl) ⟨1236030, by rfl⟩ : syracuseStep 3296081 = 2472061) B2472061
theorem B2197387 : Blo 2195435 2197387 := bstep (se 1 (by rfl) ⟨1648040, by rfl⟩ : syracuseStep 2197387 = 3296081) B3296081
theorem B7416197 : Blo 2195435 7416197 := bbase (se 4 (by rfl) ⟨695268, by rfl⟩ : syracuseStep 7416197 = 1390537) (by norm_num)
theorem B4944131 : Blo 2195435 4944131 := bstep (se 1 (by rfl) ⟨3708098, by rfl⟩ : syracuseStep 4944131 = 7416197) B7416197
theorem B3296087 : Blo 2195435 3296087 := bstep (se 1 (by rfl) ⟨2472065, by rfl⟩ : syracuseStep 3296087 = 4944131) B4944131
theorem B2197391 : Blo 2195435 2197391 := bstep (se 1 (by rfl) ⟨1648043, by rfl⟩ : syracuseStep 2197391 = 3296087) B3296087
theorem B3296093 : Blo 2195435 3296093 := bbase (se 3 (by rfl) ⟨618017, by rfl⟩ : syracuseStep 3296093 = 1236035) (by norm_num)
theorem B2197395 : Blo 2195435 2197395 := bstep (se 1 (by rfl) ⟨1648046, by rfl⟩ : syracuseStep 2197395 = 3296093) B3296093
theorem B4944149 : Blo 2195435 4944149 := bbase (se 6 (by rfl) ⟨115878, by rfl⟩ : syracuseStep 4944149 = 231757) (by norm_num)
theorem B3296099 : Blo 2195435 3296099 := bstep (se 1 (by rfl) ⟨2472074, by rfl⟩ : syracuseStep 3296099 = 4944149) B4944149
theorem B2197399 : Blo 2195435 2197399 := bstep (se 1 (by rfl) ⟨1648049, by rfl⟩ : syracuseStep 2197399 = 3296099) B3296099
theorem B8343269 : Blo 2195435 8343269 := bbase (se 4 (by rfl) ⟨782181, by rfl⟩ : syracuseStep 8343269 = 1564363) (by norm_num)
theorem B5562179 : Blo 2195435 5562179 := bstep (se 1 (by rfl) ⟨4171634, by rfl⟩ : syracuseStep 5562179 = 8343269) B8343269
theorem B3708119 : Blo 2195435 3708119 := bstep (se 1 (by rfl) ⟨2781089, by rfl⟩ : syracuseStep 3708119 = 5562179) B5562179
theorem B2472079 : Blo 2195435 2472079 := bstep (se 1 (by rfl) ⟨1854059, by rfl⟩ : syracuseStep 2472079 = 3708119) B3708119
theorem B3296105 : Blo 2195435 3296105 := bstep (se 2 (by rfl) ⟨1236039, by rfl⟩ : syracuseStep 3296105 = 2472079) B2472079
theorem B2197403 : Blo 2195435 2197403 := bstep (se 1 (by rfl) ⟨1648052, by rfl⟩ : syracuseStep 2197403 = 3296105) B3296105
theorem B4515557 : Blo 2195435 4515557 := bbase (se 4 (by rfl) ⟨423333, by rfl⟩ : syracuseStep 4515557 = 846667) (by norm_num)
theorem B48165941 : Blo 2195435 48165941 := bstep (se 5 (by rfl) ⟨2257778, by rfl⟩ : syracuseStep 48165941 = 4515557) B4515557
theorem B32110627 : Blo 2195435 32110627 := bstep (se 1 (by rfl) ⟨24082970, by rfl⟩ : syracuseStep 32110627 = 48165941) B48165941
theorem B42814169 : Blo 2195435 42814169 := bstep (se 2 (by rfl) ⟨16055313, by rfl⟩ : syracuseStep 42814169 = 32110627) B32110627
theorem B28542779 : Blo 2195435 28542779 := bstep (se 1 (by rfl) ⟨21407084, by rfl⟩ : syracuseStep 28542779 = 42814169) B42814169
theorem B19028519 : Blo 2195435 19028519 := bstep (se 1 (by rfl) ⟨14271389, by rfl⟩ : syracuseStep 19028519 = 28542779) B28542779
theorem B12685679 : Blo 2195435 12685679 := bstep (se 1 (by rfl) ⟨9514259, by rfl⟩ : syracuseStep 12685679 = 19028519) B19028519
theorem B8457119 : Blo 2195435 8457119 := bstep (se 1 (by rfl) ⟨6342839, by rfl⟩ : syracuseStep 8457119 = 12685679) B12685679
theorem B5638079 : Blo 2195435 5638079 := bstep (se 1 (by rfl) ⟨4228559, by rfl⟩ : syracuseStep 5638079 = 8457119) B8457119
theorem B3758719 : Blo 2195435 3758719 := bstep (se 1 (by rfl) ⟨2819039, by rfl⟩ : syracuseStep 3758719 = 5638079) B5638079
theorem B5011625 : Blo 2195435 5011625 := bstep (se 2 (by rfl) ⟨1879359, by rfl⟩ : syracuseStep 5011625 = 3758719) B3758719
theorem B3341083 : Blo 2195435 3341083 := bstep (se 1 (by rfl) ⟨2505812, by rfl⟩ : syracuseStep 3341083 = 5011625) B5011625
theorem B4454777 : Blo 2195435 4454777 := bstep (se 2 (by rfl) ⟨1670541, by rfl⟩ : syracuseStep 4454777 = 3341083) B3341083
theorem B11879405 : Blo 2195435 11879405 := bstep (se 3 (by rfl) ⟨2227388, by rfl⟩ : syracuseStep 11879405 = 4454777) B4454777
theorem B7919603 : Blo 2195435 7919603 := bstep (se 1 (by rfl) ⟨5939702, by rfl⟩ : syracuseStep 7919603 = 11879405) B11879405
theorem B5279735 : Blo 2195435 5279735 := bstep (se 1 (by rfl) ⟨3959801, by rfl⟩ : syracuseStep 5279735 = 7919603) B7919603
theorem B3519823 : Blo 2195435 3519823 := bstep (se 1 (by rfl) ⟨2639867, by rfl⟩ : syracuseStep 3519823 = 5279735) B5279735
theorem B4693097 : Blo 2195435 4693097 := bstep (se 2 (by rfl) ⟨1759911, by rfl⟩ : syracuseStep 4693097 = 3519823) B3519823
theorem B12514925 : Blo 2195435 12514925 := bstep (se 3 (by rfl) ⟨2346548, by rfl⟩ : syracuseStep 12514925 = 4693097) B4693097
theorem B8343283 : Blo 2195435 8343283 := bstep (se 1 (by rfl) ⟨6257462, by rfl⟩ : syracuseStep 8343283 = 12514925) B12514925
theorem B11124377 : Blo 2195435 11124377 := bstep (se 2 (by rfl) ⟨4171641, by rfl⟩ : syracuseStep 11124377 = 8343283) B8343283
theorem B7416251 : Blo 2195435 7416251 := bstep (se 1 (by rfl) ⟨5562188, by rfl⟩ : syracuseStep 7416251 = 11124377) B11124377
theorem B4944167 : Blo 2195435 4944167 := bstep (se 1 (by rfl) ⟨3708125, by rfl⟩ : syracuseStep 4944167 = 7416251) B7416251
theorem B3296111 : Blo 2195435 3296111 := bstep (se 1 (by rfl) ⟨2472083, by rfl⟩ : syracuseStep 3296111 = 4944167) B4944167
theorem B2197407 : Blo 2195435 2197407 := bstep (se 1 (by rfl) ⟨1648055, by rfl⟩ : syracuseStep 2197407 = 3296111) B3296111
theorem B3296117 : Blo 2195435 3296117 := bbase (se 5 (by rfl) ⟨154505, by rfl⟩ : syracuseStep 3296117 = 309011) (by norm_num)
theorem B2197411 : Blo 2195435 2197411 := bstep (se 1 (by rfl) ⟨1648058, by rfl⟩ : syracuseStep 2197411 = 3296117) B3296117
theorem B2227397 : Blo 2195435 2227397 := bbase (se 4 (by rfl) ⟨208818, by rfl⟩ : syracuseStep 2227397 = 417637) (by norm_num)
theorem B5939725 : Blo 2195435 5939725 := bstep (se 3 (by rfl) ⟨1113698, by rfl⟩ : syracuseStep 5939725 = 2227397) B2227397
theorem B7919633 : Blo 2195435 7919633 := bstep (se 2 (by rfl) ⟨2969862, by rfl⟩ : syracuseStep 7919633 = 5939725) B5939725
theorem B5279755 : Blo 2195435 5279755 := bstep (se 1 (by rfl) ⟨3959816, by rfl⟩ : syracuseStep 5279755 = 7919633) B7919633
theorem B7039673 : Blo 2195435 7039673 := bstep (se 2 (by rfl) ⟨2639877, by rfl⟩ : syracuseStep 7039673 = 5279755) B5279755
theorem B4693115 : Blo 2195435 4693115 := bstep (se 1 (by rfl) ⟨3519836, by rfl⟩ : syracuseStep 4693115 = 7039673) B7039673
theorem B3128743 : Blo 2195435 3128743 := bstep (se 1 (by rfl) ⟨2346557, by rfl⟩ : syracuseStep 3128743 = 4693115) B4693115
theorem B4171657 : Blo 2195435 4171657 := bstep (se 2 (by rfl) ⟨1564371, by rfl⟩ : syracuseStep 4171657 = 3128743) B3128743
theorem B5562209 : Blo 2195435 5562209 := bstep (se 2 (by rfl) ⟨2085828, by rfl⟩ : syracuseStep 5562209 = 4171657) B4171657
theorem B3708139 : Blo 2195435 3708139 := bstep (se 1 (by rfl) ⟨2781104, by rfl⟩ : syracuseStep 3708139 = 5562209) B5562209
theorem B4944185 : Blo 2195435 4944185 := bstep (se 2 (by rfl) ⟨1854069, by rfl⟩ : syracuseStep 4944185 = 3708139) B3708139
theorem B3296123 : Blo 2195435 3296123 := bstep (se 1 (by rfl) ⟨2472092, by rfl⟩ : syracuseStep 3296123 = 4944185) B4944185
theorem B2197415 : Blo 2195435 2197415 := bstep (se 1 (by rfl) ⟨1648061, by rfl⟩ : syracuseStep 2197415 = 3296123) B3296123
theorem B2472097 : Blo 2195435 2472097 := bbase (se 2 (by rfl) ⟨927036, by rfl⟩ : syracuseStep 2472097 = 1854073) (by norm_num)
theorem B3296129 : Blo 2195435 3296129 := bstep (se 2 (by rfl) ⟨1236048, by rfl⟩ : syracuseStep 3296129 = 2472097) B2472097
theorem B2197419 : Blo 2195435 2197419 := bstep (se 1 (by rfl) ⟨1648064, by rfl⟩ : syracuseStep 2197419 = 3296129) B3296129
theorem B5562229 : Blo 2195435 5562229 := bbase (se 5 (by rfl) ⟨260729, by rfl⟩ : syracuseStep 5562229 = 521459) (by norm_num)
theorem B7416305 : Blo 2195435 7416305 := bstep (se 2 (by rfl) ⟨2781114, by rfl⟩ : syracuseStep 7416305 = 5562229) B5562229
theorem B4944203 : Blo 2195435 4944203 := bstep (se 1 (by rfl) ⟨3708152, by rfl⟩ : syracuseStep 4944203 = 7416305) B7416305
theorem B3296135 : Blo 2195435 3296135 := bstep (se 1 (by rfl) ⟨2472101, by rfl⟩ : syracuseStep 3296135 = 4944203) B4944203
theorem B2197423 : Blo 2195435 2197423 := bstep (se 1 (by rfl) ⟨1648067, by rfl⟩ : syracuseStep 2197423 = 3296135) B3296135
theorem B3296141 : Blo 2195435 3296141 := bbase (se 3 (by rfl) ⟨618026, by rfl⟩ : syracuseStep 3296141 = 1236053) (by norm_num)
theorem B2197427 : Blo 2195435 2197427 := bstep (se 1 (by rfl) ⟨1648070, by rfl⟩ : syracuseStep 2197427 = 3296141) B3296141
theorem B4944221 : Blo 2195435 4944221 := bbase (se 3 (by rfl) ⟨927041, by rfl⟩ : syracuseStep 4944221 = 1854083) (by norm_num)
theorem B3296147 : Blo 2195435 3296147 := bstep (se 1 (by rfl) ⟨2472110, by rfl⟩ : syracuseStep 3296147 = 4944221) B4944221
theorem B2197431 : Blo 2195435 2197431 := bstep (se 1 (by rfl) ⟨1648073, by rfl⟩ : syracuseStep 2197431 = 3296147) B3296147
theorem B3708173 : Blo 2195435 3708173 := bbase (se 3 (by rfl) ⟨695282, by rfl⟩ : syracuseStep 3708173 = 1390565) (by norm_num)
theorem B2472115 : Blo 2195435 2472115 := bstep (se 1 (by rfl) ⟨1854086, by rfl⟩ : syracuseStep 2472115 = 3708173) B3708173
theorem B3296153 : Blo 2195435 3296153 := bstep (se 2 (by rfl) ⟨1236057, by rfl⟩ : syracuseStep 3296153 = 2472115) B2472115
theorem B2197435 : Blo 2195435 2197435 := bstep (se 1 (by rfl) ⟨1648076, by rfl⟩ : syracuseStep 2197435 = 3296153) B3296153
theorem C0 (j : ℕ) (h1 : 548858 ≤ j) (h2 : j ≤ 549358) : Blo 2195435 (4 * j + 3) := by
  interval_cases j
  · exact B2195435
  · exact B2195439
  · exact B2195443
  · exact B2195447
  · exact B2195451
  · exact B2195455
  · exact B2195459
  · exact B2195463
  · exact B2195467
  · exact B2195471
  · exact B2195475
  · exact B2195479
  · exact B2195483
  · exact B2195487
  · exact B2195491
  · exact B2195495
  · exact B2195499
  · exact B2195503
  · exact B2195507
  · exact B2195511
  · exact B2195515
  · exact B2195519
  · exact B2195523
  · exact B2195527
  · exact B2195531
  · exact B2195535
  · exact B2195539
  · exact B2195543
  · exact B2195547
  · exact B2195551
  · exact B2195555
  · exact B2195559
  · exact B2195563
  · exact B2195567
  · exact B2195571
  · exact B2195575
  · exact B2195579
  · exact B2195583
  · exact B2195587
  · exact B2195591
  · exact B2195595
  · exact B2195599
  · exact B2195603
  · exact B2195607
  · exact B2195611
  · exact B2195615
  · exact B2195619
  · exact B2195623
  · exact B2195627
  · exact B2195631
  · exact B2195635
  · exact B2195639
  · exact B2195643
  · exact B2195647
  · exact B2195651
  · exact B2195655
  · exact B2195659
  · exact B2195663
  · exact B2195667
  · exact B2195671
  · exact B2195675
  · exact B2195679
  · exact B2195683
  · exact B2195687
  · exact B2195691
  · exact B2195695
  · exact B2195699
  · exact B2195703
  · exact B2195707
  · exact B2195711
  · exact B2195715
  · exact B2195719
  · exact B2195723
  · exact B2195727
  · exact B2195731
  · exact B2195735
  · exact B2195739
  · exact B2195743
  · exact B2195747
  · exact B2195751
  · exact B2195755
  · exact B2195759
  · exact B2195763
  · exact B2195767
  · exact B2195771
  · exact B2195775
  · exact B2195779
  · exact B2195783
  · exact B2195787
  · exact B2195791
  · exact B2195795
  · exact B2195799
  · exact B2195803
  · exact B2195807
  · exact B2195811
  · exact B2195815
  · exact B2195819
  · exact B2195823
  · exact B2195827
  · exact B2195831
  · exact B2195835
  · exact B2195839
  · exact B2195843
  · exact B2195847
  · exact B2195851
  · exact B2195855
  · exact B2195859
  · exact B2195863
  · exact B2195867
  · exact B2195871
  · exact B2195875
  · exact B2195879
  · exact B2195883
  · exact B2195887
  · exact B2195891
  · exact B2195895
  · exact B2195899
  · exact B2195903
  · exact B2195907
  · exact B2195911
  · exact B2195915
  · exact B2195919
  · exact B2195923
  · exact B2195927
  · exact B2195931
  · exact B2195935
  · exact B2195939
  · exact B2195943
  · exact B2195947
  · exact B2195951
  · exact B2195955
  · exact B2195959
  · exact B2195963
  · exact B2195967
  · exact B2195971
  · exact B2195975
  · exact B2195979
  · exact B2195983
  · exact B2195987
  · exact B2195991
  · exact B2195995
  · exact B2195999
  · exact B2196003
  · exact B2196007
  · exact B2196011
  · exact B2196015
  · exact B2196019
  · exact B2196023
  · exact B2196027
  · exact B2196031
  · exact B2196035
  · exact B2196039
  · exact B2196043
  · exact B2196047
  · exact B2196051
  · exact B2196055
  · exact B2196059
  · exact B2196063
  · exact B2196067
  · exact B2196071
  · exact B2196075
  · exact B2196079
  · exact B2196083
  · exact B2196087
  · exact B2196091
  · exact B2196095
  · exact B2196099
  · exact B2196103
  · exact B2196107
  · exact B2196111
  · exact B2196115
  · exact B2196119
  · exact B2196123
  · exact B2196127
  · exact B2196131
  · exact B2196135
  · exact B2196139
  · exact B2196143
  · exact B2196147
  · exact B2196151
  · exact B2196155
  · exact B2196159
  · exact B2196163
  · exact B2196167
  · exact B2196171
  · exact B2196175
  · exact B2196179
  · exact B2196183
  · exact B2196187
  · exact B2196191
  · exact B2196195
  · exact B2196199
  · exact B2196203
  · exact B2196207
  · exact B2196211
  · exact B2196215
  · exact B2196219
  · exact B2196223
  · exact B2196227
  · exact B2196231
  · exact B2196235
  · exact B2196239
  · exact B2196243
  · exact B2196247
  · exact B2196251
  · exact B2196255
  · exact B2196259
  · exact B2196263
  · exact B2196267
  · exact B2196271
  · exact B2196275
  · exact B2196279
  · exact B2196283
  · exact B2196287
  · exact B2196291
  · exact B2196295
  · exact B2196299
  · exact B2196303
  · exact B2196307
  · exact B2196311
  · exact B2196315
  · exact B2196319
  · exact B2196323
  · exact B2196327
  · exact B2196331
  · exact B2196335
  · exact B2196339
  · exact B2196343
  · exact B2196347
  · exact B2196351
  · exact B2196355
  · exact B2196359
  · exact B2196363
  · exact B2196367
  · exact B2196371
  · exact B2196375
  · exact B2196379
  · exact B2196383
  · exact B2196387
  · exact B2196391
  · exact B2196395
  · exact B2196399
  · exact B2196403
  · exact B2196407
  · exact B2196411
  · exact B2196415
  · exact B2196419
  · exact B2196423
  · exact B2196427
  · exact B2196431
  · exact B2196435
  · exact B2196439
  · exact B2196443
  · exact B2196447
  · exact B2196451
  · exact B2196455
  · exact B2196459
  · exact B2196463
  · exact B2196467
  · exact B2196471
  · exact B2196475
  · exact B2196479
  · exact B2196483
  · exact B2196487
  · exact B2196491
  · exact B2196495
  · exact B2196499
  · exact B2196503
  · exact B2196507
  · exact B2196511
  · exact B2196515
  · exact B2196519
  · exact B2196523
  · exact B2196527
  · exact B2196531
  · exact B2196535
  · exact B2196539
  · exact B2196543
  · exact B2196547
  · exact B2196551
  · exact B2196555
  · exact B2196559
  · exact B2196563
  · exact B2196567
  · exact B2196571
  · exact B2196575
  · exact B2196579
  · exact B2196583
  · exact B2196587
  · exact B2196591
  · exact B2196595
  · exact B2196599
  · exact B2196603
  · exact B2196607
  · exact B2196611
  · exact B2196615
  · exact B2196619
  · exact B2196623
  · exact B2196627
  · exact B2196631
  · exact B2196635
  · exact B2196639
  · exact B2196643
  · exact B2196647
  · exact B2196651
  · exact B2196655
  · exact B2196659
  · exact B2196663
  · exact B2196667
  · exact B2196671
  · exact B2196675
  · exact B2196679
  · exact B2196683
  · exact B2196687
  · exact B2196691
  · exact B2196695
  · exact B2196699
  · exact B2196703
  · exact B2196707
  · exact B2196711
  · exact B2196715
  · exact B2196719
  · exact B2196723
  · exact B2196727
  · exact B2196731
  · exact B2196735
  · exact B2196739
  · exact B2196743
  · exact B2196747
  · exact B2196751
  · exact B2196755
  · exact B2196759
  · exact B2196763
  · exact B2196767
  · exact B2196771
  · exact B2196775
  · exact B2196779
  · exact B2196783
  · exact B2196787
  · exact B2196791
  · exact B2196795
  · exact B2196799
  · exact B2196803
  · exact B2196807
  · exact B2196811
  · exact B2196815
  · exact B2196819
  · exact B2196823
  · exact B2196827
  · exact B2196831
  · exact B2196835
  · exact B2196839
  · exact B2196843
  · exact B2196847
  · exact B2196851
  · exact B2196855
  · exact B2196859
  · exact B2196863
  · exact B2196867
  · exact B2196871
  · exact B2196875
  · exact B2196879
  · exact B2196883
  · exact B2196887
  · exact B2196891
  · exact B2196895
  · exact B2196899
  · exact B2196903
  · exact B2196907
  · exact B2196911
  · exact B2196915
  · exact B2196919
  · exact B2196923
  · exact B2196927
  · exact B2196931
  · exact B2196935
  · exact B2196939
  · exact B2196943
  · exact B2196947
  · exact B2196951
  · exact B2196955
  · exact B2196959
  · exact B2196963
  · exact B2196967
  · exact B2196971
  · exact B2196975
  · exact B2196979
  · exact B2196983
  · exact B2196987
  · exact B2196991
  · exact B2196995
  · exact B2196999
  · exact B2197003
  · exact B2197007
  · exact B2197011
  · exact B2197015
  · exact B2197019
  · exact B2197023
  · exact B2197027
  · exact B2197031
  · exact B2197035
  · exact B2197039
  · exact B2197043
  · exact B2197047
  · exact B2197051
  · exact B2197055
  · exact B2197059
  · exact B2197063
  · exact B2197067
  · exact B2197071
  · exact B2197075
  · exact B2197079
  · exact B2197083
  · exact B2197087
  · exact B2197091
  · exact B2197095
  · exact B2197099
  · exact B2197103
  · exact B2197107
  · exact B2197111
  · exact B2197115
  · exact B2197119
  · exact B2197123
  · exact B2197127
  · exact B2197131
  · exact B2197135
  · exact B2197139
  · exact B2197143
  · exact B2197147
  · exact B2197151
  · exact B2197155
  · exact B2197159
  · exact B2197163
  · exact B2197167
  · exact B2197171
  · exact B2197175
  · exact B2197179
  · exact B2197183
  · exact B2197187
  · exact B2197191
  · exact B2197195
  · exact B2197199
  · exact B2197203
  · exact B2197207
  · exact B2197211
  · exact B2197215
  · exact B2197219
  · exact B2197223
  · exact B2197227
  · exact B2197231
  · exact B2197235
  · exact B2197239
  · exact B2197243
  · exact B2197247
  · exact B2197251
  · exact B2197255
  · exact B2197259
  · exact B2197263
  · exact B2197267
  · exact B2197271
  · exact B2197275
  · exact B2197279
  · exact B2197283
  · exact B2197287
  · exact B2197291
  · exact B2197295
  · exact B2197299
  · exact B2197303
  · exact B2197307
  · exact B2197311
  · exact B2197315
  · exact B2197319
  · exact B2197323
  · exact B2197327
  · exact B2197331
  · exact B2197335
  · exact B2197339
  · exact B2197343
  · exact B2197347
  · exact B2197351
  · exact B2197355
  · exact B2197359
  · exact B2197363
  · exact B2197367
  · exact B2197371
  · exact B2197375
  · exact B2197379
  · exact B2197383
  · exact B2197387
  · exact B2197391
  · exact B2197395
  · exact B2197399
  · exact B2197403
  · exact B2197407
  · exact B2197411
  · exact B2197415
  · exact B2197419
  · exact B2197423
  · exact B2197427
  · exact B2197431
  · exact B2197435
theorem solution (m : ℕ) (hlo : 2195435 ≤ m) (hhi : m ≤ 2197435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 548858 ≤ j := by omega
    have hj2 : j ≤ 549358 := by omega
    have hb : Blo 2195435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
