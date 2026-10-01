-- Prove2me | solution 1 for syracuse_descends_range_2027435_2029435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:59.213303+00:00
-- url     : https://prove2.me/submissions/4f52f51d-42dc-4a3e-85cf-3b68eaf8bead

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

theorem B2280865 : Blo 2027435 2280865 := bbase (se 2 (by rfl) ⟨855324, by rfl⟩ : syracuseStep 2280865 = 1710649) (by norm_num)
theorem B3041153 : Blo 2027435 3041153 := bstep (se 2 (by rfl) ⟨1140432, by rfl⟩ : syracuseStep 3041153 = 2280865) B2280865
theorem B2027435 : Blo 2027435 2027435 := bstep (se 1 (by rfl) ⟨1520576, by rfl⟩ : syracuseStep 2027435 = 3041153) B3041153
theorem B5131957 : Blo 2027435 5131957 := bbase (se 5 (by rfl) ⟨240560, by rfl⟩ : syracuseStep 5131957 = 481121) (by norm_num)
theorem B6842609 : Blo 2027435 6842609 := bstep (se 2 (by rfl) ⟨2565978, by rfl⟩ : syracuseStep 6842609 = 5131957) B5131957
theorem B4561739 : Blo 2027435 4561739 := bstep (se 1 (by rfl) ⟨3421304, by rfl⟩ : syracuseStep 4561739 = 6842609) B6842609
theorem B3041159 : Blo 2027435 3041159 := bstep (se 1 (by rfl) ⟨2280869, by rfl⟩ : syracuseStep 3041159 = 4561739) B4561739
theorem B2027439 : Blo 2027435 2027439 := bstep (se 1 (by rfl) ⟨1520579, by rfl⟩ : syracuseStep 2027439 = 3041159) B3041159
theorem B3041165 : Blo 2027435 3041165 := bbase (se 3 (by rfl) ⟨570218, by rfl⟩ : syracuseStep 3041165 = 1140437) (by norm_num)
theorem B2027443 : Blo 2027435 2027443 := bstep (se 1 (by rfl) ⟨1520582, by rfl⟩ : syracuseStep 2027443 = 3041165) B3041165
theorem B4561757 : Blo 2027435 4561757 := bbase (se 3 (by rfl) ⟨855329, by rfl⟩ : syracuseStep 4561757 = 1710659) (by norm_num)
theorem B3041171 : Blo 2027435 3041171 := bstep (se 1 (by rfl) ⟨2280878, by rfl⟩ : syracuseStep 3041171 = 4561757) B4561757
theorem B2027447 : Blo 2027435 2027447 := bstep (se 1 (by rfl) ⟨1520585, by rfl⟩ : syracuseStep 2027447 = 3041171) B3041171
theorem B3421325 : Blo 2027435 3421325 := bbase (se 3 (by rfl) ⟨641498, by rfl⟩ : syracuseStep 3421325 = 1282997) (by norm_num)
theorem B2280883 : Blo 2027435 2280883 := bstep (se 1 (by rfl) ⟨1710662, by rfl⟩ : syracuseStep 2280883 = 3421325) B3421325
theorem B3041177 : Blo 2027435 3041177 := bstep (se 2 (by rfl) ⟨1140441, by rfl⟩ : syracuseStep 3041177 = 2280883) B2280883
theorem B2027451 : Blo 2027435 2027451 := bstep (se 1 (by rfl) ⟨1520588, by rfl⟩ : syracuseStep 2027451 = 3041177) B3041177
theorem B4871389 : Blo 2027435 4871389 := bbase (se 3 (by rfl) ⟨913385, by rfl⟩ : syracuseStep 4871389 = 1826771) (by norm_num)
theorem B6495185 : Blo 2027435 6495185 := bstep (se 2 (by rfl) ⟨2435694, by rfl⟩ : syracuseStep 6495185 = 4871389) B4871389
theorem B17320493 : Blo 2027435 17320493 := bstep (se 3 (by rfl) ⟨3247592, by rfl⟩ : syracuseStep 17320493 = 6495185) B6495185
theorem B11546995 : Blo 2027435 11546995 := bstep (se 1 (by rfl) ⟨8660246, by rfl⟩ : syracuseStep 11546995 = 17320493) B17320493
theorem B15395993 : Blo 2027435 15395993 := bstep (se 2 (by rfl) ⟨5773497, by rfl⟩ : syracuseStep 15395993 = 11546995) B11546995
theorem B10263995 : Blo 2027435 10263995 := bstep (se 1 (by rfl) ⟨7697996, by rfl⟩ : syracuseStep 10263995 = 15395993) B15395993
theorem B6842663 : Blo 2027435 6842663 := bstep (se 1 (by rfl) ⟨5131997, by rfl⟩ : syracuseStep 6842663 = 10263995) B10263995
theorem B4561775 : Blo 2027435 4561775 := bstep (se 1 (by rfl) ⟨3421331, by rfl⟩ : syracuseStep 4561775 = 6842663) B6842663
theorem B3041183 : Blo 2027435 3041183 := bstep (se 1 (by rfl) ⟨2280887, by rfl⟩ : syracuseStep 3041183 = 4561775) B4561775
theorem B2027455 : Blo 2027435 2027455 := bstep (se 1 (by rfl) ⟨1520591, by rfl⟩ : syracuseStep 2027455 = 3041183) B3041183
theorem B3041189 : Blo 2027435 3041189 := bbase (se 4 (by rfl) ⟨285111, by rfl⟩ : syracuseStep 3041189 = 570223) (by norm_num)
theorem B2027459 : Blo 2027435 2027459 := bstep (se 1 (by rfl) ⟨1520594, by rfl⟩ : syracuseStep 2027459 = 3041189) B3041189
theorem B2566009 : Blo 2027435 2566009 := bbase (se 2 (by rfl) ⟨962253, by rfl⟩ : syracuseStep 2566009 = 1924507) (by norm_num)
theorem B3421345 : Blo 2027435 3421345 := bstep (se 2 (by rfl) ⟨1283004, by rfl⟩ : syracuseStep 3421345 = 2566009) B2566009
theorem B4561793 : Blo 2027435 4561793 := bstep (se 2 (by rfl) ⟨1710672, by rfl⟩ : syracuseStep 4561793 = 3421345) B3421345
theorem B3041195 : Blo 2027435 3041195 := bstep (se 1 (by rfl) ⟨2280896, by rfl⟩ : syracuseStep 3041195 = 4561793) B4561793
theorem B2027463 : Blo 2027435 2027463 := bstep (se 1 (by rfl) ⟨1520597, by rfl⟩ : syracuseStep 2027463 = 3041195) B3041195
theorem B2280901 : Blo 2027435 2280901 := bbase (se 4 (by rfl) ⟨213834, by rfl⟩ : syracuseStep 2280901 = 427669) (by norm_num)
theorem B3041201 : Blo 2027435 3041201 := bstep (se 2 (by rfl) ⟨1140450, by rfl⟩ : syracuseStep 3041201 = 2280901) B2280901
theorem B2027467 : Blo 2027435 2027467 := bstep (se 1 (by rfl) ⟨1520600, by rfl⟩ : syracuseStep 2027467 = 3041201) B3041201
theorem B3849029 : Blo 2027435 3849029 := bbase (se 4 (by rfl) ⟨360846, by rfl⟩ : syracuseStep 3849029 = 721693) (by norm_num)
theorem B2566019 : Blo 2027435 2566019 := bstep (se 1 (by rfl) ⟨1924514, by rfl⟩ : syracuseStep 2566019 = 3849029) B3849029
theorem B6842717 : Blo 2027435 6842717 := bstep (se 3 (by rfl) ⟨1283009, by rfl⟩ : syracuseStep 6842717 = 2566019) B2566019
theorem B4561811 : Blo 2027435 4561811 := bstep (se 1 (by rfl) ⟨3421358, by rfl⟩ : syracuseStep 4561811 = 6842717) B6842717
theorem B3041207 : Blo 2027435 3041207 := bstep (se 1 (by rfl) ⟨2280905, by rfl⟩ : syracuseStep 3041207 = 4561811) B4561811
theorem B2027471 : Blo 2027435 2027471 := bstep (se 1 (by rfl) ⟨1520603, by rfl⟩ : syracuseStep 2027471 = 3041207) B3041207
theorem B3041213 : Blo 2027435 3041213 := bbase (se 3 (by rfl) ⟨570227, by rfl⟩ : syracuseStep 3041213 = 1140455) (by norm_num)
theorem B2027475 : Blo 2027435 2027475 := bstep (se 1 (by rfl) ⟨1520606, by rfl⟩ : syracuseStep 2027475 = 3041213) B3041213
theorem B4561829 : Blo 2027435 4561829 := bbase (se 4 (by rfl) ⟨427671, by rfl⟩ : syracuseStep 4561829 = 855343) (by norm_num)
theorem B3041219 : Blo 2027435 3041219 := bstep (se 1 (by rfl) ⟨2280914, by rfl⟩ : syracuseStep 3041219 = 4561829) B4561829
theorem B2027479 : Blo 2027435 2027479 := bstep (se 1 (by rfl) ⟨1520609, by rfl⟩ : syracuseStep 2027479 = 3041219) B3041219
theorem B5132069 : Blo 2027435 5132069 := bbase (se 4 (by rfl) ⟨481131, by rfl⟩ : syracuseStep 5132069 = 962263) (by norm_num)
theorem B3421379 : Blo 2027435 3421379 := bstep (se 1 (by rfl) ⟨2566034, by rfl⟩ : syracuseStep 3421379 = 5132069) B5132069
theorem B2280919 : Blo 2027435 2280919 := bstep (se 1 (by rfl) ⟨1710689, by rfl⟩ : syracuseStep 2280919 = 3421379) B3421379
theorem B3041225 : Blo 2027435 3041225 := bstep (se 2 (by rfl) ⟨1140459, by rfl⟩ : syracuseStep 3041225 = 2280919) B2280919
theorem B2027483 : Blo 2027435 2027483 := bstep (se 1 (by rfl) ⟨1520612, by rfl⟩ : syracuseStep 2027483 = 3041225) B3041225
theorem B5773589 : Blo 2027435 5773589 := bbase (se 6 (by rfl) ⟨135318, by rfl⟩ : syracuseStep 5773589 = 270637) (by norm_num)
theorem B3849059 : Blo 2027435 3849059 := bstep (se 1 (by rfl) ⟨2886794, by rfl⟩ : syracuseStep 3849059 = 5773589) B5773589
theorem B10264157 : Blo 2027435 10264157 := bstep (se 3 (by rfl) ⟨1924529, by rfl⟩ : syracuseStep 10264157 = 3849059) B3849059
theorem B6842771 : Blo 2027435 6842771 := bstep (se 1 (by rfl) ⟨5132078, by rfl⟩ : syracuseStep 6842771 = 10264157) B10264157
theorem B4561847 : Blo 2027435 4561847 := bstep (se 1 (by rfl) ⟨3421385, by rfl⟩ : syracuseStep 4561847 = 6842771) B6842771
theorem B3041231 : Blo 2027435 3041231 := bstep (se 1 (by rfl) ⟨2280923, by rfl⟩ : syracuseStep 3041231 = 4561847) B4561847
theorem B2027487 : Blo 2027435 2027487 := bstep (se 1 (by rfl) ⟨1520615, by rfl⟩ : syracuseStep 2027487 = 3041231) B3041231
theorem B3041237 : Blo 2027435 3041237 := bbase (se 7 (by rfl) ⟨35639, by rfl⟩ : syracuseStep 3041237 = 71279) (by norm_num)
theorem B2027491 : Blo 2027435 2027491 := bstep (se 1 (by rfl) ⟨1520618, by rfl⟩ : syracuseStep 2027491 = 3041237) B3041237
theorem B7698149 : Blo 2027435 7698149 := bbase (se 4 (by rfl) ⟨721701, by rfl⟩ : syracuseStep 7698149 = 1443403) (by norm_num)
theorem B5132099 : Blo 2027435 5132099 := bstep (se 1 (by rfl) ⟨3849074, by rfl⟩ : syracuseStep 5132099 = 7698149) B7698149
theorem B3421399 : Blo 2027435 3421399 := bstep (se 1 (by rfl) ⟨2566049, by rfl⟩ : syracuseStep 3421399 = 5132099) B5132099
theorem B4561865 : Blo 2027435 4561865 := bstep (se 2 (by rfl) ⟨1710699, by rfl⟩ : syracuseStep 4561865 = 3421399) B3421399
theorem B3041243 : Blo 2027435 3041243 := bstep (se 1 (by rfl) ⟨2280932, by rfl⟩ : syracuseStep 3041243 = 4561865) B4561865
theorem B2027495 : Blo 2027435 2027495 := bstep (se 1 (by rfl) ⟨1520621, by rfl⟩ : syracuseStep 2027495 = 3041243) B3041243
theorem B2280937 : Blo 2027435 2280937 := bbase (se 2 (by rfl) ⟨855351, by rfl⟩ : syracuseStep 2280937 = 1710703) (by norm_num)
theorem B3041249 : Blo 2027435 3041249 := bstep (se 2 (by rfl) ⟨1140468, by rfl⟩ : syracuseStep 3041249 = 2280937) B2280937
theorem B2027499 : Blo 2027435 2027499 := bstep (se 1 (by rfl) ⟨1520624, by rfl⟩ : syracuseStep 2027499 = 3041249) B3041249
theorem B2165113 : Blo 2027435 2165113 := bbase (se 2 (by rfl) ⟨811917, by rfl⟩ : syracuseStep 2165113 = 1623835) (by norm_num)
theorem B11547269 : Blo 2027435 11547269 := bstep (se 4 (by rfl) ⟨1082556, by rfl⟩ : syracuseStep 11547269 = 2165113) B2165113
theorem B7698179 : Blo 2027435 7698179 := bstep (se 1 (by rfl) ⟨5773634, by rfl⟩ : syracuseStep 7698179 = 11547269) B11547269
theorem B5132119 : Blo 2027435 5132119 := bstep (se 1 (by rfl) ⟨3849089, by rfl⟩ : syracuseStep 5132119 = 7698179) B7698179
theorem B6842825 : Blo 2027435 6842825 := bstep (se 2 (by rfl) ⟨2566059, by rfl⟩ : syracuseStep 6842825 = 5132119) B5132119
theorem B4561883 : Blo 2027435 4561883 := bstep (se 1 (by rfl) ⟨3421412, by rfl⟩ : syracuseStep 4561883 = 6842825) B6842825
theorem B3041255 : Blo 2027435 3041255 := bstep (se 1 (by rfl) ⟨2280941, by rfl⟩ : syracuseStep 3041255 = 4561883) B4561883
theorem B2027503 : Blo 2027435 2027503 := bstep (se 1 (by rfl) ⟨1520627, by rfl⟩ : syracuseStep 2027503 = 3041255) B3041255
theorem B3041261 : Blo 2027435 3041261 := bbase (se 3 (by rfl) ⟨570236, by rfl⟩ : syracuseStep 3041261 = 1140473) (by norm_num)
theorem B2027507 : Blo 2027435 2027507 := bstep (se 1 (by rfl) ⟨1520630, by rfl⟩ : syracuseStep 2027507 = 3041261) B3041261
theorem B4561901 : Blo 2027435 4561901 := bbase (se 3 (by rfl) ⟨855356, by rfl⟩ : syracuseStep 4561901 = 1710713) (by norm_num)
theorem B3041267 : Blo 2027435 3041267 := bstep (se 1 (by rfl) ⟨2280950, by rfl⟩ : syracuseStep 3041267 = 4561901) B4561901
theorem B2027511 : Blo 2027435 2027511 := bstep (se 1 (by rfl) ⟨1520633, by rfl⟩ : syracuseStep 2027511 = 3041267) B3041267
theorem B4330253 : Blo 2027435 4330253 := bbase (se 3 (by rfl) ⟨811922, by rfl⟩ : syracuseStep 4330253 = 1623845) (by norm_num)
theorem B2886835 : Blo 2027435 2886835 := bstep (se 1 (by rfl) ⟨2165126, by rfl⟩ : syracuseStep 2886835 = 4330253) B4330253
theorem B3849113 : Blo 2027435 3849113 := bstep (se 2 (by rfl) ⟨1443417, by rfl⟩ : syracuseStep 3849113 = 2886835) B2886835
theorem B2566075 : Blo 2027435 2566075 := bstep (se 1 (by rfl) ⟨1924556, by rfl⟩ : syracuseStep 2566075 = 3849113) B3849113
theorem B3421433 : Blo 2027435 3421433 := bstep (se 2 (by rfl) ⟨1283037, by rfl⟩ : syracuseStep 3421433 = 2566075) B2566075
theorem B2280955 : Blo 2027435 2280955 := bstep (se 1 (by rfl) ⟨1710716, by rfl⟩ : syracuseStep 2280955 = 3421433) B3421433
theorem B3041273 : Blo 2027435 3041273 := bstep (se 2 (by rfl) ⟨1140477, by rfl⟩ : syracuseStep 3041273 = 2280955) B2280955
theorem B2027515 : Blo 2027435 2027515 := bstep (se 1 (by rfl) ⟨1520636, by rfl⟩ : syracuseStep 2027515 = 3041273) B3041273
theorem B10546309 : Blo 2027435 10546309 := bbase (se 4 (by rfl) ⟨988716, by rfl⟩ : syracuseStep 10546309 = 1977433) (by norm_num)
theorem B14061745 : Blo 2027435 14061745 := bstep (se 2 (by rfl) ⟨5273154, by rfl⟩ : syracuseStep 14061745 = 10546309) B10546309
theorem B18748993 : Blo 2027435 18748993 := bstep (se 2 (by rfl) ⟨7030872, by rfl⟩ : syracuseStep 18748993 = 14061745) B14061745
theorem B24998657 : Blo 2027435 24998657 := bstep (se 2 (by rfl) ⟨9374496, by rfl⟩ : syracuseStep 24998657 = 18748993) B18748993
theorem B66663085 : Blo 2027435 66663085 := bstep (se 3 (by rfl) ⟨12499328, by rfl⟩ : syracuseStep 66663085 = 24998657) B24998657
theorem B88884113 : Blo 2027435 88884113 := bstep (se 2 (by rfl) ⟨33331542, by rfl⟩ : syracuseStep 88884113 = 66663085) B66663085
theorem B237024301 : Blo 2027435 237024301 := bstep (se 3 (by rfl) ⟨44442056, by rfl⟩ : syracuseStep 237024301 = 88884113) B88884113
theorem B316032401 : Blo 2027435 316032401 := bstep (se 2 (by rfl) ⟨118512150, by rfl⟩ : syracuseStep 316032401 = 237024301) B237024301
theorem B842753069 : Blo 2027435 842753069 := bstep (se 3 (by rfl) ⟨158016200, by rfl⟩ : syracuseStep 842753069 = 316032401) B316032401
theorem B561835379 : Blo 2027435 561835379 := bstep (se 1 (by rfl) ⟨421376534, by rfl⟩ : syracuseStep 561835379 = 842753069) B842753069
theorem B1498227677 : Blo 2027435 1498227677 := bstep (se 3 (by rfl) ⟨280917689, by rfl⟩ : syracuseStep 1498227677 = 561835379) B561835379
theorem B998818451 : Blo 2027435 998818451 := bstep (se 1 (by rfl) ⟨749113838, by rfl⟩ : syracuseStep 998818451 = 1498227677) B1498227677
theorem B665878967 : Blo 2027435 665878967 := bstep (se 1 (by rfl) ⟨499409225, by rfl⟩ : syracuseStep 665878967 = 998818451) B998818451
theorem B443919311 : Blo 2027435 443919311 := bstep (se 1 (by rfl) ⟨332939483, by rfl⟩ : syracuseStep 443919311 = 665878967) B665878967
theorem B295946207 : Blo 2027435 295946207 := bstep (se 1 (by rfl) ⟨221959655, by rfl⟩ : syracuseStep 295946207 = 443919311) B443919311
theorem B197297471 : Blo 2027435 197297471 := bstep (se 1 (by rfl) ⟨147973103, by rfl⟩ : syracuseStep 197297471 = 295946207) B295946207
theorem B131531647 : Blo 2027435 131531647 := bstep (se 1 (by rfl) ⟨98648735, by rfl⟩ : syracuseStep 131531647 = 197297471) B197297471
theorem B175375529 : Blo 2027435 175375529 := bstep (se 2 (by rfl) ⟨65765823, by rfl⟩ : syracuseStep 175375529 = 131531647) B131531647
theorem B116917019 : Blo 2027435 116917019 := bstep (se 1 (by rfl) ⟨87687764, by rfl⟩ : syracuseStep 116917019 = 175375529) B175375529
theorem B77944679 : Blo 2027435 77944679 := bstep (se 1 (by rfl) ⟨58458509, by rfl⟩ : syracuseStep 77944679 = 116917019) B116917019
theorem B51963119 : Blo 2027435 51963119 := bstep (se 1 (by rfl) ⟨38972339, by rfl⟩ : syracuseStep 51963119 = 77944679) B77944679
theorem B34642079 : Blo 2027435 34642079 := bstep (se 1 (by rfl) ⟨25981559, by rfl⟩ : syracuseStep 34642079 = 51963119) B51963119
theorem B23094719 : Blo 2027435 23094719 := bstep (se 1 (by rfl) ⟨17321039, by rfl⟩ : syracuseStep 23094719 = 34642079) B34642079
theorem B15396479 : Blo 2027435 15396479 := bstep (se 1 (by rfl) ⟨11547359, by rfl⟩ : syracuseStep 15396479 = 23094719) B23094719
theorem B10264319 : Blo 2027435 10264319 := bstep (se 1 (by rfl) ⟨7698239, by rfl⟩ : syracuseStep 10264319 = 15396479) B15396479
theorem B6842879 : Blo 2027435 6842879 := bstep (se 1 (by rfl) ⟨5132159, by rfl⟩ : syracuseStep 6842879 = 10264319) B10264319
theorem B4561919 : Blo 2027435 4561919 := bstep (se 1 (by rfl) ⟨3421439, by rfl⟩ : syracuseStep 4561919 = 6842879) B6842879
theorem B3041279 : Blo 2027435 3041279 := bstep (se 1 (by rfl) ⟨2280959, by rfl⟩ : syracuseStep 3041279 = 4561919) B4561919
theorem B2027519 : Blo 2027435 2027519 := bstep (se 1 (by rfl) ⟨1520639, by rfl⟩ : syracuseStep 2027519 = 3041279) B3041279
theorem B3041285 : Blo 2027435 3041285 := bbase (se 4 (by rfl) ⟨285120, by rfl⟩ : syracuseStep 3041285 = 570241) (by norm_num)
theorem B2027523 : Blo 2027435 2027523 := bstep (se 1 (by rfl) ⟨1520642, by rfl⟩ : syracuseStep 2027523 = 3041285) B3041285
theorem B3421453 : Blo 2027435 3421453 := bbase (se 3 (by rfl) ⟨641522, by rfl⟩ : syracuseStep 3421453 = 1283045) (by norm_num)
theorem B4561937 : Blo 2027435 4561937 := bstep (se 2 (by rfl) ⟨1710726, by rfl⟩ : syracuseStep 4561937 = 3421453) B3421453
theorem B3041291 : Blo 2027435 3041291 := bstep (se 1 (by rfl) ⟨2280968, by rfl⟩ : syracuseStep 3041291 = 4561937) B4561937
theorem B2027527 : Blo 2027435 2027527 := bstep (se 1 (by rfl) ⟨1520645, by rfl⟩ : syracuseStep 2027527 = 3041291) B3041291
theorem B2280973 : Blo 2027435 2280973 := bbase (se 3 (by rfl) ⟨427682, by rfl⟩ : syracuseStep 2280973 = 855365) (by norm_num)
theorem B3041297 : Blo 2027435 3041297 := bstep (se 2 (by rfl) ⟨1140486, by rfl⟩ : syracuseStep 3041297 = 2280973) B2280973
theorem B2027531 : Blo 2027435 2027531 := bstep (se 1 (by rfl) ⟨1520648, by rfl⟩ : syracuseStep 2027531 = 3041297) B3041297
theorem B6842933 : Blo 2027435 6842933 := bbase (se 5 (by rfl) ⟨320762, by rfl⟩ : syracuseStep 6842933 = 641525) (by norm_num)
theorem B4561955 : Blo 2027435 4561955 := bstep (se 1 (by rfl) ⟨3421466, by rfl⟩ : syracuseStep 4561955 = 6842933) B6842933
theorem B3041303 : Blo 2027435 3041303 := bstep (se 1 (by rfl) ⟨2280977, by rfl⟩ : syracuseStep 3041303 = 4561955) B4561955
theorem B2027535 : Blo 2027435 2027535 := bstep (se 1 (by rfl) ⟨1520651, by rfl⟩ : syracuseStep 2027535 = 3041303) B3041303
theorem B3041309 : Blo 2027435 3041309 := bbase (se 3 (by rfl) ⟨570245, by rfl⟩ : syracuseStep 3041309 = 1140491) (by norm_num)
theorem B2027539 : Blo 2027435 2027539 := bstep (se 1 (by rfl) ⟨1520654, by rfl⟩ : syracuseStep 2027539 = 3041309) B3041309
theorem B4561973 : Blo 2027435 4561973 := bbase (se 5 (by rfl) ⟨213842, by rfl⟩ : syracuseStep 4561973 = 427685) (by norm_num)
theorem B3041315 : Blo 2027435 3041315 := bstep (se 1 (by rfl) ⟨2280986, by rfl⟩ : syracuseStep 3041315 = 4561973) B4561973
theorem B2027543 : Blo 2027435 2027543 := bstep (se 1 (by rfl) ⟨1520657, by rfl⟩ : syracuseStep 2027543 = 3041315) B3041315
theorem B2312113 : Blo 2027435 2312113 := bbase (se 2 (by rfl) ⟨867042, by rfl⟩ : syracuseStep 2312113 = 1734085) (by norm_num)
theorem B3082817 : Blo 2027435 3082817 := bstep (se 2 (by rfl) ⟨1156056, by rfl⟩ : syracuseStep 3082817 = 2312113) B2312113
theorem B8220845 : Blo 2027435 8220845 := bstep (se 3 (by rfl) ⟨1541408, by rfl⟩ : syracuseStep 8220845 = 3082817) B3082817
theorem B5480563 : Blo 2027435 5480563 := bstep (se 1 (by rfl) ⟨4110422, by rfl⟩ : syracuseStep 5480563 = 8220845) B8220845
theorem B7307417 : Blo 2027435 7307417 := bstep (se 2 (by rfl) ⟨2740281, by rfl⟩ : syracuseStep 7307417 = 5480563) B5480563
theorem B4871611 : Blo 2027435 4871611 := bstep (se 1 (by rfl) ⟨3653708, by rfl⟩ : syracuseStep 4871611 = 7307417) B7307417
theorem B6495481 : Blo 2027435 6495481 := bstep (se 2 (by rfl) ⟨2435805, by rfl⟩ : syracuseStep 6495481 = 4871611) B4871611
theorem B8660641 : Blo 2027435 8660641 := bstep (se 2 (by rfl) ⟨3247740, by rfl⟩ : syracuseStep 8660641 = 6495481) B6495481
theorem B11547521 : Blo 2027435 11547521 := bstep (se 2 (by rfl) ⟨4330320, by rfl⟩ : syracuseStep 11547521 = 8660641) B8660641
theorem B7698347 : Blo 2027435 7698347 := bstep (se 1 (by rfl) ⟨5773760, by rfl⟩ : syracuseStep 7698347 = 11547521) B11547521
theorem B5132231 : Blo 2027435 5132231 := bstep (se 1 (by rfl) ⟨3849173, by rfl⟩ : syracuseStep 5132231 = 7698347) B7698347
theorem B3421487 : Blo 2027435 3421487 := bstep (se 1 (by rfl) ⟨2566115, by rfl⟩ : syracuseStep 3421487 = 5132231) B5132231
theorem B2280991 : Blo 2027435 2280991 := bstep (se 1 (by rfl) ⟨1710743, by rfl⟩ : syracuseStep 2280991 = 3421487) B3421487
theorem B3041321 : Blo 2027435 3041321 := bstep (se 2 (by rfl) ⟨1140495, by rfl⟩ : syracuseStep 3041321 = 2280991) B2280991
theorem B2027547 : Blo 2027435 2027547 := bstep (se 1 (by rfl) ⟨1520660, by rfl⟩ : syracuseStep 2027547 = 3041321) B3041321
theorem B6495493 : Blo 2027435 6495493 := bbase (se 4 (by rfl) ⟨608952, by rfl⟩ : syracuseStep 6495493 = 1217905) (by norm_num)
theorem B8660657 : Blo 2027435 8660657 := bstep (se 2 (by rfl) ⟨3247746, by rfl⟩ : syracuseStep 8660657 = 6495493) B6495493
theorem B5773771 : Blo 2027435 5773771 := bstep (se 1 (by rfl) ⟨4330328, by rfl⟩ : syracuseStep 5773771 = 8660657) B8660657
theorem B7698361 : Blo 2027435 7698361 := bstep (se 2 (by rfl) ⟨2886885, by rfl⟩ : syracuseStep 7698361 = 5773771) B5773771
theorem B10264481 : Blo 2027435 10264481 := bstep (se 2 (by rfl) ⟨3849180, by rfl⟩ : syracuseStep 10264481 = 7698361) B7698361
theorem B6842987 : Blo 2027435 6842987 := bstep (se 1 (by rfl) ⟨5132240, by rfl⟩ : syracuseStep 6842987 = 10264481) B10264481
theorem B4561991 : Blo 2027435 4561991 := bstep (se 1 (by rfl) ⟨3421493, by rfl⟩ : syracuseStep 4561991 = 6842987) B6842987
theorem B3041327 : Blo 2027435 3041327 := bstep (se 1 (by rfl) ⟨2280995, by rfl⟩ : syracuseStep 3041327 = 4561991) B4561991
theorem B2027551 : Blo 2027435 2027551 := bstep (se 1 (by rfl) ⟨1520663, by rfl⟩ : syracuseStep 2027551 = 3041327) B3041327
theorem B3041333 : Blo 2027435 3041333 := bbase (se 5 (by rfl) ⟨142562, by rfl⟩ : syracuseStep 3041333 = 285125) (by norm_num)
theorem B2027555 : Blo 2027435 2027555 := bstep (se 1 (by rfl) ⟨1520666, by rfl⟩ : syracuseStep 2027555 = 3041333) B3041333
theorem B5132261 : Blo 2027435 5132261 := bbase (se 4 (by rfl) ⟨481149, by rfl⟩ : syracuseStep 5132261 = 962299) (by norm_num)
theorem B3421507 : Blo 2027435 3421507 := bstep (se 1 (by rfl) ⟨2566130, by rfl⟩ : syracuseStep 3421507 = 5132261) B5132261
theorem B4562009 : Blo 2027435 4562009 := bstep (se 2 (by rfl) ⟨1710753, by rfl⟩ : syracuseStep 4562009 = 3421507) B3421507
theorem B3041339 : Blo 2027435 3041339 := bstep (se 1 (by rfl) ⟨2281004, by rfl⟩ : syracuseStep 3041339 = 4562009) B4562009
theorem B2027559 : Blo 2027435 2027559 := bstep (se 1 (by rfl) ⟨1520669, by rfl⟩ : syracuseStep 2027559 = 3041339) B3041339
theorem B2281009 : Blo 2027435 2281009 := bbase (se 2 (by rfl) ⟨855378, by rfl⟩ : syracuseStep 2281009 = 1710757) (by norm_num)
theorem B3041345 : Blo 2027435 3041345 := bstep (se 2 (by rfl) ⟨1140504, by rfl⟩ : syracuseStep 3041345 = 2281009) B2281009
theorem B2027563 : Blo 2027435 2027563 := bstep (se 1 (by rfl) ⟨1520672, by rfl⟩ : syracuseStep 2027563 = 3041345) B3041345
theorem B3124909 : Blo 2027435 3124909 := bbase (se 3 (by rfl) ⟨585920, by rfl⟩ : syracuseStep 3124909 = 1171841) (by norm_num)
theorem B4166545 : Blo 2027435 4166545 := bstep (se 2 (by rfl) ⟨1562454, by rfl⟩ : syracuseStep 4166545 = 3124909) B3124909
theorem B5555393 : Blo 2027435 5555393 := bstep (se 2 (by rfl) ⟨2083272, by rfl⟩ : syracuseStep 5555393 = 4166545) B4166545
theorem B3703595 : Blo 2027435 3703595 := bstep (se 1 (by rfl) ⟨2777696, by rfl⟩ : syracuseStep 3703595 = 5555393) B5555393
theorem B9876253 : Blo 2027435 9876253 := bstep (se 3 (by rfl) ⟨1851797, by rfl⟩ : syracuseStep 9876253 = 3703595) B3703595
theorem B13168337 : Blo 2027435 13168337 := bstep (se 2 (by rfl) ⟨4938126, by rfl⟩ : syracuseStep 13168337 = 9876253) B9876253
theorem B35115565 : Blo 2027435 35115565 := bstep (se 3 (by rfl) ⟨6584168, by rfl⟩ : syracuseStep 35115565 = 13168337) B13168337
theorem B46820753 : Blo 2027435 46820753 := bstep (se 2 (by rfl) ⟨17557782, by rfl⟩ : syracuseStep 46820753 = 35115565) B35115565
theorem B31213835 : Blo 2027435 31213835 := bstep (se 1 (by rfl) ⟨23410376, by rfl⟩ : syracuseStep 31213835 = 46820753) B46820753
theorem B20809223 : Blo 2027435 20809223 := bstep (se 1 (by rfl) ⟨15606917, by rfl⟩ : syracuseStep 20809223 = 31213835) B31213835
theorem B13872815 : Blo 2027435 13872815 := bstep (se 1 (by rfl) ⟨10404611, by rfl⟩ : syracuseStep 13872815 = 20809223) B20809223
theorem B9248543 : Blo 2027435 9248543 := bstep (se 1 (by rfl) ⟨6936407, by rfl⟩ : syracuseStep 9248543 = 13872815) B13872815
theorem B6165695 : Blo 2027435 6165695 := bstep (se 1 (by rfl) ⟨4624271, by rfl⟩ : syracuseStep 6165695 = 9248543) B9248543
theorem B4110463 : Blo 2027435 4110463 := bstep (se 1 (by rfl) ⟨3082847, by rfl⟩ : syracuseStep 4110463 = 6165695) B6165695
theorem B5480617 : Blo 2027435 5480617 := bstep (se 2 (by rfl) ⟨2055231, by rfl⟩ : syracuseStep 5480617 = 4110463) B4110463
theorem B7307489 : Blo 2027435 7307489 := bstep (se 2 (by rfl) ⟨2740308, by rfl⟩ : syracuseStep 7307489 = 5480617) B5480617
theorem B4871659 : Blo 2027435 4871659 := bstep (se 1 (by rfl) ⟨3653744, by rfl⟩ : syracuseStep 4871659 = 7307489) B7307489
theorem B6495545 : Blo 2027435 6495545 := bstep (se 2 (by rfl) ⟨2435829, by rfl⟩ : syracuseStep 6495545 = 4871659) B4871659
theorem B4330363 : Blo 2027435 4330363 := bstep (se 1 (by rfl) ⟨3247772, by rfl⟩ : syracuseStep 4330363 = 6495545) B6495545
theorem B5773817 : Blo 2027435 5773817 := bstep (se 2 (by rfl) ⟨2165181, by rfl⟩ : syracuseStep 5773817 = 4330363) B4330363
theorem B3849211 : Blo 2027435 3849211 := bstep (se 1 (by rfl) ⟨2886908, by rfl⟩ : syracuseStep 3849211 = 5773817) B5773817
theorem B5132281 : Blo 2027435 5132281 := bstep (se 2 (by rfl) ⟨1924605, by rfl⟩ : syracuseStep 5132281 = 3849211) B3849211
theorem B6843041 : Blo 2027435 6843041 := bstep (se 2 (by rfl) ⟨2566140, by rfl⟩ : syracuseStep 6843041 = 5132281) B5132281
theorem B4562027 : Blo 2027435 4562027 := bstep (se 1 (by rfl) ⟨3421520, by rfl⟩ : syracuseStep 4562027 = 6843041) B6843041
theorem B3041351 : Blo 2027435 3041351 := bstep (se 1 (by rfl) ⟨2281013, by rfl⟩ : syracuseStep 3041351 = 4562027) B4562027
theorem B2027567 : Blo 2027435 2027567 := bstep (se 1 (by rfl) ⟨1520675, by rfl⟩ : syracuseStep 2027567 = 3041351) B3041351
theorem B3041357 : Blo 2027435 3041357 := bbase (se 3 (by rfl) ⟨570254, by rfl⟩ : syracuseStep 3041357 = 1140509) (by norm_num)
theorem B2027571 : Blo 2027435 2027571 := bstep (se 1 (by rfl) ⟨1520678, by rfl⟩ : syracuseStep 2027571 = 3041357) B3041357
theorem B4562045 : Blo 2027435 4562045 := bbase (se 3 (by rfl) ⟨855383, by rfl⟩ : syracuseStep 4562045 = 1710767) (by norm_num)
theorem B3041363 : Blo 2027435 3041363 := bstep (se 1 (by rfl) ⟨2281022, by rfl⟩ : syracuseStep 3041363 = 4562045) B4562045
theorem B2027575 : Blo 2027435 2027575 := bstep (se 1 (by rfl) ⟨1520681, by rfl⟩ : syracuseStep 2027575 = 3041363) B3041363
theorem B3421541 : Blo 2027435 3421541 := bbase (se 4 (by rfl) ⟨320769, by rfl⟩ : syracuseStep 3421541 = 641539) (by norm_num)
theorem B2281027 : Blo 2027435 2281027 := bstep (se 1 (by rfl) ⟨1710770, by rfl⟩ : syracuseStep 2281027 = 3421541) B3421541
theorem B3041369 : Blo 2027435 3041369 := bstep (se 2 (by rfl) ⟨1140513, by rfl⟩ : syracuseStep 3041369 = 2281027) B2281027
theorem B2027579 : Blo 2027435 2027579 := bstep (se 1 (by rfl) ⟨1520684, by rfl⟩ : syracuseStep 2027579 = 3041369) B3041369
theorem B4330397 : Blo 2027435 4330397 := bbase (se 3 (by rfl) ⟨811949, by rfl⟩ : syracuseStep 4330397 = 1623899) (by norm_num)
theorem B2886931 : Blo 2027435 2886931 := bstep (se 1 (by rfl) ⟨2165198, by rfl⟩ : syracuseStep 2886931 = 4330397) B4330397
theorem B15396965 : Blo 2027435 15396965 := bstep (se 4 (by rfl) ⟨1443465, by rfl⟩ : syracuseStep 15396965 = 2886931) B2886931
theorem B10264643 : Blo 2027435 10264643 := bstep (se 1 (by rfl) ⟨7698482, by rfl⟩ : syracuseStep 10264643 = 15396965) B15396965
theorem B6843095 : Blo 2027435 6843095 := bstep (se 1 (by rfl) ⟨5132321, by rfl⟩ : syracuseStep 6843095 = 10264643) B10264643
theorem B4562063 : Blo 2027435 4562063 := bstep (se 1 (by rfl) ⟨3421547, by rfl⟩ : syracuseStep 4562063 = 6843095) B6843095
theorem B3041375 : Blo 2027435 3041375 := bstep (se 1 (by rfl) ⟨2281031, by rfl⟩ : syracuseStep 3041375 = 4562063) B4562063
theorem B2027583 : Blo 2027435 2027583 := bstep (se 1 (by rfl) ⟨1520687, by rfl⟩ : syracuseStep 2027583 = 3041375) B3041375
theorem B3041381 : Blo 2027435 3041381 := bbase (se 4 (by rfl) ⟨285129, by rfl⟩ : syracuseStep 3041381 = 570259) (by norm_num)
theorem B2027587 : Blo 2027435 2027587 := bstep (se 1 (by rfl) ⟨1520690, by rfl⟩ : syracuseStep 2027587 = 3041381) B3041381
theorem B10961365 : Blo 2027435 10961365 := bbase (se 7 (by rfl) ⟨128453, by rfl⟩ : syracuseStep 10961365 = 256907) (by norm_num)
theorem B14615153 : Blo 2027435 14615153 := bstep (se 2 (by rfl) ⟨5480682, by rfl⟩ : syracuseStep 14615153 = 10961365) B10961365
theorem B9743435 : Blo 2027435 9743435 := bstep (se 1 (by rfl) ⟨7307576, by rfl⟩ : syracuseStep 9743435 = 14615153) B14615153
theorem B6495623 : Blo 2027435 6495623 := bstep (se 1 (by rfl) ⟨4871717, by rfl⟩ : syracuseStep 6495623 = 9743435) B9743435
theorem B4330415 : Blo 2027435 4330415 := bstep (se 1 (by rfl) ⟨3247811, by rfl⟩ : syracuseStep 4330415 = 6495623) B6495623
theorem B2886943 : Blo 2027435 2886943 := bstep (se 1 (by rfl) ⟨2165207, by rfl⟩ : syracuseStep 2886943 = 4330415) B4330415
theorem B3849257 : Blo 2027435 3849257 := bstep (se 2 (by rfl) ⟨1443471, by rfl⟩ : syracuseStep 3849257 = 2886943) B2886943
theorem B2566171 : Blo 2027435 2566171 := bstep (se 1 (by rfl) ⟨1924628, by rfl⟩ : syracuseStep 2566171 = 3849257) B3849257
theorem B3421561 : Blo 2027435 3421561 := bstep (se 2 (by rfl) ⟨1283085, by rfl⟩ : syracuseStep 3421561 = 2566171) B2566171
theorem B4562081 : Blo 2027435 4562081 := bstep (se 2 (by rfl) ⟨1710780, by rfl⟩ : syracuseStep 4562081 = 3421561) B3421561
theorem B3041387 : Blo 2027435 3041387 := bstep (se 1 (by rfl) ⟨2281040, by rfl⟩ : syracuseStep 3041387 = 4562081) B4562081
theorem B2027591 : Blo 2027435 2027591 := bstep (se 1 (by rfl) ⟨1520693, by rfl⟩ : syracuseStep 2027591 = 3041387) B3041387
theorem B2281045 : Blo 2027435 2281045 := bbase (se 8 (by rfl) ⟨13365, by rfl⟩ : syracuseStep 2281045 = 26731) (by norm_num)
theorem B3041393 : Blo 2027435 3041393 := bstep (se 2 (by rfl) ⟨1140522, by rfl⟩ : syracuseStep 3041393 = 2281045) B2281045
theorem B2027595 : Blo 2027435 2027595 := bstep (se 1 (by rfl) ⟨1520696, by rfl⟩ : syracuseStep 2027595 = 3041393) B3041393
theorem B2566181 : Blo 2027435 2566181 := bbase (se 4 (by rfl) ⟨240579, by rfl⟩ : syracuseStep 2566181 = 481159) (by norm_num)
theorem B6843149 : Blo 2027435 6843149 := bstep (se 3 (by rfl) ⟨1283090, by rfl⟩ : syracuseStep 6843149 = 2566181) B2566181
theorem B4562099 : Blo 2027435 4562099 := bstep (se 1 (by rfl) ⟨3421574, by rfl⟩ : syracuseStep 4562099 = 6843149) B6843149
theorem B3041399 : Blo 2027435 3041399 := bstep (se 1 (by rfl) ⟨2281049, by rfl⟩ : syracuseStep 3041399 = 4562099) B4562099
theorem B2027599 : Blo 2027435 2027599 := bstep (se 1 (by rfl) ⟨1520699, by rfl⟩ : syracuseStep 2027599 = 3041399) B3041399
theorem B3041405 : Blo 2027435 3041405 := bbase (se 3 (by rfl) ⟨570263, by rfl⟩ : syracuseStep 3041405 = 1140527) (by norm_num)
theorem B2027603 : Blo 2027435 2027603 := bstep (se 1 (by rfl) ⟨1520702, by rfl⟩ : syracuseStep 2027603 = 3041405) B3041405
theorem B4562117 : Blo 2027435 4562117 := bbase (se 4 (by rfl) ⟨427698, by rfl⟩ : syracuseStep 4562117 = 855397) (by norm_num)
theorem B3041411 : Blo 2027435 3041411 := bstep (se 1 (by rfl) ⟨2281058, by rfl⟩ : syracuseStep 3041411 = 4562117) B4562117
theorem B2027607 : Blo 2027435 2027607 := bstep (se 1 (by rfl) ⟨1520705, by rfl⟩ : syracuseStep 2027607 = 3041411) B3041411
theorem B4871765 : Blo 2027435 4871765 := bbase (se 8 (by rfl) ⟨28545, by rfl⟩ : syracuseStep 4871765 = 57091) (by norm_num)
theorem B12991373 : Blo 2027435 12991373 := bstep (se 3 (by rfl) ⟨2435882, by rfl⟩ : syracuseStep 12991373 = 4871765) B4871765
theorem B8660915 : Blo 2027435 8660915 := bstep (se 1 (by rfl) ⟨6495686, by rfl⟩ : syracuseStep 8660915 = 12991373) B12991373
theorem B5773943 : Blo 2027435 5773943 := bstep (se 1 (by rfl) ⟨4330457, by rfl⟩ : syracuseStep 5773943 = 8660915) B8660915
theorem B3849295 : Blo 2027435 3849295 := bstep (se 1 (by rfl) ⟨2886971, by rfl⟩ : syracuseStep 3849295 = 5773943) B5773943
theorem B5132393 : Blo 2027435 5132393 := bstep (se 2 (by rfl) ⟨1924647, by rfl⟩ : syracuseStep 5132393 = 3849295) B3849295
theorem B3421595 : Blo 2027435 3421595 := bstep (se 1 (by rfl) ⟨2566196, by rfl⟩ : syracuseStep 3421595 = 5132393) B5132393
theorem B2281063 : Blo 2027435 2281063 := bstep (se 1 (by rfl) ⟨1710797, by rfl⟩ : syracuseStep 2281063 = 3421595) B3421595
theorem B3041417 : Blo 2027435 3041417 := bstep (se 2 (by rfl) ⟨1140531, by rfl⟩ : syracuseStep 3041417 = 2281063) B2281063
theorem B2027611 : Blo 2027435 2027611 := bstep (se 1 (by rfl) ⟨1520708, by rfl⟩ : syracuseStep 2027611 = 3041417) B3041417
theorem B10264805 : Blo 2027435 10264805 := bbase (se 4 (by rfl) ⟨962325, by rfl⟩ : syracuseStep 10264805 = 1924651) (by norm_num)
theorem B6843203 : Blo 2027435 6843203 := bstep (se 1 (by rfl) ⟨5132402, by rfl⟩ : syracuseStep 6843203 = 10264805) B10264805
theorem B4562135 : Blo 2027435 4562135 := bstep (se 1 (by rfl) ⟨3421601, by rfl⟩ : syracuseStep 4562135 = 6843203) B6843203
theorem B3041423 : Blo 2027435 3041423 := bstep (se 1 (by rfl) ⟨2281067, by rfl⟩ : syracuseStep 3041423 = 4562135) B4562135
theorem B2027615 : Blo 2027435 2027615 := bstep (se 1 (by rfl) ⟨1520711, by rfl⟩ : syracuseStep 2027615 = 3041423) B3041423
theorem B3041429 : Blo 2027435 3041429 := bbase (se 6 (by rfl) ⟨71283, by rfl⟩ : syracuseStep 3041429 = 142567) (by norm_num)
theorem B2027619 : Blo 2027435 2027619 := bstep (se 1 (by rfl) ⟨1520714, by rfl⟩ : syracuseStep 2027619 = 3041429) B3041429
theorem B8660965 : Blo 2027435 8660965 := bbase (se 4 (by rfl) ⟨811965, by rfl⟩ : syracuseStep 8660965 = 1623931) (by norm_num)
theorem B11547953 : Blo 2027435 11547953 := bstep (se 2 (by rfl) ⟨4330482, by rfl⟩ : syracuseStep 11547953 = 8660965) B8660965
theorem B7698635 : Blo 2027435 7698635 := bstep (se 1 (by rfl) ⟨5773976, by rfl⟩ : syracuseStep 7698635 = 11547953) B11547953
theorem B5132423 : Blo 2027435 5132423 := bstep (se 1 (by rfl) ⟨3849317, by rfl⟩ : syracuseStep 5132423 = 7698635) B7698635
theorem B3421615 : Blo 2027435 3421615 := bstep (se 1 (by rfl) ⟨2566211, by rfl⟩ : syracuseStep 3421615 = 5132423) B5132423
theorem B4562153 : Blo 2027435 4562153 := bstep (se 2 (by rfl) ⟨1710807, by rfl⟩ : syracuseStep 4562153 = 3421615) B3421615
theorem B3041435 : Blo 2027435 3041435 := bstep (se 1 (by rfl) ⟨2281076, by rfl⟩ : syracuseStep 3041435 = 4562153) B4562153
theorem B2027623 : Blo 2027435 2027623 := bstep (se 1 (by rfl) ⟨1520717, by rfl⟩ : syracuseStep 2027623 = 3041435) B3041435
theorem B2281081 : Blo 2027435 2281081 := bbase (se 2 (by rfl) ⟨855405, by rfl⟩ : syracuseStep 2281081 = 1710811) (by norm_num)
theorem B3041441 : Blo 2027435 3041441 := bstep (se 2 (by rfl) ⟨1140540, by rfl⟩ : syracuseStep 3041441 = 2281081) B2281081
theorem B2027627 : Blo 2027435 2027627 := bstep (se 1 (by rfl) ⟨1520720, by rfl⟩ : syracuseStep 2027627 = 3041441) B3041441
theorem B5480789 : Blo 2027435 5480789 := bbase (se 10 (by rfl) ⟨8028, by rfl⟩ : syracuseStep 5480789 = 16057) (by norm_num)
theorem B14615437 : Blo 2027435 14615437 := bstep (se 3 (by rfl) ⟨2740394, by rfl⟩ : syracuseStep 14615437 = 5480789) B5480789
theorem B19487249 : Blo 2027435 19487249 := bstep (se 2 (by rfl) ⟨7307718, by rfl⟩ : syracuseStep 19487249 = 14615437) B14615437
theorem B12991499 : Blo 2027435 12991499 := bstep (se 1 (by rfl) ⟨9743624, by rfl⟩ : syracuseStep 12991499 = 19487249) B19487249
theorem B8660999 : Blo 2027435 8660999 := bstep (se 1 (by rfl) ⟨6495749, by rfl⟩ : syracuseStep 8660999 = 12991499) B12991499
theorem B5773999 : Blo 2027435 5773999 := bstep (se 1 (by rfl) ⟨4330499, by rfl⟩ : syracuseStep 5773999 = 8660999) B8660999
theorem B7698665 : Blo 2027435 7698665 := bstep (se 2 (by rfl) ⟨2886999, by rfl⟩ : syracuseStep 7698665 = 5773999) B5773999
theorem B5132443 : Blo 2027435 5132443 := bstep (se 1 (by rfl) ⟨3849332, by rfl⟩ : syracuseStep 5132443 = 7698665) B7698665
theorem B6843257 : Blo 2027435 6843257 := bstep (se 2 (by rfl) ⟨2566221, by rfl⟩ : syracuseStep 6843257 = 5132443) B5132443
theorem B4562171 : Blo 2027435 4562171 := bstep (se 1 (by rfl) ⟨3421628, by rfl⟩ : syracuseStep 4562171 = 6843257) B6843257
theorem B3041447 : Blo 2027435 3041447 := bstep (se 1 (by rfl) ⟨2281085, by rfl⟩ : syracuseStep 3041447 = 4562171) B4562171
theorem B2027631 : Blo 2027435 2027631 := bstep (se 1 (by rfl) ⟨1520723, by rfl⟩ : syracuseStep 2027631 = 3041447) B3041447
theorem B3041453 : Blo 2027435 3041453 := bbase (se 3 (by rfl) ⟨570272, by rfl⟩ : syracuseStep 3041453 = 1140545) (by norm_num)
theorem B2027635 : Blo 2027435 2027635 := bstep (se 1 (by rfl) ⟨1520726, by rfl⟩ : syracuseStep 2027635 = 3041453) B3041453
theorem B4562189 : Blo 2027435 4562189 := bbase (se 3 (by rfl) ⟨855410, by rfl⟩ : syracuseStep 4562189 = 1710821) (by norm_num)
theorem B3041459 : Blo 2027435 3041459 := bstep (se 1 (by rfl) ⟨2281094, by rfl⟩ : syracuseStep 3041459 = 4562189) B4562189
theorem B2027639 : Blo 2027435 2027639 := bstep (se 1 (by rfl) ⟨1520729, by rfl⟩ : syracuseStep 2027639 = 3041459) B3041459
theorem B2566237 : Blo 2027435 2566237 := bbase (se 3 (by rfl) ⟨481169, by rfl⟩ : syracuseStep 2566237 = 962339) (by norm_num)
theorem B3421649 : Blo 2027435 3421649 := bstep (se 2 (by rfl) ⟨1283118, by rfl⟩ : syracuseStep 3421649 = 2566237) B2566237
theorem B2281099 : Blo 2027435 2281099 := bstep (se 1 (by rfl) ⟨1710824, by rfl⟩ : syracuseStep 2281099 = 3421649) B3421649
theorem B3041465 : Blo 2027435 3041465 := bstep (se 2 (by rfl) ⟨1140549, by rfl⟩ : syracuseStep 3041465 = 2281099) B2281099
theorem B2027643 : Blo 2027435 2027643 := bstep (se 1 (by rfl) ⟨1520732, by rfl⟩ : syracuseStep 2027643 = 3041465) B3041465
theorem B17322133 : Blo 2027435 17322133 := bbase (se 6 (by rfl) ⟨405987, by rfl⟩ : syracuseStep 17322133 = 811975) (by norm_num)
theorem B23096177 : Blo 2027435 23096177 := bstep (se 2 (by rfl) ⟨8661066, by rfl⟩ : syracuseStep 23096177 = 17322133) B17322133
theorem B15397451 : Blo 2027435 15397451 := bstep (se 1 (by rfl) ⟨11548088, by rfl⟩ : syracuseStep 15397451 = 23096177) B23096177
theorem B10264967 : Blo 2027435 10264967 := bstep (se 1 (by rfl) ⟨7698725, by rfl⟩ : syracuseStep 10264967 = 15397451) B15397451
theorem B6843311 : Blo 2027435 6843311 := bstep (se 1 (by rfl) ⟨5132483, by rfl⟩ : syracuseStep 6843311 = 10264967) B10264967
theorem B4562207 : Blo 2027435 4562207 := bstep (se 1 (by rfl) ⟨3421655, by rfl⟩ : syracuseStep 4562207 = 6843311) B6843311
theorem B3041471 : Blo 2027435 3041471 := bstep (se 1 (by rfl) ⟨2281103, by rfl⟩ : syracuseStep 3041471 = 4562207) B4562207
theorem B2027647 : Blo 2027435 2027647 := bstep (se 1 (by rfl) ⟨1520735, by rfl⟩ : syracuseStep 2027647 = 3041471) B3041471
theorem B3041477 : Blo 2027435 3041477 := bbase (se 4 (by rfl) ⟨285138, by rfl⟩ : syracuseStep 3041477 = 570277) (by norm_num)
theorem B2027651 : Blo 2027435 2027651 := bstep (se 1 (by rfl) ⟨1520738, by rfl⟩ : syracuseStep 2027651 = 3041477) B3041477
theorem B3421669 : Blo 2027435 3421669 := bbase (se 4 (by rfl) ⟨320781, by rfl⟩ : syracuseStep 3421669 = 641563) (by norm_num)
theorem B4562225 : Blo 2027435 4562225 := bstep (se 2 (by rfl) ⟨1710834, by rfl⟩ : syracuseStep 4562225 = 3421669) B3421669
theorem B3041483 : Blo 2027435 3041483 := bstep (se 1 (by rfl) ⟨2281112, by rfl⟩ : syracuseStep 3041483 = 4562225) B4562225
theorem B2027655 : Blo 2027435 2027655 := bstep (se 1 (by rfl) ⟨1520741, by rfl⟩ : syracuseStep 2027655 = 3041483) B3041483
theorem B2281117 : Blo 2027435 2281117 := bbase (se 3 (by rfl) ⟨427709, by rfl⟩ : syracuseStep 2281117 = 855419) (by norm_num)
theorem B3041489 : Blo 2027435 3041489 := bstep (se 2 (by rfl) ⟨1140558, by rfl⟩ : syracuseStep 3041489 = 2281117) B2281117
theorem B2027659 : Blo 2027435 2027659 := bstep (se 1 (by rfl) ⟨1520744, by rfl⟩ : syracuseStep 2027659 = 3041489) B3041489
theorem B6843365 : Blo 2027435 6843365 := bbase (se 4 (by rfl) ⟨641565, by rfl⟩ : syracuseStep 6843365 = 1283131) (by norm_num)
theorem B4562243 : Blo 2027435 4562243 := bstep (se 1 (by rfl) ⟨3421682, by rfl⟩ : syracuseStep 4562243 = 6843365) B6843365
theorem B3041495 : Blo 2027435 3041495 := bstep (se 1 (by rfl) ⟨2281121, by rfl⟩ : syracuseStep 3041495 = 4562243) B4562243
theorem B2027663 : Blo 2027435 2027663 := bstep (se 1 (by rfl) ⟨1520747, by rfl⟩ : syracuseStep 2027663 = 3041495) B3041495
theorem B3041501 : Blo 2027435 3041501 := bbase (se 3 (by rfl) ⟨570281, by rfl⟩ : syracuseStep 3041501 = 1140563) (by norm_num)
theorem B2027667 : Blo 2027435 2027667 := bstep (se 1 (by rfl) ⟨1520750, by rfl⟩ : syracuseStep 2027667 = 3041501) B3041501
theorem B4562261 : Blo 2027435 4562261 := bbase (se 11 (by rfl) ⟨3341, by rfl⟩ : syracuseStep 4562261 = 6683) (by norm_num)
theorem B3041507 : Blo 2027435 3041507 := bstep (se 1 (by rfl) ⟨2281130, by rfl⟩ : syracuseStep 3041507 = 4562261) B4562261
theorem B2027671 : Blo 2027435 2027671 := bstep (se 1 (by rfl) ⟨1520753, by rfl⟩ : syracuseStep 2027671 = 3041507) B3041507
theorem B2165297 : Blo 2027435 2165297 := bbase (se 2 (by rfl) ⟨811986, by rfl⟩ : syracuseStep 2165297 = 1623973) (by norm_num)
theorem B5774125 : Blo 2027435 5774125 := bstep (se 3 (by rfl) ⟨1082648, by rfl⟩ : syracuseStep 5774125 = 2165297) B2165297
theorem B7698833 : Blo 2027435 7698833 := bstep (se 2 (by rfl) ⟨2887062, by rfl⟩ : syracuseStep 7698833 = 5774125) B5774125
theorem B5132555 : Blo 2027435 5132555 := bstep (se 1 (by rfl) ⟨3849416, by rfl⟩ : syracuseStep 5132555 = 7698833) B7698833
theorem B3421703 : Blo 2027435 3421703 := bstep (se 1 (by rfl) ⟨2566277, by rfl⟩ : syracuseStep 3421703 = 5132555) B5132555
theorem B2281135 : Blo 2027435 2281135 := bstep (se 1 (by rfl) ⟨1710851, by rfl⟩ : syracuseStep 2281135 = 3421703) B3421703
theorem B3041513 : Blo 2027435 3041513 := bstep (se 2 (by rfl) ⟨1140567, by rfl⟩ : syracuseStep 3041513 = 2281135) B2281135
theorem B2027675 : Blo 2027435 2027675 := bstep (se 1 (by rfl) ⟨1520756, by rfl⟩ : syracuseStep 2027675 = 3041513) B3041513
theorem B4624525 : Blo 2027435 4624525 := bbase (se 3 (by rfl) ⟨867098, by rfl⟩ : syracuseStep 4624525 = 1734197) (by norm_num)
theorem B6166033 : Blo 2027435 6166033 := bstep (se 2 (by rfl) ⟨2312262, by rfl⟩ : syracuseStep 6166033 = 4624525) B4624525
theorem B32885509 : Blo 2027435 32885509 := bstep (se 4 (by rfl) ⟨3083016, by rfl⟩ : syracuseStep 32885509 = 6166033) B6166033
theorem B43847345 : Blo 2027435 43847345 := bstep (se 2 (by rfl) ⟨16442754, by rfl⟩ : syracuseStep 43847345 = 32885509) B32885509
theorem B29231563 : Blo 2027435 29231563 := bstep (se 1 (by rfl) ⟨21923672, by rfl⟩ : syracuseStep 29231563 = 43847345) B43847345
theorem B38975417 : Blo 2027435 38975417 := bstep (se 2 (by rfl) ⟨14615781, by rfl⟩ : syracuseStep 38975417 = 29231563) B29231563
theorem B25983611 : Blo 2027435 25983611 := bstep (se 1 (by rfl) ⟨19487708, by rfl⟩ : syracuseStep 25983611 = 38975417) B38975417
theorem B17322407 : Blo 2027435 17322407 := bstep (se 1 (by rfl) ⟨12991805, by rfl⟩ : syracuseStep 17322407 = 25983611) B25983611
theorem B11548271 : Blo 2027435 11548271 := bstep (se 1 (by rfl) ⟨8661203, by rfl⟩ : syracuseStep 11548271 = 17322407) B17322407
theorem B7698847 : Blo 2027435 7698847 := bstep (se 1 (by rfl) ⟨5774135, by rfl⟩ : syracuseStep 7698847 = 11548271) B11548271
theorem B10265129 : Blo 2027435 10265129 := bstep (se 2 (by rfl) ⟨3849423, by rfl⟩ : syracuseStep 10265129 = 7698847) B7698847
theorem B6843419 : Blo 2027435 6843419 := bstep (se 1 (by rfl) ⟨5132564, by rfl⟩ : syracuseStep 6843419 = 10265129) B10265129
theorem B4562279 : Blo 2027435 4562279 := bstep (se 1 (by rfl) ⟨3421709, by rfl⟩ : syracuseStep 4562279 = 6843419) B6843419
theorem B3041519 : Blo 2027435 3041519 := bstep (se 1 (by rfl) ⟨2281139, by rfl⟩ : syracuseStep 3041519 = 4562279) B4562279
theorem B2027679 : Blo 2027435 2027679 := bstep (se 1 (by rfl) ⟨1520759, by rfl⟩ : syracuseStep 2027679 = 3041519) B3041519
theorem B3041525 : Blo 2027435 3041525 := bbase (se 5 (by rfl) ⟨142571, by rfl⟩ : syracuseStep 3041525 = 285143) (by norm_num)
theorem B2027683 : Blo 2027435 2027683 := bstep (se 1 (by rfl) ⟨1520762, by rfl⟩ : syracuseStep 2027683 = 3041525) B3041525
theorem B2055353 : Blo 2027435 2055353 := bbase (se 2 (by rfl) ⟨770757, by rfl⟩ : syracuseStep 2055353 = 1541515) (by norm_num)
theorem B5480941 : Blo 2027435 5480941 := bstep (se 3 (by rfl) ⟨1027676, by rfl⟩ : syracuseStep 5480941 = 2055353) B2055353
theorem B7307921 : Blo 2027435 7307921 := bstep (se 2 (by rfl) ⟨2740470, by rfl⟩ : syracuseStep 7307921 = 5480941) B5480941
theorem B19487789 : Blo 2027435 19487789 := bstep (se 3 (by rfl) ⟨3653960, by rfl⟩ : syracuseStep 19487789 = 7307921) B7307921
theorem B12991859 : Blo 2027435 12991859 := bstep (se 1 (by rfl) ⟨9743894, by rfl⟩ : syracuseStep 12991859 = 19487789) B19487789
theorem B8661239 : Blo 2027435 8661239 := bstep (se 1 (by rfl) ⟨6495929, by rfl⟩ : syracuseStep 8661239 = 12991859) B12991859
theorem B5774159 : Blo 2027435 5774159 := bstep (se 1 (by rfl) ⟨4330619, by rfl⟩ : syracuseStep 5774159 = 8661239) B8661239
theorem B3849439 : Blo 2027435 3849439 := bstep (se 1 (by rfl) ⟨2887079, by rfl⟩ : syracuseStep 3849439 = 5774159) B5774159
theorem B5132585 : Blo 2027435 5132585 := bstep (se 2 (by rfl) ⟨1924719, by rfl⟩ : syracuseStep 5132585 = 3849439) B3849439
theorem B3421723 : Blo 2027435 3421723 := bstep (se 1 (by rfl) ⟨2566292, by rfl⟩ : syracuseStep 3421723 = 5132585) B5132585
theorem B4562297 : Blo 2027435 4562297 := bstep (se 2 (by rfl) ⟨1710861, by rfl⟩ : syracuseStep 4562297 = 3421723) B3421723
theorem B3041531 : Blo 2027435 3041531 := bstep (se 1 (by rfl) ⟨2281148, by rfl⟩ : syracuseStep 3041531 = 4562297) B4562297
theorem B2027687 : Blo 2027435 2027687 := bstep (se 1 (by rfl) ⟨1520765, by rfl⟩ : syracuseStep 2027687 = 3041531) B3041531
theorem B2281153 : Blo 2027435 2281153 := bbase (se 2 (by rfl) ⟨855432, by rfl⟩ : syracuseStep 2281153 = 1710865) (by norm_num)
theorem B3041537 : Blo 2027435 3041537 := bstep (se 2 (by rfl) ⟨1140576, by rfl⟩ : syracuseStep 3041537 = 2281153) B2281153
theorem B2027691 : Blo 2027435 2027691 := bstep (se 1 (by rfl) ⟨1520768, by rfl⟩ : syracuseStep 2027691 = 3041537) B3041537
theorem B5132605 : Blo 2027435 5132605 := bbase (se 3 (by rfl) ⟨962363, by rfl⟩ : syracuseStep 5132605 = 1924727) (by norm_num)
theorem B6843473 : Blo 2027435 6843473 := bstep (se 2 (by rfl) ⟨2566302, by rfl⟩ : syracuseStep 6843473 = 5132605) B5132605
theorem B4562315 : Blo 2027435 4562315 := bstep (se 1 (by rfl) ⟨3421736, by rfl⟩ : syracuseStep 4562315 = 6843473) B6843473
theorem B3041543 : Blo 2027435 3041543 := bstep (se 1 (by rfl) ⟨2281157, by rfl⟩ : syracuseStep 3041543 = 4562315) B4562315
theorem B2027695 : Blo 2027435 2027695 := bstep (se 1 (by rfl) ⟨1520771, by rfl⟩ : syracuseStep 2027695 = 3041543) B3041543
theorem B3041549 : Blo 2027435 3041549 := bbase (se 3 (by rfl) ⟨570290, by rfl⟩ : syracuseStep 3041549 = 1140581) (by norm_num)
theorem B2027699 : Blo 2027435 2027699 := bstep (se 1 (by rfl) ⟨1520774, by rfl⟩ : syracuseStep 2027699 = 3041549) B3041549
theorem B4562333 : Blo 2027435 4562333 := bbase (se 3 (by rfl) ⟨855437, by rfl⟩ : syracuseStep 4562333 = 1710875) (by norm_num)
theorem B3041555 : Blo 2027435 3041555 := bstep (se 1 (by rfl) ⟨2281166, by rfl⟩ : syracuseStep 3041555 = 4562333) B4562333
theorem B2027703 : Blo 2027435 2027703 := bstep (se 1 (by rfl) ⟨1520777, by rfl⟩ : syracuseStep 2027703 = 3041555) B3041555
theorem B3421757 : Blo 2027435 3421757 := bbase (se 3 (by rfl) ⟨641579, by rfl⟩ : syracuseStep 3421757 = 1283159) (by norm_num)
theorem B2281171 : Blo 2027435 2281171 := bstep (se 1 (by rfl) ⟨1710878, by rfl⟩ : syracuseStep 2281171 = 3421757) B3421757
theorem B3041561 : Blo 2027435 3041561 := bstep (se 2 (by rfl) ⟨1140585, by rfl⟩ : syracuseStep 3041561 = 2281171) B2281171
theorem B2027707 : Blo 2027435 2027707 := bstep (se 1 (by rfl) ⟨1520780, by rfl⟩ : syracuseStep 2027707 = 3041561) B3041561
theorem B4872005 : Blo 2027435 4872005 := bbase (se 4 (by rfl) ⟨456750, by rfl⟩ : syracuseStep 4872005 = 913501) (by norm_num)
theorem B3248003 : Blo 2027435 3248003 := bstep (se 1 (by rfl) ⟨2436002, by rfl⟩ : syracuseStep 3248003 = 4872005) B4872005
theorem B2165335 : Blo 2027435 2165335 := bstep (se 1 (by rfl) ⟨1624001, by rfl⟩ : syracuseStep 2165335 = 3248003) B3248003
theorem B11548453 : Blo 2027435 11548453 := bstep (se 4 (by rfl) ⟨1082667, by rfl⟩ : syracuseStep 11548453 = 2165335) B2165335
theorem B15397937 : Blo 2027435 15397937 := bstep (se 2 (by rfl) ⟨5774226, by rfl⟩ : syracuseStep 15397937 = 11548453) B11548453
theorem B10265291 : Blo 2027435 10265291 := bstep (se 1 (by rfl) ⟨7698968, by rfl⟩ : syracuseStep 10265291 = 15397937) B15397937
theorem B6843527 : Blo 2027435 6843527 := bstep (se 1 (by rfl) ⟨5132645, by rfl⟩ : syracuseStep 6843527 = 10265291) B10265291
theorem B4562351 : Blo 2027435 4562351 := bstep (se 1 (by rfl) ⟨3421763, by rfl⟩ : syracuseStep 4562351 = 6843527) B6843527
theorem B3041567 : Blo 2027435 3041567 := bstep (se 1 (by rfl) ⟨2281175, by rfl⟩ : syracuseStep 3041567 = 4562351) B4562351
theorem B2027711 : Blo 2027435 2027711 := bstep (se 1 (by rfl) ⟨1520783, by rfl⟩ : syracuseStep 2027711 = 3041567) B3041567
theorem B3041573 : Blo 2027435 3041573 := bbase (se 4 (by rfl) ⟨285147, by rfl⟩ : syracuseStep 3041573 = 570295) (by norm_num)
theorem B2027715 : Blo 2027435 2027715 := bstep (se 1 (by rfl) ⟨1520786, by rfl⟩ : syracuseStep 2027715 = 3041573) B3041573
theorem B2566333 : Blo 2027435 2566333 := bbase (se 3 (by rfl) ⟨481187, by rfl⟩ : syracuseStep 2566333 = 962375) (by norm_num)
theorem B3421777 : Blo 2027435 3421777 := bstep (se 2 (by rfl) ⟨1283166, by rfl⟩ : syracuseStep 3421777 = 2566333) B2566333
theorem B4562369 : Blo 2027435 4562369 := bstep (se 2 (by rfl) ⟨1710888, by rfl⟩ : syracuseStep 4562369 = 3421777) B3421777
theorem B3041579 : Blo 2027435 3041579 := bstep (se 1 (by rfl) ⟨2281184, by rfl⟩ : syracuseStep 3041579 = 4562369) B4562369
theorem B2027719 : Blo 2027435 2027719 := bstep (se 1 (by rfl) ⟨1520789, by rfl⟩ : syracuseStep 2027719 = 3041579) B3041579
theorem B2281189 : Blo 2027435 2281189 := bbase (se 4 (by rfl) ⟨213861, by rfl⟩ : syracuseStep 2281189 = 427723) (by norm_num)
theorem B3041585 : Blo 2027435 3041585 := bstep (se 2 (by rfl) ⟨1140594, by rfl⟩ : syracuseStep 3041585 = 2281189) B2281189
theorem B2027723 : Blo 2027435 2027723 := bstep (se 1 (by rfl) ⟨1520792, by rfl⟩ : syracuseStep 2027723 = 3041585) B3041585
theorem B3248029 : Blo 2027435 3248029 := bbase (se 3 (by rfl) ⟨609005, by rfl⟩ : syracuseStep 3248029 = 1218011) (by norm_num)
theorem B4330705 : Blo 2027435 4330705 := bstep (se 2 (by rfl) ⟨1624014, by rfl⟩ : syracuseStep 4330705 = 3248029) B3248029
theorem B5774273 : Blo 2027435 5774273 := bstep (se 2 (by rfl) ⟨2165352, by rfl⟩ : syracuseStep 5774273 = 4330705) B4330705
theorem B3849515 : Blo 2027435 3849515 := bstep (se 1 (by rfl) ⟨2887136, by rfl⟩ : syracuseStep 3849515 = 5774273) B5774273
theorem B2566343 : Blo 2027435 2566343 := bstep (se 1 (by rfl) ⟨1924757, by rfl⟩ : syracuseStep 2566343 = 3849515) B3849515
theorem B6843581 : Blo 2027435 6843581 := bstep (se 3 (by rfl) ⟨1283171, by rfl⟩ : syracuseStep 6843581 = 2566343) B2566343
theorem B4562387 : Blo 2027435 4562387 := bstep (se 1 (by rfl) ⟨3421790, by rfl⟩ : syracuseStep 4562387 = 6843581) B6843581
theorem B3041591 : Blo 2027435 3041591 := bstep (se 1 (by rfl) ⟨2281193, by rfl⟩ : syracuseStep 3041591 = 4562387) B4562387
theorem B2027727 : Blo 2027435 2027727 := bstep (se 1 (by rfl) ⟨1520795, by rfl⟩ : syracuseStep 2027727 = 3041591) B3041591
theorem B3041597 : Blo 2027435 3041597 := bbase (se 3 (by rfl) ⟨570299, by rfl⟩ : syracuseStep 3041597 = 1140599) (by norm_num)
theorem B2027731 : Blo 2027435 2027731 := bstep (se 1 (by rfl) ⟨1520798, by rfl⟩ : syracuseStep 2027731 = 3041597) B3041597
theorem B4562405 : Blo 2027435 4562405 := bbase (se 4 (by rfl) ⟨427725, by rfl⟩ : syracuseStep 4562405 = 855451) (by norm_num)
theorem B3041603 : Blo 2027435 3041603 := bstep (se 1 (by rfl) ⟨2281202, by rfl⟩ : syracuseStep 3041603 = 4562405) B4562405
theorem B2027735 : Blo 2027435 2027735 := bstep (se 1 (by rfl) ⟨1520801, by rfl⟩ : syracuseStep 2027735 = 3041603) B3041603
theorem B5132717 : Blo 2027435 5132717 := bbase (se 3 (by rfl) ⟨962384, by rfl⟩ : syracuseStep 5132717 = 1924769) (by norm_num)
theorem B3421811 : Blo 2027435 3421811 := bstep (se 1 (by rfl) ⟨2566358, by rfl⟩ : syracuseStep 3421811 = 5132717) B5132717
theorem B2281207 : Blo 2027435 2281207 := bstep (se 1 (by rfl) ⟨1710905, by rfl⟩ : syracuseStep 2281207 = 3421811) B3421811
theorem B3041609 : Blo 2027435 3041609 := bstep (se 2 (by rfl) ⟨1140603, by rfl⟩ : syracuseStep 3041609 = 2281207) B2281207
theorem B2027739 : Blo 2027435 2027739 := bstep (se 1 (by rfl) ⟨1520804, by rfl⟩ : syracuseStep 2027739 = 3041609) B3041609
theorem B2436041 : Blo 2027435 2436041 := bbase (se 2 (by rfl) ⟨913515, by rfl⟩ : syracuseStep 2436041 = 1827031) (by norm_num)
theorem B6496109 : Blo 2027435 6496109 := bstep (se 3 (by rfl) ⟨1218020, by rfl⟩ : syracuseStep 6496109 = 2436041) B2436041
theorem B4330739 : Blo 2027435 4330739 := bstep (se 1 (by rfl) ⟨3248054, by rfl⟩ : syracuseStep 4330739 = 6496109) B6496109
theorem B2887159 : Blo 2027435 2887159 := bstep (se 1 (by rfl) ⟨2165369, by rfl⟩ : syracuseStep 2887159 = 4330739) B4330739
theorem B3849545 : Blo 2027435 3849545 := bstep (se 2 (by rfl) ⟨1443579, by rfl⟩ : syracuseStep 3849545 = 2887159) B2887159
theorem B10265453 : Blo 2027435 10265453 := bstep (se 3 (by rfl) ⟨1924772, by rfl⟩ : syracuseStep 10265453 = 3849545) B3849545
theorem B6843635 : Blo 2027435 6843635 := bstep (se 1 (by rfl) ⟨5132726, by rfl⟩ : syracuseStep 6843635 = 10265453) B10265453
theorem B4562423 : Blo 2027435 4562423 := bstep (se 1 (by rfl) ⟨3421817, by rfl⟩ : syracuseStep 4562423 = 6843635) B6843635
theorem B3041615 : Blo 2027435 3041615 := bstep (se 1 (by rfl) ⟨2281211, by rfl⟩ : syracuseStep 3041615 = 4562423) B4562423
theorem B2027743 : Blo 2027435 2027743 := bstep (se 1 (by rfl) ⟨1520807, by rfl⟩ : syracuseStep 2027743 = 3041615) B3041615
theorem B3041621 : Blo 2027435 3041621 := bbase (se 10 (by rfl) ⟨4455, by rfl⟩ : syracuseStep 3041621 = 8911) (by norm_num)
theorem B2027747 : Blo 2027435 2027747 := bstep (se 1 (by rfl) ⟨1520810, by rfl⟩ : syracuseStep 2027747 = 3041621) B3041621
theorem B5774341 : Blo 2027435 5774341 := bbase (se 4 (by rfl) ⟨541344, by rfl⟩ : syracuseStep 5774341 = 1082689) (by norm_num)
theorem B7699121 : Blo 2027435 7699121 := bstep (se 2 (by rfl) ⟨2887170, by rfl⟩ : syracuseStep 7699121 = 5774341) B5774341
theorem B5132747 : Blo 2027435 5132747 := bstep (se 1 (by rfl) ⟨3849560, by rfl⟩ : syracuseStep 5132747 = 7699121) B7699121
theorem B3421831 : Blo 2027435 3421831 := bstep (se 1 (by rfl) ⟨2566373, by rfl⟩ : syracuseStep 3421831 = 5132747) B5132747
theorem B4562441 : Blo 2027435 4562441 := bstep (se 2 (by rfl) ⟨1710915, by rfl⟩ : syracuseStep 4562441 = 3421831) B3421831
theorem B3041627 : Blo 2027435 3041627 := bstep (se 1 (by rfl) ⟨2281220, by rfl⟩ : syracuseStep 3041627 = 4562441) B4562441
theorem B2027751 : Blo 2027435 2027751 := bstep (se 1 (by rfl) ⟨1520813, by rfl⟩ : syracuseStep 2027751 = 3041627) B3041627
theorem B2281225 : Blo 2027435 2281225 := bbase (se 2 (by rfl) ⟨855459, by rfl⟩ : syracuseStep 2281225 = 1710919) (by norm_num)
theorem B3041633 : Blo 2027435 3041633 := bstep (se 2 (by rfl) ⟨1140612, by rfl⟩ : syracuseStep 3041633 = 2281225) B2281225
theorem B2027755 : Blo 2027435 2027755 := bstep (se 1 (by rfl) ⟨1520816, by rfl⟩ : syracuseStep 2027755 = 3041633) B3041633
theorem B2926573 : Blo 2027435 2926573 := bbase (se 3 (by rfl) ⟨548732, by rfl⟩ : syracuseStep 2926573 = 1097465) (by norm_num)
theorem B15608389 : Blo 2027435 15608389 := bstep (se 4 (by rfl) ⟨1463286, by rfl⟩ : syracuseStep 15608389 = 2926573) B2926573
theorem B20811185 : Blo 2027435 20811185 := bstep (se 2 (by rfl) ⟨7804194, by rfl⟩ : syracuseStep 20811185 = 15608389) B15608389
theorem B13874123 : Blo 2027435 13874123 := bstep (se 1 (by rfl) ⟨10405592, by rfl⟩ : syracuseStep 13874123 = 20811185) B20811185
theorem B36997661 : Blo 2027435 36997661 := bstep (se 3 (by rfl) ⟨6937061, by rfl⟩ : syracuseStep 36997661 = 13874123) B13874123
theorem B24665107 : Blo 2027435 24665107 := bstep (se 1 (by rfl) ⟨18498830, by rfl⟩ : syracuseStep 24665107 = 36997661) B36997661
theorem B32886809 : Blo 2027435 32886809 := bstep (se 2 (by rfl) ⟨12332553, by rfl⟩ : syracuseStep 32886809 = 24665107) B24665107
theorem B21924539 : Blo 2027435 21924539 := bstep (se 1 (by rfl) ⟨16443404, by rfl⟩ : syracuseStep 21924539 = 32886809) B32886809
theorem B14616359 : Blo 2027435 14616359 := bstep (se 1 (by rfl) ⟨10962269, by rfl⟩ : syracuseStep 14616359 = 21924539) B21924539
theorem B9744239 : Blo 2027435 9744239 := bstep (se 1 (by rfl) ⟨7308179, by rfl⟩ : syracuseStep 9744239 = 14616359) B14616359
theorem B25984637 : Blo 2027435 25984637 := bstep (se 3 (by rfl) ⟨4872119, by rfl⟩ : syracuseStep 25984637 = 9744239) B9744239
theorem B17323091 : Blo 2027435 17323091 := bstep (se 1 (by rfl) ⟨12992318, by rfl⟩ : syracuseStep 17323091 = 25984637) B25984637
theorem B11548727 : Blo 2027435 11548727 := bstep (se 1 (by rfl) ⟨8661545, by rfl⟩ : syracuseStep 11548727 = 17323091) B17323091
theorem B7699151 : Blo 2027435 7699151 := bstep (se 1 (by rfl) ⟨5774363, by rfl⟩ : syracuseStep 7699151 = 11548727) B11548727
theorem B5132767 : Blo 2027435 5132767 := bstep (se 1 (by rfl) ⟨3849575, by rfl⟩ : syracuseStep 5132767 = 7699151) B7699151
theorem B6843689 : Blo 2027435 6843689 := bstep (se 2 (by rfl) ⟨2566383, by rfl⟩ : syracuseStep 6843689 = 5132767) B5132767
theorem B4562459 : Blo 2027435 4562459 := bstep (se 1 (by rfl) ⟨3421844, by rfl⟩ : syracuseStep 4562459 = 6843689) B6843689
theorem B3041639 : Blo 2027435 3041639 := bstep (se 1 (by rfl) ⟨2281229, by rfl⟩ : syracuseStep 3041639 = 4562459) B4562459
theorem B2027759 : Blo 2027435 2027759 := bstep (se 1 (by rfl) ⟨1520819, by rfl⟩ : syracuseStep 2027759 = 3041639) B3041639
theorem B3041645 : Blo 2027435 3041645 := bbase (se 3 (by rfl) ⟨570308, by rfl⟩ : syracuseStep 3041645 = 1140617) (by norm_num)
theorem B2027763 : Blo 2027435 2027763 := bstep (se 1 (by rfl) ⟨1520822, by rfl⟩ : syracuseStep 2027763 = 3041645) B3041645
theorem B4562477 : Blo 2027435 4562477 := bbase (se 3 (by rfl) ⟨855464, by rfl⟩ : syracuseStep 4562477 = 1710929) (by norm_num)
theorem B3041651 : Blo 2027435 3041651 := bstep (se 1 (by rfl) ⟨2281238, by rfl⟩ : syracuseStep 3041651 = 4562477) B4562477
theorem B2027767 : Blo 2027435 2027767 := bstep (se 1 (by rfl) ⟨1520825, by rfl⟩ : syracuseStep 2027767 = 3041651) B3041651
theorem B5202829 : Blo 2027435 5202829 := bbase (se 3 (by rfl) ⟨975530, by rfl⟩ : syracuseStep 5202829 = 1951061) (by norm_num)
theorem B6937105 : Blo 2027435 6937105 := bstep (se 2 (by rfl) ⟨2601414, by rfl⟩ : syracuseStep 6937105 = 5202829) B5202829
theorem B9249473 : Blo 2027435 9249473 := bstep (se 2 (by rfl) ⟨3468552, by rfl⟩ : syracuseStep 9249473 = 6937105) B6937105
theorem B6166315 : Blo 2027435 6166315 := bstep (se 1 (by rfl) ⟨4624736, by rfl⟩ : syracuseStep 6166315 = 9249473) B9249473
theorem B8221753 : Blo 2027435 8221753 := bstep (se 2 (by rfl) ⟨3083157, by rfl⟩ : syracuseStep 8221753 = 6166315) B6166315
theorem B43849349 : Blo 2027435 43849349 := bstep (se 4 (by rfl) ⟨4110876, by rfl⟩ : syracuseStep 43849349 = 8221753) B8221753
theorem B29232899 : Blo 2027435 29232899 := bstep (se 1 (by rfl) ⟨21924674, by rfl⟩ : syracuseStep 29232899 = 43849349) B43849349
theorem B19488599 : Blo 2027435 19488599 := bstep (se 1 (by rfl) ⟨14616449, by rfl⟩ : syracuseStep 19488599 = 29232899) B29232899
theorem B12992399 : Blo 2027435 12992399 := bstep (se 1 (by rfl) ⟨9744299, by rfl⟩ : syracuseStep 12992399 = 19488599) B19488599
theorem B8661599 : Blo 2027435 8661599 := bstep (se 1 (by rfl) ⟨6496199, by rfl⟩ : syracuseStep 8661599 = 12992399) B12992399
theorem B5774399 : Blo 2027435 5774399 := bstep (se 1 (by rfl) ⟨4330799, by rfl⟩ : syracuseStep 5774399 = 8661599) B8661599
theorem B3849599 : Blo 2027435 3849599 := bstep (se 1 (by rfl) ⟨2887199, by rfl⟩ : syracuseStep 3849599 = 5774399) B5774399
theorem B2566399 : Blo 2027435 2566399 := bstep (se 1 (by rfl) ⟨1924799, by rfl⟩ : syracuseStep 2566399 = 3849599) B3849599
theorem B3421865 : Blo 2027435 3421865 := bstep (se 2 (by rfl) ⟨1283199, by rfl⟩ : syracuseStep 3421865 = 2566399) B2566399
theorem B2281243 : Blo 2027435 2281243 := bstep (se 1 (by rfl) ⟨1710932, by rfl⟩ : syracuseStep 2281243 = 3421865) B3421865
theorem B3041657 : Blo 2027435 3041657 := bstep (se 2 (by rfl) ⟨1140621, by rfl⟩ : syracuseStep 3041657 = 2281243) B2281243
theorem B2027771 : Blo 2027435 2027771 := bstep (se 1 (by rfl) ⟨1520828, by rfl⟩ : syracuseStep 2027771 = 3041657) B3041657
theorem B11706389 : Blo 2027435 11706389 := bbase (se 6 (by rfl) ⟨274368, by rfl⟩ : syracuseStep 11706389 = 548737) (by norm_num)
theorem B7804259 : Blo 2027435 7804259 := bstep (se 1 (by rfl) ⟨5853194, by rfl⟩ : syracuseStep 7804259 = 11706389) B11706389
theorem B5202839 : Blo 2027435 5202839 := bstep (se 1 (by rfl) ⟨3902129, by rfl⟩ : syracuseStep 5202839 = 7804259) B7804259
theorem B13874237 : Blo 2027435 13874237 := bstep (se 3 (by rfl) ⟨2601419, by rfl⟩ : syracuseStep 13874237 = 5202839) B5202839
theorem B9249491 : Blo 2027435 9249491 := bstep (se 1 (by rfl) ⟨6937118, by rfl⟩ : syracuseStep 9249491 = 13874237) B13874237
theorem B6166327 : Blo 2027435 6166327 := bstep (se 1 (by rfl) ⟨4624745, by rfl⟩ : syracuseStep 6166327 = 9249491) B9249491
theorem B8221769 : Blo 2027435 8221769 := bstep (se 2 (by rfl) ⟨3083163, by rfl⟩ : syracuseStep 8221769 = 6166327) B6166327
theorem B5481179 : Blo 2027435 5481179 := bstep (se 1 (by rfl) ⟨4110884, by rfl⟩ : syracuseStep 5481179 = 8221769) B8221769
theorem B3654119 : Blo 2027435 3654119 := bstep (se 1 (by rfl) ⟨2740589, by rfl⟩ : syracuseStep 3654119 = 5481179) B5481179
theorem B2436079 : Blo 2027435 2436079 := bstep (se 1 (by rfl) ⟨1827059, by rfl⟩ : syracuseStep 2436079 = 3654119) B3654119
theorem B3248105 : Blo 2027435 3248105 := bstep (se 2 (by rfl) ⟨1218039, by rfl⟩ : syracuseStep 3248105 = 2436079) B2436079
theorem B34646453 : Blo 2027435 34646453 := bstep (se 5 (by rfl) ⟨1624052, by rfl⟩ : syracuseStep 34646453 = 3248105) B3248105
theorem B23097635 : Blo 2027435 23097635 := bstep (se 1 (by rfl) ⟨17323226, by rfl⟩ : syracuseStep 23097635 = 34646453) B34646453
theorem B15398423 : Blo 2027435 15398423 := bstep (se 1 (by rfl) ⟨11548817, by rfl⟩ : syracuseStep 15398423 = 23097635) B23097635
theorem B10265615 : Blo 2027435 10265615 := bstep (se 1 (by rfl) ⟨7699211, by rfl⟩ : syracuseStep 10265615 = 15398423) B15398423
theorem B6843743 : Blo 2027435 6843743 := bstep (se 1 (by rfl) ⟨5132807, by rfl⟩ : syracuseStep 6843743 = 10265615) B10265615
theorem B4562495 : Blo 2027435 4562495 := bstep (se 1 (by rfl) ⟨3421871, by rfl⟩ : syracuseStep 4562495 = 6843743) B6843743
theorem B3041663 : Blo 2027435 3041663 := bstep (se 1 (by rfl) ⟨2281247, by rfl⟩ : syracuseStep 3041663 = 4562495) B4562495
theorem B2027775 : Blo 2027435 2027775 := bstep (se 1 (by rfl) ⟨1520831, by rfl⟩ : syracuseStep 2027775 = 3041663) B3041663
theorem B3041669 : Blo 2027435 3041669 := bbase (se 4 (by rfl) ⟨285156, by rfl⟩ : syracuseStep 3041669 = 570313) (by norm_num)
theorem B2027779 : Blo 2027435 2027779 := bstep (se 1 (by rfl) ⟨1520834, by rfl⟩ : syracuseStep 2027779 = 3041669) B3041669
theorem B3421885 : Blo 2027435 3421885 := bbase (se 3 (by rfl) ⟨641603, by rfl⟩ : syracuseStep 3421885 = 1283207) (by norm_num)
theorem B4562513 : Blo 2027435 4562513 := bstep (se 2 (by rfl) ⟨1710942, by rfl⟩ : syracuseStep 4562513 = 3421885) B3421885
theorem B3041675 : Blo 2027435 3041675 := bstep (se 1 (by rfl) ⟨2281256, by rfl⟩ : syracuseStep 3041675 = 4562513) B4562513
theorem B2027783 : Blo 2027435 2027783 := bstep (se 1 (by rfl) ⟨1520837, by rfl⟩ : syracuseStep 2027783 = 3041675) B3041675
theorem B2281261 : Blo 2027435 2281261 := bbase (se 3 (by rfl) ⟨427736, by rfl⟩ : syracuseStep 2281261 = 855473) (by norm_num)
theorem B3041681 : Blo 2027435 3041681 := bstep (se 2 (by rfl) ⟨1140630, by rfl⟩ : syracuseStep 3041681 = 2281261) B2281261
theorem B2027787 : Blo 2027435 2027787 := bstep (se 1 (by rfl) ⟨1520840, by rfl⟩ : syracuseStep 2027787 = 3041681) B3041681
theorem B6843797 : Blo 2027435 6843797 := bbase (se 6 (by rfl) ⟨160401, by rfl⟩ : syracuseStep 6843797 = 320803) (by norm_num)
theorem B4562531 : Blo 2027435 4562531 := bstep (se 1 (by rfl) ⟨3421898, by rfl⟩ : syracuseStep 4562531 = 6843797) B6843797
theorem B3041687 : Blo 2027435 3041687 := bstep (se 1 (by rfl) ⟨2281265, by rfl⟩ : syracuseStep 3041687 = 4562531) B4562531
theorem B2027791 : Blo 2027435 2027791 := bstep (se 1 (by rfl) ⟨1520843, by rfl⟩ : syracuseStep 2027791 = 3041687) B3041687
theorem B3041693 : Blo 2027435 3041693 := bbase (se 3 (by rfl) ⟨570317, by rfl⟩ : syracuseStep 3041693 = 1140635) (by norm_num)
theorem B2027795 : Blo 2027435 2027795 := bstep (se 1 (by rfl) ⟨1520846, by rfl⟩ : syracuseStep 2027795 = 3041693) B3041693
theorem B4562549 : Blo 2027435 4562549 := bbase (se 5 (by rfl) ⟨213869, by rfl⟩ : syracuseStep 4562549 = 427739) (by norm_num)
theorem B3041699 : Blo 2027435 3041699 := bstep (se 1 (by rfl) ⟨2281274, by rfl⟩ : syracuseStep 3041699 = 4562549) B4562549
theorem B2027799 : Blo 2027435 2027799 := bstep (se 1 (by rfl) ⟨1520849, by rfl⟩ : syracuseStep 2027799 = 3041699) B3041699
theorem B2436113 : Blo 2027435 2436113 := bbase (se 2 (by rfl) ⟨913542, by rfl⟩ : syracuseStep 2436113 = 1827085) (by norm_num)
theorem B6496301 : Blo 2027435 6496301 := bstep (se 3 (by rfl) ⟨1218056, by rfl⟩ : syracuseStep 6496301 = 2436113) B2436113
theorem B17323469 : Blo 2027435 17323469 := bstep (se 3 (by rfl) ⟨3248150, by rfl⟩ : syracuseStep 17323469 = 6496301) B6496301
theorem B11548979 : Blo 2027435 11548979 := bstep (se 1 (by rfl) ⟨8661734, by rfl⟩ : syracuseStep 11548979 = 17323469) B17323469
theorem B7699319 : Blo 2027435 7699319 := bstep (se 1 (by rfl) ⟨5774489, by rfl⟩ : syracuseStep 7699319 = 11548979) B11548979
theorem B5132879 : Blo 2027435 5132879 := bstep (se 1 (by rfl) ⟨3849659, by rfl⟩ : syracuseStep 5132879 = 7699319) B7699319
theorem B3421919 : Blo 2027435 3421919 := bstep (se 1 (by rfl) ⟨2566439, by rfl⟩ : syracuseStep 3421919 = 5132879) B5132879
theorem B2281279 : Blo 2027435 2281279 := bstep (se 1 (by rfl) ⟨1710959, by rfl⟩ : syracuseStep 2281279 = 3421919) B3421919
theorem B3041705 : Blo 2027435 3041705 := bstep (se 2 (by rfl) ⟨1140639, by rfl⟩ : syracuseStep 3041705 = 2281279) B2281279
theorem B2027803 : Blo 2027435 2027803 := bstep (se 1 (by rfl) ⟨1520852, by rfl⟩ : syracuseStep 2027803 = 3041705) B3041705
theorem B7699333 : Blo 2027435 7699333 := bbase (se 4 (by rfl) ⟨721812, by rfl⟩ : syracuseStep 7699333 = 1443625) (by norm_num)
theorem B10265777 : Blo 2027435 10265777 := bstep (se 2 (by rfl) ⟨3849666, by rfl⟩ : syracuseStep 10265777 = 7699333) B7699333
theorem B6843851 : Blo 2027435 6843851 := bstep (se 1 (by rfl) ⟨5132888, by rfl⟩ : syracuseStep 6843851 = 10265777) B10265777
theorem B4562567 : Blo 2027435 4562567 := bstep (se 1 (by rfl) ⟨3421925, by rfl⟩ : syracuseStep 4562567 = 6843851) B6843851
theorem B3041711 : Blo 2027435 3041711 := bstep (se 1 (by rfl) ⟨2281283, by rfl⟩ : syracuseStep 3041711 = 4562567) B4562567
theorem B2027807 : Blo 2027435 2027807 := bstep (se 1 (by rfl) ⟨1520855, by rfl⟩ : syracuseStep 2027807 = 3041711) B3041711
theorem B3041717 : Blo 2027435 3041717 := bbase (se 5 (by rfl) ⟨142580, by rfl⟩ : syracuseStep 3041717 = 285161) (by norm_num)
theorem B2027811 : Blo 2027435 2027811 := bstep (se 1 (by rfl) ⟨1520858, by rfl⟩ : syracuseStep 2027811 = 3041717) B3041717
theorem B5132909 : Blo 2027435 5132909 := bbase (se 3 (by rfl) ⟨962420, by rfl⟩ : syracuseStep 5132909 = 1924841) (by norm_num)
theorem B3421939 : Blo 2027435 3421939 := bstep (se 1 (by rfl) ⟨2566454, by rfl⟩ : syracuseStep 3421939 = 5132909) B5132909
theorem B4562585 : Blo 2027435 4562585 := bstep (se 2 (by rfl) ⟨1710969, by rfl⟩ : syracuseStep 4562585 = 3421939) B3421939
theorem B3041723 : Blo 2027435 3041723 := bstep (se 1 (by rfl) ⟨2281292, by rfl⟩ : syracuseStep 3041723 = 4562585) B4562585
theorem B2027815 : Blo 2027435 2027815 := bstep (se 1 (by rfl) ⟨1520861, by rfl⟩ : syracuseStep 2027815 = 3041723) B3041723
theorem B2281297 : Blo 2027435 2281297 := bbase (se 2 (by rfl) ⟨855486, by rfl⟩ : syracuseStep 2281297 = 1710973) (by norm_num)
theorem B3041729 : Blo 2027435 3041729 := bstep (se 2 (by rfl) ⟨1140648, by rfl⟩ : syracuseStep 3041729 = 2281297) B2281297
theorem B2027819 : Blo 2027435 2027819 := bstep (se 1 (by rfl) ⟨1520864, by rfl⟩ : syracuseStep 2027819 = 3041729) B3041729
theorem B6937285 : Blo 2027435 6937285 := bbase (se 4 (by rfl) ⟨650370, by rfl⟩ : syracuseStep 6937285 = 1300741) (by norm_num)
theorem B9249713 : Blo 2027435 9249713 := bstep (se 2 (by rfl) ⟨3468642, by rfl⟩ : syracuseStep 9249713 = 6937285) B6937285
theorem B6166475 : Blo 2027435 6166475 := bstep (se 1 (by rfl) ⟨4624856, by rfl⟩ : syracuseStep 6166475 = 9249713) B9249713
theorem B4110983 : Blo 2027435 4110983 := bstep (se 1 (by rfl) ⟨3083237, by rfl⟩ : syracuseStep 4110983 = 6166475) B6166475
theorem B2740655 : Blo 2027435 2740655 := bstep (se 1 (by rfl) ⟨2055491, by rfl⟩ : syracuseStep 2740655 = 4110983) B4110983
theorem B7308413 : Blo 2027435 7308413 := bstep (se 3 (by rfl) ⟨1370327, by rfl⟩ : syracuseStep 7308413 = 2740655) B2740655
theorem B4872275 : Blo 2027435 4872275 := bstep (se 1 (by rfl) ⟨3654206, by rfl⟩ : syracuseStep 4872275 = 7308413) B7308413
theorem B3248183 : Blo 2027435 3248183 := bstep (se 1 (by rfl) ⟨2436137, by rfl⟩ : syracuseStep 3248183 = 4872275) B4872275
theorem B2165455 : Blo 2027435 2165455 := bstep (se 1 (by rfl) ⟨1624091, by rfl⟩ : syracuseStep 2165455 = 3248183) B3248183
theorem B2887273 : Blo 2027435 2887273 := bstep (se 2 (by rfl) ⟨1082727, by rfl⟩ : syracuseStep 2887273 = 2165455) B2165455
theorem B3849697 : Blo 2027435 3849697 := bstep (se 2 (by rfl) ⟨1443636, by rfl⟩ : syracuseStep 3849697 = 2887273) B2887273
theorem B5132929 : Blo 2027435 5132929 := bstep (se 2 (by rfl) ⟨1924848, by rfl⟩ : syracuseStep 5132929 = 3849697) B3849697
theorem B6843905 : Blo 2027435 6843905 := bstep (se 2 (by rfl) ⟨2566464, by rfl⟩ : syracuseStep 6843905 = 5132929) B5132929
theorem B4562603 : Blo 2027435 4562603 := bstep (se 1 (by rfl) ⟨3421952, by rfl⟩ : syracuseStep 4562603 = 6843905) B6843905
theorem B3041735 : Blo 2027435 3041735 := bstep (se 1 (by rfl) ⟨2281301, by rfl⟩ : syracuseStep 3041735 = 4562603) B4562603
theorem B2027823 : Blo 2027435 2027823 := bstep (se 1 (by rfl) ⟨1520867, by rfl⟩ : syracuseStep 2027823 = 3041735) B3041735
theorem B3041741 : Blo 2027435 3041741 := bbase (se 3 (by rfl) ⟨570326, by rfl⟩ : syracuseStep 3041741 = 1140653) (by norm_num)
theorem B2027827 : Blo 2027435 2027827 := bstep (se 1 (by rfl) ⟨1520870, by rfl⟩ : syracuseStep 2027827 = 3041741) B3041741
theorem B4562621 : Blo 2027435 4562621 := bbase (se 3 (by rfl) ⟨855491, by rfl⟩ : syracuseStep 4562621 = 1710983) (by norm_num)
theorem B3041747 : Blo 2027435 3041747 := bstep (se 1 (by rfl) ⟨2281310, by rfl⟩ : syracuseStep 3041747 = 4562621) B4562621
theorem B2027831 : Blo 2027435 2027831 := bstep (se 1 (by rfl) ⟨1520873, by rfl⟩ : syracuseStep 2027831 = 3041747) B3041747
theorem B3421973 : Blo 2027435 3421973 := bbase (se 6 (by rfl) ⟨80202, by rfl⟩ : syracuseStep 3421973 = 160405) (by norm_num)
theorem B2281315 : Blo 2027435 2281315 := bstep (se 1 (by rfl) ⟨1710986, by rfl⟩ : syracuseStep 2281315 = 3421973) B3421973
theorem B3041753 : Blo 2027435 3041753 := bstep (se 2 (by rfl) ⟨1140657, by rfl⟩ : syracuseStep 3041753 = 2281315) B2281315
theorem B2027835 : Blo 2027435 2027835 := bstep (se 1 (by rfl) ⟨1520876, by rfl⟩ : syracuseStep 2027835 = 3041753) B3041753
theorem B9877573 : Blo 2027435 9877573 := bbase (se 4 (by rfl) ⟨926022, by rfl⟩ : syracuseStep 9877573 = 1852045) (by norm_num)
theorem B13170097 : Blo 2027435 13170097 := bstep (se 2 (by rfl) ⟨4938786, by rfl⟩ : syracuseStep 13170097 = 9877573) B9877573
theorem B70240517 : Blo 2027435 70240517 := bstep (se 4 (by rfl) ⟨6585048, by rfl⟩ : syracuseStep 70240517 = 13170097) B13170097
theorem B46827011 : Blo 2027435 46827011 := bstep (se 1 (by rfl) ⟨35120258, by rfl⟩ : syracuseStep 46827011 = 70240517) B70240517
theorem B124872029 : Blo 2027435 124872029 := bstep (se 3 (by rfl) ⟨23413505, by rfl⟩ : syracuseStep 124872029 = 46827011) B46827011
theorem B83248019 : Blo 2027435 83248019 := bstep (se 1 (by rfl) ⟨62436014, by rfl⟩ : syracuseStep 83248019 = 124872029) B124872029
theorem B55498679 : Blo 2027435 55498679 := bstep (se 1 (by rfl) ⟨41624009, by rfl⟩ : syracuseStep 55498679 = 83248019) B83248019
theorem B36999119 : Blo 2027435 36999119 := bstep (se 1 (by rfl) ⟨27749339, by rfl⟩ : syracuseStep 36999119 = 55498679) B55498679
theorem B98664317 : Blo 2027435 98664317 := bstep (se 3 (by rfl) ⟨18499559, by rfl⟩ : syracuseStep 98664317 = 36999119) B36999119
theorem B65776211 : Blo 2027435 65776211 := bstep (se 1 (by rfl) ⟨49332158, by rfl⟩ : syracuseStep 65776211 = 98664317) B98664317
theorem B43850807 : Blo 2027435 43850807 := bstep (se 1 (by rfl) ⟨32888105, by rfl⟩ : syracuseStep 43850807 = 65776211) B65776211
theorem B29233871 : Blo 2027435 29233871 := bstep (se 1 (by rfl) ⟨21925403, by rfl⟩ : syracuseStep 29233871 = 43850807) B43850807
theorem B19489247 : Blo 2027435 19489247 := bstep (se 1 (by rfl) ⟨14616935, by rfl⟩ : syracuseStep 19489247 = 29233871) B29233871
theorem B12992831 : Blo 2027435 12992831 := bstep (se 1 (by rfl) ⟨9744623, by rfl⟩ : syracuseStep 12992831 = 19489247) B19489247
theorem B8661887 : Blo 2027435 8661887 := bstep (se 1 (by rfl) ⟨6496415, by rfl⟩ : syracuseStep 8661887 = 12992831) B12992831
theorem B5774591 : Blo 2027435 5774591 := bstep (se 1 (by rfl) ⟨4330943, by rfl⟩ : syracuseStep 5774591 = 8661887) B8661887
theorem B15398909 : Blo 2027435 15398909 := bstep (se 3 (by rfl) ⟨2887295, by rfl⟩ : syracuseStep 15398909 = 5774591) B5774591
theorem B10265939 : Blo 2027435 10265939 := bstep (se 1 (by rfl) ⟨7699454, by rfl⟩ : syracuseStep 10265939 = 15398909) B15398909
theorem B6843959 : Blo 2027435 6843959 := bstep (se 1 (by rfl) ⟨5132969, by rfl⟩ : syracuseStep 6843959 = 10265939) B10265939
theorem B4562639 : Blo 2027435 4562639 := bstep (se 1 (by rfl) ⟨3421979, by rfl⟩ : syracuseStep 4562639 = 6843959) B6843959
theorem B3041759 : Blo 2027435 3041759 := bstep (se 1 (by rfl) ⟨2281319, by rfl⟩ : syracuseStep 3041759 = 4562639) B4562639
theorem B2027839 : Blo 2027435 2027839 := bstep (se 1 (by rfl) ⟨1520879, by rfl⟩ : syracuseStep 2027839 = 3041759) B3041759
theorem B3041765 : Blo 2027435 3041765 := bbase (se 4 (by rfl) ⟨285165, by rfl⟩ : syracuseStep 3041765 = 570331) (by norm_num)
theorem B2027843 : Blo 2027435 2027843 := bstep (se 1 (by rfl) ⟨1520882, by rfl⟩ : syracuseStep 2027843 = 3041765) B3041765
theorem B12992885 : Blo 2027435 12992885 := bbase (se 5 (by rfl) ⟨609041, by rfl⟩ : syracuseStep 12992885 = 1218083) (by norm_num)
theorem B8661923 : Blo 2027435 8661923 := bstep (se 1 (by rfl) ⟨6496442, by rfl⟩ : syracuseStep 8661923 = 12992885) B12992885
theorem B5774615 : Blo 2027435 5774615 := bstep (se 1 (by rfl) ⟨4330961, by rfl⟩ : syracuseStep 5774615 = 8661923) B8661923
theorem B3849743 : Blo 2027435 3849743 := bstep (se 1 (by rfl) ⟨2887307, by rfl⟩ : syracuseStep 3849743 = 5774615) B5774615
theorem B2566495 : Blo 2027435 2566495 := bstep (se 1 (by rfl) ⟨1924871, by rfl⟩ : syracuseStep 2566495 = 3849743) B3849743
theorem B3421993 : Blo 2027435 3421993 := bstep (se 2 (by rfl) ⟨1283247, by rfl⟩ : syracuseStep 3421993 = 2566495) B2566495
theorem B4562657 : Blo 2027435 4562657 := bstep (se 2 (by rfl) ⟨1710996, by rfl⟩ : syracuseStep 4562657 = 3421993) B3421993
theorem B3041771 : Blo 2027435 3041771 := bstep (se 1 (by rfl) ⟨2281328, by rfl⟩ : syracuseStep 3041771 = 4562657) B4562657
theorem B2027847 : Blo 2027435 2027847 := bstep (se 1 (by rfl) ⟨1520885, by rfl⟩ : syracuseStep 2027847 = 3041771) B3041771
theorem B2281333 : Blo 2027435 2281333 := bbase (se 5 (by rfl) ⟨106937, by rfl⟩ : syracuseStep 2281333 = 213875) (by norm_num)
theorem B3041777 : Blo 2027435 3041777 := bstep (se 2 (by rfl) ⟨1140666, by rfl⟩ : syracuseStep 3041777 = 2281333) B2281333
theorem B2027851 : Blo 2027435 2027851 := bstep (se 1 (by rfl) ⟨1520888, by rfl⟩ : syracuseStep 2027851 = 3041777) B3041777
theorem B2566505 : Blo 2027435 2566505 := bbase (se 2 (by rfl) ⟨962439, by rfl⟩ : syracuseStep 2566505 = 1924879) (by norm_num)
theorem B6844013 : Blo 2027435 6844013 := bstep (se 3 (by rfl) ⟨1283252, by rfl⟩ : syracuseStep 6844013 = 2566505) B2566505
theorem B4562675 : Blo 2027435 4562675 := bstep (se 1 (by rfl) ⟨3422006, by rfl⟩ : syracuseStep 4562675 = 6844013) B6844013
theorem B3041783 : Blo 2027435 3041783 := bstep (se 1 (by rfl) ⟨2281337, by rfl⟩ : syracuseStep 3041783 = 4562675) B4562675
theorem B2027855 : Blo 2027435 2027855 := bstep (se 1 (by rfl) ⟨1520891, by rfl⟩ : syracuseStep 2027855 = 3041783) B3041783
theorem B3041789 : Blo 2027435 3041789 := bbase (se 3 (by rfl) ⟨570335, by rfl⟩ : syracuseStep 3041789 = 1140671) (by norm_num)
theorem B2027859 : Blo 2027435 2027859 := bstep (se 1 (by rfl) ⟨1520894, by rfl⟩ : syracuseStep 2027859 = 3041789) B3041789
theorem B4562693 : Blo 2027435 4562693 := bbase (se 4 (by rfl) ⟨427752, by rfl⟩ : syracuseStep 4562693 = 855505) (by norm_num)
theorem B3041795 : Blo 2027435 3041795 := bstep (se 1 (by rfl) ⟨2281346, by rfl⟩ : syracuseStep 3041795 = 4562693) B4562693
theorem B2027863 : Blo 2027435 2027863 := bstep (se 1 (by rfl) ⟨1520897, by rfl⟩ : syracuseStep 2027863 = 3041795) B3041795
theorem B3849781 : Blo 2027435 3849781 := bbase (se 5 (by rfl) ⟨180458, by rfl⟩ : syracuseStep 3849781 = 360917) (by norm_num)
theorem B5133041 : Blo 2027435 5133041 := bstep (se 2 (by rfl) ⟨1924890, by rfl⟩ : syracuseStep 5133041 = 3849781) B3849781
theorem B3422027 : Blo 2027435 3422027 := bstep (se 1 (by rfl) ⟨2566520, by rfl⟩ : syracuseStep 3422027 = 5133041) B5133041
theorem B2281351 : Blo 2027435 2281351 := bstep (se 1 (by rfl) ⟨1711013, by rfl⟩ : syracuseStep 2281351 = 3422027) B3422027
theorem B3041801 : Blo 2027435 3041801 := bstep (se 2 (by rfl) ⟨1140675, by rfl⟩ : syracuseStep 3041801 = 2281351) B2281351
theorem B2027867 : Blo 2027435 2027867 := bstep (se 1 (by rfl) ⟨1520900, by rfl⟩ : syracuseStep 2027867 = 3041801) B3041801
theorem B10266101 : Blo 2027435 10266101 := bbase (se 5 (by rfl) ⟨481223, by rfl⟩ : syracuseStep 10266101 = 962447) (by norm_num)
theorem B6844067 : Blo 2027435 6844067 := bstep (se 1 (by rfl) ⟨5133050, by rfl⟩ : syracuseStep 6844067 = 10266101) B10266101
theorem B4562711 : Blo 2027435 4562711 := bstep (se 1 (by rfl) ⟨3422033, by rfl⟩ : syracuseStep 4562711 = 6844067) B6844067
theorem B3041807 : Blo 2027435 3041807 := bstep (se 1 (by rfl) ⟨2281355, by rfl⟩ : syracuseStep 3041807 = 4562711) B4562711
theorem B2027871 : Blo 2027435 2027871 := bstep (se 1 (by rfl) ⟨1520903, by rfl⟩ : syracuseStep 2027871 = 3041807) B3041807
theorem B3041813 : Blo 2027435 3041813 := bbase (se 6 (by rfl) ⟨71292, by rfl⟩ : syracuseStep 3041813 = 142585) (by norm_num)
theorem B2027875 : Blo 2027435 2027875 := bstep (se 1 (by rfl) ⟨1520906, by rfl⟩ : syracuseStep 2027875 = 3041813) B3041813
theorem B17324117 : Blo 2027435 17324117 := bbase (se 8 (by rfl) ⟨101508, by rfl⟩ : syracuseStep 17324117 = 203017) (by norm_num)
theorem B11549411 : Blo 2027435 11549411 := bstep (se 1 (by rfl) ⟨8662058, by rfl⟩ : syracuseStep 11549411 = 17324117) B17324117
theorem B7699607 : Blo 2027435 7699607 := bstep (se 1 (by rfl) ⟨5774705, by rfl⟩ : syracuseStep 7699607 = 11549411) B11549411
theorem B5133071 : Blo 2027435 5133071 := bstep (se 1 (by rfl) ⟨3849803, by rfl⟩ : syracuseStep 5133071 = 7699607) B7699607
theorem B3422047 : Blo 2027435 3422047 := bstep (se 1 (by rfl) ⟨2566535, by rfl⟩ : syracuseStep 3422047 = 5133071) B5133071
theorem B4562729 : Blo 2027435 4562729 := bstep (se 2 (by rfl) ⟨1711023, by rfl⟩ : syracuseStep 4562729 = 3422047) B3422047
theorem B3041819 : Blo 2027435 3041819 := bstep (se 1 (by rfl) ⟨2281364, by rfl⟩ : syracuseStep 3041819 = 4562729) B4562729
theorem B2027879 : Blo 2027435 2027879 := bstep (se 1 (by rfl) ⟨1520909, by rfl⟩ : syracuseStep 2027879 = 3041819) B3041819
theorem B2281369 : Blo 2027435 2281369 := bbase (se 2 (by rfl) ⟨855513, by rfl⟩ : syracuseStep 2281369 = 1711027) (by norm_num)
theorem B3041825 : Blo 2027435 3041825 := bstep (se 2 (by rfl) ⟨1140684, by rfl⟩ : syracuseStep 3041825 = 2281369) B2281369
theorem B2027883 : Blo 2027435 2027883 := bstep (se 1 (by rfl) ⟨1520912, by rfl⟩ : syracuseStep 2027883 = 3041825) B3041825
theorem B7699637 : Blo 2027435 7699637 := bbase (se 5 (by rfl) ⟨360920, by rfl⟩ : syracuseStep 7699637 = 721841) (by norm_num)
theorem B5133091 : Blo 2027435 5133091 := bstep (se 1 (by rfl) ⟨3849818, by rfl⟩ : syracuseStep 5133091 = 7699637) B7699637
theorem B6844121 : Blo 2027435 6844121 := bstep (se 2 (by rfl) ⟨2566545, by rfl⟩ : syracuseStep 6844121 = 5133091) B5133091
theorem B4562747 : Blo 2027435 4562747 := bstep (se 1 (by rfl) ⟨3422060, by rfl⟩ : syracuseStep 4562747 = 6844121) B6844121
theorem B3041831 : Blo 2027435 3041831 := bstep (se 1 (by rfl) ⟨2281373, by rfl⟩ : syracuseStep 3041831 = 4562747) B4562747
theorem B2027887 : Blo 2027435 2027887 := bstep (se 1 (by rfl) ⟨1520915, by rfl⟩ : syracuseStep 2027887 = 3041831) B3041831
theorem B3041837 : Blo 2027435 3041837 := bbase (se 3 (by rfl) ⟨570344, by rfl⟩ : syracuseStep 3041837 = 1140689) (by norm_num)
theorem B2027891 : Blo 2027435 2027891 := bstep (se 1 (by rfl) ⟨1520918, by rfl⟩ : syracuseStep 2027891 = 3041837) B3041837
theorem B4562765 : Blo 2027435 4562765 := bbase (se 3 (by rfl) ⟨855518, by rfl⟩ : syracuseStep 4562765 = 1711037) (by norm_num)
theorem B3041843 : Blo 2027435 3041843 := bstep (se 1 (by rfl) ⟨2281382, by rfl⟩ : syracuseStep 3041843 = 4562765) B4562765
theorem B2027895 : Blo 2027435 2027895 := bstep (se 1 (by rfl) ⟨1520921, by rfl⟩ : syracuseStep 2027895 = 3041843) B3041843
theorem B2566561 : Blo 2027435 2566561 := bbase (se 2 (by rfl) ⟨962460, by rfl⟩ : syracuseStep 2566561 = 1924921) (by norm_num)
theorem B3422081 : Blo 2027435 3422081 := bstep (se 2 (by rfl) ⟨1283280, by rfl⟩ : syracuseStep 3422081 = 2566561) B2566561
theorem B2281387 : Blo 2027435 2281387 := bstep (se 1 (by rfl) ⟨1711040, by rfl⟩ : syracuseStep 2281387 = 3422081) B3422081
theorem B3041849 : Blo 2027435 3041849 := bstep (se 2 (by rfl) ⟨1140693, by rfl⟩ : syracuseStep 3041849 = 2281387) B2281387
theorem B2027899 : Blo 2027435 2027899 := bstep (se 1 (by rfl) ⟨1520924, by rfl⟩ : syracuseStep 2027899 = 3041849) B3041849
theorem B23099093 : Blo 2027435 23099093 := bbase (se 7 (by rfl) ⟨270692, by rfl⟩ : syracuseStep 23099093 = 541385) (by norm_num)
theorem B15399395 : Blo 2027435 15399395 := bstep (se 1 (by rfl) ⟨11549546, by rfl⟩ : syracuseStep 15399395 = 23099093) B23099093
theorem B10266263 : Blo 2027435 10266263 := bstep (se 1 (by rfl) ⟨7699697, by rfl⟩ : syracuseStep 10266263 = 15399395) B15399395
theorem B6844175 : Blo 2027435 6844175 := bstep (se 1 (by rfl) ⟨5133131, by rfl⟩ : syracuseStep 6844175 = 10266263) B10266263
theorem B4562783 : Blo 2027435 4562783 := bstep (se 1 (by rfl) ⟨3422087, by rfl⟩ : syracuseStep 4562783 = 6844175) B6844175
theorem B3041855 : Blo 2027435 3041855 := bstep (se 1 (by rfl) ⟨2281391, by rfl⟩ : syracuseStep 3041855 = 4562783) B4562783
theorem B2027903 : Blo 2027435 2027903 := bstep (se 1 (by rfl) ⟨1520927, by rfl⟩ : syracuseStep 2027903 = 3041855) B3041855
theorem B3041861 : Blo 2027435 3041861 := bbase (se 4 (by rfl) ⟨285174, by rfl⟩ : syracuseStep 3041861 = 570349) (by norm_num)
theorem B2027907 : Blo 2027435 2027907 := bstep (se 1 (by rfl) ⟨1520930, by rfl⟩ : syracuseStep 2027907 = 3041861) B3041861
theorem B3422101 : Blo 2027435 3422101 := bbase (se 6 (by rfl) ⟨80205, by rfl⟩ : syracuseStep 3422101 = 160411) (by norm_num)
theorem B4562801 : Blo 2027435 4562801 := bstep (se 2 (by rfl) ⟨1711050, by rfl⟩ : syracuseStep 4562801 = 3422101) B3422101
theorem B3041867 : Blo 2027435 3041867 := bstep (se 1 (by rfl) ⟨2281400, by rfl⟩ : syracuseStep 3041867 = 4562801) B4562801
theorem B2027911 : Blo 2027435 2027911 := bstep (se 1 (by rfl) ⟨1520933, by rfl⟩ : syracuseStep 2027911 = 3041867) B3041867
theorem B2281405 : Blo 2027435 2281405 := bbase (se 3 (by rfl) ⟨427763, by rfl⟩ : syracuseStep 2281405 = 855527) (by norm_num)
theorem B3041873 : Blo 2027435 3041873 := bstep (se 2 (by rfl) ⟨1140702, by rfl⟩ : syracuseStep 3041873 = 2281405) B2281405
theorem B2027915 : Blo 2027435 2027915 := bstep (se 1 (by rfl) ⟨1520936, by rfl⟩ : syracuseStep 2027915 = 3041873) B3041873
theorem B6844229 : Blo 2027435 6844229 := bbase (se 4 (by rfl) ⟨641646, by rfl⟩ : syracuseStep 6844229 = 1283293) (by norm_num)
theorem B4562819 : Blo 2027435 4562819 := bstep (se 1 (by rfl) ⟨3422114, by rfl⟩ : syracuseStep 4562819 = 6844229) B6844229
theorem B3041879 : Blo 2027435 3041879 := bstep (se 1 (by rfl) ⟨2281409, by rfl⟩ : syracuseStep 3041879 = 4562819) B4562819
theorem B2027919 : Blo 2027435 2027919 := bstep (se 1 (by rfl) ⟨1520939, by rfl⟩ : syracuseStep 2027919 = 3041879) B3041879
theorem B3041885 : Blo 2027435 3041885 := bbase (se 3 (by rfl) ⟨570353, by rfl⟩ : syracuseStep 3041885 = 1140707) (by norm_num)
theorem B2027923 : Blo 2027435 2027923 := bstep (se 1 (by rfl) ⟨1520942, by rfl⟩ : syracuseStep 2027923 = 3041885) B3041885
theorem B4562837 : Blo 2027435 4562837 := bbase (se 6 (by rfl) ⟨106941, by rfl⟩ : syracuseStep 4562837 = 213883) (by norm_num)
theorem B3041891 : Blo 2027435 3041891 := bstep (se 1 (by rfl) ⟨2281418, by rfl⟩ : syracuseStep 3041891 = 4562837) B4562837
theorem B2027927 : Blo 2027435 2027927 := bstep (se 1 (by rfl) ⟨1520945, by rfl⟩ : syracuseStep 2027927 = 3041891) B3041891
theorem B4331141 : Blo 2027435 4331141 := bbase (se 4 (by rfl) ⟨406044, by rfl⟩ : syracuseStep 4331141 = 812089) (by norm_num)
theorem B2887427 : Blo 2027435 2887427 := bstep (se 1 (by rfl) ⟨2165570, by rfl⟩ : syracuseStep 2887427 = 4331141) B4331141
theorem B7699805 : Blo 2027435 7699805 := bstep (se 3 (by rfl) ⟨1443713, by rfl⟩ : syracuseStep 7699805 = 2887427) B2887427
theorem B5133203 : Blo 2027435 5133203 := bstep (se 1 (by rfl) ⟨3849902, by rfl⟩ : syracuseStep 5133203 = 7699805) B7699805
theorem B3422135 : Blo 2027435 3422135 := bstep (se 1 (by rfl) ⟨2566601, by rfl⟩ : syracuseStep 3422135 = 5133203) B5133203
theorem B2281423 : Blo 2027435 2281423 := bstep (se 1 (by rfl) ⟨1711067, by rfl⟩ : syracuseStep 2281423 = 3422135) B3422135
theorem B3041897 : Blo 2027435 3041897 := bstep (se 2 (by rfl) ⟨1140711, by rfl⟩ : syracuseStep 3041897 = 2281423) B2281423
theorem B2027931 : Blo 2027435 2027931 := bstep (se 1 (by rfl) ⟨1520948, by rfl⟩ : syracuseStep 2027931 = 3041897) B3041897
theorem B2601625 : Blo 2027435 2601625 := bbase (se 2 (by rfl) ⟨975609, by rfl⟩ : syracuseStep 2601625 = 1951219) (by norm_num)
theorem B3468833 : Blo 2027435 3468833 := bstep (se 2 (by rfl) ⟨1300812, by rfl⟩ : syracuseStep 3468833 = 2601625) B2601625
theorem B2312555 : Blo 2027435 2312555 := bstep (se 1 (by rfl) ⟨1734416, by rfl⟩ : syracuseStep 2312555 = 3468833) B3468833
theorem B6166813 : Blo 2027435 6166813 := bstep (se 3 (by rfl) ⟨1156277, by rfl⟩ : syracuseStep 6166813 = 2312555) B2312555
theorem B8222417 : Blo 2027435 8222417 := bstep (se 2 (by rfl) ⟨3083406, by rfl⟩ : syracuseStep 8222417 = 6166813) B6166813
theorem B5481611 : Blo 2027435 5481611 := bstep (se 1 (by rfl) ⟨4111208, by rfl⟩ : syracuseStep 5481611 = 8222417) B8222417
theorem B3654407 : Blo 2027435 3654407 := bstep (se 1 (by rfl) ⟨2740805, by rfl⟩ : syracuseStep 3654407 = 5481611) B5481611
theorem B9745085 : Blo 2027435 9745085 := bstep (se 3 (by rfl) ⟨1827203, by rfl⟩ : syracuseStep 9745085 = 3654407) B3654407
theorem B6496723 : Blo 2027435 6496723 := bstep (se 1 (by rfl) ⟨4872542, by rfl⟩ : syracuseStep 6496723 = 9745085) B9745085
theorem B8662297 : Blo 2027435 8662297 := bstep (se 2 (by rfl) ⟨3248361, by rfl⟩ : syracuseStep 8662297 = 6496723) B6496723
theorem B11549729 : Blo 2027435 11549729 := bstep (se 2 (by rfl) ⟨4331148, by rfl⟩ : syracuseStep 11549729 = 8662297) B8662297
theorem B7699819 : Blo 2027435 7699819 := bstep (se 1 (by rfl) ⟨5774864, by rfl⟩ : syracuseStep 7699819 = 11549729) B11549729
theorem B10266425 : Blo 2027435 10266425 := bstep (se 2 (by rfl) ⟨3849909, by rfl⟩ : syracuseStep 10266425 = 7699819) B7699819
theorem B6844283 : Blo 2027435 6844283 := bstep (se 1 (by rfl) ⟨5133212, by rfl⟩ : syracuseStep 6844283 = 10266425) B10266425
theorem B4562855 : Blo 2027435 4562855 := bstep (se 1 (by rfl) ⟨3422141, by rfl⟩ : syracuseStep 4562855 = 6844283) B6844283
theorem B3041903 : Blo 2027435 3041903 := bstep (se 1 (by rfl) ⟨2281427, by rfl⟩ : syracuseStep 3041903 = 4562855) B4562855
theorem B2027935 : Blo 2027435 2027935 := bstep (se 1 (by rfl) ⟨1520951, by rfl⟩ : syracuseStep 2027935 = 3041903) B3041903
theorem B3041909 : Blo 2027435 3041909 := bbase (se 5 (by rfl) ⟨142589, by rfl⟩ : syracuseStep 3041909 = 285179) (by norm_num)
theorem B2027939 : Blo 2027435 2027939 := bstep (se 1 (by rfl) ⟨1520954, by rfl⟩ : syracuseStep 2027939 = 3041909) B3041909
theorem B3849925 : Blo 2027435 3849925 := bbase (se 4 (by rfl) ⟨360930, by rfl⟩ : syracuseStep 3849925 = 721861) (by norm_num)
theorem B5133233 : Blo 2027435 5133233 := bstep (se 2 (by rfl) ⟨1924962, by rfl⟩ : syracuseStep 5133233 = 3849925) B3849925
theorem B3422155 : Blo 2027435 3422155 := bstep (se 1 (by rfl) ⟨2566616, by rfl⟩ : syracuseStep 3422155 = 5133233) B5133233
theorem B4562873 : Blo 2027435 4562873 := bstep (se 2 (by rfl) ⟨1711077, by rfl⟩ : syracuseStep 4562873 = 3422155) B3422155
theorem B3041915 : Blo 2027435 3041915 := bstep (se 1 (by rfl) ⟨2281436, by rfl⟩ : syracuseStep 3041915 = 4562873) B4562873
theorem B2027943 : Blo 2027435 2027943 := bstep (se 1 (by rfl) ⟨1520957, by rfl⟩ : syracuseStep 2027943 = 3041915) B3041915
theorem B2281441 : Blo 2027435 2281441 := bbase (se 2 (by rfl) ⟨855540, by rfl⟩ : syracuseStep 2281441 = 1711081) (by norm_num)
theorem B3041921 : Blo 2027435 3041921 := bstep (se 2 (by rfl) ⟨1140720, by rfl⟩ : syracuseStep 3041921 = 2281441) B2281441
theorem B2027947 : Blo 2027435 2027947 := bstep (se 1 (by rfl) ⟨1520960, by rfl⟩ : syracuseStep 2027947 = 3041921) B3041921
theorem B5133253 : Blo 2027435 5133253 := bbase (se 4 (by rfl) ⟨481242, by rfl⟩ : syracuseStep 5133253 = 962485) (by norm_num)
theorem B6844337 : Blo 2027435 6844337 := bstep (se 2 (by rfl) ⟨2566626, by rfl⟩ : syracuseStep 6844337 = 5133253) B5133253
theorem B4562891 : Blo 2027435 4562891 := bstep (se 1 (by rfl) ⟨3422168, by rfl⟩ : syracuseStep 4562891 = 6844337) B6844337
theorem B3041927 : Blo 2027435 3041927 := bstep (se 1 (by rfl) ⟨2281445, by rfl⟩ : syracuseStep 3041927 = 4562891) B4562891
theorem B2027951 : Blo 2027435 2027951 := bstep (se 1 (by rfl) ⟨1520963, by rfl⟩ : syracuseStep 2027951 = 3041927) B3041927
theorem B3041933 : Blo 2027435 3041933 := bbase (se 3 (by rfl) ⟨570362, by rfl⟩ : syracuseStep 3041933 = 1140725) (by norm_num)
theorem B2027955 : Blo 2027435 2027955 := bstep (se 1 (by rfl) ⟨1520966, by rfl⟩ : syracuseStep 2027955 = 3041933) B3041933
theorem B4562909 : Blo 2027435 4562909 := bbase (se 3 (by rfl) ⟨855545, by rfl⟩ : syracuseStep 4562909 = 1711091) (by norm_num)
theorem B3041939 : Blo 2027435 3041939 := bstep (se 1 (by rfl) ⟨2281454, by rfl⟩ : syracuseStep 3041939 = 4562909) B4562909
theorem B2027959 : Blo 2027435 2027959 := bstep (se 1 (by rfl) ⟨1520969, by rfl⟩ : syracuseStep 2027959 = 3041939) B3041939
theorem B3422189 : Blo 2027435 3422189 := bbase (se 3 (by rfl) ⟨641660, by rfl⟩ : syracuseStep 3422189 = 1283321) (by norm_num)
theorem B2281459 : Blo 2027435 2281459 := bstep (se 1 (by rfl) ⟨1711094, by rfl⟩ : syracuseStep 2281459 = 3422189) B3422189
theorem B3041945 : Blo 2027435 3041945 := bstep (se 2 (by rfl) ⟨1140729, by rfl⟩ : syracuseStep 3041945 = 2281459) B2281459
theorem B2027963 : Blo 2027435 2027963 := bstep (se 1 (by rfl) ⟨1520972, by rfl⟩ : syracuseStep 2027963 = 3041945) B3041945
theorem B3125525 : Blo 2027435 3125525 := bbase (se 6 (by rfl) ⟨73254, by rfl⟩ : syracuseStep 3125525 = 146509) (by norm_num)
theorem B8334733 : Blo 2027435 8334733 := bstep (se 3 (by rfl) ⟨1562762, by rfl⟩ : syracuseStep 8334733 = 3125525) B3125525
theorem B11112977 : Blo 2027435 11112977 := bstep (se 2 (by rfl) ⟨4167366, by rfl⟩ : syracuseStep 11112977 = 8334733) B8334733
theorem B7408651 : Blo 2027435 7408651 := bstep (se 1 (by rfl) ⟨5556488, by rfl⟩ : syracuseStep 7408651 = 11112977) B11112977
theorem B9878201 : Blo 2027435 9878201 := bstep (se 2 (by rfl) ⟨3704325, by rfl⟩ : syracuseStep 9878201 = 7408651) B7408651
theorem B6585467 : Blo 2027435 6585467 := bstep (se 1 (by rfl) ⟨4939100, by rfl⟩ : syracuseStep 6585467 = 9878201) B9878201
theorem B17561245 : Blo 2027435 17561245 := bstep (se 3 (by rfl) ⟨3292733, by rfl⟩ : syracuseStep 17561245 = 6585467) B6585467
theorem B23414993 : Blo 2027435 23414993 := bstep (se 2 (by rfl) ⟨8780622, by rfl⟩ : syracuseStep 23414993 = 17561245) B17561245
theorem B15609995 : Blo 2027435 15609995 := bstep (se 1 (by rfl) ⟨11707496, by rfl⟩ : syracuseStep 15609995 = 23414993) B23414993
theorem B10406663 : Blo 2027435 10406663 := bstep (se 1 (by rfl) ⟨7804997, by rfl⟩ : syracuseStep 10406663 = 15609995) B15609995
theorem B6937775 : Blo 2027435 6937775 := bstep (se 1 (by rfl) ⟨5203331, by rfl⟩ : syracuseStep 6937775 = 10406663) B10406663
theorem B4625183 : Blo 2027435 4625183 := bstep (se 1 (by rfl) ⟨3468887, by rfl⟩ : syracuseStep 4625183 = 6937775) B6937775
theorem B3083455 : Blo 2027435 3083455 := bstep (se 1 (by rfl) ⟨2312591, by rfl⟩ : syracuseStep 3083455 = 4625183) B4625183
theorem B4111273 : Blo 2027435 4111273 := bstep (se 2 (by rfl) ⟨1541727, by rfl⟩ : syracuseStep 4111273 = 3083455) B3083455
theorem B5481697 : Blo 2027435 5481697 := bstep (se 2 (by rfl) ⟨2055636, by rfl⟩ : syracuseStep 5481697 = 4111273) B4111273
theorem B7308929 : Blo 2027435 7308929 := bstep (se 2 (by rfl) ⟨2740848, by rfl⟩ : syracuseStep 7308929 = 5481697) B5481697
theorem B4872619 : Blo 2027435 4872619 := bstep (se 1 (by rfl) ⟨3654464, by rfl⟩ : syracuseStep 4872619 = 7308929) B7308929
theorem B25987301 : Blo 2027435 25987301 := bstep (se 4 (by rfl) ⟨2436309, by rfl⟩ : syracuseStep 25987301 = 4872619) B4872619
theorem B17324867 : Blo 2027435 17324867 := bstep (se 1 (by rfl) ⟨12993650, by rfl⟩ : syracuseStep 17324867 = 25987301) B25987301
theorem B11549911 : Blo 2027435 11549911 := bstep (se 1 (by rfl) ⟨8662433, by rfl⟩ : syracuseStep 11549911 = 17324867) B17324867
theorem B15399881 : Blo 2027435 15399881 := bstep (se 2 (by rfl) ⟨5774955, by rfl⟩ : syracuseStep 15399881 = 11549911) B11549911
theorem B10266587 : Blo 2027435 10266587 := bstep (se 1 (by rfl) ⟨7699940, by rfl⟩ : syracuseStep 10266587 = 15399881) B15399881
theorem B6844391 : Blo 2027435 6844391 := bstep (se 1 (by rfl) ⟨5133293, by rfl⟩ : syracuseStep 6844391 = 10266587) B10266587
theorem B4562927 : Blo 2027435 4562927 := bstep (se 1 (by rfl) ⟨3422195, by rfl⟩ : syracuseStep 4562927 = 6844391) B6844391
theorem B3041951 : Blo 2027435 3041951 := bstep (se 1 (by rfl) ⟨2281463, by rfl⟩ : syracuseStep 3041951 = 4562927) B4562927
theorem B2027967 : Blo 2027435 2027967 := bstep (se 1 (by rfl) ⟨1520975, by rfl⟩ : syracuseStep 2027967 = 3041951) B3041951
theorem B3041957 : Blo 2027435 3041957 := bbase (se 4 (by rfl) ⟨285183, by rfl⟩ : syracuseStep 3041957 = 570367) (by norm_num)
theorem B2027971 : Blo 2027435 2027971 := bstep (se 1 (by rfl) ⟨1520978, by rfl⟩ : syracuseStep 2027971 = 3041957) B3041957
theorem B2566657 : Blo 2027435 2566657 := bbase (se 2 (by rfl) ⟨962496, by rfl⟩ : syracuseStep 2566657 = 1924993) (by norm_num)
theorem B3422209 : Blo 2027435 3422209 := bstep (se 2 (by rfl) ⟨1283328, by rfl⟩ : syracuseStep 3422209 = 2566657) B2566657
theorem B4562945 : Blo 2027435 4562945 := bstep (se 2 (by rfl) ⟨1711104, by rfl⟩ : syracuseStep 4562945 = 3422209) B3422209
theorem B3041963 : Blo 2027435 3041963 := bstep (se 1 (by rfl) ⟨2281472, by rfl⟩ : syracuseStep 3041963 = 4562945) B4562945
theorem B2027975 : Blo 2027435 2027975 := bstep (se 1 (by rfl) ⟨1520981, by rfl⟩ : syracuseStep 2027975 = 3041963) B3041963
theorem B2281477 : Blo 2027435 2281477 := bbase (se 4 (by rfl) ⟨213888, by rfl⟩ : syracuseStep 2281477 = 427777) (by norm_num)
theorem B3041969 : Blo 2027435 3041969 := bstep (se 2 (by rfl) ⟨1140738, by rfl⟩ : syracuseStep 3041969 = 2281477) B2281477
theorem B2027979 : Blo 2027435 2027979 := bstep (se 1 (by rfl) ⟨1520984, by rfl⟩ : syracuseStep 2027979 = 3041969) B3041969
theorem B2887501 : Blo 2027435 2887501 := bbase (se 3 (by rfl) ⟨541406, by rfl⟩ : syracuseStep 2887501 = 1082813) (by norm_num)
theorem B3850001 : Blo 2027435 3850001 := bstep (se 2 (by rfl) ⟨1443750, by rfl⟩ : syracuseStep 3850001 = 2887501) B2887501
theorem B2566667 : Blo 2027435 2566667 := bstep (se 1 (by rfl) ⟨1925000, by rfl⟩ : syracuseStep 2566667 = 3850001) B3850001
theorem B6844445 : Blo 2027435 6844445 := bstep (se 3 (by rfl) ⟨1283333, by rfl⟩ : syracuseStep 6844445 = 2566667) B2566667
theorem B4562963 : Blo 2027435 4562963 := bstep (se 1 (by rfl) ⟨3422222, by rfl⟩ : syracuseStep 4562963 = 6844445) B6844445
theorem B3041975 : Blo 2027435 3041975 := bstep (se 1 (by rfl) ⟨2281481, by rfl⟩ : syracuseStep 3041975 = 4562963) B4562963
theorem B2027983 : Blo 2027435 2027983 := bstep (se 1 (by rfl) ⟨1520987, by rfl⟩ : syracuseStep 2027983 = 3041975) B3041975
theorem B3041981 : Blo 2027435 3041981 := bbase (se 3 (by rfl) ⟨570371, by rfl⟩ : syracuseStep 3041981 = 1140743) (by norm_num)
theorem B2027987 : Blo 2027435 2027987 := bstep (se 1 (by rfl) ⟨1520990, by rfl⟩ : syracuseStep 2027987 = 3041981) B3041981
theorem B4562981 : Blo 2027435 4562981 := bbase (se 4 (by rfl) ⟨427779, by rfl⟩ : syracuseStep 4562981 = 855559) (by norm_num)
theorem B3041987 : Blo 2027435 3041987 := bstep (se 1 (by rfl) ⟨2281490, by rfl⟩ : syracuseStep 3041987 = 4562981) B4562981
theorem B2027991 : Blo 2027435 2027991 := bstep (se 1 (by rfl) ⟨1520993, by rfl⟩ : syracuseStep 2027991 = 3041987) B3041987
theorem B5133365 : Blo 2027435 5133365 := bbase (se 5 (by rfl) ⟨240626, by rfl⟩ : syracuseStep 5133365 = 481253) (by norm_num)
theorem B3422243 : Blo 2027435 3422243 := bstep (se 1 (by rfl) ⟨2566682, by rfl⟩ : syracuseStep 3422243 = 5133365) B5133365
theorem B2281495 : Blo 2027435 2281495 := bstep (se 1 (by rfl) ⟨1711121, by rfl⟩ : syracuseStep 2281495 = 3422243) B3422243
theorem B3041993 : Blo 2027435 3041993 := bstep (se 2 (by rfl) ⟨1140747, by rfl⟩ : syracuseStep 3041993 = 2281495) B2281495
theorem B2027995 : Blo 2027435 2027995 := bstep (se 1 (by rfl) ⟨1520996, by rfl⟩ : syracuseStep 2027995 = 3041993) B3041993
theorem B7309045 : Blo 2027435 7309045 := bbase (se 5 (by rfl) ⟨342611, by rfl⟩ : syracuseStep 7309045 = 685223) (by norm_num)
theorem B9745393 : Blo 2027435 9745393 := bstep (se 2 (by rfl) ⟨3654522, by rfl⟩ : syracuseStep 9745393 = 7309045) B7309045
theorem B12993857 : Blo 2027435 12993857 := bstep (se 2 (by rfl) ⟨4872696, by rfl⟩ : syracuseStep 12993857 = 9745393) B9745393
theorem B8662571 : Blo 2027435 8662571 := bstep (se 1 (by rfl) ⟨6496928, by rfl⟩ : syracuseStep 8662571 = 12993857) B12993857
theorem B5775047 : Blo 2027435 5775047 := bstep (se 1 (by rfl) ⟨4331285, by rfl⟩ : syracuseStep 5775047 = 8662571) B8662571
theorem B3850031 : Blo 2027435 3850031 := bstep (se 1 (by rfl) ⟨2887523, by rfl⟩ : syracuseStep 3850031 = 5775047) B5775047
theorem B10266749 : Blo 2027435 10266749 := bstep (se 3 (by rfl) ⟨1925015, by rfl⟩ : syracuseStep 10266749 = 3850031) B3850031
theorem B6844499 : Blo 2027435 6844499 := bstep (se 1 (by rfl) ⟨5133374, by rfl⟩ : syracuseStep 6844499 = 10266749) B10266749
theorem B4562999 : Blo 2027435 4562999 := bstep (se 1 (by rfl) ⟨3422249, by rfl⟩ : syracuseStep 4562999 = 6844499) B6844499
theorem B3041999 : Blo 2027435 3041999 := bstep (se 1 (by rfl) ⟨2281499, by rfl⟩ : syracuseStep 3041999 = 4562999) B4562999
theorem B2027999 : Blo 2027435 2027999 := bstep (se 1 (by rfl) ⟨1520999, by rfl⟩ : syracuseStep 2027999 = 3041999) B3041999
theorem B3042005 : Blo 2027435 3042005 := bbase (se 7 (by rfl) ⟨35648, by rfl⟩ : syracuseStep 3042005 = 71297) (by norm_num)
theorem B2028003 : Blo 2027435 2028003 := bstep (se 1 (by rfl) ⟨1521002, by rfl⟩ : syracuseStep 2028003 = 3042005) B3042005
theorem B9634373 : Blo 2027435 9634373 := bbase (se 4 (by rfl) ⟨903222, by rfl⟩ : syracuseStep 9634373 = 1806445) (by norm_num)
theorem B6422915 : Blo 2027435 6422915 := bstep (se 1 (by rfl) ⟨4817186, by rfl⟩ : syracuseStep 6422915 = 9634373) B9634373
theorem B4281943 : Blo 2027435 4281943 := bstep (se 1 (by rfl) ⟨3211457, by rfl⟩ : syracuseStep 4281943 = 6422915) B6422915
theorem B5709257 : Blo 2027435 5709257 := bstep (se 2 (by rfl) ⟨2140971, by rfl⟩ : syracuseStep 5709257 = 4281943) B4281943
theorem B3806171 : Blo 2027435 3806171 := bstep (se 1 (by rfl) ⟨2854628, by rfl⟩ : syracuseStep 3806171 = 5709257) B5709257
theorem B2537447 : Blo 2027435 2537447 := bstep (se 1 (by rfl) ⟨1903085, by rfl⟩ : syracuseStep 2537447 = 3806171) B3806171
theorem B6766525 : Blo 2027435 6766525 := bstep (se 3 (by rfl) ⟨1268723, by rfl⟩ : syracuseStep 6766525 = 2537447) B2537447
theorem B9022033 : Blo 2027435 9022033 := bstep (se 2 (by rfl) ⟨3383262, by rfl⟩ : syracuseStep 9022033 = 6766525) B6766525
theorem B48117509 : Blo 2027435 48117509 := bstep (se 4 (by rfl) ⟨4511016, by rfl⟩ : syracuseStep 48117509 = 9022033) B9022033
theorem B32078339 : Blo 2027435 32078339 := bstep (se 1 (by rfl) ⟨24058754, by rfl⟩ : syracuseStep 32078339 = 48117509) B48117509
theorem B21385559 : Blo 2027435 21385559 := bstep (se 1 (by rfl) ⟨16039169, by rfl⟩ : syracuseStep 21385559 = 32078339) B32078339
theorem B57028157 : Blo 2027435 57028157 := bstep (se 3 (by rfl) ⟨10692779, by rfl⟩ : syracuseStep 57028157 = 21385559) B21385559
theorem B38018771 : Blo 2027435 38018771 := bstep (se 1 (by rfl) ⟨28514078, by rfl⟩ : syracuseStep 38018771 = 57028157) B57028157
theorem B25345847 : Blo 2027435 25345847 := bstep (se 1 (by rfl) ⟨19009385, by rfl⟩ : syracuseStep 25345847 = 38018771) B38018771
theorem B16897231 : Blo 2027435 16897231 := bstep (se 1 (by rfl) ⟨12672923, by rfl⟩ : syracuseStep 16897231 = 25345847) B25345847
theorem B90118565 : Blo 2027435 90118565 := bstep (se 4 (by rfl) ⟨8448615, by rfl⟩ : syracuseStep 90118565 = 16897231) B16897231
theorem B60079043 : Blo 2027435 60079043 := bstep (se 1 (by rfl) ⟨45059282, by rfl⟩ : syracuseStep 60079043 = 90118565) B90118565
theorem B160210781 : Blo 2027435 160210781 := bstep (se 3 (by rfl) ⟨30039521, by rfl⟩ : syracuseStep 160210781 = 60079043) B60079043
theorem B106807187 : Blo 2027435 106807187 := bstep (se 1 (by rfl) ⟨80105390, by rfl⟩ : syracuseStep 106807187 = 160210781) B160210781
theorem B71204791 : Blo 2027435 71204791 := bstep (se 1 (by rfl) ⟨53403593, by rfl⟩ : syracuseStep 71204791 = 106807187) B106807187
theorem B94939721 : Blo 2027435 94939721 := bstep (se 2 (by rfl) ⟨35602395, by rfl⟩ : syracuseStep 94939721 = 71204791) B71204791
theorem B63293147 : Blo 2027435 63293147 := bstep (se 1 (by rfl) ⟨47469860, by rfl⟩ : syracuseStep 63293147 = 94939721) B94939721
theorem B42195431 : Blo 2027435 42195431 := bstep (se 1 (by rfl) ⟨31646573, by rfl⟩ : syracuseStep 42195431 = 63293147) B63293147
theorem B112521149 : Blo 2027435 112521149 := bstep (se 3 (by rfl) ⟨21097715, by rfl⟩ : syracuseStep 112521149 = 42195431) B42195431
theorem B75014099 : Blo 2027435 75014099 := bstep (se 1 (by rfl) ⟨56260574, by rfl⟩ : syracuseStep 75014099 = 112521149) B112521149
theorem B50009399 : Blo 2027435 50009399 := bstep (se 1 (by rfl) ⟨37507049, by rfl⟩ : syracuseStep 50009399 = 75014099) B75014099
theorem B33339599 : Blo 2027435 33339599 := bstep (se 1 (by rfl) ⟨25004699, by rfl⟩ : syracuseStep 33339599 = 50009399) B50009399
theorem B22226399 : Blo 2027435 22226399 := bstep (se 1 (by rfl) ⟨16669799, by rfl⟩ : syracuseStep 22226399 = 33339599) B33339599
theorem B14817599 : Blo 2027435 14817599 := bstep (se 1 (by rfl) ⟨11113199, by rfl⟩ : syracuseStep 14817599 = 22226399) B22226399
theorem B9878399 : Blo 2027435 9878399 := bstep (se 1 (by rfl) ⟨7408799, by rfl⟩ : syracuseStep 9878399 = 14817599) B14817599
theorem B6585599 : Blo 2027435 6585599 := bstep (se 1 (by rfl) ⟨4939199, by rfl⟩ : syracuseStep 6585599 = 9878399) B9878399
theorem B4390399 : Blo 2027435 4390399 := bstep (se 1 (by rfl) ⟨3292799, by rfl⟩ : syracuseStep 4390399 = 6585599) B6585599
theorem B5853865 : Blo 2027435 5853865 := bstep (se 2 (by rfl) ⟨2195199, by rfl⟩ : syracuseStep 5853865 = 4390399) B4390399
theorem B7805153 : Blo 2027435 7805153 := bstep (se 2 (by rfl) ⟨2926932, by rfl⟩ : syracuseStep 7805153 = 5853865) B5853865
theorem B5203435 : Blo 2027435 5203435 := bstep (se 1 (by rfl) ⟨3902576, by rfl⟩ : syracuseStep 5203435 = 7805153) B7805153
theorem B6937913 : Blo 2027435 6937913 := bstep (se 2 (by rfl) ⟨2601717, by rfl⟩ : syracuseStep 6937913 = 5203435) B5203435
theorem B4625275 : Blo 2027435 4625275 := bstep (se 1 (by rfl) ⟨3468956, by rfl⟩ : syracuseStep 4625275 = 6937913) B6937913
theorem B6167033 : Blo 2027435 6167033 := bstep (se 2 (by rfl) ⟨2312637, by rfl⟩ : syracuseStep 6167033 = 4625275) B4625275
theorem B4111355 : Blo 2027435 4111355 := bstep (se 1 (by rfl) ⟨3083516, by rfl⟩ : syracuseStep 4111355 = 6167033) B6167033
theorem B10963613 : Blo 2027435 10963613 := bstep (se 3 (by rfl) ⟨2055677, by rfl⟩ : syracuseStep 10963613 = 4111355) B4111355
theorem B7309075 : Blo 2027435 7309075 := bstep (se 1 (by rfl) ⟨5481806, by rfl⟩ : syracuseStep 7309075 = 10963613) B10963613
theorem B9745433 : Blo 2027435 9745433 := bstep (se 2 (by rfl) ⟨3654537, by rfl⟩ : syracuseStep 9745433 = 7309075) B7309075
theorem B6496955 : Blo 2027435 6496955 := bstep (se 1 (by rfl) ⟨4872716, by rfl⟩ : syracuseStep 6496955 = 9745433) B9745433
theorem B4331303 : Blo 2027435 4331303 := bstep (se 1 (by rfl) ⟨3248477, by rfl⟩ : syracuseStep 4331303 = 6496955) B6496955
theorem B2887535 : Blo 2027435 2887535 := bstep (se 1 (by rfl) ⟨2165651, by rfl⟩ : syracuseStep 2887535 = 4331303) B4331303
theorem B7700093 : Blo 2027435 7700093 := bstep (se 3 (by rfl) ⟨1443767, by rfl⟩ : syracuseStep 7700093 = 2887535) B2887535
theorem B5133395 : Blo 2027435 5133395 := bstep (se 1 (by rfl) ⟨3850046, by rfl⟩ : syracuseStep 5133395 = 7700093) B7700093
theorem B3422263 : Blo 2027435 3422263 := bstep (se 1 (by rfl) ⟨2566697, by rfl⟩ : syracuseStep 3422263 = 5133395) B5133395
theorem B4563017 : Blo 2027435 4563017 := bstep (se 2 (by rfl) ⟨1711131, by rfl⟩ : syracuseStep 4563017 = 3422263) B3422263
theorem B3042011 : Blo 2027435 3042011 := bstep (se 1 (by rfl) ⟨2281508, by rfl⟩ : syracuseStep 3042011 = 4563017) B4563017
theorem B2028007 : Blo 2027435 2028007 := bstep (se 1 (by rfl) ⟨1521005, by rfl⟩ : syracuseStep 2028007 = 3042011) B3042011
theorem B2281513 : Blo 2027435 2281513 := bbase (se 2 (by rfl) ⟨855567, by rfl⟩ : syracuseStep 2281513 = 1711135) (by norm_num)
theorem B3042017 : Blo 2027435 3042017 := bstep (se 2 (by rfl) ⟨1140756, by rfl⟩ : syracuseStep 3042017 = 2281513) B2281513
theorem B2028011 : Blo 2027435 2028011 := bstep (se 1 (by rfl) ⟨1521008, by rfl⟩ : syracuseStep 2028011 = 3042017) B3042017
theorem B20813813 : Blo 2027435 20813813 := bbase (se 5 (by rfl) ⟨975647, by rfl⟩ : syracuseStep 20813813 = 1951295) (by norm_num)
theorem B13875875 : Blo 2027435 13875875 := bstep (se 1 (by rfl) ⟨10406906, by rfl⟩ : syracuseStep 13875875 = 20813813) B20813813
theorem B9250583 : Blo 2027435 9250583 := bstep (se 1 (by rfl) ⟨6937937, by rfl⟩ : syracuseStep 9250583 = 13875875) B13875875
theorem B24668221 : Blo 2027435 24668221 := bstep (se 3 (by rfl) ⟨4625291, by rfl⟩ : syracuseStep 24668221 = 9250583) B9250583
theorem B32890961 : Blo 2027435 32890961 := bstep (se 2 (by rfl) ⟨12334110, by rfl⟩ : syracuseStep 32890961 = 24668221) B24668221
theorem B21927307 : Blo 2027435 21927307 := bstep (se 1 (by rfl) ⟨16445480, by rfl⟩ : syracuseStep 21927307 = 32890961) B32890961
theorem B29236409 : Blo 2027435 29236409 := bstep (se 2 (by rfl) ⟨10963653, by rfl⟩ : syracuseStep 29236409 = 21927307) B21927307
theorem B19490939 : Blo 2027435 19490939 := bstep (se 1 (by rfl) ⟨14618204, by rfl⟩ : syracuseStep 19490939 = 29236409) B29236409
theorem B12993959 : Blo 2027435 12993959 := bstep (se 1 (by rfl) ⟨9745469, by rfl⟩ : syracuseStep 12993959 = 19490939) B19490939
theorem B8662639 : Blo 2027435 8662639 := bstep (se 1 (by rfl) ⟨6496979, by rfl⟩ : syracuseStep 8662639 = 12993959) B12993959
theorem B11550185 : Blo 2027435 11550185 := bstep (se 2 (by rfl) ⟨4331319, by rfl⟩ : syracuseStep 11550185 = 8662639) B8662639
theorem B7700123 : Blo 2027435 7700123 := bstep (se 1 (by rfl) ⟨5775092, by rfl⟩ : syracuseStep 7700123 = 11550185) B11550185
theorem B5133415 : Blo 2027435 5133415 := bstep (se 1 (by rfl) ⟨3850061, by rfl⟩ : syracuseStep 5133415 = 7700123) B7700123
theorem B6844553 : Blo 2027435 6844553 := bstep (se 2 (by rfl) ⟨2566707, by rfl⟩ : syracuseStep 6844553 = 5133415) B5133415
theorem B4563035 : Blo 2027435 4563035 := bstep (se 1 (by rfl) ⟨3422276, by rfl⟩ : syracuseStep 4563035 = 6844553) B6844553
theorem B3042023 : Blo 2027435 3042023 := bstep (se 1 (by rfl) ⟨2281517, by rfl⟩ : syracuseStep 3042023 = 4563035) B4563035
theorem B2028015 : Blo 2027435 2028015 := bstep (se 1 (by rfl) ⟨1521011, by rfl⟩ : syracuseStep 2028015 = 3042023) B3042023
theorem B3042029 : Blo 2027435 3042029 := bbase (se 3 (by rfl) ⟨570380, by rfl⟩ : syracuseStep 3042029 = 1140761) (by norm_num)
theorem B2028019 : Blo 2027435 2028019 := bstep (se 1 (by rfl) ⟨1521014, by rfl⟩ : syracuseStep 2028019 = 3042029) B3042029
theorem B4563053 : Blo 2027435 4563053 := bbase (se 3 (by rfl) ⟨855572, by rfl⟩ : syracuseStep 4563053 = 1711145) (by norm_num)
theorem B3042035 : Blo 2027435 3042035 := bstep (se 1 (by rfl) ⟨2281526, by rfl⟩ : syracuseStep 3042035 = 4563053) B4563053
theorem B2028023 : Blo 2027435 2028023 := bstep (se 1 (by rfl) ⟨1521017, by rfl⟩ : syracuseStep 2028023 = 3042035) B3042035
theorem B3850085 : Blo 2027435 3850085 := bbase (se 4 (by rfl) ⟨360945, by rfl⟩ : syracuseStep 3850085 = 721891) (by norm_num)
theorem B2566723 : Blo 2027435 2566723 := bstep (se 1 (by rfl) ⟨1925042, by rfl⟩ : syracuseStep 2566723 = 3850085) B3850085
theorem B3422297 : Blo 2027435 3422297 := bstep (se 2 (by rfl) ⟨1283361, by rfl⟩ : syracuseStep 3422297 = 2566723) B2566723
theorem B2281531 : Blo 2027435 2281531 := bstep (se 1 (by rfl) ⟨1711148, by rfl⟩ : syracuseStep 2281531 = 3422297) B3422297
theorem B3042041 : Blo 2027435 3042041 := bstep (se 2 (by rfl) ⟨1140765, by rfl⟩ : syracuseStep 3042041 = 2281531) B2281531
theorem B2028027 : Blo 2027435 2028027 := bstep (se 1 (by rfl) ⟨1521020, by rfl⟩ : syracuseStep 2028027 = 3042041) B3042041
theorem B2503321 : Blo 2027435 2503321 := bbase (se 2 (by rfl) ⟨938745, by rfl⟩ : syracuseStep 2503321 = 1877491) (by norm_num)
theorem B53404181 : Blo 2027435 53404181 := bstep (se 6 (by rfl) ⟨1251660, by rfl⟩ : syracuseStep 53404181 = 2503321) B2503321
theorem B35602787 : Blo 2027435 35602787 := bstep (se 1 (by rfl) ⟨26702090, by rfl⟩ : syracuseStep 35602787 = 53404181) B53404181
theorem B23735191 : Blo 2027435 23735191 := bstep (se 1 (by rfl) ⟨17801393, by rfl⟩ : syracuseStep 23735191 = 35602787) B35602787
theorem B31646921 : Blo 2027435 31646921 := bstep (se 2 (by rfl) ⟨11867595, by rfl⟩ : syracuseStep 31646921 = 23735191) B23735191
theorem B84391789 : Blo 2027435 84391789 := bstep (se 3 (by rfl) ⟨15823460, by rfl⟩ : syracuseStep 84391789 = 31646921) B31646921
theorem B112522385 : Blo 2027435 112522385 := bstep (se 2 (by rfl) ⟨42195894, by rfl⟩ : syracuseStep 112522385 = 84391789) B84391789
theorem B75014923 : Blo 2027435 75014923 := bstep (se 1 (by rfl) ⟨56261192, by rfl⟩ : syracuseStep 75014923 = 112522385) B112522385
theorem B100019897 : Blo 2027435 100019897 := bstep (se 2 (by rfl) ⟨37507461, by rfl⟩ : syracuseStep 100019897 = 75014923) B75014923
theorem B66679931 : Blo 2027435 66679931 := bstep (se 1 (by rfl) ⟨50009948, by rfl⟩ : syracuseStep 66679931 = 100019897) B100019897
theorem B44453287 : Blo 2027435 44453287 := bstep (se 1 (by rfl) ⟨33339965, by rfl⟩ : syracuseStep 44453287 = 66679931) B66679931
theorem B59271049 : Blo 2027435 59271049 := bstep (se 2 (by rfl) ⟨22226643, by rfl⟩ : syracuseStep 59271049 = 44453287) B44453287
theorem B79028065 : Blo 2027435 79028065 := bstep (se 2 (by rfl) ⟨29635524, by rfl⟩ : syracuseStep 79028065 = 59271049) B59271049
theorem B105370753 : Blo 2027435 105370753 := bstep (se 2 (by rfl) ⟨39514032, by rfl⟩ : syracuseStep 105370753 = 79028065) B79028065
theorem B140494337 : Blo 2027435 140494337 := bstep (se 2 (by rfl) ⟨52685376, by rfl⟩ : syracuseStep 140494337 = 105370753) B105370753
theorem B93662891 : Blo 2027435 93662891 := bstep (se 1 (by rfl) ⟨70247168, by rfl⟩ : syracuseStep 93662891 = 140494337) B140494337
theorem B62441927 : Blo 2027435 62441927 := bstep (se 1 (by rfl) ⟨46831445, by rfl⟩ : syracuseStep 62441927 = 93662891) B93662891
theorem B41627951 : Blo 2027435 41627951 := bstep (se 1 (by rfl) ⟨31220963, by rfl⟩ : syracuseStep 41627951 = 62441927) B62441927
theorem B27751967 : Blo 2027435 27751967 := bstep (se 1 (by rfl) ⟨20813975, by rfl⟩ : syracuseStep 27751967 = 41627951) B41627951
theorem B18501311 : Blo 2027435 18501311 := bstep (se 1 (by rfl) ⟨13875983, by rfl⟩ : syracuseStep 18501311 = 27751967) B27751967
theorem B12334207 : Blo 2027435 12334207 := bstep (se 1 (by rfl) ⟨9250655, by rfl⟩ : syracuseStep 12334207 = 18501311) B18501311
theorem B16445609 : Blo 2027435 16445609 := bstep (se 2 (by rfl) ⟨6167103, by rfl⟩ : syracuseStep 16445609 = 12334207) B12334207
theorem B10963739 : Blo 2027435 10963739 := bstep (se 1 (by rfl) ⟨8222804, by rfl⟩ : syracuseStep 10963739 = 16445609) B16445609
theorem B7309159 : Blo 2027435 7309159 := bstep (se 1 (by rfl) ⟨5481869, by rfl⟩ : syracuseStep 7309159 = 10963739) B10963739
theorem B38982181 : Blo 2027435 38982181 := bstep (se 4 (by rfl) ⟨3654579, by rfl⟩ : syracuseStep 38982181 = 7309159) B7309159
theorem B51976241 : Blo 2027435 51976241 := bstep (se 2 (by rfl) ⟨19491090, by rfl⟩ : syracuseStep 51976241 = 38982181) B38982181
theorem B34650827 : Blo 2027435 34650827 := bstep (se 1 (by rfl) ⟨25988120, by rfl⟩ : syracuseStep 34650827 = 51976241) B51976241
theorem B23100551 : Blo 2027435 23100551 := bstep (se 1 (by rfl) ⟨17325413, by rfl⟩ : syracuseStep 23100551 = 34650827) B34650827
theorem B15400367 : Blo 2027435 15400367 := bstep (se 1 (by rfl) ⟨11550275, by rfl⟩ : syracuseStep 15400367 = 23100551) B23100551
theorem B10266911 : Blo 2027435 10266911 := bstep (se 1 (by rfl) ⟨7700183, by rfl⟩ : syracuseStep 10266911 = 15400367) B15400367
theorem B6844607 : Blo 2027435 6844607 := bstep (se 1 (by rfl) ⟨5133455, by rfl⟩ : syracuseStep 6844607 = 10266911) B10266911
theorem B4563071 : Blo 2027435 4563071 := bstep (se 1 (by rfl) ⟨3422303, by rfl⟩ : syracuseStep 4563071 = 6844607) B6844607
theorem B3042047 : Blo 2027435 3042047 := bstep (se 1 (by rfl) ⟨2281535, by rfl⟩ : syracuseStep 3042047 = 4563071) B4563071
theorem B2028031 : Blo 2027435 2028031 := bstep (se 1 (by rfl) ⟨1521023, by rfl⟩ : syracuseStep 2028031 = 3042047) B3042047
theorem B3042053 : Blo 2027435 3042053 := bbase (se 4 (by rfl) ⟨285192, by rfl⟩ : syracuseStep 3042053 = 570385) (by norm_num)
theorem B2028035 : Blo 2027435 2028035 := bstep (se 1 (by rfl) ⟨1521026, by rfl⟩ : syracuseStep 2028035 = 3042053) B3042053
theorem B3422317 : Blo 2027435 3422317 := bbase (se 3 (by rfl) ⟨641684, by rfl⟩ : syracuseStep 3422317 = 1283369) (by norm_num)
theorem B4563089 : Blo 2027435 4563089 := bstep (se 2 (by rfl) ⟨1711158, by rfl⟩ : syracuseStep 4563089 = 3422317) B3422317
theorem B3042059 : Blo 2027435 3042059 := bstep (se 1 (by rfl) ⟨2281544, by rfl⟩ : syracuseStep 3042059 = 4563089) B4563089
theorem B2028039 : Blo 2027435 2028039 := bstep (se 1 (by rfl) ⟨1521029, by rfl⟩ : syracuseStep 2028039 = 3042059) B3042059
theorem B2281549 : Blo 2027435 2281549 := bbase (se 3 (by rfl) ⟨427790, by rfl⟩ : syracuseStep 2281549 = 855581) (by norm_num)
theorem B3042065 : Blo 2027435 3042065 := bstep (se 2 (by rfl) ⟨1140774, by rfl⟩ : syracuseStep 3042065 = 2281549) B2281549
theorem B2028043 : Blo 2027435 2028043 := bstep (se 1 (by rfl) ⟨1521032, by rfl⟩ : syracuseStep 2028043 = 3042065) B3042065
theorem B6844661 : Blo 2027435 6844661 := bbase (se 5 (by rfl) ⟨320843, by rfl⟩ : syracuseStep 6844661 = 641687) (by norm_num)
theorem B4563107 : Blo 2027435 4563107 := bstep (se 1 (by rfl) ⟨3422330, by rfl⟩ : syracuseStep 4563107 = 6844661) B6844661
theorem B3042071 : Blo 2027435 3042071 := bstep (se 1 (by rfl) ⟨2281553, by rfl⟩ : syracuseStep 3042071 = 4563107) B4563107
theorem B2028047 : Blo 2027435 2028047 := bstep (se 1 (by rfl) ⟨1521035, by rfl⟩ : syracuseStep 2028047 = 3042071) B3042071
theorem B3042077 : Blo 2027435 3042077 := bbase (se 3 (by rfl) ⟨570389, by rfl⟩ : syracuseStep 3042077 = 1140779) (by norm_num)
theorem B2028051 : Blo 2027435 2028051 := bstep (se 1 (by rfl) ⟨1521038, by rfl⟩ : syracuseStep 2028051 = 3042077) B3042077
theorem B4563125 : Blo 2027435 4563125 := bbase (se 5 (by rfl) ⟨213896, by rfl⟩ : syracuseStep 4563125 = 427793) (by norm_num)
theorem B3042083 : Blo 2027435 3042083 := bstep (se 1 (by rfl) ⟨2281562, by rfl⟩ : syracuseStep 3042083 = 4563125) B4563125
theorem B2028055 : Blo 2027435 2028055 := bstep (se 1 (by rfl) ⟨1521041, by rfl⟩ : syracuseStep 2028055 = 3042083) B3042083
theorem B2436421 : Blo 2027435 2436421 := bbase (se 4 (by rfl) ⟨228414, by rfl⟩ : syracuseStep 2436421 = 456829) (by norm_num)
theorem B3248561 : Blo 2027435 3248561 := bstep (se 2 (by rfl) ⟨1218210, by rfl⟩ : syracuseStep 3248561 = 2436421) B2436421
theorem B2165707 : Blo 2027435 2165707 := bstep (se 1 (by rfl) ⟨1624280, by rfl⟩ : syracuseStep 2165707 = 3248561) B3248561
theorem B11550437 : Blo 2027435 11550437 := bstep (se 4 (by rfl) ⟨1082853, by rfl⟩ : syracuseStep 11550437 = 2165707) B2165707
theorem B7700291 : Blo 2027435 7700291 := bstep (se 1 (by rfl) ⟨5775218, by rfl⟩ : syracuseStep 7700291 = 11550437) B11550437
theorem B5133527 : Blo 2027435 5133527 := bstep (se 1 (by rfl) ⟨3850145, by rfl⟩ : syracuseStep 5133527 = 7700291) B7700291
theorem B3422351 : Blo 2027435 3422351 := bstep (se 1 (by rfl) ⟨2566763, by rfl⟩ : syracuseStep 3422351 = 5133527) B5133527
theorem B2281567 : Blo 2027435 2281567 := bstep (se 1 (by rfl) ⟨1711175, by rfl⟩ : syracuseStep 2281567 = 3422351) B3422351
theorem B3042089 : Blo 2027435 3042089 := bstep (se 2 (by rfl) ⟨1140783, by rfl⟩ : syracuseStep 3042089 = 2281567) B2281567
theorem B2028059 : Blo 2027435 2028059 := bstep (se 1 (by rfl) ⟨1521044, by rfl⟩ : syracuseStep 2028059 = 3042089) B3042089
theorem B4111469 : Blo 2027435 4111469 := bbase (se 3 (by rfl) ⟨770900, by rfl⟩ : syracuseStep 4111469 = 1541801) (by norm_num)
theorem B2740979 : Blo 2027435 2740979 := bstep (se 1 (by rfl) ⟨2055734, by rfl⟩ : syracuseStep 2740979 = 4111469) B4111469
theorem B7309277 : Blo 2027435 7309277 := bstep (se 3 (by rfl) ⟨1370489, by rfl⟩ : syracuseStep 7309277 = 2740979) B2740979
theorem B4872851 : Blo 2027435 4872851 := bstep (se 1 (by rfl) ⟨3654638, by rfl⟩ : syracuseStep 4872851 = 7309277) B7309277
theorem B3248567 : Blo 2027435 3248567 := bstep (se 1 (by rfl) ⟨2436425, by rfl⟩ : syracuseStep 3248567 = 4872851) B4872851
theorem B2165711 : Blo 2027435 2165711 := bstep (se 1 (by rfl) ⟨1624283, by rfl⟩ : syracuseStep 2165711 = 3248567) B3248567
theorem B5775229 : Blo 2027435 5775229 := bstep (se 3 (by rfl) ⟨1082855, by rfl⟩ : syracuseStep 5775229 = 2165711) B2165711
theorem B7700305 : Blo 2027435 7700305 := bstep (se 2 (by rfl) ⟨2887614, by rfl⟩ : syracuseStep 7700305 = 5775229) B5775229
theorem B10267073 : Blo 2027435 10267073 := bstep (se 2 (by rfl) ⟨3850152, by rfl⟩ : syracuseStep 10267073 = 7700305) B7700305
theorem B6844715 : Blo 2027435 6844715 := bstep (se 1 (by rfl) ⟨5133536, by rfl⟩ : syracuseStep 6844715 = 10267073) B10267073
theorem B4563143 : Blo 2027435 4563143 := bstep (se 1 (by rfl) ⟨3422357, by rfl⟩ : syracuseStep 4563143 = 6844715) B6844715
theorem B3042095 : Blo 2027435 3042095 := bstep (se 1 (by rfl) ⟨2281571, by rfl⟩ : syracuseStep 3042095 = 4563143) B4563143
theorem B2028063 : Blo 2027435 2028063 := bstep (se 1 (by rfl) ⟨1521047, by rfl⟩ : syracuseStep 2028063 = 3042095) B3042095
theorem B3042101 : Blo 2027435 3042101 := bbase (se 5 (by rfl) ⟨142598, by rfl⟩ : syracuseStep 3042101 = 285197) (by norm_num)
theorem B2028067 : Blo 2027435 2028067 := bstep (se 1 (by rfl) ⟨1521050, by rfl⟩ : syracuseStep 2028067 = 3042101) B3042101
theorem B5133557 : Blo 2027435 5133557 := bbase (se 5 (by rfl) ⟨240635, by rfl⟩ : syracuseStep 5133557 = 481271) (by norm_num)
theorem B3422371 : Blo 2027435 3422371 := bstep (se 1 (by rfl) ⟨2566778, by rfl⟩ : syracuseStep 3422371 = 5133557) B5133557
theorem B4563161 : Blo 2027435 4563161 := bstep (se 2 (by rfl) ⟨1711185, by rfl⟩ : syracuseStep 4563161 = 3422371) B3422371
theorem B3042107 : Blo 2027435 3042107 := bstep (se 1 (by rfl) ⟨2281580, by rfl⟩ : syracuseStep 3042107 = 4563161) B4563161
theorem B2028071 : Blo 2027435 2028071 := bstep (se 1 (by rfl) ⟨1521053, by rfl⟩ : syracuseStep 2028071 = 3042107) B3042107
theorem B2281585 : Blo 2027435 2281585 := bbase (se 2 (by rfl) ⟨855594, by rfl⟩ : syracuseStep 2281585 = 1711189) (by norm_num)
theorem B3042113 : Blo 2027435 3042113 := bstep (se 2 (by rfl) ⟨1140792, by rfl⟩ : syracuseStep 3042113 = 2281585) B2281585
theorem B2028075 : Blo 2027435 2028075 := bstep (se 1 (by rfl) ⟨1521056, by rfl⟩ : syracuseStep 2028075 = 3042113) B3042113
theorem B4111501 : Blo 2027435 4111501 := bbase (se 3 (by rfl) ⟨770906, by rfl⟩ : syracuseStep 4111501 = 1541813) (by norm_num)
theorem B5482001 : Blo 2027435 5482001 := bstep (se 2 (by rfl) ⟨2055750, by rfl⟩ : syracuseStep 5482001 = 4111501) B4111501
theorem B3654667 : Blo 2027435 3654667 := bstep (se 1 (by rfl) ⟨2741000, by rfl⟩ : syracuseStep 3654667 = 5482001) B5482001
theorem B4872889 : Blo 2027435 4872889 := bstep (se 2 (by rfl) ⟨1827333, by rfl⟩ : syracuseStep 4872889 = 3654667) B3654667
theorem B6497185 : Blo 2027435 6497185 := bstep (se 2 (by rfl) ⟨2436444, by rfl⟩ : syracuseStep 6497185 = 4872889) B4872889
theorem B8662913 : Blo 2027435 8662913 := bstep (se 2 (by rfl) ⟨3248592, by rfl⟩ : syracuseStep 8662913 = 6497185) B6497185
theorem B5775275 : Blo 2027435 5775275 := bstep (se 1 (by rfl) ⟨4331456, by rfl⟩ : syracuseStep 5775275 = 8662913) B8662913
theorem B3850183 : Blo 2027435 3850183 := bstep (se 1 (by rfl) ⟨2887637, by rfl⟩ : syracuseStep 3850183 = 5775275) B5775275
theorem B5133577 : Blo 2027435 5133577 := bstep (se 2 (by rfl) ⟨1925091, by rfl⟩ : syracuseStep 5133577 = 3850183) B3850183
theorem B6844769 : Blo 2027435 6844769 := bstep (se 2 (by rfl) ⟨2566788, by rfl⟩ : syracuseStep 6844769 = 5133577) B5133577
theorem B4563179 : Blo 2027435 4563179 := bstep (se 1 (by rfl) ⟨3422384, by rfl⟩ : syracuseStep 4563179 = 6844769) B6844769
theorem B3042119 : Blo 2027435 3042119 := bstep (se 1 (by rfl) ⟨2281589, by rfl⟩ : syracuseStep 3042119 = 4563179) B4563179
theorem B2028079 : Blo 2027435 2028079 := bstep (se 1 (by rfl) ⟨1521059, by rfl⟩ : syracuseStep 2028079 = 3042119) B3042119
theorem B3042125 : Blo 2027435 3042125 := bbase (se 3 (by rfl) ⟨570398, by rfl⟩ : syracuseStep 3042125 = 1140797) (by norm_num)
theorem B2028083 : Blo 2027435 2028083 := bstep (se 1 (by rfl) ⟨1521062, by rfl⟩ : syracuseStep 2028083 = 3042125) B3042125
theorem B4563197 : Blo 2027435 4563197 := bbase (se 3 (by rfl) ⟨855599, by rfl⟩ : syracuseStep 4563197 = 1711199) (by norm_num)
theorem B3042131 : Blo 2027435 3042131 := bstep (se 1 (by rfl) ⟨2281598, by rfl⟩ : syracuseStep 3042131 = 4563197) B4563197
theorem B2028087 : Blo 2027435 2028087 := bstep (se 1 (by rfl) ⟨1521065, by rfl⟩ : syracuseStep 2028087 = 3042131) B3042131
theorem B3422405 : Blo 2027435 3422405 := bbase (se 4 (by rfl) ⟨320850, by rfl⟩ : syracuseStep 3422405 = 641701) (by norm_num)
theorem B2281603 : Blo 2027435 2281603 := bstep (se 1 (by rfl) ⟨1711202, by rfl⟩ : syracuseStep 2281603 = 3422405) B3422405
theorem B3042137 : Blo 2027435 3042137 := bstep (se 2 (by rfl) ⟨1140801, by rfl⟩ : syracuseStep 3042137 = 2281603) B2281603
theorem B2028091 : Blo 2027435 2028091 := bstep (se 1 (by rfl) ⟨1521068, by rfl⟩ : syracuseStep 2028091 = 3042137) B3042137
theorem B15400853 : Blo 2027435 15400853 := bbase (se 6 (by rfl) ⟨360957, by rfl⟩ : syracuseStep 15400853 = 721915) (by norm_num)
theorem B10267235 : Blo 2027435 10267235 := bstep (se 1 (by rfl) ⟨7700426, by rfl⟩ : syracuseStep 10267235 = 15400853) B15400853
theorem B6844823 : Blo 2027435 6844823 := bstep (se 1 (by rfl) ⟨5133617, by rfl⟩ : syracuseStep 6844823 = 10267235) B10267235
theorem B4563215 : Blo 2027435 4563215 := bstep (se 1 (by rfl) ⟨3422411, by rfl⟩ : syracuseStep 4563215 = 6844823) B6844823
theorem B3042143 : Blo 2027435 3042143 := bstep (se 1 (by rfl) ⟨2281607, by rfl⟩ : syracuseStep 3042143 = 4563215) B4563215
theorem B2028095 : Blo 2027435 2028095 := bstep (se 1 (by rfl) ⟨1521071, by rfl⟩ : syracuseStep 2028095 = 3042143) B3042143
theorem B3042149 : Blo 2027435 3042149 := bbase (se 4 (by rfl) ⟨285201, by rfl⟩ : syracuseStep 3042149 = 570403) (by norm_num)
theorem B2028099 : Blo 2027435 2028099 := bstep (se 1 (by rfl) ⟨1521074, by rfl⟩ : syracuseStep 2028099 = 3042149) B3042149
theorem B3850229 : Blo 2027435 3850229 := bbase (se 5 (by rfl) ⟨180479, by rfl⟩ : syracuseStep 3850229 = 360959) (by norm_num)
theorem B2566819 : Blo 2027435 2566819 := bstep (se 1 (by rfl) ⟨1925114, by rfl⟩ : syracuseStep 2566819 = 3850229) B3850229
theorem B3422425 : Blo 2027435 3422425 := bstep (se 2 (by rfl) ⟨1283409, by rfl⟩ : syracuseStep 3422425 = 2566819) B2566819
theorem B4563233 : Blo 2027435 4563233 := bstep (se 2 (by rfl) ⟨1711212, by rfl⟩ : syracuseStep 4563233 = 3422425) B3422425
theorem B3042155 : Blo 2027435 3042155 := bstep (se 1 (by rfl) ⟨2281616, by rfl⟩ : syracuseStep 3042155 = 4563233) B4563233
theorem B2028103 : Blo 2027435 2028103 := bstep (se 1 (by rfl) ⟨1521077, by rfl⟩ : syracuseStep 2028103 = 3042155) B3042155
theorem B2281621 : Blo 2027435 2281621 := bbase (se 6 (by rfl) ⟨53475, by rfl⟩ : syracuseStep 2281621 = 106951) (by norm_num)
theorem B3042161 : Blo 2027435 3042161 := bstep (se 2 (by rfl) ⟨1140810, by rfl⟩ : syracuseStep 3042161 = 2281621) B2281621
theorem B2028107 : Blo 2027435 2028107 := bstep (se 1 (by rfl) ⟨1521080, by rfl⟩ : syracuseStep 2028107 = 3042161) B3042161
theorem B2566829 : Blo 2027435 2566829 := bbase (se 3 (by rfl) ⟨481280, by rfl⟩ : syracuseStep 2566829 = 962561) (by norm_num)
theorem B6844877 : Blo 2027435 6844877 := bstep (se 3 (by rfl) ⟨1283414, by rfl⟩ : syracuseStep 6844877 = 2566829) B2566829
theorem B4563251 : Blo 2027435 4563251 := bstep (se 1 (by rfl) ⟨3422438, by rfl⟩ : syracuseStep 4563251 = 6844877) B6844877
theorem B3042167 : Blo 2027435 3042167 := bstep (se 1 (by rfl) ⟨2281625, by rfl⟩ : syracuseStep 3042167 = 4563251) B4563251
theorem B2028111 : Blo 2027435 2028111 := bstep (se 1 (by rfl) ⟨1521083, by rfl⟩ : syracuseStep 2028111 = 3042167) B3042167
theorem B3042173 : Blo 2027435 3042173 := bbase (se 3 (by rfl) ⟨570407, by rfl⟩ : syracuseStep 3042173 = 1140815) (by norm_num)
theorem B2028115 : Blo 2027435 2028115 := bstep (se 1 (by rfl) ⟨1521086, by rfl⟩ : syracuseStep 2028115 = 3042173) B3042173
theorem B4563269 : Blo 2027435 4563269 := bbase (se 4 (by rfl) ⟨427806, by rfl⟩ : syracuseStep 4563269 = 855613) (by norm_num)
theorem B3042179 : Blo 2027435 3042179 := bstep (se 1 (by rfl) ⟨2281634, by rfl⟩ : syracuseStep 3042179 = 4563269) B4563269
theorem B2028119 : Blo 2027435 2028119 := bstep (se 1 (by rfl) ⟨1521089, by rfl⟩ : syracuseStep 2028119 = 3042179) B3042179
theorem B6938309 : Blo 2027435 6938309 := bbase (se 4 (by rfl) ⟨650466, by rfl⟩ : syracuseStep 6938309 = 1300933) (by norm_num)
theorem B18502157 : Blo 2027435 18502157 := bstep (se 3 (by rfl) ⟨3469154, by rfl⟩ : syracuseStep 18502157 = 6938309) B6938309
theorem B12334771 : Blo 2027435 12334771 := bstep (se 1 (by rfl) ⟨9251078, by rfl⟩ : syracuseStep 12334771 = 18502157) B18502157
theorem B16446361 : Blo 2027435 16446361 := bstep (se 2 (by rfl) ⟨6167385, by rfl⟩ : syracuseStep 16446361 = 12334771) B12334771
theorem B21928481 : Blo 2027435 21928481 := bstep (se 2 (by rfl) ⟨8223180, by rfl⟩ : syracuseStep 21928481 = 16446361) B16446361
theorem B14618987 : Blo 2027435 14618987 := bstep (se 1 (by rfl) ⟨10964240, by rfl⟩ : syracuseStep 14618987 = 21928481) B21928481
theorem B9745991 : Blo 2027435 9745991 := bstep (se 1 (by rfl) ⟨7309493, by rfl⟩ : syracuseStep 9745991 = 14618987) B14618987
theorem B6497327 : Blo 2027435 6497327 := bstep (se 1 (by rfl) ⟨4872995, by rfl⟩ : syracuseStep 6497327 = 9745991) B9745991
theorem B4331551 : Blo 2027435 4331551 := bstep (se 1 (by rfl) ⟨3248663, by rfl⟩ : syracuseStep 4331551 = 6497327) B6497327
theorem B5775401 : Blo 2027435 5775401 := bstep (se 2 (by rfl) ⟨2165775, by rfl⟩ : syracuseStep 5775401 = 4331551) B4331551
theorem B3850267 : Blo 2027435 3850267 := bstep (se 1 (by rfl) ⟨2887700, by rfl⟩ : syracuseStep 3850267 = 5775401) B5775401
theorem B5133689 : Blo 2027435 5133689 := bstep (se 2 (by rfl) ⟨1925133, by rfl⟩ : syracuseStep 5133689 = 3850267) B3850267
theorem B3422459 : Blo 2027435 3422459 := bstep (se 1 (by rfl) ⟨2566844, by rfl⟩ : syracuseStep 3422459 = 5133689) B5133689
theorem B2281639 : Blo 2027435 2281639 := bstep (se 1 (by rfl) ⟨1711229, by rfl⟩ : syracuseStep 2281639 = 3422459) B3422459
theorem B3042185 : Blo 2027435 3042185 := bstep (se 2 (by rfl) ⟨1140819, by rfl⟩ : syracuseStep 3042185 = 2281639) B2281639
theorem B2028123 : Blo 2027435 2028123 := bstep (se 1 (by rfl) ⟨1521092, by rfl⟩ : syracuseStep 2028123 = 3042185) B3042185
theorem B10267397 : Blo 2027435 10267397 := bbase (se 4 (by rfl) ⟨962568, by rfl⟩ : syracuseStep 10267397 = 1925137) (by norm_num)
theorem B6844931 : Blo 2027435 6844931 := bstep (se 1 (by rfl) ⟨5133698, by rfl⟩ : syracuseStep 6844931 = 10267397) B10267397
theorem B4563287 : Blo 2027435 4563287 := bstep (se 1 (by rfl) ⟨3422465, by rfl⟩ : syracuseStep 4563287 = 6844931) B6844931
theorem B3042191 : Blo 2027435 3042191 := bstep (se 1 (by rfl) ⟨2281643, by rfl⟩ : syracuseStep 3042191 = 4563287) B4563287
theorem B2028127 : Blo 2027435 2028127 := bstep (se 1 (by rfl) ⟨1521095, by rfl⟩ : syracuseStep 2028127 = 3042191) B3042191
theorem B3042197 : Blo 2027435 3042197 := bbase (se 6 (by rfl) ⟨71301, by rfl⟩ : syracuseStep 3042197 = 142603) (by norm_num)
theorem B2028131 : Blo 2027435 2028131 := bstep (se 1 (by rfl) ⟨1521098, by rfl⟩ : syracuseStep 2028131 = 3042197) B3042197
theorem B11550869 : Blo 2027435 11550869 := bbase (se 6 (by rfl) ⟨270723, by rfl⟩ : syracuseStep 11550869 = 541447) (by norm_num)
theorem B7700579 : Blo 2027435 7700579 := bstep (se 1 (by rfl) ⟨5775434, by rfl⟩ : syracuseStep 7700579 = 11550869) B11550869
theorem B5133719 : Blo 2027435 5133719 := bstep (se 1 (by rfl) ⟨3850289, by rfl⟩ : syracuseStep 5133719 = 7700579) B7700579
theorem B3422479 : Blo 2027435 3422479 := bstep (se 1 (by rfl) ⟨2566859, by rfl⟩ : syracuseStep 3422479 = 5133719) B5133719
theorem B4563305 : Blo 2027435 4563305 := bstep (se 2 (by rfl) ⟨1711239, by rfl⟩ : syracuseStep 4563305 = 3422479) B3422479
theorem B3042203 : Blo 2027435 3042203 := bstep (se 1 (by rfl) ⟨2281652, by rfl⟩ : syracuseStep 3042203 = 4563305) B4563305
theorem B2028135 : Blo 2027435 2028135 := bstep (se 1 (by rfl) ⟨1521101, by rfl⟩ : syracuseStep 2028135 = 3042203) B3042203
theorem B2281657 : Blo 2027435 2281657 := bbase (se 2 (by rfl) ⟨855621, by rfl⟩ : syracuseStep 2281657 = 1711243) (by norm_num)
theorem B3042209 : Blo 2027435 3042209 := bstep (se 2 (by rfl) ⟨1140828, by rfl⟩ : syracuseStep 3042209 = 2281657) B2281657
theorem B2028139 : Blo 2027435 2028139 := bstep (se 1 (by rfl) ⟨1521104, by rfl⟩ : syracuseStep 2028139 = 3042209) B3042209
theorem B13876757 : Blo 2027435 13876757 := bbase (se 6 (by rfl) ⟨325236, by rfl⟩ : syracuseStep 13876757 = 650473) (by norm_num)
theorem B9251171 : Blo 2027435 9251171 := bstep (se 1 (by rfl) ⟨6938378, by rfl⟩ : syracuseStep 9251171 = 13876757) B13876757
theorem B6167447 : Blo 2027435 6167447 := bstep (se 1 (by rfl) ⟨4625585, by rfl⟩ : syracuseStep 6167447 = 9251171) B9251171
theorem B4111631 : Blo 2027435 4111631 := bstep (se 1 (by rfl) ⟨3083723, by rfl⟩ : syracuseStep 4111631 = 6167447) B6167447
theorem B2741087 : Blo 2027435 2741087 := bstep (se 1 (by rfl) ⟨2055815, by rfl⟩ : syracuseStep 2741087 = 4111631) B4111631
theorem B7309565 : Blo 2027435 7309565 := bstep (se 3 (by rfl) ⟨1370543, by rfl⟩ : syracuseStep 7309565 = 2741087) B2741087
theorem B4873043 : Blo 2027435 4873043 := bstep (se 1 (by rfl) ⟨3654782, by rfl⟩ : syracuseStep 4873043 = 7309565) B7309565
theorem B3248695 : Blo 2027435 3248695 := bstep (se 1 (by rfl) ⟨2436521, by rfl⟩ : syracuseStep 3248695 = 4873043) B4873043
theorem B4331593 : Blo 2027435 4331593 := bstep (se 2 (by rfl) ⟨1624347, by rfl⟩ : syracuseStep 4331593 = 3248695) B3248695
theorem B5775457 : Blo 2027435 5775457 := bstep (se 2 (by rfl) ⟨2165796, by rfl⟩ : syracuseStep 5775457 = 4331593) B4331593
theorem B7700609 : Blo 2027435 7700609 := bstep (se 2 (by rfl) ⟨2887728, by rfl⟩ : syracuseStep 7700609 = 5775457) B5775457
theorem B5133739 : Blo 2027435 5133739 := bstep (se 1 (by rfl) ⟨3850304, by rfl⟩ : syracuseStep 5133739 = 7700609) B7700609
theorem B6844985 : Blo 2027435 6844985 := bstep (se 2 (by rfl) ⟨2566869, by rfl⟩ : syracuseStep 6844985 = 5133739) B5133739
theorem B4563323 : Blo 2027435 4563323 := bstep (se 1 (by rfl) ⟨3422492, by rfl⟩ : syracuseStep 4563323 = 6844985) B6844985
theorem B3042215 : Blo 2027435 3042215 := bstep (se 1 (by rfl) ⟨2281661, by rfl⟩ : syracuseStep 3042215 = 4563323) B4563323
theorem B2028143 : Blo 2027435 2028143 := bstep (se 1 (by rfl) ⟨1521107, by rfl⟩ : syracuseStep 2028143 = 3042215) B3042215
theorem B3042221 : Blo 2027435 3042221 := bbase (se 3 (by rfl) ⟨570416, by rfl⟩ : syracuseStep 3042221 = 1140833) (by norm_num)
theorem B2028147 : Blo 2027435 2028147 := bstep (se 1 (by rfl) ⟨1521110, by rfl⟩ : syracuseStep 2028147 = 3042221) B3042221
theorem B4563341 : Blo 2027435 4563341 := bbase (se 3 (by rfl) ⟨855626, by rfl⟩ : syracuseStep 4563341 = 1711253) (by norm_num)
theorem B3042227 : Blo 2027435 3042227 := bstep (se 1 (by rfl) ⟨2281670, by rfl⟩ : syracuseStep 3042227 = 4563341) B4563341
theorem B2028151 : Blo 2027435 2028151 := bstep (se 1 (by rfl) ⟨1521113, by rfl⟩ : syracuseStep 2028151 = 3042227) B3042227
theorem B2566885 : Blo 2027435 2566885 := bbase (se 4 (by rfl) ⟨240645, by rfl⟩ : syracuseStep 2566885 = 481291) (by norm_num)
theorem B3422513 : Blo 2027435 3422513 := bstep (se 2 (by rfl) ⟨1283442, by rfl⟩ : syracuseStep 3422513 = 2566885) B2566885
theorem B2281675 : Blo 2027435 2281675 := bstep (se 1 (by rfl) ⟨1711256, by rfl⟩ : syracuseStep 2281675 = 3422513) B3422513
theorem B3042233 : Blo 2027435 3042233 := bstep (se 2 (by rfl) ⟨1140837, by rfl⟩ : syracuseStep 3042233 = 2281675) B2281675
theorem B2028155 : Blo 2027435 2028155 := bstep (se 1 (by rfl) ⟨1521116, by rfl⟩ : syracuseStep 2028155 = 3042233) B3042233
theorem B17562901 : Blo 2027435 17562901 := bbase (se 6 (by rfl) ⟨411630, by rfl⟩ : syracuseStep 17562901 = 823261) (by norm_num)
theorem B23417201 : Blo 2027435 23417201 := bstep (se 2 (by rfl) ⟨8781450, by rfl⟩ : syracuseStep 23417201 = 17562901) B17562901
theorem B15611467 : Blo 2027435 15611467 := bstep (se 1 (by rfl) ⟨11708600, by rfl⟩ : syracuseStep 15611467 = 23417201) B23417201
theorem B20815289 : Blo 2027435 20815289 := bstep (se 2 (by rfl) ⟨7805733, by rfl⟩ : syracuseStep 20815289 = 15611467) B15611467
theorem B13876859 : Blo 2027435 13876859 := bstep (se 1 (by rfl) ⟨10407644, by rfl⟩ : syracuseStep 13876859 = 20815289) B20815289
theorem B37004957 : Blo 2027435 37004957 := bstep (se 3 (by rfl) ⟨6938429, by rfl⟩ : syracuseStep 37004957 = 13876859) B13876859
theorem B24669971 : Blo 2027435 24669971 := bstep (se 1 (by rfl) ⟨18502478, by rfl⟩ : syracuseStep 24669971 = 37004957) B37004957
theorem B16446647 : Blo 2027435 16446647 := bstep (se 1 (by rfl) ⟨12334985, by rfl⟩ : syracuseStep 16446647 = 24669971) B24669971
theorem B10964431 : Blo 2027435 10964431 := bstep (se 1 (by rfl) ⟨8223323, by rfl⟩ : syracuseStep 10964431 = 16446647) B16446647
theorem B14619241 : Blo 2027435 14619241 := bstep (se 2 (by rfl) ⟨5482215, by rfl⟩ : syracuseStep 14619241 = 10964431) B10964431
theorem B19492321 : Blo 2027435 19492321 := bstep (se 2 (by rfl) ⟨7309620, by rfl⟩ : syracuseStep 19492321 = 14619241) B14619241
theorem B25989761 : Blo 2027435 25989761 := bstep (se 2 (by rfl) ⟨9746160, by rfl⟩ : syracuseStep 25989761 = 19492321) B19492321
theorem B17326507 : Blo 2027435 17326507 := bstep (se 1 (by rfl) ⟨12994880, by rfl⟩ : syracuseStep 17326507 = 25989761) B25989761
theorem B23102009 : Blo 2027435 23102009 := bstep (se 2 (by rfl) ⟨8663253, by rfl⟩ : syracuseStep 23102009 = 17326507) B17326507
theorem B15401339 : Blo 2027435 15401339 := bstep (se 1 (by rfl) ⟨11551004, by rfl⟩ : syracuseStep 15401339 = 23102009) B23102009
theorem B10267559 : Blo 2027435 10267559 := bstep (se 1 (by rfl) ⟨7700669, by rfl⟩ : syracuseStep 10267559 = 15401339) B15401339
theorem B6845039 : Blo 2027435 6845039 := bstep (se 1 (by rfl) ⟨5133779, by rfl⟩ : syracuseStep 6845039 = 10267559) B10267559
theorem B4563359 : Blo 2027435 4563359 := bstep (se 1 (by rfl) ⟨3422519, by rfl⟩ : syracuseStep 4563359 = 6845039) B6845039
theorem B3042239 : Blo 2027435 3042239 := bstep (se 1 (by rfl) ⟨2281679, by rfl⟩ : syracuseStep 3042239 = 4563359) B4563359
theorem B2028159 : Blo 2027435 2028159 := bstep (se 1 (by rfl) ⟨1521119, by rfl⟩ : syracuseStep 2028159 = 3042239) B3042239
theorem B3042245 : Blo 2027435 3042245 := bbase (se 4 (by rfl) ⟨285210, by rfl⟩ : syracuseStep 3042245 = 570421) (by norm_num)
theorem B2028163 : Blo 2027435 2028163 := bstep (se 1 (by rfl) ⟨1521122, by rfl⟩ : syracuseStep 2028163 = 3042245) B3042245
theorem B3422533 : Blo 2027435 3422533 := bbase (se 4 (by rfl) ⟨320862, by rfl⟩ : syracuseStep 3422533 = 641725) (by norm_num)
theorem B4563377 : Blo 2027435 4563377 := bstep (se 2 (by rfl) ⟨1711266, by rfl⟩ : syracuseStep 4563377 = 3422533) B3422533
theorem B3042251 : Blo 2027435 3042251 := bstep (se 1 (by rfl) ⟨2281688, by rfl⟩ : syracuseStep 3042251 = 4563377) B4563377
theorem B2028167 : Blo 2027435 2028167 := bstep (se 1 (by rfl) ⟨1521125, by rfl⟩ : syracuseStep 2028167 = 3042251) B3042251
theorem B2281693 : Blo 2027435 2281693 := bbase (se 3 (by rfl) ⟨427817, by rfl⟩ : syracuseStep 2281693 = 855635) (by norm_num)
theorem B3042257 : Blo 2027435 3042257 := bstep (se 2 (by rfl) ⟨1140846, by rfl⟩ : syracuseStep 3042257 = 2281693) B2281693
theorem B2028171 : Blo 2027435 2028171 := bstep (se 1 (by rfl) ⟨1521128, by rfl⟩ : syracuseStep 2028171 = 3042257) B3042257
theorem B6845093 : Blo 2027435 6845093 := bbase (se 4 (by rfl) ⟨641727, by rfl⟩ : syracuseStep 6845093 = 1283455) (by norm_num)
theorem B4563395 : Blo 2027435 4563395 := bstep (se 1 (by rfl) ⟨3422546, by rfl⟩ : syracuseStep 4563395 = 6845093) B6845093
theorem B3042263 : Blo 2027435 3042263 := bstep (se 1 (by rfl) ⟨2281697, by rfl⟩ : syracuseStep 3042263 = 4563395) B4563395
theorem B2028175 : Blo 2027435 2028175 := bstep (se 1 (by rfl) ⟨1521131, by rfl⟩ : syracuseStep 2028175 = 3042263) B3042263
theorem B3042269 : Blo 2027435 3042269 := bbase (se 3 (by rfl) ⟨570425, by rfl⟩ : syracuseStep 3042269 = 1140851) (by norm_num)
theorem B2028179 : Blo 2027435 2028179 := bstep (se 1 (by rfl) ⟨1521134, by rfl⟩ : syracuseStep 2028179 = 3042269) B3042269
theorem B4563413 : Blo 2027435 4563413 := bbase (se 7 (by rfl) ⟨53477, by rfl⟩ : syracuseStep 4563413 = 106955) (by norm_num)
theorem B3042275 : Blo 2027435 3042275 := bstep (se 1 (by rfl) ⟨2281706, by rfl⟩ : syracuseStep 3042275 = 4563413) B4563413
theorem B2028183 : Blo 2027435 2028183 := bstep (se 1 (by rfl) ⟨1521137, by rfl⟩ : syracuseStep 2028183 = 3042275) B3042275
theorem B4450693 : Blo 2027435 4450693 := bbase (se 4 (by rfl) ⟨417252, by rfl⟩ : syracuseStep 4450693 = 834505) (by norm_num)
theorem B5934257 : Blo 2027435 5934257 := bstep (se 2 (by rfl) ⟨2225346, by rfl⟩ : syracuseStep 5934257 = 4450693) B4450693
theorem B3956171 : Blo 2027435 3956171 := bstep (se 1 (by rfl) ⟨2967128, by rfl⟩ : syracuseStep 3956171 = 5934257) B5934257
theorem B42199157 : Blo 2027435 42199157 := bstep (se 5 (by rfl) ⟨1978085, by rfl⟩ : syracuseStep 42199157 = 3956171) B3956171
theorem B28132771 : Blo 2027435 28132771 := bstep (se 1 (by rfl) ⟨21099578, by rfl⟩ : syracuseStep 28132771 = 42199157) B42199157
theorem B37510361 : Blo 2027435 37510361 := bstep (se 2 (by rfl) ⟨14066385, by rfl⟩ : syracuseStep 37510361 = 28132771) B28132771
theorem B25006907 : Blo 2027435 25006907 := bstep (se 1 (by rfl) ⟨18755180, by rfl⟩ : syracuseStep 25006907 = 37510361) B37510361
theorem B16671271 : Blo 2027435 16671271 := bstep (se 1 (by rfl) ⟨12503453, by rfl⟩ : syracuseStep 16671271 = 25006907) B25006907
theorem B22228361 : Blo 2027435 22228361 := bstep (se 2 (by rfl) ⟨8335635, by rfl⟩ : syracuseStep 22228361 = 16671271) B16671271
theorem B14818907 : Blo 2027435 14818907 := bstep (se 1 (by rfl) ⟨11114180, by rfl⟩ : syracuseStep 14818907 = 22228361) B22228361
theorem B39517085 : Blo 2027435 39517085 := bstep (se 3 (by rfl) ⟨7409453, by rfl⟩ : syracuseStep 39517085 = 14818907) B14818907
theorem B26344723 : Blo 2027435 26344723 := bstep (se 1 (by rfl) ⟨19758542, by rfl⟩ : syracuseStep 26344723 = 39517085) B39517085
theorem B35126297 : Blo 2027435 35126297 := bstep (se 2 (by rfl) ⟨13172361, by rfl⟩ : syracuseStep 35126297 = 26344723) B26344723
theorem B23417531 : Blo 2027435 23417531 := bstep (se 1 (by rfl) ⟨17563148, by rfl⟩ : syracuseStep 23417531 = 35126297) B35126297
theorem B15611687 : Blo 2027435 15611687 := bstep (se 1 (by rfl) ⟨11708765, by rfl⟩ : syracuseStep 15611687 = 23417531) B23417531
theorem B10407791 : Blo 2027435 10407791 := bstep (se 1 (by rfl) ⟨7805843, by rfl⟩ : syracuseStep 10407791 = 15611687) B15611687
theorem B27754109 : Blo 2027435 27754109 := bstep (se 3 (by rfl) ⟨5203895, by rfl⟩ : syracuseStep 27754109 = 10407791) B10407791
theorem B18502739 : Blo 2027435 18502739 := bstep (se 1 (by rfl) ⟨13877054, by rfl⟩ : syracuseStep 18502739 = 27754109) B27754109
theorem B12335159 : Blo 2027435 12335159 := bstep (se 1 (by rfl) ⟨9251369, by rfl⟩ : syracuseStep 12335159 = 18502739) B18502739
theorem B8223439 : Blo 2027435 8223439 := bstep (se 1 (by rfl) ⟨6167579, by rfl⟩ : syracuseStep 8223439 = 12335159) B12335159
theorem B10964585 : Blo 2027435 10964585 := bstep (se 2 (by rfl) ⟨4111719, by rfl⟩ : syracuseStep 10964585 = 8223439) B8223439
theorem B29238893 : Blo 2027435 29238893 := bstep (se 3 (by rfl) ⟨5482292, by rfl⟩ : syracuseStep 29238893 = 10964585) B10964585
theorem B19492595 : Blo 2027435 19492595 := bstep (se 1 (by rfl) ⟨14619446, by rfl⟩ : syracuseStep 19492595 = 29238893) B29238893
theorem B12995063 : Blo 2027435 12995063 := bstep (se 1 (by rfl) ⟨9746297, by rfl⟩ : syracuseStep 12995063 = 19492595) B19492595
theorem B8663375 : Blo 2027435 8663375 := bstep (se 1 (by rfl) ⟨6497531, by rfl⟩ : syracuseStep 8663375 = 12995063) B12995063
theorem B5775583 : Blo 2027435 5775583 := bstep (se 1 (by rfl) ⟨4331687, by rfl⟩ : syracuseStep 5775583 = 8663375) B8663375
theorem B7700777 : Blo 2027435 7700777 := bstep (se 2 (by rfl) ⟨2887791, by rfl⟩ : syracuseStep 7700777 = 5775583) B5775583
theorem B5133851 : Blo 2027435 5133851 := bstep (se 1 (by rfl) ⟨3850388, by rfl⟩ : syracuseStep 5133851 = 7700777) B7700777
theorem B3422567 : Blo 2027435 3422567 := bstep (se 1 (by rfl) ⟨2566925, by rfl⟩ : syracuseStep 3422567 = 5133851) B5133851
theorem B2281711 : Blo 2027435 2281711 := bstep (se 1 (by rfl) ⟨1711283, by rfl⟩ : syracuseStep 2281711 = 3422567) B3422567
theorem B3042281 : Blo 2027435 3042281 := bstep (se 2 (by rfl) ⟨1140855, by rfl⟩ : syracuseStep 3042281 = 2281711) B2281711
theorem B2028187 : Blo 2027435 2028187 := bstep (se 1 (by rfl) ⟨1521140, by rfl⟩ : syracuseStep 2028187 = 3042281) B3042281
theorem B2927197 : Blo 2027435 2927197 := bbase (se 3 (by rfl) ⟨548849, by rfl⟩ : syracuseStep 2927197 = 1097699) (by norm_num)
theorem B15611717 : Blo 2027435 15611717 := bstep (se 4 (by rfl) ⟨1463598, by rfl⟩ : syracuseStep 15611717 = 2927197) B2927197
theorem B10407811 : Blo 2027435 10407811 := bstep (se 1 (by rfl) ⟨7805858, by rfl⟩ : syracuseStep 10407811 = 15611717) B15611717
theorem B13877081 : Blo 2027435 13877081 := bstep (se 2 (by rfl) ⟨5203905, by rfl⟩ : syracuseStep 13877081 = 10407811) B10407811
theorem B9251387 : Blo 2027435 9251387 := bstep (se 1 (by rfl) ⟨6938540, by rfl⟩ : syracuseStep 9251387 = 13877081) B13877081
theorem B6167591 : Blo 2027435 6167591 := bstep (se 1 (by rfl) ⟨4625693, by rfl⟩ : syracuseStep 6167591 = 9251387) B9251387
theorem B4111727 : Blo 2027435 4111727 := bstep (se 1 (by rfl) ⟨3083795, by rfl⟩ : syracuseStep 4111727 = 6167591) B6167591
theorem B10964605 : Blo 2027435 10964605 := bstep (se 3 (by rfl) ⟨2055863, by rfl⟩ : syracuseStep 10964605 = 4111727) B4111727
theorem B14619473 : Blo 2027435 14619473 := bstep (se 2 (by rfl) ⟨5482302, by rfl⟩ : syracuseStep 14619473 = 10964605) B10964605
theorem B9746315 : Blo 2027435 9746315 := bstep (se 1 (by rfl) ⟨7309736, by rfl⟩ : syracuseStep 9746315 = 14619473) B14619473
theorem B6497543 : Blo 2027435 6497543 := bstep (se 1 (by rfl) ⟨4873157, by rfl⟩ : syracuseStep 6497543 = 9746315) B9746315
theorem B17326781 : Blo 2027435 17326781 := bstep (se 3 (by rfl) ⟨3248771, by rfl⟩ : syracuseStep 17326781 = 6497543) B6497543
theorem B11551187 : Blo 2027435 11551187 := bstep (se 1 (by rfl) ⟨8663390, by rfl⟩ : syracuseStep 11551187 = 17326781) B17326781
theorem B7700791 : Blo 2027435 7700791 := bstep (se 1 (by rfl) ⟨5775593, by rfl⟩ : syracuseStep 7700791 = 11551187) B11551187
theorem B10267721 : Blo 2027435 10267721 := bstep (se 2 (by rfl) ⟨3850395, by rfl⟩ : syracuseStep 10267721 = 7700791) B7700791
theorem B6845147 : Blo 2027435 6845147 := bstep (se 1 (by rfl) ⟨5133860, by rfl⟩ : syracuseStep 6845147 = 10267721) B10267721
theorem B4563431 : Blo 2027435 4563431 := bstep (se 1 (by rfl) ⟨3422573, by rfl⟩ : syracuseStep 4563431 = 6845147) B6845147
theorem B3042287 : Blo 2027435 3042287 := bstep (se 1 (by rfl) ⟨2281715, by rfl⟩ : syracuseStep 3042287 = 4563431) B4563431
theorem B2028191 : Blo 2027435 2028191 := bstep (se 1 (by rfl) ⟨1521143, by rfl⟩ : syracuseStep 2028191 = 3042287) B3042287
theorem B3042293 : Blo 2027435 3042293 := bbase (se 5 (by rfl) ⟨142607, by rfl⟩ : syracuseStep 3042293 = 285215) (by norm_num)
theorem B2028195 : Blo 2027435 2028195 := bstep (se 1 (by rfl) ⟨1521146, by rfl⟩ : syracuseStep 2028195 = 3042293) B3042293
theorem B2436589 : Blo 2027435 2436589 := bbase (se 3 (by rfl) ⟨456860, by rfl⟩ : syracuseStep 2436589 = 913721) (by norm_num)
theorem B3248785 : Blo 2027435 3248785 := bstep (se 2 (by rfl) ⟨1218294, by rfl⟩ : syracuseStep 3248785 = 2436589) B2436589
theorem B4331713 : Blo 2027435 4331713 := bstep (se 2 (by rfl) ⟨1624392, by rfl⟩ : syracuseStep 4331713 = 3248785) B3248785
theorem B5775617 : Blo 2027435 5775617 := bstep (se 2 (by rfl) ⟨2165856, by rfl⟩ : syracuseStep 5775617 = 4331713) B4331713
theorem B3850411 : Blo 2027435 3850411 := bstep (se 1 (by rfl) ⟨2887808, by rfl⟩ : syracuseStep 3850411 = 5775617) B5775617
theorem B5133881 : Blo 2027435 5133881 := bstep (se 2 (by rfl) ⟨1925205, by rfl⟩ : syracuseStep 5133881 = 3850411) B3850411
theorem B3422587 : Blo 2027435 3422587 := bstep (se 1 (by rfl) ⟨2566940, by rfl⟩ : syracuseStep 3422587 = 5133881) B5133881
theorem B4563449 : Blo 2027435 4563449 := bstep (se 2 (by rfl) ⟨1711293, by rfl⟩ : syracuseStep 4563449 = 3422587) B3422587
theorem B3042299 : Blo 2027435 3042299 := bstep (se 1 (by rfl) ⟨2281724, by rfl⟩ : syracuseStep 3042299 = 4563449) B4563449
theorem B2028199 : Blo 2027435 2028199 := bstep (se 1 (by rfl) ⟨1521149, by rfl⟩ : syracuseStep 2028199 = 3042299) B3042299
theorem B2281729 : Blo 2027435 2281729 := bbase (se 2 (by rfl) ⟨855648, by rfl⟩ : syracuseStep 2281729 = 1711297) (by norm_num)
theorem B3042305 : Blo 2027435 3042305 := bstep (se 2 (by rfl) ⟨1140864, by rfl⟩ : syracuseStep 3042305 = 2281729) B2281729
theorem B2028203 : Blo 2027435 2028203 := bstep (se 1 (by rfl) ⟨1521152, by rfl⟩ : syracuseStep 2028203 = 3042305) B3042305
theorem B5133901 : Blo 2027435 5133901 := bbase (se 3 (by rfl) ⟨962606, by rfl⟩ : syracuseStep 5133901 = 1925213) (by norm_num)
theorem B6845201 : Blo 2027435 6845201 := bstep (se 2 (by rfl) ⟨2566950, by rfl⟩ : syracuseStep 6845201 = 5133901) B5133901
theorem B4563467 : Blo 2027435 4563467 := bstep (se 1 (by rfl) ⟨3422600, by rfl⟩ : syracuseStep 4563467 = 6845201) B6845201
theorem B3042311 : Blo 2027435 3042311 := bstep (se 1 (by rfl) ⟨2281733, by rfl⟩ : syracuseStep 3042311 = 4563467) B4563467
theorem B2028207 : Blo 2027435 2028207 := bstep (se 1 (by rfl) ⟨1521155, by rfl⟩ : syracuseStep 2028207 = 3042311) B3042311
theorem B3042317 : Blo 2027435 3042317 := bbase (se 3 (by rfl) ⟨570434, by rfl⟩ : syracuseStep 3042317 = 1140869) (by norm_num)
theorem B2028211 : Blo 2027435 2028211 := bstep (se 1 (by rfl) ⟨1521158, by rfl⟩ : syracuseStep 2028211 = 3042317) B3042317
theorem B4563485 : Blo 2027435 4563485 := bbase (se 3 (by rfl) ⟨855653, by rfl⟩ : syracuseStep 4563485 = 1711307) (by norm_num)
theorem B3042323 : Blo 2027435 3042323 := bstep (se 1 (by rfl) ⟨2281742, by rfl⟩ : syracuseStep 3042323 = 4563485) B4563485
theorem B2028215 : Blo 2027435 2028215 := bstep (se 1 (by rfl) ⟨1521161, by rfl⟩ : syracuseStep 2028215 = 3042323) B3042323
theorem B3422621 : Blo 2027435 3422621 := bbase (se 3 (by rfl) ⟨641741, by rfl⟩ : syracuseStep 3422621 = 1283483) (by norm_num)
theorem B2281747 : Blo 2027435 2281747 := bstep (se 1 (by rfl) ⟨1711310, by rfl⟩ : syracuseStep 2281747 = 3422621) B3422621
theorem B3042329 : Blo 2027435 3042329 := bstep (se 2 (by rfl) ⟨1140873, by rfl⟩ : syracuseStep 3042329 = 2281747) B2281747
theorem B2028219 : Blo 2027435 2028219 := bstep (se 1 (by rfl) ⟨1521164, by rfl⟩ : syracuseStep 2028219 = 3042329) B3042329
theorem B41631893 : Blo 2027435 41631893 := bbase (se 6 (by rfl) ⟨975747, by rfl⟩ : syracuseStep 41631893 = 1951495) (by norm_num)
theorem B27754595 : Blo 2027435 27754595 := bstep (se 1 (by rfl) ⟨20815946, by rfl⟩ : syracuseStep 27754595 = 41631893) B41631893
theorem B18503063 : Blo 2027435 18503063 := bstep (se 1 (by rfl) ⟨13877297, by rfl⟩ : syracuseStep 18503063 = 27754595) B27754595
theorem B12335375 : Blo 2027435 12335375 := bstep (se 1 (by rfl) ⟨9251531, by rfl⟩ : syracuseStep 12335375 = 18503063) B18503063
theorem B32894333 : Blo 2027435 32894333 := bstep (se 3 (by rfl) ⟨6167687, by rfl⟩ : syracuseStep 32894333 = 12335375) B12335375
theorem B21929555 : Blo 2027435 21929555 := bstep (se 1 (by rfl) ⟨16447166, by rfl⟩ : syracuseStep 21929555 = 32894333) B32894333
theorem B14619703 : Blo 2027435 14619703 := bstep (se 1 (by rfl) ⟨10964777, by rfl⟩ : syracuseStep 14619703 = 21929555) B21929555
theorem B19492937 : Blo 2027435 19492937 := bstep (se 2 (by rfl) ⟨7309851, by rfl⟩ : syracuseStep 19492937 = 14619703) B14619703
theorem B12995291 : Blo 2027435 12995291 := bstep (se 1 (by rfl) ⟨9746468, by rfl⟩ : syracuseStep 12995291 = 19492937) B19492937
theorem B8663527 : Blo 2027435 8663527 := bstep (se 1 (by rfl) ⟨6497645, by rfl⟩ : syracuseStep 8663527 = 12995291) B12995291
theorem B11551369 : Blo 2027435 11551369 := bstep (se 2 (by rfl) ⟨4331763, by rfl⟩ : syracuseStep 11551369 = 8663527) B8663527
theorem B15401825 : Blo 2027435 15401825 := bstep (se 2 (by rfl) ⟨5775684, by rfl⟩ : syracuseStep 15401825 = 11551369) B11551369
theorem B10267883 : Blo 2027435 10267883 := bstep (se 1 (by rfl) ⟨7700912, by rfl⟩ : syracuseStep 10267883 = 15401825) B15401825
theorem B6845255 : Blo 2027435 6845255 := bstep (se 1 (by rfl) ⟨5133941, by rfl⟩ : syracuseStep 6845255 = 10267883) B10267883
theorem B4563503 : Blo 2027435 4563503 := bstep (se 1 (by rfl) ⟨3422627, by rfl⟩ : syracuseStep 4563503 = 6845255) B6845255
theorem B3042335 : Blo 2027435 3042335 := bstep (se 1 (by rfl) ⟨2281751, by rfl⟩ : syracuseStep 3042335 = 4563503) B4563503
theorem B2028223 : Blo 2027435 2028223 := bstep (se 1 (by rfl) ⟨1521167, by rfl⟩ : syracuseStep 2028223 = 3042335) B3042335
theorem B3042341 : Blo 2027435 3042341 := bbase (se 4 (by rfl) ⟨285219, by rfl⟩ : syracuseStep 3042341 = 570439) (by norm_num)
theorem B2028227 : Blo 2027435 2028227 := bstep (se 1 (by rfl) ⟨1521170, by rfl⟩ : syracuseStep 2028227 = 3042341) B3042341
theorem B2566981 : Blo 2027435 2566981 := bbase (se 4 (by rfl) ⟨240654, by rfl⟩ : syracuseStep 2566981 = 481309) (by norm_num)
theorem B3422641 : Blo 2027435 3422641 := bstep (se 2 (by rfl) ⟨1283490, by rfl⟩ : syracuseStep 3422641 = 2566981) B2566981
theorem B4563521 : Blo 2027435 4563521 := bstep (se 2 (by rfl) ⟨1711320, by rfl⟩ : syracuseStep 4563521 = 3422641) B3422641
theorem B3042347 : Blo 2027435 3042347 := bstep (se 1 (by rfl) ⟨2281760, by rfl⟩ : syracuseStep 3042347 = 4563521) B4563521
theorem B2028231 : Blo 2027435 2028231 := bstep (se 1 (by rfl) ⟨1521173, by rfl⟩ : syracuseStep 2028231 = 3042347) B3042347
theorem B2281765 : Blo 2027435 2281765 := bbase (se 4 (by rfl) ⟨213915, by rfl⟩ : syracuseStep 2281765 = 427831) (by norm_num)
theorem B3042353 : Blo 2027435 3042353 := bstep (se 2 (by rfl) ⟨1140882, by rfl⟩ : syracuseStep 3042353 = 2281765) B2281765
theorem B2028235 : Blo 2027435 2028235 := bstep (se 1 (by rfl) ⟨1521176, by rfl⟩ : syracuseStep 2028235 = 3042353) B3042353
theorem B2436637 : Blo 2027435 2436637 := bbase (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) (by norm_num)
theorem B3248849 : Blo 2027435 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B8663597 : Blo 2027435 8663597 := bstep (se 3 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 8663597 = 3248849) B3248849
theorem B5775731 : Blo 2027435 5775731 := bstep (se 1 (by rfl) ⟨4331798, by rfl⟩ : syracuseStep 5775731 = 8663597) B8663597
theorem B3850487 : Blo 2027435 3850487 := bstep (se 1 (by rfl) ⟨2887865, by rfl⟩ : syracuseStep 3850487 = 5775731) B5775731
theorem B2566991 : Blo 2027435 2566991 := bstep (se 1 (by rfl) ⟨1925243, by rfl⟩ : syracuseStep 2566991 = 3850487) B3850487
theorem B6845309 : Blo 2027435 6845309 := bstep (se 3 (by rfl) ⟨1283495, by rfl⟩ : syracuseStep 6845309 = 2566991) B2566991
theorem B4563539 : Blo 2027435 4563539 := bstep (se 1 (by rfl) ⟨3422654, by rfl⟩ : syracuseStep 4563539 = 6845309) B6845309
theorem B3042359 : Blo 2027435 3042359 := bstep (se 1 (by rfl) ⟨2281769, by rfl⟩ : syracuseStep 3042359 = 4563539) B4563539
theorem B2028239 : Blo 2027435 2028239 := bstep (se 1 (by rfl) ⟨1521179, by rfl⟩ : syracuseStep 2028239 = 3042359) B3042359
theorem B3042365 : Blo 2027435 3042365 := bbase (se 3 (by rfl) ⟨570443, by rfl⟩ : syracuseStep 3042365 = 1140887) (by norm_num)
theorem B2028243 : Blo 2027435 2028243 := bstep (se 1 (by rfl) ⟨1521182, by rfl⟩ : syracuseStep 2028243 = 3042365) B3042365
theorem B4563557 : Blo 2027435 4563557 := bbase (se 4 (by rfl) ⟨427833, by rfl⟩ : syracuseStep 4563557 = 855667) (by norm_num)
theorem B3042371 : Blo 2027435 3042371 := bstep (se 1 (by rfl) ⟨2281778, by rfl⟩ : syracuseStep 3042371 = 4563557) B4563557
theorem B2028247 : Blo 2027435 2028247 := bstep (se 1 (by rfl) ⟨1521185, by rfl⟩ : syracuseStep 2028247 = 3042371) B3042371
theorem B5134013 : Blo 2027435 5134013 := bbase (se 3 (by rfl) ⟨962627, by rfl⟩ : syracuseStep 5134013 = 1925255) (by norm_num)
theorem B3422675 : Blo 2027435 3422675 := bstep (se 1 (by rfl) ⟨2567006, by rfl⟩ : syracuseStep 3422675 = 5134013) B5134013
theorem B2281783 : Blo 2027435 2281783 := bstep (se 1 (by rfl) ⟨1711337, by rfl⟩ : syracuseStep 2281783 = 3422675) B3422675
theorem B3042377 : Blo 2027435 3042377 := bstep (se 2 (by rfl) ⟨1140891, by rfl⟩ : syracuseStep 3042377 = 2281783) B2281783
theorem B2028251 : Blo 2027435 2028251 := bstep (se 1 (by rfl) ⟨1521188, by rfl⟩ : syracuseStep 2028251 = 3042377) B3042377
theorem B3850517 : Blo 2027435 3850517 := bbase (se 6 (by rfl) ⟨90246, by rfl⟩ : syracuseStep 3850517 = 180493) (by norm_num)
theorem B10268045 : Blo 2027435 10268045 := bstep (se 3 (by rfl) ⟨1925258, by rfl⟩ : syracuseStep 10268045 = 3850517) B3850517
theorem B6845363 : Blo 2027435 6845363 := bstep (se 1 (by rfl) ⟨5134022, by rfl⟩ : syracuseStep 6845363 = 10268045) B10268045
theorem B4563575 : Blo 2027435 4563575 := bstep (se 1 (by rfl) ⟨3422681, by rfl⟩ : syracuseStep 4563575 = 6845363) B6845363
theorem B3042383 : Blo 2027435 3042383 := bstep (se 1 (by rfl) ⟨2281787, by rfl⟩ : syracuseStep 3042383 = 4563575) B4563575
theorem B2028255 : Blo 2027435 2028255 := bstep (se 1 (by rfl) ⟨1521191, by rfl⟩ : syracuseStep 2028255 = 3042383) B3042383
theorem B3042389 : Blo 2027435 3042389 := bbase (se 8 (by rfl) ⟨17826, by rfl⟩ : syracuseStep 3042389 = 35653) (by norm_num)
theorem B2028259 : Blo 2027435 2028259 := bstep (se 1 (by rfl) ⟨1521194, by rfl⟩ : syracuseStep 2028259 = 3042389) B3042389
theorem B2055937 : Blo 2027435 2055937 := bbase (se 2 (by rfl) ⟨770976, by rfl⟩ : syracuseStep 2055937 = 1541953) (by norm_num)
theorem B2741249 : Blo 2027435 2741249 := bstep (se 2 (by rfl) ⟨1027968, by rfl⟩ : syracuseStep 2741249 = 2055937) B2055937
theorem B7309997 : Blo 2027435 7309997 := bstep (se 3 (by rfl) ⟨1370624, by rfl⟩ : syracuseStep 7309997 = 2741249) B2741249
theorem B4873331 : Blo 2027435 4873331 := bstep (se 1 (by rfl) ⟨3654998, by rfl⟩ : syracuseStep 4873331 = 7309997) B7309997
theorem B12995549 : Blo 2027435 12995549 := bstep (se 3 (by rfl) ⟨2436665, by rfl⟩ : syracuseStep 12995549 = 4873331) B4873331
theorem B8663699 : Blo 2027435 8663699 := bstep (se 1 (by rfl) ⟨6497774, by rfl⟩ : syracuseStep 8663699 = 12995549) B12995549
theorem B5775799 : Blo 2027435 5775799 := bstep (se 1 (by rfl) ⟨4331849, by rfl⟩ : syracuseStep 5775799 = 8663699) B8663699
theorem B7701065 : Blo 2027435 7701065 := bstep (se 2 (by rfl) ⟨2887899, by rfl⟩ : syracuseStep 7701065 = 5775799) B5775799
theorem B5134043 : Blo 2027435 5134043 := bstep (se 1 (by rfl) ⟨3850532, by rfl⟩ : syracuseStep 5134043 = 7701065) B7701065
theorem B3422695 : Blo 2027435 3422695 := bstep (se 1 (by rfl) ⟨2567021, by rfl⟩ : syracuseStep 3422695 = 5134043) B5134043
theorem B4563593 : Blo 2027435 4563593 := bstep (se 2 (by rfl) ⟨1711347, by rfl⟩ : syracuseStep 4563593 = 3422695) B3422695
theorem B3042395 : Blo 2027435 3042395 := bstep (se 1 (by rfl) ⟨2281796, by rfl⟩ : syracuseStep 3042395 = 4563593) B4563593
theorem B2028263 : Blo 2027435 2028263 := bstep (se 1 (by rfl) ⟨1521197, by rfl⟩ : syracuseStep 2028263 = 3042395) B3042395
theorem B2281801 : Blo 2027435 2281801 := bbase (se 2 (by rfl) ⟨855675, by rfl⟩ : syracuseStep 2281801 = 1711351) (by norm_num)
theorem B3042401 : Blo 2027435 3042401 := bstep (se 2 (by rfl) ⟨1140900, by rfl⟩ : syracuseStep 3042401 = 2281801) B2281801
theorem B2028267 : Blo 2027435 2028267 := bstep (se 1 (by rfl) ⟨1521200, by rfl⟩ : syracuseStep 2028267 = 3042401) B3042401
theorem B3083917 : Blo 2027435 3083917 := bbase (se 3 (by rfl) ⟨578234, by rfl⟩ : syracuseStep 3083917 = 1156469) (by norm_num)
theorem B4111889 : Blo 2027435 4111889 := bstep (se 2 (by rfl) ⟨1541958, by rfl⟩ : syracuseStep 4111889 = 3083917) B3083917
theorem B43860149 : Blo 2027435 43860149 := bstep (se 5 (by rfl) ⟨2055944, by rfl⟩ : syracuseStep 43860149 = 4111889) B4111889
theorem B29240099 : Blo 2027435 29240099 := bstep (se 1 (by rfl) ⟨21930074, by rfl⟩ : syracuseStep 29240099 = 43860149) B43860149
theorem B19493399 : Blo 2027435 19493399 := bstep (se 1 (by rfl) ⟨14620049, by rfl⟩ : syracuseStep 19493399 = 29240099) B29240099
theorem B12995599 : Blo 2027435 12995599 := bstep (se 1 (by rfl) ⟨9746699, by rfl⟩ : syracuseStep 12995599 = 19493399) B19493399
theorem B17327465 : Blo 2027435 17327465 := bstep (se 2 (by rfl) ⟨6497799, by rfl⟩ : syracuseStep 17327465 = 12995599) B12995599
theorem B11551643 : Blo 2027435 11551643 := bstep (se 1 (by rfl) ⟨8663732, by rfl⟩ : syracuseStep 11551643 = 17327465) B17327465
theorem B7701095 : Blo 2027435 7701095 := bstep (se 1 (by rfl) ⟨5775821, by rfl⟩ : syracuseStep 7701095 = 11551643) B11551643
theorem B5134063 : Blo 2027435 5134063 := bstep (se 1 (by rfl) ⟨3850547, by rfl⟩ : syracuseStep 5134063 = 7701095) B7701095
theorem B6845417 : Blo 2027435 6845417 := bstep (se 2 (by rfl) ⟨2567031, by rfl⟩ : syracuseStep 6845417 = 5134063) B5134063
theorem B4563611 : Blo 2027435 4563611 := bstep (se 1 (by rfl) ⟨3422708, by rfl⟩ : syracuseStep 4563611 = 6845417) B6845417
theorem B3042407 : Blo 2027435 3042407 := bstep (se 1 (by rfl) ⟨2281805, by rfl⟩ : syracuseStep 3042407 = 4563611) B4563611
theorem B2028271 : Blo 2027435 2028271 := bstep (se 1 (by rfl) ⟨1521203, by rfl⟩ : syracuseStep 2028271 = 3042407) B3042407
theorem B3042413 : Blo 2027435 3042413 := bbase (se 3 (by rfl) ⟨570452, by rfl⟩ : syracuseStep 3042413 = 1140905) (by norm_num)
theorem B2028275 : Blo 2027435 2028275 := bstep (se 1 (by rfl) ⟨1521206, by rfl⟩ : syracuseStep 2028275 = 3042413) B3042413
theorem B4563629 : Blo 2027435 4563629 := bbase (se 3 (by rfl) ⟨855680, by rfl⟩ : syracuseStep 4563629 = 1711361) (by norm_num)
theorem B3042419 : Blo 2027435 3042419 := bstep (se 1 (by rfl) ⟨2281814, by rfl⟩ : syracuseStep 3042419 = 4563629) B4563629
theorem B2028279 : Blo 2027435 2028279 := bstep (se 1 (by rfl) ⟨1521209, by rfl⟩ : syracuseStep 2028279 = 3042419) B3042419
theorem B4331893 : Blo 2027435 4331893 := bbase (se 5 (by rfl) ⟨203057, by rfl⟩ : syracuseStep 4331893 = 406115) (by norm_num)
theorem B5775857 : Blo 2027435 5775857 := bstep (se 2 (by rfl) ⟨2165946, by rfl⟩ : syracuseStep 5775857 = 4331893) B4331893
theorem B3850571 : Blo 2027435 3850571 := bstep (se 1 (by rfl) ⟨2887928, by rfl⟩ : syracuseStep 3850571 = 5775857) B5775857
theorem B2567047 : Blo 2027435 2567047 := bstep (se 1 (by rfl) ⟨1925285, by rfl⟩ : syracuseStep 2567047 = 3850571) B3850571
theorem B3422729 : Blo 2027435 3422729 := bstep (se 2 (by rfl) ⟨1283523, by rfl⟩ : syracuseStep 3422729 = 2567047) B2567047
theorem B2281819 : Blo 2027435 2281819 := bstep (se 1 (by rfl) ⟨1711364, by rfl⟩ : syracuseStep 2281819 = 3422729) B3422729
theorem B3042425 : Blo 2027435 3042425 := bstep (se 2 (by rfl) ⟨1140909, by rfl⟩ : syracuseStep 3042425 = 2281819) B2281819
theorem B2028283 : Blo 2027435 2028283 := bstep (se 1 (by rfl) ⟨1521212, by rfl⟩ : syracuseStep 2028283 = 3042425) B3042425
theorem B5633189 : Blo 2027435 5633189 := bbase (se 4 (by rfl) ⟨528111, by rfl⟩ : syracuseStep 5633189 = 1056223) (by norm_num)
theorem B3755459 : Blo 2027435 3755459 := bstep (se 1 (by rfl) ⟨2816594, by rfl⟩ : syracuseStep 3755459 = 5633189) B5633189
theorem B2503639 : Blo 2027435 2503639 := bstep (se 1 (by rfl) ⟨1877729, by rfl⟩ : syracuseStep 2503639 = 3755459) B3755459
theorem B3338185 : Blo 2027435 3338185 := bstep (se 2 (by rfl) ⟨1251819, by rfl⟩ : syracuseStep 3338185 = 2503639) B2503639
theorem B4450913 : Blo 2027435 4450913 := bstep (se 2 (by rfl) ⟨1669092, by rfl⟩ : syracuseStep 4450913 = 3338185) B3338185
theorem B2967275 : Blo 2027435 2967275 := bstep (se 1 (by rfl) ⟨2225456, by rfl⟩ : syracuseStep 2967275 = 4450913) B4450913
theorem B7912733 : Blo 2027435 7912733 := bstep (se 3 (by rfl) ⟨1483637, by rfl⟩ : syracuseStep 7912733 = 2967275) B2967275
theorem B21100621 : Blo 2027435 21100621 := bstep (se 3 (by rfl) ⟨3956366, by rfl⟩ : syracuseStep 21100621 = 7912733) B7912733
theorem B28134161 : Blo 2027435 28134161 := bstep (se 2 (by rfl) ⟨10550310, by rfl⟩ : syracuseStep 28134161 = 21100621) B21100621
theorem B18756107 : Blo 2027435 18756107 := bstep (se 1 (by rfl) ⟨14067080, by rfl⟩ : syracuseStep 18756107 = 28134161) B28134161
theorem B12504071 : Blo 2027435 12504071 := bstep (se 1 (by rfl) ⟨9378053, by rfl⟩ : syracuseStep 12504071 = 18756107) B18756107
theorem B8336047 : Blo 2027435 8336047 := bstep (se 1 (by rfl) ⟨6252035, by rfl⟩ : syracuseStep 8336047 = 12504071) B12504071
theorem B11114729 : Blo 2027435 11114729 := bstep (se 2 (by rfl) ⟨4168023, by rfl⟩ : syracuseStep 11114729 = 8336047) B8336047
theorem B7409819 : Blo 2027435 7409819 := bstep (se 1 (by rfl) ⟨5557364, by rfl⟩ : syracuseStep 7409819 = 11114729) B11114729
theorem B4939879 : Blo 2027435 4939879 := bstep (se 1 (by rfl) ⟨3704909, by rfl⟩ : syracuseStep 4939879 = 7409819) B7409819
theorem B6586505 : Blo 2027435 6586505 := bstep (se 2 (by rfl) ⟨2469939, by rfl⟩ : syracuseStep 6586505 = 4939879) B4939879
theorem B4391003 : Blo 2027435 4391003 := bstep (se 1 (by rfl) ⟨3293252, by rfl⟩ : syracuseStep 4391003 = 6586505) B6586505
theorem B2927335 : Blo 2027435 2927335 := bstep (se 1 (by rfl) ⟨2195501, by rfl⟩ : syracuseStep 2927335 = 4391003) B4391003
theorem B3903113 : Blo 2027435 3903113 := bstep (se 2 (by rfl) ⟨1463667, by rfl⟩ : syracuseStep 3903113 = 2927335) B2927335
theorem B10408301 : Blo 2027435 10408301 := bstep (se 3 (by rfl) ⟨1951556, by rfl⟩ : syracuseStep 10408301 = 3903113) B3903113
theorem B6938867 : Blo 2027435 6938867 := bstep (se 1 (by rfl) ⟨5204150, by rfl⟩ : syracuseStep 6938867 = 10408301) B10408301
theorem B18503645 : Blo 2027435 18503645 := bstep (se 3 (by rfl) ⟨3469433, by rfl⟩ : syracuseStep 18503645 = 6938867) B6938867
theorem B49343053 : Blo 2027435 49343053 := bstep (se 3 (by rfl) ⟨9251822, by rfl⟩ : syracuseStep 49343053 = 18503645) B18503645
theorem B65790737 : Blo 2027435 65790737 := bstep (se 2 (by rfl) ⟨24671526, by rfl⟩ : syracuseStep 65790737 = 49343053) B49343053
theorem B43860491 : Blo 2027435 43860491 := bstep (se 1 (by rfl) ⟨32895368, by rfl⟩ : syracuseStep 43860491 = 65790737) B65790737
theorem B29240327 : Blo 2027435 29240327 := bstep (se 1 (by rfl) ⟨21930245, by rfl⟩ : syracuseStep 29240327 = 43860491) B43860491
theorem B19493551 : Blo 2027435 19493551 := bstep (se 1 (by rfl) ⟨14620163, by rfl⟩ : syracuseStep 19493551 = 29240327) B29240327
theorem B25991401 : Blo 2027435 25991401 := bstep (se 2 (by rfl) ⟨9746775, by rfl⟩ : syracuseStep 25991401 = 19493551) B19493551
theorem B34655201 : Blo 2027435 34655201 := bstep (se 2 (by rfl) ⟨12995700, by rfl⟩ : syracuseStep 34655201 = 25991401) B25991401
theorem B23103467 : Blo 2027435 23103467 := bstep (se 1 (by rfl) ⟨17327600, by rfl⟩ : syracuseStep 23103467 = 34655201) B34655201
theorem B15402311 : Blo 2027435 15402311 := bstep (se 1 (by rfl) ⟨11551733, by rfl⟩ : syracuseStep 15402311 = 23103467) B23103467
theorem B10268207 : Blo 2027435 10268207 := bstep (se 1 (by rfl) ⟨7701155, by rfl⟩ : syracuseStep 10268207 = 15402311) B15402311
theorem B6845471 : Blo 2027435 6845471 := bstep (se 1 (by rfl) ⟨5134103, by rfl⟩ : syracuseStep 6845471 = 10268207) B10268207
theorem B4563647 : Blo 2027435 4563647 := bstep (se 1 (by rfl) ⟨3422735, by rfl⟩ : syracuseStep 4563647 = 6845471) B6845471
theorem B3042431 : Blo 2027435 3042431 := bstep (se 1 (by rfl) ⟨2281823, by rfl⟩ : syracuseStep 3042431 = 4563647) B4563647
theorem B2028287 : Blo 2027435 2028287 := bstep (se 1 (by rfl) ⟨1521215, by rfl⟩ : syracuseStep 2028287 = 3042431) B3042431
theorem B3042437 : Blo 2027435 3042437 := bbase (se 4 (by rfl) ⟨285228, by rfl⟩ : syracuseStep 3042437 = 570457) (by norm_num)
theorem B2028291 : Blo 2027435 2028291 := bstep (se 1 (by rfl) ⟨1521218, by rfl⟩ : syracuseStep 2028291 = 3042437) B3042437
theorem B3422749 : Blo 2027435 3422749 := bbase (se 3 (by rfl) ⟨641765, by rfl⟩ : syracuseStep 3422749 = 1283531) (by norm_num)
theorem B4563665 : Blo 2027435 4563665 := bstep (se 2 (by rfl) ⟨1711374, by rfl⟩ : syracuseStep 4563665 = 3422749) B3422749
theorem B3042443 : Blo 2027435 3042443 := bstep (se 1 (by rfl) ⟨2281832, by rfl⟩ : syracuseStep 3042443 = 4563665) B4563665
theorem B2028295 : Blo 2027435 2028295 := bstep (se 1 (by rfl) ⟨1521221, by rfl⟩ : syracuseStep 2028295 = 3042443) B3042443
theorem B2281837 : Blo 2027435 2281837 := bbase (se 3 (by rfl) ⟨427844, by rfl⟩ : syracuseStep 2281837 = 855689) (by norm_num)
theorem B3042449 : Blo 2027435 3042449 := bstep (se 2 (by rfl) ⟨1140918, by rfl⟩ : syracuseStep 3042449 = 2281837) B2281837
theorem B2028299 : Blo 2027435 2028299 := bstep (se 1 (by rfl) ⟨1521224, by rfl⟩ : syracuseStep 2028299 = 3042449) B3042449
theorem B6845525 : Blo 2027435 6845525 := bbase (se 8 (by rfl) ⟨40110, by rfl⟩ : syracuseStep 6845525 = 80221) (by norm_num)
theorem B4563683 : Blo 2027435 4563683 := bstep (se 1 (by rfl) ⟨3422762, by rfl⟩ : syracuseStep 4563683 = 6845525) B6845525
theorem B3042455 : Blo 2027435 3042455 := bstep (se 1 (by rfl) ⟨2281841, by rfl⟩ : syracuseStep 3042455 = 4563683) B4563683
theorem B2028303 : Blo 2027435 2028303 := bstep (se 1 (by rfl) ⟨1521227, by rfl⟩ : syracuseStep 2028303 = 3042455) B3042455
theorem B3042461 : Blo 2027435 3042461 := bbase (se 3 (by rfl) ⟨570461, by rfl⟩ : syracuseStep 3042461 = 1140923) (by norm_num)
theorem B2028307 : Blo 2027435 2028307 := bstep (se 1 (by rfl) ⟨1521230, by rfl⟩ : syracuseStep 2028307 = 3042461) B3042461
theorem B4563701 : Blo 2027435 4563701 := bbase (se 5 (by rfl) ⟨213923, by rfl⟩ : syracuseStep 4563701 = 427847) (by norm_num)
theorem B3042467 : Blo 2027435 3042467 := bstep (se 1 (by rfl) ⟨2281850, by rfl⟩ : syracuseStep 3042467 = 4563701) B4563701
theorem B2028311 : Blo 2027435 2028311 := bstep (se 1 (by rfl) ⟨1521233, by rfl⟩ : syracuseStep 2028311 = 3042467) B3042467
theorem B25991765 : Blo 2027435 25991765 := bbase (se 8 (by rfl) ⟨152295, by rfl⟩ : syracuseStep 25991765 = 304591) (by norm_num)
theorem B17327843 : Blo 2027435 17327843 := bstep (se 1 (by rfl) ⟨12995882, by rfl⟩ : syracuseStep 17327843 = 25991765) B25991765
theorem B11551895 : Blo 2027435 11551895 := bstep (se 1 (by rfl) ⟨8663921, by rfl⟩ : syracuseStep 11551895 = 17327843) B17327843
theorem B7701263 : Blo 2027435 7701263 := bstep (se 1 (by rfl) ⟨5775947, by rfl⟩ : syracuseStep 7701263 = 11551895) B11551895
theorem B5134175 : Blo 2027435 5134175 := bstep (se 1 (by rfl) ⟨3850631, by rfl⟩ : syracuseStep 5134175 = 7701263) B7701263
theorem B3422783 : Blo 2027435 3422783 := bstep (se 1 (by rfl) ⟨2567087, by rfl⟩ : syracuseStep 3422783 = 5134175) B5134175
theorem B2281855 : Blo 2027435 2281855 := bstep (se 1 (by rfl) ⟨1711391, by rfl⟩ : syracuseStep 2281855 = 3422783) B3422783
theorem B3042473 : Blo 2027435 3042473 := bstep (se 2 (by rfl) ⟨1140927, by rfl⟩ : syracuseStep 3042473 = 2281855) B2281855
theorem B2028315 : Blo 2027435 2028315 := bstep (se 1 (by rfl) ⟨1521236, by rfl⟩ : syracuseStep 2028315 = 3042473) B3042473
theorem B2436733 : Blo 2027435 2436733 := bbase (se 3 (by rfl) ⟨456887, by rfl⟩ : syracuseStep 2436733 = 913775) (by norm_num)
theorem B3248977 : Blo 2027435 3248977 := bstep (se 2 (by rfl) ⟨1218366, by rfl⟩ : syracuseStep 3248977 = 2436733) B2436733
theorem B4331969 : Blo 2027435 4331969 := bstep (se 2 (by rfl) ⟨1624488, by rfl⟩ : syracuseStep 4331969 = 3248977) B3248977
theorem B2887979 : Blo 2027435 2887979 := bstep (se 1 (by rfl) ⟨2165984, by rfl⟩ : syracuseStep 2887979 = 4331969) B4331969
theorem B7701277 : Blo 2027435 7701277 := bstep (se 3 (by rfl) ⟨1443989, by rfl⟩ : syracuseStep 7701277 = 2887979) B2887979
theorem B10268369 : Blo 2027435 10268369 := bstep (se 2 (by rfl) ⟨3850638, by rfl⟩ : syracuseStep 10268369 = 7701277) B7701277
theorem B6845579 : Blo 2027435 6845579 := bstep (se 1 (by rfl) ⟨5134184, by rfl⟩ : syracuseStep 6845579 = 10268369) B10268369
theorem B4563719 : Blo 2027435 4563719 := bstep (se 1 (by rfl) ⟨3422789, by rfl⟩ : syracuseStep 4563719 = 6845579) B6845579
theorem B3042479 : Blo 2027435 3042479 := bstep (se 1 (by rfl) ⟨2281859, by rfl⟩ : syracuseStep 3042479 = 4563719) B4563719
theorem B2028319 : Blo 2027435 2028319 := bstep (se 1 (by rfl) ⟨1521239, by rfl⟩ : syracuseStep 2028319 = 3042479) B3042479
theorem B3042485 : Blo 2027435 3042485 := bbase (se 5 (by rfl) ⟨142616, by rfl⟩ : syracuseStep 3042485 = 285233) (by norm_num)
theorem B2028323 : Blo 2027435 2028323 := bstep (se 1 (by rfl) ⟨1521242, by rfl⟩ : syracuseStep 2028323 = 3042485) B3042485
theorem B5134205 : Blo 2027435 5134205 := bbase (se 3 (by rfl) ⟨962663, by rfl⟩ : syracuseStep 5134205 = 1925327) (by norm_num)
theorem B3422803 : Blo 2027435 3422803 := bstep (se 1 (by rfl) ⟨2567102, by rfl⟩ : syracuseStep 3422803 = 5134205) B5134205
theorem B4563737 : Blo 2027435 4563737 := bstep (se 2 (by rfl) ⟨1711401, by rfl⟩ : syracuseStep 4563737 = 3422803) B3422803
theorem B3042491 : Blo 2027435 3042491 := bstep (se 1 (by rfl) ⟨2281868, by rfl⟩ : syracuseStep 3042491 = 4563737) B4563737
theorem B2028327 : Blo 2027435 2028327 := bstep (se 1 (by rfl) ⟨1521245, by rfl⟩ : syracuseStep 2028327 = 3042491) B3042491
theorem B2281873 : Blo 2027435 2281873 := bbase (se 2 (by rfl) ⟨855702, by rfl⟩ : syracuseStep 2281873 = 1711405) (by norm_num)
theorem B3042497 : Blo 2027435 3042497 := bstep (se 2 (by rfl) ⟨1140936, by rfl⟩ : syracuseStep 3042497 = 2281873) B2281873
theorem B2028331 : Blo 2027435 2028331 := bstep (se 1 (by rfl) ⟨1521248, by rfl⟩ : syracuseStep 2028331 = 3042497) B3042497
theorem B3850669 : Blo 2027435 3850669 := bbase (se 3 (by rfl) ⟨722000, by rfl⟩ : syracuseStep 3850669 = 1444001) (by norm_num)
theorem B5134225 : Blo 2027435 5134225 := bstep (se 2 (by rfl) ⟨1925334, by rfl⟩ : syracuseStep 5134225 = 3850669) B3850669
theorem B6845633 : Blo 2027435 6845633 := bstep (se 2 (by rfl) ⟨2567112, by rfl⟩ : syracuseStep 6845633 = 5134225) B5134225
theorem B4563755 : Blo 2027435 4563755 := bstep (se 1 (by rfl) ⟨3422816, by rfl⟩ : syracuseStep 4563755 = 6845633) B6845633
theorem B3042503 : Blo 2027435 3042503 := bstep (se 1 (by rfl) ⟨2281877, by rfl⟩ : syracuseStep 3042503 = 4563755) B4563755
theorem B2028335 : Blo 2027435 2028335 := bstep (se 1 (by rfl) ⟨1521251, by rfl⟩ : syracuseStep 2028335 = 3042503) B3042503
theorem B3042509 : Blo 2027435 3042509 := bbase (se 3 (by rfl) ⟨570470, by rfl⟩ : syracuseStep 3042509 = 1140941) (by norm_num)
theorem B2028339 : Blo 2027435 2028339 := bstep (se 1 (by rfl) ⟨1521254, by rfl⟩ : syracuseStep 2028339 = 3042509) B3042509
theorem B4563773 : Blo 2027435 4563773 := bbase (se 3 (by rfl) ⟨855707, by rfl⟩ : syracuseStep 4563773 = 1711415) (by norm_num)
theorem B3042515 : Blo 2027435 3042515 := bstep (se 1 (by rfl) ⟨2281886, by rfl⟩ : syracuseStep 3042515 = 4563773) B4563773
theorem B2028343 : Blo 2027435 2028343 := bstep (se 1 (by rfl) ⟨1521257, by rfl⟩ : syracuseStep 2028343 = 3042515) B3042515
theorem B3422837 : Blo 2027435 3422837 := bbase (se 5 (by rfl) ⟨160445, by rfl⟩ : syracuseStep 3422837 = 320891) (by norm_num)
theorem B2281891 : Blo 2027435 2281891 := bstep (se 1 (by rfl) ⟨1711418, by rfl⟩ : syracuseStep 2281891 = 3422837) B3422837
theorem B3042521 : Blo 2027435 3042521 := bstep (se 2 (by rfl) ⟨1140945, by rfl⟩ : syracuseStep 3042521 = 2281891) B2281891
theorem B2028347 : Blo 2027435 2028347 := bstep (se 1 (by rfl) ⟨1521260, by rfl⟩ : syracuseStep 2028347 = 3042521) B3042521
theorem B4332037 : Blo 2027435 4332037 := bbase (se 4 (by rfl) ⟨406128, by rfl⟩ : syracuseStep 4332037 = 812257) (by norm_num)
theorem B5776049 : Blo 2027435 5776049 := bstep (se 2 (by rfl) ⟨2166018, by rfl⟩ : syracuseStep 5776049 = 4332037) B4332037
theorem B15402797 : Blo 2027435 15402797 := bstep (se 3 (by rfl) ⟨2888024, by rfl⟩ : syracuseStep 15402797 = 5776049) B5776049
theorem B10268531 : Blo 2027435 10268531 := bstep (se 1 (by rfl) ⟨7701398, by rfl⟩ : syracuseStep 10268531 = 15402797) B15402797
theorem B6845687 : Blo 2027435 6845687 := bstep (se 1 (by rfl) ⟨5134265, by rfl⟩ : syracuseStep 6845687 = 10268531) B10268531
theorem B4563791 : Blo 2027435 4563791 := bstep (se 1 (by rfl) ⟨3422843, by rfl⟩ : syracuseStep 4563791 = 6845687) B6845687
theorem B3042527 : Blo 2027435 3042527 := bstep (se 1 (by rfl) ⟨2281895, by rfl⟩ : syracuseStep 3042527 = 4563791) B4563791
theorem B2028351 : Blo 2027435 2028351 := bstep (se 1 (by rfl) ⟨1521263, by rfl⟩ : syracuseStep 2028351 = 3042527) B3042527
theorem B3042533 : Blo 2027435 3042533 := bbase (se 4 (by rfl) ⟨285237, by rfl⟩ : syracuseStep 3042533 = 570475) (by norm_num)
theorem B2028355 : Blo 2027435 2028355 := bstep (se 1 (by rfl) ⟨1521266, by rfl⟩ : syracuseStep 2028355 = 3042533) B3042533
theorem B9747125 : Blo 2027435 9747125 := bbase (se 5 (by rfl) ⟨456896, by rfl⟩ : syracuseStep 9747125 = 913793) (by norm_num)
theorem B6498083 : Blo 2027435 6498083 := bstep (se 1 (by rfl) ⟨4873562, by rfl⟩ : syracuseStep 6498083 = 9747125) B9747125
theorem B4332055 : Blo 2027435 4332055 := bstep (se 1 (by rfl) ⟨3249041, by rfl⟩ : syracuseStep 4332055 = 6498083) B6498083
theorem B5776073 : Blo 2027435 5776073 := bstep (se 2 (by rfl) ⟨2166027, by rfl⟩ : syracuseStep 5776073 = 4332055) B4332055
theorem B3850715 : Blo 2027435 3850715 := bstep (se 1 (by rfl) ⟨2888036, by rfl⟩ : syracuseStep 3850715 = 5776073) B5776073
theorem B2567143 : Blo 2027435 2567143 := bstep (se 1 (by rfl) ⟨1925357, by rfl⟩ : syracuseStep 2567143 = 3850715) B3850715
theorem B3422857 : Blo 2027435 3422857 := bstep (se 2 (by rfl) ⟨1283571, by rfl⟩ : syracuseStep 3422857 = 2567143) B2567143
theorem B4563809 : Blo 2027435 4563809 := bstep (se 2 (by rfl) ⟨1711428, by rfl⟩ : syracuseStep 4563809 = 3422857) B3422857
theorem B3042539 : Blo 2027435 3042539 := bstep (se 1 (by rfl) ⟨2281904, by rfl⟩ : syracuseStep 3042539 = 4563809) B4563809
theorem B2028359 : Blo 2027435 2028359 := bstep (se 1 (by rfl) ⟨1521269, by rfl⟩ : syracuseStep 2028359 = 3042539) B3042539
theorem B2281909 : Blo 2027435 2281909 := bbase (se 5 (by rfl) ⟨106964, by rfl⟩ : syracuseStep 2281909 = 213929) (by norm_num)
theorem B3042545 : Blo 2027435 3042545 := bstep (se 2 (by rfl) ⟨1140954, by rfl⟩ : syracuseStep 3042545 = 2281909) B2281909
theorem B2028363 : Blo 2027435 2028363 := bstep (se 1 (by rfl) ⟨1521272, by rfl⟩ : syracuseStep 2028363 = 3042545) B3042545
theorem B2567153 : Blo 2027435 2567153 := bbase (se 2 (by rfl) ⟨962682, by rfl⟩ : syracuseStep 2567153 = 1925365) (by norm_num)
theorem B6845741 : Blo 2027435 6845741 := bstep (se 3 (by rfl) ⟨1283576, by rfl⟩ : syracuseStep 6845741 = 2567153) B2567153
theorem B4563827 : Blo 2027435 4563827 := bstep (se 1 (by rfl) ⟨3422870, by rfl⟩ : syracuseStep 4563827 = 6845741) B6845741
theorem B3042551 : Blo 2027435 3042551 := bstep (se 1 (by rfl) ⟨2281913, by rfl⟩ : syracuseStep 3042551 = 4563827) B4563827
theorem B2028367 : Blo 2027435 2028367 := bstep (se 1 (by rfl) ⟨1521275, by rfl⟩ : syracuseStep 2028367 = 3042551) B3042551
theorem B3042557 : Blo 2027435 3042557 := bbase (se 3 (by rfl) ⟨570479, by rfl⟩ : syracuseStep 3042557 = 1140959) (by norm_num)
theorem B2028371 : Blo 2027435 2028371 := bstep (se 1 (by rfl) ⟨1521278, by rfl⟩ : syracuseStep 2028371 = 3042557) B3042557
theorem B4563845 : Blo 2027435 4563845 := bbase (se 4 (by rfl) ⟨427860, by rfl⟩ : syracuseStep 4563845 = 855721) (by norm_num)
theorem B3042563 : Blo 2027435 3042563 := bstep (se 1 (by rfl) ⟨2281922, by rfl⟩ : syracuseStep 3042563 = 4563845) B4563845
theorem B2028375 : Blo 2027435 2028375 := bstep (se 1 (by rfl) ⟨1521281, by rfl⟩ : syracuseStep 2028375 = 3042563) B3042563
theorem B2166049 : Blo 2027435 2166049 := bbase (se 2 (by rfl) ⟨812268, by rfl⟩ : syracuseStep 2166049 = 1624537) (by norm_num)
theorem B2888065 : Blo 2027435 2888065 := bstep (se 2 (by rfl) ⟨1083024, by rfl⟩ : syracuseStep 2888065 = 2166049) B2166049
theorem B3850753 : Blo 2027435 3850753 := bstep (se 2 (by rfl) ⟨1444032, by rfl⟩ : syracuseStep 3850753 = 2888065) B2888065
theorem B5134337 : Blo 2027435 5134337 := bstep (se 2 (by rfl) ⟨1925376, by rfl⟩ : syracuseStep 5134337 = 3850753) B3850753
theorem B3422891 : Blo 2027435 3422891 := bstep (se 1 (by rfl) ⟨2567168, by rfl⟩ : syracuseStep 3422891 = 5134337) B5134337
theorem B2281927 : Blo 2027435 2281927 := bstep (se 1 (by rfl) ⟨1711445, by rfl⟩ : syracuseStep 2281927 = 3422891) B3422891
theorem B3042569 : Blo 2027435 3042569 := bstep (se 2 (by rfl) ⟨1140963, by rfl⟩ : syracuseStep 3042569 = 2281927) B2281927
theorem B2028379 : Blo 2027435 2028379 := bstep (se 1 (by rfl) ⟨1521284, by rfl⟩ : syracuseStep 2028379 = 3042569) B3042569
theorem B10268693 : Blo 2027435 10268693 := bbase (se 6 (by rfl) ⟨240672, by rfl⟩ : syracuseStep 10268693 = 481345) (by norm_num)
theorem B6845795 : Blo 2027435 6845795 := bstep (se 1 (by rfl) ⟨5134346, by rfl⟩ : syracuseStep 6845795 = 10268693) B10268693
theorem B4563863 : Blo 2027435 4563863 := bstep (se 1 (by rfl) ⟨3422897, by rfl⟩ : syracuseStep 4563863 = 6845795) B6845795
theorem B3042575 : Blo 2027435 3042575 := bstep (se 1 (by rfl) ⟨2281931, by rfl⟩ : syracuseStep 3042575 = 4563863) B4563863
theorem B2028383 : Blo 2027435 2028383 := bstep (se 1 (by rfl) ⟨1521287, by rfl⟩ : syracuseStep 2028383 = 3042575) B3042575
theorem B3042581 : Blo 2027435 3042581 := bbase (se 6 (by rfl) ⟨71310, by rfl⟩ : syracuseStep 3042581 = 142621) (by norm_num)
theorem B2028387 : Blo 2027435 2028387 := bstep (se 1 (by rfl) ⟨1521290, by rfl⟩ : syracuseStep 2028387 = 3042581) B3042581
theorem B10408837 : Blo 2027435 10408837 := bbase (se 4 (by rfl) ⟨975828, by rfl⟩ : syracuseStep 10408837 = 1951657) (by norm_num)
theorem B13878449 : Blo 2027435 13878449 := bstep (se 2 (by rfl) ⟨5204418, by rfl⟩ : syracuseStep 13878449 = 10408837) B10408837
theorem B9252299 : Blo 2027435 9252299 := bstep (se 1 (by rfl) ⟨6939224, by rfl⟩ : syracuseStep 9252299 = 13878449) B13878449
theorem B6168199 : Blo 2027435 6168199 := bstep (se 1 (by rfl) ⟨4626149, by rfl⟩ : syracuseStep 6168199 = 9252299) B9252299
theorem B8224265 : Blo 2027435 8224265 := bstep (se 2 (by rfl) ⟨3084099, by rfl⟩ : syracuseStep 8224265 = 6168199) B6168199
theorem B21931373 : Blo 2027435 21931373 := bstep (se 3 (by rfl) ⟨4112132, by rfl⟩ : syracuseStep 21931373 = 8224265) B8224265
theorem B14620915 : Blo 2027435 14620915 := bstep (se 1 (by rfl) ⟨10965686, by rfl⟩ : syracuseStep 14620915 = 21931373) B21931373
theorem B19494553 : Blo 2027435 19494553 := bstep (se 2 (by rfl) ⟨7310457, by rfl⟩ : syracuseStep 19494553 = 14620915) B14620915
theorem B25992737 : Blo 2027435 25992737 := bstep (se 2 (by rfl) ⟨9747276, by rfl⟩ : syracuseStep 25992737 = 19494553) B19494553
theorem B17328491 : Blo 2027435 17328491 := bstep (se 1 (by rfl) ⟨12996368, by rfl⟩ : syracuseStep 17328491 = 25992737) B25992737
theorem B11552327 : Blo 2027435 11552327 := bstep (se 1 (by rfl) ⟨8664245, by rfl⟩ : syracuseStep 11552327 = 17328491) B17328491
theorem B7701551 : Blo 2027435 7701551 := bstep (se 1 (by rfl) ⟨5776163, by rfl⟩ : syracuseStep 7701551 = 11552327) B11552327
theorem B5134367 : Blo 2027435 5134367 := bstep (se 1 (by rfl) ⟨3850775, by rfl⟩ : syracuseStep 5134367 = 7701551) B7701551
theorem B3422911 : Blo 2027435 3422911 := bstep (se 1 (by rfl) ⟨2567183, by rfl⟩ : syracuseStep 3422911 = 5134367) B5134367
theorem B4563881 : Blo 2027435 4563881 := bstep (se 2 (by rfl) ⟨1711455, by rfl⟩ : syracuseStep 4563881 = 3422911) B3422911
theorem B3042587 : Blo 2027435 3042587 := bstep (se 1 (by rfl) ⟨2281940, by rfl⟩ : syracuseStep 3042587 = 4563881) B4563881
theorem B2028391 : Blo 2027435 2028391 := bstep (se 1 (by rfl) ⟨1521293, by rfl⟩ : syracuseStep 2028391 = 3042587) B3042587
theorem B2281945 : Blo 2027435 2281945 := bbase (se 2 (by rfl) ⟨855729, by rfl⟩ : syracuseStep 2281945 = 1711459) (by norm_num)
theorem B3042593 : Blo 2027435 3042593 := bstep (se 2 (by rfl) ⟨1140972, by rfl⟩ : syracuseStep 3042593 = 2281945) B2281945
theorem B2028395 : Blo 2027435 2028395 := bstep (se 1 (by rfl) ⟨1521296, by rfl⟩ : syracuseStep 2028395 = 3042593) B3042593
theorem B2888093 : Blo 2027435 2888093 := bbase (se 3 (by rfl) ⟨541517, by rfl⟩ : syracuseStep 2888093 = 1083035) (by norm_num)
theorem B7701581 : Blo 2027435 7701581 := bstep (se 3 (by rfl) ⟨1444046, by rfl⟩ : syracuseStep 7701581 = 2888093) B2888093
theorem B5134387 : Blo 2027435 5134387 := bstep (se 1 (by rfl) ⟨3850790, by rfl⟩ : syracuseStep 5134387 = 7701581) B7701581
theorem B6845849 : Blo 2027435 6845849 := bstep (se 2 (by rfl) ⟨2567193, by rfl⟩ : syracuseStep 6845849 = 5134387) B5134387
theorem B4563899 : Blo 2027435 4563899 := bstep (se 1 (by rfl) ⟨3422924, by rfl⟩ : syracuseStep 4563899 = 6845849) B6845849
theorem B3042599 : Blo 2027435 3042599 := bstep (se 1 (by rfl) ⟨2281949, by rfl⟩ : syracuseStep 3042599 = 4563899) B4563899
theorem B2028399 : Blo 2027435 2028399 := bstep (se 1 (by rfl) ⟨1521299, by rfl⟩ : syracuseStep 2028399 = 3042599) B3042599
theorem B3042605 : Blo 2027435 3042605 := bbase (se 3 (by rfl) ⟨570488, by rfl⟩ : syracuseStep 3042605 = 1140977) (by norm_num)
theorem B2028403 : Blo 2027435 2028403 := bstep (se 1 (by rfl) ⟨1521302, by rfl⟩ : syracuseStep 2028403 = 3042605) B3042605
theorem B4563917 : Blo 2027435 4563917 := bbase (se 3 (by rfl) ⟨855734, by rfl⟩ : syracuseStep 4563917 = 1711469) (by norm_num)
theorem B3042611 : Blo 2027435 3042611 := bstep (se 1 (by rfl) ⟨2281958, by rfl⟩ : syracuseStep 3042611 = 4563917) B4563917
theorem B2028407 : Blo 2027435 2028407 := bstep (se 1 (by rfl) ⟨1521305, by rfl⟩ : syracuseStep 2028407 = 3042611) B3042611
theorem B2567209 : Blo 2027435 2567209 := bbase (se 2 (by rfl) ⟨962703, by rfl⟩ : syracuseStep 2567209 = 1925407) (by norm_num)
theorem B3422945 : Blo 2027435 3422945 := bstep (se 2 (by rfl) ⟨1283604, by rfl⟩ : syracuseStep 3422945 = 2567209) B2567209
theorem B2281963 : Blo 2027435 2281963 := bstep (se 1 (by rfl) ⟨1711472, by rfl⟩ : syracuseStep 2281963 = 3422945) B3422945
theorem B3042617 : Blo 2027435 3042617 := bstep (se 2 (by rfl) ⟨1140981, by rfl⟩ : syracuseStep 3042617 = 2281963) B2281963
theorem B2028411 : Blo 2027435 2028411 := bstep (se 1 (by rfl) ⟨1521308, by rfl⟩ : syracuseStep 2028411 = 3042617) B3042617
theorem B16673141 : Blo 2027435 16673141 := bbase (se 5 (by rfl) ⟨781553, by rfl⟩ : syracuseStep 16673141 = 1563107) (by norm_num)
theorem B44461709 : Blo 2027435 44461709 := bstep (se 3 (by rfl) ⟨8336570, by rfl⟩ : syracuseStep 44461709 = 16673141) B16673141
theorem B29641139 : Blo 2027435 29641139 := bstep (se 1 (by rfl) ⟨22230854, by rfl⟩ : syracuseStep 29641139 = 44461709) B44461709
theorem B19760759 : Blo 2027435 19760759 := bstep (se 1 (by rfl) ⟨14820569, by rfl⟩ : syracuseStep 19760759 = 29641139) B29641139
theorem B13173839 : Blo 2027435 13173839 := bstep (se 1 (by rfl) ⟨9880379, by rfl⟩ : syracuseStep 13173839 = 19760759) B19760759
theorem B8782559 : Blo 2027435 8782559 := bstep (se 1 (by rfl) ⟨6586919, by rfl⟩ : syracuseStep 8782559 = 13173839) B13173839
theorem B5855039 : Blo 2027435 5855039 := bstep (se 1 (by rfl) ⟨4391279, by rfl⟩ : syracuseStep 5855039 = 8782559) B8782559
theorem B62453749 : Blo 2027435 62453749 := bstep (se 5 (by rfl) ⟨2927519, by rfl⟩ : syracuseStep 62453749 = 5855039) B5855039
theorem B83271665 : Blo 2027435 83271665 := bstep (se 2 (by rfl) ⟨31226874, by rfl⟩ : syracuseStep 83271665 = 62453749) B62453749
theorem B55514443 : Blo 2027435 55514443 := bstep (se 1 (by rfl) ⟨41635832, by rfl⟩ : syracuseStep 55514443 = 83271665) B83271665
theorem B74019257 : Blo 2027435 74019257 := bstep (se 2 (by rfl) ⟨27757221, by rfl⟩ : syracuseStep 74019257 = 55514443) B55514443
theorem B49346171 : Blo 2027435 49346171 := bstep (se 1 (by rfl) ⟨37009628, by rfl⟩ : syracuseStep 49346171 = 74019257) B74019257
theorem B32897447 : Blo 2027435 32897447 := bstep (se 1 (by rfl) ⟨24673085, by rfl⟩ : syracuseStep 32897447 = 49346171) B49346171
theorem B21931631 : Blo 2027435 21931631 := bstep (se 1 (by rfl) ⟨16448723, by rfl⟩ : syracuseStep 21931631 = 32897447) B32897447
theorem B14621087 : Blo 2027435 14621087 := bstep (se 1 (by rfl) ⟨10965815, by rfl⟩ : syracuseStep 14621087 = 21931631) B21931631
theorem B9747391 : Blo 2027435 9747391 := bstep (se 1 (by rfl) ⟨7310543, by rfl⟩ : syracuseStep 9747391 = 14621087) B14621087
theorem B12996521 : Blo 2027435 12996521 := bstep (se 2 (by rfl) ⟨4873695, by rfl⟩ : syracuseStep 12996521 = 9747391) B9747391
theorem B8664347 : Blo 2027435 8664347 := bstep (se 1 (by rfl) ⟨6498260, by rfl⟩ : syracuseStep 8664347 = 12996521) B12996521
theorem B23104925 : Blo 2027435 23104925 := bstep (se 3 (by rfl) ⟨4332173, by rfl⟩ : syracuseStep 23104925 = 8664347) B8664347
theorem B15403283 : Blo 2027435 15403283 := bstep (se 1 (by rfl) ⟨11552462, by rfl⟩ : syracuseStep 15403283 = 23104925) B23104925
theorem B10268855 : Blo 2027435 10268855 := bstep (se 1 (by rfl) ⟨7701641, by rfl⟩ : syracuseStep 10268855 = 15403283) B15403283
theorem B6845903 : Blo 2027435 6845903 := bstep (se 1 (by rfl) ⟨5134427, by rfl⟩ : syracuseStep 6845903 = 10268855) B10268855
theorem B4563935 : Blo 2027435 4563935 := bstep (se 1 (by rfl) ⟨3422951, by rfl⟩ : syracuseStep 4563935 = 6845903) B6845903
theorem B3042623 : Blo 2027435 3042623 := bstep (se 1 (by rfl) ⟨2281967, by rfl⟩ : syracuseStep 3042623 = 4563935) B4563935
theorem B2028415 : Blo 2027435 2028415 := bstep (se 1 (by rfl) ⟨1521311, by rfl⟩ : syracuseStep 2028415 = 3042623) B3042623
theorem B3042629 : Blo 2027435 3042629 := bbase (se 4 (by rfl) ⟨285246, by rfl⟩ : syracuseStep 3042629 = 570493) (by norm_num)
theorem B2028419 : Blo 2027435 2028419 := bstep (se 1 (by rfl) ⟨1521314, by rfl⟩ : syracuseStep 2028419 = 3042629) B3042629
theorem B3422965 : Blo 2027435 3422965 := bbase (se 5 (by rfl) ⟨160451, by rfl⟩ : syracuseStep 3422965 = 320903) (by norm_num)
theorem B4563953 : Blo 2027435 4563953 := bstep (se 2 (by rfl) ⟨1711482, by rfl⟩ : syracuseStep 4563953 = 3422965) B3422965
theorem B3042635 : Blo 2027435 3042635 := bstep (se 1 (by rfl) ⟨2281976, by rfl⟩ : syracuseStep 3042635 = 4563953) B4563953
theorem B2028423 : Blo 2027435 2028423 := bstep (se 1 (by rfl) ⟨1521317, by rfl⟩ : syracuseStep 2028423 = 3042635) B3042635
theorem B2281981 : Blo 2027435 2281981 := bbase (se 3 (by rfl) ⟨427871, by rfl⟩ : syracuseStep 2281981 = 855743) (by norm_num)
theorem B3042641 : Blo 2027435 3042641 := bstep (se 2 (by rfl) ⟨1140990, by rfl⟩ : syracuseStep 3042641 = 2281981) B2281981
theorem B2028427 : Blo 2027435 2028427 := bstep (se 1 (by rfl) ⟨1521320, by rfl⟩ : syracuseStep 2028427 = 3042641) B3042641
theorem B6845957 : Blo 2027435 6845957 := bbase (se 4 (by rfl) ⟨641808, by rfl⟩ : syracuseStep 6845957 = 1283617) (by norm_num)
theorem B4563971 : Blo 2027435 4563971 := bstep (se 1 (by rfl) ⟨3422978, by rfl⟩ : syracuseStep 4563971 = 6845957) B6845957
theorem B3042647 : Blo 2027435 3042647 := bstep (se 1 (by rfl) ⟨2281985, by rfl⟩ : syracuseStep 3042647 = 4563971) B4563971
theorem B2028431 : Blo 2027435 2028431 := bstep (se 1 (by rfl) ⟨1521323, by rfl⟩ : syracuseStep 2028431 = 3042647) B3042647
theorem B3042653 : Blo 2027435 3042653 := bbase (se 3 (by rfl) ⟨570497, by rfl⟩ : syracuseStep 3042653 = 1140995) (by norm_num)
theorem B2028435 : Blo 2027435 2028435 := bstep (se 1 (by rfl) ⟨1521326, by rfl⟩ : syracuseStep 2028435 = 3042653) B3042653
theorem B4563989 : Blo 2027435 4563989 := bbase (se 6 (by rfl) ⟨106968, by rfl⟩ : syracuseStep 4563989 = 213937) (by norm_num)
theorem B3042659 : Blo 2027435 3042659 := bstep (se 1 (by rfl) ⟨2281994, by rfl⟩ : syracuseStep 3042659 = 4563989) B4563989
theorem B2028439 : Blo 2027435 2028439 := bstep (se 1 (by rfl) ⟨1521329, by rfl⟩ : syracuseStep 2028439 = 3042659) B3042659
theorem B7701749 : Blo 2027435 7701749 := bbase (se 5 (by rfl) ⟨361019, by rfl⟩ : syracuseStep 7701749 = 722039) (by norm_num)
theorem B5134499 : Blo 2027435 5134499 := bstep (se 1 (by rfl) ⟨3850874, by rfl⟩ : syracuseStep 5134499 = 7701749) B7701749
theorem B3422999 : Blo 2027435 3422999 := bstep (se 1 (by rfl) ⟨2567249, by rfl⟩ : syracuseStep 3422999 = 5134499) B5134499
theorem B2281999 : Blo 2027435 2281999 := bstep (se 1 (by rfl) ⟨1711499, by rfl⟩ : syracuseStep 2281999 = 3422999) B3422999
theorem B3042665 : Blo 2027435 3042665 := bstep (se 2 (by rfl) ⟨1140999, by rfl⟩ : syracuseStep 3042665 = 2281999) B2281999
theorem B2028443 : Blo 2027435 2028443 := bstep (se 1 (by rfl) ⟨1521332, by rfl⟩ : syracuseStep 2028443 = 3042665) B3042665
theorem B2166121 : Blo 2027435 2166121 := bbase (se 2 (by rfl) ⟨812295, by rfl⟩ : syracuseStep 2166121 = 1624591) (by norm_num)
theorem B11552645 : Blo 2027435 11552645 := bstep (se 4 (by rfl) ⟨1083060, by rfl⟩ : syracuseStep 11552645 = 2166121) B2166121
theorem B7701763 : Blo 2027435 7701763 := bstep (se 1 (by rfl) ⟨5776322, by rfl⟩ : syracuseStep 7701763 = 11552645) B11552645
theorem B10269017 : Blo 2027435 10269017 := bstep (se 2 (by rfl) ⟨3850881, by rfl⟩ : syracuseStep 10269017 = 7701763) B7701763
theorem B6846011 : Blo 2027435 6846011 := bstep (se 1 (by rfl) ⟨5134508, by rfl⟩ : syracuseStep 6846011 = 10269017) B10269017
theorem B4564007 : Blo 2027435 4564007 := bstep (se 1 (by rfl) ⟨3423005, by rfl⟩ : syracuseStep 4564007 = 6846011) B6846011
theorem B3042671 : Blo 2027435 3042671 := bstep (se 1 (by rfl) ⟨2282003, by rfl⟩ : syracuseStep 3042671 = 4564007) B4564007
theorem B2028447 : Blo 2027435 2028447 := bstep (se 1 (by rfl) ⟨1521335, by rfl⟩ : syracuseStep 2028447 = 3042671) B3042671
theorem B3042677 : Blo 2027435 3042677 := bbase (se 5 (by rfl) ⟨142625, by rfl⟩ : syracuseStep 3042677 = 285251) (by norm_num)
theorem B2028451 : Blo 2027435 2028451 := bstep (se 1 (by rfl) ⟨1521338, by rfl⟩ : syracuseStep 2028451 = 3042677) B3042677
theorem B2888173 : Blo 2027435 2888173 := bbase (se 3 (by rfl) ⟨541532, by rfl⟩ : syracuseStep 2888173 = 1083065) (by norm_num)
theorem B3850897 : Blo 2027435 3850897 := bstep (se 2 (by rfl) ⟨1444086, by rfl⟩ : syracuseStep 3850897 = 2888173) B2888173
theorem B5134529 : Blo 2027435 5134529 := bstep (se 2 (by rfl) ⟨1925448, by rfl⟩ : syracuseStep 5134529 = 3850897) B3850897
theorem B3423019 : Blo 2027435 3423019 := bstep (se 1 (by rfl) ⟨2567264, by rfl⟩ : syracuseStep 3423019 = 5134529) B5134529
theorem B4564025 : Blo 2027435 4564025 := bstep (se 2 (by rfl) ⟨1711509, by rfl⟩ : syracuseStep 4564025 = 3423019) B3423019
theorem B3042683 : Blo 2027435 3042683 := bstep (se 1 (by rfl) ⟨2282012, by rfl⟩ : syracuseStep 3042683 = 4564025) B4564025
theorem B2028455 : Blo 2027435 2028455 := bstep (se 1 (by rfl) ⟨1521341, by rfl⟩ : syracuseStep 2028455 = 3042683) B3042683
theorem B2282017 : Blo 2027435 2282017 := bbase (se 2 (by rfl) ⟨855756, by rfl⟩ : syracuseStep 2282017 = 1711513) (by norm_num)
theorem B3042689 : Blo 2027435 3042689 := bstep (se 2 (by rfl) ⟨1141008, by rfl⟩ : syracuseStep 3042689 = 2282017) B2282017
theorem B2028459 : Blo 2027435 2028459 := bstep (se 1 (by rfl) ⟨1521344, by rfl⟩ : syracuseStep 2028459 = 3042689) B3042689
theorem B5134549 : Blo 2027435 5134549 := bbase (se 7 (by rfl) ⟨60170, by rfl⟩ : syracuseStep 5134549 = 120341) (by norm_num)
theorem B6846065 : Blo 2027435 6846065 := bstep (se 2 (by rfl) ⟨2567274, by rfl⟩ : syracuseStep 6846065 = 5134549) B5134549
theorem B4564043 : Blo 2027435 4564043 := bstep (se 1 (by rfl) ⟨3423032, by rfl⟩ : syracuseStep 4564043 = 6846065) B6846065
theorem B3042695 : Blo 2027435 3042695 := bstep (se 1 (by rfl) ⟨2282021, by rfl⟩ : syracuseStep 3042695 = 4564043) B4564043
theorem B2028463 : Blo 2027435 2028463 := bstep (se 1 (by rfl) ⟨1521347, by rfl⟩ : syracuseStep 2028463 = 3042695) B3042695
theorem B3042701 : Blo 2027435 3042701 := bbase (se 3 (by rfl) ⟨570506, by rfl⟩ : syracuseStep 3042701 = 1141013) (by norm_num)
theorem B2028467 : Blo 2027435 2028467 := bstep (se 1 (by rfl) ⟨1521350, by rfl⟩ : syracuseStep 2028467 = 3042701) B3042701
theorem B4564061 : Blo 2027435 4564061 := bbase (se 3 (by rfl) ⟨855761, by rfl⟩ : syracuseStep 4564061 = 1711523) (by norm_num)
theorem B3042707 : Blo 2027435 3042707 := bstep (se 1 (by rfl) ⟨2282030, by rfl⟩ : syracuseStep 3042707 = 4564061) B4564061
theorem B2028471 : Blo 2027435 2028471 := bstep (se 1 (by rfl) ⟨1521353, by rfl⟩ : syracuseStep 2028471 = 3042707) B3042707
theorem B3423053 : Blo 2027435 3423053 := bbase (se 3 (by rfl) ⟨641822, by rfl⟩ : syracuseStep 3423053 = 1283645) (by norm_num)
theorem B2282035 : Blo 2027435 2282035 := bstep (se 1 (by rfl) ⟨1711526, by rfl⟩ : syracuseStep 2282035 = 3423053) B3423053
theorem B3042713 : Blo 2027435 3042713 := bstep (se 2 (by rfl) ⟨1141017, by rfl⟩ : syracuseStep 3042713 = 2282035) B2282035
theorem B2028475 : Blo 2027435 2028475 := bstep (se 1 (by rfl) ⟨1521356, by rfl⟩ : syracuseStep 2028475 = 3042713) B3042713
theorem B5204645 : Blo 2027435 5204645 := bbase (se 4 (by rfl) ⟨487935, by rfl⟩ : syracuseStep 5204645 = 975871) (by norm_num)
theorem B3469763 : Blo 2027435 3469763 := bstep (se 1 (by rfl) ⟨2602322, by rfl⟩ : syracuseStep 3469763 = 5204645) B5204645
theorem B9252701 : Blo 2027435 9252701 := bstep (se 3 (by rfl) ⟨1734881, by rfl⟩ : syracuseStep 9252701 = 3469763) B3469763
theorem B6168467 : Blo 2027435 6168467 := bstep (se 1 (by rfl) ⟨4626350, by rfl⟩ : syracuseStep 6168467 = 9252701) B9252701
theorem B4112311 : Blo 2027435 4112311 := bstep (se 1 (by rfl) ⟨3084233, by rfl⟩ : syracuseStep 4112311 = 6168467) B6168467
theorem B5483081 : Blo 2027435 5483081 := bstep (se 2 (by rfl) ⟨2056155, by rfl⟩ : syracuseStep 5483081 = 4112311) B4112311
theorem B3655387 : Blo 2027435 3655387 := bstep (se 1 (by rfl) ⟨2741540, by rfl⟩ : syracuseStep 3655387 = 5483081) B5483081
theorem B19495397 : Blo 2027435 19495397 := bstep (se 4 (by rfl) ⟨1827693, by rfl⟩ : syracuseStep 19495397 = 3655387) B3655387
theorem B12996931 : Blo 2027435 12996931 := bstep (se 1 (by rfl) ⟨9747698, by rfl⟩ : syracuseStep 12996931 = 19495397) B19495397
theorem B17329241 : Blo 2027435 17329241 := bstep (se 2 (by rfl) ⟨6498465, by rfl⟩ : syracuseStep 17329241 = 12996931) B12996931
theorem B11552827 : Blo 2027435 11552827 := bstep (se 1 (by rfl) ⟨8664620, by rfl⟩ : syracuseStep 11552827 = 17329241) B17329241
theorem B15403769 : Blo 2027435 15403769 := bstep (se 2 (by rfl) ⟨5776413, by rfl⟩ : syracuseStep 15403769 = 11552827) B11552827
theorem B10269179 : Blo 2027435 10269179 := bstep (se 1 (by rfl) ⟨7701884, by rfl⟩ : syracuseStep 10269179 = 15403769) B15403769
theorem B6846119 : Blo 2027435 6846119 := bstep (se 1 (by rfl) ⟨5134589, by rfl⟩ : syracuseStep 6846119 = 10269179) B10269179
theorem B4564079 : Blo 2027435 4564079 := bstep (se 1 (by rfl) ⟨3423059, by rfl⟩ : syracuseStep 4564079 = 6846119) B6846119
theorem B3042719 : Blo 2027435 3042719 := bstep (se 1 (by rfl) ⟨2282039, by rfl⟩ : syracuseStep 3042719 = 4564079) B4564079
theorem B2028479 : Blo 2027435 2028479 := bstep (se 1 (by rfl) ⟨1521359, by rfl⟩ : syracuseStep 2028479 = 3042719) B3042719
theorem B3042725 : Blo 2027435 3042725 := bbase (se 4 (by rfl) ⟨285255, by rfl⟩ : syracuseStep 3042725 = 570511) (by norm_num)
theorem B2028483 : Blo 2027435 2028483 := bstep (se 1 (by rfl) ⟨1521362, by rfl⟩ : syracuseStep 2028483 = 3042725) B3042725
theorem B2567305 : Blo 2027435 2567305 := bbase (se 2 (by rfl) ⟨962739, by rfl⟩ : syracuseStep 2567305 = 1925479) (by norm_num)
theorem B3423073 : Blo 2027435 3423073 := bstep (se 2 (by rfl) ⟨1283652, by rfl⟩ : syracuseStep 3423073 = 2567305) B2567305
theorem B4564097 : Blo 2027435 4564097 := bstep (se 2 (by rfl) ⟨1711536, by rfl⟩ : syracuseStep 4564097 = 3423073) B3423073
theorem B3042731 : Blo 2027435 3042731 := bstep (se 1 (by rfl) ⟨2282048, by rfl⟩ : syracuseStep 3042731 = 4564097) B4564097
theorem B2028487 : Blo 2027435 2028487 := bstep (se 1 (by rfl) ⟨1521365, by rfl⟩ : syracuseStep 2028487 = 3042731) B3042731
theorem B2282053 : Blo 2027435 2282053 := bbase (se 4 (by rfl) ⟨213942, by rfl⟩ : syracuseStep 2282053 = 427885) (by norm_num)
theorem B3042737 : Blo 2027435 3042737 := bstep (se 2 (by rfl) ⟨1141026, by rfl⟩ : syracuseStep 3042737 = 2282053) B2282053
theorem B2028491 : Blo 2027435 2028491 := bstep (se 1 (by rfl) ⟨1521368, by rfl⟩ : syracuseStep 2028491 = 3042737) B3042737
theorem B3850973 : Blo 2027435 3850973 := bbase (se 3 (by rfl) ⟨722057, by rfl⟩ : syracuseStep 3850973 = 1444115) (by norm_num)
theorem B2567315 : Blo 2027435 2567315 := bstep (se 1 (by rfl) ⟨1925486, by rfl⟩ : syracuseStep 2567315 = 3850973) B3850973
theorem B6846173 : Blo 2027435 6846173 := bstep (se 3 (by rfl) ⟨1283657, by rfl⟩ : syracuseStep 6846173 = 2567315) B2567315
theorem B4564115 : Blo 2027435 4564115 := bstep (se 1 (by rfl) ⟨3423086, by rfl⟩ : syracuseStep 4564115 = 6846173) B6846173
theorem B3042743 : Blo 2027435 3042743 := bstep (se 1 (by rfl) ⟨2282057, by rfl⟩ : syracuseStep 3042743 = 4564115) B4564115
theorem B2028495 : Blo 2027435 2028495 := bstep (se 1 (by rfl) ⟨1521371, by rfl⟩ : syracuseStep 2028495 = 3042743) B3042743
theorem B3042749 : Blo 2027435 3042749 := bbase (se 3 (by rfl) ⟨570515, by rfl⟩ : syracuseStep 3042749 = 1141031) (by norm_num)
theorem B2028499 : Blo 2027435 2028499 := bstep (se 1 (by rfl) ⟨1521374, by rfl⟩ : syracuseStep 2028499 = 3042749) B3042749
theorem B4564133 : Blo 2027435 4564133 := bbase (se 4 (by rfl) ⟨427887, by rfl⟩ : syracuseStep 4564133 = 855775) (by norm_num)
theorem B3042755 : Blo 2027435 3042755 := bstep (se 1 (by rfl) ⟨2282066, by rfl⟩ : syracuseStep 3042755 = 4564133) B4564133
theorem B2028503 : Blo 2027435 2028503 := bstep (se 1 (by rfl) ⟨1521377, by rfl⟩ : syracuseStep 2028503 = 3042755) B3042755
theorem B5134661 : Blo 2027435 5134661 := bbase (se 4 (by rfl) ⟨481374, by rfl⟩ : syracuseStep 5134661 = 962749) (by norm_num)
theorem B3423107 : Blo 2027435 3423107 := bstep (se 1 (by rfl) ⟨2567330, by rfl⟩ : syracuseStep 3423107 = 5134661) B5134661
theorem B2282071 : Blo 2027435 2282071 := bstep (se 1 (by rfl) ⟨1711553, by rfl⟩ : syracuseStep 2282071 = 3423107) B3423107
theorem B3042761 : Blo 2027435 3042761 := bstep (se 2 (by rfl) ⟨1141035, by rfl⟩ : syracuseStep 3042761 = 2282071) B2282071
theorem B2028507 : Blo 2027435 2028507 := bstep (se 1 (by rfl) ⟨1521380, by rfl⟩ : syracuseStep 2028507 = 3042761) B3042761
theorem B6168565 : Blo 2027435 6168565 := bbase (se 5 (by rfl) ⟨289151, by rfl⟩ : syracuseStep 6168565 = 578303) (by norm_num)
theorem B8224753 : Blo 2027435 8224753 := bstep (se 2 (by rfl) ⟨3084282, by rfl⟩ : syracuseStep 8224753 = 6168565) B6168565
theorem B10966337 : Blo 2027435 10966337 := bstep (se 2 (by rfl) ⟨4112376, by rfl⟩ : syracuseStep 10966337 = 8224753) B8224753
theorem B7310891 : Blo 2027435 7310891 := bstep (se 1 (by rfl) ⟨5483168, by rfl⟩ : syracuseStep 7310891 = 10966337) B10966337
theorem B4873927 : Blo 2027435 4873927 := bstep (se 1 (by rfl) ⟨3655445, by rfl⟩ : syracuseStep 4873927 = 7310891) B7310891
theorem B6498569 : Blo 2027435 6498569 := bstep (se 2 (by rfl) ⟨2436963, by rfl⟩ : syracuseStep 6498569 = 4873927) B4873927
theorem B4332379 : Blo 2027435 4332379 := bstep (se 1 (by rfl) ⟨3249284, by rfl⟩ : syracuseStep 4332379 = 6498569) B6498569
theorem B5776505 : Blo 2027435 5776505 := bstep (se 2 (by rfl) ⟨2166189, by rfl⟩ : syracuseStep 5776505 = 4332379) B4332379
theorem B3851003 : Blo 2027435 3851003 := bstep (se 1 (by rfl) ⟨2888252, by rfl⟩ : syracuseStep 3851003 = 5776505) B5776505
theorem B10269341 : Blo 2027435 10269341 := bstep (se 3 (by rfl) ⟨1925501, by rfl⟩ : syracuseStep 10269341 = 3851003) B3851003
theorem B6846227 : Blo 2027435 6846227 := bstep (se 1 (by rfl) ⟨5134670, by rfl⟩ : syracuseStep 6846227 = 10269341) B10269341
theorem B4564151 : Blo 2027435 4564151 := bstep (se 1 (by rfl) ⟨3423113, by rfl⟩ : syracuseStep 4564151 = 6846227) B6846227
theorem B3042767 : Blo 2027435 3042767 := bstep (se 1 (by rfl) ⟨2282075, by rfl⟩ : syracuseStep 3042767 = 4564151) B4564151
theorem B2028511 : Blo 2027435 2028511 := bstep (se 1 (by rfl) ⟨1521383, by rfl⟩ : syracuseStep 2028511 = 3042767) B3042767
theorem B3042773 : Blo 2027435 3042773 := bbase (se 7 (by rfl) ⟨35657, by rfl⟩ : syracuseStep 3042773 = 71315) (by norm_num)
theorem B2028515 : Blo 2027435 2028515 := bstep (se 1 (by rfl) ⟨1521386, by rfl⟩ : syracuseStep 2028515 = 3042773) B3042773
theorem B7702037 : Blo 2027435 7702037 := bbase (se 6 (by rfl) ⟨180516, by rfl⟩ : syracuseStep 7702037 = 361033) (by norm_num)
theorem B5134691 : Blo 2027435 5134691 := bstep (se 1 (by rfl) ⟨3851018, by rfl⟩ : syracuseStep 5134691 = 7702037) B7702037
theorem B3423127 : Blo 2027435 3423127 := bstep (se 1 (by rfl) ⟨2567345, by rfl⟩ : syracuseStep 3423127 = 5134691) B5134691
theorem B4564169 : Blo 2027435 4564169 := bstep (se 2 (by rfl) ⟨1711563, by rfl⟩ : syracuseStep 4564169 = 3423127) B3423127
theorem B3042779 : Blo 2027435 3042779 := bstep (se 1 (by rfl) ⟨2282084, by rfl⟩ : syracuseStep 3042779 = 4564169) B4564169
theorem B2028519 : Blo 2027435 2028519 := bstep (se 1 (by rfl) ⟨1521389, by rfl⟩ : syracuseStep 2028519 = 3042779) B3042779
theorem B2282089 : Blo 2027435 2282089 := bbase (se 2 (by rfl) ⟨855783, by rfl⟩ : syracuseStep 2282089 = 1711567) (by norm_num)
theorem B3042785 : Blo 2027435 3042785 := bstep (se 2 (by rfl) ⟨1141044, by rfl⟩ : syracuseStep 3042785 = 2282089) B2282089
theorem B2028523 : Blo 2027435 2028523 := bstep (se 1 (by rfl) ⟨1521392, by rfl⟩ : syracuseStep 2028523 = 3042785) B3042785
theorem B4332413 : Blo 2027435 4332413 := bbase (se 3 (by rfl) ⟨812327, by rfl⟩ : syracuseStep 4332413 = 1624655) (by norm_num)
theorem B11553101 : Blo 2027435 11553101 := bstep (se 3 (by rfl) ⟨2166206, by rfl⟩ : syracuseStep 11553101 = 4332413) B4332413
theorem B7702067 : Blo 2027435 7702067 := bstep (se 1 (by rfl) ⟨5776550, by rfl⟩ : syracuseStep 7702067 = 11553101) B11553101
theorem B5134711 : Blo 2027435 5134711 := bstep (se 1 (by rfl) ⟨3851033, by rfl⟩ : syracuseStep 5134711 = 7702067) B7702067
theorem B6846281 : Blo 2027435 6846281 := bstep (se 2 (by rfl) ⟨2567355, by rfl⟩ : syracuseStep 6846281 = 5134711) B5134711
theorem B4564187 : Blo 2027435 4564187 := bstep (se 1 (by rfl) ⟨3423140, by rfl⟩ : syracuseStep 4564187 = 6846281) B6846281
theorem B3042791 : Blo 2027435 3042791 := bstep (se 1 (by rfl) ⟨2282093, by rfl⟩ : syracuseStep 3042791 = 4564187) B4564187
theorem B2028527 : Blo 2027435 2028527 := bstep (se 1 (by rfl) ⟨1521395, by rfl⟩ : syracuseStep 2028527 = 3042791) B3042791
theorem B3042797 : Blo 2027435 3042797 := bbase (se 3 (by rfl) ⟨570524, by rfl⟩ : syracuseStep 3042797 = 1141049) (by norm_num)
theorem B2028531 : Blo 2027435 2028531 := bstep (se 1 (by rfl) ⟨1521398, by rfl⟩ : syracuseStep 2028531 = 3042797) B3042797
theorem B4564205 : Blo 2027435 4564205 := bbase (se 3 (by rfl) ⟨855788, by rfl⟩ : syracuseStep 4564205 = 1711577) (by norm_num)
theorem B3042803 : Blo 2027435 3042803 := bstep (se 1 (by rfl) ⟨2282102, by rfl⟩ : syracuseStep 3042803 = 4564205) B4564205
theorem B2028535 : Blo 2027435 2028535 := bstep (se 1 (by rfl) ⟨1521401, by rfl⟩ : syracuseStep 2028535 = 3042803) B3042803
theorem B2888293 : Blo 2027435 2888293 := bbase (se 4 (by rfl) ⟨270777, by rfl⟩ : syracuseStep 2888293 = 541555) (by norm_num)
theorem B3851057 : Blo 2027435 3851057 := bstep (se 2 (by rfl) ⟨1444146, by rfl⟩ : syracuseStep 3851057 = 2888293) B2888293
theorem B2567371 : Blo 2027435 2567371 := bstep (se 1 (by rfl) ⟨1925528, by rfl⟩ : syracuseStep 2567371 = 3851057) B3851057
theorem B3423161 : Blo 2027435 3423161 := bstep (se 2 (by rfl) ⟨1283685, by rfl⟩ : syracuseStep 3423161 = 2567371) B2567371
theorem B2282107 : Blo 2027435 2282107 := bstep (se 1 (by rfl) ⟨1711580, by rfl⟩ : syracuseStep 2282107 = 3423161) B3423161
theorem B3042809 : Blo 2027435 3042809 := bstep (se 2 (by rfl) ⟨1141053, by rfl⟩ : syracuseStep 3042809 = 2282107) B2282107
theorem B2028539 : Blo 2027435 2028539 := bstep (se 1 (by rfl) ⟨1521404, by rfl⟩ : syracuseStep 2028539 = 3042809) B3042809
theorem B21933013 : Blo 2027435 21933013 := bbase (se 7 (by rfl) ⟨257027, by rfl⟩ : syracuseStep 21933013 = 514055) (by norm_num)
theorem B29244017 : Blo 2027435 29244017 := bstep (se 2 (by rfl) ⟨10966506, by rfl⟩ : syracuseStep 29244017 = 21933013) B21933013
theorem B77984045 : Blo 2027435 77984045 := bstep (se 3 (by rfl) ⟨14622008, by rfl⟩ : syracuseStep 77984045 = 29244017) B29244017
theorem B51989363 : Blo 2027435 51989363 := bstep (se 1 (by rfl) ⟨38992022, by rfl⟩ : syracuseStep 51989363 = 77984045) B77984045
theorem B34659575 : Blo 2027435 34659575 := bstep (se 1 (by rfl) ⟨25994681, by rfl⟩ : syracuseStep 34659575 = 51989363) B51989363
theorem B23106383 : Blo 2027435 23106383 := bstep (se 1 (by rfl) ⟨17329787, by rfl⟩ : syracuseStep 23106383 = 34659575) B34659575
theorem B15404255 : Blo 2027435 15404255 := bstep (se 1 (by rfl) ⟨11553191, by rfl⟩ : syracuseStep 15404255 = 23106383) B23106383
theorem B10269503 : Blo 2027435 10269503 := bstep (se 1 (by rfl) ⟨7702127, by rfl⟩ : syracuseStep 10269503 = 15404255) B15404255
theorem B6846335 : Blo 2027435 6846335 := bstep (se 1 (by rfl) ⟨5134751, by rfl⟩ : syracuseStep 6846335 = 10269503) B10269503
theorem B4564223 : Blo 2027435 4564223 := bstep (se 1 (by rfl) ⟨3423167, by rfl⟩ : syracuseStep 4564223 = 6846335) B6846335
theorem B3042815 : Blo 2027435 3042815 := bstep (se 1 (by rfl) ⟨2282111, by rfl⟩ : syracuseStep 3042815 = 4564223) B4564223
theorem B2028543 : Blo 2027435 2028543 := bstep (se 1 (by rfl) ⟨1521407, by rfl⟩ : syracuseStep 2028543 = 3042815) B3042815
theorem B3042821 : Blo 2027435 3042821 := bbase (se 4 (by rfl) ⟨285264, by rfl⟩ : syracuseStep 3042821 = 570529) (by norm_num)
theorem B2028547 : Blo 2027435 2028547 := bstep (se 1 (by rfl) ⟨1521410, by rfl⟩ : syracuseStep 2028547 = 3042821) B3042821
theorem B3423181 : Blo 2027435 3423181 := bbase (se 3 (by rfl) ⟨641846, by rfl⟩ : syracuseStep 3423181 = 1283693) (by norm_num)
theorem B4564241 : Blo 2027435 4564241 := bstep (se 2 (by rfl) ⟨1711590, by rfl⟩ : syracuseStep 4564241 = 3423181) B3423181
theorem B3042827 : Blo 2027435 3042827 := bstep (se 1 (by rfl) ⟨2282120, by rfl⟩ : syracuseStep 3042827 = 4564241) B4564241
theorem B2028551 : Blo 2027435 2028551 := bstep (se 1 (by rfl) ⟨1521413, by rfl⟩ : syracuseStep 2028551 = 3042827) B3042827
theorem B2282125 : Blo 2027435 2282125 := bbase (se 3 (by rfl) ⟨427898, by rfl⟩ : syracuseStep 2282125 = 855797) (by norm_num)
theorem B3042833 : Blo 2027435 3042833 := bstep (se 2 (by rfl) ⟨1141062, by rfl⟩ : syracuseStep 3042833 = 2282125) B2282125
theorem B2028555 : Blo 2027435 2028555 := bstep (se 1 (by rfl) ⟨1521416, by rfl⟩ : syracuseStep 2028555 = 3042833) B3042833
theorem B6846389 : Blo 2027435 6846389 := bbase (se 5 (by rfl) ⟨320924, by rfl⟩ : syracuseStep 6846389 = 641849) (by norm_num)
theorem B4564259 : Blo 2027435 4564259 := bstep (se 1 (by rfl) ⟨3423194, by rfl⟩ : syracuseStep 4564259 = 6846389) B6846389
theorem B3042839 : Blo 2027435 3042839 := bstep (se 1 (by rfl) ⟨2282129, by rfl⟩ : syracuseStep 3042839 = 4564259) B4564259
theorem B2028559 : Blo 2027435 2028559 := bstep (se 1 (by rfl) ⟨1521419, by rfl⟩ : syracuseStep 2028559 = 3042839) B3042839
theorem B3042845 : Blo 2027435 3042845 := bbase (se 3 (by rfl) ⟨570533, by rfl⟩ : syracuseStep 3042845 = 1141067) (by norm_num)
theorem B2028563 : Blo 2027435 2028563 := bstep (se 1 (by rfl) ⟨1521422, by rfl⟩ : syracuseStep 2028563 = 3042845) B3042845
theorem B4564277 : Blo 2027435 4564277 := bbase (se 5 (by rfl) ⟨213950, by rfl⟩ : syracuseStep 4564277 = 427901) (by norm_num)
theorem B3042851 : Blo 2027435 3042851 := bstep (se 1 (by rfl) ⟨2282138, by rfl⟩ : syracuseStep 3042851 = 4564277) B4564277
theorem B2028567 : Blo 2027435 2028567 := bstep (se 1 (by rfl) ⟨1521425, by rfl⟩ : syracuseStep 2028567 = 3042851) B3042851
theorem B2056249 : Blo 2027435 2056249 := bbase (se 2 (by rfl) ⟨771093, by rfl⟩ : syracuseStep 2056249 = 1542187) (by norm_num)
theorem B10966661 : Blo 2027435 10966661 := bstep (se 4 (by rfl) ⟨1028124, by rfl⟩ : syracuseStep 10966661 = 2056249) B2056249
theorem B7311107 : Blo 2027435 7311107 := bstep (se 1 (by rfl) ⟨5483330, by rfl⟩ : syracuseStep 7311107 = 10966661) B10966661
theorem B19496285 : Blo 2027435 19496285 := bstep (se 3 (by rfl) ⟨3655553, by rfl⟩ : syracuseStep 19496285 = 7311107) B7311107
theorem B12997523 : Blo 2027435 12997523 := bstep (se 1 (by rfl) ⟨9748142, by rfl⟩ : syracuseStep 12997523 = 19496285) B19496285
theorem B8665015 : Blo 2027435 8665015 := bstep (se 1 (by rfl) ⟨6498761, by rfl⟩ : syracuseStep 8665015 = 12997523) B12997523
theorem B11553353 : Blo 2027435 11553353 := bstep (se 2 (by rfl) ⟨4332507, by rfl⟩ : syracuseStep 11553353 = 8665015) B8665015
theorem B7702235 : Blo 2027435 7702235 := bstep (se 1 (by rfl) ⟨5776676, by rfl⟩ : syracuseStep 7702235 = 11553353) B11553353
theorem B5134823 : Blo 2027435 5134823 := bstep (se 1 (by rfl) ⟨3851117, by rfl⟩ : syracuseStep 5134823 = 7702235) B7702235
theorem B3423215 : Blo 2027435 3423215 := bstep (se 1 (by rfl) ⟨2567411, by rfl⟩ : syracuseStep 3423215 = 5134823) B5134823
theorem B2282143 : Blo 2027435 2282143 := bstep (se 1 (by rfl) ⟨1711607, by rfl⟩ : syracuseStep 2282143 = 3423215) B3423215
theorem B3042857 : Blo 2027435 3042857 := bstep (se 2 (by rfl) ⟨1141071, by rfl⟩ : syracuseStep 3042857 = 2282143) B2282143
theorem B2028571 : Blo 2027435 2028571 := bstep (se 1 (by rfl) ⟨1521428, by rfl⟩ : syracuseStep 2028571 = 3042857) B3042857
theorem B19762325 : Blo 2027435 19762325 := bbase (se 6 (by rfl) ⟨463179, by rfl⟩ : syracuseStep 19762325 = 926359) (by norm_num)
theorem B13174883 : Blo 2027435 13174883 := bstep (se 1 (by rfl) ⟨9881162, by rfl⟩ : syracuseStep 13174883 = 19762325) B19762325
theorem B8783255 : Blo 2027435 8783255 := bstep (se 1 (by rfl) ⟨6587441, by rfl⟩ : syracuseStep 8783255 = 13174883) B13174883
theorem B5855503 : Blo 2027435 5855503 := bstep (se 1 (by rfl) ⟨4391627, by rfl⟩ : syracuseStep 5855503 = 8783255) B8783255
theorem B7807337 : Blo 2027435 7807337 := bstep (se 2 (by rfl) ⟨2927751, by rfl⟩ : syracuseStep 7807337 = 5855503) B5855503
theorem B5204891 : Blo 2027435 5204891 := bstep (se 1 (by rfl) ⟨3903668, by rfl⟩ : syracuseStep 5204891 = 7807337) B7807337
theorem B3469927 : Blo 2027435 3469927 := bstep (se 1 (by rfl) ⟨2602445, by rfl⟩ : syracuseStep 3469927 = 5204891) B5204891
theorem B4626569 : Blo 2027435 4626569 := bstep (se 2 (by rfl) ⟨1734963, by rfl⟩ : syracuseStep 4626569 = 3469927) B3469927
theorem B12337517 : Blo 2027435 12337517 := bstep (se 3 (by rfl) ⟨2313284, by rfl⟩ : syracuseStep 12337517 = 4626569) B4626569
theorem B8225011 : Blo 2027435 8225011 := bstep (se 1 (by rfl) ⟨6168758, by rfl⟩ : syracuseStep 8225011 = 12337517) B12337517
theorem B10966681 : Blo 2027435 10966681 := bstep (se 2 (by rfl) ⟨4112505, by rfl⟩ : syracuseStep 10966681 = 8225011) B8225011
theorem B14622241 : Blo 2027435 14622241 := bstep (se 2 (by rfl) ⟨5483340, by rfl⟩ : syracuseStep 14622241 = 10966681) B10966681
theorem B19496321 : Blo 2027435 19496321 := bstep (se 2 (by rfl) ⟨7311120, by rfl⟩ : syracuseStep 19496321 = 14622241) B14622241
theorem B12997547 : Blo 2027435 12997547 := bstep (se 1 (by rfl) ⟨9748160, by rfl⟩ : syracuseStep 12997547 = 19496321) B19496321
theorem B8665031 : Blo 2027435 8665031 := bstep (se 1 (by rfl) ⟨6498773, by rfl⟩ : syracuseStep 8665031 = 12997547) B12997547
theorem B5776687 : Blo 2027435 5776687 := bstep (se 1 (by rfl) ⟨4332515, by rfl⟩ : syracuseStep 5776687 = 8665031) B8665031
theorem B7702249 : Blo 2027435 7702249 := bstep (se 2 (by rfl) ⟨2888343, by rfl⟩ : syracuseStep 7702249 = 5776687) B5776687
theorem B10269665 : Blo 2027435 10269665 := bstep (se 2 (by rfl) ⟨3851124, by rfl⟩ : syracuseStep 10269665 = 7702249) B7702249
theorem B6846443 : Blo 2027435 6846443 := bstep (se 1 (by rfl) ⟨5134832, by rfl⟩ : syracuseStep 6846443 = 10269665) B10269665
theorem B4564295 : Blo 2027435 4564295 := bstep (se 1 (by rfl) ⟨3423221, by rfl⟩ : syracuseStep 4564295 = 6846443) B6846443
theorem B3042863 : Blo 2027435 3042863 := bstep (se 1 (by rfl) ⟨2282147, by rfl⟩ : syracuseStep 3042863 = 4564295) B4564295
theorem B2028575 : Blo 2027435 2028575 := bstep (se 1 (by rfl) ⟨1521431, by rfl⟩ : syracuseStep 2028575 = 3042863) B3042863
theorem B3042869 : Blo 2027435 3042869 := bbase (se 5 (by rfl) ⟨142634, by rfl⟩ : syracuseStep 3042869 = 285269) (by norm_num)
theorem B2028579 : Blo 2027435 2028579 := bstep (se 1 (by rfl) ⟨1521434, by rfl⟩ : syracuseStep 2028579 = 3042869) B3042869
theorem B5134853 : Blo 2027435 5134853 := bbase (se 4 (by rfl) ⟨481392, by rfl⟩ : syracuseStep 5134853 = 962785) (by norm_num)
theorem B3423235 : Blo 2027435 3423235 := bstep (se 1 (by rfl) ⟨2567426, by rfl⟩ : syracuseStep 3423235 = 5134853) B5134853
theorem B4564313 : Blo 2027435 4564313 := bstep (se 2 (by rfl) ⟨1711617, by rfl⟩ : syracuseStep 4564313 = 3423235) B3423235
theorem B3042875 : Blo 2027435 3042875 := bstep (se 1 (by rfl) ⟨2282156, by rfl⟩ : syracuseStep 3042875 = 4564313) B4564313
theorem B2028583 : Blo 2027435 2028583 := bstep (se 1 (by rfl) ⟨1521437, by rfl⟩ : syracuseStep 2028583 = 3042875) B3042875
theorem B2282161 : Blo 2027435 2282161 := bbase (se 2 (by rfl) ⟨855810, by rfl⟩ : syracuseStep 2282161 = 1711621) (by norm_num)
theorem B3042881 : Blo 2027435 3042881 := bstep (se 2 (by rfl) ⟨1141080, by rfl⟩ : syracuseStep 3042881 = 2282161) B2282161
theorem B2028587 : Blo 2027435 2028587 := bstep (se 1 (by rfl) ⟨1521440, by rfl⟩ : syracuseStep 2028587 = 3042881) B3042881
theorem B3249413 : Blo 2027435 3249413 := bbase (se 4 (by rfl) ⟨304632, by rfl⟩ : syracuseStep 3249413 = 609265) (by norm_num)
theorem B2166275 : Blo 2027435 2166275 := bstep (se 1 (by rfl) ⟨1624706, by rfl⟩ : syracuseStep 2166275 = 3249413) B3249413
theorem B5776733 : Blo 2027435 5776733 := bstep (se 3 (by rfl) ⟨1083137, by rfl⟩ : syracuseStep 5776733 = 2166275) B2166275
theorem B3851155 : Blo 2027435 3851155 := bstep (se 1 (by rfl) ⟨2888366, by rfl⟩ : syracuseStep 3851155 = 5776733) B5776733
theorem B5134873 : Blo 2027435 5134873 := bstep (se 2 (by rfl) ⟨1925577, by rfl⟩ : syracuseStep 5134873 = 3851155) B3851155
theorem B6846497 : Blo 2027435 6846497 := bstep (se 2 (by rfl) ⟨2567436, by rfl⟩ : syracuseStep 6846497 = 5134873) B5134873
theorem B4564331 : Blo 2027435 4564331 := bstep (se 1 (by rfl) ⟨3423248, by rfl⟩ : syracuseStep 4564331 = 6846497) B6846497
theorem B3042887 : Blo 2027435 3042887 := bstep (se 1 (by rfl) ⟨2282165, by rfl⟩ : syracuseStep 3042887 = 4564331) B4564331
theorem B2028591 : Blo 2027435 2028591 := bstep (se 1 (by rfl) ⟨1521443, by rfl⟩ : syracuseStep 2028591 = 3042887) B3042887
theorem B3042893 : Blo 2027435 3042893 := bbase (se 3 (by rfl) ⟨570542, by rfl⟩ : syracuseStep 3042893 = 1141085) (by norm_num)
theorem B2028595 : Blo 2027435 2028595 := bstep (se 1 (by rfl) ⟨1521446, by rfl⟩ : syracuseStep 2028595 = 3042893) B3042893
theorem B4564349 : Blo 2027435 4564349 := bbase (se 3 (by rfl) ⟨855815, by rfl⟩ : syracuseStep 4564349 = 1711631) (by norm_num)
theorem B3042899 : Blo 2027435 3042899 := bstep (se 1 (by rfl) ⟨2282174, by rfl⟩ : syracuseStep 3042899 = 4564349) B4564349
theorem B2028599 : Blo 2027435 2028599 := bstep (se 1 (by rfl) ⟨1521449, by rfl⟩ : syracuseStep 2028599 = 3042899) B3042899
theorem B3423269 : Blo 2027435 3423269 := bbase (se 4 (by rfl) ⟨320931, by rfl⟩ : syracuseStep 3423269 = 641863) (by norm_num)
theorem B2282179 : Blo 2027435 2282179 := bstep (se 1 (by rfl) ⟨1711634, by rfl⟩ : syracuseStep 2282179 = 3423269) B3423269
theorem B3042905 : Blo 2027435 3042905 := bstep (se 2 (by rfl) ⟨1141089, by rfl⟩ : syracuseStep 3042905 = 2282179) B2282179
theorem B2028603 : Blo 2027435 2028603 := bstep (se 1 (by rfl) ⟨1521452, by rfl⟩ : syracuseStep 2028603 = 3042905) B3042905
theorem B2888389 : Blo 2027435 2888389 := bbase (se 4 (by rfl) ⟨270786, by rfl⟩ : syracuseStep 2888389 = 541573) (by norm_num)
theorem B15404741 : Blo 2027435 15404741 := bstep (se 4 (by rfl) ⟨1444194, by rfl⟩ : syracuseStep 15404741 = 2888389) B2888389
theorem B10269827 : Blo 2027435 10269827 := bstep (se 1 (by rfl) ⟨7702370, by rfl⟩ : syracuseStep 10269827 = 15404741) B15404741
theorem B6846551 : Blo 2027435 6846551 := bstep (se 1 (by rfl) ⟨5134913, by rfl⟩ : syracuseStep 6846551 = 10269827) B10269827
theorem B4564367 : Blo 2027435 4564367 := bstep (se 1 (by rfl) ⟨3423275, by rfl⟩ : syracuseStep 4564367 = 6846551) B6846551
theorem B3042911 : Blo 2027435 3042911 := bstep (se 1 (by rfl) ⟨2282183, by rfl⟩ : syracuseStep 3042911 = 4564367) B4564367
theorem B2028607 : Blo 2027435 2028607 := bstep (se 1 (by rfl) ⟨1521455, by rfl⟩ : syracuseStep 2028607 = 3042911) B3042911
theorem B3042917 : Blo 2027435 3042917 := bbase (se 4 (by rfl) ⟨285273, by rfl⟩ : syracuseStep 3042917 = 570547) (by norm_num)
theorem B2028611 : Blo 2027435 2028611 := bstep (se 1 (by rfl) ⟨1521458, by rfl⟩ : syracuseStep 2028611 = 3042917) B3042917
theorem B2166301 : Blo 2027435 2166301 := bbase (se 3 (by rfl) ⟨406181, by rfl⟩ : syracuseStep 2166301 = 812363) (by norm_num)
theorem B2888401 : Blo 2027435 2888401 := bstep (se 2 (by rfl) ⟨1083150, by rfl⟩ : syracuseStep 2888401 = 2166301) B2166301
theorem B3851201 : Blo 2027435 3851201 := bstep (se 2 (by rfl) ⟨1444200, by rfl⟩ : syracuseStep 3851201 = 2888401) B2888401
theorem B2567467 : Blo 2027435 2567467 := bstep (se 1 (by rfl) ⟨1925600, by rfl⟩ : syracuseStep 2567467 = 3851201) B3851201
theorem B3423289 : Blo 2027435 3423289 := bstep (se 2 (by rfl) ⟨1283733, by rfl⟩ : syracuseStep 3423289 = 2567467) B2567467
theorem B4564385 : Blo 2027435 4564385 := bstep (se 2 (by rfl) ⟨1711644, by rfl⟩ : syracuseStep 4564385 = 3423289) B3423289
theorem B3042923 : Blo 2027435 3042923 := bstep (se 1 (by rfl) ⟨2282192, by rfl⟩ : syracuseStep 3042923 = 4564385) B4564385
theorem B2028615 : Blo 2027435 2028615 := bstep (se 1 (by rfl) ⟨1521461, by rfl⟩ : syracuseStep 2028615 = 3042923) B3042923
theorem B2282197 : Blo 2027435 2282197 := bbase (se 7 (by rfl) ⟨26744, by rfl⟩ : syracuseStep 2282197 = 53489) (by norm_num)
theorem B3042929 : Blo 2027435 3042929 := bstep (se 2 (by rfl) ⟨1141098, by rfl⟩ : syracuseStep 3042929 = 2282197) B2282197
theorem B2028619 : Blo 2027435 2028619 := bstep (se 1 (by rfl) ⟨1521464, by rfl⟩ : syracuseStep 2028619 = 3042929) B3042929
theorem B2567477 : Blo 2027435 2567477 := bbase (se 5 (by rfl) ⟨120350, by rfl⟩ : syracuseStep 2567477 = 240701) (by norm_num)
theorem B6846605 : Blo 2027435 6846605 := bstep (se 3 (by rfl) ⟨1283738, by rfl⟩ : syracuseStep 6846605 = 2567477) B2567477
theorem B4564403 : Blo 2027435 4564403 := bstep (se 1 (by rfl) ⟨3423302, by rfl⟩ : syracuseStep 4564403 = 6846605) B6846605
theorem B3042935 : Blo 2027435 3042935 := bstep (se 1 (by rfl) ⟨2282201, by rfl⟩ : syracuseStep 3042935 = 4564403) B4564403
theorem B2028623 : Blo 2027435 2028623 := bstep (se 1 (by rfl) ⟨1521467, by rfl⟩ : syracuseStep 2028623 = 3042935) B3042935
theorem B3042941 : Blo 2027435 3042941 := bbase (se 3 (by rfl) ⟨570551, by rfl⟩ : syracuseStep 3042941 = 1141103) (by norm_num)
theorem B2028627 : Blo 2027435 2028627 := bstep (se 1 (by rfl) ⟨1521470, by rfl⟩ : syracuseStep 2028627 = 3042941) B3042941
theorem B4564421 : Blo 2027435 4564421 := bbase (se 4 (by rfl) ⟨427914, by rfl⟩ : syracuseStep 4564421 = 855829) (by norm_num)
theorem B3042947 : Blo 2027435 3042947 := bstep (se 1 (by rfl) ⟨2282210, by rfl⟩ : syracuseStep 3042947 = 4564421) B4564421
theorem B2028631 : Blo 2027435 2028631 := bstep (se 1 (by rfl) ⟨1521473, by rfl⟩ : syracuseStep 2028631 = 3042947) B3042947
theorem B14622677 : Blo 2027435 14622677 := bbase (se 7 (by rfl) ⟨171359, by rfl⟩ : syracuseStep 14622677 = 342719) (by norm_num)
theorem B9748451 : Blo 2027435 9748451 := bstep (se 1 (by rfl) ⟨7311338, by rfl⟩ : syracuseStep 9748451 = 14622677) B14622677
theorem B6498967 : Blo 2027435 6498967 := bstep (se 1 (by rfl) ⟨4874225, by rfl⟩ : syracuseStep 6498967 = 9748451) B9748451
theorem B8665289 : Blo 2027435 8665289 := bstep (se 2 (by rfl) ⟨3249483, by rfl⟩ : syracuseStep 8665289 = 6498967) B6498967
theorem B5776859 : Blo 2027435 5776859 := bstep (se 1 (by rfl) ⟨4332644, by rfl⟩ : syracuseStep 5776859 = 8665289) B8665289
theorem B3851239 : Blo 2027435 3851239 := bstep (se 1 (by rfl) ⟨2888429, by rfl⟩ : syracuseStep 3851239 = 5776859) B5776859
theorem B5134985 : Blo 2027435 5134985 := bstep (se 2 (by rfl) ⟨1925619, by rfl⟩ : syracuseStep 5134985 = 3851239) B3851239
theorem B3423323 : Blo 2027435 3423323 := bstep (se 1 (by rfl) ⟨2567492, by rfl⟩ : syracuseStep 3423323 = 5134985) B5134985
theorem B2282215 : Blo 2027435 2282215 := bstep (se 1 (by rfl) ⟨1711661, by rfl⟩ : syracuseStep 2282215 = 3423323) B3423323
theorem B3042953 : Blo 2027435 3042953 := bstep (se 2 (by rfl) ⟨1141107, by rfl⟩ : syracuseStep 3042953 = 2282215) B2282215
theorem B2028635 : Blo 2027435 2028635 := bstep (se 1 (by rfl) ⟨1521476, by rfl⟩ : syracuseStep 2028635 = 3042953) B3042953
theorem B10269989 : Blo 2027435 10269989 := bbase (se 4 (by rfl) ⟨962811, by rfl⟩ : syracuseStep 10269989 = 1925623) (by norm_num)
theorem B6846659 : Blo 2027435 6846659 := bstep (se 1 (by rfl) ⟨5134994, by rfl⟩ : syracuseStep 6846659 = 10269989) B10269989
theorem B4564439 : Blo 2027435 4564439 := bstep (se 1 (by rfl) ⟨3423329, by rfl⟩ : syracuseStep 4564439 = 6846659) B6846659
theorem B3042959 : Blo 2027435 3042959 := bstep (se 1 (by rfl) ⟨2282219, by rfl⟩ : syracuseStep 3042959 = 4564439) B4564439
theorem B2028639 : Blo 2027435 2028639 := bstep (se 1 (by rfl) ⟨1521479, by rfl⟩ : syracuseStep 2028639 = 3042959) B3042959
theorem B3042965 : Blo 2027435 3042965 := bbase (se 6 (by rfl) ⟨71319, by rfl⟩ : syracuseStep 3042965 = 142639) (by norm_num)
theorem B2028643 : Blo 2027435 2028643 := bstep (se 1 (by rfl) ⟨1521482, by rfl⟩ : syracuseStep 2028643 = 3042965) B3042965
theorem B7034789 : Blo 2027435 7034789 := bbase (se 4 (by rfl) ⟨659511, by rfl⟩ : syracuseStep 7034789 = 1319023) (by norm_num)
theorem B4689859 : Blo 2027435 4689859 := bstep (se 1 (by rfl) ⟨3517394, by rfl⟩ : syracuseStep 4689859 = 7034789) B7034789
theorem B6253145 : Blo 2027435 6253145 := bstep (se 2 (by rfl) ⟨2344929, by rfl⟩ : syracuseStep 6253145 = 4689859) B4689859
theorem B4168763 : Blo 2027435 4168763 := bstep (se 1 (by rfl) ⟨3126572, by rfl⟩ : syracuseStep 4168763 = 6253145) B6253145
theorem B2779175 : Blo 2027435 2779175 := bstep (se 1 (by rfl) ⟨2084381, by rfl⟩ : syracuseStep 2779175 = 4168763) B4168763
theorem B7411133 : Blo 2027435 7411133 := bstep (se 3 (by rfl) ⟨1389587, by rfl⟩ : syracuseStep 7411133 = 2779175) B2779175
theorem B19763021 : Blo 2027435 19763021 := bstep (se 3 (by rfl) ⟨3705566, by rfl⟩ : syracuseStep 19763021 = 7411133) B7411133
theorem B13175347 : Blo 2027435 13175347 := bstep (se 1 (by rfl) ⟨9881510, by rfl⟩ : syracuseStep 13175347 = 19763021) B19763021
theorem B17567129 : Blo 2027435 17567129 := bstep (se 2 (by rfl) ⟨6587673, by rfl⟩ : syracuseStep 17567129 = 13175347) B13175347
theorem B46845677 : Blo 2027435 46845677 := bstep (se 3 (by rfl) ⟨8783564, by rfl⟩ : syracuseStep 46845677 = 17567129) B17567129
theorem B31230451 : Blo 2027435 31230451 := bstep (se 1 (by rfl) ⟨23422838, by rfl⟩ : syracuseStep 31230451 = 46845677) B46845677
theorem B41640601 : Blo 2027435 41640601 := bstep (se 2 (by rfl) ⟨15615225, by rfl⟩ : syracuseStep 41640601 = 31230451) B31230451
theorem B55520801 : Blo 2027435 55520801 := bstep (se 2 (by rfl) ⟨20820300, by rfl⟩ : syracuseStep 55520801 = 41640601) B41640601
theorem B37013867 : Blo 2027435 37013867 := bstep (se 1 (by rfl) ⟨27760400, by rfl⟩ : syracuseStep 37013867 = 55520801) B55520801
theorem B24675911 : Blo 2027435 24675911 := bstep (se 1 (by rfl) ⟨18506933, by rfl⟩ : syracuseStep 24675911 = 37013867) B37013867
theorem B16450607 : Blo 2027435 16450607 := bstep (se 1 (by rfl) ⟨12337955, by rfl⟩ : syracuseStep 16450607 = 24675911) B24675911
theorem B10967071 : Blo 2027435 10967071 := bstep (se 1 (by rfl) ⟨8225303, by rfl⟩ : syracuseStep 10967071 = 16450607) B16450607
theorem B14622761 : Blo 2027435 14622761 := bstep (se 2 (by rfl) ⟨5483535, by rfl⟩ : syracuseStep 14622761 = 10967071) B10967071
theorem B9748507 : Blo 2027435 9748507 := bstep (se 1 (by rfl) ⟨7311380, by rfl⟩ : syracuseStep 9748507 = 14622761) B14622761
theorem B12998009 : Blo 2027435 12998009 := bstep (se 2 (by rfl) ⟨4874253, by rfl⟩ : syracuseStep 12998009 = 9748507) B9748507
theorem B8665339 : Blo 2027435 8665339 := bstep (se 1 (by rfl) ⟨6499004, by rfl⟩ : syracuseStep 8665339 = 12998009) B12998009
theorem B11553785 : Blo 2027435 11553785 := bstep (se 2 (by rfl) ⟨4332669, by rfl⟩ : syracuseStep 11553785 = 8665339) B8665339
theorem B7702523 : Blo 2027435 7702523 := bstep (se 1 (by rfl) ⟨5776892, by rfl⟩ : syracuseStep 7702523 = 11553785) B11553785
theorem B5135015 : Blo 2027435 5135015 := bstep (se 1 (by rfl) ⟨3851261, by rfl⟩ : syracuseStep 5135015 = 7702523) B7702523
theorem B3423343 : Blo 2027435 3423343 := bstep (se 1 (by rfl) ⟨2567507, by rfl⟩ : syracuseStep 3423343 = 5135015) B5135015
theorem B4564457 : Blo 2027435 4564457 := bstep (se 2 (by rfl) ⟨1711671, by rfl⟩ : syracuseStep 4564457 = 3423343) B3423343
theorem B3042971 : Blo 2027435 3042971 := bstep (se 1 (by rfl) ⟨2282228, by rfl⟩ : syracuseStep 3042971 = 4564457) B4564457
theorem B2028647 : Blo 2027435 2028647 := bstep (se 1 (by rfl) ⟨1521485, by rfl⟩ : syracuseStep 2028647 = 3042971) B3042971
theorem B2282233 : Blo 2027435 2282233 := bbase (se 2 (by rfl) ⟨855837, by rfl⟩ : syracuseStep 2282233 = 1711675) (by norm_num)
theorem B3042977 : Blo 2027435 3042977 := bstep (se 2 (by rfl) ⟨1141116, by rfl⟩ : syracuseStep 3042977 = 2282233) B2282233
theorem B2028651 : Blo 2027435 2028651 := bstep (se 1 (by rfl) ⟨1521488, by rfl⟩ : syracuseStep 2028651 = 3042977) B3042977
theorem B4112669 : Blo 2027435 4112669 := bbase (se 3 (by rfl) ⟨771125, by rfl⟩ : syracuseStep 4112669 = 1542251) (by norm_num)
theorem B2741779 : Blo 2027435 2741779 := bstep (se 1 (by rfl) ⟨2056334, by rfl⟩ : syracuseStep 2741779 = 4112669) B4112669
theorem B3655705 : Blo 2027435 3655705 := bstep (se 2 (by rfl) ⟨1370889, by rfl⟩ : syracuseStep 3655705 = 2741779) B2741779
theorem B4874273 : Blo 2027435 4874273 := bstep (se 2 (by rfl) ⟨1827852, by rfl⟩ : syracuseStep 4874273 = 3655705) B3655705
theorem B3249515 : Blo 2027435 3249515 := bstep (se 1 (by rfl) ⟨2437136, by rfl⟩ : syracuseStep 3249515 = 4874273) B4874273
theorem B8665373 : Blo 2027435 8665373 := bstep (se 3 (by rfl) ⟨1624757, by rfl⟩ : syracuseStep 8665373 = 3249515) B3249515
theorem B5776915 : Blo 2027435 5776915 := bstep (se 1 (by rfl) ⟨4332686, by rfl⟩ : syracuseStep 5776915 = 8665373) B8665373
theorem B7702553 : Blo 2027435 7702553 := bstep (se 2 (by rfl) ⟨2888457, by rfl⟩ : syracuseStep 7702553 = 5776915) B5776915
theorem B5135035 : Blo 2027435 5135035 := bstep (se 1 (by rfl) ⟨3851276, by rfl⟩ : syracuseStep 5135035 = 7702553) B7702553
theorem B6846713 : Blo 2027435 6846713 := bstep (se 2 (by rfl) ⟨2567517, by rfl⟩ : syracuseStep 6846713 = 5135035) B5135035
theorem B4564475 : Blo 2027435 4564475 := bstep (se 1 (by rfl) ⟨3423356, by rfl⟩ : syracuseStep 4564475 = 6846713) B6846713
theorem B3042983 : Blo 2027435 3042983 := bstep (se 1 (by rfl) ⟨2282237, by rfl⟩ : syracuseStep 3042983 = 4564475) B4564475
theorem B2028655 : Blo 2027435 2028655 := bstep (se 1 (by rfl) ⟨1521491, by rfl⟩ : syracuseStep 2028655 = 3042983) B3042983
theorem B3042989 : Blo 2027435 3042989 := bbase (se 3 (by rfl) ⟨570560, by rfl⟩ : syracuseStep 3042989 = 1141121) (by norm_num)
theorem B2028659 : Blo 2027435 2028659 := bstep (se 1 (by rfl) ⟨1521494, by rfl⟩ : syracuseStep 2028659 = 3042989) B3042989
theorem B4564493 : Blo 2027435 4564493 := bbase (se 3 (by rfl) ⟨855842, by rfl⟩ : syracuseStep 4564493 = 1711685) (by norm_num)
theorem B3042995 : Blo 2027435 3042995 := bstep (se 1 (by rfl) ⟨2282246, by rfl⟩ : syracuseStep 3042995 = 4564493) B4564493
theorem B2028663 : Blo 2027435 2028663 := bstep (se 1 (by rfl) ⟨1521497, by rfl⟩ : syracuseStep 2028663 = 3042995) B3042995
theorem B2567533 : Blo 2027435 2567533 := bbase (se 3 (by rfl) ⟨481412, by rfl⟩ : syracuseStep 2567533 = 962825) (by norm_num)
theorem B3423377 : Blo 2027435 3423377 := bstep (se 2 (by rfl) ⟨1283766, by rfl⟩ : syracuseStep 3423377 = 2567533) B2567533
theorem B2282251 : Blo 2027435 2282251 := bstep (se 1 (by rfl) ⟨1711688, by rfl⟩ : syracuseStep 2282251 = 3423377) B3423377
theorem B3043001 : Blo 2027435 3043001 := bstep (se 2 (by rfl) ⟨1141125, by rfl⟩ : syracuseStep 3043001 = 2282251) B2282251
theorem B2028667 : Blo 2027435 2028667 := bstep (se 1 (by rfl) ⟨1521500, by rfl⟩ : syracuseStep 2028667 = 3043001) B3043001
theorem B3655733 : Blo 2027435 3655733 := bbase (se 5 (by rfl) ⟨171362, by rfl⟩ : syracuseStep 3655733 = 342725) (by norm_num)
theorem B9748621 : Blo 2027435 9748621 := bstep (se 3 (by rfl) ⟨1827866, by rfl⟩ : syracuseStep 9748621 = 3655733) B3655733
theorem B12998161 : Blo 2027435 12998161 := bstep (se 2 (by rfl) ⟨4874310, by rfl⟩ : syracuseStep 12998161 = 9748621) B9748621
theorem B17330881 : Blo 2027435 17330881 := bstep (se 2 (by rfl) ⟨6499080, by rfl⟩ : syracuseStep 17330881 = 12998161) B12998161
theorem B23107841 : Blo 2027435 23107841 := bstep (se 2 (by rfl) ⟨8665440, by rfl⟩ : syracuseStep 23107841 = 17330881) B17330881
theorem B15405227 : Blo 2027435 15405227 := bstep (se 1 (by rfl) ⟨11553920, by rfl⟩ : syracuseStep 15405227 = 23107841) B23107841
theorem B10270151 : Blo 2027435 10270151 := bstep (se 1 (by rfl) ⟨7702613, by rfl⟩ : syracuseStep 10270151 = 15405227) B15405227
theorem B6846767 : Blo 2027435 6846767 := bstep (se 1 (by rfl) ⟨5135075, by rfl⟩ : syracuseStep 6846767 = 10270151) B10270151
theorem B4564511 : Blo 2027435 4564511 := bstep (se 1 (by rfl) ⟨3423383, by rfl⟩ : syracuseStep 4564511 = 6846767) B6846767
theorem B3043007 : Blo 2027435 3043007 := bstep (se 1 (by rfl) ⟨2282255, by rfl⟩ : syracuseStep 3043007 = 4564511) B4564511
theorem B2028671 : Blo 2027435 2028671 := bstep (se 1 (by rfl) ⟨1521503, by rfl⟩ : syracuseStep 2028671 = 3043007) B3043007
theorem B3043013 : Blo 2027435 3043013 := bbase (se 4 (by rfl) ⟨285282, by rfl⟩ : syracuseStep 3043013 = 570565) (by norm_num)
theorem B2028675 : Blo 2027435 2028675 := bstep (se 1 (by rfl) ⟨1521506, by rfl⟩ : syracuseStep 2028675 = 3043013) B3043013
theorem B3423397 : Blo 2027435 3423397 := bbase (se 4 (by rfl) ⟨320943, by rfl⟩ : syracuseStep 3423397 = 641887) (by norm_num)
theorem B4564529 : Blo 2027435 4564529 := bstep (se 2 (by rfl) ⟨1711698, by rfl⟩ : syracuseStep 4564529 = 3423397) B3423397
theorem B3043019 : Blo 2027435 3043019 := bstep (se 1 (by rfl) ⟨2282264, by rfl⟩ : syracuseStep 3043019 = 4564529) B4564529
theorem B2028679 : Blo 2027435 2028679 := bstep (se 1 (by rfl) ⟨1521509, by rfl⟩ : syracuseStep 2028679 = 3043019) B3043019
theorem B2282269 : Blo 2027435 2282269 := bbase (se 3 (by rfl) ⟨427925, by rfl⟩ : syracuseStep 2282269 = 855851) (by norm_num)
theorem B3043025 : Blo 2027435 3043025 := bstep (se 2 (by rfl) ⟨1141134, by rfl⟩ : syracuseStep 3043025 = 2282269) B2282269
theorem B2028683 : Blo 2027435 2028683 := bstep (se 1 (by rfl) ⟨1521512, by rfl⟩ : syracuseStep 2028683 = 3043025) B3043025
theorem B6846821 : Blo 2027435 6846821 := bbase (se 4 (by rfl) ⟨641889, by rfl⟩ : syracuseStep 6846821 = 1283779) (by norm_num)
theorem B4564547 : Blo 2027435 4564547 := bstep (se 1 (by rfl) ⟨3423410, by rfl⟩ : syracuseStep 4564547 = 6846821) B6846821
theorem B3043031 : Blo 2027435 3043031 := bstep (se 1 (by rfl) ⟨2282273, by rfl⟩ : syracuseStep 3043031 = 4564547) B4564547
theorem B2028687 : Blo 2027435 2028687 := bstep (se 1 (by rfl) ⟨1521515, by rfl⟩ : syracuseStep 2028687 = 3043031) B3043031
theorem B3043037 : Blo 2027435 3043037 := bbase (se 3 (by rfl) ⟨570569, by rfl⟩ : syracuseStep 3043037 = 1141139) (by norm_num)
theorem B2028691 : Blo 2027435 2028691 := bstep (se 1 (by rfl) ⟨1521518, by rfl⟩ : syracuseStep 2028691 = 3043037) B3043037
theorem B4564565 : Blo 2027435 4564565 := bbase (se 8 (by rfl) ⟨26745, by rfl⟩ : syracuseStep 4564565 = 53491) (by norm_num)
theorem B3043043 : Blo 2027435 3043043 := bstep (se 1 (by rfl) ⟨2282282, by rfl⟩ : syracuseStep 3043043 = 4564565) B4564565
theorem B2028695 : Blo 2027435 2028695 := bstep (se 1 (by rfl) ⟨1521521, by rfl⟩ : syracuseStep 2028695 = 3043043) B3043043
theorem B4332781 : Blo 2027435 4332781 := bbase (se 3 (by rfl) ⟨812396, by rfl⟩ : syracuseStep 4332781 = 1624793) (by norm_num)
theorem B5777041 : Blo 2027435 5777041 := bstep (se 2 (by rfl) ⟨2166390, by rfl⟩ : syracuseStep 5777041 = 4332781) B4332781
theorem B7702721 : Blo 2027435 7702721 := bstep (se 2 (by rfl) ⟨2888520, by rfl⟩ : syracuseStep 7702721 = 5777041) B5777041
theorem B5135147 : Blo 2027435 5135147 := bstep (se 1 (by rfl) ⟨3851360, by rfl⟩ : syracuseStep 5135147 = 7702721) B7702721
theorem B3423431 : Blo 2027435 3423431 := bstep (se 1 (by rfl) ⟨2567573, by rfl⟩ : syracuseStep 3423431 = 5135147) B5135147
theorem B2282287 : Blo 2027435 2282287 := bstep (se 1 (by rfl) ⟨1711715, by rfl⟩ : syracuseStep 2282287 = 3423431) B3423431
theorem B3043049 : Blo 2027435 3043049 := bstep (se 2 (by rfl) ⟨1141143, by rfl⟩ : syracuseStep 3043049 = 2282287) B2282287
theorem B2028699 : Blo 2027435 2028699 := bstep (se 1 (by rfl) ⟨1521524, by rfl⟩ : syracuseStep 2028699 = 3043049) B3043049
theorem B10410437 : Blo 2027435 10410437 := bbase (se 4 (by rfl) ⟨975978, by rfl⟩ : syracuseStep 10410437 = 1951957) (by norm_num)
theorem B6940291 : Blo 2027435 6940291 := bstep (se 1 (by rfl) ⟨5205218, by rfl⟩ : syracuseStep 6940291 = 10410437) B10410437
theorem B9253721 : Blo 2027435 9253721 := bstep (se 2 (by rfl) ⟨3470145, by rfl⟩ : syracuseStep 9253721 = 6940291) B6940291
theorem B24676589 : Blo 2027435 24676589 := bstep (se 3 (by rfl) ⟨4626860, by rfl⟩ : syracuseStep 24676589 = 9253721) B9253721
theorem B16451059 : Blo 2027435 16451059 := bstep (se 1 (by rfl) ⟨12338294, by rfl⟩ : syracuseStep 16451059 = 24676589) B24676589
theorem B21934745 : Blo 2027435 21934745 := bstep (se 2 (by rfl) ⟨8225529, by rfl⟩ : syracuseStep 21934745 = 16451059) B16451059
theorem B14623163 : Blo 2027435 14623163 := bstep (se 1 (by rfl) ⟨10967372, by rfl⟩ : syracuseStep 14623163 = 21934745) B21934745
theorem B9748775 : Blo 2027435 9748775 := bstep (se 1 (by rfl) ⟨7311581, by rfl⟩ : syracuseStep 9748775 = 14623163) B14623163
theorem B25996733 : Blo 2027435 25996733 := bstep (se 3 (by rfl) ⟨4874387, by rfl⟩ : syracuseStep 25996733 = 9748775) B9748775
theorem B17331155 : Blo 2027435 17331155 := bstep (se 1 (by rfl) ⟨12998366, by rfl⟩ : syracuseStep 17331155 = 25996733) B25996733
theorem B11554103 : Blo 2027435 11554103 := bstep (se 1 (by rfl) ⟨8665577, by rfl⟩ : syracuseStep 11554103 = 17331155) B17331155
theorem B7702735 : Blo 2027435 7702735 := bstep (se 1 (by rfl) ⟨5777051, by rfl⟩ : syracuseStep 7702735 = 11554103) B11554103
theorem B10270313 : Blo 2027435 10270313 := bstep (se 2 (by rfl) ⟨3851367, by rfl⟩ : syracuseStep 10270313 = 7702735) B7702735
theorem B6846875 : Blo 2027435 6846875 := bstep (se 1 (by rfl) ⟨5135156, by rfl⟩ : syracuseStep 6846875 = 10270313) B10270313
theorem B4564583 : Blo 2027435 4564583 := bstep (se 1 (by rfl) ⟨3423437, by rfl⟩ : syracuseStep 4564583 = 6846875) B6846875
theorem B3043055 : Blo 2027435 3043055 := bstep (se 1 (by rfl) ⟨2282291, by rfl⟩ : syracuseStep 3043055 = 4564583) B4564583
theorem B2028703 : Blo 2027435 2028703 := bstep (se 1 (by rfl) ⟨1521527, by rfl⟩ : syracuseStep 2028703 = 3043055) B3043055
theorem B3043061 : Blo 2027435 3043061 := bbase (se 5 (by rfl) ⟨142643, by rfl⟩ : syracuseStep 3043061 = 285287) (by norm_num)
theorem B2028707 : Blo 2027435 2028707 := bstep (se 1 (by rfl) ⟨1521530, by rfl⟩ : syracuseStep 2028707 = 3043061) B3043061
theorem B3249605 : Blo 2027435 3249605 := bbase (se 4 (by rfl) ⟨304650, by rfl⟩ : syracuseStep 3249605 = 609301) (by norm_num)
theorem B8665613 : Blo 2027435 8665613 := bstep (se 3 (by rfl) ⟨1624802, by rfl⟩ : syracuseStep 8665613 = 3249605) B3249605
theorem B5777075 : Blo 2027435 5777075 := bstep (se 1 (by rfl) ⟨4332806, by rfl⟩ : syracuseStep 5777075 = 8665613) B8665613
theorem B3851383 : Blo 2027435 3851383 := bstep (se 1 (by rfl) ⟨2888537, by rfl⟩ : syracuseStep 3851383 = 5777075) B5777075
theorem B5135177 : Blo 2027435 5135177 := bstep (se 2 (by rfl) ⟨1925691, by rfl⟩ : syracuseStep 5135177 = 3851383) B3851383
theorem B3423451 : Blo 2027435 3423451 := bstep (se 1 (by rfl) ⟨2567588, by rfl⟩ : syracuseStep 3423451 = 5135177) B5135177
theorem B4564601 : Blo 2027435 4564601 := bstep (se 2 (by rfl) ⟨1711725, by rfl⟩ : syracuseStep 4564601 = 3423451) B3423451
theorem B3043067 : Blo 2027435 3043067 := bstep (se 1 (by rfl) ⟨2282300, by rfl⟩ : syracuseStep 3043067 = 4564601) B4564601
theorem B2028711 : Blo 2027435 2028711 := bstep (se 1 (by rfl) ⟨1521533, by rfl⟩ : syracuseStep 2028711 = 3043067) B3043067
theorem B2282305 : Blo 2027435 2282305 := bbase (se 2 (by rfl) ⟨855864, by rfl⟩ : syracuseStep 2282305 = 1711729) (by norm_num)
theorem B3043073 : Blo 2027435 3043073 := bstep (se 2 (by rfl) ⟨1141152, by rfl⟩ : syracuseStep 3043073 = 2282305) B2282305
theorem B2028715 : Blo 2027435 2028715 := bstep (se 1 (by rfl) ⟨1521536, by rfl⟩ : syracuseStep 2028715 = 3043073) B3043073
theorem B5135197 : Blo 2027435 5135197 := bbase (se 3 (by rfl) ⟨962849, by rfl⟩ : syracuseStep 5135197 = 1925699) (by norm_num)
theorem B6846929 : Blo 2027435 6846929 := bstep (se 2 (by rfl) ⟨2567598, by rfl⟩ : syracuseStep 6846929 = 5135197) B5135197
theorem B4564619 : Blo 2027435 4564619 := bstep (se 1 (by rfl) ⟨3423464, by rfl⟩ : syracuseStep 4564619 = 6846929) B6846929
theorem B3043079 : Blo 2027435 3043079 := bstep (se 1 (by rfl) ⟨2282309, by rfl⟩ : syracuseStep 3043079 = 4564619) B4564619
theorem B2028719 : Blo 2027435 2028719 := bstep (se 1 (by rfl) ⟨1521539, by rfl⟩ : syracuseStep 2028719 = 3043079) B3043079
theorem B3043085 : Blo 2027435 3043085 := bbase (se 3 (by rfl) ⟨570578, by rfl⟩ : syracuseStep 3043085 = 1141157) (by norm_num)
theorem B2028723 : Blo 2027435 2028723 := bstep (se 1 (by rfl) ⟨1521542, by rfl⟩ : syracuseStep 2028723 = 3043085) B3043085
theorem B4564637 : Blo 2027435 4564637 := bbase (se 3 (by rfl) ⟨855869, by rfl⟩ : syracuseStep 4564637 = 1711739) (by norm_num)
theorem B3043091 : Blo 2027435 3043091 := bstep (se 1 (by rfl) ⟨2282318, by rfl⟩ : syracuseStep 3043091 = 4564637) B4564637
theorem B2028727 : Blo 2027435 2028727 := bstep (se 1 (by rfl) ⟨1521545, by rfl⟩ : syracuseStep 2028727 = 3043091) B3043091
theorem B3423485 : Blo 2027435 3423485 := bbase (se 3 (by rfl) ⟨641903, by rfl⟩ : syracuseStep 3423485 = 1283807) (by norm_num)
theorem B2282323 : Blo 2027435 2282323 := bstep (se 1 (by rfl) ⟨1711742, by rfl⟩ : syracuseStep 2282323 = 3423485) B3423485
theorem B3043097 : Blo 2027435 3043097 := bstep (se 2 (by rfl) ⟨1141161, by rfl⟩ : syracuseStep 3043097 = 2282323) B2282323
theorem B2028731 : Blo 2027435 2028731 := bstep (se 1 (by rfl) ⟨1521548, by rfl⟩ : syracuseStep 2028731 = 3043097) B3043097
theorem B3126709 : Blo 2027435 3126709 := bbase (se 5 (by rfl) ⟨146564, by rfl⟩ : syracuseStep 3126709 = 293129) (by norm_num)
theorem B4168945 : Blo 2027435 4168945 := bstep (se 2 (by rfl) ⟨1563354, by rfl⟩ : syracuseStep 4168945 = 3126709) B3126709
theorem B5558593 : Blo 2027435 5558593 := bstep (se 2 (by rfl) ⟨2084472, by rfl⟩ : syracuseStep 5558593 = 4168945) B4168945
theorem B7411457 : Blo 2027435 7411457 := bstep (se 2 (by rfl) ⟨2779296, by rfl⟩ : syracuseStep 7411457 = 5558593) B5558593
theorem B19763885 : Blo 2027435 19763885 := bstep (se 3 (by rfl) ⟨3705728, by rfl⟩ : syracuseStep 19763885 = 7411457) B7411457
theorem B52703693 : Blo 2027435 52703693 := bstep (se 3 (by rfl) ⟨9881942, by rfl⟩ : syracuseStep 52703693 = 19763885) B19763885
theorem B35135795 : Blo 2027435 35135795 := bstep (se 1 (by rfl) ⟨26351846, by rfl⟩ : syracuseStep 35135795 = 52703693) B52703693
theorem B23423863 : Blo 2027435 23423863 := bstep (se 1 (by rfl) ⟨17567897, by rfl⟩ : syracuseStep 23423863 = 35135795) B35135795
theorem B31231817 : Blo 2027435 31231817 := bstep (se 2 (by rfl) ⟨11711931, by rfl⟩ : syracuseStep 31231817 = 23423863) B23423863
theorem B20821211 : Blo 2027435 20821211 := bstep (se 1 (by rfl) ⟨15615908, by rfl⟩ : syracuseStep 20821211 = 31231817) B31231817
theorem B13880807 : Blo 2027435 13880807 := bstep (se 1 (by rfl) ⟨10410605, by rfl⟩ : syracuseStep 13880807 = 20821211) B20821211
theorem B9253871 : Blo 2027435 9253871 := bstep (se 1 (by rfl) ⟨6940403, by rfl⟩ : syracuseStep 9253871 = 13880807) B13880807
theorem B6169247 : Blo 2027435 6169247 := bstep (se 1 (by rfl) ⟨4626935, by rfl⟩ : syracuseStep 6169247 = 9253871) B9253871
theorem B4112831 : Blo 2027435 4112831 := bstep (se 1 (by rfl) ⟨3084623, by rfl⟩ : syracuseStep 4112831 = 6169247) B6169247
theorem B2741887 : Blo 2027435 2741887 := bstep (se 1 (by rfl) ⟨2056415, by rfl⟩ : syracuseStep 2741887 = 4112831) B4112831
theorem B3655849 : Blo 2027435 3655849 := bstep (se 2 (by rfl) ⟨1370943, by rfl⟩ : syracuseStep 3655849 = 2741887) B2741887
theorem B4874465 : Blo 2027435 4874465 := bstep (se 2 (by rfl) ⟨1827924, by rfl⟩ : syracuseStep 4874465 = 3655849) B3655849
theorem B3249643 : Blo 2027435 3249643 := bstep (se 1 (by rfl) ⟨2437232, by rfl⟩ : syracuseStep 3249643 = 4874465) B4874465
theorem B4332857 : Blo 2027435 4332857 := bstep (se 2 (by rfl) ⟨1624821, by rfl⟩ : syracuseStep 4332857 = 3249643) B3249643
theorem B11554285 : Blo 2027435 11554285 := bstep (se 3 (by rfl) ⟨2166428, by rfl⟩ : syracuseStep 11554285 = 4332857) B4332857
theorem B15405713 : Blo 2027435 15405713 := bstep (se 2 (by rfl) ⟨5777142, by rfl⟩ : syracuseStep 15405713 = 11554285) B11554285
theorem B10270475 : Blo 2027435 10270475 := bstep (se 1 (by rfl) ⟨7702856, by rfl⟩ : syracuseStep 10270475 = 15405713) B15405713
theorem B6846983 : Blo 2027435 6846983 := bstep (se 1 (by rfl) ⟨5135237, by rfl⟩ : syracuseStep 6846983 = 10270475) B10270475
theorem B4564655 : Blo 2027435 4564655 := bstep (se 1 (by rfl) ⟨3423491, by rfl⟩ : syracuseStep 4564655 = 6846983) B6846983
theorem B3043103 : Blo 2027435 3043103 := bstep (se 1 (by rfl) ⟨2282327, by rfl⟩ : syracuseStep 3043103 = 4564655) B4564655
theorem B2028735 : Blo 2027435 2028735 := bstep (se 1 (by rfl) ⟨1521551, by rfl⟩ : syracuseStep 2028735 = 3043103) B3043103
theorem B3043109 : Blo 2027435 3043109 := bbase (se 4 (by rfl) ⟨285291, by rfl⟩ : syracuseStep 3043109 = 570583) (by norm_num)
theorem B2028739 : Blo 2027435 2028739 := bstep (se 1 (by rfl) ⟨1521554, by rfl⟩ : syracuseStep 2028739 = 3043109) B3043109
theorem B2567629 : Blo 2027435 2567629 := bbase (se 3 (by rfl) ⟨481430, by rfl⟩ : syracuseStep 2567629 = 962861) (by norm_num)
theorem B3423505 : Blo 2027435 3423505 := bstep (se 2 (by rfl) ⟨1283814, by rfl⟩ : syracuseStep 3423505 = 2567629) B2567629
theorem B4564673 : Blo 2027435 4564673 := bstep (se 2 (by rfl) ⟨1711752, by rfl⟩ : syracuseStep 4564673 = 3423505) B3423505
theorem B3043115 : Blo 2027435 3043115 := bstep (se 1 (by rfl) ⟨2282336, by rfl⟩ : syracuseStep 3043115 = 4564673) B4564673
theorem B2028743 : Blo 2027435 2028743 := bstep (se 1 (by rfl) ⟨1521557, by rfl⟩ : syracuseStep 2028743 = 3043115) B3043115
theorem B2282341 : Blo 2027435 2282341 := bbase (se 4 (by rfl) ⟨213969, by rfl⟩ : syracuseStep 2282341 = 427939) (by norm_num)
theorem B3043121 : Blo 2027435 3043121 := bstep (se 2 (by rfl) ⟨1141170, by rfl⟩ : syracuseStep 3043121 = 2282341) B2282341
theorem B2028747 : Blo 2027435 2028747 := bstep (se 1 (by rfl) ⟨1521560, by rfl⟩ : syracuseStep 2028747 = 3043121) B3043121
theorem B5777189 : Blo 2027435 5777189 := bbase (se 4 (by rfl) ⟨541611, by rfl⟩ : syracuseStep 5777189 = 1083223) (by norm_num)
theorem B3851459 : Blo 2027435 3851459 := bstep (se 1 (by rfl) ⟨2888594, by rfl⟩ : syracuseStep 3851459 = 5777189) B5777189
theorem B2567639 : Blo 2027435 2567639 := bstep (se 1 (by rfl) ⟨1925729, by rfl⟩ : syracuseStep 2567639 = 3851459) B3851459
theorem B6847037 : Blo 2027435 6847037 := bstep (se 3 (by rfl) ⟨1283819, by rfl⟩ : syracuseStep 6847037 = 2567639) B2567639
theorem B4564691 : Blo 2027435 4564691 := bstep (se 1 (by rfl) ⟨3423518, by rfl⟩ : syracuseStep 4564691 = 6847037) B6847037
theorem B3043127 : Blo 2027435 3043127 := bstep (se 1 (by rfl) ⟨2282345, by rfl⟩ : syracuseStep 3043127 = 4564691) B4564691
theorem B2028751 : Blo 2027435 2028751 := bstep (se 1 (by rfl) ⟨1521563, by rfl⟩ : syracuseStep 2028751 = 3043127) B3043127
theorem B3043133 : Blo 2027435 3043133 := bbase (se 3 (by rfl) ⟨570587, by rfl⟩ : syracuseStep 3043133 = 1141175) (by norm_num)
theorem B2028755 : Blo 2027435 2028755 := bstep (se 1 (by rfl) ⟨1521566, by rfl⟩ : syracuseStep 2028755 = 3043133) B3043133
theorem B4564709 : Blo 2027435 4564709 := bbase (se 4 (by rfl) ⟨427941, by rfl⟩ : syracuseStep 4564709 = 855883) (by norm_num)
theorem B3043139 : Blo 2027435 3043139 := bstep (se 1 (by rfl) ⟨2282354, by rfl⟩ : syracuseStep 3043139 = 4564709) B4564709
theorem B2028759 : Blo 2027435 2028759 := bstep (se 1 (by rfl) ⟨1521569, by rfl⟩ : syracuseStep 2028759 = 3043139) B3043139
theorem B5135309 : Blo 2027435 5135309 := bbase (se 3 (by rfl) ⟨962870, by rfl⟩ : syracuseStep 5135309 = 1925741) (by norm_num)
theorem B3423539 : Blo 2027435 3423539 := bstep (se 1 (by rfl) ⟨2567654, by rfl⟩ : syracuseStep 3423539 = 5135309) B5135309
theorem B2282359 : Blo 2027435 2282359 := bstep (se 1 (by rfl) ⟨1711769, by rfl⟩ : syracuseStep 2282359 = 3423539) B3423539
theorem B3043145 : Blo 2027435 3043145 := bstep (se 2 (by rfl) ⟨1141179, by rfl⟩ : syracuseStep 3043145 = 2282359) B2282359
theorem B2028763 : Blo 2027435 2028763 := bstep (se 1 (by rfl) ⟨1521572, by rfl⟩ : syracuseStep 2028763 = 3043145) B3043145
theorem B9882101 : Blo 2027435 9882101 := bbase (se 5 (by rfl) ⟨463223, by rfl⟩ : syracuseStep 9882101 = 926447) (by norm_num)
theorem B6588067 : Blo 2027435 6588067 := bstep (se 1 (by rfl) ⟨4941050, by rfl⟩ : syracuseStep 6588067 = 9882101) B9882101
theorem B8784089 : Blo 2027435 8784089 := bstep (se 2 (by rfl) ⟨3294033, by rfl⟩ : syracuseStep 8784089 = 6588067) B6588067
theorem B5856059 : Blo 2027435 5856059 := bstep (se 1 (by rfl) ⟨4392044, by rfl⟩ : syracuseStep 5856059 = 8784089) B8784089
theorem B3904039 : Blo 2027435 3904039 := bstep (se 1 (by rfl) ⟨2928029, by rfl⟩ : syracuseStep 3904039 = 5856059) B5856059
theorem B5205385 : Blo 2027435 5205385 := bstep (se 2 (by rfl) ⟨1952019, by rfl⟩ : syracuseStep 5205385 = 3904039) B3904039
theorem B6940513 : Blo 2027435 6940513 := bstep (se 2 (by rfl) ⟨2602692, by rfl⟩ : syracuseStep 6940513 = 5205385) B5205385
theorem B9254017 : Blo 2027435 9254017 := bstep (se 2 (by rfl) ⟨3470256, by rfl⟩ : syracuseStep 9254017 = 6940513) B6940513
theorem B12338689 : Blo 2027435 12338689 := bstep (se 2 (by rfl) ⟨4627008, by rfl⟩ : syracuseStep 12338689 = 9254017) B9254017
theorem B16451585 : Blo 2027435 16451585 := bstep (se 2 (by rfl) ⟨6169344, by rfl⟩ : syracuseStep 16451585 = 12338689) B12338689
theorem B10967723 : Blo 2027435 10967723 := bstep (se 1 (by rfl) ⟨8225792, by rfl⟩ : syracuseStep 10967723 = 16451585) B16451585
theorem B7311815 : Blo 2027435 7311815 := bstep (se 1 (by rfl) ⟨5483861, by rfl⟩ : syracuseStep 7311815 = 10967723) B10967723
theorem B4874543 : Blo 2027435 4874543 := bstep (se 1 (by rfl) ⟨3655907, by rfl⟩ : syracuseStep 4874543 = 7311815) B7311815
theorem B3249695 : Blo 2027435 3249695 := bstep (se 1 (by rfl) ⟨2437271, by rfl⟩ : syracuseStep 3249695 = 4874543) B4874543
theorem B2166463 : Blo 2027435 2166463 := bstep (se 1 (by rfl) ⟨1624847, by rfl⟩ : syracuseStep 2166463 = 3249695) B3249695
theorem B2888617 : Blo 2027435 2888617 := bstep (se 2 (by rfl) ⟨1083231, by rfl⟩ : syracuseStep 2888617 = 2166463) B2166463
theorem B3851489 : Blo 2027435 3851489 := bstep (se 2 (by rfl) ⟨1444308, by rfl⟩ : syracuseStep 3851489 = 2888617) B2888617
theorem B10270637 : Blo 2027435 10270637 := bstep (se 3 (by rfl) ⟨1925744, by rfl⟩ : syracuseStep 10270637 = 3851489) B3851489
theorem B6847091 : Blo 2027435 6847091 := bstep (se 1 (by rfl) ⟨5135318, by rfl⟩ : syracuseStep 6847091 = 10270637) B10270637
theorem B4564727 : Blo 2027435 4564727 := bstep (se 1 (by rfl) ⟨3423545, by rfl⟩ : syracuseStep 4564727 = 6847091) B6847091
theorem B3043151 : Blo 2027435 3043151 := bstep (se 1 (by rfl) ⟨2282363, by rfl⟩ : syracuseStep 3043151 = 4564727) B4564727
theorem B2028767 : Blo 2027435 2028767 := bstep (se 1 (by rfl) ⟨1521575, by rfl⟩ : syracuseStep 2028767 = 3043151) B3043151
theorem B3043157 : Blo 2027435 3043157 := bbase (se 9 (by rfl) ⟨8915, by rfl⟩ : syracuseStep 3043157 = 17831) (by norm_num)
theorem B2028771 : Blo 2027435 2028771 := bstep (se 1 (by rfl) ⟨1521578, by rfl⟩ : syracuseStep 2028771 = 3043157) B3043157
theorem B2741941 : Blo 2027435 2741941 := bbase (se 5 (by rfl) ⟨128528, by rfl⟩ : syracuseStep 2741941 = 257057) (by norm_num)
theorem B14623685 : Blo 2027435 14623685 := bstep (se 4 (by rfl) ⟨1370970, by rfl⟩ : syracuseStep 14623685 = 2741941) B2741941
theorem B9749123 : Blo 2027435 9749123 := bstep (se 1 (by rfl) ⟨7311842, by rfl⟩ : syracuseStep 9749123 = 14623685) B14623685
theorem B6499415 : Blo 2027435 6499415 := bstep (se 1 (by rfl) ⟨4874561, by rfl⟩ : syracuseStep 6499415 = 9749123) B9749123
theorem B4332943 : Blo 2027435 4332943 := bstep (se 1 (by rfl) ⟨3249707, by rfl⟩ : syracuseStep 4332943 = 6499415) B6499415
theorem B5777257 : Blo 2027435 5777257 := bstep (se 2 (by rfl) ⟨2166471, by rfl⟩ : syracuseStep 5777257 = 4332943) B4332943
theorem B7703009 : Blo 2027435 7703009 := bstep (se 2 (by rfl) ⟨2888628, by rfl⟩ : syracuseStep 7703009 = 5777257) B5777257
theorem B5135339 : Blo 2027435 5135339 := bstep (se 1 (by rfl) ⟨3851504, by rfl⟩ : syracuseStep 5135339 = 7703009) B7703009
theorem B3423559 : Blo 2027435 3423559 := bstep (se 1 (by rfl) ⟨2567669, by rfl⟩ : syracuseStep 3423559 = 5135339) B5135339
theorem B4564745 : Blo 2027435 4564745 := bstep (se 2 (by rfl) ⟨1711779, by rfl⟩ : syracuseStep 4564745 = 3423559) B3423559
theorem B3043163 : Blo 2027435 3043163 := bstep (se 1 (by rfl) ⟨2282372, by rfl⟩ : syracuseStep 3043163 = 4564745) B4564745
theorem B2028775 : Blo 2027435 2028775 := bstep (se 1 (by rfl) ⟨1521581, by rfl⟩ : syracuseStep 2028775 = 3043163) B3043163
theorem B2282377 : Blo 2027435 2282377 := bbase (se 2 (by rfl) ⟨855891, by rfl⟩ : syracuseStep 2282377 = 1711783) (by norm_num)
theorem B3043169 : Blo 2027435 3043169 := bstep (se 2 (by rfl) ⟨1141188, by rfl⟩ : syracuseStep 3043169 = 2282377) B2282377
theorem B2028779 : Blo 2027435 2028779 := bstep (se 1 (by rfl) ⟨1521584, by rfl⟩ : syracuseStep 2028779 = 3043169) B3043169
theorem B5856101 : Blo 2027435 5856101 := bbase (se 4 (by rfl) ⟨549009, by rfl⟩ : syracuseStep 5856101 = 1098019) (by norm_num)
theorem B62465077 : Blo 2027435 62465077 := bstep (se 5 (by rfl) ⟨2928050, by rfl⟩ : syracuseStep 62465077 = 5856101) B5856101
theorem B333147077 : Blo 2027435 333147077 := bstep (se 4 (by rfl) ⟨31232538, by rfl⟩ : syracuseStep 333147077 = 62465077) B62465077
theorem B222098051 : Blo 2027435 222098051 := bstep (se 1 (by rfl) ⟨166573538, by rfl⟩ : syracuseStep 222098051 = 333147077) B333147077
theorem B148065367 : Blo 2027435 148065367 := bstep (se 1 (by rfl) ⟨111049025, by rfl⟩ : syracuseStep 148065367 = 222098051) B222098051
theorem B197420489 : Blo 2027435 197420489 := bstep (se 2 (by rfl) ⟨74032683, by rfl⟩ : syracuseStep 197420489 = 148065367) B148065367
theorem B131613659 : Blo 2027435 131613659 := bstep (se 1 (by rfl) ⟨98710244, by rfl⟩ : syracuseStep 131613659 = 197420489) B197420489
theorem B87742439 : Blo 2027435 87742439 := bstep (se 1 (by rfl) ⟨65806829, by rfl⟩ : syracuseStep 87742439 = 131613659) B131613659
theorem B58494959 : Blo 2027435 58494959 := bstep (se 1 (by rfl) ⟨43871219, by rfl⟩ : syracuseStep 58494959 = 87742439) B87742439
theorem B38996639 : Blo 2027435 38996639 := bstep (se 1 (by rfl) ⟨29247479, by rfl⟩ : syracuseStep 38996639 = 58494959) B58494959
theorem B25997759 : Blo 2027435 25997759 := bstep (se 1 (by rfl) ⟨19498319, by rfl⟩ : syracuseStep 25997759 = 38996639) B38996639
theorem B17331839 : Blo 2027435 17331839 := bstep (se 1 (by rfl) ⟨12998879, by rfl⟩ : syracuseStep 17331839 = 25997759) B25997759
theorem B11554559 : Blo 2027435 11554559 := bstep (se 1 (by rfl) ⟨8665919, by rfl⟩ : syracuseStep 11554559 = 17331839) B17331839
theorem B7703039 : Blo 2027435 7703039 := bstep (se 1 (by rfl) ⟨5777279, by rfl⟩ : syracuseStep 7703039 = 11554559) B11554559
theorem B5135359 : Blo 2027435 5135359 := bstep (se 1 (by rfl) ⟨3851519, by rfl⟩ : syracuseStep 5135359 = 7703039) B7703039
theorem B6847145 : Blo 2027435 6847145 := bstep (se 2 (by rfl) ⟨2567679, by rfl⟩ : syracuseStep 6847145 = 5135359) B5135359
theorem B4564763 : Blo 2027435 4564763 := bstep (se 1 (by rfl) ⟨3423572, by rfl⟩ : syracuseStep 4564763 = 6847145) B6847145
theorem B3043175 : Blo 2027435 3043175 := bstep (se 1 (by rfl) ⟨2282381, by rfl⟩ : syracuseStep 3043175 = 4564763) B4564763
theorem B2028783 : Blo 2027435 2028783 := bstep (se 1 (by rfl) ⟨1521587, by rfl⟩ : syracuseStep 2028783 = 3043175) B3043175
theorem B3043181 : Blo 2027435 3043181 := bbase (se 3 (by rfl) ⟨570596, by rfl⟩ : syracuseStep 3043181 = 1141193) (by norm_num)
theorem B2028787 : Blo 2027435 2028787 := bstep (se 1 (by rfl) ⟨1521590, by rfl⟩ : syracuseStep 2028787 = 3043181) B3043181
theorem B4564781 : Blo 2027435 4564781 := bbase (se 3 (by rfl) ⟨855896, by rfl⟩ : syracuseStep 4564781 = 1711793) (by norm_num)
theorem B3043187 : Blo 2027435 3043187 := bstep (se 1 (by rfl) ⟨2282390, by rfl⟩ : syracuseStep 3043187 = 4564781) B4564781
theorem B2028791 : Blo 2027435 2028791 := bstep (se 1 (by rfl) ⟨1521593, by rfl⟩ : syracuseStep 2028791 = 3043187) B3043187
theorem B8665973 : Blo 2027435 8665973 := bbase (se 5 (by rfl) ⟨406217, by rfl⟩ : syracuseStep 8665973 = 812435) (by norm_num)
theorem B5777315 : Blo 2027435 5777315 := bstep (se 1 (by rfl) ⟨4332986, by rfl⟩ : syracuseStep 5777315 = 8665973) B8665973
theorem B3851543 : Blo 2027435 3851543 := bstep (se 1 (by rfl) ⟨2888657, by rfl⟩ : syracuseStep 3851543 = 5777315) B5777315
theorem B2567695 : Blo 2027435 2567695 := bstep (se 1 (by rfl) ⟨1925771, by rfl⟩ : syracuseStep 2567695 = 3851543) B3851543
theorem B3423593 : Blo 2027435 3423593 := bstep (se 2 (by rfl) ⟨1283847, by rfl⟩ : syracuseStep 3423593 = 2567695) B2567695
theorem B2282395 : Blo 2027435 2282395 := bstep (se 1 (by rfl) ⟨1711796, by rfl⟩ : syracuseStep 2282395 = 3423593) B3423593
theorem B3043193 : Blo 2027435 3043193 := bstep (se 2 (by rfl) ⟨1141197, by rfl⟩ : syracuseStep 3043193 = 2282395) B2282395
theorem B2028795 : Blo 2027435 2028795 := bstep (se 1 (by rfl) ⟨1521596, by rfl⟩ : syracuseStep 2028795 = 3043193) B3043193
theorem B2437309 : Blo 2027435 2437309 := bbase (se 3 (by rfl) ⟨456995, by rfl⟩ : syracuseStep 2437309 = 913991) (by norm_num)
theorem B12998981 : Blo 2027435 12998981 := bstep (se 4 (by rfl) ⟨1218654, by rfl⟩ : syracuseStep 12998981 = 2437309) B2437309
theorem B34663949 : Blo 2027435 34663949 := bstep (se 3 (by rfl) ⟨6499490, by rfl⟩ : syracuseStep 34663949 = 12998981) B12998981
theorem B23109299 : Blo 2027435 23109299 := bstep (se 1 (by rfl) ⟨17331974, by rfl⟩ : syracuseStep 23109299 = 34663949) B34663949
theorem B15406199 : Blo 2027435 15406199 := bstep (se 1 (by rfl) ⟨11554649, by rfl⟩ : syracuseStep 15406199 = 23109299) B23109299
theorem B10270799 : Blo 2027435 10270799 := bstep (se 1 (by rfl) ⟨7703099, by rfl⟩ : syracuseStep 10270799 = 15406199) B15406199
theorem B6847199 : Blo 2027435 6847199 := bstep (se 1 (by rfl) ⟨5135399, by rfl⟩ : syracuseStep 6847199 = 10270799) B10270799
theorem B4564799 : Blo 2027435 4564799 := bstep (se 1 (by rfl) ⟨3423599, by rfl⟩ : syracuseStep 4564799 = 6847199) B6847199
theorem B3043199 : Blo 2027435 3043199 := bstep (se 1 (by rfl) ⟨2282399, by rfl⟩ : syracuseStep 3043199 = 4564799) B4564799
theorem B2028799 : Blo 2027435 2028799 := bstep (se 1 (by rfl) ⟨1521599, by rfl⟩ : syracuseStep 2028799 = 3043199) B3043199
theorem B3043205 : Blo 2027435 3043205 := bbase (se 4 (by rfl) ⟨285300, by rfl⟩ : syracuseStep 3043205 = 570601) (by norm_num)
theorem B2028803 : Blo 2027435 2028803 := bstep (se 1 (by rfl) ⟨1521602, by rfl⟩ : syracuseStep 2028803 = 3043205) B3043205
theorem B3423613 : Blo 2027435 3423613 := bbase (se 3 (by rfl) ⟨641927, by rfl⟩ : syracuseStep 3423613 = 1283855) (by norm_num)
theorem B4564817 : Blo 2027435 4564817 := bstep (se 2 (by rfl) ⟨1711806, by rfl⟩ : syracuseStep 4564817 = 3423613) B3423613
theorem B3043211 : Blo 2027435 3043211 := bstep (se 1 (by rfl) ⟨2282408, by rfl⟩ : syracuseStep 3043211 = 4564817) B4564817
theorem B2028807 : Blo 2027435 2028807 := bstep (se 1 (by rfl) ⟨1521605, by rfl⟩ : syracuseStep 2028807 = 3043211) B3043211
theorem B2282413 : Blo 2027435 2282413 := bbase (se 3 (by rfl) ⟨427952, by rfl⟩ : syracuseStep 2282413 = 855905) (by norm_num)
theorem B3043217 : Blo 2027435 3043217 := bstep (se 2 (by rfl) ⟨1141206, by rfl⟩ : syracuseStep 3043217 = 2282413) B2282413
theorem B2028811 : Blo 2027435 2028811 := bstep (se 1 (by rfl) ⟨1521608, by rfl⟩ : syracuseStep 2028811 = 3043217) B3043217
theorem B6847253 : Blo 2027435 6847253 := bbase (se 6 (by rfl) ⟨160482, by rfl⟩ : syracuseStep 6847253 = 320965) (by norm_num)
theorem B4564835 : Blo 2027435 4564835 := bstep (se 1 (by rfl) ⟨3423626, by rfl⟩ : syracuseStep 4564835 = 6847253) B6847253
theorem B3043223 : Blo 2027435 3043223 := bstep (se 1 (by rfl) ⟨2282417, by rfl⟩ : syracuseStep 3043223 = 4564835) B4564835
theorem B2028815 : Blo 2027435 2028815 := bstep (se 1 (by rfl) ⟨1521611, by rfl⟩ : syracuseStep 2028815 = 3043223) B3043223
theorem B3043229 : Blo 2027435 3043229 := bbase (se 3 (by rfl) ⟨570605, by rfl⟩ : syracuseStep 3043229 = 1141211) (by norm_num)
theorem B2028819 : Blo 2027435 2028819 := bstep (se 1 (by rfl) ⟨1521614, by rfl⟩ : syracuseStep 2028819 = 3043229) B3043229
theorem B4564853 : Blo 2027435 4564853 := bbase (se 5 (by rfl) ⟨213977, by rfl⟩ : syracuseStep 4564853 = 427955) (by norm_num)
theorem B3043235 : Blo 2027435 3043235 := bstep (se 1 (by rfl) ⟨2282426, by rfl⟩ : syracuseStep 3043235 = 4564853) B4564853
theorem B2028823 : Blo 2027435 2028823 := bstep (se 1 (by rfl) ⟨1521617, by rfl⟩ : syracuseStep 2028823 = 3043235) B3043235
theorem B24678101 : Blo 2027435 24678101 := bbase (se 7 (by rfl) ⟨289196, by rfl⟩ : syracuseStep 24678101 = 578393) (by norm_num)
theorem B16452067 : Blo 2027435 16452067 := bstep (se 1 (by rfl) ⟨12339050, by rfl⟩ : syracuseStep 16452067 = 24678101) B24678101
theorem B21936089 : Blo 2027435 21936089 := bstep (se 2 (by rfl) ⟨8226033, by rfl⟩ : syracuseStep 21936089 = 16452067) B16452067
theorem B14624059 : Blo 2027435 14624059 := bstep (se 1 (by rfl) ⟨10968044, by rfl⟩ : syracuseStep 14624059 = 21936089) B21936089
theorem B19498745 : Blo 2027435 19498745 := bstep (se 2 (by rfl) ⟨7312029, by rfl⟩ : syracuseStep 19498745 = 14624059) B14624059
theorem B12999163 : Blo 2027435 12999163 := bstep (se 1 (by rfl) ⟨9749372, by rfl⟩ : syracuseStep 12999163 = 19498745) B19498745
theorem B17332217 : Blo 2027435 17332217 := bstep (se 2 (by rfl) ⟨6499581, by rfl⟩ : syracuseStep 17332217 = 12999163) B12999163
theorem B11554811 : Blo 2027435 11554811 := bstep (se 1 (by rfl) ⟨8666108, by rfl⟩ : syracuseStep 11554811 = 17332217) B17332217
theorem B7703207 : Blo 2027435 7703207 := bstep (se 1 (by rfl) ⟨5777405, by rfl⟩ : syracuseStep 7703207 = 11554811) B11554811
theorem B5135471 : Blo 2027435 5135471 := bstep (se 1 (by rfl) ⟨3851603, by rfl⟩ : syracuseStep 5135471 = 7703207) B7703207
theorem B3423647 : Blo 2027435 3423647 := bstep (se 1 (by rfl) ⟨2567735, by rfl⟩ : syracuseStep 3423647 = 5135471) B5135471
theorem B2282431 : Blo 2027435 2282431 := bstep (se 1 (by rfl) ⟨1711823, by rfl⟩ : syracuseStep 2282431 = 3423647) B3423647
theorem B3043241 : Blo 2027435 3043241 := bstep (se 2 (by rfl) ⟨1141215, by rfl⟩ : syracuseStep 3043241 = 2282431) B2282431
theorem B2028827 : Blo 2027435 2028827 := bstep (se 1 (by rfl) ⟨1521620, by rfl⟩ : syracuseStep 2028827 = 3043241) B3043241
theorem B7703221 : Blo 2027435 7703221 := bbase (se 5 (by rfl) ⟨361088, by rfl⟩ : syracuseStep 7703221 = 722177) (by norm_num)
theorem B10270961 : Blo 2027435 10270961 := bstep (se 2 (by rfl) ⟨3851610, by rfl⟩ : syracuseStep 10270961 = 7703221) B7703221
theorem B6847307 : Blo 2027435 6847307 := bstep (se 1 (by rfl) ⟨5135480, by rfl⟩ : syracuseStep 6847307 = 10270961) B10270961
theorem B4564871 : Blo 2027435 4564871 := bstep (se 1 (by rfl) ⟨3423653, by rfl⟩ : syracuseStep 4564871 = 6847307) B6847307
theorem B3043247 : Blo 2027435 3043247 := bstep (se 1 (by rfl) ⟨2282435, by rfl⟩ : syracuseStep 3043247 = 4564871) B4564871
theorem B2028831 : Blo 2027435 2028831 := bstep (se 1 (by rfl) ⟨1521623, by rfl⟩ : syracuseStep 2028831 = 3043247) B3043247
theorem B3043253 : Blo 2027435 3043253 := bbase (se 5 (by rfl) ⟨142652, by rfl⟩ : syracuseStep 3043253 = 285305) (by norm_num)
theorem B2028835 : Blo 2027435 2028835 := bstep (se 1 (by rfl) ⟨1521626, by rfl⟩ : syracuseStep 2028835 = 3043253) B3043253
theorem B5135501 : Blo 2027435 5135501 := bbase (se 3 (by rfl) ⟨962906, by rfl⟩ : syracuseStep 5135501 = 1925813) (by norm_num)
theorem B3423667 : Blo 2027435 3423667 := bstep (se 1 (by rfl) ⟨2567750, by rfl⟩ : syracuseStep 3423667 = 5135501) B5135501
theorem B4564889 : Blo 2027435 4564889 := bstep (se 2 (by rfl) ⟨1711833, by rfl⟩ : syracuseStep 4564889 = 3423667) B3423667
theorem B3043259 : Blo 2027435 3043259 := bstep (se 1 (by rfl) ⟨2282444, by rfl⟩ : syracuseStep 3043259 = 4564889) B4564889
theorem B2028839 : Blo 2027435 2028839 := bstep (se 1 (by rfl) ⟨1521629, by rfl⟩ : syracuseStep 2028839 = 3043259) B3043259
theorem B2282449 : Blo 2027435 2282449 := bbase (se 2 (by rfl) ⟨855918, by rfl⟩ : syracuseStep 2282449 = 1711837) (by norm_num)
theorem B3043265 : Blo 2027435 3043265 := bstep (se 2 (by rfl) ⟨1141224, by rfl⟩ : syracuseStep 3043265 = 2282449) B2282449
theorem B2028843 : Blo 2027435 2028843 := bstep (se 1 (by rfl) ⟨1521632, by rfl⟩ : syracuseStep 2028843 = 3043265) B3043265
theorem B6588325 : Blo 2027435 6588325 := bbase (se 4 (by rfl) ⟨617655, by rfl⟩ : syracuseStep 6588325 = 1235311) (by norm_num)
theorem B8784433 : Blo 2027435 8784433 := bstep (se 2 (by rfl) ⟨3294162, by rfl⟩ : syracuseStep 8784433 = 6588325) B6588325
theorem B46850309 : Blo 2027435 46850309 := bstep (se 4 (by rfl) ⟨4392216, by rfl⟩ : syracuseStep 46850309 = 8784433) B8784433
theorem B31233539 : Blo 2027435 31233539 := bstep (se 1 (by rfl) ⟨23425154, by rfl⟩ : syracuseStep 31233539 = 46850309) B46850309
theorem B20822359 : Blo 2027435 20822359 := bstep (se 1 (by rfl) ⟨15616769, by rfl⟩ : syracuseStep 20822359 = 31233539) B31233539
theorem B27763145 : Blo 2027435 27763145 := bstep (se 2 (by rfl) ⟨10411179, by rfl⟩ : syracuseStep 27763145 = 20822359) B20822359
theorem B18508763 : Blo 2027435 18508763 := bstep (se 1 (by rfl) ⟨13881572, by rfl⟩ : syracuseStep 18508763 = 27763145) B27763145
theorem B12339175 : Blo 2027435 12339175 := bstep (se 1 (by rfl) ⟨9254381, by rfl⟩ : syracuseStep 12339175 = 18508763) B18508763
theorem B16452233 : Blo 2027435 16452233 := bstep (se 2 (by rfl) ⟨6169587, by rfl⟩ : syracuseStep 16452233 = 12339175) B12339175
theorem B10968155 : Blo 2027435 10968155 := bstep (se 1 (by rfl) ⟨8226116, by rfl⟩ : syracuseStep 10968155 = 16452233) B16452233
theorem B7312103 : Blo 2027435 7312103 := bstep (se 1 (by rfl) ⟨5484077, by rfl⟩ : syracuseStep 7312103 = 10968155) B10968155
theorem B4874735 : Blo 2027435 4874735 := bstep (se 1 (by rfl) ⟨3656051, by rfl⟩ : syracuseStep 4874735 = 7312103) B7312103
theorem B3249823 : Blo 2027435 3249823 := bstep (se 1 (by rfl) ⟨2437367, by rfl⟩ : syracuseStep 3249823 = 4874735) B4874735
theorem B4333097 : Blo 2027435 4333097 := bstep (se 2 (by rfl) ⟨1624911, by rfl⟩ : syracuseStep 4333097 = 3249823) B3249823
theorem B2888731 : Blo 2027435 2888731 := bstep (se 1 (by rfl) ⟨2166548, by rfl⟩ : syracuseStep 2888731 = 4333097) B4333097
theorem B3851641 : Blo 2027435 3851641 := bstep (se 2 (by rfl) ⟨1444365, by rfl⟩ : syracuseStep 3851641 = 2888731) B2888731
theorem B5135521 : Blo 2027435 5135521 := bstep (se 2 (by rfl) ⟨1925820, by rfl⟩ : syracuseStep 5135521 = 3851641) B3851641
theorem B6847361 : Blo 2027435 6847361 := bstep (se 2 (by rfl) ⟨2567760, by rfl⟩ : syracuseStep 6847361 = 5135521) B5135521
theorem B4564907 : Blo 2027435 4564907 := bstep (se 1 (by rfl) ⟨3423680, by rfl⟩ : syracuseStep 4564907 = 6847361) B6847361
theorem B3043271 : Blo 2027435 3043271 := bstep (se 1 (by rfl) ⟨2282453, by rfl⟩ : syracuseStep 3043271 = 4564907) B4564907
theorem B2028847 : Blo 2027435 2028847 := bstep (se 1 (by rfl) ⟨1521635, by rfl⟩ : syracuseStep 2028847 = 3043271) B3043271
theorem B3043277 : Blo 2027435 3043277 := bbase (se 3 (by rfl) ⟨570614, by rfl⟩ : syracuseStep 3043277 = 1141229) (by norm_num)
theorem B2028851 : Blo 2027435 2028851 := bstep (se 1 (by rfl) ⟨1521638, by rfl⟩ : syracuseStep 2028851 = 3043277) B3043277
theorem B4564925 : Blo 2027435 4564925 := bbase (se 3 (by rfl) ⟨855923, by rfl⟩ : syracuseStep 4564925 = 1711847) (by norm_num)
theorem B3043283 : Blo 2027435 3043283 := bstep (se 1 (by rfl) ⟨2282462, by rfl⟩ : syracuseStep 3043283 = 4564925) B4564925
theorem B2028855 : Blo 2027435 2028855 := bstep (se 1 (by rfl) ⟨1521641, by rfl⟩ : syracuseStep 2028855 = 3043283) B3043283
theorem B3423701 : Blo 2027435 3423701 := bbase (se 7 (by rfl) ⟨40121, by rfl⟩ : syracuseStep 3423701 = 80243) (by norm_num)
theorem B2282467 : Blo 2027435 2282467 := bstep (se 1 (by rfl) ⟨1711850, by rfl⟩ : syracuseStep 2282467 = 3423701) B3423701
theorem B3043289 : Blo 2027435 3043289 := bstep (se 2 (by rfl) ⟨1141233, by rfl⟩ : syracuseStep 3043289 = 2282467) B2282467
theorem B2028859 : Blo 2027435 2028859 := bstep (se 1 (by rfl) ⟨1521644, by rfl⟩ : syracuseStep 2028859 = 3043289) B3043289
theorem B8666261 : Blo 2027435 8666261 := bbase (se 6 (by rfl) ⟨203115, by rfl⟩ : syracuseStep 8666261 = 406231) (by norm_num)
theorem B5777507 : Blo 2027435 5777507 := bstep (se 1 (by rfl) ⟨4333130, by rfl⟩ : syracuseStep 5777507 = 8666261) B8666261
theorem B15406685 : Blo 2027435 15406685 := bstep (se 3 (by rfl) ⟨2888753, by rfl⟩ : syracuseStep 15406685 = 5777507) B5777507
theorem B10271123 : Blo 2027435 10271123 := bstep (se 1 (by rfl) ⟨7703342, by rfl⟩ : syracuseStep 10271123 = 15406685) B15406685
theorem B6847415 : Blo 2027435 6847415 := bstep (se 1 (by rfl) ⟨5135561, by rfl⟩ : syracuseStep 6847415 = 10271123) B10271123
theorem B4564943 : Blo 2027435 4564943 := bstep (se 1 (by rfl) ⟨3423707, by rfl⟩ : syracuseStep 4564943 = 6847415) B6847415
theorem B3043295 : Blo 2027435 3043295 := bstep (se 1 (by rfl) ⟨2282471, by rfl⟩ : syracuseStep 3043295 = 4564943) B4564943
theorem B2028863 : Blo 2027435 2028863 := bstep (se 1 (by rfl) ⟨1521647, by rfl⟩ : syracuseStep 2028863 = 3043295) B3043295
theorem B3043301 : Blo 2027435 3043301 := bbase (se 4 (by rfl) ⟨285309, by rfl⟩ : syracuseStep 3043301 = 570619) (by norm_num)
theorem B2028867 : Blo 2027435 2028867 := bstep (se 1 (by rfl) ⟨1521650, by rfl⟩ : syracuseStep 2028867 = 3043301) B3043301
theorem B5205653 : Blo 2027435 5205653 := bbase (se 6 (by rfl) ⟨122007, by rfl⟩ : syracuseStep 5205653 = 244015) (by norm_num)
theorem B3470435 : Blo 2027435 3470435 := bstep (se 1 (by rfl) ⟨2602826, by rfl⟩ : syracuseStep 3470435 = 5205653) B5205653
theorem B2313623 : Blo 2027435 2313623 := bstep (se 1 (by rfl) ⟨1735217, by rfl⟩ : syracuseStep 2313623 = 3470435) B3470435
theorem B6169661 : Blo 2027435 6169661 := bstep (se 3 (by rfl) ⟨1156811, by rfl⟩ : syracuseStep 6169661 = 2313623) B2313623
theorem B4113107 : Blo 2027435 4113107 := bstep (se 1 (by rfl) ⟨3084830, by rfl⟩ : syracuseStep 4113107 = 6169661) B6169661
theorem B2742071 : Blo 2027435 2742071 := bstep (se 1 (by rfl) ⟨2056553, by rfl⟩ : syracuseStep 2742071 = 4113107) B4113107
theorem B7312189 : Blo 2027435 7312189 := bstep (se 3 (by rfl) ⟨1371035, by rfl⟩ : syracuseStep 7312189 = 2742071) B2742071
theorem B9749585 : Blo 2027435 9749585 := bstep (se 2 (by rfl) ⟨3656094, by rfl⟩ : syracuseStep 9749585 = 7312189) B7312189
theorem B6499723 : Blo 2027435 6499723 := bstep (se 1 (by rfl) ⟨4874792, by rfl⟩ : syracuseStep 6499723 = 9749585) B9749585
theorem B8666297 : Blo 2027435 8666297 := bstep (se 2 (by rfl) ⟨3249861, by rfl⟩ : syracuseStep 8666297 = 6499723) B6499723
theorem B5777531 : Blo 2027435 5777531 := bstep (se 1 (by rfl) ⟨4333148, by rfl⟩ : syracuseStep 5777531 = 8666297) B8666297
theorem B3851687 : Blo 2027435 3851687 := bstep (se 1 (by rfl) ⟨2888765, by rfl⟩ : syracuseStep 3851687 = 5777531) B5777531
theorem B2567791 : Blo 2027435 2567791 := bstep (se 1 (by rfl) ⟨1925843, by rfl⟩ : syracuseStep 2567791 = 3851687) B3851687
theorem B3423721 : Blo 2027435 3423721 := bstep (se 2 (by rfl) ⟨1283895, by rfl⟩ : syracuseStep 3423721 = 2567791) B2567791
theorem B4564961 : Blo 2027435 4564961 := bstep (se 2 (by rfl) ⟨1711860, by rfl⟩ : syracuseStep 4564961 = 3423721) B3423721
theorem B3043307 : Blo 2027435 3043307 := bstep (se 1 (by rfl) ⟨2282480, by rfl⟩ : syracuseStep 3043307 = 4564961) B4564961
theorem B2028871 : Blo 2027435 2028871 := bstep (se 1 (by rfl) ⟨1521653, by rfl⟩ : syracuseStep 2028871 = 3043307) B3043307
theorem B2282485 : Blo 2027435 2282485 := bbase (se 5 (by rfl) ⟨106991, by rfl⟩ : syracuseStep 2282485 = 213983) (by norm_num)
theorem B3043313 : Blo 2027435 3043313 := bstep (se 2 (by rfl) ⟨1141242, by rfl⟩ : syracuseStep 3043313 = 2282485) B2282485
theorem B2028875 : Blo 2027435 2028875 := bstep (se 1 (by rfl) ⟨1521656, by rfl⟩ : syracuseStep 2028875 = 3043313) B3043313
theorem B2567801 : Blo 2027435 2567801 := bbase (se 2 (by rfl) ⟨962925, by rfl⟩ : syracuseStep 2567801 = 1925851) (by norm_num)
theorem B6847469 : Blo 2027435 6847469 := bstep (se 3 (by rfl) ⟨1283900, by rfl⟩ : syracuseStep 6847469 = 2567801) B2567801
theorem B4564979 : Blo 2027435 4564979 := bstep (se 1 (by rfl) ⟨3423734, by rfl⟩ : syracuseStep 4564979 = 6847469) B6847469
theorem B3043319 : Blo 2027435 3043319 := bstep (se 1 (by rfl) ⟨2282489, by rfl⟩ : syracuseStep 3043319 = 4564979) B4564979
theorem B2028879 : Blo 2027435 2028879 := bstep (se 1 (by rfl) ⟨1521659, by rfl⟩ : syracuseStep 2028879 = 3043319) B3043319
theorem B3043325 : Blo 2027435 3043325 := bbase (se 3 (by rfl) ⟨570623, by rfl⟩ : syracuseStep 3043325 = 1141247) (by norm_num)
theorem B2028883 : Blo 2027435 2028883 := bstep (se 1 (by rfl) ⟨1521662, by rfl⟩ : syracuseStep 2028883 = 3043325) B3043325
theorem B4564997 : Blo 2027435 4564997 := bbase (se 4 (by rfl) ⟨427968, by rfl⟩ : syracuseStep 4564997 = 855937) (by norm_num)
theorem B3043331 : Blo 2027435 3043331 := bstep (se 1 (by rfl) ⟨2282498, by rfl⟩ : syracuseStep 3043331 = 4564997) B4564997
theorem B2028887 : Blo 2027435 2028887 := bstep (se 1 (by rfl) ⟨1521665, by rfl⟩ : syracuseStep 2028887 = 3043331) B3043331
theorem B3851725 : Blo 2027435 3851725 := bbase (se 3 (by rfl) ⟨722198, by rfl⟩ : syracuseStep 3851725 = 1444397) (by norm_num)
theorem B5135633 : Blo 2027435 5135633 := bstep (se 2 (by rfl) ⟨1925862, by rfl⟩ : syracuseStep 5135633 = 3851725) B3851725
theorem B3423755 : Blo 2027435 3423755 := bstep (se 1 (by rfl) ⟨2567816, by rfl⟩ : syracuseStep 3423755 = 5135633) B5135633
theorem B2282503 : Blo 2027435 2282503 := bstep (se 1 (by rfl) ⟨1711877, by rfl⟩ : syracuseStep 2282503 = 3423755) B3423755
theorem B3043337 : Blo 2027435 3043337 := bstep (se 2 (by rfl) ⟨1141251, by rfl⟩ : syracuseStep 3043337 = 2282503) B2282503
theorem B2028891 : Blo 2027435 2028891 := bstep (se 1 (by rfl) ⟨1521668, by rfl⟩ : syracuseStep 2028891 = 3043337) B3043337
theorem B10271285 : Blo 2027435 10271285 := bbase (se 5 (by rfl) ⟨481466, by rfl⟩ : syracuseStep 10271285 = 962933) (by norm_num)
theorem B6847523 : Blo 2027435 6847523 := bstep (se 1 (by rfl) ⟨5135642, by rfl⟩ : syracuseStep 6847523 = 10271285) B10271285
theorem B4565015 : Blo 2027435 4565015 := bstep (se 1 (by rfl) ⟨3423761, by rfl⟩ : syracuseStep 4565015 = 6847523) B6847523
theorem B3043343 : Blo 2027435 3043343 := bstep (se 1 (by rfl) ⟨2282507, by rfl⟩ : syracuseStep 3043343 = 4565015) B4565015
theorem B2028895 : Blo 2027435 2028895 := bstep (se 1 (by rfl) ⟨1521671, by rfl⟩ : syracuseStep 2028895 = 3043343) B3043343
theorem B3043349 : Blo 2027435 3043349 := bbase (se 6 (by rfl) ⟨71328, by rfl⟩ : syracuseStep 3043349 = 142657) (by norm_num)
theorem B2028899 : Blo 2027435 2028899 := bstep (se 1 (by rfl) ⟨1521674, by rfl⟩ : syracuseStep 2028899 = 3043349) B3043349
theorem B18509269 : Blo 2027435 18509269 := bbase (se 7 (by rfl) ⟨216905, by rfl⟩ : syracuseStep 18509269 = 433811) (by norm_num)
theorem B24679025 : Blo 2027435 24679025 := bstep (se 2 (by rfl) ⟨9254634, by rfl⟩ : syracuseStep 24679025 = 18509269) B18509269
theorem B16452683 : Blo 2027435 16452683 := bstep (se 1 (by rfl) ⟨12339512, by rfl⟩ : syracuseStep 16452683 = 24679025) B24679025
theorem B10968455 : Blo 2027435 10968455 := bstep (se 1 (by rfl) ⟨8226341, by rfl⟩ : syracuseStep 10968455 = 16452683) B16452683
theorem B7312303 : Blo 2027435 7312303 := bstep (se 1 (by rfl) ⟨5484227, by rfl⟩ : syracuseStep 7312303 = 10968455) B10968455
theorem B9749737 : Blo 2027435 9749737 := bstep (se 2 (by rfl) ⟨3656151, by rfl⟩ : syracuseStep 9749737 = 7312303) B7312303
theorem B12999649 : Blo 2027435 12999649 := bstep (se 2 (by rfl) ⟨4874868, by rfl⟩ : syracuseStep 12999649 = 9749737) B9749737
theorem B17332865 : Blo 2027435 17332865 := bstep (se 2 (by rfl) ⟨6499824, by rfl⟩ : syracuseStep 17332865 = 12999649) B12999649
theorem B11555243 : Blo 2027435 11555243 := bstep (se 1 (by rfl) ⟨8666432, by rfl⟩ : syracuseStep 11555243 = 17332865) B17332865
theorem B7703495 : Blo 2027435 7703495 := bstep (se 1 (by rfl) ⟨5777621, by rfl⟩ : syracuseStep 7703495 = 11555243) B11555243
theorem B5135663 : Blo 2027435 5135663 := bstep (se 1 (by rfl) ⟨3851747, by rfl⟩ : syracuseStep 5135663 = 7703495) B7703495
theorem B3423775 : Blo 2027435 3423775 := bstep (se 1 (by rfl) ⟨2567831, by rfl⟩ : syracuseStep 3423775 = 5135663) B5135663
theorem B4565033 : Blo 2027435 4565033 := bstep (se 2 (by rfl) ⟨1711887, by rfl⟩ : syracuseStep 4565033 = 3423775) B3423775
theorem B3043355 : Blo 2027435 3043355 := bstep (se 1 (by rfl) ⟨2282516, by rfl⟩ : syracuseStep 3043355 = 4565033) B4565033
theorem B2028903 : Blo 2027435 2028903 := bstep (se 1 (by rfl) ⟨1521677, by rfl⟩ : syracuseStep 2028903 = 3043355) B3043355
theorem B2282521 : Blo 2027435 2282521 := bbase (se 2 (by rfl) ⟨855945, by rfl⟩ : syracuseStep 2282521 = 1711891) (by norm_num)
theorem B3043361 : Blo 2027435 3043361 := bstep (se 2 (by rfl) ⟨1141260, by rfl⟩ : syracuseStep 3043361 = 2282521) B2282521
theorem B2028907 : Blo 2027435 2028907 := bstep (se 1 (by rfl) ⟨1521680, by rfl⟩ : syracuseStep 2028907 = 3043361) B3043361
theorem B7703525 : Blo 2027435 7703525 := bbase (se 4 (by rfl) ⟨722205, by rfl⟩ : syracuseStep 7703525 = 1444411) (by norm_num)
theorem B5135683 : Blo 2027435 5135683 := bstep (se 1 (by rfl) ⟨3851762, by rfl⟩ : syracuseStep 5135683 = 7703525) B7703525
theorem B6847577 : Blo 2027435 6847577 := bstep (se 2 (by rfl) ⟨2567841, by rfl⟩ : syracuseStep 6847577 = 5135683) B5135683
theorem B4565051 : Blo 2027435 4565051 := bstep (se 1 (by rfl) ⟨3423788, by rfl⟩ : syracuseStep 4565051 = 6847577) B6847577
theorem B3043367 : Blo 2027435 3043367 := bstep (se 1 (by rfl) ⟨2282525, by rfl⟩ : syracuseStep 3043367 = 4565051) B4565051
theorem B2028911 : Blo 2027435 2028911 := bstep (se 1 (by rfl) ⟨1521683, by rfl⟩ : syracuseStep 2028911 = 3043367) B3043367
theorem B3043373 : Blo 2027435 3043373 := bbase (se 3 (by rfl) ⟨570632, by rfl⟩ : syracuseStep 3043373 = 1141265) (by norm_num)
theorem B2028915 : Blo 2027435 2028915 := bstep (se 1 (by rfl) ⟨1521686, by rfl⟩ : syracuseStep 2028915 = 3043373) B3043373
theorem B4565069 : Blo 2027435 4565069 := bbase (se 3 (by rfl) ⟨855950, by rfl⟩ : syracuseStep 4565069 = 1711901) (by norm_num)
theorem B3043379 : Blo 2027435 3043379 := bstep (se 1 (by rfl) ⟨2282534, by rfl⟩ : syracuseStep 3043379 = 4565069) B4565069
theorem B2028919 : Blo 2027435 2028919 := bstep (se 1 (by rfl) ⟨1521689, by rfl⟩ : syracuseStep 2028919 = 3043379) B3043379
theorem B2567857 : Blo 2027435 2567857 := bbase (se 2 (by rfl) ⟨962946, by rfl⟩ : syracuseStep 2567857 = 1925893) (by norm_num)
theorem B3423809 : Blo 2027435 3423809 := bstep (se 2 (by rfl) ⟨1283928, by rfl⟩ : syracuseStep 3423809 = 2567857) B2567857
theorem B2282539 : Blo 2027435 2282539 := bstep (se 1 (by rfl) ⟨1711904, by rfl⟩ : syracuseStep 2282539 = 3423809) B3423809
theorem B3043385 : Blo 2027435 3043385 := bstep (se 2 (by rfl) ⟨1141269, by rfl⟩ : syracuseStep 3043385 = 2282539) B2282539
theorem B2028923 : Blo 2027435 2028923 := bstep (se 1 (by rfl) ⟨1521692, by rfl⟩ : syracuseStep 2028923 = 3043385) B3043385
theorem B5484293 : Blo 2027435 5484293 := bbase (se 4 (by rfl) ⟨514152, by rfl⟩ : syracuseStep 5484293 = 1028305) (by norm_num)
theorem B3656195 : Blo 2027435 3656195 := bstep (se 1 (by rfl) ⟨2742146, by rfl⟩ : syracuseStep 3656195 = 5484293) B5484293
theorem B2437463 : Blo 2027435 2437463 := bstep (se 1 (by rfl) ⟨1828097, by rfl⟩ : syracuseStep 2437463 = 3656195) B3656195
theorem B6499901 : Blo 2027435 6499901 := bstep (se 3 (by rfl) ⟨1218731, by rfl⟩ : syracuseStep 6499901 = 2437463) B2437463
theorem B4333267 : Blo 2027435 4333267 := bstep (se 1 (by rfl) ⟨3249950, by rfl⟩ : syracuseStep 4333267 = 6499901) B6499901
theorem B23110757 : Blo 2027435 23110757 := bstep (se 4 (by rfl) ⟨2166633, by rfl⟩ : syracuseStep 23110757 = 4333267) B4333267
theorem B15407171 : Blo 2027435 15407171 := bstep (se 1 (by rfl) ⟨11555378, by rfl⟩ : syracuseStep 15407171 = 23110757) B23110757
theorem B10271447 : Blo 2027435 10271447 := bstep (se 1 (by rfl) ⟨7703585, by rfl⟩ : syracuseStep 10271447 = 15407171) B15407171
theorem B6847631 : Blo 2027435 6847631 := bstep (se 1 (by rfl) ⟨5135723, by rfl⟩ : syracuseStep 6847631 = 10271447) B10271447
theorem B4565087 : Blo 2027435 4565087 := bstep (se 1 (by rfl) ⟨3423815, by rfl⟩ : syracuseStep 4565087 = 6847631) B6847631
theorem B3043391 : Blo 2027435 3043391 := bstep (se 1 (by rfl) ⟨2282543, by rfl⟩ : syracuseStep 3043391 = 4565087) B4565087
theorem B2028927 : Blo 2027435 2028927 := bstep (se 1 (by rfl) ⟨1521695, by rfl⟩ : syracuseStep 2028927 = 3043391) B3043391
theorem B3043397 : Blo 2027435 3043397 := bbase (se 4 (by rfl) ⟨285318, by rfl⟩ : syracuseStep 3043397 = 570637) (by norm_num)
theorem B2028931 : Blo 2027435 2028931 := bstep (se 1 (by rfl) ⟨1521698, by rfl⟩ : syracuseStep 2028931 = 3043397) B3043397
theorem B3423829 : Blo 2027435 3423829 := bbase (se 8 (by rfl) ⟨20061, by rfl⟩ : syracuseStep 3423829 = 40123) (by norm_num)
theorem B4565105 : Blo 2027435 4565105 := bstep (se 2 (by rfl) ⟨1711914, by rfl⟩ : syracuseStep 4565105 = 3423829) B3423829
theorem B3043403 : Blo 2027435 3043403 := bstep (se 1 (by rfl) ⟨2282552, by rfl⟩ : syracuseStep 3043403 = 4565105) B4565105
theorem B2028935 : Blo 2027435 2028935 := bstep (se 1 (by rfl) ⟨1521701, by rfl⟩ : syracuseStep 2028935 = 3043403) B3043403
theorem B2282557 : Blo 2027435 2282557 := bbase (se 3 (by rfl) ⟨427979, by rfl⟩ : syracuseStep 2282557 = 855959) (by norm_num)
theorem B3043409 : Blo 2027435 3043409 := bstep (se 2 (by rfl) ⟨1141278, by rfl⟩ : syracuseStep 3043409 = 2282557) B2282557
theorem B2028939 : Blo 2027435 2028939 := bstep (se 1 (by rfl) ⟨1521704, by rfl⟩ : syracuseStep 2028939 = 3043409) B3043409
theorem B6847685 : Blo 2027435 6847685 := bbase (se 4 (by rfl) ⟨641970, by rfl⟩ : syracuseStep 6847685 = 1283941) (by norm_num)
theorem B4565123 : Blo 2027435 4565123 := bstep (se 1 (by rfl) ⟨3423842, by rfl⟩ : syracuseStep 4565123 = 6847685) B6847685
theorem B3043415 : Blo 2027435 3043415 := bstep (se 1 (by rfl) ⟨2282561, by rfl⟩ : syracuseStep 3043415 = 4565123) B4565123
theorem B2028943 : Blo 2027435 2028943 := bstep (se 1 (by rfl) ⟨1521707, by rfl⟩ : syracuseStep 2028943 = 3043415) B3043415
theorem B3043421 : Blo 2027435 3043421 := bbase (se 3 (by rfl) ⟨570641, by rfl⟩ : syracuseStep 3043421 = 1141283) (by norm_num)
theorem B2028947 : Blo 2027435 2028947 := bstep (se 1 (by rfl) ⟨1521710, by rfl⟩ : syracuseStep 2028947 = 3043421) B3043421
theorem B4565141 : Blo 2027435 4565141 := bbase (se 6 (by rfl) ⟨106995, by rfl⟩ : syracuseStep 4565141 = 213991) (by norm_num)
theorem B3043427 : Blo 2027435 3043427 := bstep (se 1 (by rfl) ⟨2282570, by rfl⟩ : syracuseStep 3043427 = 4565141) B4565141
theorem B2028951 : Blo 2027435 2028951 := bstep (se 1 (by rfl) ⟨1521713, by rfl⟩ : syracuseStep 2028951 = 3043427) B3043427
theorem B2888885 : Blo 2027435 2888885 := bbase (se 5 (by rfl) ⟨135416, by rfl⟩ : syracuseStep 2888885 = 270833) (by norm_num)
theorem B7703693 : Blo 2027435 7703693 := bstep (se 3 (by rfl) ⟨1444442, by rfl⟩ : syracuseStep 7703693 = 2888885) B2888885
theorem B5135795 : Blo 2027435 5135795 := bstep (se 1 (by rfl) ⟨3851846, by rfl⟩ : syracuseStep 5135795 = 7703693) B7703693
theorem B3423863 : Blo 2027435 3423863 := bstep (se 1 (by rfl) ⟨2567897, by rfl⟩ : syracuseStep 3423863 = 5135795) B5135795
theorem B2282575 : Blo 2027435 2282575 := bstep (se 1 (by rfl) ⟨1711931, by rfl⟩ : syracuseStep 2282575 = 3423863) B3423863
theorem B3043433 : Blo 2027435 3043433 := bstep (se 2 (by rfl) ⟨1141287, by rfl⟩ : syracuseStep 3043433 = 2282575) B2282575
theorem B2028955 : Blo 2027435 2028955 := bstep (se 1 (by rfl) ⟨1521716, by rfl⟩ : syracuseStep 2028955 = 3043433) B3043433
theorem B2196229 : Blo 2027435 2196229 := bbase (se 4 (by rfl) ⟨205896, by rfl⟩ : syracuseStep 2196229 = 411793) (by norm_num)
theorem B2928305 : Blo 2027435 2928305 := bstep (se 2 (by rfl) ⟨1098114, by rfl⟩ : syracuseStep 2928305 = 2196229) B2196229
theorem B7808813 : Blo 2027435 7808813 := bstep (se 3 (by rfl) ⟨1464152, by rfl⟩ : syracuseStep 7808813 = 2928305) B2928305
theorem B5205875 : Blo 2027435 5205875 := bstep (se 1 (by rfl) ⟨3904406, by rfl⟩ : syracuseStep 5205875 = 7808813) B7808813
theorem B55529333 : Blo 2027435 55529333 := bstep (se 5 (by rfl) ⟨2602937, by rfl⟩ : syracuseStep 55529333 = 5205875) B5205875
theorem B37019555 : Blo 2027435 37019555 := bstep (se 1 (by rfl) ⟨27764666, by rfl⟩ : syracuseStep 37019555 = 55529333) B55529333
theorem B24679703 : Blo 2027435 24679703 := bstep (se 1 (by rfl) ⟨18509777, by rfl⟩ : syracuseStep 24679703 = 37019555) B37019555
theorem B16453135 : Blo 2027435 16453135 := bstep (se 1 (by rfl) ⟨12339851, by rfl⟩ : syracuseStep 16453135 = 24679703) B24679703
theorem B21937513 : Blo 2027435 21937513 := bstep (se 2 (by rfl) ⟨8226567, by rfl⟩ : syracuseStep 21937513 = 16453135) B16453135
theorem B29250017 : Blo 2027435 29250017 := bstep (se 2 (by rfl) ⟨10968756, by rfl⟩ : syracuseStep 29250017 = 21937513) B21937513
theorem B19500011 : Blo 2027435 19500011 := bstep (se 1 (by rfl) ⟨14625008, by rfl⟩ : syracuseStep 19500011 = 29250017) B29250017
theorem B13000007 : Blo 2027435 13000007 := bstep (se 1 (by rfl) ⟨9750005, by rfl⟩ : syracuseStep 13000007 = 19500011) B19500011
theorem B8666671 : Blo 2027435 8666671 := bstep (se 1 (by rfl) ⟨6500003, by rfl⟩ : syracuseStep 8666671 = 13000007) B13000007
theorem B11555561 : Blo 2027435 11555561 := bstep (se 2 (by rfl) ⟨4333335, by rfl⟩ : syracuseStep 11555561 = 8666671) B8666671
theorem B7703707 : Blo 2027435 7703707 := bstep (se 1 (by rfl) ⟨5777780, by rfl⟩ : syracuseStep 7703707 = 11555561) B11555561
theorem B10271609 : Blo 2027435 10271609 := bstep (se 2 (by rfl) ⟨3851853, by rfl⟩ : syracuseStep 10271609 = 7703707) B7703707
theorem B6847739 : Blo 2027435 6847739 := bstep (se 1 (by rfl) ⟨5135804, by rfl⟩ : syracuseStep 6847739 = 10271609) B10271609
theorem B4565159 : Blo 2027435 4565159 := bstep (se 1 (by rfl) ⟨3423869, by rfl⟩ : syracuseStep 4565159 = 6847739) B6847739
theorem B3043439 : Blo 2027435 3043439 := bstep (se 1 (by rfl) ⟨2282579, by rfl⟩ : syracuseStep 3043439 = 4565159) B4565159
theorem B2028959 : Blo 2027435 2028959 := bstep (se 1 (by rfl) ⟨1521719, by rfl⟩ : syracuseStep 2028959 = 3043439) B3043439
theorem B3043445 : Blo 2027435 3043445 := bbase (se 5 (by rfl) ⟨142661, by rfl⟩ : syracuseStep 3043445 = 285323) (by norm_num)
theorem B2028963 : Blo 2027435 2028963 := bstep (se 1 (by rfl) ⟨1521722, by rfl⟩ : syracuseStep 2028963 = 3043445) B3043445
theorem B3851869 : Blo 2027435 3851869 := bbase (se 3 (by rfl) ⟨722225, by rfl⟩ : syracuseStep 3851869 = 1444451) (by norm_num)
theorem B5135825 : Blo 2027435 5135825 := bstep (se 2 (by rfl) ⟨1925934, by rfl⟩ : syracuseStep 5135825 = 3851869) B3851869
theorem B3423883 : Blo 2027435 3423883 := bstep (se 1 (by rfl) ⟨2567912, by rfl⟩ : syracuseStep 3423883 = 5135825) B5135825
theorem B4565177 : Blo 2027435 4565177 := bstep (se 2 (by rfl) ⟨1711941, by rfl⟩ : syracuseStep 4565177 = 3423883) B3423883
theorem B3043451 : Blo 2027435 3043451 := bstep (se 1 (by rfl) ⟨2282588, by rfl⟩ : syracuseStep 3043451 = 4565177) B4565177
theorem B2028967 : Blo 2027435 2028967 := bstep (se 1 (by rfl) ⟨1521725, by rfl⟩ : syracuseStep 2028967 = 3043451) B3043451
theorem B2282593 : Blo 2027435 2282593 := bbase (se 2 (by rfl) ⟨855972, by rfl⟩ : syracuseStep 2282593 = 1711945) (by norm_num)
theorem B3043457 : Blo 2027435 3043457 := bstep (se 2 (by rfl) ⟨1141296, by rfl⟩ : syracuseStep 3043457 = 2282593) B2282593
theorem B2028971 : Blo 2027435 2028971 := bstep (se 1 (by rfl) ⟨1521728, by rfl⟩ : syracuseStep 2028971 = 3043457) B3043457
theorem B5135845 : Blo 2027435 5135845 := bbase (se 4 (by rfl) ⟨481485, by rfl⟩ : syracuseStep 5135845 = 962971) (by norm_num)
theorem B6847793 : Blo 2027435 6847793 := bstep (se 2 (by rfl) ⟨2567922, by rfl⟩ : syracuseStep 6847793 = 5135845) B5135845
theorem B4565195 : Blo 2027435 4565195 := bstep (se 1 (by rfl) ⟨3423896, by rfl⟩ : syracuseStep 4565195 = 6847793) B6847793
theorem B3043463 : Blo 2027435 3043463 := bstep (se 1 (by rfl) ⟨2282597, by rfl⟩ : syracuseStep 3043463 = 4565195) B4565195
theorem B2028975 : Blo 2027435 2028975 := bstep (se 1 (by rfl) ⟨1521731, by rfl⟩ : syracuseStep 2028975 = 3043463) B3043463
theorem B3043469 : Blo 2027435 3043469 := bbase (se 3 (by rfl) ⟨570650, by rfl⟩ : syracuseStep 3043469 = 1141301) (by norm_num)
theorem B2028979 : Blo 2027435 2028979 := bstep (se 1 (by rfl) ⟨1521734, by rfl⟩ : syracuseStep 2028979 = 3043469) B3043469
theorem B4565213 : Blo 2027435 4565213 := bbase (se 3 (by rfl) ⟨855977, by rfl⟩ : syracuseStep 4565213 = 1711955) (by norm_num)
theorem B3043475 : Blo 2027435 3043475 := bstep (se 1 (by rfl) ⟨2282606, by rfl⟩ : syracuseStep 3043475 = 4565213) B4565213
theorem B2028983 : Blo 2027435 2028983 := bstep (se 1 (by rfl) ⟨1521737, by rfl⟩ : syracuseStep 2028983 = 3043475) B3043475
theorem B3423917 : Blo 2027435 3423917 := bbase (se 3 (by rfl) ⟨641984, by rfl⟩ : syracuseStep 3423917 = 1283969) (by norm_num)
theorem B2282611 : Blo 2027435 2282611 := bstep (se 1 (by rfl) ⟨1711958, by rfl⟩ : syracuseStep 2282611 = 3423917) B3423917
theorem B3043481 : Blo 2027435 3043481 := bstep (se 2 (by rfl) ⟨1141305, by rfl⟩ : syracuseStep 3043481 = 2282611) B2282611
theorem B2028987 : Blo 2027435 2028987 := bstep (se 1 (by rfl) ⟨1521740, by rfl⟩ : syracuseStep 2028987 = 3043481) B3043481
theorem B4627517 : Blo 2027435 4627517 := bbase (se 3 (by rfl) ⟨867659, by rfl⟩ : syracuseStep 4627517 = 1735319) (by norm_num)
theorem B12340045 : Blo 2027435 12340045 := bstep (se 3 (by rfl) ⟨2313758, by rfl⟩ : syracuseStep 12340045 = 4627517) B4627517
theorem B65813573 : Blo 2027435 65813573 := bstep (se 4 (by rfl) ⟨6170022, by rfl⟩ : syracuseStep 65813573 = 12340045) B12340045
theorem B43875715 : Blo 2027435 43875715 := bstep (se 1 (by rfl) ⟨32906786, by rfl⟩ : syracuseStep 43875715 = 65813573) B65813573
theorem B58500953 : Blo 2027435 58500953 := bstep (se 2 (by rfl) ⟨21937857, by rfl⟩ : syracuseStep 58500953 = 43875715) B43875715
theorem B39000635 : Blo 2027435 39000635 := bstep (se 1 (by rfl) ⟨29250476, by rfl⟩ : syracuseStep 39000635 = 58500953) B58500953
theorem B26000423 : Blo 2027435 26000423 := bstep (se 1 (by rfl) ⟨19500317, by rfl⟩ : syracuseStep 26000423 = 39000635) B39000635
theorem B17333615 : Blo 2027435 17333615 := bstep (se 1 (by rfl) ⟨13000211, by rfl⟩ : syracuseStep 17333615 = 26000423) B26000423
theorem B11555743 : Blo 2027435 11555743 := bstep (se 1 (by rfl) ⟨8666807, by rfl⟩ : syracuseStep 11555743 = 17333615) B17333615
theorem B15407657 : Blo 2027435 15407657 := bstep (se 2 (by rfl) ⟨5777871, by rfl⟩ : syracuseStep 15407657 = 11555743) B11555743
theorem B10271771 : Blo 2027435 10271771 := bstep (se 1 (by rfl) ⟨7703828, by rfl⟩ : syracuseStep 10271771 = 15407657) B15407657
theorem B6847847 : Blo 2027435 6847847 := bstep (se 1 (by rfl) ⟨5135885, by rfl⟩ : syracuseStep 6847847 = 10271771) B10271771
theorem B4565231 : Blo 2027435 4565231 := bstep (se 1 (by rfl) ⟨3423923, by rfl⟩ : syracuseStep 4565231 = 6847847) B6847847
theorem B3043487 : Blo 2027435 3043487 := bstep (se 1 (by rfl) ⟨2282615, by rfl⟩ : syracuseStep 3043487 = 4565231) B4565231
theorem B2028991 : Blo 2027435 2028991 := bstep (se 1 (by rfl) ⟨1521743, by rfl⟩ : syracuseStep 2028991 = 3043487) B3043487
theorem B3043493 : Blo 2027435 3043493 := bbase (se 4 (by rfl) ⟨285327, by rfl⟩ : syracuseStep 3043493 = 570655) (by norm_num)
theorem B2028995 : Blo 2027435 2028995 := bstep (se 1 (by rfl) ⟨1521746, by rfl⟩ : syracuseStep 2028995 = 3043493) B3043493
theorem B2567953 : Blo 2027435 2567953 := bbase (se 2 (by rfl) ⟨962982, by rfl⟩ : syracuseStep 2567953 = 1925965) (by norm_num)
theorem B3423937 : Blo 2027435 3423937 := bstep (se 2 (by rfl) ⟨1283976, by rfl⟩ : syracuseStep 3423937 = 2567953) B2567953
theorem B4565249 : Blo 2027435 4565249 := bstep (se 2 (by rfl) ⟨1711968, by rfl⟩ : syracuseStep 4565249 = 3423937) B3423937
theorem B3043499 : Blo 2027435 3043499 := bstep (se 1 (by rfl) ⟨2282624, by rfl⟩ : syracuseStep 3043499 = 4565249) B4565249
theorem B2028999 : Blo 2027435 2028999 := bstep (se 1 (by rfl) ⟨1521749, by rfl⟩ : syracuseStep 2028999 = 3043499) B3043499
theorem B2282629 : Blo 2027435 2282629 := bbase (se 4 (by rfl) ⟨213996, by rfl⟩ : syracuseStep 2282629 = 427993) (by norm_num)
theorem B3043505 : Blo 2027435 3043505 := bstep (se 2 (by rfl) ⟨1141314, by rfl⟩ : syracuseStep 3043505 = 2282629) B2282629
theorem B2029003 : Blo 2027435 2029003 := bstep (se 1 (by rfl) ⟨1521752, by rfl⟩ : syracuseStep 2029003 = 3043505) B3043505
theorem B6941333 : Blo 2027435 6941333 := bbase (se 6 (by rfl) ⟨162687, by rfl⟩ : syracuseStep 6941333 = 325375) (by norm_num)
theorem B18510221 : Blo 2027435 18510221 := bstep (se 3 (by rfl) ⟨3470666, by rfl⟩ : syracuseStep 18510221 = 6941333) B6941333
theorem B49360589 : Blo 2027435 49360589 := bstep (se 3 (by rfl) ⟨9255110, by rfl⟩ : syracuseStep 49360589 = 18510221) B18510221
theorem B32907059 : Blo 2027435 32907059 := bstep (se 1 (by rfl) ⟨24680294, by rfl⟩ : syracuseStep 32907059 = 49360589) B49360589
theorem B21938039 : Blo 2027435 21938039 := bstep (se 1 (by rfl) ⟨16453529, by rfl⟩ : syracuseStep 21938039 = 32907059) B32907059
theorem B14625359 : Blo 2027435 14625359 := bstep (se 1 (by rfl) ⟨10969019, by rfl⟩ : syracuseStep 14625359 = 21938039) B21938039
theorem B9750239 : Blo 2027435 9750239 := bstep (se 1 (by rfl) ⟨7312679, by rfl⟩ : syracuseStep 9750239 = 14625359) B14625359
theorem B6500159 : Blo 2027435 6500159 := bstep (se 1 (by rfl) ⟨4875119, by rfl⟩ : syracuseStep 6500159 = 9750239) B9750239
theorem B4333439 : Blo 2027435 4333439 := bstep (se 1 (by rfl) ⟨3250079, by rfl⟩ : syracuseStep 4333439 = 6500159) B6500159
theorem B2888959 : Blo 2027435 2888959 := bstep (se 1 (by rfl) ⟨2166719, by rfl⟩ : syracuseStep 2888959 = 4333439) B4333439
theorem B3851945 : Blo 2027435 3851945 := bstep (se 2 (by rfl) ⟨1444479, by rfl⟩ : syracuseStep 3851945 = 2888959) B2888959
theorem B2567963 : Blo 2027435 2567963 := bstep (se 1 (by rfl) ⟨1925972, by rfl⟩ : syracuseStep 2567963 = 3851945) B3851945
theorem B6847901 : Blo 2027435 6847901 := bstep (se 3 (by rfl) ⟨1283981, by rfl⟩ : syracuseStep 6847901 = 2567963) B2567963
theorem B4565267 : Blo 2027435 4565267 := bstep (se 1 (by rfl) ⟨3423950, by rfl⟩ : syracuseStep 4565267 = 6847901) B6847901
theorem B3043511 : Blo 2027435 3043511 := bstep (se 1 (by rfl) ⟨2282633, by rfl⟩ : syracuseStep 3043511 = 4565267) B4565267
theorem B2029007 : Blo 2027435 2029007 := bstep (se 1 (by rfl) ⟨1521755, by rfl⟩ : syracuseStep 2029007 = 3043511) B3043511
theorem B3043517 : Blo 2027435 3043517 := bbase (se 3 (by rfl) ⟨570659, by rfl⟩ : syracuseStep 3043517 = 1141319) (by norm_num)
theorem B2029011 : Blo 2027435 2029011 := bstep (se 1 (by rfl) ⟨1521758, by rfl⟩ : syracuseStep 2029011 = 3043517) B3043517
theorem B4565285 : Blo 2027435 4565285 := bbase (se 4 (by rfl) ⟨427995, by rfl⟩ : syracuseStep 4565285 = 855991) (by norm_num)
theorem B3043523 : Blo 2027435 3043523 := bstep (se 1 (by rfl) ⟨2282642, by rfl⟩ : syracuseStep 3043523 = 4565285) B4565285
theorem B2029015 : Blo 2027435 2029015 := bstep (se 1 (by rfl) ⟨1521761, by rfl⟩ : syracuseStep 2029015 = 3043523) B3043523
theorem B5135957 : Blo 2027435 5135957 := bbase (se 8 (by rfl) ⟨30093, by rfl⟩ : syracuseStep 5135957 = 60187) (by norm_num)
theorem B3423971 : Blo 2027435 3423971 := bstep (se 1 (by rfl) ⟨2567978, by rfl⟩ : syracuseStep 3423971 = 5135957) B5135957
theorem B2282647 : Blo 2027435 2282647 := bstep (se 1 (by rfl) ⟨1711985, by rfl⟩ : syracuseStep 2282647 = 3423971) B3423971
theorem B3043529 : Blo 2027435 3043529 := bstep (se 2 (by rfl) ⟨1141323, by rfl⟩ : syracuseStep 3043529 = 2282647) B2282647
theorem B2029019 : Blo 2027435 2029019 := bstep (se 1 (by rfl) ⟨1521764, by rfl⟩ : syracuseStep 2029019 = 3043529) B3043529
theorem B4875157 : Blo 2027435 4875157 := bbase (se 6 (by rfl) ⟨114261, by rfl⟩ : syracuseStep 4875157 = 228523) (by norm_num)
theorem B6500209 : Blo 2027435 6500209 := bstep (se 2 (by rfl) ⟨2437578, by rfl⟩ : syracuseStep 6500209 = 4875157) B4875157
theorem B8666945 : Blo 2027435 8666945 := bstep (se 2 (by rfl) ⟨3250104, by rfl⟩ : syracuseStep 8666945 = 6500209) B6500209
theorem B5777963 : Blo 2027435 5777963 := bstep (se 1 (by rfl) ⟨4333472, by rfl⟩ : syracuseStep 5777963 = 8666945) B8666945
theorem B3851975 : Blo 2027435 3851975 := bstep (se 1 (by rfl) ⟨2888981, by rfl⟩ : syracuseStep 3851975 = 5777963) B5777963
theorem B10271933 : Blo 2027435 10271933 := bstep (se 3 (by rfl) ⟨1925987, by rfl⟩ : syracuseStep 10271933 = 3851975) B3851975
theorem B6847955 : Blo 2027435 6847955 := bstep (se 1 (by rfl) ⟨5135966, by rfl⟩ : syracuseStep 6847955 = 10271933) B10271933
theorem B4565303 : Blo 2027435 4565303 := bstep (se 1 (by rfl) ⟨3423977, by rfl⟩ : syracuseStep 4565303 = 6847955) B6847955
theorem B3043535 : Blo 2027435 3043535 := bstep (se 1 (by rfl) ⟨2282651, by rfl⟩ : syracuseStep 3043535 = 4565303) B4565303
theorem B2029023 : Blo 2027435 2029023 := bstep (se 1 (by rfl) ⟨1521767, by rfl⟩ : syracuseStep 2029023 = 3043535) B3043535
theorem B3043541 : Blo 2027435 3043541 := bbase (se 7 (by rfl) ⟨35666, by rfl⟩ : syracuseStep 3043541 = 71333) (by norm_num)
theorem B2029027 : Blo 2027435 2029027 := bstep (se 1 (by rfl) ⟨1521770, by rfl⟩ : syracuseStep 2029027 = 3043541) B3043541
theorem B2166745 : Blo 2027435 2166745 := bbase (se 2 (by rfl) ⟨812529, by rfl⟩ : syracuseStep 2166745 = 1625059) (by norm_num)
theorem B2888993 : Blo 2027435 2888993 := bstep (se 2 (by rfl) ⟨1083372, by rfl⟩ : syracuseStep 2888993 = 2166745) B2166745
theorem B7703981 : Blo 2027435 7703981 := bstep (se 3 (by rfl) ⟨1444496, by rfl⟩ : syracuseStep 7703981 = 2888993) B2888993
theorem B5135987 : Blo 2027435 5135987 := bstep (se 1 (by rfl) ⟨3851990, by rfl⟩ : syracuseStep 5135987 = 7703981) B7703981
theorem B3423991 : Blo 2027435 3423991 := bstep (se 1 (by rfl) ⟨2567993, by rfl⟩ : syracuseStep 3423991 = 5135987) B5135987
theorem B4565321 : Blo 2027435 4565321 := bstep (se 2 (by rfl) ⟨1711995, by rfl⟩ : syracuseStep 4565321 = 3423991) B3423991
theorem B3043547 : Blo 2027435 3043547 := bstep (se 1 (by rfl) ⟨2282660, by rfl⟩ : syracuseStep 3043547 = 4565321) B4565321
theorem B2029031 : Blo 2027435 2029031 := bstep (se 1 (by rfl) ⟨1521773, by rfl⟩ : syracuseStep 2029031 = 3043547) B3043547
theorem B2282665 : Blo 2027435 2282665 := bbase (se 2 (by rfl) ⟨855999, by rfl⟩ : syracuseStep 2282665 = 1711999) (by norm_num)
theorem B3043553 : Blo 2027435 3043553 := bstep (se 2 (by rfl) ⟨1141332, by rfl⟩ : syracuseStep 3043553 = 2282665) B2282665
theorem B2029035 : Blo 2027435 2029035 := bstep (se 1 (by rfl) ⟨1521776, by rfl⟩ : syracuseStep 2029035 = 3043553) B3043553
theorem B8667013 : Blo 2027435 8667013 := bbase (se 4 (by rfl) ⟨812532, by rfl⟩ : syracuseStep 8667013 = 1625065) (by norm_num)
theorem B11556017 : Blo 2027435 11556017 := bstep (se 2 (by rfl) ⟨4333506, by rfl⟩ : syracuseStep 11556017 = 8667013) B8667013
theorem B7704011 : Blo 2027435 7704011 := bstep (se 1 (by rfl) ⟨5778008, by rfl⟩ : syracuseStep 7704011 = 11556017) B11556017
theorem B5136007 : Blo 2027435 5136007 := bstep (se 1 (by rfl) ⟨3852005, by rfl⟩ : syracuseStep 5136007 = 7704011) B7704011
theorem B6848009 : Blo 2027435 6848009 := bstep (se 2 (by rfl) ⟨2568003, by rfl⟩ : syracuseStep 6848009 = 5136007) B5136007
theorem B4565339 : Blo 2027435 4565339 := bstep (se 1 (by rfl) ⟨3424004, by rfl⟩ : syracuseStep 4565339 = 6848009) B6848009
theorem B3043559 : Blo 2027435 3043559 := bstep (se 1 (by rfl) ⟨2282669, by rfl⟩ : syracuseStep 3043559 = 4565339) B4565339
theorem B2029039 : Blo 2027435 2029039 := bstep (se 1 (by rfl) ⟨1521779, by rfl⟩ : syracuseStep 2029039 = 3043559) B3043559
theorem B3043565 : Blo 2027435 3043565 := bbase (se 3 (by rfl) ⟨570668, by rfl⟩ : syracuseStep 3043565 = 1141337) (by norm_num)
theorem B2029043 : Blo 2027435 2029043 := bstep (se 1 (by rfl) ⟨1521782, by rfl⟩ : syracuseStep 2029043 = 3043565) B3043565
theorem B4565357 : Blo 2027435 4565357 := bbase (se 3 (by rfl) ⟨856004, by rfl⟩ : syracuseStep 4565357 = 1712009) (by norm_num)
theorem B3043571 : Blo 2027435 3043571 := bstep (se 1 (by rfl) ⟨2282678, by rfl⟩ : syracuseStep 3043571 = 4565357) B4565357
theorem B2029047 : Blo 2027435 2029047 := bstep (se 1 (by rfl) ⟨1521785, by rfl⟩ : syracuseStep 2029047 = 3043571) B3043571
theorem B3852029 : Blo 2027435 3852029 := bbase (se 3 (by rfl) ⟨722255, by rfl⟩ : syracuseStep 3852029 = 1444511) (by norm_num)
theorem B2568019 : Blo 2027435 2568019 := bstep (se 1 (by rfl) ⟨1926014, by rfl⟩ : syracuseStep 2568019 = 3852029) B3852029
theorem B3424025 : Blo 2027435 3424025 := bstep (se 2 (by rfl) ⟨1284009, by rfl⟩ : syracuseStep 3424025 = 2568019) B2568019
theorem B2282683 : Blo 2027435 2282683 := bstep (se 1 (by rfl) ⟨1712012, by rfl⟩ : syracuseStep 2282683 = 3424025) B3424025
theorem B3043577 : Blo 2027435 3043577 := bstep (se 2 (by rfl) ⟨1141341, by rfl⟩ : syracuseStep 3043577 = 2282683) B2282683
theorem B2029051 : Blo 2027435 2029051 := bstep (se 1 (by rfl) ⟨1521788, by rfl⟩ : syracuseStep 2029051 = 3043577) B3043577
theorem B6254405 : Blo 2027435 6254405 := bbase (se 4 (by rfl) ⟨586350, by rfl⟩ : syracuseStep 6254405 = 1172701) (by norm_num)
theorem B4169603 : Blo 2027435 4169603 := bstep (se 1 (by rfl) ⟨3127202, by rfl⟩ : syracuseStep 4169603 = 6254405) B6254405
theorem B11118941 : Blo 2027435 11118941 := bstep (se 3 (by rfl) ⟨2084801, by rfl⟩ : syracuseStep 11118941 = 4169603) B4169603
theorem B7412627 : Blo 2027435 7412627 := bstep (se 1 (by rfl) ⟨5559470, by rfl⟩ : syracuseStep 7412627 = 11118941) B11118941
theorem B4941751 : Blo 2027435 4941751 := bstep (se 1 (by rfl) ⟨3706313, by rfl⟩ : syracuseStep 4941751 = 7412627) B7412627
theorem B6589001 : Blo 2027435 6589001 := bstep (se 2 (by rfl) ⟨2470875, by rfl⟩ : syracuseStep 6589001 = 4941751) B4941751
theorem B4392667 : Blo 2027435 4392667 := bstep (se 1 (by rfl) ⟨3294500, by rfl⟩ : syracuseStep 4392667 = 6589001) B6589001
theorem B5856889 : Blo 2027435 5856889 := bstep (se 2 (by rfl) ⟨2196333, by rfl⟩ : syracuseStep 5856889 = 4392667) B4392667
theorem B7809185 : Blo 2027435 7809185 := bstep (se 2 (by rfl) ⟨2928444, by rfl⟩ : syracuseStep 7809185 = 5856889) B5856889
theorem B5206123 : Blo 2027435 5206123 := bstep (se 1 (by rfl) ⟨3904592, by rfl⟩ : syracuseStep 5206123 = 7809185) B7809185
theorem B6941497 : Blo 2027435 6941497 := bstep (se 2 (by rfl) ⟨2603061, by rfl⟩ : syracuseStep 6941497 = 5206123) B5206123
theorem B9255329 : Blo 2027435 9255329 := bstep (se 2 (by rfl) ⟨3470748, by rfl⟩ : syracuseStep 9255329 = 6941497) B6941497
theorem B6170219 : Blo 2027435 6170219 := bstep (se 1 (by rfl) ⟨4627664, by rfl⟩ : syracuseStep 6170219 = 9255329) B9255329
theorem B4113479 : Blo 2027435 4113479 := bstep (se 1 (by rfl) ⟨3085109, by rfl⟩ : syracuseStep 4113479 = 6170219) B6170219
theorem B2742319 : Blo 2027435 2742319 := bstep (se 1 (by rfl) ⟨2056739, by rfl⟩ : syracuseStep 2742319 = 4113479) B4113479
theorem B3656425 : Blo 2027435 3656425 := bstep (se 2 (by rfl) ⟨1371159, by rfl⟩ : syracuseStep 3656425 = 2742319) B2742319
theorem B4875233 : Blo 2027435 4875233 := bstep (se 2 (by rfl) ⟨1828212, by rfl⟩ : syracuseStep 4875233 = 3656425) B3656425
theorem B52002485 : Blo 2027435 52002485 := bstep (se 5 (by rfl) ⟨2437616, by rfl⟩ : syracuseStep 52002485 = 4875233) B4875233
theorem B34668323 : Blo 2027435 34668323 := bstep (se 1 (by rfl) ⟨26001242, by rfl⟩ : syracuseStep 34668323 = 52002485) B52002485
theorem B23112215 : Blo 2027435 23112215 := bstep (se 1 (by rfl) ⟨17334161, by rfl⟩ : syracuseStep 23112215 = 34668323) B34668323
theorem B15408143 : Blo 2027435 15408143 := bstep (se 1 (by rfl) ⟨11556107, by rfl⟩ : syracuseStep 15408143 = 23112215) B23112215
theorem B10272095 : Blo 2027435 10272095 := bstep (se 1 (by rfl) ⟨7704071, by rfl⟩ : syracuseStep 10272095 = 15408143) B15408143
theorem B6848063 : Blo 2027435 6848063 := bstep (se 1 (by rfl) ⟨5136047, by rfl⟩ : syracuseStep 6848063 = 10272095) B10272095
theorem B4565375 : Blo 2027435 4565375 := bstep (se 1 (by rfl) ⟨3424031, by rfl⟩ : syracuseStep 4565375 = 6848063) B6848063
theorem B3043583 : Blo 2027435 3043583 := bstep (se 1 (by rfl) ⟨2282687, by rfl⟩ : syracuseStep 3043583 = 4565375) B4565375
theorem B2029055 : Blo 2027435 2029055 := bstep (se 1 (by rfl) ⟨1521791, by rfl⟩ : syracuseStep 2029055 = 3043583) B3043583
theorem B3043589 : Blo 2027435 3043589 := bbase (se 4 (by rfl) ⟨285336, by rfl⟩ : syracuseStep 3043589 = 570673) (by norm_num)
theorem B2029059 : Blo 2027435 2029059 := bstep (se 1 (by rfl) ⟨1521794, by rfl⟩ : syracuseStep 2029059 = 3043589) B3043589
theorem B3424045 : Blo 2027435 3424045 := bbase (se 3 (by rfl) ⟨642008, by rfl⟩ : syracuseStep 3424045 = 1284017) (by norm_num)
theorem B4565393 : Blo 2027435 4565393 := bstep (se 2 (by rfl) ⟨1712022, by rfl⟩ : syracuseStep 4565393 = 3424045) B3424045
theorem B3043595 : Blo 2027435 3043595 := bstep (se 1 (by rfl) ⟨2282696, by rfl⟩ : syracuseStep 3043595 = 4565393) B4565393
theorem B2029063 : Blo 2027435 2029063 := bstep (se 1 (by rfl) ⟨1521797, by rfl⟩ : syracuseStep 2029063 = 3043595) B3043595
theorem B2282701 : Blo 2027435 2282701 := bbase (se 3 (by rfl) ⟨428006, by rfl⟩ : syracuseStep 2282701 = 856013) (by norm_num)
theorem B3043601 : Blo 2027435 3043601 := bstep (se 2 (by rfl) ⟨1141350, by rfl⟩ : syracuseStep 3043601 = 2282701) B2282701
theorem B2029067 : Blo 2027435 2029067 := bstep (se 1 (by rfl) ⟨1521800, by rfl⟩ : syracuseStep 2029067 = 3043601) B3043601
theorem B6848117 : Blo 2027435 6848117 := bbase (se 5 (by rfl) ⟨321005, by rfl⟩ : syracuseStep 6848117 = 642011) (by norm_num)
theorem B4565411 : Blo 2027435 4565411 := bstep (se 1 (by rfl) ⟨3424058, by rfl⟩ : syracuseStep 4565411 = 6848117) B6848117
theorem B3043607 : Blo 2027435 3043607 := bstep (se 1 (by rfl) ⟨2282705, by rfl⟩ : syracuseStep 3043607 = 4565411) B4565411
theorem B2029071 : Blo 2027435 2029071 := bstep (se 1 (by rfl) ⟨1521803, by rfl⟩ : syracuseStep 2029071 = 3043607) B3043607
theorem B3043613 : Blo 2027435 3043613 := bbase (se 3 (by rfl) ⟨570677, by rfl⟩ : syracuseStep 3043613 = 1141355) (by norm_num)
theorem B2029075 : Blo 2027435 2029075 := bstep (se 1 (by rfl) ⟨1521806, by rfl⟩ : syracuseStep 2029075 = 3043613) B3043613
theorem B4565429 : Blo 2027435 4565429 := bbase (se 5 (by rfl) ⟨214004, by rfl⟩ : syracuseStep 4565429 = 428009) (by norm_num)
theorem B3043619 : Blo 2027435 3043619 := bstep (se 1 (by rfl) ⟨2282714, by rfl⟩ : syracuseStep 3043619 = 4565429) B4565429
theorem B2029079 : Blo 2027435 2029079 := bstep (se 1 (by rfl) ⟨1521809, by rfl⟩ : syracuseStep 2029079 = 3043619) B3043619
theorem B3656477 : Blo 2027435 3656477 := bbase (se 3 (by rfl) ⟨685589, by rfl⟩ : syracuseStep 3656477 = 1371179) (by norm_num)
theorem B2437651 : Blo 2027435 2437651 := bstep (se 1 (by rfl) ⟨1828238, by rfl⟩ : syracuseStep 2437651 = 3656477) B3656477
theorem B3250201 : Blo 2027435 3250201 := bstep (se 2 (by rfl) ⟨1218825, by rfl⟩ : syracuseStep 3250201 = 2437651) B2437651
theorem B4333601 : Blo 2027435 4333601 := bstep (se 2 (by rfl) ⟨1625100, by rfl⟩ : syracuseStep 4333601 = 3250201) B3250201
theorem B11556269 : Blo 2027435 11556269 := bstep (se 3 (by rfl) ⟨2166800, by rfl⟩ : syracuseStep 11556269 = 4333601) B4333601
theorem B7704179 : Blo 2027435 7704179 := bstep (se 1 (by rfl) ⟨5778134, by rfl⟩ : syracuseStep 7704179 = 11556269) B11556269
theorem B5136119 : Blo 2027435 5136119 := bstep (se 1 (by rfl) ⟨3852089, by rfl⟩ : syracuseStep 5136119 = 7704179) B7704179
theorem B3424079 : Blo 2027435 3424079 := bstep (se 1 (by rfl) ⟨2568059, by rfl⟩ : syracuseStep 3424079 = 5136119) B5136119
theorem B2282719 : Blo 2027435 2282719 := bstep (se 1 (by rfl) ⟨1712039, by rfl⟩ : syracuseStep 2282719 = 3424079) B3424079
theorem B3043625 : Blo 2027435 3043625 := bstep (se 2 (by rfl) ⟨1141359, by rfl⟩ : syracuseStep 3043625 = 2282719) B2282719
theorem B2029083 : Blo 2027435 2029083 := bstep (se 1 (by rfl) ⟨1521812, by rfl⟩ : syracuseStep 2029083 = 3043625) B3043625
theorem B5206205 : Blo 2027435 5206205 := bbase (se 3 (by rfl) ⟨976163, by rfl⟩ : syracuseStep 5206205 = 1952327) (by norm_num)
theorem B13883213 : Blo 2027435 13883213 := bstep (se 3 (by rfl) ⟨2603102, by rfl⟩ : syracuseStep 13883213 = 5206205) B5206205
theorem B9255475 : Blo 2027435 9255475 := bstep (se 1 (by rfl) ⟨6941606, by rfl⟩ : syracuseStep 9255475 = 13883213) B13883213
theorem B12340633 : Blo 2027435 12340633 := bstep (se 2 (by rfl) ⟨4627737, by rfl⟩ : syracuseStep 12340633 = 9255475) B9255475
theorem B16454177 : Blo 2027435 16454177 := bstep (se 2 (by rfl) ⟨6170316, by rfl⟩ : syracuseStep 16454177 = 12340633) B12340633
theorem B10969451 : Blo 2027435 10969451 := bstep (se 1 (by rfl) ⟨8227088, by rfl⟩ : syracuseStep 10969451 = 16454177) B16454177
theorem B7312967 : Blo 2027435 7312967 := bstep (se 1 (by rfl) ⟨5484725, by rfl⟩ : syracuseStep 7312967 = 10969451) B10969451
theorem B4875311 : Blo 2027435 4875311 := bstep (se 1 (by rfl) ⟨3656483, by rfl⟩ : syracuseStep 4875311 = 7312967) B7312967
theorem B3250207 : Blo 2027435 3250207 := bstep (se 1 (by rfl) ⟨2437655, by rfl⟩ : syracuseStep 3250207 = 4875311) B4875311
theorem B4333609 : Blo 2027435 4333609 := bstep (se 2 (by rfl) ⟨1625103, by rfl⟩ : syracuseStep 4333609 = 3250207) B3250207
theorem B5778145 : Blo 2027435 5778145 := bstep (se 2 (by rfl) ⟨2166804, by rfl⟩ : syracuseStep 5778145 = 4333609) B4333609
theorem B7704193 : Blo 2027435 7704193 := bstep (se 2 (by rfl) ⟨2889072, by rfl⟩ : syracuseStep 7704193 = 5778145) B5778145
theorem B10272257 : Blo 2027435 10272257 := bstep (se 2 (by rfl) ⟨3852096, by rfl⟩ : syracuseStep 10272257 = 7704193) B7704193
theorem B6848171 : Blo 2027435 6848171 := bstep (se 1 (by rfl) ⟨5136128, by rfl⟩ : syracuseStep 6848171 = 10272257) B10272257
theorem B4565447 : Blo 2027435 4565447 := bstep (se 1 (by rfl) ⟨3424085, by rfl⟩ : syracuseStep 4565447 = 6848171) B6848171
theorem B3043631 : Blo 2027435 3043631 := bstep (se 1 (by rfl) ⟨2282723, by rfl⟩ : syracuseStep 3043631 = 4565447) B4565447
theorem B2029087 : Blo 2027435 2029087 := bstep (se 1 (by rfl) ⟨1521815, by rfl⟩ : syracuseStep 2029087 = 3043631) B3043631
theorem B3043637 : Blo 2027435 3043637 := bbase (se 5 (by rfl) ⟨142670, by rfl⟩ : syracuseStep 3043637 = 285341) (by norm_num)
theorem B2029091 : Blo 2027435 2029091 := bstep (se 1 (by rfl) ⟨1521818, by rfl⟩ : syracuseStep 2029091 = 3043637) B3043637
theorem B5136149 : Blo 2027435 5136149 := bbase (se 6 (by rfl) ⟨120378, by rfl⟩ : syracuseStep 5136149 = 240757) (by norm_num)
theorem B3424099 : Blo 2027435 3424099 := bstep (se 1 (by rfl) ⟨2568074, by rfl⟩ : syracuseStep 3424099 = 5136149) B5136149
theorem B4565465 : Blo 2027435 4565465 := bstep (se 2 (by rfl) ⟨1712049, by rfl⟩ : syracuseStep 4565465 = 3424099) B3424099
theorem B3043643 : Blo 2027435 3043643 := bstep (se 1 (by rfl) ⟨2282732, by rfl⟩ : syracuseStep 3043643 = 4565465) B4565465
theorem B2029095 : Blo 2027435 2029095 := bstep (se 1 (by rfl) ⟨1521821, by rfl⟩ : syracuseStep 2029095 = 3043643) B3043643
theorem B2282737 : Blo 2027435 2282737 := bbase (se 2 (by rfl) ⟨856026, by rfl⟩ : syracuseStep 2282737 = 1712053) (by norm_num)
theorem B3043649 : Blo 2027435 3043649 := bstep (se 2 (by rfl) ⟨1141368, by rfl⟩ : syracuseStep 3043649 = 2282737) B2282737
theorem B2029099 : Blo 2027435 2029099 := bstep (se 1 (by rfl) ⟨1521824, by rfl⟩ : syracuseStep 2029099 = 3043649) B3043649
theorem B19501397 : Blo 2027435 19501397 := bbase (se 10 (by rfl) ⟨28566, by rfl⟩ : syracuseStep 19501397 = 57133) (by norm_num)
theorem B13000931 : Blo 2027435 13000931 := bstep (se 1 (by rfl) ⟨9750698, by rfl⟩ : syracuseStep 13000931 = 19501397) B19501397
theorem B8667287 : Blo 2027435 8667287 := bstep (se 1 (by rfl) ⟨6500465, by rfl⟩ : syracuseStep 8667287 = 13000931) B13000931
theorem B5778191 : Blo 2027435 5778191 := bstep (se 1 (by rfl) ⟨4333643, by rfl⟩ : syracuseStep 5778191 = 8667287) B8667287
theorem B3852127 : Blo 2027435 3852127 := bstep (se 1 (by rfl) ⟨2889095, by rfl⟩ : syracuseStep 3852127 = 5778191) B5778191
theorem B5136169 : Blo 2027435 5136169 := bstep (se 2 (by rfl) ⟨1926063, by rfl⟩ : syracuseStep 5136169 = 3852127) B3852127
theorem B6848225 : Blo 2027435 6848225 := bstep (se 2 (by rfl) ⟨2568084, by rfl⟩ : syracuseStep 6848225 = 5136169) B5136169
theorem B4565483 : Blo 2027435 4565483 := bstep (se 1 (by rfl) ⟨3424112, by rfl⟩ : syracuseStep 4565483 = 6848225) B6848225
theorem B3043655 : Blo 2027435 3043655 := bstep (se 1 (by rfl) ⟨2282741, by rfl⟩ : syracuseStep 3043655 = 4565483) B4565483
theorem B2029103 : Blo 2027435 2029103 := bstep (se 1 (by rfl) ⟨1521827, by rfl⟩ : syracuseStep 2029103 = 3043655) B3043655
theorem B3043661 : Blo 2027435 3043661 := bbase (se 3 (by rfl) ⟨570686, by rfl⟩ : syracuseStep 3043661 = 1141373) (by norm_num)
theorem B2029107 : Blo 2027435 2029107 := bstep (se 1 (by rfl) ⟨1521830, by rfl⟩ : syracuseStep 2029107 = 3043661) B3043661
theorem B4565501 : Blo 2027435 4565501 := bbase (se 3 (by rfl) ⟨856031, by rfl⟩ : syracuseStep 4565501 = 1712063) (by norm_num)
theorem B3043667 : Blo 2027435 3043667 := bstep (se 1 (by rfl) ⟨2282750, by rfl⟩ : syracuseStep 3043667 = 4565501) B4565501
theorem B2029111 : Blo 2027435 2029111 := bstep (se 1 (by rfl) ⟨1521833, by rfl⟩ : syracuseStep 2029111 = 3043667) B3043667
theorem B3424133 : Blo 2027435 3424133 := bbase (se 4 (by rfl) ⟨321012, by rfl⟩ : syracuseStep 3424133 = 642025) (by norm_num)
theorem B2282755 : Blo 2027435 2282755 := bstep (se 1 (by rfl) ⟨1712066, by rfl⟩ : syracuseStep 2282755 = 3424133) B3424133
theorem B3043673 : Blo 2027435 3043673 := bstep (se 2 (by rfl) ⟨1141377, by rfl⟩ : syracuseStep 3043673 = 2282755) B2282755
theorem B2029115 : Blo 2027435 2029115 := bstep (se 1 (by rfl) ⟨1521836, by rfl⟩ : syracuseStep 2029115 = 3043673) B3043673
theorem B15408629 : Blo 2027435 15408629 := bbase (se 5 (by rfl) ⟨722279, by rfl⟩ : syracuseStep 15408629 = 1444559) (by norm_num)
theorem B10272419 : Blo 2027435 10272419 := bstep (se 1 (by rfl) ⟨7704314, by rfl⟩ : syracuseStep 10272419 = 15408629) B15408629
theorem B6848279 : Blo 2027435 6848279 := bstep (se 1 (by rfl) ⟨5136209, by rfl⟩ : syracuseStep 6848279 = 10272419) B10272419
theorem B4565519 : Blo 2027435 4565519 := bstep (se 1 (by rfl) ⟨3424139, by rfl⟩ : syracuseStep 4565519 = 6848279) B6848279
theorem B3043679 : Blo 2027435 3043679 := bstep (se 1 (by rfl) ⟨2282759, by rfl⟩ : syracuseStep 3043679 = 4565519) B4565519
theorem B2029119 : Blo 2027435 2029119 := bstep (se 1 (by rfl) ⟨1521839, by rfl⟩ : syracuseStep 2029119 = 3043679) B3043679
theorem B3043685 : Blo 2027435 3043685 := bbase (se 4 (by rfl) ⟨285345, by rfl⟩ : syracuseStep 3043685 = 570691) (by norm_num)
theorem B2029123 : Blo 2027435 2029123 := bstep (se 1 (by rfl) ⟨1521842, by rfl⟩ : syracuseStep 2029123 = 3043685) B3043685
theorem B3852173 : Blo 2027435 3852173 := bbase (se 3 (by rfl) ⟨722282, by rfl⟩ : syracuseStep 3852173 = 1444565) (by norm_num)
theorem B2568115 : Blo 2027435 2568115 := bstep (se 1 (by rfl) ⟨1926086, by rfl⟩ : syracuseStep 2568115 = 3852173) B3852173
theorem B3424153 : Blo 2027435 3424153 := bstep (se 2 (by rfl) ⟨1284057, by rfl⟩ : syracuseStep 3424153 = 2568115) B2568115
theorem B4565537 : Blo 2027435 4565537 := bstep (se 2 (by rfl) ⟨1712076, by rfl⟩ : syracuseStep 4565537 = 3424153) B3424153
theorem B3043691 : Blo 2027435 3043691 := bstep (se 1 (by rfl) ⟨2282768, by rfl⟩ : syracuseStep 3043691 = 4565537) B4565537
theorem B2029127 : Blo 2027435 2029127 := bstep (se 1 (by rfl) ⟨1521845, by rfl⟩ : syracuseStep 2029127 = 3043691) B3043691
theorem B2282773 : Blo 2027435 2282773 := bbase (se 6 (by rfl) ⟨53502, by rfl⟩ : syracuseStep 2282773 = 107005) (by norm_num)
theorem B3043697 : Blo 2027435 3043697 := bstep (se 2 (by rfl) ⟨1141386, by rfl⟩ : syracuseStep 3043697 = 2282773) B2282773
theorem B2029131 : Blo 2027435 2029131 := bstep (se 1 (by rfl) ⟨1521848, by rfl⟩ : syracuseStep 2029131 = 3043697) B3043697
theorem B2568125 : Blo 2027435 2568125 := bbase (se 3 (by rfl) ⟨481523, by rfl⟩ : syracuseStep 2568125 = 963047) (by norm_num)
theorem B6848333 : Blo 2027435 6848333 := bstep (se 3 (by rfl) ⟨1284062, by rfl⟩ : syracuseStep 6848333 = 2568125) B2568125
theorem B4565555 : Blo 2027435 4565555 := bstep (se 1 (by rfl) ⟨3424166, by rfl⟩ : syracuseStep 4565555 = 6848333) B6848333
theorem B3043703 : Blo 2027435 3043703 := bstep (se 1 (by rfl) ⟨2282777, by rfl⟩ : syracuseStep 3043703 = 4565555) B4565555
theorem B2029135 : Blo 2027435 2029135 := bstep (se 1 (by rfl) ⟨1521851, by rfl⟩ : syracuseStep 2029135 = 3043703) B3043703
theorem B3043709 : Blo 2027435 3043709 := bbase (se 3 (by rfl) ⟨570695, by rfl⟩ : syracuseStep 3043709 = 1141391) (by norm_num)
theorem B2029139 : Blo 2027435 2029139 := bstep (se 1 (by rfl) ⟨1521854, by rfl⟩ : syracuseStep 2029139 = 3043709) B3043709
theorem B4565573 : Blo 2027435 4565573 := bbase (se 4 (by rfl) ⟨428022, by rfl⟩ : syracuseStep 4565573 = 856045) (by norm_num)
theorem B3043715 : Blo 2027435 3043715 := bstep (se 1 (by rfl) ⟨2282786, by rfl⟩ : syracuseStep 3043715 = 4565573) B4565573
theorem B2029143 : Blo 2027435 2029143 := bstep (se 1 (by rfl) ⟨1521857, by rfl⟩ : syracuseStep 2029143 = 3043715) B3043715
theorem B2166869 : Blo 2027435 2166869 := bbase (se 8 (by rfl) ⟨12696, by rfl⟩ : syracuseStep 2166869 = 25393) (by norm_num)
theorem B5778317 : Blo 2027435 5778317 := bstep (se 3 (by rfl) ⟨1083434, by rfl⟩ : syracuseStep 5778317 = 2166869) B2166869
theorem B3852211 : Blo 2027435 3852211 := bstep (se 1 (by rfl) ⟨2889158, by rfl⟩ : syracuseStep 3852211 = 5778317) B5778317
theorem B5136281 : Blo 2027435 5136281 := bstep (se 2 (by rfl) ⟨1926105, by rfl⟩ : syracuseStep 5136281 = 3852211) B3852211
theorem B3424187 : Blo 2027435 3424187 := bstep (se 1 (by rfl) ⟨2568140, by rfl⟩ : syracuseStep 3424187 = 5136281) B5136281
theorem B2282791 : Blo 2027435 2282791 := bstep (se 1 (by rfl) ⟨1712093, by rfl⟩ : syracuseStep 2282791 = 3424187) B3424187
theorem B3043721 : Blo 2027435 3043721 := bstep (se 2 (by rfl) ⟨1141395, by rfl⟩ : syracuseStep 3043721 = 2282791) B2282791
theorem B2029147 : Blo 2027435 2029147 := bstep (se 1 (by rfl) ⟨1521860, by rfl⟩ : syracuseStep 2029147 = 3043721) B3043721
theorem B10272581 : Blo 2027435 10272581 := bbase (se 4 (by rfl) ⟨963054, by rfl⟩ : syracuseStep 10272581 = 1926109) (by norm_num)
theorem B6848387 : Blo 2027435 6848387 := bstep (se 1 (by rfl) ⟨5136290, by rfl⟩ : syracuseStep 6848387 = 10272581) B10272581
theorem B4565591 : Blo 2027435 4565591 := bstep (se 1 (by rfl) ⟨3424193, by rfl⟩ : syracuseStep 4565591 = 6848387) B6848387
theorem B3043727 : Blo 2027435 3043727 := bstep (se 1 (by rfl) ⟨2282795, by rfl⟩ : syracuseStep 3043727 = 4565591) B4565591
theorem B2029151 : Blo 2027435 2029151 := bstep (se 1 (by rfl) ⟨1521863, by rfl⟩ : syracuseStep 2029151 = 3043727) B3043727
theorem B3043733 : Blo 2027435 3043733 := bbase (se 6 (by rfl) ⟨71337, by rfl⟩ : syracuseStep 3043733 = 142675) (by norm_num)
theorem B2029155 : Blo 2027435 2029155 := bstep (se 1 (by rfl) ⟨1521866, by rfl⟩ : syracuseStep 2029155 = 3043733) B3043733
theorem B6500645 : Blo 2027435 6500645 := bbase (se 4 (by rfl) ⟨609435, by rfl⟩ : syracuseStep 6500645 = 1218871) (by norm_num)
theorem B4333763 : Blo 2027435 4333763 := bstep (se 1 (by rfl) ⟨3250322, by rfl⟩ : syracuseStep 4333763 = 6500645) B6500645
theorem B11556701 : Blo 2027435 11556701 := bstep (se 3 (by rfl) ⟨2166881, by rfl⟩ : syracuseStep 11556701 = 4333763) B4333763
theorem B7704467 : Blo 2027435 7704467 := bstep (se 1 (by rfl) ⟨5778350, by rfl⟩ : syracuseStep 7704467 = 11556701) B11556701
theorem B5136311 : Blo 2027435 5136311 := bstep (se 1 (by rfl) ⟨3852233, by rfl⟩ : syracuseStep 5136311 = 7704467) B7704467
theorem B3424207 : Blo 2027435 3424207 := bstep (se 1 (by rfl) ⟨2568155, by rfl⟩ : syracuseStep 3424207 = 5136311) B5136311
theorem B4565609 : Blo 2027435 4565609 := bstep (se 2 (by rfl) ⟨1712103, by rfl⟩ : syracuseStep 4565609 = 3424207) B3424207
theorem B3043739 : Blo 2027435 3043739 := bstep (se 1 (by rfl) ⟨2282804, by rfl⟩ : syracuseStep 3043739 = 4565609) B4565609
theorem B2029159 : Blo 2027435 2029159 := bstep (se 1 (by rfl) ⟨1521869, by rfl⟩ : syracuseStep 2029159 = 3043739) B3043739
theorem B2282809 : Blo 2027435 2282809 := bbase (se 2 (by rfl) ⟨856053, by rfl⟩ : syracuseStep 2282809 = 1712107) (by norm_num)
theorem B3043745 : Blo 2027435 3043745 := bstep (se 2 (by rfl) ⟨1141404, by rfl⟩ : syracuseStep 3043745 = 2282809) B2282809
theorem B2029163 : Blo 2027435 2029163 := bstep (se 1 (by rfl) ⟨1521872, by rfl⟩ : syracuseStep 2029163 = 3043745) B3043745
theorem B5778373 : Blo 2027435 5778373 := bbase (se 4 (by rfl) ⟨541722, by rfl⟩ : syracuseStep 5778373 = 1083445) (by norm_num)
theorem B7704497 : Blo 2027435 7704497 := bstep (se 2 (by rfl) ⟨2889186, by rfl⟩ : syracuseStep 7704497 = 5778373) B5778373
theorem B5136331 : Blo 2027435 5136331 := bstep (se 1 (by rfl) ⟨3852248, by rfl⟩ : syracuseStep 5136331 = 7704497) B7704497
theorem B6848441 : Blo 2027435 6848441 := bstep (se 2 (by rfl) ⟨2568165, by rfl⟩ : syracuseStep 6848441 = 5136331) B5136331
theorem B4565627 : Blo 2027435 4565627 := bstep (se 1 (by rfl) ⟨3424220, by rfl⟩ : syracuseStep 4565627 = 6848441) B6848441
theorem B3043751 : Blo 2027435 3043751 := bstep (se 1 (by rfl) ⟨2282813, by rfl⟩ : syracuseStep 3043751 = 4565627) B4565627
theorem B2029167 : Blo 2027435 2029167 := bstep (se 1 (by rfl) ⟨1521875, by rfl⟩ : syracuseStep 2029167 = 3043751) B3043751
theorem B3043757 : Blo 2027435 3043757 := bbase (se 3 (by rfl) ⟨570704, by rfl⟩ : syracuseStep 3043757 = 1141409) (by norm_num)
theorem B2029171 : Blo 2027435 2029171 := bstep (se 1 (by rfl) ⟨1521878, by rfl⟩ : syracuseStep 2029171 = 3043757) B3043757
theorem B4565645 : Blo 2027435 4565645 := bbase (se 3 (by rfl) ⟨856058, by rfl⟩ : syracuseStep 4565645 = 1712117) (by norm_num)
theorem B3043763 : Blo 2027435 3043763 := bstep (se 1 (by rfl) ⟨2282822, by rfl⟩ : syracuseStep 3043763 = 4565645) B4565645
theorem B2029175 : Blo 2027435 2029175 := bstep (se 1 (by rfl) ⟨1521881, by rfl⟩ : syracuseStep 2029175 = 3043763) B3043763
theorem B2568181 : Blo 2027435 2568181 := bbase (se 5 (by rfl) ⟨120383, by rfl⟩ : syracuseStep 2568181 = 240767) (by norm_num)
theorem B3424241 : Blo 2027435 3424241 := bstep (se 2 (by rfl) ⟨1284090, by rfl⟩ : syracuseStep 3424241 = 2568181) B2568181
theorem B2282827 : Blo 2027435 2282827 := bstep (se 1 (by rfl) ⟨1712120, by rfl⟩ : syracuseStep 2282827 = 3424241) B3424241
theorem B3043769 : Blo 2027435 3043769 := bstep (se 2 (by rfl) ⟨1141413, by rfl⟩ : syracuseStep 3043769 = 2282827) B2282827
theorem B2029179 : Blo 2027435 2029179 := bstep (se 1 (by rfl) ⟨1521884, by rfl⟩ : syracuseStep 2029179 = 3043769) B3043769
theorem B15619349 : Blo 2027435 15619349 := bbase (se 6 (by rfl) ⟨366078, by rfl⟩ : syracuseStep 15619349 = 732157) (by norm_num)
theorem B41651597 : Blo 2027435 41651597 := bstep (se 3 (by rfl) ⟨7809674, by rfl⟩ : syracuseStep 41651597 = 15619349) B15619349
theorem B27767731 : Blo 2027435 27767731 := bstep (se 1 (by rfl) ⟨20825798, by rfl⟩ : syracuseStep 27767731 = 41651597) B41651597
theorem B37023641 : Blo 2027435 37023641 := bstep (se 2 (by rfl) ⟨13883865, by rfl⟩ : syracuseStep 37023641 = 27767731) B27767731
theorem B24682427 : Blo 2027435 24682427 := bstep (se 1 (by rfl) ⟨18511820, by rfl⟩ : syracuseStep 24682427 = 37023641) B37023641
theorem B16454951 : Blo 2027435 16454951 := bstep (se 1 (by rfl) ⟨12341213, by rfl⟩ : syracuseStep 16454951 = 24682427) B24682427
theorem B10969967 : Blo 2027435 10969967 := bstep (se 1 (by rfl) ⟨8227475, by rfl⟩ : syracuseStep 10969967 = 16454951) B16454951
theorem B7313311 : Blo 2027435 7313311 := bstep (se 1 (by rfl) ⟨5484983, by rfl⟩ : syracuseStep 7313311 = 10969967) B10969967
theorem B39004325 : Blo 2027435 39004325 := bstep (se 4 (by rfl) ⟨3656655, by rfl⟩ : syracuseStep 39004325 = 7313311) B7313311
theorem B26002883 : Blo 2027435 26002883 := bstep (se 1 (by rfl) ⟨19502162, by rfl⟩ : syracuseStep 26002883 = 39004325) B39004325
theorem B17335255 : Blo 2027435 17335255 := bstep (se 1 (by rfl) ⟨13001441, by rfl⟩ : syracuseStep 17335255 = 26002883) B26002883
theorem B23113673 : Blo 2027435 23113673 := bstep (se 2 (by rfl) ⟨8667627, by rfl⟩ : syracuseStep 23113673 = 17335255) B17335255
theorem B15409115 : Blo 2027435 15409115 := bstep (se 1 (by rfl) ⟨11556836, by rfl⟩ : syracuseStep 15409115 = 23113673) B23113673
theorem B10272743 : Blo 2027435 10272743 := bstep (se 1 (by rfl) ⟨7704557, by rfl⟩ : syracuseStep 10272743 = 15409115) B15409115
theorem B6848495 : Blo 2027435 6848495 := bstep (se 1 (by rfl) ⟨5136371, by rfl⟩ : syracuseStep 6848495 = 10272743) B10272743
theorem B4565663 : Blo 2027435 4565663 := bstep (se 1 (by rfl) ⟨3424247, by rfl⟩ : syracuseStep 4565663 = 6848495) B6848495
theorem B3043775 : Blo 2027435 3043775 := bstep (se 1 (by rfl) ⟨2282831, by rfl⟩ : syracuseStep 3043775 = 4565663) B4565663
theorem B2029183 : Blo 2027435 2029183 := bstep (se 1 (by rfl) ⟨1521887, by rfl⟩ : syracuseStep 2029183 = 3043775) B3043775
theorem B3043781 : Blo 2027435 3043781 := bbase (se 4 (by rfl) ⟨285354, by rfl⟩ : syracuseStep 3043781 = 570709) (by norm_num)
theorem B2029187 : Blo 2027435 2029187 := bstep (se 1 (by rfl) ⟨1521890, by rfl⟩ : syracuseStep 2029187 = 3043781) B3043781
theorem B3424261 : Blo 2027435 3424261 := bbase (se 4 (by rfl) ⟨321024, by rfl⟩ : syracuseStep 3424261 = 642049) (by norm_num)
theorem B4565681 : Blo 2027435 4565681 := bstep (se 2 (by rfl) ⟨1712130, by rfl⟩ : syracuseStep 4565681 = 3424261) B3424261
theorem B3043787 : Blo 2027435 3043787 := bstep (se 1 (by rfl) ⟨2282840, by rfl⟩ : syracuseStep 3043787 = 4565681) B4565681
theorem B2029191 : Blo 2027435 2029191 := bstep (se 1 (by rfl) ⟨1521893, by rfl⟩ : syracuseStep 2029191 = 3043787) B3043787
theorem B2282845 : Blo 2027435 2282845 := bbase (se 3 (by rfl) ⟨428033, by rfl⟩ : syracuseStep 2282845 = 856067) (by norm_num)
theorem B3043793 : Blo 2027435 3043793 := bstep (se 2 (by rfl) ⟨1141422, by rfl⟩ : syracuseStep 3043793 = 2282845) B2282845
theorem B2029195 : Blo 2027435 2029195 := bstep (se 1 (by rfl) ⟨1521896, by rfl⟩ : syracuseStep 2029195 = 3043793) B3043793
theorem B6848549 : Blo 2027435 6848549 := bbase (se 4 (by rfl) ⟨642051, by rfl⟩ : syracuseStep 6848549 = 1284103) (by norm_num)
theorem B4565699 : Blo 2027435 4565699 := bstep (se 1 (by rfl) ⟨3424274, by rfl⟩ : syracuseStep 4565699 = 6848549) B6848549
theorem B3043799 : Blo 2027435 3043799 := bstep (se 1 (by rfl) ⟨2282849, by rfl⟩ : syracuseStep 3043799 = 4565699) B4565699
theorem B2029199 : Blo 2027435 2029199 := bstep (se 1 (by rfl) ⟨1521899, by rfl⟩ : syracuseStep 2029199 = 3043799) B3043799
theorem B3043805 : Blo 2027435 3043805 := bbase (se 3 (by rfl) ⟨570713, by rfl⟩ : syracuseStep 3043805 = 1141427) (by norm_num)
theorem B2029203 : Blo 2027435 2029203 := bstep (se 1 (by rfl) ⟨1521902, by rfl⟩ : syracuseStep 2029203 = 3043805) B3043805
theorem B4565717 : Blo 2027435 4565717 := bbase (se 7 (by rfl) ⟨53504, by rfl⟩ : syracuseStep 4565717 = 107009) (by norm_num)
theorem B3043811 : Blo 2027435 3043811 := bstep (se 1 (by rfl) ⟨2282858, by rfl⟩ : syracuseStep 3043811 = 4565717) B4565717
theorem B2029207 : Blo 2027435 2029207 := bstep (se 1 (by rfl) ⟨1521905, by rfl⟩ : syracuseStep 2029207 = 3043811) B3043811
theorem B8667749 : Blo 2027435 8667749 := bbase (se 4 (by rfl) ⟨812601, by rfl⟩ : syracuseStep 8667749 = 1625203) (by norm_num)
theorem B5778499 : Blo 2027435 5778499 := bstep (se 1 (by rfl) ⟨4333874, by rfl⟩ : syracuseStep 5778499 = 8667749) B8667749
theorem B7704665 : Blo 2027435 7704665 := bstep (se 2 (by rfl) ⟨2889249, by rfl⟩ : syracuseStep 7704665 = 5778499) B5778499
theorem B5136443 : Blo 2027435 5136443 := bstep (se 1 (by rfl) ⟨3852332, by rfl⟩ : syracuseStep 5136443 = 7704665) B7704665
theorem B3424295 : Blo 2027435 3424295 := bstep (se 1 (by rfl) ⟨2568221, by rfl⟩ : syracuseStep 3424295 = 5136443) B5136443
theorem B2282863 : Blo 2027435 2282863 := bstep (se 1 (by rfl) ⟨1712147, by rfl⟩ : syracuseStep 2282863 = 3424295) B3424295
theorem B3043817 : Blo 2027435 3043817 := bstep (se 2 (by rfl) ⟨1141431, by rfl⟩ : syracuseStep 3043817 = 2282863) B2282863
theorem B2029211 : Blo 2027435 2029211 := bstep (se 1 (by rfl) ⟨1521908, by rfl⟩ : syracuseStep 2029211 = 3043817) B3043817
theorem B32910421 : Blo 2027435 32910421 := bbase (se 8 (by rfl) ⟨192834, by rfl⟩ : syracuseStep 32910421 = 385669) (by norm_num)
theorem B43880561 : Blo 2027435 43880561 := bstep (se 2 (by rfl) ⟨16455210, by rfl⟩ : syracuseStep 43880561 = 32910421) B32910421
theorem B29253707 : Blo 2027435 29253707 := bstep (se 1 (by rfl) ⟨21940280, by rfl⟩ : syracuseStep 29253707 = 43880561) B43880561
theorem B19502471 : Blo 2027435 19502471 := bstep (se 1 (by rfl) ⟨14626853, by rfl⟩ : syracuseStep 19502471 = 29253707) B29253707
theorem B13001647 : Blo 2027435 13001647 := bstep (se 1 (by rfl) ⟨9751235, by rfl⟩ : syracuseStep 13001647 = 19502471) B19502471
theorem B17335529 : Blo 2027435 17335529 := bstep (se 2 (by rfl) ⟨6500823, by rfl⟩ : syracuseStep 17335529 = 13001647) B13001647
theorem B11557019 : Blo 2027435 11557019 := bstep (se 1 (by rfl) ⟨8667764, by rfl⟩ : syracuseStep 11557019 = 17335529) B17335529
theorem B7704679 : Blo 2027435 7704679 := bstep (se 1 (by rfl) ⟨5778509, by rfl⟩ : syracuseStep 7704679 = 11557019) B11557019
theorem B10272905 : Blo 2027435 10272905 := bstep (se 2 (by rfl) ⟨3852339, by rfl⟩ : syracuseStep 10272905 = 7704679) B7704679
theorem B6848603 : Blo 2027435 6848603 := bstep (se 1 (by rfl) ⟨5136452, by rfl⟩ : syracuseStep 6848603 = 10272905) B10272905
theorem B4565735 : Blo 2027435 4565735 := bstep (se 1 (by rfl) ⟨3424301, by rfl⟩ : syracuseStep 4565735 = 6848603) B6848603
theorem B3043823 : Blo 2027435 3043823 := bstep (se 1 (by rfl) ⟨2282867, by rfl⟩ : syracuseStep 3043823 = 4565735) B4565735
theorem B2029215 : Blo 2027435 2029215 := bstep (se 1 (by rfl) ⟨1521911, by rfl⟩ : syracuseStep 2029215 = 3043823) B3043823
theorem B3043829 : Blo 2027435 3043829 := bbase (se 5 (by rfl) ⟨142679, by rfl⟩ : syracuseStep 3043829 = 285359) (by norm_num)
theorem B2029219 : Blo 2027435 2029219 := bstep (se 1 (by rfl) ⟨1521914, by rfl⟩ : syracuseStep 2029219 = 3043829) B3043829
theorem B5778533 : Blo 2027435 5778533 := bbase (se 4 (by rfl) ⟨541737, by rfl⟩ : syracuseStep 5778533 = 1083475) (by norm_num)
theorem B3852355 : Blo 2027435 3852355 := bstep (se 1 (by rfl) ⟨2889266, by rfl⟩ : syracuseStep 3852355 = 5778533) B5778533
theorem B5136473 : Blo 2027435 5136473 := bstep (se 2 (by rfl) ⟨1926177, by rfl⟩ : syracuseStep 5136473 = 3852355) B3852355
theorem B3424315 : Blo 2027435 3424315 := bstep (se 1 (by rfl) ⟨2568236, by rfl⟩ : syracuseStep 3424315 = 5136473) B5136473
theorem B4565753 : Blo 2027435 4565753 := bstep (se 2 (by rfl) ⟨1712157, by rfl⟩ : syracuseStep 4565753 = 3424315) B3424315
theorem B3043835 : Blo 2027435 3043835 := bstep (se 1 (by rfl) ⟨2282876, by rfl⟩ : syracuseStep 3043835 = 4565753) B4565753
theorem B2029223 : Blo 2027435 2029223 := bstep (se 1 (by rfl) ⟨1521917, by rfl⟩ : syracuseStep 2029223 = 3043835) B3043835
theorem B2282881 : Blo 2027435 2282881 := bbase (se 2 (by rfl) ⟨856080, by rfl⟩ : syracuseStep 2282881 = 1712161) (by norm_num)
theorem B3043841 : Blo 2027435 3043841 := bstep (se 2 (by rfl) ⟨1141440, by rfl⟩ : syracuseStep 3043841 = 2282881) B2282881
theorem B2029227 : Blo 2027435 2029227 := bstep (se 1 (by rfl) ⟨1521920, by rfl⟩ : syracuseStep 2029227 = 3043841) B3043841
theorem B5136493 : Blo 2027435 5136493 := bbase (se 3 (by rfl) ⟨963092, by rfl⟩ : syracuseStep 5136493 = 1926185) (by norm_num)
theorem B6848657 : Blo 2027435 6848657 := bstep (se 2 (by rfl) ⟨2568246, by rfl⟩ : syracuseStep 6848657 = 5136493) B5136493
theorem B4565771 : Blo 2027435 4565771 := bstep (se 1 (by rfl) ⟨3424328, by rfl⟩ : syracuseStep 4565771 = 6848657) B6848657
theorem B3043847 : Blo 2027435 3043847 := bstep (se 1 (by rfl) ⟨2282885, by rfl⟩ : syracuseStep 3043847 = 4565771) B4565771
theorem B2029231 : Blo 2027435 2029231 := bstep (se 1 (by rfl) ⟨1521923, by rfl⟩ : syracuseStep 2029231 = 3043847) B3043847
theorem B3043853 : Blo 2027435 3043853 := bbase (se 3 (by rfl) ⟨570722, by rfl⟩ : syracuseStep 3043853 = 1141445) (by norm_num)
theorem B2029235 : Blo 2027435 2029235 := bstep (se 1 (by rfl) ⟨1521926, by rfl⟩ : syracuseStep 2029235 = 3043853) B3043853
theorem B4565789 : Blo 2027435 4565789 := bbase (se 3 (by rfl) ⟨856085, by rfl⟩ : syracuseStep 4565789 = 1712171) (by norm_num)
theorem B3043859 : Blo 2027435 3043859 := bstep (se 1 (by rfl) ⟨2282894, by rfl⟩ : syracuseStep 3043859 = 4565789) B4565789
theorem B2029239 : Blo 2027435 2029239 := bstep (se 1 (by rfl) ⟨1521929, by rfl⟩ : syracuseStep 2029239 = 3043859) B3043859
theorem B3424349 : Blo 2027435 3424349 := bbase (se 3 (by rfl) ⟨642065, by rfl⟩ : syracuseStep 3424349 = 1284131) (by norm_num)
theorem B2282899 : Blo 2027435 2282899 := bstep (se 1 (by rfl) ⟨1712174, by rfl⟩ : syracuseStep 2282899 = 3424349) B3424349
theorem B3043865 : Blo 2027435 3043865 := bstep (se 2 (by rfl) ⟨1141449, by rfl⟩ : syracuseStep 3043865 = 2282899) B2282899
theorem B2029243 : Blo 2027435 2029243 := bstep (se 1 (by rfl) ⟨1521932, by rfl⟩ : syracuseStep 2029243 = 3043865) B3043865
theorem B3471077 : Blo 2027435 3471077 := bbase (se 4 (by rfl) ⟨325413, by rfl⟩ : syracuseStep 3471077 = 650827) (by norm_num)
theorem B2314051 : Blo 2027435 2314051 := bstep (se 1 (by rfl) ⟨1735538, by rfl⟩ : syracuseStep 2314051 = 3471077) B3471077
theorem B12341605 : Blo 2027435 12341605 := bstep (se 4 (by rfl) ⟨1157025, by rfl⟩ : syracuseStep 12341605 = 2314051) B2314051
theorem B16455473 : Blo 2027435 16455473 := bstep (se 2 (by rfl) ⟨6170802, by rfl⟩ : syracuseStep 16455473 = 12341605) B12341605
theorem B10970315 : Blo 2027435 10970315 := bstep (se 1 (by rfl) ⟨8227736, by rfl⟩ : syracuseStep 10970315 = 16455473) B16455473
theorem B7313543 : Blo 2027435 7313543 := bstep (se 1 (by rfl) ⟨5485157, by rfl⟩ : syracuseStep 7313543 = 10970315) B10970315
theorem B4875695 : Blo 2027435 4875695 := bstep (se 1 (by rfl) ⟨3656771, by rfl⟩ : syracuseStep 4875695 = 7313543) B7313543
theorem B3250463 : Blo 2027435 3250463 := bstep (se 1 (by rfl) ⟨2437847, by rfl⟩ : syracuseStep 3250463 = 4875695) B4875695
theorem B8667901 : Blo 2027435 8667901 := bstep (se 3 (by rfl) ⟨1625231, by rfl⟩ : syracuseStep 8667901 = 3250463) B3250463
theorem B11557201 : Blo 2027435 11557201 := bstep (se 2 (by rfl) ⟨4333950, by rfl⟩ : syracuseStep 11557201 = 8667901) B8667901
theorem B15409601 : Blo 2027435 15409601 := bstep (se 2 (by rfl) ⟨5778600, by rfl⟩ : syracuseStep 15409601 = 11557201) B11557201
theorem B10273067 : Blo 2027435 10273067 := bstep (se 1 (by rfl) ⟨7704800, by rfl⟩ : syracuseStep 10273067 = 15409601) B15409601
theorem B6848711 : Blo 2027435 6848711 := bstep (se 1 (by rfl) ⟨5136533, by rfl⟩ : syracuseStep 6848711 = 10273067) B10273067
theorem B4565807 : Blo 2027435 4565807 := bstep (se 1 (by rfl) ⟨3424355, by rfl⟩ : syracuseStep 4565807 = 6848711) B6848711
theorem B3043871 : Blo 2027435 3043871 := bstep (se 1 (by rfl) ⟨2282903, by rfl⟩ : syracuseStep 3043871 = 4565807) B4565807
theorem B2029247 : Blo 2027435 2029247 := bstep (se 1 (by rfl) ⟨1521935, by rfl⟩ : syracuseStep 2029247 = 3043871) B3043871
theorem B3043877 : Blo 2027435 3043877 := bbase (se 4 (by rfl) ⟨285363, by rfl⟩ : syracuseStep 3043877 = 570727) (by norm_num)
theorem B2029251 : Blo 2027435 2029251 := bstep (se 1 (by rfl) ⟨1521938, by rfl⟩ : syracuseStep 2029251 = 3043877) B3043877
theorem B2568277 : Blo 2027435 2568277 := bbase (se 8 (by rfl) ⟨15048, by rfl⟩ : syracuseStep 2568277 = 30097) (by norm_num)
theorem B3424369 : Blo 2027435 3424369 := bstep (se 2 (by rfl) ⟨1284138, by rfl⟩ : syracuseStep 3424369 = 2568277) B2568277
theorem B4565825 : Blo 2027435 4565825 := bstep (se 2 (by rfl) ⟨1712184, by rfl⟩ : syracuseStep 4565825 = 3424369) B3424369
theorem B3043883 : Blo 2027435 3043883 := bstep (se 1 (by rfl) ⟨2282912, by rfl⟩ : syracuseStep 3043883 = 4565825) B4565825
theorem B2029255 : Blo 2027435 2029255 := bstep (se 1 (by rfl) ⟨1521941, by rfl⟩ : syracuseStep 2029255 = 3043883) B3043883
theorem B2282917 : Blo 2027435 2282917 := bbase (se 4 (by rfl) ⟨214023, by rfl⟩ : syracuseStep 2282917 = 428047) (by norm_num)
theorem B3043889 : Blo 2027435 3043889 := bstep (se 2 (by rfl) ⟨1141458, by rfl⟩ : syracuseStep 3043889 = 2282917) B2282917
theorem B2029259 : Blo 2027435 2029259 := bstep (se 1 (by rfl) ⟨1521944, by rfl⟩ : syracuseStep 2029259 = 3043889) B3043889
theorem B4628141 : Blo 2027435 4628141 := bbase (se 3 (by rfl) ⟨867776, by rfl⟩ : syracuseStep 4628141 = 1735553) (by norm_num)
theorem B3085427 : Blo 2027435 3085427 := bstep (se 1 (by rfl) ⟨2314070, by rfl⟩ : syracuseStep 3085427 = 4628141) B4628141
theorem B2056951 : Blo 2027435 2056951 := bstep (se 1 (by rfl) ⟨1542713, by rfl⟩ : syracuseStep 2056951 = 3085427) B3085427
theorem B2742601 : Blo 2027435 2742601 := bstep (se 2 (by rfl) ⟨1028475, by rfl⟩ : syracuseStep 2742601 = 2056951) B2056951
theorem B3656801 : Blo 2027435 3656801 := bstep (se 2 (by rfl) ⟨1371300, by rfl⟩ : syracuseStep 3656801 = 2742601) B2742601
theorem B2437867 : Blo 2027435 2437867 := bstep (se 1 (by rfl) ⟨1828400, by rfl⟩ : syracuseStep 2437867 = 3656801) B3656801
theorem B13001957 : Blo 2027435 13001957 := bstep (se 4 (by rfl) ⟨1218933, by rfl⟩ : syracuseStep 13001957 = 2437867) B2437867
theorem B8667971 : Blo 2027435 8667971 := bstep (se 1 (by rfl) ⟨6500978, by rfl⟩ : syracuseStep 8667971 = 13001957) B13001957
theorem B5778647 : Blo 2027435 5778647 := bstep (se 1 (by rfl) ⟨4333985, by rfl⟩ : syracuseStep 5778647 = 8667971) B8667971
theorem B3852431 : Blo 2027435 3852431 := bstep (se 1 (by rfl) ⟨2889323, by rfl⟩ : syracuseStep 3852431 = 5778647) B5778647
theorem B2568287 : Blo 2027435 2568287 := bstep (se 1 (by rfl) ⟨1926215, by rfl⟩ : syracuseStep 2568287 = 3852431) B3852431
theorem B6848765 : Blo 2027435 6848765 := bstep (se 3 (by rfl) ⟨1284143, by rfl⟩ : syracuseStep 6848765 = 2568287) B2568287
theorem B4565843 : Blo 2027435 4565843 := bstep (se 1 (by rfl) ⟨3424382, by rfl⟩ : syracuseStep 4565843 = 6848765) B6848765
theorem B3043895 : Blo 2027435 3043895 := bstep (se 1 (by rfl) ⟨2282921, by rfl⟩ : syracuseStep 3043895 = 4565843) B4565843
theorem B2029263 : Blo 2027435 2029263 := bstep (se 1 (by rfl) ⟨1521947, by rfl⟩ : syracuseStep 2029263 = 3043895) B3043895
theorem B3043901 : Blo 2027435 3043901 := bbase (se 3 (by rfl) ⟨570731, by rfl⟩ : syracuseStep 3043901 = 1141463) (by norm_num)
theorem B2029267 : Blo 2027435 2029267 := bstep (se 1 (by rfl) ⟨1521950, by rfl⟩ : syracuseStep 2029267 = 3043901) B3043901
theorem B4565861 : Blo 2027435 4565861 := bbase (se 4 (by rfl) ⟨428049, by rfl⟩ : syracuseStep 4565861 = 856099) (by norm_num)
theorem B3043907 : Blo 2027435 3043907 := bstep (se 1 (by rfl) ⟨2282930, by rfl⟩ : syracuseStep 3043907 = 4565861) B4565861
theorem B2029271 : Blo 2027435 2029271 := bstep (se 1 (by rfl) ⟨1521953, by rfl⟩ : syracuseStep 2029271 = 3043907) B3043907
theorem B5136605 : Blo 2027435 5136605 := bbase (se 3 (by rfl) ⟨963113, by rfl⟩ : syracuseStep 5136605 = 1926227) (by norm_num)
theorem B3424403 : Blo 2027435 3424403 := bstep (se 1 (by rfl) ⟨2568302, by rfl⟩ : syracuseStep 3424403 = 5136605) B5136605
theorem B2282935 : Blo 2027435 2282935 := bstep (se 1 (by rfl) ⟨1712201, by rfl⟩ : syracuseStep 2282935 = 3424403) B3424403
theorem B3043913 : Blo 2027435 3043913 := bstep (se 2 (by rfl) ⟨1141467, by rfl⟩ : syracuseStep 3043913 = 2282935) B2282935
theorem B2029275 : Blo 2027435 2029275 := bstep (se 1 (by rfl) ⟨1521956, by rfl⟩ : syracuseStep 2029275 = 3043913) B3043913
theorem B3852461 : Blo 2027435 3852461 := bbase (se 3 (by rfl) ⟨722336, by rfl⟩ : syracuseStep 3852461 = 1444673) (by norm_num)
theorem B10273229 : Blo 2027435 10273229 := bstep (se 3 (by rfl) ⟨1926230, by rfl⟩ : syracuseStep 10273229 = 3852461) B3852461
theorem B6848819 : Blo 2027435 6848819 := bstep (se 1 (by rfl) ⟨5136614, by rfl⟩ : syracuseStep 6848819 = 10273229) B10273229
theorem B4565879 : Blo 2027435 4565879 := bstep (se 1 (by rfl) ⟨3424409, by rfl⟩ : syracuseStep 4565879 = 6848819) B6848819
theorem B3043919 : Blo 2027435 3043919 := bstep (se 1 (by rfl) ⟨2282939, by rfl⟩ : syracuseStep 3043919 = 4565879) B4565879
theorem B2029279 : Blo 2027435 2029279 := bstep (se 1 (by rfl) ⟨1521959, by rfl⟩ : syracuseStep 2029279 = 3043919) B3043919
theorem B3043925 : Blo 2027435 3043925 := bbase (se 8 (by rfl) ⟨17835, by rfl⟩ : syracuseStep 3043925 = 35671) (by norm_num)
theorem B2029283 : Blo 2027435 2029283 := bstep (se 1 (by rfl) ⟨1521962, by rfl⟩ : syracuseStep 2029283 = 3043925) B3043925
theorem B3385397 : Blo 2027435 3385397 := bbase (se 5 (by rfl) ⟨158690, by rfl⟩ : syracuseStep 3385397 = 317381) (by norm_num)
theorem B2256931 : Blo 2027435 2256931 := bstep (se 1 (by rfl) ⟨1692698, by rfl⟩ : syracuseStep 2256931 = 3385397) B3385397
theorem B3009241 : Blo 2027435 3009241 := bstep (se 2 (by rfl) ⟨1128465, by rfl⟩ : syracuseStep 3009241 = 2256931) B2256931
theorem B4012321 : Blo 2027435 4012321 := bstep (se 2 (by rfl) ⟨1504620, by rfl⟩ : syracuseStep 4012321 = 3009241) B3009241
theorem B5349761 : Blo 2027435 5349761 := bstep (se 2 (by rfl) ⟨2006160, by rfl⟩ : syracuseStep 5349761 = 4012321) B4012321
theorem B3566507 : Blo 2027435 3566507 := bstep (se 1 (by rfl) ⟨2674880, by rfl⟩ : syracuseStep 3566507 = 5349761) B5349761
theorem B9510685 : Blo 2027435 9510685 := bstep (se 3 (by rfl) ⟨1783253, by rfl⟩ : syracuseStep 9510685 = 3566507) B3566507
theorem B50723653 : Blo 2027435 50723653 := bstep (se 4 (by rfl) ⟨4755342, by rfl⟩ : syracuseStep 50723653 = 9510685) B9510685
theorem B67631537 : Blo 2027435 67631537 := bstep (se 2 (by rfl) ⟨25361826, by rfl⟩ : syracuseStep 67631537 = 50723653) B50723653
theorem B45087691 : Blo 2027435 45087691 := bstep (se 1 (by rfl) ⟨33815768, by rfl⟩ : syracuseStep 45087691 = 67631537) B67631537
theorem B60116921 : Blo 2027435 60116921 := bstep (se 2 (by rfl) ⟨22543845, by rfl⟩ : syracuseStep 60116921 = 45087691) B45087691
theorem B40077947 : Blo 2027435 40077947 := bstep (se 1 (by rfl) ⟨30058460, by rfl⟩ : syracuseStep 40077947 = 60116921) B60116921
theorem B26718631 : Blo 2027435 26718631 := bstep (se 1 (by rfl) ⟨20038973, by rfl⟩ : syracuseStep 26718631 = 40077947) B40077947
theorem B569997461 : Blo 2027435 569997461 := bstep (se 6 (by rfl) ⟨13359315, by rfl⟩ : syracuseStep 569997461 = 26718631) B26718631
theorem B379998307 : Blo 2027435 379998307 := bstep (se 1 (by rfl) ⟨284998730, by rfl⟩ : syracuseStep 379998307 = 569997461) B569997461
theorem B506664409 : Blo 2027435 506664409 := bstep (se 2 (by rfl) ⟨189999153, by rfl⟩ : syracuseStep 506664409 = 379998307) B379998307
theorem B675552545 : Blo 2027435 675552545 := bstep (se 2 (by rfl) ⟨253332204, by rfl⟩ : syracuseStep 675552545 = 506664409) B506664409
theorem B450368363 : Blo 2027435 450368363 := bstep (se 1 (by rfl) ⟨337776272, by rfl⟩ : syracuseStep 450368363 = 675552545) B675552545
theorem B300245575 : Blo 2027435 300245575 := bstep (se 1 (by rfl) ⟨225184181, by rfl⟩ : syracuseStep 300245575 = 450368363) B450368363
theorem B400327433 : Blo 2027435 400327433 := bstep (se 2 (by rfl) ⟨150122787, by rfl⟩ : syracuseStep 400327433 = 300245575) B300245575
theorem B266884955 : Blo 2027435 266884955 := bstep (se 1 (by rfl) ⟨200163716, by rfl⟩ : syracuseStep 266884955 = 400327433) B400327433
theorem B177923303 : Blo 2027435 177923303 := bstep (se 1 (by rfl) ⟨133442477, by rfl⟩ : syracuseStep 177923303 = 266884955) B266884955
theorem B118615535 : Blo 2027435 118615535 := bstep (se 1 (by rfl) ⟨88961651, by rfl⟩ : syracuseStep 118615535 = 177923303) B177923303
theorem B79077023 : Blo 2027435 79077023 := bstep (se 1 (by rfl) ⟨59307767, by rfl⟩ : syracuseStep 79077023 = 118615535) B118615535
theorem B52718015 : Blo 2027435 52718015 := bstep (se 1 (by rfl) ⟨39538511, by rfl⟩ : syracuseStep 52718015 = 79077023) B79077023
theorem B35145343 : Blo 2027435 35145343 := bstep (se 1 (by rfl) ⟨26359007, by rfl⟩ : syracuseStep 35145343 = 52718015) B52718015
theorem B46860457 : Blo 2027435 46860457 := bstep (se 2 (by rfl) ⟨17572671, by rfl⟩ : syracuseStep 46860457 = 35145343) B35145343
theorem B62480609 : Blo 2027435 62480609 := bstep (se 2 (by rfl) ⟨23430228, by rfl⟩ : syracuseStep 62480609 = 46860457) B46860457
theorem B41653739 : Blo 2027435 41653739 := bstep (se 1 (by rfl) ⟨31240304, by rfl⟩ : syracuseStep 41653739 = 62480609) B62480609
theorem B27769159 : Blo 2027435 27769159 := bstep (se 1 (by rfl) ⟨20826869, by rfl⟩ : syracuseStep 27769159 = 41653739) B41653739
theorem B37025545 : Blo 2027435 37025545 := bstep (se 2 (by rfl) ⟨13884579, by rfl⟩ : syracuseStep 37025545 = 27769159) B27769159
theorem B49367393 : Blo 2027435 49367393 := bstep (se 2 (by rfl) ⟨18512772, by rfl⟩ : syracuseStep 49367393 = 37025545) B37025545
theorem B32911595 : Blo 2027435 32911595 := bstep (se 1 (by rfl) ⟨24683696, by rfl⟩ : syracuseStep 32911595 = 49367393) B49367393
theorem B21941063 : Blo 2027435 21941063 := bstep (se 1 (by rfl) ⟨16455797, by rfl⟩ : syracuseStep 21941063 = 32911595) B32911595
theorem B14627375 : Blo 2027435 14627375 := bstep (se 1 (by rfl) ⟨10970531, by rfl⟩ : syracuseStep 14627375 = 21941063) B21941063
theorem B9751583 : Blo 2027435 9751583 := bstep (se 1 (by rfl) ⟨7313687, by rfl⟩ : syracuseStep 9751583 = 14627375) B14627375
theorem B6501055 : Blo 2027435 6501055 := bstep (se 1 (by rfl) ⟨4875791, by rfl⟩ : syracuseStep 6501055 = 9751583) B9751583
theorem B8668073 : Blo 2027435 8668073 := bstep (se 2 (by rfl) ⟨3250527, by rfl⟩ : syracuseStep 8668073 = 6501055) B6501055
theorem B5778715 : Blo 2027435 5778715 := bstep (se 1 (by rfl) ⟨4334036, by rfl⟩ : syracuseStep 5778715 = 8668073) B8668073
theorem B7704953 : Blo 2027435 7704953 := bstep (se 2 (by rfl) ⟨2889357, by rfl⟩ : syracuseStep 7704953 = 5778715) B5778715
theorem B5136635 : Blo 2027435 5136635 := bstep (se 1 (by rfl) ⟨3852476, by rfl⟩ : syracuseStep 5136635 = 7704953) B7704953
theorem B3424423 : Blo 2027435 3424423 := bstep (se 1 (by rfl) ⟨2568317, by rfl⟩ : syracuseStep 3424423 = 5136635) B5136635
theorem B4565897 : Blo 2027435 4565897 := bstep (se 2 (by rfl) ⟨1712211, by rfl⟩ : syracuseStep 4565897 = 3424423) B3424423
theorem B3043931 : Blo 2027435 3043931 := bstep (se 1 (by rfl) ⟨2282948, by rfl⟩ : syracuseStep 3043931 = 4565897) B4565897
theorem B2029287 : Blo 2027435 2029287 := bstep (se 1 (by rfl) ⟨1521965, by rfl⟩ : syracuseStep 2029287 = 3043931) B3043931
theorem B2282953 : Blo 2027435 2282953 := bbase (se 2 (by rfl) ⟨856107, by rfl⟩ : syracuseStep 2282953 = 1712215) (by norm_num)
theorem B3043937 : Blo 2027435 3043937 := bstep (se 2 (by rfl) ⟨1141476, by rfl⟩ : syracuseStep 3043937 = 2282953) B2282953
theorem B2029291 : Blo 2027435 2029291 := bstep (se 1 (by rfl) ⟨1521968, by rfl⟩ : syracuseStep 2029291 = 3043937) B3043937
theorem B17336213 : Blo 2027435 17336213 := bbase (se 6 (by rfl) ⟨406317, by rfl⟩ : syracuseStep 17336213 = 812635) (by norm_num)
theorem B11557475 : Blo 2027435 11557475 := bstep (se 1 (by rfl) ⟨8668106, by rfl⟩ : syracuseStep 11557475 = 17336213) B17336213
theorem B7704983 : Blo 2027435 7704983 := bstep (se 1 (by rfl) ⟨5778737, by rfl⟩ : syracuseStep 7704983 = 11557475) B11557475
theorem B5136655 : Blo 2027435 5136655 := bstep (se 1 (by rfl) ⟨3852491, by rfl⟩ : syracuseStep 5136655 = 7704983) B7704983
theorem B6848873 : Blo 2027435 6848873 := bstep (se 2 (by rfl) ⟨2568327, by rfl⟩ : syracuseStep 6848873 = 5136655) B5136655
theorem B4565915 : Blo 2027435 4565915 := bstep (se 1 (by rfl) ⟨3424436, by rfl⟩ : syracuseStep 4565915 = 6848873) B6848873
theorem B3043943 : Blo 2027435 3043943 := bstep (se 1 (by rfl) ⟨2282957, by rfl⟩ : syracuseStep 3043943 = 4565915) B4565915
theorem B2029295 : Blo 2027435 2029295 := bstep (se 1 (by rfl) ⟨1521971, by rfl⟩ : syracuseStep 2029295 = 3043943) B3043943
theorem B3043949 : Blo 2027435 3043949 := bbase (se 3 (by rfl) ⟨570740, by rfl⟩ : syracuseStep 3043949 = 1141481) (by norm_num)
theorem B2029299 : Blo 2027435 2029299 := bstep (se 1 (by rfl) ⟨1521974, by rfl⟩ : syracuseStep 2029299 = 3043949) B3043949
theorem B4565933 : Blo 2027435 4565933 := bbase (se 3 (by rfl) ⟨856112, by rfl⟩ : syracuseStep 4565933 = 1712225) (by norm_num)
theorem B3043955 : Blo 2027435 3043955 := bstep (se 1 (by rfl) ⟨2282966, by rfl⟩ : syracuseStep 3043955 = 4565933) B4565933
theorem B2029303 : Blo 2027435 2029303 := bstep (se 1 (by rfl) ⟨1521977, by rfl⟩ : syracuseStep 2029303 = 3043955) B3043955
theorem B5778773 : Blo 2027435 5778773 := bbase (se 11 (by rfl) ⟨4232, by rfl⟩ : syracuseStep 5778773 = 8465) (by norm_num)
theorem B3852515 : Blo 2027435 3852515 := bstep (se 1 (by rfl) ⟨2889386, by rfl⟩ : syracuseStep 3852515 = 5778773) B5778773
theorem B2568343 : Blo 2027435 2568343 := bstep (se 1 (by rfl) ⟨1926257, by rfl⟩ : syracuseStep 2568343 = 3852515) B3852515
theorem B3424457 : Blo 2027435 3424457 := bstep (se 2 (by rfl) ⟨1284171, by rfl⟩ : syracuseStep 3424457 = 2568343) B2568343
theorem B2282971 : Blo 2027435 2282971 := bstep (se 1 (by rfl) ⟨1712228, by rfl⟩ : syracuseStep 2282971 = 3424457) B3424457
theorem B3043961 : Blo 2027435 3043961 := bstep (se 2 (by rfl) ⟨1141485, by rfl⟩ : syracuseStep 3043961 = 2282971) B2282971
theorem B2029307 : Blo 2027435 2029307 := bstep (se 1 (by rfl) ⟨1521980, by rfl⟩ : syracuseStep 2029307 = 3043961) B3043961
theorem B4113997 : Blo 2027435 4113997 := bbase (se 3 (by rfl) ⟨771374, by rfl⟩ : syracuseStep 4113997 = 1542749) (by norm_num)
theorem B21941317 : Blo 2027435 21941317 := bstep (se 4 (by rfl) ⟨2056998, by rfl⟩ : syracuseStep 21941317 = 4113997) B4113997
theorem B29255089 : Blo 2027435 29255089 := bstep (se 2 (by rfl) ⟨10970658, by rfl⟩ : syracuseStep 29255089 = 21941317) B21941317
theorem B39006785 : Blo 2027435 39006785 := bstep (se 2 (by rfl) ⟨14627544, by rfl⟩ : syracuseStep 39006785 = 29255089) B29255089
theorem B26004523 : Blo 2027435 26004523 := bstep (se 1 (by rfl) ⟨19503392, by rfl⟩ : syracuseStep 26004523 = 39006785) B39006785
theorem B34672697 : Blo 2027435 34672697 := bstep (se 2 (by rfl) ⟨13002261, by rfl⟩ : syracuseStep 34672697 = 26004523) B26004523
theorem B23115131 : Blo 2027435 23115131 := bstep (se 1 (by rfl) ⟨17336348, by rfl⟩ : syracuseStep 23115131 = 34672697) B34672697
theorem B15410087 : Blo 2027435 15410087 := bstep (se 1 (by rfl) ⟨11557565, by rfl⟩ : syracuseStep 15410087 = 23115131) B23115131
theorem B10273391 : Blo 2027435 10273391 := bstep (se 1 (by rfl) ⟨7705043, by rfl⟩ : syracuseStep 10273391 = 15410087) B15410087
theorem B6848927 : Blo 2027435 6848927 := bstep (se 1 (by rfl) ⟨5136695, by rfl⟩ : syracuseStep 6848927 = 10273391) B10273391
theorem B4565951 : Blo 2027435 4565951 := bstep (se 1 (by rfl) ⟨3424463, by rfl⟩ : syracuseStep 4565951 = 6848927) B6848927
theorem B3043967 : Blo 2027435 3043967 := bstep (se 1 (by rfl) ⟨2282975, by rfl⟩ : syracuseStep 3043967 = 4565951) B4565951
theorem B2029311 : Blo 2027435 2029311 := bstep (se 1 (by rfl) ⟨1521983, by rfl⟩ : syracuseStep 2029311 = 3043967) B3043967
theorem B3043973 : Blo 2027435 3043973 := bbase (se 4 (by rfl) ⟨285372, by rfl⟩ : syracuseStep 3043973 = 570745) (by norm_num)
theorem B2029315 : Blo 2027435 2029315 := bstep (se 1 (by rfl) ⟨1521986, by rfl⟩ : syracuseStep 2029315 = 3043973) B3043973
theorem B3424477 : Blo 2027435 3424477 := bbase (se 3 (by rfl) ⟨642089, by rfl⟩ : syracuseStep 3424477 = 1284179) (by norm_num)
theorem B4565969 : Blo 2027435 4565969 := bstep (se 2 (by rfl) ⟨1712238, by rfl⟩ : syracuseStep 4565969 = 3424477) B3424477
theorem B3043979 : Blo 2027435 3043979 := bstep (se 1 (by rfl) ⟨2282984, by rfl⟩ : syracuseStep 3043979 = 4565969) B4565969
theorem B2029319 : Blo 2027435 2029319 := bstep (se 1 (by rfl) ⟨1521989, by rfl⟩ : syracuseStep 2029319 = 3043979) B3043979
theorem B2282989 : Blo 2027435 2282989 := bbase (se 3 (by rfl) ⟨428060, by rfl⟩ : syracuseStep 2282989 = 856121) (by norm_num)
theorem B3043985 : Blo 2027435 3043985 := bstep (se 2 (by rfl) ⟨1141494, by rfl⟩ : syracuseStep 3043985 = 2282989) B2282989
theorem B2029323 : Blo 2027435 2029323 := bstep (se 1 (by rfl) ⟨1521992, by rfl⟩ : syracuseStep 2029323 = 3043985) B3043985
theorem B6848981 : Blo 2027435 6848981 := bbase (se 7 (by rfl) ⟨80261, by rfl⟩ : syracuseStep 6848981 = 160523) (by norm_num)
theorem B4565987 : Blo 2027435 4565987 := bstep (se 1 (by rfl) ⟨3424490, by rfl⟩ : syracuseStep 4565987 = 6848981) B6848981
theorem B3043991 : Blo 2027435 3043991 := bstep (se 1 (by rfl) ⟨2282993, by rfl⟩ : syracuseStep 3043991 = 4565987) B4565987
theorem B2029327 : Blo 2027435 2029327 := bstep (se 1 (by rfl) ⟨1521995, by rfl⟩ : syracuseStep 2029327 = 3043991) B3043991
theorem B3043997 : Blo 2027435 3043997 := bbase (se 3 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 3043997 = 1141499) (by norm_num)
theorem B2029331 : Blo 2027435 2029331 := bstep (se 1 (by rfl) ⟨1521998, by rfl⟩ : syracuseStep 2029331 = 3043997) B3043997
theorem B4566005 : Blo 2027435 4566005 := bbase (se 5 (by rfl) ⟨214031, by rfl⟩ : syracuseStep 4566005 = 428063) (by norm_num)
theorem B3044003 : Blo 2027435 3044003 := bstep (se 1 (by rfl) ⟨2283002, by rfl⟩ : syracuseStep 3044003 = 4566005) B4566005
theorem B2029335 : Blo 2027435 2029335 := bstep (se 1 (by rfl) ⟨1522001, by rfl⟩ : syracuseStep 2029335 = 3044003) B3044003
theorem B6942469 : Blo 2027435 6942469 := bbase (se 4 (by rfl) ⟨650856, by rfl⟩ : syracuseStep 6942469 = 1301713) (by norm_num)
theorem B9256625 : Blo 2027435 9256625 := bstep (se 2 (by rfl) ⟨3471234, by rfl⟩ : syracuseStep 9256625 = 6942469) B6942469
theorem B6171083 : Blo 2027435 6171083 := bstep (se 1 (by rfl) ⟨4628312, by rfl⟩ : syracuseStep 6171083 = 9256625) B9256625
theorem B4114055 : Blo 2027435 4114055 := bstep (se 1 (by rfl) ⟨3085541, by rfl⟩ : syracuseStep 4114055 = 6171083) B6171083
theorem B2742703 : Blo 2027435 2742703 := bstep (se 1 (by rfl) ⟨2057027, by rfl⟩ : syracuseStep 2742703 = 4114055) B4114055
theorem B58510997 : Blo 2027435 58510997 := bstep (se 6 (by rfl) ⟨1371351, by rfl⟩ : syracuseStep 58510997 = 2742703) B2742703
theorem B39007331 : Blo 2027435 39007331 := bstep (se 1 (by rfl) ⟨29255498, by rfl⟩ : syracuseStep 39007331 = 58510997) B58510997
theorem B26004887 : Blo 2027435 26004887 := bstep (se 1 (by rfl) ⟨19503665, by rfl⟩ : syracuseStep 26004887 = 39007331) B39007331
theorem B17336591 : Blo 2027435 17336591 := bstep (se 1 (by rfl) ⟨13002443, by rfl⟩ : syracuseStep 17336591 = 26004887) B26004887
theorem B11557727 : Blo 2027435 11557727 := bstep (se 1 (by rfl) ⟨8668295, by rfl⟩ : syracuseStep 11557727 = 17336591) B17336591
theorem B7705151 : Blo 2027435 7705151 := bstep (se 1 (by rfl) ⟨5778863, by rfl⟩ : syracuseStep 7705151 = 11557727) B11557727
theorem B5136767 : Blo 2027435 5136767 := bstep (se 1 (by rfl) ⟨3852575, by rfl⟩ : syracuseStep 5136767 = 7705151) B7705151
theorem B3424511 : Blo 2027435 3424511 := bstep (se 1 (by rfl) ⟨2568383, by rfl⟩ : syracuseStep 3424511 = 5136767) B5136767
theorem B2283007 : Blo 2027435 2283007 := bstep (se 1 (by rfl) ⟨1712255, by rfl⟩ : syracuseStep 2283007 = 3424511) B3424511
theorem B3044009 : Blo 2027435 3044009 := bstep (se 2 (by rfl) ⟨1141503, by rfl⟩ : syracuseStep 3044009 = 2283007) B2283007
theorem B2029339 : Blo 2027435 2029339 := bstep (se 1 (by rfl) ⟨1522004, by rfl⟩ : syracuseStep 2029339 = 3044009) B3044009
theorem B2889437 : Blo 2027435 2889437 := bbase (se 3 (by rfl) ⟨541769, by rfl⟩ : syracuseStep 2889437 = 1083539) (by norm_num)
theorem B7705165 : Blo 2027435 7705165 := bstep (se 3 (by rfl) ⟨1444718, by rfl⟩ : syracuseStep 7705165 = 2889437) B2889437
theorem B10273553 : Blo 2027435 10273553 := bstep (se 2 (by rfl) ⟨3852582, by rfl⟩ : syracuseStep 10273553 = 7705165) B7705165
theorem B6849035 : Blo 2027435 6849035 := bstep (se 1 (by rfl) ⟨5136776, by rfl⟩ : syracuseStep 6849035 = 10273553) B10273553
theorem B4566023 : Blo 2027435 4566023 := bstep (se 1 (by rfl) ⟨3424517, by rfl⟩ : syracuseStep 4566023 = 6849035) B6849035
theorem B3044015 : Blo 2027435 3044015 := bstep (se 1 (by rfl) ⟨2283011, by rfl⟩ : syracuseStep 3044015 = 4566023) B4566023
theorem B2029343 : Blo 2027435 2029343 := bstep (se 1 (by rfl) ⟨1522007, by rfl⟩ : syracuseStep 2029343 = 3044015) B3044015
theorem B3044021 : Blo 2027435 3044021 := bbase (se 5 (by rfl) ⟨142688, by rfl⟩ : syracuseStep 3044021 = 285377) (by norm_num)
theorem B2029347 : Blo 2027435 2029347 := bstep (se 1 (by rfl) ⟨1522010, by rfl⟩ : syracuseStep 2029347 = 3044021) B3044021
theorem B5136797 : Blo 2027435 5136797 := bbase (se 3 (by rfl) ⟨963149, by rfl⟩ : syracuseStep 5136797 = 1926299) (by norm_num)
theorem B3424531 : Blo 2027435 3424531 := bstep (se 1 (by rfl) ⟨2568398, by rfl⟩ : syracuseStep 3424531 = 5136797) B5136797
theorem B4566041 : Blo 2027435 4566041 := bstep (se 2 (by rfl) ⟨1712265, by rfl⟩ : syracuseStep 4566041 = 3424531) B3424531
theorem B3044027 : Blo 2027435 3044027 := bstep (se 1 (by rfl) ⟨2283020, by rfl⟩ : syracuseStep 3044027 = 4566041) B4566041
theorem B2029351 : Blo 2027435 2029351 := bstep (se 1 (by rfl) ⟨1522013, by rfl⟩ : syracuseStep 2029351 = 3044027) B3044027
theorem B2283025 : Blo 2027435 2283025 := bbase (se 2 (by rfl) ⟨856134, by rfl⟩ : syracuseStep 2283025 = 1712269) (by norm_num)
theorem B3044033 : Blo 2027435 3044033 := bstep (se 2 (by rfl) ⟨1141512, by rfl⟩ : syracuseStep 3044033 = 2283025) B2283025
theorem B2029355 : Blo 2027435 2029355 := bstep (se 1 (by rfl) ⟨1522016, by rfl⟩ : syracuseStep 2029355 = 3044033) B3044033
theorem B3852613 : Blo 2027435 3852613 := bbase (se 4 (by rfl) ⟨361182, by rfl⟩ : syracuseStep 3852613 = 722365) (by norm_num)
theorem B5136817 : Blo 2027435 5136817 := bstep (se 2 (by rfl) ⟨1926306, by rfl⟩ : syracuseStep 5136817 = 3852613) B3852613
theorem B6849089 : Blo 2027435 6849089 := bstep (se 2 (by rfl) ⟨2568408, by rfl⟩ : syracuseStep 6849089 = 5136817) B5136817
theorem B4566059 : Blo 2027435 4566059 := bstep (se 1 (by rfl) ⟨3424544, by rfl⟩ : syracuseStep 4566059 = 6849089) B6849089
theorem B3044039 : Blo 2027435 3044039 := bstep (se 1 (by rfl) ⟨2283029, by rfl⟩ : syracuseStep 3044039 = 4566059) B4566059
theorem B2029359 : Blo 2027435 2029359 := bstep (se 1 (by rfl) ⟨1522019, by rfl⟩ : syracuseStep 2029359 = 3044039) B3044039
theorem B3044045 : Blo 2027435 3044045 := bbase (se 3 (by rfl) ⟨570758, by rfl⟩ : syracuseStep 3044045 = 1141517) (by norm_num)
theorem B2029363 : Blo 2027435 2029363 := bstep (se 1 (by rfl) ⟨1522022, by rfl⟩ : syracuseStep 2029363 = 3044045) B3044045
theorem B4566077 : Blo 2027435 4566077 := bbase (se 3 (by rfl) ⟨856139, by rfl⟩ : syracuseStep 4566077 = 1712279) (by norm_num)
theorem B3044051 : Blo 2027435 3044051 := bstep (se 1 (by rfl) ⟨2283038, by rfl⟩ : syracuseStep 3044051 = 4566077) B4566077
theorem B2029367 : Blo 2027435 2029367 := bstep (se 1 (by rfl) ⟨1522025, by rfl⟩ : syracuseStep 2029367 = 3044051) B3044051
theorem B3424565 : Blo 2027435 3424565 := bbase (se 5 (by rfl) ⟨160526, by rfl⟩ : syracuseStep 3424565 = 321053) (by norm_num)
theorem B2283043 : Blo 2027435 2283043 := bstep (se 1 (by rfl) ⟨1712282, by rfl⟩ : syracuseStep 2283043 = 3424565) B3424565
theorem B3044057 : Blo 2027435 3044057 := bstep (se 2 (by rfl) ⟨1141521, by rfl⟩ : syracuseStep 3044057 = 2283043) B2283043
theorem B2029371 : Blo 2027435 2029371 := bstep (se 1 (by rfl) ⟨1522028, by rfl⟩ : syracuseStep 2029371 = 3044057) B3044057
theorem B5778965 : Blo 2027435 5778965 := bbase (se 6 (by rfl) ⟨135444, by rfl⟩ : syracuseStep 5778965 = 270889) (by norm_num)
theorem B15410573 : Blo 2027435 15410573 := bstep (se 3 (by rfl) ⟨2889482, by rfl⟩ : syracuseStep 15410573 = 5778965) B5778965
theorem B10273715 : Blo 2027435 10273715 := bstep (se 1 (by rfl) ⟨7705286, by rfl⟩ : syracuseStep 10273715 = 15410573) B15410573
theorem B6849143 : Blo 2027435 6849143 := bstep (se 1 (by rfl) ⟨5136857, by rfl⟩ : syracuseStep 6849143 = 10273715) B10273715
theorem B4566095 : Blo 2027435 4566095 := bstep (se 1 (by rfl) ⟨3424571, by rfl⟩ : syracuseStep 4566095 = 6849143) B6849143
theorem B3044063 : Blo 2027435 3044063 := bstep (se 1 (by rfl) ⟨2283047, by rfl⟩ : syracuseStep 3044063 = 4566095) B4566095
theorem B2029375 : Blo 2027435 2029375 := bstep (se 1 (by rfl) ⟨1522031, by rfl⟩ : syracuseStep 2029375 = 3044063) B3044063
theorem B3044069 : Blo 2027435 3044069 := bbase (se 4 (by rfl) ⟨285381, by rfl⟩ : syracuseStep 3044069 = 570763) (by norm_num)
theorem B2029379 : Blo 2027435 2029379 := bstep (se 1 (by rfl) ⟨1522034, by rfl⟩ : syracuseStep 2029379 = 3044069) B3044069
theorem B2167121 : Blo 2027435 2167121 := bbase (se 2 (by rfl) ⟨812670, by rfl⟩ : syracuseStep 2167121 = 1625341) (by norm_num)
theorem B5778989 : Blo 2027435 5778989 := bstep (se 3 (by rfl) ⟨1083560, by rfl⟩ : syracuseStep 5778989 = 2167121) B2167121
theorem B3852659 : Blo 2027435 3852659 := bstep (se 1 (by rfl) ⟨2889494, by rfl⟩ : syracuseStep 3852659 = 5778989) B5778989
theorem B2568439 : Blo 2027435 2568439 := bstep (se 1 (by rfl) ⟨1926329, by rfl⟩ : syracuseStep 2568439 = 3852659) B3852659
theorem B3424585 : Blo 2027435 3424585 := bstep (se 2 (by rfl) ⟨1284219, by rfl⟩ : syracuseStep 3424585 = 2568439) B2568439
theorem B4566113 : Blo 2027435 4566113 := bstep (se 2 (by rfl) ⟨1712292, by rfl⟩ : syracuseStep 4566113 = 3424585) B3424585
theorem B3044075 : Blo 2027435 3044075 := bstep (se 1 (by rfl) ⟨2283056, by rfl⟩ : syracuseStep 3044075 = 4566113) B4566113
theorem B2029383 : Blo 2027435 2029383 := bstep (se 1 (by rfl) ⟨1522037, by rfl⟩ : syracuseStep 2029383 = 3044075) B3044075
theorem B2283061 : Blo 2027435 2283061 := bbase (se 5 (by rfl) ⟨107018, by rfl⟩ : syracuseStep 2283061 = 214037) (by norm_num)
theorem B3044081 : Blo 2027435 3044081 := bstep (se 2 (by rfl) ⟨1141530, by rfl⟩ : syracuseStep 3044081 = 2283061) B2283061
theorem B2029387 : Blo 2027435 2029387 := bstep (se 1 (by rfl) ⟨1522040, by rfl⟩ : syracuseStep 2029387 = 3044081) B3044081
theorem B2568449 : Blo 2027435 2568449 := bbase (se 2 (by rfl) ⟨963168, by rfl⟩ : syracuseStep 2568449 = 1926337) (by norm_num)
theorem B6849197 : Blo 2027435 6849197 := bstep (se 3 (by rfl) ⟨1284224, by rfl⟩ : syracuseStep 6849197 = 2568449) B2568449
theorem B4566131 : Blo 2027435 4566131 := bstep (se 1 (by rfl) ⟨3424598, by rfl⟩ : syracuseStep 4566131 = 6849197) B6849197
theorem B3044087 : Blo 2027435 3044087 := bstep (se 1 (by rfl) ⟨2283065, by rfl⟩ : syracuseStep 3044087 = 4566131) B4566131
theorem B2029391 : Blo 2027435 2029391 := bstep (se 1 (by rfl) ⟨1522043, by rfl⟩ : syracuseStep 2029391 = 3044087) B3044087
theorem B3044093 : Blo 2027435 3044093 := bbase (se 3 (by rfl) ⟨570767, by rfl⟩ : syracuseStep 3044093 = 1141535) (by norm_num)
theorem B2029395 : Blo 2027435 2029395 := bstep (se 1 (by rfl) ⟨1522046, by rfl⟩ : syracuseStep 2029395 = 3044093) B3044093
theorem B4566149 : Blo 2027435 4566149 := bbase (se 4 (by rfl) ⟨428076, by rfl⟩ : syracuseStep 4566149 = 856153) (by norm_num)
theorem B3044099 : Blo 2027435 3044099 := bstep (se 1 (by rfl) ⟨2283074, by rfl⟩ : syracuseStep 3044099 = 4566149) B4566149
theorem B2029399 : Blo 2027435 2029399 := bstep (se 1 (by rfl) ⟨1522049, by rfl⟩ : syracuseStep 2029399 = 3044099) B3044099
theorem B4334285 : Blo 2027435 4334285 := bbase (se 3 (by rfl) ⟨812678, by rfl⟩ : syracuseStep 4334285 = 1625357) (by norm_num)
theorem B2889523 : Blo 2027435 2889523 := bstep (se 1 (by rfl) ⟨2167142, by rfl⟩ : syracuseStep 2889523 = 4334285) B4334285
theorem B3852697 : Blo 2027435 3852697 := bstep (se 2 (by rfl) ⟨1444761, by rfl⟩ : syracuseStep 3852697 = 2889523) B2889523
theorem B5136929 : Blo 2027435 5136929 := bstep (se 2 (by rfl) ⟨1926348, by rfl⟩ : syracuseStep 5136929 = 3852697) B3852697
theorem B3424619 : Blo 2027435 3424619 := bstep (se 1 (by rfl) ⟨2568464, by rfl⟩ : syracuseStep 3424619 = 5136929) B5136929
theorem B2283079 : Blo 2027435 2283079 := bstep (se 1 (by rfl) ⟨1712309, by rfl⟩ : syracuseStep 2283079 = 3424619) B3424619
theorem B3044105 : Blo 2027435 3044105 := bstep (se 2 (by rfl) ⟨1141539, by rfl⟩ : syracuseStep 3044105 = 2283079) B2283079
theorem B2029403 : Blo 2027435 2029403 := bstep (se 1 (by rfl) ⟨1522052, by rfl⟩ : syracuseStep 2029403 = 3044105) B3044105
theorem B10273877 : Blo 2027435 10273877 := bbase (se 8 (by rfl) ⟨60198, by rfl⟩ : syracuseStep 10273877 = 120397) (by norm_num)
theorem B6849251 : Blo 2027435 6849251 := bstep (se 1 (by rfl) ⟨5136938, by rfl⟩ : syracuseStep 6849251 = 10273877) B10273877
theorem B4566167 : Blo 2027435 4566167 := bstep (se 1 (by rfl) ⟨3424625, by rfl⟩ : syracuseStep 4566167 = 6849251) B6849251
theorem B3044111 : Blo 2027435 3044111 := bstep (se 1 (by rfl) ⟨2283083, by rfl⟩ : syracuseStep 3044111 = 4566167) B4566167
theorem B2029407 : Blo 2027435 2029407 := bstep (se 1 (by rfl) ⟨1522055, by rfl⟩ : syracuseStep 2029407 = 3044111) B3044111
theorem B3044117 : Blo 2027435 3044117 := bbase (se 6 (by rfl) ⟨71346, by rfl⟩ : syracuseStep 3044117 = 142693) (by norm_num)
theorem B2029411 : Blo 2027435 2029411 := bstep (se 1 (by rfl) ⟨1522058, by rfl⟩ : syracuseStep 2029411 = 3044117) B3044117
theorem B39008789 : Blo 2027435 39008789 := bbase (se 6 (by rfl) ⟨914268, by rfl⟩ : syracuseStep 39008789 = 1828537) (by norm_num)
theorem B26005859 : Blo 2027435 26005859 := bstep (se 1 (by rfl) ⟨19504394, by rfl⟩ : syracuseStep 26005859 = 39008789) B39008789
theorem B17337239 : Blo 2027435 17337239 := bstep (se 1 (by rfl) ⟨13002929, by rfl⟩ : syracuseStep 17337239 = 26005859) B26005859
theorem B11558159 : Blo 2027435 11558159 := bstep (se 1 (by rfl) ⟨8668619, by rfl⟩ : syracuseStep 11558159 = 17337239) B17337239
theorem B7705439 : Blo 2027435 7705439 := bstep (se 1 (by rfl) ⟨5779079, by rfl⟩ : syracuseStep 7705439 = 11558159) B11558159
theorem B5136959 : Blo 2027435 5136959 := bstep (se 1 (by rfl) ⟨3852719, by rfl⟩ : syracuseStep 5136959 = 7705439) B7705439
theorem B3424639 : Blo 2027435 3424639 := bstep (se 1 (by rfl) ⟨2568479, by rfl⟩ : syracuseStep 3424639 = 5136959) B5136959
theorem B4566185 : Blo 2027435 4566185 := bstep (se 2 (by rfl) ⟨1712319, by rfl⟩ : syracuseStep 4566185 = 3424639) B3424639
theorem B3044123 : Blo 2027435 3044123 := bstep (se 1 (by rfl) ⟨2283092, by rfl⟩ : syracuseStep 3044123 = 4566185) B4566185
theorem B2029415 : Blo 2027435 2029415 := bstep (se 1 (by rfl) ⟨1522061, by rfl⟩ : syracuseStep 2029415 = 3044123) B3044123
theorem B2283097 : Blo 2027435 2283097 := bbase (se 2 (by rfl) ⟨856161, by rfl⟩ : syracuseStep 2283097 = 1712323) (by norm_num)
theorem B3044129 : Blo 2027435 3044129 := bstep (se 2 (by rfl) ⟨1141548, by rfl⟩ : syracuseStep 3044129 = 2283097) B2283097
theorem B2029419 : Blo 2027435 2029419 := bstep (se 1 (by rfl) ⟨1522064, by rfl⟩ : syracuseStep 2029419 = 3044129) B3044129
theorem B2057113 : Blo 2027435 2057113 := bbase (se 2 (by rfl) ⟨771417, by rfl⟩ : syracuseStep 2057113 = 1542835) (by norm_num)
theorem B2742817 : Blo 2027435 2742817 := bstep (se 2 (by rfl) ⟨1028556, by rfl⟩ : syracuseStep 2742817 = 2057113) B2057113
theorem B3657089 : Blo 2027435 3657089 := bstep (se 2 (by rfl) ⟨1371408, by rfl⟩ : syracuseStep 3657089 = 2742817) B2742817
theorem B9752237 : Blo 2027435 9752237 := bstep (se 3 (by rfl) ⟨1828544, by rfl⟩ : syracuseStep 9752237 = 3657089) B3657089
theorem B6501491 : Blo 2027435 6501491 := bstep (se 1 (by rfl) ⟨4876118, by rfl⟩ : syracuseStep 6501491 = 9752237) B9752237
theorem B4334327 : Blo 2027435 4334327 := bstep (se 1 (by rfl) ⟨3250745, by rfl⟩ : syracuseStep 4334327 = 6501491) B6501491
theorem B2889551 : Blo 2027435 2889551 := bstep (se 1 (by rfl) ⟨2167163, by rfl⟩ : syracuseStep 2889551 = 4334327) B4334327
theorem B7705469 : Blo 2027435 7705469 := bstep (se 3 (by rfl) ⟨1444775, by rfl⟩ : syracuseStep 7705469 = 2889551) B2889551
theorem B5136979 : Blo 2027435 5136979 := bstep (se 1 (by rfl) ⟨3852734, by rfl⟩ : syracuseStep 5136979 = 7705469) B7705469
theorem B6849305 : Blo 2027435 6849305 := bstep (se 2 (by rfl) ⟨2568489, by rfl⟩ : syracuseStep 6849305 = 5136979) B5136979
theorem B4566203 : Blo 2027435 4566203 := bstep (se 1 (by rfl) ⟨3424652, by rfl⟩ : syracuseStep 4566203 = 6849305) B6849305
theorem B3044135 : Blo 2027435 3044135 := bstep (se 1 (by rfl) ⟨2283101, by rfl⟩ : syracuseStep 3044135 = 4566203) B4566203
theorem B2029423 : Blo 2027435 2029423 := bstep (se 1 (by rfl) ⟨1522067, by rfl⟩ : syracuseStep 2029423 = 3044135) B3044135
theorem B3044141 : Blo 2027435 3044141 := bbase (se 3 (by rfl) ⟨570776, by rfl⟩ : syracuseStep 3044141 = 1141553) (by norm_num)
theorem B2029427 : Blo 2027435 2029427 := bstep (se 1 (by rfl) ⟨1522070, by rfl⟩ : syracuseStep 2029427 = 3044141) B3044141
theorem B4566221 : Blo 2027435 4566221 := bbase (se 3 (by rfl) ⟨856166, by rfl⟩ : syracuseStep 4566221 = 1712333) (by norm_num)
theorem B3044147 : Blo 2027435 3044147 := bstep (se 1 (by rfl) ⟨2283110, by rfl⟩ : syracuseStep 3044147 = 4566221) B4566221
theorem B2029431 : Blo 2027435 2029431 := bstep (se 1 (by rfl) ⟨1522073, by rfl⟩ : syracuseStep 2029431 = 3044147) B3044147
theorem B2568505 : Blo 2027435 2568505 := bbase (se 2 (by rfl) ⟨963189, by rfl⟩ : syracuseStep 2568505 = 1926379) (by norm_num)
theorem B3424673 : Blo 2027435 3424673 := bstep (se 2 (by rfl) ⟨1284252, by rfl⟩ : syracuseStep 3424673 = 2568505) B2568505
theorem B2283115 : Blo 2027435 2283115 := bstep (se 1 (by rfl) ⟨1712336, by rfl⟩ : syracuseStep 2283115 = 3424673) B3424673
theorem B3044153 : Blo 2027435 3044153 := bstep (se 2 (by rfl) ⟨1141557, by rfl⟩ : syracuseStep 3044153 = 2283115) B2283115
theorem B2029435 : Blo 2027435 2029435 := bstep (se 1 (by rfl) ⟨1522076, by rfl⟩ : syracuseStep 2029435 = 3044153) B3044153
theorem C0 (j : ℕ) (h1 : 506858 ≤ j) (h2 : j ≤ 507358) : Blo 2027435 (4 * j + 3) := by
  interval_cases j
  · exact B2027435
  · exact B2027439
  · exact B2027443
  · exact B2027447
  · exact B2027451
  · exact B2027455
  · exact B2027459
  · exact B2027463
  · exact B2027467
  · exact B2027471
  · exact B2027475
  · exact B2027479
  · exact B2027483
  · exact B2027487
  · exact B2027491
  · exact B2027495
  · exact B2027499
  · exact B2027503
  · exact B2027507
  · exact B2027511
  · exact B2027515
  · exact B2027519
  · exact B2027523
  · exact B2027527
  · exact B2027531
  · exact B2027535
  · exact B2027539
  · exact B2027543
  · exact B2027547
  · exact B2027551
  · exact B2027555
  · exact B2027559
  · exact B2027563
  · exact B2027567
  · exact B2027571
  · exact B2027575
  · exact B2027579
  · exact B2027583
  · exact B2027587
  · exact B2027591
  · exact B2027595
  · exact B2027599
  · exact B2027603
  · exact B2027607
  · exact B2027611
  · exact B2027615
  · exact B2027619
  · exact B2027623
  · exact B2027627
  · exact B2027631
  · exact B2027635
  · exact B2027639
  · exact B2027643
  · exact B2027647
  · exact B2027651
  · exact B2027655
  · exact B2027659
  · exact B2027663
  · exact B2027667
  · exact B2027671
  · exact B2027675
  · exact B2027679
  · exact B2027683
  · exact B2027687
  · exact B2027691
  · exact B2027695
  · exact B2027699
  · exact B2027703
  · exact B2027707
  · exact B2027711
  · exact B2027715
  · exact B2027719
  · exact B2027723
  · exact B2027727
  · exact B2027731
  · exact B2027735
  · exact B2027739
  · exact B2027743
  · exact B2027747
  · exact B2027751
  · exact B2027755
  · exact B2027759
  · exact B2027763
  · exact B2027767
  · exact B2027771
  · exact B2027775
  · exact B2027779
  · exact B2027783
  · exact B2027787
  · exact B2027791
  · exact B2027795
  · exact B2027799
  · exact B2027803
  · exact B2027807
  · exact B2027811
  · exact B2027815
  · exact B2027819
  · exact B2027823
  · exact B2027827
  · exact B2027831
  · exact B2027835
  · exact B2027839
  · exact B2027843
  · exact B2027847
  · exact B2027851
  · exact B2027855
  · exact B2027859
  · exact B2027863
  · exact B2027867
  · exact B2027871
  · exact B2027875
  · exact B2027879
  · exact B2027883
  · exact B2027887
  · exact B2027891
  · exact B2027895
  · exact B2027899
  · exact B2027903
  · exact B2027907
  · exact B2027911
  · exact B2027915
  · exact B2027919
  · exact B2027923
  · exact B2027927
  · exact B2027931
  · exact B2027935
  · exact B2027939
  · exact B2027943
  · exact B2027947
  · exact B2027951
  · exact B2027955
  · exact B2027959
  · exact B2027963
  · exact B2027967
  · exact B2027971
  · exact B2027975
  · exact B2027979
  · exact B2027983
  · exact B2027987
  · exact B2027991
  · exact B2027995
  · exact B2027999
  · exact B2028003
  · exact B2028007
  · exact B2028011
  · exact B2028015
  · exact B2028019
  · exact B2028023
  · exact B2028027
  · exact B2028031
  · exact B2028035
  · exact B2028039
  · exact B2028043
  · exact B2028047
  · exact B2028051
  · exact B2028055
  · exact B2028059
  · exact B2028063
  · exact B2028067
  · exact B2028071
  · exact B2028075
  · exact B2028079
  · exact B2028083
  · exact B2028087
  · exact B2028091
  · exact B2028095
  · exact B2028099
  · exact B2028103
  · exact B2028107
  · exact B2028111
  · exact B2028115
  · exact B2028119
  · exact B2028123
  · exact B2028127
  · exact B2028131
  · exact B2028135
  · exact B2028139
  · exact B2028143
  · exact B2028147
  · exact B2028151
  · exact B2028155
  · exact B2028159
  · exact B2028163
  · exact B2028167
  · exact B2028171
  · exact B2028175
  · exact B2028179
  · exact B2028183
  · exact B2028187
  · exact B2028191
  · exact B2028195
  · exact B2028199
  · exact B2028203
  · exact B2028207
  · exact B2028211
  · exact B2028215
  · exact B2028219
  · exact B2028223
  · exact B2028227
  · exact B2028231
  · exact B2028235
  · exact B2028239
  · exact B2028243
  · exact B2028247
  · exact B2028251
  · exact B2028255
  · exact B2028259
  · exact B2028263
  · exact B2028267
  · exact B2028271
  · exact B2028275
  · exact B2028279
  · exact B2028283
  · exact B2028287
  · exact B2028291
  · exact B2028295
  · exact B2028299
  · exact B2028303
  · exact B2028307
  · exact B2028311
  · exact B2028315
  · exact B2028319
  · exact B2028323
  · exact B2028327
  · exact B2028331
  · exact B2028335
  · exact B2028339
  · exact B2028343
  · exact B2028347
  · exact B2028351
  · exact B2028355
  · exact B2028359
  · exact B2028363
  · exact B2028367
  · exact B2028371
  · exact B2028375
  · exact B2028379
  · exact B2028383
  · exact B2028387
  · exact B2028391
  · exact B2028395
  · exact B2028399
  · exact B2028403
  · exact B2028407
  · exact B2028411
  · exact B2028415
  · exact B2028419
  · exact B2028423
  · exact B2028427
  · exact B2028431
  · exact B2028435
  · exact B2028439
  · exact B2028443
  · exact B2028447
  · exact B2028451
  · exact B2028455
  · exact B2028459
  · exact B2028463
  · exact B2028467
  · exact B2028471
  · exact B2028475
  · exact B2028479
  · exact B2028483
  · exact B2028487
  · exact B2028491
  · exact B2028495
  · exact B2028499
  · exact B2028503
  · exact B2028507
  · exact B2028511
  · exact B2028515
  · exact B2028519
  · exact B2028523
  · exact B2028527
  · exact B2028531
  · exact B2028535
  · exact B2028539
  · exact B2028543
  · exact B2028547
  · exact B2028551
  · exact B2028555
  · exact B2028559
  · exact B2028563
  · exact B2028567
  · exact B2028571
  · exact B2028575
  · exact B2028579
  · exact B2028583
  · exact B2028587
  · exact B2028591
  · exact B2028595
  · exact B2028599
  · exact B2028603
  · exact B2028607
  · exact B2028611
  · exact B2028615
  · exact B2028619
  · exact B2028623
  · exact B2028627
  · exact B2028631
  · exact B2028635
  · exact B2028639
  · exact B2028643
  · exact B2028647
  · exact B2028651
  · exact B2028655
  · exact B2028659
  · exact B2028663
  · exact B2028667
  · exact B2028671
  · exact B2028675
  · exact B2028679
  · exact B2028683
  · exact B2028687
  · exact B2028691
  · exact B2028695
  · exact B2028699
  · exact B2028703
  · exact B2028707
  · exact B2028711
  · exact B2028715
  · exact B2028719
  · exact B2028723
  · exact B2028727
  · exact B2028731
  · exact B2028735
  · exact B2028739
  · exact B2028743
  · exact B2028747
  · exact B2028751
  · exact B2028755
  · exact B2028759
  · exact B2028763
  · exact B2028767
  · exact B2028771
  · exact B2028775
  · exact B2028779
  · exact B2028783
  · exact B2028787
  · exact B2028791
  · exact B2028795
  · exact B2028799
  · exact B2028803
  · exact B2028807
  · exact B2028811
  · exact B2028815
  · exact B2028819
  · exact B2028823
  · exact B2028827
  · exact B2028831
  · exact B2028835
  · exact B2028839
  · exact B2028843
  · exact B2028847
  · exact B2028851
  · exact B2028855
  · exact B2028859
  · exact B2028863
  · exact B2028867
  · exact B2028871
  · exact B2028875
  · exact B2028879
  · exact B2028883
  · exact B2028887
  · exact B2028891
  · exact B2028895
  · exact B2028899
  · exact B2028903
  · exact B2028907
  · exact B2028911
  · exact B2028915
  · exact B2028919
  · exact B2028923
  · exact B2028927
  · exact B2028931
  · exact B2028935
  · exact B2028939
  · exact B2028943
  · exact B2028947
  · exact B2028951
  · exact B2028955
  · exact B2028959
  · exact B2028963
  · exact B2028967
  · exact B2028971
  · exact B2028975
  · exact B2028979
  · exact B2028983
  · exact B2028987
  · exact B2028991
  · exact B2028995
  · exact B2028999
  · exact B2029003
  · exact B2029007
  · exact B2029011
  · exact B2029015
  · exact B2029019
  · exact B2029023
  · exact B2029027
  · exact B2029031
  · exact B2029035
  · exact B2029039
  · exact B2029043
  · exact B2029047
  · exact B2029051
  · exact B2029055
  · exact B2029059
  · exact B2029063
  · exact B2029067
  · exact B2029071
  · exact B2029075
  · exact B2029079
  · exact B2029083
  · exact B2029087
  · exact B2029091
  · exact B2029095
  · exact B2029099
  · exact B2029103
  · exact B2029107
  · exact B2029111
  · exact B2029115
  · exact B2029119
  · exact B2029123
  · exact B2029127
  · exact B2029131
  · exact B2029135
  · exact B2029139
  · exact B2029143
  · exact B2029147
  · exact B2029151
  · exact B2029155
  · exact B2029159
  · exact B2029163
  · exact B2029167
  · exact B2029171
  · exact B2029175
  · exact B2029179
  · exact B2029183
  · exact B2029187
  · exact B2029191
  · exact B2029195
  · exact B2029199
  · exact B2029203
  · exact B2029207
  · exact B2029211
  · exact B2029215
  · exact B2029219
  · exact B2029223
  · exact B2029227
  · exact B2029231
  · exact B2029235
  · exact B2029239
  · exact B2029243
  · exact B2029247
  · exact B2029251
  · exact B2029255
  · exact B2029259
  · exact B2029263
  · exact B2029267
  · exact B2029271
  · exact B2029275
  · exact B2029279
  · exact B2029283
  · exact B2029287
  · exact B2029291
  · exact B2029295
  · exact B2029299
  · exact B2029303
  · exact B2029307
  · exact B2029311
  · exact B2029315
  · exact B2029319
  · exact B2029323
  · exact B2029327
  · exact B2029331
  · exact B2029335
  · exact B2029339
  · exact B2029343
  · exact B2029347
  · exact B2029351
  · exact B2029355
  · exact B2029359
  · exact B2029363
  · exact B2029367
  · exact B2029371
  · exact B2029375
  · exact B2029379
  · exact B2029383
  · exact B2029387
  · exact B2029391
  · exact B2029395
  · exact B2029399
  · exact B2029403
  · exact B2029407
  · exact B2029411
  · exact B2029415
  · exact B2029419
  · exact B2029423
  · exact B2029427
  · exact B2029431
  · exact B2029435
theorem solution (m : ℕ) (hlo : 2027435 ≤ m) (hhi : m ≤ 2029435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 506858 ≤ j := by omega
    have hj2 : j ≤ 507358 := by omega
    have hb : Blo 2027435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
