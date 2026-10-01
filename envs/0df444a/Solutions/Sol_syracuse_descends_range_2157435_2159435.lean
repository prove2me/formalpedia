-- Prove2me | solution 1 for syracuse_descends_range_2157435_2159435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:17:34.141898+00:00
-- url     : https://prove2.me/submissions/4e18e3dd-3f24-4e28-9732-1622ed062d68

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

theorem B2730505 : Blo 2157435 2730505 := bbase (se 2 (by rfl) ⟨1023939, by rfl⟩ : syracuseStep 2730505 = 2047879) (by norm_num)
theorem B3640673 : Blo 2157435 3640673 := bstep (se 2 (by rfl) ⟨1365252, by rfl⟩ : syracuseStep 3640673 = 2730505) B2730505
theorem B2427115 : Blo 2157435 2427115 := bstep (se 1 (by rfl) ⟨1820336, by rfl⟩ : syracuseStep 2427115 = 3640673) B3640673
theorem B3236153 : Blo 2157435 3236153 := bstep (se 2 (by rfl) ⟨1213557, by rfl⟩ : syracuseStep 3236153 = 2427115) B2427115
theorem B2157435 : Blo 2157435 2157435 := bstep (se 1 (by rfl) ⟨1618076, by rfl⟩ : syracuseStep 2157435 = 3236153) B3236153
theorem B7198373 : Blo 2157435 7198373 := bbase (se 4 (by rfl) ⟨674847, by rfl⟩ : syracuseStep 7198373 = 1349695) (by norm_num)
theorem B19195661 : Blo 2157435 19195661 := bstep (se 3 (by rfl) ⟨3599186, by rfl⟩ : syracuseStep 19195661 = 7198373) B7198373
theorem B51188429 : Blo 2157435 51188429 := bstep (se 3 (by rfl) ⟨9597830, by rfl⟩ : syracuseStep 51188429 = 19195661) B19195661
theorem B34125619 : Blo 2157435 34125619 := bstep (se 1 (by rfl) ⟨25594214, by rfl⟩ : syracuseStep 34125619 = 51188429) B51188429
theorem B45500825 : Blo 2157435 45500825 := bstep (se 2 (by rfl) ⟨17062809, by rfl⟩ : syracuseStep 45500825 = 34125619) B34125619
theorem B121335533 : Blo 2157435 121335533 := bstep (se 3 (by rfl) ⟨22750412, by rfl⟩ : syracuseStep 121335533 = 45500825) B45500825
theorem B80890355 : Blo 2157435 80890355 := bstep (se 1 (by rfl) ⟨60667766, by rfl⟩ : syracuseStep 80890355 = 121335533) B121335533
theorem B53926903 : Blo 2157435 53926903 := bstep (se 1 (by rfl) ⟨40445177, by rfl⟩ : syracuseStep 53926903 = 80890355) B80890355
theorem B287610149 : Blo 2157435 287610149 := bstep (se 4 (by rfl) ⟨26963451, by rfl⟩ : syracuseStep 287610149 = 53926903) B53926903
theorem B766960397 : Blo 2157435 766960397 := bstep (se 3 (by rfl) ⟨143805074, by rfl⟩ : syracuseStep 766960397 = 287610149) B287610149
theorem B511306931 : Blo 2157435 511306931 := bstep (se 1 (by rfl) ⟨383480198, by rfl⟩ : syracuseStep 511306931 = 766960397) B766960397
theorem B340871287 : Blo 2157435 340871287 := bstep (se 1 (by rfl) ⟨255653465, by rfl⟩ : syracuseStep 340871287 = 511306931) B511306931
theorem B454495049 : Blo 2157435 454495049 := bstep (se 2 (by rfl) ⟨170435643, by rfl⟩ : syracuseStep 454495049 = 340871287) B340871287
theorem B302996699 : Blo 2157435 302996699 := bstep (se 1 (by rfl) ⟨227247524, by rfl⟩ : syracuseStep 302996699 = 454495049) B454495049
theorem B201997799 : Blo 2157435 201997799 := bstep (se 1 (by rfl) ⟨151498349, by rfl⟩ : syracuseStep 201997799 = 302996699) B302996699
theorem B134665199 : Blo 2157435 134665199 := bstep (se 1 (by rfl) ⟨100998899, by rfl⟩ : syracuseStep 134665199 = 201997799) B201997799
theorem B89776799 : Blo 2157435 89776799 := bstep (se 1 (by rfl) ⟨67332599, by rfl⟩ : syracuseStep 89776799 = 134665199) B134665199
theorem B59851199 : Blo 2157435 59851199 := bstep (se 1 (by rfl) ⟨44888399, by rfl⟩ : syracuseStep 59851199 = 89776799) B89776799
theorem B39900799 : Blo 2157435 39900799 := bstep (se 1 (by rfl) ⟨29925599, by rfl⟩ : syracuseStep 39900799 = 59851199) B59851199
theorem B53201065 : Blo 2157435 53201065 := bstep (se 2 (by rfl) ⟨19950399, by rfl⟩ : syracuseStep 53201065 = 39900799) B39900799
theorem B70934753 : Blo 2157435 70934753 := bstep (se 2 (by rfl) ⟨26600532, by rfl⟩ : syracuseStep 70934753 = 53201065) B53201065
theorem B47289835 : Blo 2157435 47289835 := bstep (se 1 (by rfl) ⟨35467376, by rfl⟩ : syracuseStep 47289835 = 70934753) B70934753
theorem B63053113 : Blo 2157435 63053113 := bstep (se 2 (by rfl) ⟨23644917, by rfl⟩ : syracuseStep 63053113 = 47289835) B47289835
theorem B84070817 : Blo 2157435 84070817 := bstep (se 2 (by rfl) ⟨31526556, by rfl⟩ : syracuseStep 84070817 = 63053113) B63053113
theorem B56047211 : Blo 2157435 56047211 := bstep (se 1 (by rfl) ⟨42035408, by rfl⟩ : syracuseStep 56047211 = 84070817) B84070817
theorem B37364807 : Blo 2157435 37364807 := bstep (se 1 (by rfl) ⟨28023605, by rfl⟩ : syracuseStep 37364807 = 56047211) B56047211
theorem B24909871 : Blo 2157435 24909871 := bstep (se 1 (by rfl) ⟨18682403, by rfl⟩ : syracuseStep 24909871 = 37364807) B37364807
theorem B33213161 : Blo 2157435 33213161 := bstep (se 2 (by rfl) ⟨12454935, by rfl⟩ : syracuseStep 33213161 = 24909871) B24909871
theorem B22142107 : Blo 2157435 22142107 := bstep (se 1 (by rfl) ⟨16606580, by rfl⟩ : syracuseStep 22142107 = 33213161) B33213161
theorem B29522809 : Blo 2157435 29522809 := bstep (se 2 (by rfl) ⟨11071053, by rfl⟩ : syracuseStep 29522809 = 22142107) B22142107
theorem B39363745 : Blo 2157435 39363745 := bstep (se 2 (by rfl) ⟨14761404, by rfl⟩ : syracuseStep 39363745 = 29522809) B29522809
theorem B52484993 : Blo 2157435 52484993 := bstep (se 2 (by rfl) ⟨19681872, by rfl⟩ : syracuseStep 52484993 = 39363745) B39363745
theorem B34989995 : Blo 2157435 34989995 := bstep (se 1 (by rfl) ⟨26242496, by rfl⟩ : syracuseStep 34989995 = 52484993) B52484993
theorem B23326663 : Blo 2157435 23326663 := bstep (se 1 (by rfl) ⟨17494997, by rfl⟩ : syracuseStep 23326663 = 34989995) B34989995
theorem B31102217 : Blo 2157435 31102217 := bstep (se 2 (by rfl) ⟨11663331, by rfl⟩ : syracuseStep 31102217 = 23326663) B23326663
theorem B20734811 : Blo 2157435 20734811 := bstep (se 1 (by rfl) ⟨15551108, by rfl⟩ : syracuseStep 20734811 = 31102217) B31102217
theorem B13823207 : Blo 2157435 13823207 := bstep (se 1 (by rfl) ⟨10367405, by rfl⟩ : syracuseStep 13823207 = 20734811) B20734811
theorem B9215471 : Blo 2157435 9215471 := bstep (se 1 (by rfl) ⟨6911603, by rfl⟩ : syracuseStep 9215471 = 13823207) B13823207
theorem B24574589 : Blo 2157435 24574589 := bstep (se 3 (by rfl) ⟨4607735, by rfl⟩ : syracuseStep 24574589 = 9215471) B9215471
theorem B16383059 : Blo 2157435 16383059 := bstep (se 1 (by rfl) ⟨12287294, by rfl⟩ : syracuseStep 16383059 = 24574589) B24574589
theorem B10922039 : Blo 2157435 10922039 := bstep (se 1 (by rfl) ⟨8191529, by rfl⟩ : syracuseStep 10922039 = 16383059) B16383059
theorem B7281359 : Blo 2157435 7281359 := bstep (se 1 (by rfl) ⟨5461019, by rfl⟩ : syracuseStep 7281359 = 10922039) B10922039
theorem B4854239 : Blo 2157435 4854239 := bstep (se 1 (by rfl) ⟨3640679, by rfl⟩ : syracuseStep 4854239 = 7281359) B7281359
theorem B3236159 : Blo 2157435 3236159 := bstep (se 1 (by rfl) ⟨2427119, by rfl⟩ : syracuseStep 3236159 = 4854239) B4854239
theorem B2157439 : Blo 2157435 2157439 := bstep (se 1 (by rfl) ⟨1618079, by rfl⟩ : syracuseStep 2157439 = 3236159) B3236159
theorem B3236165 : Blo 2157435 3236165 := bbase (se 4 (by rfl) ⟨303390, by rfl⟩ : syracuseStep 3236165 = 606781) (by norm_num)
theorem B2157443 : Blo 2157435 2157443 := bstep (se 1 (by rfl) ⟨1618082, by rfl⟩ : syracuseStep 2157443 = 3236165) B3236165
theorem B3640693 : Blo 2157435 3640693 := bbase (se 5 (by rfl) ⟨170657, by rfl⟩ : syracuseStep 3640693 = 341315) (by norm_num)
theorem B4854257 : Blo 2157435 4854257 := bstep (se 2 (by rfl) ⟨1820346, by rfl⟩ : syracuseStep 4854257 = 3640693) B3640693
theorem B3236171 : Blo 2157435 3236171 := bstep (se 1 (by rfl) ⟨2427128, by rfl⟩ : syracuseStep 3236171 = 4854257) B4854257
theorem B2157447 : Blo 2157435 2157447 := bstep (se 1 (by rfl) ⟨1618085, by rfl⟩ : syracuseStep 2157447 = 3236171) B3236171
theorem B2427133 : Blo 2157435 2427133 := bbase (se 3 (by rfl) ⟨455087, by rfl⟩ : syracuseStep 2427133 = 910175) (by norm_num)
theorem B3236177 : Blo 2157435 3236177 := bstep (se 2 (by rfl) ⟨1213566, by rfl⟩ : syracuseStep 3236177 = 2427133) B2427133
theorem B2157451 : Blo 2157435 2157451 := bstep (se 1 (by rfl) ⟨1618088, by rfl⟩ : syracuseStep 2157451 = 3236177) B3236177
theorem B7281413 : Blo 2157435 7281413 := bbase (se 4 (by rfl) ⟨682632, by rfl⟩ : syracuseStep 7281413 = 1365265) (by norm_num)
theorem B4854275 : Blo 2157435 4854275 := bstep (se 1 (by rfl) ⟨3640706, by rfl⟩ : syracuseStep 4854275 = 7281413) B7281413
theorem B3236183 : Blo 2157435 3236183 := bstep (se 1 (by rfl) ⟨2427137, by rfl⟩ : syracuseStep 3236183 = 4854275) B4854275
theorem B2157455 : Blo 2157435 2157455 := bstep (se 1 (by rfl) ⟨1618091, by rfl⟩ : syracuseStep 2157455 = 3236183) B3236183
theorem B3236189 : Blo 2157435 3236189 := bbase (se 3 (by rfl) ⟨606785, by rfl⟩ : syracuseStep 3236189 = 1213571) (by norm_num)
theorem B2157459 : Blo 2157435 2157459 := bstep (se 1 (by rfl) ⟨1618094, by rfl⟩ : syracuseStep 2157459 = 3236189) B3236189
theorem B4854293 : Blo 2157435 4854293 := bbase (se 6 (by rfl) ⟨113772, by rfl⟩ : syracuseStep 4854293 = 227545) (by norm_num)
theorem B3236195 : Blo 2157435 3236195 := bstep (se 1 (by rfl) ⟨2427146, by rfl⟩ : syracuseStep 3236195 = 4854293) B4854293
theorem B2157463 : Blo 2157435 2157463 := bstep (se 1 (by rfl) ⟨1618097, by rfl⟩ : syracuseStep 2157463 = 3236195) B3236195
theorem B8191637 : Blo 2157435 8191637 := bbase (se 6 (by rfl) ⟨191991, by rfl⟩ : syracuseStep 8191637 = 383983) (by norm_num)
theorem B5461091 : Blo 2157435 5461091 := bstep (se 1 (by rfl) ⟨4095818, by rfl⟩ : syracuseStep 5461091 = 8191637) B8191637
theorem B3640727 : Blo 2157435 3640727 := bstep (se 1 (by rfl) ⟨2730545, by rfl⟩ : syracuseStep 3640727 = 5461091) B5461091
theorem B2427151 : Blo 2157435 2427151 := bstep (se 1 (by rfl) ⟨1820363, by rfl⟩ : syracuseStep 2427151 = 3640727) B3640727
theorem B3236201 : Blo 2157435 3236201 := bstep (se 2 (by rfl) ⟨1213575, by rfl⟩ : syracuseStep 3236201 = 2427151) B2427151
theorem B2157467 : Blo 2157435 2157467 := bstep (se 1 (by rfl) ⟨1618100, by rfl⟩ : syracuseStep 2157467 = 3236201) B3236201
theorem B12287477 : Blo 2157435 12287477 := bbase (se 5 (by rfl) ⟨575975, by rfl⟩ : syracuseStep 12287477 = 1151951) (by norm_num)
theorem B8191651 : Blo 2157435 8191651 := bstep (se 1 (by rfl) ⟨6143738, by rfl⟩ : syracuseStep 8191651 = 12287477) B12287477
theorem B10922201 : Blo 2157435 10922201 := bstep (se 2 (by rfl) ⟨4095825, by rfl⟩ : syracuseStep 10922201 = 8191651) B8191651
theorem B7281467 : Blo 2157435 7281467 := bstep (se 1 (by rfl) ⟨5461100, by rfl⟩ : syracuseStep 7281467 = 10922201) B10922201
theorem B4854311 : Blo 2157435 4854311 := bstep (se 1 (by rfl) ⟨3640733, by rfl⟩ : syracuseStep 4854311 = 7281467) B7281467
theorem B3236207 : Blo 2157435 3236207 := bstep (se 1 (by rfl) ⟨2427155, by rfl⟩ : syracuseStep 3236207 = 4854311) B4854311
theorem B2157471 : Blo 2157435 2157471 := bstep (se 1 (by rfl) ⟨1618103, by rfl⟩ : syracuseStep 2157471 = 3236207) B3236207
theorem B3236213 : Blo 2157435 3236213 := bbase (se 5 (by rfl) ⟨151697, by rfl⟩ : syracuseStep 3236213 = 303395) (by norm_num)
theorem B2157475 : Blo 2157435 2157475 := bstep (se 1 (by rfl) ⟨1618106, by rfl⟩ : syracuseStep 2157475 = 3236213) B3236213
theorem B2767817 : Blo 2157435 2767817 := bbase (se 2 (by rfl) ⟨1037931, by rfl⟩ : syracuseStep 2767817 = 2075863) (by norm_num)
theorem B7380845 : Blo 2157435 7380845 := bstep (se 3 (by rfl) ⟨1383908, by rfl⟩ : syracuseStep 7380845 = 2767817) B2767817
theorem B4920563 : Blo 2157435 4920563 := bstep (se 1 (by rfl) ⟨3690422, by rfl⟩ : syracuseStep 4920563 = 7380845) B7380845
theorem B3280375 : Blo 2157435 3280375 := bstep (se 1 (by rfl) ⟨2460281, by rfl⟩ : syracuseStep 3280375 = 4920563) B4920563
theorem B4373833 : Blo 2157435 4373833 := bstep (se 2 (by rfl) ⟨1640187, by rfl⟩ : syracuseStep 4373833 = 3280375) B3280375
theorem B5831777 : Blo 2157435 5831777 := bstep (se 2 (by rfl) ⟨2186916, by rfl⟩ : syracuseStep 5831777 = 4373833) B4373833
theorem B3887851 : Blo 2157435 3887851 := bstep (se 1 (by rfl) ⟨2915888, by rfl⟩ : syracuseStep 3887851 = 5831777) B5831777
theorem B5183801 : Blo 2157435 5183801 := bstep (se 2 (by rfl) ⟨1943925, by rfl⟩ : syracuseStep 5183801 = 3887851) B3887851
theorem B3455867 : Blo 2157435 3455867 := bstep (se 1 (by rfl) ⟨2591900, by rfl⟩ : syracuseStep 3455867 = 5183801) B5183801
theorem B2303911 : Blo 2157435 2303911 := bstep (se 1 (by rfl) ⟨1727933, by rfl⟩ : syracuseStep 2303911 = 3455867) B3455867
theorem B3071881 : Blo 2157435 3071881 := bstep (se 2 (by rfl) ⟨1151955, by rfl⟩ : syracuseStep 3071881 = 2303911) B2303911
theorem B4095841 : Blo 2157435 4095841 := bstep (se 2 (by rfl) ⟨1535940, by rfl⟩ : syracuseStep 4095841 = 3071881) B3071881
theorem B5461121 : Blo 2157435 5461121 := bstep (se 2 (by rfl) ⟨2047920, by rfl⟩ : syracuseStep 5461121 = 4095841) B4095841
theorem B3640747 : Blo 2157435 3640747 := bstep (se 1 (by rfl) ⟨2730560, by rfl⟩ : syracuseStep 3640747 = 5461121) B5461121
theorem B4854329 : Blo 2157435 4854329 := bstep (se 2 (by rfl) ⟨1820373, by rfl⟩ : syracuseStep 4854329 = 3640747) B3640747
theorem B3236219 : Blo 2157435 3236219 := bstep (se 1 (by rfl) ⟨2427164, by rfl⟩ : syracuseStep 3236219 = 4854329) B4854329
theorem B2157479 : Blo 2157435 2157479 := bstep (se 1 (by rfl) ⟨1618109, by rfl⟩ : syracuseStep 2157479 = 3236219) B3236219
theorem B2427169 : Blo 2157435 2427169 := bbase (se 2 (by rfl) ⟨910188, by rfl⟩ : syracuseStep 2427169 = 1820377) (by norm_num)
theorem B3236225 : Blo 2157435 3236225 := bstep (se 2 (by rfl) ⟨1213584, by rfl⟩ : syracuseStep 3236225 = 2427169) B2427169
theorem B2157483 : Blo 2157435 2157483 := bstep (se 1 (by rfl) ⟨1618112, by rfl⟩ : syracuseStep 2157483 = 3236225) B3236225
theorem B5461141 : Blo 2157435 5461141 := bbase (se 6 (by rfl) ⟨127995, by rfl⟩ : syracuseStep 5461141 = 255991) (by norm_num)
theorem B7281521 : Blo 2157435 7281521 := bstep (se 2 (by rfl) ⟨2730570, by rfl⟩ : syracuseStep 7281521 = 5461141) B5461141
theorem B4854347 : Blo 2157435 4854347 := bstep (se 1 (by rfl) ⟨3640760, by rfl⟩ : syracuseStep 4854347 = 7281521) B7281521
theorem B3236231 : Blo 2157435 3236231 := bstep (se 1 (by rfl) ⟨2427173, by rfl⟩ : syracuseStep 3236231 = 4854347) B4854347
theorem B2157487 : Blo 2157435 2157487 := bstep (se 1 (by rfl) ⟨1618115, by rfl⟩ : syracuseStep 2157487 = 3236231) B3236231
theorem B3236237 : Blo 2157435 3236237 := bbase (se 3 (by rfl) ⟨606794, by rfl⟩ : syracuseStep 3236237 = 1213589) (by norm_num)
theorem B2157491 : Blo 2157435 2157491 := bstep (se 1 (by rfl) ⟨1618118, by rfl⟩ : syracuseStep 2157491 = 3236237) B3236237
theorem B4854365 : Blo 2157435 4854365 := bbase (se 3 (by rfl) ⟨910193, by rfl⟩ : syracuseStep 4854365 = 1820387) (by norm_num)
theorem B3236243 : Blo 2157435 3236243 := bstep (se 1 (by rfl) ⟨2427182, by rfl⟩ : syracuseStep 3236243 = 4854365) B4854365
theorem B2157495 : Blo 2157435 2157495 := bstep (se 1 (by rfl) ⟨1618121, by rfl⟩ : syracuseStep 2157495 = 3236243) B3236243
theorem B3640781 : Blo 2157435 3640781 := bbase (se 3 (by rfl) ⟨682646, by rfl⟩ : syracuseStep 3640781 = 1365293) (by norm_num)
theorem B2427187 : Blo 2157435 2427187 := bstep (se 1 (by rfl) ⟨1820390, by rfl⟩ : syracuseStep 2427187 = 3640781) B3640781
theorem B3236249 : Blo 2157435 3236249 := bstep (se 2 (by rfl) ⟨1213593, by rfl⟩ : syracuseStep 3236249 = 2427187) B2427187
theorem B2157499 : Blo 2157435 2157499 := bstep (se 1 (by rfl) ⟨1618124, by rfl⟩ : syracuseStep 2157499 = 3236249) B3236249
theorem B3740813 : Blo 2157435 3740813 := bbase (se 3 (by rfl) ⟨701402, by rfl⟩ : syracuseStep 3740813 = 1402805) (by norm_num)
theorem B2493875 : Blo 2157435 2493875 := bstep (se 1 (by rfl) ⟨1870406, by rfl⟩ : syracuseStep 2493875 = 3740813) B3740813
theorem B6650333 : Blo 2157435 6650333 := bstep (se 3 (by rfl) ⟨1246937, by rfl⟩ : syracuseStep 6650333 = 2493875) B2493875
theorem B4433555 : Blo 2157435 4433555 := bstep (se 1 (by rfl) ⟨3325166, by rfl⟩ : syracuseStep 4433555 = 6650333) B6650333
theorem B2955703 : Blo 2157435 2955703 := bstep (se 1 (by rfl) ⟨2216777, by rfl⟩ : syracuseStep 2955703 = 4433555) B4433555
theorem B3940937 : Blo 2157435 3940937 := bstep (se 2 (by rfl) ⟨1477851, by rfl⟩ : syracuseStep 3940937 = 2955703) B2955703
theorem B42036661 : Blo 2157435 42036661 := bstep (se 5 (by rfl) ⟨1970468, by rfl⟩ : syracuseStep 42036661 = 3940937) B3940937
theorem B56048881 : Blo 2157435 56048881 := bstep (se 2 (by rfl) ⟨21018330, by rfl⟩ : syracuseStep 56048881 = 42036661) B42036661
theorem B74731841 : Blo 2157435 74731841 := bstep (se 2 (by rfl) ⟨28024440, by rfl⟩ : syracuseStep 74731841 = 56048881) B56048881
theorem B49821227 : Blo 2157435 49821227 := bstep (se 1 (by rfl) ⟨37365920, by rfl⟩ : syracuseStep 49821227 = 74731841) B74731841
theorem B33214151 : Blo 2157435 33214151 := bstep (se 1 (by rfl) ⟨24910613, by rfl⟩ : syracuseStep 33214151 = 49821227) B49821227
theorem B22142767 : Blo 2157435 22142767 := bstep (se 1 (by rfl) ⟨16607075, by rfl⟩ : syracuseStep 22142767 = 33214151) B33214151
theorem B29523689 : Blo 2157435 29523689 := bstep (se 2 (by rfl) ⟨11071383, by rfl⟩ : syracuseStep 29523689 = 22142767) B22142767
theorem B19682459 : Blo 2157435 19682459 := bstep (se 1 (by rfl) ⟨14761844, by rfl⟩ : syracuseStep 19682459 = 29523689) B29523689
theorem B13121639 : Blo 2157435 13121639 := bstep (se 1 (by rfl) ⟨9841229, by rfl⟩ : syracuseStep 13121639 = 19682459) B19682459
theorem B8747759 : Blo 2157435 8747759 := bstep (se 1 (by rfl) ⟨6560819, by rfl⟩ : syracuseStep 8747759 = 13121639) B13121639
theorem B5831839 : Blo 2157435 5831839 := bstep (se 1 (by rfl) ⟨4373879, by rfl⟩ : syracuseStep 5831839 = 8747759) B8747759
theorem B7775785 : Blo 2157435 7775785 := bstep (se 2 (by rfl) ⟨2915919, by rfl⟩ : syracuseStep 7775785 = 5831839) B5831839
theorem B10367713 : Blo 2157435 10367713 := bstep (se 2 (by rfl) ⟨3887892, by rfl⟩ : syracuseStep 10367713 = 7775785) B7775785
theorem B13823617 : Blo 2157435 13823617 := bstep (se 2 (by rfl) ⟨5183856, by rfl⟩ : syracuseStep 13823617 = 10367713) B10367713
theorem B18431489 : Blo 2157435 18431489 := bstep (se 2 (by rfl) ⟨6911808, by rfl⟩ : syracuseStep 18431489 = 13823617) B13823617
theorem B12287659 : Blo 2157435 12287659 := bstep (se 1 (by rfl) ⟨9215744, by rfl⟩ : syracuseStep 12287659 = 18431489) B18431489
theorem B16383545 : Blo 2157435 16383545 := bstep (se 2 (by rfl) ⟨6143829, by rfl⟩ : syracuseStep 16383545 = 12287659) B12287659
theorem B10922363 : Blo 2157435 10922363 := bstep (se 1 (by rfl) ⟨8191772, by rfl⟩ : syracuseStep 10922363 = 16383545) B16383545
theorem B7281575 : Blo 2157435 7281575 := bstep (se 1 (by rfl) ⟨5461181, by rfl⟩ : syracuseStep 7281575 = 10922363) B10922363
theorem B4854383 : Blo 2157435 4854383 := bstep (se 1 (by rfl) ⟨3640787, by rfl⟩ : syracuseStep 4854383 = 7281575) B7281575
theorem B3236255 : Blo 2157435 3236255 := bstep (se 1 (by rfl) ⟨2427191, by rfl⟩ : syracuseStep 3236255 = 4854383) B4854383
theorem B2157503 : Blo 2157435 2157503 := bstep (se 1 (by rfl) ⟨1618127, by rfl⟩ : syracuseStep 2157503 = 3236255) B3236255
theorem B3236261 : Blo 2157435 3236261 := bbase (se 4 (by rfl) ⟨303399, by rfl⟩ : syracuseStep 3236261 = 606799) (by norm_num)
theorem B2157507 : Blo 2157435 2157507 := bstep (se 1 (by rfl) ⟨1618130, by rfl⟩ : syracuseStep 2157507 = 3236261) B3236261
theorem B2730601 : Blo 2157435 2730601 := bbase (se 2 (by rfl) ⟨1023975, by rfl⟩ : syracuseStep 2730601 = 2047951) (by norm_num)
theorem B3640801 : Blo 2157435 3640801 := bstep (se 2 (by rfl) ⟨1365300, by rfl⟩ : syracuseStep 3640801 = 2730601) B2730601
theorem B4854401 : Blo 2157435 4854401 := bstep (se 2 (by rfl) ⟨1820400, by rfl⟩ : syracuseStep 4854401 = 3640801) B3640801
theorem B3236267 : Blo 2157435 3236267 := bstep (se 1 (by rfl) ⟨2427200, by rfl⟩ : syracuseStep 3236267 = 4854401) B4854401
theorem B2157511 : Blo 2157435 2157511 := bstep (se 1 (by rfl) ⟨1618133, by rfl⟩ : syracuseStep 2157511 = 3236267) B3236267
theorem B2427205 : Blo 2157435 2427205 := bbase (se 4 (by rfl) ⟨227550, by rfl⟩ : syracuseStep 2427205 = 455101) (by norm_num)
theorem B3236273 : Blo 2157435 3236273 := bstep (se 2 (by rfl) ⟨1213602, by rfl⟩ : syracuseStep 3236273 = 2427205) B2427205
theorem B2157515 : Blo 2157435 2157515 := bstep (se 1 (by rfl) ⟨1618136, by rfl⟩ : syracuseStep 2157515 = 3236273) B3236273
theorem B4095917 : Blo 2157435 4095917 := bbase (se 3 (by rfl) ⟨767984, by rfl⟩ : syracuseStep 4095917 = 1535969) (by norm_num)
theorem B2730611 : Blo 2157435 2730611 := bstep (se 1 (by rfl) ⟨2047958, by rfl⟩ : syracuseStep 2730611 = 4095917) B4095917
theorem B7281629 : Blo 2157435 7281629 := bstep (se 3 (by rfl) ⟨1365305, by rfl⟩ : syracuseStep 7281629 = 2730611) B2730611
theorem B4854419 : Blo 2157435 4854419 := bstep (se 1 (by rfl) ⟨3640814, by rfl⟩ : syracuseStep 4854419 = 7281629) B7281629
theorem B3236279 : Blo 2157435 3236279 := bstep (se 1 (by rfl) ⟨2427209, by rfl⟩ : syracuseStep 3236279 = 4854419) B4854419
theorem B2157519 : Blo 2157435 2157519 := bstep (se 1 (by rfl) ⟨1618139, by rfl⟩ : syracuseStep 2157519 = 3236279) B3236279
theorem B3236285 : Blo 2157435 3236285 := bbase (se 3 (by rfl) ⟨606803, by rfl⟩ : syracuseStep 3236285 = 1213607) (by norm_num)
theorem B2157523 : Blo 2157435 2157523 := bstep (se 1 (by rfl) ⟨1618142, by rfl⟩ : syracuseStep 2157523 = 3236285) B3236285
theorem B4854437 : Blo 2157435 4854437 := bbase (se 4 (by rfl) ⟨455103, by rfl⟩ : syracuseStep 4854437 = 910207) (by norm_num)
theorem B3236291 : Blo 2157435 3236291 := bstep (se 1 (by rfl) ⟨2427218, by rfl⟩ : syracuseStep 3236291 = 4854437) B4854437
theorem B2157527 : Blo 2157435 2157527 := bstep (se 1 (by rfl) ⟨1618145, by rfl⟩ : syracuseStep 2157527 = 3236291) B3236291
theorem B5461253 : Blo 2157435 5461253 := bbase (se 4 (by rfl) ⟨511992, by rfl⟩ : syracuseStep 5461253 = 1023985) (by norm_num)
theorem B3640835 : Blo 2157435 3640835 := bstep (se 1 (by rfl) ⟨2730626, by rfl⟩ : syracuseStep 3640835 = 5461253) B5461253
theorem B2427223 : Blo 2157435 2427223 := bstep (se 1 (by rfl) ⟨1820417, by rfl⟩ : syracuseStep 2427223 = 3640835) B3640835
theorem B3236297 : Blo 2157435 3236297 := bstep (se 2 (by rfl) ⟨1213611, by rfl⟩ : syracuseStep 3236297 = 2427223) B2427223
theorem B2157531 : Blo 2157435 2157531 := bstep (se 1 (by rfl) ⟨1618148, by rfl⟩ : syracuseStep 2157531 = 3236297) B3236297
theorem B4607941 : Blo 2157435 4607941 := bbase (se 4 (by rfl) ⟨431994, by rfl⟩ : syracuseStep 4607941 = 863989) (by norm_num)
theorem B6143921 : Blo 2157435 6143921 := bstep (se 2 (by rfl) ⟨2303970, by rfl⟩ : syracuseStep 6143921 = 4607941) B4607941
theorem B4095947 : Blo 2157435 4095947 := bstep (se 1 (by rfl) ⟨3071960, by rfl⟩ : syracuseStep 4095947 = 6143921) B6143921
theorem B10922525 : Blo 2157435 10922525 := bstep (se 3 (by rfl) ⟨2047973, by rfl⟩ : syracuseStep 10922525 = 4095947) B4095947
theorem B7281683 : Blo 2157435 7281683 := bstep (se 1 (by rfl) ⟨5461262, by rfl⟩ : syracuseStep 7281683 = 10922525) B10922525
theorem B4854455 : Blo 2157435 4854455 := bstep (se 1 (by rfl) ⟨3640841, by rfl⟩ : syracuseStep 4854455 = 7281683) B7281683
theorem B3236303 : Blo 2157435 3236303 := bstep (se 1 (by rfl) ⟨2427227, by rfl⟩ : syracuseStep 3236303 = 4854455) B4854455
theorem B2157535 : Blo 2157435 2157535 := bstep (se 1 (by rfl) ⟨1618151, by rfl⟩ : syracuseStep 2157535 = 3236303) B3236303
theorem B3236309 : Blo 2157435 3236309 := bbase (se 7 (by rfl) ⟨37925, by rfl⟩ : syracuseStep 3236309 = 75851) (by norm_num)
theorem B2157539 : Blo 2157435 2157539 := bstep (se 1 (by rfl) ⟨1618154, by rfl⟩ : syracuseStep 2157539 = 3236309) B3236309
theorem B8191925 : Blo 2157435 8191925 := bbase (se 5 (by rfl) ⟨383996, by rfl⟩ : syracuseStep 8191925 = 767993) (by norm_num)
theorem B5461283 : Blo 2157435 5461283 := bstep (se 1 (by rfl) ⟨4095962, by rfl⟩ : syracuseStep 5461283 = 8191925) B8191925
theorem B3640855 : Blo 2157435 3640855 := bstep (se 1 (by rfl) ⟨2730641, by rfl⟩ : syracuseStep 3640855 = 5461283) B5461283
theorem B4854473 : Blo 2157435 4854473 := bstep (se 2 (by rfl) ⟨1820427, by rfl⟩ : syracuseStep 4854473 = 3640855) B3640855
theorem B3236315 : Blo 2157435 3236315 := bstep (se 1 (by rfl) ⟨2427236, by rfl⟩ : syracuseStep 3236315 = 4854473) B4854473
theorem B2157543 : Blo 2157435 2157543 := bstep (se 1 (by rfl) ⟨1618157, by rfl⟩ : syracuseStep 2157543 = 3236315) B3236315
theorem B2427241 : Blo 2157435 2427241 := bbase (se 2 (by rfl) ⟨910215, by rfl⟩ : syracuseStep 2427241 = 1820431) (by norm_num)
theorem B3236321 : Blo 2157435 3236321 := bstep (se 2 (by rfl) ⟨1213620, by rfl⟩ : syracuseStep 3236321 = 2427241) B2427241
theorem B2157547 : Blo 2157435 2157547 := bstep (se 1 (by rfl) ⟨1618160, by rfl⟩ : syracuseStep 2157547 = 3236321) B3236321
theorem B4920725 : Blo 2157435 4920725 := bbase (se 6 (by rfl) ⟨115329, by rfl⟩ : syracuseStep 4920725 = 230659) (by norm_num)
theorem B3280483 : Blo 2157435 3280483 := bstep (se 1 (by rfl) ⟨2460362, by rfl⟩ : syracuseStep 3280483 = 4920725) B4920725
theorem B17495909 : Blo 2157435 17495909 := bstep (se 4 (by rfl) ⟨1640241, by rfl⟩ : syracuseStep 17495909 = 3280483) B3280483
theorem B11663939 : Blo 2157435 11663939 := bstep (se 1 (by rfl) ⟨8747954, by rfl⟩ : syracuseStep 11663939 = 17495909) B17495909
theorem B7775959 : Blo 2157435 7775959 := bstep (se 1 (by rfl) ⟨5831969, by rfl⟩ : syracuseStep 7775959 = 11663939) B11663939
theorem B10367945 : Blo 2157435 10367945 := bstep (se 2 (by rfl) ⟨3887979, by rfl⟩ : syracuseStep 10367945 = 7775959) B7775959
theorem B6911963 : Blo 2157435 6911963 := bstep (se 1 (by rfl) ⟨5183972, by rfl⟩ : syracuseStep 6911963 = 10367945) B10367945
theorem B4607975 : Blo 2157435 4607975 := bstep (se 1 (by rfl) ⟨3455981, by rfl⟩ : syracuseStep 4607975 = 6911963) B6911963
theorem B12287933 : Blo 2157435 12287933 := bstep (se 3 (by rfl) ⟨2303987, by rfl⟩ : syracuseStep 12287933 = 4607975) B4607975
theorem B8191955 : Blo 2157435 8191955 := bstep (se 1 (by rfl) ⟨6143966, by rfl⟩ : syracuseStep 8191955 = 12287933) B12287933
theorem B5461303 : Blo 2157435 5461303 := bstep (se 1 (by rfl) ⟨4095977, by rfl⟩ : syracuseStep 5461303 = 8191955) B8191955
theorem B7281737 : Blo 2157435 7281737 := bstep (se 2 (by rfl) ⟨2730651, by rfl⟩ : syracuseStep 7281737 = 5461303) B5461303
theorem B4854491 : Blo 2157435 4854491 := bstep (se 1 (by rfl) ⟨3640868, by rfl⟩ : syracuseStep 4854491 = 7281737) B7281737
theorem B3236327 : Blo 2157435 3236327 := bstep (se 1 (by rfl) ⟨2427245, by rfl⟩ : syracuseStep 3236327 = 4854491) B4854491
theorem B2157551 : Blo 2157435 2157551 := bstep (se 1 (by rfl) ⟨1618163, by rfl⟩ : syracuseStep 2157551 = 3236327) B3236327
theorem B3236333 : Blo 2157435 3236333 := bbase (se 3 (by rfl) ⟨606812, by rfl⟩ : syracuseStep 3236333 = 1213625) (by norm_num)
theorem B2157555 : Blo 2157435 2157555 := bstep (se 1 (by rfl) ⟨1618166, by rfl⟩ : syracuseStep 2157555 = 3236333) B3236333
theorem B4854509 : Blo 2157435 4854509 := bbase (se 3 (by rfl) ⟨910220, by rfl⟩ : syracuseStep 4854509 = 1820441) (by norm_num)
theorem B3236339 : Blo 2157435 3236339 := bstep (se 1 (by rfl) ⟨2427254, by rfl⟩ : syracuseStep 3236339 = 4854509) B4854509
theorem B2157559 : Blo 2157435 2157559 := bstep (se 1 (by rfl) ⟨1618169, by rfl⟩ : syracuseStep 2157559 = 3236339) B3236339
theorem B2304001 : Blo 2157435 2304001 := bbase (se 2 (by rfl) ⟨864000, by rfl⟩ : syracuseStep 2304001 = 1728001) (by norm_num)
theorem B3072001 : Blo 2157435 3072001 := bstep (se 2 (by rfl) ⟨1152000, by rfl⟩ : syracuseStep 3072001 = 2304001) B2304001
theorem B4096001 : Blo 2157435 4096001 := bstep (se 2 (by rfl) ⟨1536000, by rfl⟩ : syracuseStep 4096001 = 3072001) B3072001
theorem B2730667 : Blo 2157435 2730667 := bstep (se 1 (by rfl) ⟨2048000, by rfl⟩ : syracuseStep 2730667 = 4096001) B4096001
theorem B3640889 : Blo 2157435 3640889 := bstep (se 2 (by rfl) ⟨1365333, by rfl⟩ : syracuseStep 3640889 = 2730667) B2730667
theorem B2427259 : Blo 2157435 2427259 := bstep (se 1 (by rfl) ⟨1820444, by rfl⟩ : syracuseStep 2427259 = 3640889) B3640889
theorem B3236345 : Blo 2157435 3236345 := bstep (se 2 (by rfl) ⟨1213629, by rfl⟩ : syracuseStep 3236345 = 2427259) B2427259
theorem B2157563 : Blo 2157435 2157563 := bstep (se 1 (by rfl) ⟨1618172, by rfl⟩ : syracuseStep 2157563 = 3236345) B3236345
theorem B6312805 : Blo 2157435 6312805 := bbase (se 4 (by rfl) ⟨591825, by rfl⟩ : syracuseStep 6312805 = 1183651) (by norm_num)
theorem B33668293 : Blo 2157435 33668293 := bstep (se 4 (by rfl) ⟨3156402, by rfl⟩ : syracuseStep 33668293 = 6312805) B6312805
theorem B44891057 : Blo 2157435 44891057 := bstep (se 2 (by rfl) ⟨16834146, by rfl⟩ : syracuseStep 44891057 = 33668293) B33668293
theorem B119709485 : Blo 2157435 119709485 := bstep (se 3 (by rfl) ⟨22445528, by rfl⟩ : syracuseStep 119709485 = 44891057) B44891057
theorem B79806323 : Blo 2157435 79806323 := bstep (se 1 (by rfl) ⟨59854742, by rfl⟩ : syracuseStep 79806323 = 119709485) B119709485
theorem B53204215 : Blo 2157435 53204215 := bstep (se 1 (by rfl) ⟨39903161, by rfl⟩ : syracuseStep 53204215 = 79806323) B79806323
theorem B70938953 : Blo 2157435 70938953 := bstep (se 2 (by rfl) ⟨26602107, by rfl⟩ : syracuseStep 70938953 = 53204215) B53204215
theorem B47292635 : Blo 2157435 47292635 := bstep (se 1 (by rfl) ⟨35469476, by rfl⟩ : syracuseStep 47292635 = 70938953) B70938953
theorem B31528423 : Blo 2157435 31528423 := bstep (se 1 (by rfl) ⟨23646317, by rfl⟩ : syracuseStep 31528423 = 47292635) B47292635
theorem B168151589 : Blo 2157435 168151589 := bstep (se 4 (by rfl) ⟨15764211, by rfl⟩ : syracuseStep 168151589 = 31528423) B31528423
theorem B112101059 : Blo 2157435 112101059 := bstep (se 1 (by rfl) ⟨84075794, by rfl⟩ : syracuseStep 112101059 = 168151589) B168151589
theorem B74734039 : Blo 2157435 74734039 := bstep (se 1 (by rfl) ⟨56050529, by rfl⟩ : syracuseStep 74734039 = 112101059) B112101059
theorem B99645385 : Blo 2157435 99645385 := bstep (se 2 (by rfl) ⟨37367019, by rfl⟩ : syracuseStep 99645385 = 74734039) B74734039
theorem B132860513 : Blo 2157435 132860513 := bstep (se 2 (by rfl) ⟨49822692, by rfl⟩ : syracuseStep 132860513 = 99645385) B99645385
theorem B88573675 : Blo 2157435 88573675 := bstep (se 1 (by rfl) ⟨66430256, by rfl⟩ : syracuseStep 88573675 = 132860513) B132860513
theorem B118098233 : Blo 2157435 118098233 := bstep (se 2 (by rfl) ⟨44286837, by rfl⟩ : syracuseStep 118098233 = 88573675) B88573675
theorem B78732155 : Blo 2157435 78732155 := bstep (se 1 (by rfl) ⟨59049116, by rfl⟩ : syracuseStep 78732155 = 118098233) B118098233
theorem B52488103 : Blo 2157435 52488103 := bstep (se 1 (by rfl) ⟨39366077, by rfl⟩ : syracuseStep 52488103 = 78732155) B78732155
theorem B69984137 : Blo 2157435 69984137 := bstep (se 2 (by rfl) ⟨26244051, by rfl⟩ : syracuseStep 69984137 = 52488103) B52488103
theorem B46656091 : Blo 2157435 46656091 := bstep (se 1 (by rfl) ⟨34992068, by rfl⟩ : syracuseStep 46656091 = 69984137) B69984137
theorem B62208121 : Blo 2157435 62208121 := bstep (se 2 (by rfl) ⟨23328045, by rfl⟩ : syracuseStep 62208121 = 46656091) B46656091
theorem B82944161 : Blo 2157435 82944161 := bstep (se 2 (by rfl) ⟨31104060, by rfl⟩ : syracuseStep 82944161 = 62208121) B62208121
theorem B55296107 : Blo 2157435 55296107 := bstep (se 1 (by rfl) ⟨41472080, by rfl⟩ : syracuseStep 55296107 = 82944161) B82944161
theorem B36864071 : Blo 2157435 36864071 := bstep (se 1 (by rfl) ⟨27648053, by rfl⟩ : syracuseStep 36864071 = 55296107) B55296107
theorem B24576047 : Blo 2157435 24576047 := bstep (se 1 (by rfl) ⟨18432035, by rfl⟩ : syracuseStep 24576047 = 36864071) B36864071
theorem B16384031 : Blo 2157435 16384031 := bstep (se 1 (by rfl) ⟨12288023, by rfl⟩ : syracuseStep 16384031 = 24576047) B24576047
theorem B10922687 : Blo 2157435 10922687 := bstep (se 1 (by rfl) ⟨8192015, by rfl⟩ : syracuseStep 10922687 = 16384031) B16384031
theorem B7281791 : Blo 2157435 7281791 := bstep (se 1 (by rfl) ⟨5461343, by rfl⟩ : syracuseStep 7281791 = 10922687) B10922687
theorem B4854527 : Blo 2157435 4854527 := bstep (se 1 (by rfl) ⟨3640895, by rfl⟩ : syracuseStep 4854527 = 7281791) B7281791
theorem B3236351 : Blo 2157435 3236351 := bstep (se 1 (by rfl) ⟨2427263, by rfl⟩ : syracuseStep 3236351 = 4854527) B4854527
theorem B2157567 : Blo 2157435 2157567 := bstep (se 1 (by rfl) ⟨1618175, by rfl⟩ : syracuseStep 2157567 = 3236351) B3236351
theorem B3236357 : Blo 2157435 3236357 := bbase (se 4 (by rfl) ⟨303408, by rfl⟩ : syracuseStep 3236357 = 606817) (by norm_num)
theorem B2157571 : Blo 2157435 2157571 := bstep (se 1 (by rfl) ⟨1618178, by rfl⟩ : syracuseStep 2157571 = 3236357) B3236357
theorem B3640909 : Blo 2157435 3640909 := bbase (se 3 (by rfl) ⟨682670, by rfl⟩ : syracuseStep 3640909 = 1365341) (by norm_num)
theorem B4854545 : Blo 2157435 4854545 := bstep (se 2 (by rfl) ⟨1820454, by rfl⟩ : syracuseStep 4854545 = 3640909) B3640909
theorem B3236363 : Blo 2157435 3236363 := bstep (se 1 (by rfl) ⟨2427272, by rfl⟩ : syracuseStep 3236363 = 4854545) B4854545
theorem B2157575 : Blo 2157435 2157575 := bstep (se 1 (by rfl) ⟨1618181, by rfl⟩ : syracuseStep 2157575 = 3236363) B3236363
theorem B2427277 : Blo 2157435 2427277 := bbase (se 3 (by rfl) ⟨455114, by rfl⟩ : syracuseStep 2427277 = 910229) (by norm_num)
theorem B3236369 : Blo 2157435 3236369 := bstep (se 2 (by rfl) ⟨1213638, by rfl⟩ : syracuseStep 3236369 = 2427277) B2427277
theorem B2157579 : Blo 2157435 2157579 := bstep (se 1 (by rfl) ⟨1618184, by rfl⟩ : syracuseStep 2157579 = 3236369) B3236369
theorem B7281845 : Blo 2157435 7281845 := bbase (se 5 (by rfl) ⟨341336, by rfl⟩ : syracuseStep 7281845 = 682673) (by norm_num)
theorem B4854563 : Blo 2157435 4854563 := bstep (se 1 (by rfl) ⟨3640922, by rfl⟩ : syracuseStep 4854563 = 7281845) B7281845
theorem B3236375 : Blo 2157435 3236375 := bstep (se 1 (by rfl) ⟨2427281, by rfl⟩ : syracuseStep 3236375 = 4854563) B4854563
theorem B2157583 : Blo 2157435 2157583 := bstep (se 1 (by rfl) ⟨1618187, by rfl⟩ : syracuseStep 2157583 = 3236375) B3236375
theorem B3236381 : Blo 2157435 3236381 := bbase (se 3 (by rfl) ⟨606821, by rfl⟩ : syracuseStep 3236381 = 1213643) (by norm_num)
theorem B2157587 : Blo 2157435 2157587 := bstep (se 1 (by rfl) ⟨1618190, by rfl⟩ : syracuseStep 2157587 = 3236381) B3236381
theorem B4854581 : Blo 2157435 4854581 := bbase (se 5 (by rfl) ⟨227558, by rfl⟩ : syracuseStep 4854581 = 455117) (by norm_num)
theorem B3236387 : Blo 2157435 3236387 := bstep (se 1 (by rfl) ⟨2427290, by rfl⟩ : syracuseStep 3236387 = 4854581) B4854581
theorem B2157591 : Blo 2157435 2157591 := bstep (se 1 (by rfl) ⟨1618193, by rfl⟩ : syracuseStep 2157591 = 3236387) B3236387
theorem B2460413 : Blo 2157435 2460413 := bbase (se 3 (by rfl) ⟨461327, by rfl⟩ : syracuseStep 2460413 = 922655) (by norm_num)
theorem B6561101 : Blo 2157435 6561101 := bstep (se 3 (by rfl) ⟨1230206, by rfl⟩ : syracuseStep 6561101 = 2460413) B2460413
theorem B4374067 : Blo 2157435 4374067 := bstep (se 1 (by rfl) ⟨3280550, by rfl⟩ : syracuseStep 4374067 = 6561101) B6561101
theorem B5832089 : Blo 2157435 5832089 := bstep (se 2 (by rfl) ⟨2187033, by rfl⟩ : syracuseStep 5832089 = 4374067) B4374067
theorem B3888059 : Blo 2157435 3888059 := bstep (se 1 (by rfl) ⟨2916044, by rfl⟩ : syracuseStep 3888059 = 5832089) B5832089
theorem B10368157 : Blo 2157435 10368157 := bstep (se 3 (by rfl) ⟨1944029, by rfl⟩ : syracuseStep 10368157 = 3888059) B3888059
theorem B13824209 : Blo 2157435 13824209 := bstep (se 2 (by rfl) ⟨5184078, by rfl⟩ : syracuseStep 13824209 = 10368157) B10368157
theorem B9216139 : Blo 2157435 9216139 := bstep (se 1 (by rfl) ⟨6912104, by rfl⟩ : syracuseStep 9216139 = 13824209) B13824209
theorem B12288185 : Blo 2157435 12288185 := bstep (se 2 (by rfl) ⟨4608069, by rfl⟩ : syracuseStep 12288185 = 9216139) B9216139
theorem B8192123 : Blo 2157435 8192123 := bstep (se 1 (by rfl) ⟨6144092, by rfl⟩ : syracuseStep 8192123 = 12288185) B12288185
theorem B5461415 : Blo 2157435 5461415 := bstep (se 1 (by rfl) ⟨4096061, by rfl⟩ : syracuseStep 5461415 = 8192123) B8192123
theorem B3640943 : Blo 2157435 3640943 := bstep (se 1 (by rfl) ⟨2730707, by rfl⟩ : syracuseStep 3640943 = 5461415) B5461415
theorem B2427295 : Blo 2157435 2427295 := bstep (se 1 (by rfl) ⟨1820471, by rfl⟩ : syracuseStep 2427295 = 3640943) B3640943
theorem B3236393 : Blo 2157435 3236393 := bstep (se 2 (by rfl) ⟨1213647, by rfl⟩ : syracuseStep 3236393 = 2427295) B2427295
theorem B2157595 : Blo 2157435 2157595 := bstep (se 1 (by rfl) ⟨1618196, by rfl⟩ : syracuseStep 2157595 = 3236393) B3236393
theorem B2767969 : Blo 2157435 2767969 := bbase (se 2 (by rfl) ⟨1037988, by rfl⟩ : syracuseStep 2767969 = 2075977) (by norm_num)
theorem B14762501 : Blo 2157435 14762501 := bstep (se 4 (by rfl) ⟨1383984, by rfl⟩ : syracuseStep 14762501 = 2767969) B2767969
theorem B9841667 : Blo 2157435 9841667 := bstep (se 1 (by rfl) ⟨7381250, by rfl⟩ : syracuseStep 9841667 = 14762501) B14762501
theorem B26244445 : Blo 2157435 26244445 := bstep (se 3 (by rfl) ⟨4920833, by rfl⟩ : syracuseStep 26244445 = 9841667) B9841667
theorem B34992593 : Blo 2157435 34992593 := bstep (se 2 (by rfl) ⟨13122222, by rfl⟩ : syracuseStep 34992593 = 26244445) B26244445
theorem B23328395 : Blo 2157435 23328395 := bstep (se 1 (by rfl) ⟨17496296, by rfl⟩ : syracuseStep 23328395 = 34992593) B34992593
theorem B15552263 : Blo 2157435 15552263 := bstep (se 1 (by rfl) ⟨11664197, by rfl⟩ : syracuseStep 15552263 = 23328395) B23328395
theorem B10368175 : Blo 2157435 10368175 := bstep (se 1 (by rfl) ⟨7776131, by rfl⟩ : syracuseStep 10368175 = 15552263) B15552263
theorem B13824233 : Blo 2157435 13824233 := bstep (se 2 (by rfl) ⟨5184087, by rfl⟩ : syracuseStep 13824233 = 10368175) B10368175
theorem B9216155 : Blo 2157435 9216155 := bstep (se 1 (by rfl) ⟨6912116, by rfl⟩ : syracuseStep 9216155 = 13824233) B13824233
theorem B6144103 : Blo 2157435 6144103 := bstep (se 1 (by rfl) ⟨4608077, by rfl⟩ : syracuseStep 6144103 = 9216155) B9216155
theorem B8192137 : Blo 2157435 8192137 := bstep (se 2 (by rfl) ⟨3072051, by rfl⟩ : syracuseStep 8192137 = 6144103) B6144103
theorem B10922849 : Blo 2157435 10922849 := bstep (se 2 (by rfl) ⟨4096068, by rfl⟩ : syracuseStep 10922849 = 8192137) B8192137
theorem B7281899 : Blo 2157435 7281899 := bstep (se 1 (by rfl) ⟨5461424, by rfl⟩ : syracuseStep 7281899 = 10922849) B10922849
theorem B4854599 : Blo 2157435 4854599 := bstep (se 1 (by rfl) ⟨3640949, by rfl⟩ : syracuseStep 4854599 = 7281899) B7281899
theorem B3236399 : Blo 2157435 3236399 := bstep (se 1 (by rfl) ⟨2427299, by rfl⟩ : syracuseStep 3236399 = 4854599) B4854599
theorem B2157599 : Blo 2157435 2157599 := bstep (se 1 (by rfl) ⟨1618199, by rfl⟩ : syracuseStep 2157599 = 3236399) B3236399
theorem B3236405 : Blo 2157435 3236405 := bbase (se 5 (by rfl) ⟨151706, by rfl⟩ : syracuseStep 3236405 = 303413) (by norm_num)
theorem B2157603 : Blo 2157435 2157603 := bstep (se 1 (by rfl) ⟨1618202, by rfl⟩ : syracuseStep 2157603 = 3236405) B3236405
theorem B5461445 : Blo 2157435 5461445 := bbase (se 4 (by rfl) ⟨512010, by rfl⟩ : syracuseStep 5461445 = 1024021) (by norm_num)
theorem B3640963 : Blo 2157435 3640963 := bstep (se 1 (by rfl) ⟨2730722, by rfl⟩ : syracuseStep 3640963 = 5461445) B5461445
theorem B4854617 : Blo 2157435 4854617 := bstep (se 2 (by rfl) ⟨1820481, by rfl⟩ : syracuseStep 4854617 = 3640963) B3640963
theorem B3236411 : Blo 2157435 3236411 := bstep (se 1 (by rfl) ⟨2427308, by rfl⟩ : syracuseStep 3236411 = 4854617) B4854617
theorem B2157607 : Blo 2157435 2157607 := bstep (se 1 (by rfl) ⟨1618205, by rfl⟩ : syracuseStep 2157607 = 3236411) B3236411
theorem B2427313 : Blo 2157435 2427313 := bbase (se 2 (by rfl) ⟨910242, by rfl⟩ : syracuseStep 2427313 = 1820485) (by norm_num)
theorem B3236417 : Blo 2157435 3236417 := bstep (se 2 (by rfl) ⟨1213656, by rfl⟩ : syracuseStep 3236417 = 2427313) B2427313
theorem B2157611 : Blo 2157435 2157611 := bstep (se 1 (by rfl) ⟨1618208, by rfl⟩ : syracuseStep 2157611 = 3236417) B3236417
theorem B6144149 : Blo 2157435 6144149 := bbase (se 6 (by rfl) ⟨144003, by rfl⟩ : syracuseStep 6144149 = 288007) (by norm_num)
theorem B4096099 : Blo 2157435 4096099 := bstep (se 1 (by rfl) ⟨3072074, by rfl⟩ : syracuseStep 4096099 = 6144149) B6144149
theorem B5461465 : Blo 2157435 5461465 := bstep (se 2 (by rfl) ⟨2048049, by rfl⟩ : syracuseStep 5461465 = 4096099) B4096099
theorem B7281953 : Blo 2157435 7281953 := bstep (se 2 (by rfl) ⟨2730732, by rfl⟩ : syracuseStep 7281953 = 5461465) B5461465
theorem B4854635 : Blo 2157435 4854635 := bstep (se 1 (by rfl) ⟨3640976, by rfl⟩ : syracuseStep 4854635 = 7281953) B7281953
theorem B3236423 : Blo 2157435 3236423 := bstep (se 1 (by rfl) ⟨2427317, by rfl⟩ : syracuseStep 3236423 = 4854635) B4854635
theorem B2157615 : Blo 2157435 2157615 := bstep (se 1 (by rfl) ⟨1618211, by rfl⟩ : syracuseStep 2157615 = 3236423) B3236423
theorem B3236429 : Blo 2157435 3236429 := bbase (se 3 (by rfl) ⟨606830, by rfl⟩ : syracuseStep 3236429 = 1213661) (by norm_num)
theorem B2157619 : Blo 2157435 2157619 := bstep (se 1 (by rfl) ⟨1618214, by rfl⟩ : syracuseStep 2157619 = 3236429) B3236429
theorem B4854653 : Blo 2157435 4854653 := bbase (se 3 (by rfl) ⟨910247, by rfl⟩ : syracuseStep 4854653 = 1820495) (by norm_num)
theorem B3236435 : Blo 2157435 3236435 := bstep (se 1 (by rfl) ⟨2427326, by rfl⟩ : syracuseStep 3236435 = 4854653) B4854653
theorem B2157623 : Blo 2157435 2157623 := bstep (se 1 (by rfl) ⟨1618217, by rfl⟩ : syracuseStep 2157623 = 3236435) B3236435
theorem B3640997 : Blo 2157435 3640997 := bbase (se 4 (by rfl) ⟨341343, by rfl⟩ : syracuseStep 3640997 = 682687) (by norm_num)
theorem B2427331 : Blo 2157435 2427331 := bstep (se 1 (by rfl) ⟨1820498, by rfl⟩ : syracuseStep 2427331 = 3640997) B3640997
theorem B3236441 : Blo 2157435 3236441 := bstep (se 2 (by rfl) ⟨1213665, by rfl⟩ : syracuseStep 3236441 = 2427331) B2427331
theorem B2157627 : Blo 2157435 2157627 := bstep (se 1 (by rfl) ⟨1618220, by rfl⟩ : syracuseStep 2157627 = 3236441) B3236441
theorem B2304073 : Blo 2157435 2304073 := bbase (se 2 (by rfl) ⟨864027, by rfl⟩ : syracuseStep 2304073 = 1728055) (by norm_num)
theorem B3072097 : Blo 2157435 3072097 := bstep (se 2 (by rfl) ⟨1152036, by rfl⟩ : syracuseStep 3072097 = 2304073) B2304073
theorem B16384517 : Blo 2157435 16384517 := bstep (se 4 (by rfl) ⟨1536048, by rfl⟩ : syracuseStep 16384517 = 3072097) B3072097
theorem B10923011 : Blo 2157435 10923011 := bstep (se 1 (by rfl) ⟨8192258, by rfl⟩ : syracuseStep 10923011 = 16384517) B16384517
theorem B7282007 : Blo 2157435 7282007 := bstep (se 1 (by rfl) ⟨5461505, by rfl⟩ : syracuseStep 7282007 = 10923011) B10923011
theorem B4854671 : Blo 2157435 4854671 := bstep (se 1 (by rfl) ⟨3641003, by rfl⟩ : syracuseStep 4854671 = 7282007) B7282007
theorem B3236447 : Blo 2157435 3236447 := bstep (se 1 (by rfl) ⟨2427335, by rfl⟩ : syracuseStep 3236447 = 4854671) B4854671
theorem B2157631 : Blo 2157435 2157631 := bstep (se 1 (by rfl) ⟨1618223, by rfl⟩ : syracuseStep 2157631 = 3236447) B3236447
theorem B3236453 : Blo 2157435 3236453 := bbase (se 4 (by rfl) ⟨303417, by rfl⟩ : syracuseStep 3236453 = 606835) (by norm_num)
theorem B2157635 : Blo 2157435 2157635 := bstep (se 1 (by rfl) ⟨1618226, by rfl⟩ : syracuseStep 2157635 = 3236453) B3236453
theorem B3072109 : Blo 2157435 3072109 := bbase (se 3 (by rfl) ⟨576020, by rfl⟩ : syracuseStep 3072109 = 1152041) (by norm_num)
theorem B4096145 : Blo 2157435 4096145 := bstep (se 2 (by rfl) ⟨1536054, by rfl⟩ : syracuseStep 4096145 = 3072109) B3072109
theorem B2730763 : Blo 2157435 2730763 := bstep (se 1 (by rfl) ⟨2048072, by rfl⟩ : syracuseStep 2730763 = 4096145) B4096145
theorem B3641017 : Blo 2157435 3641017 := bstep (se 2 (by rfl) ⟨1365381, by rfl⟩ : syracuseStep 3641017 = 2730763) B2730763
theorem B4854689 : Blo 2157435 4854689 := bstep (se 2 (by rfl) ⟨1820508, by rfl⟩ : syracuseStep 4854689 = 3641017) B3641017
theorem B3236459 : Blo 2157435 3236459 := bstep (se 1 (by rfl) ⟨2427344, by rfl⟩ : syracuseStep 3236459 = 4854689) B4854689
theorem B2157639 : Blo 2157435 2157639 := bstep (se 1 (by rfl) ⟨1618229, by rfl⟩ : syracuseStep 2157639 = 3236459) B3236459
theorem B2427349 : Blo 2157435 2427349 := bbase (se 7 (by rfl) ⟨28445, by rfl⟩ : syracuseStep 2427349 = 56891) (by norm_num)
theorem B3236465 : Blo 2157435 3236465 := bstep (se 2 (by rfl) ⟨1213674, by rfl⟩ : syracuseStep 3236465 = 2427349) B2427349
theorem B2157643 : Blo 2157435 2157643 := bstep (se 1 (by rfl) ⟨1618232, by rfl⟩ : syracuseStep 2157643 = 3236465) B3236465
theorem B2730773 : Blo 2157435 2730773 := bbase (se 6 (by rfl) ⟨64002, by rfl⟩ : syracuseStep 2730773 = 128005) (by norm_num)
theorem B7282061 : Blo 2157435 7282061 := bstep (se 3 (by rfl) ⟨1365386, by rfl⟩ : syracuseStep 7282061 = 2730773) B2730773
theorem B4854707 : Blo 2157435 4854707 := bstep (se 1 (by rfl) ⟨3641030, by rfl⟩ : syracuseStep 4854707 = 7282061) B7282061
theorem B3236471 : Blo 2157435 3236471 := bstep (se 1 (by rfl) ⟨2427353, by rfl⟩ : syracuseStep 3236471 = 4854707) B4854707
theorem B2157647 : Blo 2157435 2157647 := bstep (se 1 (by rfl) ⟨1618235, by rfl⟩ : syracuseStep 2157647 = 3236471) B3236471
theorem B3236477 : Blo 2157435 3236477 := bbase (se 3 (by rfl) ⟨606839, by rfl⟩ : syracuseStep 3236477 = 1213679) (by norm_num)
theorem B2157651 : Blo 2157435 2157651 := bstep (se 1 (by rfl) ⟨1618238, by rfl⟩ : syracuseStep 2157651 = 3236477) B3236477
theorem B4854725 : Blo 2157435 4854725 := bbase (se 4 (by rfl) ⟨455130, by rfl⟩ : syracuseStep 4854725 = 910261) (by norm_num)
theorem B3236483 : Blo 2157435 3236483 := bstep (se 1 (by rfl) ⟨2427362, by rfl⟩ : syracuseStep 3236483 = 4854725) B4854725
theorem B2157655 : Blo 2157435 2157655 := bstep (se 1 (by rfl) ⟨1618241, by rfl⟩ : syracuseStep 2157655 = 3236483) B3236483
theorem B9976229 : Blo 2157435 9976229 := bbase (se 4 (by rfl) ⟨935271, by rfl⟩ : syracuseStep 9976229 = 1870543) (by norm_num)
theorem B6650819 : Blo 2157435 6650819 := bstep (se 1 (by rfl) ⟨4988114, by rfl⟩ : syracuseStep 6650819 = 9976229) B9976229
theorem B4433879 : Blo 2157435 4433879 := bstep (se 1 (by rfl) ⟨3325409, by rfl⟩ : syracuseStep 4433879 = 6650819) B6650819
theorem B2955919 : Blo 2157435 2955919 := bstep (se 1 (by rfl) ⟨2216939, by rfl⟩ : syracuseStep 2955919 = 4433879) B4433879
theorem B3941225 : Blo 2157435 3941225 := bstep (se 2 (by rfl) ⟨1477959, by rfl⟩ : syracuseStep 3941225 = 2955919) B2955919
theorem B2627483 : Blo 2157435 2627483 := bstep (se 1 (by rfl) ⟨1970612, by rfl⟩ : syracuseStep 2627483 = 3941225) B3941225
theorem B7006621 : Blo 2157435 7006621 := bstep (se 3 (by rfl) ⟨1313741, by rfl⟩ : syracuseStep 7006621 = 2627483) B2627483
theorem B9342161 : Blo 2157435 9342161 := bstep (se 2 (by rfl) ⟨3503310, by rfl⟩ : syracuseStep 9342161 = 7006621) B7006621
theorem B6228107 : Blo 2157435 6228107 := bstep (se 1 (by rfl) ⟨4671080, by rfl⟩ : syracuseStep 6228107 = 9342161) B9342161
theorem B4152071 : Blo 2157435 4152071 := bstep (se 1 (by rfl) ⟨3114053, by rfl⟩ : syracuseStep 4152071 = 6228107) B6228107
theorem B11072189 : Blo 2157435 11072189 := bstep (se 3 (by rfl) ⟨2076035, by rfl⟩ : syracuseStep 11072189 = 4152071) B4152071
theorem B7381459 : Blo 2157435 7381459 := bstep (se 1 (by rfl) ⟨5536094, by rfl⟩ : syracuseStep 7381459 = 11072189) B11072189
theorem B9841945 : Blo 2157435 9841945 := bstep (se 2 (by rfl) ⟨3690729, by rfl⟩ : syracuseStep 9841945 = 7381459) B7381459
theorem B13122593 : Blo 2157435 13122593 := bstep (se 2 (by rfl) ⟨4920972, by rfl⟩ : syracuseStep 13122593 = 9841945) B9841945
theorem B8748395 : Blo 2157435 8748395 := bstep (se 1 (by rfl) ⟨6561296, by rfl⟩ : syracuseStep 8748395 = 13122593) B13122593
theorem B5832263 : Blo 2157435 5832263 := bstep (se 1 (by rfl) ⟨4374197, by rfl⟩ : syracuseStep 5832263 = 8748395) B8748395
theorem B3888175 : Blo 2157435 3888175 := bstep (se 1 (by rfl) ⟨2916131, by rfl⟩ : syracuseStep 3888175 = 5832263) B5832263
theorem B5184233 : Blo 2157435 5184233 := bstep (se 2 (by rfl) ⟨1944087, by rfl⟩ : syracuseStep 5184233 = 3888175) B3888175
theorem B3456155 : Blo 2157435 3456155 := bstep (se 1 (by rfl) ⟨2592116, by rfl⟩ : syracuseStep 3456155 = 5184233) B5184233
theorem B9216413 : Blo 2157435 9216413 := bstep (se 3 (by rfl) ⟨1728077, by rfl⟩ : syracuseStep 9216413 = 3456155) B3456155
theorem B6144275 : Blo 2157435 6144275 := bstep (se 1 (by rfl) ⟨4608206, by rfl⟩ : syracuseStep 6144275 = 9216413) B9216413
theorem B4096183 : Blo 2157435 4096183 := bstep (se 1 (by rfl) ⟨3072137, by rfl⟩ : syracuseStep 4096183 = 6144275) B6144275
theorem B5461577 : Blo 2157435 5461577 := bstep (se 2 (by rfl) ⟨2048091, by rfl⟩ : syracuseStep 5461577 = 4096183) B4096183
theorem B3641051 : Blo 2157435 3641051 := bstep (se 1 (by rfl) ⟨2730788, by rfl⟩ : syracuseStep 3641051 = 5461577) B5461577
theorem B2427367 : Blo 2157435 2427367 := bstep (se 1 (by rfl) ⟨1820525, by rfl⟩ : syracuseStep 2427367 = 3641051) B3641051
theorem B3236489 : Blo 2157435 3236489 := bstep (se 2 (by rfl) ⟨1213683, by rfl⟩ : syracuseStep 3236489 = 2427367) B2427367
theorem B2157659 : Blo 2157435 2157659 := bstep (se 1 (by rfl) ⟨1618244, by rfl⟩ : syracuseStep 2157659 = 3236489) B3236489
theorem B10923173 : Blo 2157435 10923173 := bbase (se 4 (by rfl) ⟨1024047, by rfl⟩ : syracuseStep 10923173 = 2048095) (by norm_num)
theorem B7282115 : Blo 2157435 7282115 := bstep (se 1 (by rfl) ⟨5461586, by rfl⟩ : syracuseStep 7282115 = 10923173) B10923173
theorem B4854743 : Blo 2157435 4854743 := bstep (se 1 (by rfl) ⟨3641057, by rfl⟩ : syracuseStep 4854743 = 7282115) B7282115
theorem B3236495 : Blo 2157435 3236495 := bstep (se 1 (by rfl) ⟨2427371, by rfl⟩ : syracuseStep 3236495 = 4854743) B4854743
theorem B2157663 : Blo 2157435 2157663 := bstep (se 1 (by rfl) ⟨1618247, by rfl⟩ : syracuseStep 2157663 = 3236495) B3236495
theorem B3236501 : Blo 2157435 3236501 := bbase (se 6 (by rfl) ⟨75855, by rfl⟩ : syracuseStep 3236501 = 151711) (by norm_num)
theorem B2157667 : Blo 2157435 2157667 := bstep (se 1 (by rfl) ⟨1618250, by rfl⟩ : syracuseStep 2157667 = 3236501) B3236501
theorem B3690749 : Blo 2157435 3690749 := bbase (se 3 (by rfl) ⟨692015, by rfl⟩ : syracuseStep 3690749 = 1384031) (by norm_num)
theorem B2460499 : Blo 2157435 2460499 := bstep (se 1 (by rfl) ⟨1845374, by rfl⟩ : syracuseStep 2460499 = 3690749) B3690749
theorem B13122661 : Blo 2157435 13122661 := bstep (se 4 (by rfl) ⟨1230249, by rfl⟩ : syracuseStep 13122661 = 2460499) B2460499
theorem B17496881 : Blo 2157435 17496881 := bstep (se 2 (by rfl) ⟨6561330, by rfl⟩ : syracuseStep 17496881 = 13122661) B13122661
theorem B11664587 : Blo 2157435 11664587 := bstep (se 1 (by rfl) ⟨8748440, by rfl⟩ : syracuseStep 11664587 = 17496881) B17496881
theorem B31105565 : Blo 2157435 31105565 := bstep (se 3 (by rfl) ⟨5832293, by rfl⟩ : syracuseStep 31105565 = 11664587) B11664587
theorem B20737043 : Blo 2157435 20737043 := bstep (se 1 (by rfl) ⟨15552782, by rfl⟩ : syracuseStep 20737043 = 31105565) B31105565
theorem B13824695 : Blo 2157435 13824695 := bstep (se 1 (by rfl) ⟨10368521, by rfl⟩ : syracuseStep 13824695 = 20737043) B20737043
theorem B9216463 : Blo 2157435 9216463 := bstep (se 1 (by rfl) ⟨6912347, by rfl⟩ : syracuseStep 9216463 = 13824695) B13824695
theorem B12288617 : Blo 2157435 12288617 := bstep (se 2 (by rfl) ⟨4608231, by rfl⟩ : syracuseStep 12288617 = 9216463) B9216463
theorem B8192411 : Blo 2157435 8192411 := bstep (se 1 (by rfl) ⟨6144308, by rfl⟩ : syracuseStep 8192411 = 12288617) B12288617
theorem B5461607 : Blo 2157435 5461607 := bstep (se 1 (by rfl) ⟨4096205, by rfl⟩ : syracuseStep 5461607 = 8192411) B8192411
theorem B3641071 : Blo 2157435 3641071 := bstep (se 1 (by rfl) ⟨2730803, by rfl⟩ : syracuseStep 3641071 = 5461607) B5461607
theorem B4854761 : Blo 2157435 4854761 := bstep (se 2 (by rfl) ⟨1820535, by rfl⟩ : syracuseStep 4854761 = 3641071) B3641071
theorem B3236507 : Blo 2157435 3236507 := bstep (se 1 (by rfl) ⟨2427380, by rfl⟩ : syracuseStep 3236507 = 4854761) B4854761
theorem B2157671 : Blo 2157435 2157671 := bstep (se 1 (by rfl) ⟨1618253, by rfl⟩ : syracuseStep 2157671 = 3236507) B3236507
theorem B2427385 : Blo 2157435 2427385 := bbase (se 2 (by rfl) ⟨910269, by rfl⟩ : syracuseStep 2427385 = 1820539) (by norm_num)
theorem B3236513 : Blo 2157435 3236513 := bstep (se 2 (by rfl) ⟨1213692, by rfl⟩ : syracuseStep 3236513 = 2427385) B2427385
theorem B2157675 : Blo 2157435 2157675 := bstep (se 1 (by rfl) ⟨1618256, by rfl⟩ : syracuseStep 2157675 = 3236513) B3236513
theorem B6912373 : Blo 2157435 6912373 := bbase (se 5 (by rfl) ⟨324017, by rfl⟩ : syracuseStep 6912373 = 648035) (by norm_num)
theorem B9216497 : Blo 2157435 9216497 := bstep (se 2 (by rfl) ⟨3456186, by rfl⟩ : syracuseStep 9216497 = 6912373) B6912373
theorem B6144331 : Blo 2157435 6144331 := bstep (se 1 (by rfl) ⟨4608248, by rfl⟩ : syracuseStep 6144331 = 9216497) B9216497
theorem B8192441 : Blo 2157435 8192441 := bstep (se 2 (by rfl) ⟨3072165, by rfl⟩ : syracuseStep 8192441 = 6144331) B6144331
theorem B5461627 : Blo 2157435 5461627 := bstep (se 1 (by rfl) ⟨4096220, by rfl⟩ : syracuseStep 5461627 = 8192441) B8192441
theorem B7282169 : Blo 2157435 7282169 := bstep (se 2 (by rfl) ⟨2730813, by rfl⟩ : syracuseStep 7282169 = 5461627) B5461627
theorem B4854779 : Blo 2157435 4854779 := bstep (se 1 (by rfl) ⟨3641084, by rfl⟩ : syracuseStep 4854779 = 7282169) B7282169
theorem B3236519 : Blo 2157435 3236519 := bstep (se 1 (by rfl) ⟨2427389, by rfl⟩ : syracuseStep 3236519 = 4854779) B4854779
theorem B2157679 : Blo 2157435 2157679 := bstep (se 1 (by rfl) ⟨1618259, by rfl⟩ : syracuseStep 2157679 = 3236519) B3236519
theorem B3236525 : Blo 2157435 3236525 := bbase (se 3 (by rfl) ⟨606848, by rfl⟩ : syracuseStep 3236525 = 1213697) (by norm_num)
theorem B2157683 : Blo 2157435 2157683 := bstep (se 1 (by rfl) ⟨1618262, by rfl⟩ : syracuseStep 2157683 = 3236525) B3236525
theorem B4854797 : Blo 2157435 4854797 := bbase (se 3 (by rfl) ⟨910274, by rfl⟩ : syracuseStep 4854797 = 1820549) (by norm_num)
theorem B3236531 : Blo 2157435 3236531 := bstep (se 1 (by rfl) ⟨2427398, by rfl⟩ : syracuseStep 3236531 = 4854797) B4854797
theorem B2157687 : Blo 2157435 2157687 := bstep (se 1 (by rfl) ⟨1618265, by rfl⟩ : syracuseStep 2157687 = 3236531) B3236531
theorem B2730829 : Blo 2157435 2730829 := bbase (se 3 (by rfl) ⟨512030, by rfl⟩ : syracuseStep 2730829 = 1024061) (by norm_num)
theorem B3641105 : Blo 2157435 3641105 := bstep (se 2 (by rfl) ⟨1365414, by rfl⟩ : syracuseStep 3641105 = 2730829) B2730829
theorem B2427403 : Blo 2157435 2427403 := bstep (se 1 (by rfl) ⟨1820552, by rfl⟩ : syracuseStep 2427403 = 3641105) B3641105
theorem B3236537 : Blo 2157435 3236537 := bstep (se 2 (by rfl) ⟨1213701, by rfl⟩ : syracuseStep 3236537 = 2427403) B2427403
theorem B2157691 : Blo 2157435 2157691 := bstep (se 1 (by rfl) ⟨1618268, by rfl⟩ : syracuseStep 2157691 = 3236537) B3236537
theorem B13122805 : Blo 2157435 13122805 := bbase (se 5 (by rfl) ⟨615131, by rfl⟩ : syracuseStep 13122805 = 1230263) (by norm_num)
theorem B17497073 : Blo 2157435 17497073 := bstep (se 2 (by rfl) ⟨6561402, by rfl⟩ : syracuseStep 17497073 = 13122805) B13122805
theorem B46658861 : Blo 2157435 46658861 := bstep (se 3 (by rfl) ⟨8748536, by rfl⟩ : syracuseStep 46658861 = 17497073) B17497073
theorem B31105907 : Blo 2157435 31105907 := bstep (se 1 (by rfl) ⟨23329430, by rfl⟩ : syracuseStep 31105907 = 46658861) B46658861
theorem B20737271 : Blo 2157435 20737271 := bstep (se 1 (by rfl) ⟨15552953, by rfl⟩ : syracuseStep 20737271 = 31105907) B31105907
theorem B13824847 : Blo 2157435 13824847 := bstep (se 1 (by rfl) ⟨10368635, by rfl⟩ : syracuseStep 13824847 = 20737271) B20737271
theorem B18433129 : Blo 2157435 18433129 := bstep (se 2 (by rfl) ⟨6912423, by rfl⟩ : syracuseStep 18433129 = 13824847) B13824847
theorem B24577505 : Blo 2157435 24577505 := bstep (se 2 (by rfl) ⟨9216564, by rfl⟩ : syracuseStep 24577505 = 18433129) B18433129
theorem B16385003 : Blo 2157435 16385003 := bstep (se 1 (by rfl) ⟨12288752, by rfl⟩ : syracuseStep 16385003 = 24577505) B24577505
theorem B10923335 : Blo 2157435 10923335 := bstep (se 1 (by rfl) ⟨8192501, by rfl⟩ : syracuseStep 10923335 = 16385003) B16385003
theorem B7282223 : Blo 2157435 7282223 := bstep (se 1 (by rfl) ⟨5461667, by rfl⟩ : syracuseStep 7282223 = 10923335) B10923335
theorem B4854815 : Blo 2157435 4854815 := bstep (se 1 (by rfl) ⟨3641111, by rfl⟩ : syracuseStep 4854815 = 7282223) B7282223
theorem B3236543 : Blo 2157435 3236543 := bstep (se 1 (by rfl) ⟨2427407, by rfl⟩ : syracuseStep 3236543 = 4854815) B4854815
theorem B2157695 : Blo 2157435 2157695 := bstep (se 1 (by rfl) ⟨1618271, by rfl⟩ : syracuseStep 2157695 = 3236543) B3236543
theorem B3236549 : Blo 2157435 3236549 := bbase (se 4 (by rfl) ⟨303426, by rfl⟩ : syracuseStep 3236549 = 606853) (by norm_num)
theorem B2157699 : Blo 2157435 2157699 := bstep (se 1 (by rfl) ⟨1618274, by rfl⟩ : syracuseStep 2157699 = 3236549) B3236549
theorem B3641125 : Blo 2157435 3641125 := bbase (se 4 (by rfl) ⟨341355, by rfl⟩ : syracuseStep 3641125 = 682711) (by norm_num)
theorem B4854833 : Blo 2157435 4854833 := bstep (se 2 (by rfl) ⟨1820562, by rfl⟩ : syracuseStep 4854833 = 3641125) B3641125
theorem B3236555 : Blo 2157435 3236555 := bstep (se 1 (by rfl) ⟨2427416, by rfl⟩ : syracuseStep 3236555 = 4854833) B4854833
theorem B2157703 : Blo 2157435 2157703 := bstep (se 1 (by rfl) ⟨1618277, by rfl⟩ : syracuseStep 2157703 = 3236555) B3236555
theorem B2427421 : Blo 2157435 2427421 := bbase (se 3 (by rfl) ⟨455141, by rfl⟩ : syracuseStep 2427421 = 910283) (by norm_num)
theorem B3236561 : Blo 2157435 3236561 := bstep (se 2 (by rfl) ⟨1213710, by rfl⟩ : syracuseStep 3236561 = 2427421) B2427421
theorem B2157707 : Blo 2157435 2157707 := bstep (se 1 (by rfl) ⟨1618280, by rfl⟩ : syracuseStep 2157707 = 3236561) B3236561
theorem B7282277 : Blo 2157435 7282277 := bbase (se 4 (by rfl) ⟨682713, by rfl⟩ : syracuseStep 7282277 = 1365427) (by norm_num)
theorem B4854851 : Blo 2157435 4854851 := bstep (se 1 (by rfl) ⟨3641138, by rfl⟩ : syracuseStep 4854851 = 7282277) B7282277
theorem B3236567 : Blo 2157435 3236567 := bstep (se 1 (by rfl) ⟨2427425, by rfl⟩ : syracuseStep 3236567 = 4854851) B4854851
theorem B2157711 : Blo 2157435 2157711 := bstep (se 1 (by rfl) ⟨1618283, by rfl⟩ : syracuseStep 2157711 = 3236567) B3236567
theorem B3236573 : Blo 2157435 3236573 := bbase (se 3 (by rfl) ⟨606857, by rfl⟩ : syracuseStep 3236573 = 1213715) (by norm_num)
theorem B2157715 : Blo 2157435 2157715 := bstep (se 1 (by rfl) ⟨1618286, by rfl⟩ : syracuseStep 2157715 = 3236573) B3236573
theorem B4854869 : Blo 2157435 4854869 := bbase (se 8 (by rfl) ⟨28446, by rfl⟩ : syracuseStep 4854869 = 56893) (by norm_num)
theorem B3236579 : Blo 2157435 3236579 := bstep (se 1 (by rfl) ⟨2427434, by rfl⟩ : syracuseStep 3236579 = 4854869) B4854869
theorem B2157719 : Blo 2157435 2157719 := bstep (se 1 (by rfl) ⟨1618289, by rfl⟩ : syracuseStep 2157719 = 3236579) B3236579
theorem B10368773 : Blo 2157435 10368773 := bbase (se 4 (by rfl) ⟨972072, by rfl⟩ : syracuseStep 10368773 = 1944145) (by norm_num)
theorem B6912515 : Blo 2157435 6912515 := bstep (se 1 (by rfl) ⟨5184386, by rfl⟩ : syracuseStep 6912515 = 10368773) B10368773
theorem B4608343 : Blo 2157435 4608343 := bstep (se 1 (by rfl) ⟨3456257, by rfl⟩ : syracuseStep 4608343 = 6912515) B6912515
theorem B6144457 : Blo 2157435 6144457 := bstep (se 2 (by rfl) ⟨2304171, by rfl⟩ : syracuseStep 6144457 = 4608343) B4608343
theorem B8192609 : Blo 2157435 8192609 := bstep (se 2 (by rfl) ⟨3072228, by rfl⟩ : syracuseStep 8192609 = 6144457) B6144457
theorem B5461739 : Blo 2157435 5461739 := bstep (se 1 (by rfl) ⟨4096304, by rfl⟩ : syracuseStep 5461739 = 8192609) B8192609
theorem B3641159 : Blo 2157435 3641159 := bstep (se 1 (by rfl) ⟨2730869, by rfl⟩ : syracuseStep 3641159 = 5461739) B5461739
theorem B2427439 : Blo 2157435 2427439 := bstep (se 1 (by rfl) ⟨1820579, by rfl⟩ : syracuseStep 2427439 = 3641159) B3641159
theorem B3236585 : Blo 2157435 3236585 := bstep (se 2 (by rfl) ⟨1213719, by rfl⟩ : syracuseStep 3236585 = 2427439) B2427439
theorem B2157723 : Blo 2157435 2157723 := bstep (se 1 (by rfl) ⟨1618292, by rfl⟩ : syracuseStep 2157723 = 3236585) B3236585
theorem B17497333 : Blo 2157435 17497333 := bbase (se 5 (by rfl) ⟨820187, by rfl⟩ : syracuseStep 17497333 = 1640375) (by norm_num)
theorem B23329777 : Blo 2157435 23329777 := bstep (se 2 (by rfl) ⟨8748666, by rfl⟩ : syracuseStep 23329777 = 17497333) B17497333
theorem B31106369 : Blo 2157435 31106369 := bstep (se 2 (by rfl) ⟨11664888, by rfl⟩ : syracuseStep 31106369 = 23329777) B23329777
theorem B20737579 : Blo 2157435 20737579 := bstep (se 1 (by rfl) ⟨15553184, by rfl⟩ : syracuseStep 20737579 = 31106369) B31106369
theorem B27650105 : Blo 2157435 27650105 := bstep (se 2 (by rfl) ⟨10368789, by rfl⟩ : syracuseStep 27650105 = 20737579) B20737579
theorem B18433403 : Blo 2157435 18433403 := bstep (se 1 (by rfl) ⟨13825052, by rfl⟩ : syracuseStep 18433403 = 27650105) B27650105
theorem B12288935 : Blo 2157435 12288935 := bstep (se 1 (by rfl) ⟨9216701, by rfl⟩ : syracuseStep 12288935 = 18433403) B18433403
theorem B8192623 : Blo 2157435 8192623 := bstep (se 1 (by rfl) ⟨6144467, by rfl⟩ : syracuseStep 8192623 = 12288935) B12288935
theorem B10923497 : Blo 2157435 10923497 := bstep (se 2 (by rfl) ⟨4096311, by rfl⟩ : syracuseStep 10923497 = 8192623) B8192623
theorem B7282331 : Blo 2157435 7282331 := bstep (se 1 (by rfl) ⟨5461748, by rfl⟩ : syracuseStep 7282331 = 10923497) B10923497
theorem B4854887 : Blo 2157435 4854887 := bstep (se 1 (by rfl) ⟨3641165, by rfl⟩ : syracuseStep 4854887 = 7282331) B7282331
theorem B3236591 : Blo 2157435 3236591 := bstep (se 1 (by rfl) ⟨2427443, by rfl⟩ : syracuseStep 3236591 = 4854887) B4854887
theorem B2157727 : Blo 2157435 2157727 := bstep (se 1 (by rfl) ⟨1618295, by rfl⟩ : syracuseStep 2157727 = 3236591) B3236591
theorem B3236597 : Blo 2157435 3236597 := bbase (se 5 (by rfl) ⟨151715, by rfl⟩ : syracuseStep 3236597 = 303431) (by norm_num)
theorem B2157731 : Blo 2157435 2157731 := bstep (se 1 (by rfl) ⟨1618298, by rfl⟩ : syracuseStep 2157731 = 3236597) B3236597
theorem B29526869 : Blo 2157435 29526869 := bbase (se 9 (by rfl) ⟨86504, by rfl⟩ : syracuseStep 29526869 = 173009) (by norm_num)
theorem B19684579 : Blo 2157435 19684579 := bstep (se 1 (by rfl) ⟨14763434, by rfl⟩ : syracuseStep 19684579 = 29526869) B29526869
theorem B26246105 : Blo 2157435 26246105 := bstep (se 2 (by rfl) ⟨9842289, by rfl⟩ : syracuseStep 26246105 = 19684579) B19684579
theorem B17497403 : Blo 2157435 17497403 := bstep (se 1 (by rfl) ⟨13123052, by rfl⟩ : syracuseStep 17497403 = 26246105) B26246105
theorem B11664935 : Blo 2157435 11664935 := bstep (se 1 (by rfl) ⟨8748701, by rfl⟩ : syracuseStep 11664935 = 17497403) B17497403
theorem B7776623 : Blo 2157435 7776623 := bstep (se 1 (by rfl) ⟨5832467, by rfl⟩ : syracuseStep 7776623 = 11664935) B11664935
theorem B5184415 : Blo 2157435 5184415 := bstep (se 1 (by rfl) ⟨3888311, by rfl⟩ : syracuseStep 5184415 = 7776623) B7776623
theorem B6912553 : Blo 2157435 6912553 := bstep (se 2 (by rfl) ⟨2592207, by rfl⟩ : syracuseStep 6912553 = 5184415) B5184415
theorem B9216737 : Blo 2157435 9216737 := bstep (se 2 (by rfl) ⟨3456276, by rfl⟩ : syracuseStep 9216737 = 6912553) B6912553
theorem B6144491 : Blo 2157435 6144491 := bstep (se 1 (by rfl) ⟨4608368, by rfl⟩ : syracuseStep 6144491 = 9216737) B9216737
theorem B4096327 : Blo 2157435 4096327 := bstep (se 1 (by rfl) ⟨3072245, by rfl⟩ : syracuseStep 4096327 = 6144491) B6144491
theorem B5461769 : Blo 2157435 5461769 := bstep (se 2 (by rfl) ⟨2048163, by rfl⟩ : syracuseStep 5461769 = 4096327) B4096327
theorem B3641179 : Blo 2157435 3641179 := bstep (se 1 (by rfl) ⟨2730884, by rfl⟩ : syracuseStep 3641179 = 5461769) B5461769
theorem B4854905 : Blo 2157435 4854905 := bstep (se 2 (by rfl) ⟨1820589, by rfl⟩ : syracuseStep 4854905 = 3641179) B3641179
theorem B3236603 : Blo 2157435 3236603 := bstep (se 1 (by rfl) ⟨2427452, by rfl⟩ : syracuseStep 3236603 = 4854905) B4854905
theorem B2157735 : Blo 2157435 2157735 := bstep (se 1 (by rfl) ⟨1618301, by rfl⟩ : syracuseStep 2157735 = 3236603) B3236603
theorem B2427457 : Blo 2157435 2427457 := bbase (se 2 (by rfl) ⟨910296, by rfl⟩ : syracuseStep 2427457 = 1820593) (by norm_num)
theorem B3236609 : Blo 2157435 3236609 := bstep (se 2 (by rfl) ⟨1213728, by rfl⟩ : syracuseStep 3236609 = 2427457) B2427457
theorem B2157739 : Blo 2157435 2157739 := bstep (se 1 (by rfl) ⟨1618304, by rfl⟩ : syracuseStep 2157739 = 3236609) B3236609
theorem B5461789 : Blo 2157435 5461789 := bbase (se 3 (by rfl) ⟨1024085, by rfl⟩ : syracuseStep 5461789 = 2048171) (by norm_num)
theorem B7282385 : Blo 2157435 7282385 := bstep (se 2 (by rfl) ⟨2730894, by rfl⟩ : syracuseStep 7282385 = 5461789) B5461789
theorem B4854923 : Blo 2157435 4854923 := bstep (se 1 (by rfl) ⟨3641192, by rfl⟩ : syracuseStep 4854923 = 7282385) B7282385
theorem B3236615 : Blo 2157435 3236615 := bstep (se 1 (by rfl) ⟨2427461, by rfl⟩ : syracuseStep 3236615 = 4854923) B4854923
theorem B2157743 : Blo 2157435 2157743 := bstep (se 1 (by rfl) ⟨1618307, by rfl⟩ : syracuseStep 2157743 = 3236615) B3236615
theorem B3236621 : Blo 2157435 3236621 := bbase (se 3 (by rfl) ⟨606866, by rfl⟩ : syracuseStep 3236621 = 1213733) (by norm_num)
theorem B2157747 : Blo 2157435 2157747 := bstep (se 1 (by rfl) ⟨1618310, by rfl⟩ : syracuseStep 2157747 = 3236621) B3236621
theorem B4854941 : Blo 2157435 4854941 := bbase (se 3 (by rfl) ⟨910301, by rfl⟩ : syracuseStep 4854941 = 1820603) (by norm_num)
theorem B3236627 : Blo 2157435 3236627 := bstep (se 1 (by rfl) ⟨2427470, by rfl⟩ : syracuseStep 3236627 = 4854941) B4854941
theorem B2157751 : Blo 2157435 2157751 := bstep (se 1 (by rfl) ⟨1618313, by rfl⟩ : syracuseStep 2157751 = 3236627) B3236627
theorem B3641213 : Blo 2157435 3641213 := bbase (se 3 (by rfl) ⟨682727, by rfl⟩ : syracuseStep 3641213 = 1365455) (by norm_num)
theorem B2427475 : Blo 2157435 2427475 := bstep (se 1 (by rfl) ⟨1820606, by rfl⟩ : syracuseStep 2427475 = 3641213) B3641213
theorem B3236633 : Blo 2157435 3236633 := bstep (se 2 (by rfl) ⟨1213737, by rfl⟩ : syracuseStep 3236633 = 2427475) B2427475
theorem B2157755 : Blo 2157435 2157755 := bstep (se 1 (by rfl) ⟨1618316, by rfl⟩ : syracuseStep 2157755 = 3236633) B3236633
theorem B6912629 : Blo 2157435 6912629 := bbase (se 5 (by rfl) ⟨324029, by rfl⟩ : syracuseStep 6912629 = 648059) (by norm_num)
theorem B4608419 : Blo 2157435 4608419 := bstep (se 1 (by rfl) ⟨3456314, by rfl⟩ : syracuseStep 4608419 = 6912629) B6912629
theorem B12289117 : Blo 2157435 12289117 := bstep (se 3 (by rfl) ⟨2304209, by rfl⟩ : syracuseStep 12289117 = 4608419) B4608419
theorem B16385489 : Blo 2157435 16385489 := bstep (se 2 (by rfl) ⟨6144558, by rfl⟩ : syracuseStep 16385489 = 12289117) B12289117
theorem B10923659 : Blo 2157435 10923659 := bstep (se 1 (by rfl) ⟨8192744, by rfl⟩ : syracuseStep 10923659 = 16385489) B16385489
theorem B7282439 : Blo 2157435 7282439 := bstep (se 1 (by rfl) ⟨5461829, by rfl⟩ : syracuseStep 7282439 = 10923659) B10923659
theorem B4854959 : Blo 2157435 4854959 := bstep (se 1 (by rfl) ⟨3641219, by rfl⟩ : syracuseStep 4854959 = 7282439) B7282439
theorem B3236639 : Blo 2157435 3236639 := bstep (se 1 (by rfl) ⟨2427479, by rfl⟩ : syracuseStep 3236639 = 4854959) B4854959
theorem B2157759 : Blo 2157435 2157759 := bstep (se 1 (by rfl) ⟨1618319, by rfl⟩ : syracuseStep 2157759 = 3236639) B3236639
theorem B3236645 : Blo 2157435 3236645 := bbase (se 4 (by rfl) ⟨303435, by rfl⟩ : syracuseStep 3236645 = 606871) (by norm_num)
theorem B2157763 : Blo 2157435 2157763 := bstep (se 1 (by rfl) ⟨1618322, by rfl⟩ : syracuseStep 2157763 = 3236645) B3236645
theorem B2730925 : Blo 2157435 2730925 := bbase (se 3 (by rfl) ⟨512048, by rfl⟩ : syracuseStep 2730925 = 1024097) (by norm_num)
theorem B3641233 : Blo 2157435 3641233 := bstep (se 2 (by rfl) ⟨1365462, by rfl⟩ : syracuseStep 3641233 = 2730925) B2730925
theorem B4854977 : Blo 2157435 4854977 := bstep (se 2 (by rfl) ⟨1820616, by rfl⟩ : syracuseStep 4854977 = 3641233) B3641233
theorem B3236651 : Blo 2157435 3236651 := bstep (se 1 (by rfl) ⟨2427488, by rfl⟩ : syracuseStep 3236651 = 4854977) B4854977
theorem B2157767 : Blo 2157435 2157767 := bstep (se 1 (by rfl) ⟨1618325, by rfl⟩ : syracuseStep 2157767 = 3236651) B3236651
theorem B2427493 : Blo 2157435 2427493 := bbase (se 4 (by rfl) ⟨227577, by rfl⟩ : syracuseStep 2427493 = 455155) (by norm_num)
theorem B3236657 : Blo 2157435 3236657 := bstep (se 2 (by rfl) ⟨1213746, by rfl⟩ : syracuseStep 3236657 = 2427493) B2427493
theorem B2157771 : Blo 2157435 2157771 := bstep (se 1 (by rfl) ⟨1618328, by rfl⟩ : syracuseStep 2157771 = 3236657) B3236657
theorem B3456341 : Blo 2157435 3456341 := bbase (se 11 (by rfl) ⟨2531, by rfl⟩ : syracuseStep 3456341 = 5063) (by norm_num)
theorem B2304227 : Blo 2157435 2304227 := bstep (se 1 (by rfl) ⟨1728170, by rfl⟩ : syracuseStep 2304227 = 3456341) B3456341
theorem B6144605 : Blo 2157435 6144605 := bstep (se 3 (by rfl) ⟨1152113, by rfl⟩ : syracuseStep 6144605 = 2304227) B2304227
theorem B4096403 : Blo 2157435 4096403 := bstep (se 1 (by rfl) ⟨3072302, by rfl⟩ : syracuseStep 4096403 = 6144605) B6144605
theorem B2730935 : Blo 2157435 2730935 := bstep (se 1 (by rfl) ⟨2048201, by rfl⟩ : syracuseStep 2730935 = 4096403) B4096403
theorem B7282493 : Blo 2157435 7282493 := bstep (se 3 (by rfl) ⟨1365467, by rfl⟩ : syracuseStep 7282493 = 2730935) B2730935
theorem B4854995 : Blo 2157435 4854995 := bstep (se 1 (by rfl) ⟨3641246, by rfl⟩ : syracuseStep 4854995 = 7282493) B7282493
theorem B3236663 : Blo 2157435 3236663 := bstep (se 1 (by rfl) ⟨2427497, by rfl⟩ : syracuseStep 3236663 = 4854995) B4854995
theorem B2157775 : Blo 2157435 2157775 := bstep (se 1 (by rfl) ⟨1618331, by rfl⟩ : syracuseStep 2157775 = 3236663) B3236663
theorem B3236669 : Blo 2157435 3236669 := bbase (se 3 (by rfl) ⟨606875, by rfl⟩ : syracuseStep 3236669 = 1213751) (by norm_num)
theorem B2157779 : Blo 2157435 2157779 := bstep (se 1 (by rfl) ⟨1618334, by rfl⟩ : syracuseStep 2157779 = 3236669) B3236669
theorem B4855013 : Blo 2157435 4855013 := bbase (se 4 (by rfl) ⟨455157, by rfl⟩ : syracuseStep 4855013 = 910315) (by norm_num)
theorem B3236675 : Blo 2157435 3236675 := bstep (se 1 (by rfl) ⟨2427506, by rfl⟩ : syracuseStep 3236675 = 4855013) B4855013
theorem B2157783 : Blo 2157435 2157783 := bstep (se 1 (by rfl) ⟨1618337, by rfl⟩ : syracuseStep 2157783 = 3236675) B3236675
theorem B5461901 : Blo 2157435 5461901 := bbase (se 3 (by rfl) ⟨1024106, by rfl⟩ : syracuseStep 5461901 = 2048213) (by norm_num)
theorem B3641267 : Blo 2157435 3641267 := bstep (se 1 (by rfl) ⟨2730950, by rfl⟩ : syracuseStep 3641267 = 5461901) B5461901
theorem B2427511 : Blo 2157435 2427511 := bstep (se 1 (by rfl) ⟨1820633, by rfl⟩ : syracuseStep 2427511 = 3641267) B3641267
theorem B3236681 : Blo 2157435 3236681 := bstep (se 2 (by rfl) ⟨1213755, by rfl⟩ : syracuseStep 3236681 = 2427511) B2427511
theorem B2157787 : Blo 2157435 2157787 := bstep (se 1 (by rfl) ⟨1618340, by rfl⟩ : syracuseStep 2157787 = 3236681) B3236681
theorem B3072325 : Blo 2157435 3072325 := bbase (se 4 (by rfl) ⟨288030, by rfl⟩ : syracuseStep 3072325 = 576061) (by norm_num)
theorem B4096433 : Blo 2157435 4096433 := bstep (se 2 (by rfl) ⟨1536162, by rfl⟩ : syracuseStep 4096433 = 3072325) B3072325
theorem B10923821 : Blo 2157435 10923821 := bstep (se 3 (by rfl) ⟨2048216, by rfl⟩ : syracuseStep 10923821 = 4096433) B4096433
theorem B7282547 : Blo 2157435 7282547 := bstep (se 1 (by rfl) ⟨5461910, by rfl⟩ : syracuseStep 7282547 = 10923821) B10923821
theorem B4855031 : Blo 2157435 4855031 := bstep (se 1 (by rfl) ⟨3641273, by rfl⟩ : syracuseStep 4855031 = 7282547) B7282547
theorem B3236687 : Blo 2157435 3236687 := bstep (se 1 (by rfl) ⟨2427515, by rfl⟩ : syracuseStep 3236687 = 4855031) B4855031
theorem B2157791 : Blo 2157435 2157791 := bstep (se 1 (by rfl) ⟨1618343, by rfl⟩ : syracuseStep 2157791 = 3236687) B3236687
theorem B3236693 : Blo 2157435 3236693 := bbase (se 9 (by rfl) ⟨9482, by rfl⟩ : syracuseStep 3236693 = 18965) (by norm_num)
theorem B2157795 : Blo 2157435 2157795 := bstep (se 1 (by rfl) ⟨1618346, by rfl⟩ : syracuseStep 2157795 = 3236693) B3236693
theorem B3280861 : Blo 2157435 3280861 := bbase (se 3 (by rfl) ⟨615161, by rfl⟩ : syracuseStep 3280861 = 1230323) (by norm_num)
theorem B4374481 : Blo 2157435 4374481 := bstep (se 2 (by rfl) ⟨1640430, by rfl⟩ : syracuseStep 4374481 = 3280861) B3280861
theorem B5832641 : Blo 2157435 5832641 := bstep (se 2 (by rfl) ⟨2187240, by rfl⟩ : syracuseStep 5832641 = 4374481) B4374481
theorem B3888427 : Blo 2157435 3888427 := bstep (se 1 (by rfl) ⟨2916320, by rfl⟩ : syracuseStep 3888427 = 5832641) B5832641
theorem B5184569 : Blo 2157435 5184569 := bstep (se 2 (by rfl) ⟨1944213, by rfl⟩ : syracuseStep 5184569 = 3888427) B3888427
theorem B3456379 : Blo 2157435 3456379 := bstep (se 1 (by rfl) ⟨2592284, by rfl⟩ : syracuseStep 3456379 = 5184569) B5184569
theorem B4608505 : Blo 2157435 4608505 := bstep (se 2 (by rfl) ⟨1728189, by rfl⟩ : syracuseStep 4608505 = 3456379) B3456379
theorem B6144673 : Blo 2157435 6144673 := bstep (se 2 (by rfl) ⟨2304252, by rfl⟩ : syracuseStep 6144673 = 4608505) B4608505
theorem B8192897 : Blo 2157435 8192897 := bstep (se 2 (by rfl) ⟨3072336, by rfl⟩ : syracuseStep 8192897 = 6144673) B6144673
theorem B5461931 : Blo 2157435 5461931 := bstep (se 1 (by rfl) ⟨4096448, by rfl⟩ : syracuseStep 5461931 = 8192897) B8192897
theorem B3641287 : Blo 2157435 3641287 := bstep (se 1 (by rfl) ⟨2730965, by rfl⟩ : syracuseStep 3641287 = 5461931) B5461931
theorem B4855049 : Blo 2157435 4855049 := bstep (se 2 (by rfl) ⟨1820643, by rfl⟩ : syracuseStep 4855049 = 3641287) B3641287
theorem B3236699 : Blo 2157435 3236699 := bstep (se 1 (by rfl) ⟨2427524, by rfl⟩ : syracuseStep 3236699 = 4855049) B4855049
theorem B2157799 : Blo 2157435 2157799 := bstep (se 1 (by rfl) ⟨1618349, by rfl⟩ : syracuseStep 2157799 = 3236699) B3236699
theorem B2427529 : Blo 2157435 2427529 := bbase (se 2 (by rfl) ⟨910323, by rfl⟩ : syracuseStep 2427529 = 1820647) (by norm_num)
theorem B3236705 : Blo 2157435 3236705 := bstep (se 2 (by rfl) ⟨1213764, by rfl⟩ : syracuseStep 3236705 = 2427529) B2427529
theorem B2157803 : Blo 2157435 2157803 := bstep (se 1 (by rfl) ⟨1618352, by rfl⟩ : syracuseStep 2157803 = 3236705) B3236705
theorem B42042581 : Blo 2157435 42042581 := bbase (se 7 (by rfl) ⟨492686, by rfl⟩ : syracuseStep 42042581 = 985373) (by norm_num)
theorem B28028387 : Blo 2157435 28028387 := bstep (se 1 (by rfl) ⟨21021290, by rfl⟩ : syracuseStep 28028387 = 42042581) B42042581
theorem B74742365 : Blo 2157435 74742365 := bstep (se 3 (by rfl) ⟨14014193, by rfl⟩ : syracuseStep 74742365 = 28028387) B28028387
theorem B49828243 : Blo 2157435 49828243 := bstep (se 1 (by rfl) ⟨37371182, by rfl⟩ : syracuseStep 49828243 = 74742365) B74742365
theorem B66437657 : Blo 2157435 66437657 := bstep (se 2 (by rfl) ⟨24914121, by rfl⟩ : syracuseStep 66437657 = 49828243) B49828243
theorem B44291771 : Blo 2157435 44291771 := bstep (se 1 (by rfl) ⟨33218828, by rfl⟩ : syracuseStep 44291771 = 66437657) B66437657
theorem B29527847 : Blo 2157435 29527847 := bstep (se 1 (by rfl) ⟨22145885, by rfl⟩ : syracuseStep 29527847 = 44291771) B44291771
theorem B19685231 : Blo 2157435 19685231 := bstep (se 1 (by rfl) ⟨14763923, by rfl⟩ : syracuseStep 19685231 = 29527847) B29527847
theorem B13123487 : Blo 2157435 13123487 := bstep (se 1 (by rfl) ⟨9842615, by rfl⟩ : syracuseStep 13123487 = 19685231) B19685231
theorem B8748991 : Blo 2157435 8748991 := bstep (se 1 (by rfl) ⟨6561743, by rfl⟩ : syracuseStep 8748991 = 13123487) B13123487
theorem B46661285 : Blo 2157435 46661285 := bstep (se 4 (by rfl) ⟨4374495, by rfl⟩ : syracuseStep 46661285 = 8748991) B8748991
theorem B31107523 : Blo 2157435 31107523 := bstep (se 1 (by rfl) ⟨23330642, by rfl⟩ : syracuseStep 31107523 = 46661285) B46661285
theorem B41476697 : Blo 2157435 41476697 := bstep (se 2 (by rfl) ⟨15553761, by rfl⟩ : syracuseStep 41476697 = 31107523) B31107523
theorem B27651131 : Blo 2157435 27651131 := bstep (se 1 (by rfl) ⟨20738348, by rfl⟩ : syracuseStep 27651131 = 41476697) B41476697
theorem B18434087 : Blo 2157435 18434087 := bstep (se 1 (by rfl) ⟨13825565, by rfl⟩ : syracuseStep 18434087 = 27651131) B27651131
theorem B12289391 : Blo 2157435 12289391 := bstep (se 1 (by rfl) ⟨9217043, by rfl⟩ : syracuseStep 12289391 = 18434087) B18434087
theorem B8192927 : Blo 2157435 8192927 := bstep (se 1 (by rfl) ⟨6144695, by rfl⟩ : syracuseStep 8192927 = 12289391) B12289391
theorem B5461951 : Blo 2157435 5461951 := bstep (se 1 (by rfl) ⟨4096463, by rfl⟩ : syracuseStep 5461951 = 8192927) B8192927
theorem B7282601 : Blo 2157435 7282601 := bstep (se 2 (by rfl) ⟨2730975, by rfl⟩ : syracuseStep 7282601 = 5461951) B5461951
theorem B4855067 : Blo 2157435 4855067 := bstep (se 1 (by rfl) ⟨3641300, by rfl⟩ : syracuseStep 4855067 = 7282601) B7282601
theorem B3236711 : Blo 2157435 3236711 := bstep (se 1 (by rfl) ⟨2427533, by rfl⟩ : syracuseStep 3236711 = 4855067) B4855067
theorem B2157807 : Blo 2157435 2157807 := bstep (se 1 (by rfl) ⟨1618355, by rfl⟩ : syracuseStep 2157807 = 3236711) B3236711
theorem B3236717 : Blo 2157435 3236717 := bbase (se 3 (by rfl) ⟨606884, by rfl⟩ : syracuseStep 3236717 = 1213769) (by norm_num)
theorem B2157811 : Blo 2157435 2157811 := bstep (se 1 (by rfl) ⟨1618358, by rfl⟩ : syracuseStep 2157811 = 3236717) B3236717
theorem B4855085 : Blo 2157435 4855085 := bbase (se 3 (by rfl) ⟨910328, by rfl⟩ : syracuseStep 4855085 = 1820657) (by norm_num)
theorem B3236723 : Blo 2157435 3236723 := bstep (se 1 (by rfl) ⟨2427542, by rfl⟩ : syracuseStep 3236723 = 4855085) B4855085
theorem B2157815 : Blo 2157435 2157815 := bstep (se 1 (by rfl) ⟨1618361, by rfl⟩ : syracuseStep 2157815 = 3236723) B3236723
theorem B7007141 : Blo 2157435 7007141 := bbase (se 4 (by rfl) ⟨656919, by rfl⟩ : syracuseStep 7007141 = 1313839) (by norm_num)
theorem B4671427 : Blo 2157435 4671427 := bstep (se 1 (by rfl) ⟨3503570, by rfl⟩ : syracuseStep 4671427 = 7007141) B7007141
theorem B6228569 : Blo 2157435 6228569 := bstep (se 2 (by rfl) ⟨2335713, by rfl⟩ : syracuseStep 6228569 = 4671427) B4671427
theorem B4152379 : Blo 2157435 4152379 := bstep (se 1 (by rfl) ⟨3114284, by rfl⟩ : syracuseStep 4152379 = 6228569) B6228569
theorem B5536505 : Blo 2157435 5536505 := bstep (se 2 (by rfl) ⟨2076189, by rfl⟩ : syracuseStep 5536505 = 4152379) B4152379
theorem B3691003 : Blo 2157435 3691003 := bstep (se 1 (by rfl) ⟨2768252, by rfl⟩ : syracuseStep 3691003 = 5536505) B5536505
theorem B4921337 : Blo 2157435 4921337 := bstep (se 2 (by rfl) ⟨1845501, by rfl⟩ : syracuseStep 4921337 = 3691003) B3691003
theorem B13123565 : Blo 2157435 13123565 := bstep (se 3 (by rfl) ⟨2460668, by rfl⟩ : syracuseStep 13123565 = 4921337) B4921337
theorem B8749043 : Blo 2157435 8749043 := bstep (se 1 (by rfl) ⟨6561782, by rfl⟩ : syracuseStep 8749043 = 13123565) B13123565
theorem B5832695 : Blo 2157435 5832695 := bstep (se 1 (by rfl) ⟨4374521, by rfl⟩ : syracuseStep 5832695 = 8749043) B8749043
theorem B15553853 : Blo 2157435 15553853 := bstep (se 3 (by rfl) ⟨2916347, by rfl⟩ : syracuseStep 15553853 = 5832695) B5832695
theorem B10369235 : Blo 2157435 10369235 := bstep (se 1 (by rfl) ⟨7776926, by rfl⟩ : syracuseStep 10369235 = 15553853) B15553853
theorem B6912823 : Blo 2157435 6912823 := bstep (se 1 (by rfl) ⟨5184617, by rfl⟩ : syracuseStep 6912823 = 10369235) B10369235
theorem B9217097 : Blo 2157435 9217097 := bstep (se 2 (by rfl) ⟨3456411, by rfl⟩ : syracuseStep 9217097 = 6912823) B6912823
theorem B6144731 : Blo 2157435 6144731 := bstep (se 1 (by rfl) ⟨4608548, by rfl⟩ : syracuseStep 6144731 = 9217097) B9217097
theorem B4096487 : Blo 2157435 4096487 := bstep (se 1 (by rfl) ⟨3072365, by rfl⟩ : syracuseStep 4096487 = 6144731) B6144731
theorem B2730991 : Blo 2157435 2730991 := bstep (se 1 (by rfl) ⟨2048243, by rfl⟩ : syracuseStep 2730991 = 4096487) B4096487
theorem B3641321 : Blo 2157435 3641321 := bstep (se 2 (by rfl) ⟨1365495, by rfl⟩ : syracuseStep 3641321 = 2730991) B2730991
theorem B2427547 : Blo 2157435 2427547 := bstep (se 1 (by rfl) ⟨1820660, by rfl⟩ : syracuseStep 2427547 = 3641321) B3641321
theorem B3236729 : Blo 2157435 3236729 := bstep (se 2 (by rfl) ⟨1213773, by rfl⟩ : syracuseStep 3236729 = 2427547) B2427547
theorem B2157819 : Blo 2157435 2157819 := bstep (se 1 (by rfl) ⟨1618364, by rfl⟩ : syracuseStep 2157819 = 3236729) B3236729
theorem B3888469 : Blo 2157435 3888469 := bbase (se 17 (by rfl) ⟨44, by rfl⟩ : syracuseStep 3888469 = 89) (by norm_num)
theorem B20738501 : Blo 2157435 20738501 := bstep (se 4 (by rfl) ⟨1944234, by rfl⟩ : syracuseStep 20738501 = 3888469) B3888469
theorem B13825667 : Blo 2157435 13825667 := bstep (se 1 (by rfl) ⟨10369250, by rfl⟩ : syracuseStep 13825667 = 20738501) B20738501
theorem B36868445 : Blo 2157435 36868445 := bstep (se 3 (by rfl) ⟨6912833, by rfl⟩ : syracuseStep 36868445 = 13825667) B13825667
theorem B24578963 : Blo 2157435 24578963 := bstep (se 1 (by rfl) ⟨18434222, by rfl⟩ : syracuseStep 24578963 = 36868445) B36868445
theorem B16385975 : Blo 2157435 16385975 := bstep (se 1 (by rfl) ⟨12289481, by rfl⟩ : syracuseStep 16385975 = 24578963) B24578963
theorem B10923983 : Blo 2157435 10923983 := bstep (se 1 (by rfl) ⟨8192987, by rfl⟩ : syracuseStep 10923983 = 16385975) B16385975
theorem B7282655 : Blo 2157435 7282655 := bstep (se 1 (by rfl) ⟨5461991, by rfl⟩ : syracuseStep 7282655 = 10923983) B10923983
theorem B4855103 : Blo 2157435 4855103 := bstep (se 1 (by rfl) ⟨3641327, by rfl⟩ : syracuseStep 4855103 = 7282655) B7282655
theorem B3236735 : Blo 2157435 3236735 := bstep (se 1 (by rfl) ⟨2427551, by rfl⟩ : syracuseStep 3236735 = 4855103) B4855103
theorem B2157823 : Blo 2157435 2157823 := bstep (se 1 (by rfl) ⟨1618367, by rfl⟩ : syracuseStep 2157823 = 3236735) B3236735
theorem B3236741 : Blo 2157435 3236741 := bbase (se 4 (by rfl) ⟨303444, by rfl⟩ : syracuseStep 3236741 = 606889) (by norm_num)
theorem B2157827 : Blo 2157435 2157827 := bstep (se 1 (by rfl) ⟨1618370, by rfl⟩ : syracuseStep 2157827 = 3236741) B3236741
theorem B3641341 : Blo 2157435 3641341 := bbase (se 3 (by rfl) ⟨682751, by rfl⟩ : syracuseStep 3641341 = 1365503) (by norm_num)
theorem B4855121 : Blo 2157435 4855121 := bstep (se 2 (by rfl) ⟨1820670, by rfl⟩ : syracuseStep 4855121 = 3641341) B3641341
theorem B3236747 : Blo 2157435 3236747 := bstep (se 1 (by rfl) ⟨2427560, by rfl⟩ : syracuseStep 3236747 = 4855121) B4855121
theorem B2157831 : Blo 2157435 2157831 := bstep (se 1 (by rfl) ⟨1618373, by rfl⟩ : syracuseStep 2157831 = 3236747) B3236747
theorem B2427565 : Blo 2157435 2427565 := bbase (se 3 (by rfl) ⟨455168, by rfl⟩ : syracuseStep 2427565 = 910337) (by norm_num)
theorem B3236753 : Blo 2157435 3236753 := bstep (se 2 (by rfl) ⟨1213782, by rfl⟩ : syracuseStep 3236753 = 2427565) B2427565
theorem B2157835 : Blo 2157435 2157835 := bstep (se 1 (by rfl) ⟨1618376, by rfl⟩ : syracuseStep 2157835 = 3236753) B3236753
theorem B7282709 : Blo 2157435 7282709 := bbase (se 6 (by rfl) ⟨170688, by rfl⟩ : syracuseStep 7282709 = 341377) (by norm_num)
theorem B4855139 : Blo 2157435 4855139 := bstep (se 1 (by rfl) ⟨3641354, by rfl⟩ : syracuseStep 4855139 = 7282709) B7282709
theorem B3236759 : Blo 2157435 3236759 := bstep (se 1 (by rfl) ⟨2427569, by rfl⟩ : syracuseStep 3236759 = 4855139) B4855139
theorem B2157839 : Blo 2157435 2157839 := bstep (se 1 (by rfl) ⟨1618379, by rfl⟩ : syracuseStep 2157839 = 3236759) B3236759
theorem B3236765 : Blo 2157435 3236765 := bbase (se 3 (by rfl) ⟨606893, by rfl⟩ : syracuseStep 3236765 = 1213787) (by norm_num)
theorem B2157843 : Blo 2157435 2157843 := bstep (se 1 (by rfl) ⟨1618382, by rfl⟩ : syracuseStep 2157843 = 3236765) B3236765
theorem B4855157 : Blo 2157435 4855157 := bbase (se 5 (by rfl) ⟨227585, by rfl⟩ : syracuseStep 4855157 = 455171) (by norm_num)
theorem B3236771 : Blo 2157435 3236771 := bstep (se 1 (by rfl) ⟨2427578, by rfl⟩ : syracuseStep 3236771 = 4855157) B4855157
theorem B2157847 : Blo 2157435 2157847 := bstep (se 1 (by rfl) ⟨1618385, by rfl⟩ : syracuseStep 2157847 = 3236771) B3236771
theorem B2768293 : Blo 2157435 2768293 := bbase (se 4 (by rfl) ⟨259527, by rfl⟩ : syracuseStep 2768293 = 519055) (by norm_num)
theorem B3691057 : Blo 2157435 3691057 := bstep (se 2 (by rfl) ⟨1384146, by rfl⟩ : syracuseStep 3691057 = 2768293) B2768293
theorem B4921409 : Blo 2157435 4921409 := bstep (se 2 (by rfl) ⟨1845528, by rfl⟩ : syracuseStep 4921409 = 3691057) B3691057
theorem B13123757 : Blo 2157435 13123757 := bstep (se 3 (by rfl) ⟨2460704, by rfl⟩ : syracuseStep 13123757 = 4921409) B4921409
theorem B8749171 : Blo 2157435 8749171 := bstep (se 1 (by rfl) ⟨6561878, by rfl⟩ : syracuseStep 8749171 = 13123757) B13123757
theorem B11665561 : Blo 2157435 11665561 := bstep (se 2 (by rfl) ⟨4374585, by rfl⟩ : syracuseStep 11665561 = 8749171) B8749171
theorem B15554081 : Blo 2157435 15554081 := bstep (se 2 (by rfl) ⟨5832780, by rfl⟩ : syracuseStep 15554081 = 11665561) B11665561
theorem B10369387 : Blo 2157435 10369387 := bstep (se 1 (by rfl) ⟨7777040, by rfl⟩ : syracuseStep 10369387 = 15554081) B15554081
theorem B13825849 : Blo 2157435 13825849 := bstep (se 2 (by rfl) ⟨5184693, by rfl⟩ : syracuseStep 13825849 = 10369387) B10369387
theorem B18434465 : Blo 2157435 18434465 := bstep (se 2 (by rfl) ⟨6912924, by rfl⟩ : syracuseStep 18434465 = 13825849) B13825849
theorem B12289643 : Blo 2157435 12289643 := bstep (se 1 (by rfl) ⟨9217232, by rfl⟩ : syracuseStep 12289643 = 18434465) B18434465
theorem B8193095 : Blo 2157435 8193095 := bstep (se 1 (by rfl) ⟨6144821, by rfl⟩ : syracuseStep 8193095 = 12289643) B12289643
theorem B5462063 : Blo 2157435 5462063 := bstep (se 1 (by rfl) ⟨4096547, by rfl⟩ : syracuseStep 5462063 = 8193095) B8193095
theorem B3641375 : Blo 2157435 3641375 := bstep (se 1 (by rfl) ⟨2731031, by rfl⟩ : syracuseStep 3641375 = 5462063) B5462063
theorem B2427583 : Blo 2157435 2427583 := bstep (se 1 (by rfl) ⟨1820687, by rfl⟩ : syracuseStep 2427583 = 3641375) B3641375
theorem B3236777 : Blo 2157435 3236777 := bstep (se 2 (by rfl) ⟨1213791, by rfl⟩ : syracuseStep 3236777 = 2427583) B2427583
theorem B2157851 : Blo 2157435 2157851 := bstep (se 1 (by rfl) ⟨1618388, by rfl⟩ : syracuseStep 2157851 = 3236777) B3236777
theorem B8193109 : Blo 2157435 8193109 := bbase (se 8 (by rfl) ⟨48006, by rfl⟩ : syracuseStep 8193109 = 96013) (by norm_num)
theorem B10924145 : Blo 2157435 10924145 := bstep (se 2 (by rfl) ⟨4096554, by rfl⟩ : syracuseStep 10924145 = 8193109) B8193109
theorem B7282763 : Blo 2157435 7282763 := bstep (se 1 (by rfl) ⟨5462072, by rfl⟩ : syracuseStep 7282763 = 10924145) B10924145
theorem B4855175 : Blo 2157435 4855175 := bstep (se 1 (by rfl) ⟨3641381, by rfl⟩ : syracuseStep 4855175 = 7282763) B7282763
theorem B3236783 : Blo 2157435 3236783 := bstep (se 1 (by rfl) ⟨2427587, by rfl⟩ : syracuseStep 3236783 = 4855175) B4855175
theorem B2157855 : Blo 2157435 2157855 := bstep (se 1 (by rfl) ⟨1618391, by rfl⟩ : syracuseStep 2157855 = 3236783) B3236783
theorem B3236789 : Blo 2157435 3236789 := bbase (se 5 (by rfl) ⟨151724, by rfl⟩ : syracuseStep 3236789 = 303449) (by norm_num)
theorem B2157859 : Blo 2157435 2157859 := bstep (se 1 (by rfl) ⟨1618394, by rfl⟩ : syracuseStep 2157859 = 3236789) B3236789
theorem B5462093 : Blo 2157435 5462093 := bbase (se 3 (by rfl) ⟨1024142, by rfl⟩ : syracuseStep 5462093 = 2048285) (by norm_num)
theorem B3641395 : Blo 2157435 3641395 := bstep (se 1 (by rfl) ⟨2731046, by rfl⟩ : syracuseStep 3641395 = 5462093) B5462093
theorem B4855193 : Blo 2157435 4855193 := bstep (se 2 (by rfl) ⟨1820697, by rfl⟩ : syracuseStep 4855193 = 3641395) B3641395
theorem B3236795 : Blo 2157435 3236795 := bstep (se 1 (by rfl) ⟨2427596, by rfl⟩ : syracuseStep 3236795 = 4855193) B4855193
theorem B2157863 : Blo 2157435 2157863 := bstep (se 1 (by rfl) ⟨1618397, by rfl⟩ : syracuseStep 2157863 = 3236795) B3236795
theorem B2427601 : Blo 2157435 2427601 := bbase (se 2 (by rfl) ⟨910350, by rfl⟩ : syracuseStep 2427601 = 1820701) (by norm_num)
theorem B3236801 : Blo 2157435 3236801 := bstep (se 2 (by rfl) ⟨1213800, by rfl⟩ : syracuseStep 3236801 = 2427601) B2427601
theorem B2157867 : Blo 2157435 2157867 := bstep (se 1 (by rfl) ⟨1618400, by rfl⟩ : syracuseStep 2157867 = 3236801) B3236801
theorem B3888557 : Blo 2157435 3888557 := bbase (se 3 (by rfl) ⟨729104, by rfl⟩ : syracuseStep 3888557 = 1458209) (by norm_num)
theorem B2592371 : Blo 2157435 2592371 := bstep (se 1 (by rfl) ⟨1944278, by rfl⟩ : syracuseStep 2592371 = 3888557) B3888557
theorem B6912989 : Blo 2157435 6912989 := bstep (se 3 (by rfl) ⟨1296185, by rfl⟩ : syracuseStep 6912989 = 2592371) B2592371
theorem B4608659 : Blo 2157435 4608659 := bstep (se 1 (by rfl) ⟨3456494, by rfl⟩ : syracuseStep 4608659 = 6912989) B6912989
theorem B3072439 : Blo 2157435 3072439 := bstep (se 1 (by rfl) ⟨2304329, by rfl⟩ : syracuseStep 3072439 = 4608659) B4608659
theorem B4096585 : Blo 2157435 4096585 := bstep (se 2 (by rfl) ⟨1536219, by rfl⟩ : syracuseStep 4096585 = 3072439) B3072439
theorem B5462113 : Blo 2157435 5462113 := bstep (se 2 (by rfl) ⟨2048292, by rfl⟩ : syracuseStep 5462113 = 4096585) B4096585
theorem B7282817 : Blo 2157435 7282817 := bstep (se 2 (by rfl) ⟨2731056, by rfl⟩ : syracuseStep 7282817 = 5462113) B5462113
theorem B4855211 : Blo 2157435 4855211 := bstep (se 1 (by rfl) ⟨3641408, by rfl⟩ : syracuseStep 4855211 = 7282817) B7282817
theorem B3236807 : Blo 2157435 3236807 := bstep (se 1 (by rfl) ⟨2427605, by rfl⟩ : syracuseStep 3236807 = 4855211) B4855211
theorem B2157871 : Blo 2157435 2157871 := bstep (se 1 (by rfl) ⟨1618403, by rfl⟩ : syracuseStep 2157871 = 3236807) B3236807
theorem B3236813 : Blo 2157435 3236813 := bbase (se 3 (by rfl) ⟨606902, by rfl⟩ : syracuseStep 3236813 = 1213805) (by norm_num)
theorem B2157875 : Blo 2157435 2157875 := bstep (se 1 (by rfl) ⟨1618406, by rfl⟩ : syracuseStep 2157875 = 3236813) B3236813
theorem B4855229 : Blo 2157435 4855229 := bbase (se 3 (by rfl) ⟨910355, by rfl⟩ : syracuseStep 4855229 = 1820711) (by norm_num)
theorem B3236819 : Blo 2157435 3236819 := bstep (se 1 (by rfl) ⟨2427614, by rfl⟩ : syracuseStep 3236819 = 4855229) B4855229
theorem B2157879 : Blo 2157435 2157879 := bstep (se 1 (by rfl) ⟨1618409, by rfl⟩ : syracuseStep 2157879 = 3236819) B3236819
theorem B3641429 : Blo 2157435 3641429 := bbase (se 8 (by rfl) ⟨21336, by rfl⟩ : syracuseStep 3641429 = 42673) (by norm_num)
theorem B2427619 : Blo 2157435 2427619 := bstep (se 1 (by rfl) ⟨1820714, by rfl⟩ : syracuseStep 2427619 = 3641429) B3641429
theorem B3236825 : Blo 2157435 3236825 := bstep (se 2 (by rfl) ⟨1213809, by rfl⟩ : syracuseStep 3236825 = 2427619) B2427619
theorem B2157883 : Blo 2157435 2157883 := bstep (se 1 (by rfl) ⟨1618412, by rfl⟩ : syracuseStep 2157883 = 3236825) B3236825
theorem B2187329 : Blo 2157435 2187329 := bbase (se 2 (by rfl) ⟨820248, by rfl⟩ : syracuseStep 2187329 = 1640497) (by norm_num)
theorem B23331509 : Blo 2157435 23331509 := bstep (se 5 (by rfl) ⟨1093664, by rfl⟩ : syracuseStep 23331509 = 2187329) B2187329
theorem B15554339 : Blo 2157435 15554339 := bstep (se 1 (by rfl) ⟨11665754, by rfl⟩ : syracuseStep 15554339 = 23331509) B23331509
theorem B10369559 : Blo 2157435 10369559 := bstep (se 1 (by rfl) ⟨7777169, by rfl⟩ : syracuseStep 10369559 = 15554339) B15554339
theorem B6913039 : Blo 2157435 6913039 := bstep (se 1 (by rfl) ⟨5184779, by rfl⟩ : syracuseStep 6913039 = 10369559) B10369559
theorem B9217385 : Blo 2157435 9217385 := bstep (se 2 (by rfl) ⟨3456519, by rfl⟩ : syracuseStep 9217385 = 6913039) B6913039
theorem B6144923 : Blo 2157435 6144923 := bstep (se 1 (by rfl) ⟨4608692, by rfl⟩ : syracuseStep 6144923 = 9217385) B9217385
theorem B16386461 : Blo 2157435 16386461 := bstep (se 3 (by rfl) ⟨3072461, by rfl⟩ : syracuseStep 16386461 = 6144923) B6144923
theorem B10924307 : Blo 2157435 10924307 := bstep (se 1 (by rfl) ⟨8193230, by rfl⟩ : syracuseStep 10924307 = 16386461) B16386461
theorem B7282871 : Blo 2157435 7282871 := bstep (se 1 (by rfl) ⟨5462153, by rfl⟩ : syracuseStep 7282871 = 10924307) B10924307
theorem B4855247 : Blo 2157435 4855247 := bstep (se 1 (by rfl) ⟨3641435, by rfl⟩ : syracuseStep 4855247 = 7282871) B7282871
theorem B3236831 : Blo 2157435 3236831 := bstep (se 1 (by rfl) ⟨2427623, by rfl⟩ : syracuseStep 3236831 = 4855247) B4855247
theorem B2157887 : Blo 2157435 2157887 := bstep (se 1 (by rfl) ⟨1618415, by rfl⟩ : syracuseStep 2157887 = 3236831) B3236831
theorem B3236837 : Blo 2157435 3236837 := bbase (se 4 (by rfl) ⟨303453, by rfl⟩ : syracuseStep 3236837 = 606907) (by norm_num)
theorem B2157891 : Blo 2157435 2157891 := bstep (se 1 (by rfl) ⟨1618418, by rfl⟩ : syracuseStep 2157891 = 3236837) B3236837
theorem B3456533 : Blo 2157435 3456533 := bbase (se 6 (by rfl) ⟨81012, by rfl⟩ : syracuseStep 3456533 = 162025) (by norm_num)
theorem B9217421 : Blo 2157435 9217421 := bstep (se 3 (by rfl) ⟨1728266, by rfl⟩ : syracuseStep 9217421 = 3456533) B3456533
theorem B6144947 : Blo 2157435 6144947 := bstep (se 1 (by rfl) ⟨4608710, by rfl⟩ : syracuseStep 6144947 = 9217421) B9217421
theorem B4096631 : Blo 2157435 4096631 := bstep (se 1 (by rfl) ⟨3072473, by rfl⟩ : syracuseStep 4096631 = 6144947) B6144947
theorem B2731087 : Blo 2157435 2731087 := bstep (se 1 (by rfl) ⟨2048315, by rfl⟩ : syracuseStep 2731087 = 4096631) B4096631
theorem B3641449 : Blo 2157435 3641449 := bstep (se 2 (by rfl) ⟨1365543, by rfl⟩ : syracuseStep 3641449 = 2731087) B2731087
theorem B4855265 : Blo 2157435 4855265 := bstep (se 2 (by rfl) ⟨1820724, by rfl⟩ : syracuseStep 4855265 = 3641449) B3641449
theorem B3236843 : Blo 2157435 3236843 := bstep (se 1 (by rfl) ⟨2427632, by rfl⟩ : syracuseStep 3236843 = 4855265) B4855265
theorem B2157895 : Blo 2157435 2157895 := bstep (se 1 (by rfl) ⟨1618421, by rfl⟩ : syracuseStep 2157895 = 3236843) B3236843
theorem B2427637 : Blo 2157435 2427637 := bbase (se 5 (by rfl) ⟨113795, by rfl⟩ : syracuseStep 2427637 = 227591) (by norm_num)
theorem B3236849 : Blo 2157435 3236849 := bstep (se 2 (by rfl) ⟨1213818, by rfl⟩ : syracuseStep 3236849 = 2427637) B2427637
theorem B2157899 : Blo 2157435 2157899 := bstep (se 1 (by rfl) ⟨1618424, by rfl⟩ : syracuseStep 2157899 = 3236849) B3236849
theorem B2731097 : Blo 2157435 2731097 := bbase (se 2 (by rfl) ⟨1024161, by rfl⟩ : syracuseStep 2731097 = 2048323) (by norm_num)
theorem B7282925 : Blo 2157435 7282925 := bstep (se 3 (by rfl) ⟨1365548, by rfl⟩ : syracuseStep 7282925 = 2731097) B2731097
theorem B4855283 : Blo 2157435 4855283 := bstep (se 1 (by rfl) ⟨3641462, by rfl⟩ : syracuseStep 4855283 = 7282925) B7282925
theorem B3236855 : Blo 2157435 3236855 := bstep (se 1 (by rfl) ⟨2427641, by rfl⟩ : syracuseStep 3236855 = 4855283) B4855283
theorem B2157903 : Blo 2157435 2157903 := bstep (se 1 (by rfl) ⟨1618427, by rfl⟩ : syracuseStep 2157903 = 3236855) B3236855
theorem B3236861 : Blo 2157435 3236861 := bbase (se 3 (by rfl) ⟨606911, by rfl⟩ : syracuseStep 3236861 = 1213823) (by norm_num)
theorem B2157907 : Blo 2157435 2157907 := bstep (se 1 (by rfl) ⟨1618430, by rfl⟩ : syracuseStep 2157907 = 3236861) B3236861
theorem B4855301 : Blo 2157435 4855301 := bbase (se 4 (by rfl) ⟨455184, by rfl⟩ : syracuseStep 4855301 = 910369) (by norm_num)
theorem B3236867 : Blo 2157435 3236867 := bstep (se 1 (by rfl) ⟨2427650, by rfl⟩ : syracuseStep 3236867 = 4855301) B4855301
theorem B2157911 : Blo 2157435 2157911 := bstep (se 1 (by rfl) ⟨1618433, by rfl⟩ : syracuseStep 2157911 = 3236867) B3236867
theorem B4096669 : Blo 2157435 4096669 := bbase (se 3 (by rfl) ⟨768125, by rfl⟩ : syracuseStep 4096669 = 1536251) (by norm_num)
theorem B5462225 : Blo 2157435 5462225 := bstep (se 2 (by rfl) ⟨2048334, by rfl⟩ : syracuseStep 5462225 = 4096669) B4096669
theorem B3641483 : Blo 2157435 3641483 := bstep (se 1 (by rfl) ⟨2731112, by rfl⟩ : syracuseStep 3641483 = 5462225) B5462225
theorem B2427655 : Blo 2157435 2427655 := bstep (se 1 (by rfl) ⟨1820741, by rfl⟩ : syracuseStep 2427655 = 3641483) B3641483
theorem B3236873 : Blo 2157435 3236873 := bstep (se 2 (by rfl) ⟨1213827, by rfl⟩ : syracuseStep 3236873 = 2427655) B2427655
theorem B2157915 : Blo 2157435 2157915 := bstep (se 1 (by rfl) ⟨1618436, by rfl⟩ : syracuseStep 2157915 = 3236873) B3236873
theorem B10924469 : Blo 2157435 10924469 := bbase (se 5 (by rfl) ⟨512084, by rfl⟩ : syracuseStep 10924469 = 1024169) (by norm_num)
theorem B7282979 : Blo 2157435 7282979 := bstep (se 1 (by rfl) ⟨5462234, by rfl⟩ : syracuseStep 7282979 = 10924469) B10924469
theorem B4855319 : Blo 2157435 4855319 := bstep (se 1 (by rfl) ⟨3641489, by rfl⟩ : syracuseStep 4855319 = 7282979) B7282979
theorem B3236879 : Blo 2157435 3236879 := bstep (se 1 (by rfl) ⟨2427659, by rfl⟩ : syracuseStep 3236879 = 4855319) B4855319
theorem B2157919 : Blo 2157435 2157919 := bstep (se 1 (by rfl) ⟨1618439, by rfl⟩ : syracuseStep 2157919 = 3236879) B3236879
theorem B3236885 : Blo 2157435 3236885 := bbase (se 6 (by rfl) ⟨75864, by rfl⟩ : syracuseStep 3236885 = 151729) (by norm_num)
theorem B2157923 : Blo 2157435 2157923 := bstep (se 1 (by rfl) ⟨1618442, by rfl⟩ : syracuseStep 2157923 = 3236885) B3236885
theorem B2335829 : Blo 2157435 2335829 := bbase (se 8 (by rfl) ⟨13686, by rfl⟩ : syracuseStep 2335829 = 27373) (by norm_num)
theorem B24915509 : Blo 2157435 24915509 := bstep (se 5 (by rfl) ⟨1167914, by rfl⟩ : syracuseStep 24915509 = 2335829) B2335829
theorem B16610339 : Blo 2157435 16610339 := bstep (se 1 (by rfl) ⟨12457754, by rfl⟩ : syracuseStep 16610339 = 24915509) B24915509
theorem B11073559 : Blo 2157435 11073559 := bstep (se 1 (by rfl) ⟨8305169, by rfl⟩ : syracuseStep 11073559 = 16610339) B16610339
theorem B14764745 : Blo 2157435 14764745 := bstep (se 2 (by rfl) ⟨5536779, by rfl⟩ : syracuseStep 14764745 = 11073559) B11073559
theorem B9843163 : Blo 2157435 9843163 := bstep (se 1 (by rfl) ⟨7382372, by rfl⟩ : syracuseStep 9843163 = 14764745) B14764745
theorem B52496869 : Blo 2157435 52496869 := bstep (se 4 (by rfl) ⟨4921581, by rfl⟩ : syracuseStep 52496869 = 9843163) B9843163
theorem B69995825 : Blo 2157435 69995825 := bstep (se 2 (by rfl) ⟨26248434, by rfl⟩ : syracuseStep 69995825 = 52496869) B52496869
theorem B46663883 : Blo 2157435 46663883 := bstep (se 1 (by rfl) ⟨34997912, by rfl⟩ : syracuseStep 46663883 = 69995825) B69995825
theorem B31109255 : Blo 2157435 31109255 := bstep (se 1 (by rfl) ⟨23331941, by rfl⟩ : syracuseStep 31109255 = 46663883) B46663883
theorem B20739503 : Blo 2157435 20739503 := bstep (se 1 (by rfl) ⟨15554627, by rfl⟩ : syracuseStep 20739503 = 31109255) B31109255
theorem B13826335 : Blo 2157435 13826335 := bstep (se 1 (by rfl) ⟨10369751, by rfl⟩ : syracuseStep 13826335 = 20739503) B20739503
theorem B18435113 : Blo 2157435 18435113 := bstep (se 2 (by rfl) ⟨6913167, by rfl⟩ : syracuseStep 18435113 = 13826335) B13826335
theorem B12290075 : Blo 2157435 12290075 := bstep (se 1 (by rfl) ⟨9217556, by rfl⟩ : syracuseStep 12290075 = 18435113) B18435113
theorem B8193383 : Blo 2157435 8193383 := bstep (se 1 (by rfl) ⟨6145037, by rfl⟩ : syracuseStep 8193383 = 12290075) B12290075
theorem B5462255 : Blo 2157435 5462255 := bstep (se 1 (by rfl) ⟨4096691, by rfl⟩ : syracuseStep 5462255 = 8193383) B8193383
theorem B3641503 : Blo 2157435 3641503 := bstep (se 1 (by rfl) ⟨2731127, by rfl⟩ : syracuseStep 3641503 = 5462255) B5462255
theorem B4855337 : Blo 2157435 4855337 := bstep (se 2 (by rfl) ⟨1820751, by rfl⟩ : syracuseStep 4855337 = 3641503) B3641503
theorem B3236891 : Blo 2157435 3236891 := bstep (se 1 (by rfl) ⟨2427668, by rfl⟩ : syracuseStep 3236891 = 4855337) B4855337
theorem B2157927 : Blo 2157435 2157927 := bstep (se 1 (by rfl) ⟨1618445, by rfl⟩ : syracuseStep 2157927 = 3236891) B3236891
theorem B2427673 : Blo 2157435 2427673 := bbase (se 2 (by rfl) ⟨910377, by rfl⟩ : syracuseStep 2427673 = 1820755) (by norm_num)
theorem B3236897 : Blo 2157435 3236897 := bstep (se 2 (by rfl) ⟨1213836, by rfl⟩ : syracuseStep 3236897 = 2427673) B2427673
theorem B2157931 : Blo 2157435 2157931 := bstep (se 1 (by rfl) ⟨1618448, by rfl⟩ : syracuseStep 2157931 = 3236897) B3236897
theorem B8193413 : Blo 2157435 8193413 := bbase (se 4 (by rfl) ⟨768132, by rfl⟩ : syracuseStep 8193413 = 1536265) (by norm_num)
theorem B5462275 : Blo 2157435 5462275 := bstep (se 1 (by rfl) ⟨4096706, by rfl⟩ : syracuseStep 5462275 = 8193413) B8193413
theorem B7283033 : Blo 2157435 7283033 := bstep (se 2 (by rfl) ⟨2731137, by rfl⟩ : syracuseStep 7283033 = 5462275) B5462275
theorem B4855355 : Blo 2157435 4855355 := bstep (se 1 (by rfl) ⟨3641516, by rfl⟩ : syracuseStep 4855355 = 7283033) B7283033
theorem B3236903 : Blo 2157435 3236903 := bstep (se 1 (by rfl) ⟨2427677, by rfl⟩ : syracuseStep 3236903 = 4855355) B4855355
theorem B2157935 : Blo 2157435 2157935 := bstep (se 1 (by rfl) ⟨1618451, by rfl⟩ : syracuseStep 2157935 = 3236903) B3236903
theorem B3236909 : Blo 2157435 3236909 := bbase (se 3 (by rfl) ⟨606920, by rfl⟩ : syracuseStep 3236909 = 1213841) (by norm_num)
theorem B2157939 : Blo 2157435 2157939 := bstep (se 1 (by rfl) ⟨1618454, by rfl⟩ : syracuseStep 2157939 = 3236909) B3236909
theorem B4855373 : Blo 2157435 4855373 := bbase (se 3 (by rfl) ⟨910382, by rfl⟩ : syracuseStep 4855373 = 1820765) (by norm_num)
theorem B3236915 : Blo 2157435 3236915 := bstep (se 1 (by rfl) ⟨2427686, by rfl⟩ : syracuseStep 3236915 = 4855373) B4855373
theorem B2157943 : Blo 2157435 2157943 := bstep (se 1 (by rfl) ⟨1618457, by rfl⟩ : syracuseStep 2157943 = 3236915) B3236915
theorem B2731153 : Blo 2157435 2731153 := bbase (se 2 (by rfl) ⟨1024182, by rfl⟩ : syracuseStep 2731153 = 2048365) (by norm_num)
theorem B3641537 : Blo 2157435 3641537 := bstep (se 2 (by rfl) ⟨1365576, by rfl⟩ : syracuseStep 3641537 = 2731153) B2731153
theorem B2427691 : Blo 2157435 2427691 := bstep (se 1 (by rfl) ⟨1820768, by rfl⟩ : syracuseStep 2427691 = 3641537) B3641537
theorem B3236921 : Blo 2157435 3236921 := bstep (se 2 (by rfl) ⟨1213845, by rfl⟩ : syracuseStep 3236921 = 2427691) B2427691
theorem B2157947 : Blo 2157435 2157947 := bstep (se 1 (by rfl) ⟨1618460, by rfl⟩ : syracuseStep 2157947 = 3236921) B3236921
theorem B4608829 : Blo 2157435 4608829 := bbase (se 3 (by rfl) ⟨864155, by rfl⟩ : syracuseStep 4608829 = 1728311) (by norm_num)
theorem B24580421 : Blo 2157435 24580421 := bstep (se 4 (by rfl) ⟨2304414, by rfl⟩ : syracuseStep 24580421 = 4608829) B4608829
theorem B16386947 : Blo 2157435 16386947 := bstep (se 1 (by rfl) ⟨12290210, by rfl⟩ : syracuseStep 16386947 = 24580421) B24580421
theorem B10924631 : Blo 2157435 10924631 := bstep (se 1 (by rfl) ⟨8193473, by rfl⟩ : syracuseStep 10924631 = 16386947) B16386947
theorem B7283087 : Blo 2157435 7283087 := bstep (se 1 (by rfl) ⟨5462315, by rfl⟩ : syracuseStep 7283087 = 10924631) B10924631
theorem B4855391 : Blo 2157435 4855391 := bstep (se 1 (by rfl) ⟨3641543, by rfl⟩ : syracuseStep 4855391 = 7283087) B7283087
theorem B3236927 : Blo 2157435 3236927 := bstep (se 1 (by rfl) ⟨2427695, by rfl⟩ : syracuseStep 3236927 = 4855391) B4855391
theorem B2157951 : Blo 2157435 2157951 := bstep (se 1 (by rfl) ⟨1618463, by rfl⟩ : syracuseStep 2157951 = 3236927) B3236927
theorem B3236933 : Blo 2157435 3236933 := bbase (se 4 (by rfl) ⟨303462, by rfl⟩ : syracuseStep 3236933 = 606925) (by norm_num)
theorem B2157955 : Blo 2157435 2157955 := bstep (se 1 (by rfl) ⟨1618466, by rfl⟩ : syracuseStep 2157955 = 3236933) B3236933
theorem B3641557 : Blo 2157435 3641557 := bbase (se 7 (by rfl) ⟨42674, by rfl⟩ : syracuseStep 3641557 = 85349) (by norm_num)
theorem B4855409 : Blo 2157435 4855409 := bstep (se 2 (by rfl) ⟨1820778, by rfl⟩ : syracuseStep 4855409 = 3641557) B3641557
theorem B3236939 : Blo 2157435 3236939 := bstep (se 1 (by rfl) ⟨2427704, by rfl⟩ : syracuseStep 3236939 = 4855409) B4855409
theorem B2157959 : Blo 2157435 2157959 := bstep (se 1 (by rfl) ⟨1618469, by rfl⟩ : syracuseStep 2157959 = 3236939) B3236939
theorem B2427709 : Blo 2157435 2427709 := bbase (se 3 (by rfl) ⟨455195, by rfl⟩ : syracuseStep 2427709 = 910391) (by norm_num)
theorem B3236945 : Blo 2157435 3236945 := bstep (se 2 (by rfl) ⟨1213854, by rfl⟩ : syracuseStep 3236945 = 2427709) B2427709
theorem B2157963 : Blo 2157435 2157963 := bstep (se 1 (by rfl) ⟨1618472, by rfl⟩ : syracuseStep 2157963 = 3236945) B3236945
theorem B7283141 : Blo 2157435 7283141 := bbase (se 4 (by rfl) ⟨682794, by rfl⟩ : syracuseStep 7283141 = 1365589) (by norm_num)
theorem B4855427 : Blo 2157435 4855427 := bstep (se 1 (by rfl) ⟨3641570, by rfl⟩ : syracuseStep 4855427 = 7283141) B7283141
theorem B3236951 : Blo 2157435 3236951 := bstep (se 1 (by rfl) ⟨2427713, by rfl⟩ : syracuseStep 3236951 = 4855427) B4855427
theorem B2157967 : Blo 2157435 2157967 := bstep (se 1 (by rfl) ⟨1618475, by rfl⟩ : syracuseStep 2157967 = 3236951) B3236951
theorem B3236957 : Blo 2157435 3236957 := bbase (se 3 (by rfl) ⟨606929, by rfl⟩ : syracuseStep 3236957 = 1213859) (by norm_num)
theorem B2157971 : Blo 2157435 2157971 := bstep (se 1 (by rfl) ⟨1618478, by rfl⟩ : syracuseStep 2157971 = 3236957) B3236957
theorem B4855445 : Blo 2157435 4855445 := bbase (se 6 (by rfl) ⟨113799, by rfl⟩ : syracuseStep 4855445 = 227599) (by norm_num)
theorem B3236963 : Blo 2157435 3236963 := bstep (se 1 (by rfl) ⟨2427722, by rfl⟩ : syracuseStep 3236963 = 4855445) B4855445
theorem B2157975 : Blo 2157435 2157975 := bstep (se 1 (by rfl) ⟨1618481, by rfl⟩ : syracuseStep 2157975 = 3236963) B3236963
theorem B2304445 : Blo 2157435 2304445 := bbase (se 3 (by rfl) ⟨432083, by rfl⟩ : syracuseStep 2304445 = 864167) (by norm_num)
theorem B3072593 : Blo 2157435 3072593 := bstep (se 2 (by rfl) ⟨1152222, by rfl⟩ : syracuseStep 3072593 = 2304445) B2304445
theorem B8193581 : Blo 2157435 8193581 := bstep (se 3 (by rfl) ⟨1536296, by rfl⟩ : syracuseStep 8193581 = 3072593) B3072593
theorem B5462387 : Blo 2157435 5462387 := bstep (se 1 (by rfl) ⟨4096790, by rfl⟩ : syracuseStep 5462387 = 8193581) B8193581
theorem B3641591 : Blo 2157435 3641591 := bstep (se 1 (by rfl) ⟨2731193, by rfl⟩ : syracuseStep 3641591 = 5462387) B5462387
theorem B2427727 : Blo 2157435 2427727 := bstep (se 1 (by rfl) ⟨1820795, by rfl⟩ : syracuseStep 2427727 = 3641591) B3641591
theorem B3236969 : Blo 2157435 3236969 := bstep (se 2 (by rfl) ⟨1213863, by rfl⟩ : syracuseStep 3236969 = 2427727) B2427727
theorem B2157979 : Blo 2157435 2157979 := bstep (se 1 (by rfl) ⟨1618484, by rfl⟩ : syracuseStep 2157979 = 3236969) B3236969
theorem B2592505 : Blo 2157435 2592505 := bbase (se 2 (by rfl) ⟨972189, by rfl⟩ : syracuseStep 2592505 = 1944379) (by norm_num)
theorem B13826693 : Blo 2157435 13826693 := bstep (se 4 (by rfl) ⟨1296252, by rfl⟩ : syracuseStep 13826693 = 2592505) B2592505
theorem B9217795 : Blo 2157435 9217795 := bstep (se 1 (by rfl) ⟨6913346, by rfl⟩ : syracuseStep 9217795 = 13826693) B13826693
theorem B12290393 : Blo 2157435 12290393 := bstep (se 2 (by rfl) ⟨4608897, by rfl⟩ : syracuseStep 12290393 = 9217795) B9217795
theorem B8193595 : Blo 2157435 8193595 := bstep (se 1 (by rfl) ⟨6145196, by rfl⟩ : syracuseStep 8193595 = 12290393) B12290393
theorem B10924793 : Blo 2157435 10924793 := bstep (se 2 (by rfl) ⟨4096797, by rfl⟩ : syracuseStep 10924793 = 8193595) B8193595
theorem B7283195 : Blo 2157435 7283195 := bstep (se 1 (by rfl) ⟨5462396, by rfl⟩ : syracuseStep 7283195 = 10924793) B10924793
theorem B4855463 : Blo 2157435 4855463 := bstep (se 1 (by rfl) ⟨3641597, by rfl⟩ : syracuseStep 4855463 = 7283195) B7283195
theorem B3236975 : Blo 2157435 3236975 := bstep (se 1 (by rfl) ⟨2427731, by rfl⟩ : syracuseStep 3236975 = 4855463) B4855463
theorem B2157983 : Blo 2157435 2157983 := bstep (se 1 (by rfl) ⟨1618487, by rfl⟩ : syracuseStep 2157983 = 3236975) B3236975
theorem B3236981 : Blo 2157435 3236981 := bbase (se 5 (by rfl) ⟨151733, by rfl⟩ : syracuseStep 3236981 = 303467) (by norm_num)
theorem B2157987 : Blo 2157435 2157987 := bstep (se 1 (by rfl) ⟨1618490, by rfl⟩ : syracuseStep 2157987 = 3236981) B3236981
theorem B4096813 : Blo 2157435 4096813 := bbase (se 3 (by rfl) ⟨768152, by rfl⟩ : syracuseStep 4096813 = 1536305) (by norm_num)
theorem B5462417 : Blo 2157435 5462417 := bstep (se 2 (by rfl) ⟨2048406, by rfl⟩ : syracuseStep 5462417 = 4096813) B4096813
theorem B3641611 : Blo 2157435 3641611 := bstep (se 1 (by rfl) ⟨2731208, by rfl⟩ : syracuseStep 3641611 = 5462417) B5462417
theorem B4855481 : Blo 2157435 4855481 := bstep (se 2 (by rfl) ⟨1820805, by rfl⟩ : syracuseStep 4855481 = 3641611) B3641611
theorem B3236987 : Blo 2157435 3236987 := bstep (se 1 (by rfl) ⟨2427740, by rfl⟩ : syracuseStep 3236987 = 4855481) B4855481
theorem B2157991 : Blo 2157435 2157991 := bstep (se 1 (by rfl) ⟨1618493, by rfl⟩ : syracuseStep 2157991 = 3236987) B3236987
theorem B2427745 : Blo 2157435 2427745 := bbase (se 2 (by rfl) ⟨910404, by rfl⟩ : syracuseStep 2427745 = 1820809) (by norm_num)
theorem B3236993 : Blo 2157435 3236993 := bstep (se 2 (by rfl) ⟨1213872, by rfl⟩ : syracuseStep 3236993 = 2427745) B2427745
theorem B2157995 : Blo 2157435 2157995 := bstep (se 1 (by rfl) ⟨1618496, by rfl⟩ : syracuseStep 2157995 = 3236993) B3236993
theorem B5462437 : Blo 2157435 5462437 := bbase (se 4 (by rfl) ⟨512103, by rfl⟩ : syracuseStep 5462437 = 1024207) (by norm_num)
theorem B7283249 : Blo 2157435 7283249 := bstep (se 2 (by rfl) ⟨2731218, by rfl⟩ : syracuseStep 7283249 = 5462437) B5462437
theorem B4855499 : Blo 2157435 4855499 := bstep (se 1 (by rfl) ⟨3641624, by rfl⟩ : syracuseStep 4855499 = 7283249) B7283249
theorem B3236999 : Blo 2157435 3236999 := bstep (se 1 (by rfl) ⟨2427749, by rfl⟩ : syracuseStep 3236999 = 4855499) B4855499
theorem B2157999 : Blo 2157435 2157999 := bstep (se 1 (by rfl) ⟨1618499, by rfl⟩ : syracuseStep 2157999 = 3236999) B3236999
theorem B3237005 : Blo 2157435 3237005 := bbase (se 3 (by rfl) ⟨606938, by rfl⟩ : syracuseStep 3237005 = 1213877) (by norm_num)
theorem B2158003 : Blo 2157435 2158003 := bstep (se 1 (by rfl) ⟨1618502, by rfl⟩ : syracuseStep 2158003 = 3237005) B3237005
theorem B4855517 : Blo 2157435 4855517 := bbase (se 3 (by rfl) ⟨910409, by rfl⟩ : syracuseStep 4855517 = 1820819) (by norm_num)
theorem B3237011 : Blo 2157435 3237011 := bstep (se 1 (by rfl) ⟨2427758, by rfl⟩ : syracuseStep 3237011 = 4855517) B4855517
theorem B2158007 : Blo 2157435 2158007 := bstep (se 1 (by rfl) ⟨1618505, by rfl⟩ : syracuseStep 2158007 = 3237011) B3237011
theorem B3641645 : Blo 2157435 3641645 := bbase (se 3 (by rfl) ⟨682808, by rfl⟩ : syracuseStep 3641645 = 1365617) (by norm_num)
theorem B2427763 : Blo 2157435 2427763 := bstep (se 1 (by rfl) ⟨1820822, by rfl⟩ : syracuseStep 2427763 = 3641645) B3641645
theorem B3237017 : Blo 2157435 3237017 := bstep (se 2 (by rfl) ⟨1213881, by rfl⟩ : syracuseStep 3237017 = 2427763) B2427763
theorem B2158011 : Blo 2157435 2158011 := bstep (se 1 (by rfl) ⟨1618508, by rfl⟩ : syracuseStep 2158011 = 3237017) B3237017
theorem B2335925 : Blo 2157435 2335925 := bbase (se 5 (by rfl) ⟨109496, by rfl⟩ : syracuseStep 2335925 = 218993) (by norm_num)
theorem B6229133 : Blo 2157435 6229133 := bstep (se 3 (by rfl) ⟨1167962, by rfl⟩ : syracuseStep 6229133 = 2335925) B2335925
theorem B4152755 : Blo 2157435 4152755 := bstep (se 1 (by rfl) ⟨3114566, by rfl⟩ : syracuseStep 4152755 = 6229133) B6229133
theorem B2768503 : Blo 2157435 2768503 := bstep (se 1 (by rfl) ⟨2076377, by rfl⟩ : syracuseStep 2768503 = 4152755) B4152755
theorem B3691337 : Blo 2157435 3691337 := bstep (se 2 (by rfl) ⟨1384251, by rfl⟩ : syracuseStep 3691337 = 2768503) B2768503
theorem B9843565 : Blo 2157435 9843565 := bstep (se 3 (by rfl) ⟨1845668, by rfl⟩ : syracuseStep 9843565 = 3691337) B3691337
theorem B13124753 : Blo 2157435 13124753 := bstep (se 2 (by rfl) ⟨4921782, by rfl⟩ : syracuseStep 13124753 = 9843565) B9843565
theorem B8749835 : Blo 2157435 8749835 := bstep (se 1 (by rfl) ⟨6562376, by rfl⟩ : syracuseStep 8749835 = 13124753) B13124753
theorem B5833223 : Blo 2157435 5833223 := bstep (se 1 (by rfl) ⟨4374917, by rfl⟩ : syracuseStep 5833223 = 8749835) B8749835
theorem B3888815 : Blo 2157435 3888815 := bstep (se 1 (by rfl) ⟨2916611, by rfl⟩ : syracuseStep 3888815 = 5833223) B5833223
theorem B41480693 : Blo 2157435 41480693 := bstep (se 5 (by rfl) ⟨1944407, by rfl⟩ : syracuseStep 41480693 = 3888815) B3888815
theorem B27653795 : Blo 2157435 27653795 := bstep (se 1 (by rfl) ⟨20740346, by rfl⟩ : syracuseStep 27653795 = 41480693) B41480693
theorem B18435863 : Blo 2157435 18435863 := bstep (se 1 (by rfl) ⟨13826897, by rfl⟩ : syracuseStep 18435863 = 27653795) B27653795
theorem B12290575 : Blo 2157435 12290575 := bstep (se 1 (by rfl) ⟨9217931, by rfl⟩ : syracuseStep 12290575 = 18435863) B18435863
theorem B16387433 : Blo 2157435 16387433 := bstep (se 2 (by rfl) ⟨6145287, by rfl⟩ : syracuseStep 16387433 = 12290575) B12290575
theorem B10924955 : Blo 2157435 10924955 := bstep (se 1 (by rfl) ⟨8193716, by rfl⟩ : syracuseStep 10924955 = 16387433) B16387433
theorem B7283303 : Blo 2157435 7283303 := bstep (se 1 (by rfl) ⟨5462477, by rfl⟩ : syracuseStep 7283303 = 10924955) B10924955
theorem B4855535 : Blo 2157435 4855535 := bstep (se 1 (by rfl) ⟨3641651, by rfl⟩ : syracuseStep 4855535 = 7283303) B7283303
theorem B3237023 : Blo 2157435 3237023 := bstep (se 1 (by rfl) ⟨2427767, by rfl⟩ : syracuseStep 3237023 = 4855535) B4855535
theorem B2158015 : Blo 2157435 2158015 := bstep (se 1 (by rfl) ⟨1618511, by rfl⟩ : syracuseStep 2158015 = 3237023) B3237023
theorem B3237029 : Blo 2157435 3237029 := bbase (se 4 (by rfl) ⟨303471, by rfl⟩ : syracuseStep 3237029 = 606943) (by norm_num)
theorem B2158019 : Blo 2157435 2158019 := bstep (se 1 (by rfl) ⟨1618514, by rfl⟩ : syracuseStep 2158019 = 3237029) B3237029
theorem B2731249 : Blo 2157435 2731249 := bbase (se 2 (by rfl) ⟨1024218, by rfl⟩ : syracuseStep 2731249 = 2048437) (by norm_num)
theorem B3641665 : Blo 2157435 3641665 := bstep (se 2 (by rfl) ⟨1365624, by rfl⟩ : syracuseStep 3641665 = 2731249) B2731249
theorem B4855553 : Blo 2157435 4855553 := bstep (se 2 (by rfl) ⟨1820832, by rfl⟩ : syracuseStep 4855553 = 3641665) B3641665
theorem B3237035 : Blo 2157435 3237035 := bstep (se 1 (by rfl) ⟨2427776, by rfl⟩ : syracuseStep 3237035 = 4855553) B4855553
theorem B2158023 : Blo 2157435 2158023 := bstep (se 1 (by rfl) ⟨1618517, by rfl⟩ : syracuseStep 2158023 = 3237035) B3237035
theorem B2427781 : Blo 2157435 2427781 := bbase (se 4 (by rfl) ⟨227604, by rfl⟩ : syracuseStep 2427781 = 455209) (by norm_num)
theorem B3237041 : Blo 2157435 3237041 := bstep (se 2 (by rfl) ⟨1213890, by rfl⟩ : syracuseStep 3237041 = 2427781) B2427781
theorem B2158027 : Blo 2157435 2158027 := bstep (se 1 (by rfl) ⟨1618520, by rfl⟩ : syracuseStep 2158027 = 3237041) B3237041
theorem B8305573 : Blo 2157435 8305573 := bbase (se 4 (by rfl) ⟨778647, by rfl⟩ : syracuseStep 8305573 = 1557295) (by norm_num)
theorem B11074097 : Blo 2157435 11074097 := bstep (se 2 (by rfl) ⟨4152786, by rfl⟩ : syracuseStep 11074097 = 8305573) B8305573
theorem B29530925 : Blo 2157435 29530925 := bstep (se 3 (by rfl) ⟨5537048, by rfl⟩ : syracuseStep 29530925 = 11074097) B11074097
theorem B19687283 : Blo 2157435 19687283 := bstep (se 1 (by rfl) ⟨14765462, by rfl⟩ : syracuseStep 19687283 = 29530925) B29530925
theorem B13124855 : Blo 2157435 13124855 := bstep (se 1 (by rfl) ⟨9843641, by rfl⟩ : syracuseStep 13124855 = 19687283) B19687283
theorem B8749903 : Blo 2157435 8749903 := bstep (se 1 (by rfl) ⟨6562427, by rfl⟩ : syracuseStep 8749903 = 13124855) B13124855
theorem B11666537 : Blo 2157435 11666537 := bstep (se 2 (by rfl) ⟨4374951, by rfl⟩ : syracuseStep 11666537 = 8749903) B8749903
theorem B7777691 : Blo 2157435 7777691 := bstep (se 1 (by rfl) ⟨5833268, by rfl⟩ : syracuseStep 7777691 = 11666537) B11666537
theorem B5185127 : Blo 2157435 5185127 := bstep (se 1 (by rfl) ⟨3888845, by rfl⟩ : syracuseStep 5185127 = 7777691) B7777691
theorem B3456751 : Blo 2157435 3456751 := bstep (se 1 (by rfl) ⟨2592563, by rfl⟩ : syracuseStep 3456751 = 5185127) B5185127
theorem B4609001 : Blo 2157435 4609001 := bstep (se 2 (by rfl) ⟨1728375, by rfl⟩ : syracuseStep 4609001 = 3456751) B3456751
theorem B3072667 : Blo 2157435 3072667 := bstep (se 1 (by rfl) ⟨2304500, by rfl⟩ : syracuseStep 3072667 = 4609001) B4609001
theorem B4096889 : Blo 2157435 4096889 := bstep (se 2 (by rfl) ⟨1536333, by rfl⟩ : syracuseStep 4096889 = 3072667) B3072667
theorem B2731259 : Blo 2157435 2731259 := bstep (se 1 (by rfl) ⟨2048444, by rfl⟩ : syracuseStep 2731259 = 4096889) B4096889
theorem B7283357 : Blo 2157435 7283357 := bstep (se 3 (by rfl) ⟨1365629, by rfl⟩ : syracuseStep 7283357 = 2731259) B2731259
theorem B4855571 : Blo 2157435 4855571 := bstep (se 1 (by rfl) ⟨3641678, by rfl⟩ : syracuseStep 4855571 = 7283357) B7283357
theorem B3237047 : Blo 2157435 3237047 := bstep (se 1 (by rfl) ⟨2427785, by rfl⟩ : syracuseStep 3237047 = 4855571) B4855571
theorem B2158031 : Blo 2157435 2158031 := bstep (se 1 (by rfl) ⟨1618523, by rfl⟩ : syracuseStep 2158031 = 3237047) B3237047
theorem B3237053 : Blo 2157435 3237053 := bbase (se 3 (by rfl) ⟨606947, by rfl⟩ : syracuseStep 3237053 = 1213895) (by norm_num)
theorem B2158035 : Blo 2157435 2158035 := bstep (se 1 (by rfl) ⟨1618526, by rfl⟩ : syracuseStep 2158035 = 3237053) B3237053
theorem B4855589 : Blo 2157435 4855589 := bbase (se 4 (by rfl) ⟨455211, by rfl⟩ : syracuseStep 4855589 = 910423) (by norm_num)
theorem B3237059 : Blo 2157435 3237059 := bstep (se 1 (by rfl) ⟨2427794, by rfl⟩ : syracuseStep 3237059 = 4855589) B4855589
theorem B2158039 : Blo 2157435 2158039 := bstep (se 1 (by rfl) ⟨1618529, by rfl⟩ : syracuseStep 2158039 = 3237059) B3237059
theorem B5462549 : Blo 2157435 5462549 := bbase (se 6 (by rfl) ⟨128028, by rfl⟩ : syracuseStep 5462549 = 256057) (by norm_num)
theorem B3641699 : Blo 2157435 3641699 := bstep (se 1 (by rfl) ⟨2731274, by rfl⟩ : syracuseStep 3641699 = 5462549) B5462549
theorem B2427799 : Blo 2157435 2427799 := bstep (se 1 (by rfl) ⟨1820849, by rfl⟩ : syracuseStep 2427799 = 3641699) B3641699
theorem B3237065 : Blo 2157435 3237065 := bstep (se 2 (by rfl) ⟨1213899, by rfl⟩ : syracuseStep 3237065 = 2427799) B2427799
theorem B2158043 : Blo 2157435 2158043 := bstep (se 1 (by rfl) ⟨1618532, by rfl⟩ : syracuseStep 2158043 = 3237065) B3237065
theorem B9218069 : Blo 2157435 9218069 := bbase (se 6 (by rfl) ⟨216048, by rfl⟩ : syracuseStep 9218069 = 432097) (by norm_num)
theorem B6145379 : Blo 2157435 6145379 := bstep (se 1 (by rfl) ⟨4609034, by rfl⟩ : syracuseStep 6145379 = 9218069) B9218069
theorem B4096919 : Blo 2157435 4096919 := bstep (se 1 (by rfl) ⟨3072689, by rfl⟩ : syracuseStep 4096919 = 6145379) B6145379
theorem B10925117 : Blo 2157435 10925117 := bstep (se 3 (by rfl) ⟨2048459, by rfl⟩ : syracuseStep 10925117 = 4096919) B4096919
theorem B7283411 : Blo 2157435 7283411 := bstep (se 1 (by rfl) ⟨5462558, by rfl⟩ : syracuseStep 7283411 = 10925117) B10925117
theorem B4855607 : Blo 2157435 4855607 := bstep (se 1 (by rfl) ⟨3641705, by rfl⟩ : syracuseStep 4855607 = 7283411) B7283411
theorem B3237071 : Blo 2157435 3237071 := bstep (se 1 (by rfl) ⟨2427803, by rfl⟩ : syracuseStep 3237071 = 4855607) B4855607
theorem B2158047 : Blo 2157435 2158047 := bstep (se 1 (by rfl) ⟨1618535, by rfl⟩ : syracuseStep 2158047 = 3237071) B3237071
theorem B3237077 : Blo 2157435 3237077 := bbase (se 7 (by rfl) ⟨37934, by rfl⟩ : syracuseStep 3237077 = 75869) (by norm_num)
theorem B2158051 : Blo 2157435 2158051 := bstep (se 1 (by rfl) ⟨1618538, by rfl⟩ : syracuseStep 2158051 = 3237077) B3237077
theorem B3072701 : Blo 2157435 3072701 := bbase (se 3 (by rfl) ⟨576131, by rfl⟩ : syracuseStep 3072701 = 1152263) (by norm_num)
theorem B8193869 : Blo 2157435 8193869 := bstep (se 3 (by rfl) ⟨1536350, by rfl⟩ : syracuseStep 8193869 = 3072701) B3072701
theorem B5462579 : Blo 2157435 5462579 := bstep (se 1 (by rfl) ⟨4096934, by rfl⟩ : syracuseStep 5462579 = 8193869) B8193869
theorem B3641719 : Blo 2157435 3641719 := bstep (se 1 (by rfl) ⟨2731289, by rfl⟩ : syracuseStep 3641719 = 5462579) B5462579
theorem B4855625 : Blo 2157435 4855625 := bstep (se 2 (by rfl) ⟨1820859, by rfl⟩ : syracuseStep 4855625 = 3641719) B3641719
theorem B3237083 : Blo 2157435 3237083 := bstep (se 1 (by rfl) ⟨2427812, by rfl⟩ : syracuseStep 3237083 = 4855625) B4855625
theorem B2158055 : Blo 2157435 2158055 := bstep (se 1 (by rfl) ⟨1618541, by rfl⟩ : syracuseStep 2158055 = 3237083) B3237083
theorem B2427817 : Blo 2157435 2427817 := bbase (se 2 (by rfl) ⟨910431, by rfl⟩ : syracuseStep 2427817 = 1820863) (by norm_num)
theorem B3237089 : Blo 2157435 3237089 := bstep (se 2 (by rfl) ⟨1213908, by rfl⟩ : syracuseStep 3237089 = 2427817) B2427817
theorem B2158059 : Blo 2157435 2158059 := bstep (se 1 (by rfl) ⟨1618544, by rfl⟩ : syracuseStep 2158059 = 3237089) B3237089
theorem B10370405 : Blo 2157435 10370405 := bbase (se 4 (by rfl) ⟨972225, by rfl⟩ : syracuseStep 10370405 = 1944451) (by norm_num)
theorem B6913603 : Blo 2157435 6913603 := bstep (se 1 (by rfl) ⟨5185202, by rfl⟩ : syracuseStep 6913603 = 10370405) B10370405
theorem B9218137 : Blo 2157435 9218137 := bstep (se 2 (by rfl) ⟨3456801, by rfl⟩ : syracuseStep 9218137 = 6913603) B6913603
theorem B12290849 : Blo 2157435 12290849 := bstep (se 2 (by rfl) ⟨4609068, by rfl⟩ : syracuseStep 12290849 = 9218137) B9218137
theorem B8193899 : Blo 2157435 8193899 := bstep (se 1 (by rfl) ⟨6145424, by rfl⟩ : syracuseStep 8193899 = 12290849) B12290849
theorem B5462599 : Blo 2157435 5462599 := bstep (se 1 (by rfl) ⟨4096949, by rfl⟩ : syracuseStep 5462599 = 8193899) B8193899
theorem B7283465 : Blo 2157435 7283465 := bstep (se 2 (by rfl) ⟨2731299, by rfl⟩ : syracuseStep 7283465 = 5462599) B5462599
theorem B4855643 : Blo 2157435 4855643 := bstep (se 1 (by rfl) ⟨3641732, by rfl⟩ : syracuseStep 4855643 = 7283465) B7283465
theorem B3237095 : Blo 2157435 3237095 := bstep (se 1 (by rfl) ⟨2427821, by rfl⟩ : syracuseStep 3237095 = 4855643) B4855643
theorem B2158063 : Blo 2157435 2158063 := bstep (se 1 (by rfl) ⟨1618547, by rfl⟩ : syracuseStep 2158063 = 3237095) B3237095
theorem B3237101 : Blo 2157435 3237101 := bbase (se 3 (by rfl) ⟨606956, by rfl⟩ : syracuseStep 3237101 = 1213913) (by norm_num)
theorem B2158067 : Blo 2157435 2158067 := bstep (se 1 (by rfl) ⟨1618550, by rfl⟩ : syracuseStep 2158067 = 3237101) B3237101
theorem B4855661 : Blo 2157435 4855661 := bbase (se 3 (by rfl) ⟨910436, by rfl⟩ : syracuseStep 4855661 = 1820873) (by norm_num)
theorem B3237107 : Blo 2157435 3237107 := bstep (se 1 (by rfl) ⟨2427830, by rfl⟩ : syracuseStep 3237107 = 4855661) B4855661
theorem B2158071 : Blo 2157435 2158071 := bstep (se 1 (by rfl) ⟨1618553, by rfl⟩ : syracuseStep 2158071 = 3237107) B3237107
theorem B4096973 : Blo 2157435 4096973 := bbase (se 3 (by rfl) ⟨768182, by rfl⟩ : syracuseStep 4096973 = 1536365) (by norm_num)
theorem B2731315 : Blo 2157435 2731315 := bstep (se 1 (by rfl) ⟨2048486, by rfl⟩ : syracuseStep 2731315 = 4096973) B4096973
theorem B3641753 : Blo 2157435 3641753 := bstep (se 2 (by rfl) ⟨1365657, by rfl⟩ : syracuseStep 3641753 = 2731315) B2731315
theorem B2427835 : Blo 2157435 2427835 := bstep (se 1 (by rfl) ⟨1820876, by rfl⟩ : syracuseStep 2427835 = 3641753) B3641753
theorem B3237113 : Blo 2157435 3237113 := bstep (se 2 (by rfl) ⟨1213917, by rfl⟩ : syracuseStep 3237113 = 2427835) B2427835
theorem B2158075 : Blo 2157435 2158075 := bstep (se 1 (by rfl) ⟨1618556, by rfl⟩ : syracuseStep 2158075 = 3237113) B3237113
theorem B13304213 : Blo 2157435 13304213 := bbase (se 6 (by rfl) ⟨311817, by rfl⟩ : syracuseStep 13304213 = 623635) (by norm_num)
theorem B8869475 : Blo 2157435 8869475 := bstep (se 1 (by rfl) ⟨6652106, by rfl⟩ : syracuseStep 8869475 = 13304213) B13304213
theorem B5912983 : Blo 2157435 5912983 := bstep (se 1 (by rfl) ⟨4434737, by rfl⟩ : syracuseStep 5912983 = 8869475) B8869475
theorem B31535909 : Blo 2157435 31535909 := bstep (se 4 (by rfl) ⟨2956491, by rfl⟩ : syracuseStep 31535909 = 5912983) B5912983
theorem B21023939 : Blo 2157435 21023939 := bstep (se 1 (by rfl) ⟨15767954, by rfl⟩ : syracuseStep 21023939 = 31535909) B31535909
theorem B14015959 : Blo 2157435 14015959 := bstep (se 1 (by rfl) ⟨10511969, by rfl⟩ : syracuseStep 14015959 = 21023939) B21023939
theorem B74751781 : Blo 2157435 74751781 := bstep (se 4 (by rfl) ⟨7007979, by rfl⟩ : syracuseStep 74751781 = 14015959) B14015959
theorem B99669041 : Blo 2157435 99669041 := bstep (se 2 (by rfl) ⟨37375890, by rfl⟩ : syracuseStep 99669041 = 74751781) B74751781
theorem B66446027 : Blo 2157435 66446027 := bstep (se 1 (by rfl) ⟨49834520, by rfl⟩ : syracuseStep 66446027 = 99669041) B99669041
theorem B44297351 : Blo 2157435 44297351 := bstep (se 1 (by rfl) ⟨33223013, by rfl⟩ : syracuseStep 44297351 = 66446027) B66446027
theorem B29531567 : Blo 2157435 29531567 := bstep (se 1 (by rfl) ⟨22148675, by rfl⟩ : syracuseStep 29531567 = 44297351) B44297351
theorem B19687711 : Blo 2157435 19687711 := bstep (se 1 (by rfl) ⟨14765783, by rfl⟩ : syracuseStep 19687711 = 29531567) B29531567
theorem B26250281 : Blo 2157435 26250281 := bstep (se 2 (by rfl) ⟨9843855, by rfl⟩ : syracuseStep 26250281 = 19687711) B19687711
theorem B17500187 : Blo 2157435 17500187 := bstep (se 1 (by rfl) ⟨13125140, by rfl⟩ : syracuseStep 17500187 = 26250281) B26250281
theorem B11666791 : Blo 2157435 11666791 := bstep (se 1 (by rfl) ⟨8750093, by rfl⟩ : syracuseStep 11666791 = 17500187) B17500187
theorem B15555721 : Blo 2157435 15555721 := bstep (se 2 (by rfl) ⟨5833395, by rfl⟩ : syracuseStep 15555721 = 11666791) B11666791
theorem B20740961 : Blo 2157435 20740961 := bstep (se 2 (by rfl) ⟨7777860, by rfl⟩ : syracuseStep 20740961 = 15555721) B15555721
theorem B55309229 : Blo 2157435 55309229 := bstep (se 3 (by rfl) ⟨10370480, by rfl⟩ : syracuseStep 55309229 = 20740961) B20740961
theorem B36872819 : Blo 2157435 36872819 := bstep (se 1 (by rfl) ⟨27654614, by rfl⟩ : syracuseStep 36872819 = 55309229) B55309229
theorem B24581879 : Blo 2157435 24581879 := bstep (se 1 (by rfl) ⟨18436409, by rfl⟩ : syracuseStep 24581879 = 36872819) B36872819
theorem B16387919 : Blo 2157435 16387919 := bstep (se 1 (by rfl) ⟨12290939, by rfl⟩ : syracuseStep 16387919 = 24581879) B24581879
theorem B10925279 : Blo 2157435 10925279 := bstep (se 1 (by rfl) ⟨8193959, by rfl⟩ : syracuseStep 10925279 = 16387919) B16387919
theorem B7283519 : Blo 2157435 7283519 := bstep (se 1 (by rfl) ⟨5462639, by rfl⟩ : syracuseStep 7283519 = 10925279) B10925279
theorem B4855679 : Blo 2157435 4855679 := bstep (se 1 (by rfl) ⟨3641759, by rfl⟩ : syracuseStep 4855679 = 7283519) B7283519
theorem B3237119 : Blo 2157435 3237119 := bstep (se 1 (by rfl) ⟨2427839, by rfl⟩ : syracuseStep 3237119 = 4855679) B4855679
theorem B2158079 : Blo 2157435 2158079 := bstep (se 1 (by rfl) ⟨1618559, by rfl⟩ : syracuseStep 2158079 = 3237119) B3237119
theorem B3237125 : Blo 2157435 3237125 := bbase (se 4 (by rfl) ⟨303480, by rfl⟩ : syracuseStep 3237125 = 606961) (by norm_num)
theorem B2158083 : Blo 2157435 2158083 := bstep (se 1 (by rfl) ⟨1618562, by rfl⟩ : syracuseStep 2158083 = 3237125) B3237125
theorem B3641773 : Blo 2157435 3641773 := bbase (se 3 (by rfl) ⟨682832, by rfl⟩ : syracuseStep 3641773 = 1365665) (by norm_num)
theorem B4855697 : Blo 2157435 4855697 := bstep (se 2 (by rfl) ⟨1820886, by rfl⟩ : syracuseStep 4855697 = 3641773) B3641773
theorem B3237131 : Blo 2157435 3237131 := bstep (se 1 (by rfl) ⟨2427848, by rfl⟩ : syracuseStep 3237131 = 4855697) B4855697
theorem B2158087 : Blo 2157435 2158087 := bstep (se 1 (by rfl) ⟨1618565, by rfl⟩ : syracuseStep 2158087 = 3237131) B3237131
theorem B2427853 : Blo 2157435 2427853 := bbase (se 3 (by rfl) ⟨455222, by rfl⟩ : syracuseStep 2427853 = 910445) (by norm_num)
theorem B3237137 : Blo 2157435 3237137 := bstep (se 2 (by rfl) ⟨1213926, by rfl⟩ : syracuseStep 3237137 = 2427853) B2427853
theorem B2158091 : Blo 2157435 2158091 := bstep (se 1 (by rfl) ⟨1618568, by rfl⟩ : syracuseStep 2158091 = 3237137) B3237137
theorem B7283573 : Blo 2157435 7283573 := bbase (se 5 (by rfl) ⟨341417, by rfl⟩ : syracuseStep 7283573 = 682835) (by norm_num)
theorem B4855715 : Blo 2157435 4855715 := bstep (se 1 (by rfl) ⟨3641786, by rfl⟩ : syracuseStep 4855715 = 7283573) B7283573
theorem B3237143 : Blo 2157435 3237143 := bstep (se 1 (by rfl) ⟨2427857, by rfl⟩ : syracuseStep 3237143 = 4855715) B4855715
theorem B2158095 : Blo 2157435 2158095 := bstep (se 1 (by rfl) ⟨1618571, by rfl⟩ : syracuseStep 2158095 = 3237143) B3237143
theorem B3237149 : Blo 2157435 3237149 := bbase (se 3 (by rfl) ⟨606965, by rfl⟩ : syracuseStep 3237149 = 1213931) (by norm_num)
theorem B2158099 : Blo 2157435 2158099 := bstep (se 1 (by rfl) ⟨1618574, by rfl⟩ : syracuseStep 2158099 = 3237149) B3237149
theorem B4855733 : Blo 2157435 4855733 := bbase (se 5 (by rfl) ⟨227612, by rfl⟩ : syracuseStep 4855733 = 455225) (by norm_num)
theorem B3237155 : Blo 2157435 3237155 := bstep (se 1 (by rfl) ⟨2427866, by rfl⟩ : syracuseStep 3237155 = 4855733) B4855733
theorem B2158103 : Blo 2157435 2158103 := bstep (se 1 (by rfl) ⟨1618577, by rfl⟩ : syracuseStep 2158103 = 3237155) B3237155
theorem B5185309 : Blo 2157435 5185309 := bbase (se 3 (by rfl) ⟨972245, by rfl⟩ : syracuseStep 5185309 = 1944491) (by norm_num)
theorem B6913745 : Blo 2157435 6913745 := bstep (se 2 (by rfl) ⟨2592654, by rfl⟩ : syracuseStep 6913745 = 5185309) B5185309
theorem B4609163 : Blo 2157435 4609163 := bstep (se 1 (by rfl) ⟨3456872, by rfl⟩ : syracuseStep 4609163 = 6913745) B6913745
theorem B12291101 : Blo 2157435 12291101 := bstep (se 3 (by rfl) ⟨2304581, by rfl⟩ : syracuseStep 12291101 = 4609163) B4609163
theorem B8194067 : Blo 2157435 8194067 := bstep (se 1 (by rfl) ⟨6145550, by rfl⟩ : syracuseStep 8194067 = 12291101) B12291101
theorem B5462711 : Blo 2157435 5462711 := bstep (se 1 (by rfl) ⟨4097033, by rfl⟩ : syracuseStep 5462711 = 8194067) B8194067
theorem B3641807 : Blo 2157435 3641807 := bstep (se 1 (by rfl) ⟨2731355, by rfl⟩ : syracuseStep 3641807 = 5462711) B5462711
theorem B2427871 : Blo 2157435 2427871 := bstep (se 1 (by rfl) ⟨1820903, by rfl⟩ : syracuseStep 2427871 = 3641807) B3641807
theorem B3237161 : Blo 2157435 3237161 := bstep (se 2 (by rfl) ⟨1213935, by rfl⟩ : syracuseStep 3237161 = 2427871) B2427871
theorem B2158107 : Blo 2157435 2158107 := bstep (se 1 (by rfl) ⟨1618580, by rfl⟩ : syracuseStep 2158107 = 3237161) B3237161
theorem B3888989 : Blo 2157435 3888989 := bbase (se 3 (by rfl) ⟨729185, by rfl⟩ : syracuseStep 3888989 = 1458371) (by norm_num)
theorem B2592659 : Blo 2157435 2592659 := bstep (se 1 (by rfl) ⟨1944494, by rfl⟩ : syracuseStep 2592659 = 3888989) B3888989
theorem B6913757 : Blo 2157435 6913757 := bstep (se 3 (by rfl) ⟨1296329, by rfl⟩ : syracuseStep 6913757 = 2592659) B2592659
theorem B4609171 : Blo 2157435 4609171 := bstep (se 1 (by rfl) ⟨3456878, by rfl⟩ : syracuseStep 4609171 = 6913757) B6913757
theorem B6145561 : Blo 2157435 6145561 := bstep (se 2 (by rfl) ⟨2304585, by rfl⟩ : syracuseStep 6145561 = 4609171) B4609171
theorem B8194081 : Blo 2157435 8194081 := bstep (se 2 (by rfl) ⟨3072780, by rfl⟩ : syracuseStep 8194081 = 6145561) B6145561
theorem B10925441 : Blo 2157435 10925441 := bstep (se 2 (by rfl) ⟨4097040, by rfl⟩ : syracuseStep 10925441 = 8194081) B8194081
theorem B7283627 : Blo 2157435 7283627 := bstep (se 1 (by rfl) ⟨5462720, by rfl⟩ : syracuseStep 7283627 = 10925441) B10925441
theorem B4855751 : Blo 2157435 4855751 := bstep (se 1 (by rfl) ⟨3641813, by rfl⟩ : syracuseStep 4855751 = 7283627) B7283627
theorem B3237167 : Blo 2157435 3237167 := bstep (se 1 (by rfl) ⟨2427875, by rfl⟩ : syracuseStep 3237167 = 4855751) B4855751
theorem B2158111 : Blo 2157435 2158111 := bstep (se 1 (by rfl) ⟨1618583, by rfl⟩ : syracuseStep 2158111 = 3237167) B3237167
theorem B3237173 : Blo 2157435 3237173 := bbase (se 5 (by rfl) ⟨151742, by rfl⟩ : syracuseStep 3237173 = 303485) (by norm_num)
theorem B2158115 : Blo 2157435 2158115 := bstep (se 1 (by rfl) ⟨1618586, by rfl⟩ : syracuseStep 2158115 = 3237173) B3237173
theorem B5462741 : Blo 2157435 5462741 := bbase (se 7 (by rfl) ⟨64016, by rfl⟩ : syracuseStep 5462741 = 128033) (by norm_num)
theorem B3641827 : Blo 2157435 3641827 := bstep (se 1 (by rfl) ⟨2731370, by rfl⟩ : syracuseStep 3641827 = 5462741) B5462741
theorem B4855769 : Blo 2157435 4855769 := bstep (se 2 (by rfl) ⟨1820913, by rfl⟩ : syracuseStep 4855769 = 3641827) B3641827
theorem B3237179 : Blo 2157435 3237179 := bstep (se 1 (by rfl) ⟨2427884, by rfl⟩ : syracuseStep 3237179 = 4855769) B4855769
theorem B2158119 : Blo 2157435 2158119 := bstep (se 1 (by rfl) ⟨1618589, by rfl⟩ : syracuseStep 2158119 = 3237179) B3237179
theorem B2427889 : Blo 2157435 2427889 := bbase (se 2 (by rfl) ⟨910458, by rfl⟩ : syracuseStep 2427889 = 1820917) (by norm_num)
theorem B3237185 : Blo 2157435 3237185 := bstep (se 2 (by rfl) ⟨1213944, by rfl⟩ : syracuseStep 3237185 = 2427889) B2427889
theorem B2158123 : Blo 2157435 2158123 := bstep (se 1 (by rfl) ⟨1618592, by rfl⟩ : syracuseStep 2158123 = 3237185) B3237185
theorem B4672093 : Blo 2157435 4672093 := bbase (se 3 (by rfl) ⟨876017, by rfl⟩ : syracuseStep 4672093 = 1752035) (by norm_num)
theorem B6229457 : Blo 2157435 6229457 := bstep (se 2 (by rfl) ⟨2336046, by rfl⟩ : syracuseStep 6229457 = 4672093) B4672093
theorem B4152971 : Blo 2157435 4152971 := bstep (se 1 (by rfl) ⟨3114728, by rfl⟩ : syracuseStep 4152971 = 6229457) B6229457
theorem B11074589 : Blo 2157435 11074589 := bstep (se 3 (by rfl) ⟨2076485, by rfl⟩ : syracuseStep 11074589 = 4152971) B4152971
theorem B7383059 : Blo 2157435 7383059 := bstep (se 1 (by rfl) ⟨5537294, by rfl⟩ : syracuseStep 7383059 = 11074589) B11074589
theorem B4922039 : Blo 2157435 4922039 := bstep (se 1 (by rfl) ⟨3691529, by rfl⟩ : syracuseStep 4922039 = 7383059) B7383059
theorem B3281359 : Blo 2157435 3281359 := bstep (se 1 (by rfl) ⟨2461019, by rfl⟩ : syracuseStep 3281359 = 4922039) B4922039
theorem B4375145 : Blo 2157435 4375145 := bstep (se 2 (by rfl) ⟨1640679, by rfl⟩ : syracuseStep 4375145 = 3281359) B3281359
theorem B11667053 : Blo 2157435 11667053 := bstep (se 3 (by rfl) ⟨2187572, by rfl⟩ : syracuseStep 11667053 = 4375145) B4375145
theorem B7778035 : Blo 2157435 7778035 := bstep (se 1 (by rfl) ⟨5833526, by rfl⟩ : syracuseStep 7778035 = 11667053) B11667053
theorem B10370713 : Blo 2157435 10370713 := bstep (se 2 (by rfl) ⟨3889017, by rfl⟩ : syracuseStep 10370713 = 7778035) B7778035
theorem B13827617 : Blo 2157435 13827617 := bstep (se 2 (by rfl) ⟨5185356, by rfl⟩ : syracuseStep 13827617 = 10370713) B10370713
theorem B9218411 : Blo 2157435 9218411 := bstep (se 1 (by rfl) ⟨6913808, by rfl⟩ : syracuseStep 9218411 = 13827617) B13827617
theorem B6145607 : Blo 2157435 6145607 := bstep (se 1 (by rfl) ⟨4609205, by rfl⟩ : syracuseStep 6145607 = 9218411) B9218411
theorem B4097071 : Blo 2157435 4097071 := bstep (se 1 (by rfl) ⟨3072803, by rfl⟩ : syracuseStep 4097071 = 6145607) B6145607
theorem B5462761 : Blo 2157435 5462761 := bstep (se 2 (by rfl) ⟨2048535, by rfl⟩ : syracuseStep 5462761 = 4097071) B4097071
theorem B7283681 : Blo 2157435 7283681 := bstep (se 2 (by rfl) ⟨2731380, by rfl⟩ : syracuseStep 7283681 = 5462761) B5462761
theorem B4855787 : Blo 2157435 4855787 := bstep (se 1 (by rfl) ⟨3641840, by rfl⟩ : syracuseStep 4855787 = 7283681) B7283681
theorem B3237191 : Blo 2157435 3237191 := bstep (se 1 (by rfl) ⟨2427893, by rfl⟩ : syracuseStep 3237191 = 4855787) B4855787
theorem B2158127 : Blo 2157435 2158127 := bstep (se 1 (by rfl) ⟨1618595, by rfl⟩ : syracuseStep 2158127 = 3237191) B3237191
theorem B3237197 : Blo 2157435 3237197 := bbase (se 3 (by rfl) ⟨606974, by rfl⟩ : syracuseStep 3237197 = 1213949) (by norm_num)
theorem B2158131 : Blo 2157435 2158131 := bstep (se 1 (by rfl) ⟨1618598, by rfl⟩ : syracuseStep 2158131 = 3237197) B3237197
theorem B4855805 : Blo 2157435 4855805 := bbase (se 3 (by rfl) ⟨910463, by rfl⟩ : syracuseStep 4855805 = 1820927) (by norm_num)
theorem B3237203 : Blo 2157435 3237203 := bstep (se 1 (by rfl) ⟨2427902, by rfl⟩ : syracuseStep 3237203 = 4855805) B4855805
theorem B2158135 : Blo 2157435 2158135 := bstep (se 1 (by rfl) ⟨1618601, by rfl⟩ : syracuseStep 2158135 = 3237203) B3237203
theorem B3641861 : Blo 2157435 3641861 := bbase (se 4 (by rfl) ⟨341424, by rfl⟩ : syracuseStep 3641861 = 682849) (by norm_num)
theorem B2427907 : Blo 2157435 2427907 := bstep (se 1 (by rfl) ⟨1820930, by rfl⟩ : syracuseStep 2427907 = 3641861) B3641861
theorem B3237209 : Blo 2157435 3237209 := bstep (se 2 (by rfl) ⟨1213953, by rfl⟩ : syracuseStep 3237209 = 2427907) B2427907
theorem B2158139 : Blo 2157435 2158139 := bstep (se 1 (by rfl) ⟨1618604, by rfl⟩ : syracuseStep 2158139 = 3237209) B3237209
theorem B16388405 : Blo 2157435 16388405 := bbase (se 5 (by rfl) ⟨768206, by rfl⟩ : syracuseStep 16388405 = 1536413) (by norm_num)
theorem B10925603 : Blo 2157435 10925603 := bstep (se 1 (by rfl) ⟨8194202, by rfl⟩ : syracuseStep 10925603 = 16388405) B16388405
theorem B7283735 : Blo 2157435 7283735 := bstep (se 1 (by rfl) ⟨5462801, by rfl⟩ : syracuseStep 7283735 = 10925603) B10925603
theorem B4855823 : Blo 2157435 4855823 := bstep (se 1 (by rfl) ⟨3641867, by rfl⟩ : syracuseStep 4855823 = 7283735) B7283735
theorem B3237215 : Blo 2157435 3237215 := bstep (se 1 (by rfl) ⟨2427911, by rfl⟩ : syracuseStep 3237215 = 4855823) B4855823
theorem B2158143 : Blo 2157435 2158143 := bstep (se 1 (by rfl) ⟨1618607, by rfl⟩ : syracuseStep 2158143 = 3237215) B3237215
theorem B3237221 : Blo 2157435 3237221 := bbase (se 4 (by rfl) ⟨303489, by rfl⟩ : syracuseStep 3237221 = 606979) (by norm_num)
theorem B2158147 : Blo 2157435 2158147 := bstep (se 1 (by rfl) ⟨1618610, by rfl⟩ : syracuseStep 2158147 = 3237221) B3237221
theorem B4097117 : Blo 2157435 4097117 := bbase (se 3 (by rfl) ⟨768209, by rfl⟩ : syracuseStep 4097117 = 1536419) (by norm_num)
theorem B2731411 : Blo 2157435 2731411 := bstep (se 1 (by rfl) ⟨2048558, by rfl⟩ : syracuseStep 2731411 = 4097117) B4097117
theorem B3641881 : Blo 2157435 3641881 := bstep (se 2 (by rfl) ⟨1365705, by rfl⟩ : syracuseStep 3641881 = 2731411) B2731411
theorem B4855841 : Blo 2157435 4855841 := bstep (se 2 (by rfl) ⟨1820940, by rfl⟩ : syracuseStep 4855841 = 3641881) B3641881
theorem B3237227 : Blo 2157435 3237227 := bstep (se 1 (by rfl) ⟨2427920, by rfl⟩ : syracuseStep 3237227 = 4855841) B4855841
theorem B2158151 : Blo 2157435 2158151 := bstep (se 1 (by rfl) ⟨1618613, by rfl⟩ : syracuseStep 2158151 = 3237227) B3237227
theorem B2427925 : Blo 2157435 2427925 := bbase (se 6 (by rfl) ⟨56904, by rfl⟩ : syracuseStep 2427925 = 113809) (by norm_num)
theorem B3237233 : Blo 2157435 3237233 := bstep (se 2 (by rfl) ⟨1213962, by rfl⟩ : syracuseStep 3237233 = 2427925) B2427925
theorem B2158155 : Blo 2157435 2158155 := bstep (se 1 (by rfl) ⟨1618616, by rfl⟩ : syracuseStep 2158155 = 3237233) B3237233
theorem B2731421 : Blo 2157435 2731421 := bbase (se 3 (by rfl) ⟨512141, by rfl⟩ : syracuseStep 2731421 = 1024283) (by norm_num)
theorem B7283789 : Blo 2157435 7283789 := bstep (se 3 (by rfl) ⟨1365710, by rfl⟩ : syracuseStep 7283789 = 2731421) B2731421
theorem B4855859 : Blo 2157435 4855859 := bstep (se 1 (by rfl) ⟨3641894, by rfl⟩ : syracuseStep 4855859 = 7283789) B7283789
theorem B3237239 : Blo 2157435 3237239 := bstep (se 1 (by rfl) ⟨2427929, by rfl⟩ : syracuseStep 3237239 = 4855859) B4855859
theorem B2158159 : Blo 2157435 2158159 := bstep (se 1 (by rfl) ⟨1618619, by rfl⟩ : syracuseStep 2158159 = 3237239) B3237239
theorem B3237245 : Blo 2157435 3237245 := bbase (se 3 (by rfl) ⟨606983, by rfl⟩ : syracuseStep 3237245 = 1213967) (by norm_num)
theorem B2158163 : Blo 2157435 2158163 := bstep (se 1 (by rfl) ⟨1618622, by rfl⟩ : syracuseStep 2158163 = 3237245) B3237245
theorem B4855877 : Blo 2157435 4855877 := bbase (se 4 (by rfl) ⟨455238, by rfl⟩ : syracuseStep 4855877 = 910477) (by norm_num)
theorem B3237251 : Blo 2157435 3237251 := bstep (se 1 (by rfl) ⟨2427938, by rfl⟩ : syracuseStep 3237251 = 4855877) B4855877
theorem B2158167 : Blo 2157435 2158167 := bstep (se 1 (by rfl) ⟨1618625, by rfl⟩ : syracuseStep 2158167 = 3237251) B3237251
theorem B6145733 : Blo 2157435 6145733 := bbase (se 4 (by rfl) ⟨576162, by rfl⟩ : syracuseStep 6145733 = 1152325) (by norm_num)
theorem B4097155 : Blo 2157435 4097155 := bstep (se 1 (by rfl) ⟨3072866, by rfl⟩ : syracuseStep 4097155 = 6145733) B6145733
theorem B5462873 : Blo 2157435 5462873 := bstep (se 2 (by rfl) ⟨2048577, by rfl⟩ : syracuseStep 5462873 = 4097155) B4097155
theorem B3641915 : Blo 2157435 3641915 := bstep (se 1 (by rfl) ⟨2731436, by rfl⟩ : syracuseStep 3641915 = 5462873) B5462873
theorem B2427943 : Blo 2157435 2427943 := bstep (se 1 (by rfl) ⟨1820957, by rfl⟩ : syracuseStep 2427943 = 3641915) B3641915
theorem B3237257 : Blo 2157435 3237257 := bstep (se 2 (by rfl) ⟨1213971, by rfl⟩ : syracuseStep 3237257 = 2427943) B2427943
theorem B2158171 : Blo 2157435 2158171 := bstep (se 1 (by rfl) ⟨1618628, by rfl⟩ : syracuseStep 2158171 = 3237257) B3237257
theorem B10925765 : Blo 2157435 10925765 := bbase (se 4 (by rfl) ⟨1024290, by rfl⟩ : syracuseStep 10925765 = 2048581) (by norm_num)
theorem B7283843 : Blo 2157435 7283843 := bstep (se 1 (by rfl) ⟨5462882, by rfl⟩ : syracuseStep 7283843 = 10925765) B10925765
theorem B4855895 : Blo 2157435 4855895 := bstep (se 1 (by rfl) ⟨3641921, by rfl⟩ : syracuseStep 4855895 = 7283843) B7283843
theorem B3237263 : Blo 2157435 3237263 := bstep (se 1 (by rfl) ⟨2427947, by rfl⟩ : syracuseStep 3237263 = 4855895) B4855895
theorem B2158175 : Blo 2157435 2158175 := bstep (se 1 (by rfl) ⟨1618631, by rfl⟩ : syracuseStep 2158175 = 3237263) B3237263
theorem B3237269 : Blo 2157435 3237269 := bbase (se 6 (by rfl) ⟨75873, by rfl⟩ : syracuseStep 3237269 = 151747) (by norm_num)
theorem B2158179 : Blo 2157435 2158179 := bstep (se 1 (by rfl) ⟨1618634, by rfl⟩ : syracuseStep 2158179 = 3237269) B3237269
theorem B4609325 : Blo 2157435 4609325 := bbase (se 3 (by rfl) ⟨864248, by rfl⟩ : syracuseStep 4609325 = 1728497) (by norm_num)
theorem B12291533 : Blo 2157435 12291533 := bstep (se 3 (by rfl) ⟨2304662, by rfl⟩ : syracuseStep 12291533 = 4609325) B4609325
theorem B8194355 : Blo 2157435 8194355 := bstep (se 1 (by rfl) ⟨6145766, by rfl⟩ : syracuseStep 8194355 = 12291533) B12291533
theorem B5462903 : Blo 2157435 5462903 := bstep (se 1 (by rfl) ⟨4097177, by rfl⟩ : syracuseStep 5462903 = 8194355) B8194355
theorem B3641935 : Blo 2157435 3641935 := bstep (se 1 (by rfl) ⟨2731451, by rfl⟩ : syracuseStep 3641935 = 5462903) B5462903
theorem B4855913 : Blo 2157435 4855913 := bstep (se 2 (by rfl) ⟨1820967, by rfl⟩ : syracuseStep 4855913 = 3641935) B3641935
theorem B3237275 : Blo 2157435 3237275 := bstep (se 1 (by rfl) ⟨2427956, by rfl⟩ : syracuseStep 3237275 = 4855913) B4855913
theorem B2158183 : Blo 2157435 2158183 := bstep (se 1 (by rfl) ⟨1618637, by rfl⟩ : syracuseStep 2158183 = 3237275) B3237275
theorem B2427961 : Blo 2157435 2427961 := bbase (se 2 (by rfl) ⟨910485, by rfl⟩ : syracuseStep 2427961 = 1820971) (by norm_num)
theorem B3237281 : Blo 2157435 3237281 := bstep (se 2 (by rfl) ⟨1213980, by rfl⟩ : syracuseStep 3237281 = 2427961) B2427961
theorem B2158187 : Blo 2157435 2158187 := bstep (se 1 (by rfl) ⟨1618640, by rfl⟩ : syracuseStep 2158187 = 3237281) B3237281
theorem B3114821 : Blo 2157435 3114821 := bbase (se 4 (by rfl) ⟨292014, by rfl⟩ : syracuseStep 3114821 = 584029) (by norm_num)
theorem B8306189 : Blo 2157435 8306189 := bstep (se 3 (by rfl) ⟨1557410, by rfl⟩ : syracuseStep 8306189 = 3114821) B3114821
theorem B5537459 : Blo 2157435 5537459 := bstep (se 1 (by rfl) ⟨4153094, by rfl⟩ : syracuseStep 5537459 = 8306189) B8306189
theorem B3691639 : Blo 2157435 3691639 := bstep (se 1 (by rfl) ⟨2768729, by rfl⟩ : syracuseStep 3691639 = 5537459) B5537459
theorem B19688741 : Blo 2157435 19688741 := bstep (se 4 (by rfl) ⟨1845819, by rfl⟩ : syracuseStep 19688741 = 3691639) B3691639
theorem B13125827 : Blo 2157435 13125827 := bstep (se 1 (by rfl) ⟨9844370, by rfl⟩ : syracuseStep 13125827 = 19688741) B19688741
theorem B8750551 : Blo 2157435 8750551 := bstep (se 1 (by rfl) ⟨6562913, by rfl⟩ : syracuseStep 8750551 = 13125827) B13125827
theorem B11667401 : Blo 2157435 11667401 := bstep (se 2 (by rfl) ⟨4375275, by rfl⟩ : syracuseStep 11667401 = 8750551) B8750551
theorem B7778267 : Blo 2157435 7778267 := bstep (se 1 (by rfl) ⟨5833700, by rfl⟩ : syracuseStep 7778267 = 11667401) B11667401
theorem B5185511 : Blo 2157435 5185511 := bstep (se 1 (by rfl) ⟨3889133, by rfl⟩ : syracuseStep 5185511 = 7778267) B7778267
theorem B3457007 : Blo 2157435 3457007 := bstep (se 1 (by rfl) ⟨2592755, by rfl⟩ : syracuseStep 3457007 = 5185511) B5185511
theorem B2304671 : Blo 2157435 2304671 := bstep (se 1 (by rfl) ⟨1728503, by rfl⟩ : syracuseStep 2304671 = 3457007) B3457007
theorem B6145789 : Blo 2157435 6145789 := bstep (se 3 (by rfl) ⟨1152335, by rfl⟩ : syracuseStep 6145789 = 2304671) B2304671
theorem B8194385 : Blo 2157435 8194385 := bstep (se 2 (by rfl) ⟨3072894, by rfl⟩ : syracuseStep 8194385 = 6145789) B6145789
theorem B5462923 : Blo 2157435 5462923 := bstep (se 1 (by rfl) ⟨4097192, by rfl⟩ : syracuseStep 5462923 = 8194385) B8194385
theorem B7283897 : Blo 2157435 7283897 := bstep (se 2 (by rfl) ⟨2731461, by rfl⟩ : syracuseStep 7283897 = 5462923) B5462923
theorem B4855931 : Blo 2157435 4855931 := bstep (se 1 (by rfl) ⟨3641948, by rfl⟩ : syracuseStep 4855931 = 7283897) B7283897
theorem B3237287 : Blo 2157435 3237287 := bstep (se 1 (by rfl) ⟨2427965, by rfl⟩ : syracuseStep 3237287 = 4855931) B4855931
theorem B2158191 : Blo 2157435 2158191 := bstep (se 1 (by rfl) ⟨1618643, by rfl⟩ : syracuseStep 2158191 = 3237287) B3237287
theorem B3237293 : Blo 2157435 3237293 := bbase (se 3 (by rfl) ⟨606992, by rfl⟩ : syracuseStep 3237293 = 1213985) (by norm_num)
theorem B2158195 : Blo 2157435 2158195 := bstep (se 1 (by rfl) ⟨1618646, by rfl⟩ : syracuseStep 2158195 = 3237293) B3237293
theorem B4855949 : Blo 2157435 4855949 := bbase (se 3 (by rfl) ⟨910490, by rfl⟩ : syracuseStep 4855949 = 1820981) (by norm_num)
theorem B3237299 : Blo 2157435 3237299 := bstep (se 1 (by rfl) ⟨2427974, by rfl⟩ : syracuseStep 3237299 = 4855949) B4855949
theorem B2158199 : Blo 2157435 2158199 := bstep (se 1 (by rfl) ⟨1618649, by rfl⟩ : syracuseStep 2158199 = 3237299) B3237299
theorem B2731477 : Blo 2157435 2731477 := bbase (se 7 (by rfl) ⟨32009, by rfl⟩ : syracuseStep 2731477 = 64019) (by norm_num)
theorem B3641969 : Blo 2157435 3641969 := bstep (se 2 (by rfl) ⟨1365738, by rfl⟩ : syracuseStep 3641969 = 2731477) B2731477
theorem B2427979 : Blo 2157435 2427979 := bstep (se 1 (by rfl) ⟨1820984, by rfl⟩ : syracuseStep 2427979 = 3641969) B3641969
theorem B3237305 : Blo 2157435 3237305 := bstep (se 2 (by rfl) ⟨1213989, by rfl⟩ : syracuseStep 3237305 = 2427979) B2427979
theorem B2158203 : Blo 2157435 2158203 := bstep (se 1 (by rfl) ⟨1618652, by rfl⟩ : syracuseStep 2158203 = 3237305) B3237305
theorem B56067157 : Blo 2157435 56067157 := bbase (se 8 (by rfl) ⟨328518, by rfl⟩ : syracuseStep 56067157 = 657037) (by norm_num)
theorem B74756209 : Blo 2157435 74756209 := bstep (se 2 (by rfl) ⟨28033578, by rfl⟩ : syracuseStep 74756209 = 56067157) B56067157
theorem B99674945 : Blo 2157435 99674945 := bstep (se 2 (by rfl) ⟨37378104, by rfl⟩ : syracuseStep 99674945 = 74756209) B74756209
theorem B66449963 : Blo 2157435 66449963 := bstep (se 1 (by rfl) ⟨49837472, by rfl⟩ : syracuseStep 66449963 = 99674945) B99674945
theorem B44299975 : Blo 2157435 44299975 := bstep (se 1 (by rfl) ⟨33224981, by rfl⟩ : syracuseStep 44299975 = 66449963) B66449963
theorem B59066633 : Blo 2157435 59066633 := bstep (se 2 (by rfl) ⟨22149987, by rfl⟩ : syracuseStep 59066633 = 44299975) B44299975
theorem B39377755 : Blo 2157435 39377755 := bstep (se 1 (by rfl) ⟨29533316, by rfl⟩ : syracuseStep 39377755 = 59066633) B59066633
theorem B210014693 : Blo 2157435 210014693 := bstep (se 4 (by rfl) ⟨19688877, by rfl⟩ : syracuseStep 210014693 = 39377755) B39377755
theorem B140009795 : Blo 2157435 140009795 := bstep (se 1 (by rfl) ⟨105007346, by rfl⟩ : syracuseStep 140009795 = 210014693) B210014693
theorem B93339863 : Blo 2157435 93339863 := bstep (se 1 (by rfl) ⟨70004897, by rfl⟩ : syracuseStep 93339863 = 140009795) B140009795
theorem B62226575 : Blo 2157435 62226575 := bstep (se 1 (by rfl) ⟨46669931, by rfl⟩ : syracuseStep 62226575 = 93339863) B93339863
theorem B41484383 : Blo 2157435 41484383 := bstep (se 1 (by rfl) ⟨31113287, by rfl⟩ : syracuseStep 41484383 = 62226575) B62226575
theorem B27656255 : Blo 2157435 27656255 := bstep (se 1 (by rfl) ⟨20742191, by rfl⟩ : syracuseStep 27656255 = 41484383) B41484383
theorem B18437503 : Blo 2157435 18437503 := bstep (se 1 (by rfl) ⟨13828127, by rfl⟩ : syracuseStep 18437503 = 27656255) B27656255
theorem B24583337 : Blo 2157435 24583337 := bstep (se 2 (by rfl) ⟨9218751, by rfl⟩ : syracuseStep 24583337 = 18437503) B18437503
theorem B16388891 : Blo 2157435 16388891 := bstep (se 1 (by rfl) ⟨12291668, by rfl⟩ : syracuseStep 16388891 = 24583337) B24583337
theorem B10925927 : Blo 2157435 10925927 := bstep (se 1 (by rfl) ⟨8194445, by rfl⟩ : syracuseStep 10925927 = 16388891) B16388891
theorem B7283951 : Blo 2157435 7283951 := bstep (se 1 (by rfl) ⟨5462963, by rfl⟩ : syracuseStep 7283951 = 10925927) B10925927
theorem B4855967 : Blo 2157435 4855967 := bstep (se 1 (by rfl) ⟨3641975, by rfl⟩ : syracuseStep 4855967 = 7283951) B7283951
theorem B3237311 : Blo 2157435 3237311 := bstep (se 1 (by rfl) ⟨2427983, by rfl⟩ : syracuseStep 3237311 = 4855967) B4855967
theorem B2158207 : Blo 2157435 2158207 := bstep (se 1 (by rfl) ⟨1618655, by rfl⟩ : syracuseStep 2158207 = 3237311) B3237311
theorem B3237317 : Blo 2157435 3237317 := bbase (se 4 (by rfl) ⟨303498, by rfl⟩ : syracuseStep 3237317 = 606997) (by norm_num)
theorem B2158211 : Blo 2157435 2158211 := bstep (se 1 (by rfl) ⟨1618658, by rfl⟩ : syracuseStep 2158211 = 3237317) B3237317
theorem B3641989 : Blo 2157435 3641989 := bbase (se 4 (by rfl) ⟨341436, by rfl⟩ : syracuseStep 3641989 = 682873) (by norm_num)
theorem B4855985 : Blo 2157435 4855985 := bstep (se 2 (by rfl) ⟨1820994, by rfl⟩ : syracuseStep 4855985 = 3641989) B3641989
theorem B3237323 : Blo 2157435 3237323 := bstep (se 1 (by rfl) ⟨2427992, by rfl⟩ : syracuseStep 3237323 = 4855985) B4855985
theorem B2158215 : Blo 2157435 2158215 := bstep (se 1 (by rfl) ⟨1618661, by rfl⟩ : syracuseStep 2158215 = 3237323) B3237323
theorem B2427997 : Blo 2157435 2427997 := bbase (se 3 (by rfl) ⟨455249, by rfl⟩ : syracuseStep 2427997 = 910499) (by norm_num)
theorem B3237329 : Blo 2157435 3237329 := bstep (se 2 (by rfl) ⟨1213998, by rfl⟩ : syracuseStep 3237329 = 2427997) B2427997
theorem B2158219 : Blo 2157435 2158219 := bstep (se 1 (by rfl) ⟨1618664, by rfl⟩ : syracuseStep 2158219 = 3237329) B3237329
theorem B7284005 : Blo 2157435 7284005 := bbase (se 4 (by rfl) ⟨682875, by rfl⟩ : syracuseStep 7284005 = 1365751) (by norm_num)
theorem B4856003 : Blo 2157435 4856003 := bstep (se 1 (by rfl) ⟨3642002, by rfl⟩ : syracuseStep 4856003 = 7284005) B7284005
theorem B3237335 : Blo 2157435 3237335 := bstep (se 1 (by rfl) ⟨2428001, by rfl⟩ : syracuseStep 3237335 = 4856003) B4856003
theorem B2158223 : Blo 2157435 2158223 := bstep (se 1 (by rfl) ⟨1618667, by rfl⟩ : syracuseStep 2158223 = 3237335) B3237335
theorem B3237341 : Blo 2157435 3237341 := bbase (se 3 (by rfl) ⟨607001, by rfl⟩ : syracuseStep 3237341 = 1214003) (by norm_num)
theorem B2158227 : Blo 2157435 2158227 := bstep (se 1 (by rfl) ⟨1618670, by rfl⟩ : syracuseStep 2158227 = 3237341) B3237341
theorem B4856021 : Blo 2157435 4856021 := bbase (se 7 (by rfl) ⟨56906, by rfl⟩ : syracuseStep 4856021 = 113813) (by norm_num)
theorem B3237347 : Blo 2157435 3237347 := bstep (se 1 (by rfl) ⟨2428010, by rfl⟩ : syracuseStep 3237347 = 4856021) B4856021
theorem B2158231 : Blo 2157435 2158231 := bstep (se 1 (by rfl) ⟨1618673, by rfl⟩ : syracuseStep 2158231 = 3237347) B3237347
theorem B7484165 : Blo 2157435 7484165 := bbase (se 4 (by rfl) ⟨701640, by rfl⟩ : syracuseStep 7484165 = 1403281) (by norm_num)
theorem B4989443 : Blo 2157435 4989443 := bstep (se 1 (by rfl) ⟨3742082, by rfl⟩ : syracuseStep 4989443 = 7484165) B7484165
theorem B13305181 : Blo 2157435 13305181 := bstep (se 3 (by rfl) ⟨2494721, by rfl⟩ : syracuseStep 13305181 = 4989443) B4989443
theorem B17740241 : Blo 2157435 17740241 := bstep (se 2 (by rfl) ⟨6652590, by rfl⟩ : syracuseStep 17740241 = 13305181) B13305181
theorem B11826827 : Blo 2157435 11826827 := bstep (se 1 (by rfl) ⟨8870120, by rfl⟩ : syracuseStep 11826827 = 17740241) B17740241
theorem B7884551 : Blo 2157435 7884551 := bstep (se 1 (by rfl) ⟨5913413, by rfl⟩ : syracuseStep 7884551 = 11826827) B11826827
theorem B21025469 : Blo 2157435 21025469 := bstep (se 3 (by rfl) ⟨3942275, by rfl⟩ : syracuseStep 21025469 = 7884551) B7884551
theorem B14016979 : Blo 2157435 14016979 := bstep (se 1 (by rfl) ⟨10512734, by rfl⟩ : syracuseStep 14016979 = 21025469) B21025469
theorem B18689305 : Blo 2157435 18689305 := bstep (se 2 (by rfl) ⟨7008489, by rfl⟩ : syracuseStep 18689305 = 14016979) B14016979
theorem B24919073 : Blo 2157435 24919073 := bstep (se 2 (by rfl) ⟨9344652, by rfl⟩ : syracuseStep 24919073 = 18689305) B18689305
theorem B16612715 : Blo 2157435 16612715 := bstep (se 1 (by rfl) ⟨12459536, by rfl⟩ : syracuseStep 16612715 = 24919073) B24919073
theorem B11075143 : Blo 2157435 11075143 := bstep (se 1 (by rfl) ⟨8306357, by rfl⟩ : syracuseStep 11075143 = 16612715) B16612715
theorem B14766857 : Blo 2157435 14766857 := bstep (se 2 (by rfl) ⟨5537571, by rfl⟩ : syracuseStep 14766857 = 11075143) B11075143
theorem B9844571 : Blo 2157435 9844571 := bstep (se 1 (by rfl) ⟨7383428, by rfl⟩ : syracuseStep 9844571 = 14766857) B14766857
theorem B6563047 : Blo 2157435 6563047 := bstep (se 1 (by rfl) ⟨4922285, by rfl⟩ : syracuseStep 6563047 = 9844571) B9844571
theorem B8750729 : Blo 2157435 8750729 := bstep (se 2 (by rfl) ⟨3281523, by rfl⟩ : syracuseStep 8750729 = 6563047) B6563047
theorem B5833819 : Blo 2157435 5833819 := bstep (se 1 (by rfl) ⟨4375364, by rfl⟩ : syracuseStep 5833819 = 8750729) B8750729
theorem B7778425 : Blo 2157435 7778425 := bstep (se 2 (by rfl) ⟨2916909, by rfl⟩ : syracuseStep 7778425 = 5833819) B5833819
theorem B10371233 : Blo 2157435 10371233 := bstep (se 2 (by rfl) ⟨3889212, by rfl⟩ : syracuseStep 10371233 = 7778425) B7778425
theorem B6914155 : Blo 2157435 6914155 := bstep (se 1 (by rfl) ⟨5185616, by rfl⟩ : syracuseStep 6914155 = 10371233) B10371233
theorem B9218873 : Blo 2157435 9218873 := bstep (se 2 (by rfl) ⟨3457077, by rfl⟩ : syracuseStep 9218873 = 6914155) B6914155
theorem B6145915 : Blo 2157435 6145915 := bstep (se 1 (by rfl) ⟨4609436, by rfl⟩ : syracuseStep 6145915 = 9218873) B9218873
theorem B8194553 : Blo 2157435 8194553 := bstep (se 2 (by rfl) ⟨3072957, by rfl⟩ : syracuseStep 8194553 = 6145915) B6145915
theorem B5463035 : Blo 2157435 5463035 := bstep (se 1 (by rfl) ⟨4097276, by rfl⟩ : syracuseStep 5463035 = 8194553) B8194553
theorem B3642023 : Blo 2157435 3642023 := bstep (se 1 (by rfl) ⟨2731517, by rfl⟩ : syracuseStep 3642023 = 5463035) B5463035
theorem B2428015 : Blo 2157435 2428015 := bstep (se 1 (by rfl) ⟨1821011, by rfl⟩ : syracuseStep 2428015 = 3642023) B3642023
theorem B3237353 : Blo 2157435 3237353 := bstep (se 2 (by rfl) ⟨1214007, by rfl⟩ : syracuseStep 3237353 = 2428015) B2428015
theorem B2158235 : Blo 2157435 2158235 := bstep (se 1 (by rfl) ⟨1618676, by rfl⟩ : syracuseStep 2158235 = 3237353) B3237353
theorem B5833829 : Blo 2157435 5833829 := bbase (se 4 (by rfl) ⟨546921, by rfl⟩ : syracuseStep 5833829 = 1093843) (by norm_num)
theorem B3889219 : Blo 2157435 3889219 := bstep (se 1 (by rfl) ⟨2916914, by rfl⟩ : syracuseStep 3889219 = 5833829) B5833829
theorem B5185625 : Blo 2157435 5185625 := bstep (se 2 (by rfl) ⟨1944609, by rfl⟩ : syracuseStep 5185625 = 3889219) B3889219
theorem B13828333 : Blo 2157435 13828333 := bstep (se 3 (by rfl) ⟨2592812, by rfl⟩ : syracuseStep 13828333 = 5185625) B5185625
theorem B18437777 : Blo 2157435 18437777 := bstep (se 2 (by rfl) ⟨6914166, by rfl⟩ : syracuseStep 18437777 = 13828333) B13828333
theorem B12291851 : Blo 2157435 12291851 := bstep (se 1 (by rfl) ⟨9218888, by rfl⟩ : syracuseStep 12291851 = 18437777) B18437777
theorem B8194567 : Blo 2157435 8194567 := bstep (se 1 (by rfl) ⟨6145925, by rfl⟩ : syracuseStep 8194567 = 12291851) B12291851
theorem B10926089 : Blo 2157435 10926089 := bstep (se 2 (by rfl) ⟨4097283, by rfl⟩ : syracuseStep 10926089 = 8194567) B8194567
theorem B7284059 : Blo 2157435 7284059 := bstep (se 1 (by rfl) ⟨5463044, by rfl⟩ : syracuseStep 7284059 = 10926089) B10926089
theorem B4856039 : Blo 2157435 4856039 := bstep (se 1 (by rfl) ⟨3642029, by rfl⟩ : syracuseStep 4856039 = 7284059) B7284059
theorem B3237359 : Blo 2157435 3237359 := bstep (se 1 (by rfl) ⟨2428019, by rfl⟩ : syracuseStep 3237359 = 4856039) B4856039
theorem B2158239 : Blo 2157435 2158239 := bstep (se 1 (by rfl) ⟨1618679, by rfl⟩ : syracuseStep 2158239 = 3237359) B3237359
theorem B3237365 : Blo 2157435 3237365 := bbase (se 5 (by rfl) ⟨151751, by rfl⟩ : syracuseStep 3237365 = 303503) (by norm_num)
theorem B2158243 : Blo 2157435 2158243 := bstep (se 1 (by rfl) ⟨1618682, by rfl⟩ : syracuseStep 2158243 = 3237365) B3237365
theorem B5537605 : Blo 2157435 5537605 := bbase (se 4 (by rfl) ⟨519150, by rfl⟩ : syracuseStep 5537605 = 1038301) (by norm_num)
theorem B7383473 : Blo 2157435 7383473 := bstep (se 2 (by rfl) ⟨2768802, by rfl⟩ : syracuseStep 7383473 = 5537605) B5537605
theorem B4922315 : Blo 2157435 4922315 := bstep (se 1 (by rfl) ⟨3691736, by rfl⟩ : syracuseStep 4922315 = 7383473) B7383473
theorem B3281543 : Blo 2157435 3281543 := bstep (se 1 (by rfl) ⟨2461157, by rfl⟩ : syracuseStep 3281543 = 4922315) B4922315
theorem B2187695 : Blo 2157435 2187695 := bstep (se 1 (by rfl) ⟨1640771, by rfl⟩ : syracuseStep 2187695 = 3281543) B3281543
theorem B5833853 : Blo 2157435 5833853 := bstep (se 3 (by rfl) ⟨1093847, by rfl⟩ : syracuseStep 5833853 = 2187695) B2187695
theorem B3889235 : Blo 2157435 3889235 := bstep (se 1 (by rfl) ⟨2916926, by rfl⟩ : syracuseStep 3889235 = 5833853) B5833853
theorem B2592823 : Blo 2157435 2592823 := bstep (se 1 (by rfl) ⟨1944617, by rfl⟩ : syracuseStep 2592823 = 3889235) B3889235
theorem B3457097 : Blo 2157435 3457097 := bstep (se 2 (by rfl) ⟨1296411, by rfl⟩ : syracuseStep 3457097 = 2592823) B2592823
theorem B2304731 : Blo 2157435 2304731 := bstep (se 1 (by rfl) ⟨1728548, by rfl⟩ : syracuseStep 2304731 = 3457097) B3457097
theorem B6145949 : Blo 2157435 6145949 := bstep (se 3 (by rfl) ⟨1152365, by rfl⟩ : syracuseStep 6145949 = 2304731) B2304731
theorem B4097299 : Blo 2157435 4097299 := bstep (se 1 (by rfl) ⟨3072974, by rfl⟩ : syracuseStep 4097299 = 6145949) B6145949
theorem B5463065 : Blo 2157435 5463065 := bstep (se 2 (by rfl) ⟨2048649, by rfl⟩ : syracuseStep 5463065 = 4097299) B4097299
theorem B3642043 : Blo 2157435 3642043 := bstep (se 1 (by rfl) ⟨2731532, by rfl⟩ : syracuseStep 3642043 = 5463065) B5463065
theorem B4856057 : Blo 2157435 4856057 := bstep (se 2 (by rfl) ⟨1821021, by rfl⟩ : syracuseStep 4856057 = 3642043) B3642043
theorem B3237371 : Blo 2157435 3237371 := bstep (se 1 (by rfl) ⟨2428028, by rfl⟩ : syracuseStep 3237371 = 4856057) B4856057
theorem B2158247 : Blo 2157435 2158247 := bstep (se 1 (by rfl) ⟨1618685, by rfl⟩ : syracuseStep 2158247 = 3237371) B3237371
theorem B2428033 : Blo 2157435 2428033 := bbase (se 2 (by rfl) ⟨910512, by rfl⟩ : syracuseStep 2428033 = 1821025) (by norm_num)
theorem B3237377 : Blo 2157435 3237377 := bstep (se 2 (by rfl) ⟨1214016, by rfl⟩ : syracuseStep 3237377 = 2428033) B2428033
theorem B2158251 : Blo 2157435 2158251 := bstep (se 1 (by rfl) ⟨1618688, by rfl⟩ : syracuseStep 2158251 = 3237377) B3237377
theorem B5463085 : Blo 2157435 5463085 := bbase (se 3 (by rfl) ⟨1024328, by rfl⟩ : syracuseStep 5463085 = 2048657) (by norm_num)
theorem B7284113 : Blo 2157435 7284113 := bstep (se 2 (by rfl) ⟨2731542, by rfl⟩ : syracuseStep 7284113 = 5463085) B5463085
theorem B4856075 : Blo 2157435 4856075 := bstep (se 1 (by rfl) ⟨3642056, by rfl⟩ : syracuseStep 4856075 = 7284113) B7284113
theorem B3237383 : Blo 2157435 3237383 := bstep (se 1 (by rfl) ⟨2428037, by rfl⟩ : syracuseStep 3237383 = 4856075) B4856075
theorem B2158255 : Blo 2157435 2158255 := bstep (se 1 (by rfl) ⟨1618691, by rfl⟩ : syracuseStep 2158255 = 3237383) B3237383
theorem B3237389 : Blo 2157435 3237389 := bbase (se 3 (by rfl) ⟨607010, by rfl⟩ : syracuseStep 3237389 = 1214021) (by norm_num)
theorem B2158259 : Blo 2157435 2158259 := bstep (se 1 (by rfl) ⟨1618694, by rfl⟩ : syracuseStep 2158259 = 3237389) B3237389
theorem B4856093 : Blo 2157435 4856093 := bbase (se 3 (by rfl) ⟨910517, by rfl⟩ : syracuseStep 4856093 = 1821035) (by norm_num)
theorem B3237395 : Blo 2157435 3237395 := bstep (se 1 (by rfl) ⟨2428046, by rfl⟩ : syracuseStep 3237395 = 4856093) B4856093
theorem B2158263 : Blo 2157435 2158263 := bstep (se 1 (by rfl) ⟨1618697, by rfl⟩ : syracuseStep 2158263 = 3237395) B3237395
theorem B3642077 : Blo 2157435 3642077 := bbase (se 3 (by rfl) ⟨682889, by rfl⟩ : syracuseStep 3642077 = 1365779) (by norm_num)
theorem B2428051 : Blo 2157435 2428051 := bstep (se 1 (by rfl) ⟨1821038, by rfl⟩ : syracuseStep 2428051 = 3642077) B3642077
theorem B3237401 : Blo 2157435 3237401 := bstep (se 2 (by rfl) ⟨1214025, by rfl⟩ : syracuseStep 3237401 = 2428051) B2428051
theorem B2158267 : Blo 2157435 2158267 := bstep (se 1 (by rfl) ⟨1618700, by rfl⟩ : syracuseStep 2158267 = 3237401) B3237401
theorem B3889277 : Blo 2157435 3889277 := bbase (se 3 (by rfl) ⟨729239, by rfl⟩ : syracuseStep 3889277 = 1458479) (by norm_num)
theorem B2592851 : Blo 2157435 2592851 := bstep (se 1 (by rfl) ⟨1944638, by rfl⟩ : syracuseStep 2592851 = 3889277) B3889277
theorem B6914269 : Blo 2157435 6914269 := bstep (se 3 (by rfl) ⟨1296425, by rfl⟩ : syracuseStep 6914269 = 2592851) B2592851
theorem B9219025 : Blo 2157435 9219025 := bstep (se 2 (by rfl) ⟨3457134, by rfl⟩ : syracuseStep 9219025 = 6914269) B6914269
theorem B12292033 : Blo 2157435 12292033 := bstep (se 2 (by rfl) ⟨4609512, by rfl⟩ : syracuseStep 12292033 = 9219025) B9219025
theorem B16389377 : Blo 2157435 16389377 := bstep (se 2 (by rfl) ⟨6146016, by rfl⟩ : syracuseStep 16389377 = 12292033) B12292033
theorem B10926251 : Blo 2157435 10926251 := bstep (se 1 (by rfl) ⟨8194688, by rfl⟩ : syracuseStep 10926251 = 16389377) B16389377
theorem B7284167 : Blo 2157435 7284167 := bstep (se 1 (by rfl) ⟨5463125, by rfl⟩ : syracuseStep 7284167 = 10926251) B10926251
theorem B4856111 : Blo 2157435 4856111 := bstep (se 1 (by rfl) ⟨3642083, by rfl⟩ : syracuseStep 4856111 = 7284167) B7284167
theorem B3237407 : Blo 2157435 3237407 := bstep (se 1 (by rfl) ⟨2428055, by rfl⟩ : syracuseStep 3237407 = 4856111) B4856111
theorem B2158271 : Blo 2157435 2158271 := bstep (se 1 (by rfl) ⟨1618703, by rfl⟩ : syracuseStep 2158271 = 3237407) B3237407
theorem B3237413 : Blo 2157435 3237413 := bbase (se 4 (by rfl) ⟨303507, by rfl⟩ : syracuseStep 3237413 = 607015) (by norm_num)
theorem B2158275 : Blo 2157435 2158275 := bstep (se 1 (by rfl) ⟨1618706, by rfl⟩ : syracuseStep 2158275 = 3237413) B3237413
theorem B2731573 : Blo 2157435 2731573 := bbase (se 5 (by rfl) ⟨128042, by rfl⟩ : syracuseStep 2731573 = 256085) (by norm_num)
theorem B3642097 : Blo 2157435 3642097 := bstep (se 2 (by rfl) ⟨1365786, by rfl⟩ : syracuseStep 3642097 = 2731573) B2731573
theorem B4856129 : Blo 2157435 4856129 := bstep (se 2 (by rfl) ⟨1821048, by rfl⟩ : syracuseStep 4856129 = 3642097) B3642097
theorem B3237419 : Blo 2157435 3237419 := bstep (se 1 (by rfl) ⟨2428064, by rfl⟩ : syracuseStep 3237419 = 4856129) B4856129
theorem B2158279 : Blo 2157435 2158279 := bstep (se 1 (by rfl) ⟨1618709, by rfl⟩ : syracuseStep 2158279 = 3237419) B3237419
theorem B2428069 : Blo 2157435 2428069 := bbase (se 4 (by rfl) ⟨227631, by rfl⟩ : syracuseStep 2428069 = 455263) (by norm_num)
theorem B3237425 : Blo 2157435 3237425 := bstep (se 2 (by rfl) ⟨1214034, by rfl⟩ : syracuseStep 3237425 = 2428069) B2428069
theorem B2158283 : Blo 2157435 2158283 := bstep (se 1 (by rfl) ⟨1618712, by rfl⟩ : syracuseStep 2158283 = 3237425) B3237425
theorem B20742965 : Blo 2157435 20742965 := bbase (se 5 (by rfl) ⟨972326, by rfl⟩ : syracuseStep 20742965 = 1944653) (by norm_num)
theorem B13828643 : Blo 2157435 13828643 := bstep (se 1 (by rfl) ⟨10371482, by rfl⟩ : syracuseStep 13828643 = 20742965) B20742965
theorem B9219095 : Blo 2157435 9219095 := bstep (se 1 (by rfl) ⟨6914321, by rfl⟩ : syracuseStep 9219095 = 13828643) B13828643
theorem B6146063 : Blo 2157435 6146063 := bstep (se 1 (by rfl) ⟨4609547, by rfl⟩ : syracuseStep 6146063 = 9219095) B9219095
theorem B4097375 : Blo 2157435 4097375 := bstep (se 1 (by rfl) ⟨3073031, by rfl⟩ : syracuseStep 4097375 = 6146063) B6146063
theorem B2731583 : Blo 2157435 2731583 := bstep (se 1 (by rfl) ⟨2048687, by rfl⟩ : syracuseStep 2731583 = 4097375) B4097375
theorem B7284221 : Blo 2157435 7284221 := bstep (se 3 (by rfl) ⟨1365791, by rfl⟩ : syracuseStep 7284221 = 2731583) B2731583
theorem B4856147 : Blo 2157435 4856147 := bstep (se 1 (by rfl) ⟨3642110, by rfl⟩ : syracuseStep 4856147 = 7284221) B7284221
theorem B3237431 : Blo 2157435 3237431 := bstep (se 1 (by rfl) ⟨2428073, by rfl⟩ : syracuseStep 3237431 = 4856147) B4856147
theorem B2158287 : Blo 2157435 2158287 := bstep (se 1 (by rfl) ⟨1618715, by rfl⟩ : syracuseStep 2158287 = 3237431) B3237431
theorem B3237437 : Blo 2157435 3237437 := bbase (se 3 (by rfl) ⟨607019, by rfl⟩ : syracuseStep 3237437 = 1214039) (by norm_num)
theorem B2158291 : Blo 2157435 2158291 := bstep (se 1 (by rfl) ⟨1618718, by rfl⟩ : syracuseStep 2158291 = 3237437) B3237437
theorem B4856165 : Blo 2157435 4856165 := bbase (se 4 (by rfl) ⟨455265, by rfl⟩ : syracuseStep 4856165 = 910531) (by norm_num)
theorem B3237443 : Blo 2157435 3237443 := bstep (se 1 (by rfl) ⟨2428082, by rfl⟩ : syracuseStep 3237443 = 4856165) B4856165
theorem B2158295 : Blo 2157435 2158295 := bstep (se 1 (by rfl) ⟨1618721, by rfl⟩ : syracuseStep 2158295 = 3237443) B3237443
theorem B5463197 : Blo 2157435 5463197 := bbase (se 3 (by rfl) ⟨1024349, by rfl⟩ : syracuseStep 5463197 = 2048699) (by norm_num)
theorem B3642131 : Blo 2157435 3642131 := bstep (se 1 (by rfl) ⟨2731598, by rfl⟩ : syracuseStep 3642131 = 5463197) B5463197
theorem B2428087 : Blo 2157435 2428087 := bstep (se 1 (by rfl) ⟨1821065, by rfl⟩ : syracuseStep 2428087 = 3642131) B3642131
theorem B3237449 : Blo 2157435 3237449 := bstep (se 2 (by rfl) ⟨1214043, by rfl⟩ : syracuseStep 3237449 = 2428087) B2428087
theorem B2158299 : Blo 2157435 2158299 := bstep (se 1 (by rfl) ⟨1618724, by rfl⟩ : syracuseStep 2158299 = 3237449) B3237449
theorem B4097405 : Blo 2157435 4097405 := bbase (se 3 (by rfl) ⟨768263, by rfl⟩ : syracuseStep 4097405 = 1536527) (by norm_num)
theorem B10926413 : Blo 2157435 10926413 := bstep (se 3 (by rfl) ⟨2048702, by rfl⟩ : syracuseStep 10926413 = 4097405) B4097405
theorem B7284275 : Blo 2157435 7284275 := bstep (se 1 (by rfl) ⟨5463206, by rfl⟩ : syracuseStep 7284275 = 10926413) B10926413
theorem B4856183 : Blo 2157435 4856183 := bstep (se 1 (by rfl) ⟨3642137, by rfl⟩ : syracuseStep 4856183 = 7284275) B7284275
theorem B3237455 : Blo 2157435 3237455 := bstep (se 1 (by rfl) ⟨2428091, by rfl⟩ : syracuseStep 3237455 = 4856183) B4856183
theorem B2158303 : Blo 2157435 2158303 := bstep (se 1 (by rfl) ⟨1618727, by rfl⟩ : syracuseStep 2158303 = 3237455) B3237455
theorem B3237461 : Blo 2157435 3237461 := bbase (se 8 (by rfl) ⟨18969, by rfl⟩ : syracuseStep 3237461 = 37939) (by norm_num)
theorem B2158307 : Blo 2157435 2158307 := bstep (se 1 (by rfl) ⟨1618730, by rfl⟩ : syracuseStep 2158307 = 3237461) B3237461
theorem B13305653 : Blo 2157435 13305653 := bbase (se 5 (by rfl) ⟨623702, by rfl⟩ : syracuseStep 13305653 = 1247405) (by norm_num)
theorem B8870435 : Blo 2157435 8870435 := bstep (se 1 (by rfl) ⟨6652826, by rfl⟩ : syracuseStep 8870435 = 13305653) B13305653
theorem B5913623 : Blo 2157435 5913623 := bstep (se 1 (by rfl) ⟨4435217, by rfl⟩ : syracuseStep 5913623 = 8870435) B8870435
theorem B3942415 : Blo 2157435 3942415 := bstep (se 1 (by rfl) ⟨2956811, by rfl⟩ : syracuseStep 3942415 = 5913623) B5913623
theorem B21026213 : Blo 2157435 21026213 := bstep (se 4 (by rfl) ⟨1971207, by rfl⟩ : syracuseStep 21026213 = 3942415) B3942415
theorem B14017475 : Blo 2157435 14017475 := bstep (se 1 (by rfl) ⟨10513106, by rfl⟩ : syracuseStep 14017475 = 21026213) B21026213
theorem B9344983 : Blo 2157435 9344983 := bstep (se 1 (by rfl) ⟨7008737, by rfl⟩ : syracuseStep 9344983 = 14017475) B14017475
theorem B12459977 : Blo 2157435 12459977 := bstep (se 2 (by rfl) ⟨4672491, by rfl⟩ : syracuseStep 12459977 = 9344983) B9344983
theorem B8306651 : Blo 2157435 8306651 := bstep (se 1 (by rfl) ⟨6229988, by rfl⟩ : syracuseStep 8306651 = 12459977) B12459977
theorem B5537767 : Blo 2157435 5537767 := bstep (se 1 (by rfl) ⟨4153325, by rfl⟩ : syracuseStep 5537767 = 8306651) B8306651
theorem B7383689 : Blo 2157435 7383689 := bstep (se 2 (by rfl) ⟨2768883, by rfl⟩ : syracuseStep 7383689 = 5537767) B5537767
theorem B4922459 : Blo 2157435 4922459 := bstep (se 1 (by rfl) ⟨3691844, by rfl⟩ : syracuseStep 4922459 = 7383689) B7383689
theorem B3281639 : Blo 2157435 3281639 := bstep (se 1 (by rfl) ⟨2461229, by rfl⟩ : syracuseStep 3281639 = 4922459) B4922459
theorem B8751037 : Blo 2157435 8751037 := bstep (se 3 (by rfl) ⟨1640819, by rfl⟩ : syracuseStep 8751037 = 3281639) B3281639
theorem B11668049 : Blo 2157435 11668049 := bstep (se 2 (by rfl) ⟨4375518, by rfl⟩ : syracuseStep 11668049 = 8751037) B8751037
theorem B7778699 : Blo 2157435 7778699 := bstep (se 1 (by rfl) ⟨5834024, by rfl⟩ : syracuseStep 7778699 = 11668049) B11668049
theorem B5185799 : Blo 2157435 5185799 := bstep (se 1 (by rfl) ⟨3889349, by rfl⟩ : syracuseStep 5185799 = 7778699) B7778699
theorem B3457199 : Blo 2157435 3457199 := bstep (se 1 (by rfl) ⟨2592899, by rfl⟩ : syracuseStep 3457199 = 5185799) B5185799
theorem B9219197 : Blo 2157435 9219197 := bstep (se 3 (by rfl) ⟨1728599, by rfl⟩ : syracuseStep 9219197 = 3457199) B3457199
theorem B6146131 : Blo 2157435 6146131 := bstep (se 1 (by rfl) ⟨4609598, by rfl⟩ : syracuseStep 6146131 = 9219197) B9219197
theorem B8194841 : Blo 2157435 8194841 := bstep (se 2 (by rfl) ⟨3073065, by rfl⟩ : syracuseStep 8194841 = 6146131) B6146131
theorem B5463227 : Blo 2157435 5463227 := bstep (se 1 (by rfl) ⟨4097420, by rfl⟩ : syracuseStep 5463227 = 8194841) B8194841
theorem B3642151 : Blo 2157435 3642151 := bstep (se 1 (by rfl) ⟨2731613, by rfl⟩ : syracuseStep 3642151 = 5463227) B5463227
theorem B4856201 : Blo 2157435 4856201 := bstep (se 2 (by rfl) ⟨1821075, by rfl⟩ : syracuseStep 4856201 = 3642151) B3642151
theorem B3237467 : Blo 2157435 3237467 := bstep (se 1 (by rfl) ⟨2428100, by rfl⟩ : syracuseStep 3237467 = 4856201) B4856201
theorem B2158311 : Blo 2157435 2158311 := bstep (se 1 (by rfl) ⟨1618733, by rfl⟩ : syracuseStep 2158311 = 3237467) B3237467
theorem B2428105 : Blo 2157435 2428105 := bbase (se 2 (by rfl) ⟨910539, by rfl⟩ : syracuseStep 2428105 = 1821079) (by norm_num)
theorem B3237473 : Blo 2157435 3237473 := bstep (se 2 (by rfl) ⟨1214052, by rfl⟩ : syracuseStep 3237473 = 2428105) B2428105
theorem B2158315 : Blo 2157435 2158315 := bstep (se 1 (by rfl) ⟨1618736, by rfl⟩ : syracuseStep 2158315 = 3237473) B3237473
theorem B4922477 : Blo 2157435 4922477 := bbase (se 3 (by rfl) ⟨922964, by rfl⟩ : syracuseStep 4922477 = 1845929) (by norm_num)
theorem B3281651 : Blo 2157435 3281651 := bstep (se 1 (by rfl) ⟨2461238, by rfl⟩ : syracuseStep 3281651 = 4922477) B4922477
theorem B2187767 : Blo 2157435 2187767 := bstep (se 1 (by rfl) ⟨1640825, by rfl⟩ : syracuseStep 2187767 = 3281651) B3281651
theorem B5834045 : Blo 2157435 5834045 := bstep (se 3 (by rfl) ⟨1093883, by rfl⟩ : syracuseStep 5834045 = 2187767) B2187767
theorem B15557453 : Blo 2157435 15557453 := bstep (se 3 (by rfl) ⟨2917022, by rfl⟩ : syracuseStep 15557453 = 5834045) B5834045
theorem B10371635 : Blo 2157435 10371635 := bstep (se 1 (by rfl) ⟨7778726, by rfl⟩ : syracuseStep 10371635 = 15557453) B15557453
theorem B6914423 : Blo 2157435 6914423 := bstep (se 1 (by rfl) ⟨5185817, by rfl⟩ : syracuseStep 6914423 = 10371635) B10371635
theorem B18438461 : Blo 2157435 18438461 := bstep (se 3 (by rfl) ⟨3457211, by rfl⟩ : syracuseStep 18438461 = 6914423) B6914423
theorem B12292307 : Blo 2157435 12292307 := bstep (se 1 (by rfl) ⟨9219230, by rfl⟩ : syracuseStep 12292307 = 18438461) B18438461
theorem B8194871 : Blo 2157435 8194871 := bstep (se 1 (by rfl) ⟨6146153, by rfl⟩ : syracuseStep 8194871 = 12292307) B12292307
theorem B5463247 : Blo 2157435 5463247 := bstep (se 1 (by rfl) ⟨4097435, by rfl⟩ : syracuseStep 5463247 = 8194871) B8194871
theorem B7284329 : Blo 2157435 7284329 := bstep (se 2 (by rfl) ⟨2731623, by rfl⟩ : syracuseStep 7284329 = 5463247) B5463247
theorem B4856219 : Blo 2157435 4856219 := bstep (se 1 (by rfl) ⟨3642164, by rfl⟩ : syracuseStep 4856219 = 7284329) B7284329
theorem B3237479 : Blo 2157435 3237479 := bstep (se 1 (by rfl) ⟨2428109, by rfl⟩ : syracuseStep 3237479 = 4856219) B4856219
theorem B2158319 : Blo 2157435 2158319 := bstep (se 1 (by rfl) ⟨1618739, by rfl⟩ : syracuseStep 2158319 = 3237479) B3237479
theorem B3237485 : Blo 2157435 3237485 := bbase (se 3 (by rfl) ⟨607028, by rfl⟩ : syracuseStep 3237485 = 1214057) (by norm_num)
theorem B2158323 : Blo 2157435 2158323 := bstep (se 1 (by rfl) ⟨1618742, by rfl⟩ : syracuseStep 2158323 = 3237485) B3237485
theorem B4856237 : Blo 2157435 4856237 := bbase (se 3 (by rfl) ⟨910544, by rfl⟩ : syracuseStep 4856237 = 1821089) (by norm_num)
theorem B3237491 : Blo 2157435 3237491 := bstep (se 1 (by rfl) ⟨2428118, by rfl⟩ : syracuseStep 3237491 = 4856237) B4856237
theorem B2158327 : Blo 2157435 2158327 := bstep (se 1 (by rfl) ⟨1618745, by rfl⟩ : syracuseStep 2158327 = 3237491) B3237491
theorem B2304821 : Blo 2157435 2304821 := bbase (se 5 (by rfl) ⟨108038, by rfl⟩ : syracuseStep 2304821 = 216077) (by norm_num)
theorem B6146189 : Blo 2157435 6146189 := bstep (se 3 (by rfl) ⟨1152410, by rfl⟩ : syracuseStep 6146189 = 2304821) B2304821
theorem B4097459 : Blo 2157435 4097459 := bstep (se 1 (by rfl) ⟨3073094, by rfl⟩ : syracuseStep 4097459 = 6146189) B6146189
theorem B2731639 : Blo 2157435 2731639 := bstep (se 1 (by rfl) ⟨2048729, by rfl⟩ : syracuseStep 2731639 = 4097459) B4097459
theorem B3642185 : Blo 2157435 3642185 := bstep (se 2 (by rfl) ⟨1365819, by rfl⟩ : syracuseStep 3642185 = 2731639) B2731639
theorem B2428123 : Blo 2157435 2428123 := bstep (se 1 (by rfl) ⟨1821092, by rfl⟩ : syracuseStep 2428123 = 3642185) B3642185
theorem B3237497 : Blo 2157435 3237497 := bstep (se 2 (by rfl) ⟨1214061, by rfl⟩ : syracuseStep 3237497 = 2428123) B2428123
theorem B2158331 : Blo 2157435 2158331 := bstep (se 1 (by rfl) ⟨1618748, by rfl⟩ : syracuseStep 2158331 = 3237497) B3237497
theorem B4672541 : Blo 2157435 4672541 := bbase (se 3 (by rfl) ⟨876101, by rfl⟩ : syracuseStep 4672541 = 1752203) (by norm_num)
theorem B3115027 : Blo 2157435 3115027 := bstep (se 1 (by rfl) ⟨2336270, by rfl⟩ : syracuseStep 3115027 = 4672541) B4672541
theorem B16613477 : Blo 2157435 16613477 := bstep (se 4 (by rfl) ⟨1557513, by rfl⟩ : syracuseStep 16613477 = 3115027) B3115027
theorem B11075651 : Blo 2157435 11075651 := bstep (se 1 (by rfl) ⟨8306738, by rfl⟩ : syracuseStep 11075651 = 16613477) B16613477
theorem B7383767 : Blo 2157435 7383767 := bstep (se 1 (by rfl) ⟨5537825, by rfl⟩ : syracuseStep 7383767 = 11075651) B11075651
theorem B78760181 : Blo 2157435 78760181 := bstep (se 5 (by rfl) ⟨3691883, by rfl⟩ : syracuseStep 78760181 = 7383767) B7383767
theorem B52506787 : Blo 2157435 52506787 := bstep (se 1 (by rfl) ⟨39380090, by rfl⟩ : syracuseStep 52506787 = 78760181) B78760181
theorem B70009049 : Blo 2157435 70009049 := bstep (se 2 (by rfl) ⟨26253393, by rfl⟩ : syracuseStep 70009049 = 52506787) B52506787
theorem B46672699 : Blo 2157435 46672699 := bstep (se 1 (by rfl) ⟨35004524, by rfl⟩ : syracuseStep 46672699 = 70009049) B70009049
theorem B62230265 : Blo 2157435 62230265 := bstep (se 2 (by rfl) ⟨23336349, by rfl⟩ : syracuseStep 62230265 = 46672699) B46672699
theorem B41486843 : Blo 2157435 41486843 := bstep (se 1 (by rfl) ⟨31115132, by rfl⟩ : syracuseStep 41486843 = 62230265) B62230265
theorem B27657895 : Blo 2157435 27657895 := bstep (se 1 (by rfl) ⟨20743421, by rfl⟩ : syracuseStep 27657895 = 41486843) B41486843
theorem B36877193 : Blo 2157435 36877193 := bstep (se 2 (by rfl) ⟨13828947, by rfl⟩ : syracuseStep 36877193 = 27657895) B27657895
theorem B24584795 : Blo 2157435 24584795 := bstep (se 1 (by rfl) ⟨18438596, by rfl⟩ : syracuseStep 24584795 = 36877193) B36877193
theorem B16389863 : Blo 2157435 16389863 := bstep (se 1 (by rfl) ⟨12292397, by rfl⟩ : syracuseStep 16389863 = 24584795) B24584795
theorem B10926575 : Blo 2157435 10926575 := bstep (se 1 (by rfl) ⟨8194931, by rfl⟩ : syracuseStep 10926575 = 16389863) B16389863
theorem B7284383 : Blo 2157435 7284383 := bstep (se 1 (by rfl) ⟨5463287, by rfl⟩ : syracuseStep 7284383 = 10926575) B10926575
theorem B4856255 : Blo 2157435 4856255 := bstep (se 1 (by rfl) ⟨3642191, by rfl⟩ : syracuseStep 4856255 = 7284383) B7284383
theorem B3237503 : Blo 2157435 3237503 := bstep (se 1 (by rfl) ⟨2428127, by rfl⟩ : syracuseStep 3237503 = 4856255) B4856255
theorem B2158335 : Blo 2157435 2158335 := bstep (se 1 (by rfl) ⟨1618751, by rfl⟩ : syracuseStep 2158335 = 3237503) B3237503
theorem B3237509 : Blo 2157435 3237509 := bbase (se 4 (by rfl) ⟨303516, by rfl⟩ : syracuseStep 3237509 = 607033) (by norm_num)
theorem B2158339 : Blo 2157435 2158339 := bstep (se 1 (by rfl) ⟨1618754, by rfl⟩ : syracuseStep 2158339 = 3237509) B3237509
theorem B3642205 : Blo 2157435 3642205 := bbase (se 3 (by rfl) ⟨682913, by rfl⟩ : syracuseStep 3642205 = 1365827) (by norm_num)
theorem B4856273 : Blo 2157435 4856273 := bstep (se 2 (by rfl) ⟨1821102, by rfl⟩ : syracuseStep 4856273 = 3642205) B3642205
theorem B3237515 : Blo 2157435 3237515 := bstep (se 1 (by rfl) ⟨2428136, by rfl⟩ : syracuseStep 3237515 = 4856273) B4856273
theorem B2158343 : Blo 2157435 2158343 := bstep (se 1 (by rfl) ⟨1618757, by rfl⟩ : syracuseStep 2158343 = 3237515) B3237515
theorem B2428141 : Blo 2157435 2428141 := bbase (se 3 (by rfl) ⟨455276, by rfl⟩ : syracuseStep 2428141 = 910553) (by norm_num)
theorem B3237521 : Blo 2157435 3237521 := bstep (se 2 (by rfl) ⟨1214070, by rfl⟩ : syracuseStep 3237521 = 2428141) B2428141
theorem B2158347 : Blo 2157435 2158347 := bstep (se 1 (by rfl) ⟨1618760, by rfl⟩ : syracuseStep 2158347 = 3237521) B3237521
theorem B7284437 : Blo 2157435 7284437 := bbase (se 7 (by rfl) ⟨85364, by rfl⟩ : syracuseStep 7284437 = 170729) (by norm_num)
theorem B4856291 : Blo 2157435 4856291 := bstep (se 1 (by rfl) ⟨3642218, by rfl⟩ : syracuseStep 4856291 = 7284437) B7284437
theorem B3237527 : Blo 2157435 3237527 := bstep (se 1 (by rfl) ⟨2428145, by rfl⟩ : syracuseStep 3237527 = 4856291) B4856291
theorem B2158351 : Blo 2157435 2158351 := bstep (se 1 (by rfl) ⟨1618763, by rfl⟩ : syracuseStep 2158351 = 3237527) B3237527
theorem B3237533 : Blo 2157435 3237533 := bbase (se 3 (by rfl) ⟨607037, by rfl⟩ : syracuseStep 3237533 = 1214075) (by norm_num)
theorem B2158355 : Blo 2157435 2158355 := bstep (se 1 (by rfl) ⟨1618766, by rfl⟩ : syracuseStep 2158355 = 3237533) B3237533
theorem B4856309 : Blo 2157435 4856309 := bbase (se 5 (by rfl) ⟨227639, by rfl⟩ : syracuseStep 4856309 = 455279) (by norm_num)
theorem B3237539 : Blo 2157435 3237539 := bstep (se 1 (by rfl) ⟨2428154, by rfl⟩ : syracuseStep 3237539 = 4856309) B4856309
theorem B2158359 : Blo 2157435 2158359 := bstep (se 1 (by rfl) ⟨1618769, by rfl⟩ : syracuseStep 2158359 = 3237539) B3237539
theorem B4210093 : Blo 2157435 4210093 := bbase (se 3 (by rfl) ⟨789392, by rfl⟩ : syracuseStep 4210093 = 1578785) (by norm_num)
theorem B5613457 : Blo 2157435 5613457 := bstep (se 2 (by rfl) ⟨2105046, by rfl⟩ : syracuseStep 5613457 = 4210093) B4210093
theorem B7484609 : Blo 2157435 7484609 := bstep (se 2 (by rfl) ⟨2806728, by rfl⟩ : syracuseStep 7484609 = 5613457) B5613457
theorem B19958957 : Blo 2157435 19958957 := bstep (se 3 (by rfl) ⟨3742304, by rfl⟩ : syracuseStep 19958957 = 7484609) B7484609
theorem B13305971 : Blo 2157435 13305971 := bstep (se 1 (by rfl) ⟨9979478, by rfl⟩ : syracuseStep 13305971 = 19958957) B19958957
theorem B8870647 : Blo 2157435 8870647 := bstep (se 1 (by rfl) ⟨6652985, by rfl⟩ : syracuseStep 8870647 = 13305971) B13305971
theorem B11827529 : Blo 2157435 11827529 := bstep (se 2 (by rfl) ⟨4435323, by rfl⟩ : syracuseStep 11827529 = 8870647) B8870647
theorem B7885019 : Blo 2157435 7885019 := bstep (se 1 (by rfl) ⟨5913764, by rfl⟩ : syracuseStep 7885019 = 11827529) B11827529
theorem B5256679 : Blo 2157435 5256679 := bstep (se 1 (by rfl) ⟨3942509, by rfl⟩ : syracuseStep 5256679 = 7885019) B7885019
theorem B7008905 : Blo 2157435 7008905 := bstep (se 2 (by rfl) ⟨2628339, by rfl⟩ : syracuseStep 7008905 = 5256679) B5256679
theorem B4672603 : Blo 2157435 4672603 := bstep (se 1 (by rfl) ⟨3504452, by rfl⟩ : syracuseStep 4672603 = 7008905) B7008905
theorem B6230137 : Blo 2157435 6230137 := bstep (se 2 (by rfl) ⟨2336301, by rfl⟩ : syracuseStep 6230137 = 4672603) B4672603
theorem B8306849 : Blo 2157435 8306849 := bstep (se 2 (by rfl) ⟨3115068, by rfl⟩ : syracuseStep 8306849 = 6230137) B6230137
theorem B5537899 : Blo 2157435 5537899 := bstep (se 1 (by rfl) ⟨4153424, by rfl⟩ : syracuseStep 5537899 = 8306849) B8306849
theorem B7383865 : Blo 2157435 7383865 := bstep (se 2 (by rfl) ⟨2768949, by rfl⟩ : syracuseStep 7383865 = 5537899) B5537899
theorem B9845153 : Blo 2157435 9845153 := bstep (se 2 (by rfl) ⟨3691932, by rfl⟩ : syracuseStep 9845153 = 7383865) B7383865
theorem B6563435 : Blo 2157435 6563435 := bstep (se 1 (by rfl) ⟨4922576, by rfl⟩ : syracuseStep 6563435 = 9845153) B9845153
theorem B17502493 : Blo 2157435 17502493 := bstep (se 3 (by rfl) ⟨3281717, by rfl⟩ : syracuseStep 17502493 = 6563435) B6563435
theorem B23336657 : Blo 2157435 23336657 := bstep (se 2 (by rfl) ⟨8751246, by rfl⟩ : syracuseStep 23336657 = 17502493) B17502493
theorem B15557771 : Blo 2157435 15557771 := bstep (se 1 (by rfl) ⟨11668328, by rfl⟩ : syracuseStep 15557771 = 23336657) B23336657
theorem B41487389 : Blo 2157435 41487389 := bstep (se 3 (by rfl) ⟨7778885, by rfl⟩ : syracuseStep 41487389 = 15557771) B15557771
theorem B27658259 : Blo 2157435 27658259 := bstep (se 1 (by rfl) ⟨20743694, by rfl⟩ : syracuseStep 27658259 = 41487389) B41487389
theorem B18438839 : Blo 2157435 18438839 := bstep (se 1 (by rfl) ⟨13829129, by rfl⟩ : syracuseStep 18438839 = 27658259) B27658259
theorem B12292559 : Blo 2157435 12292559 := bstep (se 1 (by rfl) ⟨9219419, by rfl⟩ : syracuseStep 12292559 = 18438839) B18438839
theorem B8195039 : Blo 2157435 8195039 := bstep (se 1 (by rfl) ⟨6146279, by rfl⟩ : syracuseStep 8195039 = 12292559) B12292559
theorem B5463359 : Blo 2157435 5463359 := bstep (se 1 (by rfl) ⟨4097519, by rfl⟩ : syracuseStep 5463359 = 8195039) B8195039
theorem B3642239 : Blo 2157435 3642239 := bstep (se 1 (by rfl) ⟨2731679, by rfl⟩ : syracuseStep 3642239 = 5463359) B5463359
theorem B2428159 : Blo 2157435 2428159 := bstep (se 1 (by rfl) ⟨1821119, by rfl⟩ : syracuseStep 2428159 = 3642239) B3642239
theorem B3237545 : Blo 2157435 3237545 := bstep (se 2 (by rfl) ⟨1214079, by rfl⟩ : syracuseStep 3237545 = 2428159) B2428159
theorem B2158363 : Blo 2157435 2158363 := bstep (se 1 (by rfl) ⟨1618772, by rfl⟩ : syracuseStep 2158363 = 3237545) B3237545
theorem B3281725 : Blo 2157435 3281725 := bbase (se 3 (by rfl) ⟨615323, by rfl⟩ : syracuseStep 3281725 = 1230647) (by norm_num)
theorem B4375633 : Blo 2157435 4375633 := bstep (se 2 (by rfl) ⟨1640862, by rfl⟩ : syracuseStep 4375633 = 3281725) B3281725
theorem B5834177 : Blo 2157435 5834177 := bstep (se 2 (by rfl) ⟨2187816, by rfl⟩ : syracuseStep 5834177 = 4375633) B4375633
theorem B3889451 : Blo 2157435 3889451 := bstep (se 1 (by rfl) ⟨2917088, by rfl⟩ : syracuseStep 3889451 = 5834177) B5834177
theorem B2592967 : Blo 2157435 2592967 := bstep (se 1 (by rfl) ⟨1944725, by rfl⟩ : syracuseStep 2592967 = 3889451) B3889451
theorem B3457289 : Blo 2157435 3457289 := bstep (se 2 (by rfl) ⟨1296483, by rfl⟩ : syracuseStep 3457289 = 2592967) B2592967
theorem B2304859 : Blo 2157435 2304859 := bstep (se 1 (by rfl) ⟨1728644, by rfl⟩ : syracuseStep 2304859 = 3457289) B3457289
theorem B3073145 : Blo 2157435 3073145 := bstep (se 2 (by rfl) ⟨1152429, by rfl⟩ : syracuseStep 3073145 = 2304859) B2304859
theorem B8195053 : Blo 2157435 8195053 := bstep (se 3 (by rfl) ⟨1536572, by rfl⟩ : syracuseStep 8195053 = 3073145) B3073145
theorem B10926737 : Blo 2157435 10926737 := bstep (se 2 (by rfl) ⟨4097526, by rfl⟩ : syracuseStep 10926737 = 8195053) B8195053
theorem B7284491 : Blo 2157435 7284491 := bstep (se 1 (by rfl) ⟨5463368, by rfl⟩ : syracuseStep 7284491 = 10926737) B10926737
theorem B4856327 : Blo 2157435 4856327 := bstep (se 1 (by rfl) ⟨3642245, by rfl⟩ : syracuseStep 4856327 = 7284491) B7284491
theorem B3237551 : Blo 2157435 3237551 := bstep (se 1 (by rfl) ⟨2428163, by rfl⟩ : syracuseStep 3237551 = 4856327) B4856327
theorem B2158367 : Blo 2157435 2158367 := bstep (se 1 (by rfl) ⟨1618775, by rfl⟩ : syracuseStep 2158367 = 3237551) B3237551
theorem B3237557 : Blo 2157435 3237557 := bbase (se 5 (by rfl) ⟨151760, by rfl⟩ : syracuseStep 3237557 = 303521) (by norm_num)
theorem B2158371 : Blo 2157435 2158371 := bstep (se 1 (by rfl) ⟨1618778, by rfl⟩ : syracuseStep 2158371 = 3237557) B3237557
theorem B5463389 : Blo 2157435 5463389 := bbase (se 3 (by rfl) ⟨1024385, by rfl⟩ : syracuseStep 5463389 = 2048771) (by norm_num)
theorem B3642259 : Blo 2157435 3642259 := bstep (se 1 (by rfl) ⟨2731694, by rfl⟩ : syracuseStep 3642259 = 5463389) B5463389
theorem B4856345 : Blo 2157435 4856345 := bstep (se 2 (by rfl) ⟨1821129, by rfl⟩ : syracuseStep 4856345 = 3642259) B3642259
theorem B3237563 : Blo 2157435 3237563 := bstep (se 1 (by rfl) ⟨2428172, by rfl⟩ : syracuseStep 3237563 = 4856345) B4856345
theorem B2158375 : Blo 2157435 2158375 := bstep (se 1 (by rfl) ⟨1618781, by rfl⟩ : syracuseStep 2158375 = 3237563) B3237563
theorem B2428177 : Blo 2157435 2428177 := bbase (se 2 (by rfl) ⟨910566, by rfl⟩ : syracuseStep 2428177 = 1821133) (by norm_num)
theorem B3237569 : Blo 2157435 3237569 := bstep (se 2 (by rfl) ⟨1214088, by rfl⟩ : syracuseStep 3237569 = 2428177) B2428177
theorem B2158379 : Blo 2157435 2158379 := bstep (se 1 (by rfl) ⟨1618784, by rfl⟩ : syracuseStep 2158379 = 3237569) B3237569
theorem B4097557 : Blo 2157435 4097557 := bbase (se 6 (by rfl) ⟨96036, by rfl⟩ : syracuseStep 4097557 = 192073) (by norm_num)
theorem B5463409 : Blo 2157435 5463409 := bstep (se 2 (by rfl) ⟨2048778, by rfl⟩ : syracuseStep 5463409 = 4097557) B4097557
theorem B7284545 : Blo 2157435 7284545 := bstep (se 2 (by rfl) ⟨2731704, by rfl⟩ : syracuseStep 7284545 = 5463409) B5463409
theorem B4856363 : Blo 2157435 4856363 := bstep (se 1 (by rfl) ⟨3642272, by rfl⟩ : syracuseStep 4856363 = 7284545) B7284545
theorem B3237575 : Blo 2157435 3237575 := bstep (se 1 (by rfl) ⟨2428181, by rfl⟩ : syracuseStep 3237575 = 4856363) B4856363
theorem B2158383 : Blo 2157435 2158383 := bstep (se 1 (by rfl) ⟨1618787, by rfl⟩ : syracuseStep 2158383 = 3237575) B3237575
theorem B3237581 : Blo 2157435 3237581 := bbase (se 3 (by rfl) ⟨607046, by rfl⟩ : syracuseStep 3237581 = 1214093) (by norm_num)
theorem B2158387 : Blo 2157435 2158387 := bstep (se 1 (by rfl) ⟨1618790, by rfl⟩ : syracuseStep 2158387 = 3237581) B3237581
theorem B4856381 : Blo 2157435 4856381 := bbase (se 3 (by rfl) ⟨910571, by rfl⟩ : syracuseStep 4856381 = 1821143) (by norm_num)
theorem B3237587 : Blo 2157435 3237587 := bstep (se 1 (by rfl) ⟨2428190, by rfl⟩ : syracuseStep 3237587 = 4856381) B4856381
theorem B2158391 : Blo 2157435 2158391 := bstep (se 1 (by rfl) ⟨1618793, by rfl⟩ : syracuseStep 2158391 = 3237587) B3237587
theorem B3642293 : Blo 2157435 3642293 := bbase (se 5 (by rfl) ⟨170732, by rfl⟩ : syracuseStep 3642293 = 341465) (by norm_num)
theorem B2428195 : Blo 2157435 2428195 := bstep (se 1 (by rfl) ⟨1821146, by rfl⟩ : syracuseStep 2428195 = 3642293) B3642293
theorem B3237593 : Blo 2157435 3237593 := bstep (se 2 (by rfl) ⟨1214097, by rfl⟩ : syracuseStep 3237593 = 2428195) B2428195
theorem B2158395 : Blo 2157435 2158395 := bstep (se 1 (by rfl) ⟨1618796, by rfl⟩ : syracuseStep 2158395 = 3237593) B3237593
theorem B2304893 : Blo 2157435 2304893 := bbase (se 3 (by rfl) ⟨432167, by rfl⟩ : syracuseStep 2304893 = 864335) (by norm_num)
theorem B6146381 : Blo 2157435 6146381 := bstep (se 3 (by rfl) ⟨1152446, by rfl⟩ : syracuseStep 6146381 = 2304893) B2304893
theorem B16390349 : Blo 2157435 16390349 := bstep (se 3 (by rfl) ⟨3073190, by rfl⟩ : syracuseStep 16390349 = 6146381) B6146381
theorem B10926899 : Blo 2157435 10926899 := bstep (se 1 (by rfl) ⟨8195174, by rfl⟩ : syracuseStep 10926899 = 16390349) B16390349
theorem B7284599 : Blo 2157435 7284599 := bstep (se 1 (by rfl) ⟨5463449, by rfl⟩ : syracuseStep 7284599 = 10926899) B10926899
theorem B4856399 : Blo 2157435 4856399 := bstep (se 1 (by rfl) ⟨3642299, by rfl⟩ : syracuseStep 4856399 = 7284599) B7284599
theorem B3237599 : Blo 2157435 3237599 := bstep (se 1 (by rfl) ⟨2428199, by rfl⟩ : syracuseStep 3237599 = 4856399) B4856399
theorem B2158399 : Blo 2157435 2158399 := bstep (se 1 (by rfl) ⟨1618799, by rfl⟩ : syracuseStep 2158399 = 3237599) B3237599
theorem B3237605 : Blo 2157435 3237605 := bbase (se 4 (by rfl) ⟨303525, by rfl⟩ : syracuseStep 3237605 = 607051) (by norm_num)
theorem B2158403 : Blo 2157435 2158403 := bstep (se 1 (by rfl) ⟨1618802, by rfl⟩ : syracuseStep 2158403 = 3237605) B3237605
theorem B6146405 : Blo 2157435 6146405 := bbase (se 4 (by rfl) ⟨576225, by rfl⟩ : syracuseStep 6146405 = 1152451) (by norm_num)
theorem B4097603 : Blo 2157435 4097603 := bstep (se 1 (by rfl) ⟨3073202, by rfl⟩ : syracuseStep 4097603 = 6146405) B6146405
theorem B2731735 : Blo 2157435 2731735 := bstep (se 1 (by rfl) ⟨2048801, by rfl⟩ : syracuseStep 2731735 = 4097603) B4097603
theorem B3642313 : Blo 2157435 3642313 := bstep (se 2 (by rfl) ⟨1365867, by rfl⟩ : syracuseStep 3642313 = 2731735) B2731735
theorem B4856417 : Blo 2157435 4856417 := bstep (se 2 (by rfl) ⟨1821156, by rfl⟩ : syracuseStep 4856417 = 3642313) B3642313
theorem B3237611 : Blo 2157435 3237611 := bstep (se 1 (by rfl) ⟨2428208, by rfl⟩ : syracuseStep 3237611 = 4856417) B4856417
theorem B2158407 : Blo 2157435 2158407 := bstep (se 1 (by rfl) ⟨1618805, by rfl⟩ : syracuseStep 2158407 = 3237611) B3237611
theorem B2428213 : Blo 2157435 2428213 := bbase (se 5 (by rfl) ⟨113822, by rfl⟩ : syracuseStep 2428213 = 227645) (by norm_num)
theorem B3237617 : Blo 2157435 3237617 := bstep (se 2 (by rfl) ⟨1214106, by rfl⟩ : syracuseStep 3237617 = 2428213) B2428213
theorem B2158411 : Blo 2157435 2158411 := bstep (se 1 (by rfl) ⟨1618808, by rfl⟩ : syracuseStep 2158411 = 3237617) B3237617
theorem B2731745 : Blo 2157435 2731745 := bbase (se 2 (by rfl) ⟨1024404, by rfl⟩ : syracuseStep 2731745 = 2048809) (by norm_num)
theorem B7284653 : Blo 2157435 7284653 := bstep (se 3 (by rfl) ⟨1365872, by rfl⟩ : syracuseStep 7284653 = 2731745) B2731745
theorem B4856435 : Blo 2157435 4856435 := bstep (se 1 (by rfl) ⟨3642326, by rfl⟩ : syracuseStep 4856435 = 7284653) B7284653
theorem B3237623 : Blo 2157435 3237623 := bstep (se 1 (by rfl) ⟨2428217, by rfl⟩ : syracuseStep 3237623 = 4856435) B4856435
theorem B2158415 : Blo 2157435 2158415 := bstep (se 1 (by rfl) ⟨1618811, by rfl⟩ : syracuseStep 2158415 = 3237623) B3237623
theorem B3237629 : Blo 2157435 3237629 := bbase (se 3 (by rfl) ⟨607055, by rfl⟩ : syracuseStep 3237629 = 1214111) (by norm_num)
theorem B2158419 : Blo 2157435 2158419 := bstep (se 1 (by rfl) ⟨1618814, by rfl⟩ : syracuseStep 2158419 = 3237629) B3237629
theorem B4856453 : Blo 2157435 4856453 := bbase (se 4 (by rfl) ⟨455292, by rfl⟩ : syracuseStep 4856453 = 910585) (by norm_num)
theorem B3237635 : Blo 2157435 3237635 := bstep (se 1 (by rfl) ⟨2428226, by rfl⟩ : syracuseStep 3237635 = 4856453) B4856453
theorem B2158423 : Blo 2157435 2158423 := bstep (se 1 (by rfl) ⟨1618817, by rfl⟩ : syracuseStep 2158423 = 3237635) B3237635
theorem B8751509 : Blo 2157435 8751509 := bbase (se 6 (by rfl) ⟨205113, by rfl⟩ : syracuseStep 8751509 = 410227) (by norm_num)
theorem B5834339 : Blo 2157435 5834339 := bstep (se 1 (by rfl) ⟨4375754, by rfl⟩ : syracuseStep 5834339 = 8751509) B8751509
theorem B3889559 : Blo 2157435 3889559 := bstep (se 1 (by rfl) ⟨2917169, by rfl⟩ : syracuseStep 3889559 = 5834339) B5834339
theorem B10372157 : Blo 2157435 10372157 := bstep (se 3 (by rfl) ⟨1944779, by rfl⟩ : syracuseStep 10372157 = 3889559) B3889559
theorem B6914771 : Blo 2157435 6914771 := bstep (se 1 (by rfl) ⟨5186078, by rfl⟩ : syracuseStep 6914771 = 10372157) B10372157
theorem B4609847 : Blo 2157435 4609847 := bstep (se 1 (by rfl) ⟨3457385, by rfl⟩ : syracuseStep 4609847 = 6914771) B6914771
theorem B3073231 : Blo 2157435 3073231 := bstep (se 1 (by rfl) ⟨2304923, by rfl⟩ : syracuseStep 3073231 = 4609847) B4609847
theorem B4097641 : Blo 2157435 4097641 := bstep (se 2 (by rfl) ⟨1536615, by rfl⟩ : syracuseStep 4097641 = 3073231) B3073231
theorem B5463521 : Blo 2157435 5463521 := bstep (se 2 (by rfl) ⟨2048820, by rfl⟩ : syracuseStep 5463521 = 4097641) B4097641
theorem B3642347 : Blo 2157435 3642347 := bstep (se 1 (by rfl) ⟨2731760, by rfl⟩ : syracuseStep 3642347 = 5463521) B5463521
theorem B2428231 : Blo 2157435 2428231 := bstep (se 1 (by rfl) ⟨1821173, by rfl⟩ : syracuseStep 2428231 = 3642347) B3642347
theorem B3237641 : Blo 2157435 3237641 := bstep (se 2 (by rfl) ⟨1214115, by rfl⟩ : syracuseStep 3237641 = 2428231) B2428231
theorem B2158427 : Blo 2157435 2158427 := bstep (se 1 (by rfl) ⟨1618820, by rfl⟩ : syracuseStep 2158427 = 3237641) B3237641
theorem B10927061 : Blo 2157435 10927061 := bbase (se 7 (by rfl) ⟨128051, by rfl⟩ : syracuseStep 10927061 = 256103) (by norm_num)
theorem B7284707 : Blo 2157435 7284707 := bstep (se 1 (by rfl) ⟨5463530, by rfl⟩ : syracuseStep 7284707 = 10927061) B10927061
theorem B4856471 : Blo 2157435 4856471 := bstep (se 1 (by rfl) ⟨3642353, by rfl⟩ : syracuseStep 4856471 = 7284707) B7284707
theorem B3237647 : Blo 2157435 3237647 := bstep (se 1 (by rfl) ⟨2428235, by rfl⟩ : syracuseStep 3237647 = 4856471) B4856471
theorem B2158431 : Blo 2157435 2158431 := bstep (se 1 (by rfl) ⟨1618823, by rfl⟩ : syracuseStep 2158431 = 3237647) B3237647
theorem B3237653 : Blo 2157435 3237653 := bbase (se 6 (by rfl) ⟨75882, by rfl⟩ : syracuseStep 3237653 = 151765) (by norm_num)
theorem B2158435 : Blo 2157435 2158435 := bstep (se 1 (by rfl) ⟨1618826, by rfl⟩ : syracuseStep 2158435 = 3237653) B3237653
theorem B5767877 : Blo 2157435 5767877 := bbase (se 4 (by rfl) ⟨540738, by rfl⟩ : syracuseStep 5767877 = 1081477) (by norm_num)
theorem B3845251 : Blo 2157435 3845251 := bstep (se 1 (by rfl) ⟨2883938, by rfl⟩ : syracuseStep 3845251 = 5767877) B5767877
theorem B20508005 : Blo 2157435 20508005 := bstep (se 4 (by rfl) ⟨1922625, by rfl⟩ : syracuseStep 20508005 = 3845251) B3845251
theorem B13672003 : Blo 2157435 13672003 := bstep (se 1 (by rfl) ⟨10254002, by rfl⟩ : syracuseStep 13672003 = 20508005) B20508005
theorem B18229337 : Blo 2157435 18229337 := bstep (se 2 (by rfl) ⟨6836001, by rfl⟩ : syracuseStep 18229337 = 13672003) B13672003
theorem B12152891 : Blo 2157435 12152891 := bstep (se 1 (by rfl) ⟨9114668, by rfl⟩ : syracuseStep 12152891 = 18229337) B18229337
theorem B8101927 : Blo 2157435 8101927 := bstep (se 1 (by rfl) ⟨6076445, by rfl⟩ : syracuseStep 8101927 = 12152891) B12152891
theorem B10802569 : Blo 2157435 10802569 := bstep (se 2 (by rfl) ⟨4050963, by rfl⟩ : syracuseStep 10802569 = 8101927) B8101927
theorem B14403425 : Blo 2157435 14403425 := bstep (se 2 (by rfl) ⟨5401284, by rfl⟩ : syracuseStep 14403425 = 10802569) B10802569
theorem B153636533 : Blo 2157435 153636533 := bstep (se 5 (by rfl) ⟨7201712, by rfl⟩ : syracuseStep 153636533 = 14403425) B14403425
theorem B102424355 : Blo 2157435 102424355 := bstep (se 1 (by rfl) ⟨76818266, by rfl⟩ : syracuseStep 102424355 = 153636533) B153636533
theorem B68282903 : Blo 2157435 68282903 := bstep (se 1 (by rfl) ⟨51212177, by rfl⟩ : syracuseStep 68282903 = 102424355) B102424355
theorem B182087741 : Blo 2157435 182087741 := bstep (se 3 (by rfl) ⟨34141451, by rfl⟩ : syracuseStep 182087741 = 68282903) B68282903
theorem B121391827 : Blo 2157435 121391827 := bstep (se 1 (by rfl) ⟨91043870, by rfl⟩ : syracuseStep 121391827 = 182087741) B182087741
theorem B647423077 : Blo 2157435 647423077 := bstep (se 4 (by rfl) ⟨60695913, by rfl⟩ : syracuseStep 647423077 = 121391827) B121391827
theorem B863230769 : Blo 2157435 863230769 := bstep (se 2 (by rfl) ⟨323711538, by rfl⟩ : syracuseStep 863230769 = 647423077) B647423077
theorem B575487179 : Blo 2157435 575487179 := bstep (se 1 (by rfl) ⟨431615384, by rfl⟩ : syracuseStep 575487179 = 863230769) B863230769
theorem B383658119 : Blo 2157435 383658119 := bstep (se 1 (by rfl) ⟨287743589, by rfl⟩ : syracuseStep 383658119 = 575487179) B575487179
theorem B255772079 : Blo 2157435 255772079 := bstep (se 1 (by rfl) ⟨191829059, by rfl⟩ : syracuseStep 255772079 = 383658119) B383658119
theorem B170514719 : Blo 2157435 170514719 := bstep (se 1 (by rfl) ⟨127886039, by rfl⟩ : syracuseStep 170514719 = 255772079) B255772079
theorem B113676479 : Blo 2157435 113676479 := bstep (se 1 (by rfl) ⟨85257359, by rfl⟩ : syracuseStep 113676479 = 170514719) B170514719
theorem B75784319 : Blo 2157435 75784319 := bstep (se 1 (by rfl) ⟨56838239, by rfl⟩ : syracuseStep 75784319 = 113676479) B113676479
theorem B50522879 : Blo 2157435 50522879 := bstep (se 1 (by rfl) ⟨37892159, by rfl⟩ : syracuseStep 50522879 = 75784319) B75784319
theorem B33681919 : Blo 2157435 33681919 := bstep (se 1 (by rfl) ⟨25261439, by rfl⟩ : syracuseStep 33681919 = 50522879) B50522879
theorem B44909225 : Blo 2157435 44909225 := bstep (se 2 (by rfl) ⟨16840959, by rfl⟩ : syracuseStep 44909225 = 33681919) B33681919
theorem B29939483 : Blo 2157435 29939483 := bstep (se 1 (by rfl) ⟨22454612, by rfl⟩ : syracuseStep 29939483 = 44909225) B44909225
theorem B19959655 : Blo 2157435 19959655 := bstep (se 1 (by rfl) ⟨14969741, by rfl⟩ : syracuseStep 19959655 = 29939483) B29939483
theorem B26612873 : Blo 2157435 26612873 := bstep (se 2 (by rfl) ⟨9979827, by rfl⟩ : syracuseStep 26612873 = 19959655) B19959655
theorem B17741915 : Blo 2157435 17741915 := bstep (se 1 (by rfl) ⟨13306436, by rfl⟩ : syracuseStep 17741915 = 26612873) B26612873
theorem B11827943 : Blo 2157435 11827943 := bstep (se 1 (by rfl) ⟨8870957, by rfl⟩ : syracuseStep 11827943 = 17741915) B17741915
theorem B7885295 : Blo 2157435 7885295 := bstep (se 1 (by rfl) ⟨5913971, by rfl⟩ : syracuseStep 7885295 = 11827943) B11827943
theorem B5256863 : Blo 2157435 5256863 := bstep (se 1 (by rfl) ⟨3942647, by rfl⟩ : syracuseStep 5256863 = 7885295) B7885295
theorem B3504575 : Blo 2157435 3504575 := bstep (se 1 (by rfl) ⟨2628431, by rfl⟩ : syracuseStep 3504575 = 5256863) B5256863
theorem B2336383 : Blo 2157435 2336383 := bstep (se 1 (by rfl) ⟨1752287, by rfl⟩ : syracuseStep 2336383 = 3504575) B3504575
theorem B12460709 : Blo 2157435 12460709 := bstep (se 4 (by rfl) ⟨1168191, by rfl⟩ : syracuseStep 12460709 = 2336383) B2336383
theorem B33228557 : Blo 2157435 33228557 := bstep (se 3 (by rfl) ⟨6230354, by rfl⟩ : syracuseStep 33228557 = 12460709) B12460709
theorem B22152371 : Blo 2157435 22152371 := bstep (se 1 (by rfl) ⟨16614278, by rfl⟩ : syracuseStep 22152371 = 33228557) B33228557
theorem B59072989 : Blo 2157435 59072989 := bstep (se 3 (by rfl) ⟨11076185, by rfl⟩ : syracuseStep 59072989 = 22152371) B22152371
theorem B78763985 : Blo 2157435 78763985 := bstep (se 2 (by rfl) ⟨29536494, by rfl⟩ : syracuseStep 78763985 = 59072989) B59072989
theorem B52509323 : Blo 2157435 52509323 := bstep (se 1 (by rfl) ⟨39381992, by rfl⟩ : syracuseStep 52509323 = 78763985) B78763985
theorem B140024861 : Blo 2157435 140024861 := bstep (se 3 (by rfl) ⟨26254661, by rfl⟩ : syracuseStep 140024861 = 52509323) B52509323
theorem B93349907 : Blo 2157435 93349907 := bstep (se 1 (by rfl) ⟨70012430, by rfl⟩ : syracuseStep 93349907 = 140024861) B140024861
theorem B62233271 : Blo 2157435 62233271 := bstep (se 1 (by rfl) ⟨46674953, by rfl⟩ : syracuseStep 62233271 = 93349907) B93349907
theorem B41488847 : Blo 2157435 41488847 := bstep (se 1 (by rfl) ⟨31116635, by rfl⟩ : syracuseStep 41488847 = 62233271) B62233271
theorem B27659231 : Blo 2157435 27659231 := bstep (se 1 (by rfl) ⟨20744423, by rfl⟩ : syracuseStep 27659231 = 41488847) B41488847
theorem B18439487 : Blo 2157435 18439487 := bstep (se 1 (by rfl) ⟨13829615, by rfl⟩ : syracuseStep 18439487 = 27659231) B27659231
theorem B12292991 : Blo 2157435 12292991 := bstep (se 1 (by rfl) ⟨9219743, by rfl⟩ : syracuseStep 12292991 = 18439487) B18439487
theorem B8195327 : Blo 2157435 8195327 := bstep (se 1 (by rfl) ⟨6146495, by rfl⟩ : syracuseStep 8195327 = 12292991) B12292991
theorem B5463551 : Blo 2157435 5463551 := bstep (se 1 (by rfl) ⟨4097663, by rfl⟩ : syracuseStep 5463551 = 8195327) B8195327
theorem B3642367 : Blo 2157435 3642367 := bstep (se 1 (by rfl) ⟨2731775, by rfl⟩ : syracuseStep 3642367 = 5463551) B5463551
theorem B4856489 : Blo 2157435 4856489 := bstep (se 2 (by rfl) ⟨1821183, by rfl⟩ : syracuseStep 4856489 = 3642367) B3642367
theorem B3237659 : Blo 2157435 3237659 := bstep (se 1 (by rfl) ⟨2428244, by rfl⟩ : syracuseStep 3237659 = 4856489) B4856489
theorem B2158439 : Blo 2157435 2158439 := bstep (se 1 (by rfl) ⟨1618829, by rfl⟩ : syracuseStep 2158439 = 3237659) B3237659
theorem B2428249 : Blo 2157435 2428249 := bbase (se 2 (by rfl) ⟨910593, by rfl⟩ : syracuseStep 2428249 = 1821187) (by norm_num)
theorem B3237665 : Blo 2157435 3237665 := bstep (se 2 (by rfl) ⟨1214124, by rfl⟩ : syracuseStep 3237665 = 2428249) B2428249
theorem B2158443 : Blo 2157435 2158443 := bstep (se 1 (by rfl) ⟨1618832, by rfl⟩ : syracuseStep 2158443 = 3237665) B3237665
theorem B2461385 : Blo 2157435 2461385 := bbase (se 2 (by rfl) ⟨923019, by rfl⟩ : syracuseStep 2461385 = 1846039) (by norm_num)
theorem B6563693 : Blo 2157435 6563693 := bstep (se 3 (by rfl) ⟨1230692, by rfl⟩ : syracuseStep 6563693 = 2461385) B2461385
theorem B4375795 : Blo 2157435 4375795 := bstep (se 1 (by rfl) ⟨3281846, by rfl⟩ : syracuseStep 4375795 = 6563693) B6563693
theorem B5834393 : Blo 2157435 5834393 := bstep (se 2 (by rfl) ⟨2187897, by rfl⟩ : syracuseStep 5834393 = 4375795) B4375795
theorem B3889595 : Blo 2157435 3889595 := bstep (se 1 (by rfl) ⟨2917196, by rfl⟩ : syracuseStep 3889595 = 5834393) B5834393
theorem B2593063 : Blo 2157435 2593063 := bstep (se 1 (by rfl) ⟨1944797, by rfl⟩ : syracuseStep 2593063 = 3889595) B3889595
theorem B3457417 : Blo 2157435 3457417 := bstep (se 2 (by rfl) ⟨1296531, by rfl⟩ : syracuseStep 3457417 = 2593063) B2593063
theorem B4609889 : Blo 2157435 4609889 := bstep (se 2 (by rfl) ⟨1728708, by rfl⟩ : syracuseStep 4609889 = 3457417) B3457417
theorem B3073259 : Blo 2157435 3073259 := bstep (se 1 (by rfl) ⟨2304944, by rfl⟩ : syracuseStep 3073259 = 4609889) B4609889
theorem B8195357 : Blo 2157435 8195357 := bstep (se 3 (by rfl) ⟨1536629, by rfl⟩ : syracuseStep 8195357 = 3073259) B3073259
theorem B5463571 : Blo 2157435 5463571 := bstep (se 1 (by rfl) ⟨4097678, by rfl⟩ : syracuseStep 5463571 = 8195357) B8195357
theorem B7284761 : Blo 2157435 7284761 := bstep (se 2 (by rfl) ⟨2731785, by rfl⟩ : syracuseStep 7284761 = 5463571) B5463571
theorem B4856507 : Blo 2157435 4856507 := bstep (se 1 (by rfl) ⟨3642380, by rfl⟩ : syracuseStep 4856507 = 7284761) B7284761
theorem B3237671 : Blo 2157435 3237671 := bstep (se 1 (by rfl) ⟨2428253, by rfl⟩ : syracuseStep 3237671 = 4856507) B4856507
theorem B2158447 : Blo 2157435 2158447 := bstep (se 1 (by rfl) ⟨1618835, by rfl⟩ : syracuseStep 2158447 = 3237671) B3237671
theorem B3237677 : Blo 2157435 3237677 := bbase (se 3 (by rfl) ⟨607064, by rfl⟩ : syracuseStep 3237677 = 1214129) (by norm_num)
theorem B2158451 : Blo 2157435 2158451 := bstep (se 1 (by rfl) ⟨1618838, by rfl⟩ : syracuseStep 2158451 = 3237677) B3237677
theorem B4856525 : Blo 2157435 4856525 := bbase (se 3 (by rfl) ⟨910598, by rfl⟩ : syracuseStep 4856525 = 1821197) (by norm_num)
theorem B3237683 : Blo 2157435 3237683 := bstep (se 1 (by rfl) ⟨2428262, by rfl⟩ : syracuseStep 3237683 = 4856525) B4856525
theorem B2158455 : Blo 2157435 2158455 := bstep (se 1 (by rfl) ⟨1618841, by rfl⟩ : syracuseStep 2158455 = 3237683) B3237683
theorem B2731801 : Blo 2157435 2731801 := bbase (se 2 (by rfl) ⟨1024425, by rfl⟩ : syracuseStep 2731801 = 2048851) (by norm_num)
theorem B3642401 : Blo 2157435 3642401 := bstep (se 2 (by rfl) ⟨1365900, by rfl⟩ : syracuseStep 3642401 = 2731801) B2731801
theorem B2428267 : Blo 2157435 2428267 := bstep (se 1 (by rfl) ⟨1821200, by rfl⟩ : syracuseStep 2428267 = 3642401) B3642401
theorem B3237689 : Blo 2157435 3237689 := bstep (se 2 (by rfl) ⟨1214133, by rfl⟩ : syracuseStep 3237689 = 2428267) B2428267
theorem B2158459 : Blo 2157435 2158459 := bstep (se 1 (by rfl) ⟨1618844, by rfl⟩ : syracuseStep 2158459 = 3237689) B3237689
theorem B9219845 : Blo 2157435 9219845 := bbase (se 4 (by rfl) ⟨864360, by rfl⟩ : syracuseStep 9219845 = 1728721) (by norm_num)
theorem B24586253 : Blo 2157435 24586253 := bstep (se 3 (by rfl) ⟨4609922, by rfl⟩ : syracuseStep 24586253 = 9219845) B9219845
theorem B16390835 : Blo 2157435 16390835 := bstep (se 1 (by rfl) ⟨12293126, by rfl⟩ : syracuseStep 16390835 = 24586253) B24586253
theorem B10927223 : Blo 2157435 10927223 := bstep (se 1 (by rfl) ⟨8195417, by rfl⟩ : syracuseStep 10927223 = 16390835) B16390835
theorem B7284815 : Blo 2157435 7284815 := bstep (se 1 (by rfl) ⟨5463611, by rfl⟩ : syracuseStep 7284815 = 10927223) B10927223
theorem B4856543 : Blo 2157435 4856543 := bstep (se 1 (by rfl) ⟨3642407, by rfl⟩ : syracuseStep 4856543 = 7284815) B7284815
theorem B3237695 : Blo 2157435 3237695 := bstep (se 1 (by rfl) ⟨2428271, by rfl⟩ : syracuseStep 3237695 = 4856543) B4856543
theorem B2158463 : Blo 2157435 2158463 := bstep (se 1 (by rfl) ⟨1618847, by rfl⟩ : syracuseStep 2158463 = 3237695) B3237695
theorem B3237701 : Blo 2157435 3237701 := bbase (se 4 (by rfl) ⟨303534, by rfl⟩ : syracuseStep 3237701 = 607069) (by norm_num)
theorem B2158467 : Blo 2157435 2158467 := bstep (se 1 (by rfl) ⟨1618850, by rfl⟩ : syracuseStep 2158467 = 3237701) B3237701
theorem B3642421 : Blo 2157435 3642421 := bbase (se 5 (by rfl) ⟨170738, by rfl⟩ : syracuseStep 3642421 = 341477) (by norm_num)
theorem B4856561 : Blo 2157435 4856561 := bstep (se 2 (by rfl) ⟨1821210, by rfl⟩ : syracuseStep 4856561 = 3642421) B3642421
theorem B3237707 : Blo 2157435 3237707 := bstep (se 1 (by rfl) ⟨2428280, by rfl⟩ : syracuseStep 3237707 = 4856561) B4856561
theorem B2158471 : Blo 2157435 2158471 := bstep (se 1 (by rfl) ⟨1618853, by rfl⟩ : syracuseStep 2158471 = 3237707) B3237707
theorem B2428285 : Blo 2157435 2428285 := bbase (se 3 (by rfl) ⟨455303, by rfl⟩ : syracuseStep 2428285 = 910607) (by norm_num)
theorem B3237713 : Blo 2157435 3237713 := bstep (se 2 (by rfl) ⟨1214142, by rfl⟩ : syracuseStep 3237713 = 2428285) B2428285
theorem B2158475 : Blo 2157435 2158475 := bstep (se 1 (by rfl) ⟨1618856, by rfl⟩ : syracuseStep 2158475 = 3237713) B3237713
theorem B7284869 : Blo 2157435 7284869 := bbase (se 4 (by rfl) ⟨682956, by rfl⟩ : syracuseStep 7284869 = 1365913) (by norm_num)
theorem B4856579 : Blo 2157435 4856579 := bstep (se 1 (by rfl) ⟨3642434, by rfl⟩ : syracuseStep 4856579 = 7284869) B7284869
theorem B3237719 : Blo 2157435 3237719 := bstep (se 1 (by rfl) ⟨2428289, by rfl⟩ : syracuseStep 3237719 = 4856579) B4856579
theorem B2158479 : Blo 2157435 2158479 := bstep (se 1 (by rfl) ⟨1618859, by rfl⟩ : syracuseStep 2158479 = 3237719) B3237719
theorem B3237725 : Blo 2157435 3237725 := bbase (se 3 (by rfl) ⟨607073, by rfl⟩ : syracuseStep 3237725 = 1214147) (by norm_num)
theorem B2158483 : Blo 2157435 2158483 := bstep (se 1 (by rfl) ⟨1618862, by rfl⟩ : syracuseStep 2158483 = 3237725) B3237725
theorem B4856597 : Blo 2157435 4856597 := bbase (se 6 (by rfl) ⟨113826, by rfl⟩ : syracuseStep 4856597 = 227653) (by norm_num)
theorem B3237731 : Blo 2157435 3237731 := bstep (se 1 (by rfl) ⟨2428298, by rfl⟩ : syracuseStep 3237731 = 4856597) B4856597
theorem B2158487 : Blo 2157435 2158487 := bstep (se 1 (by rfl) ⟨1618865, by rfl⟩ : syracuseStep 2158487 = 3237731) B3237731
theorem B8195525 : Blo 2157435 8195525 := bbase (se 4 (by rfl) ⟨768330, by rfl⟩ : syracuseStep 8195525 = 1536661) (by norm_num)
theorem B5463683 : Blo 2157435 5463683 := bstep (se 1 (by rfl) ⟨4097762, by rfl⟩ : syracuseStep 5463683 = 8195525) B8195525
theorem B3642455 : Blo 2157435 3642455 := bstep (se 1 (by rfl) ⟨2731841, by rfl⟩ : syracuseStep 3642455 = 5463683) B5463683
theorem B2428303 : Blo 2157435 2428303 := bstep (se 1 (by rfl) ⟨1821227, by rfl⟩ : syracuseStep 2428303 = 3642455) B3642455
theorem B3237737 : Blo 2157435 3237737 := bstep (se 2 (by rfl) ⟨1214151, by rfl⟩ : syracuseStep 3237737 = 2428303) B2428303
theorem B2158491 : Blo 2157435 2158491 := bstep (se 1 (by rfl) ⟨1618868, by rfl⟩ : syracuseStep 2158491 = 3237737) B3237737
theorem B14970133 : Blo 2157435 14970133 := bbase (se 6 (by rfl) ⟨350862, by rfl⟩ : syracuseStep 14970133 = 701725) (by norm_num)
theorem B19960177 : Blo 2157435 19960177 := bstep (se 2 (by rfl) ⟨7485066, by rfl⟩ : syracuseStep 19960177 = 14970133) B14970133
theorem B26613569 : Blo 2157435 26613569 := bstep (se 2 (by rfl) ⟨9980088, by rfl⟩ : syracuseStep 26613569 = 19960177) B19960177
theorem B70969517 : Blo 2157435 70969517 := bstep (se 3 (by rfl) ⟨13306784, by rfl⟩ : syracuseStep 70969517 = 26613569) B26613569
theorem B47313011 : Blo 2157435 47313011 := bstep (se 1 (by rfl) ⟨35484758, by rfl⟩ : syracuseStep 47313011 = 70969517) B70969517
theorem B31542007 : Blo 2157435 31542007 := bstep (se 1 (by rfl) ⟨23656505, by rfl⟩ : syracuseStep 31542007 = 47313011) B47313011
theorem B42056009 : Blo 2157435 42056009 := bstep (se 2 (by rfl) ⟨15771003, by rfl⟩ : syracuseStep 42056009 = 31542007) B31542007
theorem B28037339 : Blo 2157435 28037339 := bstep (se 1 (by rfl) ⟨21028004, by rfl⟩ : syracuseStep 28037339 = 42056009) B42056009
theorem B18691559 : Blo 2157435 18691559 := bstep (se 1 (by rfl) ⟨14018669, by rfl⟩ : syracuseStep 18691559 = 28037339) B28037339
theorem B12461039 : Blo 2157435 12461039 := bstep (se 1 (by rfl) ⟨9345779, by rfl⟩ : syracuseStep 12461039 = 18691559) B18691559
theorem B8307359 : Blo 2157435 8307359 := bstep (se 1 (by rfl) ⟨6230519, by rfl⟩ : syracuseStep 8307359 = 12461039) B12461039
theorem B5538239 : Blo 2157435 5538239 := bstep (se 1 (by rfl) ⟨4153679, by rfl⟩ : syracuseStep 5538239 = 8307359) B8307359
theorem B3692159 : Blo 2157435 3692159 := bstep (se 1 (by rfl) ⟨2769119, by rfl⟩ : syracuseStep 3692159 = 5538239) B5538239
theorem B2461439 : Blo 2157435 2461439 := bstep (se 1 (by rfl) ⟨1846079, by rfl⟩ : syracuseStep 2461439 = 3692159) B3692159
theorem B6563837 : Blo 2157435 6563837 := bstep (se 3 (by rfl) ⟨1230719, by rfl⟩ : syracuseStep 6563837 = 2461439) B2461439
theorem B4375891 : Blo 2157435 4375891 := bstep (se 1 (by rfl) ⟨3281918, by rfl⟩ : syracuseStep 4375891 = 6563837) B6563837
theorem B5834521 : Blo 2157435 5834521 := bstep (se 2 (by rfl) ⟨2187945, by rfl⟩ : syracuseStep 5834521 = 4375891) B4375891
theorem B7779361 : Blo 2157435 7779361 := bstep (se 2 (by rfl) ⟨2917260, by rfl⟩ : syracuseStep 7779361 = 5834521) B5834521
theorem B10372481 : Blo 2157435 10372481 := bstep (se 2 (by rfl) ⟨3889680, by rfl⟩ : syracuseStep 10372481 = 7779361) B7779361
theorem B6914987 : Blo 2157435 6914987 := bstep (se 1 (by rfl) ⟨5186240, by rfl⟩ : syracuseStep 6914987 = 10372481) B10372481
theorem B4609991 : Blo 2157435 4609991 := bstep (se 1 (by rfl) ⟨3457493, by rfl⟩ : syracuseStep 4609991 = 6914987) B6914987
theorem B12293309 : Blo 2157435 12293309 := bstep (se 3 (by rfl) ⟨2304995, by rfl⟩ : syracuseStep 12293309 = 4609991) B4609991
theorem B8195539 : Blo 2157435 8195539 := bstep (se 1 (by rfl) ⟨6146654, by rfl⟩ : syracuseStep 8195539 = 12293309) B12293309
theorem B10927385 : Blo 2157435 10927385 := bstep (se 2 (by rfl) ⟨4097769, by rfl⟩ : syracuseStep 10927385 = 8195539) B8195539
theorem B7284923 : Blo 2157435 7284923 := bstep (se 1 (by rfl) ⟨5463692, by rfl⟩ : syracuseStep 7284923 = 10927385) B10927385
theorem B4856615 : Blo 2157435 4856615 := bstep (se 1 (by rfl) ⟨3642461, by rfl⟩ : syracuseStep 4856615 = 7284923) B7284923
theorem B3237743 : Blo 2157435 3237743 := bstep (se 1 (by rfl) ⟨2428307, by rfl⟩ : syracuseStep 3237743 = 4856615) B4856615
theorem B2158495 : Blo 2157435 2158495 := bstep (se 1 (by rfl) ⟨1618871, by rfl⟩ : syracuseStep 2158495 = 3237743) B3237743
theorem B3237749 : Blo 2157435 3237749 := bbase (se 5 (by rfl) ⟨151769, by rfl⟩ : syracuseStep 3237749 = 303539) (by norm_num)
theorem B2158499 : Blo 2157435 2158499 := bstep (se 1 (by rfl) ⟨1618874, by rfl⟩ : syracuseStep 2158499 = 3237749) B3237749
theorem B5186261 : Blo 2157435 5186261 := bbase (se 7 (by rfl) ⟨60776, by rfl⟩ : syracuseStep 5186261 = 121553) (by norm_num)
theorem B3457507 : Blo 2157435 3457507 := bstep (se 1 (by rfl) ⟨2593130, by rfl⟩ : syracuseStep 3457507 = 5186261) B5186261
theorem B4610009 : Blo 2157435 4610009 := bstep (se 2 (by rfl) ⟨1728753, by rfl⟩ : syracuseStep 4610009 = 3457507) B3457507
theorem B3073339 : Blo 2157435 3073339 := bstep (se 1 (by rfl) ⟨2305004, by rfl⟩ : syracuseStep 3073339 = 4610009) B4610009
theorem B4097785 : Blo 2157435 4097785 := bstep (se 2 (by rfl) ⟨1536669, by rfl⟩ : syracuseStep 4097785 = 3073339) B3073339
theorem B5463713 : Blo 2157435 5463713 := bstep (se 2 (by rfl) ⟨2048892, by rfl⟩ : syracuseStep 5463713 = 4097785) B4097785
theorem B3642475 : Blo 2157435 3642475 := bstep (se 1 (by rfl) ⟨2731856, by rfl⟩ : syracuseStep 3642475 = 5463713) B5463713
theorem B4856633 : Blo 2157435 4856633 := bstep (se 2 (by rfl) ⟨1821237, by rfl⟩ : syracuseStep 4856633 = 3642475) B3642475
theorem B3237755 : Blo 2157435 3237755 := bstep (se 1 (by rfl) ⟨2428316, by rfl⟩ : syracuseStep 3237755 = 4856633) B4856633
theorem B2158503 : Blo 2157435 2158503 := bstep (se 1 (by rfl) ⟨1618877, by rfl⟩ : syracuseStep 2158503 = 3237755) B3237755
theorem B2428321 : Blo 2157435 2428321 := bbase (se 2 (by rfl) ⟨910620, by rfl⟩ : syracuseStep 2428321 = 1821241) (by norm_num)
theorem B3237761 : Blo 2157435 3237761 := bstep (se 2 (by rfl) ⟨1214160, by rfl⟩ : syracuseStep 3237761 = 2428321) B2428321
theorem B2158507 : Blo 2157435 2158507 := bstep (se 1 (by rfl) ⟨1618880, by rfl⟩ : syracuseStep 2158507 = 3237761) B3237761
theorem B5463733 : Blo 2157435 5463733 := bbase (se 5 (by rfl) ⟨256112, by rfl⟩ : syracuseStep 5463733 = 512225) (by norm_num)
theorem B7284977 : Blo 2157435 7284977 := bstep (se 2 (by rfl) ⟨2731866, by rfl⟩ : syracuseStep 7284977 = 5463733) B5463733
theorem B4856651 : Blo 2157435 4856651 := bstep (se 1 (by rfl) ⟨3642488, by rfl⟩ : syracuseStep 4856651 = 7284977) B7284977
theorem B3237767 : Blo 2157435 3237767 := bstep (se 1 (by rfl) ⟨2428325, by rfl⟩ : syracuseStep 3237767 = 4856651) B4856651
theorem B2158511 : Blo 2157435 2158511 := bstep (se 1 (by rfl) ⟨1618883, by rfl⟩ : syracuseStep 2158511 = 3237767) B3237767
theorem B3237773 : Blo 2157435 3237773 := bbase (se 3 (by rfl) ⟨607082, by rfl⟩ : syracuseStep 3237773 = 1214165) (by norm_num)
theorem B2158515 : Blo 2157435 2158515 := bstep (se 1 (by rfl) ⟨1618886, by rfl⟩ : syracuseStep 2158515 = 3237773) B3237773
theorem B4856669 : Blo 2157435 4856669 := bbase (se 3 (by rfl) ⟨910625, by rfl⟩ : syracuseStep 4856669 = 1821251) (by norm_num)
theorem B3237779 : Blo 2157435 3237779 := bstep (se 1 (by rfl) ⟨2428334, by rfl⟩ : syracuseStep 3237779 = 4856669) B4856669
theorem B2158519 : Blo 2157435 2158519 := bstep (se 1 (by rfl) ⟨1618889, by rfl⟩ : syracuseStep 2158519 = 3237779) B3237779
theorem B3642509 : Blo 2157435 3642509 := bbase (se 3 (by rfl) ⟨682970, by rfl⟩ : syracuseStep 3642509 = 1365941) (by norm_num)
theorem B2428339 : Blo 2157435 2428339 := bstep (se 1 (by rfl) ⟨1821254, by rfl⟩ : syracuseStep 2428339 = 3642509) B3642509
theorem B3237785 : Blo 2157435 3237785 := bstep (se 2 (by rfl) ⟨1214169, by rfl⟩ : syracuseStep 3237785 = 2428339) B2428339
theorem B2158523 : Blo 2157435 2158523 := bstep (se 1 (by rfl) ⟨1618892, by rfl⟩ : syracuseStep 2158523 = 3237785) B3237785
theorem B5186317 : Blo 2157435 5186317 := bbase (se 3 (by rfl) ⟨972434, by rfl⟩ : syracuseStep 5186317 = 1944869) (by norm_num)
theorem B6915089 : Blo 2157435 6915089 := bstep (se 2 (by rfl) ⟨2593158, by rfl⟩ : syracuseStep 6915089 = 5186317) B5186317
theorem B18440237 : Blo 2157435 18440237 := bstep (se 3 (by rfl) ⟨3457544, by rfl⟩ : syracuseStep 18440237 = 6915089) B6915089
theorem B12293491 : Blo 2157435 12293491 := bstep (se 1 (by rfl) ⟨9220118, by rfl⟩ : syracuseStep 12293491 = 18440237) B18440237
theorem B16391321 : Blo 2157435 16391321 := bstep (se 2 (by rfl) ⟨6146745, by rfl⟩ : syracuseStep 16391321 = 12293491) B12293491
theorem B10927547 : Blo 2157435 10927547 := bstep (se 1 (by rfl) ⟨8195660, by rfl⟩ : syracuseStep 10927547 = 16391321) B16391321
theorem B7285031 : Blo 2157435 7285031 := bstep (se 1 (by rfl) ⟨5463773, by rfl⟩ : syracuseStep 7285031 = 10927547) B10927547
theorem B4856687 : Blo 2157435 4856687 := bstep (se 1 (by rfl) ⟨3642515, by rfl⟩ : syracuseStep 4856687 = 7285031) B7285031
theorem B3237791 : Blo 2157435 3237791 := bstep (se 1 (by rfl) ⟨2428343, by rfl⟩ : syracuseStep 3237791 = 4856687) B4856687
theorem B2158527 : Blo 2157435 2158527 := bstep (se 1 (by rfl) ⟨1618895, by rfl⟩ : syracuseStep 2158527 = 3237791) B3237791
theorem B3237797 : Blo 2157435 3237797 := bbase (se 4 (by rfl) ⟨303543, by rfl⟩ : syracuseStep 3237797 = 607087) (by norm_num)
theorem B2158531 : Blo 2157435 2158531 := bstep (se 1 (by rfl) ⟨1618898, by rfl⟩ : syracuseStep 2158531 = 3237797) B3237797
theorem B2731897 : Blo 2157435 2731897 := bbase (se 2 (by rfl) ⟨1024461, by rfl⟩ : syracuseStep 2731897 = 2048923) (by norm_num)
theorem B3642529 : Blo 2157435 3642529 := bstep (se 2 (by rfl) ⟨1365948, by rfl⟩ : syracuseStep 3642529 = 2731897) B2731897
theorem B4856705 : Blo 2157435 4856705 := bstep (se 2 (by rfl) ⟨1821264, by rfl⟩ : syracuseStep 4856705 = 3642529) B3642529
theorem B3237803 : Blo 2157435 3237803 := bstep (se 1 (by rfl) ⟨2428352, by rfl⟩ : syracuseStep 3237803 = 4856705) B4856705
theorem B2158535 : Blo 2157435 2158535 := bstep (se 1 (by rfl) ⟨1618901, by rfl⟩ : syracuseStep 2158535 = 3237803) B3237803
theorem B2428357 : Blo 2157435 2428357 := bbase (se 4 (by rfl) ⟨227658, by rfl⟩ : syracuseStep 2428357 = 455317) (by norm_num)
theorem B3237809 : Blo 2157435 3237809 := bstep (se 2 (by rfl) ⟨1214178, by rfl⟩ : syracuseStep 3237809 = 2428357) B2428357
theorem B2158539 : Blo 2157435 2158539 := bstep (se 1 (by rfl) ⟨1618904, by rfl⟩ : syracuseStep 2158539 = 3237809) B3237809
theorem B4097861 : Blo 2157435 4097861 := bbase (se 4 (by rfl) ⟨384174, by rfl⟩ : syracuseStep 4097861 = 768349) (by norm_num)
theorem B2731907 : Blo 2157435 2731907 := bstep (se 1 (by rfl) ⟨2048930, by rfl⟩ : syracuseStep 2731907 = 4097861) B4097861
theorem B7285085 : Blo 2157435 7285085 := bstep (se 3 (by rfl) ⟨1365953, by rfl⟩ : syracuseStep 7285085 = 2731907) B2731907
theorem B4856723 : Blo 2157435 4856723 := bstep (se 1 (by rfl) ⟨3642542, by rfl⟩ : syracuseStep 4856723 = 7285085) B7285085
theorem B3237815 : Blo 2157435 3237815 := bstep (se 1 (by rfl) ⟨2428361, by rfl⟩ : syracuseStep 3237815 = 4856723) B4856723
theorem B2158543 : Blo 2157435 2158543 := bstep (se 1 (by rfl) ⟨1618907, by rfl⟩ : syracuseStep 2158543 = 3237815) B3237815
theorem B3237821 : Blo 2157435 3237821 := bbase (se 3 (by rfl) ⟨607091, by rfl⟩ : syracuseStep 3237821 = 1214183) (by norm_num)
theorem B2158547 : Blo 2157435 2158547 := bstep (se 1 (by rfl) ⟨1618910, by rfl⟩ : syracuseStep 2158547 = 3237821) B3237821
theorem B4856741 : Blo 2157435 4856741 := bbase (se 4 (by rfl) ⟨455319, by rfl⟩ : syracuseStep 4856741 = 910639) (by norm_num)
theorem B3237827 : Blo 2157435 3237827 := bstep (se 1 (by rfl) ⟨2428370, by rfl⟩ : syracuseStep 3237827 = 4856741) B4856741
theorem B2158551 : Blo 2157435 2158551 := bstep (se 1 (by rfl) ⟨1618913, by rfl⟩ : syracuseStep 2158551 = 3237827) B3237827
theorem B5463845 : Blo 2157435 5463845 := bbase (se 4 (by rfl) ⟨512235, by rfl⟩ : syracuseStep 5463845 = 1024471) (by norm_num)
theorem B3642563 : Blo 2157435 3642563 := bstep (se 1 (by rfl) ⟨2731922, by rfl⟩ : syracuseStep 3642563 = 5463845) B5463845
theorem B2428375 : Blo 2157435 2428375 := bstep (se 1 (by rfl) ⟨1821281, by rfl⟩ : syracuseStep 2428375 = 3642563) B3642563
theorem B3237833 : Blo 2157435 3237833 := bstep (se 2 (by rfl) ⟨1214187, by rfl⟩ : syracuseStep 3237833 = 2428375) B2428375
theorem B2158555 : Blo 2157435 2158555 := bstep (se 1 (by rfl) ⟨1618916, by rfl⟩ : syracuseStep 2158555 = 3237833) B3237833
theorem B6146837 : Blo 2157435 6146837 := bbase (se 6 (by rfl) ⟨144066, by rfl⟩ : syracuseStep 6146837 = 288133) (by norm_num)
theorem B4097891 : Blo 2157435 4097891 := bstep (se 1 (by rfl) ⟨3073418, by rfl⟩ : syracuseStep 4097891 = 6146837) B6146837
theorem B10927709 : Blo 2157435 10927709 := bstep (se 3 (by rfl) ⟨2048945, by rfl⟩ : syracuseStep 10927709 = 4097891) B4097891
theorem B7285139 : Blo 2157435 7285139 := bstep (se 1 (by rfl) ⟨5463854, by rfl⟩ : syracuseStep 7285139 = 10927709) B10927709
theorem B4856759 : Blo 2157435 4856759 := bstep (se 1 (by rfl) ⟨3642569, by rfl⟩ : syracuseStep 4856759 = 7285139) B7285139
theorem B3237839 : Blo 2157435 3237839 := bstep (se 1 (by rfl) ⟨2428379, by rfl⟩ : syracuseStep 3237839 = 4856759) B4856759
theorem B2158559 : Blo 2157435 2158559 := bstep (se 1 (by rfl) ⟨1618919, by rfl⟩ : syracuseStep 2158559 = 3237839) B3237839
theorem B3237845 : Blo 2157435 3237845 := bbase (se 7 (by rfl) ⟨37943, by rfl⟩ : syracuseStep 3237845 = 75887) (by norm_num)
theorem B2158563 : Blo 2157435 2158563 := bstep (se 1 (by rfl) ⟨1618922, by rfl⟩ : syracuseStep 2158563 = 3237845) B3237845
theorem B8195813 : Blo 2157435 8195813 := bbase (se 4 (by rfl) ⟨768357, by rfl⟩ : syracuseStep 8195813 = 1536715) (by norm_num)
theorem B5463875 : Blo 2157435 5463875 := bstep (se 1 (by rfl) ⟨4097906, by rfl⟩ : syracuseStep 5463875 = 8195813) B8195813
theorem B3642583 : Blo 2157435 3642583 := bstep (se 1 (by rfl) ⟨2731937, by rfl⟩ : syracuseStep 3642583 = 5463875) B5463875
theorem B4856777 : Blo 2157435 4856777 := bstep (se 2 (by rfl) ⟨1821291, by rfl⟩ : syracuseStep 4856777 = 3642583) B3642583
theorem B3237851 : Blo 2157435 3237851 := bstep (se 1 (by rfl) ⟨2428388, by rfl⟩ : syracuseStep 3237851 = 4856777) B4856777
theorem B2158567 : Blo 2157435 2158567 := bstep (se 1 (by rfl) ⟨1618925, by rfl⟩ : syracuseStep 2158567 = 3237851) B3237851
theorem B2428393 : Blo 2157435 2428393 := bbase (se 2 (by rfl) ⟨910647, by rfl⟩ : syracuseStep 2428393 = 1821295) (by norm_num)
theorem B3237857 : Blo 2157435 3237857 := bstep (se 2 (by rfl) ⟨1214196, by rfl⟩ : syracuseStep 3237857 = 2428393) B2428393
theorem B2158571 : Blo 2157435 2158571 := bstep (se 1 (by rfl) ⟨1618928, by rfl⟩ : syracuseStep 2158571 = 3237857) B3237857
theorem B2305081 : Blo 2157435 2305081 := bbase (se 2 (by rfl) ⟨864405, by rfl⟩ : syracuseStep 2305081 = 1728811) (by norm_num)
theorem B12293765 : Blo 2157435 12293765 := bstep (se 4 (by rfl) ⟨1152540, by rfl⟩ : syracuseStep 12293765 = 2305081) B2305081
theorem B8195843 : Blo 2157435 8195843 := bstep (se 1 (by rfl) ⟨6146882, by rfl⟩ : syracuseStep 8195843 = 12293765) B12293765
theorem B5463895 : Blo 2157435 5463895 := bstep (se 1 (by rfl) ⟨4097921, by rfl⟩ : syracuseStep 5463895 = 8195843) B8195843
theorem B7285193 : Blo 2157435 7285193 := bstep (se 2 (by rfl) ⟨2731947, by rfl⟩ : syracuseStep 7285193 = 5463895) B5463895
theorem B4856795 : Blo 2157435 4856795 := bstep (se 1 (by rfl) ⟨3642596, by rfl⟩ : syracuseStep 4856795 = 7285193) B7285193
theorem B3237863 : Blo 2157435 3237863 := bstep (se 1 (by rfl) ⟨2428397, by rfl⟩ : syracuseStep 3237863 = 4856795) B4856795
theorem B2158575 : Blo 2157435 2158575 := bstep (se 1 (by rfl) ⟨1618931, by rfl⟩ : syracuseStep 2158575 = 3237863) B3237863
theorem B3237869 : Blo 2157435 3237869 := bbase (se 3 (by rfl) ⟨607100, by rfl⟩ : syracuseStep 3237869 = 1214201) (by norm_num)
theorem B2158579 : Blo 2157435 2158579 := bstep (se 1 (by rfl) ⟨1618934, by rfl⟩ : syracuseStep 2158579 = 3237869) B3237869
theorem B4856813 : Blo 2157435 4856813 := bbase (se 3 (by rfl) ⟨910652, by rfl⟩ : syracuseStep 4856813 = 1821305) (by norm_num)
theorem B3237875 : Blo 2157435 3237875 := bstep (se 1 (by rfl) ⟨2428406, by rfl⟩ : syracuseStep 3237875 = 4856813) B4856813
theorem B2158583 : Blo 2157435 2158583 := bstep (se 1 (by rfl) ⟨1618937, by rfl⟩ : syracuseStep 2158583 = 3237875) B3237875
theorem B4610189 : Blo 2157435 4610189 := bbase (se 3 (by rfl) ⟨864410, by rfl⟩ : syracuseStep 4610189 = 1728821) (by norm_num)
theorem B3073459 : Blo 2157435 3073459 := bstep (se 1 (by rfl) ⟨2305094, by rfl⟩ : syracuseStep 3073459 = 4610189) B4610189
theorem B4097945 : Blo 2157435 4097945 := bstep (se 2 (by rfl) ⟨1536729, by rfl⟩ : syracuseStep 4097945 = 3073459) B3073459
theorem B2731963 : Blo 2157435 2731963 := bstep (se 1 (by rfl) ⟨2048972, by rfl⟩ : syracuseStep 2731963 = 4097945) B4097945
theorem B3642617 : Blo 2157435 3642617 := bstep (se 2 (by rfl) ⟨1365981, by rfl⟩ : syracuseStep 3642617 = 2731963) B2731963
theorem B2428411 : Blo 2157435 2428411 := bstep (se 1 (by rfl) ⟨1821308, by rfl⟩ : syracuseStep 2428411 = 3642617) B3642617
theorem B3237881 : Blo 2157435 3237881 := bstep (se 2 (by rfl) ⟨1214205, by rfl⟩ : syracuseStep 3237881 = 2428411) B2428411
theorem B2158587 : Blo 2157435 2158587 := bstep (se 1 (by rfl) ⟨1618940, by rfl⟩ : syracuseStep 2158587 = 3237881) B3237881
theorem B9473701 : Blo 2157435 9473701 := bbase (se 4 (by rfl) ⟨888159, by rfl⟩ : syracuseStep 9473701 = 1776319) (by norm_num)
theorem B202105621 : Blo 2157435 202105621 := bstep (se 6 (by rfl) ⟨4736850, by rfl⟩ : syracuseStep 202105621 = 9473701) B9473701
theorem B1077896645 : Blo 2157435 1077896645 := bstep (se 4 (by rfl) ⟨101052810, by rfl⟩ : syracuseStep 1077896645 = 202105621) B202105621
theorem B718597763 : Blo 2157435 718597763 := bstep (se 1 (by rfl) ⟨538948322, by rfl⟩ : syracuseStep 718597763 = 1077896645) B1077896645
theorem B479065175 : Blo 2157435 479065175 := bstep (se 1 (by rfl) ⟨359298881, by rfl⟩ : syracuseStep 479065175 = 718597763) B718597763
theorem B319376783 : Blo 2157435 319376783 := bstep (se 1 (by rfl) ⟨239532587, by rfl⟩ : syracuseStep 319376783 = 479065175) B479065175
theorem B212917855 : Blo 2157435 212917855 := bstep (se 1 (by rfl) ⟨159688391, by rfl⟩ : syracuseStep 212917855 = 319376783) B319376783
theorem B283890473 : Blo 2157435 283890473 := bstep (se 2 (by rfl) ⟨106458927, by rfl⟩ : syracuseStep 283890473 = 212917855) B212917855
theorem B189260315 : Blo 2157435 189260315 := bstep (se 1 (by rfl) ⟨141945236, by rfl⟩ : syracuseStep 189260315 = 283890473) B283890473
theorem B126173543 : Blo 2157435 126173543 := bstep (se 1 (by rfl) ⟨94630157, by rfl⟩ : syracuseStep 126173543 = 189260315) B189260315
theorem B336462781 : Blo 2157435 336462781 := bstep (se 3 (by rfl) ⟨63086771, by rfl⟩ : syracuseStep 336462781 = 126173543) B126173543
theorem B448617041 : Blo 2157435 448617041 := bstep (se 2 (by rfl) ⟨168231390, by rfl⟩ : syracuseStep 448617041 = 336462781) B336462781
theorem B299078027 : Blo 2157435 299078027 := bstep (se 1 (by rfl) ⟨224308520, by rfl⟩ : syracuseStep 299078027 = 448617041) B448617041
theorem B199385351 : Blo 2157435 199385351 := bstep (se 1 (by rfl) ⟨149539013, by rfl⟩ : syracuseStep 199385351 = 299078027) B299078027
theorem B132923567 : Blo 2157435 132923567 := bstep (se 1 (by rfl) ⟨99692675, by rfl⟩ : syracuseStep 132923567 = 199385351) B199385351
theorem B88615711 : Blo 2157435 88615711 := bstep (se 1 (by rfl) ⟨66461783, by rfl⟩ : syracuseStep 88615711 = 132923567) B132923567
theorem B472617125 : Blo 2157435 472617125 := bstep (se 4 (by rfl) ⟨44307855, by rfl⟩ : syracuseStep 472617125 = 88615711) B88615711
theorem B315078083 : Blo 2157435 315078083 := bstep (se 1 (by rfl) ⟨236308562, by rfl⟩ : syracuseStep 315078083 = 472617125) B472617125
theorem B210052055 : Blo 2157435 210052055 := bstep (se 1 (by rfl) ⟨157539041, by rfl⟩ : syracuseStep 210052055 = 315078083) B315078083
theorem B140034703 : Blo 2157435 140034703 := bstep (se 1 (by rfl) ⟨105026027, by rfl⟩ : syracuseStep 140034703 = 210052055) B210052055
theorem B186712937 : Blo 2157435 186712937 := bstep (se 2 (by rfl) ⟨70017351, by rfl⟩ : syracuseStep 186712937 = 140034703) B140034703
theorem B124475291 : Blo 2157435 124475291 := bstep (se 1 (by rfl) ⟨93356468, by rfl⟩ : syracuseStep 124475291 = 186712937) B186712937
theorem B82983527 : Blo 2157435 82983527 := bstep (se 1 (by rfl) ⟨62237645, by rfl⟩ : syracuseStep 82983527 = 124475291) B124475291
theorem B55322351 : Blo 2157435 55322351 := bstep (se 1 (by rfl) ⟨41491763, by rfl⟩ : syracuseStep 55322351 = 82983527) B82983527
theorem B36881567 : Blo 2157435 36881567 := bstep (se 1 (by rfl) ⟨27661175, by rfl⟩ : syracuseStep 36881567 = 55322351) B55322351
theorem B24587711 : Blo 2157435 24587711 := bstep (se 1 (by rfl) ⟨18440783, by rfl⟩ : syracuseStep 24587711 = 36881567) B36881567
theorem B16391807 : Blo 2157435 16391807 := bstep (se 1 (by rfl) ⟨12293855, by rfl⟩ : syracuseStep 16391807 = 24587711) B24587711
theorem B10927871 : Blo 2157435 10927871 := bstep (se 1 (by rfl) ⟨8195903, by rfl⟩ : syracuseStep 10927871 = 16391807) B16391807
theorem B7285247 : Blo 2157435 7285247 := bstep (se 1 (by rfl) ⟨5463935, by rfl⟩ : syracuseStep 7285247 = 10927871) B10927871
theorem B4856831 : Blo 2157435 4856831 := bstep (se 1 (by rfl) ⟨3642623, by rfl⟩ : syracuseStep 4856831 = 7285247) B7285247
theorem B3237887 : Blo 2157435 3237887 := bstep (se 1 (by rfl) ⟨2428415, by rfl⟩ : syracuseStep 3237887 = 4856831) B4856831
theorem B2158591 : Blo 2157435 2158591 := bstep (se 1 (by rfl) ⟨1618943, by rfl⟩ : syracuseStep 2158591 = 3237887) B3237887
theorem B3237893 : Blo 2157435 3237893 := bbase (se 4 (by rfl) ⟨303552, by rfl⟩ : syracuseStep 3237893 = 607105) (by norm_num)
theorem B2158595 : Blo 2157435 2158595 := bstep (se 1 (by rfl) ⟨1618946, by rfl⟩ : syracuseStep 2158595 = 3237893) B3237893
theorem B3642637 : Blo 2157435 3642637 := bbase (se 3 (by rfl) ⟨682994, by rfl⟩ : syracuseStep 3642637 = 1365989) (by norm_num)
theorem B4856849 : Blo 2157435 4856849 := bstep (se 2 (by rfl) ⟨1821318, by rfl⟩ : syracuseStep 4856849 = 3642637) B3642637
theorem B3237899 : Blo 2157435 3237899 := bstep (se 1 (by rfl) ⟨2428424, by rfl⟩ : syracuseStep 3237899 = 4856849) B4856849
theorem B2158599 : Blo 2157435 2158599 := bstep (se 1 (by rfl) ⟨1618949, by rfl⟩ : syracuseStep 2158599 = 3237899) B3237899
theorem B2428429 : Blo 2157435 2428429 := bbase (se 3 (by rfl) ⟨455330, by rfl⟩ : syracuseStep 2428429 = 910661) (by norm_num)
theorem B3237905 : Blo 2157435 3237905 := bstep (se 2 (by rfl) ⟨1214214, by rfl⟩ : syracuseStep 3237905 = 2428429) B2428429
theorem B2158603 : Blo 2157435 2158603 := bstep (se 1 (by rfl) ⟨1618952, by rfl⟩ : syracuseStep 2158603 = 3237905) B3237905
theorem B7285301 : Blo 2157435 7285301 := bbase (se 5 (by rfl) ⟨341498, by rfl⟩ : syracuseStep 7285301 = 682997) (by norm_num)
theorem B4856867 : Blo 2157435 4856867 := bstep (se 1 (by rfl) ⟨3642650, by rfl⟩ : syracuseStep 4856867 = 7285301) B7285301
theorem B3237911 : Blo 2157435 3237911 := bstep (se 1 (by rfl) ⟨2428433, by rfl⟩ : syracuseStep 3237911 = 4856867) B4856867
theorem B2158607 : Blo 2157435 2158607 := bstep (se 1 (by rfl) ⟨1618955, by rfl⟩ : syracuseStep 2158607 = 3237911) B3237911
theorem B3237917 : Blo 2157435 3237917 := bbase (se 3 (by rfl) ⟨607109, by rfl⟩ : syracuseStep 3237917 = 1214219) (by norm_num)
theorem B2158611 : Blo 2157435 2158611 := bstep (se 1 (by rfl) ⟨1618958, by rfl⟩ : syracuseStep 2158611 = 3237917) B3237917
theorem B4856885 : Blo 2157435 4856885 := bbase (se 5 (by rfl) ⟨227666, by rfl⟩ : syracuseStep 4856885 = 455333) (by norm_num)
theorem B3237923 : Blo 2157435 3237923 := bstep (se 1 (by rfl) ⟨2428442, by rfl⟩ : syracuseStep 3237923 = 4856885) B4856885
theorem B2158615 : Blo 2157435 2158615 := bstep (se 1 (by rfl) ⟨1618961, by rfl⟩ : syracuseStep 2158615 = 3237923) B3237923
theorem B5538557 : Blo 2157435 5538557 := bbase (se 3 (by rfl) ⟨1038479, by rfl⟩ : syracuseStep 5538557 = 2076959) (by norm_num)
theorem B14769485 : Blo 2157435 14769485 := bstep (se 3 (by rfl) ⟨2769278, by rfl⟩ : syracuseStep 14769485 = 5538557) B5538557
theorem B9846323 : Blo 2157435 9846323 := bstep (se 1 (by rfl) ⟨7384742, by rfl⟩ : syracuseStep 9846323 = 14769485) B14769485
theorem B6564215 : Blo 2157435 6564215 := bstep (se 1 (by rfl) ⟨4923161, by rfl⟩ : syracuseStep 6564215 = 9846323) B9846323
theorem B4376143 : Blo 2157435 4376143 := bstep (se 1 (by rfl) ⟨3282107, by rfl⟩ : syracuseStep 4376143 = 6564215) B6564215
theorem B5834857 : Blo 2157435 5834857 := bstep (se 2 (by rfl) ⟨2188071, by rfl⟩ : syracuseStep 5834857 = 4376143) B4376143
theorem B7779809 : Blo 2157435 7779809 := bstep (se 2 (by rfl) ⟨2917428, by rfl⟩ : syracuseStep 7779809 = 5834857) B5834857
theorem B5186539 : Blo 2157435 5186539 := bstep (se 1 (by rfl) ⟨3889904, by rfl⟩ : syracuseStep 5186539 = 7779809) B7779809
theorem B6915385 : Blo 2157435 6915385 := bstep (se 2 (by rfl) ⟨2593269, by rfl⟩ : syracuseStep 6915385 = 5186539) B5186539
theorem B9220513 : Blo 2157435 9220513 := bstep (se 2 (by rfl) ⟨3457692, by rfl⟩ : syracuseStep 9220513 = 6915385) B6915385
theorem B12294017 : Blo 2157435 12294017 := bstep (se 2 (by rfl) ⟨4610256, by rfl⟩ : syracuseStep 12294017 = 9220513) B9220513
theorem B8196011 : Blo 2157435 8196011 := bstep (se 1 (by rfl) ⟨6147008, by rfl⟩ : syracuseStep 8196011 = 12294017) B12294017
theorem B5464007 : Blo 2157435 5464007 := bstep (se 1 (by rfl) ⟨4098005, by rfl⟩ : syracuseStep 5464007 = 8196011) B8196011
theorem B3642671 : Blo 2157435 3642671 := bstep (se 1 (by rfl) ⟨2732003, by rfl⟩ : syracuseStep 3642671 = 5464007) B5464007
theorem B2428447 : Blo 2157435 2428447 := bstep (se 1 (by rfl) ⟨1821335, by rfl⟩ : syracuseStep 2428447 = 3642671) B3642671
theorem B3237929 : Blo 2157435 3237929 := bstep (se 2 (by rfl) ⟨1214223, by rfl⟩ : syracuseStep 3237929 = 2428447) B2428447
theorem B2158619 : Blo 2157435 2158619 := bstep (se 1 (by rfl) ⟨1618964, by rfl⟩ : syracuseStep 2158619 = 3237929) B3237929
theorem B6915397 : Blo 2157435 6915397 := bbase (se 4 (by rfl) ⟨648318, by rfl⟩ : syracuseStep 6915397 = 1296637) (by norm_num)
theorem B9220529 : Blo 2157435 9220529 := bstep (se 2 (by rfl) ⟨3457698, by rfl⟩ : syracuseStep 9220529 = 6915397) B6915397
theorem B6147019 : Blo 2157435 6147019 := bstep (se 1 (by rfl) ⟨4610264, by rfl⟩ : syracuseStep 6147019 = 9220529) B9220529
theorem B8196025 : Blo 2157435 8196025 := bstep (se 2 (by rfl) ⟨3073509, by rfl⟩ : syracuseStep 8196025 = 6147019) B6147019
theorem B10928033 : Blo 2157435 10928033 := bstep (se 2 (by rfl) ⟨4098012, by rfl⟩ : syracuseStep 10928033 = 8196025) B8196025
theorem B7285355 : Blo 2157435 7285355 := bstep (se 1 (by rfl) ⟨5464016, by rfl⟩ : syracuseStep 7285355 = 10928033) B10928033
theorem B4856903 : Blo 2157435 4856903 := bstep (se 1 (by rfl) ⟨3642677, by rfl⟩ : syracuseStep 4856903 = 7285355) B7285355
theorem B3237935 : Blo 2157435 3237935 := bstep (se 1 (by rfl) ⟨2428451, by rfl⟩ : syracuseStep 3237935 = 4856903) B4856903
theorem B2158623 : Blo 2157435 2158623 := bstep (se 1 (by rfl) ⟨1618967, by rfl⟩ : syracuseStep 2158623 = 3237935) B3237935
theorem B3237941 : Blo 2157435 3237941 := bbase (se 5 (by rfl) ⟨151778, by rfl⟩ : syracuseStep 3237941 = 303557) (by norm_num)
theorem B2158627 : Blo 2157435 2158627 := bstep (se 1 (by rfl) ⟨1618970, by rfl⟩ : syracuseStep 2158627 = 3237941) B3237941
theorem B5464037 : Blo 2157435 5464037 := bbase (se 4 (by rfl) ⟨512253, by rfl⟩ : syracuseStep 5464037 = 1024507) (by norm_num)
theorem B3642691 : Blo 2157435 3642691 := bstep (se 1 (by rfl) ⟨2732018, by rfl⟩ : syracuseStep 3642691 = 5464037) B5464037
theorem B4856921 : Blo 2157435 4856921 := bstep (se 2 (by rfl) ⟨1821345, by rfl⟩ : syracuseStep 4856921 = 3642691) B3642691
theorem B3237947 : Blo 2157435 3237947 := bstep (se 1 (by rfl) ⟨2428460, by rfl⟩ : syracuseStep 3237947 = 4856921) B4856921
theorem B2158631 : Blo 2157435 2158631 := bstep (se 1 (by rfl) ⟨1618973, by rfl⟩ : syracuseStep 2158631 = 3237947) B3237947
theorem B2428465 : Blo 2157435 2428465 := bbase (se 2 (by rfl) ⟨910674, by rfl⟩ : syracuseStep 2428465 = 1821349) (by norm_num)
theorem B3237953 : Blo 2157435 3237953 := bstep (se 2 (by rfl) ⟨1214232, by rfl⟩ : syracuseStep 3237953 = 2428465) B2428465
theorem B2158635 : Blo 2157435 2158635 := bstep (se 1 (by rfl) ⟨1618976, by rfl⟩ : syracuseStep 2158635 = 3237953) B3237953
theorem B32410709 : Blo 2157435 32410709 := bbase (se 8 (by rfl) ⟨189906, by rfl⟩ : syracuseStep 32410709 = 379813) (by norm_num)
theorem B21607139 : Blo 2157435 21607139 := bstep (se 1 (by rfl) ⟨16205354, by rfl⟩ : syracuseStep 21607139 = 32410709) B32410709
theorem B14404759 : Blo 2157435 14404759 := bstep (se 1 (by rfl) ⟨10803569, by rfl⟩ : syracuseStep 14404759 = 21607139) B21607139
theorem B76825381 : Blo 2157435 76825381 := bstep (se 4 (by rfl) ⟨7202379, by rfl⟩ : syracuseStep 76825381 = 14404759) B14404759
theorem B102433841 : Blo 2157435 102433841 := bstep (se 2 (by rfl) ⟨38412690, by rfl⟩ : syracuseStep 102433841 = 76825381) B76825381
theorem B68289227 : Blo 2157435 68289227 := bstep (se 1 (by rfl) ⟨51216920, by rfl⟩ : syracuseStep 68289227 = 102433841) B102433841
theorem B45526151 : Blo 2157435 45526151 := bstep (se 1 (by rfl) ⟨34144613, by rfl⟩ : syracuseStep 45526151 = 68289227) B68289227
theorem B30350767 : Blo 2157435 30350767 := bstep (se 1 (by rfl) ⟨22763075, by rfl⟩ : syracuseStep 30350767 = 45526151) B45526151
theorem B40467689 : Blo 2157435 40467689 := bstep (se 2 (by rfl) ⟨15175383, by rfl⟩ : syracuseStep 40467689 = 30350767) B30350767
theorem B26978459 : Blo 2157435 26978459 := bstep (se 1 (by rfl) ⟨20233844, by rfl⟩ : syracuseStep 26978459 = 40467689) B40467689
theorem B287770229 : Blo 2157435 287770229 := bstep (se 5 (by rfl) ⟨13489229, by rfl⟩ : syracuseStep 287770229 = 26978459) B26978459
theorem B191846819 : Blo 2157435 191846819 := bstep (se 1 (by rfl) ⟨143885114, by rfl⟩ : syracuseStep 191846819 = 287770229) B287770229
theorem B127897879 : Blo 2157435 127897879 := bstep (se 1 (by rfl) ⟨95923409, by rfl⟩ : syracuseStep 127897879 = 191846819) B191846819
theorem B170530505 : Blo 2157435 170530505 := bstep (se 2 (by rfl) ⟨63948939, by rfl⟩ : syracuseStep 170530505 = 127897879) B127897879
theorem B113687003 : Blo 2157435 113687003 := bstep (se 1 (by rfl) ⟨85265252, by rfl⟩ : syracuseStep 113687003 = 170530505) B170530505
theorem B75791335 : Blo 2157435 75791335 := bstep (se 1 (by rfl) ⟨56843501, by rfl⟩ : syracuseStep 75791335 = 113687003) B113687003
theorem B101055113 : Blo 2157435 101055113 := bstep (se 2 (by rfl) ⟨37895667, by rfl⟩ : syracuseStep 101055113 = 75791335) B75791335
theorem B67370075 : Blo 2157435 67370075 := bstep (se 1 (by rfl) ⟨50527556, by rfl⟩ : syracuseStep 67370075 = 101055113) B101055113
theorem B44913383 : Blo 2157435 44913383 := bstep (se 1 (by rfl) ⟨33685037, by rfl⟩ : syracuseStep 44913383 = 67370075) B67370075
theorem B29942255 : Blo 2157435 29942255 := bstep (se 1 (by rfl) ⟨22456691, by rfl⟩ : syracuseStep 29942255 = 44913383) B44913383
theorem B79846013 : Blo 2157435 79846013 := bstep (se 3 (by rfl) ⟨14971127, by rfl⟩ : syracuseStep 79846013 = 29942255) B29942255
theorem B53230675 : Blo 2157435 53230675 := bstep (se 1 (by rfl) ⟨39923006, by rfl⟩ : syracuseStep 53230675 = 79846013) B79846013
theorem B70974233 : Blo 2157435 70974233 := bstep (se 2 (by rfl) ⟨26615337, by rfl⟩ : syracuseStep 70974233 = 53230675) B53230675
theorem B47316155 : Blo 2157435 47316155 := bstep (se 1 (by rfl) ⟨35487116, by rfl⟩ : syracuseStep 47316155 = 70974233) B70974233
theorem B126176413 : Blo 2157435 126176413 := bstep (se 3 (by rfl) ⟨23658077, by rfl⟩ : syracuseStep 126176413 = 47316155) B47316155
theorem B168235217 : Blo 2157435 168235217 := bstep (se 2 (by rfl) ⟨63088206, by rfl⟩ : syracuseStep 168235217 = 126176413) B126176413
theorem B112156811 : Blo 2157435 112156811 := bstep (se 1 (by rfl) ⟨84117608, by rfl⟩ : syracuseStep 112156811 = 168235217) B168235217
theorem B74771207 : Blo 2157435 74771207 := bstep (se 1 (by rfl) ⟨56078405, by rfl⟩ : syracuseStep 74771207 = 112156811) B112156811
theorem B49847471 : Blo 2157435 49847471 := bstep (se 1 (by rfl) ⟨37385603, by rfl⟩ : syracuseStep 49847471 = 74771207) B74771207
theorem B33231647 : Blo 2157435 33231647 := bstep (se 1 (by rfl) ⟨24923735, by rfl⟩ : syracuseStep 33231647 = 49847471) B49847471
theorem B22154431 : Blo 2157435 22154431 := bstep (se 1 (by rfl) ⟨16615823, by rfl⟩ : syracuseStep 22154431 = 33231647) B33231647
theorem B29539241 : Blo 2157435 29539241 := bstep (se 2 (by rfl) ⟨11077215, by rfl⟩ : syracuseStep 29539241 = 22154431) B22154431
theorem B19692827 : Blo 2157435 19692827 := bstep (se 1 (by rfl) ⟨14769620, by rfl⟩ : syracuseStep 19692827 = 29539241) B29539241
theorem B13128551 : Blo 2157435 13128551 := bstep (se 1 (by rfl) ⟨9846413, by rfl⟩ : syracuseStep 13128551 = 19692827) B19692827
theorem B8752367 : Blo 2157435 8752367 := bstep (se 1 (by rfl) ⟨6564275, by rfl⟩ : syracuseStep 8752367 = 13128551) B13128551
theorem B5834911 : Blo 2157435 5834911 := bstep (se 1 (by rfl) ⟨4376183, by rfl⟩ : syracuseStep 5834911 = 8752367) B8752367
theorem B7779881 : Blo 2157435 7779881 := bstep (se 2 (by rfl) ⟨2917455, by rfl⟩ : syracuseStep 7779881 = 5834911) B5834911
theorem B5186587 : Blo 2157435 5186587 := bstep (se 1 (by rfl) ⟨3889940, by rfl⟩ : syracuseStep 5186587 = 7779881) B7779881
theorem B6915449 : Blo 2157435 6915449 := bstep (se 2 (by rfl) ⟨2593293, by rfl⟩ : syracuseStep 6915449 = 5186587) B5186587
theorem B4610299 : Blo 2157435 4610299 := bstep (se 1 (by rfl) ⟨3457724, by rfl⟩ : syracuseStep 4610299 = 6915449) B6915449
theorem B6147065 : Blo 2157435 6147065 := bstep (se 2 (by rfl) ⟨2305149, by rfl⟩ : syracuseStep 6147065 = 4610299) B4610299
theorem B4098043 : Blo 2157435 4098043 := bstep (se 1 (by rfl) ⟨3073532, by rfl⟩ : syracuseStep 4098043 = 6147065) B6147065
theorem B5464057 : Blo 2157435 5464057 := bstep (se 2 (by rfl) ⟨2049021, by rfl⟩ : syracuseStep 5464057 = 4098043) B4098043
theorem B7285409 : Blo 2157435 7285409 := bstep (se 2 (by rfl) ⟨2732028, by rfl⟩ : syracuseStep 7285409 = 5464057) B5464057
theorem B4856939 : Blo 2157435 4856939 := bstep (se 1 (by rfl) ⟨3642704, by rfl⟩ : syracuseStep 4856939 = 7285409) B7285409
theorem B3237959 : Blo 2157435 3237959 := bstep (se 1 (by rfl) ⟨2428469, by rfl⟩ : syracuseStep 3237959 = 4856939) B4856939
theorem B2158639 : Blo 2157435 2158639 := bstep (se 1 (by rfl) ⟨1618979, by rfl⟩ : syracuseStep 2158639 = 3237959) B3237959
theorem B3237965 : Blo 2157435 3237965 := bbase (se 3 (by rfl) ⟨607118, by rfl⟩ : syracuseStep 3237965 = 1214237) (by norm_num)
theorem B2158643 : Blo 2157435 2158643 := bstep (se 1 (by rfl) ⟨1618982, by rfl⟩ : syracuseStep 2158643 = 3237965) B3237965
theorem B4856957 : Blo 2157435 4856957 := bbase (se 3 (by rfl) ⟨910679, by rfl⟩ : syracuseStep 4856957 = 1821359) (by norm_num)
theorem B3237971 : Blo 2157435 3237971 := bstep (se 1 (by rfl) ⟨2428478, by rfl⟩ : syracuseStep 3237971 = 4856957) B4856957
theorem B2158647 : Blo 2157435 2158647 := bstep (se 1 (by rfl) ⟨1618985, by rfl⟩ : syracuseStep 2158647 = 3237971) B3237971
theorem B3642725 : Blo 2157435 3642725 := bbase (se 4 (by rfl) ⟨341505, by rfl⟩ : syracuseStep 3642725 = 683011) (by norm_num)
theorem B2428483 : Blo 2157435 2428483 := bstep (se 1 (by rfl) ⟨1821362, by rfl⟩ : syracuseStep 2428483 = 3642725) B3642725
theorem B3237977 : Blo 2157435 3237977 := bstep (se 2 (by rfl) ⟨1214241, by rfl⟩ : syracuseStep 3237977 = 2428483) B2428483
theorem B2158651 : Blo 2157435 2158651 := bstep (se 1 (by rfl) ⟨1618988, by rfl⟩ : syracuseStep 2158651 = 3237977) B3237977
theorem B4610333 : Blo 2157435 4610333 := bbase (se 3 (by rfl) ⟨864437, by rfl⟩ : syracuseStep 4610333 = 1728875) (by norm_num)
theorem B3073555 : Blo 2157435 3073555 := bstep (se 1 (by rfl) ⟨2305166, by rfl⟩ : syracuseStep 3073555 = 4610333) B4610333
theorem B16392293 : Blo 2157435 16392293 := bstep (se 4 (by rfl) ⟨1536777, by rfl⟩ : syracuseStep 16392293 = 3073555) B3073555
theorem B10928195 : Blo 2157435 10928195 := bstep (se 1 (by rfl) ⟨8196146, by rfl⟩ : syracuseStep 10928195 = 16392293) B16392293
theorem B7285463 : Blo 2157435 7285463 := bstep (se 1 (by rfl) ⟨5464097, by rfl⟩ : syracuseStep 7285463 = 10928195) B10928195
theorem B4856975 : Blo 2157435 4856975 := bstep (se 1 (by rfl) ⟨3642731, by rfl⟩ : syracuseStep 4856975 = 7285463) B7285463
theorem B3237983 : Blo 2157435 3237983 := bstep (se 1 (by rfl) ⟨2428487, by rfl⟩ : syracuseStep 3237983 = 4856975) B4856975
theorem B2158655 : Blo 2157435 2158655 := bstep (se 1 (by rfl) ⟨1618991, by rfl⟩ : syracuseStep 2158655 = 3237983) B3237983
theorem B3237989 : Blo 2157435 3237989 := bbase (se 4 (by rfl) ⟨303561, by rfl⟩ : syracuseStep 3237989 = 607123) (by norm_num)
theorem B2158659 : Blo 2157435 2158659 := bstep (se 1 (by rfl) ⟨1618994, by rfl⟩ : syracuseStep 2158659 = 3237989) B3237989
theorem B7886117 : Blo 2157435 7886117 := bbase (se 4 (by rfl) ⟨739323, by rfl⟩ : syracuseStep 7886117 = 1478647) (by norm_num)
theorem B21029645 : Blo 2157435 21029645 := bstep (se 3 (by rfl) ⟨3943058, by rfl⟩ : syracuseStep 21029645 = 7886117) B7886117
theorem B14019763 : Blo 2157435 14019763 := bstep (se 1 (by rfl) ⟨10514822, by rfl⟩ : syracuseStep 14019763 = 21029645) B21029645
theorem B18693017 : Blo 2157435 18693017 := bstep (se 2 (by rfl) ⟨7009881, by rfl⟩ : syracuseStep 18693017 = 14019763) B14019763
theorem B12462011 : Blo 2157435 12462011 := bstep (se 1 (by rfl) ⟨9346508, by rfl⟩ : syracuseStep 12462011 = 18693017) B18693017
theorem B8308007 : Blo 2157435 8308007 := bstep (se 1 (by rfl) ⟨6231005, by rfl⟩ : syracuseStep 8308007 = 12462011) B12462011
theorem B5538671 : Blo 2157435 5538671 := bstep (se 1 (by rfl) ⟨4154003, by rfl⟩ : syracuseStep 5538671 = 8308007) B8308007
theorem B3692447 : Blo 2157435 3692447 := bstep (se 1 (by rfl) ⟨2769335, by rfl⟩ : syracuseStep 3692447 = 5538671) B5538671
theorem B2461631 : Blo 2157435 2461631 := bstep (se 1 (by rfl) ⟨1846223, by rfl⟩ : syracuseStep 2461631 = 3692447) B3692447
theorem B6564349 : Blo 2157435 6564349 := bstep (se 3 (by rfl) ⟨1230815, by rfl⟩ : syracuseStep 6564349 = 2461631) B2461631
theorem B8752465 : Blo 2157435 8752465 := bstep (se 2 (by rfl) ⟨3282174, by rfl⟩ : syracuseStep 8752465 = 6564349) B6564349
theorem B11669953 : Blo 2157435 11669953 := bstep (se 2 (by rfl) ⟨4376232, by rfl⟩ : syracuseStep 11669953 = 8752465) B8752465
theorem B15559937 : Blo 2157435 15559937 := bstep (se 2 (by rfl) ⟨5834976, by rfl⟩ : syracuseStep 15559937 = 11669953) B11669953
theorem B10373291 : Blo 2157435 10373291 := bstep (se 1 (by rfl) ⟨7779968, by rfl⟩ : syracuseStep 10373291 = 15559937) B15559937
theorem B6915527 : Blo 2157435 6915527 := bstep (se 1 (by rfl) ⟨5186645, by rfl⟩ : syracuseStep 6915527 = 10373291) B10373291
theorem B4610351 : Blo 2157435 4610351 := bstep (se 1 (by rfl) ⟨3457763, by rfl⟩ : syracuseStep 4610351 = 6915527) B6915527
theorem B3073567 : Blo 2157435 3073567 := bstep (se 1 (by rfl) ⟨2305175, by rfl⟩ : syracuseStep 3073567 = 4610351) B4610351
theorem B4098089 : Blo 2157435 4098089 := bstep (se 2 (by rfl) ⟨1536783, by rfl⟩ : syracuseStep 4098089 = 3073567) B3073567
theorem B2732059 : Blo 2157435 2732059 := bstep (se 1 (by rfl) ⟨2049044, by rfl⟩ : syracuseStep 2732059 = 4098089) B4098089
theorem B3642745 : Blo 2157435 3642745 := bstep (se 2 (by rfl) ⟨1366029, by rfl⟩ : syracuseStep 3642745 = 2732059) B2732059
theorem B4856993 : Blo 2157435 4856993 := bstep (se 2 (by rfl) ⟨1821372, by rfl⟩ : syracuseStep 4856993 = 3642745) B3642745
theorem B3237995 : Blo 2157435 3237995 := bstep (se 1 (by rfl) ⟨2428496, by rfl⟩ : syracuseStep 3237995 = 4856993) B4856993
theorem B2158663 : Blo 2157435 2158663 := bstep (se 1 (by rfl) ⟨1618997, by rfl⟩ : syracuseStep 2158663 = 3237995) B3237995
theorem B2428501 : Blo 2157435 2428501 := bbase (se 8 (by rfl) ⟨14229, by rfl⟩ : syracuseStep 2428501 = 28459) (by norm_num)
theorem B3238001 : Blo 2157435 3238001 := bstep (se 2 (by rfl) ⟨1214250, by rfl⟩ : syracuseStep 3238001 = 2428501) B2428501
theorem B2158667 : Blo 2157435 2158667 := bstep (se 1 (by rfl) ⟨1619000, by rfl⟩ : syracuseStep 2158667 = 3238001) B3238001
theorem B2732069 : Blo 2157435 2732069 := bbase (se 4 (by rfl) ⟨256131, by rfl⟩ : syracuseStep 2732069 = 512263) (by norm_num)
theorem B7285517 : Blo 2157435 7285517 := bstep (se 3 (by rfl) ⟨1366034, by rfl⟩ : syracuseStep 7285517 = 2732069) B2732069
theorem B4857011 : Blo 2157435 4857011 := bstep (se 1 (by rfl) ⟨3642758, by rfl⟩ : syracuseStep 4857011 = 7285517) B7285517
theorem B3238007 : Blo 2157435 3238007 := bstep (se 1 (by rfl) ⟨2428505, by rfl⟩ : syracuseStep 3238007 = 4857011) B4857011
theorem B2158671 : Blo 2157435 2158671 := bstep (se 1 (by rfl) ⟨1619003, by rfl⟩ : syracuseStep 2158671 = 3238007) B3238007
theorem B3238013 : Blo 2157435 3238013 := bbase (se 3 (by rfl) ⟨607127, by rfl⟩ : syracuseStep 3238013 = 1214255) (by norm_num)
theorem B2158675 : Blo 2157435 2158675 := bstep (se 1 (by rfl) ⟨1619006, by rfl⟩ : syracuseStep 2158675 = 3238013) B3238013
theorem B4857029 : Blo 2157435 4857029 := bbase (se 4 (by rfl) ⟨455346, by rfl⟩ : syracuseStep 4857029 = 910693) (by norm_num)
theorem B3238019 : Blo 2157435 3238019 := bstep (se 1 (by rfl) ⟨2428514, by rfl⟩ : syracuseStep 3238019 = 4857029) B4857029
theorem B2158679 : Blo 2157435 2158679 := bstep (se 1 (by rfl) ⟨1619009, by rfl⟩ : syracuseStep 2158679 = 3238019) B3238019
theorem B5186693 : Blo 2157435 5186693 := bbase (se 4 (by rfl) ⟨486252, by rfl⟩ : syracuseStep 5186693 = 972505) (by norm_num)
theorem B13831181 : Blo 2157435 13831181 := bstep (se 3 (by rfl) ⟨2593346, by rfl⟩ : syracuseStep 13831181 = 5186693) B5186693
theorem B9220787 : Blo 2157435 9220787 := bstep (se 1 (by rfl) ⟨6915590, by rfl⟩ : syracuseStep 9220787 = 13831181) B13831181
theorem B6147191 : Blo 2157435 6147191 := bstep (se 1 (by rfl) ⟨4610393, by rfl⟩ : syracuseStep 6147191 = 9220787) B9220787
theorem B4098127 : Blo 2157435 4098127 := bstep (se 1 (by rfl) ⟨3073595, by rfl⟩ : syracuseStep 4098127 = 6147191) B6147191
theorem B5464169 : Blo 2157435 5464169 := bstep (se 2 (by rfl) ⟨2049063, by rfl⟩ : syracuseStep 5464169 = 4098127) B4098127
theorem B3642779 : Blo 2157435 3642779 := bstep (se 1 (by rfl) ⟨2732084, by rfl⟩ : syracuseStep 3642779 = 5464169) B5464169
theorem B2428519 : Blo 2157435 2428519 := bstep (se 1 (by rfl) ⟨1821389, by rfl⟩ : syracuseStep 2428519 = 3642779) B3642779
theorem B3238025 : Blo 2157435 3238025 := bstep (se 2 (by rfl) ⟨1214259, by rfl⟩ : syracuseStep 3238025 = 2428519) B2428519
theorem B2158683 : Blo 2157435 2158683 := bstep (se 1 (by rfl) ⟨1619012, by rfl⟩ : syracuseStep 2158683 = 3238025) B3238025
theorem B10928357 : Blo 2157435 10928357 := bbase (se 4 (by rfl) ⟨1024533, by rfl⟩ : syracuseStep 10928357 = 2049067) (by norm_num)
theorem B7285571 : Blo 2157435 7285571 := bstep (se 1 (by rfl) ⟨5464178, by rfl⟩ : syracuseStep 7285571 = 10928357) B10928357
theorem B4857047 : Blo 2157435 4857047 := bstep (se 1 (by rfl) ⟨3642785, by rfl⟩ : syracuseStep 4857047 = 7285571) B7285571
theorem B3238031 : Blo 2157435 3238031 := bstep (se 1 (by rfl) ⟨2428523, by rfl⟩ : syracuseStep 3238031 = 4857047) B4857047
theorem B2158687 : Blo 2157435 2158687 := bstep (se 1 (by rfl) ⟨1619015, by rfl⟩ : syracuseStep 2158687 = 3238031) B3238031
theorem B3238037 : Blo 2157435 3238037 := bbase (se 6 (by rfl) ⟨75891, by rfl⟩ : syracuseStep 3238037 = 151783) (by norm_num)
theorem B2158691 : Blo 2157435 2158691 := bstep (se 1 (by rfl) ⟨1619018, by rfl⟩ : syracuseStep 2158691 = 3238037) B3238037
theorem B9220837 : Blo 2157435 9220837 := bbase (se 4 (by rfl) ⟨864453, by rfl⟩ : syracuseStep 9220837 = 1728907) (by norm_num)
theorem B12294449 : Blo 2157435 12294449 := bstep (se 2 (by rfl) ⟨4610418, by rfl⟩ : syracuseStep 12294449 = 9220837) B9220837
theorem B8196299 : Blo 2157435 8196299 := bstep (se 1 (by rfl) ⟨6147224, by rfl⟩ : syracuseStep 8196299 = 12294449) B12294449
theorem B5464199 : Blo 2157435 5464199 := bstep (se 1 (by rfl) ⟨4098149, by rfl⟩ : syracuseStep 5464199 = 8196299) B8196299
theorem B3642799 : Blo 2157435 3642799 := bstep (se 1 (by rfl) ⟨2732099, by rfl⟩ : syracuseStep 3642799 = 5464199) B5464199
theorem B4857065 : Blo 2157435 4857065 := bstep (se 2 (by rfl) ⟨1821399, by rfl⟩ : syracuseStep 4857065 = 3642799) B3642799
theorem B3238043 : Blo 2157435 3238043 := bstep (se 1 (by rfl) ⟨2428532, by rfl⟩ : syracuseStep 3238043 = 4857065) B4857065
theorem B2158695 : Blo 2157435 2158695 := bstep (se 1 (by rfl) ⟨1619021, by rfl⟩ : syracuseStep 2158695 = 3238043) B3238043
theorem B2428537 : Blo 2157435 2428537 := bbase (se 2 (by rfl) ⟨910701, by rfl⟩ : syracuseStep 2428537 = 1821403) (by norm_num)
theorem B3238049 : Blo 2157435 3238049 := bstep (se 2 (by rfl) ⟨1214268, by rfl⟩ : syracuseStep 3238049 = 2428537) B2428537
theorem B2158699 : Blo 2157435 2158699 := bstep (se 1 (by rfl) ⟨1619024, by rfl⟩ : syracuseStep 2158699 = 3238049) B3238049
theorem B6564469 : Blo 2157435 6564469 := bbase (se 5 (by rfl) ⟨307709, by rfl⟩ : syracuseStep 6564469 = 615419) (by norm_num)
theorem B8752625 : Blo 2157435 8752625 := bstep (se 2 (by rfl) ⟨3282234, by rfl⟩ : syracuseStep 8752625 = 6564469) B6564469
theorem B5835083 : Blo 2157435 5835083 := bstep (se 1 (by rfl) ⟨4376312, by rfl⟩ : syracuseStep 5835083 = 8752625) B8752625
theorem B15560221 : Blo 2157435 15560221 := bstep (se 3 (by rfl) ⟨2917541, by rfl⟩ : syracuseStep 15560221 = 5835083) B5835083
theorem B20746961 : Blo 2157435 20746961 := bstep (se 2 (by rfl) ⟨7780110, by rfl⟩ : syracuseStep 20746961 = 15560221) B15560221
theorem B13831307 : Blo 2157435 13831307 := bstep (se 1 (by rfl) ⟨10373480, by rfl⟩ : syracuseStep 13831307 = 20746961) B20746961
theorem B9220871 : Blo 2157435 9220871 := bstep (se 1 (by rfl) ⟨6915653, by rfl⟩ : syracuseStep 9220871 = 13831307) B13831307
theorem B6147247 : Blo 2157435 6147247 := bstep (se 1 (by rfl) ⟨4610435, by rfl⟩ : syracuseStep 6147247 = 9220871) B9220871
theorem B8196329 : Blo 2157435 8196329 := bstep (se 2 (by rfl) ⟨3073623, by rfl⟩ : syracuseStep 8196329 = 6147247) B6147247
theorem B5464219 : Blo 2157435 5464219 := bstep (se 1 (by rfl) ⟨4098164, by rfl⟩ : syracuseStep 5464219 = 8196329) B8196329
theorem B7285625 : Blo 2157435 7285625 := bstep (se 2 (by rfl) ⟨2732109, by rfl⟩ : syracuseStep 7285625 = 5464219) B5464219
theorem B4857083 : Blo 2157435 4857083 := bstep (se 1 (by rfl) ⟨3642812, by rfl⟩ : syracuseStep 4857083 = 7285625) B7285625
theorem B3238055 : Blo 2157435 3238055 := bstep (se 1 (by rfl) ⟨2428541, by rfl⟩ : syracuseStep 3238055 = 4857083) B4857083
theorem B2158703 : Blo 2157435 2158703 := bstep (se 1 (by rfl) ⟨1619027, by rfl⟩ : syracuseStep 2158703 = 3238055) B3238055
theorem B3238061 : Blo 2157435 3238061 := bbase (se 3 (by rfl) ⟨607136, by rfl⟩ : syracuseStep 3238061 = 1214273) (by norm_num)
theorem B2158707 : Blo 2157435 2158707 := bstep (se 1 (by rfl) ⟨1619030, by rfl⟩ : syracuseStep 2158707 = 3238061) B3238061
theorem B4857101 : Blo 2157435 4857101 := bbase (se 3 (by rfl) ⟨910706, by rfl⟩ : syracuseStep 4857101 = 1821413) (by norm_num)
theorem B3238067 : Blo 2157435 3238067 := bstep (se 1 (by rfl) ⟨2428550, by rfl⟩ : syracuseStep 3238067 = 4857101) B4857101
theorem B2158711 : Blo 2157435 2158711 := bstep (se 1 (by rfl) ⟨1619033, by rfl⟩ : syracuseStep 2158711 = 3238067) B3238067
theorem B2732125 : Blo 2157435 2732125 := bbase (se 3 (by rfl) ⟨512273, by rfl⟩ : syracuseStep 2732125 = 1024547) (by norm_num)
theorem B3642833 : Blo 2157435 3642833 := bstep (se 2 (by rfl) ⟨1366062, by rfl⟩ : syracuseStep 3642833 = 2732125) B2732125
theorem B2428555 : Blo 2157435 2428555 := bstep (se 1 (by rfl) ⟨1821416, by rfl⟩ : syracuseStep 2428555 = 3642833) B3642833
theorem B3238073 : Blo 2157435 3238073 := bstep (se 2 (by rfl) ⟨1214277, by rfl⟩ : syracuseStep 3238073 = 2428555) B2428555
theorem B2158715 : Blo 2157435 2158715 := bstep (se 1 (by rfl) ⟨1619036, by rfl⟩ : syracuseStep 2158715 = 3238073) B3238073
theorem B18441877 : Blo 2157435 18441877 := bbase (se 6 (by rfl) ⟨432231, by rfl⟩ : syracuseStep 18441877 = 864463) (by norm_num)
theorem B24589169 : Blo 2157435 24589169 := bstep (se 2 (by rfl) ⟨9220938, by rfl⟩ : syracuseStep 24589169 = 18441877) B18441877
theorem B16392779 : Blo 2157435 16392779 := bstep (se 1 (by rfl) ⟨12294584, by rfl⟩ : syracuseStep 16392779 = 24589169) B24589169
theorem B10928519 : Blo 2157435 10928519 := bstep (se 1 (by rfl) ⟨8196389, by rfl⟩ : syracuseStep 10928519 = 16392779) B16392779
theorem B7285679 : Blo 2157435 7285679 := bstep (se 1 (by rfl) ⟨5464259, by rfl⟩ : syracuseStep 7285679 = 10928519) B10928519
theorem B4857119 : Blo 2157435 4857119 := bstep (se 1 (by rfl) ⟨3642839, by rfl⟩ : syracuseStep 4857119 = 7285679) B7285679
theorem B3238079 : Blo 2157435 3238079 := bstep (se 1 (by rfl) ⟨2428559, by rfl⟩ : syracuseStep 3238079 = 4857119) B4857119
theorem B2158719 : Blo 2157435 2158719 := bstep (se 1 (by rfl) ⟨1619039, by rfl⟩ : syracuseStep 2158719 = 3238079) B3238079
theorem B3238085 : Blo 2157435 3238085 := bbase (se 4 (by rfl) ⟨303570, by rfl⟩ : syracuseStep 3238085 = 607141) (by norm_num)
theorem B2158723 : Blo 2157435 2158723 := bstep (se 1 (by rfl) ⟨1619042, by rfl⟩ : syracuseStep 2158723 = 3238085) B3238085
theorem B3642853 : Blo 2157435 3642853 := bbase (se 4 (by rfl) ⟨341517, by rfl⟩ : syracuseStep 3642853 = 683035) (by norm_num)
theorem B4857137 : Blo 2157435 4857137 := bstep (se 2 (by rfl) ⟨1821426, by rfl⟩ : syracuseStep 4857137 = 3642853) B3642853
theorem B3238091 : Blo 2157435 3238091 := bstep (se 1 (by rfl) ⟨2428568, by rfl⟩ : syracuseStep 3238091 = 4857137) B4857137
theorem B2158727 : Blo 2157435 2158727 := bstep (se 1 (by rfl) ⟨1619045, by rfl⟩ : syracuseStep 2158727 = 3238091) B3238091
theorem B2428573 : Blo 2157435 2428573 := bbase (se 3 (by rfl) ⟨455357, by rfl⟩ : syracuseStep 2428573 = 910715) (by norm_num)
theorem B3238097 : Blo 2157435 3238097 := bstep (se 2 (by rfl) ⟨1214286, by rfl⟩ : syracuseStep 3238097 = 2428573) B2428573
theorem B2158731 : Blo 2157435 2158731 := bstep (se 1 (by rfl) ⟨1619048, by rfl⟩ : syracuseStep 2158731 = 3238097) B3238097
theorem B7285733 : Blo 2157435 7285733 := bbase (se 4 (by rfl) ⟨683037, by rfl⟩ : syracuseStep 7285733 = 1366075) (by norm_num)
theorem B4857155 : Blo 2157435 4857155 := bstep (se 1 (by rfl) ⟨3642866, by rfl⟩ : syracuseStep 4857155 = 7285733) B7285733
theorem B3238103 : Blo 2157435 3238103 := bstep (se 1 (by rfl) ⟨2428577, by rfl⟩ : syracuseStep 3238103 = 4857155) B4857155
theorem B2158735 : Blo 2157435 2158735 := bstep (se 1 (by rfl) ⟨1619051, by rfl⟩ : syracuseStep 2158735 = 3238103) B3238103
theorem B3238109 : Blo 2157435 3238109 := bbase (se 3 (by rfl) ⟨607145, by rfl⟩ : syracuseStep 3238109 = 1214291) (by norm_num)
theorem B2158739 : Blo 2157435 2158739 := bstep (se 1 (by rfl) ⟨1619054, by rfl⟩ : syracuseStep 2158739 = 3238109) B3238109
theorem B4857173 : Blo 2157435 4857173 := bbase (se 11 (by rfl) ⟨3557, by rfl⟩ : syracuseStep 4857173 = 7115) (by norm_num)
theorem B3238115 : Blo 2157435 3238115 := bstep (se 1 (by rfl) ⟨2428586, by rfl⟩ : syracuseStep 3238115 = 4857173) B4857173
theorem B2158743 : Blo 2157435 2158743 := bstep (se 1 (by rfl) ⟨1619057, by rfl⟩ : syracuseStep 2158743 = 3238115) B3238115
theorem B2305265 : Blo 2157435 2305265 := bbase (se 2 (by rfl) ⟨864474, by rfl⟩ : syracuseStep 2305265 = 1728949) (by norm_num)
theorem B6147373 : Blo 2157435 6147373 := bstep (se 3 (by rfl) ⟨1152632, by rfl⟩ : syracuseStep 6147373 = 2305265) B2305265
theorem B8196497 : Blo 2157435 8196497 := bstep (se 2 (by rfl) ⟨3073686, by rfl⟩ : syracuseStep 8196497 = 6147373) B6147373
theorem B5464331 : Blo 2157435 5464331 := bstep (se 1 (by rfl) ⟨4098248, by rfl⟩ : syracuseStep 5464331 = 8196497) B8196497
theorem B3642887 : Blo 2157435 3642887 := bstep (se 1 (by rfl) ⟨2732165, by rfl⟩ : syracuseStep 3642887 = 5464331) B5464331
theorem B2428591 : Blo 2157435 2428591 := bstep (se 1 (by rfl) ⟨1821443, by rfl⟩ : syracuseStep 2428591 = 3642887) B3642887
theorem B3238121 : Blo 2157435 3238121 := bstep (se 2 (by rfl) ⟨1214295, by rfl⟩ : syracuseStep 3238121 = 2428591) B2428591
theorem B2158747 : Blo 2157435 2158747 := bstep (se 1 (by rfl) ⟨1619060, by rfl⟩ : syracuseStep 2158747 = 3238121) B3238121
theorem B5538893 : Blo 2157435 5538893 := bbase (se 3 (by rfl) ⟨1038542, by rfl⟩ : syracuseStep 5538893 = 2077085) (by norm_num)
theorem B59081525 : Blo 2157435 59081525 := bstep (se 5 (by rfl) ⟨2769446, by rfl⟩ : syracuseStep 59081525 = 5538893) B5538893
theorem B39387683 : Blo 2157435 39387683 := bstep (se 1 (by rfl) ⟨29540762, by rfl⟩ : syracuseStep 39387683 = 59081525) B59081525
theorem B26258455 : Blo 2157435 26258455 := bstep (se 1 (by rfl) ⟨19693841, by rfl⟩ : syracuseStep 26258455 = 39387683) B39387683
theorem B35011273 : Blo 2157435 35011273 := bstep (se 2 (by rfl) ⟨13129227, by rfl⟩ : syracuseStep 35011273 = 26258455) B26258455
theorem B46681697 : Blo 2157435 46681697 := bstep (se 2 (by rfl) ⟨17505636, by rfl⟩ : syracuseStep 46681697 = 35011273) B35011273
theorem B31121131 : Blo 2157435 31121131 := bstep (se 1 (by rfl) ⟨23340848, by rfl⟩ : syracuseStep 31121131 = 46681697) B46681697
theorem B41494841 : Blo 2157435 41494841 := bstep (se 2 (by rfl) ⟨15560565, by rfl⟩ : syracuseStep 41494841 = 31121131) B31121131
theorem B27663227 : Blo 2157435 27663227 := bstep (se 1 (by rfl) ⟨20747420, by rfl⟩ : syracuseStep 27663227 = 41494841) B41494841
theorem B18442151 : Blo 2157435 18442151 := bstep (se 1 (by rfl) ⟨13831613, by rfl⟩ : syracuseStep 18442151 = 27663227) B27663227
theorem B12294767 : Blo 2157435 12294767 := bstep (se 1 (by rfl) ⟨9221075, by rfl⟩ : syracuseStep 12294767 = 18442151) B18442151
theorem B8196511 : Blo 2157435 8196511 := bstep (se 1 (by rfl) ⟨6147383, by rfl⟩ : syracuseStep 8196511 = 12294767) B12294767
theorem B10928681 : Blo 2157435 10928681 := bstep (se 2 (by rfl) ⟨4098255, by rfl⟩ : syracuseStep 10928681 = 8196511) B8196511
theorem B7285787 : Blo 2157435 7285787 := bstep (se 1 (by rfl) ⟨5464340, by rfl⟩ : syracuseStep 7285787 = 10928681) B10928681
theorem B4857191 : Blo 2157435 4857191 := bstep (se 1 (by rfl) ⟨3642893, by rfl⟩ : syracuseStep 4857191 = 7285787) B7285787
theorem B3238127 : Blo 2157435 3238127 := bstep (se 1 (by rfl) ⟨2428595, by rfl⟩ : syracuseStep 3238127 = 4857191) B4857191
theorem B2158751 : Blo 2157435 2158751 := bstep (se 1 (by rfl) ⟨1619063, by rfl⟩ : syracuseStep 2158751 = 3238127) B3238127
theorem B3238133 : Blo 2157435 3238133 := bbase (se 5 (by rfl) ⟨151787, by rfl⟩ : syracuseStep 3238133 = 303575) (by norm_num)
theorem B2158755 : Blo 2157435 2158755 := bstep (se 1 (by rfl) ⟨1619066, by rfl⟩ : syracuseStep 2158755 = 3238133) B3238133
theorem B8752853 : Blo 2157435 8752853 := bbase (se 7 (by rfl) ⟨102572, by rfl⟩ : syracuseStep 8752853 = 205145) (by norm_num)
theorem B5835235 : Blo 2157435 5835235 := bstep (se 1 (by rfl) ⟨4376426, by rfl⟩ : syracuseStep 5835235 = 8752853) B8752853
theorem B7780313 : Blo 2157435 7780313 := bstep (se 2 (by rfl) ⟨2917617, by rfl⟩ : syracuseStep 7780313 = 5835235) B5835235
theorem B20747501 : Blo 2157435 20747501 := bstep (se 3 (by rfl) ⟨3890156, by rfl⟩ : syracuseStep 20747501 = 7780313) B7780313
theorem B13831667 : Blo 2157435 13831667 := bstep (se 1 (by rfl) ⟨10373750, by rfl⟩ : syracuseStep 13831667 = 20747501) B20747501
theorem B9221111 : Blo 2157435 9221111 := bstep (se 1 (by rfl) ⟨6915833, by rfl⟩ : syracuseStep 9221111 = 13831667) B13831667
theorem B6147407 : Blo 2157435 6147407 := bstep (se 1 (by rfl) ⟨4610555, by rfl⟩ : syracuseStep 6147407 = 9221111) B9221111
theorem B4098271 : Blo 2157435 4098271 := bstep (se 1 (by rfl) ⟨3073703, by rfl⟩ : syracuseStep 4098271 = 6147407) B6147407
theorem B5464361 : Blo 2157435 5464361 := bstep (se 2 (by rfl) ⟨2049135, by rfl⟩ : syracuseStep 5464361 = 4098271) B4098271
theorem B3642907 : Blo 2157435 3642907 := bstep (se 1 (by rfl) ⟨2732180, by rfl⟩ : syracuseStep 3642907 = 5464361) B5464361
theorem B4857209 : Blo 2157435 4857209 := bstep (se 2 (by rfl) ⟨1821453, by rfl⟩ : syracuseStep 4857209 = 3642907) B3642907
theorem B3238139 : Blo 2157435 3238139 := bstep (se 1 (by rfl) ⟨2428604, by rfl⟩ : syracuseStep 3238139 = 4857209) B4857209
theorem B2158759 : Blo 2157435 2158759 := bstep (se 1 (by rfl) ⟨1619069, by rfl⟩ : syracuseStep 2158759 = 3238139) B3238139
theorem B2428609 : Blo 2157435 2428609 := bbase (se 2 (by rfl) ⟨910728, by rfl⟩ : syracuseStep 2428609 = 1821457) (by norm_num)
theorem B3238145 : Blo 2157435 3238145 := bstep (se 2 (by rfl) ⟨1214304, by rfl⟩ : syracuseStep 3238145 = 2428609) B2428609
theorem B2158763 : Blo 2157435 2158763 := bstep (se 1 (by rfl) ⟨1619072, by rfl⟩ : syracuseStep 2158763 = 3238145) B3238145
theorem B5464381 : Blo 2157435 5464381 := bbase (se 3 (by rfl) ⟨1024571, by rfl⟩ : syracuseStep 5464381 = 2049143) (by norm_num)
theorem B7285841 : Blo 2157435 7285841 := bstep (se 2 (by rfl) ⟨2732190, by rfl⟩ : syracuseStep 7285841 = 5464381) B5464381
theorem B4857227 : Blo 2157435 4857227 := bstep (se 1 (by rfl) ⟨3642920, by rfl⟩ : syracuseStep 4857227 = 7285841) B7285841
theorem B3238151 : Blo 2157435 3238151 := bstep (se 1 (by rfl) ⟨2428613, by rfl⟩ : syracuseStep 3238151 = 4857227) B4857227
theorem B2158767 : Blo 2157435 2158767 := bstep (se 1 (by rfl) ⟨1619075, by rfl⟩ : syracuseStep 2158767 = 3238151) B3238151
theorem B3238157 : Blo 2157435 3238157 := bbase (se 3 (by rfl) ⟨607154, by rfl⟩ : syracuseStep 3238157 = 1214309) (by norm_num)
theorem B2158771 : Blo 2157435 2158771 := bstep (se 1 (by rfl) ⟨1619078, by rfl⟩ : syracuseStep 2158771 = 3238157) B3238157
theorem B4857245 : Blo 2157435 4857245 := bbase (se 3 (by rfl) ⟨910733, by rfl⟩ : syracuseStep 4857245 = 1821467) (by norm_num)
theorem B3238163 : Blo 2157435 3238163 := bstep (se 1 (by rfl) ⟨2428622, by rfl⟩ : syracuseStep 3238163 = 4857245) B4857245
theorem B2158775 : Blo 2157435 2158775 := bstep (se 1 (by rfl) ⟨1619081, by rfl⟩ : syracuseStep 2158775 = 3238163) B3238163
theorem B3642941 : Blo 2157435 3642941 := bbase (se 3 (by rfl) ⟨683051, by rfl⟩ : syracuseStep 3642941 = 1366103) (by norm_num)
theorem B2428627 : Blo 2157435 2428627 := bstep (se 1 (by rfl) ⟨1821470, by rfl⟩ : syracuseStep 2428627 = 3642941) B3642941
theorem B3238169 : Blo 2157435 3238169 := bstep (se 2 (by rfl) ⟨1214313, by rfl⟩ : syracuseStep 3238169 = 2428627) B2428627
theorem B2158779 : Blo 2157435 2158779 := bstep (se 1 (by rfl) ⟨1619084, by rfl⟩ : syracuseStep 2158779 = 3238169) B3238169
theorem B5186933 : Blo 2157435 5186933 := bbase (se 5 (by rfl) ⟨243137, by rfl⟩ : syracuseStep 5186933 = 486275) (by norm_num)
theorem B3457955 : Blo 2157435 3457955 := bstep (se 1 (by rfl) ⟨2593466, by rfl⟩ : syracuseStep 3457955 = 5186933) B5186933
theorem B2305303 : Blo 2157435 2305303 := bstep (se 1 (by rfl) ⟨1728977, by rfl⟩ : syracuseStep 2305303 = 3457955) B3457955
theorem B12294949 : Blo 2157435 12294949 := bstep (se 4 (by rfl) ⟨1152651, by rfl⟩ : syracuseStep 12294949 = 2305303) B2305303
theorem B16393265 : Blo 2157435 16393265 := bstep (se 2 (by rfl) ⟨6147474, by rfl⟩ : syracuseStep 16393265 = 12294949) B12294949
theorem B10928843 : Blo 2157435 10928843 := bstep (se 1 (by rfl) ⟨8196632, by rfl⟩ : syracuseStep 10928843 = 16393265) B16393265
theorem B7285895 : Blo 2157435 7285895 := bstep (se 1 (by rfl) ⟨5464421, by rfl⟩ : syracuseStep 7285895 = 10928843) B10928843
theorem B4857263 : Blo 2157435 4857263 := bstep (se 1 (by rfl) ⟨3642947, by rfl⟩ : syracuseStep 4857263 = 7285895) B7285895
theorem B3238175 : Blo 2157435 3238175 := bstep (se 1 (by rfl) ⟨2428631, by rfl⟩ : syracuseStep 3238175 = 4857263) B4857263
theorem B2158783 : Blo 2157435 2158783 := bstep (se 1 (by rfl) ⟨1619087, by rfl⟩ : syracuseStep 2158783 = 3238175) B3238175
theorem B3238181 : Blo 2157435 3238181 := bbase (se 4 (by rfl) ⟨303579, by rfl⟩ : syracuseStep 3238181 = 607159) (by norm_num)
theorem B2158787 : Blo 2157435 2158787 := bstep (se 1 (by rfl) ⟨1619090, by rfl⟩ : syracuseStep 2158787 = 3238181) B3238181
theorem B2732221 : Blo 2157435 2732221 := bbase (se 3 (by rfl) ⟨512291, by rfl⟩ : syracuseStep 2732221 = 1024583) (by norm_num)
theorem B3642961 : Blo 2157435 3642961 := bstep (se 2 (by rfl) ⟨1366110, by rfl⟩ : syracuseStep 3642961 = 2732221) B2732221
theorem B4857281 : Blo 2157435 4857281 := bstep (se 2 (by rfl) ⟨1821480, by rfl⟩ : syracuseStep 4857281 = 3642961) B3642961
theorem B3238187 : Blo 2157435 3238187 := bstep (se 1 (by rfl) ⟨2428640, by rfl⟩ : syracuseStep 3238187 = 4857281) B4857281
theorem B2158791 : Blo 2157435 2158791 := bstep (se 1 (by rfl) ⟨1619093, by rfl⟩ : syracuseStep 2158791 = 3238187) B3238187
theorem B2428645 : Blo 2157435 2428645 := bbase (se 4 (by rfl) ⟨227685, by rfl⟩ : syracuseStep 2428645 = 455371) (by norm_num)
theorem B3238193 : Blo 2157435 3238193 := bstep (se 2 (by rfl) ⟨1214322, by rfl⟩ : syracuseStep 3238193 = 2428645) B2428645
theorem B2158795 : Blo 2157435 2158795 := bstep (se 1 (by rfl) ⟨1619096, by rfl⟩ : syracuseStep 2158795 = 3238193) B3238193
theorem B3457981 : Blo 2157435 3457981 := bbase (se 3 (by rfl) ⟨648371, by rfl⟩ : syracuseStep 3457981 = 1296743) (by norm_num)
theorem B4610641 : Blo 2157435 4610641 := bstep (se 2 (by rfl) ⟨1728990, by rfl⟩ : syracuseStep 4610641 = 3457981) B3457981
theorem B6147521 : Blo 2157435 6147521 := bstep (se 2 (by rfl) ⟨2305320, by rfl⟩ : syracuseStep 6147521 = 4610641) B4610641
theorem B4098347 : Blo 2157435 4098347 := bstep (se 1 (by rfl) ⟨3073760, by rfl⟩ : syracuseStep 4098347 = 6147521) B6147521
theorem B2732231 : Blo 2157435 2732231 := bstep (se 1 (by rfl) ⟨2049173, by rfl⟩ : syracuseStep 2732231 = 4098347) B4098347
theorem B7285949 : Blo 2157435 7285949 := bstep (se 3 (by rfl) ⟨1366115, by rfl⟩ : syracuseStep 7285949 = 2732231) B2732231
theorem B4857299 : Blo 2157435 4857299 := bstep (se 1 (by rfl) ⟨3642974, by rfl⟩ : syracuseStep 4857299 = 7285949) B7285949
theorem B3238199 : Blo 2157435 3238199 := bstep (se 1 (by rfl) ⟨2428649, by rfl⟩ : syracuseStep 3238199 = 4857299) B4857299
theorem B2158799 : Blo 2157435 2158799 := bstep (se 1 (by rfl) ⟨1619099, by rfl⟩ : syracuseStep 2158799 = 3238199) B3238199
theorem B3238205 : Blo 2157435 3238205 := bbase (se 3 (by rfl) ⟨607163, by rfl⟩ : syracuseStep 3238205 = 1214327) (by norm_num)
theorem B2158803 : Blo 2157435 2158803 := bstep (se 1 (by rfl) ⟨1619102, by rfl⟩ : syracuseStep 2158803 = 3238205) B3238205
theorem B4857317 : Blo 2157435 4857317 := bbase (se 4 (by rfl) ⟨455373, by rfl⟩ : syracuseStep 4857317 = 910747) (by norm_num)
theorem B3238211 : Blo 2157435 3238211 := bstep (se 1 (by rfl) ⟨2428658, by rfl⟩ : syracuseStep 3238211 = 4857317) B4857317
theorem B2158807 : Blo 2157435 2158807 := bstep (se 1 (by rfl) ⟨1619105, by rfl⟩ : syracuseStep 2158807 = 3238211) B3238211
theorem B5464493 : Blo 2157435 5464493 := bbase (se 3 (by rfl) ⟨1024592, by rfl⟩ : syracuseStep 5464493 = 2049185) (by norm_num)
theorem B3642995 : Blo 2157435 3642995 := bstep (se 1 (by rfl) ⟨2732246, by rfl⟩ : syracuseStep 3642995 = 5464493) B5464493
theorem B2428663 : Blo 2157435 2428663 := bstep (se 1 (by rfl) ⟨1821497, by rfl⟩ : syracuseStep 2428663 = 3642995) B3642995
theorem B3238217 : Blo 2157435 3238217 := bstep (se 2 (by rfl) ⟨1214331, by rfl⟩ : syracuseStep 3238217 = 2428663) B2428663
theorem B2158811 : Blo 2157435 2158811 := bstep (se 1 (by rfl) ⟨1619108, by rfl⟩ : syracuseStep 2158811 = 3238217) B3238217
theorem B2593505 : Blo 2157435 2593505 := bbase (se 2 (by rfl) ⟨972564, by rfl⟩ : syracuseStep 2593505 = 1945129) (by norm_num)
theorem B6916013 : Blo 2157435 6916013 := bstep (se 3 (by rfl) ⟨1296752, by rfl⟩ : syracuseStep 6916013 = 2593505) B2593505
theorem B4610675 : Blo 2157435 4610675 := bstep (se 1 (by rfl) ⟨3458006, by rfl⟩ : syracuseStep 4610675 = 6916013) B6916013
theorem B3073783 : Blo 2157435 3073783 := bstep (se 1 (by rfl) ⟨2305337, by rfl⟩ : syracuseStep 3073783 = 4610675) B4610675
theorem B4098377 : Blo 2157435 4098377 := bstep (se 2 (by rfl) ⟨1536891, by rfl⟩ : syracuseStep 4098377 = 3073783) B3073783
theorem B10929005 : Blo 2157435 10929005 := bstep (se 3 (by rfl) ⟨2049188, by rfl⟩ : syracuseStep 10929005 = 4098377) B4098377
theorem B7286003 : Blo 2157435 7286003 := bstep (se 1 (by rfl) ⟨5464502, by rfl⟩ : syracuseStep 7286003 = 10929005) B10929005
theorem B4857335 : Blo 2157435 4857335 := bstep (se 1 (by rfl) ⟨3643001, by rfl⟩ : syracuseStep 4857335 = 7286003) B7286003
theorem B3238223 : Blo 2157435 3238223 := bstep (se 1 (by rfl) ⟨2428667, by rfl⟩ : syracuseStep 3238223 = 4857335) B4857335
theorem B2158815 : Blo 2157435 2158815 := bstep (se 1 (by rfl) ⟨1619111, by rfl⟩ : syracuseStep 2158815 = 3238223) B3238223
theorem B3238229 : Blo 2157435 3238229 := bbase (se 10 (by rfl) ⟨4743, by rfl⟩ : syracuseStep 3238229 = 9487) (by norm_num)
theorem B2158819 : Blo 2157435 2158819 := bstep (se 1 (by rfl) ⟨1619114, by rfl⟩ : syracuseStep 2158819 = 3238229) B3238229
theorem B6147589 : Blo 2157435 6147589 := bbase (se 4 (by rfl) ⟨576336, by rfl⟩ : syracuseStep 6147589 = 1152673) (by norm_num)
theorem B8196785 : Blo 2157435 8196785 := bstep (se 2 (by rfl) ⟨3073794, by rfl⟩ : syracuseStep 8196785 = 6147589) B6147589
theorem B5464523 : Blo 2157435 5464523 := bstep (se 1 (by rfl) ⟨4098392, by rfl⟩ : syracuseStep 5464523 = 8196785) B8196785
theorem B3643015 : Blo 2157435 3643015 := bstep (se 1 (by rfl) ⟨2732261, by rfl⟩ : syracuseStep 3643015 = 5464523) B5464523
theorem B4857353 : Blo 2157435 4857353 := bstep (se 2 (by rfl) ⟨1821507, by rfl⟩ : syracuseStep 4857353 = 3643015) B3643015
theorem B3238235 : Blo 2157435 3238235 := bstep (se 1 (by rfl) ⟨2428676, by rfl⟩ : syracuseStep 3238235 = 4857353) B4857353
theorem B2158823 : Blo 2157435 2158823 := bstep (se 1 (by rfl) ⟨1619117, by rfl⟩ : syracuseStep 2158823 = 3238235) B3238235
theorem B2428681 : Blo 2157435 2428681 := bbase (se 2 (by rfl) ⟨910755, by rfl⟩ : syracuseStep 2428681 = 1821511) (by norm_num)
theorem B3238241 : Blo 2157435 3238241 := bstep (se 2 (by rfl) ⟨1214340, by rfl⟩ : syracuseStep 3238241 = 2428681) B2428681
theorem B2158827 : Blo 2157435 2158827 := bstep (se 1 (by rfl) ⟨1619120, by rfl⟩ : syracuseStep 2158827 = 3238241) B3238241
theorem B8213957 : Blo 2157435 8213957 := bbase (se 4 (by rfl) ⟨770058, by rfl⟩ : syracuseStep 8213957 = 1540117) (by norm_num)
theorem B5475971 : Blo 2157435 5475971 := bstep (se 1 (by rfl) ⟨4106978, by rfl⟩ : syracuseStep 5475971 = 8213957) B8213957
theorem B14602589 : Blo 2157435 14602589 := bstep (se 3 (by rfl) ⟨2737985, by rfl⟩ : syracuseStep 14602589 = 5475971) B5475971
theorem B9735059 : Blo 2157435 9735059 := bstep (se 1 (by rfl) ⟨7301294, by rfl⟩ : syracuseStep 9735059 = 14602589) B14602589
theorem B6490039 : Blo 2157435 6490039 := bstep (se 1 (by rfl) ⟨4867529, by rfl⟩ : syracuseStep 6490039 = 9735059) B9735059
theorem B8653385 : Blo 2157435 8653385 := bstep (se 2 (by rfl) ⟨3245019, by rfl⟩ : syracuseStep 8653385 = 6490039) B6490039
theorem B5768923 : Blo 2157435 5768923 := bstep (se 1 (by rfl) ⟨4326692, by rfl⟩ : syracuseStep 5768923 = 8653385) B8653385
theorem B7691897 : Blo 2157435 7691897 := bstep (se 2 (by rfl) ⟨2884461, by rfl⟩ : syracuseStep 7691897 = 5768923) B5768923
theorem B5127931 : Blo 2157435 5127931 := bstep (se 1 (by rfl) ⟨3845948, by rfl⟩ : syracuseStep 5127931 = 7691897) B7691897
theorem B6837241 : Blo 2157435 6837241 := bstep (se 2 (by rfl) ⟨2563965, by rfl⟩ : syracuseStep 6837241 = 5127931) B5127931
theorem B583444565 : Blo 2157435 583444565 := bstep (se 8 (by rfl) ⟨3418620, by rfl⟩ : syracuseStep 583444565 = 6837241) B6837241
theorem B388963043 : Blo 2157435 388963043 := bstep (se 1 (by rfl) ⟨291722282, by rfl⟩ : syracuseStep 388963043 = 583444565) B583444565
theorem B259308695 : Blo 2157435 259308695 := bstep (se 1 (by rfl) ⟨194481521, by rfl⟩ : syracuseStep 259308695 = 388963043) B388963043
theorem B172872463 : Blo 2157435 172872463 := bstep (se 1 (by rfl) ⟨129654347, by rfl⟩ : syracuseStep 172872463 = 259308695) B259308695
theorem B230496617 : Blo 2157435 230496617 := bstep (se 2 (by rfl) ⟨86436231, by rfl⟩ : syracuseStep 230496617 = 172872463) B172872463
theorem B614657645 : Blo 2157435 614657645 := bstep (se 3 (by rfl) ⟨115248308, by rfl⟩ : syracuseStep 614657645 = 230496617) B230496617
theorem B409771763 : Blo 2157435 409771763 := bstep (se 1 (by rfl) ⟨307328822, by rfl⟩ : syracuseStep 409771763 = 614657645) B614657645
theorem B273181175 : Blo 2157435 273181175 := bstep (se 1 (by rfl) ⟨204885881, by rfl⟩ : syracuseStep 273181175 = 409771763) B409771763
theorem B182120783 : Blo 2157435 182120783 := bstep (se 1 (by rfl) ⟨136590587, by rfl⟩ : syracuseStep 182120783 = 273181175) B273181175
theorem B485655421 : Blo 2157435 485655421 := bstep (se 3 (by rfl) ⟨91060391, by rfl⟩ : syracuseStep 485655421 = 182120783) B182120783
theorem B647540561 : Blo 2157435 647540561 := bstep (se 2 (by rfl) ⟨242827710, by rfl⟩ : syracuseStep 647540561 = 485655421) B485655421
theorem B431693707 : Blo 2157435 431693707 := bstep (se 1 (by rfl) ⟨323770280, by rfl⟩ : syracuseStep 431693707 = 647540561) B647540561
theorem B575591609 : Blo 2157435 575591609 := bstep (se 2 (by rfl) ⟨215846853, by rfl⟩ : syracuseStep 575591609 = 431693707) B431693707
theorem B383727739 : Blo 2157435 383727739 := bstep (se 1 (by rfl) ⟨287795804, by rfl⟩ : syracuseStep 383727739 = 575591609) B575591609
theorem B511636985 : Blo 2157435 511636985 := bstep (se 2 (by rfl) ⟨191863869, by rfl⟩ : syracuseStep 511636985 = 383727739) B383727739
theorem B341091323 : Blo 2157435 341091323 := bstep (se 1 (by rfl) ⟨255818492, by rfl⟩ : syracuseStep 341091323 = 511636985) B511636985
theorem B227394215 : Blo 2157435 227394215 := bstep (se 1 (by rfl) ⟨170545661, by rfl⟩ : syracuseStep 227394215 = 341091323) B341091323
theorem B151596143 : Blo 2157435 151596143 := bstep (se 1 (by rfl) ⟨113697107, by rfl⟩ : syracuseStep 151596143 = 227394215) B227394215
theorem B101064095 : Blo 2157435 101064095 := bstep (se 1 (by rfl) ⟨75798071, by rfl⟩ : syracuseStep 101064095 = 151596143) B151596143
theorem B67376063 : Blo 2157435 67376063 := bstep (se 1 (by rfl) ⟨50532047, by rfl⟩ : syracuseStep 67376063 = 101064095) B101064095
theorem B179669501 : Blo 2157435 179669501 := bstep (se 3 (by rfl) ⟨33688031, by rfl⟩ : syracuseStep 179669501 = 67376063) B67376063
theorem B119779667 : Blo 2157435 119779667 := bstep (se 1 (by rfl) ⟨89834750, by rfl⟩ : syracuseStep 119779667 = 179669501) B179669501
theorem B79853111 : Blo 2157435 79853111 := bstep (se 1 (by rfl) ⟨59889833, by rfl⟩ : syracuseStep 79853111 = 119779667) B119779667
theorem B53235407 : Blo 2157435 53235407 := bstep (se 1 (by rfl) ⟨39926555, by rfl⟩ : syracuseStep 53235407 = 79853111) B79853111
theorem B35490271 : Blo 2157435 35490271 := bstep (se 1 (by rfl) ⟨26617703, by rfl⟩ : syracuseStep 35490271 = 53235407) B53235407
theorem B47320361 : Blo 2157435 47320361 := bstep (se 2 (by rfl) ⟨17745135, by rfl⟩ : syracuseStep 47320361 = 35490271) B35490271
theorem B31546907 : Blo 2157435 31546907 := bstep (se 1 (by rfl) ⟨23660180, by rfl⟩ : syracuseStep 31546907 = 47320361) B47320361
theorem B21031271 : Blo 2157435 21031271 := bstep (se 1 (by rfl) ⟨15773453, by rfl⟩ : syracuseStep 21031271 = 31546907) B31546907
theorem B14020847 : Blo 2157435 14020847 := bstep (se 1 (by rfl) ⟨10515635, by rfl⟩ : syracuseStep 14020847 = 21031271) B21031271
theorem B9347231 : Blo 2157435 9347231 := bstep (se 1 (by rfl) ⟨7010423, by rfl⟩ : syracuseStep 9347231 = 14020847) B14020847
theorem B6231487 : Blo 2157435 6231487 := bstep (se 1 (by rfl) ⟨4673615, by rfl⟩ : syracuseStep 6231487 = 9347231) B9347231
theorem B8308649 : Blo 2157435 8308649 := bstep (se 2 (by rfl) ⟨3115743, by rfl⟩ : syracuseStep 8308649 = 6231487) B6231487
theorem B5539099 : Blo 2157435 5539099 := bstep (se 1 (by rfl) ⟨4154324, by rfl⟩ : syracuseStep 5539099 = 8308649) B8308649
theorem B7385465 : Blo 2157435 7385465 := bstep (se 2 (by rfl) ⟨2769549, by rfl⟩ : syracuseStep 7385465 = 5539099) B5539099
theorem B19694573 : Blo 2157435 19694573 := bstep (se 3 (by rfl) ⟨3692732, by rfl⟩ : syracuseStep 19694573 = 7385465) B7385465
theorem B13129715 : Blo 2157435 13129715 := bstep (se 1 (by rfl) ⟨9847286, by rfl⟩ : syracuseStep 13129715 = 19694573) B19694573
theorem B35012573 : Blo 2157435 35012573 := bstep (se 3 (by rfl) ⟨6564857, by rfl⟩ : syracuseStep 35012573 = 13129715) B13129715
theorem B23341715 : Blo 2157435 23341715 := bstep (se 1 (by rfl) ⟨17506286, by rfl⟩ : syracuseStep 23341715 = 35012573) B35012573
theorem B15561143 : Blo 2157435 15561143 := bstep (se 1 (by rfl) ⟨11670857, by rfl⟩ : syracuseStep 15561143 = 23341715) B23341715
theorem B10374095 : Blo 2157435 10374095 := bstep (se 1 (by rfl) ⟨7780571, by rfl⟩ : syracuseStep 10374095 = 15561143) B15561143
theorem B27664253 : Blo 2157435 27664253 := bstep (se 3 (by rfl) ⟨5187047, by rfl⟩ : syracuseStep 27664253 = 10374095) B10374095
theorem B18442835 : Blo 2157435 18442835 := bstep (se 1 (by rfl) ⟨13832126, by rfl⟩ : syracuseStep 18442835 = 27664253) B27664253
theorem B12295223 : Blo 2157435 12295223 := bstep (se 1 (by rfl) ⟨9221417, by rfl⟩ : syracuseStep 12295223 = 18442835) B18442835
theorem B8196815 : Blo 2157435 8196815 := bstep (se 1 (by rfl) ⟨6147611, by rfl⟩ : syracuseStep 8196815 = 12295223) B12295223
theorem B5464543 : Blo 2157435 5464543 := bstep (se 1 (by rfl) ⟨4098407, by rfl⟩ : syracuseStep 5464543 = 8196815) B8196815
theorem B7286057 : Blo 2157435 7286057 := bstep (se 2 (by rfl) ⟨2732271, by rfl⟩ : syracuseStep 7286057 = 5464543) B5464543
theorem B4857371 : Blo 2157435 4857371 := bstep (se 1 (by rfl) ⟨3643028, by rfl⟩ : syracuseStep 4857371 = 7286057) B7286057
theorem B3238247 : Blo 2157435 3238247 := bstep (se 1 (by rfl) ⟨2428685, by rfl⟩ : syracuseStep 3238247 = 4857371) B4857371
theorem B2158831 : Blo 2157435 2158831 := bstep (se 1 (by rfl) ⟨1619123, by rfl⟩ : syracuseStep 2158831 = 3238247) B3238247
theorem B3238253 : Blo 2157435 3238253 := bbase (se 3 (by rfl) ⟨607172, by rfl⟩ : syracuseStep 3238253 = 1214345) (by norm_num)
theorem B2158835 : Blo 2157435 2158835 := bstep (se 1 (by rfl) ⟨1619126, by rfl⟩ : syracuseStep 2158835 = 3238253) B3238253
theorem B4857389 : Blo 2157435 4857389 := bbase (se 3 (by rfl) ⟨910760, by rfl⟩ : syracuseStep 4857389 = 1821521) (by norm_num)
theorem B3238259 : Blo 2157435 3238259 := bstep (se 1 (by rfl) ⟨2428694, by rfl⟩ : syracuseStep 3238259 = 4857389) B4857389
theorem B2158839 : Blo 2157435 2158839 := bstep (se 1 (by rfl) ⟨1619129, by rfl⟩ : syracuseStep 2158839 = 3238259) B3238259
theorem B4376597 : Blo 2157435 4376597 := bbase (se 6 (by rfl) ⟨102576, by rfl⟩ : syracuseStep 4376597 = 205153) (by norm_num)
theorem B46683701 : Blo 2157435 46683701 := bstep (se 5 (by rfl) ⟨2188298, by rfl⟩ : syracuseStep 46683701 = 4376597) B4376597
theorem B31122467 : Blo 2157435 31122467 := bstep (se 1 (by rfl) ⟨23341850, by rfl⟩ : syracuseStep 31122467 = 46683701) B46683701
theorem B20748311 : Blo 2157435 20748311 := bstep (se 1 (by rfl) ⟨15561233, by rfl⟩ : syracuseStep 20748311 = 31122467) B31122467
theorem B13832207 : Blo 2157435 13832207 := bstep (se 1 (by rfl) ⟨10374155, by rfl⟩ : syracuseStep 13832207 = 20748311) B20748311
theorem B9221471 : Blo 2157435 9221471 := bstep (se 1 (by rfl) ⟨6916103, by rfl⟩ : syracuseStep 9221471 = 13832207) B13832207
theorem B6147647 : Blo 2157435 6147647 := bstep (se 1 (by rfl) ⟨4610735, by rfl⟩ : syracuseStep 6147647 = 9221471) B9221471
theorem B4098431 : Blo 2157435 4098431 := bstep (se 1 (by rfl) ⟨3073823, by rfl⟩ : syracuseStep 4098431 = 6147647) B6147647
theorem B2732287 : Blo 2157435 2732287 := bstep (se 1 (by rfl) ⟨2049215, by rfl⟩ : syracuseStep 2732287 = 4098431) B4098431
theorem B3643049 : Blo 2157435 3643049 := bstep (se 2 (by rfl) ⟨1366143, by rfl⟩ : syracuseStep 3643049 = 2732287) B2732287
theorem B2428699 : Blo 2157435 2428699 := bstep (se 1 (by rfl) ⟨1821524, by rfl⟩ : syracuseStep 2428699 = 3643049) B3643049
theorem B3238265 : Blo 2157435 3238265 := bstep (se 2 (by rfl) ⟨1214349, by rfl⟩ : syracuseStep 3238265 = 2428699) B2428699
theorem B2158843 : Blo 2157435 2158843 := bstep (se 1 (by rfl) ⟨1619132, by rfl⟩ : syracuseStep 2158843 = 3238265) B3238265
theorem B4376605 : Blo 2157435 4376605 := bbase (se 3 (by rfl) ⟨820613, by rfl⟩ : syracuseStep 4376605 = 1641227) (by norm_num)
theorem B5835473 : Blo 2157435 5835473 := bstep (se 2 (by rfl) ⟨2188302, by rfl⟩ : syracuseStep 5835473 = 4376605) B4376605
theorem B3890315 : Blo 2157435 3890315 := bstep (se 1 (by rfl) ⟨2917736, by rfl⟩ : syracuseStep 3890315 = 5835473) B5835473
theorem B2593543 : Blo 2157435 2593543 := bstep (se 1 (by rfl) ⟨1945157, by rfl⟩ : syracuseStep 2593543 = 3890315) B3890315
theorem B3458057 : Blo 2157435 3458057 := bstep (se 2 (by rfl) ⟨1296771, by rfl⟩ : syracuseStep 3458057 = 2593543) B2593543
theorem B36885941 : Blo 2157435 36885941 := bstep (se 5 (by rfl) ⟨1729028, by rfl⟩ : syracuseStep 36885941 = 3458057) B3458057
theorem B24590627 : Blo 2157435 24590627 := bstep (se 1 (by rfl) ⟨18442970, by rfl⟩ : syracuseStep 24590627 = 36885941) B36885941
theorem B16393751 : Blo 2157435 16393751 := bstep (se 1 (by rfl) ⟨12295313, by rfl⟩ : syracuseStep 16393751 = 24590627) B24590627
theorem B10929167 : Blo 2157435 10929167 := bstep (se 1 (by rfl) ⟨8196875, by rfl⟩ : syracuseStep 10929167 = 16393751) B16393751
theorem B7286111 : Blo 2157435 7286111 := bstep (se 1 (by rfl) ⟨5464583, by rfl⟩ : syracuseStep 7286111 = 10929167) B10929167
theorem B4857407 : Blo 2157435 4857407 := bstep (se 1 (by rfl) ⟨3643055, by rfl⟩ : syracuseStep 4857407 = 7286111) B7286111
theorem B3238271 : Blo 2157435 3238271 := bstep (se 1 (by rfl) ⟨2428703, by rfl⟩ : syracuseStep 3238271 = 4857407) B4857407
theorem B2158847 : Blo 2157435 2158847 := bstep (se 1 (by rfl) ⟨1619135, by rfl⟩ : syracuseStep 2158847 = 3238271) B3238271
theorem B3238277 : Blo 2157435 3238277 := bbase (se 4 (by rfl) ⟨303588, by rfl⟩ : syracuseStep 3238277 = 607177) (by norm_num)
theorem B2158851 : Blo 2157435 2158851 := bstep (se 1 (by rfl) ⟨1619138, by rfl⟩ : syracuseStep 2158851 = 3238277) B3238277
theorem B3643069 : Blo 2157435 3643069 := bbase (se 3 (by rfl) ⟨683075, by rfl⟩ : syracuseStep 3643069 = 1366151) (by norm_num)
theorem B4857425 : Blo 2157435 4857425 := bstep (se 2 (by rfl) ⟨1821534, by rfl⟩ : syracuseStep 4857425 = 3643069) B3643069
theorem B3238283 : Blo 2157435 3238283 := bstep (se 1 (by rfl) ⟨2428712, by rfl⟩ : syracuseStep 3238283 = 4857425) B4857425
theorem B2158855 : Blo 2157435 2158855 := bstep (se 1 (by rfl) ⟨1619141, by rfl⟩ : syracuseStep 2158855 = 3238283) B3238283
theorem B2428717 : Blo 2157435 2428717 := bbase (se 3 (by rfl) ⟨455384, by rfl⟩ : syracuseStep 2428717 = 910769) (by norm_num)
theorem B3238289 : Blo 2157435 3238289 := bstep (se 2 (by rfl) ⟨1214358, by rfl⟩ : syracuseStep 3238289 = 2428717) B2428717
theorem B2158859 : Blo 2157435 2158859 := bstep (se 1 (by rfl) ⟨1619144, by rfl⟩ : syracuseStep 2158859 = 3238289) B3238289
theorem B7286165 : Blo 2157435 7286165 := bbase (se 6 (by rfl) ⟨170769, by rfl⟩ : syracuseStep 7286165 = 341539) (by norm_num)
theorem B4857443 : Blo 2157435 4857443 := bstep (se 1 (by rfl) ⟨3643082, by rfl⟩ : syracuseStep 4857443 = 7286165) B7286165
theorem B3238295 : Blo 2157435 3238295 := bstep (se 1 (by rfl) ⟨2428721, by rfl⟩ : syracuseStep 3238295 = 4857443) B4857443
theorem B2158863 : Blo 2157435 2158863 := bstep (se 1 (by rfl) ⟨1619147, by rfl⟩ : syracuseStep 2158863 = 3238295) B3238295
theorem B3238301 : Blo 2157435 3238301 := bbase (se 3 (by rfl) ⟨607181, by rfl⟩ : syracuseStep 3238301 = 1214363) (by norm_num)
theorem B2158867 : Blo 2157435 2158867 := bstep (se 1 (by rfl) ⟨1619150, by rfl⟩ : syracuseStep 2158867 = 3238301) B3238301
theorem B4857461 : Blo 2157435 4857461 := bbase (se 5 (by rfl) ⟨227693, by rfl⟩ : syracuseStep 4857461 = 455387) (by norm_num)
theorem B3238307 : Blo 2157435 3238307 := bstep (se 1 (by rfl) ⟨2428730, by rfl⟩ : syracuseStep 3238307 = 4857461) B4857461
theorem B2158871 : Blo 2157435 2158871 := bstep (se 1 (by rfl) ⟨1619153, by rfl⟩ : syracuseStep 2158871 = 3238307) B3238307
theorem B2593577 : Blo 2157435 2593577 := bbase (se 2 (by rfl) ⟨972591, by rfl⟩ : syracuseStep 2593577 = 1945183) (by norm_num)
theorem B6916205 : Blo 2157435 6916205 := bstep (se 3 (by rfl) ⟨1296788, by rfl⟩ : syracuseStep 6916205 = 2593577) B2593577
theorem B18443213 : Blo 2157435 18443213 := bstep (se 3 (by rfl) ⟨3458102, by rfl⟩ : syracuseStep 18443213 = 6916205) B6916205
theorem B12295475 : Blo 2157435 12295475 := bstep (se 1 (by rfl) ⟨9221606, by rfl⟩ : syracuseStep 12295475 = 18443213) B18443213
theorem B8196983 : Blo 2157435 8196983 := bstep (se 1 (by rfl) ⟨6147737, by rfl⟩ : syracuseStep 8196983 = 12295475) B12295475
theorem B5464655 : Blo 2157435 5464655 := bstep (se 1 (by rfl) ⟨4098491, by rfl⟩ : syracuseStep 5464655 = 8196983) B8196983
theorem B3643103 : Blo 2157435 3643103 := bstep (se 1 (by rfl) ⟨2732327, by rfl⟩ : syracuseStep 3643103 = 5464655) B5464655
theorem B2428735 : Blo 2157435 2428735 := bstep (se 1 (by rfl) ⟨1821551, by rfl⟩ : syracuseStep 2428735 = 3643103) B3643103
theorem B3238313 : Blo 2157435 3238313 := bstep (se 2 (by rfl) ⟨1214367, by rfl⟩ : syracuseStep 3238313 = 2428735) B2428735
theorem B2158875 : Blo 2157435 2158875 := bstep (se 1 (by rfl) ⟨1619156, by rfl⟩ : syracuseStep 2158875 = 3238313) B3238313
theorem B8196997 : Blo 2157435 8196997 := bbase (se 4 (by rfl) ⟨768468, by rfl⟩ : syracuseStep 8196997 = 1536937) (by norm_num)
theorem B10929329 : Blo 2157435 10929329 := bstep (se 2 (by rfl) ⟨4098498, by rfl⟩ : syracuseStep 10929329 = 8196997) B8196997
theorem B7286219 : Blo 2157435 7286219 := bstep (se 1 (by rfl) ⟨5464664, by rfl⟩ : syracuseStep 7286219 = 10929329) B10929329
theorem B4857479 : Blo 2157435 4857479 := bstep (se 1 (by rfl) ⟨3643109, by rfl⟩ : syracuseStep 4857479 = 7286219) B7286219
theorem B3238319 : Blo 2157435 3238319 := bstep (se 1 (by rfl) ⟨2428739, by rfl⟩ : syracuseStep 3238319 = 4857479) B4857479
theorem B2158879 : Blo 2157435 2158879 := bstep (se 1 (by rfl) ⟨1619159, by rfl⟩ : syracuseStep 2158879 = 3238319) B3238319
theorem B3238325 : Blo 2157435 3238325 := bbase (se 5 (by rfl) ⟨151796, by rfl⟩ : syracuseStep 3238325 = 303593) (by norm_num)
theorem B2158883 : Blo 2157435 2158883 := bstep (se 1 (by rfl) ⟨1619162, by rfl⟩ : syracuseStep 2158883 = 3238325) B3238325
theorem B5464685 : Blo 2157435 5464685 := bbase (se 3 (by rfl) ⟨1024628, by rfl⟩ : syracuseStep 5464685 = 2049257) (by norm_num)
theorem B3643123 : Blo 2157435 3643123 := bstep (se 1 (by rfl) ⟨2732342, by rfl⟩ : syracuseStep 3643123 = 5464685) B5464685
theorem B4857497 : Blo 2157435 4857497 := bstep (se 2 (by rfl) ⟨1821561, by rfl⟩ : syracuseStep 4857497 = 3643123) B3643123
theorem B3238331 : Blo 2157435 3238331 := bstep (se 1 (by rfl) ⟨2428748, by rfl⟩ : syracuseStep 3238331 = 4857497) B4857497
theorem B2158887 : Blo 2157435 2158887 := bstep (se 1 (by rfl) ⟨1619165, by rfl⟩ : syracuseStep 2158887 = 3238331) B3238331
theorem B2428753 : Blo 2157435 2428753 := bbase (se 2 (by rfl) ⟨910782, by rfl⟩ : syracuseStep 2428753 = 1821565) (by norm_num)
theorem B3238337 : Blo 2157435 3238337 := bstep (se 2 (by rfl) ⟨1214376, by rfl⟩ : syracuseStep 3238337 = 2428753) B2428753
theorem B2158891 : Blo 2157435 2158891 := bstep (se 1 (by rfl) ⟨1619168, by rfl⟩ : syracuseStep 2158891 = 3238337) B3238337
theorem B7780805 : Blo 2157435 7780805 := bbase (se 4 (by rfl) ⟨729450, by rfl⟩ : syracuseStep 7780805 = 1458901) (by norm_num)
theorem B5187203 : Blo 2157435 5187203 := bstep (se 1 (by rfl) ⟨3890402, by rfl⟩ : syracuseStep 5187203 = 7780805) B7780805
theorem B3458135 : Blo 2157435 3458135 := bstep (se 1 (by rfl) ⟨2593601, by rfl⟩ : syracuseStep 3458135 = 5187203) B5187203
theorem B2305423 : Blo 2157435 2305423 := bstep (se 1 (by rfl) ⟨1729067, by rfl⟩ : syracuseStep 2305423 = 3458135) B3458135
theorem B3073897 : Blo 2157435 3073897 := bstep (se 2 (by rfl) ⟨1152711, by rfl⟩ : syracuseStep 3073897 = 2305423) B2305423
theorem B4098529 : Blo 2157435 4098529 := bstep (se 2 (by rfl) ⟨1536948, by rfl⟩ : syracuseStep 4098529 = 3073897) B3073897
theorem B5464705 : Blo 2157435 5464705 := bstep (se 2 (by rfl) ⟨2049264, by rfl⟩ : syracuseStep 5464705 = 4098529) B4098529
theorem B7286273 : Blo 2157435 7286273 := bstep (se 2 (by rfl) ⟨2732352, by rfl⟩ : syracuseStep 7286273 = 5464705) B5464705
theorem B4857515 : Blo 2157435 4857515 := bstep (se 1 (by rfl) ⟨3643136, by rfl⟩ : syracuseStep 4857515 = 7286273) B7286273
theorem B3238343 : Blo 2157435 3238343 := bstep (se 1 (by rfl) ⟨2428757, by rfl⟩ : syracuseStep 3238343 = 4857515) B4857515
theorem B2158895 : Blo 2157435 2158895 := bstep (se 1 (by rfl) ⟨1619171, by rfl⟩ : syracuseStep 2158895 = 3238343) B3238343
theorem B3238349 : Blo 2157435 3238349 := bbase (se 3 (by rfl) ⟨607190, by rfl⟩ : syracuseStep 3238349 = 1214381) (by norm_num)
theorem B2158899 : Blo 2157435 2158899 := bstep (se 1 (by rfl) ⟨1619174, by rfl⟩ : syracuseStep 2158899 = 3238349) B3238349
theorem B4857533 : Blo 2157435 4857533 := bbase (se 3 (by rfl) ⟨910787, by rfl⟩ : syracuseStep 4857533 = 1821575) (by norm_num)
theorem B3238355 : Blo 2157435 3238355 := bstep (se 1 (by rfl) ⟨2428766, by rfl⟩ : syracuseStep 3238355 = 4857533) B4857533
theorem B2158903 : Blo 2157435 2158903 := bstep (se 1 (by rfl) ⟨1619177, by rfl⟩ : syracuseStep 2158903 = 3238355) B3238355
theorem B3643157 : Blo 2157435 3643157 := bbase (se 6 (by rfl) ⟨85386, by rfl⟩ : syracuseStep 3643157 = 170773) (by norm_num)
theorem B2428771 : Blo 2157435 2428771 := bstep (se 1 (by rfl) ⟨1821578, by rfl⟩ : syracuseStep 2428771 = 3643157) B3643157
theorem B3238361 : Blo 2157435 3238361 := bstep (se 2 (by rfl) ⟨1214385, by rfl⟩ : syracuseStep 3238361 = 2428771) B2428771
theorem B2158907 : Blo 2157435 2158907 := bstep (se 1 (by rfl) ⟨1619180, by rfl⟩ : syracuseStep 2158907 = 3238361) B3238361
theorem B14603125 : Blo 2157435 14603125 := bbase (se 5 (by rfl) ⟨684521, by rfl⟩ : syracuseStep 14603125 = 1369043) (by norm_num)
theorem B19470833 : Blo 2157435 19470833 := bstep (se 2 (by rfl) ⟨7301562, by rfl⟩ : syracuseStep 19470833 = 14603125) B14603125
theorem B12980555 : Blo 2157435 12980555 := bstep (se 1 (by rfl) ⟨9735416, by rfl⟩ : syracuseStep 12980555 = 19470833) B19470833
theorem B138459253 : Blo 2157435 138459253 := bstep (se 5 (by rfl) ⟨6490277, by rfl⟩ : syracuseStep 138459253 = 12980555) B12980555
theorem B184612337 : Blo 2157435 184612337 := bstep (se 2 (by rfl) ⟨69229626, by rfl⟩ : syracuseStep 184612337 = 138459253) B138459253
theorem B123074891 : Blo 2157435 123074891 := bstep (se 1 (by rfl) ⟨92306168, by rfl⟩ : syracuseStep 123074891 = 184612337) B184612337
theorem B82049927 : Blo 2157435 82049927 := bstep (se 1 (by rfl) ⟨61537445, by rfl⟩ : syracuseStep 82049927 = 123074891) B123074891
theorem B218799805 : Blo 2157435 218799805 := bstep (se 3 (by rfl) ⟨41024963, by rfl⟩ : syracuseStep 218799805 = 82049927) B82049927
theorem B291733073 : Blo 2157435 291733073 := bstep (se 2 (by rfl) ⟨109399902, by rfl⟩ : syracuseStep 291733073 = 218799805) B218799805
theorem B194488715 : Blo 2157435 194488715 := bstep (se 1 (by rfl) ⟨145866536, by rfl⟩ : syracuseStep 194488715 = 291733073) B291733073
theorem B129659143 : Blo 2157435 129659143 := bstep (se 1 (by rfl) ⟨97244357, by rfl⟩ : syracuseStep 129659143 = 194488715) B194488715
theorem B172878857 : Blo 2157435 172878857 := bstep (se 2 (by rfl) ⟨64829571, by rfl⟩ : syracuseStep 172878857 = 129659143) B129659143
theorem B115252571 : Blo 2157435 115252571 := bstep (se 1 (by rfl) ⟨86439428, by rfl⟩ : syracuseStep 115252571 = 172878857) B172878857
theorem B307340189 : Blo 2157435 307340189 := bstep (se 3 (by rfl) ⟨57626285, by rfl⟩ : syracuseStep 307340189 = 115252571) B115252571
theorem B204893459 : Blo 2157435 204893459 := bstep (se 1 (by rfl) ⟨153670094, by rfl⟩ : syracuseStep 204893459 = 307340189) B307340189
theorem B136595639 : Blo 2157435 136595639 := bstep (se 1 (by rfl) ⟨102446729, by rfl⟩ : syracuseStep 136595639 = 204893459) B204893459
theorem B91063759 : Blo 2157435 91063759 := bstep (se 1 (by rfl) ⟨68297819, by rfl⟩ : syracuseStep 91063759 = 136595639) B136595639
theorem B121418345 : Blo 2157435 121418345 := bstep (se 2 (by rfl) ⟨45531879, by rfl⟩ : syracuseStep 121418345 = 91063759) B91063759
theorem B80945563 : Blo 2157435 80945563 := bstep (se 1 (by rfl) ⟨60709172, by rfl⟩ : syracuseStep 80945563 = 121418345) B121418345
theorem B107927417 : Blo 2157435 107927417 := bstep (se 2 (by rfl) ⟨40472781, by rfl⟩ : syracuseStep 107927417 = 80945563) B80945563
theorem B287806445 : Blo 2157435 287806445 := bstep (se 3 (by rfl) ⟨53963708, by rfl⟩ : syracuseStep 287806445 = 107927417) B107927417
theorem B191870963 : Blo 2157435 191870963 := bstep (se 1 (by rfl) ⟨143903222, by rfl⟩ : syracuseStep 191870963 = 287806445) B287806445
theorem B127913975 : Blo 2157435 127913975 := bstep (se 1 (by rfl) ⟨95935481, by rfl⟩ : syracuseStep 127913975 = 191870963) B191870963
theorem B85275983 : Blo 2157435 85275983 := bstep (se 1 (by rfl) ⟨63956987, by rfl⟩ : syracuseStep 85275983 = 127913975) B127913975
theorem B56850655 : Blo 2157435 56850655 := bstep (se 1 (by rfl) ⟨42637991, by rfl⟩ : syracuseStep 56850655 = 85275983) B85275983
theorem B75800873 : Blo 2157435 75800873 := bstep (se 2 (by rfl) ⟨28425327, by rfl⟩ : syracuseStep 75800873 = 56850655) B56850655
theorem B50533915 : Blo 2157435 50533915 := bstep (se 1 (by rfl) ⟨37900436, by rfl⟩ : syracuseStep 50533915 = 75800873) B75800873
theorem B67378553 : Blo 2157435 67378553 := bstep (se 2 (by rfl) ⟨25266957, by rfl⟩ : syracuseStep 67378553 = 50533915) B50533915
theorem B44919035 : Blo 2157435 44919035 := bstep (se 1 (by rfl) ⟨33689276, by rfl⟩ : syracuseStep 44919035 = 67378553) B67378553
theorem B29946023 : Blo 2157435 29946023 := bstep (se 1 (by rfl) ⟨22459517, by rfl⟩ : syracuseStep 29946023 = 44919035) B44919035
theorem B19964015 : Blo 2157435 19964015 := bstep (se 1 (by rfl) ⟨14973011, by rfl⟩ : syracuseStep 19964015 = 29946023) B29946023
theorem B13309343 : Blo 2157435 13309343 := bstep (se 1 (by rfl) ⟨9982007, by rfl⟩ : syracuseStep 13309343 = 19964015) B19964015
theorem B8872895 : Blo 2157435 8872895 := bstep (se 1 (by rfl) ⟨6654671, by rfl⟩ : syracuseStep 8872895 = 13309343) B13309343
theorem B5915263 : Blo 2157435 5915263 := bstep (se 1 (by rfl) ⟨4436447, by rfl⟩ : syracuseStep 5915263 = 8872895) B8872895
theorem B7887017 : Blo 2157435 7887017 := bstep (se 2 (by rfl) ⟨2957631, by rfl⟩ : syracuseStep 7887017 = 5915263) B5915263
theorem B21032045 : Blo 2157435 21032045 := bstep (se 3 (by rfl) ⟨3943508, by rfl⟩ : syracuseStep 21032045 = 7887017) B7887017
theorem B14021363 : Blo 2157435 14021363 := bstep (se 1 (by rfl) ⟨10516022, by rfl⟩ : syracuseStep 14021363 = 21032045) B21032045
theorem B37390301 : Blo 2157435 37390301 := bstep (se 3 (by rfl) ⟨7010681, by rfl⟩ : syracuseStep 37390301 = 14021363) B14021363
theorem B24926867 : Blo 2157435 24926867 := bstep (se 1 (by rfl) ⟨18695150, by rfl⟩ : syracuseStep 24926867 = 37390301) B37390301
theorem B16617911 : Blo 2157435 16617911 := bstep (se 1 (by rfl) ⟨12463433, by rfl⟩ : syracuseStep 16617911 = 24926867) B24926867
theorem B177257717 : Blo 2157435 177257717 := bstep (se 5 (by rfl) ⟨8308955, by rfl⟩ : syracuseStep 177257717 = 16617911) B16617911
theorem B118171811 : Blo 2157435 118171811 := bstep (se 1 (by rfl) ⟨88628858, by rfl⟩ : syracuseStep 118171811 = 177257717) B177257717
theorem B78781207 : Blo 2157435 78781207 := bstep (se 1 (by rfl) ⟨59085905, by rfl⟩ : syracuseStep 78781207 = 118171811) B118171811
theorem B105041609 : Blo 2157435 105041609 := bstep (se 2 (by rfl) ⟨39390603, by rfl⟩ : syracuseStep 105041609 = 78781207) B78781207
theorem B70027739 : Blo 2157435 70027739 := bstep (se 1 (by rfl) ⟨52520804, by rfl⟩ : syracuseStep 70027739 = 105041609) B105041609
theorem B46685159 : Blo 2157435 46685159 := bstep (se 1 (by rfl) ⟨35013869, by rfl⟩ : syracuseStep 46685159 = 70027739) B70027739
theorem B31123439 : Blo 2157435 31123439 := bstep (se 1 (by rfl) ⟨23342579, by rfl⟩ : syracuseStep 31123439 = 46685159) B46685159
theorem B20748959 : Blo 2157435 20748959 := bstep (se 1 (by rfl) ⟨15561719, by rfl⟩ : syracuseStep 20748959 = 31123439) B31123439
theorem B13832639 : Blo 2157435 13832639 := bstep (se 1 (by rfl) ⟨10374479, by rfl⟩ : syracuseStep 13832639 = 20748959) B20748959
theorem B9221759 : Blo 2157435 9221759 := bstep (se 1 (by rfl) ⟨6916319, by rfl⟩ : syracuseStep 9221759 = 13832639) B13832639
theorem B6147839 : Blo 2157435 6147839 := bstep (se 1 (by rfl) ⟨4610879, by rfl⟩ : syracuseStep 6147839 = 9221759) B9221759
theorem B16394237 : Blo 2157435 16394237 := bstep (se 3 (by rfl) ⟨3073919, by rfl⟩ : syracuseStep 16394237 = 6147839) B6147839
theorem B10929491 : Blo 2157435 10929491 := bstep (se 1 (by rfl) ⟨8197118, by rfl⟩ : syracuseStep 10929491 = 16394237) B16394237
theorem B7286327 : Blo 2157435 7286327 := bstep (se 1 (by rfl) ⟨5464745, by rfl⟩ : syracuseStep 7286327 = 10929491) B10929491
theorem B4857551 : Blo 2157435 4857551 := bstep (se 1 (by rfl) ⟨3643163, by rfl⟩ : syracuseStep 4857551 = 7286327) B7286327
theorem B3238367 : Blo 2157435 3238367 := bstep (se 1 (by rfl) ⟨2428775, by rfl⟩ : syracuseStep 3238367 = 4857551) B4857551
theorem B2158911 : Blo 2157435 2158911 := bstep (se 1 (by rfl) ⟨1619183, by rfl⟩ : syracuseStep 2158911 = 3238367) B3238367
theorem B3238373 : Blo 2157435 3238373 := bbase (se 4 (by rfl) ⟨303597, by rfl⟩ : syracuseStep 3238373 = 607195) (by norm_num)
theorem B2158915 : Blo 2157435 2158915 := bstep (se 1 (by rfl) ⟨1619186, by rfl⟩ : syracuseStep 2158915 = 3238373) B3238373
theorem B13832693 : Blo 2157435 13832693 := bbase (se 5 (by rfl) ⟨648407, by rfl⟩ : syracuseStep 13832693 = 1296815) (by norm_num)
theorem B9221795 : Blo 2157435 9221795 := bstep (se 1 (by rfl) ⟨6916346, by rfl⟩ : syracuseStep 9221795 = 13832693) B13832693
theorem B6147863 : Blo 2157435 6147863 := bstep (se 1 (by rfl) ⟨4610897, by rfl⟩ : syracuseStep 6147863 = 9221795) B9221795
theorem B4098575 : Blo 2157435 4098575 := bstep (se 1 (by rfl) ⟨3073931, by rfl⟩ : syracuseStep 4098575 = 6147863) B6147863
theorem B2732383 : Blo 2157435 2732383 := bstep (se 1 (by rfl) ⟨2049287, by rfl⟩ : syracuseStep 2732383 = 4098575) B4098575
theorem B3643177 : Blo 2157435 3643177 := bstep (se 2 (by rfl) ⟨1366191, by rfl⟩ : syracuseStep 3643177 = 2732383) B2732383
theorem B4857569 : Blo 2157435 4857569 := bstep (se 2 (by rfl) ⟨1821588, by rfl⟩ : syracuseStep 4857569 = 3643177) B3643177
theorem B3238379 : Blo 2157435 3238379 := bstep (se 1 (by rfl) ⟨2428784, by rfl⟩ : syracuseStep 3238379 = 4857569) B4857569
theorem B2158919 : Blo 2157435 2158919 := bstep (se 1 (by rfl) ⟨1619189, by rfl⟩ : syracuseStep 2158919 = 3238379) B3238379
theorem B2428789 : Blo 2157435 2428789 := bbase (se 5 (by rfl) ⟨113849, by rfl⟩ : syracuseStep 2428789 = 227699) (by norm_num)
theorem B3238385 : Blo 2157435 3238385 := bstep (se 2 (by rfl) ⟨1214394, by rfl⟩ : syracuseStep 3238385 = 2428789) B2428789
theorem B2158923 : Blo 2157435 2158923 := bstep (se 1 (by rfl) ⟨1619192, by rfl⟩ : syracuseStep 2158923 = 3238385) B3238385
theorem B2732393 : Blo 2157435 2732393 := bbase (se 2 (by rfl) ⟨1024647, by rfl⟩ : syracuseStep 2732393 = 2049295) (by norm_num)
theorem B7286381 : Blo 2157435 7286381 := bstep (se 3 (by rfl) ⟨1366196, by rfl⟩ : syracuseStep 7286381 = 2732393) B2732393
theorem B4857587 : Blo 2157435 4857587 := bstep (se 1 (by rfl) ⟨3643190, by rfl⟩ : syracuseStep 4857587 = 7286381) B7286381
theorem B3238391 : Blo 2157435 3238391 := bstep (se 1 (by rfl) ⟨2428793, by rfl⟩ : syracuseStep 3238391 = 4857587) B4857587
theorem B2158927 : Blo 2157435 2158927 := bstep (se 1 (by rfl) ⟨1619195, by rfl⟩ : syracuseStep 2158927 = 3238391) B3238391
theorem B3238397 : Blo 2157435 3238397 := bbase (se 3 (by rfl) ⟨607199, by rfl⟩ : syracuseStep 3238397 = 1214399) (by norm_num)
theorem B2158931 : Blo 2157435 2158931 := bstep (se 1 (by rfl) ⟨1619198, by rfl⟩ : syracuseStep 2158931 = 3238397) B3238397
theorem B4857605 : Blo 2157435 4857605 := bbase (se 4 (by rfl) ⟨455400, by rfl⟩ : syracuseStep 4857605 = 910801) (by norm_num)
theorem B3238403 : Blo 2157435 3238403 := bstep (se 1 (by rfl) ⟨2428802, by rfl⟩ : syracuseStep 3238403 = 4857605) B4857605
theorem B2158935 : Blo 2157435 2158935 := bstep (se 1 (by rfl) ⟨1619201, by rfl⟩ : syracuseStep 2158935 = 3238403) B3238403
theorem B4098613 : Blo 2157435 4098613 := bbase (se 5 (by rfl) ⟨192122, by rfl⟩ : syracuseStep 4098613 = 384245) (by norm_num)
theorem B5464817 : Blo 2157435 5464817 := bstep (se 2 (by rfl) ⟨2049306, by rfl⟩ : syracuseStep 5464817 = 4098613) B4098613
theorem B3643211 : Blo 2157435 3643211 := bstep (se 1 (by rfl) ⟨2732408, by rfl⟩ : syracuseStep 3643211 = 5464817) B5464817
theorem B2428807 : Blo 2157435 2428807 := bstep (se 1 (by rfl) ⟨1821605, by rfl⟩ : syracuseStep 2428807 = 3643211) B3643211
theorem B3238409 : Blo 2157435 3238409 := bstep (se 2 (by rfl) ⟨1214403, by rfl⟩ : syracuseStep 3238409 = 2428807) B2428807
theorem B2158939 : Blo 2157435 2158939 := bstep (se 1 (by rfl) ⟨1619204, by rfl⟩ : syracuseStep 2158939 = 3238409) B3238409
theorem B10929653 : Blo 2157435 10929653 := bbase (se 5 (by rfl) ⟨512327, by rfl⟩ : syracuseStep 10929653 = 1024655) (by norm_num)
theorem B7286435 : Blo 2157435 7286435 := bstep (se 1 (by rfl) ⟨5464826, by rfl⟩ : syracuseStep 7286435 = 10929653) B10929653
theorem B4857623 : Blo 2157435 4857623 := bstep (se 1 (by rfl) ⟨3643217, by rfl⟩ : syracuseStep 4857623 = 7286435) B7286435
theorem B3238415 : Blo 2157435 3238415 := bstep (se 1 (by rfl) ⟨2428811, by rfl⟩ : syracuseStep 3238415 = 4857623) B4857623
theorem B2158943 : Blo 2157435 2158943 := bstep (se 1 (by rfl) ⟨1619207, by rfl⟩ : syracuseStep 2158943 = 3238415) B3238415
theorem B3238421 : Blo 2157435 3238421 := bbase (se 6 (by rfl) ⟨75900, by rfl⟩ : syracuseStep 3238421 = 151801) (by norm_num)
theorem B2158947 : Blo 2157435 2158947 := bstep (se 1 (by rfl) ⟨1619210, by rfl⟩ : syracuseStep 2158947 = 3238421) B3238421
theorem B18443861 : Blo 2157435 18443861 := bbase (se 8 (by rfl) ⟨108069, by rfl⟩ : syracuseStep 18443861 = 216139) (by norm_num)
theorem B12295907 : Blo 2157435 12295907 := bstep (se 1 (by rfl) ⟨9221930, by rfl⟩ : syracuseStep 12295907 = 18443861) B18443861
theorem B8197271 : Blo 2157435 8197271 := bstep (se 1 (by rfl) ⟨6147953, by rfl⟩ : syracuseStep 8197271 = 12295907) B12295907
theorem B5464847 : Blo 2157435 5464847 := bstep (se 1 (by rfl) ⟨4098635, by rfl⟩ : syracuseStep 5464847 = 8197271) B8197271
theorem B3643231 : Blo 2157435 3643231 := bstep (se 1 (by rfl) ⟨2732423, by rfl⟩ : syracuseStep 3643231 = 5464847) B5464847
theorem B4857641 : Blo 2157435 4857641 := bstep (se 2 (by rfl) ⟨1821615, by rfl⟩ : syracuseStep 4857641 = 3643231) B3643231
theorem B3238427 : Blo 2157435 3238427 := bstep (se 1 (by rfl) ⟨2428820, by rfl⟩ : syracuseStep 3238427 = 4857641) B4857641
theorem B2158951 : Blo 2157435 2158951 := bstep (se 1 (by rfl) ⟨1619213, by rfl⟩ : syracuseStep 2158951 = 3238427) B3238427
theorem B2428825 : Blo 2157435 2428825 := bbase (se 2 (by rfl) ⟨910809, by rfl⟩ : syracuseStep 2428825 = 1821619) (by norm_num)
theorem B3238433 : Blo 2157435 3238433 := bstep (se 2 (by rfl) ⟨1214412, by rfl⟩ : syracuseStep 3238433 = 2428825) B2428825
theorem B2158955 : Blo 2157435 2158955 := bstep (se 1 (by rfl) ⟨1619216, by rfl⟩ : syracuseStep 2158955 = 3238433) B3238433
theorem B8197301 : Blo 2157435 8197301 := bbase (se 5 (by rfl) ⟨384248, by rfl⟩ : syracuseStep 8197301 = 768497) (by norm_num)
theorem B5464867 : Blo 2157435 5464867 := bstep (se 1 (by rfl) ⟨4098650, by rfl⟩ : syracuseStep 5464867 = 8197301) B8197301
theorem B7286489 : Blo 2157435 7286489 := bstep (se 2 (by rfl) ⟨2732433, by rfl⟩ : syracuseStep 7286489 = 5464867) B5464867
theorem B4857659 : Blo 2157435 4857659 := bstep (se 1 (by rfl) ⟨3643244, by rfl⟩ : syracuseStep 4857659 = 7286489) B7286489
theorem B3238439 : Blo 2157435 3238439 := bstep (se 1 (by rfl) ⟨2428829, by rfl⟩ : syracuseStep 3238439 = 4857659) B4857659
theorem B2158959 : Blo 2157435 2158959 := bstep (se 1 (by rfl) ⟨1619219, by rfl⟩ : syracuseStep 2158959 = 3238439) B3238439
theorem B3238445 : Blo 2157435 3238445 := bbase (se 3 (by rfl) ⟨607208, by rfl⟩ : syracuseStep 3238445 = 1214417) (by norm_num)
theorem B2158963 : Blo 2157435 2158963 := bstep (se 1 (by rfl) ⟨1619222, by rfl⟩ : syracuseStep 2158963 = 3238445) B3238445
theorem B4857677 : Blo 2157435 4857677 := bbase (se 3 (by rfl) ⟨910814, by rfl⟩ : syracuseStep 4857677 = 1821629) (by norm_num)
theorem B3238451 : Blo 2157435 3238451 := bstep (se 1 (by rfl) ⟨2428838, by rfl⟩ : syracuseStep 3238451 = 4857677) B4857677
theorem B2158967 : Blo 2157435 2158967 := bstep (se 1 (by rfl) ⟨1619225, by rfl⟩ : syracuseStep 2158967 = 3238451) B3238451
theorem B2732449 : Blo 2157435 2732449 := bbase (se 2 (by rfl) ⟨1024668, by rfl⟩ : syracuseStep 2732449 = 2049337) (by norm_num)
theorem B3643265 : Blo 2157435 3643265 := bstep (se 2 (by rfl) ⟨1366224, by rfl⟩ : syracuseStep 3643265 = 2732449) B2732449
theorem B2428843 : Blo 2157435 2428843 := bstep (se 1 (by rfl) ⟨1821632, by rfl⟩ : syracuseStep 2428843 = 3643265) B3643265
theorem B3238457 : Blo 2157435 3238457 := bstep (se 2 (by rfl) ⟨1214421, by rfl⟩ : syracuseStep 3238457 = 2428843) B2428843
theorem B2158971 : Blo 2157435 2158971 := bstep (se 1 (by rfl) ⟨1619228, by rfl⟩ : syracuseStep 2158971 = 3238457) B3238457
theorem B24592085 : Blo 2157435 24592085 := bbase (se 7 (by rfl) ⟨288188, by rfl⟩ : syracuseStep 24592085 = 576377) (by norm_num)
theorem B16394723 : Blo 2157435 16394723 := bstep (se 1 (by rfl) ⟨12296042, by rfl⟩ : syracuseStep 16394723 = 24592085) B24592085
theorem B10929815 : Blo 2157435 10929815 := bstep (se 1 (by rfl) ⟨8197361, by rfl⟩ : syracuseStep 10929815 = 16394723) B16394723
theorem B7286543 : Blo 2157435 7286543 := bstep (se 1 (by rfl) ⟨5464907, by rfl⟩ : syracuseStep 7286543 = 10929815) B10929815
theorem B4857695 : Blo 2157435 4857695 := bstep (se 1 (by rfl) ⟨3643271, by rfl⟩ : syracuseStep 4857695 = 7286543) B7286543
theorem B3238463 : Blo 2157435 3238463 := bstep (se 1 (by rfl) ⟨2428847, by rfl⟩ : syracuseStep 3238463 = 4857695) B4857695
theorem B2158975 : Blo 2157435 2158975 := bstep (se 1 (by rfl) ⟨1619231, by rfl⟩ : syracuseStep 2158975 = 3238463) B3238463
theorem B3238469 : Blo 2157435 3238469 := bbase (se 4 (by rfl) ⟨303606, by rfl⟩ : syracuseStep 3238469 = 607213) (by norm_num)
theorem B2158979 : Blo 2157435 2158979 := bstep (se 1 (by rfl) ⟨1619234, by rfl⟩ : syracuseStep 2158979 = 3238469) B3238469
theorem B3643285 : Blo 2157435 3643285 := bbase (se 6 (by rfl) ⟨85389, by rfl⟩ : syracuseStep 3643285 = 170779) (by norm_num)
theorem B4857713 : Blo 2157435 4857713 := bstep (se 2 (by rfl) ⟨1821642, by rfl⟩ : syracuseStep 4857713 = 3643285) B3643285
theorem B3238475 : Blo 2157435 3238475 := bstep (se 1 (by rfl) ⟨2428856, by rfl⟩ : syracuseStep 3238475 = 4857713) B4857713
theorem B2158983 : Blo 2157435 2158983 := bstep (se 1 (by rfl) ⟨1619237, by rfl⟩ : syracuseStep 2158983 = 3238475) B3238475
theorem B2428861 : Blo 2157435 2428861 := bbase (se 3 (by rfl) ⟨455411, by rfl⟩ : syracuseStep 2428861 = 910823) (by norm_num)
theorem B3238481 : Blo 2157435 3238481 := bstep (se 2 (by rfl) ⟨1214430, by rfl⟩ : syracuseStep 3238481 = 2428861) B2428861
theorem B2158987 : Blo 2157435 2158987 := bstep (se 1 (by rfl) ⟨1619240, by rfl⟩ : syracuseStep 2158987 = 3238481) B3238481
theorem B7286597 : Blo 2157435 7286597 := bbase (se 4 (by rfl) ⟨683118, by rfl⟩ : syracuseStep 7286597 = 1366237) (by norm_num)
theorem B4857731 : Blo 2157435 4857731 := bstep (se 1 (by rfl) ⟨3643298, by rfl⟩ : syracuseStep 4857731 = 7286597) B7286597
theorem B3238487 : Blo 2157435 3238487 := bstep (se 1 (by rfl) ⟨2428865, by rfl⟩ : syracuseStep 3238487 = 4857731) B4857731
theorem B2158991 : Blo 2157435 2158991 := bstep (se 1 (by rfl) ⟨1619243, by rfl⟩ : syracuseStep 2158991 = 3238487) B3238487
theorem B3238493 : Blo 2157435 3238493 := bbase (se 3 (by rfl) ⟨607217, by rfl⟩ : syracuseStep 3238493 = 1214435) (by norm_num)
theorem B2158995 : Blo 2157435 2158995 := bstep (se 1 (by rfl) ⟨1619246, by rfl⟩ : syracuseStep 2158995 = 3238493) B3238493
theorem B4857749 : Blo 2157435 4857749 := bbase (se 6 (by rfl) ⟨113853, by rfl⟩ : syracuseStep 4857749 = 227707) (by norm_num)
theorem B3238499 : Blo 2157435 3238499 := bstep (se 1 (by rfl) ⟨2428874, by rfl⟩ : syracuseStep 3238499 = 4857749) B4857749
theorem B2158999 : Blo 2157435 2158999 := bstep (se 1 (by rfl) ⟨1619249, by rfl⟩ : syracuseStep 2158999 = 3238499) B3238499
theorem B4611077 : Blo 2157435 4611077 := bbase (se 4 (by rfl) ⟨432288, by rfl⟩ : syracuseStep 4611077 = 864577) (by norm_num)
theorem B3074051 : Blo 2157435 3074051 := bstep (se 1 (by rfl) ⟨2305538, by rfl⟩ : syracuseStep 3074051 = 4611077) B4611077
theorem B8197469 : Blo 2157435 8197469 := bstep (se 3 (by rfl) ⟨1537025, by rfl⟩ : syracuseStep 8197469 = 3074051) B3074051
theorem B5464979 : Blo 2157435 5464979 := bstep (se 1 (by rfl) ⟨4098734, by rfl⟩ : syracuseStep 5464979 = 8197469) B8197469
theorem B3643319 : Blo 2157435 3643319 := bstep (se 1 (by rfl) ⟨2732489, by rfl⟩ : syracuseStep 3643319 = 5464979) B5464979
theorem B2428879 : Blo 2157435 2428879 := bstep (se 1 (by rfl) ⟨1821659, by rfl⟩ : syracuseStep 2428879 = 3643319) B3643319
theorem B3238505 : Blo 2157435 3238505 := bstep (se 2 (by rfl) ⟨1214439, by rfl⟩ : syracuseStep 3238505 = 2428879) B2428879
theorem B2159003 : Blo 2157435 2159003 := bstep (se 1 (by rfl) ⟨1619252, by rfl⟩ : syracuseStep 2159003 = 3238505) B3238505
theorem B17988725 : Blo 2157435 17988725 := bbase (se 5 (by rfl) ⟨843221, by rfl⟩ : syracuseStep 17988725 = 1686443) (by norm_num)
theorem B11992483 : Blo 2157435 11992483 := bstep (se 1 (by rfl) ⟨8994362, by rfl⟩ : syracuseStep 11992483 = 17988725) B17988725
theorem B15989977 : Blo 2157435 15989977 := bstep (se 2 (by rfl) ⟨5996241, by rfl⟩ : syracuseStep 15989977 = 11992483) B11992483
theorem B21319969 : Blo 2157435 21319969 := bstep (se 2 (by rfl) ⟨7994988, by rfl⟩ : syracuseStep 21319969 = 15989977) B15989977
theorem B28426625 : Blo 2157435 28426625 := bstep (se 2 (by rfl) ⟨10659984, by rfl⟩ : syracuseStep 28426625 = 21319969) B21319969
theorem B18951083 : Blo 2157435 18951083 := bstep (se 1 (by rfl) ⟨14213312, by rfl⟩ : syracuseStep 18951083 = 28426625) B28426625
theorem B12634055 : Blo 2157435 12634055 := bstep (se 1 (by rfl) ⟨9475541, by rfl⟩ : syracuseStep 12634055 = 18951083) B18951083
theorem B8422703 : Blo 2157435 8422703 := bstep (se 1 (by rfl) ⟨6317027, by rfl⟩ : syracuseStep 8422703 = 12634055) B12634055
theorem B5615135 : Blo 2157435 5615135 := bstep (se 1 (by rfl) ⟨4211351, by rfl⟩ : syracuseStep 5615135 = 8422703) B8422703
theorem B3743423 : Blo 2157435 3743423 := bstep (se 1 (by rfl) ⟨2807567, by rfl⟩ : syracuseStep 3743423 = 5615135) B5615135
theorem B2495615 : Blo 2157435 2495615 := bstep (se 1 (by rfl) ⟨1871711, by rfl⟩ : syracuseStep 2495615 = 3743423) B3743423
theorem B6654973 : Blo 2157435 6654973 := bstep (se 3 (by rfl) ⟨1247807, by rfl⟩ : syracuseStep 6654973 = 2495615) B2495615
theorem B8873297 : Blo 2157435 8873297 := bstep (se 2 (by rfl) ⟨3327486, by rfl⟩ : syracuseStep 8873297 = 6654973) B6654973
theorem B5915531 : Blo 2157435 5915531 := bstep (se 1 (by rfl) ⟨4436648, by rfl⟩ : syracuseStep 5915531 = 8873297) B8873297
theorem B15774749 : Blo 2157435 15774749 := bstep (se 3 (by rfl) ⟨2957765, by rfl⟩ : syracuseStep 15774749 = 5915531) B5915531
theorem B10516499 : Blo 2157435 10516499 := bstep (se 1 (by rfl) ⟨7887374, by rfl⟩ : syracuseStep 10516499 = 15774749) B15774749
theorem B7010999 : Blo 2157435 7010999 := bstep (se 1 (by rfl) ⟨5258249, by rfl⟩ : syracuseStep 7010999 = 10516499) B10516499
theorem B4673999 : Blo 2157435 4673999 := bstep (se 1 (by rfl) ⟨3505499, by rfl⟩ : syracuseStep 4673999 = 7010999) B7010999
theorem B3115999 : Blo 2157435 3115999 := bstep (se 1 (by rfl) ⟨2336999, by rfl⟩ : syracuseStep 3115999 = 4673999) B4673999
theorem B4154665 : Blo 2157435 4154665 := bstep (se 2 (by rfl) ⟨1557999, by rfl⟩ : syracuseStep 4154665 = 3115999) B3115999
theorem B5539553 : Blo 2157435 5539553 := bstep (se 2 (by rfl) ⟨2077332, by rfl⟩ : syracuseStep 5539553 = 4154665) B4154665
theorem B3693035 : Blo 2157435 3693035 := bstep (se 1 (by rfl) ⟨2769776, by rfl⟩ : syracuseStep 3693035 = 5539553) B5539553
theorem B2462023 : Blo 2157435 2462023 := bstep (se 1 (by rfl) ⟨1846517, by rfl⟩ : syracuseStep 2462023 = 3693035) B3693035
theorem B3282697 : Blo 2157435 3282697 := bstep (se 2 (by rfl) ⟨1231011, by rfl⟩ : syracuseStep 3282697 = 2462023) B2462023
theorem B4376929 : Blo 2157435 4376929 := bstep (se 2 (by rfl) ⟨1641348, by rfl⟩ : syracuseStep 4376929 = 3282697) B3282697
theorem B5835905 : Blo 2157435 5835905 := bstep (se 2 (by rfl) ⟨2188464, by rfl⟩ : syracuseStep 5835905 = 4376929) B4376929
theorem B3890603 : Blo 2157435 3890603 := bstep (se 1 (by rfl) ⟨2917952, by rfl⟩ : syracuseStep 3890603 = 5835905) B5835905
theorem B10374941 : Blo 2157435 10374941 := bstep (se 3 (by rfl) ⟨1945301, by rfl⟩ : syracuseStep 10374941 = 3890603) B3890603
theorem B6916627 : Blo 2157435 6916627 := bstep (se 1 (by rfl) ⟨5187470, by rfl⟩ : syracuseStep 6916627 = 10374941) B10374941
theorem B9222169 : Blo 2157435 9222169 := bstep (se 2 (by rfl) ⟨3458313, by rfl⟩ : syracuseStep 9222169 = 6916627) B6916627
theorem B12296225 : Blo 2157435 12296225 := bstep (se 2 (by rfl) ⟨4611084, by rfl⟩ : syracuseStep 12296225 = 9222169) B9222169
theorem B8197483 : Blo 2157435 8197483 := bstep (se 1 (by rfl) ⟨6148112, by rfl⟩ : syracuseStep 8197483 = 12296225) B12296225
theorem B10929977 : Blo 2157435 10929977 := bstep (se 2 (by rfl) ⟨4098741, by rfl⟩ : syracuseStep 10929977 = 8197483) B8197483
theorem B7286651 : Blo 2157435 7286651 := bstep (se 1 (by rfl) ⟨5464988, by rfl⟩ : syracuseStep 7286651 = 10929977) B10929977
theorem B4857767 : Blo 2157435 4857767 := bstep (se 1 (by rfl) ⟨3643325, by rfl⟩ : syracuseStep 4857767 = 7286651) B7286651
theorem B3238511 : Blo 2157435 3238511 := bstep (se 1 (by rfl) ⟨2428883, by rfl⟩ : syracuseStep 3238511 = 4857767) B4857767
theorem B2159007 : Blo 2157435 2159007 := bstep (se 1 (by rfl) ⟨1619255, by rfl⟩ : syracuseStep 2159007 = 3238511) B3238511
theorem B3238517 : Blo 2157435 3238517 := bbase (se 5 (by rfl) ⟨151805, by rfl⟩ : syracuseStep 3238517 = 303611) (by norm_num)
theorem B2159011 : Blo 2157435 2159011 := bstep (se 1 (by rfl) ⟨1619258, by rfl⟩ : syracuseStep 2159011 = 3238517) B3238517
theorem B4098757 : Blo 2157435 4098757 := bbase (se 4 (by rfl) ⟨384258, by rfl⟩ : syracuseStep 4098757 = 768517) (by norm_num)
theorem B5465009 : Blo 2157435 5465009 := bstep (se 2 (by rfl) ⟨2049378, by rfl⟩ : syracuseStep 5465009 = 4098757) B4098757
theorem B3643339 : Blo 2157435 3643339 := bstep (se 1 (by rfl) ⟨2732504, by rfl⟩ : syracuseStep 3643339 = 5465009) B5465009
theorem B4857785 : Blo 2157435 4857785 := bstep (se 2 (by rfl) ⟨1821669, by rfl⟩ : syracuseStep 4857785 = 3643339) B3643339
theorem B3238523 : Blo 2157435 3238523 := bstep (se 1 (by rfl) ⟨2428892, by rfl⟩ : syracuseStep 3238523 = 4857785) B4857785
theorem B2159015 : Blo 2157435 2159015 := bstep (se 1 (by rfl) ⟨1619261, by rfl⟩ : syracuseStep 2159015 = 3238523) B3238523
theorem B2428897 : Blo 2157435 2428897 := bbase (se 2 (by rfl) ⟨910836, by rfl⟩ : syracuseStep 2428897 = 1821673) (by norm_num)
theorem B3238529 : Blo 2157435 3238529 := bstep (se 2 (by rfl) ⟨1214448, by rfl⟩ : syracuseStep 3238529 = 2428897) B2428897
theorem B2159019 : Blo 2157435 2159019 := bstep (se 1 (by rfl) ⟨1619264, by rfl⟩ : syracuseStep 2159019 = 3238529) B3238529
theorem B5465029 : Blo 2157435 5465029 := bbase (se 4 (by rfl) ⟨512346, by rfl⟩ : syracuseStep 5465029 = 1024693) (by norm_num)
theorem B7286705 : Blo 2157435 7286705 := bstep (se 2 (by rfl) ⟨2732514, by rfl⟩ : syracuseStep 7286705 = 5465029) B5465029
theorem B4857803 : Blo 2157435 4857803 := bstep (se 1 (by rfl) ⟨3643352, by rfl⟩ : syracuseStep 4857803 = 7286705) B7286705
theorem B3238535 : Blo 2157435 3238535 := bstep (se 1 (by rfl) ⟨2428901, by rfl⟩ : syracuseStep 3238535 = 4857803) B4857803
theorem B2159023 : Blo 2157435 2159023 := bstep (se 1 (by rfl) ⟨1619267, by rfl⟩ : syracuseStep 2159023 = 3238535) B3238535
theorem B3238541 : Blo 2157435 3238541 := bbase (se 3 (by rfl) ⟨607226, by rfl⟩ : syracuseStep 3238541 = 1214453) (by norm_num)
theorem B2159027 : Blo 2157435 2159027 := bstep (se 1 (by rfl) ⟨1619270, by rfl⟩ : syracuseStep 2159027 = 3238541) B3238541
theorem B4857821 : Blo 2157435 4857821 := bbase (se 3 (by rfl) ⟨910841, by rfl⟩ : syracuseStep 4857821 = 1821683) (by norm_num)
theorem B3238547 : Blo 2157435 3238547 := bstep (se 1 (by rfl) ⟨2428910, by rfl⟩ : syracuseStep 3238547 = 4857821) B4857821
theorem B2159031 : Blo 2157435 2159031 := bstep (se 1 (by rfl) ⟨1619273, by rfl⟩ : syracuseStep 2159031 = 3238547) B3238547
theorem B3643373 : Blo 2157435 3643373 := bbase (se 3 (by rfl) ⟨683132, by rfl⟩ : syracuseStep 3643373 = 1366265) (by norm_num)
theorem B2428915 : Blo 2157435 2428915 := bstep (se 1 (by rfl) ⟨1821686, by rfl⟩ : syracuseStep 2428915 = 3643373) B3643373
theorem B3238553 : Blo 2157435 3238553 := bstep (se 2 (by rfl) ⟨1214457, by rfl⟩ : syracuseStep 3238553 = 2428915) B2428915
theorem B2159035 : Blo 2157435 2159035 := bstep (se 1 (by rfl) ⟨1619276, by rfl⟩ : syracuseStep 2159035 = 3238553) B3238553
theorem B2769817 : Blo 2157435 2769817 := bbase (se 2 (by rfl) ⟨1038681, by rfl⟩ : syracuseStep 2769817 = 2077363) (by norm_num)
theorem B3693089 : Blo 2157435 3693089 := bstep (se 2 (by rfl) ⟨1384908, by rfl⟩ : syracuseStep 3693089 = 2769817) B2769817
theorem B2462059 : Blo 2157435 2462059 := bstep (se 1 (by rfl) ⟨1846544, by rfl⟩ : syracuseStep 2462059 = 3693089) B3693089
theorem B13130981 : Blo 2157435 13130981 := bstep (se 4 (by rfl) ⟨1231029, by rfl⟩ : syracuseStep 13130981 = 2462059) B2462059
theorem B8753987 : Blo 2157435 8753987 := bstep (se 1 (by rfl) ⟨6565490, by rfl⟩ : syracuseStep 8753987 = 13130981) B13130981
theorem B5835991 : Blo 2157435 5835991 := bstep (se 1 (by rfl) ⟨4376993, by rfl⟩ : syracuseStep 5835991 = 8753987) B8753987
theorem B7781321 : Blo 2157435 7781321 := bstep (se 2 (by rfl) ⟨2917995, by rfl⟩ : syracuseStep 7781321 = 5835991) B5835991
theorem B5187547 : Blo 2157435 5187547 := bstep (se 1 (by rfl) ⟨3890660, by rfl⟩ : syracuseStep 5187547 = 7781321) B7781321
theorem B27666917 : Blo 2157435 27666917 := bstep (se 4 (by rfl) ⟨2593773, by rfl⟩ : syracuseStep 27666917 = 5187547) B5187547
theorem B18444611 : Blo 2157435 18444611 := bstep (se 1 (by rfl) ⟨13833458, by rfl⟩ : syracuseStep 18444611 = 27666917) B27666917
theorem B12296407 : Blo 2157435 12296407 := bstep (se 1 (by rfl) ⟨9222305, by rfl⟩ : syracuseStep 12296407 = 18444611) B18444611
theorem B16395209 : Blo 2157435 16395209 := bstep (se 2 (by rfl) ⟨6148203, by rfl⟩ : syracuseStep 16395209 = 12296407) B12296407
theorem B10930139 : Blo 2157435 10930139 := bstep (se 1 (by rfl) ⟨8197604, by rfl⟩ : syracuseStep 10930139 = 16395209) B16395209
theorem B7286759 : Blo 2157435 7286759 := bstep (se 1 (by rfl) ⟨5465069, by rfl⟩ : syracuseStep 7286759 = 10930139) B10930139
theorem B4857839 : Blo 2157435 4857839 := bstep (se 1 (by rfl) ⟨3643379, by rfl⟩ : syracuseStep 4857839 = 7286759) B7286759
theorem B3238559 : Blo 2157435 3238559 := bstep (se 1 (by rfl) ⟨2428919, by rfl⟩ : syracuseStep 3238559 = 4857839) B4857839
theorem B2159039 : Blo 2157435 2159039 := bstep (se 1 (by rfl) ⟨1619279, by rfl⟩ : syracuseStep 2159039 = 3238559) B3238559
theorem B3238565 : Blo 2157435 3238565 := bbase (se 4 (by rfl) ⟨303615, by rfl⟩ : syracuseStep 3238565 = 607231) (by norm_num)
theorem B2159043 : Blo 2157435 2159043 := bstep (se 1 (by rfl) ⟨1619282, by rfl⟩ : syracuseStep 2159043 = 3238565) B3238565
theorem B2732545 : Blo 2157435 2732545 := bbase (se 2 (by rfl) ⟨1024704, by rfl⟩ : syracuseStep 2732545 = 2049409) (by norm_num)
theorem B3643393 : Blo 2157435 3643393 := bstep (se 2 (by rfl) ⟨1366272, by rfl⟩ : syracuseStep 3643393 = 2732545) B2732545
theorem B4857857 : Blo 2157435 4857857 := bstep (se 2 (by rfl) ⟨1821696, by rfl⟩ : syracuseStep 4857857 = 3643393) B3643393
theorem B3238571 : Blo 2157435 3238571 := bstep (se 1 (by rfl) ⟨2428928, by rfl⟩ : syracuseStep 3238571 = 4857857) B4857857
theorem B2159047 : Blo 2157435 2159047 := bstep (se 1 (by rfl) ⟨1619285, by rfl⟩ : syracuseStep 2159047 = 3238571) B3238571
theorem B2428933 : Blo 2157435 2428933 := bbase (se 4 (by rfl) ⟨227712, by rfl⟩ : syracuseStep 2428933 = 455425) (by norm_num)
theorem B3238577 : Blo 2157435 3238577 := bstep (se 2 (by rfl) ⟨1214466, by rfl⟩ : syracuseStep 3238577 = 2428933) B2428933
theorem B2159051 : Blo 2157435 2159051 := bstep (se 1 (by rfl) ⟨1619288, by rfl⟩ : syracuseStep 2159051 = 3238577) B3238577
theorem B3074125 : Blo 2157435 3074125 := bbase (se 3 (by rfl) ⟨576398, by rfl⟩ : syracuseStep 3074125 = 1152797) (by norm_num)
theorem B4098833 : Blo 2157435 4098833 := bstep (se 2 (by rfl) ⟨1537062, by rfl⟩ : syracuseStep 4098833 = 3074125) B3074125
theorem B2732555 : Blo 2157435 2732555 := bstep (se 1 (by rfl) ⟨2049416, by rfl⟩ : syracuseStep 2732555 = 4098833) B4098833
theorem B7286813 : Blo 2157435 7286813 := bstep (se 3 (by rfl) ⟨1366277, by rfl⟩ : syracuseStep 7286813 = 2732555) B2732555
theorem B4857875 : Blo 2157435 4857875 := bstep (se 1 (by rfl) ⟨3643406, by rfl⟩ : syracuseStep 4857875 = 7286813) B7286813
theorem B3238583 : Blo 2157435 3238583 := bstep (se 1 (by rfl) ⟨2428937, by rfl⟩ : syracuseStep 3238583 = 4857875) B4857875
theorem B2159055 : Blo 2157435 2159055 := bstep (se 1 (by rfl) ⟨1619291, by rfl⟩ : syracuseStep 2159055 = 3238583) B3238583
theorem B3238589 : Blo 2157435 3238589 := bbase (se 3 (by rfl) ⟨607235, by rfl⟩ : syracuseStep 3238589 = 1214471) (by norm_num)
theorem B2159059 : Blo 2157435 2159059 := bstep (se 1 (by rfl) ⟨1619294, by rfl⟩ : syracuseStep 2159059 = 3238589) B3238589
theorem B4857893 : Blo 2157435 4857893 := bbase (se 4 (by rfl) ⟨455427, by rfl⟩ : syracuseStep 4857893 = 910855) (by norm_num)
theorem B3238595 : Blo 2157435 3238595 := bstep (se 1 (by rfl) ⟨2428946, by rfl⟩ : syracuseStep 3238595 = 4857893) B4857893
theorem B2159063 : Blo 2157435 2159063 := bstep (se 1 (by rfl) ⟨1619297, by rfl⟩ : syracuseStep 2159063 = 3238595) B3238595
theorem B5465141 : Blo 2157435 5465141 := bbase (se 5 (by rfl) ⟨256178, by rfl⟩ : syracuseStep 5465141 = 512357) (by norm_num)
theorem B3643427 : Blo 2157435 3643427 := bstep (se 1 (by rfl) ⟨2732570, by rfl⟩ : syracuseStep 3643427 = 5465141) B5465141
theorem B2428951 : Blo 2157435 2428951 := bstep (se 1 (by rfl) ⟨1821713, by rfl⟩ : syracuseStep 2428951 = 3643427) B3643427
theorem B3238601 : Blo 2157435 3238601 := bstep (se 2 (by rfl) ⟨1214475, by rfl⟩ : syracuseStep 3238601 = 2428951) B2428951
theorem B2159067 : Blo 2157435 2159067 := bstep (se 1 (by rfl) ⟨1619300, by rfl⟩ : syracuseStep 2159067 = 3238601) B3238601
theorem B6565589 : Blo 2157435 6565589 := bbase (se 7 (by rfl) ⟨76940, by rfl⟩ : syracuseStep 6565589 = 153881) (by norm_num)
theorem B4377059 : Blo 2157435 4377059 := bstep (se 1 (by rfl) ⟨3282794, by rfl⟩ : syracuseStep 4377059 = 6565589) B6565589
theorem B2918039 : Blo 2157435 2918039 := bstep (se 1 (by rfl) ⟨2188529, by rfl⟩ : syracuseStep 2918039 = 4377059) B4377059
theorem B7781437 : Blo 2157435 7781437 := bstep (se 3 (by rfl) ⟨1459019, by rfl⟩ : syracuseStep 7781437 = 2918039) B2918039
theorem B10375249 : Blo 2157435 10375249 := bstep (se 2 (by rfl) ⟨3890718, by rfl⟩ : syracuseStep 10375249 = 7781437) B7781437
theorem B13833665 : Blo 2157435 13833665 := bstep (se 2 (by rfl) ⟨5187624, by rfl⟩ : syracuseStep 13833665 = 10375249) B10375249
theorem B9222443 : Blo 2157435 9222443 := bstep (se 1 (by rfl) ⟨6916832, by rfl⟩ : syracuseStep 9222443 = 13833665) B13833665
theorem B6148295 : Blo 2157435 6148295 := bstep (se 1 (by rfl) ⟨4611221, by rfl⟩ : syracuseStep 6148295 = 9222443) B9222443
theorem B4098863 : Blo 2157435 4098863 := bstep (se 1 (by rfl) ⟨3074147, by rfl⟩ : syracuseStep 4098863 = 6148295) B6148295
theorem B10930301 : Blo 2157435 10930301 := bstep (se 3 (by rfl) ⟨2049431, by rfl⟩ : syracuseStep 10930301 = 4098863) B4098863
theorem B7286867 : Blo 2157435 7286867 := bstep (se 1 (by rfl) ⟨5465150, by rfl⟩ : syracuseStep 7286867 = 10930301) B10930301
theorem B4857911 : Blo 2157435 4857911 := bstep (se 1 (by rfl) ⟨3643433, by rfl⟩ : syracuseStep 4857911 = 7286867) B7286867
theorem B3238607 : Blo 2157435 3238607 := bstep (se 1 (by rfl) ⟨2428955, by rfl⟩ : syracuseStep 3238607 = 4857911) B4857911
theorem B2159071 : Blo 2157435 2159071 := bstep (se 1 (by rfl) ⟨1619303, by rfl⟩ : syracuseStep 2159071 = 3238607) B3238607
theorem B3238613 : Blo 2157435 3238613 := bbase (se 7 (by rfl) ⟨37952, by rfl⟩ : syracuseStep 3238613 = 75905) (by norm_num)
theorem B2159075 : Blo 2157435 2159075 := bstep (se 1 (by rfl) ⟨1619306, by rfl⟩ : syracuseStep 2159075 = 3238613) B3238613
theorem B33238421 : Blo 2157435 33238421 := bbase (se 6 (by rfl) ⟨779025, by rfl⟩ : syracuseStep 33238421 = 1558051) (by norm_num)
theorem B22158947 : Blo 2157435 22158947 := bstep (se 1 (by rfl) ⟨16619210, by rfl⟩ : syracuseStep 22158947 = 33238421) B33238421
theorem B14772631 : Blo 2157435 14772631 := bstep (se 1 (by rfl) ⟨11079473, by rfl⟩ : syracuseStep 14772631 = 22158947) B22158947
theorem B19696841 : Blo 2157435 19696841 := bstep (se 2 (by rfl) ⟨7386315, by rfl⟩ : syracuseStep 19696841 = 14772631) B14772631
theorem B13131227 : Blo 2157435 13131227 := bstep (se 1 (by rfl) ⟨9848420, by rfl⟩ : syracuseStep 13131227 = 19696841) B19696841
theorem B8754151 : Blo 2157435 8754151 := bstep (se 1 (by rfl) ⟨6565613, by rfl⟩ : syracuseStep 8754151 = 13131227) B13131227
theorem B11672201 : Blo 2157435 11672201 := bstep (se 2 (by rfl) ⟨4377075, by rfl⟩ : syracuseStep 11672201 = 8754151) B8754151
theorem B7781467 : Blo 2157435 7781467 := bstep (se 1 (by rfl) ⟨5836100, by rfl⟩ : syracuseStep 7781467 = 11672201) B11672201
theorem B10375289 : Blo 2157435 10375289 := bstep (se 2 (by rfl) ⟨3890733, by rfl⟩ : syracuseStep 10375289 = 7781467) B7781467
theorem B6916859 : Blo 2157435 6916859 := bstep (se 1 (by rfl) ⟨5187644, by rfl⟩ : syracuseStep 6916859 = 10375289) B10375289
theorem B4611239 : Blo 2157435 4611239 := bstep (se 1 (by rfl) ⟨3458429, by rfl⟩ : syracuseStep 4611239 = 6916859) B6916859
theorem B3074159 : Blo 2157435 3074159 := bstep (se 1 (by rfl) ⟨2305619, by rfl⟩ : syracuseStep 3074159 = 4611239) B4611239
theorem B8197757 : Blo 2157435 8197757 := bstep (se 3 (by rfl) ⟨1537079, by rfl⟩ : syracuseStep 8197757 = 3074159) B3074159
theorem B5465171 : Blo 2157435 5465171 := bstep (se 1 (by rfl) ⟨4098878, by rfl⟩ : syracuseStep 5465171 = 8197757) B8197757
theorem B3643447 : Blo 2157435 3643447 := bstep (se 1 (by rfl) ⟨2732585, by rfl⟩ : syracuseStep 3643447 = 5465171) B5465171
theorem B4857929 : Blo 2157435 4857929 := bstep (se 2 (by rfl) ⟨1821723, by rfl⟩ : syracuseStep 4857929 = 3643447) B3643447
theorem B3238619 : Blo 2157435 3238619 := bstep (se 1 (by rfl) ⟨2428964, by rfl⟩ : syracuseStep 3238619 = 4857929) B4857929
theorem B2159079 : Blo 2157435 2159079 := bstep (se 1 (by rfl) ⟨1619309, by rfl⟩ : syracuseStep 2159079 = 3238619) B3238619
theorem B2428969 : Blo 2157435 2428969 := bbase (se 2 (by rfl) ⟨910863, by rfl⟩ : syracuseStep 2428969 = 1821727) (by norm_num)
theorem B3238625 : Blo 2157435 3238625 := bstep (se 2 (by rfl) ⟨1214484, by rfl⟩ : syracuseStep 3238625 = 2428969) B2428969
theorem B2159083 : Blo 2157435 2159083 := bstep (se 1 (by rfl) ⟨1619312, by rfl⟩ : syracuseStep 2159083 = 3238625) B3238625
theorem B35016725 : Blo 2157435 35016725 := bbase (se 6 (by rfl) ⟨820704, by rfl⟩ : syracuseStep 35016725 = 1641409) (by norm_num)
theorem B23344483 : Blo 2157435 23344483 := bstep (se 1 (by rfl) ⟨17508362, by rfl⟩ : syracuseStep 23344483 = 35016725) B35016725
theorem B31125977 : Blo 2157435 31125977 := bstep (se 2 (by rfl) ⟨11672241, by rfl⟩ : syracuseStep 31125977 = 23344483) B23344483
theorem B20750651 : Blo 2157435 20750651 := bstep (se 1 (by rfl) ⟨15562988, by rfl⟩ : syracuseStep 20750651 = 31125977) B31125977
theorem B13833767 : Blo 2157435 13833767 := bstep (se 1 (by rfl) ⟨10375325, by rfl⟩ : syracuseStep 13833767 = 20750651) B20750651
theorem B9222511 : Blo 2157435 9222511 := bstep (se 1 (by rfl) ⟨6916883, by rfl⟩ : syracuseStep 9222511 = 13833767) B13833767
theorem B12296681 : Blo 2157435 12296681 := bstep (se 2 (by rfl) ⟨4611255, by rfl⟩ : syracuseStep 12296681 = 9222511) B9222511
theorem B8197787 : Blo 2157435 8197787 := bstep (se 1 (by rfl) ⟨6148340, by rfl⟩ : syracuseStep 8197787 = 12296681) B12296681
theorem B5465191 : Blo 2157435 5465191 := bstep (se 1 (by rfl) ⟨4098893, by rfl⟩ : syracuseStep 5465191 = 8197787) B8197787
theorem B7286921 : Blo 2157435 7286921 := bstep (se 2 (by rfl) ⟨2732595, by rfl⟩ : syracuseStep 7286921 = 5465191) B5465191
theorem B4857947 : Blo 2157435 4857947 := bstep (se 1 (by rfl) ⟨3643460, by rfl⟩ : syracuseStep 4857947 = 7286921) B7286921
theorem B3238631 : Blo 2157435 3238631 := bstep (se 1 (by rfl) ⟨2428973, by rfl⟩ : syracuseStep 3238631 = 4857947) B4857947
theorem B2159087 : Blo 2157435 2159087 := bstep (se 1 (by rfl) ⟨1619315, by rfl⟩ : syracuseStep 2159087 = 3238631) B3238631
theorem B3238637 : Blo 2157435 3238637 := bbase (se 3 (by rfl) ⟨607244, by rfl⟩ : syracuseStep 3238637 = 1214489) (by norm_num)
theorem B2159091 : Blo 2157435 2159091 := bstep (se 1 (by rfl) ⟨1619318, by rfl⟩ : syracuseStep 2159091 = 3238637) B3238637
theorem B4857965 : Blo 2157435 4857965 := bbase (se 3 (by rfl) ⟨910868, by rfl⟩ : syracuseStep 4857965 = 1821737) (by norm_num)
theorem B3238643 : Blo 2157435 3238643 := bstep (se 1 (by rfl) ⟨2428982, by rfl⟩ : syracuseStep 3238643 = 4857965) B4857965
theorem B2159095 : Blo 2157435 2159095 := bstep (se 1 (by rfl) ⟨1619321, by rfl⟩ : syracuseStep 2159095 = 3238643) B3238643
theorem B4098917 : Blo 2157435 4098917 := bbase (se 4 (by rfl) ⟨384273, by rfl⟩ : syracuseStep 4098917 = 768547) (by norm_num)
theorem B2732611 : Blo 2157435 2732611 := bstep (se 1 (by rfl) ⟨2049458, by rfl⟩ : syracuseStep 2732611 = 4098917) B4098917
theorem B3643481 : Blo 2157435 3643481 := bstep (se 2 (by rfl) ⟨1366305, by rfl⟩ : syracuseStep 3643481 = 2732611) B2732611
theorem B2428987 : Blo 2157435 2428987 := bstep (se 1 (by rfl) ⟨1821740, by rfl⟩ : syracuseStep 2428987 = 3643481) B3643481
theorem B3238649 : Blo 2157435 3238649 := bstep (se 2 (by rfl) ⟨1214493, by rfl⟩ : syracuseStep 3238649 = 2428987) B2428987
theorem B2159099 : Blo 2157435 2159099 := bstep (se 1 (by rfl) ⟨1619324, by rfl⟩ : syracuseStep 2159099 = 3238649) B3238649
theorem B3245429 : Blo 2157435 3245429 := bbase (se 5 (by rfl) ⟨152129, by rfl⟩ : syracuseStep 3245429 = 304259) (by norm_num)
theorem B2163619 : Blo 2157435 2163619 := bstep (se 1 (by rfl) ⟨1622714, by rfl⟩ : syracuseStep 2163619 = 3245429) B3245429
theorem B2884825 : Blo 2157435 2884825 := bstep (se 2 (by rfl) ⟨1081809, by rfl⟩ : syracuseStep 2884825 = 2163619) B2163619
theorem B3846433 : Blo 2157435 3846433 := bstep (se 2 (by rfl) ⟨1442412, by rfl⟩ : syracuseStep 3846433 = 2884825) B2884825
theorem B5128577 : Blo 2157435 5128577 := bstep (se 2 (by rfl) ⟨1923216, by rfl⟩ : syracuseStep 5128577 = 3846433) B3846433
theorem B54704821 : Blo 2157435 54704821 := bstep (se 5 (by rfl) ⟨2564288, by rfl⟩ : syracuseStep 54704821 = 5128577) B5128577
theorem B72939761 : Blo 2157435 72939761 := bstep (se 2 (by rfl) ⟨27352410, by rfl⟩ : syracuseStep 72939761 = 54704821) B54704821
theorem B48626507 : Blo 2157435 48626507 := bstep (se 1 (by rfl) ⟨36469880, by rfl⟩ : syracuseStep 48626507 = 72939761) B72939761
theorem B32417671 : Blo 2157435 32417671 := bstep (se 1 (by rfl) ⟨24313253, by rfl⟩ : syracuseStep 32417671 = 48626507) B48626507
theorem B43223561 : Blo 2157435 43223561 := bstep (se 2 (by rfl) ⟨16208835, by rfl⟩ : syracuseStep 43223561 = 32417671) B32417671
theorem B28815707 : Blo 2157435 28815707 := bstep (se 1 (by rfl) ⟨21611780, by rfl⟩ : syracuseStep 28815707 = 43223561) B43223561
theorem B76841885 : Blo 2157435 76841885 := bstep (se 3 (by rfl) ⟨14407853, by rfl⟩ : syracuseStep 76841885 = 28815707) B28815707
theorem B51227923 : Blo 2157435 51227923 := bstep (se 1 (by rfl) ⟨38420942, by rfl⟩ : syracuseStep 51227923 = 76841885) B76841885
theorem B68303897 : Blo 2157435 68303897 := bstep (se 2 (by rfl) ⟨25613961, by rfl⟩ : syracuseStep 68303897 = 51227923) B51227923
theorem B45535931 : Blo 2157435 45535931 := bstep (se 1 (by rfl) ⟨34151948, by rfl⟩ : syracuseStep 45535931 = 68303897) B68303897
theorem B30357287 : Blo 2157435 30357287 := bstep (se 1 (by rfl) ⟨22767965, by rfl⟩ : syracuseStep 30357287 = 45535931) B45535931
theorem B20238191 : Blo 2157435 20238191 := bstep (se 1 (by rfl) ⟨15178643, by rfl⟩ : syracuseStep 20238191 = 30357287) B30357287
theorem B13492127 : Blo 2157435 13492127 := bstep (se 1 (by rfl) ⟨10119095, by rfl⟩ : syracuseStep 13492127 = 20238191) B20238191
theorem B35979005 : Blo 2157435 35979005 := bstep (se 3 (by rfl) ⟨6746063, by rfl⟩ : syracuseStep 35979005 = 13492127) B13492127
theorem B23986003 : Blo 2157435 23986003 := bstep (se 1 (by rfl) ⟨17989502, by rfl⟩ : syracuseStep 23986003 = 35979005) B35979005
theorem B31981337 : Blo 2157435 31981337 := bstep (se 2 (by rfl) ⟨11993001, by rfl⟩ : syracuseStep 31981337 = 23986003) B23986003
theorem B21320891 : Blo 2157435 21320891 := bstep (se 1 (by rfl) ⟨15990668, by rfl⟩ : syracuseStep 21320891 = 31981337) B31981337
theorem B14213927 : Blo 2157435 14213927 := bstep (se 1 (by rfl) ⟨10660445, by rfl⟩ : syracuseStep 14213927 = 21320891) B21320891
theorem B37903805 : Blo 2157435 37903805 := bstep (se 3 (by rfl) ⟨7106963, by rfl⟩ : syracuseStep 37903805 = 14213927) B14213927
theorem B25269203 : Blo 2157435 25269203 := bstep (se 1 (by rfl) ⟨18951902, by rfl⟩ : syracuseStep 25269203 = 37903805) B37903805
theorem B67384541 : Blo 2157435 67384541 := bstep (se 3 (by rfl) ⟨12634601, by rfl⟩ : syracuseStep 67384541 = 25269203) B25269203
theorem B44923027 : Blo 2157435 44923027 := bstep (se 1 (by rfl) ⟨33692270, by rfl⟩ : syracuseStep 44923027 = 67384541) B67384541
theorem B59897369 : Blo 2157435 59897369 := bstep (se 2 (by rfl) ⟨22461513, by rfl⟩ : syracuseStep 59897369 = 44923027) B44923027
theorem B39931579 : Blo 2157435 39931579 := bstep (se 1 (by rfl) ⟨29948684, by rfl⟩ : syracuseStep 39931579 = 59897369) B59897369
theorem B53242105 : Blo 2157435 53242105 := bstep (se 2 (by rfl) ⟨19965789, by rfl⟩ : syracuseStep 53242105 = 39931579) B39931579
theorem B70989473 : Blo 2157435 70989473 := bstep (se 2 (by rfl) ⟨26621052, by rfl⟩ : syracuseStep 70989473 = 53242105) B53242105
theorem B47326315 : Blo 2157435 47326315 := bstep (se 1 (by rfl) ⟨35494736, by rfl⟩ : syracuseStep 47326315 = 70989473) B70989473
theorem B63101753 : Blo 2157435 63101753 := bstep (se 2 (by rfl) ⟨23663157, by rfl⟩ : syracuseStep 63101753 = 47326315) B47326315
theorem B42067835 : Blo 2157435 42067835 := bstep (se 1 (by rfl) ⟨31550876, by rfl⟩ : syracuseStep 42067835 = 63101753) B63101753
theorem B28045223 : Blo 2157435 28045223 := bstep (se 1 (by rfl) ⟨21033917, by rfl⟩ : syracuseStep 28045223 = 42067835) B42067835
theorem B18696815 : Blo 2157435 18696815 := bstep (se 1 (by rfl) ⟨14022611, by rfl⟩ : syracuseStep 18696815 = 28045223) B28045223
theorem B12464543 : Blo 2157435 12464543 := bstep (se 1 (by rfl) ⟨9348407, by rfl⟩ : syracuseStep 12464543 = 18696815) B18696815
theorem B8309695 : Blo 2157435 8309695 := bstep (se 1 (by rfl) ⟨6232271, by rfl⟩ : syracuseStep 8309695 = 12464543) B12464543
theorem B11079593 : Blo 2157435 11079593 := bstep (se 2 (by rfl) ⟨4154847, by rfl⟩ : syracuseStep 11079593 = 8309695) B8309695
theorem B7386395 : Blo 2157435 7386395 := bstep (se 1 (by rfl) ⟨5539796, by rfl⟩ : syracuseStep 7386395 = 11079593) B11079593
theorem B19697053 : Blo 2157435 19697053 := bstep (se 3 (by rfl) ⟨3693197, by rfl⟩ : syracuseStep 19697053 = 7386395) B7386395
theorem B26262737 : Blo 2157435 26262737 := bstep (se 2 (by rfl) ⟨9848526, by rfl⟩ : syracuseStep 26262737 = 19697053) B19697053
theorem B17508491 : Blo 2157435 17508491 := bstep (se 1 (by rfl) ⟨13131368, by rfl⟩ : syracuseStep 17508491 = 26262737) B26262737
theorem B11672327 : Blo 2157435 11672327 := bstep (se 1 (by rfl) ⟨8754245, by rfl⟩ : syracuseStep 11672327 = 17508491) B17508491
theorem B7781551 : Blo 2157435 7781551 := bstep (se 1 (by rfl) ⟨5836163, by rfl⟩ : syracuseStep 7781551 = 11672327) B11672327
theorem B41501605 : Blo 2157435 41501605 := bstep (se 4 (by rfl) ⟨3890775, by rfl⟩ : syracuseStep 41501605 = 7781551) B7781551
theorem B55335473 : Blo 2157435 55335473 := bstep (se 2 (by rfl) ⟨20750802, by rfl⟩ : syracuseStep 55335473 = 41501605) B41501605
theorem B36890315 : Blo 2157435 36890315 := bstep (se 1 (by rfl) ⟨27667736, by rfl⟩ : syracuseStep 36890315 = 55335473) B55335473
theorem B24593543 : Blo 2157435 24593543 := bstep (se 1 (by rfl) ⟨18445157, by rfl⟩ : syracuseStep 24593543 = 36890315) B36890315
theorem B16395695 : Blo 2157435 16395695 := bstep (se 1 (by rfl) ⟨12296771, by rfl⟩ : syracuseStep 16395695 = 24593543) B24593543
theorem B10930463 : Blo 2157435 10930463 := bstep (se 1 (by rfl) ⟨8197847, by rfl⟩ : syracuseStep 10930463 = 16395695) B16395695
theorem B7286975 : Blo 2157435 7286975 := bstep (se 1 (by rfl) ⟨5465231, by rfl⟩ : syracuseStep 7286975 = 10930463) B10930463
theorem B4857983 : Blo 2157435 4857983 := bstep (se 1 (by rfl) ⟨3643487, by rfl⟩ : syracuseStep 4857983 = 7286975) B7286975
theorem B3238655 : Blo 2157435 3238655 := bstep (se 1 (by rfl) ⟨2428991, by rfl⟩ : syracuseStep 3238655 = 4857983) B4857983
theorem B2159103 : Blo 2157435 2159103 := bstep (se 1 (by rfl) ⟨1619327, by rfl⟩ : syracuseStep 2159103 = 3238655) B3238655
theorem B3238661 : Blo 2157435 3238661 := bbase (se 4 (by rfl) ⟨303624, by rfl⟩ : syracuseStep 3238661 = 607249) (by norm_num)
theorem B2159107 : Blo 2157435 2159107 := bstep (se 1 (by rfl) ⟨1619330, by rfl⟩ : syracuseStep 2159107 = 3238661) B3238661
theorem B3643501 : Blo 2157435 3643501 := bbase (se 3 (by rfl) ⟨683156, by rfl⟩ : syracuseStep 3643501 = 1366313) (by norm_num)
theorem B4858001 : Blo 2157435 4858001 := bstep (se 2 (by rfl) ⟨1821750, by rfl⟩ : syracuseStep 4858001 = 3643501) B3643501
theorem B3238667 : Blo 2157435 3238667 := bstep (se 1 (by rfl) ⟨2429000, by rfl⟩ : syracuseStep 3238667 = 4858001) B4858001
theorem B2159111 : Blo 2157435 2159111 := bstep (se 1 (by rfl) ⟨1619333, by rfl⟩ : syracuseStep 2159111 = 3238667) B3238667
theorem B2429005 : Blo 2157435 2429005 := bbase (se 3 (by rfl) ⟨455438, by rfl⟩ : syracuseStep 2429005 = 910877) (by norm_num)
theorem B3238673 : Blo 2157435 3238673 := bstep (se 2 (by rfl) ⟨1214502, by rfl⟩ : syracuseStep 3238673 = 2429005) B2429005
theorem B2159115 : Blo 2157435 2159115 := bstep (se 1 (by rfl) ⟨1619336, by rfl⟩ : syracuseStep 2159115 = 3238673) B3238673
theorem B7287029 : Blo 2157435 7287029 := bbase (se 5 (by rfl) ⟨341579, by rfl⟩ : syracuseStep 7287029 = 683159) (by norm_num)
theorem B4858019 : Blo 2157435 4858019 := bstep (se 1 (by rfl) ⟨3643514, by rfl⟩ : syracuseStep 4858019 = 7287029) B7287029
theorem B3238679 : Blo 2157435 3238679 := bstep (se 1 (by rfl) ⟨2429009, by rfl⟩ : syracuseStep 3238679 = 4858019) B4858019
theorem B2159119 : Blo 2157435 2159119 := bstep (se 1 (by rfl) ⟨1619339, by rfl⟩ : syracuseStep 2159119 = 3238679) B3238679
theorem B3238685 : Blo 2157435 3238685 := bbase (se 3 (by rfl) ⟨607253, by rfl⟩ : syracuseStep 3238685 = 1214507) (by norm_num)
theorem B2159123 : Blo 2157435 2159123 := bstep (se 1 (by rfl) ⟨1619342, by rfl⟩ : syracuseStep 2159123 = 3238685) B3238685
theorem B4858037 : Blo 2157435 4858037 := bbase (se 5 (by rfl) ⟨227720, by rfl⟩ : syracuseStep 4858037 = 455441) (by norm_num)
theorem B3238691 : Blo 2157435 3238691 := bstep (se 1 (by rfl) ⟨2429018, by rfl⟩ : syracuseStep 3238691 = 4858037) B4858037
theorem B2159127 : Blo 2157435 2159127 := bstep (se 1 (by rfl) ⟨1619345, by rfl⟩ : syracuseStep 2159127 = 3238691) B3238691
theorem B2593885 : Blo 2157435 2593885 := bbase (se 3 (by rfl) ⟨486353, by rfl⟩ : syracuseStep 2593885 = 972707) (by norm_num)
theorem B3458513 : Blo 2157435 3458513 := bstep (se 2 (by rfl) ⟨1296942, by rfl⟩ : syracuseStep 3458513 = 2593885) B2593885
theorem B2305675 : Blo 2157435 2305675 := bstep (se 1 (by rfl) ⟨1729256, by rfl⟩ : syracuseStep 2305675 = 3458513) B3458513
theorem B12296933 : Blo 2157435 12296933 := bstep (se 4 (by rfl) ⟨1152837, by rfl⟩ : syracuseStep 12296933 = 2305675) B2305675
theorem B8197955 : Blo 2157435 8197955 := bstep (se 1 (by rfl) ⟨6148466, by rfl⟩ : syracuseStep 8197955 = 12296933) B12296933
theorem B5465303 : Blo 2157435 5465303 := bstep (se 1 (by rfl) ⟨4098977, by rfl⟩ : syracuseStep 5465303 = 8197955) B8197955
theorem B3643535 : Blo 2157435 3643535 := bstep (se 1 (by rfl) ⟨2732651, by rfl⟩ : syracuseStep 3643535 = 5465303) B5465303
theorem B2429023 : Blo 2157435 2429023 := bstep (se 1 (by rfl) ⟨1821767, by rfl⟩ : syracuseStep 2429023 = 3643535) B3643535
theorem B3238697 : Blo 2157435 3238697 := bstep (se 2 (by rfl) ⟨1214511, by rfl⟩ : syracuseStep 3238697 = 2429023) B2429023
theorem B2159131 : Blo 2157435 2159131 := bstep (se 1 (by rfl) ⟨1619348, by rfl⟩ : syracuseStep 2159131 = 3238697) B3238697
theorem B7781669 : Blo 2157435 7781669 := bbase (se 4 (by rfl) ⟨729531, by rfl⟩ : syracuseStep 7781669 = 1459063) (by norm_num)
theorem B5187779 : Blo 2157435 5187779 := bstep (se 1 (by rfl) ⟨3890834, by rfl⟩ : syracuseStep 5187779 = 7781669) B7781669
theorem B3458519 : Blo 2157435 3458519 := bstep (se 1 (by rfl) ⟨2593889, by rfl⟩ : syracuseStep 3458519 = 5187779) B5187779
theorem B2305679 : Blo 2157435 2305679 := bstep (se 1 (by rfl) ⟨1729259, by rfl⟩ : syracuseStep 2305679 = 3458519) B3458519
theorem B6148477 : Blo 2157435 6148477 := bstep (se 3 (by rfl) ⟨1152839, by rfl⟩ : syracuseStep 6148477 = 2305679) B2305679
theorem B8197969 : Blo 2157435 8197969 := bstep (se 2 (by rfl) ⟨3074238, by rfl⟩ : syracuseStep 8197969 = 6148477) B6148477
theorem B10930625 : Blo 2157435 10930625 := bstep (se 2 (by rfl) ⟨4098984, by rfl⟩ : syracuseStep 10930625 = 8197969) B8197969
theorem B7287083 : Blo 2157435 7287083 := bstep (se 1 (by rfl) ⟨5465312, by rfl⟩ : syracuseStep 7287083 = 10930625) B10930625
theorem B4858055 : Blo 2157435 4858055 := bstep (se 1 (by rfl) ⟨3643541, by rfl⟩ : syracuseStep 4858055 = 7287083) B7287083
theorem B3238703 : Blo 2157435 3238703 := bstep (se 1 (by rfl) ⟨2429027, by rfl⟩ : syracuseStep 3238703 = 4858055) B4858055
theorem B2159135 : Blo 2157435 2159135 := bstep (se 1 (by rfl) ⟨1619351, by rfl⟩ : syracuseStep 2159135 = 3238703) B3238703
theorem B3238709 : Blo 2157435 3238709 := bbase (se 5 (by rfl) ⟨151814, by rfl⟩ : syracuseStep 3238709 = 303629) (by norm_num)
theorem B2159139 : Blo 2157435 2159139 := bstep (se 1 (by rfl) ⟨1619354, by rfl⟩ : syracuseStep 2159139 = 3238709) B3238709
theorem B5465333 : Blo 2157435 5465333 := bbase (se 5 (by rfl) ⟨256187, by rfl⟩ : syracuseStep 5465333 = 512375) (by norm_num)
theorem B3643555 : Blo 2157435 3643555 := bstep (se 1 (by rfl) ⟨2732666, by rfl⟩ : syracuseStep 3643555 = 5465333) B5465333
theorem B4858073 : Blo 2157435 4858073 := bstep (se 2 (by rfl) ⟨1821777, by rfl⟩ : syracuseStep 4858073 = 3643555) B3643555
theorem B3238715 : Blo 2157435 3238715 := bstep (se 1 (by rfl) ⟨2429036, by rfl⟩ : syracuseStep 3238715 = 4858073) B4858073
theorem B2159143 : Blo 2157435 2159143 := bstep (se 1 (by rfl) ⟨1619357, by rfl⟩ : syracuseStep 2159143 = 3238715) B3238715
theorem B2429041 : Blo 2157435 2429041 := bbase (se 2 (by rfl) ⟨910890, by rfl⟩ : syracuseStep 2429041 = 1821781) (by norm_num)
theorem B3238721 : Blo 2157435 3238721 := bstep (se 2 (by rfl) ⟨1214520, by rfl⟩ : syracuseStep 3238721 = 2429041) B2429041
theorem B2159147 : Blo 2157435 2159147 := bstep (se 1 (by rfl) ⟨1619360, by rfl⟩ : syracuseStep 2159147 = 3238721) B3238721
theorem B2769961 : Blo 2157435 2769961 := bbase (se 2 (by rfl) ⟨1038735, by rfl⟩ : syracuseStep 2769961 = 2077471) (by norm_num)
theorem B3693281 : Blo 2157435 3693281 := bstep (se 2 (by rfl) ⟨1384980, by rfl⟩ : syracuseStep 3693281 = 2769961) B2769961
theorem B9848749 : Blo 2157435 9848749 := bstep (se 3 (by rfl) ⟨1846640, by rfl⟩ : syracuseStep 9848749 = 3693281) B3693281
theorem B13131665 : Blo 2157435 13131665 := bstep (se 2 (by rfl) ⟨4924374, by rfl⟩ : syracuseStep 13131665 = 9848749) B9848749
theorem B8754443 : Blo 2157435 8754443 := bstep (se 1 (by rfl) ⟨6565832, by rfl⟩ : syracuseStep 8754443 = 13131665) B13131665
theorem B5836295 : Blo 2157435 5836295 := bstep (se 1 (by rfl) ⟨4377221, by rfl⟩ : syracuseStep 5836295 = 8754443) B8754443
theorem B3890863 : Blo 2157435 3890863 := bstep (se 1 (by rfl) ⟨2918147, by rfl⟩ : syracuseStep 3890863 = 5836295) B5836295
theorem B5187817 : Blo 2157435 5187817 := bstep (se 2 (by rfl) ⟨1945431, by rfl⟩ : syracuseStep 5187817 = 3890863) B3890863
theorem B6917089 : Blo 2157435 6917089 := bstep (se 2 (by rfl) ⟨2593908, by rfl⟩ : syracuseStep 6917089 = 5187817) B5187817
theorem B9222785 : Blo 2157435 9222785 := bstep (se 2 (by rfl) ⟨3458544, by rfl⟩ : syracuseStep 9222785 = 6917089) B6917089
theorem B6148523 : Blo 2157435 6148523 := bstep (se 1 (by rfl) ⟨4611392, by rfl⟩ : syracuseStep 6148523 = 9222785) B9222785
theorem B4099015 : Blo 2157435 4099015 := bstep (se 1 (by rfl) ⟨3074261, by rfl⟩ : syracuseStep 4099015 = 6148523) B6148523
theorem B5465353 : Blo 2157435 5465353 := bstep (se 2 (by rfl) ⟨2049507, by rfl⟩ : syracuseStep 5465353 = 4099015) B4099015
theorem B7287137 : Blo 2157435 7287137 := bstep (se 2 (by rfl) ⟨2732676, by rfl⟩ : syracuseStep 7287137 = 5465353) B5465353
theorem B4858091 : Blo 2157435 4858091 := bstep (se 1 (by rfl) ⟨3643568, by rfl⟩ : syracuseStep 4858091 = 7287137) B7287137
theorem B3238727 : Blo 2157435 3238727 := bstep (se 1 (by rfl) ⟨2429045, by rfl⟩ : syracuseStep 3238727 = 4858091) B4858091
theorem B2159151 : Blo 2157435 2159151 := bstep (se 1 (by rfl) ⟨1619363, by rfl⟩ : syracuseStep 2159151 = 3238727) B3238727
theorem B3238733 : Blo 2157435 3238733 := bbase (se 3 (by rfl) ⟨607262, by rfl⟩ : syracuseStep 3238733 = 1214525) (by norm_num)
theorem B2159155 : Blo 2157435 2159155 := bstep (se 1 (by rfl) ⟨1619366, by rfl⟩ : syracuseStep 2159155 = 3238733) B3238733
theorem B4858109 : Blo 2157435 4858109 := bbase (se 3 (by rfl) ⟨910895, by rfl⟩ : syracuseStep 4858109 = 1821791) (by norm_num)
theorem B3238739 : Blo 2157435 3238739 := bstep (se 1 (by rfl) ⟨2429054, by rfl⟩ : syracuseStep 3238739 = 4858109) B4858109
theorem B2159159 : Blo 2157435 2159159 := bstep (se 1 (by rfl) ⟨1619369, by rfl⟩ : syracuseStep 2159159 = 3238739) B3238739
theorem B3643589 : Blo 2157435 3643589 := bbase (se 4 (by rfl) ⟨341586, by rfl⟩ : syracuseStep 3643589 = 683173) (by norm_num)
theorem B2429059 : Blo 2157435 2429059 := bstep (se 1 (by rfl) ⟨1821794, by rfl⟩ : syracuseStep 2429059 = 3643589) B3643589
theorem B3238745 : Blo 2157435 3238745 := bstep (se 2 (by rfl) ⟨1214529, by rfl⟩ : syracuseStep 3238745 = 2429059) B2429059
theorem B2159163 : Blo 2157435 2159163 := bstep (se 1 (by rfl) ⟨1619372, by rfl⟩ : syracuseStep 2159163 = 3238745) B3238745
theorem B16396181 : Blo 2157435 16396181 := bbase (se 6 (by rfl) ⟨384285, by rfl⟩ : syracuseStep 16396181 = 768571) (by norm_num)
theorem B10930787 : Blo 2157435 10930787 := bstep (se 1 (by rfl) ⟨8198090, by rfl⟩ : syracuseStep 10930787 = 16396181) B16396181
theorem B7287191 : Blo 2157435 7287191 := bstep (se 1 (by rfl) ⟨5465393, by rfl⟩ : syracuseStep 7287191 = 10930787) B10930787
theorem B4858127 : Blo 2157435 4858127 := bstep (se 1 (by rfl) ⟨3643595, by rfl⟩ : syracuseStep 4858127 = 7287191) B7287191
theorem B3238751 : Blo 2157435 3238751 := bstep (se 1 (by rfl) ⟨2429063, by rfl⟩ : syracuseStep 3238751 = 4858127) B4858127
theorem B2159167 : Blo 2157435 2159167 := bstep (se 1 (by rfl) ⟨1619375, by rfl⟩ : syracuseStep 2159167 = 3238751) B3238751
theorem B3238757 : Blo 2157435 3238757 := bbase (se 4 (by rfl) ⟨303633, by rfl⟩ : syracuseStep 3238757 = 607267) (by norm_num)
theorem B2159171 : Blo 2157435 2159171 := bstep (se 1 (by rfl) ⟨1619378, by rfl⟩ : syracuseStep 2159171 = 3238757) B3238757
theorem B4099061 : Blo 2157435 4099061 := bbase (se 5 (by rfl) ⟨192143, by rfl⟩ : syracuseStep 4099061 = 384287) (by norm_num)
theorem B2732707 : Blo 2157435 2732707 := bstep (se 1 (by rfl) ⟨2049530, by rfl⟩ : syracuseStep 2732707 = 4099061) B4099061
theorem B3643609 : Blo 2157435 3643609 := bstep (se 2 (by rfl) ⟨1366353, by rfl⟩ : syracuseStep 3643609 = 2732707) B2732707
theorem B4858145 : Blo 2157435 4858145 := bstep (se 2 (by rfl) ⟨1821804, by rfl⟩ : syracuseStep 4858145 = 3643609) B3643609
theorem B3238763 : Blo 2157435 3238763 := bstep (se 1 (by rfl) ⟨2429072, by rfl⟩ : syracuseStep 3238763 = 4858145) B4858145
theorem B2159175 : Blo 2157435 2159175 := bstep (se 1 (by rfl) ⟨1619381, by rfl⟩ : syracuseStep 2159175 = 3238763) B3238763
theorem B2429077 : Blo 2157435 2429077 := bbase (se 6 (by rfl) ⟨56931, by rfl⟩ : syracuseStep 2429077 = 113863) (by norm_num)
theorem B3238769 : Blo 2157435 3238769 := bstep (se 2 (by rfl) ⟨1214538, by rfl⟩ : syracuseStep 3238769 = 2429077) B2429077
theorem B2159179 : Blo 2157435 2159179 := bstep (se 1 (by rfl) ⟨1619384, by rfl⟩ : syracuseStep 2159179 = 3238769) B3238769
theorem B2732717 : Blo 2157435 2732717 := bbase (se 3 (by rfl) ⟨512384, by rfl⟩ : syracuseStep 2732717 = 1024769) (by norm_num)
theorem B7287245 : Blo 2157435 7287245 := bstep (se 3 (by rfl) ⟨1366358, by rfl⟩ : syracuseStep 7287245 = 2732717) B2732717
theorem B4858163 : Blo 2157435 4858163 := bstep (se 1 (by rfl) ⟨3643622, by rfl⟩ : syracuseStep 4858163 = 7287245) B7287245
theorem B3238775 : Blo 2157435 3238775 := bstep (se 1 (by rfl) ⟨2429081, by rfl⟩ : syracuseStep 3238775 = 4858163) B4858163
theorem B2159183 : Blo 2157435 2159183 := bstep (se 1 (by rfl) ⟨1619387, by rfl⟩ : syracuseStep 2159183 = 3238775) B3238775
theorem B3238781 : Blo 2157435 3238781 := bbase (se 3 (by rfl) ⟨607271, by rfl⟩ : syracuseStep 3238781 = 1214543) (by norm_num)
theorem B2159187 : Blo 2157435 2159187 := bstep (se 1 (by rfl) ⟨1619390, by rfl⟩ : syracuseStep 2159187 = 3238781) B3238781
theorem B4858181 : Blo 2157435 4858181 := bbase (se 4 (by rfl) ⟨455454, by rfl⟩ : syracuseStep 4858181 = 910909) (by norm_num)
theorem B3238787 : Blo 2157435 3238787 := bstep (se 1 (by rfl) ⟨2429090, by rfl⟩ : syracuseStep 3238787 = 4858181) B4858181
theorem B2159191 : Blo 2157435 2159191 := bstep (se 1 (by rfl) ⟨1619393, by rfl⟩ : syracuseStep 2159191 = 3238787) B3238787
theorem B5615621 : Blo 2157435 5615621 := bbase (se 4 (by rfl) ⟨526464, by rfl⟩ : syracuseStep 5615621 = 1052929) (by norm_num)
theorem B3743747 : Blo 2157435 3743747 := bstep (se 1 (by rfl) ⟨2807810, by rfl⟩ : syracuseStep 3743747 = 5615621) B5615621
theorem B2495831 : Blo 2157435 2495831 := bstep (se 1 (by rfl) ⟨1871873, by rfl⟩ : syracuseStep 2495831 = 3743747) B3743747
theorem B6655549 : Blo 2157435 6655549 := bstep (se 3 (by rfl) ⟨1247915, by rfl⟩ : syracuseStep 6655549 = 2495831) B2495831
theorem B8874065 : Blo 2157435 8874065 := bstep (se 2 (by rfl) ⟨3327774, by rfl⟩ : syracuseStep 8874065 = 6655549) B6655549
theorem B5916043 : Blo 2157435 5916043 := bstep (se 1 (by rfl) ⟨4437032, by rfl⟩ : syracuseStep 5916043 = 8874065) B8874065
theorem B31552229 : Blo 2157435 31552229 := bstep (se 4 (by rfl) ⟨2958021, by rfl⟩ : syracuseStep 31552229 = 5916043) B5916043
theorem B21034819 : Blo 2157435 21034819 := bstep (se 1 (by rfl) ⟨15776114, by rfl⟩ : syracuseStep 21034819 = 31552229) B31552229
theorem B28046425 : Blo 2157435 28046425 := bstep (se 2 (by rfl) ⟨10517409, by rfl⟩ : syracuseStep 28046425 = 21034819) B21034819
theorem B37395233 : Blo 2157435 37395233 := bstep (se 2 (by rfl) ⟨14023212, by rfl⟩ : syracuseStep 37395233 = 28046425) B28046425
theorem B24930155 : Blo 2157435 24930155 := bstep (se 1 (by rfl) ⟨18697616, by rfl⟩ : syracuseStep 24930155 = 37395233) B37395233
theorem B16620103 : Blo 2157435 16620103 := bstep (se 1 (by rfl) ⟨12465077, by rfl⟩ : syracuseStep 16620103 = 24930155) B24930155
theorem B22160137 : Blo 2157435 22160137 := bstep (se 2 (by rfl) ⟨8310051, by rfl⟩ : syracuseStep 22160137 = 16620103) B16620103
theorem B29546849 : Blo 2157435 29546849 := bstep (se 2 (by rfl) ⟨11080068, by rfl⟩ : syracuseStep 29546849 = 22160137) B22160137
theorem B19697899 : Blo 2157435 19697899 := bstep (se 1 (by rfl) ⟨14773424, by rfl⟩ : syracuseStep 19697899 = 29546849) B29546849
theorem B26263865 : Blo 2157435 26263865 := bstep (se 2 (by rfl) ⟨9848949, by rfl⟩ : syracuseStep 26263865 = 19697899) B19697899
theorem B17509243 : Blo 2157435 17509243 := bstep (se 1 (by rfl) ⟨13131932, by rfl⟩ : syracuseStep 17509243 = 26263865) B26263865
theorem B23345657 : Blo 2157435 23345657 := bstep (se 2 (by rfl) ⟨8754621, by rfl⟩ : syracuseStep 23345657 = 17509243) B17509243
theorem B15563771 : Blo 2157435 15563771 := bstep (se 1 (by rfl) ⟨11672828, by rfl⟩ : syracuseStep 15563771 = 23345657) B23345657
theorem B10375847 : Blo 2157435 10375847 := bstep (se 1 (by rfl) ⟨7781885, by rfl⟩ : syracuseStep 10375847 = 15563771) B15563771
theorem B6917231 : Blo 2157435 6917231 := bstep (se 1 (by rfl) ⟨5187923, by rfl⟩ : syracuseStep 6917231 = 10375847) B10375847
theorem B4611487 : Blo 2157435 4611487 := bstep (se 1 (by rfl) ⟨3458615, by rfl⟩ : syracuseStep 4611487 = 6917231) B6917231
theorem B6148649 : Blo 2157435 6148649 := bstep (se 2 (by rfl) ⟨2305743, by rfl⟩ : syracuseStep 6148649 = 4611487) B4611487
theorem B4099099 : Blo 2157435 4099099 := bstep (se 1 (by rfl) ⟨3074324, by rfl⟩ : syracuseStep 4099099 = 6148649) B6148649
theorem B5465465 : Blo 2157435 5465465 := bstep (se 2 (by rfl) ⟨2049549, by rfl⟩ : syracuseStep 5465465 = 4099099) B4099099
theorem B3643643 : Blo 2157435 3643643 := bstep (se 1 (by rfl) ⟨2732732, by rfl⟩ : syracuseStep 3643643 = 5465465) B5465465
theorem B2429095 : Blo 2157435 2429095 := bstep (se 1 (by rfl) ⟨1821821, by rfl⟩ : syracuseStep 2429095 = 3643643) B3643643
theorem B3238793 : Blo 2157435 3238793 := bstep (se 2 (by rfl) ⟨1214547, by rfl⟩ : syracuseStep 3238793 = 2429095) B2429095
theorem B2159195 : Blo 2157435 2159195 := bstep (se 1 (by rfl) ⟨1619396, by rfl⟩ : syracuseStep 2159195 = 3238793) B3238793
theorem B10930949 : Blo 2157435 10930949 := bbase (se 4 (by rfl) ⟨1024776, by rfl⟩ : syracuseStep 10930949 = 2049553) (by norm_num)
theorem B7287299 : Blo 2157435 7287299 := bstep (se 1 (by rfl) ⟨5465474, by rfl⟩ : syracuseStep 7287299 = 10930949) B10930949
theorem B4858199 : Blo 2157435 4858199 := bstep (se 1 (by rfl) ⟨3643649, by rfl⟩ : syracuseStep 4858199 = 7287299) B7287299
theorem B3238799 : Blo 2157435 3238799 := bstep (se 1 (by rfl) ⟨2429099, by rfl⟩ : syracuseStep 3238799 = 4858199) B4858199
theorem B2159199 : Blo 2157435 2159199 := bstep (se 1 (by rfl) ⟨1619399, by rfl⟩ : syracuseStep 2159199 = 3238799) B3238799
theorem B3238805 : Blo 2157435 3238805 := bbase (se 6 (by rfl) ⟨75909, by rfl⟩ : syracuseStep 3238805 = 151819) (by norm_num)
theorem B2159203 : Blo 2157435 2159203 := bstep (se 1 (by rfl) ⟨1619402, by rfl⟩ : syracuseStep 2159203 = 3238805) B3238805
theorem B12297365 : Blo 2157435 12297365 := bbase (se 6 (by rfl) ⟨288219, by rfl⟩ : syracuseStep 12297365 = 576439) (by norm_num)
theorem B8198243 : Blo 2157435 8198243 := bstep (se 1 (by rfl) ⟨6148682, by rfl⟩ : syracuseStep 8198243 = 12297365) B12297365
theorem B5465495 : Blo 2157435 5465495 := bstep (se 1 (by rfl) ⟨4099121, by rfl⟩ : syracuseStep 5465495 = 8198243) B8198243
theorem B3643663 : Blo 2157435 3643663 := bstep (se 1 (by rfl) ⟨2732747, by rfl⟩ : syracuseStep 3643663 = 5465495) B5465495
theorem B4858217 : Blo 2157435 4858217 := bstep (se 2 (by rfl) ⟨1821831, by rfl⟩ : syracuseStep 4858217 = 3643663) B3643663
theorem B3238811 : Blo 2157435 3238811 := bstep (se 1 (by rfl) ⟨2429108, by rfl⟩ : syracuseStep 3238811 = 4858217) B4858217
theorem B2159207 : Blo 2157435 2159207 := bstep (se 1 (by rfl) ⟨1619405, by rfl⟩ : syracuseStep 2159207 = 3238811) B3238811
theorem B2429113 : Blo 2157435 2429113 := bbase (se 2 (by rfl) ⟨910917, by rfl⟩ : syracuseStep 2429113 = 1821835) (by norm_num)
theorem B3238817 : Blo 2157435 3238817 := bstep (se 2 (by rfl) ⟨1214556, by rfl⟩ : syracuseStep 3238817 = 2429113) B2429113
theorem B2159211 : Blo 2157435 2159211 := bstep (se 1 (by rfl) ⟨1619408, by rfl⟩ : syracuseStep 2159211 = 3238817) B3238817
theorem B7781957 : Blo 2157435 7781957 := bbase (se 4 (by rfl) ⟨729558, by rfl⟩ : syracuseStep 7781957 = 1459117) (by norm_num)
theorem B5187971 : Blo 2157435 5187971 := bstep (se 1 (by rfl) ⟨3890978, by rfl⟩ : syracuseStep 5187971 = 7781957) B7781957
theorem B3458647 : Blo 2157435 3458647 := bstep (se 1 (by rfl) ⟨2593985, by rfl⟩ : syracuseStep 3458647 = 5187971) B5187971
theorem B4611529 : Blo 2157435 4611529 := bstep (se 2 (by rfl) ⟨1729323, by rfl⟩ : syracuseStep 4611529 = 3458647) B3458647
theorem B6148705 : Blo 2157435 6148705 := bstep (se 2 (by rfl) ⟨2305764, by rfl⟩ : syracuseStep 6148705 = 4611529) B4611529
theorem B8198273 : Blo 2157435 8198273 := bstep (se 2 (by rfl) ⟨3074352, by rfl⟩ : syracuseStep 8198273 = 6148705) B6148705
theorem B5465515 : Blo 2157435 5465515 := bstep (se 1 (by rfl) ⟨4099136, by rfl⟩ : syracuseStep 5465515 = 8198273) B8198273
theorem B7287353 : Blo 2157435 7287353 := bstep (se 2 (by rfl) ⟨2732757, by rfl⟩ : syracuseStep 7287353 = 5465515) B5465515
theorem B4858235 : Blo 2157435 4858235 := bstep (se 1 (by rfl) ⟨3643676, by rfl⟩ : syracuseStep 4858235 = 7287353) B7287353
theorem B3238823 : Blo 2157435 3238823 := bstep (se 1 (by rfl) ⟨2429117, by rfl⟩ : syracuseStep 3238823 = 4858235) B4858235
theorem B2159215 : Blo 2157435 2159215 := bstep (se 1 (by rfl) ⟨1619411, by rfl⟩ : syracuseStep 2159215 = 3238823) B3238823
theorem B3238829 : Blo 2157435 3238829 := bbase (se 3 (by rfl) ⟨607280, by rfl⟩ : syracuseStep 3238829 = 1214561) (by norm_num)
theorem B2159219 : Blo 2157435 2159219 := bstep (se 1 (by rfl) ⟨1619414, by rfl⟩ : syracuseStep 2159219 = 3238829) B3238829
theorem B4858253 : Blo 2157435 4858253 := bbase (se 3 (by rfl) ⟨910922, by rfl⟩ : syracuseStep 4858253 = 1821845) (by norm_num)
theorem B3238835 : Blo 2157435 3238835 := bstep (se 1 (by rfl) ⟨2429126, by rfl⟩ : syracuseStep 3238835 = 4858253) B4858253
theorem B2159223 : Blo 2157435 2159223 := bstep (se 1 (by rfl) ⟨1619417, by rfl⟩ : syracuseStep 2159223 = 3238835) B3238835
theorem B2732773 : Blo 2157435 2732773 := bbase (se 4 (by rfl) ⟨256197, by rfl⟩ : syracuseStep 2732773 = 512395) (by norm_num)
theorem B3643697 : Blo 2157435 3643697 := bstep (se 2 (by rfl) ⟨1366386, by rfl⟩ : syracuseStep 3643697 = 2732773) B2732773
theorem B2429131 : Blo 2157435 2429131 := bstep (se 1 (by rfl) ⟨1821848, by rfl⟩ : syracuseStep 2429131 = 3643697) B3643697
theorem B3238841 : Blo 2157435 3238841 := bstep (se 2 (by rfl) ⟨1214565, by rfl⟩ : syracuseStep 3238841 = 2429131) B2429131
theorem B2159227 : Blo 2157435 2159227 := bstep (se 1 (by rfl) ⟨1619420, by rfl⟩ : syracuseStep 2159227 = 3238841) B3238841
theorem B5540125 : Blo 2157435 5540125 := bbase (se 3 (by rfl) ⟨1038773, by rfl⟩ : syracuseStep 5540125 = 2077547) (by norm_num)
theorem B7386833 : Blo 2157435 7386833 := bstep (se 2 (by rfl) ⟨2770062, by rfl⟩ : syracuseStep 7386833 = 5540125) B5540125
theorem B19698221 : Blo 2157435 19698221 := bstep (se 3 (by rfl) ⟨3693416, by rfl⟩ : syracuseStep 19698221 = 7386833) B7386833
theorem B13132147 : Blo 2157435 13132147 := bstep (se 1 (by rfl) ⟨9849110, by rfl⟩ : syracuseStep 13132147 = 19698221) B19698221
theorem B17509529 : Blo 2157435 17509529 := bstep (se 2 (by rfl) ⟨6566073, by rfl⟩ : syracuseStep 17509529 = 13132147) B13132147
theorem B11673019 : Blo 2157435 11673019 := bstep (se 1 (by rfl) ⟨8754764, by rfl⟩ : syracuseStep 11673019 = 17509529) B17509529
theorem B15564025 : Blo 2157435 15564025 := bstep (se 2 (by rfl) ⟨5836509, by rfl⟩ : syracuseStep 15564025 = 11673019) B11673019
theorem B20752033 : Blo 2157435 20752033 := bstep (se 2 (by rfl) ⟨7782012, by rfl⟩ : syracuseStep 20752033 = 15564025) B15564025
theorem B27669377 : Blo 2157435 27669377 := bstep (se 2 (by rfl) ⟨10376016, by rfl⟩ : syracuseStep 27669377 = 20752033) B20752033
theorem B18446251 : Blo 2157435 18446251 := bstep (se 1 (by rfl) ⟨13834688, by rfl⟩ : syracuseStep 18446251 = 27669377) B27669377
theorem B24595001 : Blo 2157435 24595001 := bstep (se 2 (by rfl) ⟨9223125, by rfl⟩ : syracuseStep 24595001 = 18446251) B18446251
theorem B16396667 : Blo 2157435 16396667 := bstep (se 1 (by rfl) ⟨12297500, by rfl⟩ : syracuseStep 16396667 = 24595001) B24595001
theorem B10931111 : Blo 2157435 10931111 := bstep (se 1 (by rfl) ⟨8198333, by rfl⟩ : syracuseStep 10931111 = 16396667) B16396667
theorem B7287407 : Blo 2157435 7287407 := bstep (se 1 (by rfl) ⟨5465555, by rfl⟩ : syracuseStep 7287407 = 10931111) B10931111
theorem B4858271 : Blo 2157435 4858271 := bstep (se 1 (by rfl) ⟨3643703, by rfl⟩ : syracuseStep 4858271 = 7287407) B7287407
theorem B3238847 : Blo 2157435 3238847 := bstep (se 1 (by rfl) ⟨2429135, by rfl⟩ : syracuseStep 3238847 = 4858271) B4858271
theorem B2159231 : Blo 2157435 2159231 := bstep (se 1 (by rfl) ⟨1619423, by rfl⟩ : syracuseStep 2159231 = 3238847) B3238847
theorem B3238853 : Blo 2157435 3238853 := bbase (se 4 (by rfl) ⟨303642, by rfl⟩ : syracuseStep 3238853 = 607285) (by norm_num)
theorem B2159235 : Blo 2157435 2159235 := bstep (se 1 (by rfl) ⟨1619426, by rfl⟩ : syracuseStep 2159235 = 3238853) B3238853
theorem B3643717 : Blo 2157435 3643717 := bbase (se 4 (by rfl) ⟨341598, by rfl⟩ : syracuseStep 3643717 = 683197) (by norm_num)
theorem B4858289 : Blo 2157435 4858289 := bstep (se 2 (by rfl) ⟨1821858, by rfl⟩ : syracuseStep 4858289 = 3643717) B3643717
theorem B3238859 : Blo 2157435 3238859 := bstep (se 1 (by rfl) ⟨2429144, by rfl⟩ : syracuseStep 3238859 = 4858289) B4858289
theorem B2159239 : Blo 2157435 2159239 := bstep (se 1 (by rfl) ⟨1619429, by rfl⟩ : syracuseStep 2159239 = 3238859) B3238859
theorem B2429149 : Blo 2157435 2429149 := bbase (se 3 (by rfl) ⟨455465, by rfl⟩ : syracuseStep 2429149 = 910931) (by norm_num)
theorem B3238865 : Blo 2157435 3238865 := bstep (se 2 (by rfl) ⟨1214574, by rfl⟩ : syracuseStep 3238865 = 2429149) B2429149
theorem B2159243 : Blo 2157435 2159243 := bstep (se 1 (by rfl) ⟨1619432, by rfl⟩ : syracuseStep 2159243 = 3238865) B3238865
theorem B7287461 : Blo 2157435 7287461 := bbase (se 4 (by rfl) ⟨683199, by rfl⟩ : syracuseStep 7287461 = 1366399) (by norm_num)
theorem B4858307 : Blo 2157435 4858307 := bstep (se 1 (by rfl) ⟨3643730, by rfl⟩ : syracuseStep 4858307 = 7287461) B7287461
theorem B3238871 : Blo 2157435 3238871 := bstep (se 1 (by rfl) ⟨2429153, by rfl⟩ : syracuseStep 3238871 = 4858307) B4858307
theorem B2159247 : Blo 2157435 2159247 := bstep (se 1 (by rfl) ⟨1619435, by rfl⟩ : syracuseStep 2159247 = 3238871) B3238871
theorem B3238877 : Blo 2157435 3238877 := bbase (se 3 (by rfl) ⟨607289, by rfl⟩ : syracuseStep 3238877 = 1214579) (by norm_num)
theorem B2159251 : Blo 2157435 2159251 := bstep (se 1 (by rfl) ⟨1619438, by rfl⟩ : syracuseStep 2159251 = 3238877) B3238877
theorem B4858325 : Blo 2157435 4858325 := bbase (se 7 (by rfl) ⟨56933, by rfl⟩ : syracuseStep 4858325 = 113867) (by norm_num)
theorem B3238883 : Blo 2157435 3238883 := bstep (se 1 (by rfl) ⟨2429162, by rfl⟩ : syracuseStep 3238883 = 4858325) B4858325
theorem B2159255 : Blo 2157435 2159255 := bstep (se 1 (by rfl) ⟨1619441, by rfl⟩ : syracuseStep 2159255 = 3238883) B3238883
theorem B11673173 : Blo 2157435 11673173 := bbase (se 8 (by rfl) ⟨68397, by rfl⟩ : syracuseStep 11673173 = 136795) (by norm_num)
theorem B31128461 : Blo 2157435 31128461 := bstep (se 3 (by rfl) ⟨5836586, by rfl⟩ : syracuseStep 31128461 = 11673173) B11673173
theorem B20752307 : Blo 2157435 20752307 := bstep (se 1 (by rfl) ⟨15564230, by rfl⟩ : syracuseStep 20752307 = 31128461) B31128461
theorem B13834871 : Blo 2157435 13834871 := bstep (se 1 (by rfl) ⟨10376153, by rfl⟩ : syracuseStep 13834871 = 20752307) B20752307
theorem B9223247 : Blo 2157435 9223247 := bstep (se 1 (by rfl) ⟨6917435, by rfl⟩ : syracuseStep 9223247 = 13834871) B13834871
theorem B6148831 : Blo 2157435 6148831 := bstep (se 1 (by rfl) ⟨4611623, by rfl⟩ : syracuseStep 6148831 = 9223247) B9223247
theorem B8198441 : Blo 2157435 8198441 := bstep (se 2 (by rfl) ⟨3074415, by rfl⟩ : syracuseStep 8198441 = 6148831) B6148831
theorem B5465627 : Blo 2157435 5465627 := bstep (se 1 (by rfl) ⟨4099220, by rfl⟩ : syracuseStep 5465627 = 8198441) B8198441
theorem B3643751 : Blo 2157435 3643751 := bstep (se 1 (by rfl) ⟨2732813, by rfl⟩ : syracuseStep 3643751 = 5465627) B5465627
theorem B2429167 : Blo 2157435 2429167 := bstep (se 1 (by rfl) ⟨1821875, by rfl⟩ : syracuseStep 2429167 = 3643751) B3643751
theorem B3238889 : Blo 2157435 3238889 := bstep (se 2 (by rfl) ⟨1214583, by rfl⟩ : syracuseStep 3238889 = 2429167) B2429167
theorem B2159259 : Blo 2157435 2159259 := bstep (se 1 (by rfl) ⟨1619444, by rfl⟩ : syracuseStep 2159259 = 3238889) B3238889
theorem B21035477 : Blo 2157435 21035477 := bbase (se 7 (by rfl) ⟨246509, by rfl⟩ : syracuseStep 21035477 = 493019) (by norm_num)
theorem B56094605 : Blo 2157435 56094605 := bstep (se 3 (by rfl) ⟨10517738, by rfl⟩ : syracuseStep 56094605 = 21035477) B21035477
theorem B37396403 : Blo 2157435 37396403 := bstep (se 1 (by rfl) ⟨28047302, by rfl⟩ : syracuseStep 37396403 = 56094605) B56094605
theorem B24930935 : Blo 2157435 24930935 := bstep (se 1 (by rfl) ⟨18698201, by rfl⟩ : syracuseStep 24930935 = 37396403) B37396403
theorem B16620623 : Blo 2157435 16620623 := bstep (se 1 (by rfl) ⟨12465467, by rfl⟩ : syracuseStep 16620623 = 24930935) B24930935
theorem B11080415 : Blo 2157435 11080415 := bstep (se 1 (by rfl) ⟨8310311, by rfl⟩ : syracuseStep 11080415 = 16620623) B16620623
theorem B29547773 : Blo 2157435 29547773 := bstep (se 3 (by rfl) ⟨5540207, by rfl⟩ : syracuseStep 29547773 = 11080415) B11080415
theorem B19698515 : Blo 2157435 19698515 := bstep (se 1 (by rfl) ⟨14773886, by rfl⟩ : syracuseStep 19698515 = 29547773) B29547773
theorem B13132343 : Blo 2157435 13132343 := bstep (se 1 (by rfl) ⟨9849257, by rfl⟩ : syracuseStep 13132343 = 19698515) B19698515
theorem B8754895 : Blo 2157435 8754895 := bstep (se 1 (by rfl) ⟨6566171, by rfl⟩ : syracuseStep 8754895 = 13132343) B13132343
theorem B11673193 : Blo 2157435 11673193 := bstep (se 2 (by rfl) ⟨4377447, by rfl⟩ : syracuseStep 11673193 = 8754895) B8754895
theorem B15564257 : Blo 2157435 15564257 := bstep (se 2 (by rfl) ⟨5836596, by rfl⟩ : syracuseStep 15564257 = 11673193) B11673193
theorem B10376171 : Blo 2157435 10376171 := bstep (se 1 (by rfl) ⟨7782128, by rfl⟩ : syracuseStep 10376171 = 15564257) B15564257
theorem B6917447 : Blo 2157435 6917447 := bstep (se 1 (by rfl) ⟨5188085, by rfl⟩ : syracuseStep 6917447 = 10376171) B10376171
theorem B18446525 : Blo 2157435 18446525 := bstep (se 3 (by rfl) ⟨3458723, by rfl⟩ : syracuseStep 18446525 = 6917447) B6917447
theorem B12297683 : Blo 2157435 12297683 := bstep (se 1 (by rfl) ⟨9223262, by rfl⟩ : syracuseStep 12297683 = 18446525) B18446525
theorem B8198455 : Blo 2157435 8198455 := bstep (se 1 (by rfl) ⟨6148841, by rfl⟩ : syracuseStep 8198455 = 12297683) B12297683
theorem B10931273 : Blo 2157435 10931273 := bstep (se 2 (by rfl) ⟨4099227, by rfl⟩ : syracuseStep 10931273 = 8198455) B8198455
theorem B7287515 : Blo 2157435 7287515 := bstep (se 1 (by rfl) ⟨5465636, by rfl⟩ : syracuseStep 7287515 = 10931273) B10931273
theorem B4858343 : Blo 2157435 4858343 := bstep (se 1 (by rfl) ⟨3643757, by rfl⟩ : syracuseStep 4858343 = 7287515) B7287515
theorem B3238895 : Blo 2157435 3238895 := bstep (se 1 (by rfl) ⟨2429171, by rfl⟩ : syracuseStep 3238895 = 4858343) B4858343
theorem B2159263 : Blo 2157435 2159263 := bstep (se 1 (by rfl) ⟨1619447, by rfl⟩ : syracuseStep 2159263 = 3238895) B3238895
theorem B3238901 : Blo 2157435 3238901 := bbase (se 5 (by rfl) ⟨151823, by rfl⟩ : syracuseStep 3238901 = 303647) (by norm_num)
theorem B2159267 : Blo 2157435 2159267 := bstep (se 1 (by rfl) ⟨1619450, by rfl⟩ : syracuseStep 2159267 = 3238901) B3238901
theorem B2594053 : Blo 2157435 2594053 := bbase (se 4 (by rfl) ⟨243192, by rfl⟩ : syracuseStep 2594053 = 486385) (by norm_num)
theorem B3458737 : Blo 2157435 3458737 := bstep (se 2 (by rfl) ⟨1297026, by rfl⟩ : syracuseStep 3458737 = 2594053) B2594053
theorem B4611649 : Blo 2157435 4611649 := bstep (se 2 (by rfl) ⟨1729368, by rfl⟩ : syracuseStep 4611649 = 3458737) B3458737
theorem B6148865 : Blo 2157435 6148865 := bstep (se 2 (by rfl) ⟨2305824, by rfl⟩ : syracuseStep 6148865 = 4611649) B4611649
theorem B4099243 : Blo 2157435 4099243 := bstep (se 1 (by rfl) ⟨3074432, by rfl⟩ : syracuseStep 4099243 = 6148865) B6148865
theorem B5465657 : Blo 2157435 5465657 := bstep (se 2 (by rfl) ⟨2049621, by rfl⟩ : syracuseStep 5465657 = 4099243) B4099243
theorem B3643771 : Blo 2157435 3643771 := bstep (se 1 (by rfl) ⟨2732828, by rfl⟩ : syracuseStep 3643771 = 5465657) B5465657
theorem B4858361 : Blo 2157435 4858361 := bstep (se 2 (by rfl) ⟨1821885, by rfl⟩ : syracuseStep 4858361 = 3643771) B3643771
theorem B3238907 : Blo 2157435 3238907 := bstep (se 1 (by rfl) ⟨2429180, by rfl⟩ : syracuseStep 3238907 = 4858361) B4858361
theorem B2159271 : Blo 2157435 2159271 := bstep (se 1 (by rfl) ⟨1619453, by rfl⟩ : syracuseStep 2159271 = 3238907) B3238907
theorem B2429185 : Blo 2157435 2429185 := bbase (se 2 (by rfl) ⟨910944, by rfl⟩ : syracuseStep 2429185 = 1821889) (by norm_num)
theorem B3238913 : Blo 2157435 3238913 := bstep (se 2 (by rfl) ⟨1214592, by rfl⟩ : syracuseStep 3238913 = 2429185) B2429185
theorem B2159275 : Blo 2157435 2159275 := bstep (se 1 (by rfl) ⟨1619456, by rfl⟩ : syracuseStep 2159275 = 3238913) B3238913
theorem B5465677 : Blo 2157435 5465677 := bbase (se 3 (by rfl) ⟨1024814, by rfl⟩ : syracuseStep 5465677 = 2049629) (by norm_num)
theorem B7287569 : Blo 2157435 7287569 := bstep (se 2 (by rfl) ⟨2732838, by rfl⟩ : syracuseStep 7287569 = 5465677) B5465677
theorem B4858379 : Blo 2157435 4858379 := bstep (se 1 (by rfl) ⟨3643784, by rfl⟩ : syracuseStep 4858379 = 7287569) B7287569
theorem B3238919 : Blo 2157435 3238919 := bstep (se 1 (by rfl) ⟨2429189, by rfl⟩ : syracuseStep 3238919 = 4858379) B4858379
theorem B2159279 : Blo 2157435 2159279 := bstep (se 1 (by rfl) ⟨1619459, by rfl⟩ : syracuseStep 2159279 = 3238919) B3238919
theorem B3238925 : Blo 2157435 3238925 := bbase (se 3 (by rfl) ⟨607298, by rfl⟩ : syracuseStep 3238925 = 1214597) (by norm_num)
theorem B2159283 : Blo 2157435 2159283 := bstep (se 1 (by rfl) ⟨1619462, by rfl⟩ : syracuseStep 2159283 = 3238925) B3238925
theorem B4858397 : Blo 2157435 4858397 := bbase (se 3 (by rfl) ⟨910949, by rfl⟩ : syracuseStep 4858397 = 1821899) (by norm_num)
theorem B3238931 : Blo 2157435 3238931 := bstep (se 1 (by rfl) ⟨2429198, by rfl⟩ : syracuseStep 3238931 = 4858397) B4858397
theorem B2159287 : Blo 2157435 2159287 := bstep (se 1 (by rfl) ⟨1619465, by rfl⟩ : syracuseStep 2159287 = 3238931) B3238931
theorem B3643805 : Blo 2157435 3643805 := bbase (se 3 (by rfl) ⟨683213, by rfl⟩ : syracuseStep 3643805 = 1366427) (by norm_num)
theorem B2429203 : Blo 2157435 2429203 := bstep (se 1 (by rfl) ⟨1821902, by rfl⟩ : syracuseStep 2429203 = 3643805) B3643805
theorem B3238937 : Blo 2157435 3238937 := bstep (se 2 (by rfl) ⟨1214601, by rfl⟩ : syracuseStep 3238937 = 2429203) B2429203
theorem B2159291 : Blo 2157435 2159291 := bstep (se 1 (by rfl) ⟨1619468, by rfl⟩ : syracuseStep 2159291 = 3238937) B3238937
theorem B19698805 : Blo 2157435 19698805 := bbase (se 5 (by rfl) ⟨923381, by rfl⟩ : syracuseStep 19698805 = 1846763) (by norm_num)
theorem B26265073 : Blo 2157435 26265073 := bstep (se 2 (by rfl) ⟨9849402, by rfl⟩ : syracuseStep 26265073 = 19698805) B19698805
theorem B35020097 : Blo 2157435 35020097 := bstep (se 2 (by rfl) ⟨13132536, by rfl⟩ : syracuseStep 35020097 = 26265073) B26265073
theorem B23346731 : Blo 2157435 23346731 := bstep (se 1 (by rfl) ⟨17510048, by rfl⟩ : syracuseStep 23346731 = 35020097) B35020097
theorem B15564487 : Blo 2157435 15564487 := bstep (se 1 (by rfl) ⟨11673365, by rfl⟩ : syracuseStep 15564487 = 23346731) B23346731
theorem B20752649 : Blo 2157435 20752649 := bstep (se 2 (by rfl) ⟨7782243, by rfl⟩ : syracuseStep 20752649 = 15564487) B15564487
theorem B13835099 : Blo 2157435 13835099 := bstep (se 1 (by rfl) ⟨10376324, by rfl⟩ : syracuseStep 13835099 = 20752649) B20752649
theorem B9223399 : Blo 2157435 9223399 := bstep (se 1 (by rfl) ⟨6917549, by rfl⟩ : syracuseStep 9223399 = 13835099) B13835099
theorem B12297865 : Blo 2157435 12297865 := bstep (se 2 (by rfl) ⟨4611699, by rfl⟩ : syracuseStep 12297865 = 9223399) B9223399
theorem B16397153 : Blo 2157435 16397153 := bstep (se 2 (by rfl) ⟨6148932, by rfl⟩ : syracuseStep 16397153 = 12297865) B12297865
theorem B10931435 : Blo 2157435 10931435 := bstep (se 1 (by rfl) ⟨8198576, by rfl⟩ : syracuseStep 10931435 = 16397153) B16397153
theorem B7287623 : Blo 2157435 7287623 := bstep (se 1 (by rfl) ⟨5465717, by rfl⟩ : syracuseStep 7287623 = 10931435) B10931435
theorem B4858415 : Blo 2157435 4858415 := bstep (se 1 (by rfl) ⟨3643811, by rfl⟩ : syracuseStep 4858415 = 7287623) B7287623
theorem B3238943 : Blo 2157435 3238943 := bstep (se 1 (by rfl) ⟨2429207, by rfl⟩ : syracuseStep 3238943 = 4858415) B4858415
theorem B2159295 : Blo 2157435 2159295 := bstep (se 1 (by rfl) ⟨1619471, by rfl⟩ : syracuseStep 2159295 = 3238943) B3238943
theorem B3238949 : Blo 2157435 3238949 := bbase (se 4 (by rfl) ⟨303651, by rfl⟩ : syracuseStep 3238949 = 607303) (by norm_num)
theorem B2159299 : Blo 2157435 2159299 := bstep (se 1 (by rfl) ⟨1619474, by rfl⟩ : syracuseStep 2159299 = 3238949) B3238949
theorem B2732869 : Blo 2157435 2732869 := bbase (se 4 (by rfl) ⟨256206, by rfl⟩ : syracuseStep 2732869 = 512413) (by norm_num)
theorem B3643825 : Blo 2157435 3643825 := bstep (se 2 (by rfl) ⟨1366434, by rfl⟩ : syracuseStep 3643825 = 2732869) B2732869
theorem B4858433 : Blo 2157435 4858433 := bstep (se 2 (by rfl) ⟨1821912, by rfl⟩ : syracuseStep 4858433 = 3643825) B3643825
theorem B3238955 : Blo 2157435 3238955 := bstep (se 1 (by rfl) ⟨2429216, by rfl⟩ : syracuseStep 3238955 = 4858433) B4858433
theorem B2159303 : Blo 2157435 2159303 := bstep (se 1 (by rfl) ⟨1619477, by rfl⟩ : syracuseStep 2159303 = 3238955) B3238955
theorem B2429221 : Blo 2157435 2429221 := bbase (se 4 (by rfl) ⟨227739, by rfl⟩ : syracuseStep 2429221 = 455479) (by norm_num)
theorem B3238961 : Blo 2157435 3238961 := bstep (se 2 (by rfl) ⟨1214610, by rfl⟩ : syracuseStep 3238961 = 2429221) B2429221
theorem B2159307 : Blo 2157435 2159307 := bstep (se 1 (by rfl) ⟨1619480, by rfl⟩ : syracuseStep 2159307 = 3238961) B3238961
theorem B2594101 : Blo 2157435 2594101 := bbase (se 5 (by rfl) ⟨121598, by rfl⟩ : syracuseStep 2594101 = 243197) (by norm_num)
theorem B3458801 : Blo 2157435 3458801 := bstep (se 2 (by rfl) ⟨1297050, by rfl⟩ : syracuseStep 3458801 = 2594101) B2594101
theorem B9223469 : Blo 2157435 9223469 := bstep (se 3 (by rfl) ⟨1729400, by rfl⟩ : syracuseStep 9223469 = 3458801) B3458801
theorem B6148979 : Blo 2157435 6148979 := bstep (se 1 (by rfl) ⟨4611734, by rfl⟩ : syracuseStep 6148979 = 9223469) B9223469
theorem B4099319 : Blo 2157435 4099319 := bstep (se 1 (by rfl) ⟨3074489, by rfl⟩ : syracuseStep 4099319 = 6148979) B6148979
theorem B2732879 : Blo 2157435 2732879 := bstep (se 1 (by rfl) ⟨2049659, by rfl⟩ : syracuseStep 2732879 = 4099319) B4099319
theorem B7287677 : Blo 2157435 7287677 := bstep (se 3 (by rfl) ⟨1366439, by rfl⟩ : syracuseStep 7287677 = 2732879) B2732879
theorem B4858451 : Blo 2157435 4858451 := bstep (se 1 (by rfl) ⟨3643838, by rfl⟩ : syracuseStep 4858451 = 7287677) B7287677
theorem B3238967 : Blo 2157435 3238967 := bstep (se 1 (by rfl) ⟨2429225, by rfl⟩ : syracuseStep 3238967 = 4858451) B4858451
theorem B2159311 : Blo 2157435 2159311 := bstep (se 1 (by rfl) ⟨1619483, by rfl⟩ : syracuseStep 2159311 = 3238967) B3238967
theorem B3238973 : Blo 2157435 3238973 := bbase (se 3 (by rfl) ⟨607307, by rfl⟩ : syracuseStep 3238973 = 1214615) (by norm_num)
theorem B2159315 : Blo 2157435 2159315 := bstep (se 1 (by rfl) ⟨1619486, by rfl⟩ : syracuseStep 2159315 = 3238973) B3238973
theorem B4858469 : Blo 2157435 4858469 := bbase (se 4 (by rfl) ⟨455481, by rfl⟩ : syracuseStep 4858469 = 910963) (by norm_num)
theorem B3238979 : Blo 2157435 3238979 := bstep (se 1 (by rfl) ⟨2429234, by rfl⟩ : syracuseStep 3238979 = 4858469) B4858469
theorem B2159319 : Blo 2157435 2159319 := bstep (se 1 (by rfl) ⟨1619489, by rfl⟩ : syracuseStep 2159319 = 3238979) B3238979
theorem B5465789 : Blo 2157435 5465789 := bbase (se 3 (by rfl) ⟨1024835, by rfl⟩ : syracuseStep 5465789 = 2049671) (by norm_num)
theorem B3643859 : Blo 2157435 3643859 := bstep (se 1 (by rfl) ⟨2732894, by rfl⟩ : syracuseStep 3643859 = 5465789) B5465789
theorem B2429239 : Blo 2157435 2429239 := bstep (se 1 (by rfl) ⟨1821929, by rfl⟩ : syracuseStep 2429239 = 3643859) B3643859
theorem B3238985 : Blo 2157435 3238985 := bstep (se 2 (by rfl) ⟨1214619, by rfl⟩ : syracuseStep 3238985 = 2429239) B2429239
theorem B2159323 : Blo 2157435 2159323 := bstep (se 1 (by rfl) ⟨1619492, by rfl⟩ : syracuseStep 2159323 = 3238985) B3238985
theorem B4099349 : Blo 2157435 4099349 := bbase (se 6 (by rfl) ⟨96078, by rfl⟩ : syracuseStep 4099349 = 192157) (by norm_num)
theorem B10931597 : Blo 2157435 10931597 := bstep (se 3 (by rfl) ⟨2049674, by rfl⟩ : syracuseStep 10931597 = 4099349) B4099349
theorem B7287731 : Blo 2157435 7287731 := bstep (se 1 (by rfl) ⟨5465798, by rfl⟩ : syracuseStep 7287731 = 10931597) B10931597
theorem B4858487 : Blo 2157435 4858487 := bstep (se 1 (by rfl) ⟨3643865, by rfl⟩ : syracuseStep 4858487 = 7287731) B7287731
theorem B3238991 : Blo 2157435 3238991 := bstep (se 1 (by rfl) ⟨2429243, by rfl⟩ : syracuseStep 3238991 = 4858487) B4858487
theorem B2159327 : Blo 2157435 2159327 := bstep (se 1 (by rfl) ⟨1619495, by rfl⟩ : syracuseStep 2159327 = 3238991) B3238991
theorem B3238997 : Blo 2157435 3238997 := bbase (se 8 (by rfl) ⟨18978, by rfl⟩ : syracuseStep 3238997 = 37957) (by norm_num)
theorem B2159331 : Blo 2157435 2159331 := bstep (se 1 (by rfl) ⟨1619498, by rfl⟩ : syracuseStep 2159331 = 3238997) B3238997
theorem B7782389 : Blo 2157435 7782389 := bbase (se 5 (by rfl) ⟨364799, by rfl⟩ : syracuseStep 7782389 = 729599) (by norm_num)
theorem B5188259 : Blo 2157435 5188259 := bstep (se 1 (by rfl) ⟨3891194, by rfl⟩ : syracuseStep 5188259 = 7782389) B7782389
theorem B13835357 : Blo 2157435 13835357 := bstep (se 3 (by rfl) ⟨2594129, by rfl⟩ : syracuseStep 13835357 = 5188259) B5188259
theorem B9223571 : Blo 2157435 9223571 := bstep (se 1 (by rfl) ⟨6917678, by rfl⟩ : syracuseStep 9223571 = 13835357) B13835357
theorem B6149047 : Blo 2157435 6149047 := bstep (se 1 (by rfl) ⟨4611785, by rfl⟩ : syracuseStep 6149047 = 9223571) B9223571
theorem B8198729 : Blo 2157435 8198729 := bstep (se 2 (by rfl) ⟨3074523, by rfl⟩ : syracuseStep 8198729 = 6149047) B6149047
theorem B5465819 : Blo 2157435 5465819 := bstep (se 1 (by rfl) ⟨4099364, by rfl⟩ : syracuseStep 5465819 = 8198729) B8198729
theorem B3643879 : Blo 2157435 3643879 := bstep (se 1 (by rfl) ⟨2732909, by rfl⟩ : syracuseStep 3643879 = 5465819) B5465819
theorem B4858505 : Blo 2157435 4858505 := bstep (se 2 (by rfl) ⟨1821939, by rfl⟩ : syracuseStep 4858505 = 3643879) B3643879
theorem B3239003 : Blo 2157435 3239003 := bstep (se 1 (by rfl) ⟨2429252, by rfl⟩ : syracuseStep 3239003 = 4858505) B4858505
theorem B2159335 : Blo 2157435 2159335 := bstep (se 1 (by rfl) ⟨1619501, by rfl⟩ : syracuseStep 2159335 = 3239003) B3239003
theorem B2429257 : Blo 2157435 2429257 := bbase (se 2 (by rfl) ⟨910971, by rfl⟩ : syracuseStep 2429257 = 1821943) (by norm_num)
theorem B3239009 : Blo 2157435 3239009 := bstep (se 2 (by rfl) ⟨1214628, by rfl⟩ : syracuseStep 3239009 = 2429257) B2429257
theorem B2159339 : Blo 2157435 2159339 := bstep (se 1 (by rfl) ⟨1619504, by rfl⟩ : syracuseStep 2159339 = 3239009) B3239009
theorem B5540413 : Blo 2157435 5540413 := bbase (se 3 (by rfl) ⟨1038827, by rfl⟩ : syracuseStep 5540413 = 2077655) (by norm_num)
theorem B7387217 : Blo 2157435 7387217 := bstep (se 2 (by rfl) ⟨2770206, by rfl⟩ : syracuseStep 7387217 = 5540413) B5540413
theorem B4924811 : Blo 2157435 4924811 := bstep (se 1 (by rfl) ⟨3693608, by rfl⟩ : syracuseStep 4924811 = 7387217) B7387217
theorem B13132829 : Blo 2157435 13132829 := bstep (se 3 (by rfl) ⟨2462405, by rfl⟩ : syracuseStep 13132829 = 4924811) B4924811
theorem B8755219 : Blo 2157435 8755219 := bstep (se 1 (by rfl) ⟨6566414, by rfl⟩ : syracuseStep 8755219 = 13132829) B13132829
theorem B46694501 : Blo 2157435 46694501 := bstep (se 4 (by rfl) ⟨4377609, by rfl⟩ : syracuseStep 46694501 = 8755219) B8755219
theorem B31129667 : Blo 2157435 31129667 := bstep (se 1 (by rfl) ⟨23347250, by rfl⟩ : syracuseStep 31129667 = 46694501) B46694501
theorem B20753111 : Blo 2157435 20753111 := bstep (se 1 (by rfl) ⟨15564833, by rfl⟩ : syracuseStep 20753111 = 31129667) B31129667
theorem B13835407 : Blo 2157435 13835407 := bstep (se 1 (by rfl) ⟨10376555, by rfl⟩ : syracuseStep 13835407 = 20753111) B20753111
theorem B18447209 : Blo 2157435 18447209 := bstep (se 2 (by rfl) ⟨6917703, by rfl⟩ : syracuseStep 18447209 = 13835407) B13835407
theorem B12298139 : Blo 2157435 12298139 := bstep (se 1 (by rfl) ⟨9223604, by rfl⟩ : syracuseStep 12298139 = 18447209) B18447209
theorem B8198759 : Blo 2157435 8198759 := bstep (se 1 (by rfl) ⟨6149069, by rfl⟩ : syracuseStep 8198759 = 12298139) B12298139
theorem B5465839 : Blo 2157435 5465839 := bstep (se 1 (by rfl) ⟨4099379, by rfl⟩ : syracuseStep 5465839 = 8198759) B8198759
theorem B7287785 : Blo 2157435 7287785 := bstep (se 2 (by rfl) ⟨2732919, by rfl⟩ : syracuseStep 7287785 = 5465839) B5465839
theorem B4858523 : Blo 2157435 4858523 := bstep (se 1 (by rfl) ⟨3643892, by rfl⟩ : syracuseStep 4858523 = 7287785) B7287785
theorem B3239015 : Blo 2157435 3239015 := bstep (se 1 (by rfl) ⟨2429261, by rfl⟩ : syracuseStep 3239015 = 4858523) B4858523
theorem B2159343 : Blo 2157435 2159343 := bstep (se 1 (by rfl) ⟨1619507, by rfl⟩ : syracuseStep 2159343 = 3239015) B3239015
theorem B3239021 : Blo 2157435 3239021 := bbase (se 3 (by rfl) ⟨607316, by rfl⟩ : syracuseStep 3239021 = 1214633) (by norm_num)
theorem B2159347 : Blo 2157435 2159347 := bstep (se 1 (by rfl) ⟨1619510, by rfl⟩ : syracuseStep 2159347 = 3239021) B3239021
theorem B4858541 : Blo 2157435 4858541 := bbase (se 3 (by rfl) ⟨910976, by rfl⟩ : syracuseStep 4858541 = 1821953) (by norm_num)
theorem B3239027 : Blo 2157435 3239027 := bstep (se 1 (by rfl) ⟨2429270, by rfl⟩ : syracuseStep 3239027 = 4858541) B4858541
theorem B2159351 : Blo 2157435 2159351 := bstep (se 1 (by rfl) ⟨1619513, by rfl⟩ : syracuseStep 2159351 = 3239027) B3239027
theorem B4611829 : Blo 2157435 4611829 := bbase (se 5 (by rfl) ⟨216179, by rfl⟩ : syracuseStep 4611829 = 432359) (by norm_num)
theorem B6149105 : Blo 2157435 6149105 := bstep (se 2 (by rfl) ⟨2305914, by rfl⟩ : syracuseStep 6149105 = 4611829) B4611829
theorem B4099403 : Blo 2157435 4099403 := bstep (se 1 (by rfl) ⟨3074552, by rfl⟩ : syracuseStep 4099403 = 6149105) B6149105
theorem B2732935 : Blo 2157435 2732935 := bstep (se 1 (by rfl) ⟨2049701, by rfl⟩ : syracuseStep 2732935 = 4099403) B4099403
theorem B3643913 : Blo 2157435 3643913 := bstep (se 2 (by rfl) ⟨1366467, by rfl⟩ : syracuseStep 3643913 = 2732935) B2732935
theorem B2429275 : Blo 2157435 2429275 := bstep (se 1 (by rfl) ⟨1821956, by rfl⟩ : syracuseStep 2429275 = 3643913) B3643913
theorem B3239033 : Blo 2157435 3239033 := bstep (se 2 (by rfl) ⟨1214637, by rfl⟩ : syracuseStep 3239033 = 2429275) B2429275
theorem B2159355 : Blo 2157435 2159355 := bstep (se 1 (by rfl) ⟨1619516, by rfl⟩ : syracuseStep 2159355 = 3239033) B3239033
theorem B18699029 : Blo 2157435 18699029 := bbase (se 6 (by rfl) ⟨438258, by rfl⟩ : syracuseStep 18699029 = 876517) (by norm_num)
theorem B12466019 : Blo 2157435 12466019 := bstep (se 1 (by rfl) ⟨9349514, by rfl⟩ : syracuseStep 12466019 = 18699029) B18699029
theorem B33242717 : Blo 2157435 33242717 := bstep (se 3 (by rfl) ⟨6233009, by rfl⟩ : syracuseStep 33242717 = 12466019) B12466019
theorem B22161811 : Blo 2157435 22161811 := bstep (se 1 (by rfl) ⟨16621358, by rfl⟩ : syracuseStep 22161811 = 33242717) B33242717
theorem B29549081 : Blo 2157435 29549081 := bstep (se 2 (by rfl) ⟨11080905, by rfl⟩ : syracuseStep 29549081 = 22161811) B22161811
theorem B78797549 : Blo 2157435 78797549 := bstep (se 3 (by rfl) ⟨14774540, by rfl⟩ : syracuseStep 78797549 = 29549081) B29549081
theorem B52531699 : Blo 2157435 52531699 := bstep (se 1 (by rfl) ⟨39398774, by rfl⟩ : syracuseStep 52531699 = 78797549) B78797549
theorem B70042265 : Blo 2157435 70042265 := bstep (se 2 (by rfl) ⟨26265849, by rfl⟩ : syracuseStep 70042265 = 52531699) B52531699
theorem B46694843 : Blo 2157435 46694843 := bstep (se 1 (by rfl) ⟨35021132, by rfl⟩ : syracuseStep 46694843 = 70042265) B70042265
theorem B31129895 : Blo 2157435 31129895 := bstep (se 1 (by rfl) ⟨23347421, by rfl⟩ : syracuseStep 31129895 = 46694843) B46694843
theorem B20753263 : Blo 2157435 20753263 := bstep (se 1 (by rfl) ⟨15564947, by rfl⟩ : syracuseStep 20753263 = 31129895) B31129895
theorem B27671017 : Blo 2157435 27671017 := bstep (se 2 (by rfl) ⟨10376631, by rfl⟩ : syracuseStep 27671017 = 20753263) B20753263
theorem B36894689 : Blo 2157435 36894689 := bstep (se 2 (by rfl) ⟨13835508, by rfl⟩ : syracuseStep 36894689 = 27671017) B27671017
theorem B24596459 : Blo 2157435 24596459 := bstep (se 1 (by rfl) ⟨18447344, by rfl⟩ : syracuseStep 24596459 = 36894689) B36894689
theorem B16397639 : Blo 2157435 16397639 := bstep (se 1 (by rfl) ⟨12298229, by rfl⟩ : syracuseStep 16397639 = 24596459) B24596459
theorem B10931759 : Blo 2157435 10931759 := bstep (se 1 (by rfl) ⟨8198819, by rfl⟩ : syracuseStep 10931759 = 16397639) B16397639
theorem B7287839 : Blo 2157435 7287839 := bstep (se 1 (by rfl) ⟨5465879, by rfl⟩ : syracuseStep 7287839 = 10931759) B10931759
theorem B4858559 : Blo 2157435 4858559 := bstep (se 1 (by rfl) ⟨3643919, by rfl⟩ : syracuseStep 4858559 = 7287839) B7287839
theorem B3239039 : Blo 2157435 3239039 := bstep (se 1 (by rfl) ⟨2429279, by rfl⟩ : syracuseStep 3239039 = 4858559) B4858559
theorem B2159359 : Blo 2157435 2159359 := bstep (se 1 (by rfl) ⟨1619519, by rfl⟩ : syracuseStep 2159359 = 3239039) B3239039
theorem B3239045 : Blo 2157435 3239045 := bbase (se 4 (by rfl) ⟨303660, by rfl⟩ : syracuseStep 3239045 = 607321) (by norm_num)
theorem B2159363 : Blo 2157435 2159363 := bstep (se 1 (by rfl) ⟨1619522, by rfl⟩ : syracuseStep 2159363 = 3239045) B3239045
theorem B3643933 : Blo 2157435 3643933 := bbase (se 3 (by rfl) ⟨683237, by rfl⟩ : syracuseStep 3643933 = 1366475) (by norm_num)
theorem B4858577 : Blo 2157435 4858577 := bstep (se 2 (by rfl) ⟨1821966, by rfl⟩ : syracuseStep 4858577 = 3643933) B3643933
theorem B3239051 : Blo 2157435 3239051 := bstep (se 1 (by rfl) ⟨2429288, by rfl⟩ : syracuseStep 3239051 = 4858577) B4858577
theorem B2159367 : Blo 2157435 2159367 := bstep (se 1 (by rfl) ⟨1619525, by rfl⟩ : syracuseStep 2159367 = 3239051) B3239051
theorem B2429293 : Blo 2157435 2429293 := bbase (se 3 (by rfl) ⟨455492, by rfl⟩ : syracuseStep 2429293 = 910985) (by norm_num)
theorem B3239057 : Blo 2157435 3239057 := bstep (se 2 (by rfl) ⟨1214646, by rfl⟩ : syracuseStep 3239057 = 2429293) B2429293
theorem B2159371 : Blo 2157435 2159371 := bstep (se 1 (by rfl) ⟨1619528, by rfl⟩ : syracuseStep 2159371 = 3239057) B3239057
theorem B7287893 : Blo 2157435 7287893 := bbase (se 8 (by rfl) ⟨42702, by rfl⟩ : syracuseStep 7287893 = 85405) (by norm_num)
theorem B4858595 : Blo 2157435 4858595 := bstep (se 1 (by rfl) ⟨3643946, by rfl⟩ : syracuseStep 4858595 = 7287893) B7287893
theorem B3239063 : Blo 2157435 3239063 := bstep (se 1 (by rfl) ⟨2429297, by rfl⟩ : syracuseStep 3239063 = 4858595) B4858595
theorem B2159375 : Blo 2157435 2159375 := bstep (se 1 (by rfl) ⟨1619531, by rfl⟩ : syracuseStep 2159375 = 3239063) B3239063
theorem B3239069 : Blo 2157435 3239069 := bbase (se 3 (by rfl) ⟨607325, by rfl⟩ : syracuseStep 3239069 = 1214651) (by norm_num)
theorem B2159379 : Blo 2157435 2159379 := bstep (se 1 (by rfl) ⟨1619534, by rfl⟩ : syracuseStep 2159379 = 3239069) B3239069
theorem B4858613 : Blo 2157435 4858613 := bbase (se 5 (by rfl) ⟨227747, by rfl⟩ : syracuseStep 4858613 = 455495) (by norm_num)
theorem B3239075 : Blo 2157435 3239075 := bstep (se 1 (by rfl) ⟨2429306, by rfl⟩ : syracuseStep 3239075 = 4858613) B4858613
theorem B2159383 : Blo 2157435 2159383 := bstep (se 1 (by rfl) ⟨1619537, by rfl⟩ : syracuseStep 2159383 = 3239075) B3239075
theorem B27671381 : Blo 2157435 27671381 := bbase (se 9 (by rfl) ⟨81068, by rfl⟩ : syracuseStep 27671381 = 162137) (by norm_num)
theorem B18447587 : Blo 2157435 18447587 := bstep (se 1 (by rfl) ⟨13835690, by rfl⟩ : syracuseStep 18447587 = 27671381) B27671381
theorem B12298391 : Blo 2157435 12298391 := bstep (se 1 (by rfl) ⟨9223793, by rfl⟩ : syracuseStep 12298391 = 18447587) B18447587
theorem B8198927 : Blo 2157435 8198927 := bstep (se 1 (by rfl) ⟨6149195, by rfl⟩ : syracuseStep 8198927 = 12298391) B12298391
theorem B5465951 : Blo 2157435 5465951 := bstep (se 1 (by rfl) ⟨4099463, by rfl⟩ : syracuseStep 5465951 = 8198927) B8198927
theorem B3643967 : Blo 2157435 3643967 := bstep (se 1 (by rfl) ⟨2732975, by rfl⟩ : syracuseStep 3643967 = 5465951) B5465951
theorem B2429311 : Blo 2157435 2429311 := bstep (se 1 (by rfl) ⟨1821983, by rfl⟩ : syracuseStep 2429311 = 3643967) B3643967
theorem B3239081 : Blo 2157435 3239081 := bstep (se 2 (by rfl) ⟨1214655, by rfl⟩ : syracuseStep 3239081 = 2429311) B2429311
theorem B2159387 : Blo 2157435 2159387 := bstep (se 1 (by rfl) ⟨1619540, by rfl⟩ : syracuseStep 2159387 = 3239081) B3239081
theorem B2594197 : Blo 2157435 2594197 := bbase (se 6 (by rfl) ⟨60801, by rfl⟩ : syracuseStep 2594197 = 121603) (by norm_num)
theorem B3458929 : Blo 2157435 3458929 := bstep (se 2 (by rfl) ⟨1297098, by rfl⟩ : syracuseStep 3458929 = 2594197) B2594197
theorem B4611905 : Blo 2157435 4611905 := bstep (se 2 (by rfl) ⟨1729464, by rfl⟩ : syracuseStep 4611905 = 3458929) B3458929
theorem B3074603 : Blo 2157435 3074603 := bstep (se 1 (by rfl) ⟨2305952, by rfl⟩ : syracuseStep 3074603 = 4611905) B4611905
theorem B8198941 : Blo 2157435 8198941 := bstep (se 3 (by rfl) ⟨1537301, by rfl⟩ : syracuseStep 8198941 = 3074603) B3074603
theorem B10931921 : Blo 2157435 10931921 := bstep (se 2 (by rfl) ⟨4099470, by rfl⟩ : syracuseStep 10931921 = 8198941) B8198941
theorem B7287947 : Blo 2157435 7287947 := bstep (se 1 (by rfl) ⟨5465960, by rfl⟩ : syracuseStep 7287947 = 10931921) B10931921
theorem B4858631 : Blo 2157435 4858631 := bstep (se 1 (by rfl) ⟨3643973, by rfl⟩ : syracuseStep 4858631 = 7287947) B7287947
theorem B3239087 : Blo 2157435 3239087 := bstep (se 1 (by rfl) ⟨2429315, by rfl⟩ : syracuseStep 3239087 = 4858631) B4858631
theorem B2159391 : Blo 2157435 2159391 := bstep (se 1 (by rfl) ⟨1619543, by rfl⟩ : syracuseStep 2159391 = 3239087) B3239087
theorem B3239093 : Blo 2157435 3239093 := bbase (se 5 (by rfl) ⟨151832, by rfl⟩ : syracuseStep 3239093 = 303665) (by norm_num)
theorem B2159395 : Blo 2157435 2159395 := bstep (se 1 (by rfl) ⟨1619546, by rfl⟩ : syracuseStep 2159395 = 3239093) B3239093
theorem B5465981 : Blo 2157435 5465981 := bbase (se 3 (by rfl) ⟨1024871, by rfl⟩ : syracuseStep 5465981 = 2049743) (by norm_num)
theorem B3643987 : Blo 2157435 3643987 := bstep (se 1 (by rfl) ⟨2732990, by rfl⟩ : syracuseStep 3643987 = 5465981) B5465981
theorem B4858649 : Blo 2157435 4858649 := bstep (se 2 (by rfl) ⟨1821993, by rfl⟩ : syracuseStep 4858649 = 3643987) B3643987
theorem B3239099 : Blo 2157435 3239099 := bstep (se 1 (by rfl) ⟨2429324, by rfl⟩ : syracuseStep 3239099 = 4858649) B4858649
theorem B2159399 : Blo 2157435 2159399 := bstep (se 1 (by rfl) ⟨1619549, by rfl⟩ : syracuseStep 2159399 = 3239099) B3239099
theorem B2429329 : Blo 2157435 2429329 := bbase (se 2 (by rfl) ⟨910998, by rfl⟩ : syracuseStep 2429329 = 1821997) (by norm_num)
theorem B3239105 : Blo 2157435 3239105 := bstep (se 2 (by rfl) ⟨1214664, by rfl⟩ : syracuseStep 3239105 = 2429329) B2429329
theorem B2159403 : Blo 2157435 2159403 := bstep (se 1 (by rfl) ⟨1619552, by rfl⟩ : syracuseStep 2159403 = 3239105) B3239105
theorem B4099501 : Blo 2157435 4099501 := bbase (se 3 (by rfl) ⟨768656, by rfl⟩ : syracuseStep 4099501 = 1537313) (by norm_num)
theorem B5466001 : Blo 2157435 5466001 := bstep (se 2 (by rfl) ⟨2049750, by rfl⟩ : syracuseStep 5466001 = 4099501) B4099501
theorem B7288001 : Blo 2157435 7288001 := bstep (se 2 (by rfl) ⟨2733000, by rfl⟩ : syracuseStep 7288001 = 5466001) B5466001
theorem B4858667 : Blo 2157435 4858667 := bstep (se 1 (by rfl) ⟨3644000, by rfl⟩ : syracuseStep 4858667 = 7288001) B7288001
theorem B3239111 : Blo 2157435 3239111 := bstep (se 1 (by rfl) ⟨2429333, by rfl⟩ : syracuseStep 3239111 = 4858667) B4858667
theorem B2159407 : Blo 2157435 2159407 := bstep (se 1 (by rfl) ⟨1619555, by rfl⟩ : syracuseStep 2159407 = 3239111) B3239111
theorem B3239117 : Blo 2157435 3239117 := bbase (se 3 (by rfl) ⟨607334, by rfl⟩ : syracuseStep 3239117 = 1214669) (by norm_num)
theorem B2159411 : Blo 2157435 2159411 := bstep (se 1 (by rfl) ⟨1619558, by rfl⟩ : syracuseStep 2159411 = 3239117) B3239117
theorem B4858685 : Blo 2157435 4858685 := bbase (se 3 (by rfl) ⟨911003, by rfl⟩ : syracuseStep 4858685 = 1822007) (by norm_num)
theorem B3239123 : Blo 2157435 3239123 := bstep (se 1 (by rfl) ⟨2429342, by rfl⟩ : syracuseStep 3239123 = 4858685) B4858685
theorem B2159415 : Blo 2157435 2159415 := bstep (se 1 (by rfl) ⟨1619561, by rfl⟩ : syracuseStep 2159415 = 3239123) B3239123
theorem B3644021 : Blo 2157435 3644021 := bbase (se 5 (by rfl) ⟨170813, by rfl⟩ : syracuseStep 3644021 = 341627) (by norm_num)
theorem B2429347 : Blo 2157435 2429347 := bstep (se 1 (by rfl) ⟨1822010, by rfl⟩ : syracuseStep 2429347 = 3644021) B3644021
theorem B3239129 : Blo 2157435 3239129 := bstep (se 2 (by rfl) ⟨1214673, by rfl⟩ : syracuseStep 3239129 = 2429347) B2429347
theorem B2159419 : Blo 2157435 2159419 := bstep (se 1 (by rfl) ⟨1619564, by rfl⟩ : syracuseStep 2159419 = 3239129) B3239129
theorem B4611973 : Blo 2157435 4611973 := bbase (se 4 (by rfl) ⟨432372, by rfl⟩ : syracuseStep 4611973 = 864745) (by norm_num)
theorem B6149297 : Blo 2157435 6149297 := bstep (se 2 (by rfl) ⟨2305986, by rfl⟩ : syracuseStep 6149297 = 4611973) B4611973
theorem B16398125 : Blo 2157435 16398125 := bstep (se 3 (by rfl) ⟨3074648, by rfl⟩ : syracuseStep 16398125 = 6149297) B6149297
theorem B10932083 : Blo 2157435 10932083 := bstep (se 1 (by rfl) ⟨8199062, by rfl⟩ : syracuseStep 10932083 = 16398125) B16398125
theorem B7288055 : Blo 2157435 7288055 := bstep (se 1 (by rfl) ⟨5466041, by rfl⟩ : syracuseStep 7288055 = 10932083) B10932083
theorem B4858703 : Blo 2157435 4858703 := bstep (se 1 (by rfl) ⟨3644027, by rfl⟩ : syracuseStep 4858703 = 7288055) B7288055
theorem B3239135 : Blo 2157435 3239135 := bstep (se 1 (by rfl) ⟨2429351, by rfl⟩ : syracuseStep 3239135 = 4858703) B4858703
theorem B2159423 : Blo 2157435 2159423 := bstep (se 1 (by rfl) ⟨1619567, by rfl⟩ : syracuseStep 2159423 = 3239135) B3239135
theorem B3239141 : Blo 2157435 3239141 := bbase (se 4 (by rfl) ⟨303669, by rfl⟩ : syracuseStep 3239141 = 607339) (by norm_num)
theorem B2159427 : Blo 2157435 2159427 := bstep (se 1 (by rfl) ⟨1619570, by rfl⟩ : syracuseStep 2159427 = 3239141) B3239141
theorem B10376981 : Blo 2157435 10376981 := bbase (se 6 (by rfl) ⟨243210, by rfl⟩ : syracuseStep 10376981 = 486421) (by norm_num)
theorem B6917987 : Blo 2157435 6917987 := bstep (se 1 (by rfl) ⟨5188490, by rfl⟩ : syracuseStep 6917987 = 10376981) B10376981
theorem B4611991 : Blo 2157435 4611991 := bstep (se 1 (by rfl) ⟨3458993, by rfl⟩ : syracuseStep 4611991 = 6917987) B6917987
theorem B6149321 : Blo 2157435 6149321 := bstep (se 2 (by rfl) ⟨2305995, by rfl⟩ : syracuseStep 6149321 = 4611991) B4611991
theorem B4099547 : Blo 2157435 4099547 := bstep (se 1 (by rfl) ⟨3074660, by rfl⟩ : syracuseStep 4099547 = 6149321) B6149321
theorem B2733031 : Blo 2157435 2733031 := bstep (se 1 (by rfl) ⟨2049773, by rfl⟩ : syracuseStep 2733031 = 4099547) B4099547
theorem B3644041 : Blo 2157435 3644041 := bstep (se 2 (by rfl) ⟨1366515, by rfl⟩ : syracuseStep 3644041 = 2733031) B2733031
theorem B4858721 : Blo 2157435 4858721 := bstep (se 2 (by rfl) ⟨1822020, by rfl⟩ : syracuseStep 4858721 = 3644041) B3644041
theorem B3239147 : Blo 2157435 3239147 := bstep (se 1 (by rfl) ⟨2429360, by rfl⟩ : syracuseStep 3239147 = 4858721) B4858721
theorem B2159431 : Blo 2157435 2159431 := bstep (se 1 (by rfl) ⟨1619573, by rfl⟩ : syracuseStep 2159431 = 3239147) B3239147
theorem B2429365 : Blo 2157435 2429365 := bbase (se 5 (by rfl) ⟨113876, by rfl⟩ : syracuseStep 2429365 = 227753) (by norm_num)
theorem B3239153 : Blo 2157435 3239153 := bstep (se 2 (by rfl) ⟨1214682, by rfl⟩ : syracuseStep 3239153 = 2429365) B2429365
theorem B2159435 : Blo 2157435 2159435 := bstep (se 1 (by rfl) ⟨1619576, by rfl⟩ : syracuseStep 2159435 = 3239153) B3239153
theorem C0 (j : ℕ) (h1 : 539358 ≤ j) (h2 : j ≤ 539858) : Blo 2157435 (4 * j + 3) := by
  interval_cases j
  · exact B2157435
  · exact B2157439
  · exact B2157443
  · exact B2157447
  · exact B2157451
  · exact B2157455
  · exact B2157459
  · exact B2157463
  · exact B2157467
  · exact B2157471
  · exact B2157475
  · exact B2157479
  · exact B2157483
  · exact B2157487
  · exact B2157491
  · exact B2157495
  · exact B2157499
  · exact B2157503
  · exact B2157507
  · exact B2157511
  · exact B2157515
  · exact B2157519
  · exact B2157523
  · exact B2157527
  · exact B2157531
  · exact B2157535
  · exact B2157539
  · exact B2157543
  · exact B2157547
  · exact B2157551
  · exact B2157555
  · exact B2157559
  · exact B2157563
  · exact B2157567
  · exact B2157571
  · exact B2157575
  · exact B2157579
  · exact B2157583
  · exact B2157587
  · exact B2157591
  · exact B2157595
  · exact B2157599
  · exact B2157603
  · exact B2157607
  · exact B2157611
  · exact B2157615
  · exact B2157619
  · exact B2157623
  · exact B2157627
  · exact B2157631
  · exact B2157635
  · exact B2157639
  · exact B2157643
  · exact B2157647
  · exact B2157651
  · exact B2157655
  · exact B2157659
  · exact B2157663
  · exact B2157667
  · exact B2157671
  · exact B2157675
  · exact B2157679
  · exact B2157683
  · exact B2157687
  · exact B2157691
  · exact B2157695
  · exact B2157699
  · exact B2157703
  · exact B2157707
  · exact B2157711
  · exact B2157715
  · exact B2157719
  · exact B2157723
  · exact B2157727
  · exact B2157731
  · exact B2157735
  · exact B2157739
  · exact B2157743
  · exact B2157747
  · exact B2157751
  · exact B2157755
  · exact B2157759
  · exact B2157763
  · exact B2157767
  · exact B2157771
  · exact B2157775
  · exact B2157779
  · exact B2157783
  · exact B2157787
  · exact B2157791
  · exact B2157795
  · exact B2157799
  · exact B2157803
  · exact B2157807
  · exact B2157811
  · exact B2157815
  · exact B2157819
  · exact B2157823
  · exact B2157827
  · exact B2157831
  · exact B2157835
  · exact B2157839
  · exact B2157843
  · exact B2157847
  · exact B2157851
  · exact B2157855
  · exact B2157859
  · exact B2157863
  · exact B2157867
  · exact B2157871
  · exact B2157875
  · exact B2157879
  · exact B2157883
  · exact B2157887
  · exact B2157891
  · exact B2157895
  · exact B2157899
  · exact B2157903
  · exact B2157907
  · exact B2157911
  · exact B2157915
  · exact B2157919
  · exact B2157923
  · exact B2157927
  · exact B2157931
  · exact B2157935
  · exact B2157939
  · exact B2157943
  · exact B2157947
  · exact B2157951
  · exact B2157955
  · exact B2157959
  · exact B2157963
  · exact B2157967
  · exact B2157971
  · exact B2157975
  · exact B2157979
  · exact B2157983
  · exact B2157987
  · exact B2157991
  · exact B2157995
  · exact B2157999
  · exact B2158003
  · exact B2158007
  · exact B2158011
  · exact B2158015
  · exact B2158019
  · exact B2158023
  · exact B2158027
  · exact B2158031
  · exact B2158035
  · exact B2158039
  · exact B2158043
  · exact B2158047
  · exact B2158051
  · exact B2158055
  · exact B2158059
  · exact B2158063
  · exact B2158067
  · exact B2158071
  · exact B2158075
  · exact B2158079
  · exact B2158083
  · exact B2158087
  · exact B2158091
  · exact B2158095
  · exact B2158099
  · exact B2158103
  · exact B2158107
  · exact B2158111
  · exact B2158115
  · exact B2158119
  · exact B2158123
  · exact B2158127
  · exact B2158131
  · exact B2158135
  · exact B2158139
  · exact B2158143
  · exact B2158147
  · exact B2158151
  · exact B2158155
  · exact B2158159
  · exact B2158163
  · exact B2158167
  · exact B2158171
  · exact B2158175
  · exact B2158179
  · exact B2158183
  · exact B2158187
  · exact B2158191
  · exact B2158195
  · exact B2158199
  · exact B2158203
  · exact B2158207
  · exact B2158211
  · exact B2158215
  · exact B2158219
  · exact B2158223
  · exact B2158227
  · exact B2158231
  · exact B2158235
  · exact B2158239
  · exact B2158243
  · exact B2158247
  · exact B2158251
  · exact B2158255
  · exact B2158259
  · exact B2158263
  · exact B2158267
  · exact B2158271
  · exact B2158275
  · exact B2158279
  · exact B2158283
  · exact B2158287
  · exact B2158291
  · exact B2158295
  · exact B2158299
  · exact B2158303
  · exact B2158307
  · exact B2158311
  · exact B2158315
  · exact B2158319
  · exact B2158323
  · exact B2158327
  · exact B2158331
  · exact B2158335
  · exact B2158339
  · exact B2158343
  · exact B2158347
  · exact B2158351
  · exact B2158355
  · exact B2158359
  · exact B2158363
  · exact B2158367
  · exact B2158371
  · exact B2158375
  · exact B2158379
  · exact B2158383
  · exact B2158387
  · exact B2158391
  · exact B2158395
  · exact B2158399
  · exact B2158403
  · exact B2158407
  · exact B2158411
  · exact B2158415
  · exact B2158419
  · exact B2158423
  · exact B2158427
  · exact B2158431
  · exact B2158435
  · exact B2158439
  · exact B2158443
  · exact B2158447
  · exact B2158451
  · exact B2158455
  · exact B2158459
  · exact B2158463
  · exact B2158467
  · exact B2158471
  · exact B2158475
  · exact B2158479
  · exact B2158483
  · exact B2158487
  · exact B2158491
  · exact B2158495
  · exact B2158499
  · exact B2158503
  · exact B2158507
  · exact B2158511
  · exact B2158515
  · exact B2158519
  · exact B2158523
  · exact B2158527
  · exact B2158531
  · exact B2158535
  · exact B2158539
  · exact B2158543
  · exact B2158547
  · exact B2158551
  · exact B2158555
  · exact B2158559
  · exact B2158563
  · exact B2158567
  · exact B2158571
  · exact B2158575
  · exact B2158579
  · exact B2158583
  · exact B2158587
  · exact B2158591
  · exact B2158595
  · exact B2158599
  · exact B2158603
  · exact B2158607
  · exact B2158611
  · exact B2158615
  · exact B2158619
  · exact B2158623
  · exact B2158627
  · exact B2158631
  · exact B2158635
  · exact B2158639
  · exact B2158643
  · exact B2158647
  · exact B2158651
  · exact B2158655
  · exact B2158659
  · exact B2158663
  · exact B2158667
  · exact B2158671
  · exact B2158675
  · exact B2158679
  · exact B2158683
  · exact B2158687
  · exact B2158691
  · exact B2158695
  · exact B2158699
  · exact B2158703
  · exact B2158707
  · exact B2158711
  · exact B2158715
  · exact B2158719
  · exact B2158723
  · exact B2158727
  · exact B2158731
  · exact B2158735
  · exact B2158739
  · exact B2158743
  · exact B2158747
  · exact B2158751
  · exact B2158755
  · exact B2158759
  · exact B2158763
  · exact B2158767
  · exact B2158771
  · exact B2158775
  · exact B2158779
  · exact B2158783
  · exact B2158787
  · exact B2158791
  · exact B2158795
  · exact B2158799
  · exact B2158803
  · exact B2158807
  · exact B2158811
  · exact B2158815
  · exact B2158819
  · exact B2158823
  · exact B2158827
  · exact B2158831
  · exact B2158835
  · exact B2158839
  · exact B2158843
  · exact B2158847
  · exact B2158851
  · exact B2158855
  · exact B2158859
  · exact B2158863
  · exact B2158867
  · exact B2158871
  · exact B2158875
  · exact B2158879
  · exact B2158883
  · exact B2158887
  · exact B2158891
  · exact B2158895
  · exact B2158899
  · exact B2158903
  · exact B2158907
  · exact B2158911
  · exact B2158915
  · exact B2158919
  · exact B2158923
  · exact B2158927
  · exact B2158931
  · exact B2158935
  · exact B2158939
  · exact B2158943
  · exact B2158947
  · exact B2158951
  · exact B2158955
  · exact B2158959
  · exact B2158963
  · exact B2158967
  · exact B2158971
  · exact B2158975
  · exact B2158979
  · exact B2158983
  · exact B2158987
  · exact B2158991
  · exact B2158995
  · exact B2158999
  · exact B2159003
  · exact B2159007
  · exact B2159011
  · exact B2159015
  · exact B2159019
  · exact B2159023
  · exact B2159027
  · exact B2159031
  · exact B2159035
  · exact B2159039
  · exact B2159043
  · exact B2159047
  · exact B2159051
  · exact B2159055
  · exact B2159059
  · exact B2159063
  · exact B2159067
  · exact B2159071
  · exact B2159075
  · exact B2159079
  · exact B2159083
  · exact B2159087
  · exact B2159091
  · exact B2159095
  · exact B2159099
  · exact B2159103
  · exact B2159107
  · exact B2159111
  · exact B2159115
  · exact B2159119
  · exact B2159123
  · exact B2159127
  · exact B2159131
  · exact B2159135
  · exact B2159139
  · exact B2159143
  · exact B2159147
  · exact B2159151
  · exact B2159155
  · exact B2159159
  · exact B2159163
  · exact B2159167
  · exact B2159171
  · exact B2159175
  · exact B2159179
  · exact B2159183
  · exact B2159187
  · exact B2159191
  · exact B2159195
  · exact B2159199
  · exact B2159203
  · exact B2159207
  · exact B2159211
  · exact B2159215
  · exact B2159219
  · exact B2159223
  · exact B2159227
  · exact B2159231
  · exact B2159235
  · exact B2159239
  · exact B2159243
  · exact B2159247
  · exact B2159251
  · exact B2159255
  · exact B2159259
  · exact B2159263
  · exact B2159267
  · exact B2159271
  · exact B2159275
  · exact B2159279
  · exact B2159283
  · exact B2159287
  · exact B2159291
  · exact B2159295
  · exact B2159299
  · exact B2159303
  · exact B2159307
  · exact B2159311
  · exact B2159315
  · exact B2159319
  · exact B2159323
  · exact B2159327
  · exact B2159331
  · exact B2159335
  · exact B2159339
  · exact B2159343
  · exact B2159347
  · exact B2159351
  · exact B2159355
  · exact B2159359
  · exact B2159363
  · exact B2159367
  · exact B2159371
  · exact B2159375
  · exact B2159379
  · exact B2159383
  · exact B2159387
  · exact B2159391
  · exact B2159395
  · exact B2159399
  · exact B2159403
  · exact B2159407
  · exact B2159411
  · exact B2159415
  · exact B2159419
  · exact B2159423
  · exact B2159427
  · exact B2159431
  · exact B2159435
theorem solution (m : ℕ) (hlo : 2157435 ≤ m) (hhi : m ≤ 2159435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 539358 ≤ j := by omega
    have hj2 : j ≤ 539858 := by omega
    have hb : Blo 2157435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
