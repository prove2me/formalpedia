-- Prove2me | solution 1 for syracuse_descends_range_1987435_1989435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:20.906853+00:00
-- url     : https://prove2.me/submissions/42f86279-5647-409c-a499-018c8dc63dfa

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

theorem B2235865 : Blo 1987435 2235865 := bbase (se 2 (by rfl) ⟨838449, by rfl⟩ : syracuseStep 2235865 = 1676899) (by norm_num)
theorem B2981153 : Blo 1987435 2981153 := bstep (se 2 (by rfl) ⟨1117932, by rfl⟩ : syracuseStep 2981153 = 2235865) B2235865
theorem B1987435 : Blo 1987435 1987435 := bstep (se 1 (by rfl) ⟨1490576, by rfl⟩ : syracuseStep 1987435 = 2981153) B2981153
theorem B2829773 : Blo 1987435 2829773 := bbase (se 3 (by rfl) ⟨530582, by rfl⟩ : syracuseStep 2829773 = 1061165) (by norm_num)
theorem B7546061 : Blo 1987435 7546061 := bstep (se 3 (by rfl) ⟨1414886, by rfl⟩ : syracuseStep 7546061 = 2829773) B2829773
theorem B5030707 : Blo 1987435 5030707 := bstep (se 1 (by rfl) ⟨3773030, by rfl⟩ : syracuseStep 5030707 = 7546061) B7546061
theorem B6707609 : Blo 1987435 6707609 := bstep (se 2 (by rfl) ⟨2515353, by rfl⟩ : syracuseStep 6707609 = 5030707) B5030707
theorem B4471739 : Blo 1987435 4471739 := bstep (se 1 (by rfl) ⟨3353804, by rfl⟩ : syracuseStep 4471739 = 6707609) B6707609
theorem B2981159 : Blo 1987435 2981159 := bstep (se 1 (by rfl) ⟨2235869, by rfl⟩ : syracuseStep 2981159 = 4471739) B4471739
theorem B1987439 : Blo 1987435 1987439 := bstep (se 1 (by rfl) ⟨1490579, by rfl⟩ : syracuseStep 1987439 = 2981159) B2981159
theorem B2981165 : Blo 1987435 2981165 := bbase (se 3 (by rfl) ⟨558968, by rfl⟩ : syracuseStep 2981165 = 1117937) (by norm_num)
theorem B1987443 : Blo 1987435 1987443 := bstep (se 1 (by rfl) ⟨1490582, by rfl⟩ : syracuseStep 1987443 = 2981165) B2981165
theorem B4471757 : Blo 1987435 4471757 := bbase (se 3 (by rfl) ⟨838454, by rfl⟩ : syracuseStep 4471757 = 1676909) (by norm_num)
theorem B2981171 : Blo 1987435 2981171 := bstep (se 1 (by rfl) ⟨2235878, by rfl⟩ : syracuseStep 2981171 = 4471757) B4471757
theorem B1987447 : Blo 1987435 1987447 := bstep (se 1 (by rfl) ⟨1490585, by rfl⟩ : syracuseStep 1987447 = 2981171) B2981171
theorem B2515369 : Blo 1987435 2515369 := bbase (se 2 (by rfl) ⟨943263, by rfl⟩ : syracuseStep 2515369 = 1886527) (by norm_num)
theorem B3353825 : Blo 1987435 3353825 := bstep (se 2 (by rfl) ⟨1257684, by rfl⟩ : syracuseStep 3353825 = 2515369) B2515369
theorem B2235883 : Blo 1987435 2235883 := bstep (se 1 (by rfl) ⟨1676912, by rfl⟩ : syracuseStep 2235883 = 3353825) B3353825
theorem B2981177 : Blo 1987435 2981177 := bstep (se 2 (by rfl) ⟨1117941, by rfl⟩ : syracuseStep 2981177 = 2235883) B2235883
theorem B1987451 : Blo 1987435 1987451 := bstep (se 1 (by rfl) ⟨1490588, by rfl⟩ : syracuseStep 1987451 = 2981177) B2981177
theorem B14521301 : Blo 1987435 14521301 := bbase (se 7 (by rfl) ⟨170171, by rfl⟩ : syracuseStep 14521301 = 340343) (by norm_num)
theorem B9680867 : Blo 1987435 9680867 := bstep (se 1 (by rfl) ⟨7260650, by rfl⟩ : syracuseStep 9680867 = 14521301) B14521301
theorem B6453911 : Blo 1987435 6453911 := bstep (se 1 (by rfl) ⟨4840433, by rfl⟩ : syracuseStep 6453911 = 9680867) B9680867
theorem B4302607 : Blo 1987435 4302607 := bstep (se 1 (by rfl) ⟨3226955, by rfl⟩ : syracuseStep 4302607 = 6453911) B6453911
theorem B5736809 : Blo 1987435 5736809 := bstep (se 2 (by rfl) ⟨2151303, by rfl⟩ : syracuseStep 5736809 = 4302607) B4302607
theorem B3824539 : Blo 1987435 3824539 := bstep (se 1 (by rfl) ⟨2868404, by rfl⟩ : syracuseStep 3824539 = 5736809) B5736809
theorem B20397541 : Blo 1987435 20397541 := bstep (se 4 (by rfl) ⟨1912269, by rfl⟩ : syracuseStep 20397541 = 3824539) B3824539
theorem B27196721 : Blo 1987435 27196721 := bstep (se 2 (by rfl) ⟨10198770, by rfl⟩ : syracuseStep 27196721 = 20397541) B20397541
theorem B18131147 : Blo 1987435 18131147 := bstep (se 1 (by rfl) ⟨13598360, by rfl⟩ : syracuseStep 18131147 = 27196721) B27196721
theorem B12087431 : Blo 1987435 12087431 := bstep (se 1 (by rfl) ⟨9065573, by rfl⟩ : syracuseStep 12087431 = 18131147) B18131147
theorem B8058287 : Blo 1987435 8058287 := bstep (se 1 (by rfl) ⟨6043715, by rfl⟩ : syracuseStep 8058287 = 12087431) B12087431
theorem B5372191 : Blo 1987435 5372191 := bstep (se 1 (by rfl) ⟨4029143, by rfl⟩ : syracuseStep 5372191 = 8058287) B8058287
theorem B7162921 : Blo 1987435 7162921 := bstep (se 2 (by rfl) ⟨2686095, by rfl⟩ : syracuseStep 7162921 = 5372191) B5372191
theorem B9550561 : Blo 1987435 9550561 := bstep (se 2 (by rfl) ⟨3581460, by rfl⟩ : syracuseStep 9550561 = 7162921) B7162921
theorem B12734081 : Blo 1987435 12734081 := bstep (se 2 (by rfl) ⟨4775280, by rfl⟩ : syracuseStep 12734081 = 9550561) B9550561
theorem B8489387 : Blo 1987435 8489387 := bstep (se 1 (by rfl) ⟨6367040, by rfl⟩ : syracuseStep 8489387 = 12734081) B12734081
theorem B22638365 : Blo 1987435 22638365 := bstep (se 3 (by rfl) ⟨4244693, by rfl⟩ : syracuseStep 22638365 = 8489387) B8489387
theorem B15092243 : Blo 1987435 15092243 := bstep (se 1 (by rfl) ⟨11319182, by rfl⟩ : syracuseStep 15092243 = 22638365) B22638365
theorem B10061495 : Blo 1987435 10061495 := bstep (se 1 (by rfl) ⟨7546121, by rfl⟩ : syracuseStep 10061495 = 15092243) B15092243
theorem B6707663 : Blo 1987435 6707663 := bstep (se 1 (by rfl) ⟨5030747, by rfl⟩ : syracuseStep 6707663 = 10061495) B10061495
theorem B4471775 : Blo 1987435 4471775 := bstep (se 1 (by rfl) ⟨3353831, by rfl⟩ : syracuseStep 4471775 = 6707663) B6707663
theorem B2981183 : Blo 1987435 2981183 := bstep (se 1 (by rfl) ⟨2235887, by rfl⟩ : syracuseStep 2981183 = 4471775) B4471775
theorem B1987455 : Blo 1987435 1987455 := bstep (se 1 (by rfl) ⟨1490591, by rfl⟩ : syracuseStep 1987455 = 2981183) B2981183
theorem B2981189 : Blo 1987435 2981189 := bbase (se 4 (by rfl) ⟨279486, by rfl⟩ : syracuseStep 2981189 = 558973) (by norm_num)
theorem B1987459 : Blo 1987435 1987459 := bstep (se 1 (by rfl) ⟨1490594, by rfl⟩ : syracuseStep 1987459 = 2981189) B2981189
theorem B3353845 : Blo 1987435 3353845 := bbase (se 5 (by rfl) ⟨157211, by rfl⟩ : syracuseStep 3353845 = 314423) (by norm_num)
theorem B4471793 : Blo 1987435 4471793 := bstep (se 2 (by rfl) ⟨1676922, by rfl⟩ : syracuseStep 4471793 = 3353845) B3353845
theorem B2981195 : Blo 1987435 2981195 := bstep (se 1 (by rfl) ⟨2235896, by rfl⟩ : syracuseStep 2981195 = 4471793) B4471793
theorem B1987463 : Blo 1987435 1987463 := bstep (se 1 (by rfl) ⟨1490597, by rfl⟩ : syracuseStep 1987463 = 2981195) B2981195
theorem B2235901 : Blo 1987435 2235901 := bbase (se 3 (by rfl) ⟨419231, by rfl⟩ : syracuseStep 2235901 = 838463) (by norm_num)
theorem B2981201 : Blo 1987435 2981201 := bstep (se 2 (by rfl) ⟨1117950, by rfl⟩ : syracuseStep 2981201 = 2235901) B2235901
theorem B1987467 : Blo 1987435 1987467 := bstep (se 1 (by rfl) ⟨1490600, by rfl⟩ : syracuseStep 1987467 = 2981201) B2981201
theorem B6707717 : Blo 1987435 6707717 := bbase (se 4 (by rfl) ⟨628848, by rfl⟩ : syracuseStep 6707717 = 1257697) (by norm_num)
theorem B4471811 : Blo 1987435 4471811 := bstep (se 1 (by rfl) ⟨3353858, by rfl⟩ : syracuseStep 4471811 = 6707717) B6707717
theorem B2981207 : Blo 1987435 2981207 := bstep (se 1 (by rfl) ⟨2235905, by rfl⟩ : syracuseStep 2981207 = 4471811) B4471811
theorem B1987471 : Blo 1987435 1987471 := bstep (se 1 (by rfl) ⟨1490603, by rfl⟩ : syracuseStep 1987471 = 2981207) B2981207
theorem B2981213 : Blo 1987435 2981213 := bbase (se 3 (by rfl) ⟨558977, by rfl⟩ : syracuseStep 2981213 = 1117955) (by norm_num)
theorem B1987475 : Blo 1987435 1987475 := bstep (se 1 (by rfl) ⟨1490606, by rfl⟩ : syracuseStep 1987475 = 2981213) B2981213
theorem B4471829 : Blo 1987435 4471829 := bbase (se 6 (by rfl) ⟨104808, by rfl⟩ : syracuseStep 4471829 = 209617) (by norm_num)
theorem B2981219 : Blo 1987435 2981219 := bstep (se 1 (by rfl) ⟨2235914, by rfl⟩ : syracuseStep 2981219 = 4471829) B4471829
theorem B1987479 : Blo 1987435 1987479 := bstep (se 1 (by rfl) ⟨1490609, by rfl⟩ : syracuseStep 1987479 = 2981219) B2981219
theorem B7546229 : Blo 1987435 7546229 := bbase (se 5 (by rfl) ⟨353729, by rfl⟩ : syracuseStep 7546229 = 707459) (by norm_num)
theorem B5030819 : Blo 1987435 5030819 := bstep (se 1 (by rfl) ⟨3773114, by rfl⟩ : syracuseStep 5030819 = 7546229) B7546229
theorem B3353879 : Blo 1987435 3353879 := bstep (se 1 (by rfl) ⟨2515409, by rfl⟩ : syracuseStep 3353879 = 5030819) B5030819
theorem B2235919 : Blo 1987435 2235919 := bstep (se 1 (by rfl) ⟨1676939, by rfl⟩ : syracuseStep 2235919 = 3353879) B3353879
theorem B2981225 : Blo 1987435 2981225 := bstep (se 2 (by rfl) ⟨1117959, by rfl⟩ : syracuseStep 2981225 = 2235919) B2235919
theorem B1987483 : Blo 1987435 1987483 := bstep (se 1 (by rfl) ⟨1490612, by rfl⟩ : syracuseStep 1987483 = 2981225) B2981225
theorem B2122381 : Blo 1987435 2122381 := bbase (se 3 (by rfl) ⟨397946, by rfl⟩ : syracuseStep 2122381 = 795893) (by norm_num)
theorem B11319365 : Blo 1987435 11319365 := bstep (se 4 (by rfl) ⟨1061190, by rfl⟩ : syracuseStep 11319365 = 2122381) B2122381
theorem B7546243 : Blo 1987435 7546243 := bstep (se 1 (by rfl) ⟨5659682, by rfl⟩ : syracuseStep 7546243 = 11319365) B11319365
theorem B10061657 : Blo 1987435 10061657 := bstep (se 2 (by rfl) ⟨3773121, by rfl⟩ : syracuseStep 10061657 = 7546243) B7546243
theorem B6707771 : Blo 1987435 6707771 := bstep (se 1 (by rfl) ⟨5030828, by rfl⟩ : syracuseStep 6707771 = 10061657) B10061657
theorem B4471847 : Blo 1987435 4471847 := bstep (se 1 (by rfl) ⟨3353885, by rfl⟩ : syracuseStep 4471847 = 6707771) B6707771
theorem B2981231 : Blo 1987435 2981231 := bstep (se 1 (by rfl) ⟨2235923, by rfl⟩ : syracuseStep 2981231 = 4471847) B4471847
theorem B1987487 : Blo 1987435 1987487 := bstep (se 1 (by rfl) ⟨1490615, by rfl⟩ : syracuseStep 1987487 = 2981231) B2981231
theorem B2981237 : Blo 1987435 2981237 := bbase (se 5 (by rfl) ⟨139745, by rfl⟩ : syracuseStep 2981237 = 279491) (by norm_num)
theorem B1987491 : Blo 1987435 1987491 := bstep (se 1 (by rfl) ⟨1490618, by rfl⟩ : syracuseStep 1987491 = 2981237) B2981237
theorem B2829853 : Blo 1987435 2829853 := bbase (se 3 (by rfl) ⟨530597, by rfl⟩ : syracuseStep 2829853 = 1061195) (by norm_num)
theorem B3773137 : Blo 1987435 3773137 := bstep (se 2 (by rfl) ⟨1414926, by rfl⟩ : syracuseStep 3773137 = 2829853) B2829853
theorem B5030849 : Blo 1987435 5030849 := bstep (se 2 (by rfl) ⟨1886568, by rfl⟩ : syracuseStep 5030849 = 3773137) B3773137
theorem B3353899 : Blo 1987435 3353899 := bstep (se 1 (by rfl) ⟨2515424, by rfl⟩ : syracuseStep 3353899 = 5030849) B5030849
theorem B4471865 : Blo 1987435 4471865 := bstep (se 2 (by rfl) ⟨1676949, by rfl⟩ : syracuseStep 4471865 = 3353899) B3353899
theorem B2981243 : Blo 1987435 2981243 := bstep (se 1 (by rfl) ⟨2235932, by rfl⟩ : syracuseStep 2981243 = 4471865) B4471865
theorem B1987495 : Blo 1987435 1987495 := bstep (se 1 (by rfl) ⟨1490621, by rfl⟩ : syracuseStep 1987495 = 2981243) B2981243
theorem B2235937 : Blo 1987435 2235937 := bbase (se 2 (by rfl) ⟨838476, by rfl⟩ : syracuseStep 2235937 = 1676953) (by norm_num)
theorem B2981249 : Blo 1987435 2981249 := bstep (se 2 (by rfl) ⟨1117968, by rfl⟩ : syracuseStep 2981249 = 2235937) B2235937
theorem B1987499 : Blo 1987435 1987499 := bstep (se 1 (by rfl) ⟨1490624, by rfl⟩ : syracuseStep 1987499 = 2981249) B2981249
theorem B5030869 : Blo 1987435 5030869 := bbase (se 7 (by rfl) ⟨58955, by rfl⟩ : syracuseStep 5030869 = 117911) (by norm_num)
theorem B6707825 : Blo 1987435 6707825 := bstep (se 2 (by rfl) ⟨2515434, by rfl⟩ : syracuseStep 6707825 = 5030869) B5030869
theorem B4471883 : Blo 1987435 4471883 := bstep (se 1 (by rfl) ⟨3353912, by rfl⟩ : syracuseStep 4471883 = 6707825) B6707825
theorem B2981255 : Blo 1987435 2981255 := bstep (se 1 (by rfl) ⟨2235941, by rfl⟩ : syracuseStep 2981255 = 4471883) B4471883
theorem B1987503 : Blo 1987435 1987503 := bstep (se 1 (by rfl) ⟨1490627, by rfl⟩ : syracuseStep 1987503 = 2981255) B2981255
theorem B2981261 : Blo 1987435 2981261 := bbase (se 3 (by rfl) ⟨558986, by rfl⟩ : syracuseStep 2981261 = 1117973) (by norm_num)
theorem B1987507 : Blo 1987435 1987507 := bstep (se 1 (by rfl) ⟨1490630, by rfl⟩ : syracuseStep 1987507 = 2981261) B2981261
theorem B4471901 : Blo 1987435 4471901 := bbase (se 3 (by rfl) ⟨838481, by rfl⟩ : syracuseStep 4471901 = 1676963) (by norm_num)
theorem B2981267 : Blo 1987435 2981267 := bstep (se 1 (by rfl) ⟨2235950, by rfl⟩ : syracuseStep 2981267 = 4471901) B4471901
theorem B1987511 : Blo 1987435 1987511 := bstep (se 1 (by rfl) ⟨1490633, by rfl⟩ : syracuseStep 1987511 = 2981267) B2981267
theorem B3353933 : Blo 1987435 3353933 := bbase (se 3 (by rfl) ⟨628862, by rfl⟩ : syracuseStep 3353933 = 1257725) (by norm_num)
theorem B2235955 : Blo 1987435 2235955 := bstep (se 1 (by rfl) ⟨1676966, by rfl⟩ : syracuseStep 2235955 = 3353933) B3353933
theorem B2981273 : Blo 1987435 2981273 := bstep (se 2 (by rfl) ⟨1117977, by rfl⟩ : syracuseStep 2981273 = 2235955) B2235955
theorem B1987515 : Blo 1987435 1987515 := bstep (se 1 (by rfl) ⟨1490636, by rfl⟩ : syracuseStep 1987515 = 2981273) B2981273
theorem B6454117 : Blo 1987435 6454117 := bbase (se 4 (by rfl) ⟨605073, by rfl⟩ : syracuseStep 6454117 = 1210147) (by norm_num)
theorem B8605489 : Blo 1987435 8605489 := bstep (se 2 (by rfl) ⟨3227058, by rfl⟩ : syracuseStep 8605489 = 6454117) B6454117
theorem B11473985 : Blo 1987435 11473985 := bstep (se 2 (by rfl) ⟨4302744, by rfl⟩ : syracuseStep 11473985 = 8605489) B8605489
theorem B7649323 : Blo 1987435 7649323 := bstep (se 1 (by rfl) ⟨5736992, by rfl⟩ : syracuseStep 7649323 = 11473985) B11473985
theorem B40796389 : Blo 1987435 40796389 := bstep (se 4 (by rfl) ⟨3824661, by rfl⟩ : syracuseStep 40796389 = 7649323) B7649323
theorem B54395185 : Blo 1987435 54395185 := bstep (se 2 (by rfl) ⟨20398194, by rfl⟩ : syracuseStep 54395185 = 40796389) B40796389
theorem B72526913 : Blo 1987435 72526913 := bstep (se 2 (by rfl) ⟨27197592, by rfl⟩ : syracuseStep 72526913 = 54395185) B54395185
theorem B48351275 : Blo 1987435 48351275 := bstep (se 1 (by rfl) ⟨36263456, by rfl⟩ : syracuseStep 48351275 = 72526913) B72526913
theorem B32234183 : Blo 1987435 32234183 := bstep (se 1 (by rfl) ⟨24175637, by rfl⟩ : syracuseStep 32234183 = 48351275) B48351275
theorem B21489455 : Blo 1987435 21489455 := bstep (se 1 (by rfl) ⟨16117091, by rfl⟩ : syracuseStep 21489455 = 32234183) B32234183
theorem B14326303 : Blo 1987435 14326303 := bstep (se 1 (by rfl) ⟨10744727, by rfl⟩ : syracuseStep 14326303 = 21489455) B21489455
theorem B19101737 : Blo 1987435 19101737 := bstep (se 2 (by rfl) ⟨7163151, by rfl⟩ : syracuseStep 19101737 = 14326303) B14326303
theorem B12734491 : Blo 1987435 12734491 := bstep (se 1 (by rfl) ⟨9550868, by rfl⟩ : syracuseStep 12734491 = 19101737) B19101737
theorem B16979321 : Blo 1987435 16979321 := bstep (se 2 (by rfl) ⟨6367245, by rfl⟩ : syracuseStep 16979321 = 12734491) B12734491
theorem B11319547 : Blo 1987435 11319547 := bstep (se 1 (by rfl) ⟨8489660, by rfl⟩ : syracuseStep 11319547 = 16979321) B16979321
theorem B15092729 : Blo 1987435 15092729 := bstep (se 2 (by rfl) ⟨5659773, by rfl⟩ : syracuseStep 15092729 = 11319547) B11319547
theorem B10061819 : Blo 1987435 10061819 := bstep (se 1 (by rfl) ⟨7546364, by rfl⟩ : syracuseStep 10061819 = 15092729) B15092729
theorem B6707879 : Blo 1987435 6707879 := bstep (se 1 (by rfl) ⟨5030909, by rfl⟩ : syracuseStep 6707879 = 10061819) B10061819
theorem B4471919 : Blo 1987435 4471919 := bstep (se 1 (by rfl) ⟨3353939, by rfl⟩ : syracuseStep 4471919 = 6707879) B6707879
theorem B2981279 : Blo 1987435 2981279 := bstep (se 1 (by rfl) ⟨2235959, by rfl⟩ : syracuseStep 2981279 = 4471919) B4471919
theorem B1987519 : Blo 1987435 1987519 := bstep (se 1 (by rfl) ⟨1490639, by rfl⟩ : syracuseStep 1987519 = 2981279) B2981279
theorem B2981285 : Blo 1987435 2981285 := bbase (se 4 (by rfl) ⟨279495, by rfl⟩ : syracuseStep 2981285 = 558991) (by norm_num)
theorem B1987523 : Blo 1987435 1987523 := bstep (se 1 (by rfl) ⟨1490642, by rfl⟩ : syracuseStep 1987523 = 2981285) B2981285
theorem B2515465 : Blo 1987435 2515465 := bbase (se 2 (by rfl) ⟨943299, by rfl⟩ : syracuseStep 2515465 = 1886599) (by norm_num)
theorem B3353953 : Blo 1987435 3353953 := bstep (se 2 (by rfl) ⟨1257732, by rfl⟩ : syracuseStep 3353953 = 2515465) B2515465
theorem B4471937 : Blo 1987435 4471937 := bstep (se 2 (by rfl) ⟨1676976, by rfl⟩ : syracuseStep 4471937 = 3353953) B3353953
theorem B2981291 : Blo 1987435 2981291 := bstep (se 1 (by rfl) ⟨2235968, by rfl⟩ : syracuseStep 2981291 = 4471937) B4471937
theorem B1987527 : Blo 1987435 1987527 := bstep (se 1 (by rfl) ⟨1490645, by rfl⟩ : syracuseStep 1987527 = 2981291) B2981291
theorem B2235973 : Blo 1987435 2235973 := bbase (se 4 (by rfl) ⟨209622, by rfl⟩ : syracuseStep 2235973 = 419245) (by norm_num)
theorem B2981297 : Blo 1987435 2981297 := bstep (se 2 (by rfl) ⟨1117986, by rfl⟩ : syracuseStep 2981297 = 2235973) B2235973
theorem B1987531 : Blo 1987435 1987531 := bstep (se 1 (by rfl) ⟨1490648, by rfl⟩ : syracuseStep 1987531 = 2981297) B2981297
theorem B3773213 : Blo 1987435 3773213 := bbase (se 3 (by rfl) ⟨707477, by rfl⟩ : syracuseStep 3773213 = 1414955) (by norm_num)
theorem B2515475 : Blo 1987435 2515475 := bstep (se 1 (by rfl) ⟨1886606, by rfl⟩ : syracuseStep 2515475 = 3773213) B3773213
theorem B6707933 : Blo 1987435 6707933 := bstep (se 3 (by rfl) ⟨1257737, by rfl⟩ : syracuseStep 6707933 = 2515475) B2515475
theorem B4471955 : Blo 1987435 4471955 := bstep (se 1 (by rfl) ⟨3353966, by rfl⟩ : syracuseStep 4471955 = 6707933) B6707933
theorem B2981303 : Blo 1987435 2981303 := bstep (se 1 (by rfl) ⟨2235977, by rfl⟩ : syracuseStep 2981303 = 4471955) B4471955
theorem B1987535 : Blo 1987435 1987535 := bstep (se 1 (by rfl) ⟨1490651, by rfl⟩ : syracuseStep 1987535 = 2981303) B2981303
theorem B2981309 : Blo 1987435 2981309 := bbase (se 3 (by rfl) ⟨558995, by rfl⟩ : syracuseStep 2981309 = 1117991) (by norm_num)
theorem B1987539 : Blo 1987435 1987539 := bstep (se 1 (by rfl) ⟨1490654, by rfl⟩ : syracuseStep 1987539 = 2981309) B2981309
theorem B4471973 : Blo 1987435 4471973 := bbase (se 4 (by rfl) ⟨419247, by rfl⟩ : syracuseStep 4471973 = 838495) (by norm_num)
theorem B2981315 : Blo 1987435 2981315 := bstep (se 1 (by rfl) ⟨2235986, by rfl⟩ : syracuseStep 2981315 = 4471973) B4471973
theorem B1987543 : Blo 1987435 1987543 := bstep (se 1 (by rfl) ⟨1490657, by rfl⟩ : syracuseStep 1987543 = 2981315) B2981315
theorem B5030981 : Blo 1987435 5030981 := bbase (se 4 (by rfl) ⟨471654, by rfl⟩ : syracuseStep 5030981 = 943309) (by norm_num)
theorem B3353987 : Blo 1987435 3353987 := bstep (se 1 (by rfl) ⟨2515490, by rfl⟩ : syracuseStep 3353987 = 5030981) B5030981
theorem B2235991 : Blo 1987435 2235991 := bstep (se 1 (by rfl) ⟨1676993, by rfl⟩ : syracuseStep 2235991 = 3353987) B3353987
theorem B2981321 : Blo 1987435 2981321 := bstep (se 2 (by rfl) ⟨1117995, by rfl⟩ : syracuseStep 2981321 = 2235991) B2235991
theorem B1987547 : Blo 1987435 1987547 := bstep (se 1 (by rfl) ⟨1490660, by rfl⟩ : syracuseStep 1987547 = 2981321) B2981321
theorem B6367349 : Blo 1987435 6367349 := bbase (se 5 (by rfl) ⟨298469, by rfl⟩ : syracuseStep 6367349 = 596939) (by norm_num)
theorem B4244899 : Blo 1987435 4244899 := bstep (se 1 (by rfl) ⟨3183674, by rfl⟩ : syracuseStep 4244899 = 6367349) B6367349
theorem B5659865 : Blo 1987435 5659865 := bstep (se 2 (by rfl) ⟨2122449, by rfl⟩ : syracuseStep 5659865 = 4244899) B4244899
theorem B3773243 : Blo 1987435 3773243 := bstep (se 1 (by rfl) ⟨2829932, by rfl⟩ : syracuseStep 3773243 = 5659865) B5659865
theorem B10061981 : Blo 1987435 10061981 := bstep (se 3 (by rfl) ⟨1886621, by rfl⟩ : syracuseStep 10061981 = 3773243) B3773243
theorem B6707987 : Blo 1987435 6707987 := bstep (se 1 (by rfl) ⟨5030990, by rfl⟩ : syracuseStep 6707987 = 10061981) B10061981
theorem B4471991 : Blo 1987435 4471991 := bstep (se 1 (by rfl) ⟨3353993, by rfl⟩ : syracuseStep 4471991 = 6707987) B6707987
theorem B2981327 : Blo 1987435 2981327 := bstep (se 1 (by rfl) ⟨2235995, by rfl⟩ : syracuseStep 2981327 = 4471991) B4471991
theorem B1987551 : Blo 1987435 1987551 := bstep (se 1 (by rfl) ⟨1490663, by rfl⟩ : syracuseStep 1987551 = 2981327) B2981327
theorem B2981333 : Blo 1987435 2981333 := bbase (se 7 (by rfl) ⟨34937, by rfl⟩ : syracuseStep 2981333 = 69875) (by norm_num)
theorem B1987555 : Blo 1987435 1987555 := bstep (se 1 (by rfl) ⟨1490666, by rfl⟩ : syracuseStep 1987555 = 2981333) B2981333
theorem B7546517 : Blo 1987435 7546517 := bbase (se 6 (by rfl) ⟨176871, by rfl⟩ : syracuseStep 7546517 = 353743) (by norm_num)
theorem B5031011 : Blo 1987435 5031011 := bstep (se 1 (by rfl) ⟨3773258, by rfl⟩ : syracuseStep 5031011 = 7546517) B7546517
theorem B3354007 : Blo 1987435 3354007 := bstep (se 1 (by rfl) ⟨2515505, by rfl⟩ : syracuseStep 3354007 = 5031011) B5031011
theorem B4472009 : Blo 1987435 4472009 := bstep (se 2 (by rfl) ⟨1677003, by rfl⟩ : syracuseStep 4472009 = 3354007) B3354007
theorem B2981339 : Blo 1987435 2981339 := bstep (se 1 (by rfl) ⟨2236004, by rfl⟩ : syracuseStep 2981339 = 4472009) B4472009
theorem B1987559 : Blo 1987435 1987559 := bstep (se 1 (by rfl) ⟨1490669, by rfl⟩ : syracuseStep 1987559 = 2981339) B2981339
theorem B2236009 : Blo 1987435 2236009 := bbase (se 2 (by rfl) ⟨838503, by rfl⟩ : syracuseStep 2236009 = 1677007) (by norm_num)
theorem B2981345 : Blo 1987435 2981345 := bstep (se 2 (by rfl) ⟨1118004, by rfl⟩ : syracuseStep 2981345 = 2236009) B2236009
theorem B1987563 : Blo 1987435 1987563 := bstep (se 1 (by rfl) ⟨1490672, by rfl⟩ : syracuseStep 1987563 = 2981345) B2981345
theorem B4244933 : Blo 1987435 4244933 := bbase (se 4 (by rfl) ⟨397962, by rfl⟩ : syracuseStep 4244933 = 795925) (by norm_num)
theorem B11319821 : Blo 1987435 11319821 := bstep (se 3 (by rfl) ⟨2122466, by rfl⟩ : syracuseStep 11319821 = 4244933) B4244933
theorem B7546547 : Blo 1987435 7546547 := bstep (se 1 (by rfl) ⟨5659910, by rfl⟩ : syracuseStep 7546547 = 11319821) B11319821
theorem B5031031 : Blo 1987435 5031031 := bstep (se 1 (by rfl) ⟨3773273, by rfl⟩ : syracuseStep 5031031 = 7546547) B7546547
theorem B6708041 : Blo 1987435 6708041 := bstep (se 2 (by rfl) ⟨2515515, by rfl⟩ : syracuseStep 6708041 = 5031031) B5031031
theorem B4472027 : Blo 1987435 4472027 := bstep (se 1 (by rfl) ⟨3354020, by rfl⟩ : syracuseStep 4472027 = 6708041) B6708041
theorem B2981351 : Blo 1987435 2981351 := bstep (se 1 (by rfl) ⟨2236013, by rfl⟩ : syracuseStep 2981351 = 4472027) B4472027
theorem B1987567 : Blo 1987435 1987567 := bstep (se 1 (by rfl) ⟨1490675, by rfl⟩ : syracuseStep 1987567 = 2981351) B2981351
theorem B2981357 : Blo 1987435 2981357 := bbase (se 3 (by rfl) ⟨559004, by rfl⟩ : syracuseStep 2981357 = 1118009) (by norm_num)
theorem B1987571 : Blo 1987435 1987571 := bstep (se 1 (by rfl) ⟨1490678, by rfl⟩ : syracuseStep 1987571 = 2981357) B2981357
theorem B4472045 : Blo 1987435 4472045 := bbase (se 3 (by rfl) ⟨838508, by rfl⟩ : syracuseStep 4472045 = 1677017) (by norm_num)
theorem B2981363 : Blo 1987435 2981363 := bstep (se 1 (by rfl) ⟨2236022, by rfl⟩ : syracuseStep 2981363 = 4472045) B4472045
theorem B1987575 : Blo 1987435 1987575 := bstep (se 1 (by rfl) ⟨1490681, by rfl⟩ : syracuseStep 1987575 = 2981363) B2981363
theorem B2829973 : Blo 1987435 2829973 := bbase (se 6 (by rfl) ⟨66327, by rfl⟩ : syracuseStep 2829973 = 132655) (by norm_num)
theorem B3773297 : Blo 1987435 3773297 := bstep (se 2 (by rfl) ⟨1414986, by rfl⟩ : syracuseStep 3773297 = 2829973) B2829973
theorem B2515531 : Blo 1987435 2515531 := bstep (se 1 (by rfl) ⟨1886648, by rfl⟩ : syracuseStep 2515531 = 3773297) B3773297
theorem B3354041 : Blo 1987435 3354041 := bstep (se 2 (by rfl) ⟨1257765, by rfl⟩ : syracuseStep 3354041 = 2515531) B2515531
theorem B2236027 : Blo 1987435 2236027 := bstep (se 1 (by rfl) ⟨1677020, by rfl⟩ : syracuseStep 2236027 = 3354041) B3354041
theorem B2981369 : Blo 1987435 2981369 := bstep (se 2 (by rfl) ⟨1118013, by rfl⟩ : syracuseStep 2981369 = 2236027) B2236027
theorem B1987579 : Blo 1987435 1987579 := bstep (se 1 (by rfl) ⟨1490684, by rfl⟩ : syracuseStep 1987579 = 2981369) B2981369
theorem B6454325 : Blo 1987435 6454325 := bbase (se 5 (by rfl) ⟨302546, by rfl⟩ : syracuseStep 6454325 = 605093) (by norm_num)
theorem B4302883 : Blo 1987435 4302883 := bstep (se 1 (by rfl) ⟨3227162, by rfl⟩ : syracuseStep 4302883 = 6454325) B6454325
theorem B5737177 : Blo 1987435 5737177 := bstep (se 2 (by rfl) ⟨2151441, by rfl⟩ : syracuseStep 5737177 = 4302883) B4302883
theorem B7649569 : Blo 1987435 7649569 := bstep (se 2 (by rfl) ⟨2868588, by rfl⟩ : syracuseStep 7649569 = 5737177) B5737177
theorem B40797701 : Blo 1987435 40797701 := bstep (se 4 (by rfl) ⟨3824784, by rfl⟩ : syracuseStep 40797701 = 7649569) B7649569
theorem B27198467 : Blo 1987435 27198467 := bstep (se 1 (by rfl) ⟨20398850, by rfl⟩ : syracuseStep 27198467 = 40797701) B40797701
theorem B18132311 : Blo 1987435 18132311 := bstep (se 1 (by rfl) ⟨13599233, by rfl⟩ : syracuseStep 18132311 = 27198467) B27198467
theorem B12088207 : Blo 1987435 12088207 := bstep (se 1 (by rfl) ⟨9066155, by rfl⟩ : syracuseStep 12088207 = 18132311) B18132311
theorem B64470437 : Blo 1987435 64470437 := bstep (se 4 (by rfl) ⟨6044103, by rfl⟩ : syracuseStep 64470437 = 12088207) B12088207
theorem B42980291 : Blo 1987435 42980291 := bstep (se 1 (by rfl) ⟨32235218, by rfl⟩ : syracuseStep 42980291 = 64470437) B64470437
theorem B28653527 : Blo 1987435 28653527 := bstep (se 1 (by rfl) ⟨21490145, by rfl⟩ : syracuseStep 28653527 = 42980291) B42980291
theorem B76409405 : Blo 1987435 76409405 := bstep (se 3 (by rfl) ⟨14326763, by rfl⟩ : syracuseStep 76409405 = 28653527) B28653527
theorem B50939603 : Blo 1987435 50939603 := bstep (se 1 (by rfl) ⟨38204702, by rfl⟩ : syracuseStep 50939603 = 76409405) B76409405
theorem B33959735 : Blo 1987435 33959735 := bstep (se 1 (by rfl) ⟨25469801, by rfl⟩ : syracuseStep 33959735 = 50939603) B50939603
theorem B22639823 : Blo 1987435 22639823 := bstep (se 1 (by rfl) ⟨16979867, by rfl⟩ : syracuseStep 22639823 = 33959735) B33959735
theorem B15093215 : Blo 1987435 15093215 := bstep (se 1 (by rfl) ⟨11319911, by rfl⟩ : syracuseStep 15093215 = 22639823) B22639823
theorem B10062143 : Blo 1987435 10062143 := bstep (se 1 (by rfl) ⟨7546607, by rfl⟩ : syracuseStep 10062143 = 15093215) B15093215
theorem B6708095 : Blo 1987435 6708095 := bstep (se 1 (by rfl) ⟨5031071, by rfl⟩ : syracuseStep 6708095 = 10062143) B10062143
theorem B4472063 : Blo 1987435 4472063 := bstep (se 1 (by rfl) ⟨3354047, by rfl⟩ : syracuseStep 4472063 = 6708095) B6708095
theorem B2981375 : Blo 1987435 2981375 := bstep (se 1 (by rfl) ⟨2236031, by rfl⟩ : syracuseStep 2981375 = 4472063) B4472063
theorem B1987583 : Blo 1987435 1987583 := bstep (se 1 (by rfl) ⟨1490687, by rfl⟩ : syracuseStep 1987583 = 2981375) B2981375
theorem B2981381 : Blo 1987435 2981381 := bbase (se 4 (by rfl) ⟨279504, by rfl⟩ : syracuseStep 2981381 = 559009) (by norm_num)
theorem B1987587 : Blo 1987435 1987587 := bstep (se 1 (by rfl) ⟨1490690, by rfl⟩ : syracuseStep 1987587 = 2981381) B2981381
theorem B3354061 : Blo 1987435 3354061 := bbase (se 3 (by rfl) ⟨628886, by rfl⟩ : syracuseStep 3354061 = 1257773) (by norm_num)
theorem B4472081 : Blo 1987435 4472081 := bstep (se 2 (by rfl) ⟨1677030, by rfl⟩ : syracuseStep 4472081 = 3354061) B3354061
theorem B2981387 : Blo 1987435 2981387 := bstep (se 1 (by rfl) ⟨2236040, by rfl⟩ : syracuseStep 2981387 = 4472081) B4472081
theorem B1987591 : Blo 1987435 1987591 := bstep (se 1 (by rfl) ⟨1490693, by rfl⟩ : syracuseStep 1987591 = 2981387) B2981387
theorem B2236045 : Blo 1987435 2236045 := bbase (se 3 (by rfl) ⟨419258, by rfl⟩ : syracuseStep 2236045 = 838517) (by norm_num)
theorem B2981393 : Blo 1987435 2981393 := bstep (se 2 (by rfl) ⟨1118022, by rfl⟩ : syracuseStep 2981393 = 2236045) B2236045
theorem B1987595 : Blo 1987435 1987595 := bstep (se 1 (by rfl) ⟨1490696, by rfl⟩ : syracuseStep 1987595 = 2981393) B2981393
theorem B6708149 : Blo 1987435 6708149 := bbase (se 5 (by rfl) ⟨314444, by rfl⟩ : syracuseStep 6708149 = 628889) (by norm_num)
theorem B4472099 : Blo 1987435 4472099 := bstep (se 1 (by rfl) ⟨3354074, by rfl⟩ : syracuseStep 4472099 = 6708149) B6708149
theorem B2981399 : Blo 1987435 2981399 := bstep (se 1 (by rfl) ⟨2236049, by rfl⟩ : syracuseStep 2981399 = 4472099) B4472099
theorem B1987599 : Blo 1987435 1987599 := bstep (se 1 (by rfl) ⟨1490699, by rfl⟩ : syracuseStep 1987599 = 2981399) B2981399
theorem B2981405 : Blo 1987435 2981405 := bbase (se 3 (by rfl) ⟨559013, by rfl⟩ : syracuseStep 2981405 = 1118027) (by norm_num)
theorem B1987603 : Blo 1987435 1987603 := bstep (se 1 (by rfl) ⟨1490702, by rfl⟩ : syracuseStep 1987603 = 2981405) B2981405
theorem B4472117 : Blo 1987435 4472117 := bbase (se 5 (by rfl) ⟨209630, by rfl⟩ : syracuseStep 4472117 = 419261) (by norm_num)
theorem B2981411 : Blo 1987435 2981411 := bstep (se 1 (by rfl) ⟨2236058, by rfl⟩ : syracuseStep 2981411 = 4472117) B4472117
theorem B1987607 : Blo 1987435 1987607 := bstep (se 1 (by rfl) ⟨1490705, by rfl⟩ : syracuseStep 1987607 = 2981411) B2981411
theorem B10199573 : Blo 1987435 10199573 := bbase (se 6 (by rfl) ⟨239052, by rfl⟩ : syracuseStep 10199573 = 478105) (by norm_num)
theorem B6799715 : Blo 1987435 6799715 := bstep (se 1 (by rfl) ⟨5099786, by rfl⟩ : syracuseStep 6799715 = 10199573) B10199573
theorem B4533143 : Blo 1987435 4533143 := bstep (se 1 (by rfl) ⟨3399857, by rfl⟩ : syracuseStep 4533143 = 6799715) B6799715
theorem B12088381 : Blo 1987435 12088381 := bstep (se 3 (by rfl) ⟨2266571, by rfl⟩ : syracuseStep 12088381 = 4533143) B4533143
theorem B16117841 : Blo 1987435 16117841 := bstep (se 2 (by rfl) ⟨6044190, by rfl⟩ : syracuseStep 16117841 = 12088381) B12088381
theorem B10745227 : Blo 1987435 10745227 := bstep (se 1 (by rfl) ⟨8058920, by rfl⟩ : syracuseStep 10745227 = 16117841) B16117841
theorem B14326969 : Blo 1987435 14326969 := bstep (se 2 (by rfl) ⟨5372613, by rfl⟩ : syracuseStep 14326969 = 10745227) B10745227
theorem B19102625 : Blo 1987435 19102625 := bstep (se 2 (by rfl) ⟨7163484, by rfl⟩ : syracuseStep 19102625 = 14326969) B14326969
theorem B12735083 : Blo 1987435 12735083 := bstep (se 1 (by rfl) ⟨9551312, by rfl⟩ : syracuseStep 12735083 = 19102625) B19102625
theorem B8490055 : Blo 1987435 8490055 := bstep (se 1 (by rfl) ⟨6367541, by rfl⟩ : syracuseStep 8490055 = 12735083) B12735083
theorem B11320073 : Blo 1987435 11320073 := bstep (se 2 (by rfl) ⟨4245027, by rfl⟩ : syracuseStep 11320073 = 8490055) B8490055
theorem B7546715 : Blo 1987435 7546715 := bstep (se 1 (by rfl) ⟨5660036, by rfl⟩ : syracuseStep 7546715 = 11320073) B11320073
theorem B5031143 : Blo 1987435 5031143 := bstep (se 1 (by rfl) ⟨3773357, by rfl⟩ : syracuseStep 5031143 = 7546715) B7546715
theorem B3354095 : Blo 1987435 3354095 := bstep (se 1 (by rfl) ⟨2515571, by rfl⟩ : syracuseStep 3354095 = 5031143) B5031143
theorem B2236063 : Blo 1987435 2236063 := bstep (se 1 (by rfl) ⟨1677047, by rfl⟩ : syracuseStep 2236063 = 3354095) B3354095
theorem B2981417 : Blo 1987435 2981417 := bstep (se 2 (by rfl) ⟨1118031, by rfl⟩ : syracuseStep 2981417 = 2236063) B2236063
theorem B1987611 : Blo 1987435 1987611 := bstep (se 1 (by rfl) ⟨1490708, by rfl⟩ : syracuseStep 1987611 = 2981417) B2981417
theorem B3581749 : Blo 1987435 3581749 := bbase (se 5 (by rfl) ⟨167894, by rfl⟩ : syracuseStep 3581749 = 335789) (by norm_num)
theorem B19102661 : Blo 1987435 19102661 := bstep (se 4 (by rfl) ⟨1790874, by rfl⟩ : syracuseStep 19102661 = 3581749) B3581749
theorem B12735107 : Blo 1987435 12735107 := bstep (se 1 (by rfl) ⟨9551330, by rfl⟩ : syracuseStep 12735107 = 19102661) B19102661
theorem B8490071 : Blo 1987435 8490071 := bstep (se 1 (by rfl) ⟨6367553, by rfl⟩ : syracuseStep 8490071 = 12735107) B12735107
theorem B5660047 : Blo 1987435 5660047 := bstep (se 1 (by rfl) ⟨4245035, by rfl⟩ : syracuseStep 5660047 = 8490071) B8490071
theorem B7546729 : Blo 1987435 7546729 := bstep (se 2 (by rfl) ⟨2830023, by rfl⟩ : syracuseStep 7546729 = 5660047) B5660047
theorem B10062305 : Blo 1987435 10062305 := bstep (se 2 (by rfl) ⟨3773364, by rfl⟩ : syracuseStep 10062305 = 7546729) B7546729
theorem B6708203 : Blo 1987435 6708203 := bstep (se 1 (by rfl) ⟨5031152, by rfl⟩ : syracuseStep 6708203 = 10062305) B10062305
theorem B4472135 : Blo 1987435 4472135 := bstep (se 1 (by rfl) ⟨3354101, by rfl⟩ : syracuseStep 4472135 = 6708203) B6708203
theorem B2981423 : Blo 1987435 2981423 := bstep (se 1 (by rfl) ⟨2236067, by rfl⟩ : syracuseStep 2981423 = 4472135) B4472135
theorem B1987615 : Blo 1987435 1987615 := bstep (se 1 (by rfl) ⟨1490711, by rfl⟩ : syracuseStep 1987615 = 2981423) B2981423
theorem B2981429 : Blo 1987435 2981429 := bbase (se 5 (by rfl) ⟨139754, by rfl⟩ : syracuseStep 2981429 = 279509) (by norm_num)
theorem B1987619 : Blo 1987435 1987619 := bstep (se 1 (by rfl) ⟨1490714, by rfl⟩ : syracuseStep 1987619 = 2981429) B2981429
theorem B5031173 : Blo 1987435 5031173 := bbase (se 4 (by rfl) ⟨471672, by rfl⟩ : syracuseStep 5031173 = 943345) (by norm_num)
theorem B3354115 : Blo 1987435 3354115 := bstep (se 1 (by rfl) ⟨2515586, by rfl⟩ : syracuseStep 3354115 = 5031173) B5031173
theorem B4472153 : Blo 1987435 4472153 := bstep (se 2 (by rfl) ⟨1677057, by rfl⟩ : syracuseStep 4472153 = 3354115) B3354115
theorem B2981435 : Blo 1987435 2981435 := bstep (se 1 (by rfl) ⟨2236076, by rfl⟩ : syracuseStep 2981435 = 4472153) B4472153
theorem B1987623 : Blo 1987435 1987623 := bstep (se 1 (by rfl) ⟨1490717, by rfl⟩ : syracuseStep 1987623 = 2981435) B2981435
theorem B2236081 : Blo 1987435 2236081 := bbase (se 2 (by rfl) ⟨838530, by rfl⟩ : syracuseStep 2236081 = 1677061) (by norm_num)
theorem B2981441 : Blo 1987435 2981441 := bstep (se 2 (by rfl) ⟨1118040, by rfl⟩ : syracuseStep 2981441 = 2236081) B2236081
theorem B1987627 : Blo 1987435 1987627 := bstep (se 1 (by rfl) ⟨1490720, by rfl⟩ : syracuseStep 1987627 = 2981441) B2981441
theorem B2297521 : Blo 1987435 2297521 := bbase (se 2 (by rfl) ⟨861570, by rfl⟩ : syracuseStep 2297521 = 1723141) (by norm_num)
theorem B3063361 : Blo 1987435 3063361 := bstep (se 2 (by rfl) ⟨1148760, by rfl⟩ : syracuseStep 3063361 = 2297521) B2297521
theorem B4084481 : Blo 1987435 4084481 := bstep (se 2 (by rfl) ⟨1531680, by rfl⟩ : syracuseStep 4084481 = 3063361) B3063361
theorem B2722987 : Blo 1987435 2722987 := bstep (se 1 (by rfl) ⟨2042240, by rfl⟩ : syracuseStep 2722987 = 4084481) B4084481
theorem B14522597 : Blo 1987435 14522597 := bstep (se 4 (by rfl) ⟨1361493, by rfl⟩ : syracuseStep 14522597 = 2722987) B2722987
theorem B9681731 : Blo 1987435 9681731 := bstep (se 1 (by rfl) ⟨7261298, by rfl⟩ : syracuseStep 9681731 = 14522597) B14522597
theorem B6454487 : Blo 1987435 6454487 := bstep (se 1 (by rfl) ⟨4840865, by rfl⟩ : syracuseStep 6454487 = 9681731) B9681731
theorem B4302991 : Blo 1987435 4302991 := bstep (se 1 (by rfl) ⟨3227243, by rfl⟩ : syracuseStep 4302991 = 6454487) B6454487
theorem B5737321 : Blo 1987435 5737321 := bstep (se 2 (by rfl) ⟨2151495, by rfl⟩ : syracuseStep 5737321 = 4302991) B4302991
theorem B7649761 : Blo 1987435 7649761 := bstep (se 2 (by rfl) ⟨2868660, by rfl⟩ : syracuseStep 7649761 = 5737321) B5737321
theorem B10199681 : Blo 1987435 10199681 := bstep (se 2 (by rfl) ⟨3824880, by rfl⟩ : syracuseStep 10199681 = 7649761) B7649761
theorem B6799787 : Blo 1987435 6799787 := bstep (se 1 (by rfl) ⟨5099840, by rfl⟩ : syracuseStep 6799787 = 10199681) B10199681
theorem B4533191 : Blo 1987435 4533191 := bstep (se 1 (by rfl) ⟨3399893, by rfl⟩ : syracuseStep 4533191 = 6799787) B6799787
theorem B3022127 : Blo 1987435 3022127 := bstep (se 1 (by rfl) ⟨2266595, by rfl⟩ : syracuseStep 3022127 = 4533191) B4533191
theorem B2014751 : Blo 1987435 2014751 := bstep (se 1 (by rfl) ⟨1511063, by rfl⟩ : syracuseStep 2014751 = 3022127) B3022127
theorem B5372669 : Blo 1987435 5372669 := bstep (se 3 (by rfl) ⟨1007375, by rfl⟩ : syracuseStep 5372669 = 2014751) B2014751
theorem B3581779 : Blo 1987435 3581779 := bstep (se 1 (by rfl) ⟨2686334, by rfl⟩ : syracuseStep 3581779 = 5372669) B5372669
theorem B4775705 : Blo 1987435 4775705 := bstep (se 2 (by rfl) ⟨1790889, by rfl⟩ : syracuseStep 4775705 = 3581779) B3581779
theorem B3183803 : Blo 1987435 3183803 := bstep (se 1 (by rfl) ⟨2387852, by rfl⟩ : syracuseStep 3183803 = 4775705) B4775705
theorem B2122535 : Blo 1987435 2122535 := bstep (se 1 (by rfl) ⟨1591901, by rfl⟩ : syracuseStep 2122535 = 3183803) B3183803
theorem B5660093 : Blo 1987435 5660093 := bstep (se 3 (by rfl) ⟨1061267, by rfl⟩ : syracuseStep 5660093 = 2122535) B2122535
theorem B3773395 : Blo 1987435 3773395 := bstep (se 1 (by rfl) ⟨2830046, by rfl⟩ : syracuseStep 3773395 = 5660093) B5660093
theorem B5031193 : Blo 1987435 5031193 := bstep (se 2 (by rfl) ⟨1886697, by rfl⟩ : syracuseStep 5031193 = 3773395) B3773395
theorem B6708257 : Blo 1987435 6708257 := bstep (se 2 (by rfl) ⟨2515596, by rfl⟩ : syracuseStep 6708257 = 5031193) B5031193
theorem B4472171 : Blo 1987435 4472171 := bstep (se 1 (by rfl) ⟨3354128, by rfl⟩ : syracuseStep 4472171 = 6708257) B6708257
theorem B2981447 : Blo 1987435 2981447 := bstep (se 1 (by rfl) ⟨2236085, by rfl⟩ : syracuseStep 2981447 = 4472171) B4472171
theorem B1987631 : Blo 1987435 1987631 := bstep (se 1 (by rfl) ⟨1490723, by rfl⟩ : syracuseStep 1987631 = 2981447) B2981447
theorem B2981453 : Blo 1987435 2981453 := bbase (se 3 (by rfl) ⟨559022, by rfl⟩ : syracuseStep 2981453 = 1118045) (by norm_num)
theorem B1987635 : Blo 1987435 1987635 := bstep (se 1 (by rfl) ⟨1490726, by rfl⟩ : syracuseStep 1987635 = 2981453) B2981453
theorem B4472189 : Blo 1987435 4472189 := bbase (se 3 (by rfl) ⟨838535, by rfl⟩ : syracuseStep 4472189 = 1677071) (by norm_num)
theorem B2981459 : Blo 1987435 2981459 := bstep (se 1 (by rfl) ⟨2236094, by rfl⟩ : syracuseStep 2981459 = 4472189) B4472189
theorem B1987639 : Blo 1987435 1987639 := bstep (se 1 (by rfl) ⟨1490729, by rfl⟩ : syracuseStep 1987639 = 2981459) B2981459
theorem B3354149 : Blo 1987435 3354149 := bbase (se 4 (by rfl) ⟨314451, by rfl⟩ : syracuseStep 3354149 = 628903) (by norm_num)
theorem B2236099 : Blo 1987435 2236099 := bstep (se 1 (by rfl) ⟨1677074, by rfl⟩ : syracuseStep 2236099 = 3354149) B3354149
theorem B2981465 : Blo 1987435 2981465 := bstep (se 2 (by rfl) ⟨1118049, by rfl⟩ : syracuseStep 2981465 = 2236099) B2236099
theorem B1987643 : Blo 1987435 1987643 := bstep (se 1 (by rfl) ⟨1490732, by rfl⟩ : syracuseStep 1987643 = 2981465) B2981465
theorem B2830069 : Blo 1987435 2830069 := bbase (se 5 (by rfl) ⟨132659, by rfl⟩ : syracuseStep 2830069 = 265319) (by norm_num)
theorem B15093701 : Blo 1987435 15093701 := bstep (se 4 (by rfl) ⟨1415034, by rfl⟩ : syracuseStep 15093701 = 2830069) B2830069
theorem B10062467 : Blo 1987435 10062467 := bstep (se 1 (by rfl) ⟨7546850, by rfl⟩ : syracuseStep 10062467 = 15093701) B15093701
theorem B6708311 : Blo 1987435 6708311 := bstep (se 1 (by rfl) ⟨5031233, by rfl⟩ : syracuseStep 6708311 = 10062467) B10062467
theorem B4472207 : Blo 1987435 4472207 := bstep (se 1 (by rfl) ⟨3354155, by rfl⟩ : syracuseStep 4472207 = 6708311) B6708311
theorem B2981471 : Blo 1987435 2981471 := bstep (se 1 (by rfl) ⟨2236103, by rfl⟩ : syracuseStep 2981471 = 4472207) B4472207
theorem B1987647 : Blo 1987435 1987647 := bstep (se 1 (by rfl) ⟨1490735, by rfl⟩ : syracuseStep 1987647 = 2981471) B2981471
theorem B2981477 : Blo 1987435 2981477 := bbase (se 4 (by rfl) ⟨279513, by rfl⟩ : syracuseStep 2981477 = 559027) (by norm_num)
theorem B1987651 : Blo 1987435 1987651 := bstep (se 1 (by rfl) ⟨1490738, by rfl⟩ : syracuseStep 1987651 = 2981477) B2981477
theorem B2122561 : Blo 1987435 2122561 := bbase (se 2 (by rfl) ⟨795960, by rfl⟩ : syracuseStep 2122561 = 1591921) (by norm_num)
theorem B2830081 : Blo 1987435 2830081 := bstep (se 2 (by rfl) ⟨1061280, by rfl⟩ : syracuseStep 2830081 = 2122561) B2122561
theorem B3773441 : Blo 1987435 3773441 := bstep (se 2 (by rfl) ⟨1415040, by rfl⟩ : syracuseStep 3773441 = 2830081) B2830081
theorem B2515627 : Blo 1987435 2515627 := bstep (se 1 (by rfl) ⟨1886720, by rfl⟩ : syracuseStep 2515627 = 3773441) B3773441
theorem B3354169 : Blo 1987435 3354169 := bstep (se 2 (by rfl) ⟨1257813, by rfl⟩ : syracuseStep 3354169 = 2515627) B2515627
theorem B4472225 : Blo 1987435 4472225 := bstep (se 2 (by rfl) ⟨1677084, by rfl⟩ : syracuseStep 4472225 = 3354169) B3354169
theorem B2981483 : Blo 1987435 2981483 := bstep (se 1 (by rfl) ⟨2236112, by rfl⟩ : syracuseStep 2981483 = 4472225) B4472225
theorem B1987655 : Blo 1987435 1987655 := bstep (se 1 (by rfl) ⟨1490741, by rfl⟩ : syracuseStep 1987655 = 2981483) B2981483
theorem B2236117 : Blo 1987435 2236117 := bbase (se 7 (by rfl) ⟨26204, by rfl⟩ : syracuseStep 2236117 = 52409) (by norm_num)
theorem B2981489 : Blo 1987435 2981489 := bstep (se 2 (by rfl) ⟨1118058, by rfl⟩ : syracuseStep 2981489 = 2236117) B2236117
theorem B1987659 : Blo 1987435 1987659 := bstep (se 1 (by rfl) ⟨1490744, by rfl⟩ : syracuseStep 1987659 = 2981489) B2981489
theorem B2515637 : Blo 1987435 2515637 := bbase (se 5 (by rfl) ⟨117920, by rfl⟩ : syracuseStep 2515637 = 235841) (by norm_num)
theorem B6708365 : Blo 1987435 6708365 := bstep (se 3 (by rfl) ⟨1257818, by rfl⟩ : syracuseStep 6708365 = 2515637) B2515637
theorem B4472243 : Blo 1987435 4472243 := bstep (se 1 (by rfl) ⟨3354182, by rfl⟩ : syracuseStep 4472243 = 6708365) B6708365
theorem B2981495 : Blo 1987435 2981495 := bstep (se 1 (by rfl) ⟨2236121, by rfl⟩ : syracuseStep 2981495 = 4472243) B4472243
theorem B1987663 : Blo 1987435 1987663 := bstep (se 1 (by rfl) ⟨1490747, by rfl⟩ : syracuseStep 1987663 = 2981495) B2981495
theorem B2981501 : Blo 1987435 2981501 := bbase (se 3 (by rfl) ⟨559031, by rfl⟩ : syracuseStep 2981501 = 1118063) (by norm_num)
theorem B1987667 : Blo 1987435 1987667 := bstep (se 1 (by rfl) ⟨1490750, by rfl⟩ : syracuseStep 1987667 = 2981501) B2981501
theorem B4472261 : Blo 1987435 4472261 := bbase (se 4 (by rfl) ⟨419274, by rfl⟩ : syracuseStep 4472261 = 838549) (by norm_num)
theorem B2981507 : Blo 1987435 2981507 := bstep (se 1 (by rfl) ⟨2236130, by rfl⟩ : syracuseStep 2981507 = 4472261) B4472261
theorem B1987671 : Blo 1987435 1987671 := bstep (se 1 (by rfl) ⟨1490753, by rfl⟩ : syracuseStep 1987671 = 2981507) B2981507
theorem B9551621 : Blo 1987435 9551621 := bbase (se 4 (by rfl) ⟨895464, by rfl⟩ : syracuseStep 9551621 = 1790929) (by norm_num)
theorem B6367747 : Blo 1987435 6367747 := bstep (se 1 (by rfl) ⟨4775810, by rfl⟩ : syracuseStep 6367747 = 9551621) B9551621
theorem B8490329 : Blo 1987435 8490329 := bstep (se 2 (by rfl) ⟨3183873, by rfl⟩ : syracuseStep 8490329 = 6367747) B6367747
theorem B5660219 : Blo 1987435 5660219 := bstep (se 1 (by rfl) ⟨4245164, by rfl⟩ : syracuseStep 5660219 = 8490329) B8490329
theorem B3773479 : Blo 1987435 3773479 := bstep (se 1 (by rfl) ⟨2830109, by rfl⟩ : syracuseStep 3773479 = 5660219) B5660219
theorem B5031305 : Blo 1987435 5031305 := bstep (se 2 (by rfl) ⟨1886739, by rfl⟩ : syracuseStep 5031305 = 3773479) B3773479
theorem B3354203 : Blo 1987435 3354203 := bstep (se 1 (by rfl) ⟨2515652, by rfl⟩ : syracuseStep 3354203 = 5031305) B5031305
theorem B2236135 : Blo 1987435 2236135 := bstep (se 1 (by rfl) ⟨1677101, by rfl⟩ : syracuseStep 2236135 = 3354203) B3354203
theorem B2981513 : Blo 1987435 2981513 := bstep (se 2 (by rfl) ⟨1118067, by rfl⟩ : syracuseStep 2981513 = 2236135) B2236135
theorem B1987675 : Blo 1987435 1987675 := bstep (se 1 (by rfl) ⟨1490756, by rfl⟩ : syracuseStep 1987675 = 2981513) B2981513
theorem B10062629 : Blo 1987435 10062629 := bbase (se 4 (by rfl) ⟨943371, by rfl⟩ : syracuseStep 10062629 = 1886743) (by norm_num)
theorem B6708419 : Blo 1987435 6708419 := bstep (se 1 (by rfl) ⟨5031314, by rfl⟩ : syracuseStep 6708419 = 10062629) B10062629
theorem B4472279 : Blo 1987435 4472279 := bstep (se 1 (by rfl) ⟨3354209, by rfl⟩ : syracuseStep 4472279 = 6708419) B6708419
theorem B2981519 : Blo 1987435 2981519 := bstep (se 1 (by rfl) ⟨2236139, by rfl⟩ : syracuseStep 2981519 = 4472279) B4472279
theorem B1987679 : Blo 1987435 1987679 := bstep (se 1 (by rfl) ⟨1490759, by rfl⟩ : syracuseStep 1987679 = 2981519) B2981519
theorem B2981525 : Blo 1987435 2981525 := bbase (se 6 (by rfl) ⟨69879, by rfl⟩ : syracuseStep 2981525 = 139759) (by norm_num)
theorem B1987683 : Blo 1987435 1987683 := bstep (se 1 (by rfl) ⟨1490762, by rfl⟩ : syracuseStep 1987683 = 2981525) B2981525
theorem B4533317 : Blo 1987435 4533317 := bbase (se 4 (by rfl) ⟨424998, by rfl⟩ : syracuseStep 4533317 = 849997) (by norm_num)
theorem B3022211 : Blo 1987435 3022211 := bstep (se 1 (by rfl) ⟨2266658, by rfl⟩ : syracuseStep 3022211 = 4533317) B4533317
theorem B8059229 : Blo 1987435 8059229 := bstep (se 3 (by rfl) ⟨1511105, by rfl⟩ : syracuseStep 8059229 = 3022211) B3022211
theorem B5372819 : Blo 1987435 5372819 := bstep (se 1 (by rfl) ⟨4029614, by rfl⟩ : syracuseStep 5372819 = 8059229) B8059229
theorem B3581879 : Blo 1987435 3581879 := bstep (se 1 (by rfl) ⟨2686409, by rfl⟩ : syracuseStep 3581879 = 5372819) B5372819
theorem B9551677 : Blo 1987435 9551677 := bstep (se 3 (by rfl) ⟨1790939, by rfl⟩ : syracuseStep 9551677 = 3581879) B3581879
theorem B12735569 : Blo 1987435 12735569 := bstep (se 2 (by rfl) ⟨4775838, by rfl⟩ : syracuseStep 12735569 = 9551677) B9551677
theorem B8490379 : Blo 1987435 8490379 := bstep (se 1 (by rfl) ⟨6367784, by rfl⟩ : syracuseStep 8490379 = 12735569) B12735569
theorem B11320505 : Blo 1987435 11320505 := bstep (se 2 (by rfl) ⟨4245189, by rfl⟩ : syracuseStep 11320505 = 8490379) B8490379
theorem B7547003 : Blo 1987435 7547003 := bstep (se 1 (by rfl) ⟨5660252, by rfl⟩ : syracuseStep 7547003 = 11320505) B11320505
theorem B5031335 : Blo 1987435 5031335 := bstep (se 1 (by rfl) ⟨3773501, by rfl⟩ : syracuseStep 5031335 = 7547003) B7547003
theorem B3354223 : Blo 1987435 3354223 := bstep (se 1 (by rfl) ⟨2515667, by rfl⟩ : syracuseStep 3354223 = 5031335) B5031335
theorem B4472297 : Blo 1987435 4472297 := bstep (se 2 (by rfl) ⟨1677111, by rfl⟩ : syracuseStep 4472297 = 3354223) B3354223
theorem B2981531 : Blo 1987435 2981531 := bstep (se 1 (by rfl) ⟨2236148, by rfl⟩ : syracuseStep 2981531 = 4472297) B4472297
theorem B1987687 : Blo 1987435 1987687 := bstep (se 1 (by rfl) ⟨1490765, by rfl⟩ : syracuseStep 1987687 = 2981531) B2981531
theorem B2236153 : Blo 1987435 2236153 := bbase (se 2 (by rfl) ⟨838557, by rfl⟩ : syracuseStep 2236153 = 1677115) (by norm_num)
theorem B2981537 : Blo 1987435 2981537 := bstep (se 2 (by rfl) ⟨1118076, by rfl⟩ : syracuseStep 2981537 = 2236153) B2236153
theorem B1987691 : Blo 1987435 1987691 := bstep (se 1 (by rfl) ⟨1490768, by rfl⟩ : syracuseStep 1987691 = 2981537) B2981537
theorem B2387929 : Blo 1987435 2387929 := bbase (se 2 (by rfl) ⟨895473, by rfl⟩ : syracuseStep 2387929 = 1790947) (by norm_num)
theorem B3183905 : Blo 1987435 3183905 := bstep (se 2 (by rfl) ⟨1193964, by rfl⟩ : syracuseStep 3183905 = 2387929) B2387929
theorem B8490413 : Blo 1987435 8490413 := bstep (se 3 (by rfl) ⟨1591952, by rfl⟩ : syracuseStep 8490413 = 3183905) B3183905
theorem B5660275 : Blo 1987435 5660275 := bstep (se 1 (by rfl) ⟨4245206, by rfl⟩ : syracuseStep 5660275 = 8490413) B8490413
theorem B7547033 : Blo 1987435 7547033 := bstep (se 2 (by rfl) ⟨2830137, by rfl⟩ : syracuseStep 7547033 = 5660275) B5660275
theorem B5031355 : Blo 1987435 5031355 := bstep (se 1 (by rfl) ⟨3773516, by rfl⟩ : syracuseStep 5031355 = 7547033) B7547033
theorem B6708473 : Blo 1987435 6708473 := bstep (se 2 (by rfl) ⟨2515677, by rfl⟩ : syracuseStep 6708473 = 5031355) B5031355
theorem B4472315 : Blo 1987435 4472315 := bstep (se 1 (by rfl) ⟨3354236, by rfl⟩ : syracuseStep 4472315 = 6708473) B6708473
theorem B2981543 : Blo 1987435 2981543 := bstep (se 1 (by rfl) ⟨2236157, by rfl⟩ : syracuseStep 2981543 = 4472315) B4472315
theorem B1987695 : Blo 1987435 1987695 := bstep (se 1 (by rfl) ⟨1490771, by rfl⟩ : syracuseStep 1987695 = 2981543) B2981543
theorem B2981549 : Blo 1987435 2981549 := bbase (se 3 (by rfl) ⟨559040, by rfl⟩ : syracuseStep 2981549 = 1118081) (by norm_num)
theorem B1987699 : Blo 1987435 1987699 := bstep (se 1 (by rfl) ⟨1490774, by rfl⟩ : syracuseStep 1987699 = 2981549) B2981549
theorem B4472333 : Blo 1987435 4472333 := bbase (se 3 (by rfl) ⟨838562, by rfl⟩ : syracuseStep 4472333 = 1677125) (by norm_num)
theorem B2981555 : Blo 1987435 2981555 := bstep (se 1 (by rfl) ⟨2236166, by rfl⟩ : syracuseStep 2981555 = 4472333) B4472333
theorem B1987703 : Blo 1987435 1987703 := bstep (se 1 (by rfl) ⟨1490777, by rfl⟩ : syracuseStep 1987703 = 2981555) B2981555
theorem B2515693 : Blo 1987435 2515693 := bbase (se 3 (by rfl) ⟨471692, by rfl⟩ : syracuseStep 2515693 = 943385) (by norm_num)
theorem B3354257 : Blo 1987435 3354257 := bstep (se 2 (by rfl) ⟨1257846, by rfl⟩ : syracuseStep 3354257 = 2515693) B2515693
theorem B2236171 : Blo 1987435 2236171 := bstep (se 1 (by rfl) ⟨1677128, by rfl⟩ : syracuseStep 2236171 = 3354257) B3354257
theorem B2981561 : Blo 1987435 2981561 := bstep (se 2 (by rfl) ⟨1118085, by rfl⟩ : syracuseStep 2981561 = 2236171) B2236171
theorem B1987707 : Blo 1987435 1987707 := bstep (se 1 (by rfl) ⟨1490780, by rfl⟩ : syracuseStep 1987707 = 2981561) B2981561
theorem B2266685 : Blo 1987435 2266685 := bbase (se 3 (by rfl) ⟨425003, by rfl⟩ : syracuseStep 2266685 = 850007) (by norm_num)
theorem B24177973 : Blo 1987435 24177973 := bstep (se 5 (by rfl) ⟨1133342, by rfl⟩ : syracuseStep 24177973 = 2266685) B2266685
theorem B32237297 : Blo 1987435 32237297 := bstep (se 2 (by rfl) ⟨12088986, by rfl⟩ : syracuseStep 32237297 = 24177973) B24177973
theorem B21491531 : Blo 1987435 21491531 := bstep (se 1 (by rfl) ⟨16118648, by rfl⟩ : syracuseStep 21491531 = 32237297) B32237297
theorem B14327687 : Blo 1987435 14327687 := bstep (se 1 (by rfl) ⟨10745765, by rfl⟩ : syracuseStep 14327687 = 21491531) B21491531
theorem B9551791 : Blo 1987435 9551791 := bstep (se 1 (by rfl) ⟨7163843, by rfl⟩ : syracuseStep 9551791 = 14327687) B14327687
theorem B12735721 : Blo 1987435 12735721 := bstep (se 2 (by rfl) ⟨4775895, by rfl⟩ : syracuseStep 12735721 = 9551791) B9551791
theorem B16980961 : Blo 1987435 16980961 := bstep (se 2 (by rfl) ⟨6367860, by rfl⟩ : syracuseStep 16980961 = 12735721) B12735721
theorem B22641281 : Blo 1987435 22641281 := bstep (se 2 (by rfl) ⟨8490480, by rfl⟩ : syracuseStep 22641281 = 16980961) B16980961
theorem B15094187 : Blo 1987435 15094187 := bstep (se 1 (by rfl) ⟨11320640, by rfl⟩ : syracuseStep 15094187 = 22641281) B22641281
theorem B10062791 : Blo 1987435 10062791 := bstep (se 1 (by rfl) ⟨7547093, by rfl⟩ : syracuseStep 10062791 = 15094187) B15094187
theorem B6708527 : Blo 1987435 6708527 := bstep (se 1 (by rfl) ⟨5031395, by rfl⟩ : syracuseStep 6708527 = 10062791) B10062791
theorem B4472351 : Blo 1987435 4472351 := bstep (se 1 (by rfl) ⟨3354263, by rfl⟩ : syracuseStep 4472351 = 6708527) B6708527
theorem B2981567 : Blo 1987435 2981567 := bstep (se 1 (by rfl) ⟨2236175, by rfl⟩ : syracuseStep 2981567 = 4472351) B4472351
theorem B1987711 : Blo 1987435 1987711 := bstep (se 1 (by rfl) ⟨1490783, by rfl⟩ : syracuseStep 1987711 = 2981567) B2981567
theorem B2981573 : Blo 1987435 2981573 := bbase (se 4 (by rfl) ⟨279522, by rfl⟩ : syracuseStep 2981573 = 559045) (by norm_num)
theorem B1987715 : Blo 1987435 1987715 := bstep (se 1 (by rfl) ⟨1490786, by rfl⟩ : syracuseStep 1987715 = 2981573) B2981573
theorem B3354277 : Blo 1987435 3354277 := bbase (se 4 (by rfl) ⟨314463, by rfl⟩ : syracuseStep 3354277 = 628927) (by norm_num)
theorem B4472369 : Blo 1987435 4472369 := bstep (se 2 (by rfl) ⟨1677138, by rfl⟩ : syracuseStep 4472369 = 3354277) B3354277
theorem B2981579 : Blo 1987435 2981579 := bstep (se 1 (by rfl) ⟨2236184, by rfl⟩ : syracuseStep 2981579 = 4472369) B4472369
theorem B1987719 : Blo 1987435 1987719 := bstep (se 1 (by rfl) ⟨1490789, by rfl⟩ : syracuseStep 1987719 = 2981579) B2981579
theorem B2236189 : Blo 1987435 2236189 := bbase (se 3 (by rfl) ⟨419285, by rfl⟩ : syracuseStep 2236189 = 838571) (by norm_num)
theorem B2981585 : Blo 1987435 2981585 := bstep (se 2 (by rfl) ⟨1118094, by rfl⟩ : syracuseStep 2981585 = 2236189) B2236189
theorem B1987723 : Blo 1987435 1987723 := bstep (se 1 (by rfl) ⟨1490792, by rfl⟩ : syracuseStep 1987723 = 2981585) B2981585
theorem B6708581 : Blo 1987435 6708581 := bbase (se 4 (by rfl) ⟨628929, by rfl⟩ : syracuseStep 6708581 = 1257859) (by norm_num)
theorem B4472387 : Blo 1987435 4472387 := bstep (se 1 (by rfl) ⟨3354290, by rfl⟩ : syracuseStep 4472387 = 6708581) B6708581
theorem B2981591 : Blo 1987435 2981591 := bstep (se 1 (by rfl) ⟨2236193, by rfl⟩ : syracuseStep 2981591 = 4472387) B4472387
theorem B1987727 : Blo 1987435 1987727 := bstep (se 1 (by rfl) ⟨1490795, by rfl⟩ : syracuseStep 1987727 = 2981591) B2981591
theorem B2981597 : Blo 1987435 2981597 := bbase (se 3 (by rfl) ⟨559049, by rfl⟩ : syracuseStep 2981597 = 1118099) (by norm_num)
theorem B1987731 : Blo 1987435 1987731 := bstep (se 1 (by rfl) ⟨1490798, by rfl⟩ : syracuseStep 1987731 = 2981597) B2981597
theorem B4472405 : Blo 1987435 4472405 := bbase (se 8 (by rfl) ⟨26205, by rfl⟩ : syracuseStep 4472405 = 52411) (by norm_num)
theorem B2981603 : Blo 1987435 2981603 := bstep (se 1 (by rfl) ⟨2236202, by rfl⟩ : syracuseStep 2981603 = 4472405) B4472405
theorem B1987735 : Blo 1987435 1987735 := bstep (se 1 (by rfl) ⟨1490801, by rfl⟩ : syracuseStep 1987735 = 2981603) B2981603
theorem B4245301 : Blo 1987435 4245301 := bbase (se 5 (by rfl) ⟨198998, by rfl⟩ : syracuseStep 4245301 = 397997) (by norm_num)
theorem B5660401 : Blo 1987435 5660401 := bstep (se 2 (by rfl) ⟨2122650, by rfl⟩ : syracuseStep 5660401 = 4245301) B4245301
theorem B7547201 : Blo 1987435 7547201 := bstep (se 2 (by rfl) ⟨2830200, by rfl⟩ : syracuseStep 7547201 = 5660401) B5660401
theorem B5031467 : Blo 1987435 5031467 := bstep (se 1 (by rfl) ⟨3773600, by rfl⟩ : syracuseStep 5031467 = 7547201) B7547201
theorem B3354311 : Blo 1987435 3354311 := bstep (se 1 (by rfl) ⟨2515733, by rfl⟩ : syracuseStep 3354311 = 5031467) B5031467
theorem B2236207 : Blo 1987435 2236207 := bstep (se 1 (by rfl) ⟨1677155, by rfl⟩ : syracuseStep 2236207 = 3354311) B3354311
theorem B2981609 : Blo 1987435 2981609 := bstep (se 2 (by rfl) ⟨1118103, by rfl⟩ : syracuseStep 2981609 = 2236207) B2236207
theorem B1987739 : Blo 1987435 1987739 := bstep (se 1 (by rfl) ⟨1490804, by rfl⟩ : syracuseStep 1987739 = 2981609) B2981609
theorem B15300373 : Blo 1987435 15300373 := bbase (se 6 (by rfl) ⟨358602, by rfl⟩ : syracuseStep 15300373 = 717205) (by norm_num)
theorem B20400497 : Blo 1987435 20400497 := bstep (se 2 (by rfl) ⟨7650186, by rfl⟩ : syracuseStep 20400497 = 15300373) B15300373
theorem B13600331 : Blo 1987435 13600331 := bstep (se 1 (by rfl) ⟨10200248, by rfl⟩ : syracuseStep 13600331 = 20400497) B20400497
theorem B9066887 : Blo 1987435 9066887 := bstep (se 1 (by rfl) ⟨6800165, by rfl⟩ : syracuseStep 9066887 = 13600331) B13600331
theorem B6044591 : Blo 1987435 6044591 := bstep (se 1 (by rfl) ⟨4533443, by rfl⟩ : syracuseStep 6044591 = 9066887) B9066887
theorem B16118909 : Blo 1987435 16118909 := bstep (se 3 (by rfl) ⟨3022295, by rfl⟩ : syracuseStep 16118909 = 6044591) B6044591
theorem B10745939 : Blo 1987435 10745939 := bstep (se 1 (by rfl) ⟨8059454, by rfl⟩ : syracuseStep 10745939 = 16118909) B16118909
theorem B7163959 : Blo 1987435 7163959 := bstep (se 1 (by rfl) ⟨5372969, by rfl⟩ : syracuseStep 7163959 = 10745939) B10745939
theorem B9551945 : Blo 1987435 9551945 := bstep (se 2 (by rfl) ⟨3581979, by rfl⟩ : syracuseStep 9551945 = 7163959) B7163959
theorem B25471853 : Blo 1987435 25471853 := bstep (se 3 (by rfl) ⟨4775972, by rfl⟩ : syracuseStep 25471853 = 9551945) B9551945
theorem B16981235 : Blo 1987435 16981235 := bstep (se 1 (by rfl) ⟨12735926, by rfl⟩ : syracuseStep 16981235 = 25471853) B25471853
theorem B11320823 : Blo 1987435 11320823 := bstep (se 1 (by rfl) ⟨8490617, by rfl⟩ : syracuseStep 11320823 = 16981235) B16981235
theorem B7547215 : Blo 1987435 7547215 := bstep (se 1 (by rfl) ⟨5660411, by rfl⟩ : syracuseStep 7547215 = 11320823) B11320823
theorem B10062953 : Blo 1987435 10062953 := bstep (se 2 (by rfl) ⟨3773607, by rfl⟩ : syracuseStep 10062953 = 7547215) B7547215
theorem B6708635 : Blo 1987435 6708635 := bstep (se 1 (by rfl) ⟨5031476, by rfl⟩ : syracuseStep 6708635 = 10062953) B10062953
theorem B4472423 : Blo 1987435 4472423 := bstep (se 1 (by rfl) ⟨3354317, by rfl⟩ : syracuseStep 4472423 = 6708635) B6708635
theorem B2981615 : Blo 1987435 2981615 := bstep (se 1 (by rfl) ⟨2236211, by rfl⟩ : syracuseStep 2981615 = 4472423) B4472423
theorem B1987743 : Blo 1987435 1987743 := bstep (se 1 (by rfl) ⟨1490807, by rfl⟩ : syracuseStep 1987743 = 2981615) B2981615
theorem B2981621 : Blo 1987435 2981621 := bbase (se 5 (by rfl) ⟨139763, by rfl⟩ : syracuseStep 2981621 = 279527) (by norm_num)
theorem B1987747 : Blo 1987435 1987747 := bstep (se 1 (by rfl) ⟨1490810, by rfl⟩ : syracuseStep 1987747 = 2981621) B2981621
theorem B3022309 : Blo 1987435 3022309 := bbase (se 4 (by rfl) ⟨283341, by rfl⟩ : syracuseStep 3022309 = 566683) (by norm_num)
theorem B4029745 : Blo 1987435 4029745 := bstep (se 2 (by rfl) ⟨1511154, by rfl⟩ : syracuseStep 4029745 = 3022309) B3022309
theorem B5372993 : Blo 1987435 5372993 := bstep (se 2 (by rfl) ⟨2014872, by rfl⟩ : syracuseStep 5372993 = 4029745) B4029745
theorem B3581995 : Blo 1987435 3581995 := bstep (se 1 (by rfl) ⟨2686496, by rfl⟩ : syracuseStep 3581995 = 5372993) B5372993
theorem B4775993 : Blo 1987435 4775993 := bstep (se 2 (by rfl) ⟨1790997, by rfl⟩ : syracuseStep 4775993 = 3581995) B3581995
theorem B3183995 : Blo 1987435 3183995 := bstep (se 1 (by rfl) ⟨2387996, by rfl⟩ : syracuseStep 3183995 = 4775993) B4775993
theorem B8490653 : Blo 1987435 8490653 := bstep (se 3 (by rfl) ⟨1591997, by rfl⟩ : syracuseStep 8490653 = 3183995) B3183995
theorem B5660435 : Blo 1987435 5660435 := bstep (se 1 (by rfl) ⟨4245326, by rfl⟩ : syracuseStep 5660435 = 8490653) B8490653
theorem B3773623 : Blo 1987435 3773623 := bstep (se 1 (by rfl) ⟨2830217, by rfl⟩ : syracuseStep 3773623 = 5660435) B5660435
theorem B5031497 : Blo 1987435 5031497 := bstep (se 2 (by rfl) ⟨1886811, by rfl⟩ : syracuseStep 5031497 = 3773623) B3773623
theorem B3354331 : Blo 1987435 3354331 := bstep (se 1 (by rfl) ⟨2515748, by rfl⟩ : syracuseStep 3354331 = 5031497) B5031497
theorem B4472441 : Blo 1987435 4472441 := bstep (se 2 (by rfl) ⟨1677165, by rfl⟩ : syracuseStep 4472441 = 3354331) B3354331
theorem B2981627 : Blo 1987435 2981627 := bstep (se 1 (by rfl) ⟨2236220, by rfl⟩ : syracuseStep 2981627 = 4472441) B4472441
theorem B1987751 : Blo 1987435 1987751 := bstep (se 1 (by rfl) ⟨1490813, by rfl⟩ : syracuseStep 1987751 = 2981627) B2981627
theorem B2236225 : Blo 1987435 2236225 := bbase (se 2 (by rfl) ⟨838584, by rfl⟩ : syracuseStep 2236225 = 1677169) (by norm_num)
theorem B2981633 : Blo 1987435 2981633 := bstep (se 2 (by rfl) ⟨1118112, by rfl⟩ : syracuseStep 2981633 = 2236225) B2236225
theorem B1987755 : Blo 1987435 1987755 := bstep (se 1 (by rfl) ⟨1490816, by rfl⟩ : syracuseStep 1987755 = 2981633) B2981633
theorem B5031517 : Blo 1987435 5031517 := bbase (se 3 (by rfl) ⟨943409, by rfl⟩ : syracuseStep 5031517 = 1886819) (by norm_num)
theorem B6708689 : Blo 1987435 6708689 := bstep (se 2 (by rfl) ⟨2515758, by rfl⟩ : syracuseStep 6708689 = 5031517) B5031517
theorem B4472459 : Blo 1987435 4472459 := bstep (se 1 (by rfl) ⟨3354344, by rfl⟩ : syracuseStep 4472459 = 6708689) B6708689
theorem B2981639 : Blo 1987435 2981639 := bstep (se 1 (by rfl) ⟨2236229, by rfl⟩ : syracuseStep 2981639 = 4472459) B4472459
theorem B1987759 : Blo 1987435 1987759 := bstep (se 1 (by rfl) ⟨1490819, by rfl⟩ : syracuseStep 1987759 = 2981639) B2981639
theorem B2981645 : Blo 1987435 2981645 := bbase (se 3 (by rfl) ⟨559058, by rfl⟩ : syracuseStep 2981645 = 1118117) (by norm_num)
theorem B1987763 : Blo 1987435 1987763 := bstep (se 1 (by rfl) ⟨1490822, by rfl⟩ : syracuseStep 1987763 = 2981645) B2981645
theorem B4472477 : Blo 1987435 4472477 := bbase (se 3 (by rfl) ⟨838589, by rfl⟩ : syracuseStep 4472477 = 1677179) (by norm_num)
theorem B2981651 : Blo 1987435 2981651 := bstep (se 1 (by rfl) ⟨2236238, by rfl⟩ : syracuseStep 2981651 = 4472477) B4472477
theorem B1987767 : Blo 1987435 1987767 := bstep (se 1 (by rfl) ⟨1490825, by rfl⟩ : syracuseStep 1987767 = 2981651) B2981651
theorem B3354365 : Blo 1987435 3354365 := bbase (se 3 (by rfl) ⟨628943, by rfl⟩ : syracuseStep 3354365 = 1257887) (by norm_num)
theorem B2236243 : Blo 1987435 2236243 := bstep (se 1 (by rfl) ⟨1677182, by rfl⟩ : syracuseStep 2236243 = 3354365) B3354365
theorem B2981657 : Blo 1987435 2981657 := bstep (se 2 (by rfl) ⟨1118121, by rfl⟩ : syracuseStep 2981657 = 2236243) B2236243
theorem B1987771 : Blo 1987435 1987771 := bstep (se 1 (by rfl) ⟨1490828, by rfl⟩ : syracuseStep 1987771 = 2981657) B2981657
theorem B2388025 : Blo 1987435 2388025 := bbase (se 2 (by rfl) ⟨895509, by rfl⟩ : syracuseStep 2388025 = 1791019) (by norm_num)
theorem B3184033 : Blo 1987435 3184033 := bstep (se 2 (by rfl) ⟨1194012, by rfl⟩ : syracuseStep 3184033 = 2388025) B2388025
theorem B4245377 : Blo 1987435 4245377 := bstep (se 2 (by rfl) ⟨1592016, by rfl⟩ : syracuseStep 4245377 = 3184033) B3184033
theorem B11321005 : Blo 1987435 11321005 := bstep (se 3 (by rfl) ⟨2122688, by rfl⟩ : syracuseStep 11321005 = 4245377) B4245377
theorem B15094673 : Blo 1987435 15094673 := bstep (se 2 (by rfl) ⟨5660502, by rfl⟩ : syracuseStep 15094673 = 11321005) B11321005
theorem B10063115 : Blo 1987435 10063115 := bstep (se 1 (by rfl) ⟨7547336, by rfl⟩ : syracuseStep 10063115 = 15094673) B15094673
theorem B6708743 : Blo 1987435 6708743 := bstep (se 1 (by rfl) ⟨5031557, by rfl⟩ : syracuseStep 6708743 = 10063115) B10063115
theorem B4472495 : Blo 1987435 4472495 := bstep (se 1 (by rfl) ⟨3354371, by rfl⟩ : syracuseStep 4472495 = 6708743) B6708743
theorem B2981663 : Blo 1987435 2981663 := bstep (se 1 (by rfl) ⟨2236247, by rfl⟩ : syracuseStep 2981663 = 4472495) B4472495
theorem B1987775 : Blo 1987435 1987775 := bstep (se 1 (by rfl) ⟨1490831, by rfl⟩ : syracuseStep 1987775 = 2981663) B2981663
theorem B2981669 : Blo 1987435 2981669 := bbase (se 4 (by rfl) ⟨279531, by rfl⟩ : syracuseStep 2981669 = 559063) (by norm_num)
theorem B1987779 : Blo 1987435 1987779 := bstep (se 1 (by rfl) ⟨1490834, by rfl⟩ : syracuseStep 1987779 = 2981669) B2981669
theorem B2515789 : Blo 1987435 2515789 := bbase (se 3 (by rfl) ⟨471710, by rfl⟩ : syracuseStep 2515789 = 943421) (by norm_num)
theorem B3354385 : Blo 1987435 3354385 := bstep (se 2 (by rfl) ⟨1257894, by rfl⟩ : syracuseStep 3354385 = 2515789) B2515789
theorem B4472513 : Blo 1987435 4472513 := bstep (se 2 (by rfl) ⟨1677192, by rfl⟩ : syracuseStep 4472513 = 3354385) B3354385
theorem B2981675 : Blo 1987435 2981675 := bstep (se 1 (by rfl) ⟨2236256, by rfl⟩ : syracuseStep 2981675 = 4472513) B4472513
theorem B1987783 : Blo 1987435 1987783 := bstep (se 1 (by rfl) ⟨1490837, by rfl⟩ : syracuseStep 1987783 = 2981675) B2981675
theorem B2236261 : Blo 1987435 2236261 := bbase (se 4 (by rfl) ⟨209649, by rfl⟩ : syracuseStep 2236261 = 419299) (by norm_num)
theorem B2981681 : Blo 1987435 2981681 := bstep (se 2 (by rfl) ⟨1118130, by rfl⟩ : syracuseStep 2981681 = 2236261) B2236261
theorem B1987787 : Blo 1987435 1987787 := bstep (se 1 (by rfl) ⟨1490840, by rfl⟩ : syracuseStep 1987787 = 2981681) B2981681
theorem B5660549 : Blo 1987435 5660549 := bbase (se 4 (by rfl) ⟨530676, by rfl⟩ : syracuseStep 5660549 = 1061353) (by norm_num)
theorem B3773699 : Blo 1987435 3773699 := bstep (se 1 (by rfl) ⟨2830274, by rfl⟩ : syracuseStep 3773699 = 5660549) B5660549
theorem B2515799 : Blo 1987435 2515799 := bstep (se 1 (by rfl) ⟨1886849, by rfl⟩ : syracuseStep 2515799 = 3773699) B3773699
theorem B6708797 : Blo 1987435 6708797 := bstep (se 3 (by rfl) ⟨1257899, by rfl⟩ : syracuseStep 6708797 = 2515799) B2515799
theorem B4472531 : Blo 1987435 4472531 := bstep (se 1 (by rfl) ⟨3354398, by rfl⟩ : syracuseStep 4472531 = 6708797) B6708797
theorem B2981687 : Blo 1987435 2981687 := bstep (se 1 (by rfl) ⟨2236265, by rfl⟩ : syracuseStep 2981687 = 4472531) B4472531
theorem B1987791 : Blo 1987435 1987791 := bstep (se 1 (by rfl) ⟨1490843, by rfl⟩ : syracuseStep 1987791 = 2981687) B2981687
theorem B2981693 : Blo 1987435 2981693 := bbase (se 3 (by rfl) ⟨559067, by rfl⟩ : syracuseStep 2981693 = 1118135) (by norm_num)
theorem B1987795 : Blo 1987435 1987795 := bstep (se 1 (by rfl) ⟨1490846, by rfl⟩ : syracuseStep 1987795 = 2981693) B2981693
theorem B4472549 : Blo 1987435 4472549 := bbase (se 4 (by rfl) ⟨419301, by rfl⟩ : syracuseStep 4472549 = 838603) (by norm_num)
theorem B2981699 : Blo 1987435 2981699 := bstep (se 1 (by rfl) ⟨2236274, by rfl⟩ : syracuseStep 2981699 = 4472549) B4472549
theorem B1987799 : Blo 1987435 1987799 := bstep (se 1 (by rfl) ⟨1490849, by rfl⟩ : syracuseStep 1987799 = 2981699) B2981699
theorem B5031629 : Blo 1987435 5031629 := bbase (se 3 (by rfl) ⟨943430, by rfl⟩ : syracuseStep 5031629 = 1886861) (by norm_num)
theorem B3354419 : Blo 1987435 3354419 := bstep (se 1 (by rfl) ⟨2515814, by rfl⟩ : syracuseStep 3354419 = 5031629) B5031629
theorem B2236279 : Blo 1987435 2236279 := bstep (se 1 (by rfl) ⟨1677209, by rfl⟩ : syracuseStep 2236279 = 3354419) B3354419
theorem B2981705 : Blo 1987435 2981705 := bstep (se 2 (by rfl) ⟨1118139, by rfl⟩ : syracuseStep 2981705 = 2236279) B2236279
theorem B1987803 : Blo 1987435 1987803 := bstep (se 1 (by rfl) ⟨1490852, by rfl⟩ : syracuseStep 1987803 = 2981705) B2981705
theorem B3184085 : Blo 1987435 3184085 := bbase (se 7 (by rfl) ⟨37313, by rfl⟩ : syracuseStep 3184085 = 74627) (by norm_num)
theorem B2122723 : Blo 1987435 2122723 := bstep (se 1 (by rfl) ⟨1592042, by rfl⟩ : syracuseStep 2122723 = 3184085) B3184085
theorem B2830297 : Blo 1987435 2830297 := bstep (se 2 (by rfl) ⟨1061361, by rfl⟩ : syracuseStep 2830297 = 2122723) B2122723
theorem B3773729 : Blo 1987435 3773729 := bstep (se 2 (by rfl) ⟨1415148, by rfl⟩ : syracuseStep 3773729 = 2830297) B2830297
theorem B10063277 : Blo 1987435 10063277 := bstep (se 3 (by rfl) ⟨1886864, by rfl⟩ : syracuseStep 10063277 = 3773729) B3773729
theorem B6708851 : Blo 1987435 6708851 := bstep (se 1 (by rfl) ⟨5031638, by rfl⟩ : syracuseStep 6708851 = 10063277) B10063277
theorem B4472567 : Blo 1987435 4472567 := bstep (se 1 (by rfl) ⟨3354425, by rfl⟩ : syracuseStep 4472567 = 6708851) B6708851
theorem B2981711 : Blo 1987435 2981711 := bstep (se 1 (by rfl) ⟨2236283, by rfl⟩ : syracuseStep 2981711 = 4472567) B4472567
theorem B1987807 : Blo 1987435 1987807 := bstep (se 1 (by rfl) ⟨1490855, by rfl⟩ : syracuseStep 1987807 = 2981711) B2981711
theorem B2981717 : Blo 1987435 2981717 := bbase (se 9 (by rfl) ⟨8735, by rfl⟩ : syracuseStep 2981717 = 17471) (by norm_num)
theorem B1987811 : Blo 1987435 1987811 := bstep (se 1 (by rfl) ⟨1490858, by rfl⟩ : syracuseStep 1987811 = 2981717) B2981717
theorem B9552293 : Blo 1987435 9552293 := bbase (se 4 (by rfl) ⟨895527, by rfl⟩ : syracuseStep 9552293 = 1791055) (by norm_num)
theorem B6368195 : Blo 1987435 6368195 := bstep (se 1 (by rfl) ⟨4776146, by rfl⟩ : syracuseStep 6368195 = 9552293) B9552293
theorem B4245463 : Blo 1987435 4245463 := bstep (se 1 (by rfl) ⟨3184097, by rfl⟩ : syracuseStep 4245463 = 6368195) B6368195
theorem B5660617 : Blo 1987435 5660617 := bstep (se 2 (by rfl) ⟨2122731, by rfl⟩ : syracuseStep 5660617 = 4245463) B4245463
theorem B7547489 : Blo 1987435 7547489 := bstep (se 2 (by rfl) ⟨2830308, by rfl⟩ : syracuseStep 7547489 = 5660617) B5660617
theorem B5031659 : Blo 1987435 5031659 := bstep (se 1 (by rfl) ⟨3773744, by rfl⟩ : syracuseStep 5031659 = 7547489) B7547489
theorem B3354439 : Blo 1987435 3354439 := bstep (se 1 (by rfl) ⟨2515829, by rfl⟩ : syracuseStep 3354439 = 5031659) B5031659
theorem B4472585 : Blo 1987435 4472585 := bstep (se 2 (by rfl) ⟨1677219, by rfl⟩ : syracuseStep 4472585 = 3354439) B3354439
theorem B2981723 : Blo 1987435 2981723 := bstep (se 1 (by rfl) ⟨2236292, by rfl⟩ : syracuseStep 2981723 = 4472585) B4472585
theorem B1987815 : Blo 1987435 1987815 := bstep (se 1 (by rfl) ⟨1490861, by rfl⟩ : syracuseStep 1987815 = 2981723) B2981723
theorem B2236297 : Blo 1987435 2236297 := bbase (se 2 (by rfl) ⟨838611, by rfl⟩ : syracuseStep 2236297 = 1677223) (by norm_num)
theorem B2981729 : Blo 1987435 2981729 := bstep (se 2 (by rfl) ⟨1118148, by rfl⟩ : syracuseStep 2981729 = 2236297) B2236297
theorem B1987819 : Blo 1987435 1987819 := bstep (se 1 (by rfl) ⟨1490864, by rfl⟩ : syracuseStep 1987819 = 2981729) B2981729
theorem B3630997 : Blo 1987435 3630997 := bbase (se 6 (by rfl) ⟨85101, by rfl⟩ : syracuseStep 3630997 = 170203) (by norm_num)
theorem B4841329 : Blo 1987435 4841329 := bstep (se 2 (by rfl) ⟨1815498, by rfl⟩ : syracuseStep 4841329 = 3630997) B3630997
theorem B6455105 : Blo 1987435 6455105 := bstep (se 2 (by rfl) ⟨2420664, by rfl⟩ : syracuseStep 6455105 = 4841329) B4841329
theorem B4303403 : Blo 1987435 4303403 := bstep (se 1 (by rfl) ⟨3227552, by rfl⟩ : syracuseStep 4303403 = 6455105) B6455105
theorem B2868935 : Blo 1987435 2868935 := bstep (se 1 (by rfl) ⟨2151701, by rfl⟩ : syracuseStep 2868935 = 4303403) B4303403
theorem B7650493 : Blo 1987435 7650493 := bstep (se 3 (by rfl) ⟨1434467, by rfl⟩ : syracuseStep 7650493 = 2868935) B2868935
theorem B40802629 : Blo 1987435 40802629 := bstep (se 4 (by rfl) ⟨3825246, by rfl⟩ : syracuseStep 40802629 = 7650493) B7650493
theorem B54403505 : Blo 1987435 54403505 := bstep (se 2 (by rfl) ⟨20401314, by rfl⟩ : syracuseStep 54403505 = 40802629) B40802629
theorem B36269003 : Blo 1987435 36269003 := bstep (se 1 (by rfl) ⟨27201752, by rfl⟩ : syracuseStep 36269003 = 54403505) B54403505
theorem B96717341 : Blo 1987435 96717341 := bstep (se 3 (by rfl) ⟨18134501, by rfl⟩ : syracuseStep 96717341 = 36269003) B36269003
theorem B64478227 : Blo 1987435 64478227 := bstep (se 1 (by rfl) ⟨48358670, by rfl⟩ : syracuseStep 64478227 = 96717341) B96717341
theorem B85970969 : Blo 1987435 85970969 := bstep (se 2 (by rfl) ⟨32239113, by rfl⟩ : syracuseStep 85970969 = 64478227) B64478227
theorem B57313979 : Blo 1987435 57313979 := bstep (se 1 (by rfl) ⟨42985484, by rfl⟩ : syracuseStep 57313979 = 85970969) B85970969
theorem B38209319 : Blo 1987435 38209319 := bstep (se 1 (by rfl) ⟨28656989, by rfl⟩ : syracuseStep 38209319 = 57313979) B57313979
theorem B25472879 : Blo 1987435 25472879 := bstep (se 1 (by rfl) ⟨19104659, by rfl⟩ : syracuseStep 25472879 = 38209319) B38209319
theorem B16981919 : Blo 1987435 16981919 := bstep (se 1 (by rfl) ⟨12736439, by rfl⟩ : syracuseStep 16981919 = 25472879) B25472879
theorem B11321279 : Blo 1987435 11321279 := bstep (se 1 (by rfl) ⟨8490959, by rfl⟩ : syracuseStep 11321279 = 16981919) B16981919
theorem B7547519 : Blo 1987435 7547519 := bstep (se 1 (by rfl) ⟨5660639, by rfl⟩ : syracuseStep 7547519 = 11321279) B11321279
theorem B5031679 : Blo 1987435 5031679 := bstep (se 1 (by rfl) ⟨3773759, by rfl⟩ : syracuseStep 5031679 = 7547519) B7547519
theorem B6708905 : Blo 1987435 6708905 := bstep (se 2 (by rfl) ⟨2515839, by rfl⟩ : syracuseStep 6708905 = 5031679) B5031679
theorem B4472603 : Blo 1987435 4472603 := bstep (se 1 (by rfl) ⟨3354452, by rfl⟩ : syracuseStep 4472603 = 6708905) B6708905
theorem B2981735 : Blo 1987435 2981735 := bstep (se 1 (by rfl) ⟨2236301, by rfl⟩ : syracuseStep 2981735 = 4472603) B4472603
theorem B1987823 : Blo 1987435 1987823 := bstep (se 1 (by rfl) ⟨1490867, by rfl⟩ : syracuseStep 1987823 = 2981735) B2981735
theorem B2981741 : Blo 1987435 2981741 := bbase (se 3 (by rfl) ⟨559076, by rfl⟩ : syracuseStep 2981741 = 1118153) (by norm_num)
theorem B1987827 : Blo 1987435 1987827 := bstep (se 1 (by rfl) ⟨1490870, by rfl⟩ : syracuseStep 1987827 = 2981741) B2981741
theorem B4472621 : Blo 1987435 4472621 := bbase (se 3 (by rfl) ⟨838616, by rfl⟩ : syracuseStep 4472621 = 1677233) (by norm_num)
theorem B2981747 : Blo 1987435 2981747 := bstep (se 1 (by rfl) ⟨2236310, by rfl⟩ : syracuseStep 2981747 = 4472621) B4472621
theorem B1987831 : Blo 1987435 1987831 := bstep (se 1 (by rfl) ⟨1490873, by rfl⟩ : syracuseStep 1987831 = 2981747) B2981747
theorem B8491013 : Blo 1987435 8491013 := bbase (se 4 (by rfl) ⟨796032, by rfl⟩ : syracuseStep 8491013 = 1592065) (by norm_num)
theorem B5660675 : Blo 1987435 5660675 := bstep (se 1 (by rfl) ⟨4245506, by rfl⟩ : syracuseStep 5660675 = 8491013) B8491013
theorem B3773783 : Blo 1987435 3773783 := bstep (se 1 (by rfl) ⟨2830337, by rfl⟩ : syracuseStep 3773783 = 5660675) B5660675
theorem B2515855 : Blo 1987435 2515855 := bstep (se 1 (by rfl) ⟨1886891, by rfl⟩ : syracuseStep 2515855 = 3773783) B3773783
theorem B3354473 : Blo 1987435 3354473 := bstep (se 2 (by rfl) ⟨1257927, by rfl⟩ : syracuseStep 3354473 = 2515855) B2515855
theorem B2236315 : Blo 1987435 2236315 := bstep (se 1 (by rfl) ⟨1677236, by rfl⟩ : syracuseStep 2236315 = 3354473) B3354473
theorem B2981753 : Blo 1987435 2981753 := bstep (se 2 (by rfl) ⟨1118157, by rfl⟩ : syracuseStep 2981753 = 2236315) B2236315
theorem B1987835 : Blo 1987435 1987835 := bstep (se 1 (by rfl) ⟨1490876, by rfl⟩ : syracuseStep 1987835 = 2981753) B2981753
theorem B2014961 : Blo 1987435 2014961 := bbase (se 2 (by rfl) ⟨755610, by rfl⟩ : syracuseStep 2014961 = 1511221) (by norm_num)
theorem B5373229 : Blo 1987435 5373229 := bstep (se 3 (by rfl) ⟨1007480, by rfl⟩ : syracuseStep 5373229 = 2014961) B2014961
theorem B7164305 : Blo 1987435 7164305 := bstep (se 2 (by rfl) ⟨2686614, by rfl⟩ : syracuseStep 7164305 = 5373229) B5373229
theorem B4776203 : Blo 1987435 4776203 := bstep (se 1 (by rfl) ⟨3582152, by rfl⟩ : syracuseStep 4776203 = 7164305) B7164305
theorem B12736541 : Blo 1987435 12736541 := bstep (se 3 (by rfl) ⟨2388101, by rfl⟩ : syracuseStep 12736541 = 4776203) B4776203
theorem B33964109 : Blo 1987435 33964109 := bstep (se 3 (by rfl) ⟨6368270, by rfl⟩ : syracuseStep 33964109 = 12736541) B12736541
theorem B22642739 : Blo 1987435 22642739 := bstep (se 1 (by rfl) ⟨16982054, by rfl⟩ : syracuseStep 22642739 = 33964109) B33964109
theorem B15095159 : Blo 1987435 15095159 := bstep (se 1 (by rfl) ⟨11321369, by rfl⟩ : syracuseStep 15095159 = 22642739) B22642739
theorem B10063439 : Blo 1987435 10063439 := bstep (se 1 (by rfl) ⟨7547579, by rfl⟩ : syracuseStep 10063439 = 15095159) B15095159
theorem B6708959 : Blo 1987435 6708959 := bstep (se 1 (by rfl) ⟨5031719, by rfl⟩ : syracuseStep 6708959 = 10063439) B10063439
theorem B4472639 : Blo 1987435 4472639 := bstep (se 1 (by rfl) ⟨3354479, by rfl⟩ : syracuseStep 4472639 = 6708959) B6708959
theorem B2981759 : Blo 1987435 2981759 := bstep (se 1 (by rfl) ⟨2236319, by rfl⟩ : syracuseStep 2981759 = 4472639) B4472639
theorem B1987839 : Blo 1987435 1987839 := bstep (se 1 (by rfl) ⟨1490879, by rfl⟩ : syracuseStep 1987839 = 2981759) B2981759
theorem B2981765 : Blo 1987435 2981765 := bbase (se 4 (by rfl) ⟨279540, by rfl⟩ : syracuseStep 2981765 = 559081) (by norm_num)
theorem B1987843 : Blo 1987435 1987843 := bstep (se 1 (by rfl) ⟨1490882, by rfl⟩ : syracuseStep 1987843 = 2981765) B2981765
theorem B3354493 : Blo 1987435 3354493 := bbase (se 3 (by rfl) ⟨628967, by rfl⟩ : syracuseStep 3354493 = 1257935) (by norm_num)
theorem B4472657 : Blo 1987435 4472657 := bstep (se 2 (by rfl) ⟨1677246, by rfl⟩ : syracuseStep 4472657 = 3354493) B3354493
theorem B2981771 : Blo 1987435 2981771 := bstep (se 1 (by rfl) ⟨2236328, by rfl⟩ : syracuseStep 2981771 = 4472657) B4472657
theorem B1987847 : Blo 1987435 1987847 := bstep (se 1 (by rfl) ⟨1490885, by rfl⟩ : syracuseStep 1987847 = 2981771) B2981771
theorem B2236333 : Blo 1987435 2236333 := bbase (se 3 (by rfl) ⟨419312, by rfl⟩ : syracuseStep 2236333 = 838625) (by norm_num)
theorem B2981777 : Blo 1987435 2981777 := bstep (se 2 (by rfl) ⟨1118166, by rfl⟩ : syracuseStep 2981777 = 2236333) B2236333
theorem B1987851 : Blo 1987435 1987851 := bstep (se 1 (by rfl) ⟨1490888, by rfl⟩ : syracuseStep 1987851 = 2981777) B2981777
theorem B6709013 : Blo 1987435 6709013 := bbase (se 6 (by rfl) ⟨157242, by rfl⟩ : syracuseStep 6709013 = 314485) (by norm_num)
theorem B4472675 : Blo 1987435 4472675 := bstep (se 1 (by rfl) ⟨3354506, by rfl⟩ : syracuseStep 4472675 = 6709013) B6709013
theorem B2981783 : Blo 1987435 2981783 := bstep (se 1 (by rfl) ⟨2236337, by rfl⟩ : syracuseStep 2981783 = 4472675) B4472675
theorem B1987855 : Blo 1987435 1987855 := bstep (se 1 (by rfl) ⟨1490891, by rfl⟩ : syracuseStep 1987855 = 2981783) B2981783
theorem B2981789 : Blo 1987435 2981789 := bbase (se 3 (by rfl) ⟨559085, by rfl⟩ : syracuseStep 2981789 = 1118171) (by norm_num)
theorem B1987859 : Blo 1987435 1987859 := bstep (se 1 (by rfl) ⟨1490894, by rfl⟩ : syracuseStep 1987859 = 2981789) B2981789
theorem B4472693 : Blo 1987435 4472693 := bbase (se 5 (by rfl) ⟨209657, by rfl⟩ : syracuseStep 4472693 = 419315) (by norm_num)
theorem B2981795 : Blo 1987435 2981795 := bstep (se 1 (by rfl) ⟨2236346, by rfl⟩ : syracuseStep 2981795 = 4472693) B4472693
theorem B1987863 : Blo 1987435 1987863 := bstep (se 1 (by rfl) ⟨1490897, by rfl⟩ : syracuseStep 1987863 = 2981795) B2981795
theorem B19365749 : Blo 1987435 19365749 := bbase (se 5 (by rfl) ⟨907769, by rfl⟩ : syracuseStep 19365749 = 1815539) (by norm_num)
theorem B12910499 : Blo 1987435 12910499 := bstep (se 1 (by rfl) ⟨9682874, by rfl⟩ : syracuseStep 12910499 = 19365749) B19365749
theorem B8606999 : Blo 1987435 8606999 := bstep (se 1 (by rfl) ⟨6455249, by rfl⟩ : syracuseStep 8606999 = 12910499) B12910499
theorem B22951997 : Blo 1987435 22951997 := bstep (se 3 (by rfl) ⟨4303499, by rfl⟩ : syracuseStep 22951997 = 8606999) B8606999
theorem B15301331 : Blo 1987435 15301331 := bstep (se 1 (by rfl) ⟨11475998, by rfl⟩ : syracuseStep 15301331 = 22951997) B22951997
theorem B10200887 : Blo 1987435 10200887 := bstep (se 1 (by rfl) ⟨7650665, by rfl⟩ : syracuseStep 10200887 = 15301331) B15301331
theorem B6800591 : Blo 1987435 6800591 := bstep (se 1 (by rfl) ⟨5100443, by rfl⟩ : syracuseStep 6800591 = 10200887) B10200887
theorem B4533727 : Blo 1987435 4533727 := bstep (se 1 (by rfl) ⟨3400295, by rfl⟩ : syracuseStep 4533727 = 6800591) B6800591
theorem B6044969 : Blo 1987435 6044969 := bstep (se 2 (by rfl) ⟨2266863, by rfl⟩ : syracuseStep 6044969 = 4533727) B4533727
theorem B16119917 : Blo 1987435 16119917 := bstep (se 3 (by rfl) ⟨3022484, by rfl⟩ : syracuseStep 16119917 = 6044969) B6044969
theorem B10746611 : Blo 1987435 10746611 := bstep (se 1 (by rfl) ⟨8059958, by rfl⟩ : syracuseStep 10746611 = 16119917) B16119917
theorem B7164407 : Blo 1987435 7164407 := bstep (se 1 (by rfl) ⟨5373305, by rfl⟩ : syracuseStep 7164407 = 10746611) B10746611
theorem B19105085 : Blo 1987435 19105085 := bstep (se 3 (by rfl) ⟨3582203, by rfl⟩ : syracuseStep 19105085 = 7164407) B7164407
theorem B12736723 : Blo 1987435 12736723 := bstep (se 1 (by rfl) ⟨9552542, by rfl⟩ : syracuseStep 12736723 = 19105085) B19105085
theorem B16982297 : Blo 1987435 16982297 := bstep (se 2 (by rfl) ⟨6368361, by rfl⟩ : syracuseStep 16982297 = 12736723) B12736723
theorem B11321531 : Blo 1987435 11321531 := bstep (se 1 (by rfl) ⟨8491148, by rfl⟩ : syracuseStep 11321531 = 16982297) B16982297
theorem B7547687 : Blo 1987435 7547687 := bstep (se 1 (by rfl) ⟨5660765, by rfl⟩ : syracuseStep 7547687 = 11321531) B11321531
theorem B5031791 : Blo 1987435 5031791 := bstep (se 1 (by rfl) ⟨3773843, by rfl⟩ : syracuseStep 5031791 = 7547687) B7547687
theorem B3354527 : Blo 1987435 3354527 := bstep (se 1 (by rfl) ⟨2515895, by rfl⟩ : syracuseStep 3354527 = 5031791) B5031791
theorem B2236351 : Blo 1987435 2236351 := bstep (se 1 (by rfl) ⟨1677263, by rfl⟩ : syracuseStep 2236351 = 3354527) B3354527
theorem B2981801 : Blo 1987435 2981801 := bstep (se 2 (by rfl) ⟨1118175, by rfl⟩ : syracuseStep 2981801 = 2236351) B2236351
theorem B1987867 : Blo 1987435 1987867 := bstep (se 1 (by rfl) ⟨1490900, by rfl⟩ : syracuseStep 1987867 = 2981801) B2981801
theorem B7547701 : Blo 1987435 7547701 := bbase (se 5 (by rfl) ⟨353798, by rfl⟩ : syracuseStep 7547701 = 707597) (by norm_num)
theorem B10063601 : Blo 1987435 10063601 := bstep (se 2 (by rfl) ⟨3773850, by rfl⟩ : syracuseStep 10063601 = 7547701) B7547701
theorem B6709067 : Blo 1987435 6709067 := bstep (se 1 (by rfl) ⟨5031800, by rfl⟩ : syracuseStep 6709067 = 10063601) B10063601
theorem B4472711 : Blo 1987435 4472711 := bstep (se 1 (by rfl) ⟨3354533, by rfl⟩ : syracuseStep 4472711 = 6709067) B6709067
theorem B2981807 : Blo 1987435 2981807 := bstep (se 1 (by rfl) ⟨2236355, by rfl⟩ : syracuseStep 2981807 = 4472711) B4472711
theorem B1987871 : Blo 1987435 1987871 := bstep (se 1 (by rfl) ⟨1490903, by rfl⟩ : syracuseStep 1987871 = 2981807) B2981807
theorem B2981813 : Blo 1987435 2981813 := bbase (se 5 (by rfl) ⟨139772, by rfl⟩ : syracuseStep 2981813 = 279545) (by norm_num)
theorem B1987875 : Blo 1987435 1987875 := bstep (se 1 (by rfl) ⟨1490906, by rfl⟩ : syracuseStep 1987875 = 2981813) B2981813
theorem B5031821 : Blo 1987435 5031821 := bbase (se 3 (by rfl) ⟨943466, by rfl⟩ : syracuseStep 5031821 = 1886933) (by norm_num)
theorem B3354547 : Blo 1987435 3354547 := bstep (se 1 (by rfl) ⟨2515910, by rfl⟩ : syracuseStep 3354547 = 5031821) B5031821
theorem B4472729 : Blo 1987435 4472729 := bstep (se 2 (by rfl) ⟨1677273, by rfl⟩ : syracuseStep 4472729 = 3354547) B3354547
theorem B2981819 : Blo 1987435 2981819 := bstep (se 1 (by rfl) ⟨2236364, by rfl⟩ : syracuseStep 2981819 = 4472729) B4472729
theorem B1987879 : Blo 1987435 1987879 := bstep (se 1 (by rfl) ⟨1490909, by rfl⟩ : syracuseStep 1987879 = 2981819) B2981819
theorem B2236369 : Blo 1987435 2236369 := bbase (se 2 (by rfl) ⟨838638, by rfl⟩ : syracuseStep 2236369 = 1677277) (by norm_num)
theorem B2981825 : Blo 1987435 2981825 := bstep (se 2 (by rfl) ⟨1118184, by rfl⟩ : syracuseStep 2981825 = 2236369) B2236369
theorem B1987883 : Blo 1987435 1987883 := bstep (se 1 (by rfl) ⟨1490912, by rfl⟩ : syracuseStep 1987883 = 2981825) B2981825
theorem B3184213 : Blo 1987435 3184213 := bbase (se 8 (by rfl) ⟨18657, by rfl⟩ : syracuseStep 3184213 = 37315) (by norm_num)
theorem B4245617 : Blo 1987435 4245617 := bstep (se 2 (by rfl) ⟨1592106, by rfl⟩ : syracuseStep 4245617 = 3184213) B3184213
theorem B2830411 : Blo 1987435 2830411 := bstep (se 1 (by rfl) ⟨2122808, by rfl⟩ : syracuseStep 2830411 = 4245617) B4245617
theorem B3773881 : Blo 1987435 3773881 := bstep (se 2 (by rfl) ⟨1415205, by rfl⟩ : syracuseStep 3773881 = 2830411) B2830411
theorem B5031841 : Blo 1987435 5031841 := bstep (se 2 (by rfl) ⟨1886940, by rfl⟩ : syracuseStep 5031841 = 3773881) B3773881
theorem B6709121 : Blo 1987435 6709121 := bstep (se 2 (by rfl) ⟨2515920, by rfl⟩ : syracuseStep 6709121 = 5031841) B5031841
theorem B4472747 : Blo 1987435 4472747 := bstep (se 1 (by rfl) ⟨3354560, by rfl⟩ : syracuseStep 4472747 = 6709121) B6709121
theorem B2981831 : Blo 1987435 2981831 := bstep (se 1 (by rfl) ⟨2236373, by rfl⟩ : syracuseStep 2981831 = 4472747) B4472747
theorem B1987887 : Blo 1987435 1987887 := bstep (se 1 (by rfl) ⟨1490915, by rfl⟩ : syracuseStep 1987887 = 2981831) B2981831
theorem B2981837 : Blo 1987435 2981837 := bbase (se 3 (by rfl) ⟨559094, by rfl⟩ : syracuseStep 2981837 = 1118189) (by norm_num)
theorem B1987891 : Blo 1987435 1987891 := bstep (se 1 (by rfl) ⟨1490918, by rfl⟩ : syracuseStep 1987891 = 2981837) B2981837
theorem B4472765 : Blo 1987435 4472765 := bbase (se 3 (by rfl) ⟨838643, by rfl⟩ : syracuseStep 4472765 = 1677287) (by norm_num)
theorem B2981843 : Blo 1987435 2981843 := bstep (se 1 (by rfl) ⟨2236382, by rfl⟩ : syracuseStep 2981843 = 4472765) B4472765
theorem B1987895 : Blo 1987435 1987895 := bstep (se 1 (by rfl) ⟨1490921, by rfl⟩ : syracuseStep 1987895 = 2981843) B2981843
theorem B3354581 : Blo 1987435 3354581 := bbase (se 7 (by rfl) ⟨39311, by rfl⟩ : syracuseStep 3354581 = 78623) (by norm_num)
theorem B2236387 : Blo 1987435 2236387 := bstep (se 1 (by rfl) ⟨1677290, by rfl⟩ : syracuseStep 2236387 = 3354581) B3354581
theorem B2981849 : Blo 1987435 2981849 := bstep (se 2 (by rfl) ⟨1118193, by rfl⟩ : syracuseStep 2981849 = 2236387) B2236387
theorem B1987899 : Blo 1987435 1987899 := bstep (se 1 (by rfl) ⟨1490924, by rfl⟩ : syracuseStep 1987899 = 2981849) B2981849
theorem B8491301 : Blo 1987435 8491301 := bbase (se 4 (by rfl) ⟨796059, by rfl⟩ : syracuseStep 8491301 = 1592119) (by norm_num)
theorem B5660867 : Blo 1987435 5660867 := bstep (se 1 (by rfl) ⟨4245650, by rfl⟩ : syracuseStep 5660867 = 8491301) B8491301
theorem B15095645 : Blo 1987435 15095645 := bstep (se 3 (by rfl) ⟨2830433, by rfl⟩ : syracuseStep 15095645 = 5660867) B5660867
theorem B10063763 : Blo 1987435 10063763 := bstep (se 1 (by rfl) ⟨7547822, by rfl⟩ : syracuseStep 10063763 = 15095645) B15095645
theorem B6709175 : Blo 1987435 6709175 := bstep (se 1 (by rfl) ⟨5031881, by rfl⟩ : syracuseStep 6709175 = 10063763) B10063763
theorem B4472783 : Blo 1987435 4472783 := bstep (se 1 (by rfl) ⟨3354587, by rfl⟩ : syracuseStep 4472783 = 6709175) B6709175
theorem B2981855 : Blo 1987435 2981855 := bstep (se 1 (by rfl) ⟨2236391, by rfl⟩ : syracuseStep 2981855 = 4472783) B4472783
theorem B1987903 : Blo 1987435 1987903 := bstep (se 1 (by rfl) ⟨1490927, by rfl⟩ : syracuseStep 1987903 = 2981855) B2981855
theorem B2981861 : Blo 1987435 2981861 := bbase (se 4 (by rfl) ⟨279549, by rfl⟩ : syracuseStep 2981861 = 559099) (by norm_num)
theorem B1987907 : Blo 1987435 1987907 := bstep (se 1 (by rfl) ⟨1490930, by rfl⟩ : syracuseStep 1987907 = 2981861) B2981861
theorem B4030069 : Blo 1987435 4030069 := bbase (se 5 (by rfl) ⟨188909, by rfl⟩ : syracuseStep 4030069 = 377819) (by norm_num)
theorem B5373425 : Blo 1987435 5373425 := bstep (se 2 (by rfl) ⟨2015034, by rfl⟩ : syracuseStep 5373425 = 4030069) B4030069
theorem B14329133 : Blo 1987435 14329133 := bstep (se 3 (by rfl) ⟨2686712, by rfl⟩ : syracuseStep 14329133 = 5373425) B5373425
theorem B9552755 : Blo 1987435 9552755 := bstep (se 1 (by rfl) ⟨7164566, by rfl⟩ : syracuseStep 9552755 = 14329133) B14329133
theorem B6368503 : Blo 1987435 6368503 := bstep (se 1 (by rfl) ⟨4776377, by rfl⟩ : syracuseStep 6368503 = 9552755) B9552755
theorem B8491337 : Blo 1987435 8491337 := bstep (se 2 (by rfl) ⟨3184251, by rfl⟩ : syracuseStep 8491337 = 6368503) B6368503
theorem B5660891 : Blo 1987435 5660891 := bstep (se 1 (by rfl) ⟨4245668, by rfl⟩ : syracuseStep 5660891 = 8491337) B8491337
theorem B3773927 : Blo 1987435 3773927 := bstep (se 1 (by rfl) ⟨2830445, by rfl⟩ : syracuseStep 3773927 = 5660891) B5660891
theorem B2515951 : Blo 1987435 2515951 := bstep (se 1 (by rfl) ⟨1886963, by rfl⟩ : syracuseStep 2515951 = 3773927) B3773927
theorem B3354601 : Blo 1987435 3354601 := bstep (se 2 (by rfl) ⟨1257975, by rfl⟩ : syracuseStep 3354601 = 2515951) B2515951
theorem B4472801 : Blo 1987435 4472801 := bstep (se 2 (by rfl) ⟨1677300, by rfl⟩ : syracuseStep 4472801 = 3354601) B3354601
theorem B2981867 : Blo 1987435 2981867 := bstep (se 1 (by rfl) ⟨2236400, by rfl⟩ : syracuseStep 2981867 = 4472801) B4472801
theorem B1987911 : Blo 1987435 1987911 := bstep (se 1 (by rfl) ⟨1490933, by rfl⟩ : syracuseStep 1987911 = 2981867) B2981867
theorem B2236405 : Blo 1987435 2236405 := bbase (se 5 (by rfl) ⟨104831, by rfl⟩ : syracuseStep 2236405 = 209663) (by norm_num)
theorem B2981873 : Blo 1987435 2981873 := bstep (se 2 (by rfl) ⟨1118202, by rfl⟩ : syracuseStep 2981873 = 2236405) B2236405
theorem B1987915 : Blo 1987435 1987915 := bstep (se 1 (by rfl) ⟨1490936, by rfl⟩ : syracuseStep 1987915 = 2981873) B2981873
theorem B2515961 : Blo 1987435 2515961 := bbase (se 2 (by rfl) ⟨943485, by rfl⟩ : syracuseStep 2515961 = 1886971) (by norm_num)
theorem B6709229 : Blo 1987435 6709229 := bstep (se 3 (by rfl) ⟨1257980, by rfl⟩ : syracuseStep 6709229 = 2515961) B2515961
theorem B4472819 : Blo 1987435 4472819 := bstep (se 1 (by rfl) ⟨3354614, by rfl⟩ : syracuseStep 4472819 = 6709229) B6709229
theorem B2981879 : Blo 1987435 2981879 := bstep (se 1 (by rfl) ⟨2236409, by rfl⟩ : syracuseStep 2981879 = 4472819) B4472819
theorem B1987919 : Blo 1987435 1987919 := bstep (se 1 (by rfl) ⟨1490939, by rfl⟩ : syracuseStep 1987919 = 2981879) B2981879
theorem B2981885 : Blo 1987435 2981885 := bbase (se 3 (by rfl) ⟨559103, by rfl⟩ : syracuseStep 2981885 = 1118207) (by norm_num)
theorem B1987923 : Blo 1987435 1987923 := bstep (se 1 (by rfl) ⟨1490942, by rfl⟩ : syracuseStep 1987923 = 2981885) B2981885
theorem B4472837 : Blo 1987435 4472837 := bbase (se 4 (by rfl) ⟨419328, by rfl⟩ : syracuseStep 4472837 = 838657) (by norm_num)
theorem B2981891 : Blo 1987435 2981891 := bstep (se 1 (by rfl) ⟨2236418, by rfl⟩ : syracuseStep 2981891 = 4472837) B4472837
theorem B1987927 : Blo 1987435 1987927 := bstep (se 1 (by rfl) ⟨1490945, by rfl⟩ : syracuseStep 1987927 = 2981891) B2981891
theorem B3773965 : Blo 1987435 3773965 := bbase (se 3 (by rfl) ⟨707618, by rfl⟩ : syracuseStep 3773965 = 1415237) (by norm_num)
theorem B5031953 : Blo 1987435 5031953 := bstep (se 2 (by rfl) ⟨1886982, by rfl⟩ : syracuseStep 5031953 = 3773965) B3773965
theorem B3354635 : Blo 1987435 3354635 := bstep (se 1 (by rfl) ⟨2515976, by rfl⟩ : syracuseStep 3354635 = 5031953) B5031953
theorem B2236423 : Blo 1987435 2236423 := bstep (se 1 (by rfl) ⟨1677317, by rfl⟩ : syracuseStep 2236423 = 3354635) B3354635
theorem B2981897 : Blo 1987435 2981897 := bstep (se 2 (by rfl) ⟨1118211, by rfl⟩ : syracuseStep 2981897 = 2236423) B2236423
theorem B1987931 : Blo 1987435 1987931 := bstep (se 1 (by rfl) ⟨1490948, by rfl⟩ : syracuseStep 1987931 = 2981897) B2981897
theorem B10063925 : Blo 1987435 10063925 := bbase (se 5 (by rfl) ⟨471746, by rfl⟩ : syracuseStep 10063925 = 943493) (by norm_num)
theorem B6709283 : Blo 1987435 6709283 := bstep (se 1 (by rfl) ⟨5031962, by rfl⟩ : syracuseStep 6709283 = 10063925) B10063925
theorem B4472855 : Blo 1987435 4472855 := bstep (se 1 (by rfl) ⟨3354641, by rfl⟩ : syracuseStep 4472855 = 6709283) B6709283
theorem B2981903 : Blo 1987435 2981903 := bstep (se 1 (by rfl) ⟨2236427, by rfl⟩ : syracuseStep 2981903 = 4472855) B4472855
theorem B1987935 : Blo 1987435 1987935 := bstep (se 1 (by rfl) ⟨1490951, by rfl⟩ : syracuseStep 1987935 = 2981903) B2981903
theorem B2981909 : Blo 1987435 2981909 := bbase (se 6 (by rfl) ⟨69888, by rfl⟩ : syracuseStep 2981909 = 139777) (by norm_num)
theorem B1987939 : Blo 1987435 1987939 := bstep (se 1 (by rfl) ⟨1490954, by rfl⟩ : syracuseStep 1987939 = 2981909) B2981909
theorem B4030133 : Blo 1987435 4030133 := bbase (se 5 (by rfl) ⟨188912, by rfl⟩ : syracuseStep 4030133 = 377825) (by norm_num)
theorem B10747021 : Blo 1987435 10747021 := bstep (se 3 (by rfl) ⟨2015066, by rfl⟩ : syracuseStep 10747021 = 4030133) B4030133
theorem B14329361 : Blo 1987435 14329361 := bstep (se 2 (by rfl) ⟨5373510, by rfl⟩ : syracuseStep 14329361 = 10747021) B10747021
theorem B9552907 : Blo 1987435 9552907 := bstep (se 1 (by rfl) ⟨7164680, by rfl⟩ : syracuseStep 9552907 = 14329361) B14329361
theorem B12737209 : Blo 1987435 12737209 := bstep (se 2 (by rfl) ⟨4776453, by rfl⟩ : syracuseStep 12737209 = 9552907) B9552907
theorem B16982945 : Blo 1987435 16982945 := bstep (se 2 (by rfl) ⟨6368604, by rfl⟩ : syracuseStep 16982945 = 12737209) B12737209
theorem B11321963 : Blo 1987435 11321963 := bstep (se 1 (by rfl) ⟨8491472, by rfl⟩ : syracuseStep 11321963 = 16982945) B16982945
theorem B7547975 : Blo 1987435 7547975 := bstep (se 1 (by rfl) ⟨5660981, by rfl⟩ : syracuseStep 7547975 = 11321963) B11321963
theorem B5031983 : Blo 1987435 5031983 := bstep (se 1 (by rfl) ⟨3773987, by rfl⟩ : syracuseStep 5031983 = 7547975) B7547975
theorem B3354655 : Blo 1987435 3354655 := bstep (se 1 (by rfl) ⟨2515991, by rfl⟩ : syracuseStep 3354655 = 5031983) B5031983
theorem B4472873 : Blo 1987435 4472873 := bstep (se 2 (by rfl) ⟨1677327, by rfl⟩ : syracuseStep 4472873 = 3354655) B3354655
theorem B2981915 : Blo 1987435 2981915 := bstep (se 1 (by rfl) ⟨2236436, by rfl⟩ : syracuseStep 2981915 = 4472873) B4472873
theorem B1987943 : Blo 1987435 1987943 := bstep (se 1 (by rfl) ⟨1490957, by rfl⟩ : syracuseStep 1987943 = 2981915) B2981915
theorem B2236441 : Blo 1987435 2236441 := bbase (se 2 (by rfl) ⟨838665, by rfl⟩ : syracuseStep 2236441 = 1677331) (by norm_num)
theorem B2981921 : Blo 1987435 2981921 := bstep (se 2 (by rfl) ⟨1118220, by rfl⟩ : syracuseStep 2981921 = 2236441) B2236441
theorem B1987947 : Blo 1987435 1987947 := bstep (se 1 (by rfl) ⟨1490960, by rfl⟩ : syracuseStep 1987947 = 2981921) B2981921
theorem B7548005 : Blo 1987435 7548005 := bbase (se 4 (by rfl) ⟨707625, by rfl⟩ : syracuseStep 7548005 = 1415251) (by norm_num)
theorem B5032003 : Blo 1987435 5032003 := bstep (se 1 (by rfl) ⟨3774002, by rfl⟩ : syracuseStep 5032003 = 7548005) B7548005
theorem B6709337 : Blo 1987435 6709337 := bstep (se 2 (by rfl) ⟨2516001, by rfl⟩ : syracuseStep 6709337 = 5032003) B5032003
theorem B4472891 : Blo 1987435 4472891 := bstep (se 1 (by rfl) ⟨3354668, by rfl⟩ : syracuseStep 4472891 = 6709337) B6709337
theorem B2981927 : Blo 1987435 2981927 := bstep (se 1 (by rfl) ⟨2236445, by rfl⟩ : syracuseStep 2981927 = 4472891) B4472891
theorem B1987951 : Blo 1987435 1987951 := bstep (se 1 (by rfl) ⟨1490963, by rfl⟩ : syracuseStep 1987951 = 2981927) B2981927
theorem B2981933 : Blo 1987435 2981933 := bbase (se 3 (by rfl) ⟨559112, by rfl⟩ : syracuseStep 2981933 = 1118225) (by norm_num)
theorem B1987955 : Blo 1987435 1987955 := bstep (se 1 (by rfl) ⟨1490966, by rfl⟩ : syracuseStep 1987955 = 2981933) B2981933
theorem B4472909 : Blo 1987435 4472909 := bbase (se 3 (by rfl) ⟨838670, by rfl⟩ : syracuseStep 4472909 = 1677341) (by norm_num)
theorem B2981939 : Blo 1987435 2981939 := bstep (se 1 (by rfl) ⟨2236454, by rfl⟩ : syracuseStep 2981939 = 4472909) B4472909
theorem B1987959 : Blo 1987435 1987959 := bstep (se 1 (by rfl) ⟨1490969, by rfl⟩ : syracuseStep 1987959 = 2981939) B2981939
theorem B2516017 : Blo 1987435 2516017 := bbase (se 2 (by rfl) ⟨943506, by rfl⟩ : syracuseStep 2516017 = 1887013) (by norm_num)
theorem B3354689 : Blo 1987435 3354689 := bstep (se 2 (by rfl) ⟨1258008, by rfl⟩ : syracuseStep 3354689 = 2516017) B2516017
theorem B2236459 : Blo 1987435 2236459 := bstep (se 1 (by rfl) ⟨1677344, by rfl⟩ : syracuseStep 2236459 = 3354689) B3354689
theorem B2981945 : Blo 1987435 2981945 := bstep (se 2 (by rfl) ⟨1118229, by rfl⟩ : syracuseStep 2981945 = 2236459) B2236459
theorem B1987963 : Blo 1987435 1987963 := bstep (se 1 (by rfl) ⟨1490972, by rfl⟩ : syracuseStep 1987963 = 2981945) B2981945
theorem B36271637 : Blo 1987435 36271637 := bbase (se 6 (by rfl) ⟨850116, by rfl⟩ : syracuseStep 36271637 = 1700233) (by norm_num)
theorem B24181091 : Blo 1987435 24181091 := bstep (se 1 (by rfl) ⟨18135818, by rfl⟩ : syracuseStep 24181091 = 36271637) B36271637
theorem B16120727 : Blo 1987435 16120727 := bstep (se 1 (by rfl) ⟨12090545, by rfl⟩ : syracuseStep 16120727 = 24181091) B24181091
theorem B10747151 : Blo 1987435 10747151 := bstep (se 1 (by rfl) ⟨8060363, by rfl⟩ : syracuseStep 10747151 = 16120727) B16120727
theorem B7164767 : Blo 1987435 7164767 := bstep (se 1 (by rfl) ⟨5373575, by rfl⟩ : syracuseStep 7164767 = 10747151) B10747151
theorem B4776511 : Blo 1987435 4776511 := bstep (se 1 (by rfl) ⟨3582383, by rfl⟩ : syracuseStep 4776511 = 7164767) B7164767
theorem B6368681 : Blo 1987435 6368681 := bstep (se 2 (by rfl) ⟨2388255, by rfl⟩ : syracuseStep 6368681 = 4776511) B4776511
theorem B4245787 : Blo 1987435 4245787 := bstep (se 1 (by rfl) ⟨3184340, by rfl⟩ : syracuseStep 4245787 = 6368681) B6368681
theorem B22644197 : Blo 1987435 22644197 := bstep (se 4 (by rfl) ⟨2122893, by rfl⟩ : syracuseStep 22644197 = 4245787) B4245787
theorem B15096131 : Blo 1987435 15096131 := bstep (se 1 (by rfl) ⟨11322098, by rfl⟩ : syracuseStep 15096131 = 22644197) B22644197
theorem B10064087 : Blo 1987435 10064087 := bstep (se 1 (by rfl) ⟨7548065, by rfl⟩ : syracuseStep 10064087 = 15096131) B15096131
theorem B6709391 : Blo 1987435 6709391 := bstep (se 1 (by rfl) ⟨5032043, by rfl⟩ : syracuseStep 6709391 = 10064087) B10064087
theorem B4472927 : Blo 1987435 4472927 := bstep (se 1 (by rfl) ⟨3354695, by rfl⟩ : syracuseStep 4472927 = 6709391) B6709391
theorem B2981951 : Blo 1987435 2981951 := bstep (se 1 (by rfl) ⟨2236463, by rfl⟩ : syracuseStep 2981951 = 4472927) B4472927
theorem B1987967 : Blo 1987435 1987967 := bstep (se 1 (by rfl) ⟨1490975, by rfl⟩ : syracuseStep 1987967 = 2981951) B2981951
theorem B2981957 : Blo 1987435 2981957 := bbase (se 4 (by rfl) ⟨279558, by rfl⟩ : syracuseStep 2981957 = 559117) (by norm_num)
theorem B1987971 : Blo 1987435 1987971 := bstep (se 1 (by rfl) ⟨1490978, by rfl⟩ : syracuseStep 1987971 = 2981957) B2981957
theorem B3354709 : Blo 1987435 3354709 := bbase (se 8 (by rfl) ⟨19656, by rfl⟩ : syracuseStep 3354709 = 39313) (by norm_num)
theorem B4472945 : Blo 1987435 4472945 := bstep (se 2 (by rfl) ⟨1677354, by rfl⟩ : syracuseStep 4472945 = 3354709) B3354709
theorem B2981963 : Blo 1987435 2981963 := bstep (se 1 (by rfl) ⟨2236472, by rfl⟩ : syracuseStep 2981963 = 4472945) B4472945
theorem B1987975 : Blo 1987435 1987975 := bstep (se 1 (by rfl) ⟨1490981, by rfl⟩ : syracuseStep 1987975 = 2981963) B2981963
theorem B2236477 : Blo 1987435 2236477 := bbase (se 3 (by rfl) ⟨419339, by rfl⟩ : syracuseStep 2236477 = 838679) (by norm_num)
theorem B2981969 : Blo 1987435 2981969 := bstep (se 2 (by rfl) ⟨1118238, by rfl⟩ : syracuseStep 2981969 = 2236477) B2236477
theorem B1987979 : Blo 1987435 1987979 := bstep (se 1 (by rfl) ⟨1490984, by rfl⟩ : syracuseStep 1987979 = 2981969) B2981969
theorem B6709445 : Blo 1987435 6709445 := bbase (se 4 (by rfl) ⟨629010, by rfl⟩ : syracuseStep 6709445 = 1258021) (by norm_num)
theorem B4472963 : Blo 1987435 4472963 := bstep (se 1 (by rfl) ⟨3354722, by rfl⟩ : syracuseStep 4472963 = 6709445) B6709445
theorem B2981975 : Blo 1987435 2981975 := bstep (se 1 (by rfl) ⟨2236481, by rfl⟩ : syracuseStep 2981975 = 4472963) B4472963
theorem B1987983 : Blo 1987435 1987983 := bstep (se 1 (by rfl) ⟨1490987, by rfl⟩ : syracuseStep 1987983 = 2981975) B2981975
theorem B2981981 : Blo 1987435 2981981 := bbase (se 3 (by rfl) ⟨559121, by rfl⟩ : syracuseStep 2981981 = 1118243) (by norm_num)
theorem B1987987 : Blo 1987435 1987987 := bstep (se 1 (by rfl) ⟨1490990, by rfl⟩ : syracuseStep 1987987 = 2981981) B2981981
theorem B4472981 : Blo 1987435 4472981 := bbase (se 6 (by rfl) ⟨104835, by rfl⟩ : syracuseStep 4472981 = 209671) (by norm_num)
theorem B2981987 : Blo 1987435 2981987 := bstep (se 1 (by rfl) ⟨2236490, by rfl⟩ : syracuseStep 2981987 = 4472981) B4472981
theorem B1987991 : Blo 1987435 1987991 := bstep (se 1 (by rfl) ⟨1490993, by rfl⟩ : syracuseStep 1987991 = 2981987) B2981987
theorem B2830565 : Blo 1987435 2830565 := bbase (se 4 (by rfl) ⟨265365, by rfl⟩ : syracuseStep 2830565 = 530731) (by norm_num)
theorem B7548173 : Blo 1987435 7548173 := bstep (se 3 (by rfl) ⟨1415282, by rfl⟩ : syracuseStep 7548173 = 2830565) B2830565
theorem B5032115 : Blo 1987435 5032115 := bstep (se 1 (by rfl) ⟨3774086, by rfl⟩ : syracuseStep 5032115 = 7548173) B7548173
theorem B3354743 : Blo 1987435 3354743 := bstep (se 1 (by rfl) ⟨2516057, by rfl⟩ : syracuseStep 3354743 = 5032115) B5032115
theorem B2236495 : Blo 1987435 2236495 := bstep (se 1 (by rfl) ⟨1677371, by rfl⟩ : syracuseStep 2236495 = 3354743) B3354743
theorem B2981993 : Blo 1987435 2981993 := bstep (se 2 (by rfl) ⟨1118247, by rfl⟩ : syracuseStep 2981993 = 2236495) B2236495
theorem B1987995 : Blo 1987435 1987995 := bstep (se 1 (by rfl) ⟨1490996, by rfl⟩ : syracuseStep 1987995 = 2981993) B2981993
theorem B2869189 : Blo 1987435 2869189 := bbase (se 4 (by rfl) ⟨268986, by rfl⟩ : syracuseStep 2869189 = 537973) (by norm_num)
theorem B15302341 : Blo 1987435 15302341 := bstep (se 4 (by rfl) ⟨1434594, by rfl⟩ : syracuseStep 15302341 = 2869189) B2869189
theorem B81612485 : Blo 1987435 81612485 := bstep (se 4 (by rfl) ⟨7651170, by rfl⟩ : syracuseStep 81612485 = 15302341) B15302341
theorem B54408323 : Blo 1987435 54408323 := bstep (se 1 (by rfl) ⟨40806242, by rfl⟩ : syracuseStep 54408323 = 81612485) B81612485
theorem B36272215 : Blo 1987435 36272215 := bstep (se 1 (by rfl) ⟨27204161, by rfl⟩ : syracuseStep 36272215 = 54408323) B54408323
theorem B48362953 : Blo 1987435 48362953 := bstep (se 2 (by rfl) ⟨18136107, by rfl⟩ : syracuseStep 48362953 = 36272215) B36272215
theorem B64483937 : Blo 1987435 64483937 := bstep (se 2 (by rfl) ⟨24181476, by rfl⟩ : syracuseStep 64483937 = 48362953) B48362953
theorem B42989291 : Blo 1987435 42989291 := bstep (se 1 (by rfl) ⟨32241968, by rfl⟩ : syracuseStep 42989291 = 64483937) B64483937
theorem B28659527 : Blo 1987435 28659527 := bstep (se 1 (by rfl) ⟨21494645, by rfl⟩ : syracuseStep 28659527 = 42989291) B42989291
theorem B19106351 : Blo 1987435 19106351 := bstep (se 1 (by rfl) ⟨14329763, by rfl⟩ : syracuseStep 19106351 = 28659527) B28659527
theorem B12737567 : Blo 1987435 12737567 := bstep (se 1 (by rfl) ⟨9553175, by rfl⟩ : syracuseStep 12737567 = 19106351) B19106351
theorem B8491711 : Blo 1987435 8491711 := bstep (se 1 (by rfl) ⟨6368783, by rfl⟩ : syracuseStep 8491711 = 12737567) B12737567
theorem B11322281 : Blo 1987435 11322281 := bstep (se 2 (by rfl) ⟨4245855, by rfl⟩ : syracuseStep 11322281 = 8491711) B8491711
theorem B7548187 : Blo 1987435 7548187 := bstep (se 1 (by rfl) ⟨5661140, by rfl⟩ : syracuseStep 7548187 = 11322281) B11322281
theorem B10064249 : Blo 1987435 10064249 := bstep (se 2 (by rfl) ⟨3774093, by rfl⟩ : syracuseStep 10064249 = 7548187) B7548187
theorem B6709499 : Blo 1987435 6709499 := bstep (se 1 (by rfl) ⟨5032124, by rfl⟩ : syracuseStep 6709499 = 10064249) B10064249
theorem B4472999 : Blo 1987435 4472999 := bstep (se 1 (by rfl) ⟨3354749, by rfl⟩ : syracuseStep 4472999 = 6709499) B6709499
theorem B2981999 : Blo 1987435 2981999 := bstep (se 1 (by rfl) ⟨2236499, by rfl⟩ : syracuseStep 2981999 = 4472999) B4472999
theorem B1987999 : Blo 1987435 1987999 := bstep (se 1 (by rfl) ⟨1490999, by rfl⟩ : syracuseStep 1987999 = 2981999) B2981999
theorem B2982005 : Blo 1987435 2982005 := bbase (se 5 (by rfl) ⟨139781, by rfl⟩ : syracuseStep 2982005 = 279563) (by norm_num)
theorem B1988003 : Blo 1987435 1988003 := bstep (se 1 (by rfl) ⟨1491002, by rfl⟩ : syracuseStep 1988003 = 2982005) B2982005
theorem B3774109 : Blo 1987435 3774109 := bbase (se 3 (by rfl) ⟨707645, by rfl⟩ : syracuseStep 3774109 = 1415291) (by norm_num)
theorem B5032145 : Blo 1987435 5032145 := bstep (se 2 (by rfl) ⟨1887054, by rfl⟩ : syracuseStep 5032145 = 3774109) B3774109
theorem B3354763 : Blo 1987435 3354763 := bstep (se 1 (by rfl) ⟨2516072, by rfl⟩ : syracuseStep 3354763 = 5032145) B5032145
theorem B4473017 : Blo 1987435 4473017 := bstep (se 2 (by rfl) ⟨1677381, by rfl⟩ : syracuseStep 4473017 = 3354763) B3354763
theorem B2982011 : Blo 1987435 2982011 := bstep (se 1 (by rfl) ⟨2236508, by rfl⟩ : syracuseStep 2982011 = 4473017) B4473017
theorem B1988007 : Blo 1987435 1988007 := bstep (se 1 (by rfl) ⟨1491005, by rfl⟩ : syracuseStep 1988007 = 2982011) B2982011
theorem B2236513 : Blo 1987435 2236513 := bbase (se 2 (by rfl) ⟨838692, by rfl⟩ : syracuseStep 2236513 = 1677385) (by norm_num)
theorem B2982017 : Blo 1987435 2982017 := bstep (se 2 (by rfl) ⟨1118256, by rfl⟩ : syracuseStep 2982017 = 2236513) B2236513
theorem B1988011 : Blo 1987435 1988011 := bstep (se 1 (by rfl) ⟨1491008, by rfl⟩ : syracuseStep 1988011 = 2982017) B2982017
theorem B5032165 : Blo 1987435 5032165 := bbase (se 4 (by rfl) ⟨471765, by rfl⟩ : syracuseStep 5032165 = 943531) (by norm_num)
theorem B6709553 : Blo 1987435 6709553 := bstep (se 2 (by rfl) ⟨2516082, by rfl⟩ : syracuseStep 6709553 = 5032165) B5032165
theorem B4473035 : Blo 1987435 4473035 := bstep (se 1 (by rfl) ⟨3354776, by rfl⟩ : syracuseStep 4473035 = 6709553) B6709553
theorem B2982023 : Blo 1987435 2982023 := bstep (se 1 (by rfl) ⟨2236517, by rfl⟩ : syracuseStep 2982023 = 4473035) B4473035
theorem B1988015 : Blo 1987435 1988015 := bstep (se 1 (by rfl) ⟨1491011, by rfl⟩ : syracuseStep 1988015 = 2982023) B2982023
theorem B2982029 : Blo 1987435 2982029 := bbase (se 3 (by rfl) ⟨559130, by rfl⟩ : syracuseStep 2982029 = 1118261) (by norm_num)
theorem B1988019 : Blo 1987435 1988019 := bstep (se 1 (by rfl) ⟨1491014, by rfl⟩ : syracuseStep 1988019 = 2982029) B2982029
theorem B4473053 : Blo 1987435 4473053 := bbase (se 3 (by rfl) ⟨838697, by rfl⟩ : syracuseStep 4473053 = 1677395) (by norm_num)
theorem B2982035 : Blo 1987435 2982035 := bstep (se 1 (by rfl) ⟨2236526, by rfl⟩ : syracuseStep 2982035 = 4473053) B4473053
theorem B1988023 : Blo 1987435 1988023 := bstep (se 1 (by rfl) ⟨1491017, by rfl⟩ : syracuseStep 1988023 = 2982035) B2982035
theorem B3354797 : Blo 1987435 3354797 := bbase (se 3 (by rfl) ⟨629024, by rfl⟩ : syracuseStep 3354797 = 1258049) (by norm_num)
theorem B2236531 : Blo 1987435 2236531 := bstep (se 1 (by rfl) ⟨1677398, by rfl⟩ : syracuseStep 2236531 = 3354797) B3354797
theorem B2982041 : Blo 1987435 2982041 := bstep (se 2 (by rfl) ⟨1118265, by rfl⟩ : syracuseStep 2982041 = 2236531) B2236531
theorem B1988027 : Blo 1987435 1988027 := bstep (se 1 (by rfl) ⟨1491020, by rfl⟩ : syracuseStep 1988027 = 2982041) B2982041
theorem B9683669 : Blo 1987435 9683669 := bbase (se 7 (by rfl) ⟨113480, by rfl⟩ : syracuseStep 9683669 = 226961) (by norm_num)
theorem B25823117 : Blo 1987435 25823117 := bstep (se 3 (by rfl) ⟨4841834, by rfl⟩ : syracuseStep 25823117 = 9683669) B9683669
theorem B17215411 : Blo 1987435 17215411 := bstep (se 1 (by rfl) ⟨12911558, by rfl⟩ : syracuseStep 17215411 = 25823117) B25823117
theorem B22953881 : Blo 1987435 22953881 := bstep (se 2 (by rfl) ⟨8607705, by rfl⟩ : syracuseStep 22953881 = 17215411) B17215411
theorem B61210349 : Blo 1987435 61210349 := bstep (se 3 (by rfl) ⟨11476940, by rfl⟩ : syracuseStep 61210349 = 22953881) B22953881
theorem B40806899 : Blo 1987435 40806899 := bstep (se 1 (by rfl) ⟨30605174, by rfl⟩ : syracuseStep 40806899 = 61210349) B61210349
theorem B27204599 : Blo 1987435 27204599 := bstep (se 1 (by rfl) ⟨20403449, by rfl⟩ : syracuseStep 27204599 = 40806899) B40806899
theorem B18136399 : Blo 1987435 18136399 := bstep (se 1 (by rfl) ⟨13602299, by rfl⟩ : syracuseStep 18136399 = 27204599) B27204599
theorem B24181865 : Blo 1987435 24181865 := bstep (se 2 (by rfl) ⟨9068199, by rfl⟩ : syracuseStep 24181865 = 18136399) B18136399
theorem B16121243 : Blo 1987435 16121243 := bstep (se 1 (by rfl) ⟨12090932, by rfl⟩ : syracuseStep 16121243 = 24181865) B24181865
theorem B10747495 : Blo 1987435 10747495 := bstep (se 1 (by rfl) ⟨8060621, by rfl⟩ : syracuseStep 10747495 = 16121243) B16121243
theorem B57319973 : Blo 1987435 57319973 := bstep (se 4 (by rfl) ⟨5373747, by rfl⟩ : syracuseStep 57319973 = 10747495) B10747495
theorem B38213315 : Blo 1987435 38213315 := bstep (se 1 (by rfl) ⟨28659986, by rfl⟩ : syracuseStep 38213315 = 57319973) B57319973
theorem B25475543 : Blo 1987435 25475543 := bstep (se 1 (by rfl) ⟨19106657, by rfl⟩ : syracuseStep 25475543 = 38213315) B38213315
theorem B16983695 : Blo 1987435 16983695 := bstep (se 1 (by rfl) ⟨12737771, by rfl⟩ : syracuseStep 16983695 = 25475543) B25475543
theorem B11322463 : Blo 1987435 11322463 := bstep (se 1 (by rfl) ⟨8491847, by rfl⟩ : syracuseStep 11322463 = 16983695) B16983695
theorem B15096617 : Blo 1987435 15096617 := bstep (se 2 (by rfl) ⟨5661231, by rfl⟩ : syracuseStep 15096617 = 11322463) B11322463
theorem B10064411 : Blo 1987435 10064411 := bstep (se 1 (by rfl) ⟨7548308, by rfl⟩ : syracuseStep 10064411 = 15096617) B15096617
theorem B6709607 : Blo 1987435 6709607 := bstep (se 1 (by rfl) ⟨5032205, by rfl⟩ : syracuseStep 6709607 = 10064411) B10064411
theorem B4473071 : Blo 1987435 4473071 := bstep (se 1 (by rfl) ⟨3354803, by rfl⟩ : syracuseStep 4473071 = 6709607) B6709607
theorem B2982047 : Blo 1987435 2982047 := bstep (se 1 (by rfl) ⟨2236535, by rfl⟩ : syracuseStep 2982047 = 4473071) B4473071
theorem B1988031 : Blo 1987435 1988031 := bstep (se 1 (by rfl) ⟨1491023, by rfl⟩ : syracuseStep 1988031 = 2982047) B2982047
theorem B2982053 : Blo 1987435 2982053 := bbase (se 4 (by rfl) ⟨279567, by rfl⟩ : syracuseStep 2982053 = 559135) (by norm_num)
theorem B1988035 : Blo 1987435 1988035 := bstep (se 1 (by rfl) ⟨1491026, by rfl⟩ : syracuseStep 1988035 = 2982053) B2982053
theorem B2516113 : Blo 1987435 2516113 := bbase (se 2 (by rfl) ⟨943542, by rfl⟩ : syracuseStep 2516113 = 1887085) (by norm_num)
theorem B3354817 : Blo 1987435 3354817 := bstep (se 2 (by rfl) ⟨1258056, by rfl⟩ : syracuseStep 3354817 = 2516113) B2516113
theorem B4473089 : Blo 1987435 4473089 := bstep (se 2 (by rfl) ⟨1677408, by rfl⟩ : syracuseStep 4473089 = 3354817) B3354817
theorem B2982059 : Blo 1987435 2982059 := bstep (se 1 (by rfl) ⟨2236544, by rfl⟩ : syracuseStep 2982059 = 4473089) B4473089
theorem B1988039 : Blo 1987435 1988039 := bstep (se 1 (by rfl) ⟨1491029, by rfl⟩ : syracuseStep 1988039 = 2982059) B2982059
theorem B2236549 : Blo 1987435 2236549 := bbase (se 4 (by rfl) ⟨209676, by rfl⟩ : syracuseStep 2236549 = 419353) (by norm_num)
theorem B2982065 : Blo 1987435 2982065 := bstep (se 2 (by rfl) ⟨1118274, by rfl⟩ : syracuseStep 2982065 = 2236549) B2236549
theorem B1988043 : Blo 1987435 1988043 := bstep (se 1 (by rfl) ⟨1491032, by rfl⟩ : syracuseStep 1988043 = 2982065) B2982065
theorem B2723557 : Blo 1987435 2723557 := bbase (se 4 (by rfl) ⟨255333, by rfl⟩ : syracuseStep 2723557 = 510667) (by norm_num)
theorem B3631409 : Blo 1987435 3631409 := bstep (se 2 (by rfl) ⟨1361778, by rfl⟩ : syracuseStep 3631409 = 2723557) B2723557
theorem B2420939 : Blo 1987435 2420939 := bstep (se 1 (by rfl) ⟨1815704, by rfl⟩ : syracuseStep 2420939 = 3631409) B3631409
theorem B6455837 : Blo 1987435 6455837 := bstep (se 3 (by rfl) ⟨1210469, by rfl⟩ : syracuseStep 6455837 = 2420939) B2420939
theorem B4303891 : Blo 1987435 4303891 := bstep (se 1 (by rfl) ⟨3227918, by rfl⟩ : syracuseStep 4303891 = 6455837) B6455837
theorem B5738521 : Blo 1987435 5738521 := bstep (se 2 (by rfl) ⟨2151945, by rfl⟩ : syracuseStep 5738521 = 4303891) B4303891
theorem B7651361 : Blo 1987435 7651361 := bstep (se 2 (by rfl) ⟨2869260, by rfl⟩ : syracuseStep 7651361 = 5738521) B5738521
theorem B5100907 : Blo 1987435 5100907 := bstep (se 1 (by rfl) ⟨3825680, by rfl⟩ : syracuseStep 5100907 = 7651361) B7651361
theorem B6801209 : Blo 1987435 6801209 := bstep (se 2 (by rfl) ⟨2550453, by rfl⟩ : syracuseStep 6801209 = 5100907) B5100907
theorem B4534139 : Blo 1987435 4534139 := bstep (se 1 (by rfl) ⟨3400604, by rfl⟩ : syracuseStep 4534139 = 6801209) B6801209
theorem B3022759 : Blo 1987435 3022759 := bstep (se 1 (by rfl) ⟨2267069, by rfl⟩ : syracuseStep 3022759 = 4534139) B4534139
theorem B4030345 : Blo 1987435 4030345 := bstep (se 2 (by rfl) ⟨1511379, by rfl⟩ : syracuseStep 4030345 = 3022759) B3022759
theorem B5373793 : Blo 1987435 5373793 := bstep (se 2 (by rfl) ⟨2015172, by rfl⟩ : syracuseStep 5373793 = 4030345) B4030345
theorem B7165057 : Blo 1987435 7165057 := bstep (se 2 (by rfl) ⟨2686896, by rfl⟩ : syracuseStep 7165057 = 5373793) B5373793
theorem B9553409 : Blo 1987435 9553409 := bstep (se 2 (by rfl) ⟨3582528, by rfl⟩ : syracuseStep 9553409 = 7165057) B7165057
theorem B6368939 : Blo 1987435 6368939 := bstep (se 1 (by rfl) ⟨4776704, by rfl⟩ : syracuseStep 6368939 = 9553409) B9553409
theorem B4245959 : Blo 1987435 4245959 := bstep (se 1 (by rfl) ⟨3184469, by rfl⟩ : syracuseStep 4245959 = 6368939) B6368939
theorem B2830639 : Blo 1987435 2830639 := bstep (se 1 (by rfl) ⟨2122979, by rfl⟩ : syracuseStep 2830639 = 4245959) B4245959
theorem B3774185 : Blo 1987435 3774185 := bstep (se 2 (by rfl) ⟨1415319, by rfl⟩ : syracuseStep 3774185 = 2830639) B2830639
theorem B2516123 : Blo 1987435 2516123 := bstep (se 1 (by rfl) ⟨1887092, by rfl⟩ : syracuseStep 2516123 = 3774185) B3774185
theorem B6709661 : Blo 1987435 6709661 := bstep (se 3 (by rfl) ⟨1258061, by rfl⟩ : syracuseStep 6709661 = 2516123) B2516123
theorem B4473107 : Blo 1987435 4473107 := bstep (se 1 (by rfl) ⟨3354830, by rfl⟩ : syracuseStep 4473107 = 6709661) B6709661
theorem B2982071 : Blo 1987435 2982071 := bstep (se 1 (by rfl) ⟨2236553, by rfl⟩ : syracuseStep 2982071 = 4473107) B4473107
theorem B1988047 : Blo 1987435 1988047 := bstep (se 1 (by rfl) ⟨1491035, by rfl⟩ : syracuseStep 1988047 = 2982071) B2982071
theorem B2982077 : Blo 1987435 2982077 := bbase (se 3 (by rfl) ⟨559139, by rfl⟩ : syracuseStep 2982077 = 1118279) (by norm_num)
theorem B1988051 : Blo 1987435 1988051 := bstep (se 1 (by rfl) ⟨1491038, by rfl⟩ : syracuseStep 1988051 = 2982077) B2982077
theorem B4473125 : Blo 1987435 4473125 := bbase (se 4 (by rfl) ⟨419355, by rfl⟩ : syracuseStep 4473125 = 838711) (by norm_num)
theorem B2982083 : Blo 1987435 2982083 := bstep (se 1 (by rfl) ⟨2236562, by rfl⟩ : syracuseStep 2982083 = 4473125) B4473125
theorem B1988055 : Blo 1987435 1988055 := bstep (se 1 (by rfl) ⟨1491041, by rfl⟩ : syracuseStep 1988055 = 2982083) B2982083
theorem B5032277 : Blo 1987435 5032277 := bbase (se 10 (by rfl) ⟨7371, by rfl⟩ : syracuseStep 5032277 = 14743) (by norm_num)
theorem B3354851 : Blo 1987435 3354851 := bstep (se 1 (by rfl) ⟨2516138, by rfl⟩ : syracuseStep 3354851 = 5032277) B5032277
theorem B2236567 : Blo 1987435 2236567 := bstep (se 1 (by rfl) ⟨1677425, by rfl⟩ : syracuseStep 2236567 = 3354851) B3354851
theorem B2982089 : Blo 1987435 2982089 := bstep (se 2 (by rfl) ⟨1118283, by rfl⟩ : syracuseStep 2982089 = 2236567) B2236567
theorem B1988059 : Blo 1987435 1988059 := bstep (se 1 (by rfl) ⟨1491044, by rfl⟩ : syracuseStep 1988059 = 2982089) B2982089
theorem B3582557 : Blo 1987435 3582557 := bbase (se 3 (by rfl) ⟨671729, by rfl⟩ : syracuseStep 3582557 = 1343459) (by norm_num)
theorem B2388371 : Blo 1987435 2388371 := bstep (se 1 (by rfl) ⟨1791278, by rfl⟩ : syracuseStep 2388371 = 3582557) B3582557
theorem B6368989 : Blo 1987435 6368989 := bstep (se 3 (by rfl) ⟨1194185, by rfl⟩ : syracuseStep 6368989 = 2388371) B2388371
theorem B8491985 : Blo 1987435 8491985 := bstep (se 2 (by rfl) ⟨3184494, by rfl⟩ : syracuseStep 8491985 = 6368989) B6368989
theorem B5661323 : Blo 1987435 5661323 := bstep (se 1 (by rfl) ⟨4245992, by rfl⟩ : syracuseStep 5661323 = 8491985) B8491985
theorem B3774215 : Blo 1987435 3774215 := bstep (se 1 (by rfl) ⟨2830661, by rfl⟩ : syracuseStep 3774215 = 5661323) B5661323
theorem B10064573 : Blo 1987435 10064573 := bstep (se 3 (by rfl) ⟨1887107, by rfl⟩ : syracuseStep 10064573 = 3774215) B3774215
theorem B6709715 : Blo 1987435 6709715 := bstep (se 1 (by rfl) ⟨5032286, by rfl⟩ : syracuseStep 6709715 = 10064573) B10064573
theorem B4473143 : Blo 1987435 4473143 := bstep (se 1 (by rfl) ⟨3354857, by rfl⟩ : syracuseStep 4473143 = 6709715) B6709715
theorem B2982095 : Blo 1987435 2982095 := bstep (se 1 (by rfl) ⟨2236571, by rfl⟩ : syracuseStep 2982095 = 4473143) B4473143
theorem B1988063 : Blo 1987435 1988063 := bstep (se 1 (by rfl) ⟨1491047, by rfl⟩ : syracuseStep 1988063 = 2982095) B2982095
theorem B2982101 : Blo 1987435 2982101 := bbase (se 7 (by rfl) ⟨34946, by rfl⟩ : syracuseStep 2982101 = 69893) (by norm_num)
theorem B1988067 : Blo 1987435 1988067 := bstep (se 1 (by rfl) ⟨1491050, by rfl⟩ : syracuseStep 1988067 = 2982101) B2982101
theorem B2123005 : Blo 1987435 2123005 := bbase (se 3 (by rfl) ⟨398063, by rfl⟩ : syracuseStep 2123005 = 796127) (by norm_num)
theorem B2830673 : Blo 1987435 2830673 := bstep (se 2 (by rfl) ⟨1061502, by rfl⟩ : syracuseStep 2830673 = 2123005) B2123005
theorem B7548461 : Blo 1987435 7548461 := bstep (se 3 (by rfl) ⟨1415336, by rfl⟩ : syracuseStep 7548461 = 2830673) B2830673
theorem B5032307 : Blo 1987435 5032307 := bstep (se 1 (by rfl) ⟨3774230, by rfl⟩ : syracuseStep 5032307 = 7548461) B7548461
theorem B3354871 : Blo 1987435 3354871 := bstep (se 1 (by rfl) ⟨2516153, by rfl⟩ : syracuseStep 3354871 = 5032307) B5032307
theorem B4473161 : Blo 1987435 4473161 := bstep (se 2 (by rfl) ⟨1677435, by rfl⟩ : syracuseStep 4473161 = 3354871) B3354871
theorem B2982107 : Blo 1987435 2982107 := bstep (se 1 (by rfl) ⟨2236580, by rfl⟩ : syracuseStep 2982107 = 4473161) B4473161
theorem B1988071 : Blo 1987435 1988071 := bstep (se 1 (by rfl) ⟨1491053, by rfl⟩ : syracuseStep 1988071 = 2982107) B2982107
theorem B2236585 : Blo 1987435 2236585 := bbase (se 2 (by rfl) ⟨838719, by rfl⟩ : syracuseStep 2236585 = 1677439) (by norm_num)
theorem B2982113 : Blo 1987435 2982113 := bstep (se 2 (by rfl) ⟨1118292, by rfl⟩ : syracuseStep 2982113 = 2236585) B2236585
theorem B1988075 : Blo 1987435 1988075 := bstep (se 1 (by rfl) ⟨1491056, by rfl⟩ : syracuseStep 1988075 = 2982113) B2982113
theorem B8492053 : Blo 1987435 8492053 := bbase (se 6 (by rfl) ⟨199032, by rfl⟩ : syracuseStep 8492053 = 398065) (by norm_num)
theorem B11322737 : Blo 1987435 11322737 := bstep (se 2 (by rfl) ⟨4246026, by rfl⟩ : syracuseStep 11322737 = 8492053) B8492053
theorem B7548491 : Blo 1987435 7548491 := bstep (se 1 (by rfl) ⟨5661368, by rfl⟩ : syracuseStep 7548491 = 11322737) B11322737
theorem B5032327 : Blo 1987435 5032327 := bstep (se 1 (by rfl) ⟨3774245, by rfl⟩ : syracuseStep 5032327 = 7548491) B7548491
theorem B6709769 : Blo 1987435 6709769 := bstep (se 2 (by rfl) ⟨2516163, by rfl⟩ : syracuseStep 6709769 = 5032327) B5032327
theorem B4473179 : Blo 1987435 4473179 := bstep (se 1 (by rfl) ⟨3354884, by rfl⟩ : syracuseStep 4473179 = 6709769) B6709769
theorem B2982119 : Blo 1987435 2982119 := bstep (se 1 (by rfl) ⟨2236589, by rfl⟩ : syracuseStep 2982119 = 4473179) B4473179
theorem B1988079 : Blo 1987435 1988079 := bstep (se 1 (by rfl) ⟨1491059, by rfl⟩ : syracuseStep 1988079 = 2982119) B2982119
theorem B2982125 : Blo 1987435 2982125 := bbase (se 3 (by rfl) ⟨559148, by rfl⟩ : syracuseStep 2982125 = 1118297) (by norm_num)
theorem B1988083 : Blo 1987435 1988083 := bstep (se 1 (by rfl) ⟨1491062, by rfl⟩ : syracuseStep 1988083 = 2982125) B2982125
theorem B4473197 : Blo 1987435 4473197 := bbase (se 3 (by rfl) ⟨838724, by rfl⟩ : syracuseStep 4473197 = 1677449) (by norm_num)
theorem B2982131 : Blo 1987435 2982131 := bstep (se 1 (by rfl) ⟨2236598, by rfl⟩ : syracuseStep 2982131 = 4473197) B4473197
theorem B1988087 : Blo 1987435 1988087 := bstep (se 1 (by rfl) ⟨1491065, by rfl⟩ : syracuseStep 1988087 = 2982131) B2982131
theorem B3774269 : Blo 1987435 3774269 := bbase (se 3 (by rfl) ⟨707675, by rfl⟩ : syracuseStep 3774269 = 1415351) (by norm_num)
theorem B2516179 : Blo 1987435 2516179 := bstep (se 1 (by rfl) ⟨1887134, by rfl⟩ : syracuseStep 2516179 = 3774269) B3774269
theorem B3354905 : Blo 1987435 3354905 := bstep (se 2 (by rfl) ⟨1258089, by rfl⟩ : syracuseStep 3354905 = 2516179) B2516179
theorem B2236603 : Blo 1987435 2236603 := bstep (se 1 (by rfl) ⟨1677452, by rfl⟩ : syracuseStep 2236603 = 3354905) B3354905
theorem B2982137 : Blo 1987435 2982137 := bstep (se 2 (by rfl) ⟨1118301, by rfl⟩ : syracuseStep 2982137 = 2236603) B2236603
theorem B1988091 : Blo 1987435 1988091 := bstep (se 1 (by rfl) ⟨1491068, by rfl⟩ : syracuseStep 1988091 = 2982137) B2982137
theorem B2388409 : Blo 1987435 2388409 := bbase (se 2 (by rfl) ⟨895653, by rfl⟩ : syracuseStep 2388409 = 1791307) (by norm_num)
theorem B50952725 : Blo 1987435 50952725 := bstep (se 6 (by rfl) ⟨1194204, by rfl⟩ : syracuseStep 50952725 = 2388409) B2388409
theorem B33968483 : Blo 1987435 33968483 := bstep (se 1 (by rfl) ⟨25476362, by rfl⟩ : syracuseStep 33968483 = 50952725) B50952725
theorem B22645655 : Blo 1987435 22645655 := bstep (se 1 (by rfl) ⟨16984241, by rfl⟩ : syracuseStep 22645655 = 33968483) B33968483
theorem B15097103 : Blo 1987435 15097103 := bstep (se 1 (by rfl) ⟨11322827, by rfl⟩ : syracuseStep 15097103 = 22645655) B22645655
theorem B10064735 : Blo 1987435 10064735 := bstep (se 1 (by rfl) ⟨7548551, by rfl⟩ : syracuseStep 10064735 = 15097103) B15097103
theorem B6709823 : Blo 1987435 6709823 := bstep (se 1 (by rfl) ⟨5032367, by rfl⟩ : syracuseStep 6709823 = 10064735) B10064735
theorem B4473215 : Blo 1987435 4473215 := bstep (se 1 (by rfl) ⟨3354911, by rfl⟩ : syracuseStep 4473215 = 6709823) B6709823
theorem B2982143 : Blo 1987435 2982143 := bstep (se 1 (by rfl) ⟨2236607, by rfl⟩ : syracuseStep 2982143 = 4473215) B4473215
theorem B1988095 : Blo 1987435 1988095 := bstep (se 1 (by rfl) ⟨1491071, by rfl⟩ : syracuseStep 1988095 = 2982143) B2982143
theorem B2982149 : Blo 1987435 2982149 := bbase (se 4 (by rfl) ⟨279576, by rfl⟩ : syracuseStep 2982149 = 559153) (by norm_num)
theorem B1988099 : Blo 1987435 1988099 := bstep (se 1 (by rfl) ⟨1491074, by rfl⟩ : syracuseStep 1988099 = 2982149) B2982149
theorem B3354925 : Blo 1987435 3354925 := bbase (se 3 (by rfl) ⟨629048, by rfl⟩ : syracuseStep 3354925 = 1258097) (by norm_num)
theorem B4473233 : Blo 1987435 4473233 := bstep (se 2 (by rfl) ⟨1677462, by rfl⟩ : syracuseStep 4473233 = 3354925) B3354925
theorem B2982155 : Blo 1987435 2982155 := bstep (se 1 (by rfl) ⟨2236616, by rfl⟩ : syracuseStep 2982155 = 4473233) B4473233
theorem B1988103 : Blo 1987435 1988103 := bstep (se 1 (by rfl) ⟨1491077, by rfl⟩ : syracuseStep 1988103 = 2982155) B2982155
theorem B2236621 : Blo 1987435 2236621 := bbase (se 3 (by rfl) ⟨419366, by rfl⟩ : syracuseStep 2236621 = 838733) (by norm_num)
theorem B2982161 : Blo 1987435 2982161 := bstep (se 2 (by rfl) ⟨1118310, by rfl⟩ : syracuseStep 2982161 = 2236621) B2236621
theorem B1988107 : Blo 1987435 1988107 := bstep (se 1 (by rfl) ⟨1491080, by rfl⟩ : syracuseStep 1988107 = 2982161) B2982161
theorem B6709877 : Blo 1987435 6709877 := bbase (se 5 (by rfl) ⟨314525, by rfl⟩ : syracuseStep 6709877 = 629051) (by norm_num)
theorem B4473251 : Blo 1987435 4473251 := bstep (se 1 (by rfl) ⟨3354938, by rfl⟩ : syracuseStep 4473251 = 6709877) B6709877
theorem B2982167 : Blo 1987435 2982167 := bstep (se 1 (by rfl) ⟨2236625, by rfl⟩ : syracuseStep 2982167 = 4473251) B4473251
theorem B1988111 : Blo 1987435 1988111 := bstep (se 1 (by rfl) ⟨1491083, by rfl⟩ : syracuseStep 1988111 = 2982167) B2982167
theorem B2982173 : Blo 1987435 2982173 := bbase (se 3 (by rfl) ⟨559157, by rfl⟩ : syracuseStep 2982173 = 1118315) (by norm_num)
theorem B1988115 : Blo 1987435 1988115 := bstep (se 1 (by rfl) ⟨1491086, by rfl⟩ : syracuseStep 1988115 = 2982173) B2982173
theorem B4473269 : Blo 1987435 4473269 := bbase (se 5 (by rfl) ⟨209684, by rfl⟩ : syracuseStep 4473269 = 419369) (by norm_num)
theorem B2982179 : Blo 1987435 2982179 := bstep (se 1 (by rfl) ⟨2236634, by rfl⟩ : syracuseStep 2982179 = 4473269) B4473269
theorem B1988119 : Blo 1987435 1988119 := bstep (se 1 (by rfl) ⟨1491089, by rfl⟩ : syracuseStep 1988119 = 2982179) B2982179
theorem B6045749 : Blo 1987435 6045749 := bbase (se 5 (by rfl) ⟨283394, by rfl⟩ : syracuseStep 6045749 = 566789) (by norm_num)
theorem B4030499 : Blo 1987435 4030499 := bstep (se 1 (by rfl) ⟨3022874, by rfl⟩ : syracuseStep 4030499 = 6045749) B6045749
theorem B10747997 : Blo 1987435 10747997 := bstep (se 3 (by rfl) ⟨2015249, by rfl⟩ : syracuseStep 10747997 = 4030499) B4030499
theorem B7165331 : Blo 1987435 7165331 := bstep (se 1 (by rfl) ⟨5373998, by rfl⟩ : syracuseStep 7165331 = 10747997) B10747997
theorem B4776887 : Blo 1987435 4776887 := bstep (se 1 (by rfl) ⟨3582665, by rfl⟩ : syracuseStep 4776887 = 7165331) B7165331
theorem B3184591 : Blo 1987435 3184591 := bstep (se 1 (by rfl) ⟨2388443, by rfl⟩ : syracuseStep 3184591 = 4776887) B4776887
theorem B4246121 : Blo 1987435 4246121 := bstep (se 2 (by rfl) ⟨1592295, by rfl⟩ : syracuseStep 4246121 = 3184591) B3184591
theorem B11322989 : Blo 1987435 11322989 := bstep (se 3 (by rfl) ⟨2123060, by rfl⟩ : syracuseStep 11322989 = 4246121) B4246121
theorem B7548659 : Blo 1987435 7548659 := bstep (se 1 (by rfl) ⟨5661494, by rfl⟩ : syracuseStep 7548659 = 11322989) B11322989
theorem B5032439 : Blo 1987435 5032439 := bstep (se 1 (by rfl) ⟨3774329, by rfl⟩ : syracuseStep 5032439 = 7548659) B7548659
theorem B3354959 : Blo 1987435 3354959 := bstep (se 1 (by rfl) ⟨2516219, by rfl⟩ : syracuseStep 3354959 = 5032439) B5032439
theorem B2236639 : Blo 1987435 2236639 := bstep (se 1 (by rfl) ⟨1677479, by rfl⟩ : syracuseStep 2236639 = 3354959) B3354959
theorem B2982185 : Blo 1987435 2982185 := bstep (se 2 (by rfl) ⟨1118319, by rfl⟩ : syracuseStep 2982185 = 2236639) B2236639
theorem B1988123 : Blo 1987435 1988123 := bstep (se 1 (by rfl) ⟨1491092, by rfl⟩ : syracuseStep 1988123 = 2982185) B2982185
theorem B3184597 : Blo 1987435 3184597 := bbase (se 7 (by rfl) ⟨37319, by rfl⟩ : syracuseStep 3184597 = 74639) (by norm_num)
theorem B4246129 : Blo 1987435 4246129 := bstep (se 2 (by rfl) ⟨1592298, by rfl⟩ : syracuseStep 4246129 = 3184597) B3184597
theorem B5661505 : Blo 1987435 5661505 := bstep (se 2 (by rfl) ⟨2123064, by rfl⟩ : syracuseStep 5661505 = 4246129) B4246129
theorem B7548673 : Blo 1987435 7548673 := bstep (se 2 (by rfl) ⟨2830752, by rfl⟩ : syracuseStep 7548673 = 5661505) B5661505
theorem B10064897 : Blo 1987435 10064897 := bstep (se 2 (by rfl) ⟨3774336, by rfl⟩ : syracuseStep 10064897 = 7548673) B7548673
theorem B6709931 : Blo 1987435 6709931 := bstep (se 1 (by rfl) ⟨5032448, by rfl⟩ : syracuseStep 6709931 = 10064897) B10064897
theorem B4473287 : Blo 1987435 4473287 := bstep (se 1 (by rfl) ⟨3354965, by rfl⟩ : syracuseStep 4473287 = 6709931) B6709931
theorem B2982191 : Blo 1987435 2982191 := bstep (se 1 (by rfl) ⟨2236643, by rfl⟩ : syracuseStep 2982191 = 4473287) B4473287
theorem B1988127 : Blo 1987435 1988127 := bstep (se 1 (by rfl) ⟨1491095, by rfl⟩ : syracuseStep 1988127 = 2982191) B2982191
theorem B2982197 : Blo 1987435 2982197 := bbase (se 5 (by rfl) ⟨139790, by rfl⟩ : syracuseStep 2982197 = 279581) (by norm_num)
theorem B1988131 : Blo 1987435 1988131 := bstep (se 1 (by rfl) ⟨1491098, by rfl⟩ : syracuseStep 1988131 = 2982197) B2982197
theorem B5032469 : Blo 1987435 5032469 := bbase (se 6 (by rfl) ⟨117948, by rfl⟩ : syracuseStep 5032469 = 235897) (by norm_num)
theorem B3354979 : Blo 1987435 3354979 := bstep (se 1 (by rfl) ⟨2516234, by rfl⟩ : syracuseStep 3354979 = 5032469) B5032469
theorem B4473305 : Blo 1987435 4473305 := bstep (se 2 (by rfl) ⟨1677489, by rfl⟩ : syracuseStep 4473305 = 3354979) B3354979
theorem B2982203 : Blo 1987435 2982203 := bstep (se 1 (by rfl) ⟨2236652, by rfl⟩ : syracuseStep 2982203 = 4473305) B4473305
theorem B1988135 : Blo 1987435 1988135 := bstep (se 1 (by rfl) ⟨1491101, by rfl⟩ : syracuseStep 1988135 = 2982203) B2982203
theorem B2236657 : Blo 1987435 2236657 := bbase (se 2 (by rfl) ⟨838746, by rfl⟩ : syracuseStep 2236657 = 1677493) (by norm_num)
theorem B2982209 : Blo 1987435 2982209 := bstep (se 2 (by rfl) ⟨1118328, by rfl⟩ : syracuseStep 2982209 = 2236657) B2236657
theorem B1988139 : Blo 1987435 1988139 := bstep (se 1 (by rfl) ⟨1491104, by rfl⟩ : syracuseStep 1988139 = 2982209) B2982209
theorem B8061077 : Blo 1987435 8061077 := bbase (se 6 (by rfl) ⟨188931, by rfl⟩ : syracuseStep 8061077 = 377863) (by norm_num)
theorem B21496205 : Blo 1987435 21496205 := bstep (se 3 (by rfl) ⟨4030538, by rfl⟩ : syracuseStep 21496205 = 8061077) B8061077
theorem B14330803 : Blo 1987435 14330803 := bstep (se 1 (by rfl) ⟨10748102, by rfl⟩ : syracuseStep 14330803 = 21496205) B21496205
theorem B19107737 : Blo 1987435 19107737 := bstep (se 2 (by rfl) ⟨7165401, by rfl⟩ : syracuseStep 19107737 = 14330803) B14330803
theorem B12738491 : Blo 1987435 12738491 := bstep (se 1 (by rfl) ⟨9553868, by rfl⟩ : syracuseStep 12738491 = 19107737) B19107737
theorem B8492327 : Blo 1987435 8492327 := bstep (se 1 (by rfl) ⟨6369245, by rfl⟩ : syracuseStep 8492327 = 12738491) B12738491
theorem B5661551 : Blo 1987435 5661551 := bstep (se 1 (by rfl) ⟨4246163, by rfl⟩ : syracuseStep 5661551 = 8492327) B8492327
theorem B3774367 : Blo 1987435 3774367 := bstep (se 1 (by rfl) ⟨2830775, by rfl⟩ : syracuseStep 3774367 = 5661551) B5661551
theorem B5032489 : Blo 1987435 5032489 := bstep (se 2 (by rfl) ⟨1887183, by rfl⟩ : syracuseStep 5032489 = 3774367) B3774367
theorem B6709985 : Blo 1987435 6709985 := bstep (se 2 (by rfl) ⟨2516244, by rfl⟩ : syracuseStep 6709985 = 5032489) B5032489
theorem B4473323 : Blo 1987435 4473323 := bstep (se 1 (by rfl) ⟨3354992, by rfl⟩ : syracuseStep 4473323 = 6709985) B6709985
theorem B2982215 : Blo 1987435 2982215 := bstep (se 1 (by rfl) ⟨2236661, by rfl⟩ : syracuseStep 2982215 = 4473323) B4473323
theorem B1988143 : Blo 1987435 1988143 := bstep (se 1 (by rfl) ⟨1491107, by rfl⟩ : syracuseStep 1988143 = 2982215) B2982215
theorem B2982221 : Blo 1987435 2982221 := bbase (se 3 (by rfl) ⟨559166, by rfl⟩ : syracuseStep 2982221 = 1118333) (by norm_num)
theorem B1988147 : Blo 1987435 1988147 := bstep (se 1 (by rfl) ⟨1491110, by rfl⟩ : syracuseStep 1988147 = 2982221) B2982221
theorem B4473341 : Blo 1987435 4473341 := bbase (se 3 (by rfl) ⟨838751, by rfl⟩ : syracuseStep 4473341 = 1677503) (by norm_num)
theorem B2982227 : Blo 1987435 2982227 := bstep (se 1 (by rfl) ⟨2236670, by rfl⟩ : syracuseStep 2982227 = 4473341) B4473341
theorem B1988151 : Blo 1987435 1988151 := bstep (se 1 (by rfl) ⟨1491113, by rfl⟩ : syracuseStep 1988151 = 2982227) B2982227
theorem B3355013 : Blo 1987435 3355013 := bbase (se 4 (by rfl) ⟨314532, by rfl⟩ : syracuseStep 3355013 = 629065) (by norm_num)
theorem B2236675 : Blo 1987435 2236675 := bstep (se 1 (by rfl) ⟨1677506, by rfl⟩ : syracuseStep 2236675 = 3355013) B3355013
theorem B2982233 : Blo 1987435 2982233 := bstep (se 2 (by rfl) ⟨1118337, by rfl⟩ : syracuseStep 2982233 = 2236675) B2236675
theorem B1988155 : Blo 1987435 1988155 := bstep (se 1 (by rfl) ⟨1491116, by rfl⟩ : syracuseStep 1988155 = 2982233) B2982233
theorem B15097589 : Blo 1987435 15097589 := bbase (se 5 (by rfl) ⟨707699, by rfl⟩ : syracuseStep 15097589 = 1415399) (by norm_num)
theorem B10065059 : Blo 1987435 10065059 := bstep (se 1 (by rfl) ⟨7548794, by rfl⟩ : syracuseStep 10065059 = 15097589) B15097589
theorem B6710039 : Blo 1987435 6710039 := bstep (se 1 (by rfl) ⟨5032529, by rfl⟩ : syracuseStep 6710039 = 10065059) B10065059
theorem B4473359 : Blo 1987435 4473359 := bstep (se 1 (by rfl) ⟨3355019, by rfl⟩ : syracuseStep 4473359 = 6710039) B6710039
theorem B2982239 : Blo 1987435 2982239 := bstep (se 1 (by rfl) ⟨2236679, by rfl⟩ : syracuseStep 2982239 = 4473359) B4473359
theorem B1988159 : Blo 1987435 1988159 := bstep (se 1 (by rfl) ⟨1491119, by rfl⟩ : syracuseStep 1988159 = 2982239) B2982239
theorem B2982245 : Blo 1987435 2982245 := bbase (se 4 (by rfl) ⟨279585, by rfl⟩ : syracuseStep 2982245 = 559171) (by norm_num)
theorem B1988163 : Blo 1987435 1988163 := bstep (se 1 (by rfl) ⟨1491122, by rfl⟩ : syracuseStep 1988163 = 2982245) B2982245
theorem B3774413 : Blo 1987435 3774413 := bbase (se 3 (by rfl) ⟨707702, by rfl⟩ : syracuseStep 3774413 = 1415405) (by norm_num)
theorem B2516275 : Blo 1987435 2516275 := bstep (se 1 (by rfl) ⟨1887206, by rfl⟩ : syracuseStep 2516275 = 3774413) B3774413
theorem B3355033 : Blo 1987435 3355033 := bstep (se 2 (by rfl) ⟨1258137, by rfl⟩ : syracuseStep 3355033 = 2516275) B2516275
theorem B4473377 : Blo 1987435 4473377 := bstep (se 2 (by rfl) ⟨1677516, by rfl⟩ : syracuseStep 4473377 = 3355033) B3355033
theorem B2982251 : Blo 1987435 2982251 := bstep (se 1 (by rfl) ⟨2236688, by rfl⟩ : syracuseStep 2982251 = 4473377) B4473377
theorem B1988167 : Blo 1987435 1988167 := bstep (se 1 (by rfl) ⟨1491125, by rfl⟩ : syracuseStep 1988167 = 2982251) B2982251
theorem B2236693 : Blo 1987435 2236693 := bbase (se 6 (by rfl) ⟨52422, by rfl⟩ : syracuseStep 2236693 = 104845) (by norm_num)
theorem B2982257 : Blo 1987435 2982257 := bstep (se 2 (by rfl) ⟨1118346, by rfl⟩ : syracuseStep 2982257 = 2236693) B2236693
theorem B1988171 : Blo 1987435 1988171 := bstep (se 1 (by rfl) ⟨1491128, by rfl⟩ : syracuseStep 1988171 = 2982257) B2982257
theorem B2516285 : Blo 1987435 2516285 := bbase (se 3 (by rfl) ⟨471803, by rfl⟩ : syracuseStep 2516285 = 943607) (by norm_num)
theorem B6710093 : Blo 1987435 6710093 := bstep (se 3 (by rfl) ⟨1258142, by rfl⟩ : syracuseStep 6710093 = 2516285) B2516285
theorem B4473395 : Blo 1987435 4473395 := bstep (se 1 (by rfl) ⟨3355046, by rfl⟩ : syracuseStep 4473395 = 6710093) B6710093
theorem B2982263 : Blo 1987435 2982263 := bstep (se 1 (by rfl) ⟨2236697, by rfl⟩ : syracuseStep 2982263 = 4473395) B4473395
theorem B1988175 : Blo 1987435 1988175 := bstep (se 1 (by rfl) ⟨1491131, by rfl⟩ : syracuseStep 1988175 = 2982263) B2982263
theorem B2982269 : Blo 1987435 2982269 := bbase (se 3 (by rfl) ⟨559175, by rfl⟩ : syracuseStep 2982269 = 1118351) (by norm_num)
theorem B1988179 : Blo 1987435 1988179 := bstep (se 1 (by rfl) ⟨1491134, by rfl⟩ : syracuseStep 1988179 = 2982269) B2982269
theorem B4473413 : Blo 1987435 4473413 := bbase (se 4 (by rfl) ⟨419382, by rfl⟩ : syracuseStep 4473413 = 838765) (by norm_num)
theorem B2982275 : Blo 1987435 2982275 := bstep (se 1 (by rfl) ⟨2236706, by rfl⟩ : syracuseStep 2982275 = 4473413) B4473413
theorem B1988183 : Blo 1987435 1988183 := bstep (se 1 (by rfl) ⟨1491137, by rfl⟩ : syracuseStep 1988183 = 2982275) B2982275
theorem B2123129 : Blo 1987435 2123129 := bbase (se 2 (by rfl) ⟨796173, by rfl⟩ : syracuseStep 2123129 = 1592347) (by norm_num)
theorem B5661677 : Blo 1987435 5661677 := bstep (se 3 (by rfl) ⟨1061564, by rfl⟩ : syracuseStep 5661677 = 2123129) B2123129
theorem B3774451 : Blo 1987435 3774451 := bstep (se 1 (by rfl) ⟨2830838, by rfl⟩ : syracuseStep 3774451 = 5661677) B5661677
theorem B5032601 : Blo 1987435 5032601 := bstep (se 2 (by rfl) ⟨1887225, by rfl⟩ : syracuseStep 5032601 = 3774451) B3774451
theorem B3355067 : Blo 1987435 3355067 := bstep (se 1 (by rfl) ⟨2516300, by rfl⟩ : syracuseStep 3355067 = 5032601) B5032601
theorem B2236711 : Blo 1987435 2236711 := bstep (se 1 (by rfl) ⟨1677533, by rfl⟩ : syracuseStep 2236711 = 3355067) B3355067
theorem B2982281 : Blo 1987435 2982281 := bstep (se 2 (by rfl) ⟨1118355, by rfl⟩ : syracuseStep 2982281 = 2236711) B2236711
theorem B1988187 : Blo 1987435 1988187 := bstep (se 1 (by rfl) ⟨1491140, by rfl⟩ : syracuseStep 1988187 = 2982281) B2982281
theorem B10065221 : Blo 1987435 10065221 := bbase (se 4 (by rfl) ⟨943614, by rfl⟩ : syracuseStep 10065221 = 1887229) (by norm_num)
theorem B6710147 : Blo 1987435 6710147 := bstep (se 1 (by rfl) ⟨5032610, by rfl⟩ : syracuseStep 6710147 = 10065221) B10065221
theorem B4473431 : Blo 1987435 4473431 := bstep (se 1 (by rfl) ⟨3355073, by rfl⟩ : syracuseStep 4473431 = 6710147) B6710147
theorem B2982287 : Blo 1987435 2982287 := bstep (se 1 (by rfl) ⟨2236715, by rfl⟩ : syracuseStep 2982287 = 4473431) B4473431
theorem B1988191 : Blo 1987435 1988191 := bstep (se 1 (by rfl) ⟨1491143, by rfl⟩ : syracuseStep 1988191 = 2982287) B2982287
theorem B2982293 : Blo 1987435 2982293 := bbase (se 6 (by rfl) ⟨69897, by rfl⟩ : syracuseStep 2982293 = 139795) (by norm_num)
theorem B1988195 : Blo 1987435 1988195 := bstep (se 1 (by rfl) ⟨1491146, by rfl⟩ : syracuseStep 1988195 = 2982293) B2982293
theorem B4777069 : Blo 1987435 4777069 := bbase (se 3 (by rfl) ⟨895700, by rfl⟩ : syracuseStep 4777069 = 1791401) (by norm_num)
theorem B6369425 : Blo 1987435 6369425 := bstep (se 2 (by rfl) ⟨2388534, by rfl⟩ : syracuseStep 6369425 = 4777069) B4777069
theorem B4246283 : Blo 1987435 4246283 := bstep (se 1 (by rfl) ⟨3184712, by rfl⟩ : syracuseStep 4246283 = 6369425) B6369425
theorem B11323421 : Blo 1987435 11323421 := bstep (se 3 (by rfl) ⟨2123141, by rfl⟩ : syracuseStep 11323421 = 4246283) B4246283
theorem B7548947 : Blo 1987435 7548947 := bstep (se 1 (by rfl) ⟨5661710, by rfl⟩ : syracuseStep 7548947 = 11323421) B11323421
theorem B5032631 : Blo 1987435 5032631 := bstep (se 1 (by rfl) ⟨3774473, by rfl⟩ : syracuseStep 5032631 = 7548947) B7548947
theorem B3355087 : Blo 1987435 3355087 := bstep (se 1 (by rfl) ⟨2516315, by rfl⟩ : syracuseStep 3355087 = 5032631) B5032631
theorem B4473449 : Blo 1987435 4473449 := bstep (se 2 (by rfl) ⟨1677543, by rfl⟩ : syracuseStep 4473449 = 3355087) B3355087
theorem B2982299 : Blo 1987435 2982299 := bstep (se 1 (by rfl) ⟨2236724, by rfl⟩ : syracuseStep 2982299 = 4473449) B4473449
theorem B1988199 : Blo 1987435 1988199 := bstep (se 1 (by rfl) ⟨1491149, by rfl⟩ : syracuseStep 1988199 = 2982299) B2982299
theorem B2236729 : Blo 1987435 2236729 := bbase (se 2 (by rfl) ⟨838773, by rfl⟩ : syracuseStep 2236729 = 1677547) (by norm_num)
theorem B2982305 : Blo 1987435 2982305 := bstep (se 2 (by rfl) ⟨1118364, by rfl⟩ : syracuseStep 2982305 = 2236729) B2236729
theorem B1988203 : Blo 1987435 1988203 := bstep (se 1 (by rfl) ⟨1491152, by rfl⟩ : syracuseStep 1988203 = 2982305) B2982305
theorem B5661733 : Blo 1987435 5661733 := bbase (se 4 (by rfl) ⟨530787, by rfl⟩ : syracuseStep 5661733 = 1061575) (by norm_num)
theorem B7548977 : Blo 1987435 7548977 := bstep (se 2 (by rfl) ⟨2830866, by rfl⟩ : syracuseStep 7548977 = 5661733) B5661733
theorem B5032651 : Blo 1987435 5032651 := bstep (se 1 (by rfl) ⟨3774488, by rfl⟩ : syracuseStep 5032651 = 7548977) B7548977
theorem B6710201 : Blo 1987435 6710201 := bstep (se 2 (by rfl) ⟨2516325, by rfl⟩ : syracuseStep 6710201 = 5032651) B5032651
theorem B4473467 : Blo 1987435 4473467 := bstep (se 1 (by rfl) ⟨3355100, by rfl⟩ : syracuseStep 4473467 = 6710201) B6710201
theorem B2982311 : Blo 1987435 2982311 := bstep (se 1 (by rfl) ⟨2236733, by rfl⟩ : syracuseStep 2982311 = 4473467) B4473467
theorem B1988207 : Blo 1987435 1988207 := bstep (se 1 (by rfl) ⟨1491155, by rfl⟩ : syracuseStep 1988207 = 2982311) B2982311
theorem B2982317 : Blo 1987435 2982317 := bbase (se 3 (by rfl) ⟨559184, by rfl⟩ : syracuseStep 2982317 = 1118369) (by norm_num)
theorem B1988211 : Blo 1987435 1988211 := bstep (se 1 (by rfl) ⟨1491158, by rfl⟩ : syracuseStep 1988211 = 2982317) B2982317
theorem B4473485 : Blo 1987435 4473485 := bbase (se 3 (by rfl) ⟨838778, by rfl⟩ : syracuseStep 4473485 = 1677557) (by norm_num)
theorem B2982323 : Blo 1987435 2982323 := bstep (se 1 (by rfl) ⟨2236742, by rfl⟩ : syracuseStep 2982323 = 4473485) B4473485
theorem B1988215 : Blo 1987435 1988215 := bstep (se 1 (by rfl) ⟨1491161, by rfl⟩ : syracuseStep 1988215 = 2982323) B2982323
theorem B2516341 : Blo 1987435 2516341 := bbase (se 5 (by rfl) ⟨117953, by rfl⟩ : syracuseStep 2516341 = 235907) (by norm_num)
theorem B3355121 : Blo 1987435 3355121 := bstep (se 2 (by rfl) ⟨1258170, by rfl⟩ : syracuseStep 3355121 = 2516341) B2516341
theorem B2236747 : Blo 1987435 2236747 := bstep (se 1 (by rfl) ⟨1677560, by rfl⟩ : syracuseStep 2236747 = 3355121) B3355121
theorem B2982329 : Blo 1987435 2982329 := bstep (se 2 (by rfl) ⟨1118373, by rfl⟩ : syracuseStep 2982329 = 2236747) B2236747
theorem B1988219 : Blo 1987435 1988219 := bstep (se 1 (by rfl) ⟨1491164, by rfl⟩ : syracuseStep 1988219 = 2982329) B2982329
theorem B10748533 : Blo 1987435 10748533 := bbase (se 5 (by rfl) ⟨503837, by rfl⟩ : syracuseStep 10748533 = 1007675) (by norm_num)
theorem B14331377 : Blo 1987435 14331377 := bstep (se 2 (by rfl) ⟨5374266, by rfl⟩ : syracuseStep 14331377 = 10748533) B10748533
theorem B38217005 : Blo 1987435 38217005 := bstep (se 3 (by rfl) ⟨7165688, by rfl⟩ : syracuseStep 38217005 = 14331377) B14331377
theorem B25478003 : Blo 1987435 25478003 := bstep (se 1 (by rfl) ⟨19108502, by rfl⟩ : syracuseStep 25478003 = 38217005) B38217005
theorem B16985335 : Blo 1987435 16985335 := bstep (se 1 (by rfl) ⟨12739001, by rfl⟩ : syracuseStep 16985335 = 25478003) B25478003
theorem B22647113 : Blo 1987435 22647113 := bstep (se 2 (by rfl) ⟨8492667, by rfl⟩ : syracuseStep 22647113 = 16985335) B16985335
theorem B15098075 : Blo 1987435 15098075 := bstep (se 1 (by rfl) ⟨11323556, by rfl⟩ : syracuseStep 15098075 = 22647113) B22647113
theorem B10065383 : Blo 1987435 10065383 := bstep (se 1 (by rfl) ⟨7549037, by rfl⟩ : syracuseStep 10065383 = 15098075) B15098075
theorem B6710255 : Blo 1987435 6710255 := bstep (se 1 (by rfl) ⟨5032691, by rfl⟩ : syracuseStep 6710255 = 10065383) B10065383
theorem B4473503 : Blo 1987435 4473503 := bstep (se 1 (by rfl) ⟨3355127, by rfl⟩ : syracuseStep 4473503 = 6710255) B6710255
theorem B2982335 : Blo 1987435 2982335 := bstep (se 1 (by rfl) ⟨2236751, by rfl⟩ : syracuseStep 2982335 = 4473503) B4473503
theorem B1988223 : Blo 1987435 1988223 := bstep (se 1 (by rfl) ⟨1491167, by rfl⟩ : syracuseStep 1988223 = 2982335) B2982335
theorem B2982341 : Blo 1987435 2982341 := bbase (se 4 (by rfl) ⟨279594, by rfl⟩ : syracuseStep 2982341 = 559189) (by norm_num)
theorem B1988227 : Blo 1987435 1988227 := bstep (se 1 (by rfl) ⟨1491170, by rfl⟩ : syracuseStep 1988227 = 2982341) B2982341
theorem B3355141 : Blo 1987435 3355141 := bbase (se 4 (by rfl) ⟨314544, by rfl⟩ : syracuseStep 3355141 = 629089) (by norm_num)
theorem B4473521 : Blo 1987435 4473521 := bstep (se 2 (by rfl) ⟨1677570, by rfl⟩ : syracuseStep 4473521 = 3355141) B3355141
theorem B2982347 : Blo 1987435 2982347 := bstep (se 1 (by rfl) ⟨2236760, by rfl⟩ : syracuseStep 2982347 = 4473521) B4473521
theorem B1988231 : Blo 1987435 1988231 := bstep (se 1 (by rfl) ⟨1491173, by rfl⟩ : syracuseStep 1988231 = 2982347) B2982347
theorem B2236765 : Blo 1987435 2236765 := bbase (se 3 (by rfl) ⟨419393, by rfl⟩ : syracuseStep 2236765 = 838787) (by norm_num)
theorem B2982353 : Blo 1987435 2982353 := bstep (se 2 (by rfl) ⟨1118382, by rfl⟩ : syracuseStep 2982353 = 2236765) B2236765
theorem B1988235 : Blo 1987435 1988235 := bstep (se 1 (by rfl) ⟨1491176, by rfl⟩ : syracuseStep 1988235 = 2982353) B2982353
theorem B6710309 : Blo 1987435 6710309 := bbase (se 4 (by rfl) ⟨629091, by rfl⟩ : syracuseStep 6710309 = 1258183) (by norm_num)
theorem B4473539 : Blo 1987435 4473539 := bstep (se 1 (by rfl) ⟨3355154, by rfl⟩ : syracuseStep 4473539 = 6710309) B6710309
theorem B2982359 : Blo 1987435 2982359 := bstep (se 1 (by rfl) ⟨2236769, by rfl⟩ : syracuseStep 2982359 = 4473539) B4473539
theorem B1988239 : Blo 1987435 1988239 := bstep (se 1 (by rfl) ⟨1491179, by rfl⟩ : syracuseStep 1988239 = 2982359) B2982359
theorem B2982365 : Blo 1987435 2982365 := bbase (se 3 (by rfl) ⟨559193, by rfl⟩ : syracuseStep 2982365 = 1118387) (by norm_num)
theorem B1988243 : Blo 1987435 1988243 := bstep (se 1 (by rfl) ⟨1491182, by rfl⟩ : syracuseStep 1988243 = 2982365) B2982365
theorem B4473557 : Blo 1987435 4473557 := bbase (se 7 (by rfl) ⟨52424, by rfl⟩ : syracuseStep 4473557 = 104849) (by norm_num)
theorem B2982371 : Blo 1987435 2982371 := bstep (se 1 (by rfl) ⟨2236778, by rfl⟩ : syracuseStep 2982371 = 4473557) B4473557
theorem B1988247 : Blo 1987435 1988247 := bstep (se 1 (by rfl) ⟨1491185, by rfl⟩ : syracuseStep 1988247 = 2982371) B2982371
theorem B8492789 : Blo 1987435 8492789 := bbase (se 5 (by rfl) ⟨398099, by rfl⟩ : syracuseStep 8492789 = 796199) (by norm_num)
theorem B5661859 : Blo 1987435 5661859 := bstep (se 1 (by rfl) ⟨4246394, by rfl⟩ : syracuseStep 5661859 = 8492789) B8492789
theorem B7549145 : Blo 1987435 7549145 := bstep (se 2 (by rfl) ⟨2830929, by rfl⟩ : syracuseStep 7549145 = 5661859) B5661859
theorem B5032763 : Blo 1987435 5032763 := bstep (se 1 (by rfl) ⟨3774572, by rfl⟩ : syracuseStep 5032763 = 7549145) B7549145
theorem B3355175 : Blo 1987435 3355175 := bstep (se 1 (by rfl) ⟨2516381, by rfl⟩ : syracuseStep 3355175 = 5032763) B5032763
theorem B2236783 : Blo 1987435 2236783 := bstep (se 1 (by rfl) ⟨1677587, by rfl⟩ : syracuseStep 2236783 = 3355175) B3355175
theorem B2982377 : Blo 1987435 2982377 := bstep (se 2 (by rfl) ⟨1118391, by rfl⟩ : syracuseStep 2982377 = 2236783) B2236783
theorem B1988251 : Blo 1987435 1988251 := bstep (se 1 (by rfl) ⟨1491188, by rfl⟩ : syracuseStep 1988251 = 2982377) B2982377
theorem B4030765 : Blo 1987435 4030765 := bbase (se 3 (by rfl) ⟨755768, by rfl⟩ : syracuseStep 4030765 = 1511537) (by norm_num)
theorem B21497413 : Blo 1987435 21497413 := bstep (se 4 (by rfl) ⟨2015382, by rfl⟩ : syracuseStep 21497413 = 4030765) B4030765
theorem B28663217 : Blo 1987435 28663217 := bstep (se 2 (by rfl) ⟨10748706, by rfl⟩ : syracuseStep 28663217 = 21497413) B21497413
theorem B19108811 : Blo 1987435 19108811 := bstep (se 1 (by rfl) ⟨14331608, by rfl⟩ : syracuseStep 19108811 = 28663217) B28663217
theorem B12739207 : Blo 1987435 12739207 := bstep (se 1 (by rfl) ⟨9554405, by rfl⟩ : syracuseStep 12739207 = 19108811) B19108811
theorem B16985609 : Blo 1987435 16985609 := bstep (se 2 (by rfl) ⟨6369603, by rfl⟩ : syracuseStep 16985609 = 12739207) B12739207
theorem B11323739 : Blo 1987435 11323739 := bstep (se 1 (by rfl) ⟨8492804, by rfl⟩ : syracuseStep 11323739 = 16985609) B16985609
theorem B7549159 : Blo 1987435 7549159 := bstep (se 1 (by rfl) ⟨5661869, by rfl⟩ : syracuseStep 7549159 = 11323739) B11323739
theorem B10065545 : Blo 1987435 10065545 := bstep (se 2 (by rfl) ⟨3774579, by rfl⟩ : syracuseStep 10065545 = 7549159) B7549159
theorem B6710363 : Blo 1987435 6710363 := bstep (se 1 (by rfl) ⟨5032772, by rfl⟩ : syracuseStep 6710363 = 10065545) B10065545
theorem B4473575 : Blo 1987435 4473575 := bstep (se 1 (by rfl) ⟨3355181, by rfl⟩ : syracuseStep 4473575 = 6710363) B6710363
theorem B2982383 : Blo 1987435 2982383 := bstep (se 1 (by rfl) ⟨2236787, by rfl⟩ : syracuseStep 2982383 = 4473575) B4473575
theorem B1988255 : Blo 1987435 1988255 := bstep (se 1 (by rfl) ⟨1491191, by rfl⟩ : syracuseStep 1988255 = 2982383) B2982383
theorem B2982389 : Blo 1987435 2982389 := bbase (se 5 (by rfl) ⟨139799, by rfl⟩ : syracuseStep 2982389 = 279599) (by norm_num)
theorem B1988259 : Blo 1987435 1988259 := bstep (se 1 (by rfl) ⟨1491194, by rfl⟩ : syracuseStep 1988259 = 2982389) B2982389
theorem B5661893 : Blo 1987435 5661893 := bbase (se 4 (by rfl) ⟨530802, by rfl⟩ : syracuseStep 5661893 = 1061605) (by norm_num)
theorem B3774595 : Blo 1987435 3774595 := bstep (se 1 (by rfl) ⟨2830946, by rfl⟩ : syracuseStep 3774595 = 5661893) B5661893
theorem B5032793 : Blo 1987435 5032793 := bstep (se 2 (by rfl) ⟨1887297, by rfl⟩ : syracuseStep 5032793 = 3774595) B3774595
theorem B3355195 : Blo 1987435 3355195 := bstep (se 1 (by rfl) ⟨2516396, by rfl⟩ : syracuseStep 3355195 = 5032793) B5032793
theorem B4473593 : Blo 1987435 4473593 := bstep (se 2 (by rfl) ⟨1677597, by rfl⟩ : syracuseStep 4473593 = 3355195) B3355195
theorem B2982395 : Blo 1987435 2982395 := bstep (se 1 (by rfl) ⟨2236796, by rfl⟩ : syracuseStep 2982395 = 4473593) B4473593
theorem B1988263 : Blo 1987435 1988263 := bstep (se 1 (by rfl) ⟨1491197, by rfl⟩ : syracuseStep 1988263 = 2982395) B2982395
theorem B2236801 : Blo 1987435 2236801 := bbase (se 2 (by rfl) ⟨838800, by rfl⟩ : syracuseStep 2236801 = 1677601) (by norm_num)
theorem B2982401 : Blo 1987435 2982401 := bstep (se 2 (by rfl) ⟨1118400, by rfl⟩ : syracuseStep 2982401 = 2236801) B2236801
theorem B1988267 : Blo 1987435 1988267 := bstep (se 1 (by rfl) ⟨1491200, by rfl⟩ : syracuseStep 1988267 = 2982401) B2982401
theorem B5032813 : Blo 1987435 5032813 := bbase (se 3 (by rfl) ⟨943652, by rfl⟩ : syracuseStep 5032813 = 1887305) (by norm_num)
theorem B6710417 : Blo 1987435 6710417 := bstep (se 2 (by rfl) ⟨2516406, by rfl⟩ : syracuseStep 6710417 = 5032813) B5032813
theorem B4473611 : Blo 1987435 4473611 := bstep (se 1 (by rfl) ⟨3355208, by rfl⟩ : syracuseStep 4473611 = 6710417) B6710417
theorem B2982407 : Blo 1987435 2982407 := bstep (se 1 (by rfl) ⟨2236805, by rfl⟩ : syracuseStep 2982407 = 4473611) B4473611
theorem B1988271 : Blo 1987435 1988271 := bstep (se 1 (by rfl) ⟨1491203, by rfl⟩ : syracuseStep 1988271 = 2982407) B2982407
theorem B2982413 : Blo 1987435 2982413 := bbase (se 3 (by rfl) ⟨559202, by rfl⟩ : syracuseStep 2982413 = 1118405) (by norm_num)
theorem B1988275 : Blo 1987435 1988275 := bstep (se 1 (by rfl) ⟨1491206, by rfl⟩ : syracuseStep 1988275 = 2982413) B2982413
theorem B4473629 : Blo 1987435 4473629 := bbase (se 3 (by rfl) ⟨838805, by rfl⟩ : syracuseStep 4473629 = 1677611) (by norm_num)
theorem B2982419 : Blo 1987435 2982419 := bstep (se 1 (by rfl) ⟨2236814, by rfl⟩ : syracuseStep 2982419 = 4473629) B4473629
theorem B1988279 : Blo 1987435 1988279 := bstep (se 1 (by rfl) ⟨1491209, by rfl⟩ : syracuseStep 1988279 = 2982419) B2982419
theorem B3355229 : Blo 1987435 3355229 := bbase (se 3 (by rfl) ⟨629105, by rfl⟩ : syracuseStep 3355229 = 1258211) (by norm_num)
theorem B2236819 : Blo 1987435 2236819 := bstep (se 1 (by rfl) ⟨1677614, by rfl⟩ : syracuseStep 2236819 = 3355229) B3355229
theorem B2982425 : Blo 1987435 2982425 := bstep (se 2 (by rfl) ⟨1118409, by rfl⟩ : syracuseStep 2982425 = 2236819) B2236819
theorem B1988283 : Blo 1987435 1988283 := bstep (se 1 (by rfl) ⟨1491212, by rfl⟩ : syracuseStep 1988283 = 2982425) B2982425
theorem B3184853 : Blo 1987435 3184853 := bbase (se 7 (by rfl) ⟨37322, by rfl⟩ : syracuseStep 3184853 = 74645) (by norm_num)
theorem B8492941 : Blo 1987435 8492941 := bstep (se 3 (by rfl) ⟨1592426, by rfl⟩ : syracuseStep 8492941 = 3184853) B3184853
theorem B11323921 : Blo 1987435 11323921 := bstep (se 2 (by rfl) ⟨4246470, by rfl⟩ : syracuseStep 11323921 = 8492941) B8492941
theorem B15098561 : Blo 1987435 15098561 := bstep (se 2 (by rfl) ⟨5661960, by rfl⟩ : syracuseStep 15098561 = 11323921) B11323921
theorem B10065707 : Blo 1987435 10065707 := bstep (se 1 (by rfl) ⟨7549280, by rfl⟩ : syracuseStep 10065707 = 15098561) B15098561
theorem B6710471 : Blo 1987435 6710471 := bstep (se 1 (by rfl) ⟨5032853, by rfl⟩ : syracuseStep 6710471 = 10065707) B10065707
theorem B4473647 : Blo 1987435 4473647 := bstep (se 1 (by rfl) ⟨3355235, by rfl⟩ : syracuseStep 4473647 = 6710471) B6710471
theorem B2982431 : Blo 1987435 2982431 := bstep (se 1 (by rfl) ⟨2236823, by rfl⟩ : syracuseStep 2982431 = 4473647) B4473647
theorem B1988287 : Blo 1987435 1988287 := bstep (se 1 (by rfl) ⟨1491215, by rfl⟩ : syracuseStep 1988287 = 2982431) B2982431
theorem B2982437 : Blo 1987435 2982437 := bbase (se 4 (by rfl) ⟨279603, by rfl⟩ : syracuseStep 2982437 = 559207) (by norm_num)
theorem B1988291 : Blo 1987435 1988291 := bstep (se 1 (by rfl) ⟨1491218, by rfl⟩ : syracuseStep 1988291 = 2982437) B2982437
theorem B2516437 : Blo 1987435 2516437 := bbase (se 7 (by rfl) ⟨29489, by rfl⟩ : syracuseStep 2516437 = 58979) (by norm_num)
theorem B3355249 : Blo 1987435 3355249 := bstep (se 2 (by rfl) ⟨1258218, by rfl⟩ : syracuseStep 3355249 = 2516437) B2516437
theorem B4473665 : Blo 1987435 4473665 := bstep (se 2 (by rfl) ⟨1677624, by rfl⟩ : syracuseStep 4473665 = 3355249) B3355249
theorem B2982443 : Blo 1987435 2982443 := bstep (se 1 (by rfl) ⟨2236832, by rfl⟩ : syracuseStep 2982443 = 4473665) B4473665
theorem B1988295 : Blo 1987435 1988295 := bstep (se 1 (by rfl) ⟨1491221, by rfl⟩ : syracuseStep 1988295 = 2982443) B2982443
theorem B2236837 : Blo 1987435 2236837 := bbase (se 4 (by rfl) ⟨209703, by rfl⟩ : syracuseStep 2236837 = 419407) (by norm_num)
theorem B2982449 : Blo 1987435 2982449 := bstep (se 2 (by rfl) ⟨1118418, by rfl⟩ : syracuseStep 2982449 = 2236837) B2236837
theorem B1988299 : Blo 1987435 1988299 := bstep (se 1 (by rfl) ⟨1491224, by rfl⟩ : syracuseStep 1988299 = 2982449) B2982449
theorem B7263749 : Blo 1987435 7263749 := bbase (se 4 (by rfl) ⟨680976, by rfl⟩ : syracuseStep 7263749 = 1361953) (by norm_num)
theorem B4842499 : Blo 1987435 4842499 := bstep (se 1 (by rfl) ⟨3631874, by rfl⟩ : syracuseStep 4842499 = 7263749) B7263749
theorem B6456665 : Blo 1987435 6456665 := bstep (se 2 (by rfl) ⟨2421249, by rfl⟩ : syracuseStep 6456665 = 4842499) B4842499
theorem B17217773 : Blo 1987435 17217773 := bstep (se 3 (by rfl) ⟨3228332, by rfl⟩ : syracuseStep 17217773 = 6456665) B6456665
theorem B11478515 : Blo 1987435 11478515 := bstep (se 1 (by rfl) ⟨8608886, by rfl⟩ : syracuseStep 11478515 = 17217773) B17217773
theorem B30609373 : Blo 1987435 30609373 := bstep (se 3 (by rfl) ⟨5739257, by rfl⟩ : syracuseStep 30609373 = 11478515) B11478515
theorem B40812497 : Blo 1987435 40812497 := bstep (se 2 (by rfl) ⟨15304686, by rfl⟩ : syracuseStep 40812497 = 30609373) B30609373
theorem B27208331 : Blo 1987435 27208331 := bstep (se 1 (by rfl) ⟨20406248, by rfl⟩ : syracuseStep 27208331 = 40812497) B40812497
theorem B18138887 : Blo 1987435 18138887 := bstep (se 1 (by rfl) ⟨13604165, by rfl⟩ : syracuseStep 18138887 = 27208331) B27208331
theorem B12092591 : Blo 1987435 12092591 := bstep (se 1 (by rfl) ⟨9069443, by rfl⟩ : syracuseStep 12092591 = 18138887) B18138887
theorem B8061727 : Blo 1987435 8061727 := bstep (se 1 (by rfl) ⟨6046295, by rfl⟩ : syracuseStep 8061727 = 12092591) B12092591
theorem B10748969 : Blo 1987435 10748969 := bstep (se 2 (by rfl) ⟨4030863, by rfl⟩ : syracuseStep 10748969 = 8061727) B8061727
theorem B7165979 : Blo 1987435 7165979 := bstep (se 1 (by rfl) ⟨5374484, by rfl⟩ : syracuseStep 7165979 = 10748969) B10748969
theorem B4777319 : Blo 1987435 4777319 := bstep (se 1 (by rfl) ⟨3582989, by rfl⟩ : syracuseStep 4777319 = 7165979) B7165979
theorem B12739517 : Blo 1987435 12739517 := bstep (se 3 (by rfl) ⟨2388659, by rfl⟩ : syracuseStep 12739517 = 4777319) B4777319
theorem B8493011 : Blo 1987435 8493011 := bstep (se 1 (by rfl) ⟨6369758, by rfl⟩ : syracuseStep 8493011 = 12739517) B12739517
theorem B5662007 : Blo 1987435 5662007 := bstep (se 1 (by rfl) ⟨4246505, by rfl⟩ : syracuseStep 5662007 = 8493011) B8493011
theorem B3774671 : Blo 1987435 3774671 := bstep (se 1 (by rfl) ⟨2831003, by rfl⟩ : syracuseStep 3774671 = 5662007) B5662007
theorem B2516447 : Blo 1987435 2516447 := bstep (se 1 (by rfl) ⟨1887335, by rfl⟩ : syracuseStep 2516447 = 3774671) B3774671
theorem B6710525 : Blo 1987435 6710525 := bstep (se 3 (by rfl) ⟨1258223, by rfl⟩ : syracuseStep 6710525 = 2516447) B2516447
theorem B4473683 : Blo 1987435 4473683 := bstep (se 1 (by rfl) ⟨3355262, by rfl⟩ : syracuseStep 4473683 = 6710525) B6710525
theorem B2982455 : Blo 1987435 2982455 := bstep (se 1 (by rfl) ⟨2236841, by rfl⟩ : syracuseStep 2982455 = 4473683) B4473683
theorem B1988303 : Blo 1987435 1988303 := bstep (se 1 (by rfl) ⟨1491227, by rfl⟩ : syracuseStep 1988303 = 2982455) B2982455
theorem B2982461 : Blo 1987435 2982461 := bbase (se 3 (by rfl) ⟨559211, by rfl⟩ : syracuseStep 2982461 = 1118423) (by norm_num)
theorem B1988307 : Blo 1987435 1988307 := bstep (se 1 (by rfl) ⟨1491230, by rfl⟩ : syracuseStep 1988307 = 2982461) B2982461
theorem B4473701 : Blo 1987435 4473701 := bbase (se 4 (by rfl) ⟨419409, by rfl⟩ : syracuseStep 4473701 = 838819) (by norm_num)
theorem B2982467 : Blo 1987435 2982467 := bstep (se 1 (by rfl) ⟨2236850, by rfl⟩ : syracuseStep 2982467 = 4473701) B4473701
theorem B1988311 : Blo 1987435 1988311 := bstep (se 1 (by rfl) ⟨1491233, by rfl⟩ : syracuseStep 1988311 = 2982467) B2982467
theorem B5032925 : Blo 1987435 5032925 := bbase (se 3 (by rfl) ⟨943673, by rfl⟩ : syracuseStep 5032925 = 1887347) (by norm_num)
theorem B3355283 : Blo 1987435 3355283 := bstep (se 1 (by rfl) ⟨2516462, by rfl⟩ : syracuseStep 3355283 = 5032925) B5032925
theorem B2236855 : Blo 1987435 2236855 := bstep (se 1 (by rfl) ⟨1677641, by rfl⟩ : syracuseStep 2236855 = 3355283) B3355283
theorem B2982473 : Blo 1987435 2982473 := bstep (se 2 (by rfl) ⟨1118427, by rfl⟩ : syracuseStep 2982473 = 2236855) B2236855
theorem B1988315 : Blo 1987435 1988315 := bstep (se 1 (by rfl) ⟨1491236, by rfl⟩ : syracuseStep 1988315 = 2982473) B2982473
theorem B3774701 : Blo 1987435 3774701 := bbase (se 3 (by rfl) ⟨707756, by rfl⟩ : syracuseStep 3774701 = 1415513) (by norm_num)
theorem B10065869 : Blo 1987435 10065869 := bstep (se 3 (by rfl) ⟨1887350, by rfl⟩ : syracuseStep 10065869 = 3774701) B3774701
theorem B6710579 : Blo 1987435 6710579 := bstep (se 1 (by rfl) ⟨5032934, by rfl⟩ : syracuseStep 6710579 = 10065869) B10065869
theorem B4473719 : Blo 1987435 4473719 := bstep (se 1 (by rfl) ⟨3355289, by rfl⟩ : syracuseStep 4473719 = 6710579) B6710579
theorem B2982479 : Blo 1987435 2982479 := bstep (se 1 (by rfl) ⟨2236859, by rfl⟩ : syracuseStep 2982479 = 4473719) B4473719
theorem B1988319 : Blo 1987435 1988319 := bstep (se 1 (by rfl) ⟨1491239, by rfl⟩ : syracuseStep 1988319 = 2982479) B2982479
theorem B2982485 : Blo 1987435 2982485 := bbase (se 8 (by rfl) ⟨17475, by rfl⟩ : syracuseStep 2982485 = 34951) (by norm_num)
theorem B1988323 : Blo 1987435 1988323 := bstep (se 1 (by rfl) ⟨1491242, by rfl⟩ : syracuseStep 1988323 = 2982485) B2982485
theorem B5374549 : Blo 1987435 5374549 := bbase (se 8 (by rfl) ⟨31491, by rfl⟩ : syracuseStep 5374549 = 62983) (by norm_num)
theorem B7166065 : Blo 1987435 7166065 := bstep (se 2 (by rfl) ⟨2687274, by rfl⟩ : syracuseStep 7166065 = 5374549) B5374549
theorem B9554753 : Blo 1987435 9554753 := bstep (se 2 (by rfl) ⟨3583032, by rfl⟩ : syracuseStep 9554753 = 7166065) B7166065
theorem B6369835 : Blo 1987435 6369835 := bstep (se 1 (by rfl) ⟨4777376, by rfl⟩ : syracuseStep 6369835 = 9554753) B9554753
theorem B8493113 : Blo 1987435 8493113 := bstep (se 2 (by rfl) ⟨3184917, by rfl⟩ : syracuseStep 8493113 = 6369835) B6369835
theorem B5662075 : Blo 1987435 5662075 := bstep (se 1 (by rfl) ⟨4246556, by rfl⟩ : syracuseStep 5662075 = 8493113) B8493113
theorem B7549433 : Blo 1987435 7549433 := bstep (se 2 (by rfl) ⟨2831037, by rfl⟩ : syracuseStep 7549433 = 5662075) B5662075
theorem B5032955 : Blo 1987435 5032955 := bstep (se 1 (by rfl) ⟨3774716, by rfl⟩ : syracuseStep 5032955 = 7549433) B7549433
theorem B3355303 : Blo 1987435 3355303 := bstep (se 1 (by rfl) ⟨2516477, by rfl⟩ : syracuseStep 3355303 = 5032955) B5032955
theorem B4473737 : Blo 1987435 4473737 := bstep (se 2 (by rfl) ⟨1677651, by rfl⟩ : syracuseStep 4473737 = 3355303) B3355303
theorem B2982491 : Blo 1987435 2982491 := bstep (se 1 (by rfl) ⟨2236868, by rfl⟩ : syracuseStep 2982491 = 4473737) B4473737
theorem B1988327 : Blo 1987435 1988327 := bstep (se 1 (by rfl) ⟨1491245, by rfl⟩ : syracuseStep 1988327 = 2982491) B2982491
theorem B2236873 : Blo 1987435 2236873 := bbase (se 2 (by rfl) ⟨838827, by rfl⟩ : syracuseStep 2236873 = 1677655) (by norm_num)
theorem B2982497 : Blo 1987435 2982497 := bstep (se 2 (by rfl) ⟨1118436, by rfl⟩ : syracuseStep 2982497 = 2236873) B2236873
theorem B1988331 : Blo 1987435 1988331 := bstep (se 1 (by rfl) ⟨1491248, by rfl⟩ : syracuseStep 1988331 = 2982497) B2982497
theorem B16986293 : Blo 1987435 16986293 := bbase (se 5 (by rfl) ⟨796232, by rfl⟩ : syracuseStep 16986293 = 1592465) (by norm_num)
theorem B11324195 : Blo 1987435 11324195 := bstep (se 1 (by rfl) ⟨8493146, by rfl⟩ : syracuseStep 11324195 = 16986293) B16986293
theorem B7549463 : Blo 1987435 7549463 := bstep (se 1 (by rfl) ⟨5662097, by rfl⟩ : syracuseStep 7549463 = 11324195) B11324195
theorem B5032975 : Blo 1987435 5032975 := bstep (se 1 (by rfl) ⟨3774731, by rfl⟩ : syracuseStep 5032975 = 7549463) B7549463
theorem B6710633 : Blo 1987435 6710633 := bstep (se 2 (by rfl) ⟨2516487, by rfl⟩ : syracuseStep 6710633 = 5032975) B5032975
theorem B4473755 : Blo 1987435 4473755 := bstep (se 1 (by rfl) ⟨3355316, by rfl⟩ : syracuseStep 4473755 = 6710633) B6710633
theorem B2982503 : Blo 1987435 2982503 := bstep (se 1 (by rfl) ⟨2236877, by rfl⟩ : syracuseStep 2982503 = 4473755) B4473755
theorem B1988335 : Blo 1987435 1988335 := bstep (se 1 (by rfl) ⟨1491251, by rfl⟩ : syracuseStep 1988335 = 2982503) B2982503
theorem B2982509 : Blo 1987435 2982509 := bbase (se 3 (by rfl) ⟨559220, by rfl⟩ : syracuseStep 2982509 = 1118441) (by norm_num)
theorem B1988339 : Blo 1987435 1988339 := bstep (se 1 (by rfl) ⟨1491254, by rfl⟩ : syracuseStep 1988339 = 2982509) B2982509
theorem B4473773 : Blo 1987435 4473773 := bbase (se 3 (by rfl) ⟨838832, by rfl⟩ : syracuseStep 4473773 = 1677665) (by norm_num)
theorem B2982515 : Blo 1987435 2982515 := bstep (se 1 (by rfl) ⟨2236886, by rfl⟩ : syracuseStep 2982515 = 4473773) B4473773
theorem B1988343 : Blo 1987435 1988343 := bstep (se 1 (by rfl) ⟨1491257, by rfl⟩ : syracuseStep 1988343 = 2982515) B2982515
theorem B5662133 : Blo 1987435 5662133 := bbase (se 5 (by rfl) ⟨265412, by rfl⟩ : syracuseStep 5662133 = 530825) (by norm_num)
theorem B3774755 : Blo 1987435 3774755 := bstep (se 1 (by rfl) ⟨2831066, by rfl⟩ : syracuseStep 3774755 = 5662133) B5662133
theorem B2516503 : Blo 1987435 2516503 := bstep (se 1 (by rfl) ⟨1887377, by rfl⟩ : syracuseStep 2516503 = 3774755) B3774755
theorem B3355337 : Blo 1987435 3355337 := bstep (se 2 (by rfl) ⟨1258251, by rfl⟩ : syracuseStep 3355337 = 2516503) B2516503
theorem B2236891 : Blo 1987435 2236891 := bstep (se 1 (by rfl) ⟨1677668, by rfl⟩ : syracuseStep 2236891 = 3355337) B3355337
theorem B2982521 : Blo 1987435 2982521 := bstep (se 2 (by rfl) ⟨1118445, by rfl⟩ : syracuseStep 2982521 = 2236891) B2236891
theorem B1988347 : Blo 1987435 1988347 := bstep (se 1 (by rfl) ⟨1491260, by rfl⟩ : syracuseStep 1988347 = 2982521) B2982521
theorem B5447941 : Blo 1987435 5447941 := bbase (se 4 (by rfl) ⟨510744, by rfl⟩ : syracuseStep 5447941 = 1021489) (by norm_num)
theorem B29055685 : Blo 1987435 29055685 := bstep (se 4 (by rfl) ⟨2723970, by rfl⟩ : syracuseStep 29055685 = 5447941) B5447941
theorem B38740913 : Blo 1987435 38740913 := bstep (se 2 (by rfl) ⟨14527842, by rfl⟩ : syracuseStep 38740913 = 29055685) B29055685
theorem B25827275 : Blo 1987435 25827275 := bstep (se 1 (by rfl) ⟨19370456, by rfl⟩ : syracuseStep 25827275 = 38740913) B38740913
theorem B17218183 : Blo 1987435 17218183 := bstep (se 1 (by rfl) ⟨12913637, by rfl⟩ : syracuseStep 17218183 = 25827275) B25827275
theorem B22957577 : Blo 1987435 22957577 := bstep (se 2 (by rfl) ⟨8609091, by rfl⟩ : syracuseStep 22957577 = 17218183) B17218183
theorem B15305051 : Blo 1987435 15305051 := bstep (se 1 (by rfl) ⟨11478788, by rfl⟩ : syracuseStep 15305051 = 22957577) B22957577
theorem B10203367 : Blo 1987435 10203367 := bstep (se 1 (by rfl) ⟨7652525, by rfl⟩ : syracuseStep 10203367 = 15305051) B15305051
theorem B13604489 : Blo 1987435 13604489 := bstep (se 2 (by rfl) ⟨5101683, by rfl⟩ : syracuseStep 13604489 = 10203367) B10203367
theorem B9069659 : Blo 1987435 9069659 := bstep (se 1 (by rfl) ⟨6802244, by rfl⟩ : syracuseStep 9069659 = 13604489) B13604489
theorem B6046439 : Blo 1987435 6046439 := bstep (se 1 (by rfl) ⟨4534829, by rfl⟩ : syracuseStep 6046439 = 9069659) B9069659
theorem B64495349 : Blo 1987435 64495349 := bstep (se 5 (by rfl) ⟨3023219, by rfl⟩ : syracuseStep 64495349 = 6046439) B6046439
theorem B42996899 : Blo 1987435 42996899 := bstep (se 1 (by rfl) ⟨32247674, by rfl⟩ : syracuseStep 42996899 = 64495349) B64495349
theorem B28664599 : Blo 1987435 28664599 := bstep (se 1 (by rfl) ⟨21498449, by rfl⟩ : syracuseStep 28664599 = 42996899) B42996899
theorem B38219465 : Blo 1987435 38219465 := bstep (se 2 (by rfl) ⟨14332299, by rfl⟩ : syracuseStep 38219465 = 28664599) B28664599
theorem B25479643 : Blo 1987435 25479643 := bstep (se 1 (by rfl) ⟨19109732, by rfl⟩ : syracuseStep 25479643 = 38219465) B38219465
theorem B33972857 : Blo 1987435 33972857 := bstep (se 2 (by rfl) ⟨12739821, by rfl⟩ : syracuseStep 33972857 = 25479643) B25479643
theorem B22648571 : Blo 1987435 22648571 := bstep (se 1 (by rfl) ⟨16986428, by rfl⟩ : syracuseStep 22648571 = 33972857) B33972857
theorem B15099047 : Blo 1987435 15099047 := bstep (se 1 (by rfl) ⟨11324285, by rfl⟩ : syracuseStep 15099047 = 22648571) B22648571
theorem B10066031 : Blo 1987435 10066031 := bstep (se 1 (by rfl) ⟨7549523, by rfl⟩ : syracuseStep 10066031 = 15099047) B15099047
theorem B6710687 : Blo 1987435 6710687 := bstep (se 1 (by rfl) ⟨5033015, by rfl⟩ : syracuseStep 6710687 = 10066031) B10066031
theorem B4473791 : Blo 1987435 4473791 := bstep (se 1 (by rfl) ⟨3355343, by rfl⟩ : syracuseStep 4473791 = 6710687) B6710687
theorem B2982527 : Blo 1987435 2982527 := bstep (se 1 (by rfl) ⟨2236895, by rfl⟩ : syracuseStep 2982527 = 4473791) B4473791
theorem B1988351 : Blo 1987435 1988351 := bstep (se 1 (by rfl) ⟨1491263, by rfl⟩ : syracuseStep 1988351 = 2982527) B2982527
theorem B2982533 : Blo 1987435 2982533 := bbase (se 4 (by rfl) ⟨279612, by rfl⟩ : syracuseStep 2982533 = 559225) (by norm_num)
theorem B1988355 : Blo 1987435 1988355 := bstep (se 1 (by rfl) ⟨1491266, by rfl⟩ : syracuseStep 1988355 = 2982533) B2982533
theorem B3355357 : Blo 1987435 3355357 := bbase (se 3 (by rfl) ⟨629129, by rfl⟩ : syracuseStep 3355357 = 1258259) (by norm_num)
theorem B4473809 : Blo 1987435 4473809 := bstep (se 2 (by rfl) ⟨1677678, by rfl⟩ : syracuseStep 4473809 = 3355357) B3355357
theorem B2982539 : Blo 1987435 2982539 := bstep (se 1 (by rfl) ⟨2236904, by rfl⟩ : syracuseStep 2982539 = 4473809) B4473809
theorem B1988359 : Blo 1987435 1988359 := bstep (se 1 (by rfl) ⟨1491269, by rfl⟩ : syracuseStep 1988359 = 2982539) B2982539
theorem B2236909 : Blo 1987435 2236909 := bbase (se 3 (by rfl) ⟨419420, by rfl⟩ : syracuseStep 2236909 = 838841) (by norm_num)
theorem B2982545 : Blo 1987435 2982545 := bstep (se 2 (by rfl) ⟨1118454, by rfl⟩ : syracuseStep 2982545 = 2236909) B2236909
theorem B1988363 : Blo 1987435 1988363 := bstep (se 1 (by rfl) ⟨1491272, by rfl⟩ : syracuseStep 1988363 = 2982545) B2982545
theorem B6710741 : Blo 1987435 6710741 := bbase (se 7 (by rfl) ⟨78641, by rfl⟩ : syracuseStep 6710741 = 157283) (by norm_num)
theorem B4473827 : Blo 1987435 4473827 := bstep (se 1 (by rfl) ⟨3355370, by rfl⟩ : syracuseStep 4473827 = 6710741) B6710741
theorem B2982551 : Blo 1987435 2982551 := bstep (se 1 (by rfl) ⟨2236913, by rfl⟩ : syracuseStep 2982551 = 4473827) B4473827
theorem B1988367 : Blo 1987435 1988367 := bstep (se 1 (by rfl) ⟨1491275, by rfl⟩ : syracuseStep 1988367 = 2982551) B2982551
theorem B2982557 : Blo 1987435 2982557 := bbase (se 3 (by rfl) ⟨559229, by rfl⟩ : syracuseStep 2982557 = 1118459) (by norm_num)
theorem B1988371 : Blo 1987435 1988371 := bstep (se 1 (by rfl) ⟨1491278, by rfl⟩ : syracuseStep 1988371 = 2982557) B2982557
theorem B4473845 : Blo 1987435 4473845 := bbase (se 5 (by rfl) ⟨209711, by rfl⟩ : syracuseStep 4473845 = 419423) (by norm_num)
theorem B2982563 : Blo 1987435 2982563 := bstep (se 1 (by rfl) ⟨2236922, by rfl⟩ : syracuseStep 2982563 = 4473845) B4473845
theorem B1988375 : Blo 1987435 1988375 := bstep (se 1 (by rfl) ⟨1491281, by rfl⟩ : syracuseStep 1988375 = 2982563) B2982563
theorem B5241917 : Blo 1987435 5241917 := bbase (se 3 (by rfl) ⟨982859, by rfl⟩ : syracuseStep 5241917 = 1965719) (by norm_num)
theorem B3494611 : Blo 1987435 3494611 := bstep (se 1 (by rfl) ⟨2620958, by rfl⟩ : syracuseStep 3494611 = 5241917) B5241917
theorem B4659481 : Blo 1987435 4659481 := bstep (se 2 (by rfl) ⟨1747305, by rfl⟩ : syracuseStep 4659481 = 3494611) B3494611
theorem B6212641 : Blo 1987435 6212641 := bstep (se 2 (by rfl) ⟨2329740, by rfl⟩ : syracuseStep 6212641 = 4659481) B4659481
theorem B8283521 : Blo 1987435 8283521 := bstep (se 2 (by rfl) ⟨3106320, by rfl⟩ : syracuseStep 8283521 = 6212641) B6212641
theorem B5522347 : Blo 1987435 5522347 := bstep (se 1 (by rfl) ⟨4141760, by rfl⟩ : syracuseStep 5522347 = 8283521) B8283521
theorem B29452517 : Blo 1987435 29452517 := bstep (se 4 (by rfl) ⟨2761173, by rfl⟩ : syracuseStep 29452517 = 5522347) B5522347
theorem B19635011 : Blo 1987435 19635011 := bstep (se 1 (by rfl) ⟨14726258, by rfl⟩ : syracuseStep 19635011 = 29452517) B29452517
theorem B13090007 : Blo 1987435 13090007 := bstep (se 1 (by rfl) ⟨9817505, by rfl⟩ : syracuseStep 13090007 = 19635011) B19635011
theorem B34906685 : Blo 1987435 34906685 := bstep (se 3 (by rfl) ⟨6545003, by rfl⟩ : syracuseStep 34906685 = 13090007) B13090007
theorem B93084493 : Blo 1987435 93084493 := bstep (se 3 (by rfl) ⟨17453342, by rfl⟩ : syracuseStep 93084493 = 34906685) B34906685
theorem B124112657 : Blo 1987435 124112657 := bstep (se 2 (by rfl) ⟨46542246, by rfl⟩ : syracuseStep 124112657 = 93084493) B93084493
theorem B82741771 : Blo 1987435 82741771 := bstep (se 1 (by rfl) ⟨62056328, by rfl⟩ : syracuseStep 82741771 = 124112657) B124112657
theorem B110322361 : Blo 1987435 110322361 := bstep (se 2 (by rfl) ⟨41370885, by rfl⟩ : syracuseStep 110322361 = 82741771) B82741771
theorem B147096481 : Blo 1987435 147096481 := bstep (se 2 (by rfl) ⟨55161180, by rfl⟩ : syracuseStep 147096481 = 110322361) B110322361
theorem B196128641 : Blo 1987435 196128641 := bstep (se 2 (by rfl) ⟨73548240, by rfl⟩ : syracuseStep 196128641 = 147096481) B147096481
theorem B130752427 : Blo 1987435 130752427 := bstep (se 1 (by rfl) ⟨98064320, by rfl⟩ : syracuseStep 130752427 = 196128641) B196128641
theorem B174336569 : Blo 1987435 174336569 := bstep (se 2 (by rfl) ⟨65376213, by rfl⟩ : syracuseStep 174336569 = 130752427) B130752427
theorem B116224379 : Blo 1987435 116224379 := bstep (se 1 (by rfl) ⟨87168284, by rfl⟩ : syracuseStep 116224379 = 174336569) B174336569
theorem B77482919 : Blo 1987435 77482919 := bstep (se 1 (by rfl) ⟨58112189, by rfl⟩ : syracuseStep 77482919 = 116224379) B116224379
theorem B206621117 : Blo 1987435 206621117 := bstep (se 3 (by rfl) ⟨38741459, by rfl⟩ : syracuseStep 206621117 = 77482919) B77482919
theorem B137747411 : Blo 1987435 137747411 := bstep (se 1 (by rfl) ⟨103310558, by rfl⟩ : syracuseStep 137747411 = 206621117) B206621117
theorem B91831607 : Blo 1987435 91831607 := bstep (se 1 (by rfl) ⟨68873705, by rfl⟩ : syracuseStep 91831607 = 137747411) B137747411
theorem B61221071 : Blo 1987435 61221071 := bstep (se 1 (by rfl) ⟨45915803, by rfl⟩ : syracuseStep 61221071 = 91831607) B91831607
theorem B40814047 : Blo 1987435 40814047 := bstep (se 1 (by rfl) ⟨30610535, by rfl⟩ : syracuseStep 40814047 = 61221071) B61221071
theorem B54418729 : Blo 1987435 54418729 := bstep (se 2 (by rfl) ⟨20407023, by rfl⟩ : syracuseStep 54418729 = 40814047) B40814047
theorem B72558305 : Blo 1987435 72558305 := bstep (se 2 (by rfl) ⟨27209364, by rfl⟩ : syracuseStep 72558305 = 54418729) B54418729
theorem B48372203 : Blo 1987435 48372203 := bstep (se 1 (by rfl) ⟨36279152, by rfl⟩ : syracuseStep 48372203 = 72558305) B72558305
theorem B32248135 : Blo 1987435 32248135 := bstep (se 1 (by rfl) ⟨24186101, by rfl⟩ : syracuseStep 32248135 = 48372203) B48372203
theorem B42997513 : Blo 1987435 42997513 := bstep (se 2 (by rfl) ⟨16124067, by rfl⟩ : syracuseStep 42997513 = 32248135) B32248135
theorem B57330017 : Blo 1987435 57330017 := bstep (se 2 (by rfl) ⟨21498756, by rfl⟩ : syracuseStep 57330017 = 42997513) B42997513
theorem B38220011 : Blo 1987435 38220011 := bstep (se 1 (by rfl) ⟨28665008, by rfl⟩ : syracuseStep 38220011 = 57330017) B57330017
theorem B25480007 : Blo 1987435 25480007 := bstep (se 1 (by rfl) ⟨19110005, by rfl⟩ : syracuseStep 25480007 = 38220011) B38220011
theorem B16986671 : Blo 1987435 16986671 := bstep (se 1 (by rfl) ⟨12740003, by rfl⟩ : syracuseStep 16986671 = 25480007) B25480007
theorem B11324447 : Blo 1987435 11324447 := bstep (se 1 (by rfl) ⟨8493335, by rfl⟩ : syracuseStep 11324447 = 16986671) B16986671
theorem B7549631 : Blo 1987435 7549631 := bstep (se 1 (by rfl) ⟨5662223, by rfl⟩ : syracuseStep 7549631 = 11324447) B11324447
theorem B5033087 : Blo 1987435 5033087 := bstep (se 1 (by rfl) ⟨3774815, by rfl⟩ : syracuseStep 5033087 = 7549631) B7549631
theorem B3355391 : Blo 1987435 3355391 := bstep (se 1 (by rfl) ⟨2516543, by rfl⟩ : syracuseStep 3355391 = 5033087) B5033087
theorem B2236927 : Blo 1987435 2236927 := bstep (se 1 (by rfl) ⟨1677695, by rfl⟩ : syracuseStep 2236927 = 3355391) B3355391
theorem B2982569 : Blo 1987435 2982569 := bstep (se 2 (by rfl) ⟨1118463, by rfl⟩ : syracuseStep 2982569 = 2236927) B2236927
theorem B1988379 : Blo 1987435 1988379 := bstep (se 1 (by rfl) ⟨1491284, by rfl⟩ : syracuseStep 1988379 = 2982569) B2982569
theorem B2831117 : Blo 1987435 2831117 := bbase (se 3 (by rfl) ⟨530834, by rfl⟩ : syracuseStep 2831117 = 1061669) (by norm_num)
theorem B7549645 : Blo 1987435 7549645 := bstep (se 3 (by rfl) ⟨1415558, by rfl⟩ : syracuseStep 7549645 = 2831117) B2831117
theorem B10066193 : Blo 1987435 10066193 := bstep (se 2 (by rfl) ⟨3774822, by rfl⟩ : syracuseStep 10066193 = 7549645) B7549645
theorem B6710795 : Blo 1987435 6710795 := bstep (se 1 (by rfl) ⟨5033096, by rfl⟩ : syracuseStep 6710795 = 10066193) B10066193
theorem B4473863 : Blo 1987435 4473863 := bstep (se 1 (by rfl) ⟨3355397, by rfl⟩ : syracuseStep 4473863 = 6710795) B6710795
theorem B2982575 : Blo 1987435 2982575 := bstep (se 1 (by rfl) ⟨2236931, by rfl⟩ : syracuseStep 2982575 = 4473863) B4473863
theorem B1988383 : Blo 1987435 1988383 := bstep (se 1 (by rfl) ⟨1491287, by rfl⟩ : syracuseStep 1988383 = 2982575) B2982575
theorem B2982581 : Blo 1987435 2982581 := bbase (se 5 (by rfl) ⟨139808, by rfl⟩ : syracuseStep 2982581 = 279617) (by norm_num)
theorem B1988387 : Blo 1987435 1988387 := bstep (se 1 (by rfl) ⟨1491290, by rfl⟩ : syracuseStep 1988387 = 2982581) B2982581
theorem B5033117 : Blo 1987435 5033117 := bbase (se 3 (by rfl) ⟨943709, by rfl⟩ : syracuseStep 5033117 = 1887419) (by norm_num)
theorem B3355411 : Blo 1987435 3355411 := bstep (se 1 (by rfl) ⟨2516558, by rfl⟩ : syracuseStep 3355411 = 5033117) B5033117
theorem B4473881 : Blo 1987435 4473881 := bstep (se 2 (by rfl) ⟨1677705, by rfl⟩ : syracuseStep 4473881 = 3355411) B3355411
theorem B2982587 : Blo 1987435 2982587 := bstep (se 1 (by rfl) ⟨2236940, by rfl⟩ : syracuseStep 2982587 = 4473881) B4473881
theorem B1988391 : Blo 1987435 1988391 := bstep (se 1 (by rfl) ⟨1491293, by rfl⟩ : syracuseStep 1988391 = 2982587) B2982587
theorem B2236945 : Blo 1987435 2236945 := bbase (se 2 (by rfl) ⟨838854, by rfl⟩ : syracuseStep 2236945 = 1677709) (by norm_num)
theorem B2982593 : Blo 1987435 2982593 := bstep (se 2 (by rfl) ⟨1118472, by rfl⟩ : syracuseStep 2982593 = 2236945) B2236945
theorem B1988395 : Blo 1987435 1988395 := bstep (se 1 (by rfl) ⟨1491296, by rfl⟩ : syracuseStep 1988395 = 2982593) B2982593
theorem B3774853 : Blo 1987435 3774853 := bbase (se 4 (by rfl) ⟨353892, by rfl⟩ : syracuseStep 3774853 = 707785) (by norm_num)
theorem B5033137 : Blo 1987435 5033137 := bstep (se 2 (by rfl) ⟨1887426, by rfl⟩ : syracuseStep 5033137 = 3774853) B3774853
theorem B6710849 : Blo 1987435 6710849 := bstep (se 2 (by rfl) ⟨2516568, by rfl⟩ : syracuseStep 6710849 = 5033137) B5033137
theorem B4473899 : Blo 1987435 4473899 := bstep (se 1 (by rfl) ⟨3355424, by rfl⟩ : syracuseStep 4473899 = 6710849) B6710849
theorem B2982599 : Blo 1987435 2982599 := bstep (se 1 (by rfl) ⟨2236949, by rfl⟩ : syracuseStep 2982599 = 4473899) B4473899
theorem B1988399 : Blo 1987435 1988399 := bstep (se 1 (by rfl) ⟨1491299, by rfl⟩ : syracuseStep 1988399 = 2982599) B2982599
theorem B2982605 : Blo 1987435 2982605 := bbase (se 3 (by rfl) ⟨559238, by rfl⟩ : syracuseStep 2982605 = 1118477) (by norm_num)
theorem B1988403 : Blo 1987435 1988403 := bstep (se 1 (by rfl) ⟨1491302, by rfl⟩ : syracuseStep 1988403 = 2982605) B2982605
theorem B4473917 : Blo 1987435 4473917 := bbase (se 3 (by rfl) ⟨838859, by rfl⟩ : syracuseStep 4473917 = 1677719) (by norm_num)
theorem B2982611 : Blo 1987435 2982611 := bstep (se 1 (by rfl) ⟨2236958, by rfl⟩ : syracuseStep 2982611 = 4473917) B4473917
theorem B1988407 : Blo 1987435 1988407 := bstep (se 1 (by rfl) ⟨1491305, by rfl⟩ : syracuseStep 1988407 = 2982611) B2982611
theorem B3355445 : Blo 1987435 3355445 := bbase (se 5 (by rfl) ⟨157286, by rfl⟩ : syracuseStep 3355445 = 314573) (by norm_num)
theorem B2236963 : Blo 1987435 2236963 := bstep (se 1 (by rfl) ⟨1677722, by rfl⟩ : syracuseStep 2236963 = 3355445) B3355445
theorem B2982617 : Blo 1987435 2982617 := bstep (se 2 (by rfl) ⟨1118481, by rfl⟩ : syracuseStep 2982617 = 2236963) B2236963
theorem B1988411 : Blo 1987435 1988411 := bstep (se 1 (by rfl) ⟨1491308, by rfl⟩ : syracuseStep 1988411 = 2982617) B2982617
theorem B5662325 : Blo 1987435 5662325 := bbase (se 5 (by rfl) ⟨265421, by rfl⟩ : syracuseStep 5662325 = 530843) (by norm_num)
theorem B15099533 : Blo 1987435 15099533 := bstep (se 3 (by rfl) ⟨2831162, by rfl⟩ : syracuseStep 15099533 = 5662325) B5662325
theorem B10066355 : Blo 1987435 10066355 := bstep (se 1 (by rfl) ⟨7549766, by rfl⟩ : syracuseStep 10066355 = 15099533) B15099533
theorem B6710903 : Blo 1987435 6710903 := bstep (se 1 (by rfl) ⟨5033177, by rfl⟩ : syracuseStep 6710903 = 10066355) B10066355
theorem B4473935 : Blo 1987435 4473935 := bstep (se 1 (by rfl) ⟨3355451, by rfl⟩ : syracuseStep 4473935 = 6710903) B6710903
theorem B2982623 : Blo 1987435 2982623 := bstep (se 1 (by rfl) ⟨2236967, by rfl⟩ : syracuseStep 2982623 = 4473935) B4473935
theorem B1988415 : Blo 1987435 1988415 := bstep (se 1 (by rfl) ⟨1491311, by rfl⟩ : syracuseStep 1988415 = 2982623) B2982623
theorem B2982629 : Blo 1987435 2982629 := bbase (se 4 (by rfl) ⟨279621, by rfl⟩ : syracuseStep 2982629 = 559243) (by norm_num)
theorem B1988419 : Blo 1987435 1988419 := bstep (se 1 (by rfl) ⟨1491314, by rfl⟩ : syracuseStep 1988419 = 2982629) B2982629
theorem B2123381 : Blo 1987435 2123381 := bbase (se 5 (by rfl) ⟨99533, by rfl⟩ : syracuseStep 2123381 = 199067) (by norm_num)
theorem B5662349 : Blo 1987435 5662349 := bstep (se 3 (by rfl) ⟨1061690, by rfl⟩ : syracuseStep 5662349 = 2123381) B2123381
theorem B3774899 : Blo 1987435 3774899 := bstep (se 1 (by rfl) ⟨2831174, by rfl⟩ : syracuseStep 3774899 = 5662349) B5662349
theorem B2516599 : Blo 1987435 2516599 := bstep (se 1 (by rfl) ⟨1887449, by rfl⟩ : syracuseStep 2516599 = 3774899) B3774899
theorem B3355465 : Blo 1987435 3355465 := bstep (se 2 (by rfl) ⟨1258299, by rfl⟩ : syracuseStep 3355465 = 2516599) B2516599
theorem B4473953 : Blo 1987435 4473953 := bstep (se 2 (by rfl) ⟨1677732, by rfl⟩ : syracuseStep 4473953 = 3355465) B3355465
theorem B2982635 : Blo 1987435 2982635 := bstep (se 1 (by rfl) ⟨2236976, by rfl⟩ : syracuseStep 2982635 = 4473953) B4473953
theorem B1988423 : Blo 1987435 1988423 := bstep (se 1 (by rfl) ⟨1491317, by rfl⟩ : syracuseStep 1988423 = 2982635) B2982635
theorem B2236981 : Blo 1987435 2236981 := bbase (se 5 (by rfl) ⟨104858, by rfl⟩ : syracuseStep 2236981 = 209717) (by norm_num)
theorem B2982641 : Blo 1987435 2982641 := bstep (se 2 (by rfl) ⟨1118490, by rfl⟩ : syracuseStep 2982641 = 2236981) B2236981
theorem B1988427 : Blo 1987435 1988427 := bstep (se 1 (by rfl) ⟨1491320, by rfl⟩ : syracuseStep 1988427 = 2982641) B2982641
theorem B2516609 : Blo 1987435 2516609 := bbase (se 2 (by rfl) ⟨943728, by rfl⟩ : syracuseStep 2516609 = 1887457) (by norm_num)
theorem B6710957 : Blo 1987435 6710957 := bstep (se 3 (by rfl) ⟨1258304, by rfl⟩ : syracuseStep 6710957 = 2516609) B2516609
theorem B4473971 : Blo 1987435 4473971 := bstep (se 1 (by rfl) ⟨3355478, by rfl⟩ : syracuseStep 4473971 = 6710957) B6710957
theorem B2982647 : Blo 1987435 2982647 := bstep (se 1 (by rfl) ⟨2236985, by rfl⟩ : syracuseStep 2982647 = 4473971) B4473971
theorem B1988431 : Blo 1987435 1988431 := bstep (se 1 (by rfl) ⟨1491323, by rfl⟩ : syracuseStep 1988431 = 2982647) B2982647
theorem B2982653 : Blo 1987435 2982653 := bbase (se 3 (by rfl) ⟨559247, by rfl⟩ : syracuseStep 2982653 = 1118495) (by norm_num)
theorem B1988435 : Blo 1987435 1988435 := bstep (se 1 (by rfl) ⟨1491326, by rfl⟩ : syracuseStep 1988435 = 2982653) B2982653
theorem B4473989 : Blo 1987435 4473989 := bbase (se 4 (by rfl) ⟨419436, by rfl⟩ : syracuseStep 4473989 = 838873) (by norm_num)
theorem B2982659 : Blo 1987435 2982659 := bstep (se 1 (by rfl) ⟨2236994, by rfl⟩ : syracuseStep 2982659 = 4473989) B4473989
theorem B1988439 : Blo 1987435 1988439 := bstep (se 1 (by rfl) ⟨1491329, by rfl⟩ : syracuseStep 1988439 = 2982659) B2982659
theorem B4246805 : Blo 1987435 4246805 := bbase (se 6 (by rfl) ⟨99534, by rfl⟩ : syracuseStep 4246805 = 199069) (by norm_num)
theorem B2831203 : Blo 1987435 2831203 := bstep (se 1 (by rfl) ⟨2123402, by rfl⟩ : syracuseStep 2831203 = 4246805) B4246805
theorem B3774937 : Blo 1987435 3774937 := bstep (se 2 (by rfl) ⟨1415601, by rfl⟩ : syracuseStep 3774937 = 2831203) B2831203
theorem B5033249 : Blo 1987435 5033249 := bstep (se 2 (by rfl) ⟨1887468, by rfl⟩ : syracuseStep 5033249 = 3774937) B3774937
theorem B3355499 : Blo 1987435 3355499 := bstep (se 1 (by rfl) ⟨2516624, by rfl⟩ : syracuseStep 3355499 = 5033249) B5033249
theorem B2236999 : Blo 1987435 2236999 := bstep (se 1 (by rfl) ⟨1677749, by rfl⟩ : syracuseStep 2236999 = 3355499) B3355499
theorem B2982665 : Blo 1987435 2982665 := bstep (se 2 (by rfl) ⟨1118499, by rfl⟩ : syracuseStep 2982665 = 2236999) B2236999
theorem B1988443 : Blo 1987435 1988443 := bstep (se 1 (by rfl) ⟨1491332, by rfl⟩ : syracuseStep 1988443 = 2982665) B2982665
theorem B10066517 : Blo 1987435 10066517 := bbase (se 8 (by rfl) ⟨58983, by rfl⟩ : syracuseStep 10066517 = 117967) (by norm_num)
theorem B6711011 : Blo 1987435 6711011 := bstep (se 1 (by rfl) ⟨5033258, by rfl⟩ : syracuseStep 6711011 = 10066517) B10066517
theorem B4474007 : Blo 1987435 4474007 := bstep (se 1 (by rfl) ⟨3355505, by rfl⟩ : syracuseStep 4474007 = 6711011) B6711011
theorem B2982671 : Blo 1987435 2982671 := bstep (se 1 (by rfl) ⟨2237003, by rfl⟩ : syracuseStep 2982671 = 4474007) B4474007
theorem B1988447 : Blo 1987435 1988447 := bstep (se 1 (by rfl) ⟨1491335, by rfl⟩ : syracuseStep 1988447 = 2982671) B2982671
theorem B2982677 : Blo 1987435 2982677 := bbase (se 6 (by rfl) ⟨69906, by rfl⟩ : syracuseStep 2982677 = 139813) (by norm_num)
theorem B1988451 : Blo 1987435 1988451 := bstep (se 1 (by rfl) ⟨1491338, by rfl⟩ : syracuseStep 1988451 = 2982677) B2982677
theorem B8172341 : Blo 1987435 8172341 := bbase (se 5 (by rfl) ⟨383078, by rfl⟩ : syracuseStep 8172341 = 766157) (by norm_num)
theorem B5448227 : Blo 1987435 5448227 := bstep (se 1 (by rfl) ⟨4086170, by rfl⟩ : syracuseStep 5448227 = 8172341) B8172341
theorem B58114421 : Blo 1987435 58114421 := bstep (se 5 (by rfl) ⟨2724113, by rfl⟩ : syracuseStep 58114421 = 5448227) B5448227
theorem B38742947 : Blo 1987435 38742947 := bstep (se 1 (by rfl) ⟨29057210, by rfl⟩ : syracuseStep 38742947 = 58114421) B58114421
theorem B25828631 : Blo 1987435 25828631 := bstep (se 1 (by rfl) ⟨19371473, by rfl⟩ : syracuseStep 25828631 = 38742947) B38742947
theorem B17219087 : Blo 1987435 17219087 := bstep (se 1 (by rfl) ⟨12914315, by rfl⟩ : syracuseStep 17219087 = 25828631) B25828631
theorem B11479391 : Blo 1987435 11479391 := bstep (se 1 (by rfl) ⟨8609543, by rfl⟩ : syracuseStep 11479391 = 17219087) B17219087
theorem B7652927 : Blo 1987435 7652927 := bstep (se 1 (by rfl) ⟨5739695, by rfl⟩ : syracuseStep 7652927 = 11479391) B11479391
theorem B5101951 : Blo 1987435 5101951 := bstep (se 1 (by rfl) ⟨3826463, by rfl⟩ : syracuseStep 5101951 = 7652927) B7652927
theorem B6802601 : Blo 1987435 6802601 := bstep (se 2 (by rfl) ⟨2550975, by rfl⟩ : syracuseStep 6802601 = 5101951) B5101951
theorem B18140269 : Blo 1987435 18140269 := bstep (se 3 (by rfl) ⟨3401300, by rfl⟩ : syracuseStep 18140269 = 6802601) B6802601
theorem B24187025 : Blo 1987435 24187025 := bstep (se 2 (by rfl) ⟨9070134, by rfl⟩ : syracuseStep 24187025 = 18140269) B18140269
theorem B16124683 : Blo 1987435 16124683 := bstep (se 1 (by rfl) ⟨12093512, by rfl⟩ : syracuseStep 16124683 = 24187025) B24187025
theorem B21499577 : Blo 1987435 21499577 := bstep (se 2 (by rfl) ⟨8062341, by rfl⟩ : syracuseStep 21499577 = 16124683) B16124683
theorem B14333051 : Blo 1987435 14333051 := bstep (se 1 (by rfl) ⟨10749788, by rfl⟩ : syracuseStep 14333051 = 21499577) B21499577
theorem B38221469 : Blo 1987435 38221469 := bstep (se 3 (by rfl) ⟨7166525, by rfl⟩ : syracuseStep 38221469 = 14333051) B14333051
theorem B25480979 : Blo 1987435 25480979 := bstep (se 1 (by rfl) ⟨19110734, by rfl⟩ : syracuseStep 25480979 = 38221469) B38221469
theorem B16987319 : Blo 1987435 16987319 := bstep (se 1 (by rfl) ⟨12740489, by rfl⟩ : syracuseStep 16987319 = 25480979) B25480979
theorem B11324879 : Blo 1987435 11324879 := bstep (se 1 (by rfl) ⟨8493659, by rfl⟩ : syracuseStep 11324879 = 16987319) B16987319
theorem B7549919 : Blo 1987435 7549919 := bstep (se 1 (by rfl) ⟨5662439, by rfl⟩ : syracuseStep 7549919 = 11324879) B11324879
theorem B5033279 : Blo 1987435 5033279 := bstep (se 1 (by rfl) ⟨3774959, by rfl⟩ : syracuseStep 5033279 = 7549919) B7549919
theorem B3355519 : Blo 1987435 3355519 := bstep (se 1 (by rfl) ⟨2516639, by rfl⟩ : syracuseStep 3355519 = 5033279) B5033279
theorem B4474025 : Blo 1987435 4474025 := bstep (se 2 (by rfl) ⟨1677759, by rfl⟩ : syracuseStep 4474025 = 3355519) B3355519
theorem B2982683 : Blo 1987435 2982683 := bstep (se 1 (by rfl) ⟨2237012, by rfl⟩ : syracuseStep 2982683 = 4474025) B4474025
theorem B1988455 : Blo 1987435 1988455 := bstep (se 1 (by rfl) ⟨1491341, by rfl⟩ : syracuseStep 1988455 = 2982683) B2982683
theorem B2237017 : Blo 1987435 2237017 := bbase (se 2 (by rfl) ⟨838881, by rfl⟩ : syracuseStep 2237017 = 1677763) (by norm_num)
theorem B2982689 : Blo 1987435 2982689 := bstep (se 2 (by rfl) ⟨1118508, by rfl⟩ : syracuseStep 2982689 = 2237017) B2237017
theorem B1988459 : Blo 1987435 1988459 := bstep (se 1 (by rfl) ⟨1491344, by rfl⟩ : syracuseStep 1988459 = 2982689) B2982689
theorem B2724125 : Blo 1987435 2724125 := bbase (se 3 (by rfl) ⟨510773, by rfl⟩ : syracuseStep 2724125 = 1021547) (by norm_num)
theorem B7264333 : Blo 1987435 7264333 := bstep (se 3 (by rfl) ⟨1362062, by rfl⟩ : syracuseStep 7264333 = 2724125) B2724125
theorem B9685777 : Blo 1987435 9685777 := bstep (se 2 (by rfl) ⟨3632166, by rfl⟩ : syracuseStep 9685777 = 7264333) B7264333
theorem B12914369 : Blo 1987435 12914369 := bstep (se 2 (by rfl) ⟨4842888, by rfl⟩ : syracuseStep 12914369 = 9685777) B9685777
theorem B8609579 : Blo 1987435 8609579 := bstep (se 1 (by rfl) ⟨6457184, by rfl⟩ : syracuseStep 8609579 = 12914369) B12914369
theorem B5739719 : Blo 1987435 5739719 := bstep (se 1 (by rfl) ⟨4304789, by rfl⟩ : syracuseStep 5739719 = 8609579) B8609579
theorem B15305917 : Blo 1987435 15305917 := bstep (se 3 (by rfl) ⟨2869859, by rfl⟩ : syracuseStep 15305917 = 5739719) B5739719
theorem B20407889 : Blo 1987435 20407889 := bstep (se 2 (by rfl) ⟨7652958, by rfl⟩ : syracuseStep 20407889 = 15305917) B15305917
theorem B13605259 : Blo 1987435 13605259 := bstep (se 1 (by rfl) ⟨10203944, by rfl⟩ : syracuseStep 13605259 = 20407889) B20407889
theorem B18140345 : Blo 1987435 18140345 := bstep (se 2 (by rfl) ⟨6802629, by rfl⟩ : syracuseStep 18140345 = 13605259) B13605259
theorem B12093563 : Blo 1987435 12093563 := bstep (se 1 (by rfl) ⟨9070172, by rfl⟩ : syracuseStep 12093563 = 18140345) B18140345
theorem B32249501 : Blo 1987435 32249501 := bstep (se 3 (by rfl) ⟨6046781, by rfl⟩ : syracuseStep 32249501 = 12093563) B12093563
theorem B21499667 : Blo 1987435 21499667 := bstep (se 1 (by rfl) ⟨16124750, by rfl⟩ : syracuseStep 21499667 = 32249501) B32249501
theorem B14333111 : Blo 1987435 14333111 := bstep (se 1 (by rfl) ⟨10749833, by rfl⟩ : syracuseStep 14333111 = 21499667) B21499667
theorem B9555407 : Blo 1987435 9555407 := bstep (se 1 (by rfl) ⟨7166555, by rfl⟩ : syracuseStep 9555407 = 14333111) B14333111
theorem B6370271 : Blo 1987435 6370271 := bstep (se 1 (by rfl) ⟨4777703, by rfl⟩ : syracuseStep 6370271 = 9555407) B9555407
theorem B4246847 : Blo 1987435 4246847 := bstep (se 1 (by rfl) ⟨3185135, by rfl⟩ : syracuseStep 4246847 = 6370271) B6370271
theorem B2831231 : Blo 1987435 2831231 := bstep (se 1 (by rfl) ⟨2123423, by rfl⟩ : syracuseStep 2831231 = 4246847) B4246847
theorem B7549949 : Blo 1987435 7549949 := bstep (se 3 (by rfl) ⟨1415615, by rfl⟩ : syracuseStep 7549949 = 2831231) B2831231
theorem B5033299 : Blo 1987435 5033299 := bstep (se 1 (by rfl) ⟨3774974, by rfl⟩ : syracuseStep 5033299 = 7549949) B7549949
theorem B6711065 : Blo 1987435 6711065 := bstep (se 2 (by rfl) ⟨2516649, by rfl⟩ : syracuseStep 6711065 = 5033299) B5033299
theorem B4474043 : Blo 1987435 4474043 := bstep (se 1 (by rfl) ⟨3355532, by rfl⟩ : syracuseStep 4474043 = 6711065) B6711065
theorem B2982695 : Blo 1987435 2982695 := bstep (se 1 (by rfl) ⟨2237021, by rfl⟩ : syracuseStep 2982695 = 4474043) B4474043
theorem B1988463 : Blo 1987435 1988463 := bstep (se 1 (by rfl) ⟨1491347, by rfl⟩ : syracuseStep 1988463 = 2982695) B2982695
theorem B2982701 : Blo 1987435 2982701 := bbase (se 3 (by rfl) ⟨559256, by rfl⟩ : syracuseStep 2982701 = 1118513) (by norm_num)
theorem B1988467 : Blo 1987435 1988467 := bstep (se 1 (by rfl) ⟨1491350, by rfl⟩ : syracuseStep 1988467 = 2982701) B2982701
theorem B4474061 : Blo 1987435 4474061 := bbase (se 3 (by rfl) ⟨838886, by rfl⟩ : syracuseStep 4474061 = 1677773) (by norm_num)
theorem B2982707 : Blo 1987435 2982707 := bstep (se 1 (by rfl) ⟨2237030, by rfl⟩ : syracuseStep 2982707 = 4474061) B4474061
theorem B1988471 : Blo 1987435 1988471 := bstep (se 1 (by rfl) ⟨1491353, by rfl⟩ : syracuseStep 1988471 = 2982707) B2982707
theorem B2516665 : Blo 1987435 2516665 := bbase (se 2 (by rfl) ⟨943749, by rfl⟩ : syracuseStep 2516665 = 1887499) (by norm_num)
theorem B3355553 : Blo 1987435 3355553 := bstep (se 2 (by rfl) ⟨1258332, by rfl⟩ : syracuseStep 3355553 = 2516665) B2516665
theorem B2237035 : Blo 1987435 2237035 := bstep (se 1 (by rfl) ⟨1677776, by rfl⟩ : syracuseStep 2237035 = 3355553) B3355553
theorem B2982713 : Blo 1987435 2982713 := bstep (se 2 (by rfl) ⟨1118517, by rfl⟩ : syracuseStep 2982713 = 2237035) B2237035
theorem B1988475 : Blo 1987435 1988475 := bstep (se 1 (by rfl) ⟨1491356, by rfl⟩ : syracuseStep 1988475 = 2982713) B2982713
theorem B4777741 : Blo 1987435 4777741 := bbase (se 3 (by rfl) ⟨895826, by rfl⟩ : syracuseStep 4777741 = 1791653) (by norm_num)
theorem B6370321 : Blo 1987435 6370321 := bstep (se 2 (by rfl) ⟨2388870, by rfl⟩ : syracuseStep 6370321 = 4777741) B4777741
theorem B8493761 : Blo 1987435 8493761 := bstep (se 2 (by rfl) ⟨3185160, by rfl⟩ : syracuseStep 8493761 = 6370321) B6370321
theorem B22650029 : Blo 1987435 22650029 := bstep (se 3 (by rfl) ⟨4246880, by rfl⟩ : syracuseStep 22650029 = 8493761) B8493761
theorem B15100019 : Blo 1987435 15100019 := bstep (se 1 (by rfl) ⟨11325014, by rfl⟩ : syracuseStep 15100019 = 22650029) B22650029
theorem B10066679 : Blo 1987435 10066679 := bstep (se 1 (by rfl) ⟨7550009, by rfl⟩ : syracuseStep 10066679 = 15100019) B15100019
theorem B6711119 : Blo 1987435 6711119 := bstep (se 1 (by rfl) ⟨5033339, by rfl⟩ : syracuseStep 6711119 = 10066679) B10066679
theorem B4474079 : Blo 1987435 4474079 := bstep (se 1 (by rfl) ⟨3355559, by rfl⟩ : syracuseStep 4474079 = 6711119) B6711119
theorem B2982719 : Blo 1987435 2982719 := bstep (se 1 (by rfl) ⟨2237039, by rfl⟩ : syracuseStep 2982719 = 4474079) B4474079
theorem B1988479 : Blo 1987435 1988479 := bstep (se 1 (by rfl) ⟨1491359, by rfl⟩ : syracuseStep 1988479 = 2982719) B2982719
theorem B2982725 : Blo 1987435 2982725 := bbase (se 4 (by rfl) ⟨279630, by rfl⟩ : syracuseStep 2982725 = 559261) (by norm_num)
theorem B1988483 : Blo 1987435 1988483 := bstep (se 1 (by rfl) ⟨1491362, by rfl⟩ : syracuseStep 1988483 = 2982725) B2982725
theorem B3355573 : Blo 1987435 3355573 := bbase (se 5 (by rfl) ⟨157292, by rfl⟩ : syracuseStep 3355573 = 314585) (by norm_num)
theorem B4474097 : Blo 1987435 4474097 := bstep (se 2 (by rfl) ⟨1677786, by rfl⟩ : syracuseStep 4474097 = 3355573) B3355573
theorem B2982731 : Blo 1987435 2982731 := bstep (se 1 (by rfl) ⟨2237048, by rfl⟩ : syracuseStep 2982731 = 4474097) B4474097
theorem B1988487 : Blo 1987435 1988487 := bstep (se 1 (by rfl) ⟨1491365, by rfl⟩ : syracuseStep 1988487 = 2982731) B2982731
theorem B2237053 : Blo 1987435 2237053 := bbase (se 3 (by rfl) ⟨419447, by rfl⟩ : syracuseStep 2237053 = 838895) (by norm_num)
theorem B2982737 : Blo 1987435 2982737 := bstep (se 2 (by rfl) ⟨1118526, by rfl⟩ : syracuseStep 2982737 = 2237053) B2237053
theorem B1988491 : Blo 1987435 1988491 := bstep (se 1 (by rfl) ⟨1491368, by rfl⟩ : syracuseStep 1988491 = 2982737) B2982737
theorem B6711173 : Blo 1987435 6711173 := bbase (se 4 (by rfl) ⟨629172, by rfl⟩ : syracuseStep 6711173 = 1258345) (by norm_num)
theorem B4474115 : Blo 1987435 4474115 := bstep (se 1 (by rfl) ⟨3355586, by rfl⟩ : syracuseStep 4474115 = 6711173) B6711173
theorem B2982743 : Blo 1987435 2982743 := bstep (se 1 (by rfl) ⟨2237057, by rfl⟩ : syracuseStep 2982743 = 4474115) B4474115
theorem B1988495 : Blo 1987435 1988495 := bstep (se 1 (by rfl) ⟨1491371, by rfl⟩ : syracuseStep 1988495 = 2982743) B2982743
theorem B2982749 : Blo 1987435 2982749 := bbase (se 3 (by rfl) ⟨559265, by rfl⟩ : syracuseStep 2982749 = 1118531) (by norm_num)
theorem B1988499 : Blo 1987435 1988499 := bstep (se 1 (by rfl) ⟨1491374, by rfl⟩ : syracuseStep 1988499 = 2982749) B2982749
theorem B4474133 : Blo 1987435 4474133 := bbase (se 6 (by rfl) ⟨104862, by rfl⟩ : syracuseStep 4474133 = 209725) (by norm_num)
theorem B2982755 : Blo 1987435 2982755 := bstep (se 1 (by rfl) ⟨2237066, by rfl⟩ : syracuseStep 2982755 = 4474133) B4474133
theorem B1988503 : Blo 1987435 1988503 := bstep (se 1 (by rfl) ⟨1491377, by rfl⟩ : syracuseStep 1988503 = 2982755) B2982755
theorem B7550117 : Blo 1987435 7550117 := bbase (se 4 (by rfl) ⟨707823, by rfl⟩ : syracuseStep 7550117 = 1415647) (by norm_num)
theorem B5033411 : Blo 1987435 5033411 := bstep (se 1 (by rfl) ⟨3775058, by rfl⟩ : syracuseStep 5033411 = 7550117) B7550117
theorem B3355607 : Blo 1987435 3355607 := bstep (se 1 (by rfl) ⟨2516705, by rfl⟩ : syracuseStep 3355607 = 5033411) B5033411
theorem B2237071 : Blo 1987435 2237071 := bstep (se 1 (by rfl) ⟨1677803, by rfl⟩ : syracuseStep 2237071 = 3355607) B3355607
theorem B2982761 : Blo 1987435 2982761 := bstep (se 2 (by rfl) ⟨1118535, by rfl⟩ : syracuseStep 2982761 = 2237071) B2237071
theorem B1988507 : Blo 1987435 1988507 := bstep (se 1 (by rfl) ⟨1491380, by rfl⟩ : syracuseStep 1988507 = 2982761) B2982761
theorem B4246949 : Blo 1987435 4246949 := bbase (se 4 (by rfl) ⟨398151, by rfl⟩ : syracuseStep 4246949 = 796303) (by norm_num)
theorem B11325197 : Blo 1987435 11325197 := bstep (se 3 (by rfl) ⟨2123474, by rfl⟩ : syracuseStep 11325197 = 4246949) B4246949
theorem B7550131 : Blo 1987435 7550131 := bstep (se 1 (by rfl) ⟨5662598, by rfl⟩ : syracuseStep 7550131 = 11325197) B11325197
theorem B10066841 : Blo 1987435 10066841 := bstep (se 2 (by rfl) ⟨3775065, by rfl⟩ : syracuseStep 10066841 = 7550131) B7550131
theorem B6711227 : Blo 1987435 6711227 := bstep (se 1 (by rfl) ⟨5033420, by rfl⟩ : syracuseStep 6711227 = 10066841) B10066841
theorem B4474151 : Blo 1987435 4474151 := bstep (se 1 (by rfl) ⟨3355613, by rfl⟩ : syracuseStep 4474151 = 6711227) B6711227
theorem B2982767 : Blo 1987435 2982767 := bstep (se 1 (by rfl) ⟨2237075, by rfl⟩ : syracuseStep 2982767 = 4474151) B4474151
theorem B1988511 : Blo 1987435 1988511 := bstep (se 1 (by rfl) ⟨1491383, by rfl⟩ : syracuseStep 1988511 = 2982767) B2982767
theorem B2982773 : Blo 1987435 2982773 := bbase (se 5 (by rfl) ⟨139817, by rfl⟩ : syracuseStep 2982773 = 279635) (by norm_num)
theorem B1988515 : Blo 1987435 1988515 := bstep (se 1 (by rfl) ⟨1491386, by rfl⟩ : syracuseStep 1988515 = 2982773) B2982773
theorem B3023477 : Blo 1987435 3023477 := bbase (se 5 (by rfl) ⟨141725, by rfl⟩ : syracuseStep 3023477 = 283451) (by norm_num)
theorem B2015651 : Blo 1987435 2015651 := bstep (se 1 (by rfl) ⟨1511738, by rfl⟩ : syracuseStep 2015651 = 3023477) B3023477
theorem B5375069 : Blo 1987435 5375069 := bstep (se 3 (by rfl) ⟨1007825, by rfl⟩ : syracuseStep 5375069 = 2015651) B2015651
theorem B3583379 : Blo 1987435 3583379 := bstep (se 1 (by rfl) ⟨2687534, by rfl⟩ : syracuseStep 3583379 = 5375069) B5375069
theorem B9555677 : Blo 1987435 9555677 := bstep (se 3 (by rfl) ⟨1791689, by rfl⟩ : syracuseStep 9555677 = 3583379) B3583379
theorem B6370451 : Blo 1987435 6370451 := bstep (se 1 (by rfl) ⟨4777838, by rfl⟩ : syracuseStep 6370451 = 9555677) B9555677
theorem B4246967 : Blo 1987435 4246967 := bstep (se 1 (by rfl) ⟨3185225, by rfl⟩ : syracuseStep 4246967 = 6370451) B6370451
theorem B2831311 : Blo 1987435 2831311 := bstep (se 1 (by rfl) ⟨2123483, by rfl⟩ : syracuseStep 2831311 = 4246967) B4246967
theorem B3775081 : Blo 1987435 3775081 := bstep (se 2 (by rfl) ⟨1415655, by rfl⟩ : syracuseStep 3775081 = 2831311) B2831311
theorem B5033441 : Blo 1987435 5033441 := bstep (se 2 (by rfl) ⟨1887540, by rfl⟩ : syracuseStep 5033441 = 3775081) B3775081
theorem B3355627 : Blo 1987435 3355627 := bstep (se 1 (by rfl) ⟨2516720, by rfl⟩ : syracuseStep 3355627 = 5033441) B5033441
theorem B4474169 : Blo 1987435 4474169 := bstep (se 2 (by rfl) ⟨1677813, by rfl⟩ : syracuseStep 4474169 = 3355627) B3355627
theorem B2982779 : Blo 1987435 2982779 := bstep (se 1 (by rfl) ⟨2237084, by rfl⟩ : syracuseStep 2982779 = 4474169) B4474169
theorem B1988519 : Blo 1987435 1988519 := bstep (se 1 (by rfl) ⟨1491389, by rfl⟩ : syracuseStep 1988519 = 2982779) B2982779
theorem B2237089 : Blo 1987435 2237089 := bbase (se 2 (by rfl) ⟨838908, by rfl⟩ : syracuseStep 2237089 = 1677817) (by norm_num)
theorem B2982785 : Blo 1987435 2982785 := bstep (se 2 (by rfl) ⟨1118544, by rfl⟩ : syracuseStep 2982785 = 2237089) B2237089
theorem B1988523 : Blo 1987435 1988523 := bstep (se 1 (by rfl) ⟨1491392, by rfl⟩ : syracuseStep 1988523 = 2982785) B2982785
theorem B5033461 : Blo 1987435 5033461 := bbase (se 5 (by rfl) ⟨235943, by rfl⟩ : syracuseStep 5033461 = 471887) (by norm_num)
theorem B6711281 : Blo 1987435 6711281 := bstep (se 2 (by rfl) ⟨2516730, by rfl⟩ : syracuseStep 6711281 = 5033461) B5033461
theorem B4474187 : Blo 1987435 4474187 := bstep (se 1 (by rfl) ⟨3355640, by rfl⟩ : syracuseStep 4474187 = 6711281) B6711281
theorem B2982791 : Blo 1987435 2982791 := bstep (se 1 (by rfl) ⟨2237093, by rfl⟩ : syracuseStep 2982791 = 4474187) B4474187
theorem B1988527 : Blo 1987435 1988527 := bstep (se 1 (by rfl) ⟨1491395, by rfl⟩ : syracuseStep 1988527 = 2982791) B2982791
theorem B2982797 : Blo 1987435 2982797 := bbase (se 3 (by rfl) ⟨559274, by rfl⟩ : syracuseStep 2982797 = 1118549) (by norm_num)
theorem B1988531 : Blo 1987435 1988531 := bstep (se 1 (by rfl) ⟨1491398, by rfl⟩ : syracuseStep 1988531 = 2982797) B2982797
theorem B4474205 : Blo 1987435 4474205 := bbase (se 3 (by rfl) ⟨838913, by rfl⟩ : syracuseStep 4474205 = 1677827) (by norm_num)
theorem B2982803 : Blo 1987435 2982803 := bstep (se 1 (by rfl) ⟨2237102, by rfl⟩ : syracuseStep 2982803 = 4474205) B4474205
theorem B1988535 : Blo 1987435 1988535 := bstep (se 1 (by rfl) ⟨1491401, by rfl⟩ : syracuseStep 1988535 = 2982803) B2982803
theorem B3355661 : Blo 1987435 3355661 := bbase (se 3 (by rfl) ⟨629186, by rfl⟩ : syracuseStep 3355661 = 1258373) (by norm_num)
theorem B2237107 : Blo 1987435 2237107 := bstep (se 1 (by rfl) ⟨1677830, by rfl⟩ : syracuseStep 2237107 = 3355661) B3355661
theorem B2982809 : Blo 1987435 2982809 := bstep (se 2 (by rfl) ⟨1118553, by rfl⟩ : syracuseStep 2982809 = 2237107) B2237107
theorem B1988539 : Blo 1987435 1988539 := bstep (se 1 (by rfl) ⟨1491404, by rfl⟩ : syracuseStep 1988539 = 2982809) B2982809
theorem B6457445 : Blo 1987435 6457445 := bbase (se 4 (by rfl) ⟨605385, by rfl⟩ : syracuseStep 6457445 = 1210771) (by norm_num)
theorem B4304963 : Blo 1987435 4304963 := bstep (se 1 (by rfl) ⟨3228722, by rfl⟩ : syracuseStep 4304963 = 6457445) B6457445
theorem B2869975 : Blo 1987435 2869975 := bstep (se 1 (by rfl) ⟨2152481, by rfl⟩ : syracuseStep 2869975 = 4304963) B4304963
theorem B15306533 : Blo 1987435 15306533 := bstep (se 4 (by rfl) ⟨1434987, by rfl⟩ : syracuseStep 15306533 = 2869975) B2869975
theorem B10204355 : Blo 1987435 10204355 := bstep (se 1 (by rfl) ⟨7653266, by rfl⟩ : syracuseStep 10204355 = 15306533) B15306533
theorem B6802903 : Blo 1987435 6802903 := bstep (se 1 (by rfl) ⟨5102177, by rfl⟩ : syracuseStep 6802903 = 10204355) B10204355
theorem B9070537 : Blo 1987435 9070537 := bstep (se 2 (by rfl) ⟨3401451, by rfl⟩ : syracuseStep 9070537 = 6802903) B6802903
theorem B12094049 : Blo 1987435 12094049 := bstep (se 2 (by rfl) ⟨4535268, by rfl⟩ : syracuseStep 12094049 = 9070537) B9070537
theorem B8062699 : Blo 1987435 8062699 := bstep (se 1 (by rfl) ⟨6047024, by rfl⟩ : syracuseStep 8062699 = 12094049) B12094049
theorem B10750265 : Blo 1987435 10750265 := bstep (se 2 (by rfl) ⟨4031349, by rfl⟩ : syracuseStep 10750265 = 8062699) B8062699
theorem B7166843 : Blo 1987435 7166843 := bstep (se 1 (by rfl) ⟨5375132, by rfl⟩ : syracuseStep 7166843 = 10750265) B10750265
theorem B4777895 : Blo 1987435 4777895 := bstep (se 1 (by rfl) ⟨3583421, by rfl⟩ : syracuseStep 4777895 = 7166843) B7166843
theorem B3185263 : Blo 1987435 3185263 := bstep (se 1 (by rfl) ⟨2388947, by rfl⟩ : syracuseStep 3185263 = 4777895) B4777895
theorem B16988069 : Blo 1987435 16988069 := bstep (se 4 (by rfl) ⟨1592631, by rfl⟩ : syracuseStep 16988069 = 3185263) B3185263
theorem B11325379 : Blo 1987435 11325379 := bstep (se 1 (by rfl) ⟨8494034, by rfl⟩ : syracuseStep 11325379 = 16988069) B16988069
theorem B15100505 : Blo 1987435 15100505 := bstep (se 2 (by rfl) ⟨5662689, by rfl⟩ : syracuseStep 15100505 = 11325379) B11325379
theorem B10067003 : Blo 1987435 10067003 := bstep (se 1 (by rfl) ⟨7550252, by rfl⟩ : syracuseStep 10067003 = 15100505) B15100505
theorem B6711335 : Blo 1987435 6711335 := bstep (se 1 (by rfl) ⟨5033501, by rfl⟩ : syracuseStep 6711335 = 10067003) B10067003
theorem B4474223 : Blo 1987435 4474223 := bstep (se 1 (by rfl) ⟨3355667, by rfl⟩ : syracuseStep 4474223 = 6711335) B6711335
theorem B2982815 : Blo 1987435 2982815 := bstep (se 1 (by rfl) ⟨2237111, by rfl⟩ : syracuseStep 2982815 = 4474223) B4474223
theorem B1988543 : Blo 1987435 1988543 := bstep (se 1 (by rfl) ⟨1491407, by rfl⟩ : syracuseStep 1988543 = 2982815) B2982815
theorem B2982821 : Blo 1987435 2982821 := bbase (se 4 (by rfl) ⟨279639, by rfl⟩ : syracuseStep 2982821 = 559279) (by norm_num)
theorem B1988547 : Blo 1987435 1988547 := bstep (se 1 (by rfl) ⟨1491410, by rfl⟩ : syracuseStep 1988547 = 2982821) B2982821
theorem B2516761 : Blo 1987435 2516761 := bbase (se 2 (by rfl) ⟨943785, by rfl⟩ : syracuseStep 2516761 = 1887571) (by norm_num)
theorem B3355681 : Blo 1987435 3355681 := bstep (se 2 (by rfl) ⟨1258380, by rfl⟩ : syracuseStep 3355681 = 2516761) B2516761
theorem B4474241 : Blo 1987435 4474241 := bstep (se 2 (by rfl) ⟨1677840, by rfl⟩ : syracuseStep 4474241 = 3355681) B3355681
theorem B2982827 : Blo 1987435 2982827 := bstep (se 1 (by rfl) ⟨2237120, by rfl⟩ : syracuseStep 2982827 = 4474241) B4474241
theorem B1988551 : Blo 1987435 1988551 := bstep (se 1 (by rfl) ⟨1491413, by rfl⟩ : syracuseStep 1988551 = 2982827) B2982827
theorem B2237125 : Blo 1987435 2237125 := bbase (se 4 (by rfl) ⟨209730, by rfl⟩ : syracuseStep 2237125 = 419461) (by norm_num)
theorem B2982833 : Blo 1987435 2982833 := bstep (se 2 (by rfl) ⟨1118562, by rfl⟩ : syracuseStep 2982833 = 2237125) B2237125
theorem B1988555 : Blo 1987435 1988555 := bstep (se 1 (by rfl) ⟨1491416, by rfl⟩ : syracuseStep 1988555 = 2982833) B2982833
theorem B3775157 : Blo 1987435 3775157 := bbase (se 5 (by rfl) ⟨176960, by rfl⟩ : syracuseStep 3775157 = 353921) (by norm_num)
theorem B2516771 : Blo 1987435 2516771 := bstep (se 1 (by rfl) ⟨1887578, by rfl⟩ : syracuseStep 2516771 = 3775157) B3775157
theorem B6711389 : Blo 1987435 6711389 := bstep (se 3 (by rfl) ⟨1258385, by rfl⟩ : syracuseStep 6711389 = 2516771) B2516771
theorem B4474259 : Blo 1987435 4474259 := bstep (se 1 (by rfl) ⟨3355694, by rfl⟩ : syracuseStep 4474259 = 6711389) B6711389
theorem B2982839 : Blo 1987435 2982839 := bstep (se 1 (by rfl) ⟨2237129, by rfl⟩ : syracuseStep 2982839 = 4474259) B4474259
theorem B1988559 : Blo 1987435 1988559 := bstep (se 1 (by rfl) ⟨1491419, by rfl⟩ : syracuseStep 1988559 = 2982839) B2982839
theorem B2982845 : Blo 1987435 2982845 := bbase (se 3 (by rfl) ⟨559283, by rfl⟩ : syracuseStep 2982845 = 1118567) (by norm_num)
theorem B1988563 : Blo 1987435 1988563 := bstep (se 1 (by rfl) ⟨1491422, by rfl⟩ : syracuseStep 1988563 = 2982845) B2982845
theorem B4474277 : Blo 1987435 4474277 := bbase (se 4 (by rfl) ⟨419463, by rfl⟩ : syracuseStep 4474277 = 838927) (by norm_num)
theorem B2982851 : Blo 1987435 2982851 := bstep (se 1 (by rfl) ⟨2237138, by rfl⟩ : syracuseStep 2982851 = 4474277) B4474277
theorem B1988567 : Blo 1987435 1988567 := bstep (se 1 (by rfl) ⟨1491425, by rfl⟩ : syracuseStep 1988567 = 2982851) B2982851
theorem B5033573 : Blo 1987435 5033573 := bbase (se 4 (by rfl) ⟨471897, by rfl⟩ : syracuseStep 5033573 = 943795) (by norm_num)
theorem B3355715 : Blo 1987435 3355715 := bstep (se 1 (by rfl) ⟨2516786, by rfl⟩ : syracuseStep 3355715 = 5033573) B5033573
theorem B2237143 : Blo 1987435 2237143 := bstep (se 1 (by rfl) ⟨1677857, by rfl⟩ : syracuseStep 2237143 = 3355715) B3355715
theorem B2982857 : Blo 1987435 2982857 := bstep (se 2 (by rfl) ⟨1118571, by rfl⟩ : syracuseStep 2982857 = 2237143) B2237143
theorem B1988571 : Blo 1987435 1988571 := bstep (se 1 (by rfl) ⟨1491428, by rfl⟩ : syracuseStep 1988571 = 2982857) B2982857
theorem B4777973 : Blo 1987435 4777973 := bbase (se 5 (by rfl) ⟨223967, by rfl⟩ : syracuseStep 4777973 = 447935) (by norm_num)
theorem B3185315 : Blo 1987435 3185315 := bstep (se 1 (by rfl) ⟨2388986, by rfl⟩ : syracuseStep 3185315 = 4777973) B4777973
theorem B2123543 : Blo 1987435 2123543 := bstep (se 1 (by rfl) ⟨1592657, by rfl⟩ : syracuseStep 2123543 = 3185315) B3185315
theorem B5662781 : Blo 1987435 5662781 := bstep (se 3 (by rfl) ⟨1061771, by rfl⟩ : syracuseStep 5662781 = 2123543) B2123543
theorem B3775187 : Blo 1987435 3775187 := bstep (se 1 (by rfl) ⟨2831390, by rfl⟩ : syracuseStep 3775187 = 5662781) B5662781
theorem B10067165 : Blo 1987435 10067165 := bstep (se 3 (by rfl) ⟨1887593, by rfl⟩ : syracuseStep 10067165 = 3775187) B3775187
theorem B6711443 : Blo 1987435 6711443 := bstep (se 1 (by rfl) ⟨5033582, by rfl⟩ : syracuseStep 6711443 = 10067165) B10067165
theorem B4474295 : Blo 1987435 4474295 := bstep (se 1 (by rfl) ⟨3355721, by rfl⟩ : syracuseStep 4474295 = 6711443) B6711443
theorem B2982863 : Blo 1987435 2982863 := bstep (se 1 (by rfl) ⟨2237147, by rfl⟩ : syracuseStep 2982863 = 4474295) B4474295
theorem B1988575 : Blo 1987435 1988575 := bstep (se 1 (by rfl) ⟨1491431, by rfl⟩ : syracuseStep 1988575 = 2982863) B2982863
theorem B2982869 : Blo 1987435 2982869 := bbase (se 7 (by rfl) ⟨34955, by rfl⟩ : syracuseStep 2982869 = 69911) (by norm_num)
theorem B1988579 : Blo 1987435 1988579 := bstep (se 1 (by rfl) ⟨1491434, by rfl⟩ : syracuseStep 1988579 = 2982869) B2982869
theorem B7550405 : Blo 1987435 7550405 := bbase (se 4 (by rfl) ⟨707850, by rfl⟩ : syracuseStep 7550405 = 1415701) (by norm_num)
theorem B5033603 : Blo 1987435 5033603 := bstep (se 1 (by rfl) ⟨3775202, by rfl⟩ : syracuseStep 5033603 = 7550405) B7550405
theorem B3355735 : Blo 1987435 3355735 := bstep (se 1 (by rfl) ⟨2516801, by rfl⟩ : syracuseStep 3355735 = 5033603) B5033603
theorem B4474313 : Blo 1987435 4474313 := bstep (se 2 (by rfl) ⟨1677867, by rfl⟩ : syracuseStep 4474313 = 3355735) B3355735
theorem B2982875 : Blo 1987435 2982875 := bstep (se 1 (by rfl) ⟨2237156, by rfl⟩ : syracuseStep 2982875 = 4474313) B4474313
theorem B1988583 : Blo 1987435 1988583 := bstep (se 1 (by rfl) ⟨1491437, by rfl⟩ : syracuseStep 1988583 = 2982875) B2982875
theorem B2237161 : Blo 1987435 2237161 := bbase (se 2 (by rfl) ⟨838935, by rfl⟩ : syracuseStep 2237161 = 1677871) (by norm_num)
theorem B2982881 : Blo 1987435 2982881 := bstep (se 2 (by rfl) ⟨1118580, by rfl⟩ : syracuseStep 2982881 = 2237161) B2237161
theorem B1988587 : Blo 1987435 1988587 := bstep (se 1 (by rfl) ⟨1491440, by rfl⟩ : syracuseStep 1988587 = 2982881) B2982881
theorem B11325653 : Blo 1987435 11325653 := bbase (se 7 (by rfl) ⟨132722, by rfl⟩ : syracuseStep 11325653 = 265445) (by norm_num)
theorem B7550435 : Blo 1987435 7550435 := bstep (se 1 (by rfl) ⟨5662826, by rfl⟩ : syracuseStep 7550435 = 11325653) B11325653
theorem B5033623 : Blo 1987435 5033623 := bstep (se 1 (by rfl) ⟨3775217, by rfl⟩ : syracuseStep 5033623 = 7550435) B7550435
theorem B6711497 : Blo 1987435 6711497 := bstep (se 2 (by rfl) ⟨2516811, by rfl⟩ : syracuseStep 6711497 = 5033623) B5033623
theorem B4474331 : Blo 1987435 4474331 := bstep (se 1 (by rfl) ⟨3355748, by rfl⟩ : syracuseStep 4474331 = 6711497) B6711497
theorem B2982887 : Blo 1987435 2982887 := bstep (se 1 (by rfl) ⟨2237165, by rfl⟩ : syracuseStep 2982887 = 4474331) B4474331
theorem B1988591 : Blo 1987435 1988591 := bstep (se 1 (by rfl) ⟨1491443, by rfl⟩ : syracuseStep 1988591 = 2982887) B2982887
theorem B2982893 : Blo 1987435 2982893 := bbase (se 3 (by rfl) ⟨559292, by rfl⟩ : syracuseStep 2982893 = 1118585) (by norm_num)
theorem B1988595 : Blo 1987435 1988595 := bstep (se 1 (by rfl) ⟨1491446, by rfl⟩ : syracuseStep 1988595 = 2982893) B2982893
theorem B4474349 : Blo 1987435 4474349 := bbase (se 3 (by rfl) ⟨838940, by rfl⟩ : syracuseStep 4474349 = 1677881) (by norm_num)
theorem B2982899 : Blo 1987435 2982899 := bstep (se 1 (by rfl) ⟨2237174, by rfl⟩ : syracuseStep 2982899 = 4474349) B4474349
theorem B1988599 : Blo 1987435 1988599 := bstep (se 1 (by rfl) ⟨1491449, by rfl⟩ : syracuseStep 1988599 = 2982899) B2982899
theorem B3023605 : Blo 1987435 3023605 := bbase (se 5 (by rfl) ⟨141731, by rfl⟩ : syracuseStep 3023605 = 283463) (by norm_num)
theorem B4031473 : Blo 1987435 4031473 := bstep (se 2 (by rfl) ⟨1511802, by rfl⟩ : syracuseStep 4031473 = 3023605) B3023605
theorem B5375297 : Blo 1987435 5375297 := bstep (se 2 (by rfl) ⟨2015736, by rfl⟩ : syracuseStep 5375297 = 4031473) B4031473
theorem B3583531 : Blo 1987435 3583531 := bstep (se 1 (by rfl) ⟨2687648, by rfl⟩ : syracuseStep 3583531 = 5375297) B5375297
theorem B4778041 : Blo 1987435 4778041 := bstep (se 2 (by rfl) ⟨1791765, by rfl⟩ : syracuseStep 4778041 = 3583531) B3583531
theorem B6370721 : Blo 1987435 6370721 := bstep (se 2 (by rfl) ⟨2389020, by rfl⟩ : syracuseStep 6370721 = 4778041) B4778041
theorem B4247147 : Blo 1987435 4247147 := bstep (se 1 (by rfl) ⟨3185360, by rfl⟩ : syracuseStep 4247147 = 6370721) B6370721
theorem B2831431 : Blo 1987435 2831431 := bstep (se 1 (by rfl) ⟨2123573, by rfl⟩ : syracuseStep 2831431 = 4247147) B4247147
theorem B3775241 : Blo 1987435 3775241 := bstep (se 2 (by rfl) ⟨1415715, by rfl⟩ : syracuseStep 3775241 = 2831431) B2831431
theorem B2516827 : Blo 1987435 2516827 := bstep (se 1 (by rfl) ⟨1887620, by rfl⟩ : syracuseStep 2516827 = 3775241) B3775241
theorem B3355769 : Blo 1987435 3355769 := bstep (se 2 (by rfl) ⟨1258413, by rfl⟩ : syracuseStep 3355769 = 2516827) B2516827
theorem B2237179 : Blo 1987435 2237179 := bstep (se 1 (by rfl) ⟨1677884, by rfl⟩ : syracuseStep 2237179 = 3355769) B3355769
theorem B2982905 : Blo 1987435 2982905 := bstep (se 2 (by rfl) ⟨1118589, by rfl⟩ : syracuseStep 2982905 = 2237179) B2237179
theorem B1988603 : Blo 1987435 1988603 := bstep (se 1 (by rfl) ⟨1491452, by rfl⟩ : syracuseStep 1988603 = 2982905) B2982905
theorem B18141653 : Blo 1987435 18141653 := bbase (se 7 (by rfl) ⟨212597, by rfl⟩ : syracuseStep 18141653 = 425195) (by norm_num)
theorem B12094435 : Blo 1987435 12094435 := bstep (se 1 (by rfl) ⟨9070826, by rfl⟩ : syracuseStep 12094435 = 18141653) B18141653
theorem B16125913 : Blo 1987435 16125913 := bstep (se 2 (by rfl) ⟨6047217, by rfl⟩ : syracuseStep 16125913 = 12094435) B12094435
theorem B21501217 : Blo 1987435 21501217 := bstep (se 2 (by rfl) ⟨8062956, by rfl⟩ : syracuseStep 21501217 = 16125913) B16125913
theorem B114673157 : Blo 1987435 114673157 := bstep (se 4 (by rfl) ⟨10750608, by rfl⟩ : syracuseStep 114673157 = 21501217) B21501217
theorem B76448771 : Blo 1987435 76448771 := bstep (se 1 (by rfl) ⟨57336578, by rfl⟩ : syracuseStep 76448771 = 114673157) B114673157
theorem B50965847 : Blo 1987435 50965847 := bstep (se 1 (by rfl) ⟨38224385, by rfl⟩ : syracuseStep 50965847 = 76448771) B76448771
theorem B33977231 : Blo 1987435 33977231 := bstep (se 1 (by rfl) ⟨25482923, by rfl⟩ : syracuseStep 33977231 = 50965847) B50965847
theorem B22651487 : Blo 1987435 22651487 := bstep (se 1 (by rfl) ⟨16988615, by rfl⟩ : syracuseStep 22651487 = 33977231) B33977231
theorem B15100991 : Blo 1987435 15100991 := bstep (se 1 (by rfl) ⟨11325743, by rfl⟩ : syracuseStep 15100991 = 22651487) B22651487
theorem B10067327 : Blo 1987435 10067327 := bstep (se 1 (by rfl) ⟨7550495, by rfl⟩ : syracuseStep 10067327 = 15100991) B15100991
theorem B6711551 : Blo 1987435 6711551 := bstep (se 1 (by rfl) ⟨5033663, by rfl⟩ : syracuseStep 6711551 = 10067327) B10067327
theorem B4474367 : Blo 1987435 4474367 := bstep (se 1 (by rfl) ⟨3355775, by rfl⟩ : syracuseStep 4474367 = 6711551) B6711551
theorem B2982911 : Blo 1987435 2982911 := bstep (se 1 (by rfl) ⟨2237183, by rfl⟩ : syracuseStep 2982911 = 4474367) B4474367
theorem B1988607 : Blo 1987435 1988607 := bstep (se 1 (by rfl) ⟨1491455, by rfl⟩ : syracuseStep 1988607 = 2982911) B2982911
theorem B2982917 : Blo 1987435 2982917 := bbase (se 4 (by rfl) ⟨279648, by rfl⟩ : syracuseStep 2982917 = 559297) (by norm_num)
theorem B1988611 : Blo 1987435 1988611 := bstep (se 1 (by rfl) ⟨1491458, by rfl⟩ : syracuseStep 1988611 = 2982917) B2982917
theorem B3355789 : Blo 1987435 3355789 := bbase (se 3 (by rfl) ⟨629210, by rfl⟩ : syracuseStep 3355789 = 1258421) (by norm_num)
theorem B4474385 : Blo 1987435 4474385 := bstep (se 2 (by rfl) ⟨1677894, by rfl⟩ : syracuseStep 4474385 = 3355789) B3355789
theorem B2982923 : Blo 1987435 2982923 := bstep (se 1 (by rfl) ⟨2237192, by rfl⟩ : syracuseStep 2982923 = 4474385) B4474385
theorem B1988615 : Blo 1987435 1988615 := bstep (se 1 (by rfl) ⟨1491461, by rfl⟩ : syracuseStep 1988615 = 2982923) B2982923
theorem B2237197 : Blo 1987435 2237197 := bbase (se 3 (by rfl) ⟨419474, by rfl⟩ : syracuseStep 2237197 = 838949) (by norm_num)
theorem B2982929 : Blo 1987435 2982929 := bstep (se 2 (by rfl) ⟨1118598, by rfl⟩ : syracuseStep 2982929 = 2237197) B2237197
theorem B1988619 : Blo 1987435 1988619 := bstep (se 1 (by rfl) ⟨1491464, by rfl⟩ : syracuseStep 1988619 = 2982929) B2982929
theorem B6711605 : Blo 1987435 6711605 := bbase (se 5 (by rfl) ⟨314606, by rfl⟩ : syracuseStep 6711605 = 629213) (by norm_num)
theorem B4474403 : Blo 1987435 4474403 := bstep (se 1 (by rfl) ⟨3355802, by rfl⟩ : syracuseStep 4474403 = 6711605) B6711605
theorem B2982935 : Blo 1987435 2982935 := bstep (se 1 (by rfl) ⟨2237201, by rfl⟩ : syracuseStep 2982935 = 4474403) B4474403
theorem B1988623 : Blo 1987435 1988623 := bstep (se 1 (by rfl) ⟨1491467, by rfl⟩ : syracuseStep 1988623 = 2982935) B2982935
theorem B2982941 : Blo 1987435 2982941 := bbase (se 3 (by rfl) ⟨559301, by rfl⟩ : syracuseStep 2982941 = 1118603) (by norm_num)
theorem B1988627 : Blo 1987435 1988627 := bstep (se 1 (by rfl) ⟨1491470, by rfl⟩ : syracuseStep 1988627 = 2982941) B2982941
theorem B4474421 : Blo 1987435 4474421 := bbase (se 5 (by rfl) ⟨209738, by rfl⟩ : syracuseStep 4474421 = 419477) (by norm_num)
theorem B2982947 : Blo 1987435 2982947 := bstep (se 1 (by rfl) ⟨2237210, by rfl⟩ : syracuseStep 2982947 = 4474421) B4474421
theorem B1988631 : Blo 1987435 1988631 := bstep (se 1 (by rfl) ⟨1491473, by rfl⟩ : syracuseStep 1988631 = 2982947) B2982947
theorem B4778117 : Blo 1987435 4778117 := bbase (se 4 (by rfl) ⟨447948, by rfl⟩ : syracuseStep 4778117 = 895897) (by norm_num)
theorem B3185411 : Blo 1987435 3185411 := bstep (se 1 (by rfl) ⟨2389058, by rfl⟩ : syracuseStep 3185411 = 4778117) B4778117
theorem B8494429 : Blo 1987435 8494429 := bstep (se 3 (by rfl) ⟨1592705, by rfl⟩ : syracuseStep 8494429 = 3185411) B3185411
theorem B11325905 : Blo 1987435 11325905 := bstep (se 2 (by rfl) ⟨4247214, by rfl⟩ : syracuseStep 11325905 = 8494429) B8494429
theorem B7550603 : Blo 1987435 7550603 := bstep (se 1 (by rfl) ⟨5662952, by rfl⟩ : syracuseStep 7550603 = 11325905) B11325905
theorem B5033735 : Blo 1987435 5033735 := bstep (se 1 (by rfl) ⟨3775301, by rfl⟩ : syracuseStep 5033735 = 7550603) B7550603
theorem B3355823 : Blo 1987435 3355823 := bstep (se 1 (by rfl) ⟨2516867, by rfl⟩ : syracuseStep 3355823 = 5033735) B5033735
theorem B2237215 : Blo 1987435 2237215 := bstep (se 1 (by rfl) ⟨1677911, by rfl⟩ : syracuseStep 2237215 = 3355823) B3355823
theorem B2982953 : Blo 1987435 2982953 := bstep (se 2 (by rfl) ⟨1118607, by rfl⟩ : syracuseStep 2982953 = 2237215) B2237215
theorem B1988635 : Blo 1987435 1988635 := bstep (se 1 (by rfl) ⟨1491476, by rfl⟩ : syracuseStep 1988635 = 2982953) B2982953
theorem B2551213 : Blo 1987435 2551213 := bbase (se 3 (by rfl) ⟨478352, by rfl⟩ : syracuseStep 2551213 = 956705) (by norm_num)
theorem B3401617 : Blo 1987435 3401617 := bstep (se 2 (by rfl) ⟨1275606, by rfl⟩ : syracuseStep 3401617 = 2551213) B2551213
theorem B4535489 : Blo 1987435 4535489 := bstep (se 2 (by rfl) ⟨1700808, by rfl⟩ : syracuseStep 4535489 = 3401617) B3401617
theorem B3023659 : Blo 1987435 3023659 := bstep (se 1 (by rfl) ⟨2267744, by rfl⟩ : syracuseStep 3023659 = 4535489) B4535489
theorem B4031545 : Blo 1987435 4031545 := bstep (se 2 (by rfl) ⟨1511829, by rfl⟩ : syracuseStep 4031545 = 3023659) B3023659
theorem B5375393 : Blo 1987435 5375393 := bstep (se 2 (by rfl) ⟨2015772, by rfl⟩ : syracuseStep 5375393 = 4031545) B4031545
theorem B3583595 : Blo 1987435 3583595 := bstep (se 1 (by rfl) ⟨2687696, by rfl⟩ : syracuseStep 3583595 = 5375393) B5375393
theorem B2389063 : Blo 1987435 2389063 := bstep (se 1 (by rfl) ⟨1791797, by rfl⟩ : syracuseStep 2389063 = 3583595) B3583595
theorem B3185417 : Blo 1987435 3185417 := bstep (se 2 (by rfl) ⟨1194531, by rfl⟩ : syracuseStep 3185417 = 2389063) B2389063
theorem B8494445 : Blo 1987435 8494445 := bstep (se 3 (by rfl) ⟨1592708, by rfl⟩ : syracuseStep 8494445 = 3185417) B3185417
theorem B5662963 : Blo 1987435 5662963 := bstep (se 1 (by rfl) ⟨4247222, by rfl⟩ : syracuseStep 5662963 = 8494445) B8494445
theorem B7550617 : Blo 1987435 7550617 := bstep (se 2 (by rfl) ⟨2831481, by rfl⟩ : syracuseStep 7550617 = 5662963) B5662963
theorem B10067489 : Blo 1987435 10067489 := bstep (se 2 (by rfl) ⟨3775308, by rfl⟩ : syracuseStep 10067489 = 7550617) B7550617
theorem B6711659 : Blo 1987435 6711659 := bstep (se 1 (by rfl) ⟨5033744, by rfl⟩ : syracuseStep 6711659 = 10067489) B10067489
theorem B4474439 : Blo 1987435 4474439 := bstep (se 1 (by rfl) ⟨3355829, by rfl⟩ : syracuseStep 4474439 = 6711659) B6711659
theorem B2982959 : Blo 1987435 2982959 := bstep (se 1 (by rfl) ⟨2237219, by rfl⟩ : syracuseStep 2982959 = 4474439) B4474439
theorem B1988639 : Blo 1987435 1988639 := bstep (se 1 (by rfl) ⟨1491479, by rfl⟩ : syracuseStep 1988639 = 2982959) B2982959
theorem B2982965 : Blo 1987435 2982965 := bbase (se 5 (by rfl) ⟨139826, by rfl⟩ : syracuseStep 2982965 = 279653) (by norm_num)
theorem B1988643 : Blo 1987435 1988643 := bstep (se 1 (by rfl) ⟨1491482, by rfl⟩ : syracuseStep 1988643 = 2982965) B2982965
theorem B5033765 : Blo 1987435 5033765 := bbase (se 4 (by rfl) ⟨471915, by rfl⟩ : syracuseStep 5033765 = 943831) (by norm_num)
theorem B3355843 : Blo 1987435 3355843 := bstep (se 1 (by rfl) ⟨2516882, by rfl⟩ : syracuseStep 3355843 = 5033765) B5033765
theorem B4474457 : Blo 1987435 4474457 := bstep (se 2 (by rfl) ⟨1677921, by rfl⟩ : syracuseStep 4474457 = 3355843) B3355843
theorem B2982971 : Blo 1987435 2982971 := bstep (se 1 (by rfl) ⟨2237228, by rfl⟩ : syracuseStep 2982971 = 4474457) B4474457
theorem B1988647 : Blo 1987435 1988647 := bstep (se 1 (by rfl) ⟨1491485, by rfl⟩ : syracuseStep 1988647 = 2982971) B2982971
theorem B2237233 : Blo 1987435 2237233 := bbase (se 2 (by rfl) ⟨838962, by rfl⟩ : syracuseStep 2237233 = 1677925) (by norm_num)
theorem B2982977 : Blo 1987435 2982977 := bstep (se 2 (by rfl) ⟨1118616, by rfl⟩ : syracuseStep 2982977 = 2237233) B2237233
theorem B1988651 : Blo 1987435 1988651 := bstep (se 1 (by rfl) ⟨1491488, by rfl⟩ : syracuseStep 1988651 = 2982977) B2982977
theorem B4778165 : Blo 1987435 4778165 := bbase (se 5 (by rfl) ⟨223976, by rfl⟩ : syracuseStep 4778165 = 447953) (by norm_num)
theorem B3185443 : Blo 1987435 3185443 := bstep (se 1 (by rfl) ⟨2389082, by rfl⟩ : syracuseStep 3185443 = 4778165) B4778165
theorem B4247257 : Blo 1987435 4247257 := bstep (se 2 (by rfl) ⟨1592721, by rfl⟩ : syracuseStep 4247257 = 3185443) B3185443
theorem B5663009 : Blo 1987435 5663009 := bstep (se 2 (by rfl) ⟨2123628, by rfl⟩ : syracuseStep 5663009 = 4247257) B4247257
theorem B3775339 : Blo 1987435 3775339 := bstep (se 1 (by rfl) ⟨2831504, by rfl⟩ : syracuseStep 3775339 = 5663009) B5663009
theorem B5033785 : Blo 1987435 5033785 := bstep (se 2 (by rfl) ⟨1887669, by rfl⟩ : syracuseStep 5033785 = 3775339) B3775339
theorem B6711713 : Blo 1987435 6711713 := bstep (se 2 (by rfl) ⟨2516892, by rfl⟩ : syracuseStep 6711713 = 5033785) B5033785
theorem B4474475 : Blo 1987435 4474475 := bstep (se 1 (by rfl) ⟨3355856, by rfl⟩ : syracuseStep 4474475 = 6711713) B6711713
theorem B2982983 : Blo 1987435 2982983 := bstep (se 1 (by rfl) ⟨2237237, by rfl⟩ : syracuseStep 2982983 = 4474475) B4474475
theorem B1988655 : Blo 1987435 1988655 := bstep (se 1 (by rfl) ⟨1491491, by rfl⟩ : syracuseStep 1988655 = 2982983) B2982983
theorem B2982989 : Blo 1987435 2982989 := bbase (se 3 (by rfl) ⟨559310, by rfl⟩ : syracuseStep 2982989 = 1118621) (by norm_num)
theorem B1988659 : Blo 1987435 1988659 := bstep (se 1 (by rfl) ⟨1491494, by rfl⟩ : syracuseStep 1988659 = 2982989) B2982989
theorem B4474493 : Blo 1987435 4474493 := bbase (se 3 (by rfl) ⟨838967, by rfl⟩ : syracuseStep 4474493 = 1677935) (by norm_num)
theorem B2982995 : Blo 1987435 2982995 := bstep (se 1 (by rfl) ⟨2237246, by rfl⟩ : syracuseStep 2982995 = 4474493) B4474493
theorem B1988663 : Blo 1987435 1988663 := bstep (se 1 (by rfl) ⟨1491497, by rfl⟩ : syracuseStep 1988663 = 2982995) B2982995
theorem B3355877 : Blo 1987435 3355877 := bbase (se 4 (by rfl) ⟨314613, by rfl⟩ : syracuseStep 3355877 = 629227) (by norm_num)
theorem B2237251 : Blo 1987435 2237251 := bstep (se 1 (by rfl) ⟨1677938, by rfl⟩ : syracuseStep 2237251 = 3355877) B3355877
theorem B2983001 : Blo 1987435 2983001 := bstep (se 2 (by rfl) ⟨1118625, by rfl⟩ : syracuseStep 2983001 = 2237251) B2237251
theorem B1988667 : Blo 1987435 1988667 := bstep (se 1 (by rfl) ⟨1491500, by rfl⟩ : syracuseStep 1988667 = 2983001) B2983001
theorem B4843397 : Blo 1987435 4843397 := bbase (se 4 (by rfl) ⟨454068, by rfl⟩ : syracuseStep 4843397 = 908137) (by norm_num)
theorem B3228931 : Blo 1987435 3228931 := bstep (se 1 (by rfl) ⟨2421698, by rfl⟩ : syracuseStep 3228931 = 4843397) B4843397
theorem B4305241 : Blo 1987435 4305241 := bstep (se 2 (by rfl) ⟨1614465, by rfl⟩ : syracuseStep 4305241 = 3228931) B3228931
theorem B5740321 : Blo 1987435 5740321 := bstep (se 2 (by rfl) ⟨2152620, by rfl⟩ : syracuseStep 5740321 = 4305241) B4305241
theorem B7653761 : Blo 1987435 7653761 := bstep (se 2 (by rfl) ⟨2870160, by rfl⟩ : syracuseStep 7653761 = 5740321) B5740321
theorem B5102507 : Blo 1987435 5102507 := bstep (se 1 (by rfl) ⟨3826880, by rfl⟩ : syracuseStep 5102507 = 7653761) B7653761
theorem B3401671 : Blo 1987435 3401671 := bstep (se 1 (by rfl) ⟨2551253, by rfl⟩ : syracuseStep 3401671 = 5102507) B5102507
theorem B4535561 : Blo 1987435 4535561 := bstep (se 2 (by rfl) ⟨1700835, by rfl⟩ : syracuseStep 4535561 = 3401671) B3401671
theorem B12094829 : Blo 1987435 12094829 := bstep (se 3 (by rfl) ⟨2267780, by rfl⟩ : syracuseStep 12094829 = 4535561) B4535561
theorem B8063219 : Blo 1987435 8063219 := bstep (se 1 (by rfl) ⟨6047414, by rfl⟩ : syracuseStep 8063219 = 12094829) B12094829
theorem B5375479 : Blo 1987435 5375479 := bstep (se 1 (by rfl) ⟨4031609, by rfl⟩ : syracuseStep 5375479 = 8063219) B8063219
theorem B7167305 : Blo 1987435 7167305 := bstep (se 2 (by rfl) ⟨2687739, by rfl⟩ : syracuseStep 7167305 = 5375479) B5375479
theorem B4778203 : Blo 1987435 4778203 := bstep (se 1 (by rfl) ⟨3583652, by rfl⟩ : syracuseStep 4778203 = 7167305) B7167305
theorem B6370937 : Blo 1987435 6370937 := bstep (se 2 (by rfl) ⟨2389101, by rfl⟩ : syracuseStep 6370937 = 4778203) B4778203
theorem B4247291 : Blo 1987435 4247291 := bstep (se 1 (by rfl) ⟨3185468, by rfl⟩ : syracuseStep 4247291 = 6370937) B6370937
theorem B2831527 : Blo 1987435 2831527 := bstep (se 1 (by rfl) ⟨2123645, by rfl⟩ : syracuseStep 2831527 = 4247291) B4247291
theorem B15101477 : Blo 1987435 15101477 := bstep (se 4 (by rfl) ⟨1415763, by rfl⟩ : syracuseStep 15101477 = 2831527) B2831527
theorem B10067651 : Blo 1987435 10067651 := bstep (se 1 (by rfl) ⟨7550738, by rfl⟩ : syracuseStep 10067651 = 15101477) B15101477
theorem B6711767 : Blo 1987435 6711767 := bstep (se 1 (by rfl) ⟨5033825, by rfl⟩ : syracuseStep 6711767 = 10067651) B10067651
theorem B4474511 : Blo 1987435 4474511 := bstep (se 1 (by rfl) ⟨3355883, by rfl⟩ : syracuseStep 4474511 = 6711767) B6711767
theorem B2983007 : Blo 1987435 2983007 := bstep (se 1 (by rfl) ⟨2237255, by rfl⟩ : syracuseStep 2983007 = 4474511) B4474511
theorem B1988671 : Blo 1987435 1988671 := bstep (se 1 (by rfl) ⟨1491503, by rfl⟩ : syracuseStep 1988671 = 2983007) B2983007
theorem B2983013 : Blo 1987435 2983013 := bbase (se 4 (by rfl) ⟨279657, by rfl⟩ : syracuseStep 2983013 = 559315) (by norm_num)
theorem B1988675 : Blo 1987435 1988675 := bstep (se 1 (by rfl) ⟨1491506, by rfl⟩ : syracuseStep 1988675 = 2983013) B2983013
theorem B4247309 : Blo 1987435 4247309 := bbase (se 3 (by rfl) ⟨796370, by rfl⟩ : syracuseStep 4247309 = 1592741) (by norm_num)
theorem B2831539 : Blo 1987435 2831539 := bstep (se 1 (by rfl) ⟨2123654, by rfl⟩ : syracuseStep 2831539 = 4247309) B4247309
theorem B3775385 : Blo 1987435 3775385 := bstep (se 2 (by rfl) ⟨1415769, by rfl⟩ : syracuseStep 3775385 = 2831539) B2831539
theorem B2516923 : Blo 1987435 2516923 := bstep (se 1 (by rfl) ⟨1887692, by rfl⟩ : syracuseStep 2516923 = 3775385) B3775385
theorem B3355897 : Blo 1987435 3355897 := bstep (se 2 (by rfl) ⟨1258461, by rfl⟩ : syracuseStep 3355897 = 2516923) B2516923
theorem B4474529 : Blo 1987435 4474529 := bstep (se 2 (by rfl) ⟨1677948, by rfl⟩ : syracuseStep 4474529 = 3355897) B3355897
theorem B2983019 : Blo 1987435 2983019 := bstep (se 1 (by rfl) ⟨2237264, by rfl⟩ : syracuseStep 2983019 = 4474529) B4474529
theorem B1988679 : Blo 1987435 1988679 := bstep (se 1 (by rfl) ⟨1491509, by rfl⟩ : syracuseStep 1988679 = 2983019) B2983019
theorem B2237269 : Blo 1987435 2237269 := bbase (se 9 (by rfl) ⟨6554, by rfl⟩ : syracuseStep 2237269 = 13109) (by norm_num)
theorem B2983025 : Blo 1987435 2983025 := bstep (se 2 (by rfl) ⟨1118634, by rfl⟩ : syracuseStep 2983025 = 2237269) B2237269
theorem B1988683 : Blo 1987435 1988683 := bstep (se 1 (by rfl) ⟨1491512, by rfl⟩ : syracuseStep 1988683 = 2983025) B2983025
theorem B2516933 : Blo 1987435 2516933 := bbase (se 4 (by rfl) ⟨235962, by rfl⟩ : syracuseStep 2516933 = 471925) (by norm_num)
theorem B6711821 : Blo 1987435 6711821 := bstep (se 3 (by rfl) ⟨1258466, by rfl⟩ : syracuseStep 6711821 = 2516933) B2516933
theorem B4474547 : Blo 1987435 4474547 := bstep (se 1 (by rfl) ⟨3355910, by rfl⟩ : syracuseStep 4474547 = 6711821) B6711821
theorem B2983031 : Blo 1987435 2983031 := bstep (se 1 (by rfl) ⟨2237273, by rfl⟩ : syracuseStep 2983031 = 4474547) B4474547
theorem B1988687 : Blo 1987435 1988687 := bstep (se 1 (by rfl) ⟨1491515, by rfl⟩ : syracuseStep 1988687 = 2983031) B2983031
theorem B2983037 : Blo 1987435 2983037 := bbase (se 3 (by rfl) ⟨559319, by rfl⟩ : syracuseStep 2983037 = 1118639) (by norm_num)
theorem B1988691 : Blo 1987435 1988691 := bstep (se 1 (by rfl) ⟨1491518, by rfl⟩ : syracuseStep 1988691 = 2983037) B2983037
theorem B4474565 : Blo 1987435 4474565 := bbase (se 4 (by rfl) ⟨419490, by rfl⟩ : syracuseStep 4474565 = 838981) (by norm_num)
theorem B2983043 : Blo 1987435 2983043 := bstep (se 1 (by rfl) ⟨2237282, by rfl⟩ : syracuseStep 2983043 = 4474565) B4474565
theorem B1988695 : Blo 1987435 1988695 := bstep (se 1 (by rfl) ⟨1491521, by rfl⟩ : syracuseStep 1988695 = 2983043) B2983043
theorem B2551289 : Blo 1987435 2551289 := bbase (se 2 (by rfl) ⟨956733, by rfl⟩ : syracuseStep 2551289 = 1913467) (by norm_num)
theorem B6803437 : Blo 1987435 6803437 := bstep (se 3 (by rfl) ⟨1275644, by rfl⟩ : syracuseStep 6803437 = 2551289) B2551289
theorem B9071249 : Blo 1987435 9071249 := bstep (se 2 (by rfl) ⟨3401718, by rfl⟩ : syracuseStep 9071249 = 6803437) B6803437
theorem B24189997 : Blo 1987435 24189997 := bstep (se 3 (by rfl) ⟨4535624, by rfl⟩ : syracuseStep 24189997 = 9071249) B9071249
theorem B32253329 : Blo 1987435 32253329 := bstep (se 2 (by rfl) ⟨12094998, by rfl⟩ : syracuseStep 32253329 = 24189997) B24189997
theorem B21502219 : Blo 1987435 21502219 := bstep (se 1 (by rfl) ⟨16126664, by rfl⟩ : syracuseStep 21502219 = 32253329) B32253329
theorem B28669625 : Blo 1987435 28669625 := bstep (se 2 (by rfl) ⟨10751109, by rfl⟩ : syracuseStep 28669625 = 21502219) B21502219
theorem B19113083 : Blo 1987435 19113083 := bstep (se 1 (by rfl) ⟨14334812, by rfl⟩ : syracuseStep 19113083 = 28669625) B28669625
theorem B12742055 : Blo 1987435 12742055 := bstep (se 1 (by rfl) ⟨9556541, by rfl⟩ : syracuseStep 12742055 = 19113083) B19113083
theorem B8494703 : Blo 1987435 8494703 := bstep (se 1 (by rfl) ⟨6371027, by rfl⟩ : syracuseStep 8494703 = 12742055) B12742055
theorem B5663135 : Blo 1987435 5663135 := bstep (se 1 (by rfl) ⟨4247351, by rfl⟩ : syracuseStep 5663135 = 8494703) B8494703
theorem B3775423 : Blo 1987435 3775423 := bstep (se 1 (by rfl) ⟨2831567, by rfl⟩ : syracuseStep 3775423 = 5663135) B5663135
theorem B5033897 : Blo 1987435 5033897 := bstep (se 2 (by rfl) ⟨1887711, by rfl⟩ : syracuseStep 5033897 = 3775423) B3775423
theorem B3355931 : Blo 1987435 3355931 := bstep (se 1 (by rfl) ⟨2516948, by rfl⟩ : syracuseStep 3355931 = 5033897) B5033897
theorem B2237287 : Blo 1987435 2237287 := bstep (se 1 (by rfl) ⟨1677965, by rfl⟩ : syracuseStep 2237287 = 3355931) B3355931
theorem B2983049 : Blo 1987435 2983049 := bstep (se 2 (by rfl) ⟨1118643, by rfl⟩ : syracuseStep 2983049 = 2237287) B2237287
theorem B1988699 : Blo 1987435 1988699 := bstep (se 1 (by rfl) ⟨1491524, by rfl⟩ : syracuseStep 1988699 = 2983049) B2983049
theorem B10067813 : Blo 1987435 10067813 := bbase (se 4 (by rfl) ⟨943857, by rfl⟩ : syracuseStep 10067813 = 1887715) (by norm_num)
theorem B6711875 : Blo 1987435 6711875 := bstep (se 1 (by rfl) ⟨5033906, by rfl⟩ : syracuseStep 6711875 = 10067813) B10067813
theorem B4474583 : Blo 1987435 4474583 := bstep (se 1 (by rfl) ⟨3355937, by rfl⟩ : syracuseStep 4474583 = 6711875) B6711875
theorem B2983055 : Blo 1987435 2983055 := bstep (se 1 (by rfl) ⟨2237291, by rfl⟩ : syracuseStep 2983055 = 4474583) B4474583
theorem B1988703 : Blo 1987435 1988703 := bstep (se 1 (by rfl) ⟨1491527, by rfl⟩ : syracuseStep 1988703 = 2983055) B2983055
theorem B2983061 : Blo 1987435 2983061 := bbase (se 6 (by rfl) ⟨69915, by rfl⟩ : syracuseStep 2983061 = 139831) (by norm_num)
theorem B1988707 : Blo 1987435 1988707 := bstep (se 1 (by rfl) ⟨1491530, by rfl⟩ : syracuseStep 1988707 = 2983061) B2983061
theorem B8063381 : Blo 1987435 8063381 := bbase (se 6 (by rfl) ⟨188985, by rfl⟩ : syracuseStep 8063381 = 377971) (by norm_num)
theorem B5375587 : Blo 1987435 5375587 := bstep (se 1 (by rfl) ⟨4031690, by rfl⟩ : syracuseStep 5375587 = 8063381) B8063381
theorem B7167449 : Blo 1987435 7167449 := bstep (se 2 (by rfl) ⟨2687793, by rfl⟩ : syracuseStep 7167449 = 5375587) B5375587
theorem B4778299 : Blo 1987435 4778299 := bstep (se 1 (by rfl) ⟨3583724, by rfl⟩ : syracuseStep 4778299 = 7167449) B7167449
theorem B6371065 : Blo 1987435 6371065 := bstep (se 2 (by rfl) ⟨2389149, by rfl⟩ : syracuseStep 6371065 = 4778299) B4778299
theorem B8494753 : Blo 1987435 8494753 := bstep (se 2 (by rfl) ⟨3185532, by rfl⟩ : syracuseStep 8494753 = 6371065) B6371065
theorem B11326337 : Blo 1987435 11326337 := bstep (se 2 (by rfl) ⟨4247376, by rfl⟩ : syracuseStep 11326337 = 8494753) B8494753
theorem B7550891 : Blo 1987435 7550891 := bstep (se 1 (by rfl) ⟨5663168, by rfl⟩ : syracuseStep 7550891 = 11326337) B11326337
theorem B5033927 : Blo 1987435 5033927 := bstep (se 1 (by rfl) ⟨3775445, by rfl⟩ : syracuseStep 5033927 = 7550891) B7550891
theorem B3355951 : Blo 1987435 3355951 := bstep (se 1 (by rfl) ⟨2516963, by rfl⟩ : syracuseStep 3355951 = 5033927) B5033927
theorem B4474601 : Blo 1987435 4474601 := bstep (se 2 (by rfl) ⟨1677975, by rfl⟩ : syracuseStep 4474601 = 3355951) B3355951
theorem B2983067 : Blo 1987435 2983067 := bstep (se 1 (by rfl) ⟨2237300, by rfl⟩ : syracuseStep 2983067 = 4474601) B4474601
theorem B1988711 : Blo 1987435 1988711 := bstep (se 1 (by rfl) ⟨1491533, by rfl⟩ : syracuseStep 1988711 = 2983067) B2983067
theorem B2237305 : Blo 1987435 2237305 := bbase (se 2 (by rfl) ⟨838989, by rfl⟩ : syracuseStep 2237305 = 1677979) (by norm_num)
theorem B2983073 : Blo 1987435 2983073 := bstep (se 2 (by rfl) ⟨1118652, by rfl⟩ : syracuseStep 2983073 = 2237305) B2237305
theorem B1988715 : Blo 1987435 1988715 := bstep (se 1 (by rfl) ⟨1491536, by rfl⟩ : syracuseStep 1988715 = 2983073) B2983073
theorem B3826973 : Blo 1987435 3826973 := bbase (se 3 (by rfl) ⟨717557, by rfl⟩ : syracuseStep 3826973 = 1435115) (by norm_num)
theorem B10205261 : Blo 1987435 10205261 := bstep (se 3 (by rfl) ⟨1913486, by rfl⟩ : syracuseStep 10205261 = 3826973) B3826973
theorem B6803507 : Blo 1987435 6803507 := bstep (se 1 (by rfl) ⟨5102630, by rfl⟩ : syracuseStep 6803507 = 10205261) B10205261
theorem B4535671 : Blo 1987435 4535671 := bstep (se 1 (by rfl) ⟨3401753, by rfl⟩ : syracuseStep 4535671 = 6803507) B6803507
theorem B6047561 : Blo 1987435 6047561 := bstep (se 2 (by rfl) ⟨2267835, by rfl⟩ : syracuseStep 6047561 = 4535671) B4535671
theorem B4031707 : Blo 1987435 4031707 := bstep (se 1 (by rfl) ⟨3023780, by rfl⟩ : syracuseStep 4031707 = 6047561) B6047561
theorem B5375609 : Blo 1987435 5375609 := bstep (se 2 (by rfl) ⟨2015853, by rfl⟩ : syracuseStep 5375609 = 4031707) B4031707
theorem B3583739 : Blo 1987435 3583739 := bstep (se 1 (by rfl) ⟨2687804, by rfl⟩ : syracuseStep 3583739 = 5375609) B5375609
theorem B2389159 : Blo 1987435 2389159 := bstep (se 1 (by rfl) ⟨1791869, by rfl⟩ : syracuseStep 2389159 = 3583739) B3583739
theorem B12742181 : Blo 1987435 12742181 := bstep (se 4 (by rfl) ⟨1194579, by rfl⟩ : syracuseStep 12742181 = 2389159) B2389159
theorem B8494787 : Blo 1987435 8494787 := bstep (se 1 (by rfl) ⟨6371090, by rfl⟩ : syracuseStep 8494787 = 12742181) B12742181
theorem B5663191 : Blo 1987435 5663191 := bstep (se 1 (by rfl) ⟨4247393, by rfl⟩ : syracuseStep 5663191 = 8494787) B8494787
theorem B7550921 : Blo 1987435 7550921 := bstep (se 2 (by rfl) ⟨2831595, by rfl⟩ : syracuseStep 7550921 = 5663191) B5663191
theorem B5033947 : Blo 1987435 5033947 := bstep (se 1 (by rfl) ⟨3775460, by rfl⟩ : syracuseStep 5033947 = 7550921) B7550921
theorem B6711929 : Blo 1987435 6711929 := bstep (se 2 (by rfl) ⟨2516973, by rfl⟩ : syracuseStep 6711929 = 5033947) B5033947
theorem B4474619 : Blo 1987435 4474619 := bstep (se 1 (by rfl) ⟨3355964, by rfl⟩ : syracuseStep 4474619 = 6711929) B6711929
theorem B2983079 : Blo 1987435 2983079 := bstep (se 1 (by rfl) ⟨2237309, by rfl⟩ : syracuseStep 2983079 = 4474619) B4474619
theorem B1988719 : Blo 1987435 1988719 := bstep (se 1 (by rfl) ⟨1491539, by rfl⟩ : syracuseStep 1988719 = 2983079) B2983079
theorem B2983085 : Blo 1987435 2983085 := bbase (se 3 (by rfl) ⟨559328, by rfl⟩ : syracuseStep 2983085 = 1118657) (by norm_num)
theorem B1988723 : Blo 1987435 1988723 := bstep (se 1 (by rfl) ⟨1491542, by rfl⟩ : syracuseStep 1988723 = 2983085) B2983085
theorem B4474637 : Blo 1987435 4474637 := bbase (se 3 (by rfl) ⟨838994, by rfl⟩ : syracuseStep 4474637 = 1677989) (by norm_num)
theorem B2983091 : Blo 1987435 2983091 := bstep (se 1 (by rfl) ⟨2237318, by rfl⟩ : syracuseStep 2983091 = 4474637) B4474637
theorem B1988727 : Blo 1987435 1988727 := bstep (se 1 (by rfl) ⟨1491545, by rfl⟩ : syracuseStep 1988727 = 2983091) B2983091
theorem B2516989 : Blo 1987435 2516989 := bbase (se 3 (by rfl) ⟨471935, by rfl⟩ : syracuseStep 2516989 = 943871) (by norm_num)
theorem B3355985 : Blo 1987435 3355985 := bstep (se 2 (by rfl) ⟨1258494, by rfl⟩ : syracuseStep 3355985 = 2516989) B2516989
theorem B2237323 : Blo 1987435 2237323 := bstep (se 1 (by rfl) ⟨1677992, by rfl⟩ : syracuseStep 2237323 = 3355985) B3355985
theorem B2983097 : Blo 1987435 2983097 := bstep (se 2 (by rfl) ⟨1118661, by rfl⟩ : syracuseStep 2983097 = 2237323) B2237323
theorem B1988731 : Blo 1987435 1988731 := bstep (se 1 (by rfl) ⟨1491548, by rfl⟩ : syracuseStep 1988731 = 2983097) B2983097
theorem B6371141 : Blo 1987435 6371141 := bbase (se 4 (by rfl) ⟨597294, by rfl⟩ : syracuseStep 6371141 = 1194589) (by norm_num)
theorem B16989709 : Blo 1987435 16989709 := bstep (se 3 (by rfl) ⟨3185570, by rfl⟩ : syracuseStep 16989709 = 6371141) B6371141
theorem B22652945 : Blo 1987435 22652945 := bstep (se 2 (by rfl) ⟨8494854, by rfl⟩ : syracuseStep 22652945 = 16989709) B16989709
theorem B15101963 : Blo 1987435 15101963 := bstep (se 1 (by rfl) ⟨11326472, by rfl⟩ : syracuseStep 15101963 = 22652945) B22652945
theorem B10067975 : Blo 1987435 10067975 := bstep (se 1 (by rfl) ⟨7550981, by rfl⟩ : syracuseStep 10067975 = 15101963) B15101963
theorem B6711983 : Blo 1987435 6711983 := bstep (se 1 (by rfl) ⟨5033987, by rfl⟩ : syracuseStep 6711983 = 10067975) B10067975
theorem B4474655 : Blo 1987435 4474655 := bstep (se 1 (by rfl) ⟨3355991, by rfl⟩ : syracuseStep 4474655 = 6711983) B6711983
theorem B2983103 : Blo 1987435 2983103 := bstep (se 1 (by rfl) ⟨2237327, by rfl⟩ : syracuseStep 2983103 = 4474655) B4474655
theorem B1988735 : Blo 1987435 1988735 := bstep (se 1 (by rfl) ⟨1491551, by rfl⟩ : syracuseStep 1988735 = 2983103) B2983103
theorem B2983109 : Blo 1987435 2983109 := bbase (se 4 (by rfl) ⟨279666, by rfl⟩ : syracuseStep 2983109 = 559333) (by norm_num)
theorem B1988739 : Blo 1987435 1988739 := bstep (se 1 (by rfl) ⟨1491554, by rfl⟩ : syracuseStep 1988739 = 2983109) B2983109
theorem B3356005 : Blo 1987435 3356005 := bbase (se 4 (by rfl) ⟨314625, by rfl⟩ : syracuseStep 3356005 = 629251) (by norm_num)
theorem B4474673 : Blo 1987435 4474673 := bstep (se 2 (by rfl) ⟨1678002, by rfl⟩ : syracuseStep 4474673 = 3356005) B3356005
theorem B2983115 : Blo 1987435 2983115 := bstep (se 1 (by rfl) ⟨2237336, by rfl⟩ : syracuseStep 2983115 = 4474673) B4474673
theorem B1988743 : Blo 1987435 1988743 := bstep (se 1 (by rfl) ⟨1491557, by rfl⟩ : syracuseStep 1988743 = 2983115) B2983115
theorem B2237341 : Blo 1987435 2237341 := bbase (se 3 (by rfl) ⟨419501, by rfl⟩ : syracuseStep 2237341 = 839003) (by norm_num)
theorem B2983121 : Blo 1987435 2983121 := bstep (se 2 (by rfl) ⟨1118670, by rfl⟩ : syracuseStep 2983121 = 2237341) B2237341
theorem B1988747 : Blo 1987435 1988747 := bstep (se 1 (by rfl) ⟨1491560, by rfl⟩ : syracuseStep 1988747 = 2983121) B2983121
theorem B6712037 : Blo 1987435 6712037 := bbase (se 4 (by rfl) ⟨629253, by rfl⟩ : syracuseStep 6712037 = 1258507) (by norm_num)
theorem B4474691 : Blo 1987435 4474691 := bstep (se 1 (by rfl) ⟨3356018, by rfl⟩ : syracuseStep 4474691 = 6712037) B6712037
theorem B2983127 : Blo 1987435 2983127 := bstep (se 1 (by rfl) ⟨2237345, by rfl⟩ : syracuseStep 2983127 = 4474691) B4474691
theorem B1988751 : Blo 1987435 1988751 := bstep (se 1 (by rfl) ⟨1491563, by rfl⟩ : syracuseStep 1988751 = 2983127) B2983127
theorem B2983133 : Blo 1987435 2983133 := bbase (se 3 (by rfl) ⟨559337, by rfl⟩ : syracuseStep 2983133 = 1118675) (by norm_num)
theorem B1988755 : Blo 1987435 1988755 := bstep (se 1 (by rfl) ⟨1491566, by rfl⟩ : syracuseStep 1988755 = 2983133) B2983133
theorem B4474709 : Blo 1987435 4474709 := bbase (se 9 (by rfl) ⟨13109, by rfl⟩ : syracuseStep 4474709 = 26219) (by norm_num)
theorem B2983139 : Blo 1987435 2983139 := bstep (se 1 (by rfl) ⟨2237354, by rfl⟩ : syracuseStep 2983139 = 4474709) B4474709
theorem B1988759 : Blo 1987435 1988759 := bstep (se 1 (by rfl) ⟨1491569, by rfl⟩ : syracuseStep 1988759 = 2983139) B2983139
theorem B5663317 : Blo 1987435 5663317 := bbase (se 8 (by rfl) ⟨33183, by rfl⟩ : syracuseStep 5663317 = 66367) (by norm_num)
theorem B7551089 : Blo 1987435 7551089 := bstep (se 2 (by rfl) ⟨2831658, by rfl⟩ : syracuseStep 7551089 = 5663317) B5663317
theorem B5034059 : Blo 1987435 5034059 := bstep (se 1 (by rfl) ⟨3775544, by rfl⟩ : syracuseStep 5034059 = 7551089) B7551089
theorem B3356039 : Blo 1987435 3356039 := bstep (se 1 (by rfl) ⟨2517029, by rfl⟩ : syracuseStep 3356039 = 5034059) B5034059
theorem B2237359 : Blo 1987435 2237359 := bstep (se 1 (by rfl) ⟨1678019, by rfl⟩ : syracuseStep 2237359 = 3356039) B3356039
theorem B2983145 : Blo 1987435 2983145 := bstep (se 2 (by rfl) ⟨1118679, by rfl⟩ : syracuseStep 2983145 = 2237359) B2237359
theorem B1988763 : Blo 1987435 1988763 := bstep (se 1 (by rfl) ⟨1491572, by rfl⟩ : syracuseStep 1988763 = 2983145) B2983145
theorem B8285141 : Blo 1987435 8285141 := bbase (se 7 (by rfl) ⟨97091, by rfl⟩ : syracuseStep 8285141 = 194183) (by norm_num)
theorem B5523427 : Blo 1987435 5523427 := bstep (se 1 (by rfl) ⟨4142570, by rfl⟩ : syracuseStep 5523427 = 8285141) B8285141
theorem B7364569 : Blo 1987435 7364569 := bstep (se 2 (by rfl) ⟨2761713, by rfl⟩ : syracuseStep 7364569 = 5523427) B5523427
theorem B9819425 : Blo 1987435 9819425 := bstep (se 2 (by rfl) ⟨3682284, by rfl⟩ : syracuseStep 9819425 = 7364569) B7364569
theorem B26185133 : Blo 1987435 26185133 := bstep (se 3 (by rfl) ⟨4909712, by rfl⟩ : syracuseStep 26185133 = 9819425) B9819425
theorem B17456755 : Blo 1987435 17456755 := bstep (se 1 (by rfl) ⟨13092566, by rfl⟩ : syracuseStep 17456755 = 26185133) B26185133
theorem B23275673 : Blo 1987435 23275673 := bstep (se 2 (by rfl) ⟨8728377, by rfl⟩ : syracuseStep 23275673 = 17456755) B17456755
theorem B15517115 : Blo 1987435 15517115 := bstep (se 1 (by rfl) ⟨11637836, by rfl⟩ : syracuseStep 15517115 = 23275673) B23275673
theorem B10344743 : Blo 1987435 10344743 := bstep (se 1 (by rfl) ⟨7758557, by rfl⟩ : syracuseStep 10344743 = 15517115) B15517115
theorem B6896495 : Blo 1987435 6896495 := bstep (se 1 (by rfl) ⟨5172371, by rfl⟩ : syracuseStep 6896495 = 10344743) B10344743
theorem B4597663 : Blo 1987435 4597663 := bstep (se 1 (by rfl) ⟨3448247, by rfl⟩ : syracuseStep 4597663 = 6896495) B6896495
theorem B6130217 : Blo 1987435 6130217 := bstep (se 2 (by rfl) ⟨2298831, by rfl⟩ : syracuseStep 6130217 = 4597663) B4597663
theorem B4086811 : Blo 1987435 4086811 := bstep (se 1 (by rfl) ⟨3065108, by rfl⟩ : syracuseStep 4086811 = 6130217) B6130217
theorem B5449081 : Blo 1987435 5449081 := bstep (se 2 (by rfl) ⟨2043405, by rfl⟩ : syracuseStep 5449081 = 4086811) B4086811
theorem B7265441 : Blo 1987435 7265441 := bstep (se 2 (by rfl) ⟨2724540, by rfl⟩ : syracuseStep 7265441 = 5449081) B5449081
theorem B4843627 : Blo 1987435 4843627 := bstep (se 1 (by rfl) ⟨3632720, by rfl⟩ : syracuseStep 4843627 = 7265441) B7265441
theorem B25832677 : Blo 1987435 25832677 := bstep (se 4 (by rfl) ⟨2421813, by rfl⟩ : syracuseStep 25832677 = 4843627) B4843627
theorem B34443569 : Blo 1987435 34443569 := bstep (se 2 (by rfl) ⟨12916338, by rfl⟩ : syracuseStep 34443569 = 25832677) B25832677
theorem B22962379 : Blo 1987435 22962379 := bstep (se 1 (by rfl) ⟨17221784, by rfl⟩ : syracuseStep 22962379 = 34443569) B34443569
theorem B30616505 : Blo 1987435 30616505 := bstep (se 2 (by rfl) ⟨11481189, by rfl⟩ : syracuseStep 30616505 = 22962379) B22962379
theorem B20411003 : Blo 1987435 20411003 := bstep (se 1 (by rfl) ⟨15308252, by rfl⟩ : syracuseStep 20411003 = 30616505) B30616505
theorem B13607335 : Blo 1987435 13607335 := bstep (se 1 (by rfl) ⟨10205501, by rfl⟩ : syracuseStep 13607335 = 20411003) B20411003
theorem B18143113 : Blo 1987435 18143113 := bstep (se 2 (by rfl) ⟨6803667, by rfl⟩ : syracuseStep 18143113 = 13607335) B13607335
theorem B24190817 : Blo 1987435 24190817 := bstep (se 2 (by rfl) ⟨9071556, by rfl⟩ : syracuseStep 24190817 = 18143113) B18143113
theorem B64508845 : Blo 1987435 64508845 := bstep (se 3 (by rfl) ⟨12095408, by rfl⟩ : syracuseStep 64508845 = 24190817) B24190817
theorem B86011793 : Blo 1987435 86011793 := bstep (se 2 (by rfl) ⟨32254422, by rfl⟩ : syracuseStep 86011793 = 64508845) B64508845
theorem B57341195 : Blo 1987435 57341195 := bstep (se 1 (by rfl) ⟨43005896, by rfl⟩ : syracuseStep 57341195 = 86011793) B86011793
theorem B38227463 : Blo 1987435 38227463 := bstep (se 1 (by rfl) ⟨28670597, by rfl⟩ : syracuseStep 38227463 = 57341195) B57341195
theorem B25484975 : Blo 1987435 25484975 := bstep (se 1 (by rfl) ⟨19113731, by rfl⟩ : syracuseStep 25484975 = 38227463) B38227463
theorem B16989983 : Blo 1987435 16989983 := bstep (se 1 (by rfl) ⟨12742487, by rfl⟩ : syracuseStep 16989983 = 25484975) B25484975
theorem B11326655 : Blo 1987435 11326655 := bstep (se 1 (by rfl) ⟨8494991, by rfl⟩ : syracuseStep 11326655 = 16989983) B16989983
theorem B7551103 : Blo 1987435 7551103 := bstep (se 1 (by rfl) ⟨5663327, by rfl⟩ : syracuseStep 7551103 = 11326655) B11326655
theorem B10068137 : Blo 1987435 10068137 := bstep (se 2 (by rfl) ⟨3775551, by rfl⟩ : syracuseStep 10068137 = 7551103) B7551103
theorem B6712091 : Blo 1987435 6712091 := bstep (se 1 (by rfl) ⟨5034068, by rfl⟩ : syracuseStep 6712091 = 10068137) B10068137
theorem B4474727 : Blo 1987435 4474727 := bstep (se 1 (by rfl) ⟨3356045, by rfl⟩ : syracuseStep 4474727 = 6712091) B6712091
theorem B2983151 : Blo 1987435 2983151 := bstep (se 1 (by rfl) ⟨2237363, by rfl⟩ : syracuseStep 2983151 = 4474727) B4474727
theorem B1988767 : Blo 1987435 1988767 := bstep (se 1 (by rfl) ⟨1491575, by rfl⟩ : syracuseStep 1988767 = 2983151) B2983151
theorem B2983157 : Blo 1987435 2983157 := bbase (se 5 (by rfl) ⟨139835, by rfl⟩ : syracuseStep 2983157 = 279671) (by norm_num)
theorem B1988771 : Blo 1987435 1988771 := bstep (se 1 (by rfl) ⟨1491578, by rfl⟩ : syracuseStep 1988771 = 2983157) B2983157
theorem B4778453 : Blo 1987435 4778453 := bbase (se 7 (by rfl) ⟨55997, by rfl⟩ : syracuseStep 4778453 = 111995) (by norm_num)
theorem B12742541 : Blo 1987435 12742541 := bstep (se 3 (by rfl) ⟨2389226, by rfl⟩ : syracuseStep 12742541 = 4778453) B4778453
theorem B8495027 : Blo 1987435 8495027 := bstep (se 1 (by rfl) ⟨6371270, by rfl⟩ : syracuseStep 8495027 = 12742541) B12742541
theorem B5663351 : Blo 1987435 5663351 := bstep (se 1 (by rfl) ⟨4247513, by rfl⟩ : syracuseStep 5663351 = 8495027) B8495027
theorem B3775567 : Blo 1987435 3775567 := bstep (se 1 (by rfl) ⟨2831675, by rfl⟩ : syracuseStep 3775567 = 5663351) B5663351
theorem B5034089 : Blo 1987435 5034089 := bstep (se 2 (by rfl) ⟨1887783, by rfl⟩ : syracuseStep 5034089 = 3775567) B3775567
theorem B3356059 : Blo 1987435 3356059 := bstep (se 1 (by rfl) ⟨2517044, by rfl⟩ : syracuseStep 3356059 = 5034089) B5034089
theorem B4474745 : Blo 1987435 4474745 := bstep (se 2 (by rfl) ⟨1678029, by rfl⟩ : syracuseStep 4474745 = 3356059) B3356059
theorem B2983163 : Blo 1987435 2983163 := bstep (se 1 (by rfl) ⟨2237372, by rfl⟩ : syracuseStep 2983163 = 4474745) B4474745
theorem B1988775 : Blo 1987435 1988775 := bstep (se 1 (by rfl) ⟨1491581, by rfl⟩ : syracuseStep 1988775 = 2983163) B2983163
theorem B2237377 : Blo 1987435 2237377 := bbase (se 2 (by rfl) ⟨839016, by rfl⟩ : syracuseStep 2237377 = 1678033) (by norm_num)
theorem B2983169 : Blo 1987435 2983169 := bstep (se 2 (by rfl) ⟨1118688, by rfl⟩ : syracuseStep 2983169 = 2237377) B2237377
theorem B1988779 : Blo 1987435 1988779 := bstep (se 1 (by rfl) ⟨1491584, by rfl⟩ : syracuseStep 1988779 = 2983169) B2983169
theorem B5034109 : Blo 1987435 5034109 := bbase (se 3 (by rfl) ⟨943895, by rfl⟩ : syracuseStep 5034109 = 1887791) (by norm_num)
theorem B6712145 : Blo 1987435 6712145 := bstep (se 2 (by rfl) ⟨2517054, by rfl⟩ : syracuseStep 6712145 = 5034109) B5034109
theorem B4474763 : Blo 1987435 4474763 := bstep (se 1 (by rfl) ⟨3356072, by rfl⟩ : syracuseStep 4474763 = 6712145) B6712145
theorem B2983175 : Blo 1987435 2983175 := bstep (se 1 (by rfl) ⟨2237381, by rfl⟩ : syracuseStep 2983175 = 4474763) B4474763
theorem B1988783 : Blo 1987435 1988783 := bstep (se 1 (by rfl) ⟨1491587, by rfl⟩ : syracuseStep 1988783 = 2983175) B2983175
theorem B2983181 : Blo 1987435 2983181 := bbase (se 3 (by rfl) ⟨559346, by rfl⟩ : syracuseStep 2983181 = 1118693) (by norm_num)
theorem B1988787 : Blo 1987435 1988787 := bstep (se 1 (by rfl) ⟨1491590, by rfl⟩ : syracuseStep 1988787 = 2983181) B2983181
theorem B4474781 : Blo 1987435 4474781 := bbase (se 3 (by rfl) ⟨839021, by rfl⟩ : syracuseStep 4474781 = 1678043) (by norm_num)
theorem B2983187 : Blo 1987435 2983187 := bstep (se 1 (by rfl) ⟨2237390, by rfl⟩ : syracuseStep 2983187 = 4474781) B4474781
theorem B1988791 : Blo 1987435 1988791 := bstep (se 1 (by rfl) ⟨1491593, by rfl⟩ : syracuseStep 1988791 = 2983187) B2983187
theorem B3356093 : Blo 1987435 3356093 := bbase (se 3 (by rfl) ⟨629267, by rfl⟩ : syracuseStep 3356093 = 1258535) (by norm_num)
theorem B2237395 : Blo 1987435 2237395 := bstep (se 1 (by rfl) ⟨1678046, by rfl⟩ : syracuseStep 2237395 = 3356093) B3356093
theorem B2983193 : Blo 1987435 2983193 := bstep (se 2 (by rfl) ⟨1118697, by rfl⟩ : syracuseStep 2983193 = 2237395) B2237395
theorem B1988795 : Blo 1987435 1988795 := bstep (se 1 (by rfl) ⟨1491596, by rfl⟩ : syracuseStep 1988795 = 2983193) B2983193
theorem B11326837 : Blo 1987435 11326837 := bbase (se 5 (by rfl) ⟨530945, by rfl⟩ : syracuseStep 11326837 = 1061891) (by norm_num)
theorem B15102449 : Blo 1987435 15102449 := bstep (se 2 (by rfl) ⟨5663418, by rfl⟩ : syracuseStep 15102449 = 11326837) B11326837
theorem B10068299 : Blo 1987435 10068299 := bstep (se 1 (by rfl) ⟨7551224, by rfl⟩ : syracuseStep 10068299 = 15102449) B15102449
theorem B6712199 : Blo 1987435 6712199 := bstep (se 1 (by rfl) ⟨5034149, by rfl⟩ : syracuseStep 6712199 = 10068299) B10068299
theorem B4474799 : Blo 1987435 4474799 := bstep (se 1 (by rfl) ⟨3356099, by rfl⟩ : syracuseStep 4474799 = 6712199) B6712199
theorem B2983199 : Blo 1987435 2983199 := bstep (se 1 (by rfl) ⟨2237399, by rfl⟩ : syracuseStep 2983199 = 4474799) B4474799
theorem B1988799 : Blo 1987435 1988799 := bstep (se 1 (by rfl) ⟨1491599, by rfl⟩ : syracuseStep 1988799 = 2983199) B2983199
theorem B2983205 : Blo 1987435 2983205 := bbase (se 4 (by rfl) ⟨279675, by rfl⟩ : syracuseStep 2983205 = 559351) (by norm_num)
theorem B1988803 : Blo 1987435 1988803 := bstep (se 1 (by rfl) ⟨1491602, by rfl⟩ : syracuseStep 1988803 = 2983205) B2983205
theorem B2517085 : Blo 1987435 2517085 := bbase (se 3 (by rfl) ⟨471953, by rfl⟩ : syracuseStep 2517085 = 943907) (by norm_num)
theorem B3356113 : Blo 1987435 3356113 := bstep (se 2 (by rfl) ⟨1258542, by rfl⟩ : syracuseStep 3356113 = 2517085) B2517085
theorem B4474817 : Blo 1987435 4474817 := bstep (se 2 (by rfl) ⟨1678056, by rfl⟩ : syracuseStep 4474817 = 3356113) B3356113
theorem B2983211 : Blo 1987435 2983211 := bstep (se 1 (by rfl) ⟨2237408, by rfl⟩ : syracuseStep 2983211 = 4474817) B4474817
theorem B1988807 : Blo 1987435 1988807 := bstep (se 1 (by rfl) ⟨1491605, by rfl⟩ : syracuseStep 1988807 = 2983211) B2983211
theorem B2237413 : Blo 1987435 2237413 := bbase (se 4 (by rfl) ⟨209757, by rfl⟩ : syracuseStep 2237413 = 419515) (by norm_num)
theorem B2983217 : Blo 1987435 2983217 := bstep (se 2 (by rfl) ⟨1118706, by rfl⟩ : syracuseStep 2983217 = 2237413) B2237413
theorem B1988811 : Blo 1987435 1988811 := bstep (se 1 (by rfl) ⟨1491608, by rfl⟩ : syracuseStep 1988811 = 2983217) B2983217
theorem B13607669 : Blo 1987435 13607669 := bbase (se 5 (by rfl) ⟨637859, by rfl⟩ : syracuseStep 13607669 = 1275719) (by norm_num)
theorem B9071779 : Blo 1987435 9071779 := bstep (se 1 (by rfl) ⟨6803834, by rfl⟩ : syracuseStep 9071779 = 13607669) B13607669
theorem B12095705 : Blo 1987435 12095705 := bstep (se 2 (by rfl) ⟨4535889, by rfl⟩ : syracuseStep 12095705 = 9071779) B9071779
theorem B8063803 : Blo 1987435 8063803 := bstep (se 1 (by rfl) ⟨6047852, by rfl⟩ : syracuseStep 8063803 = 12095705) B12095705
theorem B10751737 : Blo 1987435 10751737 := bstep (se 2 (by rfl) ⟨4031901, by rfl⟩ : syracuseStep 10751737 = 8063803) B8063803
theorem B14335649 : Blo 1987435 14335649 := bstep (se 2 (by rfl) ⟨5375868, by rfl⟩ : syracuseStep 14335649 = 10751737) B10751737
theorem B9557099 : Blo 1987435 9557099 := bstep (se 1 (by rfl) ⟨7167824, by rfl⟩ : syracuseStep 9557099 = 14335649) B14335649
theorem B6371399 : Blo 1987435 6371399 := bstep (se 1 (by rfl) ⟨4778549, by rfl⟩ : syracuseStep 6371399 = 9557099) B9557099
theorem B4247599 : Blo 1987435 4247599 := bstep (se 1 (by rfl) ⟨3185699, by rfl⟩ : syracuseStep 4247599 = 6371399) B6371399
theorem B5663465 : Blo 1987435 5663465 := bstep (se 2 (by rfl) ⟨2123799, by rfl⟩ : syracuseStep 5663465 = 4247599) B4247599
theorem B3775643 : Blo 1987435 3775643 := bstep (se 1 (by rfl) ⟨2831732, by rfl⟩ : syracuseStep 3775643 = 5663465) B5663465
theorem B2517095 : Blo 1987435 2517095 := bstep (se 1 (by rfl) ⟨1887821, by rfl⟩ : syracuseStep 2517095 = 3775643) B3775643
theorem B6712253 : Blo 1987435 6712253 := bstep (se 3 (by rfl) ⟨1258547, by rfl⟩ : syracuseStep 6712253 = 2517095) B2517095
theorem B4474835 : Blo 1987435 4474835 := bstep (se 1 (by rfl) ⟨3356126, by rfl⟩ : syracuseStep 4474835 = 6712253) B6712253
theorem B2983223 : Blo 1987435 2983223 := bstep (se 1 (by rfl) ⟨2237417, by rfl⟩ : syracuseStep 2983223 = 4474835) B4474835
theorem B1988815 : Blo 1987435 1988815 := bstep (se 1 (by rfl) ⟨1491611, by rfl⟩ : syracuseStep 1988815 = 2983223) B2983223
theorem B2983229 : Blo 1987435 2983229 := bbase (se 3 (by rfl) ⟨559355, by rfl⟩ : syracuseStep 2983229 = 1118711) (by norm_num)
theorem B1988819 : Blo 1987435 1988819 := bstep (se 1 (by rfl) ⟨1491614, by rfl⟩ : syracuseStep 1988819 = 2983229) B2983229
theorem B4474853 : Blo 1987435 4474853 := bbase (se 4 (by rfl) ⟨419517, by rfl⟩ : syracuseStep 4474853 = 839035) (by norm_num)
theorem B2983235 : Blo 1987435 2983235 := bstep (se 1 (by rfl) ⟨2237426, by rfl⟩ : syracuseStep 2983235 = 4474853) B4474853
theorem B1988823 : Blo 1987435 1988823 := bstep (se 1 (by rfl) ⟨1491617, by rfl⟩ : syracuseStep 1988823 = 2983235) B2983235
theorem B5034221 : Blo 1987435 5034221 := bbase (se 3 (by rfl) ⟨943916, by rfl⟩ : syracuseStep 5034221 = 1887833) (by norm_num)
theorem B3356147 : Blo 1987435 3356147 := bstep (se 1 (by rfl) ⟨2517110, by rfl⟩ : syracuseStep 3356147 = 5034221) B5034221
theorem B2237431 : Blo 1987435 2237431 := bstep (se 1 (by rfl) ⟨1678073, by rfl⟩ : syracuseStep 2237431 = 3356147) B3356147
theorem B2983241 : Blo 1987435 2983241 := bstep (se 2 (by rfl) ⟨1118715, by rfl⟩ : syracuseStep 2983241 = 2237431) B2237431
theorem B1988827 : Blo 1987435 1988827 := bstep (se 1 (by rfl) ⟨1491620, by rfl⟩ : syracuseStep 1988827 = 2983241) B2983241
theorem B3185725 : Blo 1987435 3185725 := bbase (se 3 (by rfl) ⟨597323, by rfl⟩ : syracuseStep 3185725 = 1194647) (by norm_num)
theorem B4247633 : Blo 1987435 4247633 := bstep (se 2 (by rfl) ⟨1592862, by rfl⟩ : syracuseStep 4247633 = 3185725) B3185725
theorem B2831755 : Blo 1987435 2831755 := bstep (se 1 (by rfl) ⟨2123816, by rfl⟩ : syracuseStep 2831755 = 4247633) B4247633
theorem B3775673 : Blo 1987435 3775673 := bstep (se 2 (by rfl) ⟨1415877, by rfl⟩ : syracuseStep 3775673 = 2831755) B2831755
theorem B10068461 : Blo 1987435 10068461 := bstep (se 3 (by rfl) ⟨1887836, by rfl⟩ : syracuseStep 10068461 = 3775673) B3775673
theorem B6712307 : Blo 1987435 6712307 := bstep (se 1 (by rfl) ⟨5034230, by rfl⟩ : syracuseStep 6712307 = 10068461) B10068461
theorem B4474871 : Blo 1987435 4474871 := bstep (se 1 (by rfl) ⟨3356153, by rfl⟩ : syracuseStep 4474871 = 6712307) B6712307
theorem B2983247 : Blo 1987435 2983247 := bstep (se 1 (by rfl) ⟨2237435, by rfl⟩ : syracuseStep 2983247 = 4474871) B4474871
theorem B1988831 : Blo 1987435 1988831 := bstep (se 1 (by rfl) ⟨1491623, by rfl⟩ : syracuseStep 1988831 = 2983247) B2983247
theorem B2983253 : Blo 1987435 2983253 := bbase (se 12 (by rfl) ⟨1092, by rfl⟩ : syracuseStep 2983253 = 2185) (by norm_num)
theorem B1988835 : Blo 1987435 1988835 := bstep (se 1 (by rfl) ⟨1491626, by rfl⟩ : syracuseStep 1988835 = 2983253) B2983253
theorem B2123825 : Blo 1987435 2123825 := bbase (se 2 (by rfl) ⟨796434, by rfl⟩ : syracuseStep 2123825 = 1592869) (by norm_num)
theorem B5663533 : Blo 1987435 5663533 := bstep (se 3 (by rfl) ⟨1061912, by rfl⟩ : syracuseStep 5663533 = 2123825) B2123825
theorem B7551377 : Blo 1987435 7551377 := bstep (se 2 (by rfl) ⟨2831766, by rfl⟩ : syracuseStep 7551377 = 5663533) B5663533
theorem B5034251 : Blo 1987435 5034251 := bstep (se 1 (by rfl) ⟨3775688, by rfl⟩ : syracuseStep 5034251 = 7551377) B7551377
theorem B3356167 : Blo 1987435 3356167 := bstep (se 1 (by rfl) ⟨2517125, by rfl⟩ : syracuseStep 3356167 = 5034251) B5034251
theorem B4474889 : Blo 1987435 4474889 := bstep (se 2 (by rfl) ⟨1678083, by rfl⟩ : syracuseStep 4474889 = 3356167) B3356167
theorem B2983259 : Blo 1987435 2983259 := bstep (se 1 (by rfl) ⟨2237444, by rfl⟩ : syracuseStep 2983259 = 4474889) B4474889
theorem B1988839 : Blo 1987435 1988839 := bstep (se 1 (by rfl) ⟨1491629, by rfl⟩ : syracuseStep 1988839 = 2983259) B2983259
theorem B2237449 : Blo 1987435 2237449 := bbase (se 2 (by rfl) ⟨839043, by rfl⟩ : syracuseStep 2237449 = 1678087) (by norm_num)
theorem B2983265 : Blo 1987435 2983265 := bstep (se 2 (by rfl) ⟨1118724, by rfl⟩ : syracuseStep 2983265 = 2237449) B2237449
theorem B1988843 : Blo 1987435 1988843 := bstep (se 1 (by rfl) ⟨1491632, by rfl⟩ : syracuseStep 1988843 = 2983265) B2983265
theorem B3632869 : Blo 1987435 3632869 := bbase (se 4 (by rfl) ⟨340581, by rfl⟩ : syracuseStep 3632869 = 681163) (by norm_num)
theorem B19375301 : Blo 1987435 19375301 := bstep (se 4 (by rfl) ⟨1816434, by rfl⟩ : syracuseStep 19375301 = 3632869) B3632869
theorem B12916867 : Blo 1987435 12916867 := bstep (se 1 (by rfl) ⟨9687650, by rfl⟩ : syracuseStep 12916867 = 19375301) B19375301
theorem B17222489 : Blo 1987435 17222489 := bstep (se 2 (by rfl) ⟨6458433, by rfl⟩ : syracuseStep 17222489 = 12916867) B12916867
theorem B11481659 : Blo 1987435 11481659 := bstep (se 1 (by rfl) ⟨8611244, by rfl⟩ : syracuseStep 11481659 = 17222489) B17222489
theorem B7654439 : Blo 1987435 7654439 := bstep (se 1 (by rfl) ⟨5740829, by rfl⟩ : syracuseStep 7654439 = 11481659) B11481659
theorem B5102959 : Blo 1987435 5102959 := bstep (se 1 (by rfl) ⟨3827219, by rfl⟩ : syracuseStep 5102959 = 7654439) B7654439
theorem B6803945 : Blo 1987435 6803945 := bstep (se 2 (by rfl) ⟨2551479, by rfl⟩ : syracuseStep 6803945 = 5102959) B5102959
theorem B4535963 : Blo 1987435 4535963 := bstep (se 1 (by rfl) ⟨3401972, by rfl⟩ : syracuseStep 4535963 = 6803945) B6803945
theorem B3023975 : Blo 1987435 3023975 := bstep (se 1 (by rfl) ⟨2267981, by rfl⟩ : syracuseStep 3023975 = 4535963) B4535963
theorem B2015983 : Blo 1987435 2015983 := bstep (se 1 (by rfl) ⟨1511987, by rfl⟩ : syracuseStep 2015983 = 3023975) B3023975
theorem B2687977 : Blo 1987435 2687977 := bstep (se 2 (by rfl) ⟨1007991, by rfl⟩ : syracuseStep 2687977 = 2015983) B2015983
theorem B3583969 : Blo 1987435 3583969 := bstep (se 2 (by rfl) ⟨1343988, by rfl⟩ : syracuseStep 3583969 = 2687977) B2687977
theorem B19114501 : Blo 1987435 19114501 := bstep (se 4 (by rfl) ⟨1791984, by rfl⟩ : syracuseStep 19114501 = 3583969) B3583969
theorem B25486001 : Blo 1987435 25486001 := bstep (se 2 (by rfl) ⟨9557250, by rfl⟩ : syracuseStep 25486001 = 19114501) B19114501
theorem B16990667 : Blo 1987435 16990667 := bstep (se 1 (by rfl) ⟨12743000, by rfl⟩ : syracuseStep 16990667 = 25486001) B25486001
theorem B11327111 : Blo 1987435 11327111 := bstep (se 1 (by rfl) ⟨8495333, by rfl⟩ : syracuseStep 11327111 = 16990667) B16990667
theorem B7551407 : Blo 1987435 7551407 := bstep (se 1 (by rfl) ⟨5663555, by rfl⟩ : syracuseStep 7551407 = 11327111) B11327111
theorem B5034271 : Blo 1987435 5034271 := bstep (se 1 (by rfl) ⟨3775703, by rfl⟩ : syracuseStep 5034271 = 7551407) B7551407
theorem B6712361 : Blo 1987435 6712361 := bstep (se 2 (by rfl) ⟨2517135, by rfl⟩ : syracuseStep 6712361 = 5034271) B5034271
theorem B4474907 : Blo 1987435 4474907 := bstep (se 1 (by rfl) ⟨3356180, by rfl⟩ : syracuseStep 4474907 = 6712361) B6712361
theorem B2983271 : Blo 1987435 2983271 := bstep (se 1 (by rfl) ⟨2237453, by rfl⟩ : syracuseStep 2983271 = 4474907) B4474907
theorem B1988847 : Blo 1987435 1988847 := bstep (se 1 (by rfl) ⟨1491635, by rfl⟩ : syracuseStep 1988847 = 2983271) B2983271
theorem B2983277 : Blo 1987435 2983277 := bbase (se 3 (by rfl) ⟨559364, by rfl⟩ : syracuseStep 2983277 = 1118729) (by norm_num)
theorem B1988851 : Blo 1987435 1988851 := bstep (se 1 (by rfl) ⟨1491638, by rfl⟩ : syracuseStep 1988851 = 2983277) B2983277
theorem B4474925 : Blo 1987435 4474925 := bbase (se 3 (by rfl) ⟨839048, by rfl⟩ : syracuseStep 4474925 = 1678097) (by norm_num)
theorem B2983283 : Blo 1987435 2983283 := bstep (se 1 (by rfl) ⟨2237462, by rfl⟩ : syracuseStep 2983283 = 4474925) B4474925
theorem B1988855 : Blo 1987435 1988855 := bstep (se 1 (by rfl) ⟨1491641, by rfl⟩ : syracuseStep 1988855 = 2983283) B2983283
theorem B8747029 : Blo 1987435 8747029 := bbase (se 6 (by rfl) ⟨205008, by rfl⟩ : syracuseStep 8747029 = 410017) (by norm_num)
theorem B46650821 : Blo 1987435 46650821 := bstep (se 4 (by rfl) ⟨4373514, by rfl⟩ : syracuseStep 46650821 = 8747029) B8747029
theorem B124402189 : Blo 1987435 124402189 := bstep (se 3 (by rfl) ⟨23325410, by rfl⟩ : syracuseStep 124402189 = 46650821) B46650821
theorem B165869585 : Blo 1987435 165869585 := bstep (se 2 (by rfl) ⟨62201094, by rfl⟩ : syracuseStep 165869585 = 124402189) B124402189
theorem B110579723 : Blo 1987435 110579723 := bstep (se 1 (by rfl) ⟨82934792, by rfl⟩ : syracuseStep 110579723 = 165869585) B165869585
theorem B73719815 : Blo 1987435 73719815 := bstep (se 1 (by rfl) ⟨55289861, by rfl⟩ : syracuseStep 73719815 = 110579723) B110579723
theorem B196586173 : Blo 1987435 196586173 := bstep (se 3 (by rfl) ⟨36859907, by rfl⟩ : syracuseStep 196586173 = 73719815) B73719815
theorem B1048459589 : Blo 1987435 1048459589 := bstep (se 4 (by rfl) ⟨98293086, by rfl⟩ : syracuseStep 1048459589 = 196586173) B196586173
theorem B698973059 : Blo 1987435 698973059 := bstep (se 1 (by rfl) ⟨524229794, by rfl⟩ : syracuseStep 698973059 = 1048459589) B1048459589
theorem B1863928157 : Blo 1987435 1863928157 := bstep (se 3 (by rfl) ⟨349486529, by rfl⟩ : syracuseStep 1863928157 = 698973059) B698973059
theorem B4970475085 : Blo 1987435 4970475085 := bstep (se 3 (by rfl) ⟨931964078, by rfl⟩ : syracuseStep 4970475085 = 1863928157) B1863928157
theorem B6627300113 : Blo 1987435 6627300113 := bstep (se 2 (by rfl) ⟨2485237542, by rfl⟩ : syracuseStep 6627300113 = 4970475085) B4970475085
theorem B4418200075 : Blo 1987435 4418200075 := bstep (se 1 (by rfl) ⟨3313650056, by rfl⟩ : syracuseStep 4418200075 = 6627300113) B6627300113
theorem B5890933433 : Blo 1987435 5890933433 := bstep (se 2 (by rfl) ⟨2209100037, by rfl⟩ : syracuseStep 5890933433 = 4418200075) B4418200075
theorem B3927288955 : Blo 1987435 3927288955 := bstep (se 1 (by rfl) ⟨2945466716, by rfl⟩ : syracuseStep 3927288955 = 5890933433) B5890933433
theorem B5236385273 : Blo 1987435 5236385273 := bstep (se 2 (by rfl) ⟨1963644477, by rfl⟩ : syracuseStep 5236385273 = 3927288955) B3927288955
theorem B3490923515 : Blo 1987435 3490923515 := bstep (se 1 (by rfl) ⟨2618192636, by rfl⟩ : syracuseStep 3490923515 = 5236385273) B5236385273
theorem B9309129373 : Blo 1987435 9309129373 := bstep (se 3 (by rfl) ⟨1745461757, by rfl⟩ : syracuseStep 9309129373 = 3490923515) B3490923515
theorem B49648689989 : Blo 1987435 49648689989 := bstep (se 4 (by rfl) ⟨4654564686, by rfl⟩ : syracuseStep 49648689989 = 9309129373) B9309129373
theorem B33099126659 : Blo 1987435 33099126659 := bstep (se 1 (by rfl) ⟨24824344994, by rfl⟩ : syracuseStep 33099126659 = 49648689989) B49648689989
theorem B22066084439 : Blo 1987435 22066084439 := bstep (se 1 (by rfl) ⟨16549563329, by rfl⟩ : syracuseStep 22066084439 = 33099126659) B33099126659
theorem B14710722959 : Blo 1987435 14710722959 := bstep (se 1 (by rfl) ⟨11033042219, by rfl⟩ : syracuseStep 14710722959 = 22066084439) B22066084439
theorem B9807148639 : Blo 1987435 9807148639 := bstep (se 1 (by rfl) ⟨7355361479, by rfl⟩ : syracuseStep 9807148639 = 14710722959) B14710722959
theorem B52304792741 : Blo 1987435 52304792741 := bstep (se 4 (by rfl) ⟨4903574319, by rfl⟩ : syracuseStep 52304792741 = 9807148639) B9807148639
theorem B34869861827 : Blo 1987435 34869861827 := bstep (se 1 (by rfl) ⟨26152396370, by rfl⟩ : syracuseStep 34869861827 = 52304792741) B52304792741
theorem B23246574551 : Blo 1987435 23246574551 := bstep (se 1 (by rfl) ⟨17434930913, by rfl⟩ : syracuseStep 23246574551 = 34869861827) B34869861827
theorem B15497716367 : Blo 1987435 15497716367 := bstep (se 1 (by rfl) ⟨11623287275, by rfl⟩ : syracuseStep 15497716367 = 23246574551) B23246574551
theorem B10331810911 : Blo 1987435 10331810911 := bstep (se 1 (by rfl) ⟨7748858183, by rfl⟩ : syracuseStep 10331810911 = 15497716367) B15497716367
theorem B13775747881 : Blo 1987435 13775747881 := bstep (se 2 (by rfl) ⟨5165905455, by rfl⟩ : syracuseStep 13775747881 = 10331810911) B10331810911
theorem B18367663841 : Blo 1987435 18367663841 := bstep (se 2 (by rfl) ⟨6887873940, by rfl⟩ : syracuseStep 18367663841 = 13775747881) B13775747881
theorem B12245109227 : Blo 1987435 12245109227 := bstep (se 1 (by rfl) ⟨9183831920, by rfl⟩ : syracuseStep 12245109227 = 18367663841) B18367663841
theorem B8163406151 : Blo 1987435 8163406151 := bstep (se 1 (by rfl) ⟨6122554613, by rfl⟩ : syracuseStep 8163406151 = 12245109227) B12245109227
theorem B5442270767 : Blo 1987435 5442270767 := bstep (se 1 (by rfl) ⟨4081703075, by rfl⟩ : syracuseStep 5442270767 = 8163406151) B8163406151
theorem B3628180511 : Blo 1987435 3628180511 := bstep (se 1 (by rfl) ⟨2721135383, by rfl⟩ : syracuseStep 3628180511 = 5442270767) B5442270767
theorem B2418787007 : Blo 1987435 2418787007 := bstep (se 1 (by rfl) ⟨1814090255, by rfl⟩ : syracuseStep 2418787007 = 3628180511) B3628180511
theorem B1612524671 : Blo 1987435 1612524671 := bstep (se 1 (by rfl) ⟨1209393503, by rfl⟩ : syracuseStep 1612524671 = 2418787007) B2418787007
theorem B1075016447 : Blo 1987435 1075016447 := bstep (se 1 (by rfl) ⟨806262335, by rfl⟩ : syracuseStep 1075016447 = 1612524671) B1612524671
theorem B716677631 : Blo 1987435 716677631 := bstep (se 1 (by rfl) ⟨537508223, by rfl⟩ : syracuseStep 716677631 = 1075016447) B1075016447
theorem B477785087 : Blo 1987435 477785087 := bstep (se 1 (by rfl) ⟨358338815, by rfl⟩ : syracuseStep 477785087 = 716677631) B716677631
theorem B318523391 : Blo 1987435 318523391 := bstep (se 1 (by rfl) ⟨238892543, by rfl⟩ : syracuseStep 318523391 = 477785087) B477785087
theorem B212348927 : Blo 1987435 212348927 := bstep (se 1 (by rfl) ⟨159261695, by rfl⟩ : syracuseStep 212348927 = 318523391) B318523391
theorem B141565951 : Blo 1987435 141565951 := bstep (se 1 (by rfl) ⟨106174463, by rfl⟩ : syracuseStep 141565951 = 212348927) B212348927
theorem B755018405 : Blo 1987435 755018405 := bstep (se 4 (by rfl) ⟨70782975, by rfl⟩ : syracuseStep 755018405 = 141565951) B141565951
theorem B503345603 : Blo 1987435 503345603 := bstep (se 1 (by rfl) ⟨377509202, by rfl⟩ : syracuseStep 503345603 = 755018405) B755018405
theorem B335563735 : Blo 1987435 335563735 := bstep (se 1 (by rfl) ⟨251672801, by rfl⟩ : syracuseStep 335563735 = 503345603) B503345603
theorem B447418313 : Blo 1987435 447418313 := bstep (se 2 (by rfl) ⟨167781867, by rfl⟩ : syracuseStep 447418313 = 335563735) B335563735
theorem B298278875 : Blo 1987435 298278875 := bstep (se 1 (by rfl) ⟨223709156, by rfl⟩ : syracuseStep 298278875 = 447418313) B447418313
theorem B198852583 : Blo 1987435 198852583 := bstep (se 1 (by rfl) ⟨149139437, by rfl⟩ : syracuseStep 198852583 = 298278875) B298278875
theorem B265136777 : Blo 1987435 265136777 := bstep (se 2 (by rfl) ⟨99426291, by rfl⟩ : syracuseStep 265136777 = 198852583) B198852583
theorem B176757851 : Blo 1987435 176757851 := bstep (se 1 (by rfl) ⟨132568388, by rfl⟩ : syracuseStep 176757851 = 265136777) B265136777
theorem B117838567 : Blo 1987435 117838567 := bstep (se 1 (by rfl) ⟨88378925, by rfl⟩ : syracuseStep 117838567 = 176757851) B176757851
theorem B157118089 : Blo 1987435 157118089 := bstep (se 2 (by rfl) ⟨58919283, by rfl⟩ : syracuseStep 157118089 = 117838567) B117838567
theorem B209490785 : Blo 1987435 209490785 := bstep (se 2 (by rfl) ⟨78559044, by rfl⟩ : syracuseStep 209490785 = 157118089) B157118089
theorem B139660523 : Blo 1987435 139660523 := bstep (se 1 (by rfl) ⟨104745392, by rfl⟩ : syracuseStep 139660523 = 209490785) B209490785
theorem B93107015 : Blo 1987435 93107015 := bstep (se 1 (by rfl) ⟨69830261, by rfl⟩ : syracuseStep 93107015 = 139660523) B139660523
theorem B62071343 : Blo 1987435 62071343 := bstep (se 1 (by rfl) ⟨46553507, by rfl⟩ : syracuseStep 62071343 = 93107015) B93107015
theorem B41380895 : Blo 1987435 41380895 := bstep (se 1 (by rfl) ⟨31035671, by rfl⟩ : syracuseStep 41380895 = 62071343) B62071343
theorem B27587263 : Blo 1987435 27587263 := bstep (se 1 (by rfl) ⟨20690447, by rfl⟩ : syracuseStep 27587263 = 41380895) B41380895
theorem B36783017 : Blo 1987435 36783017 := bstep (se 2 (by rfl) ⟨13793631, by rfl⟩ : syracuseStep 36783017 = 27587263) B27587263
theorem B24522011 : Blo 1987435 24522011 := bstep (se 1 (by rfl) ⟨18391508, by rfl⟩ : syracuseStep 24522011 = 36783017) B36783017
theorem B16348007 : Blo 1987435 16348007 := bstep (se 1 (by rfl) ⟨12261005, by rfl⟩ : syracuseStep 16348007 = 24522011) B24522011
theorem B10898671 : Blo 1987435 10898671 := bstep (se 1 (by rfl) ⟨8174003, by rfl⟩ : syracuseStep 10898671 = 16348007) B16348007
theorem B14531561 : Blo 1987435 14531561 := bstep (se 2 (by rfl) ⟨5449335, by rfl⟩ : syracuseStep 14531561 = 10898671) B10898671
theorem B9687707 : Blo 1987435 9687707 := bstep (se 1 (by rfl) ⟨7265780, by rfl⟩ : syracuseStep 9687707 = 14531561) B14531561
theorem B6458471 : Blo 1987435 6458471 := bstep (se 1 (by rfl) ⟨4843853, by rfl⟩ : syracuseStep 6458471 = 9687707) B9687707
theorem B4305647 : Blo 1987435 4305647 := bstep (se 1 (by rfl) ⟨3229235, by rfl⟩ : syracuseStep 4305647 = 6458471) B6458471
theorem B11481725 : Blo 1987435 11481725 := bstep (se 3 (by rfl) ⟨2152823, by rfl⟩ : syracuseStep 11481725 = 4305647) B4305647
theorem B7654483 : Blo 1987435 7654483 := bstep (se 1 (by rfl) ⟨5740862, by rfl⟩ : syracuseStep 7654483 = 11481725) B11481725
theorem B40823909 : Blo 1987435 40823909 := bstep (se 4 (by rfl) ⟨3827241, by rfl⟩ : syracuseStep 40823909 = 7654483) B7654483
theorem B27215939 : Blo 1987435 27215939 := bstep (se 1 (by rfl) ⟨20411954, by rfl⟩ : syracuseStep 27215939 = 40823909) B40823909
theorem B72575837 : Blo 1987435 72575837 := bstep (se 3 (by rfl) ⟨13607969, by rfl⟩ : syracuseStep 72575837 = 27215939) B27215939
theorem B48383891 : Blo 1987435 48383891 := bstep (se 1 (by rfl) ⟨36287918, by rfl⟩ : syracuseStep 48383891 = 72575837) B72575837
theorem B32255927 : Blo 1987435 32255927 := bstep (se 1 (by rfl) ⟨24191945, by rfl⟩ : syracuseStep 32255927 = 48383891) B48383891
theorem B21503951 : Blo 1987435 21503951 := bstep (se 1 (by rfl) ⟨16127963, by rfl⟩ : syracuseStep 21503951 = 32255927) B32255927
theorem B14335967 : Blo 1987435 14335967 := bstep (se 1 (by rfl) ⟨10751975, by rfl⟩ : syracuseStep 14335967 = 21503951) B21503951
theorem B9557311 : Blo 1987435 9557311 := bstep (se 1 (by rfl) ⟨7167983, by rfl⟩ : syracuseStep 9557311 = 14335967) B14335967
theorem B12743081 : Blo 1987435 12743081 := bstep (se 2 (by rfl) ⟨4778655, by rfl⟩ : syracuseStep 12743081 = 9557311) B9557311
theorem B8495387 : Blo 1987435 8495387 := bstep (se 1 (by rfl) ⟨6371540, by rfl⟩ : syracuseStep 8495387 = 12743081) B12743081
theorem B5663591 : Blo 1987435 5663591 := bstep (se 1 (by rfl) ⟨4247693, by rfl⟩ : syracuseStep 5663591 = 8495387) B8495387
theorem B3775727 : Blo 1987435 3775727 := bstep (se 1 (by rfl) ⟨2831795, by rfl⟩ : syracuseStep 3775727 = 5663591) B5663591
theorem B2517151 : Blo 1987435 2517151 := bstep (se 1 (by rfl) ⟨1887863, by rfl⟩ : syracuseStep 2517151 = 3775727) B3775727
theorem B3356201 : Blo 1987435 3356201 := bstep (se 2 (by rfl) ⟨1258575, by rfl⟩ : syracuseStep 3356201 = 2517151) B2517151
theorem B2237467 : Blo 1987435 2237467 := bstep (se 1 (by rfl) ⟨1678100, by rfl⟩ : syracuseStep 2237467 = 3356201) B3356201
theorem B2983289 : Blo 1987435 2983289 := bstep (se 2 (by rfl) ⟨1118733, by rfl⟩ : syracuseStep 2983289 = 2237467) B2237467
theorem B1988859 : Blo 1987435 1988859 := bstep (se 1 (by rfl) ⟨1491644, by rfl⟩ : syracuseStep 1988859 = 2983289) B2983289
theorem B2043505 : Blo 1987435 2043505 := bbase (se 2 (by rfl) ⟨766314, by rfl⟩ : syracuseStep 2043505 = 1532629) (by norm_num)
theorem B2724673 : Blo 1987435 2724673 := bstep (se 2 (by rfl) ⟨1021752, by rfl⟩ : syracuseStep 2724673 = 2043505) B2043505
theorem B3632897 : Blo 1987435 3632897 := bstep (se 2 (by rfl) ⟨1362336, by rfl⟩ : syracuseStep 3632897 = 2724673) B2724673
theorem B2421931 : Blo 1987435 2421931 := bstep (se 1 (by rfl) ⟨1816448, by rfl⟩ : syracuseStep 2421931 = 3632897) B3632897
theorem B3229241 : Blo 1987435 3229241 := bstep (se 2 (by rfl) ⟨1210965, by rfl⟩ : syracuseStep 3229241 = 2421931) B2421931
theorem B8611309 : Blo 1987435 8611309 := bstep (se 3 (by rfl) ⟨1614620, by rfl⟩ : syracuseStep 8611309 = 3229241) B3229241
theorem B11481745 : Blo 1987435 11481745 := bstep (se 2 (by rfl) ⟨4305654, by rfl⟩ : syracuseStep 11481745 = 8611309) B8611309
theorem B15308993 : Blo 1987435 15308993 := bstep (se 2 (by rfl) ⟨5740872, by rfl⟩ : syracuseStep 15308993 = 11481745) B11481745
theorem B10205995 : Blo 1987435 10205995 := bstep (se 1 (by rfl) ⟨7654496, by rfl⟩ : syracuseStep 10205995 = 15308993) B15308993
theorem B13607993 : Blo 1987435 13607993 := bstep (se 2 (by rfl) ⟨5102997, by rfl⟩ : syracuseStep 13607993 = 10205995) B10205995
theorem B9071995 : Blo 1987435 9071995 := bstep (se 1 (by rfl) ⟨6803996, by rfl⟩ : syracuseStep 9071995 = 13607993) B13607993
theorem B12095993 : Blo 1987435 12095993 := bstep (se 2 (by rfl) ⟨4535997, by rfl⟩ : syracuseStep 12095993 = 9071995) B9071995
theorem B32255981 : Blo 1987435 32255981 := bstep (se 3 (by rfl) ⟨6047996, by rfl⟩ : syracuseStep 32255981 = 12095993) B12095993
theorem B21503987 : Blo 1987435 21503987 := bstep (se 1 (by rfl) ⟨16127990, by rfl⟩ : syracuseStep 21503987 = 32255981) B32255981
theorem B14335991 : Blo 1987435 14335991 := bstep (se 1 (by rfl) ⟨10751993, by rfl⟩ : syracuseStep 14335991 = 21503987) B21503987
theorem B9557327 : Blo 1987435 9557327 := bstep (se 1 (by rfl) ⟨7167995, by rfl⟩ : syracuseStep 9557327 = 14335991) B14335991
theorem B6371551 : Blo 1987435 6371551 := bstep (se 1 (by rfl) ⟨4778663, by rfl⟩ : syracuseStep 6371551 = 9557327) B9557327
theorem B33981605 : Blo 1987435 33981605 := bstep (se 4 (by rfl) ⟨3185775, by rfl⟩ : syracuseStep 33981605 = 6371551) B6371551
theorem B22654403 : Blo 1987435 22654403 := bstep (se 1 (by rfl) ⟨16990802, by rfl⟩ : syracuseStep 22654403 = 33981605) B33981605
theorem B15102935 : Blo 1987435 15102935 := bstep (se 1 (by rfl) ⟨11327201, by rfl⟩ : syracuseStep 15102935 = 22654403) B22654403
theorem B10068623 : Blo 1987435 10068623 := bstep (se 1 (by rfl) ⟨7551467, by rfl⟩ : syracuseStep 10068623 = 15102935) B15102935
theorem B6712415 : Blo 1987435 6712415 := bstep (se 1 (by rfl) ⟨5034311, by rfl⟩ : syracuseStep 6712415 = 10068623) B10068623
theorem B4474943 : Blo 1987435 4474943 := bstep (se 1 (by rfl) ⟨3356207, by rfl⟩ : syracuseStep 4474943 = 6712415) B6712415
theorem B2983295 : Blo 1987435 2983295 := bstep (se 1 (by rfl) ⟨2237471, by rfl⟩ : syracuseStep 2983295 = 4474943) B4474943
theorem B1988863 : Blo 1987435 1988863 := bstep (se 1 (by rfl) ⟨1491647, by rfl⟩ : syracuseStep 1988863 = 2983295) B2983295
theorem B2983301 : Blo 1987435 2983301 := bbase (se 4 (by rfl) ⟨279684, by rfl⟩ : syracuseStep 2983301 = 559369) (by norm_num)
theorem B1988867 : Blo 1987435 1988867 := bstep (se 1 (by rfl) ⟨1491650, by rfl⟩ : syracuseStep 1988867 = 2983301) B2983301
theorem B3356221 : Blo 1987435 3356221 := bbase (se 3 (by rfl) ⟨629291, by rfl⟩ : syracuseStep 3356221 = 1258583) (by norm_num)
theorem B4474961 : Blo 1987435 4474961 := bstep (se 2 (by rfl) ⟨1678110, by rfl⟩ : syracuseStep 4474961 = 3356221) B3356221
theorem B2983307 : Blo 1987435 2983307 := bstep (se 1 (by rfl) ⟨2237480, by rfl⟩ : syracuseStep 2983307 = 4474961) B4474961
theorem B1988871 : Blo 1987435 1988871 := bstep (se 1 (by rfl) ⟨1491653, by rfl⟩ : syracuseStep 1988871 = 2983307) B2983307
theorem B2237485 : Blo 1987435 2237485 := bbase (se 3 (by rfl) ⟨419528, by rfl⟩ : syracuseStep 2237485 = 839057) (by norm_num)
theorem B2983313 : Blo 1987435 2983313 := bstep (se 2 (by rfl) ⟨1118742, by rfl⟩ : syracuseStep 2983313 = 2237485) B2237485
theorem B1988875 : Blo 1987435 1988875 := bstep (se 1 (by rfl) ⟨1491656, by rfl⟩ : syracuseStep 1988875 = 2983313) B2983313
theorem B6712469 : Blo 1987435 6712469 := bbase (se 6 (by rfl) ⟨157323, by rfl⟩ : syracuseStep 6712469 = 314647) (by norm_num)
theorem B4474979 : Blo 1987435 4474979 := bstep (se 1 (by rfl) ⟨3356234, by rfl⟩ : syracuseStep 4474979 = 6712469) B6712469
theorem B2983319 : Blo 1987435 2983319 := bstep (se 1 (by rfl) ⟨2237489, by rfl⟩ : syracuseStep 2983319 = 4474979) B4474979
theorem B1988879 : Blo 1987435 1988879 := bstep (se 1 (by rfl) ⟨1491659, by rfl⟩ : syracuseStep 1988879 = 2983319) B2983319
theorem B2983325 : Blo 1987435 2983325 := bbase (se 3 (by rfl) ⟨559373, by rfl⟩ : syracuseStep 2983325 = 1118747) (by norm_num)
theorem B1988883 : Blo 1987435 1988883 := bstep (se 1 (by rfl) ⟨1491662, by rfl⟩ : syracuseStep 1988883 = 2983325) B2983325
theorem B4474997 : Blo 1987435 4474997 := bbase (se 5 (by rfl) ⟨209765, by rfl⟩ : syracuseStep 4474997 = 419531) (by norm_num)
theorem B2983331 : Blo 1987435 2983331 := bstep (se 1 (by rfl) ⟨2237498, by rfl⟩ : syracuseStep 2983331 = 4474997) B4474997
theorem B1988887 : Blo 1987435 1988887 := bstep (se 1 (by rfl) ⟨1491665, by rfl⟩ : syracuseStep 1988887 = 2983331) B2983331
theorem B3185821 : Blo 1987435 3185821 := bbase (se 3 (by rfl) ⟨597341, by rfl⟩ : syracuseStep 3185821 = 1194683) (by norm_num)
theorem B16991045 : Blo 1987435 16991045 := bstep (se 4 (by rfl) ⟨1592910, by rfl⟩ : syracuseStep 16991045 = 3185821) B3185821
theorem B11327363 : Blo 1987435 11327363 := bstep (se 1 (by rfl) ⟨8495522, by rfl⟩ : syracuseStep 11327363 = 16991045) B16991045
theorem B7551575 : Blo 1987435 7551575 := bstep (se 1 (by rfl) ⟨5663681, by rfl⟩ : syracuseStep 7551575 = 11327363) B11327363
theorem B5034383 : Blo 1987435 5034383 := bstep (se 1 (by rfl) ⟨3775787, by rfl⟩ : syracuseStep 5034383 = 7551575) B7551575
theorem B3356255 : Blo 1987435 3356255 := bstep (se 1 (by rfl) ⟨2517191, by rfl⟩ : syracuseStep 3356255 = 5034383) B5034383
theorem B2237503 : Blo 1987435 2237503 := bstep (se 1 (by rfl) ⟨1678127, by rfl⟩ : syracuseStep 2237503 = 3356255) B3356255
theorem B2983337 : Blo 1987435 2983337 := bstep (se 2 (by rfl) ⟨1118751, by rfl⟩ : syracuseStep 2983337 = 2237503) B2237503
theorem B1988891 : Blo 1987435 1988891 := bstep (se 1 (by rfl) ⟨1491668, by rfl⟩ : syracuseStep 1988891 = 2983337) B2983337
theorem B7551589 : Blo 1987435 7551589 := bbase (se 4 (by rfl) ⟨707961, by rfl⟩ : syracuseStep 7551589 = 1415923) (by norm_num)
theorem B10068785 : Blo 1987435 10068785 := bstep (se 2 (by rfl) ⟨3775794, by rfl⟩ : syracuseStep 10068785 = 7551589) B7551589
theorem B6712523 : Blo 1987435 6712523 := bstep (se 1 (by rfl) ⟨5034392, by rfl⟩ : syracuseStep 6712523 = 10068785) B10068785
theorem B4475015 : Blo 1987435 4475015 := bstep (se 1 (by rfl) ⟨3356261, by rfl⟩ : syracuseStep 4475015 = 6712523) B6712523
theorem B2983343 : Blo 1987435 2983343 := bstep (se 1 (by rfl) ⟨2237507, by rfl⟩ : syracuseStep 2983343 = 4475015) B4475015
theorem B1988895 : Blo 1987435 1988895 := bstep (se 1 (by rfl) ⟨1491671, by rfl⟩ : syracuseStep 1988895 = 2983343) B2983343
theorem B2983349 : Blo 1987435 2983349 := bbase (se 5 (by rfl) ⟨139844, by rfl⟩ : syracuseStep 2983349 = 279689) (by norm_num)
theorem B1988899 : Blo 1987435 1988899 := bstep (se 1 (by rfl) ⟨1491674, by rfl⟩ : syracuseStep 1988899 = 2983349) B2983349
theorem B5034413 : Blo 1987435 5034413 := bbase (se 3 (by rfl) ⟨943952, by rfl⟩ : syracuseStep 5034413 = 1887905) (by norm_num)
theorem B3356275 : Blo 1987435 3356275 := bstep (se 1 (by rfl) ⟨2517206, by rfl⟩ : syracuseStep 3356275 = 5034413) B5034413
theorem B4475033 : Blo 1987435 4475033 := bstep (se 2 (by rfl) ⟨1678137, by rfl⟩ : syracuseStep 4475033 = 3356275) B3356275
theorem B2983355 : Blo 1987435 2983355 := bstep (se 1 (by rfl) ⟨2237516, by rfl⟩ : syracuseStep 2983355 = 4475033) B4475033
theorem B1988903 : Blo 1987435 1988903 := bstep (se 1 (by rfl) ⟨1491677, by rfl⟩ : syracuseStep 1988903 = 2983355) B2983355
theorem B2237521 : Blo 1987435 2237521 := bbase (se 2 (by rfl) ⟨839070, by rfl⟩ : syracuseStep 2237521 = 1678141) (by norm_num)
theorem B2983361 : Blo 1987435 2983361 := bstep (se 2 (by rfl) ⟨1118760, by rfl⟩ : syracuseStep 2983361 = 2237521) B2237521
theorem B1988907 : Blo 1987435 1988907 := bstep (se 1 (by rfl) ⟨1491680, by rfl⟩ : syracuseStep 1988907 = 2983361) B2983361
theorem B2831869 : Blo 1987435 2831869 := bbase (se 3 (by rfl) ⟨530975, by rfl⟩ : syracuseStep 2831869 = 1061951) (by norm_num)
theorem B3775825 : Blo 1987435 3775825 := bstep (se 2 (by rfl) ⟨1415934, by rfl⟩ : syracuseStep 3775825 = 2831869) B2831869
theorem B5034433 : Blo 1987435 5034433 := bstep (se 2 (by rfl) ⟨1887912, by rfl⟩ : syracuseStep 5034433 = 3775825) B3775825
theorem B6712577 : Blo 1987435 6712577 := bstep (se 2 (by rfl) ⟨2517216, by rfl⟩ : syracuseStep 6712577 = 5034433) B5034433
theorem B4475051 : Blo 1987435 4475051 := bstep (se 1 (by rfl) ⟨3356288, by rfl⟩ : syracuseStep 4475051 = 6712577) B6712577
theorem B2983367 : Blo 1987435 2983367 := bstep (se 1 (by rfl) ⟨2237525, by rfl⟩ : syracuseStep 2983367 = 4475051) B4475051
theorem B1988911 : Blo 1987435 1988911 := bstep (se 1 (by rfl) ⟨1491683, by rfl⟩ : syracuseStep 1988911 = 2983367) B2983367
theorem B2983373 : Blo 1987435 2983373 := bbase (se 3 (by rfl) ⟨559382, by rfl⟩ : syracuseStep 2983373 = 1118765) (by norm_num)
theorem B1988915 : Blo 1987435 1988915 := bstep (se 1 (by rfl) ⟨1491686, by rfl⟩ : syracuseStep 1988915 = 2983373) B2983373
theorem B4475069 : Blo 1987435 4475069 := bbase (se 3 (by rfl) ⟨839075, by rfl⟩ : syracuseStep 4475069 = 1678151) (by norm_num)
theorem B2983379 : Blo 1987435 2983379 := bstep (se 1 (by rfl) ⟨2237534, by rfl⟩ : syracuseStep 2983379 = 4475069) B4475069
theorem B1988919 : Blo 1987435 1988919 := bstep (se 1 (by rfl) ⟨1491689, by rfl⟩ : syracuseStep 1988919 = 2983379) B2983379
theorem B3356309 : Blo 1987435 3356309 := bbase (se 6 (by rfl) ⟨78663, by rfl⟩ : syracuseStep 3356309 = 157327) (by norm_num)
theorem B2237539 : Blo 1987435 2237539 := bstep (se 1 (by rfl) ⟨1678154, by rfl⟩ : syracuseStep 2237539 = 3356309) B3356309
theorem B2983385 : Blo 1987435 2983385 := bstep (se 2 (by rfl) ⟨1118769, by rfl⟩ : syracuseStep 2983385 = 2237539) B2237539
theorem B1988923 : Blo 1987435 1988923 := bstep (se 1 (by rfl) ⟨1491692, by rfl⟩ : syracuseStep 1988923 = 2983385) B2983385
theorem B2688085 : Blo 1987435 2688085 := bbase (se 8 (by rfl) ⟨15750, by rfl⟩ : syracuseStep 2688085 = 31501) (by norm_num)
theorem B14336453 : Blo 1987435 14336453 := bstep (se 4 (by rfl) ⟨1344042, by rfl⟩ : syracuseStep 14336453 = 2688085) B2688085
theorem B9557635 : Blo 1987435 9557635 := bstep (se 1 (by rfl) ⟨7168226, by rfl⟩ : syracuseStep 9557635 = 14336453) B14336453
theorem B12743513 : Blo 1987435 12743513 := bstep (se 2 (by rfl) ⟨4778817, by rfl⟩ : syracuseStep 12743513 = 9557635) B9557635
theorem B8495675 : Blo 1987435 8495675 := bstep (se 1 (by rfl) ⟨6371756, by rfl⟩ : syracuseStep 8495675 = 12743513) B12743513
theorem B5663783 : Blo 1987435 5663783 := bstep (se 1 (by rfl) ⟨4247837, by rfl⟩ : syracuseStep 5663783 = 8495675) B8495675
theorem B15103421 : Blo 1987435 15103421 := bstep (se 3 (by rfl) ⟨2831891, by rfl⟩ : syracuseStep 15103421 = 5663783) B5663783
theorem B10068947 : Blo 1987435 10068947 := bstep (se 1 (by rfl) ⟨7551710, by rfl⟩ : syracuseStep 10068947 = 15103421) B15103421
theorem B6712631 : Blo 1987435 6712631 := bstep (se 1 (by rfl) ⟨5034473, by rfl⟩ : syracuseStep 6712631 = 10068947) B10068947
theorem B4475087 : Blo 1987435 4475087 := bstep (se 1 (by rfl) ⟨3356315, by rfl⟩ : syracuseStep 4475087 = 6712631) B6712631
theorem B2983391 : Blo 1987435 2983391 := bstep (se 1 (by rfl) ⟨2237543, by rfl⟩ : syracuseStep 2983391 = 4475087) B4475087
theorem B1988927 : Blo 1987435 1988927 := bstep (se 1 (by rfl) ⟨1491695, by rfl⟩ : syracuseStep 1988927 = 2983391) B2983391
theorem B2983397 : Blo 1987435 2983397 := bbase (se 4 (by rfl) ⟨279693, by rfl⟩ : syracuseStep 2983397 = 559387) (by norm_num)
theorem B1988931 : Blo 1987435 1988931 := bstep (se 1 (by rfl) ⟨1491698, by rfl⟩ : syracuseStep 1988931 = 2983397) B2983397
theorem B6804245 : Blo 1987435 6804245 := bbase (se 6 (by rfl) ⟨159474, by rfl⟩ : syracuseStep 6804245 = 318949) (by norm_num)
theorem B4536163 : Blo 1987435 4536163 := bstep (se 1 (by rfl) ⟨3402122, by rfl⟩ : syracuseStep 4536163 = 6804245) B6804245
theorem B6048217 : Blo 1987435 6048217 := bstep (se 2 (by rfl) ⟨2268081, by rfl⟩ : syracuseStep 6048217 = 4536163) B4536163
theorem B8064289 : Blo 1987435 8064289 := bstep (se 2 (by rfl) ⟨3024108, by rfl⟩ : syracuseStep 8064289 = 6048217) B6048217
theorem B43009541 : Blo 1987435 43009541 := bstep (se 4 (by rfl) ⟨4032144, by rfl⟩ : syracuseStep 43009541 = 8064289) B8064289
theorem B28673027 : Blo 1987435 28673027 := bstep (se 1 (by rfl) ⟨21504770, by rfl⟩ : syracuseStep 28673027 = 43009541) B43009541
theorem B19115351 : Blo 1987435 19115351 := bstep (se 1 (by rfl) ⟨14336513, by rfl⟩ : syracuseStep 19115351 = 28673027) B28673027
theorem B12743567 : Blo 1987435 12743567 := bstep (se 1 (by rfl) ⟨9557675, by rfl⟩ : syracuseStep 12743567 = 19115351) B19115351
theorem B8495711 : Blo 1987435 8495711 := bstep (se 1 (by rfl) ⟨6371783, by rfl⟩ : syracuseStep 8495711 = 12743567) B12743567
theorem B5663807 : Blo 1987435 5663807 := bstep (se 1 (by rfl) ⟨4247855, by rfl⟩ : syracuseStep 5663807 = 8495711) B8495711
theorem B3775871 : Blo 1987435 3775871 := bstep (se 1 (by rfl) ⟨2831903, by rfl⟩ : syracuseStep 3775871 = 5663807) B5663807
theorem B2517247 : Blo 1987435 2517247 := bstep (se 1 (by rfl) ⟨1887935, by rfl⟩ : syracuseStep 2517247 = 3775871) B3775871
theorem B3356329 : Blo 1987435 3356329 := bstep (se 2 (by rfl) ⟨1258623, by rfl⟩ : syracuseStep 3356329 = 2517247) B2517247
theorem B4475105 : Blo 1987435 4475105 := bstep (se 2 (by rfl) ⟨1678164, by rfl⟩ : syracuseStep 4475105 = 3356329) B3356329
theorem B2983403 : Blo 1987435 2983403 := bstep (se 1 (by rfl) ⟨2237552, by rfl⟩ : syracuseStep 2983403 = 4475105) B4475105
theorem B1988935 : Blo 1987435 1988935 := bstep (se 1 (by rfl) ⟨1491701, by rfl⟩ : syracuseStep 1988935 = 2983403) B2983403
theorem B2237557 : Blo 1987435 2237557 := bbase (se 5 (by rfl) ⟨104885, by rfl⟩ : syracuseStep 2237557 = 209771) (by norm_num)
theorem B2983409 : Blo 1987435 2983409 := bstep (se 2 (by rfl) ⟨1118778, by rfl⟩ : syracuseStep 2983409 = 2237557) B2237557
theorem B1988939 : Blo 1987435 1988939 := bstep (se 1 (by rfl) ⟨1491704, by rfl⟩ : syracuseStep 1988939 = 2983409) B2983409
theorem B2517257 : Blo 1987435 2517257 := bbase (se 2 (by rfl) ⟨943971, by rfl⟩ : syracuseStep 2517257 = 1887943) (by norm_num)
theorem B6712685 : Blo 1987435 6712685 := bstep (se 3 (by rfl) ⟨1258628, by rfl⟩ : syracuseStep 6712685 = 2517257) B2517257
theorem B4475123 : Blo 1987435 4475123 := bstep (se 1 (by rfl) ⟨3356342, by rfl⟩ : syracuseStep 4475123 = 6712685) B6712685
theorem B2983415 : Blo 1987435 2983415 := bstep (se 1 (by rfl) ⟨2237561, by rfl⟩ : syracuseStep 2983415 = 4475123) B4475123
theorem B1988943 : Blo 1987435 1988943 := bstep (se 1 (by rfl) ⟨1491707, by rfl⟩ : syracuseStep 1988943 = 2983415) B2983415
theorem B2983421 : Blo 1987435 2983421 := bbase (se 3 (by rfl) ⟨559391, by rfl⟩ : syracuseStep 2983421 = 1118783) (by norm_num)
theorem B1988947 : Blo 1987435 1988947 := bstep (se 1 (by rfl) ⟨1491710, by rfl⟩ : syracuseStep 1988947 = 2983421) B2983421
theorem B4475141 : Blo 1987435 4475141 := bbase (se 4 (by rfl) ⟨419544, by rfl⟩ : syracuseStep 4475141 = 839089) (by norm_num)
theorem B2983427 : Blo 1987435 2983427 := bstep (se 1 (by rfl) ⟨2237570, by rfl⟩ : syracuseStep 2983427 = 4475141) B4475141
theorem B1988951 : Blo 1987435 1988951 := bstep (se 1 (by rfl) ⟨1491713, by rfl⟩ : syracuseStep 1988951 = 2983427) B2983427
theorem B3775909 : Blo 1987435 3775909 := bbase (se 4 (by rfl) ⟨353991, by rfl⟩ : syracuseStep 3775909 = 707983) (by norm_num)
theorem B5034545 : Blo 1987435 5034545 := bstep (se 2 (by rfl) ⟨1887954, by rfl⟩ : syracuseStep 5034545 = 3775909) B3775909
theorem B3356363 : Blo 1987435 3356363 := bstep (se 1 (by rfl) ⟨2517272, by rfl⟩ : syracuseStep 3356363 = 5034545) B5034545
theorem B2237575 : Blo 1987435 2237575 := bstep (se 1 (by rfl) ⟨1678181, by rfl⟩ : syracuseStep 2237575 = 3356363) B3356363
theorem B2983433 : Blo 1987435 2983433 := bstep (se 2 (by rfl) ⟨1118787, by rfl⟩ : syracuseStep 2983433 = 2237575) B2237575
theorem B1988955 : Blo 1987435 1988955 := bstep (se 1 (by rfl) ⟨1491716, by rfl⟩ : syracuseStep 1988955 = 2983433) B2983433
theorem B10069109 : Blo 1987435 10069109 := bbase (se 5 (by rfl) ⟨471989, by rfl⟩ : syracuseStep 10069109 = 943979) (by norm_num)
theorem B6712739 : Blo 1987435 6712739 := bstep (se 1 (by rfl) ⟨5034554, by rfl⟩ : syracuseStep 6712739 = 10069109) B10069109
theorem B4475159 : Blo 1987435 4475159 := bstep (se 1 (by rfl) ⟨3356369, by rfl⟩ : syracuseStep 4475159 = 6712739) B6712739
theorem B2983439 : Blo 1987435 2983439 := bstep (se 1 (by rfl) ⟨2237579, by rfl⟩ : syracuseStep 2983439 = 4475159) B4475159
theorem B1988959 : Blo 1987435 1988959 := bstep (se 1 (by rfl) ⟨1491719, by rfl⟩ : syracuseStep 1988959 = 2983439) B2983439
theorem B2983445 : Blo 1987435 2983445 := bbase (se 6 (by rfl) ⟨69924, by rfl⟩ : syracuseStep 2983445 = 139849) (by norm_num)
theorem B1988963 : Blo 1987435 1988963 := bstep (se 1 (by rfl) ⟨1491722, by rfl⟩ : syracuseStep 1988963 = 2983445) B2983445
theorem B2389457 : Blo 1987435 2389457 := bbase (se 2 (by rfl) ⟨896046, by rfl⟩ : syracuseStep 2389457 = 1792093) (by norm_num)
theorem B6371885 : Blo 1987435 6371885 := bstep (se 3 (by rfl) ⟨1194728, by rfl⟩ : syracuseStep 6371885 = 2389457) B2389457
theorem B16991693 : Blo 1987435 16991693 := bstep (se 3 (by rfl) ⟨3185942, by rfl⟩ : syracuseStep 16991693 = 6371885) B6371885
theorem B11327795 : Blo 1987435 11327795 := bstep (se 1 (by rfl) ⟨8495846, by rfl⟩ : syracuseStep 11327795 = 16991693) B16991693
theorem B7551863 : Blo 1987435 7551863 := bstep (se 1 (by rfl) ⟨5663897, by rfl⟩ : syracuseStep 7551863 = 11327795) B11327795
theorem B5034575 : Blo 1987435 5034575 := bstep (se 1 (by rfl) ⟨3775931, by rfl⟩ : syracuseStep 5034575 = 7551863) B7551863
theorem B3356383 : Blo 1987435 3356383 := bstep (se 1 (by rfl) ⟨2517287, by rfl⟩ : syracuseStep 3356383 = 5034575) B5034575
theorem B4475177 : Blo 1987435 4475177 := bstep (se 2 (by rfl) ⟨1678191, by rfl⟩ : syracuseStep 4475177 = 3356383) B3356383
theorem B2983451 : Blo 1987435 2983451 := bstep (se 1 (by rfl) ⟨2237588, by rfl⟩ : syracuseStep 2983451 = 4475177) B4475177
theorem B1988967 : Blo 1987435 1988967 := bstep (se 1 (by rfl) ⟨1491725, by rfl⟩ : syracuseStep 1988967 = 2983451) B2983451
theorem B2237593 : Blo 1987435 2237593 := bbase (se 2 (by rfl) ⟨839097, by rfl⟩ : syracuseStep 2237593 = 1678195) (by norm_num)
theorem B2983457 : Blo 1987435 2983457 := bstep (se 2 (by rfl) ⟨1118796, by rfl⟩ : syracuseStep 2983457 = 2237593) B2237593
theorem B1988971 : Blo 1987435 1988971 := bstep (se 1 (by rfl) ⟨1491728, by rfl⟩ : syracuseStep 1988971 = 2983457) B2983457
theorem B7551893 : Blo 1987435 7551893 := bbase (se 6 (by rfl) ⟨176997, by rfl⟩ : syracuseStep 7551893 = 353995) (by norm_num)
theorem B5034595 : Blo 1987435 5034595 := bstep (se 1 (by rfl) ⟨3775946, by rfl⟩ : syracuseStep 5034595 = 7551893) B7551893
theorem B6712793 : Blo 1987435 6712793 := bstep (se 2 (by rfl) ⟨2517297, by rfl⟩ : syracuseStep 6712793 = 5034595) B5034595
theorem B4475195 : Blo 1987435 4475195 := bstep (se 1 (by rfl) ⟨3356396, by rfl⟩ : syracuseStep 4475195 = 6712793) B6712793
theorem B2983463 : Blo 1987435 2983463 := bstep (se 1 (by rfl) ⟨2237597, by rfl⟩ : syracuseStep 2983463 = 4475195) B4475195
theorem B1988975 : Blo 1987435 1988975 := bstep (se 1 (by rfl) ⟨1491731, by rfl⟩ : syracuseStep 1988975 = 2983463) B2983463
theorem B2983469 : Blo 1987435 2983469 := bbase (se 3 (by rfl) ⟨559400, by rfl⟩ : syracuseStep 2983469 = 1118801) (by norm_num)
theorem B1988979 : Blo 1987435 1988979 := bstep (se 1 (by rfl) ⟨1491734, by rfl⟩ : syracuseStep 1988979 = 2983469) B2983469
theorem B4475213 : Blo 1987435 4475213 := bbase (se 3 (by rfl) ⟨839102, by rfl⟩ : syracuseStep 4475213 = 1678205) (by norm_num)
theorem B2983475 : Blo 1987435 2983475 := bstep (se 1 (by rfl) ⟨2237606, by rfl⟩ : syracuseStep 2983475 = 4475213) B4475213
theorem B1988983 : Blo 1987435 1988983 := bstep (se 1 (by rfl) ⟨1491737, by rfl⟩ : syracuseStep 1988983 = 2983475) B2983475
theorem B2517313 : Blo 1987435 2517313 := bbase (se 2 (by rfl) ⟨943992, by rfl⟩ : syracuseStep 2517313 = 1887985) (by norm_num)
theorem B3356417 : Blo 1987435 3356417 := bstep (se 2 (by rfl) ⟨1258656, by rfl⟩ : syracuseStep 3356417 = 2517313) B2517313
theorem B2237611 : Blo 1987435 2237611 := bstep (se 1 (by rfl) ⟨1678208, by rfl⟩ : syracuseStep 2237611 = 3356417) B3356417
theorem B2983481 : Blo 1987435 2983481 := bstep (se 2 (by rfl) ⟨1118805, by rfl⟩ : syracuseStep 2983481 = 2237611) B2237611
theorem B1988987 : Blo 1987435 1988987 := bstep (se 1 (by rfl) ⟨1491740, by rfl⟩ : syracuseStep 1988987 = 2983481) B2983481
theorem B3185981 : Blo 1987435 3185981 := bbase (se 3 (by rfl) ⟨597371, by rfl⟩ : syracuseStep 3185981 = 1194743) (by norm_num)
theorem B2123987 : Blo 1987435 2123987 := bstep (se 1 (by rfl) ⟨1592990, by rfl⟩ : syracuseStep 2123987 = 3185981) B3185981
theorem B22655861 : Blo 1987435 22655861 := bstep (se 5 (by rfl) ⟨1061993, by rfl⟩ : syracuseStep 22655861 = 2123987) B2123987
theorem B15103907 : Blo 1987435 15103907 := bstep (se 1 (by rfl) ⟨11327930, by rfl⟩ : syracuseStep 15103907 = 22655861) B22655861
theorem B10069271 : Blo 1987435 10069271 := bstep (se 1 (by rfl) ⟨7551953, by rfl⟩ : syracuseStep 10069271 = 15103907) B15103907
theorem B6712847 : Blo 1987435 6712847 := bstep (se 1 (by rfl) ⟨5034635, by rfl⟩ : syracuseStep 6712847 = 10069271) B10069271
theorem B4475231 : Blo 1987435 4475231 := bstep (se 1 (by rfl) ⟨3356423, by rfl⟩ : syracuseStep 4475231 = 6712847) B6712847
theorem B2983487 : Blo 1987435 2983487 := bstep (se 1 (by rfl) ⟨2237615, by rfl⟩ : syracuseStep 2983487 = 4475231) B4475231
theorem B1988991 : Blo 1987435 1988991 := bstep (se 1 (by rfl) ⟨1491743, by rfl⟩ : syracuseStep 1988991 = 2983487) B2983487
theorem B2983493 : Blo 1987435 2983493 := bbase (se 4 (by rfl) ⟨279702, by rfl⟩ : syracuseStep 2983493 = 559405) (by norm_num)
theorem B1988995 : Blo 1987435 1988995 := bstep (se 1 (by rfl) ⟨1491746, by rfl⟩ : syracuseStep 1988995 = 2983493) B2983493
theorem B3356437 : Blo 1987435 3356437 := bbase (se 6 (by rfl) ⟨78666, by rfl⟩ : syracuseStep 3356437 = 157333) (by norm_num)
theorem B4475249 : Blo 1987435 4475249 := bstep (se 2 (by rfl) ⟨1678218, by rfl⟩ : syracuseStep 4475249 = 3356437) B3356437
theorem B2983499 : Blo 1987435 2983499 := bstep (se 1 (by rfl) ⟨2237624, by rfl⟩ : syracuseStep 2983499 = 4475249) B4475249
theorem B1988999 : Blo 1987435 1988999 := bstep (se 1 (by rfl) ⟨1491749, by rfl⟩ : syracuseStep 1988999 = 2983499) B2983499
theorem B2237629 : Blo 1987435 2237629 := bbase (se 3 (by rfl) ⟨419555, by rfl⟩ : syracuseStep 2237629 = 839111) (by norm_num)
theorem B2983505 : Blo 1987435 2983505 := bstep (se 2 (by rfl) ⟨1118814, by rfl⟩ : syracuseStep 2983505 = 2237629) B2237629
theorem B1989003 : Blo 1987435 1989003 := bstep (se 1 (by rfl) ⟨1491752, by rfl⟩ : syracuseStep 1989003 = 2983505) B2983505
theorem B6712901 : Blo 1987435 6712901 := bbase (se 4 (by rfl) ⟨629334, by rfl⟩ : syracuseStep 6712901 = 1258669) (by norm_num)
theorem B4475267 : Blo 1987435 4475267 := bstep (se 1 (by rfl) ⟨3356450, by rfl⟩ : syracuseStep 4475267 = 6712901) B6712901
theorem B2983511 : Blo 1987435 2983511 := bstep (se 1 (by rfl) ⟨2237633, by rfl⟩ : syracuseStep 2983511 = 4475267) B4475267
theorem B1989007 : Blo 1987435 1989007 := bstep (se 1 (by rfl) ⟨1491755, by rfl⟩ : syracuseStep 1989007 = 2983511) B2983511
theorem B2983517 : Blo 1987435 2983517 := bbase (se 3 (by rfl) ⟨559409, by rfl⟩ : syracuseStep 2983517 = 1118819) (by norm_num)
theorem B1989011 : Blo 1987435 1989011 := bstep (se 1 (by rfl) ⟨1491758, by rfl⟩ : syracuseStep 1989011 = 2983517) B2983517
theorem B4475285 : Blo 1987435 4475285 := bbase (se 6 (by rfl) ⟨104889, by rfl⟩ : syracuseStep 4475285 = 209779) (by norm_num)
theorem B2983523 : Blo 1987435 2983523 := bstep (se 1 (by rfl) ⟨2237642, by rfl⟩ : syracuseStep 2983523 = 4475285) B4475285
theorem B1989015 : Blo 1987435 1989015 := bstep (se 1 (by rfl) ⟨1491761, by rfl⟩ : syracuseStep 1989015 = 2983523) B2983523
theorem B6372053 : Blo 1987435 6372053 := bbase (se 7 (by rfl) ⟨74672, by rfl⟩ : syracuseStep 6372053 = 149345) (by norm_num)
theorem B4248035 : Blo 1987435 4248035 := bstep (se 1 (by rfl) ⟨3186026, by rfl⟩ : syracuseStep 4248035 = 6372053) B6372053
theorem B2832023 : Blo 1987435 2832023 := bstep (se 1 (by rfl) ⟨2124017, by rfl⟩ : syracuseStep 2832023 = 4248035) B4248035
theorem B7552061 : Blo 1987435 7552061 := bstep (se 3 (by rfl) ⟨1416011, by rfl⟩ : syracuseStep 7552061 = 2832023) B2832023
theorem B5034707 : Blo 1987435 5034707 := bstep (se 1 (by rfl) ⟨3776030, by rfl⟩ : syracuseStep 5034707 = 7552061) B7552061
theorem B3356471 : Blo 1987435 3356471 := bstep (se 1 (by rfl) ⟨2517353, by rfl⟩ : syracuseStep 3356471 = 5034707) B5034707
theorem B2237647 : Blo 1987435 2237647 := bstep (se 1 (by rfl) ⟨1678235, by rfl⟩ : syracuseStep 2237647 = 3356471) B3356471
theorem B2983529 : Blo 1987435 2983529 := bstep (se 2 (by rfl) ⟨1118823, by rfl⟩ : syracuseStep 2983529 = 2237647) B2237647
theorem B1989019 : Blo 1987435 1989019 := bstep (se 1 (by rfl) ⟨1491764, by rfl⟩ : syracuseStep 1989019 = 2983529) B2983529
theorem B8496085 : Blo 1987435 8496085 := bbase (se 7 (by rfl) ⟨99563, by rfl⟩ : syracuseStep 8496085 = 199127) (by norm_num)
theorem B11328113 : Blo 1987435 11328113 := bstep (se 2 (by rfl) ⟨4248042, by rfl⟩ : syracuseStep 11328113 = 8496085) B8496085
theorem B7552075 : Blo 1987435 7552075 := bstep (se 1 (by rfl) ⟨5664056, by rfl⟩ : syracuseStep 7552075 = 11328113) B11328113
theorem B10069433 : Blo 1987435 10069433 := bstep (se 2 (by rfl) ⟨3776037, by rfl⟩ : syracuseStep 10069433 = 7552075) B7552075
theorem B6712955 : Blo 1987435 6712955 := bstep (se 1 (by rfl) ⟨5034716, by rfl⟩ : syracuseStep 6712955 = 10069433) B10069433
theorem B4475303 : Blo 1987435 4475303 := bstep (se 1 (by rfl) ⟨3356477, by rfl⟩ : syracuseStep 4475303 = 6712955) B6712955
theorem B2983535 : Blo 1987435 2983535 := bstep (se 1 (by rfl) ⟨2237651, by rfl⟩ : syracuseStep 2983535 = 4475303) B4475303
theorem B1989023 : Blo 1987435 1989023 := bstep (se 1 (by rfl) ⟨1491767, by rfl⟩ : syracuseStep 1989023 = 2983535) B2983535
theorem B2983541 : Blo 1987435 2983541 := bbase (se 5 (by rfl) ⟨139853, by rfl⟩ : syracuseStep 2983541 = 279707) (by norm_num)
theorem B1989027 : Blo 1987435 1989027 := bstep (se 1 (by rfl) ⟨1491770, by rfl⟩ : syracuseStep 1989027 = 2983541) B2983541
theorem B3776053 : Blo 1987435 3776053 := bbase (se 5 (by rfl) ⟨177002, by rfl⟩ : syracuseStep 3776053 = 354005) (by norm_num)
theorem B5034737 : Blo 1987435 5034737 := bstep (se 2 (by rfl) ⟨1888026, by rfl⟩ : syracuseStep 5034737 = 3776053) B3776053
theorem B3356491 : Blo 1987435 3356491 := bstep (se 1 (by rfl) ⟨2517368, by rfl⟩ : syracuseStep 3356491 = 5034737) B5034737
theorem B4475321 : Blo 1987435 4475321 := bstep (se 2 (by rfl) ⟨1678245, by rfl⟩ : syracuseStep 4475321 = 3356491) B3356491
theorem B2983547 : Blo 1987435 2983547 := bstep (se 1 (by rfl) ⟨2237660, by rfl⟩ : syracuseStep 2983547 = 4475321) B4475321
theorem B1989031 : Blo 1987435 1989031 := bstep (se 1 (by rfl) ⟨1491773, by rfl⟩ : syracuseStep 1989031 = 2983547) B2983547
theorem B2237665 : Blo 1987435 2237665 := bbase (se 2 (by rfl) ⟨839124, by rfl⟩ : syracuseStep 2237665 = 1678249) (by norm_num)
theorem B2983553 : Blo 1987435 2983553 := bstep (se 2 (by rfl) ⟨1118832, by rfl⟩ : syracuseStep 2983553 = 2237665) B2237665
theorem B1989035 : Blo 1987435 1989035 := bstep (se 1 (by rfl) ⟨1491776, by rfl⟩ : syracuseStep 1989035 = 2983553) B2983553
theorem B5034757 : Blo 1987435 5034757 := bbase (se 4 (by rfl) ⟨472008, by rfl⟩ : syracuseStep 5034757 = 944017) (by norm_num)
theorem B6713009 : Blo 1987435 6713009 := bstep (se 2 (by rfl) ⟨2517378, by rfl⟩ : syracuseStep 6713009 = 5034757) B5034757
theorem B4475339 : Blo 1987435 4475339 := bstep (se 1 (by rfl) ⟨3356504, by rfl⟩ : syracuseStep 4475339 = 6713009) B6713009
theorem B2983559 : Blo 1987435 2983559 := bstep (se 1 (by rfl) ⟨2237669, by rfl⟩ : syracuseStep 2983559 = 4475339) B4475339
theorem B1989039 : Blo 1987435 1989039 := bstep (se 1 (by rfl) ⟨1491779, by rfl⟩ : syracuseStep 1989039 = 2983559) B2983559
theorem B2983565 : Blo 1987435 2983565 := bbase (se 3 (by rfl) ⟨559418, by rfl⟩ : syracuseStep 2983565 = 1118837) (by norm_num)
theorem B1989043 : Blo 1987435 1989043 := bstep (se 1 (by rfl) ⟨1491782, by rfl⟩ : syracuseStep 1989043 = 2983565) B2983565
theorem B4475357 : Blo 1987435 4475357 := bbase (se 3 (by rfl) ⟨839129, by rfl⟩ : syracuseStep 4475357 = 1678259) (by norm_num)
theorem B2983571 : Blo 1987435 2983571 := bstep (se 1 (by rfl) ⟨2237678, by rfl⟩ : syracuseStep 2983571 = 4475357) B4475357
theorem B1989047 : Blo 1987435 1989047 := bstep (se 1 (by rfl) ⟨1491785, by rfl⟩ : syracuseStep 1989047 = 2983571) B2983571
theorem B3356525 : Blo 1987435 3356525 := bbase (se 3 (by rfl) ⟨629348, by rfl⟩ : syracuseStep 3356525 = 1258697) (by norm_num)
theorem B2237683 : Blo 1987435 2237683 := bstep (se 1 (by rfl) ⟨1678262, by rfl⟩ : syracuseStep 2237683 = 3356525) B3356525
theorem B2983577 : Blo 1987435 2983577 := bstep (se 2 (by rfl) ⟨1118841, by rfl⟩ : syracuseStep 2983577 = 2237683) B2237683
theorem B1989051 : Blo 1987435 1989051 := bstep (se 1 (by rfl) ⟨1491788, by rfl⟩ : syracuseStep 1989051 = 2983577) B2983577
theorem B2551745 : Blo 1987435 2551745 := bbase (se 2 (by rfl) ⟨956904, by rfl⟩ : syracuseStep 2551745 = 1913809) (by norm_num)
theorem B6804653 : Blo 1987435 6804653 := bstep (se 3 (by rfl) ⟨1275872, by rfl⟩ : syracuseStep 6804653 = 2551745) B2551745
theorem B18145741 : Blo 1987435 18145741 := bstep (se 3 (by rfl) ⟨3402326, by rfl⟩ : syracuseStep 18145741 = 6804653) B6804653
theorem B24194321 : Blo 1987435 24194321 := bstep (se 2 (by rfl) ⟨9072870, by rfl⟩ : syracuseStep 24194321 = 18145741) B18145741
theorem B16129547 : Blo 1987435 16129547 := bstep (se 1 (by rfl) ⟨12097160, by rfl⟩ : syracuseStep 16129547 = 24194321) B24194321
theorem B10753031 : Blo 1987435 10753031 := bstep (se 1 (by rfl) ⟨8064773, by rfl⟩ : syracuseStep 10753031 = 16129547) B16129547
theorem B28674749 : Blo 1987435 28674749 := bstep (se 3 (by rfl) ⟨5376515, by rfl⟩ : syracuseStep 28674749 = 10753031) B10753031
theorem B19116499 : Blo 1987435 19116499 := bstep (se 1 (by rfl) ⟨14337374, by rfl⟩ : syracuseStep 19116499 = 28674749) B28674749
theorem B25488665 : Blo 1987435 25488665 := bstep (se 2 (by rfl) ⟨9558249, by rfl⟩ : syracuseStep 25488665 = 19116499) B19116499
theorem B16992443 : Blo 1987435 16992443 := bstep (se 1 (by rfl) ⟨12744332, by rfl⟩ : syracuseStep 16992443 = 25488665) B25488665
theorem B11328295 : Blo 1987435 11328295 := bstep (se 1 (by rfl) ⟨8496221, by rfl⟩ : syracuseStep 11328295 = 16992443) B16992443
theorem B15104393 : Blo 1987435 15104393 := bstep (se 2 (by rfl) ⟨5664147, by rfl⟩ : syracuseStep 15104393 = 11328295) B11328295
theorem B10069595 : Blo 1987435 10069595 := bstep (se 1 (by rfl) ⟨7552196, by rfl⟩ : syracuseStep 10069595 = 15104393) B15104393
theorem B6713063 : Blo 1987435 6713063 := bstep (se 1 (by rfl) ⟨5034797, by rfl⟩ : syracuseStep 6713063 = 10069595) B10069595
theorem B4475375 : Blo 1987435 4475375 := bstep (se 1 (by rfl) ⟨3356531, by rfl⟩ : syracuseStep 4475375 = 6713063) B6713063
theorem B2983583 : Blo 1987435 2983583 := bstep (se 1 (by rfl) ⟨2237687, by rfl⟩ : syracuseStep 2983583 = 4475375) B4475375
theorem B1989055 : Blo 1987435 1989055 := bstep (se 1 (by rfl) ⟨1491791, by rfl⟩ : syracuseStep 1989055 = 2983583) B2983583
theorem B2983589 : Blo 1987435 2983589 := bbase (se 4 (by rfl) ⟨279711, by rfl⟩ : syracuseStep 2983589 = 559423) (by norm_num)
theorem B1989059 : Blo 1987435 1989059 := bstep (se 1 (by rfl) ⟨1491794, by rfl⟩ : syracuseStep 1989059 = 2983589) B2983589
theorem B2517409 : Blo 1987435 2517409 := bbase (se 2 (by rfl) ⟨944028, by rfl⟩ : syracuseStep 2517409 = 1888057) (by norm_num)
theorem B3356545 : Blo 1987435 3356545 := bstep (se 2 (by rfl) ⟨1258704, by rfl⟩ : syracuseStep 3356545 = 2517409) B2517409
theorem B4475393 : Blo 1987435 4475393 := bstep (se 2 (by rfl) ⟨1678272, by rfl⟩ : syracuseStep 4475393 = 3356545) B3356545
theorem B2983595 : Blo 1987435 2983595 := bstep (se 1 (by rfl) ⟨2237696, by rfl⟩ : syracuseStep 2983595 = 4475393) B4475393
theorem B1989063 : Blo 1987435 1989063 := bstep (se 1 (by rfl) ⟨1491797, by rfl⟩ : syracuseStep 1989063 = 2983595) B2983595
theorem B2237701 : Blo 1987435 2237701 := bbase (se 4 (by rfl) ⟨209784, by rfl⟩ : syracuseStep 2237701 = 419569) (by norm_num)
theorem B2983601 : Blo 1987435 2983601 := bstep (se 2 (by rfl) ⟨1118850, by rfl⟩ : syracuseStep 2983601 = 2237701) B2237701
theorem B1989067 : Blo 1987435 1989067 := bstep (se 1 (by rfl) ⟨1491800, by rfl⟩ : syracuseStep 1989067 = 2983601) B2983601
theorem B2124073 : Blo 1987435 2124073 := bbase (se 2 (by rfl) ⟨796527, by rfl⟩ : syracuseStep 2124073 = 1593055) (by norm_num)
theorem B2832097 : Blo 1987435 2832097 := bstep (se 2 (by rfl) ⟨1062036, by rfl⟩ : syracuseStep 2832097 = 2124073) B2124073
theorem B3776129 : Blo 1987435 3776129 := bstep (se 2 (by rfl) ⟨1416048, by rfl⟩ : syracuseStep 3776129 = 2832097) B2832097
theorem B2517419 : Blo 1987435 2517419 := bstep (se 1 (by rfl) ⟨1888064, by rfl⟩ : syracuseStep 2517419 = 3776129) B3776129
theorem B6713117 : Blo 1987435 6713117 := bstep (se 3 (by rfl) ⟨1258709, by rfl⟩ : syracuseStep 6713117 = 2517419) B2517419
theorem B4475411 : Blo 1987435 4475411 := bstep (se 1 (by rfl) ⟨3356558, by rfl⟩ : syracuseStep 4475411 = 6713117) B6713117
theorem B2983607 : Blo 1987435 2983607 := bstep (se 1 (by rfl) ⟨2237705, by rfl⟩ : syracuseStep 2983607 = 4475411) B4475411
theorem B1989071 : Blo 1987435 1989071 := bstep (se 1 (by rfl) ⟨1491803, by rfl⟩ : syracuseStep 1989071 = 2983607) B2983607
theorem B2983613 : Blo 1987435 2983613 := bbase (se 3 (by rfl) ⟨559427, by rfl⟩ : syracuseStep 2983613 = 1118855) (by norm_num)
theorem B1989075 : Blo 1987435 1989075 := bstep (se 1 (by rfl) ⟨1491806, by rfl⟩ : syracuseStep 1989075 = 2983613) B2983613
theorem B4475429 : Blo 1987435 4475429 := bbase (se 4 (by rfl) ⟨419571, by rfl⟩ : syracuseStep 4475429 = 839143) (by norm_num)
theorem B2983619 : Blo 1987435 2983619 := bstep (se 1 (by rfl) ⟨2237714, by rfl⟩ : syracuseStep 2983619 = 4475429) B4475429
theorem B1989079 : Blo 1987435 1989079 := bstep (se 1 (by rfl) ⟨1491809, by rfl⟩ : syracuseStep 1989079 = 2983619) B2983619
theorem B5034869 : Blo 1987435 5034869 := bbase (se 5 (by rfl) ⟨236009, by rfl⟩ : syracuseStep 5034869 = 472019) (by norm_num)
theorem B3356579 : Blo 1987435 3356579 := bstep (se 1 (by rfl) ⟨2517434, by rfl⟩ : syracuseStep 3356579 = 5034869) B5034869
theorem B2237719 : Blo 1987435 2237719 := bstep (se 1 (by rfl) ⟨1678289, by rfl⟩ : syracuseStep 2237719 = 3356579) B3356579
theorem B2983625 : Blo 1987435 2983625 := bstep (se 2 (by rfl) ⟨1118859, by rfl⟩ : syracuseStep 2983625 = 2237719) B2237719
theorem B1989083 : Blo 1987435 1989083 := bstep (se 1 (by rfl) ⟨1491812, by rfl⟩ : syracuseStep 1989083 = 2983625) B2983625
theorem B9196805 : Blo 1987435 9196805 := bbase (se 4 (by rfl) ⟨862200, by rfl⟩ : syracuseStep 9196805 = 1724401) (by norm_num)
theorem B24524813 : Blo 1987435 24524813 := bstep (se 3 (by rfl) ⟨4598402, by rfl⟩ : syracuseStep 24524813 = 9196805) B9196805
theorem B65399501 : Blo 1987435 65399501 := bstep (se 3 (by rfl) ⟨12262406, by rfl⟩ : syracuseStep 65399501 = 24524813) B24524813
theorem B43599667 : Blo 1987435 43599667 := bstep (se 1 (by rfl) ⟨32699750, by rfl⟩ : syracuseStep 43599667 = 65399501) B65399501
theorem B58132889 : Blo 1987435 58132889 := bstep (se 2 (by rfl) ⟨21799833, by rfl⟩ : syracuseStep 58132889 = 43599667) B43599667
theorem B38755259 : Blo 1987435 38755259 := bstep (se 1 (by rfl) ⟨29066444, by rfl⟩ : syracuseStep 38755259 = 58132889) B58132889
theorem B25836839 : Blo 1987435 25836839 := bstep (se 1 (by rfl) ⟨19377629, by rfl⟩ : syracuseStep 25836839 = 38755259) B38755259
theorem B17224559 : Blo 1987435 17224559 := bstep (se 1 (by rfl) ⟨12918419, by rfl⟩ : syracuseStep 17224559 = 25836839) B25836839
theorem B11483039 : Blo 1987435 11483039 := bstep (se 1 (by rfl) ⟨8612279, by rfl⟩ : syracuseStep 11483039 = 17224559) B17224559
theorem B7655359 : Blo 1987435 7655359 := bstep (se 1 (by rfl) ⟨5741519, by rfl⟩ : syracuseStep 7655359 = 11483039) B11483039
theorem B10207145 : Blo 1987435 10207145 := bstep (se 2 (by rfl) ⟨3827679, by rfl⟩ : syracuseStep 10207145 = 7655359) B7655359
theorem B27219053 : Blo 1987435 27219053 := bstep (se 3 (by rfl) ⟨5103572, by rfl⟩ : syracuseStep 27219053 = 10207145) B10207145
theorem B18146035 : Blo 1987435 18146035 := bstep (se 1 (by rfl) ⟨13609526, by rfl⟩ : syracuseStep 18146035 = 27219053) B27219053
theorem B24194713 : Blo 1987435 24194713 := bstep (se 2 (by rfl) ⟨9073017, by rfl⟩ : syracuseStep 24194713 = 18146035) B18146035
theorem B32259617 : Blo 1987435 32259617 := bstep (se 2 (by rfl) ⟨12097356, by rfl⟩ : syracuseStep 32259617 = 24194713) B24194713
theorem B21506411 : Blo 1987435 21506411 := bstep (se 1 (by rfl) ⟨16129808, by rfl⟩ : syracuseStep 21506411 = 32259617) B32259617
theorem B14337607 : Blo 1987435 14337607 := bstep (se 1 (by rfl) ⟨10753205, by rfl⟩ : syracuseStep 14337607 = 21506411) B21506411
theorem B19116809 : Blo 1987435 19116809 := bstep (se 2 (by rfl) ⟨7168803, by rfl⟩ : syracuseStep 19116809 = 14337607) B14337607
theorem B12744539 : Blo 1987435 12744539 := bstep (se 1 (by rfl) ⟨9558404, by rfl⟩ : syracuseStep 12744539 = 19116809) B19116809
theorem B8496359 : Blo 1987435 8496359 := bstep (se 1 (by rfl) ⟨6372269, by rfl⟩ : syracuseStep 8496359 = 12744539) B12744539
theorem B5664239 : Blo 1987435 5664239 := bstep (se 1 (by rfl) ⟨4248179, by rfl⟩ : syracuseStep 5664239 = 8496359) B8496359
theorem B3776159 : Blo 1987435 3776159 := bstep (se 1 (by rfl) ⟨2832119, by rfl⟩ : syracuseStep 3776159 = 5664239) B5664239
theorem B10069757 : Blo 1987435 10069757 := bstep (se 3 (by rfl) ⟨1888079, by rfl⟩ : syracuseStep 10069757 = 3776159) B3776159
theorem B6713171 : Blo 1987435 6713171 := bstep (se 1 (by rfl) ⟨5034878, by rfl⟩ : syracuseStep 6713171 = 10069757) B10069757
theorem B4475447 : Blo 1987435 4475447 := bstep (se 1 (by rfl) ⟨3356585, by rfl⟩ : syracuseStep 4475447 = 6713171) B6713171
theorem B2983631 : Blo 1987435 2983631 := bstep (se 1 (by rfl) ⟨2237723, by rfl⟩ : syracuseStep 2983631 = 4475447) B4475447
theorem B1989087 : Blo 1987435 1989087 := bstep (se 1 (by rfl) ⟨1491815, by rfl⟩ : syracuseStep 1989087 = 2983631) B2983631
theorem B2983637 : Blo 1987435 2983637 := bbase (se 7 (by rfl) ⟨34964, by rfl⟩ : syracuseStep 2983637 = 69929) (by norm_num)
theorem B1989091 : Blo 1987435 1989091 := bstep (se 1 (by rfl) ⟨1491818, by rfl⟩ : syracuseStep 1989091 = 2983637) B2983637
theorem B4248197 : Blo 1987435 4248197 := bbase (se 4 (by rfl) ⟨398268, by rfl⟩ : syracuseStep 4248197 = 796537) (by norm_num)
theorem B2832131 : Blo 1987435 2832131 := bstep (se 1 (by rfl) ⟨2124098, by rfl⟩ : syracuseStep 2832131 = 4248197) B4248197
theorem B7552349 : Blo 1987435 7552349 := bstep (se 3 (by rfl) ⟨1416065, by rfl⟩ : syracuseStep 7552349 = 2832131) B2832131
theorem B5034899 : Blo 1987435 5034899 := bstep (se 1 (by rfl) ⟨3776174, by rfl⟩ : syracuseStep 5034899 = 7552349) B7552349
theorem B3356599 : Blo 1987435 3356599 := bstep (se 1 (by rfl) ⟨2517449, by rfl⟩ : syracuseStep 3356599 = 5034899) B5034899
theorem B4475465 : Blo 1987435 4475465 := bstep (se 2 (by rfl) ⟨1678299, by rfl⟩ : syracuseStep 4475465 = 3356599) B3356599
theorem B2983643 : Blo 1987435 2983643 := bstep (se 1 (by rfl) ⟨2237732, by rfl⟩ : syracuseStep 2983643 = 4475465) B4475465
theorem B1989095 : Blo 1987435 1989095 := bstep (se 1 (by rfl) ⟨1491821, by rfl⟩ : syracuseStep 1989095 = 2983643) B2983643
theorem B2237737 : Blo 1987435 2237737 := bbase (se 2 (by rfl) ⟨839151, by rfl⟩ : syracuseStep 2237737 = 1678303) (by norm_num)
theorem B2983649 : Blo 1987435 2983649 := bstep (se 2 (by rfl) ⟨1118868, by rfl⟩ : syracuseStep 2983649 = 2237737) B2237737
theorem B1989099 : Blo 1987435 1989099 := bstep (se 1 (by rfl) ⟨1491824, by rfl⟩ : syracuseStep 1989099 = 2983649) B2983649
theorem B4032485 : Blo 1987435 4032485 := bbase (se 4 (by rfl) ⟨378045, by rfl⟩ : syracuseStep 4032485 = 756091) (by norm_num)
theorem B2688323 : Blo 1987435 2688323 := bstep (se 1 (by rfl) ⟨2016242, by rfl⟩ : syracuseStep 2688323 = 4032485) B4032485
theorem B7168861 : Blo 1987435 7168861 := bstep (se 3 (by rfl) ⟨1344161, by rfl⟩ : syracuseStep 7168861 = 2688323) B2688323
theorem B9558481 : Blo 1987435 9558481 := bstep (se 2 (by rfl) ⟨3584430, by rfl⟩ : syracuseStep 9558481 = 7168861) B7168861
theorem B12744641 : Blo 1987435 12744641 := bstep (se 2 (by rfl) ⟨4779240, by rfl⟩ : syracuseStep 12744641 = 9558481) B9558481
theorem B8496427 : Blo 1987435 8496427 := bstep (se 1 (by rfl) ⟨6372320, by rfl⟩ : syracuseStep 8496427 = 12744641) B12744641
theorem B11328569 : Blo 1987435 11328569 := bstep (se 2 (by rfl) ⟨4248213, by rfl⟩ : syracuseStep 11328569 = 8496427) B8496427
theorem B7552379 : Blo 1987435 7552379 := bstep (se 1 (by rfl) ⟨5664284, by rfl⟩ : syracuseStep 7552379 = 11328569) B11328569
theorem B5034919 : Blo 1987435 5034919 := bstep (se 1 (by rfl) ⟨3776189, by rfl⟩ : syracuseStep 5034919 = 7552379) B7552379
theorem B6713225 : Blo 1987435 6713225 := bstep (se 2 (by rfl) ⟨2517459, by rfl⟩ : syracuseStep 6713225 = 5034919) B5034919
theorem B4475483 : Blo 1987435 4475483 := bstep (se 1 (by rfl) ⟨3356612, by rfl⟩ : syracuseStep 4475483 = 6713225) B6713225
theorem B2983655 : Blo 1987435 2983655 := bstep (se 1 (by rfl) ⟨2237741, by rfl⟩ : syracuseStep 2983655 = 4475483) B4475483
theorem B1989103 : Blo 1987435 1989103 := bstep (se 1 (by rfl) ⟨1491827, by rfl⟩ : syracuseStep 1989103 = 2983655) B2983655
theorem B2983661 : Blo 1987435 2983661 := bbase (se 3 (by rfl) ⟨559436, by rfl⟩ : syracuseStep 2983661 = 1118873) (by norm_num)
theorem B1989107 : Blo 1987435 1989107 := bstep (se 1 (by rfl) ⟨1491830, by rfl⟩ : syracuseStep 1989107 = 2983661) B2983661
theorem B4475501 : Blo 1987435 4475501 := bbase (se 3 (by rfl) ⟨839156, by rfl⟩ : syracuseStep 4475501 = 1678313) (by norm_num)
theorem B2983667 : Blo 1987435 2983667 := bstep (se 1 (by rfl) ⟨2237750, by rfl⟩ : syracuseStep 2983667 = 4475501) B4475501
theorem B1989111 : Blo 1987435 1989111 := bstep (se 1 (by rfl) ⟨1491833, by rfl⟩ : syracuseStep 1989111 = 2983667) B2983667
theorem B3776213 : Blo 1987435 3776213 := bbase (se 7 (by rfl) ⟨44252, by rfl⟩ : syracuseStep 3776213 = 88505) (by norm_num)
theorem B2517475 : Blo 1987435 2517475 := bstep (se 1 (by rfl) ⟨1888106, by rfl⟩ : syracuseStep 2517475 = 3776213) B3776213
theorem B3356633 : Blo 1987435 3356633 := bstep (se 2 (by rfl) ⟨1258737, by rfl⟩ : syracuseStep 3356633 = 2517475) B2517475
theorem B2237755 : Blo 1987435 2237755 := bstep (se 1 (by rfl) ⟨1678316, by rfl⟩ : syracuseStep 2237755 = 3356633) B3356633
theorem B2983673 : Blo 1987435 2983673 := bstep (se 2 (by rfl) ⟨1118877, by rfl⟩ : syracuseStep 2983673 = 2237755) B2237755
theorem B1989115 : Blo 1987435 1989115 := bstep (se 1 (by rfl) ⟨1491836, by rfl⟩ : syracuseStep 1989115 = 2983673) B2983673
theorem B4536581 : Blo 1987435 4536581 := bbase (se 4 (by rfl) ⟨425304, by rfl⟩ : syracuseStep 4536581 = 850609) (by norm_num)
theorem B12097549 : Blo 1987435 12097549 := bstep (se 3 (by rfl) ⟨2268290, by rfl⟩ : syracuseStep 12097549 = 4536581) B4536581
theorem B16130065 : Blo 1987435 16130065 := bstep (se 2 (by rfl) ⟨6048774, by rfl⟩ : syracuseStep 16130065 = 12097549) B12097549
theorem B21506753 : Blo 1987435 21506753 := bstep (se 2 (by rfl) ⟨8065032, by rfl⟩ : syracuseStep 21506753 = 16130065) B16130065
theorem B57351341 : Blo 1987435 57351341 := bstep (se 3 (by rfl) ⟨10753376, by rfl⟩ : syracuseStep 57351341 = 21506753) B21506753
theorem B38234227 : Blo 1987435 38234227 := bstep (se 1 (by rfl) ⟨28675670, by rfl⟩ : syracuseStep 38234227 = 57351341) B57351341
theorem B50978969 : Blo 1987435 50978969 := bstep (se 2 (by rfl) ⟨19117113, by rfl⟩ : syracuseStep 50978969 = 38234227) B38234227
theorem B33985979 : Blo 1987435 33985979 := bstep (se 1 (by rfl) ⟨25489484, by rfl⟩ : syracuseStep 33985979 = 50978969) B50978969
theorem B22657319 : Blo 1987435 22657319 := bstep (se 1 (by rfl) ⟨16992989, by rfl⟩ : syracuseStep 22657319 = 33985979) B33985979
theorem B15104879 : Blo 1987435 15104879 := bstep (se 1 (by rfl) ⟨11328659, by rfl⟩ : syracuseStep 15104879 = 22657319) B22657319
theorem B10069919 : Blo 1987435 10069919 := bstep (se 1 (by rfl) ⟨7552439, by rfl⟩ : syracuseStep 10069919 = 15104879) B15104879
theorem B6713279 : Blo 1987435 6713279 := bstep (se 1 (by rfl) ⟨5034959, by rfl⟩ : syracuseStep 6713279 = 10069919) B10069919
theorem B4475519 : Blo 1987435 4475519 := bstep (se 1 (by rfl) ⟨3356639, by rfl⟩ : syracuseStep 4475519 = 6713279) B6713279
theorem B2983679 : Blo 1987435 2983679 := bstep (se 1 (by rfl) ⟨2237759, by rfl⟩ : syracuseStep 2983679 = 4475519) B4475519
theorem B1989119 : Blo 1987435 1989119 := bstep (se 1 (by rfl) ⟨1491839, by rfl⟩ : syracuseStep 1989119 = 2983679) B2983679
theorem B2983685 : Blo 1987435 2983685 := bbase (se 4 (by rfl) ⟨279720, by rfl⟩ : syracuseStep 2983685 = 559441) (by norm_num)
theorem B1989123 : Blo 1987435 1989123 := bstep (se 1 (by rfl) ⟨1491842, by rfl⟩ : syracuseStep 1989123 = 2983685) B2983685
theorem B3356653 : Blo 1987435 3356653 := bbase (se 3 (by rfl) ⟨629372, by rfl⟩ : syracuseStep 3356653 = 1258745) (by norm_num)
theorem B4475537 : Blo 1987435 4475537 := bstep (se 2 (by rfl) ⟨1678326, by rfl⟩ : syracuseStep 4475537 = 3356653) B3356653
theorem B2983691 : Blo 1987435 2983691 := bstep (se 1 (by rfl) ⟨2237768, by rfl⟩ : syracuseStep 2983691 = 4475537) B4475537
theorem B1989127 : Blo 1987435 1989127 := bstep (se 1 (by rfl) ⟨1491845, by rfl⟩ : syracuseStep 1989127 = 2983691) B2983691
theorem B2237773 : Blo 1987435 2237773 := bbase (se 3 (by rfl) ⟨419582, by rfl⟩ : syracuseStep 2237773 = 839165) (by norm_num)
theorem B2983697 : Blo 1987435 2983697 := bstep (se 2 (by rfl) ⟨1118886, by rfl⟩ : syracuseStep 2983697 = 2237773) B2237773
theorem B1989131 : Blo 1987435 1989131 := bstep (se 1 (by rfl) ⟨1491848, by rfl⟩ : syracuseStep 1989131 = 2983697) B2983697
theorem B6713333 : Blo 1987435 6713333 := bbase (se 5 (by rfl) ⟨314687, by rfl⟩ : syracuseStep 6713333 = 629375) (by norm_num)
theorem B4475555 : Blo 1987435 4475555 := bstep (se 1 (by rfl) ⟨3356666, by rfl⟩ : syracuseStep 4475555 = 6713333) B6713333
theorem B2983703 : Blo 1987435 2983703 := bstep (se 1 (by rfl) ⟨2237777, by rfl⟩ : syracuseStep 2983703 = 4475555) B4475555
theorem B1989135 : Blo 1987435 1989135 := bstep (se 1 (by rfl) ⟨1491851, by rfl⟩ : syracuseStep 1989135 = 2983703) B2983703
theorem B2983709 : Blo 1987435 2983709 := bbase (se 3 (by rfl) ⟨559445, by rfl⟩ : syracuseStep 2983709 = 1118891) (by norm_num)
theorem B1989139 : Blo 1987435 1989139 := bstep (se 1 (by rfl) ⟨1491854, by rfl⟩ : syracuseStep 1989139 = 2983709) B2983709
theorem B4475573 : Blo 1987435 4475573 := bbase (se 5 (by rfl) ⟨209792, by rfl⟩ : syracuseStep 4475573 = 419585) (by norm_num)
theorem B2983715 : Blo 1987435 2983715 := bstep (se 1 (by rfl) ⟨2237786, by rfl⟩ : syracuseStep 2983715 = 4475573) B4475573
theorem B1989143 : Blo 1987435 1989143 := bstep (se 1 (by rfl) ⟨1491857, by rfl⟩ : syracuseStep 1989143 = 2983715) B2983715
theorem B11328821 : Blo 1987435 11328821 := bbase (se 5 (by rfl) ⟨531038, by rfl⟩ : syracuseStep 11328821 = 1062077) (by norm_num)
theorem B7552547 : Blo 1987435 7552547 := bstep (se 1 (by rfl) ⟨5664410, by rfl⟩ : syracuseStep 7552547 = 11328821) B11328821
theorem B5035031 : Blo 1987435 5035031 := bstep (se 1 (by rfl) ⟨3776273, by rfl⟩ : syracuseStep 5035031 = 7552547) B7552547
theorem B3356687 : Blo 1987435 3356687 := bstep (se 1 (by rfl) ⟨2517515, by rfl⟩ : syracuseStep 3356687 = 5035031) B5035031
theorem B2237791 : Blo 1987435 2237791 := bstep (se 1 (by rfl) ⟨1678343, by rfl⟩ : syracuseStep 2237791 = 3356687) B3356687
theorem B2983721 : Blo 1987435 2983721 := bstep (se 2 (by rfl) ⟨1118895, by rfl⟩ : syracuseStep 2983721 = 2237791) B2237791
theorem B1989147 : Blo 1987435 1989147 := bstep (se 1 (by rfl) ⟨1491860, by rfl⟩ : syracuseStep 1989147 = 2983721) B2983721
theorem B5664421 : Blo 1987435 5664421 := bbase (se 4 (by rfl) ⟨531039, by rfl⟩ : syracuseStep 5664421 = 1062079) (by norm_num)
theorem B7552561 : Blo 1987435 7552561 := bstep (se 2 (by rfl) ⟨2832210, by rfl⟩ : syracuseStep 7552561 = 5664421) B5664421
theorem B10070081 : Blo 1987435 10070081 := bstep (se 2 (by rfl) ⟨3776280, by rfl⟩ : syracuseStep 10070081 = 7552561) B7552561
theorem B6713387 : Blo 1987435 6713387 := bstep (se 1 (by rfl) ⟨5035040, by rfl⟩ : syracuseStep 6713387 = 10070081) B10070081
theorem B4475591 : Blo 1987435 4475591 := bstep (se 1 (by rfl) ⟨3356693, by rfl⟩ : syracuseStep 4475591 = 6713387) B6713387
theorem B2983727 : Blo 1987435 2983727 := bstep (se 1 (by rfl) ⟨2237795, by rfl⟩ : syracuseStep 2983727 = 4475591) B4475591
theorem B1989151 : Blo 1987435 1989151 := bstep (se 1 (by rfl) ⟨1491863, by rfl⟩ : syracuseStep 1989151 = 2983727) B2983727
theorem B2983733 : Blo 1987435 2983733 := bbase (se 5 (by rfl) ⟨139862, by rfl⟩ : syracuseStep 2983733 = 279725) (by norm_num)
theorem B1989155 : Blo 1987435 1989155 := bstep (se 1 (by rfl) ⟨1491866, by rfl⟩ : syracuseStep 1989155 = 2983733) B2983733
theorem B5035061 : Blo 1987435 5035061 := bbase (se 5 (by rfl) ⟨236018, by rfl⟩ : syracuseStep 5035061 = 472037) (by norm_num)
theorem B3356707 : Blo 1987435 3356707 := bstep (se 1 (by rfl) ⟨2517530, by rfl⟩ : syracuseStep 3356707 = 5035061) B5035061
theorem B4475609 : Blo 1987435 4475609 := bstep (se 2 (by rfl) ⟨1678353, by rfl⟩ : syracuseStep 4475609 = 3356707) B3356707
theorem B2983739 : Blo 1987435 2983739 := bstep (se 1 (by rfl) ⟨2237804, by rfl⟩ : syracuseStep 2983739 = 4475609) B4475609
theorem B1989159 : Blo 1987435 1989159 := bstep (se 1 (by rfl) ⟨1491869, by rfl⟩ : syracuseStep 1989159 = 2983739) B2983739
theorem B2237809 : Blo 1987435 2237809 := bbase (se 2 (by rfl) ⟨839178, by rfl⟩ : syracuseStep 2237809 = 1678357) (by norm_num)
theorem B2983745 : Blo 1987435 2983745 := bstep (se 2 (by rfl) ⟨1118904, by rfl⟩ : syracuseStep 2983745 = 2237809) B2237809
theorem B1989163 : Blo 1987435 1989163 := bstep (se 1 (by rfl) ⟨1491872, by rfl⟩ : syracuseStep 1989163 = 2983745) B2983745
theorem B7169093 : Blo 1987435 7169093 := bbase (se 4 (by rfl) ⟨672102, by rfl⟩ : syracuseStep 7169093 = 1344205) (by norm_num)
theorem B4779395 : Blo 1987435 4779395 := bstep (se 1 (by rfl) ⟨3584546, by rfl⟩ : syracuseStep 4779395 = 7169093) B7169093
theorem B3186263 : Blo 1987435 3186263 := bstep (se 1 (by rfl) ⟨2389697, by rfl⟩ : syracuseStep 3186263 = 4779395) B4779395
theorem B8496701 : Blo 1987435 8496701 := bstep (se 3 (by rfl) ⟨1593131, by rfl⟩ : syracuseStep 8496701 = 3186263) B3186263
theorem B5664467 : Blo 1987435 5664467 := bstep (se 1 (by rfl) ⟨4248350, by rfl⟩ : syracuseStep 5664467 = 8496701) B8496701
theorem B3776311 : Blo 1987435 3776311 := bstep (se 1 (by rfl) ⟨2832233, by rfl⟩ : syracuseStep 3776311 = 5664467) B5664467
theorem B5035081 : Blo 1987435 5035081 := bstep (se 2 (by rfl) ⟨1888155, by rfl⟩ : syracuseStep 5035081 = 3776311) B3776311
theorem B6713441 : Blo 1987435 6713441 := bstep (se 2 (by rfl) ⟨2517540, by rfl⟩ : syracuseStep 6713441 = 5035081) B5035081
theorem B4475627 : Blo 1987435 4475627 := bstep (se 1 (by rfl) ⟨3356720, by rfl⟩ : syracuseStep 4475627 = 6713441) B6713441
theorem B2983751 : Blo 1987435 2983751 := bstep (se 1 (by rfl) ⟨2237813, by rfl⟩ : syracuseStep 2983751 = 4475627) B4475627
theorem B1989167 : Blo 1987435 1989167 := bstep (se 1 (by rfl) ⟨1491875, by rfl⟩ : syracuseStep 1989167 = 2983751) B2983751
theorem B2983757 : Blo 1987435 2983757 := bbase (se 3 (by rfl) ⟨559454, by rfl⟩ : syracuseStep 2983757 = 1118909) (by norm_num)
theorem B1989171 : Blo 1987435 1989171 := bstep (se 1 (by rfl) ⟨1491878, by rfl⟩ : syracuseStep 1989171 = 2983757) B2983757
theorem B4475645 : Blo 1987435 4475645 := bbase (se 3 (by rfl) ⟨839183, by rfl⟩ : syracuseStep 4475645 = 1678367) (by norm_num)
theorem B2983763 : Blo 1987435 2983763 := bstep (se 1 (by rfl) ⟨2237822, by rfl⟩ : syracuseStep 2983763 = 4475645) B4475645
theorem B1989175 : Blo 1987435 1989175 := bstep (se 1 (by rfl) ⟨1491881, by rfl⟩ : syracuseStep 1989175 = 2983763) B2983763
theorem B3356741 : Blo 1987435 3356741 := bbase (se 4 (by rfl) ⟨314694, by rfl⟩ : syracuseStep 3356741 = 629389) (by norm_num)
theorem B2237827 : Blo 1987435 2237827 := bstep (se 1 (by rfl) ⟨1678370, by rfl⟩ : syracuseStep 2237827 = 3356741) B3356741
theorem B2983769 : Blo 1987435 2983769 := bstep (se 2 (by rfl) ⟨1118913, by rfl⟩ : syracuseStep 2983769 = 2237827) B2237827
theorem B1989179 : Blo 1987435 1989179 := bstep (se 1 (by rfl) ⟨1491884, by rfl⟩ : syracuseStep 1989179 = 2983769) B2983769
theorem B15105365 : Blo 1987435 15105365 := bbase (se 11 (by rfl) ⟨11063, by rfl⟩ : syracuseStep 15105365 = 22127) (by norm_num)
theorem B10070243 : Blo 1987435 10070243 := bstep (se 1 (by rfl) ⟨7552682, by rfl⟩ : syracuseStep 10070243 = 15105365) B15105365
theorem B6713495 : Blo 1987435 6713495 := bstep (se 1 (by rfl) ⟨5035121, by rfl⟩ : syracuseStep 6713495 = 10070243) B10070243
theorem B4475663 : Blo 1987435 4475663 := bstep (se 1 (by rfl) ⟨3356747, by rfl⟩ : syracuseStep 4475663 = 6713495) B6713495
theorem B2983775 : Blo 1987435 2983775 := bstep (se 1 (by rfl) ⟨2237831, by rfl⟩ : syracuseStep 2983775 = 4475663) B4475663
theorem B1989183 : Blo 1987435 1989183 := bstep (se 1 (by rfl) ⟨1491887, by rfl⟩ : syracuseStep 1989183 = 2983775) B2983775
theorem B2983781 : Blo 1987435 2983781 := bbase (se 4 (by rfl) ⟨279729, by rfl⟩ : syracuseStep 2983781 = 559459) (by norm_num)
theorem B1989187 : Blo 1987435 1989187 := bstep (se 1 (by rfl) ⟨1491890, by rfl⟩ : syracuseStep 1989187 = 2983781) B2983781
theorem B3776357 : Blo 1987435 3776357 := bbase (se 4 (by rfl) ⟨354033, by rfl⟩ : syracuseStep 3776357 = 708067) (by norm_num)
theorem B2517571 : Blo 1987435 2517571 := bstep (se 1 (by rfl) ⟨1888178, by rfl⟩ : syracuseStep 2517571 = 3776357) B3776357
theorem B3356761 : Blo 1987435 3356761 := bstep (se 2 (by rfl) ⟨1258785, by rfl⟩ : syracuseStep 3356761 = 2517571) B2517571
theorem B4475681 : Blo 1987435 4475681 := bstep (se 2 (by rfl) ⟨1678380, by rfl⟩ : syracuseStep 4475681 = 3356761) B3356761
theorem B2983787 : Blo 1987435 2983787 := bstep (se 1 (by rfl) ⟨2237840, by rfl⟩ : syracuseStep 2983787 = 4475681) B4475681
theorem B1989191 : Blo 1987435 1989191 := bstep (se 1 (by rfl) ⟨1491893, by rfl⟩ : syracuseStep 1989191 = 2983787) B2983787
theorem B2237845 : Blo 1987435 2237845 := bbase (se 6 (by rfl) ⟨52449, by rfl⟩ : syracuseStep 2237845 = 104899) (by norm_num)
theorem B2983793 : Blo 1987435 2983793 := bstep (se 2 (by rfl) ⟨1118922, by rfl⟩ : syracuseStep 2983793 = 2237845) B2237845
theorem B1989195 : Blo 1987435 1989195 := bstep (se 1 (by rfl) ⟨1491896, by rfl⟩ : syracuseStep 1989195 = 2983793) B2983793
theorem B2517581 : Blo 1987435 2517581 := bbase (se 3 (by rfl) ⟨472046, by rfl⟩ : syracuseStep 2517581 = 944093) (by norm_num)
theorem B6713549 : Blo 1987435 6713549 := bstep (se 3 (by rfl) ⟨1258790, by rfl⟩ : syracuseStep 6713549 = 2517581) B2517581
theorem B4475699 : Blo 1987435 4475699 := bstep (se 1 (by rfl) ⟨3356774, by rfl⟩ : syracuseStep 4475699 = 6713549) B6713549
theorem B2983799 : Blo 1987435 2983799 := bstep (se 1 (by rfl) ⟨2237849, by rfl⟩ : syracuseStep 2983799 = 4475699) B4475699
theorem B1989199 : Blo 1987435 1989199 := bstep (se 1 (by rfl) ⟨1491899, by rfl⟩ : syracuseStep 1989199 = 2983799) B2983799
theorem B2983805 : Blo 1987435 2983805 := bbase (se 3 (by rfl) ⟨559463, by rfl⟩ : syracuseStep 2983805 = 1118927) (by norm_num)
theorem B1989203 : Blo 1987435 1989203 := bstep (se 1 (by rfl) ⟨1491902, by rfl⟩ : syracuseStep 1989203 = 2983805) B2983805
theorem B4475717 : Blo 1987435 4475717 := bbase (se 4 (by rfl) ⟨419598, by rfl⟩ : syracuseStep 4475717 = 839197) (by norm_num)
theorem B2983811 : Blo 1987435 2983811 := bstep (se 1 (by rfl) ⟨2237858, by rfl⟩ : syracuseStep 2983811 = 4475717) B4475717
theorem B1989207 : Blo 1987435 1989207 := bstep (se 1 (by rfl) ⟨1491905, by rfl⟩ : syracuseStep 1989207 = 2983811) B2983811
theorem B4248445 : Blo 1987435 4248445 := bbase (se 3 (by rfl) ⟨796583, by rfl⟩ : syracuseStep 4248445 = 1593167) (by norm_num)
theorem B5664593 : Blo 1987435 5664593 := bstep (se 2 (by rfl) ⟨2124222, by rfl⟩ : syracuseStep 5664593 = 4248445) B4248445
theorem B3776395 : Blo 1987435 3776395 := bstep (se 1 (by rfl) ⟨2832296, by rfl⟩ : syracuseStep 3776395 = 5664593) B5664593
theorem B5035193 : Blo 1987435 5035193 := bstep (se 2 (by rfl) ⟨1888197, by rfl⟩ : syracuseStep 5035193 = 3776395) B3776395
theorem B3356795 : Blo 1987435 3356795 := bstep (se 1 (by rfl) ⟨2517596, by rfl⟩ : syracuseStep 3356795 = 5035193) B5035193
theorem B2237863 : Blo 1987435 2237863 := bstep (se 1 (by rfl) ⟨1678397, by rfl⟩ : syracuseStep 2237863 = 3356795) B3356795
theorem B2983817 : Blo 1987435 2983817 := bstep (se 2 (by rfl) ⟨1118931, by rfl⟩ : syracuseStep 2983817 = 2237863) B2237863
theorem B1989211 : Blo 1987435 1989211 := bstep (se 1 (by rfl) ⟨1491908, by rfl⟩ : syracuseStep 1989211 = 2983817) B2983817
theorem B10070405 : Blo 1987435 10070405 := bbase (se 4 (by rfl) ⟨944100, by rfl⟩ : syracuseStep 10070405 = 1888201) (by norm_num)
theorem B6713603 : Blo 1987435 6713603 := bstep (se 1 (by rfl) ⟨5035202, by rfl⟩ : syracuseStep 6713603 = 10070405) B10070405
theorem B4475735 : Blo 1987435 4475735 := bstep (se 1 (by rfl) ⟨3356801, by rfl⟩ : syracuseStep 4475735 = 6713603) B6713603
theorem B2983823 : Blo 1987435 2983823 := bstep (se 1 (by rfl) ⟨2237867, by rfl⟩ : syracuseStep 2983823 = 4475735) B4475735
theorem B1989215 : Blo 1987435 1989215 := bstep (se 1 (by rfl) ⟨1491911, by rfl⟩ : syracuseStep 1989215 = 2983823) B2983823
theorem B2983829 : Blo 1987435 2983829 := bbase (se 6 (by rfl) ⟨69933, by rfl⟩ : syracuseStep 2983829 = 139867) (by norm_num)
theorem B1989219 : Blo 1987435 1989219 := bstep (se 1 (by rfl) ⟨1491914, by rfl⟩ : syracuseStep 1989219 = 2983829) B2983829
theorem B2389765 : Blo 1987435 2389765 := bbase (se 4 (by rfl) ⟨224040, by rfl⟩ : syracuseStep 2389765 = 448081) (by norm_num)
theorem B3186353 : Blo 1987435 3186353 := bstep (se 2 (by rfl) ⟨1194882, by rfl⟩ : syracuseStep 3186353 = 2389765) B2389765
theorem B2124235 : Blo 1987435 2124235 := bstep (se 1 (by rfl) ⟨1593176, by rfl⟩ : syracuseStep 2124235 = 3186353) B3186353
theorem B11329253 : Blo 1987435 11329253 := bstep (se 4 (by rfl) ⟨1062117, by rfl⟩ : syracuseStep 11329253 = 2124235) B2124235
theorem B7552835 : Blo 1987435 7552835 := bstep (se 1 (by rfl) ⟨5664626, by rfl⟩ : syracuseStep 7552835 = 11329253) B11329253
theorem B5035223 : Blo 1987435 5035223 := bstep (se 1 (by rfl) ⟨3776417, by rfl⟩ : syracuseStep 5035223 = 7552835) B7552835
theorem B3356815 : Blo 1987435 3356815 := bstep (se 1 (by rfl) ⟨2517611, by rfl⟩ : syracuseStep 3356815 = 5035223) B5035223
theorem B4475753 : Blo 1987435 4475753 := bstep (se 2 (by rfl) ⟨1678407, by rfl⟩ : syracuseStep 4475753 = 3356815) B3356815
theorem B2983835 : Blo 1987435 2983835 := bstep (se 1 (by rfl) ⟨2237876, by rfl⟩ : syracuseStep 2983835 = 4475753) B4475753
theorem B1989223 : Blo 1987435 1989223 := bstep (se 1 (by rfl) ⟨1491917, by rfl⟩ : syracuseStep 1989223 = 2983835) B2983835
theorem B2237881 : Blo 1987435 2237881 := bbase (se 2 (by rfl) ⟨839205, by rfl⟩ : syracuseStep 2237881 = 1678411) (by norm_num)
theorem B2983841 : Blo 1987435 2983841 := bstep (se 2 (by rfl) ⟨1118940, by rfl⟩ : syracuseStep 2983841 = 2237881) B2237881
theorem B1989227 : Blo 1987435 1989227 := bstep (se 1 (by rfl) ⟨1491920, by rfl⟩ : syracuseStep 1989227 = 2983841) B2983841
theorem B3402629 : Blo 1987435 3402629 := bbase (se 4 (by rfl) ⟨318996, by rfl⟩ : syracuseStep 3402629 = 637993) (by norm_num)
theorem B2268419 : Blo 1987435 2268419 := bstep (se 1 (by rfl) ⟨1701314, by rfl⟩ : syracuseStep 2268419 = 3402629) B3402629
theorem B6049117 : Blo 1987435 6049117 := bstep (se 3 (by rfl) ⟨1134209, by rfl⟩ : syracuseStep 6049117 = 2268419) B2268419
theorem B8065489 : Blo 1987435 8065489 := bstep (se 2 (by rfl) ⟨3024558, by rfl⟩ : syracuseStep 8065489 = 6049117) B6049117
theorem B10753985 : Blo 1987435 10753985 := bstep (se 2 (by rfl) ⟨4032744, by rfl⟩ : syracuseStep 10753985 = 8065489) B8065489
theorem B7169323 : Blo 1987435 7169323 := bstep (se 1 (by rfl) ⟨5376992, by rfl⟩ : syracuseStep 7169323 = 10753985) B10753985
theorem B9559097 : Blo 1987435 9559097 := bstep (se 2 (by rfl) ⟨3584661, by rfl⟩ : syracuseStep 9559097 = 7169323) B7169323
theorem B6372731 : Blo 1987435 6372731 := bstep (se 1 (by rfl) ⟨4779548, by rfl⟩ : syracuseStep 6372731 = 9559097) B9559097
theorem B4248487 : Blo 1987435 4248487 := bstep (se 1 (by rfl) ⟨3186365, by rfl⟩ : syracuseStep 4248487 = 6372731) B6372731
theorem B5664649 : Blo 1987435 5664649 := bstep (se 2 (by rfl) ⟨2124243, by rfl⟩ : syracuseStep 5664649 = 4248487) B4248487
theorem B7552865 : Blo 1987435 7552865 := bstep (se 2 (by rfl) ⟨2832324, by rfl⟩ : syracuseStep 7552865 = 5664649) B5664649
theorem B5035243 : Blo 1987435 5035243 := bstep (se 1 (by rfl) ⟨3776432, by rfl⟩ : syracuseStep 5035243 = 7552865) B7552865
theorem B6713657 : Blo 1987435 6713657 := bstep (se 2 (by rfl) ⟨2517621, by rfl⟩ : syracuseStep 6713657 = 5035243) B5035243
theorem B4475771 : Blo 1987435 4475771 := bstep (se 1 (by rfl) ⟨3356828, by rfl⟩ : syracuseStep 4475771 = 6713657) B6713657
theorem B2983847 : Blo 1987435 2983847 := bstep (se 1 (by rfl) ⟨2237885, by rfl⟩ : syracuseStep 2983847 = 4475771) B4475771
theorem B1989231 : Blo 1987435 1989231 := bstep (se 1 (by rfl) ⟨1491923, by rfl⟩ : syracuseStep 1989231 = 2983847) B2983847
theorem B2983853 : Blo 1987435 2983853 := bbase (se 3 (by rfl) ⟨559472, by rfl⟩ : syracuseStep 2983853 = 1118945) (by norm_num)
theorem B1989235 : Blo 1987435 1989235 := bstep (se 1 (by rfl) ⟨1491926, by rfl⟩ : syracuseStep 1989235 = 2983853) B2983853
theorem B4475789 : Blo 1987435 4475789 := bbase (se 3 (by rfl) ⟨839210, by rfl⟩ : syracuseStep 4475789 = 1678421) (by norm_num)
theorem B2983859 : Blo 1987435 2983859 := bstep (se 1 (by rfl) ⟨2237894, by rfl⟩ : syracuseStep 2983859 = 4475789) B4475789
theorem B1989239 : Blo 1987435 1989239 := bstep (se 1 (by rfl) ⟨1491929, by rfl⟩ : syracuseStep 1989239 = 2983859) B2983859
theorem B2517637 : Blo 1987435 2517637 := bbase (se 4 (by rfl) ⟨236028, by rfl⟩ : syracuseStep 2517637 = 472057) (by norm_num)
theorem B3356849 : Blo 1987435 3356849 := bstep (se 2 (by rfl) ⟨1258818, by rfl⟩ : syracuseStep 3356849 = 2517637) B2517637
theorem B2237899 : Blo 1987435 2237899 := bstep (se 1 (by rfl) ⟨1678424, by rfl⟩ : syracuseStep 2237899 = 3356849) B3356849
theorem B2983865 : Blo 1987435 2983865 := bstep (se 2 (by rfl) ⟨1118949, by rfl⟩ : syracuseStep 2983865 = 2237899) B2237899
theorem B1989243 : Blo 1987435 1989243 := bstep (se 1 (by rfl) ⟨1491932, by rfl⟩ : syracuseStep 1989243 = 2983865) B2983865
theorem B2389793 : Blo 1987435 2389793 := bbase (se 2 (by rfl) ⟨896172, by rfl⟩ : syracuseStep 2389793 = 1792345) (by norm_num)
theorem B25491125 : Blo 1987435 25491125 := bstep (se 5 (by rfl) ⟨1194896, by rfl⟩ : syracuseStep 25491125 = 2389793) B2389793
theorem B16994083 : Blo 1987435 16994083 := bstep (se 1 (by rfl) ⟨12745562, by rfl⟩ : syracuseStep 16994083 = 25491125) B25491125
theorem B22658777 : Blo 1987435 22658777 := bstep (se 2 (by rfl) ⟨8497041, by rfl⟩ : syracuseStep 22658777 = 16994083) B16994083
theorem B15105851 : Blo 1987435 15105851 := bstep (se 1 (by rfl) ⟨11329388, by rfl⟩ : syracuseStep 15105851 = 22658777) B22658777
theorem B10070567 : Blo 1987435 10070567 := bstep (se 1 (by rfl) ⟨7552925, by rfl⟩ : syracuseStep 10070567 = 15105851) B15105851
theorem B6713711 : Blo 1987435 6713711 := bstep (se 1 (by rfl) ⟨5035283, by rfl⟩ : syracuseStep 6713711 = 10070567) B10070567
theorem B4475807 : Blo 1987435 4475807 := bstep (se 1 (by rfl) ⟨3356855, by rfl⟩ : syracuseStep 4475807 = 6713711) B6713711
theorem B2983871 : Blo 1987435 2983871 := bstep (se 1 (by rfl) ⟨2237903, by rfl⟩ : syracuseStep 2983871 = 4475807) B4475807
theorem B1989247 : Blo 1987435 1989247 := bstep (se 1 (by rfl) ⟨1491935, by rfl⟩ : syracuseStep 1989247 = 2983871) B2983871
theorem B2983877 : Blo 1987435 2983877 := bbase (se 4 (by rfl) ⟨279738, by rfl⟩ : syracuseStep 2983877 = 559477) (by norm_num)
theorem B1989251 : Blo 1987435 1989251 := bstep (se 1 (by rfl) ⟨1491938, by rfl⟩ : syracuseStep 1989251 = 2983877) B2983877
theorem B3356869 : Blo 1987435 3356869 := bbase (se 4 (by rfl) ⟨314706, by rfl⟩ : syracuseStep 3356869 = 629413) (by norm_num)
theorem B4475825 : Blo 1987435 4475825 := bstep (se 2 (by rfl) ⟨1678434, by rfl⟩ : syracuseStep 4475825 = 3356869) B3356869
theorem B2983883 : Blo 1987435 2983883 := bstep (se 1 (by rfl) ⟨2237912, by rfl⟩ : syracuseStep 2983883 = 4475825) B4475825
theorem B1989255 : Blo 1987435 1989255 := bstep (se 1 (by rfl) ⟨1491941, by rfl⟩ : syracuseStep 1989255 = 2983883) B2983883
theorem B2237917 : Blo 1987435 2237917 := bbase (se 3 (by rfl) ⟨419609, by rfl⟩ : syracuseStep 2237917 = 839219) (by norm_num)
theorem B2983889 : Blo 1987435 2983889 := bstep (se 2 (by rfl) ⟨1118958, by rfl⟩ : syracuseStep 2983889 = 2237917) B2237917
theorem B1989259 : Blo 1987435 1989259 := bstep (se 1 (by rfl) ⟨1491944, by rfl⟩ : syracuseStep 1989259 = 2983889) B2983889
theorem B6713765 : Blo 1987435 6713765 := bbase (se 4 (by rfl) ⟨629415, by rfl⟩ : syracuseStep 6713765 = 1258831) (by norm_num)
theorem B4475843 : Blo 1987435 4475843 := bstep (se 1 (by rfl) ⟨3356882, by rfl⟩ : syracuseStep 4475843 = 6713765) B6713765
theorem B2983895 : Blo 1987435 2983895 := bstep (se 1 (by rfl) ⟨2237921, by rfl⟩ : syracuseStep 2983895 = 4475843) B4475843
theorem B1989263 : Blo 1987435 1989263 := bstep (se 1 (by rfl) ⟨1491947, by rfl⟩ : syracuseStep 1989263 = 2983895) B2983895
theorem B2983901 : Blo 1987435 2983901 := bbase (se 3 (by rfl) ⟨559481, by rfl⟩ : syracuseStep 2983901 = 1118963) (by norm_num)
theorem B1989267 : Blo 1987435 1989267 := bstep (se 1 (by rfl) ⟨1491950, by rfl⟩ : syracuseStep 1989267 = 2983901) B2983901
theorem B4475861 : Blo 1987435 4475861 := bbase (se 7 (by rfl) ⟨52451, by rfl⟩ : syracuseStep 4475861 = 104903) (by norm_num)
theorem B2983907 : Blo 1987435 2983907 := bstep (se 1 (by rfl) ⟨2237930, by rfl⟩ : syracuseStep 2983907 = 4475861) B4475861
theorem B1989271 : Blo 1987435 1989271 := bstep (se 1 (by rfl) ⟨1491953, by rfl⟩ : syracuseStep 1989271 = 2983907) B2983907
theorem B3584741 : Blo 1987435 3584741 := bbase (se 4 (by rfl) ⟨336069, by rfl⟩ : syracuseStep 3584741 = 672139) (by norm_num)
theorem B9559309 : Blo 1987435 9559309 := bstep (se 3 (by rfl) ⟨1792370, by rfl⟩ : syracuseStep 9559309 = 3584741) B3584741
theorem B12745745 : Blo 1987435 12745745 := bstep (se 2 (by rfl) ⟨4779654, by rfl⟩ : syracuseStep 12745745 = 9559309) B9559309
theorem B8497163 : Blo 1987435 8497163 := bstep (se 1 (by rfl) ⟨6372872, by rfl⟩ : syracuseStep 8497163 = 12745745) B12745745
theorem B5664775 : Blo 1987435 5664775 := bstep (se 1 (by rfl) ⟨4248581, by rfl⟩ : syracuseStep 5664775 = 8497163) B8497163
theorem B7553033 : Blo 1987435 7553033 := bstep (se 2 (by rfl) ⟨2832387, by rfl⟩ : syracuseStep 7553033 = 5664775) B5664775
theorem B5035355 : Blo 1987435 5035355 := bstep (se 1 (by rfl) ⟨3776516, by rfl⟩ : syracuseStep 5035355 = 7553033) B7553033
theorem B3356903 : Blo 1987435 3356903 := bstep (se 1 (by rfl) ⟨2517677, by rfl⟩ : syracuseStep 3356903 = 5035355) B5035355
theorem B2237935 : Blo 1987435 2237935 := bstep (se 1 (by rfl) ⟨1678451, by rfl⟩ : syracuseStep 2237935 = 3356903) B3356903
theorem B2983913 : Blo 1987435 2983913 := bstep (se 2 (by rfl) ⟨1118967, by rfl⟩ : syracuseStep 2983913 = 2237935) B2237935
theorem B1989275 : Blo 1987435 1989275 := bstep (se 1 (by rfl) ⟨1491956, by rfl⟩ : syracuseStep 1989275 = 2983913) B2983913
theorem B16994357 : Blo 1987435 16994357 := bbase (se 5 (by rfl) ⟨796610, by rfl⟩ : syracuseStep 16994357 = 1593221) (by norm_num)
theorem B11329571 : Blo 1987435 11329571 := bstep (se 1 (by rfl) ⟨8497178, by rfl⟩ : syracuseStep 11329571 = 16994357) B16994357
theorem B7553047 : Blo 1987435 7553047 := bstep (se 1 (by rfl) ⟨5664785, by rfl⟩ : syracuseStep 7553047 = 11329571) B11329571
theorem B10070729 : Blo 1987435 10070729 := bstep (se 2 (by rfl) ⟨3776523, by rfl⟩ : syracuseStep 10070729 = 7553047) B7553047
theorem B6713819 : Blo 1987435 6713819 := bstep (se 1 (by rfl) ⟨5035364, by rfl⟩ : syracuseStep 6713819 = 10070729) B10070729
theorem B4475879 : Blo 1987435 4475879 := bstep (se 1 (by rfl) ⟨3356909, by rfl⟩ : syracuseStep 4475879 = 6713819) B6713819
theorem B2983919 : Blo 1987435 2983919 := bstep (se 1 (by rfl) ⟨2237939, by rfl⟩ : syracuseStep 2983919 = 4475879) B4475879
theorem B1989279 : Blo 1987435 1989279 := bstep (se 1 (by rfl) ⟨1491959, by rfl⟩ : syracuseStep 1989279 = 2983919) B2983919
theorem B2983925 : Blo 1987435 2983925 := bbase (se 5 (by rfl) ⟨139871, by rfl⟩ : syracuseStep 2983925 = 279743) (by norm_num)
theorem B1989283 : Blo 1987435 1989283 := bstep (se 1 (by rfl) ⟨1491962, by rfl⟩ : syracuseStep 1989283 = 2983925) B2983925
theorem B4598869 : Blo 1987435 4598869 := bbase (se 8 (by rfl) ⟨26946, by rfl⟩ : syracuseStep 4598869 = 53893) (by norm_num)
theorem B6131825 : Blo 1987435 6131825 := bstep (se 2 (by rfl) ⟨2299434, by rfl⟩ : syracuseStep 6131825 = 4598869) B4598869
theorem B4087883 : Blo 1987435 4087883 := bstep (se 1 (by rfl) ⟨3065912, by rfl⟩ : syracuseStep 4087883 = 6131825) B6131825
theorem B2725255 : Blo 1987435 2725255 := bstep (se 1 (by rfl) ⟨2043941, by rfl⟩ : syracuseStep 2725255 = 4087883) B4087883
theorem B3633673 : Blo 1987435 3633673 := bstep (se 2 (by rfl) ⟨1362627, by rfl⟩ : syracuseStep 3633673 = 2725255) B2725255
theorem B4844897 : Blo 1987435 4844897 := bstep (se 2 (by rfl) ⟨1816836, by rfl⟩ : syracuseStep 4844897 = 3633673) B3633673
theorem B3229931 : Blo 1987435 3229931 := bstep (se 1 (by rfl) ⟨2422448, by rfl⟩ : syracuseStep 3229931 = 4844897) B4844897
theorem B2153287 : Blo 1987435 2153287 := bstep (se 1 (by rfl) ⟨1614965, by rfl⟩ : syracuseStep 2153287 = 3229931) B3229931
theorem B2871049 : Blo 1987435 2871049 := bstep (se 2 (by rfl) ⟨1076643, by rfl⟩ : syracuseStep 2871049 = 2153287) B2153287
theorem B3828065 : Blo 1987435 3828065 := bstep (se 2 (by rfl) ⟨1435524, by rfl⟩ : syracuseStep 3828065 = 2871049) B2871049
theorem B40832693 : Blo 1987435 40832693 := bstep (se 5 (by rfl) ⟨1914032, by rfl⟩ : syracuseStep 40832693 = 3828065) B3828065
theorem B27221795 : Blo 1987435 27221795 := bstep (se 1 (by rfl) ⟨20416346, by rfl⟩ : syracuseStep 27221795 = 40832693) B40832693
theorem B18147863 : Blo 1987435 18147863 := bstep (se 1 (by rfl) ⟨13610897, by rfl⟩ : syracuseStep 18147863 = 27221795) B27221795
theorem B12098575 : Blo 1987435 12098575 := bstep (se 1 (by rfl) ⟨9073931, by rfl⟩ : syracuseStep 12098575 = 18147863) B18147863
theorem B16131433 : Blo 1987435 16131433 := bstep (se 2 (by rfl) ⟨6049287, by rfl⟩ : syracuseStep 16131433 = 12098575) B12098575
theorem B21508577 : Blo 1987435 21508577 := bstep (se 2 (by rfl) ⟨8065716, by rfl⟩ : syracuseStep 21508577 = 16131433) B16131433
theorem B14339051 : Blo 1987435 14339051 := bstep (se 1 (by rfl) ⟨10754288, by rfl⟩ : syracuseStep 14339051 = 21508577) B21508577
theorem B9559367 : Blo 1987435 9559367 := bstep (se 1 (by rfl) ⟨7169525, by rfl⟩ : syracuseStep 9559367 = 14339051) B14339051
theorem B6372911 : Blo 1987435 6372911 := bstep (se 1 (by rfl) ⟨4779683, by rfl⟩ : syracuseStep 6372911 = 9559367) B9559367
theorem B4248607 : Blo 1987435 4248607 := bstep (se 1 (by rfl) ⟨3186455, by rfl⟩ : syracuseStep 4248607 = 6372911) B6372911
theorem B5664809 : Blo 1987435 5664809 := bstep (se 2 (by rfl) ⟨2124303, by rfl⟩ : syracuseStep 5664809 = 4248607) B4248607
theorem B3776539 : Blo 1987435 3776539 := bstep (se 1 (by rfl) ⟨2832404, by rfl⟩ : syracuseStep 3776539 = 5664809) B5664809
theorem B5035385 : Blo 1987435 5035385 := bstep (se 2 (by rfl) ⟨1888269, by rfl⟩ : syracuseStep 5035385 = 3776539) B3776539
theorem B3356923 : Blo 1987435 3356923 := bstep (se 1 (by rfl) ⟨2517692, by rfl⟩ : syracuseStep 3356923 = 5035385) B5035385
theorem B4475897 : Blo 1987435 4475897 := bstep (se 2 (by rfl) ⟨1678461, by rfl⟩ : syracuseStep 4475897 = 3356923) B3356923
theorem B2983931 : Blo 1987435 2983931 := bstep (se 1 (by rfl) ⟨2237948, by rfl⟩ : syracuseStep 2983931 = 4475897) B4475897
theorem B1989287 : Blo 1987435 1989287 := bstep (se 1 (by rfl) ⟨1491965, by rfl⟩ : syracuseStep 1989287 = 2983931) B2983931
theorem B2237953 : Blo 1987435 2237953 := bbase (se 2 (by rfl) ⟨839232, by rfl⟩ : syracuseStep 2237953 = 1678465) (by norm_num)
theorem B2983937 : Blo 1987435 2983937 := bstep (se 2 (by rfl) ⟨1118976, by rfl⟩ : syracuseStep 2983937 = 2237953) B2237953
theorem B1989291 : Blo 1987435 1989291 := bstep (se 1 (by rfl) ⟨1491968, by rfl⟩ : syracuseStep 1989291 = 2983937) B2983937
theorem B5035405 : Blo 1987435 5035405 := bbase (se 3 (by rfl) ⟨944138, by rfl⟩ : syracuseStep 5035405 = 1888277) (by norm_num)
theorem B6713873 : Blo 1987435 6713873 := bstep (se 2 (by rfl) ⟨2517702, by rfl⟩ : syracuseStep 6713873 = 5035405) B5035405
theorem B4475915 : Blo 1987435 4475915 := bstep (se 1 (by rfl) ⟨3356936, by rfl⟩ : syracuseStep 4475915 = 6713873) B6713873
theorem B2983943 : Blo 1987435 2983943 := bstep (se 1 (by rfl) ⟨2237957, by rfl⟩ : syracuseStep 2983943 = 4475915) B4475915
theorem B1989295 : Blo 1987435 1989295 := bstep (se 1 (by rfl) ⟨1491971, by rfl⟩ : syracuseStep 1989295 = 2983943) B2983943
theorem B2983949 : Blo 1987435 2983949 := bbase (se 3 (by rfl) ⟨559490, by rfl⟩ : syracuseStep 2983949 = 1118981) (by norm_num)
theorem B1989299 : Blo 1987435 1989299 := bstep (se 1 (by rfl) ⟨1491974, by rfl⟩ : syracuseStep 1989299 = 2983949) B2983949
theorem B4475933 : Blo 1987435 4475933 := bbase (se 3 (by rfl) ⟨839237, by rfl⟩ : syracuseStep 4475933 = 1678475) (by norm_num)
theorem B2983955 : Blo 1987435 2983955 := bstep (se 1 (by rfl) ⟨2237966, by rfl⟩ : syracuseStep 2983955 = 4475933) B4475933
theorem B1989303 : Blo 1987435 1989303 := bstep (se 1 (by rfl) ⟨1491977, by rfl⟩ : syracuseStep 1989303 = 2983955) B2983955
theorem B3356957 : Blo 1987435 3356957 := bbase (se 3 (by rfl) ⟨629429, by rfl⟩ : syracuseStep 3356957 = 1258859) (by norm_num)
theorem B2237971 : Blo 1987435 2237971 := bstep (se 1 (by rfl) ⟨1678478, by rfl⟩ : syracuseStep 2237971 = 3356957) B3356957
theorem B2983961 : Blo 1987435 2983961 := bstep (se 2 (by rfl) ⟨1118985, by rfl⟩ : syracuseStep 2983961 = 2237971) B2237971
theorem B1989307 : Blo 1987435 1989307 := bstep (se 1 (by rfl) ⟨1491980, by rfl⟩ : syracuseStep 1989307 = 2983961) B2983961
theorem B12745973 : Blo 1987435 12745973 := bbase (se 5 (by rfl) ⟨597467, by rfl⟩ : syracuseStep 12745973 = 1194935) (by norm_num)
theorem B8497315 : Blo 1987435 8497315 := bstep (se 1 (by rfl) ⟨6372986, by rfl⟩ : syracuseStep 8497315 = 12745973) B12745973
theorem B11329753 : Blo 1987435 11329753 := bstep (se 2 (by rfl) ⟨4248657, by rfl⟩ : syracuseStep 11329753 = 8497315) B8497315
theorem B15106337 : Blo 1987435 15106337 := bstep (se 2 (by rfl) ⟨5664876, by rfl⟩ : syracuseStep 15106337 = 11329753) B11329753
theorem B10070891 : Blo 1987435 10070891 := bstep (se 1 (by rfl) ⟨7553168, by rfl⟩ : syracuseStep 10070891 = 15106337) B15106337
theorem B6713927 : Blo 1987435 6713927 := bstep (se 1 (by rfl) ⟨5035445, by rfl⟩ : syracuseStep 6713927 = 10070891) B10070891
theorem B4475951 : Blo 1987435 4475951 := bstep (se 1 (by rfl) ⟨3356963, by rfl⟩ : syracuseStep 4475951 = 6713927) B6713927
theorem B2983967 : Blo 1987435 2983967 := bstep (se 1 (by rfl) ⟨2237975, by rfl⟩ : syracuseStep 2983967 = 4475951) B4475951
theorem B1989311 : Blo 1987435 1989311 := bstep (se 1 (by rfl) ⟨1491983, by rfl⟩ : syracuseStep 1989311 = 2983967) B2983967
theorem B2983973 : Blo 1987435 2983973 := bbase (se 4 (by rfl) ⟨279747, by rfl⟩ : syracuseStep 2983973 = 559495) (by norm_num)
theorem B1989315 : Blo 1987435 1989315 := bstep (se 1 (by rfl) ⟨1491986, by rfl⟩ : syracuseStep 1989315 = 2983973) B2983973
theorem B2517733 : Blo 1987435 2517733 := bbase (se 4 (by rfl) ⟨236037, by rfl⟩ : syracuseStep 2517733 = 472075) (by norm_num)
theorem B3356977 : Blo 1987435 3356977 := bstep (se 2 (by rfl) ⟨1258866, by rfl⟩ : syracuseStep 3356977 = 2517733) B2517733
theorem B4475969 : Blo 1987435 4475969 := bstep (se 2 (by rfl) ⟨1678488, by rfl⟩ : syracuseStep 4475969 = 3356977) B3356977
theorem B2983979 : Blo 1987435 2983979 := bstep (se 1 (by rfl) ⟨2237984, by rfl⟩ : syracuseStep 2983979 = 4475969) B4475969
theorem B1989319 : Blo 1987435 1989319 := bstep (se 1 (by rfl) ⟨1491989, by rfl⟩ : syracuseStep 1989319 = 2983979) B2983979
theorem B2237989 : Blo 1987435 2237989 := bbase (se 4 (by rfl) ⟨209811, by rfl⟩ : syracuseStep 2237989 = 419623) (by norm_num)
theorem B2983985 : Blo 1987435 2983985 := bstep (se 2 (by rfl) ⟨1118994, by rfl⟩ : syracuseStep 2983985 = 2237989) B2237989
theorem B1989323 : Blo 1987435 1989323 := bstep (se 1 (by rfl) ⟨1491992, by rfl⟩ : syracuseStep 1989323 = 2983985) B2983985
theorem B9689989 : Blo 1987435 9689989 := bbase (se 4 (by rfl) ⟨908436, by rfl⟩ : syracuseStep 9689989 = 1816873) (by norm_num)
theorem B12919985 : Blo 1987435 12919985 := bstep (se 2 (by rfl) ⟨4844994, by rfl⟩ : syracuseStep 12919985 = 9689989) B9689989
theorem B8613323 : Blo 1987435 8613323 := bstep (se 1 (by rfl) ⟨6459992, by rfl⟩ : syracuseStep 8613323 = 12919985) B12919985
theorem B5742215 : Blo 1987435 5742215 := bstep (se 1 (by rfl) ⟨4306661, by rfl⟩ : syracuseStep 5742215 = 8613323) B8613323
theorem B3828143 : Blo 1987435 3828143 := bstep (se 1 (by rfl) ⟨2871107, by rfl⟩ : syracuseStep 3828143 = 5742215) B5742215
theorem B2552095 : Blo 1987435 2552095 := bstep (se 1 (by rfl) ⟨1914071, by rfl⟩ : syracuseStep 2552095 = 3828143) B3828143
theorem B3402793 : Blo 1987435 3402793 := bstep (se 2 (by rfl) ⟨1276047, by rfl⟩ : syracuseStep 3402793 = 2552095) B2552095
theorem B4537057 : Blo 1987435 4537057 := bstep (se 2 (by rfl) ⟨1701396, by rfl⟩ : syracuseStep 4537057 = 3402793) B3402793
theorem B6049409 : Blo 1987435 6049409 := bstep (se 2 (by rfl) ⟨2268528, by rfl⟩ : syracuseStep 6049409 = 4537057) B4537057
theorem B16131757 : Blo 1987435 16131757 := bstep (se 3 (by rfl) ⟨3024704, by rfl⟩ : syracuseStep 16131757 = 6049409) B6049409
theorem B21509009 : Blo 1987435 21509009 := bstep (se 2 (by rfl) ⟨8065878, by rfl⟩ : syracuseStep 21509009 = 16131757) B16131757
theorem B14339339 : Blo 1987435 14339339 := bstep (se 1 (by rfl) ⟨10754504, by rfl⟩ : syracuseStep 14339339 = 21509009) B21509009
theorem B9559559 : Blo 1987435 9559559 := bstep (se 1 (by rfl) ⟨7169669, by rfl⟩ : syracuseStep 9559559 = 14339339) B14339339
theorem B6373039 : Blo 1987435 6373039 := bstep (se 1 (by rfl) ⟨4779779, by rfl⟩ : syracuseStep 6373039 = 9559559) B9559559
theorem B8497385 : Blo 1987435 8497385 := bstep (se 2 (by rfl) ⟨3186519, by rfl⟩ : syracuseStep 8497385 = 6373039) B6373039
theorem B5664923 : Blo 1987435 5664923 := bstep (se 1 (by rfl) ⟨4248692, by rfl⟩ : syracuseStep 5664923 = 8497385) B8497385
theorem B3776615 : Blo 1987435 3776615 := bstep (se 1 (by rfl) ⟨2832461, by rfl⟩ : syracuseStep 3776615 = 5664923) B5664923
theorem B2517743 : Blo 1987435 2517743 := bstep (se 1 (by rfl) ⟨1888307, by rfl⟩ : syracuseStep 2517743 = 3776615) B3776615
theorem B6713981 : Blo 1987435 6713981 := bstep (se 3 (by rfl) ⟨1258871, by rfl⟩ : syracuseStep 6713981 = 2517743) B2517743
theorem B4475987 : Blo 1987435 4475987 := bstep (se 1 (by rfl) ⟨3356990, by rfl⟩ : syracuseStep 4475987 = 6713981) B6713981
theorem B2983991 : Blo 1987435 2983991 := bstep (se 1 (by rfl) ⟨2237993, by rfl⟩ : syracuseStep 2983991 = 4475987) B4475987
theorem B1989327 : Blo 1987435 1989327 := bstep (se 1 (by rfl) ⟨1491995, by rfl⟩ : syracuseStep 1989327 = 2983991) B2983991
theorem B2983997 : Blo 1987435 2983997 := bbase (se 3 (by rfl) ⟨559499, by rfl⟩ : syracuseStep 2983997 = 1118999) (by norm_num)
theorem B1989331 : Blo 1987435 1989331 := bstep (se 1 (by rfl) ⟨1491998, by rfl⟩ : syracuseStep 1989331 = 2983997) B2983997
theorem B4476005 : Blo 1987435 4476005 := bbase (se 4 (by rfl) ⟨419625, by rfl⟩ : syracuseStep 4476005 = 839251) (by norm_num)
theorem B2984003 : Blo 1987435 2984003 := bstep (se 1 (by rfl) ⟨2238002, by rfl⟩ : syracuseStep 2984003 = 4476005) B4476005
theorem B1989335 : Blo 1987435 1989335 := bstep (se 1 (by rfl) ⟨1492001, by rfl⟩ : syracuseStep 1989335 = 2984003) B2984003
theorem B5035517 : Blo 1987435 5035517 := bbase (se 3 (by rfl) ⟨944159, by rfl⟩ : syracuseStep 5035517 = 1888319) (by norm_num)
theorem B3357011 : Blo 1987435 3357011 := bstep (se 1 (by rfl) ⟨2517758, by rfl⟩ : syracuseStep 3357011 = 5035517) B5035517
theorem B2238007 : Blo 1987435 2238007 := bstep (se 1 (by rfl) ⟨1678505, by rfl⟩ : syracuseStep 2238007 = 3357011) B3357011
theorem B2984009 : Blo 1987435 2984009 := bstep (se 2 (by rfl) ⟨1119003, by rfl⟩ : syracuseStep 2984009 = 2238007) B2238007
theorem B1989339 : Blo 1987435 1989339 := bstep (se 1 (by rfl) ⟨1492004, by rfl⟩ : syracuseStep 1989339 = 2984009) B2984009
theorem B3776645 : Blo 1987435 3776645 := bbase (se 4 (by rfl) ⟨354060, by rfl⟩ : syracuseStep 3776645 = 708121) (by norm_num)
theorem B10071053 : Blo 1987435 10071053 := bstep (se 3 (by rfl) ⟨1888322, by rfl⟩ : syracuseStep 10071053 = 3776645) B3776645
theorem B6714035 : Blo 1987435 6714035 := bstep (se 1 (by rfl) ⟨5035526, by rfl⟩ : syracuseStep 6714035 = 10071053) B10071053
theorem B4476023 : Blo 1987435 4476023 := bstep (se 1 (by rfl) ⟨3357017, by rfl⟩ : syracuseStep 4476023 = 6714035) B6714035
theorem B2984015 : Blo 1987435 2984015 := bstep (se 1 (by rfl) ⟨2238011, by rfl⟩ : syracuseStep 2984015 = 4476023) B4476023
theorem B1989343 : Blo 1987435 1989343 := bstep (se 1 (by rfl) ⟨1492007, by rfl⟩ : syracuseStep 1989343 = 2984015) B2984015
theorem B2984021 : Blo 1987435 2984021 := bbase (se 8 (by rfl) ⟨17484, by rfl⟩ : syracuseStep 2984021 = 34969) (by norm_num)
theorem B1989347 : Blo 1987435 1989347 := bstep (se 1 (by rfl) ⟨1492010, by rfl⟩ : syracuseStep 1989347 = 2984021) B2984021
theorem B10208501 : Blo 1987435 10208501 := bbase (se 5 (by rfl) ⟨478523, by rfl⟩ : syracuseStep 10208501 = 957047) (by norm_num)
theorem B6805667 : Blo 1987435 6805667 := bstep (se 1 (by rfl) ⟨5104250, by rfl⟩ : syracuseStep 6805667 = 10208501) B10208501
theorem B18148445 : Blo 1987435 18148445 := bstep (se 3 (by rfl) ⟨3402833, by rfl⟩ : syracuseStep 18148445 = 6805667) B6805667
theorem B12098963 : Blo 1987435 12098963 := bstep (se 1 (by rfl) ⟨9074222, by rfl⟩ : syracuseStep 12098963 = 18148445) B18148445
theorem B8065975 : Blo 1987435 8065975 := bstep (se 1 (by rfl) ⟨6049481, by rfl⟩ : syracuseStep 8065975 = 12098963) B12098963
theorem B10754633 : Blo 1987435 10754633 := bstep (se 2 (by rfl) ⟨4032987, by rfl⟩ : syracuseStep 10754633 = 8065975) B8065975
theorem B28679021 : Blo 1987435 28679021 := bstep (se 3 (by rfl) ⟨5377316, by rfl⟩ : syracuseStep 28679021 = 10754633) B10754633
theorem B19119347 : Blo 1987435 19119347 := bstep (se 1 (by rfl) ⟨14339510, by rfl⟩ : syracuseStep 19119347 = 28679021) B28679021
theorem B12746231 : Blo 1987435 12746231 := bstep (se 1 (by rfl) ⟨9559673, by rfl⟩ : syracuseStep 12746231 = 19119347) B19119347
theorem B8497487 : Blo 1987435 8497487 := bstep (se 1 (by rfl) ⟨6373115, by rfl⟩ : syracuseStep 8497487 = 12746231) B12746231
theorem B5664991 : Blo 1987435 5664991 := bstep (se 1 (by rfl) ⟨4248743, by rfl⟩ : syracuseStep 5664991 = 8497487) B8497487
theorem B7553321 : Blo 1987435 7553321 := bstep (se 2 (by rfl) ⟨2832495, by rfl⟩ : syracuseStep 7553321 = 5664991) B5664991
theorem B5035547 : Blo 1987435 5035547 := bstep (se 1 (by rfl) ⟨3776660, by rfl⟩ : syracuseStep 5035547 = 7553321) B7553321
theorem B3357031 : Blo 1987435 3357031 := bstep (se 1 (by rfl) ⟨2517773, by rfl⟩ : syracuseStep 3357031 = 5035547) B5035547
theorem B4476041 : Blo 1987435 4476041 := bstep (se 2 (by rfl) ⟨1678515, by rfl⟩ : syracuseStep 4476041 = 3357031) B3357031
theorem B2984027 : Blo 1987435 2984027 := bstep (se 1 (by rfl) ⟨2238020, by rfl⟩ : syracuseStep 2984027 = 4476041) B4476041
theorem B1989351 : Blo 1987435 1989351 := bstep (se 1 (by rfl) ⟨1492013, by rfl⟩ : syracuseStep 1989351 = 2984027) B2984027
theorem B2238025 : Blo 1987435 2238025 := bbase (se 2 (by rfl) ⟨839259, by rfl⟩ : syracuseStep 2238025 = 1678519) (by norm_num)
theorem B2984033 : Blo 1987435 2984033 := bstep (se 2 (by rfl) ⟨1119012, by rfl⟩ : syracuseStep 2984033 = 2238025) B2238025
theorem B1989355 : Blo 1987435 1989355 := bstep (se 1 (by rfl) ⟨1492016, by rfl⟩ : syracuseStep 1989355 = 2984033) B2984033
theorem B10488997 : Blo 1987435 10488997 := bbase (se 4 (by rfl) ⟨983343, by rfl⟩ : syracuseStep 10488997 = 1966687) (by norm_num)
theorem B13985329 : Blo 1987435 13985329 := bstep (se 2 (by rfl) ⟨5244498, by rfl⟩ : syracuseStep 13985329 = 10488997) B10488997
theorem B18647105 : Blo 1987435 18647105 := bstep (se 2 (by rfl) ⟨6992664, by rfl⟩ : syracuseStep 18647105 = 13985329) B13985329
theorem B49725613 : Blo 1987435 49725613 := bstep (se 3 (by rfl) ⟨9323552, by rfl⟩ : syracuseStep 49725613 = 18647105) B18647105
theorem B66300817 : Blo 1987435 66300817 := bstep (se 2 (by rfl) ⟨24862806, by rfl⟩ : syracuseStep 66300817 = 49725613) B49725613
theorem B88401089 : Blo 1987435 88401089 := bstep (se 2 (by rfl) ⟨33150408, by rfl⟩ : syracuseStep 88401089 = 66300817) B66300817
theorem B235736237 : Blo 1987435 235736237 := bstep (se 3 (by rfl) ⟨44200544, by rfl⟩ : syracuseStep 235736237 = 88401089) B88401089
theorem B157157491 : Blo 1987435 157157491 := bstep (se 1 (by rfl) ⟨117868118, by rfl⟩ : syracuseStep 157157491 = 235736237) B235736237
theorem B209543321 : Blo 1987435 209543321 := bstep (se 2 (by rfl) ⟨78578745, by rfl⟩ : syracuseStep 209543321 = 157157491) B157157491
theorem B139695547 : Blo 1987435 139695547 := bstep (se 1 (by rfl) ⟨104771660, by rfl⟩ : syracuseStep 139695547 = 209543321) B209543321
theorem B186260729 : Blo 1987435 186260729 := bstep (se 2 (by rfl) ⟨69847773, by rfl⟩ : syracuseStep 186260729 = 139695547) B139695547
theorem B496695277 : Blo 1987435 496695277 := bstep (se 3 (by rfl) ⟨93130364, by rfl⟩ : syracuseStep 496695277 = 186260729) B186260729
theorem B662260369 : Blo 1987435 662260369 := bstep (se 2 (by rfl) ⟨248347638, by rfl⟩ : syracuseStep 662260369 = 496695277) B496695277
theorem B883013825 : Blo 1987435 883013825 := bstep (se 2 (by rfl) ⟨331130184, by rfl⟩ : syracuseStep 883013825 = 662260369) B662260369
theorem B588675883 : Blo 1987435 588675883 := bstep (se 1 (by rfl) ⟨441506912, by rfl⟩ : syracuseStep 588675883 = 883013825) B883013825
theorem B784901177 : Blo 1987435 784901177 := bstep (se 2 (by rfl) ⟨294337941, by rfl⟩ : syracuseStep 784901177 = 588675883) B588675883
theorem B523267451 : Blo 1987435 523267451 := bstep (se 1 (by rfl) ⟨392450588, by rfl⟩ : syracuseStep 523267451 = 784901177) B784901177
theorem B348844967 : Blo 1987435 348844967 := bstep (se 1 (by rfl) ⟨261633725, by rfl⟩ : syracuseStep 348844967 = 523267451) B523267451
theorem B232563311 : Blo 1987435 232563311 := bstep (se 1 (by rfl) ⟨174422483, by rfl⟩ : syracuseStep 232563311 = 348844967) B348844967
theorem B155042207 : Blo 1987435 155042207 := bstep (se 1 (by rfl) ⟨116281655, by rfl⟩ : syracuseStep 155042207 = 232563311) B232563311
theorem B103361471 : Blo 1987435 103361471 := bstep (se 1 (by rfl) ⟨77521103, by rfl⟩ : syracuseStep 103361471 = 155042207) B155042207
theorem B68907647 : Blo 1987435 68907647 := bstep (se 1 (by rfl) ⟨51680735, by rfl⟩ : syracuseStep 68907647 = 103361471) B103361471
theorem B45938431 : Blo 1987435 45938431 := bstep (se 1 (by rfl) ⟨34453823, by rfl⟩ : syracuseStep 45938431 = 68907647) B68907647
theorem B61251241 : Blo 1987435 61251241 := bstep (se 2 (by rfl) ⟨22969215, by rfl⟩ : syracuseStep 61251241 = 45938431) B45938431
theorem B81668321 : Blo 1987435 81668321 := bstep (se 2 (by rfl) ⟨30625620, by rfl⟩ : syracuseStep 81668321 = 61251241) B61251241
theorem B54445547 : Blo 1987435 54445547 := bstep (se 1 (by rfl) ⟨40834160, by rfl⟩ : syracuseStep 54445547 = 81668321) B81668321
theorem B36297031 : Blo 1987435 36297031 := bstep (se 1 (by rfl) ⟨27222773, by rfl⟩ : syracuseStep 36297031 = 54445547) B54445547
theorem B48396041 : Blo 1987435 48396041 := bstep (se 2 (by rfl) ⟨18148515, by rfl⟩ : syracuseStep 48396041 = 36297031) B36297031
theorem B32264027 : Blo 1987435 32264027 := bstep (se 1 (by rfl) ⟨24198020, by rfl⟩ : syracuseStep 32264027 = 48396041) B48396041
theorem B21509351 : Blo 1987435 21509351 := bstep (se 1 (by rfl) ⟨16132013, by rfl⟩ : syracuseStep 21509351 = 32264027) B32264027
theorem B14339567 : Blo 1987435 14339567 := bstep (se 1 (by rfl) ⟨10754675, by rfl⟩ : syracuseStep 14339567 = 21509351) B21509351
theorem B9559711 : Blo 1987435 9559711 := bstep (se 1 (by rfl) ⟨7169783, by rfl⟩ : syracuseStep 9559711 = 14339567) B14339567
theorem B12746281 : Blo 1987435 12746281 := bstep (se 2 (by rfl) ⟨4779855, by rfl⟩ : syracuseStep 12746281 = 9559711) B9559711
theorem B16995041 : Blo 1987435 16995041 := bstep (se 2 (by rfl) ⟨6373140, by rfl⟩ : syracuseStep 16995041 = 12746281) B12746281
theorem B11330027 : Blo 1987435 11330027 := bstep (se 1 (by rfl) ⟨8497520, by rfl⟩ : syracuseStep 11330027 = 16995041) B16995041
theorem B7553351 : Blo 1987435 7553351 := bstep (se 1 (by rfl) ⟨5665013, by rfl⟩ : syracuseStep 7553351 = 11330027) B11330027
theorem B5035567 : Blo 1987435 5035567 := bstep (se 1 (by rfl) ⟨3776675, by rfl⟩ : syracuseStep 5035567 = 7553351) B7553351
theorem B6714089 : Blo 1987435 6714089 := bstep (se 2 (by rfl) ⟨2517783, by rfl⟩ : syracuseStep 6714089 = 5035567) B5035567
theorem B4476059 : Blo 1987435 4476059 := bstep (se 1 (by rfl) ⟨3357044, by rfl⟩ : syracuseStep 4476059 = 6714089) B6714089
theorem B2984039 : Blo 1987435 2984039 := bstep (se 1 (by rfl) ⟨2238029, by rfl⟩ : syracuseStep 2984039 = 4476059) B4476059
theorem B1989359 : Blo 1987435 1989359 := bstep (se 1 (by rfl) ⟨1492019, by rfl⟩ : syracuseStep 1989359 = 2984039) B2984039
theorem B2984045 : Blo 1987435 2984045 := bbase (se 3 (by rfl) ⟨559508, by rfl⟩ : syracuseStep 2984045 = 1119017) (by norm_num)
theorem B1989363 : Blo 1987435 1989363 := bstep (se 1 (by rfl) ⟨1492022, by rfl⟩ : syracuseStep 1989363 = 2984045) B2984045
theorem B4476077 : Blo 1987435 4476077 := bbase (se 3 (by rfl) ⟨839264, by rfl⟩ : syracuseStep 4476077 = 1678529) (by norm_num)
theorem B2984051 : Blo 1987435 2984051 := bstep (se 1 (by rfl) ⟨2238038, by rfl⟩ : syracuseStep 2984051 = 4476077) B4476077
theorem B1989367 : Blo 1987435 1989367 := bstep (se 1 (by rfl) ⟨1492025, by rfl⟩ : syracuseStep 1989367 = 2984051) B2984051
theorem B3024773 : Blo 1987435 3024773 := bbase (se 4 (by rfl) ⟨283572, by rfl⟩ : syracuseStep 3024773 = 567145) (by norm_num)
theorem B2016515 : Blo 1987435 2016515 := bstep (se 1 (by rfl) ⟨1512386, by rfl⟩ : syracuseStep 2016515 = 3024773) B3024773
theorem B5377373 : Blo 1987435 5377373 := bstep (se 3 (by rfl) ⟨1008257, by rfl⟩ : syracuseStep 5377373 = 2016515) B2016515
theorem B3584915 : Blo 1987435 3584915 := bstep (se 1 (by rfl) ⟨2688686, by rfl⟩ : syracuseStep 3584915 = 5377373) B5377373
theorem B2389943 : Blo 1987435 2389943 := bstep (se 1 (by rfl) ⟨1792457, by rfl⟩ : syracuseStep 2389943 = 3584915) B3584915
theorem B6373181 : Blo 1987435 6373181 := bstep (se 3 (by rfl) ⟨1194971, by rfl⟩ : syracuseStep 6373181 = 2389943) B2389943
theorem B4248787 : Blo 1987435 4248787 := bstep (se 1 (by rfl) ⟨3186590, by rfl⟩ : syracuseStep 4248787 = 6373181) B6373181
theorem B5665049 : Blo 1987435 5665049 := bstep (se 2 (by rfl) ⟨2124393, by rfl⟩ : syracuseStep 5665049 = 4248787) B4248787
theorem B3776699 : Blo 1987435 3776699 := bstep (se 1 (by rfl) ⟨2832524, by rfl⟩ : syracuseStep 3776699 = 5665049) B5665049
theorem B2517799 : Blo 1987435 2517799 := bstep (se 1 (by rfl) ⟨1888349, by rfl⟩ : syracuseStep 2517799 = 3776699) B3776699
theorem B3357065 : Blo 1987435 3357065 := bstep (se 2 (by rfl) ⟨1258899, by rfl⟩ : syracuseStep 3357065 = 2517799) B2517799
theorem B2238043 : Blo 1987435 2238043 := bstep (se 1 (by rfl) ⟨1678532, by rfl⟩ : syracuseStep 2238043 = 3357065) B3357065
theorem B2984057 : Blo 1987435 2984057 := bstep (se 2 (by rfl) ⟨1119021, by rfl⟩ : syracuseStep 2984057 = 2238043) B2238043
theorem B1989371 : Blo 1987435 1989371 := bstep (se 1 (by rfl) ⟨1492028, by rfl⟩ : syracuseStep 1989371 = 2984057) B2984057
theorem B18148661 : Blo 1987435 18148661 := bbase (se 5 (by rfl) ⟨850718, by rfl⟩ : syracuseStep 18148661 = 1701437) (by norm_num)
theorem B12099107 : Blo 1987435 12099107 := bstep (se 1 (by rfl) ⟨9074330, by rfl⟩ : syracuseStep 12099107 = 18148661) B18148661
theorem B8066071 : Blo 1987435 8066071 := bstep (se 1 (by rfl) ⟨6049553, by rfl⟩ : syracuseStep 8066071 = 12099107) B12099107
theorem B10754761 : Blo 1987435 10754761 := bstep (se 2 (by rfl) ⟨4033035, by rfl⟩ : syracuseStep 10754761 = 8066071) B8066071
theorem B14339681 : Blo 1987435 14339681 := bstep (se 2 (by rfl) ⟨5377380, by rfl⟩ : syracuseStep 14339681 = 10754761) B10754761
theorem B9559787 : Blo 1987435 9559787 := bstep (se 1 (by rfl) ⟨7169840, by rfl⟩ : syracuseStep 9559787 = 14339681) B14339681
theorem B25492765 : Blo 1987435 25492765 := bstep (se 3 (by rfl) ⟨4779893, by rfl⟩ : syracuseStep 25492765 = 9559787) B9559787
theorem B33990353 : Blo 1987435 33990353 := bstep (se 2 (by rfl) ⟨12746382, by rfl⟩ : syracuseStep 33990353 = 25492765) B25492765
theorem B22660235 : Blo 1987435 22660235 := bstep (se 1 (by rfl) ⟨16995176, by rfl⟩ : syracuseStep 22660235 = 33990353) B33990353
theorem B15106823 : Blo 1987435 15106823 := bstep (se 1 (by rfl) ⟨11330117, by rfl⟩ : syracuseStep 15106823 = 22660235) B22660235
theorem B10071215 : Blo 1987435 10071215 := bstep (se 1 (by rfl) ⟨7553411, by rfl⟩ : syracuseStep 10071215 = 15106823) B15106823
theorem B6714143 : Blo 1987435 6714143 := bstep (se 1 (by rfl) ⟨5035607, by rfl⟩ : syracuseStep 6714143 = 10071215) B10071215
theorem B4476095 : Blo 1987435 4476095 := bstep (se 1 (by rfl) ⟨3357071, by rfl⟩ : syracuseStep 4476095 = 6714143) B6714143
theorem B2984063 : Blo 1987435 2984063 := bstep (se 1 (by rfl) ⟨2238047, by rfl⟩ : syracuseStep 2984063 = 4476095) B4476095
theorem B1989375 : Blo 1987435 1989375 := bstep (se 1 (by rfl) ⟨1492031, by rfl⟩ : syracuseStep 1989375 = 2984063) B2984063
theorem B2984069 : Blo 1987435 2984069 := bbase (se 4 (by rfl) ⟨279756, by rfl⟩ : syracuseStep 2984069 = 559513) (by norm_num)
theorem B1989379 : Blo 1987435 1989379 := bstep (se 1 (by rfl) ⟨1492034, by rfl⟩ : syracuseStep 1989379 = 2984069) B2984069
theorem B3357085 : Blo 1987435 3357085 := bbase (se 3 (by rfl) ⟨629453, by rfl⟩ : syracuseStep 3357085 = 1258907) (by norm_num)
theorem B4476113 : Blo 1987435 4476113 := bstep (se 2 (by rfl) ⟨1678542, by rfl⟩ : syracuseStep 4476113 = 3357085) B3357085
theorem B2984075 : Blo 1987435 2984075 := bstep (se 1 (by rfl) ⟨2238056, by rfl⟩ : syracuseStep 2984075 = 4476113) B4476113
theorem B1989383 : Blo 1987435 1989383 := bstep (se 1 (by rfl) ⟨1492037, by rfl⟩ : syracuseStep 1989383 = 2984075) B2984075
theorem B2238061 : Blo 1987435 2238061 := bbase (se 3 (by rfl) ⟨419636, by rfl⟩ : syracuseStep 2238061 = 839273) (by norm_num)
theorem B2984081 : Blo 1987435 2984081 := bstep (se 2 (by rfl) ⟨1119030, by rfl⟩ : syracuseStep 2984081 = 2238061) B2238061
theorem B1989387 : Blo 1987435 1989387 := bstep (se 1 (by rfl) ⟨1492040, by rfl⟩ : syracuseStep 1989387 = 2984081) B2984081
theorem B6714197 : Blo 1987435 6714197 := bbase (se 9 (by rfl) ⟨19670, by rfl⟩ : syracuseStep 6714197 = 39341) (by norm_num)
theorem B4476131 : Blo 1987435 4476131 := bstep (se 1 (by rfl) ⟨3357098, by rfl⟩ : syracuseStep 4476131 = 6714197) B6714197
theorem B2984087 : Blo 1987435 2984087 := bstep (se 1 (by rfl) ⟨2238065, by rfl⟩ : syracuseStep 2984087 = 4476131) B4476131
theorem B1989391 : Blo 1987435 1989391 := bstep (se 1 (by rfl) ⟨1492043, by rfl⟩ : syracuseStep 1989391 = 2984087) B2984087
theorem B2984093 : Blo 1987435 2984093 := bbase (se 3 (by rfl) ⟨559517, by rfl⟩ : syracuseStep 2984093 = 1119035) (by norm_num)
theorem B1989395 : Blo 1987435 1989395 := bstep (se 1 (by rfl) ⟨1492046, by rfl⟩ : syracuseStep 1989395 = 2984093) B2984093
theorem B4476149 : Blo 1987435 4476149 := bbase (se 5 (by rfl) ⟨209819, by rfl⟩ : syracuseStep 4476149 = 419639) (by norm_num)
theorem B2984099 : Blo 1987435 2984099 := bstep (se 1 (by rfl) ⟨2238074, by rfl⟩ : syracuseStep 2984099 = 4476149) B4476149
theorem B1989399 : Blo 1987435 1989399 := bstep (se 1 (by rfl) ⟨1492049, by rfl⟩ : syracuseStep 1989399 = 2984099) B2984099
theorem B6637717 : Blo 1987435 6637717 := bbase (se 6 (by rfl) ⟨155571, by rfl⟩ : syracuseStep 6637717 = 311143) (by norm_num)
theorem B35401157 : Blo 1987435 35401157 := bstep (se 4 (by rfl) ⟨3318858, by rfl⟩ : syracuseStep 35401157 = 6637717) B6637717
theorem B23600771 : Blo 1987435 23600771 := bstep (se 1 (by rfl) ⟨17700578, by rfl⟩ : syracuseStep 23600771 = 35401157) B35401157
theorem B15733847 : Blo 1987435 15733847 := bstep (se 1 (by rfl) ⟨11800385, by rfl⟩ : syracuseStep 15733847 = 23600771) B23600771
theorem B10489231 : Blo 1987435 10489231 := bstep (se 1 (by rfl) ⟨7866923, by rfl⟩ : syracuseStep 10489231 = 15733847) B15733847
theorem B13985641 : Blo 1987435 13985641 := bstep (se 2 (by rfl) ⟨5244615, by rfl⟩ : syracuseStep 13985641 = 10489231) B10489231
theorem B18647521 : Blo 1987435 18647521 := bstep (se 2 (by rfl) ⟨6992820, by rfl⟩ : syracuseStep 18647521 = 13985641) B13985641
theorem B397813781 : Blo 1987435 397813781 := bstep (se 6 (by rfl) ⟨9323760, by rfl⟩ : syracuseStep 397813781 = 18647521) B18647521
theorem B265209187 : Blo 1987435 265209187 := bstep (se 1 (by rfl) ⟨198906890, by rfl⟩ : syracuseStep 265209187 = 397813781) B397813781
theorem B353612249 : Blo 1987435 353612249 := bstep (se 2 (by rfl) ⟨132604593, by rfl⟩ : syracuseStep 353612249 = 265209187) B265209187
theorem B235741499 : Blo 1987435 235741499 := bstep (se 1 (by rfl) ⟨176806124, by rfl⟩ : syracuseStep 235741499 = 353612249) B353612249
theorem B157160999 : Blo 1987435 157160999 := bstep (se 1 (by rfl) ⟨117870749, by rfl⟩ : syracuseStep 157160999 = 235741499) B235741499
theorem B104773999 : Blo 1987435 104773999 := bstep (se 1 (by rfl) ⟨78580499, by rfl⟩ : syracuseStep 104773999 = 157160999) B157160999
theorem B139698665 : Blo 1987435 139698665 := bstep (se 2 (by rfl) ⟨52386999, by rfl⟩ : syracuseStep 139698665 = 104773999) B104773999
theorem B93132443 : Blo 1987435 93132443 := bstep (se 1 (by rfl) ⟨69849332, by rfl⟩ : syracuseStep 93132443 = 139698665) B139698665
theorem B62088295 : Blo 1987435 62088295 := bstep (se 1 (by rfl) ⟨46566221, by rfl⟩ : syracuseStep 62088295 = 93132443) B93132443
theorem B82784393 : Blo 1987435 82784393 := bstep (se 2 (by rfl) ⟨31044147, by rfl⟩ : syracuseStep 82784393 = 62088295) B62088295
theorem B55189595 : Blo 1987435 55189595 := bstep (se 1 (by rfl) ⟨41392196, by rfl⟩ : syracuseStep 55189595 = 82784393) B82784393
theorem B36793063 : Blo 1987435 36793063 := bstep (se 1 (by rfl) ⟨27594797, by rfl⟩ : syracuseStep 36793063 = 55189595) B55189595
theorem B49057417 : Blo 1987435 49057417 := bstep (se 2 (by rfl) ⟨18396531, by rfl⟩ : syracuseStep 49057417 = 36793063) B36793063
theorem B65409889 : Blo 1987435 65409889 := bstep (se 2 (by rfl) ⟨24528708, by rfl⟩ : syracuseStep 65409889 = 49057417) B49057417
theorem B87213185 : Blo 1987435 87213185 := bstep (se 2 (by rfl) ⟨32704944, by rfl⟩ : syracuseStep 87213185 = 65409889) B65409889
theorem B58142123 : Blo 1987435 58142123 := bstep (se 1 (by rfl) ⟨43606592, by rfl⟩ : syracuseStep 58142123 = 87213185) B87213185
theorem B38761415 : Blo 1987435 38761415 := bstep (se 1 (by rfl) ⟨29071061, by rfl⟩ : syracuseStep 38761415 = 58142123) B58142123
theorem B25840943 : Blo 1987435 25840943 := bstep (se 1 (by rfl) ⟨19380707, by rfl⟩ : syracuseStep 25840943 = 38761415) B38761415
theorem B17227295 : Blo 1987435 17227295 := bstep (se 1 (by rfl) ⟨12920471, by rfl⟩ : syracuseStep 17227295 = 25840943) B25840943
theorem B11484863 : Blo 1987435 11484863 := bstep (se 1 (by rfl) ⟨8613647, by rfl⟩ : syracuseStep 11484863 = 17227295) B17227295
theorem B7656575 : Blo 1987435 7656575 := bstep (se 1 (by rfl) ⟨5742431, by rfl⟩ : syracuseStep 7656575 = 11484863) B11484863
theorem B81670133 : Blo 1987435 81670133 := bstep (se 5 (by rfl) ⟨3828287, by rfl⟩ : syracuseStep 81670133 = 7656575) B7656575
theorem B54446755 : Blo 1987435 54446755 := bstep (se 1 (by rfl) ⟨40835066, by rfl⟩ : syracuseStep 54446755 = 81670133) B81670133
theorem B72595673 : Blo 1987435 72595673 := bstep (se 2 (by rfl) ⟨27223377, by rfl⟩ : syracuseStep 72595673 = 54446755) B54446755
theorem B48397115 : Blo 1987435 48397115 := bstep (se 1 (by rfl) ⟨36297836, by rfl⟩ : syracuseStep 48397115 = 72595673) B72595673
theorem B32264743 : Blo 1987435 32264743 := bstep (se 1 (by rfl) ⟨24198557, by rfl⟩ : syracuseStep 32264743 = 48397115) B48397115
theorem B43019657 : Blo 1987435 43019657 := bstep (se 2 (by rfl) ⟨16132371, by rfl⟩ : syracuseStep 43019657 = 32264743) B32264743
theorem B28679771 : Blo 1987435 28679771 := bstep (se 1 (by rfl) ⟨21509828, by rfl⟩ : syracuseStep 28679771 = 43019657) B43019657
theorem B19119847 : Blo 1987435 19119847 := bstep (se 1 (by rfl) ⟨14339885, by rfl⟩ : syracuseStep 19119847 = 28679771) B28679771
theorem B25493129 : Blo 1987435 25493129 := bstep (se 2 (by rfl) ⟨9559923, by rfl⟩ : syracuseStep 25493129 = 19119847) B19119847
theorem B16995419 : Blo 1987435 16995419 := bstep (se 1 (by rfl) ⟨12746564, by rfl⟩ : syracuseStep 16995419 = 25493129) B25493129
theorem B11330279 : Blo 1987435 11330279 := bstep (se 1 (by rfl) ⟨8497709, by rfl⟩ : syracuseStep 11330279 = 16995419) B16995419
theorem B7553519 : Blo 1987435 7553519 := bstep (se 1 (by rfl) ⟨5665139, by rfl⟩ : syracuseStep 7553519 = 11330279) B11330279
theorem B5035679 : Blo 1987435 5035679 := bstep (se 1 (by rfl) ⟨3776759, by rfl⟩ : syracuseStep 5035679 = 7553519) B7553519
theorem B3357119 : Blo 1987435 3357119 := bstep (se 1 (by rfl) ⟨2517839, by rfl⟩ : syracuseStep 3357119 = 5035679) B5035679
theorem B2238079 : Blo 1987435 2238079 := bstep (se 1 (by rfl) ⟨1678559, by rfl⟩ : syracuseStep 2238079 = 3357119) B3357119
theorem B2984105 : Blo 1987435 2984105 := bstep (se 2 (by rfl) ⟨1119039, by rfl⟩ : syracuseStep 2984105 = 2238079) B2238079
theorem B1989403 : Blo 1987435 1989403 := bstep (se 1 (by rfl) ⟨1492052, by rfl⟩ : syracuseStep 1989403 = 2984105) B2984105
theorem B16132405 : Blo 1987435 16132405 := bbase (se 5 (by rfl) ⟨756206, by rfl⟩ : syracuseStep 16132405 = 1512413) (by norm_num)
theorem B21509873 : Blo 1987435 21509873 := bstep (se 2 (by rfl) ⟨8066202, by rfl⟩ : syracuseStep 21509873 = 16132405) B16132405
theorem B14339915 : Blo 1987435 14339915 := bstep (se 1 (by rfl) ⟨10754936, by rfl⟩ : syracuseStep 14339915 = 21509873) B21509873
theorem B9559943 : Blo 1987435 9559943 := bstep (se 1 (by rfl) ⟨7169957, by rfl⟩ : syracuseStep 9559943 = 14339915) B14339915
theorem B6373295 : Blo 1987435 6373295 := bstep (se 1 (by rfl) ⟨4779971, by rfl⟩ : syracuseStep 6373295 = 9559943) B9559943
theorem B4248863 : Blo 1987435 4248863 := bstep (se 1 (by rfl) ⟨3186647, by rfl⟩ : syracuseStep 4248863 = 6373295) B6373295
theorem B2832575 : Blo 1987435 2832575 := bstep (se 1 (by rfl) ⟨2124431, by rfl⟩ : syracuseStep 2832575 = 4248863) B4248863
theorem B7553533 : Blo 1987435 7553533 := bstep (se 3 (by rfl) ⟨1416287, by rfl⟩ : syracuseStep 7553533 = 2832575) B2832575
theorem B10071377 : Blo 1987435 10071377 := bstep (se 2 (by rfl) ⟨3776766, by rfl⟩ : syracuseStep 10071377 = 7553533) B7553533
theorem B6714251 : Blo 1987435 6714251 := bstep (se 1 (by rfl) ⟨5035688, by rfl⟩ : syracuseStep 6714251 = 10071377) B10071377
theorem B4476167 : Blo 1987435 4476167 := bstep (se 1 (by rfl) ⟨3357125, by rfl⟩ : syracuseStep 4476167 = 6714251) B6714251
theorem B2984111 : Blo 1987435 2984111 := bstep (se 1 (by rfl) ⟨2238083, by rfl⟩ : syracuseStep 2984111 = 4476167) B4476167
theorem B1989407 : Blo 1987435 1989407 := bstep (se 1 (by rfl) ⟨1492055, by rfl⟩ : syracuseStep 1989407 = 2984111) B2984111
theorem B2984117 : Blo 1987435 2984117 := bbase (se 5 (by rfl) ⟨139880, by rfl⟩ : syracuseStep 2984117 = 279761) (by norm_num)
theorem B1989411 : Blo 1987435 1989411 := bstep (se 1 (by rfl) ⟨1492058, by rfl⟩ : syracuseStep 1989411 = 2984117) B2984117
theorem B5035709 : Blo 1987435 5035709 := bbase (se 3 (by rfl) ⟨944195, by rfl⟩ : syracuseStep 5035709 = 1888391) (by norm_num)
theorem B3357139 : Blo 1987435 3357139 := bstep (se 1 (by rfl) ⟨2517854, by rfl⟩ : syracuseStep 3357139 = 5035709) B5035709
theorem B4476185 : Blo 1987435 4476185 := bstep (se 2 (by rfl) ⟨1678569, by rfl⟩ : syracuseStep 4476185 = 3357139) B3357139
theorem B2984123 : Blo 1987435 2984123 := bstep (se 1 (by rfl) ⟨2238092, by rfl⟩ : syracuseStep 2984123 = 4476185) B4476185
theorem B1989415 : Blo 1987435 1989415 := bstep (se 1 (by rfl) ⟨1492061, by rfl⟩ : syracuseStep 1989415 = 2984123) B2984123
theorem B2238097 : Blo 1987435 2238097 := bbase (se 2 (by rfl) ⟨839286, by rfl⟩ : syracuseStep 2238097 = 1678573) (by norm_num)
theorem B2984129 : Blo 1987435 2984129 := bstep (se 2 (by rfl) ⟨1119048, by rfl⟩ : syracuseStep 2984129 = 2238097) B2238097
theorem B1989419 : Blo 1987435 1989419 := bstep (se 1 (by rfl) ⟨1492064, by rfl⟩ : syracuseStep 1989419 = 2984129) B2984129
theorem B3776797 : Blo 1987435 3776797 := bbase (se 3 (by rfl) ⟨708149, by rfl⟩ : syracuseStep 3776797 = 1416299) (by norm_num)
theorem B5035729 : Blo 1987435 5035729 := bstep (se 2 (by rfl) ⟨1888398, by rfl⟩ : syracuseStep 5035729 = 3776797) B3776797
theorem B6714305 : Blo 1987435 6714305 := bstep (se 2 (by rfl) ⟨2517864, by rfl⟩ : syracuseStep 6714305 = 5035729) B5035729
theorem B4476203 : Blo 1987435 4476203 := bstep (se 1 (by rfl) ⟨3357152, by rfl⟩ : syracuseStep 4476203 = 6714305) B6714305
theorem B2984135 : Blo 1987435 2984135 := bstep (se 1 (by rfl) ⟨2238101, by rfl⟩ : syracuseStep 2984135 = 4476203) B4476203
theorem B1989423 : Blo 1987435 1989423 := bstep (se 1 (by rfl) ⟨1492067, by rfl⟩ : syracuseStep 1989423 = 2984135) B2984135
theorem B2984141 : Blo 1987435 2984141 := bbase (se 3 (by rfl) ⟨559526, by rfl⟩ : syracuseStep 2984141 = 1119053) (by norm_num)
theorem B1989427 : Blo 1987435 1989427 := bstep (se 1 (by rfl) ⟨1492070, by rfl⟩ : syracuseStep 1989427 = 2984141) B2984141
theorem B4476221 : Blo 1987435 4476221 := bbase (se 3 (by rfl) ⟨839291, by rfl⟩ : syracuseStep 4476221 = 1678583) (by norm_num)
theorem B2984147 : Blo 1987435 2984147 := bstep (se 1 (by rfl) ⟨2238110, by rfl⟩ : syracuseStep 2984147 = 4476221) B4476221
theorem B1989431 : Blo 1987435 1989431 := bstep (se 1 (by rfl) ⟨1492073, by rfl⟩ : syracuseStep 1989431 = 2984147) B2984147
theorem B3357173 : Blo 1987435 3357173 := bbase (se 5 (by rfl) ⟨157367, by rfl⟩ : syracuseStep 3357173 = 314735) (by norm_num)
theorem B2238115 : Blo 1987435 2238115 := bstep (se 1 (by rfl) ⟨1678586, by rfl⟩ : syracuseStep 2238115 = 3357173) B3357173
theorem B2984153 : Blo 1987435 2984153 := bstep (se 2 (by rfl) ⟨1119057, by rfl⟩ : syracuseStep 2984153 = 2238115) B2238115
theorem B1989435 : Blo 1987435 1989435 := bstep (se 1 (by rfl) ⟨1492076, by rfl⟩ : syracuseStep 1989435 = 2984153) B2984153
theorem C0 (j : ℕ) (h1 : 496858 ≤ j) (h2 : j ≤ 497358) : Blo 1987435 (4 * j + 3) := by
  interval_cases j
  · exact B1987435
  · exact B1987439
  · exact B1987443
  · exact B1987447
  · exact B1987451
  · exact B1987455
  · exact B1987459
  · exact B1987463
  · exact B1987467
  · exact B1987471
  · exact B1987475
  · exact B1987479
  · exact B1987483
  · exact B1987487
  · exact B1987491
  · exact B1987495
  · exact B1987499
  · exact B1987503
  · exact B1987507
  · exact B1987511
  · exact B1987515
  · exact B1987519
  · exact B1987523
  · exact B1987527
  · exact B1987531
  · exact B1987535
  · exact B1987539
  · exact B1987543
  · exact B1987547
  · exact B1987551
  · exact B1987555
  · exact B1987559
  · exact B1987563
  · exact B1987567
  · exact B1987571
  · exact B1987575
  · exact B1987579
  · exact B1987583
  · exact B1987587
  · exact B1987591
  · exact B1987595
  · exact B1987599
  · exact B1987603
  · exact B1987607
  · exact B1987611
  · exact B1987615
  · exact B1987619
  · exact B1987623
  · exact B1987627
  · exact B1987631
  · exact B1987635
  · exact B1987639
  · exact B1987643
  · exact B1987647
  · exact B1987651
  · exact B1987655
  · exact B1987659
  · exact B1987663
  · exact B1987667
  · exact B1987671
  · exact B1987675
  · exact B1987679
  · exact B1987683
  · exact B1987687
  · exact B1987691
  · exact B1987695
  · exact B1987699
  · exact B1987703
  · exact B1987707
  · exact B1987711
  · exact B1987715
  · exact B1987719
  · exact B1987723
  · exact B1987727
  · exact B1987731
  · exact B1987735
  · exact B1987739
  · exact B1987743
  · exact B1987747
  · exact B1987751
  · exact B1987755
  · exact B1987759
  · exact B1987763
  · exact B1987767
  · exact B1987771
  · exact B1987775
  · exact B1987779
  · exact B1987783
  · exact B1987787
  · exact B1987791
  · exact B1987795
  · exact B1987799
  · exact B1987803
  · exact B1987807
  · exact B1987811
  · exact B1987815
  · exact B1987819
  · exact B1987823
  · exact B1987827
  · exact B1987831
  · exact B1987835
  · exact B1987839
  · exact B1987843
  · exact B1987847
  · exact B1987851
  · exact B1987855
  · exact B1987859
  · exact B1987863
  · exact B1987867
  · exact B1987871
  · exact B1987875
  · exact B1987879
  · exact B1987883
  · exact B1987887
  · exact B1987891
  · exact B1987895
  · exact B1987899
  · exact B1987903
  · exact B1987907
  · exact B1987911
  · exact B1987915
  · exact B1987919
  · exact B1987923
  · exact B1987927
  · exact B1987931
  · exact B1987935
  · exact B1987939
  · exact B1987943
  · exact B1987947
  · exact B1987951
  · exact B1987955
  · exact B1987959
  · exact B1987963
  · exact B1987967
  · exact B1987971
  · exact B1987975
  · exact B1987979
  · exact B1987983
  · exact B1987987
  · exact B1987991
  · exact B1987995
  · exact B1987999
  · exact B1988003
  · exact B1988007
  · exact B1988011
  · exact B1988015
  · exact B1988019
  · exact B1988023
  · exact B1988027
  · exact B1988031
  · exact B1988035
  · exact B1988039
  · exact B1988043
  · exact B1988047
  · exact B1988051
  · exact B1988055
  · exact B1988059
  · exact B1988063
  · exact B1988067
  · exact B1988071
  · exact B1988075
  · exact B1988079
  · exact B1988083
  · exact B1988087
  · exact B1988091
  · exact B1988095
  · exact B1988099
  · exact B1988103
  · exact B1988107
  · exact B1988111
  · exact B1988115
  · exact B1988119
  · exact B1988123
  · exact B1988127
  · exact B1988131
  · exact B1988135
  · exact B1988139
  · exact B1988143
  · exact B1988147
  · exact B1988151
  · exact B1988155
  · exact B1988159
  · exact B1988163
  · exact B1988167
  · exact B1988171
  · exact B1988175
  · exact B1988179
  · exact B1988183
  · exact B1988187
  · exact B1988191
  · exact B1988195
  · exact B1988199
  · exact B1988203
  · exact B1988207
  · exact B1988211
  · exact B1988215
  · exact B1988219
  · exact B1988223
  · exact B1988227
  · exact B1988231
  · exact B1988235
  · exact B1988239
  · exact B1988243
  · exact B1988247
  · exact B1988251
  · exact B1988255
  · exact B1988259
  · exact B1988263
  · exact B1988267
  · exact B1988271
  · exact B1988275
  · exact B1988279
  · exact B1988283
  · exact B1988287
  · exact B1988291
  · exact B1988295
  · exact B1988299
  · exact B1988303
  · exact B1988307
  · exact B1988311
  · exact B1988315
  · exact B1988319
  · exact B1988323
  · exact B1988327
  · exact B1988331
  · exact B1988335
  · exact B1988339
  · exact B1988343
  · exact B1988347
  · exact B1988351
  · exact B1988355
  · exact B1988359
  · exact B1988363
  · exact B1988367
  · exact B1988371
  · exact B1988375
  · exact B1988379
  · exact B1988383
  · exact B1988387
  · exact B1988391
  · exact B1988395
  · exact B1988399
  · exact B1988403
  · exact B1988407
  · exact B1988411
  · exact B1988415
  · exact B1988419
  · exact B1988423
  · exact B1988427
  · exact B1988431
  · exact B1988435
  · exact B1988439
  · exact B1988443
  · exact B1988447
  · exact B1988451
  · exact B1988455
  · exact B1988459
  · exact B1988463
  · exact B1988467
  · exact B1988471
  · exact B1988475
  · exact B1988479
  · exact B1988483
  · exact B1988487
  · exact B1988491
  · exact B1988495
  · exact B1988499
  · exact B1988503
  · exact B1988507
  · exact B1988511
  · exact B1988515
  · exact B1988519
  · exact B1988523
  · exact B1988527
  · exact B1988531
  · exact B1988535
  · exact B1988539
  · exact B1988543
  · exact B1988547
  · exact B1988551
  · exact B1988555
  · exact B1988559
  · exact B1988563
  · exact B1988567
  · exact B1988571
  · exact B1988575
  · exact B1988579
  · exact B1988583
  · exact B1988587
  · exact B1988591
  · exact B1988595
  · exact B1988599
  · exact B1988603
  · exact B1988607
  · exact B1988611
  · exact B1988615
  · exact B1988619
  · exact B1988623
  · exact B1988627
  · exact B1988631
  · exact B1988635
  · exact B1988639
  · exact B1988643
  · exact B1988647
  · exact B1988651
  · exact B1988655
  · exact B1988659
  · exact B1988663
  · exact B1988667
  · exact B1988671
  · exact B1988675
  · exact B1988679
  · exact B1988683
  · exact B1988687
  · exact B1988691
  · exact B1988695
  · exact B1988699
  · exact B1988703
  · exact B1988707
  · exact B1988711
  · exact B1988715
  · exact B1988719
  · exact B1988723
  · exact B1988727
  · exact B1988731
  · exact B1988735
  · exact B1988739
  · exact B1988743
  · exact B1988747
  · exact B1988751
  · exact B1988755
  · exact B1988759
  · exact B1988763
  · exact B1988767
  · exact B1988771
  · exact B1988775
  · exact B1988779
  · exact B1988783
  · exact B1988787
  · exact B1988791
  · exact B1988795
  · exact B1988799
  · exact B1988803
  · exact B1988807
  · exact B1988811
  · exact B1988815
  · exact B1988819
  · exact B1988823
  · exact B1988827
  · exact B1988831
  · exact B1988835
  · exact B1988839
  · exact B1988843
  · exact B1988847
  · exact B1988851
  · exact B1988855
  · exact B1988859
  · exact B1988863
  · exact B1988867
  · exact B1988871
  · exact B1988875
  · exact B1988879
  · exact B1988883
  · exact B1988887
  · exact B1988891
  · exact B1988895
  · exact B1988899
  · exact B1988903
  · exact B1988907
  · exact B1988911
  · exact B1988915
  · exact B1988919
  · exact B1988923
  · exact B1988927
  · exact B1988931
  · exact B1988935
  · exact B1988939
  · exact B1988943
  · exact B1988947
  · exact B1988951
  · exact B1988955
  · exact B1988959
  · exact B1988963
  · exact B1988967
  · exact B1988971
  · exact B1988975
  · exact B1988979
  · exact B1988983
  · exact B1988987
  · exact B1988991
  · exact B1988995
  · exact B1988999
  · exact B1989003
  · exact B1989007
  · exact B1989011
  · exact B1989015
  · exact B1989019
  · exact B1989023
  · exact B1989027
  · exact B1989031
  · exact B1989035
  · exact B1989039
  · exact B1989043
  · exact B1989047
  · exact B1989051
  · exact B1989055
  · exact B1989059
  · exact B1989063
  · exact B1989067
  · exact B1989071
  · exact B1989075
  · exact B1989079
  · exact B1989083
  · exact B1989087
  · exact B1989091
  · exact B1989095
  · exact B1989099
  · exact B1989103
  · exact B1989107
  · exact B1989111
  · exact B1989115
  · exact B1989119
  · exact B1989123
  · exact B1989127
  · exact B1989131
  · exact B1989135
  · exact B1989139
  · exact B1989143
  · exact B1989147
  · exact B1989151
  · exact B1989155
  · exact B1989159
  · exact B1989163
  · exact B1989167
  · exact B1989171
  · exact B1989175
  · exact B1989179
  · exact B1989183
  · exact B1989187
  · exact B1989191
  · exact B1989195
  · exact B1989199
  · exact B1989203
  · exact B1989207
  · exact B1989211
  · exact B1989215
  · exact B1989219
  · exact B1989223
  · exact B1989227
  · exact B1989231
  · exact B1989235
  · exact B1989239
  · exact B1989243
  · exact B1989247
  · exact B1989251
  · exact B1989255
  · exact B1989259
  · exact B1989263
  · exact B1989267
  · exact B1989271
  · exact B1989275
  · exact B1989279
  · exact B1989283
  · exact B1989287
  · exact B1989291
  · exact B1989295
  · exact B1989299
  · exact B1989303
  · exact B1989307
  · exact B1989311
  · exact B1989315
  · exact B1989319
  · exact B1989323
  · exact B1989327
  · exact B1989331
  · exact B1989335
  · exact B1989339
  · exact B1989343
  · exact B1989347
  · exact B1989351
  · exact B1989355
  · exact B1989359
  · exact B1989363
  · exact B1989367
  · exact B1989371
  · exact B1989375
  · exact B1989379
  · exact B1989383
  · exact B1989387
  · exact B1989391
  · exact B1989395
  · exact B1989399
  · exact B1989403
  · exact B1989407
  · exact B1989411
  · exact B1989415
  · exact B1989419
  · exact B1989423
  · exact B1989427
  · exact B1989431
  · exact B1989435
theorem solution (m : ℕ) (hlo : 1987435 ≤ m) (hhi : m ≤ 1989435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 496858 ≤ j := by omega
    have hj2 : j ≤ 497358 := by omega
    have hb : Blo 1987435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
