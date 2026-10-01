-- Prove2me | solution 1 for syracuse_descends_range_1981435_1983435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:14.034987+00:00
-- url     : https://prove2.me/submissions/8567388c-0721-49aa-a950-df14f1364612

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

theorem B4519061 : Blo 1981435 4519061 := bbase (se 6 (by rfl) ⟨105915, by rfl⟩ : syracuseStep 4519061 = 211831) (by norm_num)
theorem B3012707 : Blo 1981435 3012707 := bstep (se 1 (by rfl) ⟨2259530, by rfl⟩ : syracuseStep 3012707 = 4519061) B4519061
theorem B2008471 : Blo 1981435 2008471 := bstep (se 1 (by rfl) ⟨1506353, by rfl⟩ : syracuseStep 2008471 = 3012707) B3012707
theorem B2677961 : Blo 1981435 2677961 := bstep (se 2 (by rfl) ⟨1004235, by rfl⟩ : syracuseStep 2677961 = 2008471) B2008471
theorem B7141229 : Blo 1981435 7141229 := bstep (se 3 (by rfl) ⟨1338980, by rfl⟩ : syracuseStep 7141229 = 2677961) B2677961
theorem B4760819 : Blo 1981435 4760819 := bstep (se 1 (by rfl) ⟨3570614, by rfl⟩ : syracuseStep 4760819 = 7141229) B7141229
theorem B3173879 : Blo 1981435 3173879 := bstep (se 1 (by rfl) ⟨2380409, by rfl⟩ : syracuseStep 3173879 = 4760819) B4760819
theorem B2115919 : Blo 1981435 2115919 := bstep (se 1 (by rfl) ⟨1586939, by rfl⟩ : syracuseStep 2115919 = 3173879) B3173879
theorem B2821225 : Blo 1981435 2821225 := bstep (se 2 (by rfl) ⟨1057959, by rfl⟩ : syracuseStep 2821225 = 2115919) B2115919
theorem B3761633 : Blo 1981435 3761633 := bstep (se 2 (by rfl) ⟨1410612, by rfl⟩ : syracuseStep 3761633 = 2821225) B2821225
theorem B2507755 : Blo 1981435 2507755 := bstep (se 1 (by rfl) ⟨1880816, by rfl⟩ : syracuseStep 2507755 = 3761633) B3761633
theorem B3343673 : Blo 1981435 3343673 := bstep (se 2 (by rfl) ⟨1253877, by rfl⟩ : syracuseStep 3343673 = 2507755) B2507755
theorem B2229115 : Blo 1981435 2229115 := bstep (se 1 (by rfl) ⟨1671836, by rfl⟩ : syracuseStep 2229115 = 3343673) B3343673
theorem B2972153 : Blo 1981435 2972153 := bstep (se 2 (by rfl) ⟨1114557, by rfl⟩ : syracuseStep 2972153 = 2229115) B2229115
theorem B1981435 : Blo 1981435 1981435 := bstep (se 1 (by rfl) ⟨1486076, by rfl⟩ : syracuseStep 1981435 = 2972153) B2972153
theorem B32135573 : Blo 1981435 32135573 := bbase (se 6 (by rfl) ⟨753177, by rfl⟩ : syracuseStep 32135573 = 1506355) (by norm_num)
theorem B85694861 : Blo 1981435 85694861 := bstep (se 3 (by rfl) ⟨16067786, by rfl⟩ : syracuseStep 85694861 = 32135573) B32135573
theorem B57129907 : Blo 1981435 57129907 := bstep (se 1 (by rfl) ⟨42847430, by rfl⟩ : syracuseStep 57129907 = 85694861) B85694861
theorem B76173209 : Blo 1981435 76173209 := bstep (se 2 (by rfl) ⟨28564953, by rfl⟩ : syracuseStep 76173209 = 57129907) B57129907
theorem B50782139 : Blo 1981435 50782139 := bstep (se 1 (by rfl) ⟨38086604, by rfl⟩ : syracuseStep 50782139 = 76173209) B76173209
theorem B33854759 : Blo 1981435 33854759 := bstep (se 1 (by rfl) ⟨25391069, by rfl⟩ : syracuseStep 33854759 = 50782139) B50782139
theorem B22569839 : Blo 1981435 22569839 := bstep (se 1 (by rfl) ⟨16927379, by rfl⟩ : syracuseStep 22569839 = 33854759) B33854759
theorem B15046559 : Blo 1981435 15046559 := bstep (se 1 (by rfl) ⟨11284919, by rfl⟩ : syracuseStep 15046559 = 22569839) B22569839
theorem B10031039 : Blo 1981435 10031039 := bstep (se 1 (by rfl) ⟨7523279, by rfl⟩ : syracuseStep 10031039 = 15046559) B15046559
theorem B6687359 : Blo 1981435 6687359 := bstep (se 1 (by rfl) ⟨5015519, by rfl⟩ : syracuseStep 6687359 = 10031039) B10031039
theorem B4458239 : Blo 1981435 4458239 := bstep (se 1 (by rfl) ⟨3343679, by rfl⟩ : syracuseStep 4458239 = 6687359) B6687359
theorem B2972159 : Blo 1981435 2972159 := bstep (se 1 (by rfl) ⟨2229119, by rfl⟩ : syracuseStep 2972159 = 4458239) B4458239
theorem B1981439 : Blo 1981435 1981439 := bstep (se 1 (by rfl) ⟨1486079, by rfl⟩ : syracuseStep 1981439 = 2972159) B2972159
theorem B2972165 : Blo 1981435 2972165 := bbase (se 4 (by rfl) ⟨278640, by rfl⟩ : syracuseStep 2972165 = 557281) (by norm_num)
theorem B1981443 : Blo 1981435 1981443 := bstep (se 1 (by rfl) ⟨1486082, by rfl⟩ : syracuseStep 1981443 = 2972165) B2972165
theorem B3343693 : Blo 1981435 3343693 := bbase (se 3 (by rfl) ⟨626942, by rfl⟩ : syracuseStep 3343693 = 1253885) (by norm_num)
theorem B4458257 : Blo 1981435 4458257 := bstep (se 2 (by rfl) ⟨1671846, by rfl⟩ : syracuseStep 4458257 = 3343693) B3343693
theorem B2972171 : Blo 1981435 2972171 := bstep (se 1 (by rfl) ⟨2229128, by rfl⟩ : syracuseStep 2972171 = 4458257) B4458257
theorem B1981447 : Blo 1981435 1981447 := bstep (se 1 (by rfl) ⟨1486085, by rfl⟩ : syracuseStep 1981447 = 2972171) B2972171
theorem B2229133 : Blo 1981435 2229133 := bbase (se 3 (by rfl) ⟨417962, by rfl⟩ : syracuseStep 2229133 = 835925) (by norm_num)
theorem B2972177 : Blo 1981435 2972177 := bstep (se 2 (by rfl) ⟨1114566, by rfl⟩ : syracuseStep 2972177 = 2229133) B2229133
theorem B1981451 : Blo 1981435 1981451 := bstep (se 1 (by rfl) ⟨1486088, by rfl⟩ : syracuseStep 1981451 = 2972177) B2972177
theorem B6687413 : Blo 1981435 6687413 := bbase (se 5 (by rfl) ⟨313472, by rfl⟩ : syracuseStep 6687413 = 626945) (by norm_num)
theorem B4458275 : Blo 1981435 4458275 := bstep (se 1 (by rfl) ⟨3343706, by rfl⟩ : syracuseStep 4458275 = 6687413) B6687413
theorem B2972183 : Blo 1981435 2972183 := bstep (se 1 (by rfl) ⟨2229137, by rfl⟩ : syracuseStep 2972183 = 4458275) B4458275
theorem B1981455 : Blo 1981435 1981455 := bstep (se 1 (by rfl) ⟨1486091, by rfl⟩ : syracuseStep 1981455 = 2972183) B2972183
theorem B2972189 : Blo 1981435 2972189 := bbase (se 3 (by rfl) ⟨557285, by rfl⟩ : syracuseStep 2972189 = 1114571) (by norm_num)
theorem B1981459 : Blo 1981435 1981459 := bstep (se 1 (by rfl) ⟨1486094, by rfl⟩ : syracuseStep 1981459 = 2972189) B2972189
theorem B4458293 : Blo 1981435 4458293 := bbase (se 5 (by rfl) ⟨208982, by rfl⟩ : syracuseStep 4458293 = 417965) (by norm_num)
theorem B2972195 : Blo 1981435 2972195 := bstep (se 1 (by rfl) ⟨2229146, by rfl⟩ : syracuseStep 2972195 = 4458293) B4458293
theorem B1981463 : Blo 1981435 1981463 := bstep (se 1 (by rfl) ⟨1486097, by rfl⟩ : syracuseStep 1981463 = 2972195) B2972195
theorem B4289645 : Blo 1981435 4289645 := bbase (se 3 (by rfl) ⟨804308, by rfl⟩ : syracuseStep 4289645 = 1608617) (by norm_num)
theorem B11439053 : Blo 1981435 11439053 := bstep (se 3 (by rfl) ⟨2144822, by rfl⟩ : syracuseStep 11439053 = 4289645) B4289645
theorem B7626035 : Blo 1981435 7626035 := bstep (se 1 (by rfl) ⟨5719526, by rfl⟩ : syracuseStep 7626035 = 11439053) B11439053
theorem B20336093 : Blo 1981435 20336093 := bstep (se 3 (by rfl) ⟨3813017, by rfl⟩ : syracuseStep 20336093 = 7626035) B7626035
theorem B13557395 : Blo 1981435 13557395 := bstep (se 1 (by rfl) ⟨10168046, by rfl⟩ : syracuseStep 13557395 = 20336093) B20336093
theorem B9038263 : Blo 1981435 9038263 := bstep (se 1 (by rfl) ⟨6778697, by rfl⟩ : syracuseStep 9038263 = 13557395) B13557395
theorem B12051017 : Blo 1981435 12051017 := bstep (se 2 (by rfl) ⟨4519131, by rfl⟩ : syracuseStep 12051017 = 9038263) B9038263
theorem B8034011 : Blo 1981435 8034011 := bstep (se 1 (by rfl) ⟨6025508, by rfl⟩ : syracuseStep 8034011 = 12051017) B12051017
theorem B5356007 : Blo 1981435 5356007 := bstep (se 1 (by rfl) ⟨4017005, by rfl⟩ : syracuseStep 5356007 = 8034011) B8034011
theorem B3570671 : Blo 1981435 3570671 := bstep (se 1 (by rfl) ⟨2678003, by rfl⟩ : syracuseStep 3570671 = 5356007) B5356007
theorem B2380447 : Blo 1981435 2380447 := bstep (se 1 (by rfl) ⟨1785335, by rfl⟩ : syracuseStep 2380447 = 3570671) B3570671
theorem B12695717 : Blo 1981435 12695717 := bstep (se 4 (by rfl) ⟨1190223, by rfl⟩ : syracuseStep 12695717 = 2380447) B2380447
theorem B8463811 : Blo 1981435 8463811 := bstep (se 1 (by rfl) ⟨6347858, by rfl⟩ : syracuseStep 8463811 = 12695717) B12695717
theorem B11285081 : Blo 1981435 11285081 := bstep (se 2 (by rfl) ⟨4231905, by rfl⟩ : syracuseStep 11285081 = 8463811) B8463811
theorem B7523387 : Blo 1981435 7523387 := bstep (se 1 (by rfl) ⟨5642540, by rfl⟩ : syracuseStep 7523387 = 11285081) B11285081
theorem B5015591 : Blo 1981435 5015591 := bstep (se 1 (by rfl) ⟨3761693, by rfl⟩ : syracuseStep 5015591 = 7523387) B7523387
theorem B3343727 : Blo 1981435 3343727 := bstep (se 1 (by rfl) ⟨2507795, by rfl⟩ : syracuseStep 3343727 = 5015591) B5015591
theorem B2229151 : Blo 1981435 2229151 := bstep (se 1 (by rfl) ⟨1671863, by rfl⟩ : syracuseStep 2229151 = 3343727) B3343727
theorem B2972201 : Blo 1981435 2972201 := bstep (se 2 (by rfl) ⟨1114575, by rfl⟩ : syracuseStep 2972201 = 2229151) B2229151
theorem B1981467 : Blo 1981435 1981467 := bstep (se 1 (by rfl) ⟨1486100, by rfl⟩ : syracuseStep 1981467 = 2972201) B2972201
theorem B4580797 : Blo 1981435 4580797 := bbase (se 3 (by rfl) ⟨858899, by rfl⟩ : syracuseStep 4580797 = 1717799) (by norm_num)
theorem B6107729 : Blo 1981435 6107729 := bstep (se 2 (by rfl) ⟨2290398, by rfl⟩ : syracuseStep 6107729 = 4580797) B4580797
theorem B16287277 : Blo 1981435 16287277 := bstep (se 3 (by rfl) ⟨3053864, by rfl⟩ : syracuseStep 16287277 = 6107729) B6107729
theorem B21716369 : Blo 1981435 21716369 := bstep (se 2 (by rfl) ⟨8143638, by rfl⟩ : syracuseStep 21716369 = 16287277) B16287277
theorem B14477579 : Blo 1981435 14477579 := bstep (se 1 (by rfl) ⟨10858184, by rfl⟩ : syracuseStep 14477579 = 21716369) B21716369
theorem B9651719 : Blo 1981435 9651719 := bstep (se 1 (by rfl) ⟨7238789, by rfl⟩ : syracuseStep 9651719 = 14477579) B14477579
theorem B6434479 : Blo 1981435 6434479 := bstep (se 1 (by rfl) ⟨4825859, by rfl⟩ : syracuseStep 6434479 = 9651719) B9651719
theorem B8579305 : Blo 1981435 8579305 := bstep (se 2 (by rfl) ⟨3217239, by rfl⟩ : syracuseStep 8579305 = 6434479) B6434479
theorem B11439073 : Blo 1981435 11439073 := bstep (se 2 (by rfl) ⟨4289652, by rfl⟩ : syracuseStep 11439073 = 8579305) B8579305
theorem B15252097 : Blo 1981435 15252097 := bstep (se 2 (by rfl) ⟨5719536, by rfl⟩ : syracuseStep 15252097 = 11439073) B11439073
theorem B20336129 : Blo 1981435 20336129 := bstep (se 2 (by rfl) ⟨7626048, by rfl⟩ : syracuseStep 20336129 = 15252097) B15252097
theorem B13557419 : Blo 1981435 13557419 := bstep (se 1 (by rfl) ⟨10168064, by rfl⟩ : syracuseStep 13557419 = 20336129) B20336129
theorem B9038279 : Blo 1981435 9038279 := bstep (se 1 (by rfl) ⟨6778709, by rfl⟩ : syracuseStep 9038279 = 13557419) B13557419
theorem B6025519 : Blo 1981435 6025519 := bstep (se 1 (by rfl) ⟨4519139, by rfl⟩ : syracuseStep 6025519 = 9038279) B9038279
theorem B8034025 : Blo 1981435 8034025 := bstep (se 2 (by rfl) ⟨3012759, by rfl⟩ : syracuseStep 8034025 = 6025519) B6025519
theorem B10712033 : Blo 1981435 10712033 := bstep (se 2 (by rfl) ⟨4017012, by rfl⟩ : syracuseStep 10712033 = 8034025) B8034025
theorem B7141355 : Blo 1981435 7141355 := bstep (se 1 (by rfl) ⟨5356016, by rfl⟩ : syracuseStep 7141355 = 10712033) B10712033
theorem B4760903 : Blo 1981435 4760903 := bstep (se 1 (by rfl) ⟨3570677, by rfl⟩ : syracuseStep 4760903 = 7141355) B7141355
theorem B12695741 : Blo 1981435 12695741 := bstep (se 3 (by rfl) ⟨2380451, by rfl⟩ : syracuseStep 12695741 = 4760903) B4760903
theorem B8463827 : Blo 1981435 8463827 := bstep (se 1 (by rfl) ⟨6347870, by rfl⟩ : syracuseStep 8463827 = 12695741) B12695741
theorem B5642551 : Blo 1981435 5642551 := bstep (se 1 (by rfl) ⟨4231913, by rfl⟩ : syracuseStep 5642551 = 8463827) B8463827
theorem B7523401 : Blo 1981435 7523401 := bstep (se 2 (by rfl) ⟨2821275, by rfl⟩ : syracuseStep 7523401 = 5642551) B5642551
theorem B10031201 : Blo 1981435 10031201 := bstep (se 2 (by rfl) ⟨3761700, by rfl⟩ : syracuseStep 10031201 = 7523401) B7523401
theorem B6687467 : Blo 1981435 6687467 := bstep (se 1 (by rfl) ⟨5015600, by rfl⟩ : syracuseStep 6687467 = 10031201) B10031201
theorem B4458311 : Blo 1981435 4458311 := bstep (se 1 (by rfl) ⟨3343733, by rfl⟩ : syracuseStep 4458311 = 6687467) B6687467
theorem B2972207 : Blo 1981435 2972207 := bstep (se 1 (by rfl) ⟨2229155, by rfl⟩ : syracuseStep 2972207 = 4458311) B4458311
theorem B1981471 : Blo 1981435 1981471 := bstep (se 1 (by rfl) ⟨1486103, by rfl⟩ : syracuseStep 1981471 = 2972207) B2972207
theorem B2972213 : Blo 1981435 2972213 := bbase (se 5 (by rfl) ⟨139322, by rfl⟩ : syracuseStep 2972213 = 278645) (by norm_num)
theorem B1981475 : Blo 1981435 1981475 := bstep (se 1 (by rfl) ⟨1486106, by rfl⟩ : syracuseStep 1981475 = 2972213) B2972213
theorem B5015621 : Blo 1981435 5015621 := bbase (se 4 (by rfl) ⟨470214, by rfl⟩ : syracuseStep 5015621 = 940429) (by norm_num)
theorem B3343747 : Blo 1981435 3343747 := bstep (se 1 (by rfl) ⟨2507810, by rfl⟩ : syracuseStep 3343747 = 5015621) B5015621
theorem B4458329 : Blo 1981435 4458329 := bstep (se 2 (by rfl) ⟨1671873, by rfl⟩ : syracuseStep 4458329 = 3343747) B3343747
theorem B2972219 : Blo 1981435 2972219 := bstep (se 1 (by rfl) ⟨2229164, by rfl⟩ : syracuseStep 2972219 = 4458329) B4458329
theorem B1981479 : Blo 1981435 1981479 := bstep (se 1 (by rfl) ⟨1486109, by rfl⟩ : syracuseStep 1981479 = 2972219) B2972219
theorem B2229169 : Blo 1981435 2229169 := bbase (se 2 (by rfl) ⟨835938, by rfl⟩ : syracuseStep 2229169 = 1671877) (by norm_num)
theorem B2972225 : Blo 1981435 2972225 := bstep (se 2 (by rfl) ⟨1114584, by rfl⟩ : syracuseStep 2972225 = 2229169) B2229169
theorem B1981483 : Blo 1981435 1981483 := bstep (se 1 (by rfl) ⟨1486112, by rfl⟩ : syracuseStep 1981483 = 2972225) B2972225
theorem B5642597 : Blo 1981435 5642597 := bbase (se 4 (by rfl) ⟨528993, by rfl⟩ : syracuseStep 5642597 = 1057987) (by norm_num)
theorem B3761731 : Blo 1981435 3761731 := bstep (se 1 (by rfl) ⟨2821298, by rfl⟩ : syracuseStep 3761731 = 5642597) B5642597
theorem B5015641 : Blo 1981435 5015641 := bstep (se 2 (by rfl) ⟨1880865, by rfl⟩ : syracuseStep 5015641 = 3761731) B3761731
theorem B6687521 : Blo 1981435 6687521 := bstep (se 2 (by rfl) ⟨2507820, by rfl⟩ : syracuseStep 6687521 = 5015641) B5015641
theorem B4458347 : Blo 1981435 4458347 := bstep (se 1 (by rfl) ⟨3343760, by rfl⟩ : syracuseStep 4458347 = 6687521) B6687521
theorem B2972231 : Blo 1981435 2972231 := bstep (se 1 (by rfl) ⟨2229173, by rfl⟩ : syracuseStep 2972231 = 4458347) B4458347
theorem B1981487 : Blo 1981435 1981487 := bstep (se 1 (by rfl) ⟨1486115, by rfl⟩ : syracuseStep 1981487 = 2972231) B2972231
theorem B2972237 : Blo 1981435 2972237 := bbase (se 3 (by rfl) ⟨557294, by rfl⟩ : syracuseStep 2972237 = 1114589) (by norm_num)
theorem B1981491 : Blo 1981435 1981491 := bstep (se 1 (by rfl) ⟨1486118, by rfl⟩ : syracuseStep 1981491 = 2972237) B2972237
theorem B4458365 : Blo 1981435 4458365 := bbase (se 3 (by rfl) ⟨835943, by rfl⟩ : syracuseStep 4458365 = 1671887) (by norm_num)
theorem B2972243 : Blo 1981435 2972243 := bstep (se 1 (by rfl) ⟨2229182, by rfl⟩ : syracuseStep 2972243 = 4458365) B4458365
theorem B1981495 : Blo 1981435 1981495 := bstep (se 1 (by rfl) ⟨1486121, by rfl⟩ : syracuseStep 1981495 = 2972243) B2972243
theorem B3343781 : Blo 1981435 3343781 := bbase (se 4 (by rfl) ⟨313479, by rfl⟩ : syracuseStep 3343781 = 626959) (by norm_num)
theorem B2229187 : Blo 1981435 2229187 := bstep (se 1 (by rfl) ⟨1671890, by rfl⟩ : syracuseStep 2229187 = 3343781) B3343781
theorem B2972249 : Blo 1981435 2972249 := bstep (se 2 (by rfl) ⟨1114593, by rfl⟩ : syracuseStep 2972249 = 2229187) B2229187
theorem B1981499 : Blo 1981435 1981499 := bstep (se 1 (by rfl) ⟨1486124, by rfl⟩ : syracuseStep 1981499 = 2972249) B2972249
theorem B4760981 : Blo 1981435 4760981 := bbase (se 6 (by rfl) ⟨111585, by rfl⟩ : syracuseStep 4760981 = 223171) (by norm_num)
theorem B3173987 : Blo 1981435 3173987 := bstep (se 1 (by rfl) ⟨2380490, by rfl⟩ : syracuseStep 3173987 = 4760981) B4760981
theorem B2115991 : Blo 1981435 2115991 := bstep (se 1 (by rfl) ⟨1586993, by rfl⟩ : syracuseStep 2115991 = 3173987) B3173987
theorem B2821321 : Blo 1981435 2821321 := bstep (se 2 (by rfl) ⟨1057995, by rfl⟩ : syracuseStep 2821321 = 2115991) B2115991
theorem B15047045 : Blo 1981435 15047045 := bstep (se 4 (by rfl) ⟨1410660, by rfl⟩ : syracuseStep 15047045 = 2821321) B2821321
theorem B10031363 : Blo 1981435 10031363 := bstep (se 1 (by rfl) ⟨7523522, by rfl⟩ : syracuseStep 10031363 = 15047045) B15047045
theorem B6687575 : Blo 1981435 6687575 := bstep (se 1 (by rfl) ⟨5015681, by rfl⟩ : syracuseStep 6687575 = 10031363) B10031363
theorem B4458383 : Blo 1981435 4458383 := bstep (se 1 (by rfl) ⟨3343787, by rfl⟩ : syracuseStep 4458383 = 6687575) B6687575
theorem B2972255 : Blo 1981435 2972255 := bstep (se 1 (by rfl) ⟨2229191, by rfl⟩ : syracuseStep 2972255 = 4458383) B4458383
theorem B1981503 : Blo 1981435 1981503 := bstep (se 1 (by rfl) ⟨1486127, by rfl⟩ : syracuseStep 1981503 = 2972255) B2972255
theorem B2972261 : Blo 1981435 2972261 := bbase (se 4 (by rfl) ⟨278649, by rfl⟩ : syracuseStep 2972261 = 557299) (by norm_num)
theorem B1981507 : Blo 1981435 1981507 := bstep (se 1 (by rfl) ⟨1486130, by rfl⟩ : syracuseStep 1981507 = 2972261) B2972261
theorem B2821333 : Blo 1981435 2821333 := bbase (se 7 (by rfl) ⟨33062, by rfl⟩ : syracuseStep 2821333 = 66125) (by norm_num)
theorem B3761777 : Blo 1981435 3761777 := bstep (se 2 (by rfl) ⟨1410666, by rfl⟩ : syracuseStep 3761777 = 2821333) B2821333
theorem B2507851 : Blo 1981435 2507851 := bstep (se 1 (by rfl) ⟨1880888, by rfl⟩ : syracuseStep 2507851 = 3761777) B3761777
theorem B3343801 : Blo 1981435 3343801 := bstep (se 2 (by rfl) ⟨1253925, by rfl⟩ : syracuseStep 3343801 = 2507851) B2507851
theorem B4458401 : Blo 1981435 4458401 := bstep (se 2 (by rfl) ⟨1671900, by rfl⟩ : syracuseStep 4458401 = 3343801) B3343801
theorem B2972267 : Blo 1981435 2972267 := bstep (se 1 (by rfl) ⟨2229200, by rfl⟩ : syracuseStep 2972267 = 4458401) B4458401
theorem B1981511 : Blo 1981435 1981511 := bstep (se 1 (by rfl) ⟨1486133, by rfl⟩ : syracuseStep 1981511 = 2972267) B2972267
theorem B2229205 : Blo 1981435 2229205 := bbase (se 7 (by rfl) ⟨26123, by rfl⟩ : syracuseStep 2229205 = 52247) (by norm_num)
theorem B2972273 : Blo 1981435 2972273 := bstep (se 2 (by rfl) ⟨1114602, by rfl⟩ : syracuseStep 2972273 = 2229205) B2229205
theorem B1981515 : Blo 1981435 1981515 := bstep (se 1 (by rfl) ⟨1486136, by rfl⟩ : syracuseStep 1981515 = 2972273) B2972273
theorem B2507861 : Blo 1981435 2507861 := bbase (se 8 (by rfl) ⟨14694, by rfl⟩ : syracuseStep 2507861 = 29389) (by norm_num)
theorem B6687629 : Blo 1981435 6687629 := bstep (se 3 (by rfl) ⟨1253930, by rfl⟩ : syracuseStep 6687629 = 2507861) B2507861
theorem B4458419 : Blo 1981435 4458419 := bstep (se 1 (by rfl) ⟨3343814, by rfl⟩ : syracuseStep 4458419 = 6687629) B6687629
theorem B2972279 : Blo 1981435 2972279 := bstep (se 1 (by rfl) ⟨2229209, by rfl⟩ : syracuseStep 2972279 = 4458419) B4458419
theorem B1981519 : Blo 1981435 1981519 := bstep (se 1 (by rfl) ⟨1486139, by rfl⟩ : syracuseStep 1981519 = 2972279) B2972279
theorem B2972285 : Blo 1981435 2972285 := bbase (se 3 (by rfl) ⟨557303, by rfl⟩ : syracuseStep 2972285 = 1114607) (by norm_num)
theorem B1981523 : Blo 1981435 1981523 := bstep (se 1 (by rfl) ⟨1486142, by rfl⟩ : syracuseStep 1981523 = 2972285) B2972285
theorem B4458437 : Blo 1981435 4458437 := bbase (se 4 (by rfl) ⟨417978, by rfl⟩ : syracuseStep 4458437 = 835957) (by norm_num)
theorem B2972291 : Blo 1981435 2972291 := bstep (se 1 (by rfl) ⟨2229218, by rfl⟩ : syracuseStep 2972291 = 4458437) B4458437
theorem B1981527 : Blo 1981435 1981527 := bstep (se 1 (by rfl) ⟨1486145, by rfl⟩ : syracuseStep 1981527 = 2972291) B2972291
theorem B8464085 : Blo 1981435 8464085 := bbase (se 7 (by rfl) ⟨99188, by rfl⟩ : syracuseStep 8464085 = 198377) (by norm_num)
theorem B5642723 : Blo 1981435 5642723 := bstep (se 1 (by rfl) ⟨4232042, by rfl⟩ : syracuseStep 5642723 = 8464085) B8464085
theorem B3761815 : Blo 1981435 3761815 := bstep (se 1 (by rfl) ⟨2821361, by rfl⟩ : syracuseStep 3761815 = 5642723) B5642723
theorem B5015753 : Blo 1981435 5015753 := bstep (se 2 (by rfl) ⟨1880907, by rfl⟩ : syracuseStep 5015753 = 3761815) B3761815
theorem B3343835 : Blo 1981435 3343835 := bstep (se 1 (by rfl) ⟨2507876, by rfl⟩ : syracuseStep 3343835 = 5015753) B5015753
theorem B2229223 : Blo 1981435 2229223 := bstep (se 1 (by rfl) ⟨1671917, by rfl⟩ : syracuseStep 2229223 = 3343835) B3343835
theorem B2972297 : Blo 1981435 2972297 := bstep (se 2 (by rfl) ⟨1114611, by rfl⟩ : syracuseStep 2972297 = 2229223) B2229223
theorem B1981531 : Blo 1981435 1981531 := bstep (se 1 (by rfl) ⟨1486148, by rfl⟩ : syracuseStep 1981531 = 2972297) B2972297
theorem B10031525 : Blo 1981435 10031525 := bbase (se 4 (by rfl) ⟨940455, by rfl⟩ : syracuseStep 10031525 = 1880911) (by norm_num)
theorem B6687683 : Blo 1981435 6687683 := bstep (se 1 (by rfl) ⟨5015762, by rfl⟩ : syracuseStep 6687683 = 10031525) B10031525
theorem B4458455 : Blo 1981435 4458455 := bstep (se 1 (by rfl) ⟨3343841, by rfl⟩ : syracuseStep 4458455 = 6687683) B6687683
theorem B2972303 : Blo 1981435 2972303 := bstep (se 1 (by rfl) ⟨2229227, by rfl⟩ : syracuseStep 2972303 = 4458455) B4458455
theorem B1981535 : Blo 1981435 1981535 := bstep (se 1 (by rfl) ⟨1486151, by rfl⟩ : syracuseStep 1981535 = 2972303) B2972303
theorem B2972309 : Blo 1981435 2972309 := bbase (se 6 (by rfl) ⟨69663, by rfl⟩ : syracuseStep 2972309 = 139327) (by norm_num)
theorem B1981539 : Blo 1981435 1981539 := bstep (se 1 (by rfl) ⟨1486154, by rfl⟩ : syracuseStep 1981539 = 2972309) B2972309
theorem B3012869 : Blo 1981435 3012869 := bbase (se 4 (by rfl) ⟨282456, by rfl⟩ : syracuseStep 3012869 = 564913) (by norm_num)
theorem B8034317 : Blo 1981435 8034317 := bstep (se 3 (by rfl) ⟨1506434, by rfl⟩ : syracuseStep 8034317 = 3012869) B3012869
theorem B5356211 : Blo 1981435 5356211 := bstep (se 1 (by rfl) ⟨4017158, by rfl⟩ : syracuseStep 5356211 = 8034317) B8034317
theorem B14283229 : Blo 1981435 14283229 := bstep (se 3 (by rfl) ⟨2678105, by rfl⟩ : syracuseStep 14283229 = 5356211) B5356211
theorem B19044305 : Blo 1981435 19044305 := bstep (se 2 (by rfl) ⟨7141614, by rfl⟩ : syracuseStep 19044305 = 14283229) B14283229
theorem B12696203 : Blo 1981435 12696203 := bstep (se 1 (by rfl) ⟨9522152, by rfl⟩ : syracuseStep 12696203 = 19044305) B19044305
theorem B8464135 : Blo 1981435 8464135 := bstep (se 1 (by rfl) ⟨6348101, by rfl⟩ : syracuseStep 8464135 = 12696203) B12696203
theorem B11285513 : Blo 1981435 11285513 := bstep (se 2 (by rfl) ⟨4232067, by rfl⟩ : syracuseStep 11285513 = 8464135) B8464135
theorem B7523675 : Blo 1981435 7523675 := bstep (se 1 (by rfl) ⟨5642756, by rfl⟩ : syracuseStep 7523675 = 11285513) B11285513
theorem B5015783 : Blo 1981435 5015783 := bstep (se 1 (by rfl) ⟨3761837, by rfl⟩ : syracuseStep 5015783 = 7523675) B7523675
theorem B3343855 : Blo 1981435 3343855 := bstep (se 1 (by rfl) ⟨2507891, by rfl⟩ : syracuseStep 3343855 = 5015783) B5015783
theorem B4458473 : Blo 1981435 4458473 := bstep (se 2 (by rfl) ⟨1671927, by rfl⟩ : syracuseStep 4458473 = 3343855) B3343855
theorem B2972315 : Blo 1981435 2972315 := bstep (se 1 (by rfl) ⟨2229236, by rfl⟩ : syracuseStep 2972315 = 4458473) B4458473
theorem B1981543 : Blo 1981435 1981543 := bstep (se 1 (by rfl) ⟨1486157, by rfl⟩ : syracuseStep 1981543 = 2972315) B2972315
theorem B2229241 : Blo 1981435 2229241 := bbase (se 2 (by rfl) ⟨835965, by rfl⟩ : syracuseStep 2229241 = 1671931) (by norm_num)
theorem B2972321 : Blo 1981435 2972321 := bstep (se 2 (by rfl) ⟨1114620, by rfl⟩ : syracuseStep 2972321 = 2229241) B2229241
theorem B1981547 : Blo 1981435 1981547 := bstep (se 1 (by rfl) ⟨1486160, by rfl⟩ : syracuseStep 1981547 = 2972321) B2972321
theorem B2259661 : Blo 1981435 2259661 := bbase (se 3 (by rfl) ⟨423686, by rfl⟩ : syracuseStep 2259661 = 847373) (by norm_num)
theorem B3012881 : Blo 1981435 3012881 := bstep (se 2 (by rfl) ⟨1129830, by rfl⟩ : syracuseStep 3012881 = 2259661) B2259661
theorem B32137397 : Blo 1981435 32137397 := bstep (se 5 (by rfl) ⟨1506440, by rfl⟩ : syracuseStep 32137397 = 3012881) B3012881
theorem B21424931 : Blo 1981435 21424931 := bstep (se 1 (by rfl) ⟨16068698, by rfl⟩ : syracuseStep 21424931 = 32137397) B32137397
theorem B14283287 : Blo 1981435 14283287 := bstep (se 1 (by rfl) ⟨10712465, by rfl⟩ : syracuseStep 14283287 = 21424931) B21424931
theorem B9522191 : Blo 1981435 9522191 := bstep (se 1 (by rfl) ⟨7141643, by rfl⟩ : syracuseStep 9522191 = 14283287) B14283287
theorem B6348127 : Blo 1981435 6348127 := bstep (se 1 (by rfl) ⟨4761095, by rfl⟩ : syracuseStep 6348127 = 9522191) B9522191
theorem B8464169 : Blo 1981435 8464169 := bstep (se 2 (by rfl) ⟨3174063, by rfl⟩ : syracuseStep 8464169 = 6348127) B6348127
theorem B5642779 : Blo 1981435 5642779 := bstep (se 1 (by rfl) ⟨4232084, by rfl⟩ : syracuseStep 5642779 = 8464169) B8464169
theorem B7523705 : Blo 1981435 7523705 := bstep (se 2 (by rfl) ⟨2821389, by rfl⟩ : syracuseStep 7523705 = 5642779) B5642779
theorem B5015803 : Blo 1981435 5015803 := bstep (se 1 (by rfl) ⟨3761852, by rfl⟩ : syracuseStep 5015803 = 7523705) B7523705
theorem B6687737 : Blo 1981435 6687737 := bstep (se 2 (by rfl) ⟨2507901, by rfl⟩ : syracuseStep 6687737 = 5015803) B5015803
theorem B4458491 : Blo 1981435 4458491 := bstep (se 1 (by rfl) ⟨3343868, by rfl⟩ : syracuseStep 4458491 = 6687737) B6687737
theorem B2972327 : Blo 1981435 2972327 := bstep (se 1 (by rfl) ⟨2229245, by rfl⟩ : syracuseStep 2972327 = 4458491) B4458491
theorem B1981551 : Blo 1981435 1981551 := bstep (se 1 (by rfl) ⟨1486163, by rfl⟩ : syracuseStep 1981551 = 2972327) B2972327
theorem B2972333 : Blo 1981435 2972333 := bbase (se 3 (by rfl) ⟨557312, by rfl⟩ : syracuseStep 2972333 = 1114625) (by norm_num)
theorem B1981555 : Blo 1981435 1981555 := bstep (se 1 (by rfl) ⟨1486166, by rfl⟩ : syracuseStep 1981555 = 2972333) B2972333
theorem B4458509 : Blo 1981435 4458509 := bbase (se 3 (by rfl) ⟨835970, by rfl⟩ : syracuseStep 4458509 = 1671941) (by norm_num)
theorem B2972339 : Blo 1981435 2972339 := bstep (se 1 (by rfl) ⟨2229254, by rfl⟩ : syracuseStep 2972339 = 4458509) B4458509
theorem B1981559 : Blo 1981435 1981559 := bstep (se 1 (by rfl) ⟨1486169, by rfl⟩ : syracuseStep 1981559 = 2972339) B2972339
theorem B2507917 : Blo 1981435 2507917 := bbase (se 3 (by rfl) ⟨470234, by rfl⟩ : syracuseStep 2507917 = 940469) (by norm_num)
theorem B3343889 : Blo 1981435 3343889 := bstep (se 2 (by rfl) ⟨1253958, by rfl⟩ : syracuseStep 3343889 = 2507917) B2507917
theorem B2229259 : Blo 1981435 2229259 := bstep (se 1 (by rfl) ⟨1671944, by rfl⟩ : syracuseStep 2229259 = 3343889) B3343889
theorem B2972345 : Blo 1981435 2972345 := bstep (se 2 (by rfl) ⟨1114629, by rfl⟩ : syracuseStep 2972345 = 2229259) B2229259
theorem B1981563 : Blo 1981435 1981563 := bstep (se 1 (by rfl) ⟨1486172, by rfl⟩ : syracuseStep 1981563 = 2972345) B2972345
theorem B19044533 : Blo 1981435 19044533 := bbase (se 5 (by rfl) ⟨892712, by rfl⟩ : syracuseStep 19044533 = 1785425) (by norm_num)
theorem B12696355 : Blo 1981435 12696355 := bstep (se 1 (by rfl) ⟨9522266, by rfl⟩ : syracuseStep 12696355 = 19044533) B19044533
theorem B16928473 : Blo 1981435 16928473 := bstep (se 2 (by rfl) ⟨6348177, by rfl⟩ : syracuseStep 16928473 = 12696355) B12696355
theorem B22571297 : Blo 1981435 22571297 := bstep (se 2 (by rfl) ⟨8464236, by rfl⟩ : syracuseStep 22571297 = 16928473) B16928473
theorem B15047531 : Blo 1981435 15047531 := bstep (se 1 (by rfl) ⟨11285648, by rfl⟩ : syracuseStep 15047531 = 22571297) B22571297
theorem B10031687 : Blo 1981435 10031687 := bstep (se 1 (by rfl) ⟨7523765, by rfl⟩ : syracuseStep 10031687 = 15047531) B15047531
theorem B6687791 : Blo 1981435 6687791 := bstep (se 1 (by rfl) ⟨5015843, by rfl⟩ : syracuseStep 6687791 = 10031687) B10031687
theorem B4458527 : Blo 1981435 4458527 := bstep (se 1 (by rfl) ⟨3343895, by rfl⟩ : syracuseStep 4458527 = 6687791) B6687791
theorem B2972351 : Blo 1981435 2972351 := bstep (se 1 (by rfl) ⟨2229263, by rfl⟩ : syracuseStep 2972351 = 4458527) B4458527
theorem B1981567 : Blo 1981435 1981567 := bstep (se 1 (by rfl) ⟨1486175, by rfl⟩ : syracuseStep 1981567 = 2972351) B2972351
theorem B2972357 : Blo 1981435 2972357 := bbase (se 4 (by rfl) ⟨278658, by rfl⟩ : syracuseStep 2972357 = 557317) (by norm_num)
theorem B1981571 : Blo 1981435 1981571 := bstep (se 1 (by rfl) ⟨1486178, by rfl⟩ : syracuseStep 1981571 = 2972357) B2972357
theorem B3343909 : Blo 1981435 3343909 := bbase (se 4 (by rfl) ⟨313491, by rfl⟩ : syracuseStep 3343909 = 626983) (by norm_num)
theorem B4458545 : Blo 1981435 4458545 := bstep (se 2 (by rfl) ⟨1671954, by rfl⟩ : syracuseStep 4458545 = 3343909) B3343909
theorem B2972363 : Blo 1981435 2972363 := bstep (se 1 (by rfl) ⟨2229272, by rfl⟩ : syracuseStep 2972363 = 4458545) B4458545
theorem B1981575 : Blo 1981435 1981575 := bstep (se 1 (by rfl) ⟨1486181, by rfl⟩ : syracuseStep 1981575 = 2972363) B2972363
theorem B2229277 : Blo 1981435 2229277 := bbase (se 3 (by rfl) ⟨417989, by rfl⟩ : syracuseStep 2229277 = 835979) (by norm_num)
theorem B2972369 : Blo 1981435 2972369 := bstep (se 2 (by rfl) ⟨1114638, by rfl⟩ : syracuseStep 2972369 = 2229277) B2229277
theorem B1981579 : Blo 1981435 1981579 := bstep (se 1 (by rfl) ⟨1486184, by rfl⟩ : syracuseStep 1981579 = 2972369) B2972369
theorem B6687845 : Blo 1981435 6687845 := bbase (se 4 (by rfl) ⟨626985, by rfl⟩ : syracuseStep 6687845 = 1253971) (by norm_num)
theorem B4458563 : Blo 1981435 4458563 := bstep (se 1 (by rfl) ⟨3343922, by rfl⟩ : syracuseStep 4458563 = 6687845) B6687845
theorem B2972375 : Blo 1981435 2972375 := bstep (se 1 (by rfl) ⟨2229281, by rfl⟩ : syracuseStep 2972375 = 4458563) B4458563
theorem B1981583 : Blo 1981435 1981583 := bstep (se 1 (by rfl) ⟨1486187, by rfl⟩ : syracuseStep 1981583 = 2972375) B2972375
theorem B2972381 : Blo 1981435 2972381 := bbase (se 3 (by rfl) ⟨557321, by rfl⟩ : syracuseStep 2972381 = 1114643) (by norm_num)
theorem B1981587 : Blo 1981435 1981587 := bstep (se 1 (by rfl) ⟨1486190, by rfl⟩ : syracuseStep 1981587 = 2972381) B2972381
theorem B4458581 : Blo 1981435 4458581 := bbase (se 8 (by rfl) ⟨26124, by rfl⟩ : syracuseStep 4458581 = 52249) (by norm_num)
theorem B2972387 : Blo 1981435 2972387 := bstep (se 1 (by rfl) ⟨2229290, by rfl⟩ : syracuseStep 2972387 = 4458581) B4458581
theorem B1981591 : Blo 1981435 1981591 := bstep (se 1 (by rfl) ⟨1486193, by rfl⟩ : syracuseStep 1981591 = 2972387) B2972387
theorem B2380601 : Blo 1981435 2380601 := bbase (se 2 (by rfl) ⟨892725, by rfl⟩ : syracuseStep 2380601 = 1785451) (by norm_num)
theorem B6348269 : Blo 1981435 6348269 := bstep (se 3 (by rfl) ⟨1190300, by rfl⟩ : syracuseStep 6348269 = 2380601) B2380601
theorem B4232179 : Blo 1981435 4232179 := bstep (se 1 (by rfl) ⟨3174134, by rfl⟩ : syracuseStep 4232179 = 6348269) B6348269
theorem B5642905 : Blo 1981435 5642905 := bstep (se 2 (by rfl) ⟨2116089, by rfl⟩ : syracuseStep 5642905 = 4232179) B4232179
theorem B7523873 : Blo 1981435 7523873 := bstep (se 2 (by rfl) ⟨2821452, by rfl⟩ : syracuseStep 7523873 = 5642905) B5642905
theorem B5015915 : Blo 1981435 5015915 := bstep (se 1 (by rfl) ⟨3761936, by rfl⟩ : syracuseStep 5015915 = 7523873) B7523873
theorem B3343943 : Blo 1981435 3343943 := bstep (se 1 (by rfl) ⟨2507957, by rfl⟩ : syracuseStep 3343943 = 5015915) B5015915
theorem B2229295 : Blo 1981435 2229295 := bstep (se 1 (by rfl) ⟨1671971, by rfl⟩ : syracuseStep 2229295 = 3343943) B3343943
theorem B2972393 : Blo 1981435 2972393 := bstep (se 2 (by rfl) ⟨1114647, by rfl⟩ : syracuseStep 2972393 = 2229295) B2229295
theorem B1981595 : Blo 1981435 1981595 := bstep (se 1 (by rfl) ⟨1486196, by rfl⟩ : syracuseStep 1981595 = 2972393) B2972393
theorem B2413085 : Blo 1981435 2413085 := bbase (se 3 (by rfl) ⟨452453, by rfl⟩ : syracuseStep 2413085 = 904907) (by norm_num)
theorem B6434893 : Blo 1981435 6434893 := bstep (se 3 (by rfl) ⟨1206542, by rfl⟩ : syracuseStep 6434893 = 2413085) B2413085
theorem B8579857 : Blo 1981435 8579857 := bstep (se 2 (by rfl) ⟨3217446, by rfl⟩ : syracuseStep 8579857 = 6434893) B6434893
theorem B11439809 : Blo 1981435 11439809 := bstep (se 2 (by rfl) ⟨4289928, by rfl⟩ : syracuseStep 11439809 = 8579857) B8579857
theorem B7626539 : Blo 1981435 7626539 := bstep (se 1 (by rfl) ⟨5719904, by rfl⟩ : syracuseStep 7626539 = 11439809) B11439809
theorem B20337437 : Blo 1981435 20337437 := bstep (se 3 (by rfl) ⟨3813269, by rfl⟩ : syracuseStep 20337437 = 7626539) B7626539
theorem B54233165 : Blo 1981435 54233165 := bstep (se 3 (by rfl) ⟨10168718, by rfl⟩ : syracuseStep 54233165 = 20337437) B20337437
theorem B36155443 : Blo 1981435 36155443 := bstep (se 1 (by rfl) ⟨27116582, by rfl⟩ : syracuseStep 36155443 = 54233165) B54233165
theorem B48207257 : Blo 1981435 48207257 := bstep (se 2 (by rfl) ⟨18077721, by rfl⟩ : syracuseStep 48207257 = 36155443) B36155443
theorem B32138171 : Blo 1981435 32138171 := bstep (se 1 (by rfl) ⟨24103628, by rfl⟩ : syracuseStep 32138171 = 48207257) B48207257
theorem B21425447 : Blo 1981435 21425447 := bstep (se 1 (by rfl) ⟨16069085, by rfl⟩ : syracuseStep 21425447 = 32138171) B32138171
theorem B14283631 : Blo 1981435 14283631 := bstep (se 1 (by rfl) ⟨10712723, by rfl⟩ : syracuseStep 14283631 = 21425447) B21425447
theorem B19044841 : Blo 1981435 19044841 := bstep (se 2 (by rfl) ⟨7141815, by rfl⟩ : syracuseStep 19044841 = 14283631) B14283631
theorem B25393121 : Blo 1981435 25393121 := bstep (se 2 (by rfl) ⟨9522420, by rfl⟩ : syracuseStep 25393121 = 19044841) B19044841
theorem B16928747 : Blo 1981435 16928747 := bstep (se 1 (by rfl) ⟨12696560, by rfl⟩ : syracuseStep 16928747 = 25393121) B25393121
theorem B11285831 : Blo 1981435 11285831 := bstep (se 1 (by rfl) ⟨8464373, by rfl⟩ : syracuseStep 11285831 = 16928747) B16928747
theorem B7523887 : Blo 1981435 7523887 := bstep (se 1 (by rfl) ⟨5642915, by rfl⟩ : syracuseStep 7523887 = 11285831) B11285831
theorem B10031849 : Blo 1981435 10031849 := bstep (se 2 (by rfl) ⟨3761943, by rfl⟩ : syracuseStep 10031849 = 7523887) B7523887
theorem B6687899 : Blo 1981435 6687899 := bstep (se 1 (by rfl) ⟨5015924, by rfl⟩ : syracuseStep 6687899 = 10031849) B10031849
theorem B4458599 : Blo 1981435 4458599 := bstep (se 1 (by rfl) ⟨3343949, by rfl⟩ : syracuseStep 4458599 = 6687899) B6687899
theorem B2972399 : Blo 1981435 2972399 := bstep (se 1 (by rfl) ⟨2229299, by rfl⟩ : syracuseStep 2972399 = 4458599) B4458599
theorem B1981599 : Blo 1981435 1981599 := bstep (se 1 (by rfl) ⟨1486199, by rfl⟩ : syracuseStep 1981599 = 2972399) B2972399
theorem B2972405 : Blo 1981435 2972405 := bbase (se 5 (by rfl) ⟨139331, by rfl⟩ : syracuseStep 2972405 = 278663) (by norm_num)
theorem B1981603 : Blo 1981435 1981603 := bstep (se 1 (by rfl) ⟨1486202, by rfl⟩ : syracuseStep 1981603 = 2972405) B2972405
theorem B5797973 : Blo 1981435 5797973 := bbase (se 8 (by rfl) ⟨33972, by rfl⟩ : syracuseStep 5797973 = 67945) (by norm_num)
theorem B3865315 : Blo 1981435 3865315 := bstep (se 1 (by rfl) ⟨2898986, by rfl⟩ : syracuseStep 3865315 = 5797973) B5797973
theorem B5153753 : Blo 1981435 5153753 := bstep (se 2 (by rfl) ⟨1932657, by rfl⟩ : syracuseStep 5153753 = 3865315) B3865315
theorem B13743341 : Blo 1981435 13743341 := bstep (se 3 (by rfl) ⟨2576876, by rfl⟩ : syracuseStep 13743341 = 5153753) B5153753
theorem B9162227 : Blo 1981435 9162227 := bstep (se 1 (by rfl) ⟨6871670, by rfl⟩ : syracuseStep 9162227 = 13743341) B13743341
theorem B6108151 : Blo 1981435 6108151 := bstep (se 1 (by rfl) ⟨4581113, by rfl⟩ : syracuseStep 6108151 = 9162227) B9162227
theorem B8144201 : Blo 1981435 8144201 := bstep (se 2 (by rfl) ⟨3054075, by rfl⟩ : syracuseStep 8144201 = 6108151) B6108151
theorem B5429467 : Blo 1981435 5429467 := bstep (se 1 (by rfl) ⟨4072100, by rfl⟩ : syracuseStep 5429467 = 8144201) B8144201
theorem B7239289 : Blo 1981435 7239289 := bstep (se 2 (by rfl) ⟨2714733, by rfl⟩ : syracuseStep 7239289 = 5429467) B5429467
theorem B9652385 : Blo 1981435 9652385 := bstep (se 2 (by rfl) ⟨3619644, by rfl⟩ : syracuseStep 9652385 = 7239289) B7239289
theorem B25739693 : Blo 1981435 25739693 := bstep (se 3 (by rfl) ⟨4826192, by rfl⟩ : syracuseStep 25739693 = 9652385) B9652385
theorem B17159795 : Blo 1981435 17159795 := bstep (se 1 (by rfl) ⟨12869846, by rfl⟩ : syracuseStep 17159795 = 25739693) B25739693
theorem B11439863 : Blo 1981435 11439863 := bstep (se 1 (by rfl) ⟨8579897, by rfl⟩ : syracuseStep 11439863 = 17159795) B17159795
theorem B7626575 : Blo 1981435 7626575 := bstep (se 1 (by rfl) ⟨5719931, by rfl⟩ : syracuseStep 7626575 = 11439863) B11439863
theorem B5084383 : Blo 1981435 5084383 := bstep (se 1 (by rfl) ⟨3813287, by rfl⟩ : syracuseStep 5084383 = 7626575) B7626575
theorem B6779177 : Blo 1981435 6779177 := bstep (se 2 (by rfl) ⟨2542191, by rfl⟩ : syracuseStep 6779177 = 5084383) B5084383
theorem B4519451 : Blo 1981435 4519451 := bstep (se 1 (by rfl) ⟨3389588, by rfl⟩ : syracuseStep 4519451 = 6779177) B6779177
theorem B3012967 : Blo 1981435 3012967 := bstep (se 1 (by rfl) ⟨2259725, by rfl⟩ : syracuseStep 3012967 = 4519451) B4519451
theorem B4017289 : Blo 1981435 4017289 := bstep (se 2 (by rfl) ⟨1506483, by rfl⟩ : syracuseStep 4017289 = 3012967) B3012967
theorem B5356385 : Blo 1981435 5356385 := bstep (se 2 (by rfl) ⟨2008644, by rfl⟩ : syracuseStep 5356385 = 4017289) B4017289
theorem B3570923 : Blo 1981435 3570923 := bstep (se 1 (by rfl) ⟨2678192, by rfl⟩ : syracuseStep 3570923 = 5356385) B5356385
theorem B9522461 : Blo 1981435 9522461 := bstep (se 3 (by rfl) ⟨1785461, by rfl⟩ : syracuseStep 9522461 = 3570923) B3570923
theorem B6348307 : Blo 1981435 6348307 := bstep (se 1 (by rfl) ⟨4761230, by rfl⟩ : syracuseStep 6348307 = 9522461) B9522461
theorem B8464409 : Blo 1981435 8464409 := bstep (se 2 (by rfl) ⟨3174153, by rfl⟩ : syracuseStep 8464409 = 6348307) B6348307
theorem B5642939 : Blo 1981435 5642939 := bstep (se 1 (by rfl) ⟨4232204, by rfl⟩ : syracuseStep 5642939 = 8464409) B8464409
theorem B3761959 : Blo 1981435 3761959 := bstep (se 1 (by rfl) ⟨2821469, by rfl⟩ : syracuseStep 3761959 = 5642939) B5642939
theorem B5015945 : Blo 1981435 5015945 := bstep (se 2 (by rfl) ⟨1880979, by rfl⟩ : syracuseStep 5015945 = 3761959) B3761959
theorem B3343963 : Blo 1981435 3343963 := bstep (se 1 (by rfl) ⟨2507972, by rfl⟩ : syracuseStep 3343963 = 5015945) B5015945
theorem B4458617 : Blo 1981435 4458617 := bstep (se 2 (by rfl) ⟨1671981, by rfl⟩ : syracuseStep 4458617 = 3343963) B3343963
theorem B2972411 : Blo 1981435 2972411 := bstep (se 1 (by rfl) ⟨2229308, by rfl⟩ : syracuseStep 2972411 = 4458617) B4458617
theorem B1981607 : Blo 1981435 1981607 := bstep (se 1 (by rfl) ⟨1486205, by rfl⟩ : syracuseStep 1981607 = 2972411) B2972411
theorem B2229313 : Blo 1981435 2229313 := bbase (se 2 (by rfl) ⟨835992, by rfl⟩ : syracuseStep 2229313 = 1671985) (by norm_num)
theorem B2972417 : Blo 1981435 2972417 := bstep (se 2 (by rfl) ⟨1114656, by rfl⟩ : syracuseStep 2972417 = 2229313) B2229313
theorem B1981611 : Blo 1981435 1981611 := bstep (se 1 (by rfl) ⟨1486208, by rfl⟩ : syracuseStep 1981611 = 2972417) B2972417
theorem B5015965 : Blo 1981435 5015965 := bbase (se 3 (by rfl) ⟨940493, by rfl⟩ : syracuseStep 5015965 = 1880987) (by norm_num)
theorem B6687953 : Blo 1981435 6687953 := bstep (se 2 (by rfl) ⟨2507982, by rfl⟩ : syracuseStep 6687953 = 5015965) B5015965
theorem B4458635 : Blo 1981435 4458635 := bstep (se 1 (by rfl) ⟨3343976, by rfl⟩ : syracuseStep 4458635 = 6687953) B6687953
theorem B2972423 : Blo 1981435 2972423 := bstep (se 1 (by rfl) ⟨2229317, by rfl⟩ : syracuseStep 2972423 = 4458635) B4458635
theorem B1981615 : Blo 1981435 1981615 := bstep (se 1 (by rfl) ⟨1486211, by rfl⟩ : syracuseStep 1981615 = 2972423) B2972423
theorem B2972429 : Blo 1981435 2972429 := bbase (se 3 (by rfl) ⟨557330, by rfl⟩ : syracuseStep 2972429 = 1114661) (by norm_num)
theorem B1981619 : Blo 1981435 1981619 := bstep (se 1 (by rfl) ⟨1486214, by rfl⟩ : syracuseStep 1981619 = 2972429) B2972429
theorem B4458653 : Blo 1981435 4458653 := bbase (se 3 (by rfl) ⟨835997, by rfl⟩ : syracuseStep 4458653 = 1671995) (by norm_num)
theorem B2972435 : Blo 1981435 2972435 := bstep (se 1 (by rfl) ⟨2229326, by rfl⟩ : syracuseStep 2972435 = 4458653) B4458653
theorem B1981623 : Blo 1981435 1981623 := bstep (se 1 (by rfl) ⟨1486217, by rfl⟩ : syracuseStep 1981623 = 2972435) B2972435
theorem B3343997 : Blo 1981435 3343997 := bbase (se 3 (by rfl) ⟨626999, by rfl⟩ : syracuseStep 3343997 = 1253999) (by norm_num)
theorem B2229331 : Blo 1981435 2229331 := bstep (se 1 (by rfl) ⟨1671998, by rfl⟩ : syracuseStep 2229331 = 3343997) B3343997
theorem B2972441 : Blo 1981435 2972441 := bstep (se 2 (by rfl) ⟨1114665, by rfl⟩ : syracuseStep 2972441 = 2229331) B2229331
theorem B1981627 : Blo 1981435 1981627 := bstep (se 1 (by rfl) ⟨1486220, by rfl⟩ : syracuseStep 1981627 = 2972441) B2972441
theorem B6026005 : Blo 1981435 6026005 := bbase (se 6 (by rfl) ⟨141234, by rfl⟩ : syracuseStep 6026005 = 282469) (by norm_num)
theorem B32138693 : Blo 1981435 32138693 := bstep (se 4 (by rfl) ⟨3013002, by rfl⟩ : syracuseStep 32138693 = 6026005) B6026005
theorem B21425795 : Blo 1981435 21425795 := bstep (se 1 (by rfl) ⟨16069346, by rfl⟩ : syracuseStep 21425795 = 32138693) B32138693
theorem B14283863 : Blo 1981435 14283863 := bstep (se 1 (by rfl) ⟨10712897, by rfl⟩ : syracuseStep 14283863 = 21425795) B21425795
theorem B9522575 : Blo 1981435 9522575 := bstep (se 1 (by rfl) ⟨7141931, by rfl⟩ : syracuseStep 9522575 = 14283863) B14283863
theorem B6348383 : Blo 1981435 6348383 := bstep (se 1 (by rfl) ⟨4761287, by rfl⟩ : syracuseStep 6348383 = 9522575) B9522575
theorem B4232255 : Blo 1981435 4232255 := bstep (se 1 (by rfl) ⟨3174191, by rfl⟩ : syracuseStep 4232255 = 6348383) B6348383
theorem B11286013 : Blo 1981435 11286013 := bstep (se 3 (by rfl) ⟨2116127, by rfl⟩ : syracuseStep 11286013 = 4232255) B4232255
theorem B15048017 : Blo 1981435 15048017 := bstep (se 2 (by rfl) ⟨5643006, by rfl⟩ : syracuseStep 15048017 = 11286013) B11286013
theorem B10032011 : Blo 1981435 10032011 := bstep (se 1 (by rfl) ⟨7524008, by rfl⟩ : syracuseStep 10032011 = 15048017) B15048017
theorem B6688007 : Blo 1981435 6688007 := bstep (se 1 (by rfl) ⟨5016005, by rfl⟩ : syracuseStep 6688007 = 10032011) B10032011
theorem B4458671 : Blo 1981435 4458671 := bstep (se 1 (by rfl) ⟨3344003, by rfl⟩ : syracuseStep 4458671 = 6688007) B6688007
theorem B2972447 : Blo 1981435 2972447 := bstep (se 1 (by rfl) ⟨2229335, by rfl⟩ : syracuseStep 2972447 = 4458671) B4458671
theorem B1981631 : Blo 1981435 1981631 := bstep (se 1 (by rfl) ⟨1486223, by rfl⟩ : syracuseStep 1981631 = 2972447) B2972447
theorem B2972453 : Blo 1981435 2972453 := bbase (se 4 (by rfl) ⟨278667, by rfl⟩ : syracuseStep 2972453 = 557335) (by norm_num)
theorem B1981635 : Blo 1981435 1981635 := bstep (se 1 (by rfl) ⟨1486226, by rfl⟩ : syracuseStep 1981635 = 2972453) B2972453
theorem B2508013 : Blo 1981435 2508013 := bbase (se 3 (by rfl) ⟨470252, by rfl⟩ : syracuseStep 2508013 = 940505) (by norm_num)
theorem B3344017 : Blo 1981435 3344017 := bstep (se 2 (by rfl) ⟨1254006, by rfl⟩ : syracuseStep 3344017 = 2508013) B2508013
theorem B4458689 : Blo 1981435 4458689 := bstep (se 2 (by rfl) ⟨1672008, by rfl⟩ : syracuseStep 4458689 = 3344017) B3344017
theorem B2972459 : Blo 1981435 2972459 := bstep (se 1 (by rfl) ⟨2229344, by rfl⟩ : syracuseStep 2972459 = 4458689) B4458689
theorem B1981639 : Blo 1981435 1981639 := bstep (se 1 (by rfl) ⟨1486229, by rfl⟩ : syracuseStep 1981639 = 2972459) B2972459
theorem B2229349 : Blo 1981435 2229349 := bbase (se 4 (by rfl) ⟨209001, by rfl⟩ : syracuseStep 2229349 = 418003) (by norm_num)
theorem B2972465 : Blo 1981435 2972465 := bstep (se 2 (by rfl) ⟨1114674, by rfl⟩ : syracuseStep 2972465 = 2229349) B2229349
theorem B1981643 : Blo 1981435 1981643 := bstep (se 1 (by rfl) ⟨1486232, by rfl⟩ : syracuseStep 1981643 = 2972465) B2972465
theorem B2116145 : Blo 1981435 2116145 := bbase (se 2 (by rfl) ⟨793554, by rfl⟩ : syracuseStep 2116145 = 1587109) (by norm_num)
theorem B5643053 : Blo 1981435 5643053 := bstep (se 3 (by rfl) ⟨1058072, by rfl⟩ : syracuseStep 5643053 = 2116145) B2116145
theorem B3762035 : Blo 1981435 3762035 := bstep (se 1 (by rfl) ⟨2821526, by rfl⟩ : syracuseStep 3762035 = 5643053) B5643053
theorem B2508023 : Blo 1981435 2508023 := bstep (se 1 (by rfl) ⟨1881017, by rfl⟩ : syracuseStep 2508023 = 3762035) B3762035
theorem B6688061 : Blo 1981435 6688061 := bstep (se 3 (by rfl) ⟨1254011, by rfl⟩ : syracuseStep 6688061 = 2508023) B2508023
theorem B4458707 : Blo 1981435 4458707 := bstep (se 1 (by rfl) ⟨3344030, by rfl⟩ : syracuseStep 4458707 = 6688061) B6688061
theorem B2972471 : Blo 1981435 2972471 := bstep (se 1 (by rfl) ⟨2229353, by rfl⟩ : syracuseStep 2972471 = 4458707) B4458707
theorem B1981647 : Blo 1981435 1981647 := bstep (se 1 (by rfl) ⟨1486235, by rfl⟩ : syracuseStep 1981647 = 2972471) B2972471
theorem B2972477 : Blo 1981435 2972477 := bbase (se 3 (by rfl) ⟨557339, by rfl⟩ : syracuseStep 2972477 = 1114679) (by norm_num)
theorem B1981651 : Blo 1981435 1981651 := bstep (se 1 (by rfl) ⟨1486238, by rfl⟩ : syracuseStep 1981651 = 2972477) B2972477
theorem B4458725 : Blo 1981435 4458725 := bbase (se 4 (by rfl) ⟨418005, by rfl⟩ : syracuseStep 4458725 = 836011) (by norm_num)
theorem B2972483 : Blo 1981435 2972483 := bstep (se 1 (by rfl) ⟨2229362, by rfl⟩ : syracuseStep 2972483 = 4458725) B4458725
theorem B1981655 : Blo 1981435 1981655 := bstep (se 1 (by rfl) ⟨1486241, by rfl⟩ : syracuseStep 1981655 = 2972483) B2972483
theorem B5016077 : Blo 1981435 5016077 := bbase (se 3 (by rfl) ⟨940514, by rfl⟩ : syracuseStep 5016077 = 1881029) (by norm_num)
theorem B3344051 : Blo 1981435 3344051 := bstep (se 1 (by rfl) ⟨2508038, by rfl⟩ : syracuseStep 3344051 = 5016077) B5016077
theorem B2229367 : Blo 1981435 2229367 := bstep (se 1 (by rfl) ⟨1672025, by rfl⟩ : syracuseStep 2229367 = 3344051) B3344051
theorem B2972489 : Blo 1981435 2972489 := bstep (se 2 (by rfl) ⟨1114683, by rfl⟩ : syracuseStep 2972489 = 2229367) B2229367
theorem B1981659 : Blo 1981435 1981659 := bstep (se 1 (by rfl) ⟨1486244, by rfl⟩ : syracuseStep 1981659 = 2972489) B2972489
theorem B2821549 : Blo 1981435 2821549 := bbase (se 3 (by rfl) ⟨529040, by rfl⟩ : syracuseStep 2821549 = 1058081) (by norm_num)
theorem B3762065 : Blo 1981435 3762065 := bstep (se 2 (by rfl) ⟨1410774, by rfl⟩ : syracuseStep 3762065 = 2821549) B2821549
theorem B10032173 : Blo 1981435 10032173 := bstep (se 3 (by rfl) ⟨1881032, by rfl⟩ : syracuseStep 10032173 = 3762065) B3762065
theorem B6688115 : Blo 1981435 6688115 := bstep (se 1 (by rfl) ⟨5016086, by rfl⟩ : syracuseStep 6688115 = 10032173) B10032173
theorem B4458743 : Blo 1981435 4458743 := bstep (se 1 (by rfl) ⟨3344057, by rfl⟩ : syracuseStep 4458743 = 6688115) B6688115
theorem B2972495 : Blo 1981435 2972495 := bstep (se 1 (by rfl) ⟨2229371, by rfl⟩ : syracuseStep 2972495 = 4458743) B4458743
theorem B1981663 : Blo 1981435 1981663 := bstep (se 1 (by rfl) ⟨1486247, by rfl⟩ : syracuseStep 1981663 = 2972495) B2972495
theorem B2972501 : Blo 1981435 2972501 := bbase (se 9 (by rfl) ⟨8708, by rfl⟩ : syracuseStep 2972501 = 17417) (by norm_num)
theorem B1981667 : Blo 1981435 1981667 := bstep (se 1 (by rfl) ⟨1486250, by rfl⟩ : syracuseStep 1981667 = 2972501) B2972501
theorem B4232341 : Blo 1981435 4232341 := bbase (se 6 (by rfl) ⟨99195, by rfl⟩ : syracuseStep 4232341 = 198391) (by norm_num)
theorem B5643121 : Blo 1981435 5643121 := bstep (se 2 (by rfl) ⟨2116170, by rfl⟩ : syracuseStep 5643121 = 4232341) B4232341
theorem B7524161 : Blo 1981435 7524161 := bstep (se 2 (by rfl) ⟨2821560, by rfl⟩ : syracuseStep 7524161 = 5643121) B5643121
theorem B5016107 : Blo 1981435 5016107 := bstep (se 1 (by rfl) ⟨3762080, by rfl⟩ : syracuseStep 5016107 = 7524161) B7524161
theorem B3344071 : Blo 1981435 3344071 := bstep (se 1 (by rfl) ⟨2508053, by rfl⟩ : syracuseStep 3344071 = 5016107) B5016107
theorem B4458761 : Blo 1981435 4458761 := bstep (se 2 (by rfl) ⟨1672035, by rfl⟩ : syracuseStep 4458761 = 3344071) B3344071
theorem B2972507 : Blo 1981435 2972507 := bstep (se 1 (by rfl) ⟨2229380, by rfl⟩ : syracuseStep 2972507 = 4458761) B4458761
theorem B1981671 : Blo 1981435 1981671 := bstep (se 1 (by rfl) ⟨1486253, by rfl⟩ : syracuseStep 1981671 = 2972507) B2972507
theorem B2229385 : Blo 1981435 2229385 := bbase (se 2 (by rfl) ⟨836019, by rfl⟩ : syracuseStep 2229385 = 1672039) (by norm_num)
theorem B2972513 : Blo 1981435 2972513 := bstep (se 2 (by rfl) ⟨1114692, by rfl⟩ : syracuseStep 2972513 = 2229385) B2229385
theorem B1981675 : Blo 1981435 1981675 := bstep (se 1 (by rfl) ⟨1486256, by rfl⟩ : syracuseStep 1981675 = 2972513) B2972513
theorem B38091221 : Blo 1981435 38091221 := bbase (se 7 (by rfl) ⟨446381, by rfl⟩ : syracuseStep 38091221 = 892763) (by norm_num)
theorem B25394147 : Blo 1981435 25394147 := bstep (se 1 (by rfl) ⟨19045610, by rfl⟩ : syracuseStep 25394147 = 38091221) B38091221
theorem B16929431 : Blo 1981435 16929431 := bstep (se 1 (by rfl) ⟨12697073, by rfl⟩ : syracuseStep 16929431 = 25394147) B25394147
theorem B11286287 : Blo 1981435 11286287 := bstep (se 1 (by rfl) ⟨8464715, by rfl⟩ : syracuseStep 11286287 = 16929431) B16929431
theorem B7524191 : Blo 1981435 7524191 := bstep (se 1 (by rfl) ⟨5643143, by rfl⟩ : syracuseStep 7524191 = 11286287) B11286287
theorem B5016127 : Blo 1981435 5016127 := bstep (se 1 (by rfl) ⟨3762095, by rfl⟩ : syracuseStep 5016127 = 7524191) B7524191
theorem B6688169 : Blo 1981435 6688169 := bstep (se 2 (by rfl) ⟨2508063, by rfl⟩ : syracuseStep 6688169 = 5016127) B5016127
theorem B4458779 : Blo 1981435 4458779 := bstep (se 1 (by rfl) ⟨3344084, by rfl⟩ : syracuseStep 4458779 = 6688169) B6688169
theorem B2972519 : Blo 1981435 2972519 := bstep (se 1 (by rfl) ⟨2229389, by rfl⟩ : syracuseStep 2972519 = 4458779) B4458779
theorem B1981679 : Blo 1981435 1981679 := bstep (se 1 (by rfl) ⟨1486259, by rfl⟩ : syracuseStep 1981679 = 2972519) B2972519
theorem B2972525 : Blo 1981435 2972525 := bbase (se 3 (by rfl) ⟨557348, by rfl⟩ : syracuseStep 2972525 = 1114697) (by norm_num)
theorem B1981683 : Blo 1981435 1981683 := bstep (se 1 (by rfl) ⟨1486262, by rfl⟩ : syracuseStep 1981683 = 2972525) B2972525
theorem B4458797 : Blo 1981435 4458797 := bbase (se 3 (by rfl) ⟨836024, by rfl⟩ : syracuseStep 4458797 = 1672049) (by norm_num)
theorem B2972531 : Blo 1981435 2972531 := bstep (se 1 (by rfl) ⟨2229398, by rfl⟩ : syracuseStep 2972531 = 4458797) B4458797
theorem B1981687 : Blo 1981435 1981687 := bstep (se 1 (by rfl) ⟨1486265, by rfl⟩ : syracuseStep 1981687 = 2972531) B2972531
theorem B5356613 : Blo 1981435 5356613 := bbase (se 4 (by rfl) ⟨502182, by rfl⟩ : syracuseStep 5356613 = 1004365) (by norm_num)
theorem B3571075 : Blo 1981435 3571075 := bstep (se 1 (by rfl) ⟨2678306, by rfl⟩ : syracuseStep 3571075 = 5356613) B5356613
theorem B4761433 : Blo 1981435 4761433 := bstep (se 2 (by rfl) ⟨1785537, by rfl⟩ : syracuseStep 4761433 = 3571075) B3571075
theorem B6348577 : Blo 1981435 6348577 := bstep (se 2 (by rfl) ⟨2380716, by rfl⟩ : syracuseStep 6348577 = 4761433) B4761433
theorem B8464769 : Blo 1981435 8464769 := bstep (se 2 (by rfl) ⟨3174288, by rfl⟩ : syracuseStep 8464769 = 6348577) B6348577
theorem B5643179 : Blo 1981435 5643179 := bstep (se 1 (by rfl) ⟨4232384, by rfl⟩ : syracuseStep 5643179 = 8464769) B8464769
theorem B3762119 : Blo 1981435 3762119 := bstep (se 1 (by rfl) ⟨2821589, by rfl⟩ : syracuseStep 3762119 = 5643179) B5643179
theorem B2508079 : Blo 1981435 2508079 := bstep (se 1 (by rfl) ⟨1881059, by rfl⟩ : syracuseStep 2508079 = 3762119) B3762119
theorem B3344105 : Blo 1981435 3344105 := bstep (se 2 (by rfl) ⟨1254039, by rfl⟩ : syracuseStep 3344105 = 2508079) B2508079
theorem B2229403 : Blo 1981435 2229403 := bstep (se 1 (by rfl) ⟨1672052, by rfl⟩ : syracuseStep 2229403 = 3344105) B3344105
theorem B2972537 : Blo 1981435 2972537 := bstep (se 2 (by rfl) ⟨1114701, by rfl⟩ : syracuseStep 2972537 = 2229403) B2229403
theorem B1981691 : Blo 1981435 1981691 := bstep (se 1 (by rfl) ⟨1486268, by rfl⟩ : syracuseStep 1981691 = 2972537) B2972537
theorem B2008733 : Blo 1981435 2008733 := bbase (se 3 (by rfl) ⟨376637, by rfl⟩ : syracuseStep 2008733 = 753275) (by norm_num)
theorem B5356621 : Blo 1981435 5356621 := bstep (se 3 (by rfl) ⟨1004366, by rfl⟩ : syracuseStep 5356621 = 2008733) B2008733
theorem B28568645 : Blo 1981435 28568645 := bstep (se 4 (by rfl) ⟨2678310, by rfl⟩ : syracuseStep 28568645 = 5356621) B5356621
theorem B19045763 : Blo 1981435 19045763 := bstep (se 1 (by rfl) ⟨14284322, by rfl⟩ : syracuseStep 19045763 = 28568645) B28568645
theorem B12697175 : Blo 1981435 12697175 := bstep (se 1 (by rfl) ⟨9522881, by rfl⟩ : syracuseStep 12697175 = 19045763) B19045763
theorem B33859133 : Blo 1981435 33859133 := bstep (se 3 (by rfl) ⟨6348587, by rfl⟩ : syracuseStep 33859133 = 12697175) B12697175
theorem B22572755 : Blo 1981435 22572755 := bstep (se 1 (by rfl) ⟨16929566, by rfl⟩ : syracuseStep 22572755 = 33859133) B33859133
theorem B15048503 : Blo 1981435 15048503 := bstep (se 1 (by rfl) ⟨11286377, by rfl⟩ : syracuseStep 15048503 = 22572755) B22572755
theorem B10032335 : Blo 1981435 10032335 := bstep (se 1 (by rfl) ⟨7524251, by rfl⟩ : syracuseStep 10032335 = 15048503) B15048503
theorem B6688223 : Blo 1981435 6688223 := bstep (se 1 (by rfl) ⟨5016167, by rfl⟩ : syracuseStep 6688223 = 10032335) B10032335
theorem B4458815 : Blo 1981435 4458815 := bstep (se 1 (by rfl) ⟨3344111, by rfl⟩ : syracuseStep 4458815 = 6688223) B6688223
theorem B2972543 : Blo 1981435 2972543 := bstep (se 1 (by rfl) ⟨2229407, by rfl⟩ : syracuseStep 2972543 = 4458815) B4458815
theorem B1981695 : Blo 1981435 1981695 := bstep (se 1 (by rfl) ⟨1486271, by rfl⟩ : syracuseStep 1981695 = 2972543) B2972543
theorem B2972549 : Blo 1981435 2972549 := bbase (se 4 (by rfl) ⟨278676, by rfl⟩ : syracuseStep 2972549 = 557353) (by norm_num)
theorem B1981699 : Blo 1981435 1981699 := bstep (se 1 (by rfl) ⟨1486274, by rfl⟩ : syracuseStep 1981699 = 2972549) B2972549
theorem B3344125 : Blo 1981435 3344125 := bbase (se 3 (by rfl) ⟨627023, by rfl⟩ : syracuseStep 3344125 = 1254047) (by norm_num)
theorem B4458833 : Blo 1981435 4458833 := bstep (se 2 (by rfl) ⟨1672062, by rfl⟩ : syracuseStep 4458833 = 3344125) B3344125
theorem B2972555 : Blo 1981435 2972555 := bstep (se 1 (by rfl) ⟨2229416, by rfl⟩ : syracuseStep 2972555 = 4458833) B4458833
theorem B1981703 : Blo 1981435 1981703 := bstep (se 1 (by rfl) ⟨1486277, by rfl⟩ : syracuseStep 1981703 = 2972555) B2972555
theorem B2229421 : Blo 1981435 2229421 := bbase (se 3 (by rfl) ⟨418016, by rfl⟩ : syracuseStep 2229421 = 836033) (by norm_num)
theorem B2972561 : Blo 1981435 2972561 := bstep (se 2 (by rfl) ⟨1114710, by rfl⟩ : syracuseStep 2972561 = 2229421) B2229421
theorem B1981707 : Blo 1981435 1981707 := bstep (se 1 (by rfl) ⟨1486280, by rfl⟩ : syracuseStep 1981707 = 2972561) B2972561
theorem B6688277 : Blo 1981435 6688277 := bbase (se 6 (by rfl) ⟨156756, by rfl⟩ : syracuseStep 6688277 = 313513) (by norm_num)
theorem B4458851 : Blo 1981435 4458851 := bstep (se 1 (by rfl) ⟨3344138, by rfl⟩ : syracuseStep 4458851 = 6688277) B6688277
theorem B2972567 : Blo 1981435 2972567 := bstep (se 1 (by rfl) ⟨2229425, by rfl⟩ : syracuseStep 2972567 = 4458851) B4458851
theorem B1981711 : Blo 1981435 1981711 := bstep (se 1 (by rfl) ⟨1486283, by rfl⟩ : syracuseStep 1981711 = 2972567) B2972567
theorem B2972573 : Blo 1981435 2972573 := bbase (se 3 (by rfl) ⟨557357, by rfl⟩ : syracuseStep 2972573 = 1114715) (by norm_num)
theorem B1981715 : Blo 1981435 1981715 := bstep (se 1 (by rfl) ⟨1486286, by rfl⟩ : syracuseStep 1981715 = 2972573) B2972573
theorem B4458869 : Blo 1981435 4458869 := bbase (se 5 (by rfl) ⟨209009, by rfl⟩ : syracuseStep 4458869 = 418019) (by norm_num)
theorem B2972579 : Blo 1981435 2972579 := bstep (se 1 (by rfl) ⟨2229434, by rfl⟩ : syracuseStep 2972579 = 4458869) B4458869
theorem B1981719 : Blo 1981435 1981719 := bstep (se 1 (by rfl) ⟨1486289, by rfl⟩ : syracuseStep 1981719 = 2972579) B2972579
theorem B4761509 : Blo 1981435 4761509 := bbase (se 4 (by rfl) ⟨446391, by rfl⟩ : syracuseStep 4761509 = 892783) (by norm_num)
theorem B12697357 : Blo 1981435 12697357 := bstep (se 3 (by rfl) ⟨2380754, by rfl⟩ : syracuseStep 12697357 = 4761509) B4761509
theorem B16929809 : Blo 1981435 16929809 := bstep (se 2 (by rfl) ⟨6348678, by rfl⟩ : syracuseStep 16929809 = 12697357) B12697357
theorem B11286539 : Blo 1981435 11286539 := bstep (se 1 (by rfl) ⟨8464904, by rfl⟩ : syracuseStep 11286539 = 16929809) B16929809
theorem B7524359 : Blo 1981435 7524359 := bstep (se 1 (by rfl) ⟨5643269, by rfl⟩ : syracuseStep 7524359 = 11286539) B11286539
theorem B5016239 : Blo 1981435 5016239 := bstep (se 1 (by rfl) ⟨3762179, by rfl⟩ : syracuseStep 5016239 = 7524359) B7524359
theorem B3344159 : Blo 1981435 3344159 := bstep (se 1 (by rfl) ⟨2508119, by rfl⟩ : syracuseStep 3344159 = 5016239) B5016239
theorem B2229439 : Blo 1981435 2229439 := bstep (se 1 (by rfl) ⟨1672079, by rfl⟩ : syracuseStep 2229439 = 3344159) B3344159
theorem B2972585 : Blo 1981435 2972585 := bstep (se 2 (by rfl) ⟨1114719, by rfl⟩ : syracuseStep 2972585 = 2229439) B2229439
theorem B1981723 : Blo 1981435 1981723 := bstep (se 1 (by rfl) ⟨1486292, by rfl⟩ : syracuseStep 1981723 = 2972585) B2972585
theorem B7524373 : Blo 1981435 7524373 := bbase (se 6 (by rfl) ⟨176352, by rfl⟩ : syracuseStep 7524373 = 352705) (by norm_num)
theorem B10032497 : Blo 1981435 10032497 := bstep (se 2 (by rfl) ⟨3762186, by rfl⟩ : syracuseStep 10032497 = 7524373) B7524373
theorem B6688331 : Blo 1981435 6688331 := bstep (se 1 (by rfl) ⟨5016248, by rfl⟩ : syracuseStep 6688331 = 10032497) B10032497
theorem B4458887 : Blo 1981435 4458887 := bstep (se 1 (by rfl) ⟨3344165, by rfl⟩ : syracuseStep 4458887 = 6688331) B6688331
theorem B2972591 : Blo 1981435 2972591 := bstep (se 1 (by rfl) ⟨2229443, by rfl⟩ : syracuseStep 2972591 = 4458887) B4458887
theorem B1981727 : Blo 1981435 1981727 := bstep (se 1 (by rfl) ⟨1486295, by rfl⟩ : syracuseStep 1981727 = 2972591) B2972591
theorem B2972597 : Blo 1981435 2972597 := bbase (se 5 (by rfl) ⟨139340, by rfl⟩ : syracuseStep 2972597 = 278681) (by norm_num)
theorem B1981731 : Blo 1981435 1981731 := bstep (se 1 (by rfl) ⟨1486298, by rfl⟩ : syracuseStep 1981731 = 2972597) B2972597
theorem B5016269 : Blo 1981435 5016269 := bbase (se 3 (by rfl) ⟨940550, by rfl⟩ : syracuseStep 5016269 = 1881101) (by norm_num)
theorem B3344179 : Blo 1981435 3344179 := bstep (se 1 (by rfl) ⟨2508134, by rfl⟩ : syracuseStep 3344179 = 5016269) B5016269
theorem B4458905 : Blo 1981435 4458905 := bstep (se 2 (by rfl) ⟨1672089, by rfl⟩ : syracuseStep 4458905 = 3344179) B3344179
theorem B2972603 : Blo 1981435 2972603 := bstep (se 1 (by rfl) ⟨2229452, by rfl⟩ : syracuseStep 2972603 = 4458905) B4458905
theorem B1981735 : Blo 1981435 1981735 := bstep (se 1 (by rfl) ⟨1486301, by rfl⟩ : syracuseStep 1981735 = 2972603) B2972603
theorem B2229457 : Blo 1981435 2229457 := bbase (se 2 (by rfl) ⟨836046, by rfl⟩ : syracuseStep 2229457 = 1672093) (by norm_num)
theorem B2972609 : Blo 1981435 2972609 := bstep (se 2 (by rfl) ⟨1114728, by rfl⟩ : syracuseStep 2972609 = 2229457) B2229457
theorem B1981739 : Blo 1981435 1981739 := bstep (se 1 (by rfl) ⟨1486304, by rfl⟩ : syracuseStep 1981739 = 2972609) B2972609
theorem B8580485 : Blo 1981435 8580485 := bbase (se 4 (by rfl) ⟨804420, by rfl⟩ : syracuseStep 8580485 = 1608841) (by norm_num)
theorem B5720323 : Blo 1981435 5720323 := bstep (se 1 (by rfl) ⟨4290242, by rfl⟩ : syracuseStep 5720323 = 8580485) B8580485
theorem B7627097 : Blo 1981435 7627097 := bstep (se 2 (by rfl) ⟨2860161, by rfl⟩ : syracuseStep 7627097 = 5720323) B5720323
theorem B5084731 : Blo 1981435 5084731 := bstep (se 1 (by rfl) ⟨3813548, by rfl⟩ : syracuseStep 5084731 = 7627097) B7627097
theorem B6779641 : Blo 1981435 6779641 := bstep (se 2 (by rfl) ⟨2542365, by rfl⟩ : syracuseStep 6779641 = 5084731) B5084731
theorem B9039521 : Blo 1981435 9039521 := bstep (se 2 (by rfl) ⟨3389820, by rfl⟩ : syracuseStep 9039521 = 6779641) B6779641
theorem B6026347 : Blo 1981435 6026347 := bstep (se 1 (by rfl) ⟨4519760, by rfl⟩ : syracuseStep 6026347 = 9039521) B9039521
theorem B8035129 : Blo 1981435 8035129 := bstep (se 2 (by rfl) ⟨3013173, by rfl⟩ : syracuseStep 8035129 = 6026347) B6026347
theorem B10713505 : Blo 1981435 10713505 := bstep (se 2 (by rfl) ⟨4017564, by rfl⟩ : syracuseStep 10713505 = 8035129) B8035129
theorem B14284673 : Blo 1981435 14284673 := bstep (se 2 (by rfl) ⟨5356752, by rfl⟩ : syracuseStep 14284673 = 10713505) B10713505
theorem B9523115 : Blo 1981435 9523115 := bstep (se 1 (by rfl) ⟨7142336, by rfl⟩ : syracuseStep 9523115 = 14284673) B14284673
theorem B6348743 : Blo 1981435 6348743 := bstep (se 1 (by rfl) ⟨4761557, by rfl⟩ : syracuseStep 6348743 = 9523115) B9523115
theorem B4232495 : Blo 1981435 4232495 := bstep (se 1 (by rfl) ⟨3174371, by rfl⟩ : syracuseStep 4232495 = 6348743) B6348743
theorem B2821663 : Blo 1981435 2821663 := bstep (se 1 (by rfl) ⟨2116247, by rfl⟩ : syracuseStep 2821663 = 4232495) B4232495
theorem B3762217 : Blo 1981435 3762217 := bstep (se 2 (by rfl) ⟨1410831, by rfl⟩ : syracuseStep 3762217 = 2821663) B2821663
theorem B5016289 : Blo 1981435 5016289 := bstep (se 2 (by rfl) ⟨1881108, by rfl⟩ : syracuseStep 5016289 = 3762217) B3762217
theorem B6688385 : Blo 1981435 6688385 := bstep (se 2 (by rfl) ⟨2508144, by rfl⟩ : syracuseStep 6688385 = 5016289) B5016289
theorem B4458923 : Blo 1981435 4458923 := bstep (se 1 (by rfl) ⟨3344192, by rfl⟩ : syracuseStep 4458923 = 6688385) B6688385
theorem B2972615 : Blo 1981435 2972615 := bstep (se 1 (by rfl) ⟨2229461, by rfl⟩ : syracuseStep 2972615 = 4458923) B4458923
theorem B1981743 : Blo 1981435 1981743 := bstep (se 1 (by rfl) ⟨1486307, by rfl⟩ : syracuseStep 1981743 = 2972615) B2972615
theorem B2972621 : Blo 1981435 2972621 := bbase (se 3 (by rfl) ⟨557366, by rfl⟩ : syracuseStep 2972621 = 1114733) (by norm_num)
theorem B1981747 : Blo 1981435 1981747 := bstep (se 1 (by rfl) ⟨1486310, by rfl⟩ : syracuseStep 1981747 = 2972621) B2972621
theorem B4458941 : Blo 1981435 4458941 := bbase (se 3 (by rfl) ⟨836051, by rfl⟩ : syracuseStep 4458941 = 1672103) (by norm_num)
theorem B2972627 : Blo 1981435 2972627 := bstep (se 1 (by rfl) ⟨2229470, by rfl⟩ : syracuseStep 2972627 = 4458941) B4458941
theorem B1981751 : Blo 1981435 1981751 := bstep (se 1 (by rfl) ⟨1486313, by rfl⟩ : syracuseStep 1981751 = 2972627) B2972627
theorem B3344213 : Blo 1981435 3344213 := bbase (se 9 (by rfl) ⟨9797, by rfl⟩ : syracuseStep 3344213 = 19595) (by norm_num)
theorem B2229475 : Blo 1981435 2229475 := bstep (se 1 (by rfl) ⟨1672106, by rfl⟩ : syracuseStep 2229475 = 3344213) B3344213
theorem B2972633 : Blo 1981435 2972633 := bstep (se 2 (by rfl) ⟨1114737, by rfl⟩ : syracuseStep 2972633 = 2229475) B2229475
theorem B1981755 : Blo 1981435 1981755 := bstep (se 1 (by rfl) ⟨1486316, by rfl⟩ : syracuseStep 1981755 = 2972633) B2972633
theorem B2714941 : Blo 1981435 2714941 := bbase (se 3 (by rfl) ⟨509051, by rfl⟩ : syracuseStep 2714941 = 1018103) (by norm_num)
theorem B3619921 : Blo 1981435 3619921 := bstep (se 2 (by rfl) ⟨1357470, by rfl⟩ : syracuseStep 3619921 = 2714941) B2714941
theorem B4826561 : Blo 1981435 4826561 := bstep (se 2 (by rfl) ⟨1809960, by rfl⟩ : syracuseStep 4826561 = 3619921) B3619921
theorem B12870829 : Blo 1981435 12870829 := bstep (se 3 (by rfl) ⟨2413280, by rfl⟩ : syracuseStep 12870829 = 4826561) B4826561
theorem B17161105 : Blo 1981435 17161105 := bstep (se 2 (by rfl) ⟨6435414, by rfl⟩ : syracuseStep 17161105 = 12870829) B12870829
theorem B22881473 : Blo 1981435 22881473 := bstep (se 2 (by rfl) ⟨8580552, by rfl⟩ : syracuseStep 22881473 = 17161105) B17161105
theorem B15254315 : Blo 1981435 15254315 := bstep (se 1 (by rfl) ⟨11440736, by rfl⟩ : syracuseStep 15254315 = 22881473) B22881473
theorem B10169543 : Blo 1981435 10169543 := bstep (se 1 (by rfl) ⟨7627157, by rfl⟩ : syracuseStep 10169543 = 15254315) B15254315
theorem B6779695 : Blo 1981435 6779695 := bstep (se 1 (by rfl) ⟨5084771, by rfl⟩ : syracuseStep 6779695 = 10169543) B10169543
theorem B9039593 : Blo 1981435 9039593 := bstep (se 2 (by rfl) ⟨3389847, by rfl⟩ : syracuseStep 9039593 = 6779695) B6779695
theorem B6026395 : Blo 1981435 6026395 := bstep (se 1 (by rfl) ⟨4519796, by rfl⟩ : syracuseStep 6026395 = 9039593) B9039593
theorem B8035193 : Blo 1981435 8035193 := bstep (se 2 (by rfl) ⟨3013197, by rfl⟩ : syracuseStep 8035193 = 6026395) B6026395
theorem B5356795 : Blo 1981435 5356795 := bstep (se 1 (by rfl) ⟨4017596, by rfl⟩ : syracuseStep 5356795 = 8035193) B8035193
theorem B7142393 : Blo 1981435 7142393 := bstep (se 2 (by rfl) ⟨2678397, by rfl⟩ : syracuseStep 7142393 = 5356795) B5356795
theorem B4761595 : Blo 1981435 4761595 := bstep (se 1 (by rfl) ⟨3571196, by rfl⟩ : syracuseStep 4761595 = 7142393) B7142393
theorem B6348793 : Blo 1981435 6348793 := bstep (se 2 (by rfl) ⟨2380797, by rfl⟩ : syracuseStep 6348793 = 4761595) B4761595
theorem B8465057 : Blo 1981435 8465057 := bstep (se 2 (by rfl) ⟨3174396, by rfl⟩ : syracuseStep 8465057 = 6348793) B6348793
theorem B5643371 : Blo 1981435 5643371 := bstep (se 1 (by rfl) ⟨4232528, by rfl⟩ : syracuseStep 5643371 = 8465057) B8465057
theorem B15048989 : Blo 1981435 15048989 := bstep (se 3 (by rfl) ⟨2821685, by rfl⟩ : syracuseStep 15048989 = 5643371) B5643371
theorem B10032659 : Blo 1981435 10032659 := bstep (se 1 (by rfl) ⟨7524494, by rfl⟩ : syracuseStep 10032659 = 15048989) B15048989
theorem B6688439 : Blo 1981435 6688439 := bstep (se 1 (by rfl) ⟨5016329, by rfl⟩ : syracuseStep 6688439 = 10032659) B10032659
theorem B4458959 : Blo 1981435 4458959 := bstep (se 1 (by rfl) ⟨3344219, by rfl⟩ : syracuseStep 4458959 = 6688439) B6688439
theorem B2972639 : Blo 1981435 2972639 := bstep (se 1 (by rfl) ⟨2229479, by rfl⟩ : syracuseStep 2972639 = 4458959) B4458959
theorem B1981759 : Blo 1981435 1981759 := bstep (se 1 (by rfl) ⟨1486319, by rfl⟩ : syracuseStep 1981759 = 2972639) B2972639
theorem B2972645 : Blo 1981435 2972645 := bbase (se 4 (by rfl) ⟨278685, by rfl⟩ : syracuseStep 2972645 = 557371) (by norm_num)
theorem B1981763 : Blo 1981435 1981763 := bstep (se 1 (by rfl) ⟨1486322, by rfl⟩ : syracuseStep 1981763 = 2972645) B2972645
theorem B8465093 : Blo 1981435 8465093 := bbase (se 4 (by rfl) ⟨793602, by rfl⟩ : syracuseStep 8465093 = 1587205) (by norm_num)
theorem B5643395 : Blo 1981435 5643395 := bstep (se 1 (by rfl) ⟨4232546, by rfl⟩ : syracuseStep 5643395 = 8465093) B8465093
theorem B3762263 : Blo 1981435 3762263 := bstep (se 1 (by rfl) ⟨2821697, by rfl⟩ : syracuseStep 3762263 = 5643395) B5643395
theorem B2508175 : Blo 1981435 2508175 := bstep (se 1 (by rfl) ⟨1881131, by rfl⟩ : syracuseStep 2508175 = 3762263) B3762263
theorem B3344233 : Blo 1981435 3344233 := bstep (se 2 (by rfl) ⟨1254087, by rfl⟩ : syracuseStep 3344233 = 2508175) B2508175
theorem B4458977 : Blo 1981435 4458977 := bstep (se 2 (by rfl) ⟨1672116, by rfl⟩ : syracuseStep 4458977 = 3344233) B3344233
theorem B2972651 : Blo 1981435 2972651 := bstep (se 1 (by rfl) ⟨2229488, by rfl⟩ : syracuseStep 2972651 = 4458977) B4458977
theorem B1981767 : Blo 1981435 1981767 := bstep (se 1 (by rfl) ⟨1486325, by rfl⟩ : syracuseStep 1981767 = 2972651) B2972651
theorem B2229493 : Blo 1981435 2229493 := bbase (se 5 (by rfl) ⟨104507, by rfl⟩ : syracuseStep 2229493 = 209015) (by norm_num)
theorem B2972657 : Blo 1981435 2972657 := bstep (se 2 (by rfl) ⟨1114746, by rfl⟩ : syracuseStep 2972657 = 2229493) B2229493
theorem B1981771 : Blo 1981435 1981771 := bstep (se 1 (by rfl) ⟨1486328, by rfl⟩ : syracuseStep 1981771 = 2972657) B2972657
theorem B2508185 : Blo 1981435 2508185 := bbase (se 2 (by rfl) ⟨940569, by rfl⟩ : syracuseStep 2508185 = 1881139) (by norm_num)
theorem B6688493 : Blo 1981435 6688493 := bstep (se 3 (by rfl) ⟨1254092, by rfl⟩ : syracuseStep 6688493 = 2508185) B2508185
theorem B4458995 : Blo 1981435 4458995 := bstep (se 1 (by rfl) ⟨3344246, by rfl⟩ : syracuseStep 4458995 = 6688493) B6688493
theorem B2972663 : Blo 1981435 2972663 := bstep (se 1 (by rfl) ⟨2229497, by rfl⟩ : syracuseStep 2972663 = 4458995) B4458995
theorem B1981775 : Blo 1981435 1981775 := bstep (se 1 (by rfl) ⟨1486331, by rfl⟩ : syracuseStep 1981775 = 2972663) B2972663
theorem B2972669 : Blo 1981435 2972669 := bbase (se 3 (by rfl) ⟨557375, by rfl⟩ : syracuseStep 2972669 = 1114751) (by norm_num)
theorem B1981779 : Blo 1981435 1981779 := bstep (se 1 (by rfl) ⟨1486334, by rfl⟩ : syracuseStep 1981779 = 2972669) B2972669
theorem B4459013 : Blo 1981435 4459013 := bbase (se 4 (by rfl) ⟨418032, by rfl⟩ : syracuseStep 4459013 = 836065) (by norm_num)
theorem B2972675 : Blo 1981435 2972675 := bstep (se 1 (by rfl) ⟨2229506, by rfl⟩ : syracuseStep 2972675 = 4459013) B4459013
theorem B1981783 : Blo 1981435 1981783 := bstep (se 1 (by rfl) ⟨1486337, by rfl⟩ : syracuseStep 1981783 = 2972675) B2972675
theorem B3762301 : Blo 1981435 3762301 := bbase (se 3 (by rfl) ⟨705431, by rfl⟩ : syracuseStep 3762301 = 1410863) (by norm_num)
theorem B5016401 : Blo 1981435 5016401 := bstep (se 2 (by rfl) ⟨1881150, by rfl⟩ : syracuseStep 5016401 = 3762301) B3762301
theorem B3344267 : Blo 1981435 3344267 := bstep (se 1 (by rfl) ⟨2508200, by rfl⟩ : syracuseStep 3344267 = 5016401) B5016401
theorem B2229511 : Blo 1981435 2229511 := bstep (se 1 (by rfl) ⟨1672133, by rfl⟩ : syracuseStep 2229511 = 3344267) B3344267
theorem B2972681 : Blo 1981435 2972681 := bstep (se 2 (by rfl) ⟨1114755, by rfl⟩ : syracuseStep 2972681 = 2229511) B2229511
theorem B1981787 : Blo 1981435 1981787 := bstep (se 1 (by rfl) ⟨1486340, by rfl⟩ : syracuseStep 1981787 = 2972681) B2972681
theorem B10032821 : Blo 1981435 10032821 := bbase (se 5 (by rfl) ⟨470288, by rfl⟩ : syracuseStep 10032821 = 940577) (by norm_num)
theorem B6688547 : Blo 1981435 6688547 := bstep (se 1 (by rfl) ⟨5016410, by rfl⟩ : syracuseStep 6688547 = 10032821) B10032821
theorem B4459031 : Blo 1981435 4459031 := bstep (se 1 (by rfl) ⟨3344273, by rfl⟩ : syracuseStep 4459031 = 6688547) B6688547
theorem B2972687 : Blo 1981435 2972687 := bstep (se 1 (by rfl) ⟨2229515, by rfl⟩ : syracuseStep 2972687 = 4459031) B4459031
theorem B1981791 : Blo 1981435 1981791 := bstep (se 1 (by rfl) ⟨1486343, by rfl⟩ : syracuseStep 1981791 = 2972687) B2972687
theorem B2972693 : Blo 1981435 2972693 := bbase (se 6 (by rfl) ⟨69672, by rfl⟩ : syracuseStep 2972693 = 139345) (by norm_num)
theorem B1981795 : Blo 1981435 1981795 := bstep (se 1 (by rfl) ⟨1486346, by rfl⟩ : syracuseStep 1981795 = 2972693) B2972693
theorem B9163109 : Blo 1981435 9163109 := bbase (se 4 (by rfl) ⟨859041, by rfl⟩ : syracuseStep 9163109 = 1718083) (by norm_num)
theorem B6108739 : Blo 1981435 6108739 := bstep (se 1 (by rfl) ⟨4581554, by rfl⟩ : syracuseStep 6108739 = 9163109) B9163109
theorem B32579941 : Blo 1981435 32579941 := bstep (se 4 (by rfl) ⟨3054369, by rfl⟩ : syracuseStep 32579941 = 6108739) B6108739
theorem B43439921 : Blo 1981435 43439921 := bstep (se 2 (by rfl) ⟨16289970, by rfl⟩ : syracuseStep 43439921 = 32579941) B32579941
theorem B28959947 : Blo 1981435 28959947 := bstep (se 1 (by rfl) ⟨21719960, by rfl⟩ : syracuseStep 28959947 = 43439921) B43439921
theorem B19306631 : Blo 1981435 19306631 := bstep (se 1 (by rfl) ⟨14479973, by rfl⟩ : syracuseStep 19306631 = 28959947) B28959947
theorem B51484349 : Blo 1981435 51484349 := bstep (se 3 (by rfl) ⟨9653315, by rfl⟩ : syracuseStep 51484349 = 19306631) B19306631
theorem B34322899 : Blo 1981435 34322899 := bstep (se 1 (by rfl) ⟨25742174, by rfl⟩ : syracuseStep 34322899 = 51484349) B51484349
theorem B45763865 : Blo 1981435 45763865 := bstep (se 2 (by rfl) ⟨17161449, by rfl⟩ : syracuseStep 45763865 = 34322899) B34322899
theorem B30509243 : Blo 1981435 30509243 := bstep (se 1 (by rfl) ⟨22881932, by rfl⟩ : syracuseStep 30509243 = 45763865) B45763865
theorem B20339495 : Blo 1981435 20339495 := bstep (se 1 (by rfl) ⟨15254621, by rfl⟩ : syracuseStep 20339495 = 30509243) B30509243
theorem B13559663 : Blo 1981435 13559663 := bstep (se 1 (by rfl) ⟨10169747, by rfl⟩ : syracuseStep 13559663 = 20339495) B20339495
theorem B9039775 : Blo 1981435 9039775 := bstep (se 1 (by rfl) ⟨6779831, by rfl⟩ : syracuseStep 9039775 = 13559663) B13559663
theorem B12053033 : Blo 1981435 12053033 := bstep (se 2 (by rfl) ⟨4519887, by rfl⟩ : syracuseStep 12053033 = 9039775) B9039775
theorem B8035355 : Blo 1981435 8035355 := bstep (se 1 (by rfl) ⟨6026516, by rfl⟩ : syracuseStep 8035355 = 12053033) B12053033
theorem B5356903 : Blo 1981435 5356903 := bstep (se 1 (by rfl) ⟨4017677, by rfl⟩ : syracuseStep 5356903 = 8035355) B8035355
theorem B7142537 : Blo 1981435 7142537 := bstep (se 2 (by rfl) ⟨2678451, by rfl⟩ : syracuseStep 7142537 = 5356903) B5356903
theorem B19046765 : Blo 1981435 19046765 := bstep (se 3 (by rfl) ⟨3571268, by rfl⟩ : syracuseStep 19046765 = 7142537) B7142537
theorem B12697843 : Blo 1981435 12697843 := bstep (se 1 (by rfl) ⟨9523382, by rfl⟩ : syracuseStep 12697843 = 19046765) B19046765
theorem B16930457 : Blo 1981435 16930457 := bstep (se 2 (by rfl) ⟨6348921, by rfl⟩ : syracuseStep 16930457 = 12697843) B12697843
theorem B11286971 : Blo 1981435 11286971 := bstep (se 1 (by rfl) ⟨8465228, by rfl⟩ : syracuseStep 11286971 = 16930457) B16930457
theorem B7524647 : Blo 1981435 7524647 := bstep (se 1 (by rfl) ⟨5643485, by rfl⟩ : syracuseStep 7524647 = 11286971) B11286971
theorem B5016431 : Blo 1981435 5016431 := bstep (se 1 (by rfl) ⟨3762323, by rfl⟩ : syracuseStep 5016431 = 7524647) B7524647
theorem B3344287 : Blo 1981435 3344287 := bstep (se 1 (by rfl) ⟨2508215, by rfl⟩ : syracuseStep 3344287 = 5016431) B5016431
theorem B4459049 : Blo 1981435 4459049 := bstep (se 2 (by rfl) ⟨1672143, by rfl⟩ : syracuseStep 4459049 = 3344287) B3344287
theorem B2972699 : Blo 1981435 2972699 := bstep (se 1 (by rfl) ⟨2229524, by rfl⟩ : syracuseStep 2972699 = 4459049) B4459049
theorem B1981799 : Blo 1981435 1981799 := bstep (se 1 (by rfl) ⟨1486349, by rfl⟩ : syracuseStep 1981799 = 2972699) B2972699
theorem B2229529 : Blo 1981435 2229529 := bbase (se 2 (by rfl) ⟨836073, by rfl⟩ : syracuseStep 2229529 = 1672147) (by norm_num)
theorem B2972705 : Blo 1981435 2972705 := bstep (se 2 (by rfl) ⟨1114764, by rfl⟩ : syracuseStep 2972705 = 2229529) B2229529
theorem B1981803 : Blo 1981435 1981803 := bstep (se 1 (by rfl) ⟨1486352, by rfl⟩ : syracuseStep 1981803 = 2972705) B2972705
theorem B7524677 : Blo 1981435 7524677 := bbase (se 4 (by rfl) ⟨705438, by rfl⟩ : syracuseStep 7524677 = 1410877) (by norm_num)
theorem B5016451 : Blo 1981435 5016451 := bstep (se 1 (by rfl) ⟨3762338, by rfl⟩ : syracuseStep 5016451 = 7524677) B7524677
theorem B6688601 : Blo 1981435 6688601 := bstep (se 2 (by rfl) ⟨2508225, by rfl⟩ : syracuseStep 6688601 = 5016451) B5016451
theorem B4459067 : Blo 1981435 4459067 := bstep (se 1 (by rfl) ⟨3344300, by rfl⟩ : syracuseStep 4459067 = 6688601) B6688601
theorem B2972711 : Blo 1981435 2972711 := bstep (se 1 (by rfl) ⟨2229533, by rfl⟩ : syracuseStep 2972711 = 4459067) B4459067
theorem B1981807 : Blo 1981435 1981807 := bstep (se 1 (by rfl) ⟨1486355, by rfl⟩ : syracuseStep 1981807 = 2972711) B2972711
theorem B2972717 : Blo 1981435 2972717 := bbase (se 3 (by rfl) ⟨557384, by rfl⟩ : syracuseStep 2972717 = 1114769) (by norm_num)
theorem B1981811 : Blo 1981435 1981811 := bstep (se 1 (by rfl) ⟨1486358, by rfl⟩ : syracuseStep 1981811 = 2972717) B2972717
theorem B4459085 : Blo 1981435 4459085 := bbase (se 3 (by rfl) ⟨836078, by rfl⟩ : syracuseStep 4459085 = 1672157) (by norm_num)
theorem B2972723 : Blo 1981435 2972723 := bstep (se 1 (by rfl) ⟨2229542, by rfl⟩ : syracuseStep 2972723 = 4459085) B4459085
theorem B1981815 : Blo 1981435 1981815 := bstep (se 1 (by rfl) ⟨1486361, by rfl⟩ : syracuseStep 1981815 = 2972723) B2972723
theorem B2508241 : Blo 1981435 2508241 := bbase (se 2 (by rfl) ⟨940590, by rfl⟩ : syracuseStep 2508241 = 1881181) (by norm_num)
theorem B3344321 : Blo 1981435 3344321 := bstep (se 2 (by rfl) ⟨1254120, by rfl⟩ : syracuseStep 3344321 = 2508241) B2508241
theorem B2229547 : Blo 1981435 2229547 := bstep (se 1 (by rfl) ⟨1672160, by rfl⟩ : syracuseStep 2229547 = 3344321) B3344321
theorem B2972729 : Blo 1981435 2972729 := bstep (se 2 (by rfl) ⟨1114773, by rfl⟩ : syracuseStep 2972729 = 2229547) B2229547
theorem B1981819 : Blo 1981435 1981819 := bstep (se 1 (by rfl) ⟨1486364, by rfl⟩ : syracuseStep 1981819 = 2972729) B2972729
theorem B4761749 : Blo 1981435 4761749 := bbase (se 6 (by rfl) ⟨111603, by rfl⟩ : syracuseStep 4761749 = 223207) (by norm_num)
theorem B3174499 : Blo 1981435 3174499 := bstep (se 1 (by rfl) ⟨2380874, by rfl⟩ : syracuseStep 3174499 = 4761749) B4761749
theorem B4232665 : Blo 1981435 4232665 := bstep (se 2 (by rfl) ⟨1587249, by rfl⟩ : syracuseStep 4232665 = 3174499) B3174499
theorem B22574213 : Blo 1981435 22574213 := bstep (se 4 (by rfl) ⟨2116332, by rfl⟩ : syracuseStep 22574213 = 4232665) B4232665
theorem B15049475 : Blo 1981435 15049475 := bstep (se 1 (by rfl) ⟨11287106, by rfl⟩ : syracuseStep 15049475 = 22574213) B22574213
theorem B10032983 : Blo 1981435 10032983 := bstep (se 1 (by rfl) ⟨7524737, by rfl⟩ : syracuseStep 10032983 = 15049475) B15049475
theorem B6688655 : Blo 1981435 6688655 := bstep (se 1 (by rfl) ⟨5016491, by rfl⟩ : syracuseStep 6688655 = 10032983) B10032983
theorem B4459103 : Blo 1981435 4459103 := bstep (se 1 (by rfl) ⟨3344327, by rfl⟩ : syracuseStep 4459103 = 6688655) B6688655
theorem B2972735 : Blo 1981435 2972735 := bstep (se 1 (by rfl) ⟨2229551, by rfl⟩ : syracuseStep 2972735 = 4459103) B4459103
theorem B1981823 : Blo 1981435 1981823 := bstep (se 1 (by rfl) ⟨1486367, by rfl⟩ : syracuseStep 1981823 = 2972735) B2972735
theorem B2972741 : Blo 1981435 2972741 := bbase (se 4 (by rfl) ⟨278694, by rfl⟩ : syracuseStep 2972741 = 557389) (by norm_num)
theorem B1981827 : Blo 1981435 1981827 := bstep (se 1 (by rfl) ⟨1486370, by rfl⟩ : syracuseStep 1981827 = 2972741) B2972741
theorem B3344341 : Blo 1981435 3344341 := bbase (se 7 (by rfl) ⟨39191, by rfl⟩ : syracuseStep 3344341 = 78383) (by norm_num)
theorem B4459121 : Blo 1981435 4459121 := bstep (se 2 (by rfl) ⟨1672170, by rfl⟩ : syracuseStep 4459121 = 3344341) B3344341
theorem B2972747 : Blo 1981435 2972747 := bstep (se 1 (by rfl) ⟨2229560, by rfl⟩ : syracuseStep 2972747 = 4459121) B4459121
theorem B1981831 : Blo 1981435 1981831 := bstep (se 1 (by rfl) ⟨1486373, by rfl⟩ : syracuseStep 1981831 = 2972747) B2972747
theorem B2229565 : Blo 1981435 2229565 := bbase (se 3 (by rfl) ⟨418043, by rfl⟩ : syracuseStep 2229565 = 836087) (by norm_num)
theorem B2972753 : Blo 1981435 2972753 := bstep (se 2 (by rfl) ⟨1114782, by rfl⟩ : syracuseStep 2972753 = 2229565) B2229565
theorem B1981835 : Blo 1981435 1981835 := bstep (se 1 (by rfl) ⟨1486376, by rfl⟩ : syracuseStep 1981835 = 2972753) B2972753
theorem B6688709 : Blo 1981435 6688709 := bbase (se 4 (by rfl) ⟨627066, by rfl⟩ : syracuseStep 6688709 = 1254133) (by norm_num)
theorem B4459139 : Blo 1981435 4459139 := bstep (se 1 (by rfl) ⟨3344354, by rfl⟩ : syracuseStep 4459139 = 6688709) B6688709
theorem B2972759 : Blo 1981435 2972759 := bstep (se 1 (by rfl) ⟨2229569, by rfl⟩ : syracuseStep 2972759 = 4459139) B4459139
theorem B1981839 : Blo 1981435 1981839 := bstep (se 1 (by rfl) ⟨1486379, by rfl⟩ : syracuseStep 1981839 = 2972759) B2972759
theorem B2972765 : Blo 1981435 2972765 := bbase (se 3 (by rfl) ⟨557393, by rfl⟩ : syracuseStep 2972765 = 1114787) (by norm_num)
theorem B1981843 : Blo 1981435 1981843 := bstep (se 1 (by rfl) ⟨1486382, by rfl⟩ : syracuseStep 1981843 = 2972765) B2972765
theorem B4459157 : Blo 1981435 4459157 := bbase (se 6 (by rfl) ⟨104511, by rfl⟩ : syracuseStep 4459157 = 209023) (by norm_num)
theorem B2972771 : Blo 1981435 2972771 := bstep (se 1 (by rfl) ⟨2229578, by rfl⟩ : syracuseStep 2972771 = 4459157) B4459157
theorem B1981847 : Blo 1981435 1981847 := bstep (se 1 (by rfl) ⟨1486385, by rfl⟩ : syracuseStep 1981847 = 2972771) B2972771
theorem B2380909 : Blo 1981435 2380909 := bbase (se 3 (by rfl) ⟨446420, by rfl⟩ : syracuseStep 2380909 = 892841) (by norm_num)
theorem B3174545 : Blo 1981435 3174545 := bstep (se 2 (by rfl) ⟨1190454, by rfl⟩ : syracuseStep 3174545 = 2380909) B2380909
theorem B2116363 : Blo 1981435 2116363 := bstep (se 1 (by rfl) ⟨1587272, by rfl⟩ : syracuseStep 2116363 = 3174545) B3174545
theorem B2821817 : Blo 1981435 2821817 := bstep (se 2 (by rfl) ⟨1058181, by rfl⟩ : syracuseStep 2821817 = 2116363) B2116363
theorem B7524845 : Blo 1981435 7524845 := bstep (se 3 (by rfl) ⟨1410908, by rfl⟩ : syracuseStep 7524845 = 2821817) B2821817
theorem B5016563 : Blo 1981435 5016563 := bstep (se 1 (by rfl) ⟨3762422, by rfl⟩ : syracuseStep 5016563 = 7524845) B7524845
theorem B3344375 : Blo 1981435 3344375 := bstep (se 1 (by rfl) ⟨2508281, by rfl⟩ : syracuseStep 3344375 = 5016563) B5016563
theorem B2229583 : Blo 1981435 2229583 := bstep (se 1 (by rfl) ⟨1672187, by rfl⟩ : syracuseStep 2229583 = 3344375) B3344375
theorem B2972777 : Blo 1981435 2972777 := bstep (se 2 (by rfl) ⟨1114791, by rfl⟩ : syracuseStep 2972777 = 2229583) B2229583
theorem B1981851 : Blo 1981435 1981851 := bstep (se 1 (by rfl) ⟨1486388, by rfl⟩ : syracuseStep 1981851 = 2972777) B2972777
theorem B13047061 : Blo 1981435 13047061 := bbase (se 6 (by rfl) ⟨305790, by rfl⟩ : syracuseStep 13047061 = 611581) (by norm_num)
theorem B17396081 : Blo 1981435 17396081 := bstep (se 2 (by rfl) ⟨6523530, by rfl⟩ : syracuseStep 17396081 = 13047061) B13047061
theorem B185558197 : Blo 1981435 185558197 := bstep (se 5 (by rfl) ⟨8698040, by rfl⟩ : syracuseStep 185558197 = 17396081) B17396081
theorem B247410929 : Blo 1981435 247410929 := bstep (se 2 (by rfl) ⟨92779098, by rfl⟩ : syracuseStep 247410929 = 185558197) B185558197
theorem B164940619 : Blo 1981435 164940619 := bstep (se 1 (by rfl) ⟨123705464, by rfl⟩ : syracuseStep 164940619 = 247410929) B247410929
theorem B219920825 : Blo 1981435 219920825 := bstep (se 2 (by rfl) ⟨82470309, by rfl⟩ : syracuseStep 219920825 = 164940619) B164940619
theorem B146613883 : Blo 1981435 146613883 := bstep (se 1 (by rfl) ⟨109960412, by rfl⟩ : syracuseStep 146613883 = 219920825) B219920825
theorem B195485177 : Blo 1981435 195485177 := bstep (se 2 (by rfl) ⟨73306941, by rfl⟩ : syracuseStep 195485177 = 146613883) B146613883
theorem B130323451 : Blo 1981435 130323451 := bstep (se 1 (by rfl) ⟨97742588, by rfl⟩ : syracuseStep 130323451 = 195485177) B195485177
theorem B173764601 : Blo 1981435 173764601 := bstep (se 2 (by rfl) ⟨65161725, by rfl⟩ : syracuseStep 173764601 = 130323451) B130323451
theorem B115843067 : Blo 1981435 115843067 := bstep (se 1 (by rfl) ⟨86882300, by rfl⟩ : syracuseStep 115843067 = 173764601) B173764601
theorem B77228711 : Blo 1981435 77228711 := bstep (se 1 (by rfl) ⟨57921533, by rfl⟩ : syracuseStep 77228711 = 115843067) B115843067
theorem B51485807 : Blo 1981435 51485807 := bstep (se 1 (by rfl) ⟨38614355, by rfl⟩ : syracuseStep 51485807 = 77228711) B77228711
theorem B34323871 : Blo 1981435 34323871 := bstep (se 1 (by rfl) ⟨25742903, by rfl⟩ : syracuseStep 34323871 = 51485807) B51485807
theorem B45765161 : Blo 1981435 45765161 := bstep (se 2 (by rfl) ⟨17161935, by rfl⟩ : syracuseStep 45765161 = 34323871) B34323871
theorem B30510107 : Blo 1981435 30510107 := bstep (se 1 (by rfl) ⟨22882580, by rfl⟩ : syracuseStep 30510107 = 45765161) B45765161
theorem B20340071 : Blo 1981435 20340071 := bstep (se 1 (by rfl) ⟨15255053, by rfl⟩ : syracuseStep 20340071 = 30510107) B30510107
theorem B13560047 : Blo 1981435 13560047 := bstep (se 1 (by rfl) ⟨10170035, by rfl⟩ : syracuseStep 13560047 = 20340071) B20340071
theorem B9040031 : Blo 1981435 9040031 := bstep (se 1 (by rfl) ⟨6780023, by rfl⟩ : syracuseStep 9040031 = 13560047) B13560047
theorem B6026687 : Blo 1981435 6026687 := bstep (se 1 (by rfl) ⟨4520015, by rfl⟩ : syracuseStep 6026687 = 9040031) B9040031
theorem B4017791 : Blo 1981435 4017791 := bstep (se 1 (by rfl) ⟨3013343, by rfl⟩ : syracuseStep 4017791 = 6026687) B6026687
theorem B2678527 : Blo 1981435 2678527 := bstep (se 1 (by rfl) ⟨2008895, by rfl⟩ : syracuseStep 2678527 = 4017791) B4017791
theorem B14285477 : Blo 1981435 14285477 := bstep (se 4 (by rfl) ⟨1339263, by rfl⟩ : syracuseStep 14285477 = 2678527) B2678527
theorem B9523651 : Blo 1981435 9523651 := bstep (se 1 (by rfl) ⟨7142738, by rfl⟩ : syracuseStep 9523651 = 14285477) B14285477
theorem B12698201 : Blo 1981435 12698201 := bstep (se 2 (by rfl) ⟨4761825, by rfl⟩ : syracuseStep 12698201 = 9523651) B9523651
theorem B8465467 : Blo 1981435 8465467 := bstep (se 1 (by rfl) ⟨6349100, by rfl⟩ : syracuseStep 8465467 = 12698201) B12698201
theorem B11287289 : Blo 1981435 11287289 := bstep (se 2 (by rfl) ⟨4232733, by rfl⟩ : syracuseStep 11287289 = 8465467) B8465467
theorem B7524859 : Blo 1981435 7524859 := bstep (se 1 (by rfl) ⟨5643644, by rfl⟩ : syracuseStep 7524859 = 11287289) B11287289
theorem B10033145 : Blo 1981435 10033145 := bstep (se 2 (by rfl) ⟨3762429, by rfl⟩ : syracuseStep 10033145 = 7524859) B7524859
theorem B6688763 : Blo 1981435 6688763 := bstep (se 1 (by rfl) ⟨5016572, by rfl⟩ : syracuseStep 6688763 = 10033145) B10033145
theorem B4459175 : Blo 1981435 4459175 := bstep (se 1 (by rfl) ⟨3344381, by rfl⟩ : syracuseStep 4459175 = 6688763) B6688763
theorem B2972783 : Blo 1981435 2972783 := bstep (se 1 (by rfl) ⟨2229587, by rfl⟩ : syracuseStep 2972783 = 4459175) B4459175
theorem B1981855 : Blo 1981435 1981855 := bstep (se 1 (by rfl) ⟨1486391, by rfl⟩ : syracuseStep 1981855 = 2972783) B2972783
theorem B2972789 : Blo 1981435 2972789 := bbase (se 5 (by rfl) ⟨139349, by rfl⟩ : syracuseStep 2972789 = 278699) (by norm_num)
theorem B1981859 : Blo 1981435 1981859 := bstep (se 1 (by rfl) ⟨1486394, by rfl⟩ : syracuseStep 1981859 = 2972789) B2972789
theorem B3762445 : Blo 1981435 3762445 := bbase (se 3 (by rfl) ⟨705458, by rfl⟩ : syracuseStep 3762445 = 1410917) (by norm_num)
theorem B5016593 : Blo 1981435 5016593 := bstep (se 2 (by rfl) ⟨1881222, by rfl⟩ : syracuseStep 5016593 = 3762445) B3762445
theorem B3344395 : Blo 1981435 3344395 := bstep (se 1 (by rfl) ⟨2508296, by rfl⟩ : syracuseStep 3344395 = 5016593) B5016593
theorem B4459193 : Blo 1981435 4459193 := bstep (se 2 (by rfl) ⟨1672197, by rfl⟩ : syracuseStep 4459193 = 3344395) B3344395
theorem B2972795 : Blo 1981435 2972795 := bstep (se 1 (by rfl) ⟨2229596, by rfl⟩ : syracuseStep 2972795 = 4459193) B4459193
theorem B1981863 : Blo 1981435 1981863 := bstep (se 1 (by rfl) ⟨1486397, by rfl⟩ : syracuseStep 1981863 = 2972795) B2972795
theorem B2229601 : Blo 1981435 2229601 := bbase (se 2 (by rfl) ⟨836100, by rfl⟩ : syracuseStep 2229601 = 1672201) (by norm_num)
theorem B2972801 : Blo 1981435 2972801 := bstep (se 2 (by rfl) ⟨1114800, by rfl⟩ : syracuseStep 2972801 = 2229601) B2229601
theorem B1981867 : Blo 1981435 1981867 := bstep (se 1 (by rfl) ⟨1486400, by rfl⟩ : syracuseStep 1981867 = 2972801) B2972801
theorem B5016613 : Blo 1981435 5016613 := bbase (se 4 (by rfl) ⟨470307, by rfl⟩ : syracuseStep 5016613 = 940615) (by norm_num)
theorem B6688817 : Blo 1981435 6688817 := bstep (se 2 (by rfl) ⟨2508306, by rfl⟩ : syracuseStep 6688817 = 5016613) B5016613
theorem B4459211 : Blo 1981435 4459211 := bstep (se 1 (by rfl) ⟨3344408, by rfl⟩ : syracuseStep 4459211 = 6688817) B6688817
theorem B2972807 : Blo 1981435 2972807 := bstep (se 1 (by rfl) ⟨2229605, by rfl⟩ : syracuseStep 2972807 = 4459211) B4459211
theorem B1981871 : Blo 1981435 1981871 := bstep (se 1 (by rfl) ⟨1486403, by rfl⟩ : syracuseStep 1981871 = 2972807) B2972807
theorem B2972813 : Blo 1981435 2972813 := bbase (se 3 (by rfl) ⟨557402, by rfl⟩ : syracuseStep 2972813 = 1114805) (by norm_num)
theorem B1981875 : Blo 1981435 1981875 := bstep (se 1 (by rfl) ⟨1486406, by rfl⟩ : syracuseStep 1981875 = 2972813) B2972813
theorem B4459229 : Blo 1981435 4459229 := bbase (se 3 (by rfl) ⟨836105, by rfl⟩ : syracuseStep 4459229 = 1672211) (by norm_num)
theorem B2972819 : Blo 1981435 2972819 := bstep (se 1 (by rfl) ⟨2229614, by rfl⟩ : syracuseStep 2972819 = 4459229) B4459229
theorem B1981879 : Blo 1981435 1981879 := bstep (se 1 (by rfl) ⟨1486409, by rfl⟩ : syracuseStep 1981879 = 2972819) B2972819
theorem B3344429 : Blo 1981435 3344429 := bbase (se 3 (by rfl) ⟨627080, by rfl⟩ : syracuseStep 3344429 = 1254161) (by norm_num)
theorem B2229619 : Blo 1981435 2229619 := bstep (se 1 (by rfl) ⟨1672214, by rfl⟩ : syracuseStep 2229619 = 3344429) B3344429
theorem B2972825 : Blo 1981435 2972825 := bstep (se 2 (by rfl) ⟨1114809, by rfl⟩ : syracuseStep 2972825 = 2229619) B2229619
theorem B1981883 : Blo 1981435 1981883 := bstep (se 1 (by rfl) ⟨1486412, by rfl⟩ : syracuseStep 1981883 = 2972825) B2972825
theorem B28571413 : Blo 1981435 28571413 := bbase (se 6 (by rfl) ⟨669642, by rfl⟩ : syracuseStep 28571413 = 1339285) (by norm_num)
theorem B38095217 : Blo 1981435 38095217 := bstep (se 2 (by rfl) ⟨14285706, by rfl⟩ : syracuseStep 38095217 = 28571413) B28571413
theorem B25396811 : Blo 1981435 25396811 := bstep (se 1 (by rfl) ⟨19047608, by rfl⟩ : syracuseStep 25396811 = 38095217) B38095217
theorem B16931207 : Blo 1981435 16931207 := bstep (se 1 (by rfl) ⟨12698405, by rfl⟩ : syracuseStep 16931207 = 25396811) B25396811
theorem B11287471 : Blo 1981435 11287471 := bstep (se 1 (by rfl) ⟨8465603, by rfl⟩ : syracuseStep 11287471 = 16931207) B16931207
theorem B15049961 : Blo 1981435 15049961 := bstep (se 2 (by rfl) ⟨5643735, by rfl⟩ : syracuseStep 15049961 = 11287471) B11287471
theorem B10033307 : Blo 1981435 10033307 := bstep (se 1 (by rfl) ⟨7524980, by rfl⟩ : syracuseStep 10033307 = 15049961) B15049961
theorem B6688871 : Blo 1981435 6688871 := bstep (se 1 (by rfl) ⟨5016653, by rfl⟩ : syracuseStep 6688871 = 10033307) B10033307
theorem B4459247 : Blo 1981435 4459247 := bstep (se 1 (by rfl) ⟨3344435, by rfl⟩ : syracuseStep 4459247 = 6688871) B6688871
theorem B2972831 : Blo 1981435 2972831 := bstep (se 1 (by rfl) ⟨2229623, by rfl⟩ : syracuseStep 2972831 = 4459247) B4459247
theorem B1981887 : Blo 1981435 1981887 := bstep (se 1 (by rfl) ⟨1486415, by rfl⟩ : syracuseStep 1981887 = 2972831) B2972831
theorem B2972837 : Blo 1981435 2972837 := bbase (se 4 (by rfl) ⟨278703, by rfl⟩ : syracuseStep 2972837 = 557407) (by norm_num)
theorem B1981891 : Blo 1981435 1981891 := bstep (se 1 (by rfl) ⟨1486418, by rfl⟩ : syracuseStep 1981891 = 2972837) B2972837
theorem B2508337 : Blo 1981435 2508337 := bbase (se 2 (by rfl) ⟨940626, by rfl⟩ : syracuseStep 2508337 = 1881253) (by norm_num)
theorem B3344449 : Blo 1981435 3344449 := bstep (se 2 (by rfl) ⟨1254168, by rfl⟩ : syracuseStep 3344449 = 2508337) B2508337
theorem B4459265 : Blo 1981435 4459265 := bstep (se 2 (by rfl) ⟨1672224, by rfl⟩ : syracuseStep 4459265 = 3344449) B3344449
theorem B2972843 : Blo 1981435 2972843 := bstep (se 1 (by rfl) ⟨2229632, by rfl⟩ : syracuseStep 2972843 = 4459265) B4459265
theorem B1981895 : Blo 1981435 1981895 := bstep (se 1 (by rfl) ⟨1486421, by rfl⟩ : syracuseStep 1981895 = 2972843) B2972843
theorem B2229637 : Blo 1981435 2229637 := bbase (se 4 (by rfl) ⟨209028, by rfl⟩ : syracuseStep 2229637 = 418057) (by norm_num)
theorem B2972849 : Blo 1981435 2972849 := bstep (se 2 (by rfl) ⟨1114818, by rfl⟩ : syracuseStep 2972849 = 2229637) B2229637
theorem B1981899 : Blo 1981435 1981899 := bstep (se 1 (by rfl) ⟨1486424, by rfl⟩ : syracuseStep 1981899 = 2972849) B2972849
theorem B4232837 : Blo 1981435 4232837 := bbase (se 4 (by rfl) ⟨396828, by rfl⟩ : syracuseStep 4232837 = 793657) (by norm_num)
theorem B2821891 : Blo 1981435 2821891 := bstep (se 1 (by rfl) ⟨2116418, by rfl⟩ : syracuseStep 2821891 = 4232837) B4232837
theorem B3762521 : Blo 1981435 3762521 := bstep (se 2 (by rfl) ⟨1410945, by rfl⟩ : syracuseStep 3762521 = 2821891) B2821891
theorem B2508347 : Blo 1981435 2508347 := bstep (se 1 (by rfl) ⟨1881260, by rfl⟩ : syracuseStep 2508347 = 3762521) B3762521
theorem B6688925 : Blo 1981435 6688925 := bstep (se 3 (by rfl) ⟨1254173, by rfl⟩ : syracuseStep 6688925 = 2508347) B2508347
theorem B4459283 : Blo 1981435 4459283 := bstep (se 1 (by rfl) ⟨3344462, by rfl⟩ : syracuseStep 4459283 = 6688925) B6688925
theorem B2972855 : Blo 1981435 2972855 := bstep (se 1 (by rfl) ⟨2229641, by rfl⟩ : syracuseStep 2972855 = 4459283) B4459283
theorem B1981903 : Blo 1981435 1981903 := bstep (se 1 (by rfl) ⟨1486427, by rfl⟩ : syracuseStep 1981903 = 2972855) B2972855
theorem B2972861 : Blo 1981435 2972861 := bbase (se 3 (by rfl) ⟨557411, by rfl⟩ : syracuseStep 2972861 = 1114823) (by norm_num)
theorem B1981907 : Blo 1981435 1981907 := bstep (se 1 (by rfl) ⟨1486430, by rfl⟩ : syracuseStep 1981907 = 2972861) B2972861
theorem B4459301 : Blo 1981435 4459301 := bbase (se 4 (by rfl) ⟨418059, by rfl⟩ : syracuseStep 4459301 = 836119) (by norm_num)
theorem B2972867 : Blo 1981435 2972867 := bstep (se 1 (by rfl) ⟨2229650, by rfl⟩ : syracuseStep 2972867 = 4459301) B4459301
theorem B1981911 : Blo 1981435 1981911 := bstep (se 1 (by rfl) ⟨1486433, by rfl⟩ : syracuseStep 1981911 = 2972867) B2972867
theorem B5016725 : Blo 1981435 5016725 := bbase (se 6 (by rfl) ⟨117579, by rfl⟩ : syracuseStep 5016725 = 235159) (by norm_num)
theorem B3344483 : Blo 1981435 3344483 := bstep (se 1 (by rfl) ⟨2508362, by rfl⟩ : syracuseStep 3344483 = 5016725) B5016725
theorem B2229655 : Blo 1981435 2229655 := bstep (se 1 (by rfl) ⟨1672241, by rfl⟩ : syracuseStep 2229655 = 3344483) B3344483
theorem B2972873 : Blo 1981435 2972873 := bstep (se 2 (by rfl) ⟨1114827, by rfl⟩ : syracuseStep 2972873 = 2229655) B2229655
theorem B1981915 : Blo 1981435 1981915 := bstep (se 1 (by rfl) ⟨1486436, by rfl⟩ : syracuseStep 1981915 = 2972873) B2972873
theorem B3174653 : Blo 1981435 3174653 := bbase (se 3 (by rfl) ⟨595247, by rfl⟩ : syracuseStep 3174653 = 1190495) (by norm_num)
theorem B8465741 : Blo 1981435 8465741 := bstep (se 3 (by rfl) ⟨1587326, by rfl⟩ : syracuseStep 8465741 = 3174653) B3174653
theorem B5643827 : Blo 1981435 5643827 := bstep (se 1 (by rfl) ⟨4232870, by rfl⟩ : syracuseStep 5643827 = 8465741) B8465741
theorem B3762551 : Blo 1981435 3762551 := bstep (se 1 (by rfl) ⟨2821913, by rfl⟩ : syracuseStep 3762551 = 5643827) B5643827
theorem B10033469 : Blo 1981435 10033469 := bstep (se 3 (by rfl) ⟨1881275, by rfl⟩ : syracuseStep 10033469 = 3762551) B3762551
theorem B6688979 : Blo 1981435 6688979 := bstep (se 1 (by rfl) ⟨5016734, by rfl⟩ : syracuseStep 6688979 = 10033469) B10033469
theorem B4459319 : Blo 1981435 4459319 := bstep (se 1 (by rfl) ⟨3344489, by rfl⟩ : syracuseStep 4459319 = 6688979) B6688979
theorem B2972879 : Blo 1981435 2972879 := bstep (se 1 (by rfl) ⟨2229659, by rfl⟩ : syracuseStep 2972879 = 4459319) B4459319
theorem B1981919 : Blo 1981435 1981919 := bstep (se 1 (by rfl) ⟨1486439, by rfl⟩ : syracuseStep 1981919 = 2972879) B2972879
theorem B2972885 : Blo 1981435 2972885 := bbase (se 7 (by rfl) ⟨34838, by rfl⟩ : syracuseStep 2972885 = 69677) (by norm_num)
theorem B1981923 : Blo 1981435 1981923 := bstep (se 1 (by rfl) ⟨1486442, by rfl⟩ : syracuseStep 1981923 = 2972885) B2972885
theorem B2821925 : Blo 1981435 2821925 := bbase (se 4 (by rfl) ⟨264555, by rfl⟩ : syracuseStep 2821925 = 529111) (by norm_num)
theorem B7525133 : Blo 1981435 7525133 := bstep (se 3 (by rfl) ⟨1410962, by rfl⟩ : syracuseStep 7525133 = 2821925) B2821925
theorem B5016755 : Blo 1981435 5016755 := bstep (se 1 (by rfl) ⟨3762566, by rfl⟩ : syracuseStep 5016755 = 7525133) B7525133
theorem B3344503 : Blo 1981435 3344503 := bstep (se 1 (by rfl) ⟨2508377, by rfl⟩ : syracuseStep 3344503 = 5016755) B5016755
theorem B4459337 : Blo 1981435 4459337 := bstep (se 2 (by rfl) ⟨1672251, by rfl⟩ : syracuseStep 4459337 = 3344503) B3344503
theorem B2972891 : Blo 1981435 2972891 := bstep (se 1 (by rfl) ⟨2229668, by rfl⟩ : syracuseStep 2972891 = 4459337) B4459337
theorem B1981927 : Blo 1981435 1981927 := bstep (se 1 (by rfl) ⟨1486445, by rfl⟩ : syracuseStep 1981927 = 2972891) B2972891
theorem B2229673 : Blo 1981435 2229673 := bbase (se 2 (by rfl) ⟨836127, by rfl⟩ : syracuseStep 2229673 = 1672255) (by norm_num)
theorem B2972897 : Blo 1981435 2972897 := bstep (se 2 (by rfl) ⟨1114836, by rfl⟩ : syracuseStep 2972897 = 2229673) B2229673
theorem B1981931 : Blo 1981435 1981931 := bstep (se 1 (by rfl) ⟨1486448, by rfl⟩ : syracuseStep 1981931 = 2972897) B2972897
theorem B2381009 : Blo 1981435 2381009 := bbase (se 2 (by rfl) ⟨892878, by rfl⟩ : syracuseStep 2381009 = 1785757) (by norm_num)
theorem B6349357 : Blo 1981435 6349357 := bstep (se 3 (by rfl) ⟨1190504, by rfl⟩ : syracuseStep 6349357 = 2381009) B2381009
theorem B8465809 : Blo 1981435 8465809 := bstep (se 2 (by rfl) ⟨3174678, by rfl⟩ : syracuseStep 8465809 = 6349357) B6349357
theorem B11287745 : Blo 1981435 11287745 := bstep (se 2 (by rfl) ⟨4232904, by rfl⟩ : syracuseStep 11287745 = 8465809) B8465809
theorem B7525163 : Blo 1981435 7525163 := bstep (se 1 (by rfl) ⟨5643872, by rfl⟩ : syracuseStep 7525163 = 11287745) B11287745
theorem B5016775 : Blo 1981435 5016775 := bstep (se 1 (by rfl) ⟨3762581, by rfl⟩ : syracuseStep 5016775 = 7525163) B7525163
theorem B6689033 : Blo 1981435 6689033 := bstep (se 2 (by rfl) ⟨2508387, by rfl⟩ : syracuseStep 6689033 = 5016775) B5016775
theorem B4459355 : Blo 1981435 4459355 := bstep (se 1 (by rfl) ⟨3344516, by rfl⟩ : syracuseStep 4459355 = 6689033) B6689033
theorem B2972903 : Blo 1981435 2972903 := bstep (se 1 (by rfl) ⟨2229677, by rfl⟩ : syracuseStep 2972903 = 4459355) B4459355
theorem B1981935 : Blo 1981435 1981935 := bstep (se 1 (by rfl) ⟨1486451, by rfl⟩ : syracuseStep 1981935 = 2972903) B2972903
theorem B2972909 : Blo 1981435 2972909 := bbase (se 3 (by rfl) ⟨557420, by rfl⟩ : syracuseStep 2972909 = 1114841) (by norm_num)
theorem B1981939 : Blo 1981435 1981939 := bstep (se 1 (by rfl) ⟨1486454, by rfl⟩ : syracuseStep 1981939 = 2972909) B2972909
theorem B4459373 : Blo 1981435 4459373 := bbase (se 3 (by rfl) ⟨836132, by rfl⟩ : syracuseStep 4459373 = 1672265) (by norm_num)
theorem B2972915 : Blo 1981435 2972915 := bstep (se 1 (by rfl) ⟨2229686, by rfl⟩ : syracuseStep 2972915 = 4459373) B4459373
theorem B1981943 : Blo 1981435 1981943 := bstep (se 1 (by rfl) ⟨1486457, by rfl⟩ : syracuseStep 1981943 = 2972915) B2972915
theorem B3762605 : Blo 1981435 3762605 := bbase (se 3 (by rfl) ⟨705488, by rfl⟩ : syracuseStep 3762605 = 1410977) (by norm_num)
theorem B2508403 : Blo 1981435 2508403 := bstep (se 1 (by rfl) ⟨1881302, by rfl⟩ : syracuseStep 2508403 = 3762605) B3762605
theorem B3344537 : Blo 1981435 3344537 := bstep (se 2 (by rfl) ⟨1254201, by rfl⟩ : syracuseStep 3344537 = 2508403) B2508403
theorem B2229691 : Blo 1981435 2229691 := bstep (se 1 (by rfl) ⟨1672268, by rfl⟩ : syracuseStep 2229691 = 3344537) B3344537
theorem B2972921 : Blo 1981435 2972921 := bstep (se 2 (by rfl) ⟨1114845, by rfl⟩ : syracuseStep 2972921 = 2229691) B2229691
theorem B1981947 : Blo 1981435 1981947 := bstep (se 1 (by rfl) ⟨1486460, by rfl⟩ : syracuseStep 1981947 = 2972921) B2972921
theorem B6436037 : Blo 1981435 6436037 := bbase (se 4 (by rfl) ⟨603378, by rfl⟩ : syracuseStep 6436037 = 1206757) (by norm_num)
theorem B4290691 : Blo 1981435 4290691 := bstep (se 1 (by rfl) ⟨3218018, by rfl⟩ : syracuseStep 4290691 = 6436037) B6436037
theorem B5720921 : Blo 1981435 5720921 := bstep (se 2 (by rfl) ⟨2145345, by rfl⟩ : syracuseStep 5720921 = 4290691) B4290691
theorem B3813947 : Blo 1981435 3813947 := bstep (se 1 (by rfl) ⟨2860460, by rfl⟩ : syracuseStep 3813947 = 5720921) B5720921
theorem B2542631 : Blo 1981435 2542631 := bstep (se 1 (by rfl) ⟨1906973, by rfl⟩ : syracuseStep 2542631 = 3813947) B3813947
theorem B27121397 : Blo 1981435 27121397 := bstep (se 5 (by rfl) ⟨1271315, by rfl⟩ : syracuseStep 27121397 = 2542631) B2542631
theorem B72323725 : Blo 1981435 72323725 := bstep (se 3 (by rfl) ⟨13560698, by rfl⟩ : syracuseStep 72323725 = 27121397) B27121397
theorem B96431633 : Blo 1981435 96431633 := bstep (se 2 (by rfl) ⟨36161862, by rfl⟩ : syracuseStep 96431633 = 72323725) B72323725
theorem B64287755 : Blo 1981435 64287755 := bstep (se 1 (by rfl) ⟨48215816, by rfl⟩ : syracuseStep 64287755 = 96431633) B96431633
theorem B42858503 : Blo 1981435 42858503 := bstep (se 1 (by rfl) ⟨32143877, by rfl⟩ : syracuseStep 42858503 = 64287755) B64287755
theorem B28572335 : Blo 1981435 28572335 := bstep (se 1 (by rfl) ⟨21429251, by rfl⟩ : syracuseStep 28572335 = 42858503) B42858503
theorem B19048223 : Blo 1981435 19048223 := bstep (se 1 (by rfl) ⟨14286167, by rfl⟩ : syracuseStep 19048223 = 28572335) B28572335
theorem B50795261 : Blo 1981435 50795261 := bstep (se 3 (by rfl) ⟨9524111, by rfl⟩ : syracuseStep 50795261 = 19048223) B19048223
theorem B33863507 : Blo 1981435 33863507 := bstep (se 1 (by rfl) ⟨25397630, by rfl⟩ : syracuseStep 33863507 = 50795261) B50795261
theorem B22575671 : Blo 1981435 22575671 := bstep (se 1 (by rfl) ⟨16931753, by rfl⟩ : syracuseStep 22575671 = 33863507) B33863507
theorem B15050447 : Blo 1981435 15050447 := bstep (se 1 (by rfl) ⟨11287835, by rfl⟩ : syracuseStep 15050447 = 22575671) B22575671
theorem B10033631 : Blo 1981435 10033631 := bstep (se 1 (by rfl) ⟨7525223, by rfl⟩ : syracuseStep 10033631 = 15050447) B15050447
theorem B6689087 : Blo 1981435 6689087 := bstep (se 1 (by rfl) ⟨5016815, by rfl⟩ : syracuseStep 6689087 = 10033631) B10033631
theorem B4459391 : Blo 1981435 4459391 := bstep (se 1 (by rfl) ⟨3344543, by rfl⟩ : syracuseStep 4459391 = 6689087) B6689087
theorem B2972927 : Blo 1981435 2972927 := bstep (se 1 (by rfl) ⟨2229695, by rfl⟩ : syracuseStep 2972927 = 4459391) B4459391
theorem B1981951 : Blo 1981435 1981951 := bstep (se 1 (by rfl) ⟨1486463, by rfl⟩ : syracuseStep 1981951 = 2972927) B2972927
theorem B2972933 : Blo 1981435 2972933 := bbase (se 4 (by rfl) ⟨278712, by rfl⟩ : syracuseStep 2972933 = 557425) (by norm_num)
theorem B1981955 : Blo 1981435 1981955 := bstep (se 1 (by rfl) ⟨1486466, by rfl⟩ : syracuseStep 1981955 = 2972933) B2972933
theorem B3344557 : Blo 1981435 3344557 := bbase (se 3 (by rfl) ⟨627104, by rfl⟩ : syracuseStep 3344557 = 1254209) (by norm_num)
theorem B4459409 : Blo 1981435 4459409 := bstep (se 2 (by rfl) ⟨1672278, by rfl⟩ : syracuseStep 4459409 = 3344557) B3344557
theorem B2972939 : Blo 1981435 2972939 := bstep (se 1 (by rfl) ⟨2229704, by rfl⟩ : syracuseStep 2972939 = 4459409) B4459409
theorem B1981959 : Blo 1981435 1981959 := bstep (se 1 (by rfl) ⟨1486469, by rfl⟩ : syracuseStep 1981959 = 2972939) B2972939
theorem B2229709 : Blo 1981435 2229709 := bbase (se 3 (by rfl) ⟨418070, by rfl⟩ : syracuseStep 2229709 = 836141) (by norm_num)
theorem B2972945 : Blo 1981435 2972945 := bstep (se 2 (by rfl) ⟨1114854, by rfl⟩ : syracuseStep 2972945 = 2229709) B2229709
theorem B1981963 : Blo 1981435 1981963 := bstep (se 1 (by rfl) ⟨1486472, by rfl⟩ : syracuseStep 1981963 = 2972945) B2972945
theorem B6689141 : Blo 1981435 6689141 := bbase (se 5 (by rfl) ⟨313553, by rfl⟩ : syracuseStep 6689141 = 627107) (by norm_num)
theorem B4459427 : Blo 1981435 4459427 := bstep (se 1 (by rfl) ⟨3344570, by rfl⟩ : syracuseStep 4459427 = 6689141) B6689141
theorem B2972951 : Blo 1981435 2972951 := bstep (se 1 (by rfl) ⟨2229713, by rfl⟩ : syracuseStep 2972951 = 4459427) B4459427
theorem B1981967 : Blo 1981435 1981967 := bstep (se 1 (by rfl) ⟨1486475, by rfl⟩ : syracuseStep 1981967 = 2972951) B2972951
theorem B2972957 : Blo 1981435 2972957 := bbase (se 3 (by rfl) ⟨557429, by rfl⟩ : syracuseStep 2972957 = 1114859) (by norm_num)
theorem B1981971 : Blo 1981435 1981971 := bstep (se 1 (by rfl) ⟨1486478, by rfl⟩ : syracuseStep 1981971 = 2972957) B2972957
theorem B4459445 : Blo 1981435 4459445 := bbase (se 5 (by rfl) ⟨209036, by rfl⟩ : syracuseStep 4459445 = 418073) (by norm_num)
theorem B2972963 : Blo 1981435 2972963 := bstep (se 1 (by rfl) ⟨2229722, by rfl⟩ : syracuseStep 2972963 = 4459445) B4459445
theorem B1981975 : Blo 1981435 1981975 := bstep (se 1 (by rfl) ⟨1486481, by rfl⟩ : syracuseStep 1981975 = 2972963) B2972963
theorem B2145377 : Blo 1981435 2145377 := bbase (se 2 (by rfl) ⟨804516, by rfl⟩ : syracuseStep 2145377 = 1609033) (by norm_num)
theorem B5721005 : Blo 1981435 5721005 := bstep (se 3 (by rfl) ⟨1072688, by rfl⟩ : syracuseStep 5721005 = 2145377) B2145377
theorem B3814003 : Blo 1981435 3814003 := bstep (se 1 (by rfl) ⟨2860502, by rfl⟩ : syracuseStep 3814003 = 5721005) B5721005
theorem B5085337 : Blo 1981435 5085337 := bstep (se 2 (by rfl) ⟨1907001, by rfl⟩ : syracuseStep 5085337 = 3814003) B3814003
theorem B6780449 : Blo 1981435 6780449 := bstep (se 2 (by rfl) ⟨2542668, by rfl⟩ : syracuseStep 6780449 = 5085337) B5085337
theorem B4520299 : Blo 1981435 4520299 := bstep (se 1 (by rfl) ⟨3390224, by rfl⟩ : syracuseStep 4520299 = 6780449) B6780449
theorem B6027065 : Blo 1981435 6027065 := bstep (se 2 (by rfl) ⟨2260149, by rfl⟩ : syracuseStep 6027065 = 4520299) B4520299
theorem B4018043 : Blo 1981435 4018043 := bstep (se 1 (by rfl) ⟨3013532, by rfl⟩ : syracuseStep 4018043 = 6027065) B6027065
theorem B10714781 : Blo 1981435 10714781 := bstep (se 3 (by rfl) ⟨2009021, by rfl⟩ : syracuseStep 10714781 = 4018043) B4018043
theorem B7143187 : Blo 1981435 7143187 := bstep (se 1 (by rfl) ⟨5357390, by rfl⟩ : syracuseStep 7143187 = 10714781) B10714781
theorem B9524249 : Blo 1981435 9524249 := bstep (se 2 (by rfl) ⟨3571593, by rfl⟩ : syracuseStep 9524249 = 7143187) B7143187
theorem B6349499 : Blo 1981435 6349499 := bstep (se 1 (by rfl) ⟨4762124, by rfl⟩ : syracuseStep 6349499 = 9524249) B9524249
theorem B4232999 : Blo 1981435 4232999 := bstep (se 1 (by rfl) ⟨3174749, by rfl⟩ : syracuseStep 4232999 = 6349499) B6349499
theorem B11287997 : Blo 1981435 11287997 := bstep (se 3 (by rfl) ⟨2116499, by rfl⟩ : syracuseStep 11287997 = 4232999) B4232999
theorem B7525331 : Blo 1981435 7525331 := bstep (se 1 (by rfl) ⟨5643998, by rfl⟩ : syracuseStep 7525331 = 11287997) B11287997
theorem B5016887 : Blo 1981435 5016887 := bstep (se 1 (by rfl) ⟨3762665, by rfl⟩ : syracuseStep 5016887 = 7525331) B7525331
theorem B3344591 : Blo 1981435 3344591 := bstep (se 1 (by rfl) ⟨2508443, by rfl⟩ : syracuseStep 3344591 = 5016887) B5016887
theorem B2229727 : Blo 1981435 2229727 := bstep (se 1 (by rfl) ⟨1672295, by rfl⟩ : syracuseStep 2229727 = 3344591) B3344591
theorem B2972969 : Blo 1981435 2972969 := bstep (se 2 (by rfl) ⟨1114863, by rfl⟩ : syracuseStep 2972969 = 2229727) B2229727
theorem B1981979 : Blo 1981435 1981979 := bstep (se 1 (by rfl) ⟨1486484, by rfl⟩ : syracuseStep 1981979 = 2972969) B2972969
theorem B8036101 : Blo 1981435 8036101 := bbase (se 4 (by rfl) ⟨753384, by rfl⟩ : syracuseStep 8036101 = 1506769) (by norm_num)
theorem B10714801 : Blo 1981435 10714801 := bstep (se 2 (by rfl) ⟨4018050, by rfl⟩ : syracuseStep 10714801 = 8036101) B8036101
theorem B14286401 : Blo 1981435 14286401 := bstep (se 2 (by rfl) ⟨5357400, by rfl⟩ : syracuseStep 14286401 = 10714801) B10714801
theorem B9524267 : Blo 1981435 9524267 := bstep (se 1 (by rfl) ⟨7143200, by rfl⟩ : syracuseStep 9524267 = 14286401) B14286401
theorem B6349511 : Blo 1981435 6349511 := bstep (se 1 (by rfl) ⟨4762133, by rfl⟩ : syracuseStep 6349511 = 9524267) B9524267
theorem B4233007 : Blo 1981435 4233007 := bstep (se 1 (by rfl) ⟨3174755, by rfl⟩ : syracuseStep 4233007 = 6349511) B6349511
theorem B5644009 : Blo 1981435 5644009 := bstep (se 2 (by rfl) ⟨2116503, by rfl⟩ : syracuseStep 5644009 = 4233007) B4233007
theorem B7525345 : Blo 1981435 7525345 := bstep (se 2 (by rfl) ⟨2822004, by rfl⟩ : syracuseStep 7525345 = 5644009) B5644009
theorem B10033793 : Blo 1981435 10033793 := bstep (se 2 (by rfl) ⟨3762672, by rfl⟩ : syracuseStep 10033793 = 7525345) B7525345
theorem B6689195 : Blo 1981435 6689195 := bstep (se 1 (by rfl) ⟨5016896, by rfl⟩ : syracuseStep 6689195 = 10033793) B10033793
theorem B4459463 : Blo 1981435 4459463 := bstep (se 1 (by rfl) ⟨3344597, by rfl⟩ : syracuseStep 4459463 = 6689195) B6689195
theorem B2972975 : Blo 1981435 2972975 := bstep (se 1 (by rfl) ⟨2229731, by rfl⟩ : syracuseStep 2972975 = 4459463) B4459463
theorem B1981983 : Blo 1981435 1981983 := bstep (se 1 (by rfl) ⟨1486487, by rfl⟩ : syracuseStep 1981983 = 2972975) B2972975
theorem B2972981 : Blo 1981435 2972981 := bbase (se 5 (by rfl) ⟨139358, by rfl⟩ : syracuseStep 2972981 = 278717) (by norm_num)
theorem B1981987 : Blo 1981435 1981987 := bstep (se 1 (by rfl) ⟨1486490, by rfl⟩ : syracuseStep 1981987 = 2972981) B2972981
theorem B5016917 : Blo 1981435 5016917 := bbase (se 11 (by rfl) ⟨3674, by rfl⟩ : syracuseStep 5016917 = 7349) (by norm_num)
theorem B3344611 : Blo 1981435 3344611 := bstep (se 1 (by rfl) ⟨2508458, by rfl⟩ : syracuseStep 3344611 = 5016917) B5016917
theorem B4459481 : Blo 1981435 4459481 := bstep (se 2 (by rfl) ⟨1672305, by rfl⟩ : syracuseStep 4459481 = 3344611) B3344611
theorem B2972987 : Blo 1981435 2972987 := bstep (se 1 (by rfl) ⟨2229740, by rfl⟩ : syracuseStep 2972987 = 4459481) B4459481
theorem B1981991 : Blo 1981435 1981991 := bstep (se 1 (by rfl) ⟨1486493, by rfl⟩ : syracuseStep 1981991 = 2972987) B2972987
theorem B2229745 : Blo 1981435 2229745 := bbase (se 2 (by rfl) ⟨836154, by rfl⟩ : syracuseStep 2229745 = 1672309) (by norm_num)
theorem B2972993 : Blo 1981435 2972993 := bstep (se 2 (by rfl) ⟨1114872, by rfl⟩ : syracuseStep 2972993 = 2229745) B2229745
theorem B1981995 : Blo 1981435 1981995 := bstep (se 1 (by rfl) ⟨1486496, by rfl⟩ : syracuseStep 1981995 = 2972993) B2972993
theorem B12699125 : Blo 1981435 12699125 := bbase (se 5 (by rfl) ⟨595271, by rfl⟩ : syracuseStep 12699125 = 1190543) (by norm_num)
theorem B8466083 : Blo 1981435 8466083 := bstep (se 1 (by rfl) ⟨6349562, by rfl⟩ : syracuseStep 8466083 = 12699125) B12699125
theorem B5644055 : Blo 1981435 5644055 := bstep (se 1 (by rfl) ⟨4233041, by rfl⟩ : syracuseStep 5644055 = 8466083) B8466083
theorem B3762703 : Blo 1981435 3762703 := bstep (se 1 (by rfl) ⟨2822027, by rfl⟩ : syracuseStep 3762703 = 5644055) B5644055
theorem B5016937 : Blo 1981435 5016937 := bstep (se 2 (by rfl) ⟨1881351, by rfl⟩ : syracuseStep 5016937 = 3762703) B3762703
theorem B6689249 : Blo 1981435 6689249 := bstep (se 2 (by rfl) ⟨2508468, by rfl⟩ : syracuseStep 6689249 = 5016937) B5016937
theorem B4459499 : Blo 1981435 4459499 := bstep (se 1 (by rfl) ⟨3344624, by rfl⟩ : syracuseStep 4459499 = 6689249) B6689249
theorem B2972999 : Blo 1981435 2972999 := bstep (se 1 (by rfl) ⟨2229749, by rfl⟩ : syracuseStep 2972999 = 4459499) B4459499
theorem B1981999 : Blo 1981435 1981999 := bstep (se 1 (by rfl) ⟨1486499, by rfl⟩ : syracuseStep 1981999 = 2972999) B2972999
theorem B2973005 : Blo 1981435 2973005 := bbase (se 3 (by rfl) ⟨557438, by rfl⟩ : syracuseStep 2973005 = 1114877) (by norm_num)
theorem B1982003 : Blo 1981435 1982003 := bstep (se 1 (by rfl) ⟨1486502, by rfl⟩ : syracuseStep 1982003 = 2973005) B2973005
theorem B4459517 : Blo 1981435 4459517 := bbase (se 3 (by rfl) ⟨836159, by rfl⟩ : syracuseStep 4459517 = 1672319) (by norm_num)
theorem B2973011 : Blo 1981435 2973011 := bstep (se 1 (by rfl) ⟨2229758, by rfl⟩ : syracuseStep 2973011 = 4459517) B4459517
theorem B1982007 : Blo 1981435 1982007 := bstep (se 1 (by rfl) ⟨1486505, by rfl⟩ : syracuseStep 1982007 = 2973011) B2973011
theorem B3344645 : Blo 1981435 3344645 := bbase (se 4 (by rfl) ⟨313560, by rfl⟩ : syracuseStep 3344645 = 627121) (by norm_num)
theorem B2229763 : Blo 1981435 2229763 := bstep (se 1 (by rfl) ⟨1672322, by rfl⟩ : syracuseStep 2229763 = 3344645) B3344645
theorem B2973017 : Blo 1981435 2973017 := bstep (se 2 (by rfl) ⟨1114881, by rfl⟩ : syracuseStep 2973017 = 2229763) B2229763
theorem B1982011 : Blo 1981435 1982011 := bstep (se 1 (by rfl) ⟨1486508, by rfl⟩ : syracuseStep 1982011 = 2973017) B2973017
theorem B15050933 : Blo 1981435 15050933 := bbase (se 5 (by rfl) ⟨705512, by rfl⟩ : syracuseStep 15050933 = 1411025) (by norm_num)
theorem B10033955 : Blo 1981435 10033955 := bstep (se 1 (by rfl) ⟨7525466, by rfl⟩ : syracuseStep 10033955 = 15050933) B15050933
theorem B6689303 : Blo 1981435 6689303 := bstep (se 1 (by rfl) ⟨5016977, by rfl⟩ : syracuseStep 6689303 = 10033955) B10033955
theorem B4459535 : Blo 1981435 4459535 := bstep (se 1 (by rfl) ⟨3344651, by rfl⟩ : syracuseStep 4459535 = 6689303) B6689303
theorem B2973023 : Blo 1981435 2973023 := bstep (se 1 (by rfl) ⟨2229767, by rfl⟩ : syracuseStep 2973023 = 4459535) B4459535
theorem B1982015 : Blo 1981435 1982015 := bstep (se 1 (by rfl) ⟨1486511, by rfl⟩ : syracuseStep 1982015 = 2973023) B2973023
theorem B2973029 : Blo 1981435 2973029 := bbase (se 4 (by rfl) ⟨278721, by rfl⟩ : syracuseStep 2973029 = 557443) (by norm_num)
theorem B1982019 : Blo 1981435 1982019 := bstep (se 1 (by rfl) ⟨1486514, by rfl⟩ : syracuseStep 1982019 = 2973029) B2973029
theorem B3762749 : Blo 1981435 3762749 := bbase (se 3 (by rfl) ⟨705515, by rfl⟩ : syracuseStep 3762749 = 1411031) (by norm_num)
theorem B2508499 : Blo 1981435 2508499 := bstep (se 1 (by rfl) ⟨1881374, by rfl⟩ : syracuseStep 2508499 = 3762749) B3762749
theorem B3344665 : Blo 1981435 3344665 := bstep (se 2 (by rfl) ⟨1254249, by rfl⟩ : syracuseStep 3344665 = 2508499) B2508499
theorem B4459553 : Blo 1981435 4459553 := bstep (se 2 (by rfl) ⟨1672332, by rfl⟩ : syracuseStep 4459553 = 3344665) B3344665
theorem B2973035 : Blo 1981435 2973035 := bstep (se 1 (by rfl) ⟨2229776, by rfl⟩ : syracuseStep 2973035 = 4459553) B4459553
theorem B1982023 : Blo 1981435 1982023 := bstep (se 1 (by rfl) ⟨1486517, by rfl⟩ : syracuseStep 1982023 = 2973035) B2973035
theorem B2229781 : Blo 1981435 2229781 := bbase (se 6 (by rfl) ⟨52260, by rfl⟩ : syracuseStep 2229781 = 104521) (by norm_num)
theorem B2973041 : Blo 1981435 2973041 := bstep (se 2 (by rfl) ⟨1114890, by rfl⟩ : syracuseStep 2973041 = 2229781) B2229781
theorem B1982027 : Blo 1981435 1982027 := bstep (se 1 (by rfl) ⟨1486520, by rfl⟩ : syracuseStep 1982027 = 2973041) B2973041
theorem B2508509 : Blo 1981435 2508509 := bbase (se 3 (by rfl) ⟨470345, by rfl⟩ : syracuseStep 2508509 = 940691) (by norm_num)
theorem B6689357 : Blo 1981435 6689357 := bstep (se 3 (by rfl) ⟨1254254, by rfl⟩ : syracuseStep 6689357 = 2508509) B2508509
theorem B4459571 : Blo 1981435 4459571 := bstep (se 1 (by rfl) ⟨3344678, by rfl⟩ : syracuseStep 4459571 = 6689357) B6689357
theorem B2973047 : Blo 1981435 2973047 := bstep (se 1 (by rfl) ⟨2229785, by rfl⟩ : syracuseStep 2973047 = 4459571) B4459571
theorem B1982031 : Blo 1981435 1982031 := bstep (se 1 (by rfl) ⟨1486523, by rfl⟩ : syracuseStep 1982031 = 2973047) B2973047
theorem B2973053 : Blo 1981435 2973053 := bbase (se 3 (by rfl) ⟨557447, by rfl⟩ : syracuseStep 2973053 = 1114895) (by norm_num)
theorem B1982035 : Blo 1981435 1982035 := bstep (se 1 (by rfl) ⟨1486526, by rfl⟩ : syracuseStep 1982035 = 2973053) B2973053
theorem B4459589 : Blo 1981435 4459589 := bbase (se 4 (by rfl) ⟨418086, by rfl⟩ : syracuseStep 4459589 = 836173) (by norm_num)
theorem B2973059 : Blo 1981435 2973059 := bstep (se 1 (by rfl) ⟨2229794, by rfl⟩ : syracuseStep 2973059 = 4459589) B4459589
theorem B1982039 : Blo 1981435 1982039 := bstep (se 1 (by rfl) ⟨1486529, by rfl⟩ : syracuseStep 1982039 = 2973059) B2973059
theorem B5644181 : Blo 1981435 5644181 := bbase (se 6 (by rfl) ⟨132285, by rfl⟩ : syracuseStep 5644181 = 264571) (by norm_num)
theorem B3762787 : Blo 1981435 3762787 := bstep (se 1 (by rfl) ⟨2822090, by rfl⟩ : syracuseStep 3762787 = 5644181) B5644181
theorem B5017049 : Blo 1981435 5017049 := bstep (se 2 (by rfl) ⟨1881393, by rfl⟩ : syracuseStep 5017049 = 3762787) B3762787
theorem B3344699 : Blo 1981435 3344699 := bstep (se 1 (by rfl) ⟨2508524, by rfl⟩ : syracuseStep 3344699 = 5017049) B5017049
theorem B2229799 : Blo 1981435 2229799 := bstep (se 1 (by rfl) ⟨1672349, by rfl⟩ : syracuseStep 2229799 = 3344699) B3344699
theorem B2973065 : Blo 1981435 2973065 := bstep (se 2 (by rfl) ⟨1114899, by rfl⟩ : syracuseStep 2973065 = 2229799) B2229799
theorem B1982043 : Blo 1981435 1982043 := bstep (se 1 (by rfl) ⟨1486532, by rfl⟩ : syracuseStep 1982043 = 2973065) B2973065
theorem B10034117 : Blo 1981435 10034117 := bbase (se 4 (by rfl) ⟨940698, by rfl⟩ : syracuseStep 10034117 = 1881397) (by norm_num)
theorem B6689411 : Blo 1981435 6689411 := bstep (se 1 (by rfl) ⟨5017058, by rfl⟩ : syracuseStep 6689411 = 10034117) B10034117
theorem B4459607 : Blo 1981435 4459607 := bstep (se 1 (by rfl) ⟨3344705, by rfl⟩ : syracuseStep 4459607 = 6689411) B6689411
theorem B2973071 : Blo 1981435 2973071 := bstep (se 1 (by rfl) ⟨2229803, by rfl⟩ : syracuseStep 2973071 = 4459607) B4459607
theorem B1982047 : Blo 1981435 1982047 := bstep (se 1 (by rfl) ⟨1486535, by rfl⟩ : syracuseStep 1982047 = 2973071) B2973071
theorem B2973077 : Blo 1981435 2973077 := bbase (se 6 (by rfl) ⟨69681, by rfl⟩ : syracuseStep 2973077 = 139363) (by norm_num)
theorem B1982051 : Blo 1981435 1982051 := bstep (se 1 (by rfl) ⟨1486538, by rfl⟩ : syracuseStep 1982051 = 2973077) B2973077
theorem B7143461 : Blo 1981435 7143461 := bbase (se 4 (by rfl) ⟨669699, by rfl⟩ : syracuseStep 7143461 = 1339399) (by norm_num)
theorem B4762307 : Blo 1981435 4762307 := bstep (se 1 (by rfl) ⟨3571730, by rfl⟩ : syracuseStep 4762307 = 7143461) B7143461
theorem B3174871 : Blo 1981435 3174871 := bstep (se 1 (by rfl) ⟨2381153, by rfl⟩ : syracuseStep 3174871 = 4762307) B4762307
theorem B4233161 : Blo 1981435 4233161 := bstep (se 2 (by rfl) ⟨1587435, by rfl⟩ : syracuseStep 4233161 = 3174871) B3174871
theorem B11288429 : Blo 1981435 11288429 := bstep (se 3 (by rfl) ⟨2116580, by rfl⟩ : syracuseStep 11288429 = 4233161) B4233161
theorem B7525619 : Blo 1981435 7525619 := bstep (se 1 (by rfl) ⟨5644214, by rfl⟩ : syracuseStep 7525619 = 11288429) B11288429
theorem B5017079 : Blo 1981435 5017079 := bstep (se 1 (by rfl) ⟨3762809, by rfl⟩ : syracuseStep 5017079 = 7525619) B7525619
theorem B3344719 : Blo 1981435 3344719 := bstep (se 1 (by rfl) ⟨2508539, by rfl⟩ : syracuseStep 3344719 = 5017079) B5017079
theorem B4459625 : Blo 1981435 4459625 := bstep (se 2 (by rfl) ⟨1672359, by rfl⟩ : syracuseStep 4459625 = 3344719) B3344719
theorem B2973083 : Blo 1981435 2973083 := bstep (se 1 (by rfl) ⟨2229812, by rfl⟩ : syracuseStep 2973083 = 4459625) B4459625
theorem B1982055 : Blo 1981435 1982055 := bstep (se 1 (by rfl) ⟨1486541, by rfl⟩ : syracuseStep 1982055 = 2973083) B2973083
theorem B2229817 : Blo 1981435 2229817 := bbase (se 2 (by rfl) ⟨836181, by rfl⟩ : syracuseStep 2229817 = 1672363) (by norm_num)
theorem B2973089 : Blo 1981435 2973089 := bstep (se 2 (by rfl) ⟨1114908, by rfl⟩ : syracuseStep 2973089 = 2229817) B2229817
theorem B1982059 : Blo 1981435 1982059 := bstep (se 1 (by rfl) ⟨1486544, by rfl⟩ : syracuseStep 1982059 = 2973089) B2973089
theorem B2116589 : Blo 1981435 2116589 := bbase (se 3 (by rfl) ⟨396860, by rfl⟩ : syracuseStep 2116589 = 793721) (by norm_num)
theorem B5644237 : Blo 1981435 5644237 := bstep (se 3 (by rfl) ⟨1058294, by rfl⟩ : syracuseStep 5644237 = 2116589) B2116589
theorem B7525649 : Blo 1981435 7525649 := bstep (se 2 (by rfl) ⟨2822118, by rfl⟩ : syracuseStep 7525649 = 5644237) B5644237
theorem B5017099 : Blo 1981435 5017099 := bstep (se 1 (by rfl) ⟨3762824, by rfl⟩ : syracuseStep 5017099 = 7525649) B7525649
theorem B6689465 : Blo 1981435 6689465 := bstep (se 2 (by rfl) ⟨2508549, by rfl⟩ : syracuseStep 6689465 = 5017099) B5017099
theorem B4459643 : Blo 1981435 4459643 := bstep (se 1 (by rfl) ⟨3344732, by rfl⟩ : syracuseStep 4459643 = 6689465) B6689465
theorem B2973095 : Blo 1981435 2973095 := bstep (se 1 (by rfl) ⟨2229821, by rfl⟩ : syracuseStep 2973095 = 4459643) B4459643
theorem B1982063 : Blo 1981435 1982063 := bstep (se 1 (by rfl) ⟨1486547, by rfl⟩ : syracuseStep 1982063 = 2973095) B2973095
theorem B2973101 : Blo 1981435 2973101 := bbase (se 3 (by rfl) ⟨557456, by rfl⟩ : syracuseStep 2973101 = 1114913) (by norm_num)
theorem B1982067 : Blo 1981435 1982067 := bstep (se 1 (by rfl) ⟨1486550, by rfl⟩ : syracuseStep 1982067 = 2973101) B2973101
theorem B4459661 : Blo 1981435 4459661 := bbase (se 3 (by rfl) ⟨836186, by rfl⟩ : syracuseStep 4459661 = 1672373) (by norm_num)
theorem B2973107 : Blo 1981435 2973107 := bstep (se 1 (by rfl) ⟨2229830, by rfl⟩ : syracuseStep 2973107 = 4459661) B4459661
theorem B1982071 : Blo 1981435 1982071 := bstep (se 1 (by rfl) ⟨1486553, by rfl⟩ : syracuseStep 1982071 = 2973107) B2973107
theorem B2508565 : Blo 1981435 2508565 := bbase (se 6 (by rfl) ⟨58794, by rfl⟩ : syracuseStep 2508565 = 117589) (by norm_num)
theorem B3344753 : Blo 1981435 3344753 := bstep (se 2 (by rfl) ⟨1254282, by rfl⟩ : syracuseStep 3344753 = 2508565) B2508565
theorem B2229835 : Blo 1981435 2229835 := bstep (se 1 (by rfl) ⟨1672376, by rfl⟩ : syracuseStep 2229835 = 3344753) B3344753
theorem B2973113 : Blo 1981435 2973113 := bstep (se 2 (by rfl) ⟨1114917, by rfl⟩ : syracuseStep 2973113 = 2229835) B2229835
theorem B1982075 : Blo 1981435 1982075 := bstep (se 1 (by rfl) ⟨1486556, by rfl⟩ : syracuseStep 1982075 = 2973113) B2973113
theorem B2860645 : Blo 1981435 2860645 := bbase (se 4 (by rfl) ⟨268185, by rfl⟩ : syracuseStep 2860645 = 536371) (by norm_num)
theorem B3814193 : Blo 1981435 3814193 := bstep (se 2 (by rfl) ⟨1430322, by rfl⟩ : syracuseStep 3814193 = 2860645) B2860645
theorem B10171181 : Blo 1981435 10171181 := bstep (se 3 (by rfl) ⟨1907096, by rfl⟩ : syracuseStep 10171181 = 3814193) B3814193
theorem B27123149 : Blo 1981435 27123149 := bstep (se 3 (by rfl) ⟨5085590, by rfl⟩ : syracuseStep 27123149 = 10171181) B10171181
theorem B18082099 : Blo 1981435 18082099 := bstep (se 1 (by rfl) ⟨13561574, by rfl⟩ : syracuseStep 18082099 = 27123149) B27123149
theorem B96437861 : Blo 1981435 96437861 := bstep (se 4 (by rfl) ⟨9041049, by rfl⟩ : syracuseStep 96437861 = 18082099) B18082099
theorem B64291907 : Blo 1981435 64291907 := bstep (se 1 (by rfl) ⟨48218930, by rfl⟩ : syracuseStep 64291907 = 96437861) B96437861
theorem B42861271 : Blo 1981435 42861271 := bstep (se 1 (by rfl) ⟨32145953, by rfl⟩ : syracuseStep 42861271 = 64291907) B64291907
theorem B57148361 : Blo 1981435 57148361 := bstep (se 2 (by rfl) ⟨21430635, by rfl⟩ : syracuseStep 57148361 = 42861271) B42861271
theorem B38098907 : Blo 1981435 38098907 := bstep (se 1 (by rfl) ⟨28574180, by rfl⟩ : syracuseStep 38098907 = 57148361) B57148361
theorem B25399271 : Blo 1981435 25399271 := bstep (se 1 (by rfl) ⟨19049453, by rfl⟩ : syracuseStep 25399271 = 38098907) B38098907
theorem B16932847 : Blo 1981435 16932847 := bstep (se 1 (by rfl) ⟨12699635, by rfl⟩ : syracuseStep 16932847 = 25399271) B25399271
theorem B22577129 : Blo 1981435 22577129 := bstep (se 2 (by rfl) ⟨8466423, by rfl⟩ : syracuseStep 22577129 = 16932847) B16932847
theorem B15051419 : Blo 1981435 15051419 := bstep (se 1 (by rfl) ⟨11288564, by rfl⟩ : syracuseStep 15051419 = 22577129) B22577129
theorem B10034279 : Blo 1981435 10034279 := bstep (se 1 (by rfl) ⟨7525709, by rfl⟩ : syracuseStep 10034279 = 15051419) B15051419
theorem B6689519 : Blo 1981435 6689519 := bstep (se 1 (by rfl) ⟨5017139, by rfl⟩ : syracuseStep 6689519 = 10034279) B10034279
theorem B4459679 : Blo 1981435 4459679 := bstep (se 1 (by rfl) ⟨3344759, by rfl⟩ : syracuseStep 4459679 = 6689519) B6689519
theorem B2973119 : Blo 1981435 2973119 := bstep (se 1 (by rfl) ⟨2229839, by rfl⟩ : syracuseStep 2973119 = 4459679) B4459679
theorem B1982079 : Blo 1981435 1982079 := bstep (se 1 (by rfl) ⟨1486559, by rfl⟩ : syracuseStep 1982079 = 2973119) B2973119
theorem B2973125 : Blo 1981435 2973125 := bbase (se 4 (by rfl) ⟨278730, by rfl⟩ : syracuseStep 2973125 = 557461) (by norm_num)
theorem B1982083 : Blo 1981435 1982083 := bstep (se 1 (by rfl) ⟨1486562, by rfl⟩ : syracuseStep 1982083 = 2973125) B2973125
theorem B3344773 : Blo 1981435 3344773 := bbase (se 4 (by rfl) ⟨313572, by rfl⟩ : syracuseStep 3344773 = 627145) (by norm_num)
theorem B4459697 : Blo 1981435 4459697 := bstep (se 2 (by rfl) ⟨1672386, by rfl⟩ : syracuseStep 4459697 = 3344773) B3344773
theorem B2973131 : Blo 1981435 2973131 := bstep (se 1 (by rfl) ⟨2229848, by rfl⟩ : syracuseStep 2973131 = 4459697) B4459697
theorem B1982087 : Blo 1981435 1982087 := bstep (se 1 (by rfl) ⟨1486565, by rfl⟩ : syracuseStep 1982087 = 2973131) B2973131
theorem B2229853 : Blo 1981435 2229853 := bbase (se 3 (by rfl) ⟨418097, by rfl⟩ : syracuseStep 2229853 = 836195) (by norm_num)
theorem B2973137 : Blo 1981435 2973137 := bstep (se 2 (by rfl) ⟨1114926, by rfl⟩ : syracuseStep 2973137 = 2229853) B2229853
theorem B1982091 : Blo 1981435 1982091 := bstep (se 1 (by rfl) ⟨1486568, by rfl⟩ : syracuseStep 1982091 = 2973137) B2973137
theorem B6689573 : Blo 1981435 6689573 := bbase (se 4 (by rfl) ⟨627147, by rfl⟩ : syracuseStep 6689573 = 1254295) (by norm_num)
theorem B4459715 : Blo 1981435 4459715 := bstep (se 1 (by rfl) ⟨3344786, by rfl⟩ : syracuseStep 4459715 = 6689573) B6689573
theorem B2973143 : Blo 1981435 2973143 := bstep (se 1 (by rfl) ⟨2229857, by rfl⟩ : syracuseStep 2973143 = 4459715) B4459715
theorem B1982095 : Blo 1981435 1982095 := bstep (se 1 (by rfl) ⟨1486571, by rfl⟩ : syracuseStep 1982095 = 2973143) B2973143
theorem B2973149 : Blo 1981435 2973149 := bbase (se 3 (by rfl) ⟨557465, by rfl⟩ : syracuseStep 2973149 = 1114931) (by norm_num)
theorem B1982099 : Blo 1981435 1982099 := bstep (se 1 (by rfl) ⟨1486574, by rfl⟩ : syracuseStep 1982099 = 2973149) B2973149
theorem B4459733 : Blo 1981435 4459733 := bbase (se 7 (by rfl) ⟨52262, by rfl⟩ : syracuseStep 4459733 = 104525) (by norm_num)
theorem B2973155 : Blo 1981435 2973155 := bstep (se 1 (by rfl) ⟨2229866, by rfl⟩ : syracuseStep 2973155 = 4459733) B4459733
theorem B1982103 : Blo 1981435 1982103 := bstep (se 1 (by rfl) ⟨1486577, by rfl⟩ : syracuseStep 1982103 = 2973155) B2973155
theorem B6349909 : Blo 1981435 6349909 := bbase (se 8 (by rfl) ⟨37206, by rfl⟩ : syracuseStep 6349909 = 74413) (by norm_num)
theorem B8466545 : Blo 1981435 8466545 := bstep (se 2 (by rfl) ⟨3174954, by rfl⟩ : syracuseStep 8466545 = 6349909) B6349909
theorem B5644363 : Blo 1981435 5644363 := bstep (se 1 (by rfl) ⟨4233272, by rfl⟩ : syracuseStep 5644363 = 8466545) B8466545
theorem B7525817 : Blo 1981435 7525817 := bstep (se 2 (by rfl) ⟨2822181, by rfl⟩ : syracuseStep 7525817 = 5644363) B5644363
theorem B5017211 : Blo 1981435 5017211 := bstep (se 1 (by rfl) ⟨3762908, by rfl⟩ : syracuseStep 5017211 = 7525817) B7525817
theorem B3344807 : Blo 1981435 3344807 := bstep (se 1 (by rfl) ⟨2508605, by rfl⟩ : syracuseStep 3344807 = 5017211) B5017211
theorem B2229871 : Blo 1981435 2229871 := bstep (se 1 (by rfl) ⟨1672403, by rfl⟩ : syracuseStep 2229871 = 3344807) B3344807
theorem B2973161 : Blo 1981435 2973161 := bstep (se 2 (by rfl) ⟨1114935, by rfl⟩ : syracuseStep 2973161 = 2229871) B2229871
theorem B1982107 : Blo 1981435 1982107 := bstep (se 1 (by rfl) ⟨1486580, by rfl⟩ : syracuseStep 1982107 = 2973161) B2973161
theorem B3013733 : Blo 1981435 3013733 := bbase (se 4 (by rfl) ⟨282537, by rfl⟩ : syracuseStep 3013733 = 565075) (by norm_num)
theorem B2009155 : Blo 1981435 2009155 := bstep (se 1 (by rfl) ⟨1506866, by rfl⟩ : syracuseStep 2009155 = 3013733) B3013733
theorem B2678873 : Blo 1981435 2678873 := bstep (se 2 (by rfl) ⟨1004577, by rfl⟩ : syracuseStep 2678873 = 2009155) B2009155
theorem B7143661 : Blo 1981435 7143661 := bstep (se 3 (by rfl) ⟨1339436, by rfl⟩ : syracuseStep 7143661 = 2678873) B2678873
theorem B9524881 : Blo 1981435 9524881 := bstep (se 2 (by rfl) ⟨3571830, by rfl⟩ : syracuseStep 9524881 = 7143661) B7143661
theorem B12699841 : Blo 1981435 12699841 := bstep (se 2 (by rfl) ⟨4762440, by rfl⟩ : syracuseStep 12699841 = 9524881) B9524881
theorem B16933121 : Blo 1981435 16933121 := bstep (se 2 (by rfl) ⟨6349920, by rfl⟩ : syracuseStep 16933121 = 12699841) B12699841
theorem B11288747 : Blo 1981435 11288747 := bstep (se 1 (by rfl) ⟨8466560, by rfl⟩ : syracuseStep 11288747 = 16933121) B16933121
theorem B7525831 : Blo 1981435 7525831 := bstep (se 1 (by rfl) ⟨5644373, by rfl⟩ : syracuseStep 7525831 = 11288747) B11288747
theorem B10034441 : Blo 1981435 10034441 := bstep (se 2 (by rfl) ⟨3762915, by rfl⟩ : syracuseStep 10034441 = 7525831) B7525831
theorem B6689627 : Blo 1981435 6689627 := bstep (se 1 (by rfl) ⟨5017220, by rfl⟩ : syracuseStep 6689627 = 10034441) B10034441
theorem B4459751 : Blo 1981435 4459751 := bstep (se 1 (by rfl) ⟨3344813, by rfl⟩ : syracuseStep 4459751 = 6689627) B6689627
theorem B2973167 : Blo 1981435 2973167 := bstep (se 1 (by rfl) ⟨2229875, by rfl⟩ : syracuseStep 2973167 = 4459751) B4459751
theorem B1982111 : Blo 1981435 1982111 := bstep (se 1 (by rfl) ⟨1486583, by rfl⟩ : syracuseStep 1982111 = 2973167) B2973167
theorem B2973173 : Blo 1981435 2973173 := bbase (se 5 (by rfl) ⟨139367, by rfl⟩ : syracuseStep 2973173 = 278735) (by norm_num)
theorem B1982115 : Blo 1981435 1982115 := bstep (se 1 (by rfl) ⟨1486586, by rfl⟩ : syracuseStep 1982115 = 2973173) B2973173
theorem B2116649 : Blo 1981435 2116649 := bbase (se 2 (by rfl) ⟨793743, by rfl⟩ : syracuseStep 2116649 = 1587487) (by norm_num)
theorem B5644397 : Blo 1981435 5644397 := bstep (se 3 (by rfl) ⟨1058324, by rfl⟩ : syracuseStep 5644397 = 2116649) B2116649
theorem B3762931 : Blo 1981435 3762931 := bstep (se 1 (by rfl) ⟨2822198, by rfl⟩ : syracuseStep 3762931 = 5644397) B5644397
theorem B5017241 : Blo 1981435 5017241 := bstep (se 2 (by rfl) ⟨1881465, by rfl⟩ : syracuseStep 5017241 = 3762931) B3762931
theorem B3344827 : Blo 1981435 3344827 := bstep (se 1 (by rfl) ⟨2508620, by rfl⟩ : syracuseStep 3344827 = 5017241) B5017241
theorem B4459769 : Blo 1981435 4459769 := bstep (se 2 (by rfl) ⟨1672413, by rfl⟩ : syracuseStep 4459769 = 3344827) B3344827
theorem B2973179 : Blo 1981435 2973179 := bstep (se 1 (by rfl) ⟨2229884, by rfl⟩ : syracuseStep 2973179 = 4459769) B4459769
theorem B1982119 : Blo 1981435 1982119 := bstep (se 1 (by rfl) ⟨1486589, by rfl⟩ : syracuseStep 1982119 = 2973179) B2973179
theorem B2229889 : Blo 1981435 2229889 := bbase (se 2 (by rfl) ⟨836208, by rfl⟩ : syracuseStep 2229889 = 1672417) (by norm_num)
theorem B2973185 : Blo 1981435 2973185 := bstep (se 2 (by rfl) ⟨1114944, by rfl⟩ : syracuseStep 2973185 = 2229889) B2229889
theorem B1982123 : Blo 1981435 1982123 := bstep (se 1 (by rfl) ⟨1486592, by rfl⟩ : syracuseStep 1982123 = 2973185) B2973185
theorem B5017261 : Blo 1981435 5017261 := bbase (se 3 (by rfl) ⟨940736, by rfl⟩ : syracuseStep 5017261 = 1881473) (by norm_num)
theorem B6689681 : Blo 1981435 6689681 := bstep (se 2 (by rfl) ⟨2508630, by rfl⟩ : syracuseStep 6689681 = 5017261) B5017261
theorem B4459787 : Blo 1981435 4459787 := bstep (se 1 (by rfl) ⟨3344840, by rfl⟩ : syracuseStep 4459787 = 6689681) B6689681
theorem B2973191 : Blo 1981435 2973191 := bstep (se 1 (by rfl) ⟨2229893, by rfl⟩ : syracuseStep 2973191 = 4459787) B4459787
theorem B1982127 : Blo 1981435 1982127 := bstep (se 1 (by rfl) ⟨1486595, by rfl⟩ : syracuseStep 1982127 = 2973191) B2973191
theorem B2973197 : Blo 1981435 2973197 := bbase (se 3 (by rfl) ⟨557474, by rfl⟩ : syracuseStep 2973197 = 1114949) (by norm_num)
theorem B1982131 : Blo 1981435 1982131 := bstep (se 1 (by rfl) ⟨1486598, by rfl⟩ : syracuseStep 1982131 = 2973197) B2973197
theorem B4459805 : Blo 1981435 4459805 := bbase (se 3 (by rfl) ⟨836213, by rfl⟩ : syracuseStep 4459805 = 1672427) (by norm_num)
theorem B2973203 : Blo 1981435 2973203 := bstep (se 1 (by rfl) ⟨2229902, by rfl⟩ : syracuseStep 2973203 = 4459805) B4459805
theorem B1982135 : Blo 1981435 1982135 := bstep (se 1 (by rfl) ⟨1486601, by rfl⟩ : syracuseStep 1982135 = 2973203) B2973203
theorem B3344861 : Blo 1981435 3344861 := bbase (se 3 (by rfl) ⟨627161, by rfl⟩ : syracuseStep 3344861 = 1254323) (by norm_num)
theorem B2229907 : Blo 1981435 2229907 := bstep (se 1 (by rfl) ⟨1672430, by rfl⟩ : syracuseStep 2229907 = 3344861) B3344861
theorem B2973209 : Blo 1981435 2973209 := bstep (se 2 (by rfl) ⟨1114953, by rfl⟩ : syracuseStep 2973209 = 2229907) B2229907
theorem B1982139 : Blo 1981435 1982139 := bstep (se 1 (by rfl) ⟨1486604, by rfl⟩ : syracuseStep 1982139 = 2973209) B2973209
theorem B3013781 : Blo 1981435 3013781 := bbase (se 6 (by rfl) ⟨70635, by rfl⟩ : syracuseStep 3013781 = 141271) (by norm_num)
theorem B8036749 : Blo 1981435 8036749 := bstep (se 3 (by rfl) ⟨1506890, by rfl⟩ : syracuseStep 8036749 = 3013781) B3013781
theorem B10715665 : Blo 1981435 10715665 := bstep (se 2 (by rfl) ⟨4018374, by rfl⟩ : syracuseStep 10715665 = 8036749) B8036749
theorem B14287553 : Blo 1981435 14287553 := bstep (se 2 (by rfl) ⟨5357832, by rfl⟩ : syracuseStep 14287553 = 10715665) B10715665
theorem B9525035 : Blo 1981435 9525035 := bstep (se 1 (by rfl) ⟨7143776, by rfl⟩ : syracuseStep 9525035 = 14287553) B14287553
theorem B6350023 : Blo 1981435 6350023 := bstep (se 1 (by rfl) ⟨4762517, by rfl⟩ : syracuseStep 6350023 = 9525035) B9525035
theorem B8466697 : Blo 1981435 8466697 := bstep (se 2 (by rfl) ⟨3175011, by rfl⟩ : syracuseStep 8466697 = 6350023) B6350023
theorem B11288929 : Blo 1981435 11288929 := bstep (se 2 (by rfl) ⟨4233348, by rfl⟩ : syracuseStep 11288929 = 8466697) B8466697
theorem B15051905 : Blo 1981435 15051905 := bstep (se 2 (by rfl) ⟨5644464, by rfl⟩ : syracuseStep 15051905 = 11288929) B11288929
theorem B10034603 : Blo 1981435 10034603 := bstep (se 1 (by rfl) ⟨7525952, by rfl⟩ : syracuseStep 10034603 = 15051905) B15051905
theorem B6689735 : Blo 1981435 6689735 := bstep (se 1 (by rfl) ⟨5017301, by rfl⟩ : syracuseStep 6689735 = 10034603) B10034603
theorem B4459823 : Blo 1981435 4459823 := bstep (se 1 (by rfl) ⟨3344867, by rfl⟩ : syracuseStep 4459823 = 6689735) B6689735
theorem B2973215 : Blo 1981435 2973215 := bstep (se 1 (by rfl) ⟨2229911, by rfl⟩ : syracuseStep 2973215 = 4459823) B4459823
theorem B1982143 : Blo 1981435 1982143 := bstep (se 1 (by rfl) ⟨1486607, by rfl⟩ : syracuseStep 1982143 = 2973215) B2973215
theorem B2973221 : Blo 1981435 2973221 := bbase (se 4 (by rfl) ⟨278739, by rfl⟩ : syracuseStep 2973221 = 557479) (by norm_num)
theorem B1982147 : Blo 1981435 1982147 := bstep (se 1 (by rfl) ⟨1486610, by rfl⟩ : syracuseStep 1982147 = 2973221) B2973221
theorem B2508661 : Blo 1981435 2508661 := bbase (se 5 (by rfl) ⟨117593, by rfl⟩ : syracuseStep 2508661 = 235187) (by norm_num)
theorem B3344881 : Blo 1981435 3344881 := bstep (se 2 (by rfl) ⟨1254330, by rfl⟩ : syracuseStep 3344881 = 2508661) B2508661
theorem B4459841 : Blo 1981435 4459841 := bstep (se 2 (by rfl) ⟨1672440, by rfl⟩ : syracuseStep 4459841 = 3344881) B3344881
theorem B2973227 : Blo 1981435 2973227 := bstep (se 1 (by rfl) ⟨2229920, by rfl⟩ : syracuseStep 2973227 = 4459841) B4459841
theorem B1982151 : Blo 1981435 1982151 := bstep (se 1 (by rfl) ⟨1486613, by rfl⟩ : syracuseStep 1982151 = 2973227) B2973227
theorem B2229925 : Blo 1981435 2229925 := bbase (se 4 (by rfl) ⟨209055, by rfl⟩ : syracuseStep 2229925 = 418111) (by norm_num)
theorem B2973233 : Blo 1981435 2973233 := bstep (se 2 (by rfl) ⟨1114962, by rfl⟩ : syracuseStep 2973233 = 2229925) B2229925
theorem B1982155 : Blo 1981435 1982155 := bstep (se 1 (by rfl) ⟨1486616, by rfl⟩ : syracuseStep 1982155 = 2973233) B2973233
theorem B3218357 : Blo 1981435 3218357 := bbase (se 5 (by rfl) ⟨150860, by rfl⟩ : syracuseStep 3218357 = 301721) (by norm_num)
theorem B2145571 : Blo 1981435 2145571 := bstep (se 1 (by rfl) ⟨1609178, by rfl⟩ : syracuseStep 2145571 = 3218357) B3218357
theorem B11443045 : Blo 1981435 11443045 := bstep (se 4 (by rfl) ⟨1072785, by rfl⟩ : syracuseStep 11443045 = 2145571) B2145571
theorem B15257393 : Blo 1981435 15257393 := bstep (se 2 (by rfl) ⟨5721522, by rfl⟩ : syracuseStep 15257393 = 11443045) B11443045
theorem B10171595 : Blo 1981435 10171595 := bstep (se 1 (by rfl) ⟨7628696, by rfl⟩ : syracuseStep 10171595 = 15257393) B15257393
theorem B27124253 : Blo 1981435 27124253 := bstep (se 3 (by rfl) ⟨5085797, by rfl⟩ : syracuseStep 27124253 = 10171595) B10171595
theorem B18082835 : Blo 1981435 18082835 := bstep (se 1 (by rfl) ⟨13562126, by rfl⟩ : syracuseStep 18082835 = 27124253) B27124253
theorem B12055223 : Blo 1981435 12055223 := bstep (se 1 (by rfl) ⟨9041417, by rfl⟩ : syracuseStep 12055223 = 18082835) B18082835
theorem B8036815 : Blo 1981435 8036815 := bstep (se 1 (by rfl) ⟨6027611, by rfl⟩ : syracuseStep 8036815 = 12055223) B12055223
theorem B10715753 : Blo 1981435 10715753 := bstep (se 2 (by rfl) ⟨4018407, by rfl⟩ : syracuseStep 10715753 = 8036815) B8036815
theorem B28575341 : Blo 1981435 28575341 := bstep (se 3 (by rfl) ⟨5357876, by rfl⟩ : syracuseStep 28575341 = 10715753) B10715753
theorem B19050227 : Blo 1981435 19050227 := bstep (se 1 (by rfl) ⟨14287670, by rfl⟩ : syracuseStep 19050227 = 28575341) B28575341
theorem B12700151 : Blo 1981435 12700151 := bstep (se 1 (by rfl) ⟨9525113, by rfl⟩ : syracuseStep 12700151 = 19050227) B19050227
theorem B8466767 : Blo 1981435 8466767 := bstep (se 1 (by rfl) ⟨6350075, by rfl⟩ : syracuseStep 8466767 = 12700151) B12700151
theorem B5644511 : Blo 1981435 5644511 := bstep (se 1 (by rfl) ⟨4233383, by rfl⟩ : syracuseStep 5644511 = 8466767) B8466767
theorem B3763007 : Blo 1981435 3763007 := bstep (se 1 (by rfl) ⟨2822255, by rfl⟩ : syracuseStep 3763007 = 5644511) B5644511
theorem B2508671 : Blo 1981435 2508671 := bstep (se 1 (by rfl) ⟨1881503, by rfl⟩ : syracuseStep 2508671 = 3763007) B3763007
theorem B6689789 : Blo 1981435 6689789 := bstep (se 3 (by rfl) ⟨1254335, by rfl⟩ : syracuseStep 6689789 = 2508671) B2508671
theorem B4459859 : Blo 1981435 4459859 := bstep (se 1 (by rfl) ⟨3344894, by rfl⟩ : syracuseStep 4459859 = 6689789) B6689789
theorem B2973239 : Blo 1981435 2973239 := bstep (se 1 (by rfl) ⟨2229929, by rfl⟩ : syracuseStep 2973239 = 4459859) B4459859
theorem B1982159 : Blo 1981435 1982159 := bstep (se 1 (by rfl) ⟨1486619, by rfl⟩ : syracuseStep 1982159 = 2973239) B2973239
theorem B2973245 : Blo 1981435 2973245 := bbase (se 3 (by rfl) ⟨557483, by rfl⟩ : syracuseStep 2973245 = 1114967) (by norm_num)
theorem B1982163 : Blo 1981435 1982163 := bstep (se 1 (by rfl) ⟨1486622, by rfl⟩ : syracuseStep 1982163 = 2973245) B2973245
theorem B4459877 : Blo 1981435 4459877 := bbase (se 4 (by rfl) ⟨418113, by rfl⟩ : syracuseStep 4459877 = 836227) (by norm_num)
theorem B2973251 : Blo 1981435 2973251 := bstep (se 1 (by rfl) ⟨2229938, by rfl⟩ : syracuseStep 2973251 = 4459877) B4459877
theorem B1982167 : Blo 1981435 1982167 := bstep (se 1 (by rfl) ⟨1486625, by rfl⟩ : syracuseStep 1982167 = 2973251) B2973251
theorem B5017373 : Blo 1981435 5017373 := bbase (se 3 (by rfl) ⟨940757, by rfl⟩ : syracuseStep 5017373 = 1881515) (by norm_num)
theorem B3344915 : Blo 1981435 3344915 := bstep (se 1 (by rfl) ⟨2508686, by rfl⟩ : syracuseStep 3344915 = 5017373) B5017373
theorem B2229943 : Blo 1981435 2229943 := bstep (se 1 (by rfl) ⟨1672457, by rfl⟩ : syracuseStep 2229943 = 3344915) B3344915
theorem B2973257 : Blo 1981435 2973257 := bstep (se 2 (by rfl) ⟨1114971, by rfl⟩ : syracuseStep 2973257 = 2229943) B2229943
theorem B1982171 : Blo 1981435 1982171 := bstep (se 1 (by rfl) ⟨1486628, by rfl⟩ : syracuseStep 1982171 = 2973257) B2973257
theorem B3763037 : Blo 1981435 3763037 := bbase (se 3 (by rfl) ⟨705569, by rfl⟩ : syracuseStep 3763037 = 1411139) (by norm_num)
theorem B10034765 : Blo 1981435 10034765 := bstep (se 3 (by rfl) ⟨1881518, by rfl⟩ : syracuseStep 10034765 = 3763037) B3763037
theorem B6689843 : Blo 1981435 6689843 := bstep (se 1 (by rfl) ⟨5017382, by rfl⟩ : syracuseStep 6689843 = 10034765) B10034765
theorem B4459895 : Blo 1981435 4459895 := bstep (se 1 (by rfl) ⟨3344921, by rfl⟩ : syracuseStep 4459895 = 6689843) B6689843
theorem B2973263 : Blo 1981435 2973263 := bstep (se 1 (by rfl) ⟨2229947, by rfl⟩ : syracuseStep 2973263 = 4459895) B4459895
theorem B1982175 : Blo 1981435 1982175 := bstep (se 1 (by rfl) ⟨1486631, by rfl⟩ : syracuseStep 1982175 = 2973263) B2973263
theorem B2973269 : Blo 1981435 2973269 := bbase (se 8 (by rfl) ⟨17421, by rfl⟩ : syracuseStep 2973269 = 34843) (by norm_num)
theorem B1982179 : Blo 1981435 1982179 := bstep (se 1 (by rfl) ⟨1486634, by rfl⟩ : syracuseStep 1982179 = 2973269) B2973269
theorem B8466869 : Blo 1981435 8466869 := bbase (se 5 (by rfl) ⟨396884, by rfl⟩ : syracuseStep 8466869 = 793769) (by norm_num)
theorem B5644579 : Blo 1981435 5644579 := bstep (se 1 (by rfl) ⟨4233434, by rfl⟩ : syracuseStep 5644579 = 8466869) B8466869
theorem B7526105 : Blo 1981435 7526105 := bstep (se 2 (by rfl) ⟨2822289, by rfl⟩ : syracuseStep 7526105 = 5644579) B5644579
theorem B5017403 : Blo 1981435 5017403 := bstep (se 1 (by rfl) ⟨3763052, by rfl⟩ : syracuseStep 5017403 = 7526105) B7526105
theorem B3344935 : Blo 1981435 3344935 := bstep (se 1 (by rfl) ⟨2508701, by rfl⟩ : syracuseStep 3344935 = 5017403) B5017403
theorem B4459913 : Blo 1981435 4459913 := bstep (se 2 (by rfl) ⟨1672467, by rfl⟩ : syracuseStep 4459913 = 3344935) B3344935
theorem B2973275 : Blo 1981435 2973275 := bstep (se 1 (by rfl) ⟨2229956, by rfl⟩ : syracuseStep 2973275 = 4459913) B4459913
theorem B1982183 : Blo 1981435 1982183 := bstep (se 1 (by rfl) ⟨1486637, by rfl⟩ : syracuseStep 1982183 = 2973275) B2973275
theorem B2229961 : Blo 1981435 2229961 := bbase (se 2 (by rfl) ⟨836235, by rfl⟩ : syracuseStep 2229961 = 1672471) (by norm_num)
theorem B2973281 : Blo 1981435 2973281 := bstep (se 2 (by rfl) ⟨1114980, by rfl⟩ : syracuseStep 2973281 = 2229961) B2229961
theorem B1982187 : Blo 1981435 1982187 := bstep (se 1 (by rfl) ⟨1486640, by rfl⟩ : syracuseStep 1982187 = 2973281) B2973281
theorem B4291213 : Blo 1981435 4291213 := bbase (se 3 (by rfl) ⟨804602, by rfl⟩ : syracuseStep 4291213 = 1609205) (by norm_num)
theorem B5721617 : Blo 1981435 5721617 := bstep (se 2 (by rfl) ⟨2145606, by rfl⟩ : syracuseStep 5721617 = 4291213) B4291213
theorem B3814411 : Blo 1981435 3814411 := bstep (se 1 (by rfl) ⟨2860808, by rfl⟩ : syracuseStep 3814411 = 5721617) B5721617
theorem B5085881 : Blo 1981435 5085881 := bstep (se 2 (by rfl) ⟨1907205, by rfl⟩ : syracuseStep 5085881 = 3814411) B3814411
theorem B3390587 : Blo 1981435 3390587 := bstep (se 1 (by rfl) ⟨2542940, by rfl⟩ : syracuseStep 3390587 = 5085881) B5085881
theorem B2260391 : Blo 1981435 2260391 := bstep (se 1 (by rfl) ⟨1695293, by rfl⟩ : syracuseStep 2260391 = 3390587) B3390587
theorem B6027709 : Blo 1981435 6027709 := bstep (se 3 (by rfl) ⟨1130195, by rfl⟩ : syracuseStep 6027709 = 2260391) B2260391
theorem B8036945 : Blo 1981435 8036945 := bstep (se 2 (by rfl) ⟨3013854, by rfl⟩ : syracuseStep 8036945 = 6027709) B6027709
theorem B5357963 : Blo 1981435 5357963 := bstep (se 1 (by rfl) ⟨4018472, by rfl⟩ : syracuseStep 5357963 = 8036945) B8036945
theorem B3571975 : Blo 1981435 3571975 := bstep (se 1 (by rfl) ⟨2678981, by rfl⟩ : syracuseStep 3571975 = 5357963) B5357963
theorem B4762633 : Blo 1981435 4762633 := bstep (se 2 (by rfl) ⟨1785987, by rfl⟩ : syracuseStep 4762633 = 3571975) B3571975
theorem B6350177 : Blo 1981435 6350177 := bstep (se 2 (by rfl) ⟨2381316, by rfl⟩ : syracuseStep 6350177 = 4762633) B4762633
theorem B16933805 : Blo 1981435 16933805 := bstep (se 3 (by rfl) ⟨3175088, by rfl⟩ : syracuseStep 16933805 = 6350177) B6350177
theorem B11289203 : Blo 1981435 11289203 := bstep (se 1 (by rfl) ⟨8466902, by rfl⟩ : syracuseStep 11289203 = 16933805) B16933805
theorem B7526135 : Blo 1981435 7526135 := bstep (se 1 (by rfl) ⟨5644601, by rfl⟩ : syracuseStep 7526135 = 11289203) B11289203
theorem B5017423 : Blo 1981435 5017423 := bstep (se 1 (by rfl) ⟨3763067, by rfl⟩ : syracuseStep 5017423 = 7526135) B7526135
theorem B6689897 : Blo 1981435 6689897 := bstep (se 2 (by rfl) ⟨2508711, by rfl⟩ : syracuseStep 6689897 = 5017423) B5017423
theorem B4459931 : Blo 1981435 4459931 := bstep (se 1 (by rfl) ⟨3344948, by rfl⟩ : syracuseStep 4459931 = 6689897) B6689897
theorem B2973287 : Blo 1981435 2973287 := bstep (se 1 (by rfl) ⟨2229965, by rfl⟩ : syracuseStep 2973287 = 4459931) B4459931
theorem B1982191 : Blo 1981435 1982191 := bstep (se 1 (by rfl) ⟨1486643, by rfl⟩ : syracuseStep 1982191 = 2973287) B2973287
theorem B2973293 : Blo 1981435 2973293 := bbase (se 3 (by rfl) ⟨557492, by rfl⟩ : syracuseStep 2973293 = 1114985) (by norm_num)
theorem B1982195 : Blo 1981435 1982195 := bstep (se 1 (by rfl) ⟨1486646, by rfl⟩ : syracuseStep 1982195 = 2973293) B2973293
theorem B4459949 : Blo 1981435 4459949 := bbase (se 3 (by rfl) ⟨836240, by rfl⟩ : syracuseStep 4459949 = 1672481) (by norm_num)
theorem B2973299 : Blo 1981435 2973299 := bstep (se 1 (by rfl) ⟨2229974, by rfl⟩ : syracuseStep 2973299 = 4459949) B4459949
theorem B1982199 : Blo 1981435 1982199 := bstep (se 1 (by rfl) ⟨1486649, by rfl⟩ : syracuseStep 1982199 = 2973299) B2973299
theorem B3175109 : Blo 1981435 3175109 := bbase (se 4 (by rfl) ⟨297666, by rfl⟩ : syracuseStep 3175109 = 595333) (by norm_num)
theorem B2116739 : Blo 1981435 2116739 := bstep (se 1 (by rfl) ⟨1587554, by rfl⟩ : syracuseStep 2116739 = 3175109) B3175109
theorem B5644637 : Blo 1981435 5644637 := bstep (se 3 (by rfl) ⟨1058369, by rfl⟩ : syracuseStep 5644637 = 2116739) B2116739
theorem B3763091 : Blo 1981435 3763091 := bstep (se 1 (by rfl) ⟨2822318, by rfl⟩ : syracuseStep 3763091 = 5644637) B5644637
theorem B2508727 : Blo 1981435 2508727 := bstep (se 1 (by rfl) ⟨1881545, by rfl⟩ : syracuseStep 2508727 = 3763091) B3763091
theorem B3344969 : Blo 1981435 3344969 := bstep (se 2 (by rfl) ⟨1254363, by rfl⟩ : syracuseStep 3344969 = 2508727) B2508727
theorem B2229979 : Blo 1981435 2229979 := bstep (se 1 (by rfl) ⟨1672484, by rfl⟩ : syracuseStep 2229979 = 3344969) B3344969
theorem B2973305 : Blo 1981435 2973305 := bstep (se 2 (by rfl) ⟨1114989, by rfl⟩ : syracuseStep 2973305 = 2229979) B2229979
theorem B1982203 : Blo 1981435 1982203 := bstep (se 1 (by rfl) ⟨1486652, by rfl⟩ : syracuseStep 1982203 = 2973305) B2973305
theorem B9655301 : Blo 1981435 9655301 := bbase (se 4 (by rfl) ⟨905184, by rfl⟩ : syracuseStep 9655301 = 1810369) (by norm_num)
theorem B25747469 : Blo 1981435 25747469 := bstep (se 3 (by rfl) ⟨4827650, by rfl⟩ : syracuseStep 25747469 = 9655301) B9655301
theorem B17164979 : Blo 1981435 17164979 := bstep (se 1 (by rfl) ⟨12873734, by rfl⟩ : syracuseStep 17164979 = 25747469) B25747469
theorem B11443319 : Blo 1981435 11443319 := bstep (se 1 (by rfl) ⟨8582489, by rfl⟩ : syracuseStep 11443319 = 17164979) B17164979
theorem B7628879 : Blo 1981435 7628879 := bstep (se 1 (by rfl) ⟨5721659, by rfl⟩ : syracuseStep 7628879 = 11443319) B11443319
theorem B5085919 : Blo 1981435 5085919 := bstep (se 1 (by rfl) ⟨3814439, by rfl⟩ : syracuseStep 5085919 = 7628879) B7628879
theorem B27124901 : Blo 1981435 27124901 := bstep (se 4 (by rfl) ⟨2542959, by rfl⟩ : syracuseStep 27124901 = 5085919) B5085919
theorem B18083267 : Blo 1981435 18083267 := bstep (se 1 (by rfl) ⟨13562450, by rfl⟩ : syracuseStep 18083267 = 27124901) B27124901
theorem B12055511 : Blo 1981435 12055511 := bstep (se 1 (by rfl) ⟨9041633, by rfl⟩ : syracuseStep 12055511 = 18083267) B18083267
theorem B32148029 : Blo 1981435 32148029 := bstep (se 3 (by rfl) ⟨6027755, by rfl⟩ : syracuseStep 32148029 = 12055511) B12055511
theorem B85728077 : Blo 1981435 85728077 := bstep (se 3 (by rfl) ⟨16074014, by rfl⟩ : syracuseStep 85728077 = 32148029) B32148029
theorem B57152051 : Blo 1981435 57152051 := bstep (se 1 (by rfl) ⟨42864038, by rfl⟩ : syracuseStep 57152051 = 85728077) B85728077
theorem B38101367 : Blo 1981435 38101367 := bstep (se 1 (by rfl) ⟨28576025, by rfl⟩ : syracuseStep 38101367 = 57152051) B57152051
theorem B25400911 : Blo 1981435 25400911 := bstep (se 1 (by rfl) ⟨19050683, by rfl⟩ : syracuseStep 25400911 = 38101367) B38101367
theorem B33867881 : Blo 1981435 33867881 := bstep (se 2 (by rfl) ⟨12700455, by rfl⟩ : syracuseStep 33867881 = 25400911) B25400911
theorem B22578587 : Blo 1981435 22578587 := bstep (se 1 (by rfl) ⟨16933940, by rfl⟩ : syracuseStep 22578587 = 33867881) B33867881
theorem B15052391 : Blo 1981435 15052391 := bstep (se 1 (by rfl) ⟨11289293, by rfl⟩ : syracuseStep 15052391 = 22578587) B22578587
theorem B10034927 : Blo 1981435 10034927 := bstep (se 1 (by rfl) ⟨7526195, by rfl⟩ : syracuseStep 10034927 = 15052391) B15052391
theorem B6689951 : Blo 1981435 6689951 := bstep (se 1 (by rfl) ⟨5017463, by rfl⟩ : syracuseStep 6689951 = 10034927) B10034927
theorem B4459967 : Blo 1981435 4459967 := bstep (se 1 (by rfl) ⟨3344975, by rfl⟩ : syracuseStep 4459967 = 6689951) B6689951
theorem B2973311 : Blo 1981435 2973311 := bstep (se 1 (by rfl) ⟨2229983, by rfl⟩ : syracuseStep 2973311 = 4459967) B4459967
theorem B1982207 : Blo 1981435 1982207 := bstep (se 1 (by rfl) ⟨1486655, by rfl⟩ : syracuseStep 1982207 = 2973311) B2973311
theorem B2973317 : Blo 1981435 2973317 := bbase (se 4 (by rfl) ⟨278748, by rfl⟩ : syracuseStep 2973317 = 557497) (by norm_num)
theorem B1982211 : Blo 1981435 1982211 := bstep (se 1 (by rfl) ⟨1486658, by rfl⟩ : syracuseStep 1982211 = 2973317) B2973317
theorem B3344989 : Blo 1981435 3344989 := bbase (se 3 (by rfl) ⟨627185, by rfl⟩ : syracuseStep 3344989 = 1254371) (by norm_num)
theorem B4459985 : Blo 1981435 4459985 := bstep (se 2 (by rfl) ⟨1672494, by rfl⟩ : syracuseStep 4459985 = 3344989) B3344989
theorem B2973323 : Blo 1981435 2973323 := bstep (se 1 (by rfl) ⟨2229992, by rfl⟩ : syracuseStep 2973323 = 4459985) B4459985
theorem B1982215 : Blo 1981435 1982215 := bstep (se 1 (by rfl) ⟨1486661, by rfl⟩ : syracuseStep 1982215 = 2973323) B2973323
theorem B2229997 : Blo 1981435 2229997 := bbase (se 3 (by rfl) ⟨418124, by rfl⟩ : syracuseStep 2229997 = 836249) (by norm_num)
theorem B2973329 : Blo 1981435 2973329 := bstep (se 2 (by rfl) ⟨1114998, by rfl⟩ : syracuseStep 2973329 = 2229997) B2229997
theorem B1982219 : Blo 1981435 1982219 := bstep (se 1 (by rfl) ⟨1486664, by rfl⟩ : syracuseStep 1982219 = 2973329) B2973329
theorem B6690005 : Blo 1981435 6690005 := bbase (se 7 (by rfl) ⟨78398, by rfl⟩ : syracuseStep 6690005 = 156797) (by norm_num)
theorem B4460003 : Blo 1981435 4460003 := bstep (se 1 (by rfl) ⟨3345002, by rfl⟩ : syracuseStep 4460003 = 6690005) B6690005
theorem B2973335 : Blo 1981435 2973335 := bstep (se 1 (by rfl) ⟨2230001, by rfl⟩ : syracuseStep 2973335 = 4460003) B4460003
theorem B1982223 : Blo 1981435 1982223 := bstep (se 1 (by rfl) ⟨1486667, by rfl⟩ : syracuseStep 1982223 = 2973335) B2973335
theorem B2973341 : Blo 1981435 2973341 := bbase (se 3 (by rfl) ⟨557501, by rfl⟩ : syracuseStep 2973341 = 1115003) (by norm_num)
theorem B1982227 : Blo 1981435 1982227 := bstep (se 1 (by rfl) ⟨1486670, by rfl⟩ : syracuseStep 1982227 = 2973341) B2973341
theorem B4460021 : Blo 1981435 4460021 := bbase (se 5 (by rfl) ⟨209063, by rfl⟩ : syracuseStep 4460021 = 418127) (by norm_num)
theorem B2973347 : Blo 1981435 2973347 := bstep (se 1 (by rfl) ⟨2230010, by rfl⟩ : syracuseStep 2973347 = 4460021) B4460021
theorem B1982231 : Blo 1981435 1982231 := bstep (se 1 (by rfl) ⟨1486673, by rfl⟩ : syracuseStep 1982231 = 2973347) B2973347
theorem B2260441 : Blo 1981435 2260441 := bbase (se 2 (by rfl) ⟨847665, by rfl⟩ : syracuseStep 2260441 = 1695331) (by norm_num)
theorem B3013921 : Blo 1981435 3013921 := bstep (se 2 (by rfl) ⟨1130220, by rfl⟩ : syracuseStep 3013921 = 2260441) B2260441
theorem B16074245 : Blo 1981435 16074245 := bstep (se 4 (by rfl) ⟨1506960, by rfl⟩ : syracuseStep 16074245 = 3013921) B3013921
theorem B42864653 : Blo 1981435 42864653 := bstep (se 3 (by rfl) ⟨8037122, by rfl⟩ : syracuseStep 42864653 = 16074245) B16074245
theorem B28576435 : Blo 1981435 28576435 := bstep (se 1 (by rfl) ⟨21432326, by rfl⟩ : syracuseStep 28576435 = 42864653) B42864653
theorem B38101913 : Blo 1981435 38101913 := bstep (se 2 (by rfl) ⟨14288217, by rfl⟩ : syracuseStep 38101913 = 28576435) B28576435
theorem B25401275 : Blo 1981435 25401275 := bstep (se 1 (by rfl) ⟨19050956, by rfl⟩ : syracuseStep 25401275 = 38101913) B38101913
theorem B16934183 : Blo 1981435 16934183 := bstep (se 1 (by rfl) ⟨12700637, by rfl⟩ : syracuseStep 16934183 = 25401275) B25401275
theorem B11289455 : Blo 1981435 11289455 := bstep (se 1 (by rfl) ⟨8467091, by rfl⟩ : syracuseStep 11289455 = 16934183) B16934183
theorem B7526303 : Blo 1981435 7526303 := bstep (se 1 (by rfl) ⟨5644727, by rfl⟩ : syracuseStep 7526303 = 11289455) B11289455
theorem B5017535 : Blo 1981435 5017535 := bstep (se 1 (by rfl) ⟨3763151, by rfl⟩ : syracuseStep 5017535 = 7526303) B7526303
theorem B3345023 : Blo 1981435 3345023 := bstep (se 1 (by rfl) ⟨2508767, by rfl⟩ : syracuseStep 3345023 = 5017535) B5017535
theorem B2230015 : Blo 1981435 2230015 := bstep (se 1 (by rfl) ⟨1672511, by rfl⟩ : syracuseStep 2230015 = 3345023) B3345023
theorem B2973353 : Blo 1981435 2973353 := bstep (se 2 (by rfl) ⟨1115007, by rfl⟩ : syracuseStep 2973353 = 2230015) B2230015
theorem B1982235 : Blo 1981435 1982235 := bstep (se 1 (by rfl) ⟨1486676, by rfl⟩ : syracuseStep 1982235 = 2973353) B2973353
theorem B2116777 : Blo 1981435 2116777 := bbase (se 2 (by rfl) ⟨793791, by rfl⟩ : syracuseStep 2116777 = 1587583) (by norm_num)
theorem B2822369 : Blo 1981435 2822369 := bstep (se 2 (by rfl) ⟨1058388, by rfl⟩ : syracuseStep 2822369 = 2116777) B2116777
theorem B7526317 : Blo 1981435 7526317 := bstep (se 3 (by rfl) ⟨1411184, by rfl⟩ : syracuseStep 7526317 = 2822369) B2822369
theorem B10035089 : Blo 1981435 10035089 := bstep (se 2 (by rfl) ⟨3763158, by rfl⟩ : syracuseStep 10035089 = 7526317) B7526317
theorem B6690059 : Blo 1981435 6690059 := bstep (se 1 (by rfl) ⟨5017544, by rfl⟩ : syracuseStep 6690059 = 10035089) B10035089
theorem B4460039 : Blo 1981435 4460039 := bstep (se 1 (by rfl) ⟨3345029, by rfl⟩ : syracuseStep 4460039 = 6690059) B6690059
theorem B2973359 : Blo 1981435 2973359 := bstep (se 1 (by rfl) ⟨2230019, by rfl⟩ : syracuseStep 2973359 = 4460039) B4460039
theorem B1982239 : Blo 1981435 1982239 := bstep (se 1 (by rfl) ⟨1486679, by rfl⟩ : syracuseStep 1982239 = 2973359) B2973359
theorem B2973365 : Blo 1981435 2973365 := bbase (se 5 (by rfl) ⟨139376, by rfl⟩ : syracuseStep 2973365 = 278753) (by norm_num)
theorem B1982243 : Blo 1981435 1982243 := bstep (se 1 (by rfl) ⟨1486682, by rfl⟩ : syracuseStep 1982243 = 2973365) B2973365
theorem B5017565 : Blo 1981435 5017565 := bbase (se 3 (by rfl) ⟨940793, by rfl⟩ : syracuseStep 5017565 = 1881587) (by norm_num)
theorem B3345043 : Blo 1981435 3345043 := bstep (se 1 (by rfl) ⟨2508782, by rfl⟩ : syracuseStep 3345043 = 5017565) B5017565
theorem B4460057 : Blo 1981435 4460057 := bstep (se 2 (by rfl) ⟨1672521, by rfl⟩ : syracuseStep 4460057 = 3345043) B3345043
theorem B2973371 : Blo 1981435 2973371 := bstep (se 1 (by rfl) ⟨2230028, by rfl⟩ : syracuseStep 2973371 = 4460057) B4460057
theorem B1982247 : Blo 1981435 1982247 := bstep (se 1 (by rfl) ⟨1486685, by rfl⟩ : syracuseStep 1982247 = 2973371) B2973371
theorem B2230033 : Blo 1981435 2230033 := bbase (se 2 (by rfl) ⟨836262, by rfl⟩ : syracuseStep 2230033 = 1672525) (by norm_num)
theorem B2973377 : Blo 1981435 2973377 := bstep (se 2 (by rfl) ⟨1115016, by rfl⟩ : syracuseStep 2973377 = 2230033) B2230033
theorem B1982251 : Blo 1981435 1982251 := bstep (se 1 (by rfl) ⟨1486688, by rfl⟩ : syracuseStep 1982251 = 2973377) B2973377
theorem B3763189 : Blo 1981435 3763189 := bbase (se 5 (by rfl) ⟨176399, by rfl⟩ : syracuseStep 3763189 = 352799) (by norm_num)
theorem B5017585 : Blo 1981435 5017585 := bstep (se 2 (by rfl) ⟨1881594, by rfl⟩ : syracuseStep 5017585 = 3763189) B3763189
theorem B6690113 : Blo 1981435 6690113 := bstep (se 2 (by rfl) ⟨2508792, by rfl⟩ : syracuseStep 6690113 = 5017585) B5017585
theorem B4460075 : Blo 1981435 4460075 := bstep (se 1 (by rfl) ⟨3345056, by rfl⟩ : syracuseStep 4460075 = 6690113) B6690113
theorem B2973383 : Blo 1981435 2973383 := bstep (se 1 (by rfl) ⟨2230037, by rfl⟩ : syracuseStep 2973383 = 4460075) B4460075
theorem B1982255 : Blo 1981435 1982255 := bstep (se 1 (by rfl) ⟨1486691, by rfl⟩ : syracuseStep 1982255 = 2973383) B2973383
theorem B2973389 : Blo 1981435 2973389 := bbase (se 3 (by rfl) ⟨557510, by rfl⟩ : syracuseStep 2973389 = 1115021) (by norm_num)
theorem B1982259 : Blo 1981435 1982259 := bstep (se 1 (by rfl) ⟨1486694, by rfl⟩ : syracuseStep 1982259 = 2973389) B2973389
theorem B4460093 : Blo 1981435 4460093 := bbase (se 3 (by rfl) ⟨836267, by rfl⟩ : syracuseStep 4460093 = 1672535) (by norm_num)
theorem B2973395 : Blo 1981435 2973395 := bstep (se 1 (by rfl) ⟨2230046, by rfl⟩ : syracuseStep 2973395 = 4460093) B4460093
theorem B1982263 : Blo 1981435 1982263 := bstep (se 1 (by rfl) ⟨1486697, by rfl⟩ : syracuseStep 1982263 = 2973395) B2973395
theorem B3345077 : Blo 1981435 3345077 := bbase (se 5 (by rfl) ⟨156800, by rfl⟩ : syracuseStep 3345077 = 313601) (by norm_num)
theorem B2230051 : Blo 1981435 2230051 := bstep (se 1 (by rfl) ⟨1672538, by rfl⟩ : syracuseStep 2230051 = 3345077) B3345077
theorem B2973401 : Blo 1981435 2973401 := bstep (se 2 (by rfl) ⟨1115025, by rfl⟩ : syracuseStep 2973401 = 2230051) B2230051
theorem B1982267 : Blo 1981435 1982267 := bstep (se 1 (by rfl) ⟨1486700, by rfl⟩ : syracuseStep 1982267 = 2973401) B2973401
theorem B2381413 : Blo 1981435 2381413 := bbase (se 4 (by rfl) ⟨223257, by rfl⟩ : syracuseStep 2381413 = 446515) (by norm_num)
theorem B3175217 : Blo 1981435 3175217 := bstep (se 2 (by rfl) ⟨1190706, by rfl⟩ : syracuseStep 3175217 = 2381413) B2381413
theorem B2116811 : Blo 1981435 2116811 := bstep (se 1 (by rfl) ⟨1587608, by rfl⟩ : syracuseStep 2116811 = 3175217) B3175217
theorem B5644829 : Blo 1981435 5644829 := bstep (se 3 (by rfl) ⟨1058405, by rfl⟩ : syracuseStep 5644829 = 2116811) B2116811
theorem B15052877 : Blo 1981435 15052877 := bstep (se 3 (by rfl) ⟨2822414, by rfl⟩ : syracuseStep 15052877 = 5644829) B5644829
theorem B10035251 : Blo 1981435 10035251 := bstep (se 1 (by rfl) ⟨7526438, by rfl⟩ : syracuseStep 10035251 = 15052877) B15052877
theorem B6690167 : Blo 1981435 6690167 := bstep (se 1 (by rfl) ⟨5017625, by rfl⟩ : syracuseStep 6690167 = 10035251) B10035251
theorem B4460111 : Blo 1981435 4460111 := bstep (se 1 (by rfl) ⟨3345083, by rfl⟩ : syracuseStep 4460111 = 6690167) B6690167
theorem B2973407 : Blo 1981435 2973407 := bstep (se 1 (by rfl) ⟨2230055, by rfl⟩ : syracuseStep 2973407 = 4460111) B4460111
theorem B1982271 : Blo 1981435 1982271 := bstep (se 1 (by rfl) ⟨1486703, by rfl⟩ : syracuseStep 1982271 = 2973407) B2973407
theorem B2973413 : Blo 1981435 2973413 := bbase (se 4 (by rfl) ⟨278757, by rfl⟩ : syracuseStep 2973413 = 557515) (by norm_num)
theorem B1982275 : Blo 1981435 1982275 := bstep (se 1 (by rfl) ⟨1486706, by rfl⟩ : syracuseStep 1982275 = 2973413) B2973413
theorem B5644853 : Blo 1981435 5644853 := bbase (se 5 (by rfl) ⟨264602, by rfl⟩ : syracuseStep 5644853 = 529205) (by norm_num)
theorem B3763235 : Blo 1981435 3763235 := bstep (se 1 (by rfl) ⟨2822426, by rfl⟩ : syracuseStep 3763235 = 5644853) B5644853
theorem B2508823 : Blo 1981435 2508823 := bstep (se 1 (by rfl) ⟨1881617, by rfl⟩ : syracuseStep 2508823 = 3763235) B3763235
theorem B3345097 : Blo 1981435 3345097 := bstep (se 2 (by rfl) ⟨1254411, by rfl⟩ : syracuseStep 3345097 = 2508823) B2508823
theorem B4460129 : Blo 1981435 4460129 := bstep (se 2 (by rfl) ⟨1672548, by rfl⟩ : syracuseStep 4460129 = 3345097) B3345097
theorem B2973419 : Blo 1981435 2973419 := bstep (se 1 (by rfl) ⟨2230064, by rfl⟩ : syracuseStep 2973419 = 4460129) B4460129
theorem B1982279 : Blo 1981435 1982279 := bstep (se 1 (by rfl) ⟨1486709, by rfl⟩ : syracuseStep 1982279 = 2973419) B2973419
theorem B2230069 : Blo 1981435 2230069 := bbase (se 5 (by rfl) ⟨104534, by rfl⟩ : syracuseStep 2230069 = 209069) (by norm_num)
theorem B2973425 : Blo 1981435 2973425 := bstep (se 2 (by rfl) ⟨1115034, by rfl⟩ : syracuseStep 2973425 = 2230069) B2230069
theorem B1982283 : Blo 1981435 1982283 := bstep (se 1 (by rfl) ⟨1486712, by rfl⟩ : syracuseStep 1982283 = 2973425) B2973425
theorem B2508833 : Blo 1981435 2508833 := bbase (se 2 (by rfl) ⟨940812, by rfl⟩ : syracuseStep 2508833 = 1881625) (by norm_num)
theorem B6690221 : Blo 1981435 6690221 := bstep (se 3 (by rfl) ⟨1254416, by rfl⟩ : syracuseStep 6690221 = 2508833) B2508833
theorem B4460147 : Blo 1981435 4460147 := bstep (se 1 (by rfl) ⟨3345110, by rfl⟩ : syracuseStep 4460147 = 6690221) B6690221
theorem B2973431 : Blo 1981435 2973431 := bstep (se 1 (by rfl) ⟨2230073, by rfl⟩ : syracuseStep 2973431 = 4460147) B4460147
theorem B1982287 : Blo 1981435 1982287 := bstep (se 1 (by rfl) ⟨1486715, by rfl⟩ : syracuseStep 1982287 = 2973431) B2973431
theorem B2973437 : Blo 1981435 2973437 := bbase (se 3 (by rfl) ⟨557519, by rfl⟩ : syracuseStep 2973437 = 1115039) (by norm_num)
theorem B1982291 : Blo 1981435 1982291 := bstep (se 1 (by rfl) ⟨1486718, by rfl⟩ : syracuseStep 1982291 = 2973437) B2973437
theorem B4460165 : Blo 1981435 4460165 := bbase (se 4 (by rfl) ⟨418140, by rfl⟩ : syracuseStep 4460165 = 836281) (by norm_num)
theorem B2973443 : Blo 1981435 2973443 := bstep (se 1 (by rfl) ⟨2230082, by rfl⟩ : syracuseStep 2973443 = 4460165) B4460165
theorem B1982295 : Blo 1981435 1982295 := bstep (se 1 (by rfl) ⟨1486721, by rfl⟩ : syracuseStep 1982295 = 2973443) B2973443
theorem B4018693 : Blo 1981435 4018693 := bbase (se 4 (by rfl) ⟨376752, by rfl⟩ : syracuseStep 4018693 = 753505) (by norm_num)
theorem B5358257 : Blo 1981435 5358257 := bstep (se 2 (by rfl) ⟨2009346, by rfl⟩ : syracuseStep 5358257 = 4018693) B4018693
theorem B3572171 : Blo 1981435 3572171 := bstep (se 1 (by rfl) ⟨2679128, by rfl⟩ : syracuseStep 3572171 = 5358257) B5358257
theorem B2381447 : Blo 1981435 2381447 := bstep (se 1 (by rfl) ⟨1786085, by rfl⟩ : syracuseStep 2381447 = 3572171) B3572171
theorem B6350525 : Blo 1981435 6350525 := bstep (se 3 (by rfl) ⟨1190723, by rfl⟩ : syracuseStep 6350525 = 2381447) B2381447
theorem B4233683 : Blo 1981435 4233683 := bstep (se 1 (by rfl) ⟨3175262, by rfl⟩ : syracuseStep 4233683 = 6350525) B6350525
theorem B2822455 : Blo 1981435 2822455 := bstep (se 1 (by rfl) ⟨2116841, by rfl⟩ : syracuseStep 2822455 = 4233683) B4233683
theorem B3763273 : Blo 1981435 3763273 := bstep (se 2 (by rfl) ⟨1411227, by rfl⟩ : syracuseStep 3763273 = 2822455) B2822455
theorem B5017697 : Blo 1981435 5017697 := bstep (se 2 (by rfl) ⟨1881636, by rfl⟩ : syracuseStep 5017697 = 3763273) B3763273
theorem B3345131 : Blo 1981435 3345131 := bstep (se 1 (by rfl) ⟨2508848, by rfl⟩ : syracuseStep 3345131 = 5017697) B5017697
theorem B2230087 : Blo 1981435 2230087 := bstep (se 1 (by rfl) ⟨1672565, by rfl⟩ : syracuseStep 2230087 = 3345131) B3345131
theorem B2973449 : Blo 1981435 2973449 := bstep (se 2 (by rfl) ⟨1115043, by rfl⟩ : syracuseStep 2973449 = 2230087) B2230087
theorem B1982299 : Blo 1981435 1982299 := bstep (se 1 (by rfl) ⟨1486724, by rfl⟩ : syracuseStep 1982299 = 2973449) B2973449
theorem B10035413 : Blo 1981435 10035413 := bbase (se 7 (by rfl) ⟨117602, by rfl⟩ : syracuseStep 10035413 = 235205) (by norm_num)
theorem B6690275 : Blo 1981435 6690275 := bstep (se 1 (by rfl) ⟨5017706, by rfl⟩ : syracuseStep 6690275 = 10035413) B10035413
theorem B4460183 : Blo 1981435 4460183 := bstep (se 1 (by rfl) ⟨3345137, by rfl⟩ : syracuseStep 4460183 = 6690275) B6690275
theorem B2973455 : Blo 1981435 2973455 := bstep (se 1 (by rfl) ⟨2230091, by rfl⟩ : syracuseStep 2973455 = 4460183) B4460183
theorem B1982303 : Blo 1981435 1982303 := bstep (se 1 (by rfl) ⟨1486727, by rfl⟩ : syracuseStep 1982303 = 2973455) B2973455
theorem B2973461 : Blo 1981435 2973461 := bbase (se 6 (by rfl) ⟨69690, by rfl⟩ : syracuseStep 2973461 = 139381) (by norm_num)
theorem B1982307 : Blo 1981435 1982307 := bstep (se 1 (by rfl) ⟨1486730, by rfl⟩ : syracuseStep 1982307 = 2973461) B2973461
theorem B2036773 : Blo 1981435 2036773 := bbase (se 4 (by rfl) ⟨190947, by rfl⟩ : syracuseStep 2036773 = 381895) (by norm_num)
theorem B2715697 : Blo 1981435 2715697 := bstep (se 2 (by rfl) ⟨1018386, by rfl⟩ : syracuseStep 2715697 = 2036773) B2036773
theorem B14483717 : Blo 1981435 14483717 := bstep (se 4 (by rfl) ⟨1357848, by rfl⟩ : syracuseStep 14483717 = 2715697) B2715697
theorem B9655811 : Blo 1981435 9655811 := bstep (se 1 (by rfl) ⟨7241858, by rfl⟩ : syracuseStep 9655811 = 14483717) B14483717
theorem B6437207 : Blo 1981435 6437207 := bstep (se 1 (by rfl) ⟨4827905, by rfl⟩ : syracuseStep 6437207 = 9655811) B9655811
theorem B4291471 : Blo 1981435 4291471 := bstep (se 1 (by rfl) ⟨3218603, by rfl⟩ : syracuseStep 4291471 = 6437207) B6437207
theorem B22887845 : Blo 1981435 22887845 := bstep (se 4 (by rfl) ⟨2145735, by rfl⟩ : syracuseStep 22887845 = 4291471) B4291471
theorem B15258563 : Blo 1981435 15258563 := bstep (se 1 (by rfl) ⟨11443922, by rfl⟩ : syracuseStep 15258563 = 22887845) B22887845
theorem B10172375 : Blo 1981435 10172375 := bstep (se 1 (by rfl) ⟨7629281, by rfl⟩ : syracuseStep 10172375 = 15258563) B15258563
theorem B6781583 : Blo 1981435 6781583 := bstep (se 1 (by rfl) ⟨5086187, by rfl⟩ : syracuseStep 6781583 = 10172375) B10172375
theorem B4521055 : Blo 1981435 4521055 := bstep (se 1 (by rfl) ⟨3390791, by rfl⟩ : syracuseStep 4521055 = 6781583) B6781583
theorem B6028073 : Blo 1981435 6028073 := bstep (se 2 (by rfl) ⟨2260527, by rfl⟩ : syracuseStep 6028073 = 4521055) B4521055
theorem B4018715 : Blo 1981435 4018715 := bstep (se 1 (by rfl) ⟨3014036, by rfl⟩ : syracuseStep 4018715 = 6028073) B6028073
theorem B42866293 : Blo 1981435 42866293 := bstep (se 5 (by rfl) ⟨2009357, by rfl⟩ : syracuseStep 42866293 = 4018715) B4018715
theorem B57155057 : Blo 1981435 57155057 := bstep (se 2 (by rfl) ⟨21433146, by rfl⟩ : syracuseStep 57155057 = 42866293) B42866293
theorem B38103371 : Blo 1981435 38103371 := bstep (se 1 (by rfl) ⟨28577528, by rfl⟩ : syracuseStep 38103371 = 57155057) B57155057
theorem B25402247 : Blo 1981435 25402247 := bstep (se 1 (by rfl) ⟨19051685, by rfl⟩ : syracuseStep 25402247 = 38103371) B38103371
theorem B16934831 : Blo 1981435 16934831 := bstep (se 1 (by rfl) ⟨12701123, by rfl⟩ : syracuseStep 16934831 = 25402247) B25402247
theorem B11289887 : Blo 1981435 11289887 := bstep (se 1 (by rfl) ⟨8467415, by rfl⟩ : syracuseStep 11289887 = 16934831) B16934831
theorem B7526591 : Blo 1981435 7526591 := bstep (se 1 (by rfl) ⟨5644943, by rfl⟩ : syracuseStep 7526591 = 11289887) B11289887
theorem B5017727 : Blo 1981435 5017727 := bstep (se 1 (by rfl) ⟨3763295, by rfl⟩ : syracuseStep 5017727 = 7526591) B7526591
theorem B3345151 : Blo 1981435 3345151 := bstep (se 1 (by rfl) ⟨2508863, by rfl⟩ : syracuseStep 3345151 = 5017727) B5017727
theorem B4460201 : Blo 1981435 4460201 := bstep (se 2 (by rfl) ⟨1672575, by rfl⟩ : syracuseStep 4460201 = 3345151) B3345151
theorem B2973467 : Blo 1981435 2973467 := bstep (se 1 (by rfl) ⟨2230100, by rfl⟩ : syracuseStep 2973467 = 4460201) B4460201
theorem B1982311 : Blo 1981435 1982311 := bstep (se 1 (by rfl) ⟨1486733, by rfl⟩ : syracuseStep 1982311 = 2973467) B2973467
theorem B2230105 : Blo 1981435 2230105 := bbase (se 2 (by rfl) ⟨836289, by rfl⟩ : syracuseStep 2230105 = 1672579) (by norm_num)
theorem B2973473 : Blo 1981435 2973473 := bstep (se 2 (by rfl) ⟨1115052, by rfl⟩ : syracuseStep 2973473 = 2230105) B2230105
theorem B1982315 : Blo 1981435 1982315 := bstep (se 1 (by rfl) ⟨1486736, by rfl⟩ : syracuseStep 1982315 = 2973473) B2973473
theorem B4233725 : Blo 1981435 4233725 := bbase (se 3 (by rfl) ⟨793823, by rfl⟩ : syracuseStep 4233725 = 1587647) (by norm_num)
theorem B2822483 : Blo 1981435 2822483 := bstep (se 1 (by rfl) ⟨2116862, by rfl⟩ : syracuseStep 2822483 = 4233725) B4233725
theorem B7526621 : Blo 1981435 7526621 := bstep (se 3 (by rfl) ⟨1411241, by rfl⟩ : syracuseStep 7526621 = 2822483) B2822483
theorem B5017747 : Blo 1981435 5017747 := bstep (se 1 (by rfl) ⟨3763310, by rfl⟩ : syracuseStep 5017747 = 7526621) B7526621
theorem B6690329 : Blo 1981435 6690329 := bstep (se 2 (by rfl) ⟨2508873, by rfl⟩ : syracuseStep 6690329 = 5017747) B5017747
theorem B4460219 : Blo 1981435 4460219 := bstep (se 1 (by rfl) ⟨3345164, by rfl⟩ : syracuseStep 4460219 = 6690329) B6690329
theorem B2973479 : Blo 1981435 2973479 := bstep (se 1 (by rfl) ⟨2230109, by rfl⟩ : syracuseStep 2973479 = 4460219) B4460219
theorem B1982319 : Blo 1981435 1982319 := bstep (se 1 (by rfl) ⟨1486739, by rfl⟩ : syracuseStep 1982319 = 2973479) B2973479
theorem B2973485 : Blo 1981435 2973485 := bbase (se 3 (by rfl) ⟨557528, by rfl⟩ : syracuseStep 2973485 = 1115057) (by norm_num)
theorem B1982323 : Blo 1981435 1982323 := bstep (se 1 (by rfl) ⟨1486742, by rfl⟩ : syracuseStep 1982323 = 2973485) B2973485
theorem B4460237 : Blo 1981435 4460237 := bbase (se 3 (by rfl) ⟨836294, by rfl⟩ : syracuseStep 4460237 = 1672589) (by norm_num)
theorem B2973491 : Blo 1981435 2973491 := bstep (se 1 (by rfl) ⟨2230118, by rfl⟩ : syracuseStep 2973491 = 4460237) B4460237
theorem B1982327 : Blo 1981435 1982327 := bstep (se 1 (by rfl) ⟨1486745, by rfl⟩ : syracuseStep 1982327 = 2973491) B2973491
theorem B2508889 : Blo 1981435 2508889 := bbase (se 2 (by rfl) ⟨940833, by rfl⟩ : syracuseStep 2508889 = 1881667) (by norm_num)
theorem B3345185 : Blo 1981435 3345185 := bstep (se 2 (by rfl) ⟨1254444, by rfl⟩ : syracuseStep 3345185 = 2508889) B2508889
theorem B2230123 : Blo 1981435 2230123 := bstep (se 1 (by rfl) ⟨1672592, by rfl⟩ : syracuseStep 2230123 = 3345185) B3345185
theorem B2973497 : Blo 1981435 2973497 := bstep (se 2 (by rfl) ⟨1115061, by rfl⟩ : syracuseStep 2973497 = 2230123) B2230123
theorem B1982331 : Blo 1981435 1982331 := bstep (se 1 (by rfl) ⟨1486748, by rfl⟩ : syracuseStep 1982331 = 2973497) B2973497
theorem B7144469 : Blo 1981435 7144469 := bbase (se 6 (by rfl) ⟨167448, by rfl⟩ : syracuseStep 7144469 = 334897) (by norm_num)
theorem B4762979 : Blo 1981435 4762979 := bstep (se 1 (by rfl) ⟨3572234, by rfl⟩ : syracuseStep 4762979 = 7144469) B7144469
theorem B3175319 : Blo 1981435 3175319 := bstep (se 1 (by rfl) ⟨2381489, by rfl⟩ : syracuseStep 3175319 = 4762979) B4762979
theorem B8467517 : Blo 1981435 8467517 := bstep (se 3 (by rfl) ⟨1587659, by rfl⟩ : syracuseStep 8467517 = 3175319) B3175319
theorem B22580045 : Blo 1981435 22580045 := bstep (se 3 (by rfl) ⟨4233758, by rfl⟩ : syracuseStep 22580045 = 8467517) B8467517
theorem B15053363 : Blo 1981435 15053363 := bstep (se 1 (by rfl) ⟨11290022, by rfl⟩ : syracuseStep 15053363 = 22580045) B22580045
theorem B10035575 : Blo 1981435 10035575 := bstep (se 1 (by rfl) ⟨7526681, by rfl⟩ : syracuseStep 10035575 = 15053363) B15053363
theorem B6690383 : Blo 1981435 6690383 := bstep (se 1 (by rfl) ⟨5017787, by rfl⟩ : syracuseStep 6690383 = 10035575) B10035575
theorem B4460255 : Blo 1981435 4460255 := bstep (se 1 (by rfl) ⟨3345191, by rfl⟩ : syracuseStep 4460255 = 6690383) B6690383
theorem B2973503 : Blo 1981435 2973503 := bstep (se 1 (by rfl) ⟨2230127, by rfl⟩ : syracuseStep 2973503 = 4460255) B4460255
theorem B1982335 : Blo 1981435 1982335 := bstep (se 1 (by rfl) ⟨1486751, by rfl⟩ : syracuseStep 1982335 = 2973503) B2973503
theorem B2973509 : Blo 1981435 2973509 := bbase (se 4 (by rfl) ⟨278766, by rfl⟩ : syracuseStep 2973509 = 557533) (by norm_num)
theorem B1982339 : Blo 1981435 1982339 := bstep (se 1 (by rfl) ⟨1486754, by rfl⟩ : syracuseStep 1982339 = 2973509) B2973509
theorem B3345205 : Blo 1981435 3345205 := bbase (se 5 (by rfl) ⟨156806, by rfl⟩ : syracuseStep 3345205 = 313613) (by norm_num)
theorem B4460273 : Blo 1981435 4460273 := bstep (se 2 (by rfl) ⟨1672602, by rfl⟩ : syracuseStep 4460273 = 3345205) B3345205
theorem B2973515 : Blo 1981435 2973515 := bstep (se 1 (by rfl) ⟨2230136, by rfl⟩ : syracuseStep 2973515 = 4460273) B4460273
theorem B1982343 : Blo 1981435 1982343 := bstep (se 1 (by rfl) ⟨1486757, by rfl⟩ : syracuseStep 1982343 = 2973515) B2973515
theorem B2230141 : Blo 1981435 2230141 := bbase (se 3 (by rfl) ⟨418151, by rfl⟩ : syracuseStep 2230141 = 836303) (by norm_num)
theorem B2973521 : Blo 1981435 2973521 := bstep (se 2 (by rfl) ⟨1115070, by rfl⟩ : syracuseStep 2973521 = 2230141) B2230141
theorem B1982347 : Blo 1981435 1982347 := bstep (se 1 (by rfl) ⟨1486760, by rfl⟩ : syracuseStep 1982347 = 2973521) B2973521
theorem B6690437 : Blo 1981435 6690437 := bbase (se 4 (by rfl) ⟨627228, by rfl⟩ : syracuseStep 6690437 = 1254457) (by norm_num)
theorem B4460291 : Blo 1981435 4460291 := bstep (se 1 (by rfl) ⟨3345218, by rfl⟩ : syracuseStep 4460291 = 6690437) B6690437
theorem B2973527 : Blo 1981435 2973527 := bstep (se 1 (by rfl) ⟨2230145, by rfl⟩ : syracuseStep 2973527 = 4460291) B4460291
theorem B1982351 : Blo 1981435 1982351 := bstep (se 1 (by rfl) ⟨1486763, by rfl⟩ : syracuseStep 1982351 = 2973527) B2973527
theorem B2973533 : Blo 1981435 2973533 := bbase (se 3 (by rfl) ⟨557537, by rfl⟩ : syracuseStep 2973533 = 1115075) (by norm_num)
theorem B1982355 : Blo 1981435 1982355 := bstep (se 1 (by rfl) ⟨1486766, by rfl⟩ : syracuseStep 1982355 = 2973533) B2973533
theorem B4460309 : Blo 1981435 4460309 := bbase (se 6 (by rfl) ⟨104538, by rfl⟩ : syracuseStep 4460309 = 209077) (by norm_num)
theorem B2973539 : Blo 1981435 2973539 := bstep (se 1 (by rfl) ⟨2230154, by rfl⟩ : syracuseStep 2973539 = 4460309) B4460309
theorem B1982359 : Blo 1981435 1982359 := bstep (se 1 (by rfl) ⟨1486769, by rfl⟩ : syracuseStep 1982359 = 2973539) B2973539
theorem B7526789 : Blo 1981435 7526789 := bbase (se 4 (by rfl) ⟨705636, by rfl⟩ : syracuseStep 7526789 = 1411273) (by norm_num)
theorem B5017859 : Blo 1981435 5017859 := bstep (se 1 (by rfl) ⟨3763394, by rfl⟩ : syracuseStep 5017859 = 7526789) B7526789
theorem B3345239 : Blo 1981435 3345239 := bstep (se 1 (by rfl) ⟨2508929, by rfl⟩ : syracuseStep 3345239 = 5017859) B5017859
theorem B2230159 : Blo 1981435 2230159 := bstep (se 1 (by rfl) ⟨1672619, by rfl⟩ : syracuseStep 2230159 = 3345239) B3345239
theorem B2973545 : Blo 1981435 2973545 := bstep (se 2 (by rfl) ⟨1115079, by rfl⟩ : syracuseStep 2973545 = 2230159) B2230159
theorem B1982363 : Blo 1981435 1982363 := bstep (se 1 (by rfl) ⟨1486772, by rfl⟩ : syracuseStep 1982363 = 2973545) B2973545
theorem B6350741 : Blo 1981435 6350741 := bbase (se 6 (by rfl) ⟨148845, by rfl⟩ : syracuseStep 6350741 = 297691) (by norm_num)
theorem B4233827 : Blo 1981435 4233827 := bstep (se 1 (by rfl) ⟨3175370, by rfl⟩ : syracuseStep 4233827 = 6350741) B6350741
theorem B11290205 : Blo 1981435 11290205 := bstep (se 3 (by rfl) ⟨2116913, by rfl⟩ : syracuseStep 11290205 = 4233827) B4233827
theorem B7526803 : Blo 1981435 7526803 := bstep (se 1 (by rfl) ⟨5645102, by rfl⟩ : syracuseStep 7526803 = 11290205) B11290205
theorem B10035737 : Blo 1981435 10035737 := bstep (se 2 (by rfl) ⟨3763401, by rfl⟩ : syracuseStep 10035737 = 7526803) B7526803
theorem B6690491 : Blo 1981435 6690491 := bstep (se 1 (by rfl) ⟨5017868, by rfl⟩ : syracuseStep 6690491 = 10035737) B10035737
theorem B4460327 : Blo 1981435 4460327 := bstep (se 1 (by rfl) ⟨3345245, by rfl⟩ : syracuseStep 4460327 = 6690491) B6690491
theorem B2973551 : Blo 1981435 2973551 := bstep (se 1 (by rfl) ⟨2230163, by rfl⟩ : syracuseStep 2973551 = 4460327) B4460327
theorem B1982367 : Blo 1981435 1982367 := bstep (se 1 (by rfl) ⟨1486775, by rfl⟩ : syracuseStep 1982367 = 2973551) B2973551
theorem B2973557 : Blo 1981435 2973557 := bbase (se 5 (by rfl) ⟨139385, by rfl⟩ : syracuseStep 2973557 = 278771) (by norm_num)
theorem B1982371 : Blo 1981435 1982371 := bstep (se 1 (by rfl) ⟨1486778, by rfl⟩ : syracuseStep 1982371 = 2973557) B2973557
theorem B4233845 : Blo 1981435 4233845 := bbase (se 5 (by rfl) ⟨198461, by rfl⟩ : syracuseStep 4233845 = 396923) (by norm_num)
theorem B2822563 : Blo 1981435 2822563 := bstep (se 1 (by rfl) ⟨2116922, by rfl⟩ : syracuseStep 2822563 = 4233845) B4233845
theorem B3763417 : Blo 1981435 3763417 := bstep (se 2 (by rfl) ⟨1411281, by rfl⟩ : syracuseStep 3763417 = 2822563) B2822563
theorem B5017889 : Blo 1981435 5017889 := bstep (se 2 (by rfl) ⟨1881708, by rfl⟩ : syracuseStep 5017889 = 3763417) B3763417
theorem B3345259 : Blo 1981435 3345259 := bstep (se 1 (by rfl) ⟨2508944, by rfl⟩ : syracuseStep 3345259 = 5017889) B5017889
theorem B4460345 : Blo 1981435 4460345 := bstep (se 2 (by rfl) ⟨1672629, by rfl⟩ : syracuseStep 4460345 = 3345259) B3345259
theorem B2973563 : Blo 1981435 2973563 := bstep (se 1 (by rfl) ⟨2230172, by rfl⟩ : syracuseStep 2973563 = 4460345) B4460345
theorem B1982375 : Blo 1981435 1982375 := bstep (se 1 (by rfl) ⟨1486781, by rfl⟩ : syracuseStep 1982375 = 2973563) B2973563
theorem B2230177 : Blo 1981435 2230177 := bbase (se 2 (by rfl) ⟨836316, by rfl⟩ : syracuseStep 2230177 = 1672633) (by norm_num)
theorem B2973569 : Blo 1981435 2973569 := bstep (se 2 (by rfl) ⟨1115088, by rfl⟩ : syracuseStep 2973569 = 2230177) B2230177
theorem B1982379 : Blo 1981435 1982379 := bstep (se 1 (by rfl) ⟨1486784, by rfl⟩ : syracuseStep 1982379 = 2973569) B2973569
theorem B5017909 : Blo 1981435 5017909 := bbase (se 5 (by rfl) ⟨235214, by rfl⟩ : syracuseStep 5017909 = 470429) (by norm_num)
theorem B6690545 : Blo 1981435 6690545 := bstep (se 2 (by rfl) ⟨2508954, by rfl⟩ : syracuseStep 6690545 = 5017909) B5017909
theorem B4460363 : Blo 1981435 4460363 := bstep (se 1 (by rfl) ⟨3345272, by rfl⟩ : syracuseStep 4460363 = 6690545) B6690545
theorem B2973575 : Blo 1981435 2973575 := bstep (se 1 (by rfl) ⟨2230181, by rfl⟩ : syracuseStep 2973575 = 4460363) B4460363
theorem B1982383 : Blo 1981435 1982383 := bstep (se 1 (by rfl) ⟨1486787, by rfl⟩ : syracuseStep 1982383 = 2973575) B2973575
theorem B2973581 : Blo 1981435 2973581 := bbase (se 3 (by rfl) ⟨557546, by rfl⟩ : syracuseStep 2973581 = 1115093) (by norm_num)
theorem B1982387 : Blo 1981435 1982387 := bstep (se 1 (by rfl) ⟨1486790, by rfl⟩ : syracuseStep 1982387 = 2973581) B2973581
theorem B4460381 : Blo 1981435 4460381 := bbase (se 3 (by rfl) ⟨836321, by rfl⟩ : syracuseStep 4460381 = 1672643) (by norm_num)
theorem B2973587 : Blo 1981435 2973587 := bstep (se 1 (by rfl) ⟨2230190, by rfl⟩ : syracuseStep 2973587 = 4460381) B4460381
theorem B1982391 : Blo 1981435 1982391 := bstep (se 1 (by rfl) ⟨1486793, by rfl⟩ : syracuseStep 1982391 = 2973587) B2973587
theorem B3345293 : Blo 1981435 3345293 := bbase (se 3 (by rfl) ⟨627242, by rfl⟩ : syracuseStep 3345293 = 1254485) (by norm_num)
theorem B2230195 : Blo 1981435 2230195 := bstep (se 1 (by rfl) ⟨1672646, by rfl⟩ : syracuseStep 2230195 = 3345293) B3345293
theorem B2973593 : Blo 1981435 2973593 := bstep (se 2 (by rfl) ⟨1115097, by rfl⟩ : syracuseStep 2973593 = 2230195) B2230195
theorem B1982395 : Blo 1981435 1982395 := bstep (se 1 (by rfl) ⟨1486796, by rfl⟩ : syracuseStep 1982395 = 2973593) B2973593
theorem B4291661 : Blo 1981435 4291661 := bbase (se 3 (by rfl) ⟨804686, by rfl⟩ : syracuseStep 4291661 = 1609373) (by norm_num)
theorem B11444429 : Blo 1981435 11444429 := bstep (se 3 (by rfl) ⟨2145830, by rfl⟩ : syracuseStep 11444429 = 4291661) B4291661
theorem B30518477 : Blo 1981435 30518477 := bstep (se 3 (by rfl) ⟨5722214, by rfl⟩ : syracuseStep 30518477 = 11444429) B11444429
theorem B20345651 : Blo 1981435 20345651 := bstep (se 1 (by rfl) ⟨15259238, by rfl⟩ : syracuseStep 20345651 = 30518477) B30518477
theorem B13563767 : Blo 1981435 13563767 := bstep (se 1 (by rfl) ⟨10172825, by rfl⟩ : syracuseStep 13563767 = 20345651) B20345651
theorem B9042511 : Blo 1981435 9042511 := bstep (se 1 (by rfl) ⟨6781883, by rfl⟩ : syracuseStep 9042511 = 13563767) B13563767
theorem B12056681 : Blo 1981435 12056681 := bstep (se 2 (by rfl) ⟨4521255, by rfl⟩ : syracuseStep 12056681 = 9042511) B9042511
theorem B8037787 : Blo 1981435 8037787 := bstep (se 1 (by rfl) ⟨6028340, by rfl⟩ : syracuseStep 8037787 = 12056681) B12056681
theorem B10717049 : Blo 1981435 10717049 := bstep (se 2 (by rfl) ⟨4018893, by rfl⟩ : syracuseStep 10717049 = 8037787) B8037787
theorem B7144699 : Blo 1981435 7144699 := bstep (se 1 (by rfl) ⟨5358524, by rfl⟩ : syracuseStep 7144699 = 10717049) B10717049
theorem B9526265 : Blo 1981435 9526265 := bstep (se 2 (by rfl) ⟨3572349, by rfl⟩ : syracuseStep 9526265 = 7144699) B7144699
theorem B6350843 : Blo 1981435 6350843 := bstep (se 1 (by rfl) ⟨4763132, by rfl⟩ : syracuseStep 6350843 = 9526265) B9526265
theorem B16935581 : Blo 1981435 16935581 := bstep (se 3 (by rfl) ⟨3175421, by rfl⟩ : syracuseStep 16935581 = 6350843) B6350843
theorem B11290387 : Blo 1981435 11290387 := bstep (se 1 (by rfl) ⟨8467790, by rfl⟩ : syracuseStep 11290387 = 16935581) B16935581
theorem B15053849 : Blo 1981435 15053849 := bstep (se 2 (by rfl) ⟨5645193, by rfl⟩ : syracuseStep 15053849 = 11290387) B11290387
theorem B10035899 : Blo 1981435 10035899 := bstep (se 1 (by rfl) ⟨7526924, by rfl⟩ : syracuseStep 10035899 = 15053849) B15053849
theorem B6690599 : Blo 1981435 6690599 := bstep (se 1 (by rfl) ⟨5017949, by rfl⟩ : syracuseStep 6690599 = 10035899) B10035899
theorem B4460399 : Blo 1981435 4460399 := bstep (se 1 (by rfl) ⟨3345299, by rfl⟩ : syracuseStep 4460399 = 6690599) B6690599
theorem B2973599 : Blo 1981435 2973599 := bstep (se 1 (by rfl) ⟨2230199, by rfl⟩ : syracuseStep 2973599 = 4460399) B4460399
theorem B1982399 : Blo 1981435 1982399 := bstep (se 1 (by rfl) ⟨1486799, by rfl⟩ : syracuseStep 1982399 = 2973599) B2973599
theorem B2973605 : Blo 1981435 2973605 := bbase (se 4 (by rfl) ⟨278775, by rfl⟩ : syracuseStep 2973605 = 557551) (by norm_num)
theorem B1982403 : Blo 1981435 1982403 := bstep (se 1 (by rfl) ⟨1486802, by rfl⟩ : syracuseStep 1982403 = 2973605) B2973605
theorem B2508985 : Blo 1981435 2508985 := bbase (se 2 (by rfl) ⟨940869, by rfl⟩ : syracuseStep 2508985 = 1881739) (by norm_num)
theorem B3345313 : Blo 1981435 3345313 := bstep (se 2 (by rfl) ⟨1254492, by rfl⟩ : syracuseStep 3345313 = 2508985) B2508985
theorem B4460417 : Blo 1981435 4460417 := bstep (se 2 (by rfl) ⟨1672656, by rfl⟩ : syracuseStep 4460417 = 3345313) B3345313
theorem B2973611 : Blo 1981435 2973611 := bstep (se 1 (by rfl) ⟨2230208, by rfl⟩ : syracuseStep 2973611 = 4460417) B4460417
theorem B1982407 : Blo 1981435 1982407 := bstep (se 1 (by rfl) ⟨1486805, by rfl⟩ : syracuseStep 1982407 = 2973611) B2973611
theorem B2230213 : Blo 1981435 2230213 := bbase (se 4 (by rfl) ⟨209082, by rfl⟩ : syracuseStep 2230213 = 418165) (by norm_num)
theorem B2973617 : Blo 1981435 2973617 := bstep (se 2 (by rfl) ⟨1115106, by rfl⟩ : syracuseStep 2973617 = 2230213) B2230213
theorem B1982411 : Blo 1981435 1982411 := bstep (se 1 (by rfl) ⟨1486808, by rfl⟩ : syracuseStep 1982411 = 2973617) B2973617
theorem B3763493 : Blo 1981435 3763493 := bbase (se 4 (by rfl) ⟨352827, by rfl⟩ : syracuseStep 3763493 = 705655) (by norm_num)
theorem B2508995 : Blo 1981435 2508995 := bstep (se 1 (by rfl) ⟨1881746, by rfl⟩ : syracuseStep 2508995 = 3763493) B3763493
theorem B6690653 : Blo 1981435 6690653 := bstep (se 3 (by rfl) ⟨1254497, by rfl⟩ : syracuseStep 6690653 = 2508995) B2508995
theorem B4460435 : Blo 1981435 4460435 := bstep (se 1 (by rfl) ⟨3345326, by rfl⟩ : syracuseStep 4460435 = 6690653) B6690653
theorem B2973623 : Blo 1981435 2973623 := bstep (se 1 (by rfl) ⟨2230217, by rfl⟩ : syracuseStep 2973623 = 4460435) B4460435
theorem B1982415 : Blo 1981435 1982415 := bstep (se 1 (by rfl) ⟨1486811, by rfl⟩ : syracuseStep 1982415 = 2973623) B2973623
theorem B2973629 : Blo 1981435 2973629 := bbase (se 3 (by rfl) ⟨557555, by rfl⟩ : syracuseStep 2973629 = 1115111) (by norm_num)
theorem B1982419 : Blo 1981435 1982419 := bstep (se 1 (by rfl) ⟨1486814, by rfl⟩ : syracuseStep 1982419 = 2973629) B2973629
theorem B4460453 : Blo 1981435 4460453 := bbase (se 4 (by rfl) ⟨418167, by rfl⟩ : syracuseStep 4460453 = 836335) (by norm_num)
theorem B2973635 : Blo 1981435 2973635 := bstep (se 1 (by rfl) ⟨2230226, by rfl⟩ : syracuseStep 2973635 = 4460453) B4460453
theorem B1982423 : Blo 1981435 1982423 := bstep (se 1 (by rfl) ⟨1486817, by rfl⟩ : syracuseStep 1982423 = 2973635) B2973635
theorem B5018021 : Blo 1981435 5018021 := bbase (se 4 (by rfl) ⟨470439, by rfl⟩ : syracuseStep 5018021 = 940879) (by norm_num)
theorem B3345347 : Blo 1981435 3345347 := bstep (se 1 (by rfl) ⟨2509010, by rfl⟩ : syracuseStep 3345347 = 5018021) B5018021
theorem B2230231 : Blo 1981435 2230231 := bstep (se 1 (by rfl) ⟨1672673, by rfl⟩ : syracuseStep 2230231 = 3345347) B3345347
theorem B2973641 : Blo 1981435 2973641 := bstep (se 2 (by rfl) ⟨1115115, by rfl⟩ : syracuseStep 2973641 = 2230231) B2230231
theorem B1982427 : Blo 1981435 1982427 := bstep (se 1 (by rfl) ⟨1486820, by rfl⟩ : syracuseStep 1982427 = 2973641) B2973641
theorem B5645285 : Blo 1981435 5645285 := bbase (se 4 (by rfl) ⟨529245, by rfl⟩ : syracuseStep 5645285 = 1058491) (by norm_num)
theorem B3763523 : Blo 1981435 3763523 := bstep (se 1 (by rfl) ⟨2822642, by rfl⟩ : syracuseStep 3763523 = 5645285) B5645285
theorem B10036061 : Blo 1981435 10036061 := bstep (se 3 (by rfl) ⟨1881761, by rfl⟩ : syracuseStep 10036061 = 3763523) B3763523
theorem B6690707 : Blo 1981435 6690707 := bstep (se 1 (by rfl) ⟨5018030, by rfl⟩ : syracuseStep 6690707 = 10036061) B10036061
theorem B4460471 : Blo 1981435 4460471 := bstep (se 1 (by rfl) ⟨3345353, by rfl⟩ : syracuseStep 4460471 = 6690707) B6690707
theorem B2973647 : Blo 1981435 2973647 := bstep (se 1 (by rfl) ⟨2230235, by rfl⟩ : syracuseStep 2973647 = 4460471) B4460471
theorem B1982431 : Blo 1981435 1982431 := bstep (se 1 (by rfl) ⟨1486823, by rfl⟩ : syracuseStep 1982431 = 2973647) B2973647
theorem B2973653 : Blo 1981435 2973653 := bbase (se 7 (by rfl) ⟨34847, by rfl⟩ : syracuseStep 2973653 = 69695) (by norm_num)
theorem B1982435 : Blo 1981435 1982435 := bstep (se 1 (by rfl) ⟨1486826, by rfl⟩ : syracuseStep 1982435 = 2973653) B2973653
theorem B7527077 : Blo 1981435 7527077 := bbase (se 4 (by rfl) ⟨705663, by rfl⟩ : syracuseStep 7527077 = 1411327) (by norm_num)
theorem B5018051 : Blo 1981435 5018051 := bstep (se 1 (by rfl) ⟨3763538, by rfl⟩ : syracuseStep 5018051 = 7527077) B7527077
theorem B3345367 : Blo 1981435 3345367 := bstep (se 1 (by rfl) ⟨2509025, by rfl⟩ : syracuseStep 3345367 = 5018051) B5018051
theorem B4460489 : Blo 1981435 4460489 := bstep (se 2 (by rfl) ⟨1672683, by rfl⟩ : syracuseStep 4460489 = 3345367) B3345367
theorem B2973659 : Blo 1981435 2973659 := bstep (se 1 (by rfl) ⟨2230244, by rfl⟩ : syracuseStep 2973659 = 4460489) B4460489
theorem B1982439 : Blo 1981435 1982439 := bstep (se 1 (by rfl) ⟨1486829, by rfl⟩ : syracuseStep 1982439 = 2973659) B2973659
theorem B2230249 : Blo 1981435 2230249 := bbase (se 2 (by rfl) ⟨836343, by rfl⟩ : syracuseStep 2230249 = 1672687) (by norm_num)
theorem B2973665 : Blo 1981435 2973665 := bstep (se 2 (by rfl) ⟨1115124, by rfl⟩ : syracuseStep 2973665 = 2230249) B2230249
theorem B1982443 : Blo 1981435 1982443 := bstep (se 1 (by rfl) ⟨1486832, by rfl⟩ : syracuseStep 1982443 = 2973665) B2973665
theorem B3572437 : Blo 1981435 3572437 := bbase (se 7 (by rfl) ⟨41864, by rfl⟩ : syracuseStep 3572437 = 83729) (by norm_num)
theorem B4763249 : Blo 1981435 4763249 := bstep (se 2 (by rfl) ⟨1786218, by rfl⟩ : syracuseStep 4763249 = 3572437) B3572437
theorem B3175499 : Blo 1981435 3175499 := bstep (se 1 (by rfl) ⟨2381624, by rfl⟩ : syracuseStep 3175499 = 4763249) B4763249
theorem B2116999 : Blo 1981435 2116999 := bstep (se 1 (by rfl) ⟨1587749, by rfl⟩ : syracuseStep 2116999 = 3175499) B3175499
theorem B11290661 : Blo 1981435 11290661 := bstep (se 4 (by rfl) ⟨1058499, by rfl⟩ : syracuseStep 11290661 = 2116999) B2116999
theorem B7527107 : Blo 1981435 7527107 := bstep (se 1 (by rfl) ⟨5645330, by rfl⟩ : syracuseStep 7527107 = 11290661) B11290661
theorem B5018071 : Blo 1981435 5018071 := bstep (se 1 (by rfl) ⟨3763553, by rfl⟩ : syracuseStep 5018071 = 7527107) B7527107
theorem B6690761 : Blo 1981435 6690761 := bstep (se 2 (by rfl) ⟨2509035, by rfl⟩ : syracuseStep 6690761 = 5018071) B5018071
theorem B4460507 : Blo 1981435 4460507 := bstep (se 1 (by rfl) ⟨3345380, by rfl⟩ : syracuseStep 4460507 = 6690761) B6690761
theorem B2973671 : Blo 1981435 2973671 := bstep (se 1 (by rfl) ⟨2230253, by rfl⟩ : syracuseStep 2973671 = 4460507) B4460507
theorem B1982447 : Blo 1981435 1982447 := bstep (se 1 (by rfl) ⟨1486835, by rfl⟩ : syracuseStep 1982447 = 2973671) B2973671
theorem B2973677 : Blo 1981435 2973677 := bbase (se 3 (by rfl) ⟨557564, by rfl⟩ : syracuseStep 2973677 = 1115129) (by norm_num)
theorem B1982451 : Blo 1981435 1982451 := bstep (se 1 (by rfl) ⟨1486838, by rfl⟩ : syracuseStep 1982451 = 2973677) B2973677
theorem B4460525 : Blo 1981435 4460525 := bbase (se 3 (by rfl) ⟨836348, by rfl⟩ : syracuseStep 4460525 = 1672697) (by norm_num)
theorem B2973683 : Blo 1981435 2973683 := bstep (se 1 (by rfl) ⟨2230262, by rfl⟩ : syracuseStep 2973683 = 4460525) B4460525
theorem B1982455 : Blo 1981435 1982455 := bstep (se 1 (by rfl) ⟨1486841, by rfl⟩ : syracuseStep 1982455 = 2973683) B2973683
theorem B2543285 : Blo 1981435 2543285 := bbase (se 5 (by rfl) ⟨119216, by rfl⟩ : syracuseStep 2543285 = 238433) (by norm_num)
theorem B6782093 : Blo 1981435 6782093 := bstep (se 3 (by rfl) ⟨1271642, by rfl⟩ : syracuseStep 6782093 = 2543285) B2543285
theorem B4521395 : Blo 1981435 4521395 := bstep (se 1 (by rfl) ⟨3391046, by rfl⟩ : syracuseStep 4521395 = 6782093) B6782093
theorem B3014263 : Blo 1981435 3014263 := bstep (se 1 (by rfl) ⟨2260697, by rfl⟩ : syracuseStep 3014263 = 4521395) B4521395
theorem B16076069 : Blo 1981435 16076069 := bstep (se 4 (by rfl) ⟨1507131, by rfl⟩ : syracuseStep 16076069 = 3014263) B3014263
theorem B10717379 : Blo 1981435 10717379 := bstep (se 1 (by rfl) ⟨8038034, by rfl⟩ : syracuseStep 10717379 = 16076069) B16076069
theorem B7144919 : Blo 1981435 7144919 := bstep (se 1 (by rfl) ⟨5358689, by rfl⟩ : syracuseStep 7144919 = 10717379) B10717379
theorem B4763279 : Blo 1981435 4763279 := bstep (se 1 (by rfl) ⟨3572459, by rfl⟩ : syracuseStep 4763279 = 7144919) B7144919
theorem B3175519 : Blo 1981435 3175519 := bstep (se 1 (by rfl) ⟨2381639, by rfl⟩ : syracuseStep 3175519 = 4763279) B4763279
theorem B4234025 : Blo 1981435 4234025 := bstep (se 2 (by rfl) ⟨1587759, by rfl⟩ : syracuseStep 4234025 = 3175519) B3175519
theorem B2822683 : Blo 1981435 2822683 := bstep (se 1 (by rfl) ⟨2117012, by rfl⟩ : syracuseStep 2822683 = 4234025) B4234025
theorem B3763577 : Blo 1981435 3763577 := bstep (se 2 (by rfl) ⟨1411341, by rfl⟩ : syracuseStep 3763577 = 2822683) B2822683
theorem B2509051 : Blo 1981435 2509051 := bstep (se 1 (by rfl) ⟨1881788, by rfl⟩ : syracuseStep 2509051 = 3763577) B3763577
theorem B3345401 : Blo 1981435 3345401 := bstep (se 2 (by rfl) ⟨1254525, by rfl⟩ : syracuseStep 3345401 = 2509051) B2509051
theorem B2230267 : Blo 1981435 2230267 := bstep (se 1 (by rfl) ⟨1672700, by rfl⟩ : syracuseStep 2230267 = 3345401) B3345401
theorem B2973689 : Blo 1981435 2973689 := bstep (se 2 (by rfl) ⟨1115133, by rfl⟩ : syracuseStep 2973689 = 2230267) B2230267
theorem B1982459 : Blo 1981435 1982459 := bstep (se 1 (by rfl) ⟨1486844, by rfl⟩ : syracuseStep 1982459 = 2973689) B2973689
theorem B3621205 : Blo 1981435 3621205 := bbase (se 10 (by rfl) ⟨5304, by rfl⟩ : syracuseStep 3621205 = 10609) (by norm_num)
theorem B19313093 : Blo 1981435 19313093 := bstep (se 4 (by rfl) ⟨1810602, by rfl⟩ : syracuseStep 19313093 = 3621205) B3621205
theorem B51501581 : Blo 1981435 51501581 := bstep (se 3 (by rfl) ⟨9656546, by rfl⟩ : syracuseStep 51501581 = 19313093) B19313093
theorem B34334387 : Blo 1981435 34334387 := bstep (se 1 (by rfl) ⟨25750790, by rfl⟩ : syracuseStep 34334387 = 51501581) B51501581
theorem B22889591 : Blo 1981435 22889591 := bstep (se 1 (by rfl) ⟨17167193, by rfl⟩ : syracuseStep 22889591 = 34334387) B34334387
theorem B15259727 : Blo 1981435 15259727 := bstep (se 1 (by rfl) ⟨11444795, by rfl⟩ : syracuseStep 15259727 = 22889591) B22889591
theorem B10173151 : Blo 1981435 10173151 := bstep (se 1 (by rfl) ⟨7629863, by rfl⟩ : syracuseStep 10173151 = 15259727) B15259727
theorem B54256805 : Blo 1981435 54256805 := bstep (se 4 (by rfl) ⟨5086575, by rfl⟩ : syracuseStep 54256805 = 10173151) B10173151
theorem B36171203 : Blo 1981435 36171203 := bstep (se 1 (by rfl) ⟨27128402, by rfl⟩ : syracuseStep 36171203 = 54256805) B54256805
theorem B385826165 : Blo 1981435 385826165 := bstep (se 5 (by rfl) ⟨18085601, by rfl⟩ : syracuseStep 385826165 = 36171203) B36171203
theorem B257217443 : Blo 1981435 257217443 := bstep (se 1 (by rfl) ⟨192913082, by rfl⟩ : syracuseStep 257217443 = 385826165) B385826165
theorem B171478295 : Blo 1981435 171478295 := bstep (se 1 (by rfl) ⟨128608721, by rfl⟩ : syracuseStep 171478295 = 257217443) B257217443
theorem B114318863 : Blo 1981435 114318863 := bstep (se 1 (by rfl) ⟨85739147, by rfl⟩ : syracuseStep 114318863 = 171478295) B171478295
theorem B76212575 : Blo 1981435 76212575 := bstep (se 1 (by rfl) ⟨57159431, by rfl⟩ : syracuseStep 76212575 = 114318863) B114318863
theorem B50808383 : Blo 1981435 50808383 := bstep (se 1 (by rfl) ⟨38106287, by rfl⟩ : syracuseStep 50808383 = 76212575) B76212575
theorem B33872255 : Blo 1981435 33872255 := bstep (se 1 (by rfl) ⟨25404191, by rfl⟩ : syracuseStep 33872255 = 50808383) B50808383
theorem B22581503 : Blo 1981435 22581503 := bstep (se 1 (by rfl) ⟨16936127, by rfl⟩ : syracuseStep 22581503 = 33872255) B33872255
theorem B15054335 : Blo 1981435 15054335 := bstep (se 1 (by rfl) ⟨11290751, by rfl⟩ : syracuseStep 15054335 = 22581503) B22581503
theorem B10036223 : Blo 1981435 10036223 := bstep (se 1 (by rfl) ⟨7527167, by rfl⟩ : syracuseStep 10036223 = 15054335) B15054335
theorem B6690815 : Blo 1981435 6690815 := bstep (se 1 (by rfl) ⟨5018111, by rfl⟩ : syracuseStep 6690815 = 10036223) B10036223
theorem B4460543 : Blo 1981435 4460543 := bstep (se 1 (by rfl) ⟨3345407, by rfl⟩ : syracuseStep 4460543 = 6690815) B6690815
theorem B2973695 : Blo 1981435 2973695 := bstep (se 1 (by rfl) ⟨2230271, by rfl⟩ : syracuseStep 2973695 = 4460543) B4460543
theorem B1982463 : Blo 1981435 1982463 := bstep (se 1 (by rfl) ⟨1486847, by rfl⟩ : syracuseStep 1982463 = 2973695) B2973695
theorem B2973701 : Blo 1981435 2973701 := bbase (se 4 (by rfl) ⟨278784, by rfl⟩ : syracuseStep 2973701 = 557569) (by norm_num)
theorem B1982467 : Blo 1981435 1982467 := bstep (se 1 (by rfl) ⟨1486850, by rfl⟩ : syracuseStep 1982467 = 2973701) B2973701
theorem B3345421 : Blo 1981435 3345421 := bbase (se 3 (by rfl) ⟨627266, by rfl⟩ : syracuseStep 3345421 = 1254533) (by norm_num)
theorem B4460561 : Blo 1981435 4460561 := bstep (se 2 (by rfl) ⟨1672710, by rfl⟩ : syracuseStep 4460561 = 3345421) B3345421
theorem B2973707 : Blo 1981435 2973707 := bstep (se 1 (by rfl) ⟨2230280, by rfl⟩ : syracuseStep 2973707 = 4460561) B4460561
theorem B1982471 : Blo 1981435 1982471 := bstep (se 1 (by rfl) ⟨1486853, by rfl⟩ : syracuseStep 1982471 = 2973707) B2973707
theorem B2230285 : Blo 1981435 2230285 := bbase (se 3 (by rfl) ⟨418178, by rfl⟩ : syracuseStep 2230285 = 836357) (by norm_num)
theorem B2973713 : Blo 1981435 2973713 := bstep (se 2 (by rfl) ⟨1115142, by rfl⟩ : syracuseStep 2973713 = 2230285) B2230285
theorem B1982475 : Blo 1981435 1982475 := bstep (se 1 (by rfl) ⟨1486856, by rfl⟩ : syracuseStep 1982475 = 2973713) B2973713
theorem B6690869 : Blo 1981435 6690869 := bbase (se 5 (by rfl) ⟨313634, by rfl⟩ : syracuseStep 6690869 = 627269) (by norm_num)
theorem B4460579 : Blo 1981435 4460579 := bstep (se 1 (by rfl) ⟨3345434, by rfl⟩ : syracuseStep 4460579 = 6690869) B6690869
theorem B2973719 : Blo 1981435 2973719 := bstep (se 1 (by rfl) ⟨2230289, by rfl⟩ : syracuseStep 2973719 = 4460579) B4460579
theorem B1982479 : Blo 1981435 1982479 := bstep (se 1 (by rfl) ⟨1486859, by rfl⟩ : syracuseStep 1982479 = 2973719) B2973719
theorem B2973725 : Blo 1981435 2973725 := bbase (se 3 (by rfl) ⟨557573, by rfl⟩ : syracuseStep 2973725 = 1115147) (by norm_num)
theorem B1982483 : Blo 1981435 1982483 := bstep (se 1 (by rfl) ⟨1486862, by rfl⟩ : syracuseStep 1982483 = 2973725) B2973725
theorem B4460597 : Blo 1981435 4460597 := bbase (se 5 (by rfl) ⟨209090, by rfl⟩ : syracuseStep 4460597 = 418181) (by norm_num)
theorem B2973731 : Blo 1981435 2973731 := bstep (se 1 (by rfl) ⟨2230298, by rfl⟩ : syracuseStep 2973731 = 4460597) B4460597
theorem B1982487 : Blo 1981435 1982487 := bstep (se 1 (by rfl) ⟨1486865, by rfl⟩ : syracuseStep 1982487 = 2973731) B2973731
theorem B9526709 : Blo 1981435 9526709 := bbase (se 5 (by rfl) ⟨446564, by rfl⟩ : syracuseStep 9526709 = 893129) (by norm_num)
theorem B6351139 : Blo 1981435 6351139 := bstep (se 1 (by rfl) ⟨4763354, by rfl⟩ : syracuseStep 6351139 = 9526709) B9526709
theorem B8468185 : Blo 1981435 8468185 := bstep (se 2 (by rfl) ⟨3175569, by rfl⟩ : syracuseStep 8468185 = 6351139) B6351139
theorem B11290913 : Blo 1981435 11290913 := bstep (se 2 (by rfl) ⟨4234092, by rfl⟩ : syracuseStep 11290913 = 8468185) B8468185
theorem B7527275 : Blo 1981435 7527275 := bstep (se 1 (by rfl) ⟨5645456, by rfl⟩ : syracuseStep 7527275 = 11290913) B11290913
theorem B5018183 : Blo 1981435 5018183 := bstep (se 1 (by rfl) ⟨3763637, by rfl⟩ : syracuseStep 5018183 = 7527275) B7527275
theorem B3345455 : Blo 1981435 3345455 := bstep (se 1 (by rfl) ⟨2509091, by rfl⟩ : syracuseStep 3345455 = 5018183) B5018183
theorem B2230303 : Blo 1981435 2230303 := bstep (se 1 (by rfl) ⟨1672727, by rfl⟩ : syracuseStep 2230303 = 3345455) B3345455
theorem B2973737 : Blo 1981435 2973737 := bstep (se 2 (by rfl) ⟨1115151, by rfl⟩ : syracuseStep 2973737 = 2230303) B2230303
theorem B1982491 : Blo 1981435 1982491 := bstep (se 1 (by rfl) ⟨1486868, by rfl⟩ : syracuseStep 1982491 = 2973737) B2973737
theorem B9042949 : Blo 1981435 9042949 := bbase (se 4 (by rfl) ⟨847776, by rfl⟩ : syracuseStep 9042949 = 1695553) (by norm_num)
theorem B12057265 : Blo 1981435 12057265 := bstep (se 2 (by rfl) ⟨4521474, by rfl⟩ : syracuseStep 12057265 = 9042949) B9042949
theorem B16076353 : Blo 1981435 16076353 := bstep (se 2 (by rfl) ⟨6028632, by rfl⟩ : syracuseStep 16076353 = 12057265) B12057265
theorem B21435137 : Blo 1981435 21435137 := bstep (se 2 (by rfl) ⟨8038176, by rfl⟩ : syracuseStep 21435137 = 16076353) B16076353
theorem B14290091 : Blo 1981435 14290091 := bstep (se 1 (by rfl) ⟨10717568, by rfl⟩ : syracuseStep 14290091 = 21435137) B21435137
theorem B9526727 : Blo 1981435 9526727 := bstep (se 1 (by rfl) ⟨7145045, by rfl⟩ : syracuseStep 9526727 = 14290091) B14290091
theorem B6351151 : Blo 1981435 6351151 := bstep (se 1 (by rfl) ⟨4763363, by rfl⟩ : syracuseStep 6351151 = 9526727) B9526727
theorem B8468201 : Blo 1981435 8468201 := bstep (se 2 (by rfl) ⟨3175575, by rfl⟩ : syracuseStep 8468201 = 6351151) B6351151
theorem B5645467 : Blo 1981435 5645467 := bstep (se 1 (by rfl) ⟨4234100, by rfl⟩ : syracuseStep 5645467 = 8468201) B8468201
theorem B7527289 : Blo 1981435 7527289 := bstep (se 2 (by rfl) ⟨2822733, by rfl⟩ : syracuseStep 7527289 = 5645467) B5645467
theorem B10036385 : Blo 1981435 10036385 := bstep (se 2 (by rfl) ⟨3763644, by rfl⟩ : syracuseStep 10036385 = 7527289) B7527289
theorem B6690923 : Blo 1981435 6690923 := bstep (se 1 (by rfl) ⟨5018192, by rfl⟩ : syracuseStep 6690923 = 10036385) B10036385
theorem B4460615 : Blo 1981435 4460615 := bstep (se 1 (by rfl) ⟨3345461, by rfl⟩ : syracuseStep 4460615 = 6690923) B6690923
theorem B2973743 : Blo 1981435 2973743 := bstep (se 1 (by rfl) ⟨2230307, by rfl⟩ : syracuseStep 2973743 = 4460615) B4460615
theorem B1982495 : Blo 1981435 1982495 := bstep (se 1 (by rfl) ⟨1486871, by rfl⟩ : syracuseStep 1982495 = 2973743) B2973743
theorem B2973749 : Blo 1981435 2973749 := bbase (se 5 (by rfl) ⟨139394, by rfl⟩ : syracuseStep 2973749 = 278789) (by norm_num)
theorem B1982499 : Blo 1981435 1982499 := bstep (se 1 (by rfl) ⟨1486874, by rfl⟩ : syracuseStep 1982499 = 2973749) B2973749
theorem B5018213 : Blo 1981435 5018213 := bbase (se 4 (by rfl) ⟨470457, by rfl⟩ : syracuseStep 5018213 = 940915) (by norm_num)
theorem B3345475 : Blo 1981435 3345475 := bstep (se 1 (by rfl) ⟨2509106, by rfl⟩ : syracuseStep 3345475 = 5018213) B5018213
theorem B4460633 : Blo 1981435 4460633 := bstep (se 2 (by rfl) ⟨1672737, by rfl⟩ : syracuseStep 4460633 = 3345475) B3345475
theorem B2973755 : Blo 1981435 2973755 := bstep (se 1 (by rfl) ⟨2230316, by rfl⟩ : syracuseStep 2973755 = 4460633) B4460633
theorem B1982503 : Blo 1981435 1982503 := bstep (se 1 (by rfl) ⟨1486877, by rfl⟩ : syracuseStep 1982503 = 2973755) B2973755
theorem B2230321 : Blo 1981435 2230321 := bbase (se 2 (by rfl) ⟨836370, by rfl⟩ : syracuseStep 2230321 = 1672741) (by norm_num)
theorem B2973761 : Blo 1981435 2973761 := bstep (se 2 (by rfl) ⟨1115160, by rfl⟩ : syracuseStep 2973761 = 2230321) B2230321
theorem B1982507 : Blo 1981435 1982507 := bstep (se 1 (by rfl) ⟨1486880, by rfl⟩ : syracuseStep 1982507 = 2973761) B2973761
theorem B9526805 : Blo 1981435 9526805 := bbase (se 6 (by rfl) ⟨223284, by rfl⟩ : syracuseStep 9526805 = 446569) (by norm_num)
theorem B6351203 : Blo 1981435 6351203 := bstep (se 1 (by rfl) ⟨4763402, by rfl⟩ : syracuseStep 6351203 = 9526805) B9526805
theorem B4234135 : Blo 1981435 4234135 := bstep (se 1 (by rfl) ⟨3175601, by rfl⟩ : syracuseStep 4234135 = 6351203) B6351203
theorem B5645513 : Blo 1981435 5645513 := bstep (se 2 (by rfl) ⟨2117067, by rfl⟩ : syracuseStep 5645513 = 4234135) B4234135
theorem B3763675 : Blo 1981435 3763675 := bstep (se 1 (by rfl) ⟨2822756, by rfl⟩ : syracuseStep 3763675 = 5645513) B5645513
theorem B5018233 : Blo 1981435 5018233 := bstep (se 2 (by rfl) ⟨1881837, by rfl⟩ : syracuseStep 5018233 = 3763675) B3763675
theorem B6690977 : Blo 1981435 6690977 := bstep (se 2 (by rfl) ⟨2509116, by rfl⟩ : syracuseStep 6690977 = 5018233) B5018233
theorem B4460651 : Blo 1981435 4460651 := bstep (se 1 (by rfl) ⟨3345488, by rfl⟩ : syracuseStep 4460651 = 6690977) B6690977
theorem B2973767 : Blo 1981435 2973767 := bstep (se 1 (by rfl) ⟨2230325, by rfl⟩ : syracuseStep 2973767 = 4460651) B4460651
theorem B1982511 : Blo 1981435 1982511 := bstep (se 1 (by rfl) ⟨1486883, by rfl⟩ : syracuseStep 1982511 = 2973767) B2973767
theorem B2973773 : Blo 1981435 2973773 := bbase (se 3 (by rfl) ⟨557582, by rfl⟩ : syracuseStep 2973773 = 1115165) (by norm_num)
theorem B1982515 : Blo 1981435 1982515 := bstep (se 1 (by rfl) ⟨1486886, by rfl⟩ : syracuseStep 1982515 = 2973773) B2973773
theorem B4460669 : Blo 1981435 4460669 := bbase (se 3 (by rfl) ⟨836375, by rfl⟩ : syracuseStep 4460669 = 1672751) (by norm_num)
theorem B2973779 : Blo 1981435 2973779 := bstep (se 1 (by rfl) ⟨2230334, by rfl⟩ : syracuseStep 2973779 = 4460669) B4460669
theorem B1982519 : Blo 1981435 1982519 := bstep (se 1 (by rfl) ⟨1486889, by rfl⟩ : syracuseStep 1982519 = 2973779) B2973779
theorem B3345509 : Blo 1981435 3345509 := bbase (se 4 (by rfl) ⟨313641, by rfl⟩ : syracuseStep 3345509 = 627283) (by norm_num)
theorem B2230339 : Blo 1981435 2230339 := bstep (se 1 (by rfl) ⟨1672754, by rfl⟩ : syracuseStep 2230339 = 3345509) B3345509
theorem B2973785 : Blo 1981435 2973785 := bstep (se 2 (by rfl) ⟨1115169, by rfl⟩ : syracuseStep 2973785 = 2230339) B2230339
theorem B1982523 : Blo 1981435 1982523 := bstep (se 1 (by rfl) ⟨1486892, by rfl⟩ : syracuseStep 1982523 = 2973785) B2973785
theorem B3572581 : Blo 1981435 3572581 := bbase (se 4 (by rfl) ⟨334929, by rfl⟩ : syracuseStep 3572581 = 669859) (by norm_num)
theorem B4763441 : Blo 1981435 4763441 := bstep (se 2 (by rfl) ⟨1786290, by rfl⟩ : syracuseStep 4763441 = 3572581) B3572581
theorem B3175627 : Blo 1981435 3175627 := bstep (se 1 (by rfl) ⟨2381720, by rfl⟩ : syracuseStep 3175627 = 4763441) B4763441
theorem B4234169 : Blo 1981435 4234169 := bstep (se 2 (by rfl) ⟨1587813, by rfl⟩ : syracuseStep 4234169 = 3175627) B3175627
theorem B2822779 : Blo 1981435 2822779 := bstep (se 1 (by rfl) ⟨2117084, by rfl⟩ : syracuseStep 2822779 = 4234169) B4234169
theorem B15054821 : Blo 1981435 15054821 := bstep (se 4 (by rfl) ⟨1411389, by rfl⟩ : syracuseStep 15054821 = 2822779) B2822779
theorem B10036547 : Blo 1981435 10036547 := bstep (se 1 (by rfl) ⟨7527410, by rfl⟩ : syracuseStep 10036547 = 15054821) B15054821
theorem B6691031 : Blo 1981435 6691031 := bstep (se 1 (by rfl) ⟨5018273, by rfl⟩ : syracuseStep 6691031 = 10036547) B10036547
theorem B4460687 : Blo 1981435 4460687 := bstep (se 1 (by rfl) ⟨3345515, by rfl⟩ : syracuseStep 4460687 = 6691031) B6691031
theorem B2973791 : Blo 1981435 2973791 := bstep (se 1 (by rfl) ⟨2230343, by rfl⟩ : syracuseStep 2973791 = 4460687) B4460687
theorem B1982527 : Blo 1981435 1982527 := bstep (se 1 (by rfl) ⟨1486895, by rfl⟩ : syracuseStep 1982527 = 2973791) B2973791
theorem B2973797 : Blo 1981435 2973797 := bbase (se 4 (by rfl) ⟨278793, by rfl⟩ : syracuseStep 2973797 = 557587) (by norm_num)
theorem B1982531 : Blo 1981435 1982531 := bstep (se 1 (by rfl) ⟨1486898, by rfl⟩ : syracuseStep 1982531 = 2973797) B2973797
theorem B4763461 : Blo 1981435 4763461 := bbase (se 4 (by rfl) ⟨446574, by rfl⟩ : syracuseStep 4763461 = 893149) (by norm_num)
theorem B6351281 : Blo 1981435 6351281 := bstep (se 2 (by rfl) ⟨2381730, by rfl⟩ : syracuseStep 6351281 = 4763461) B4763461
theorem B4234187 : Blo 1981435 4234187 := bstep (se 1 (by rfl) ⟨3175640, by rfl⟩ : syracuseStep 4234187 = 6351281) B6351281
theorem B2822791 : Blo 1981435 2822791 := bstep (se 1 (by rfl) ⟨2117093, by rfl⟩ : syracuseStep 2822791 = 4234187) B4234187
theorem B3763721 : Blo 1981435 3763721 := bstep (se 2 (by rfl) ⟨1411395, by rfl⟩ : syracuseStep 3763721 = 2822791) B2822791
theorem B2509147 : Blo 1981435 2509147 := bstep (se 1 (by rfl) ⟨1881860, by rfl⟩ : syracuseStep 2509147 = 3763721) B3763721
theorem B3345529 : Blo 1981435 3345529 := bstep (se 2 (by rfl) ⟨1254573, by rfl⟩ : syracuseStep 3345529 = 2509147) B2509147
theorem B4460705 : Blo 1981435 4460705 := bstep (se 2 (by rfl) ⟨1672764, by rfl⟩ : syracuseStep 4460705 = 3345529) B3345529
theorem B2973803 : Blo 1981435 2973803 := bstep (se 1 (by rfl) ⟨2230352, by rfl⟩ : syracuseStep 2973803 = 4460705) B4460705
theorem B1982535 : Blo 1981435 1982535 := bstep (se 1 (by rfl) ⟨1486901, by rfl⟩ : syracuseStep 1982535 = 2973803) B2973803
theorem B2230357 : Blo 1981435 2230357 := bbase (se 8 (by rfl) ⟨13068, by rfl⟩ : syracuseStep 2230357 = 26137) (by norm_num)
theorem B2973809 : Blo 1981435 2973809 := bstep (se 2 (by rfl) ⟨1115178, by rfl⟩ : syracuseStep 2973809 = 2230357) B2230357
theorem B1982539 : Blo 1981435 1982539 := bstep (se 1 (by rfl) ⟨1486904, by rfl⟩ : syracuseStep 1982539 = 2973809) B2973809
theorem B2509157 : Blo 1981435 2509157 := bbase (se 4 (by rfl) ⟨235233, by rfl⟩ : syracuseStep 2509157 = 470467) (by norm_num)
theorem B6691085 : Blo 1981435 6691085 := bstep (se 3 (by rfl) ⟨1254578, by rfl⟩ : syracuseStep 6691085 = 2509157) B2509157
theorem B4460723 : Blo 1981435 4460723 := bstep (se 1 (by rfl) ⟨3345542, by rfl⟩ : syracuseStep 4460723 = 6691085) B6691085
theorem B2973815 : Blo 1981435 2973815 := bstep (se 1 (by rfl) ⟨2230361, by rfl⟩ : syracuseStep 2973815 = 4460723) B4460723
theorem B1982543 : Blo 1981435 1982543 := bstep (se 1 (by rfl) ⟨1486907, by rfl⟩ : syracuseStep 1982543 = 2973815) B2973815
theorem B2973821 : Blo 1981435 2973821 := bbase (se 3 (by rfl) ⟨557591, by rfl⟩ : syracuseStep 2973821 = 1115183) (by norm_num)
theorem B1982547 : Blo 1981435 1982547 := bstep (se 1 (by rfl) ⟨1486910, by rfl⟩ : syracuseStep 1982547 = 2973821) B2973821
theorem B4460741 : Blo 1981435 4460741 := bbase (se 4 (by rfl) ⟨418194, by rfl⟩ : syracuseStep 4460741 = 836389) (by norm_num)
theorem B2973827 : Blo 1981435 2973827 := bstep (se 1 (by rfl) ⟨2230370, by rfl⟩ : syracuseStep 2973827 = 4460741) B4460741
theorem B1982551 : Blo 1981435 1982551 := bstep (se 1 (by rfl) ⟨1486913, by rfl⟩ : syracuseStep 1982551 = 2973827) B2973827
theorem B4828501 : Blo 1981435 4828501 := bbase (se 11 (by rfl) ⟨3536, by rfl⟩ : syracuseStep 4828501 = 7073) (by norm_num)
theorem B6438001 : Blo 1981435 6438001 := bstep (se 2 (by rfl) ⟨2414250, by rfl⟩ : syracuseStep 6438001 = 4828501) B4828501
theorem B8584001 : Blo 1981435 8584001 := bstep (se 2 (by rfl) ⟨3219000, by rfl⟩ : syracuseStep 8584001 = 6438001) B6438001
theorem B5722667 : Blo 1981435 5722667 := bstep (se 1 (by rfl) ⟨4292000, by rfl⟩ : syracuseStep 5722667 = 8584001) B8584001
theorem B3815111 : Blo 1981435 3815111 := bstep (se 1 (by rfl) ⟨2861333, by rfl⟩ : syracuseStep 3815111 = 5722667) B5722667
theorem B2543407 : Blo 1981435 2543407 := bstep (se 1 (by rfl) ⟨1907555, by rfl⟩ : syracuseStep 2543407 = 3815111) B3815111
theorem B13564837 : Blo 1981435 13564837 := bstep (se 4 (by rfl) ⟨1271703, by rfl⟩ : syracuseStep 13564837 = 2543407) B2543407
theorem B18086449 : Blo 1981435 18086449 := bstep (se 2 (by rfl) ⟨6782418, by rfl⟩ : syracuseStep 18086449 = 13564837) B13564837
theorem B24115265 : Blo 1981435 24115265 := bstep (se 2 (by rfl) ⟨9043224, by rfl⟩ : syracuseStep 24115265 = 18086449) B18086449
theorem B16076843 : Blo 1981435 16076843 := bstep (se 1 (by rfl) ⟨12057632, by rfl⟩ : syracuseStep 16076843 = 24115265) B24115265
theorem B10717895 : Blo 1981435 10717895 := bstep (se 1 (by rfl) ⟨8038421, by rfl⟩ : syracuseStep 10717895 = 16076843) B16076843
theorem B7145263 : Blo 1981435 7145263 := bstep (se 1 (by rfl) ⟨5358947, by rfl⟩ : syracuseStep 7145263 = 10717895) B10717895
theorem B9527017 : Blo 1981435 9527017 := bstep (se 2 (by rfl) ⟨3572631, by rfl⟩ : syracuseStep 9527017 = 7145263) B7145263
theorem B12702689 : Blo 1981435 12702689 := bstep (se 2 (by rfl) ⟨4763508, by rfl⟩ : syracuseStep 12702689 = 9527017) B9527017
theorem B8468459 : Blo 1981435 8468459 := bstep (se 1 (by rfl) ⟨6351344, by rfl⟩ : syracuseStep 8468459 = 12702689) B12702689
theorem B5645639 : Blo 1981435 5645639 := bstep (se 1 (by rfl) ⟨4234229, by rfl⟩ : syracuseStep 5645639 = 8468459) B8468459
theorem B3763759 : Blo 1981435 3763759 := bstep (se 1 (by rfl) ⟨2822819, by rfl⟩ : syracuseStep 3763759 = 5645639) B5645639
theorem B5018345 : Blo 1981435 5018345 := bstep (se 2 (by rfl) ⟨1881879, by rfl⟩ : syracuseStep 5018345 = 3763759) B3763759
theorem B3345563 : Blo 1981435 3345563 := bstep (se 1 (by rfl) ⟨2509172, by rfl⟩ : syracuseStep 3345563 = 5018345) B5018345
theorem B2230375 : Blo 1981435 2230375 := bstep (se 1 (by rfl) ⟨1672781, by rfl⟩ : syracuseStep 2230375 = 3345563) B3345563
theorem B2973833 : Blo 1981435 2973833 := bstep (se 2 (by rfl) ⟨1115187, by rfl⟩ : syracuseStep 2973833 = 2230375) B2230375
theorem B1982555 : Blo 1981435 1982555 := bstep (se 1 (by rfl) ⟨1486916, by rfl⟩ : syracuseStep 1982555 = 2973833) B2973833
theorem B10036709 : Blo 1981435 10036709 := bbase (se 4 (by rfl) ⟨940941, by rfl⟩ : syracuseStep 10036709 = 1881883) (by norm_num)
theorem B6691139 : Blo 1981435 6691139 := bstep (se 1 (by rfl) ⟨5018354, by rfl⟩ : syracuseStep 6691139 = 10036709) B10036709
theorem B4460759 : Blo 1981435 4460759 := bstep (se 1 (by rfl) ⟨3345569, by rfl⟩ : syracuseStep 4460759 = 6691139) B6691139
theorem B2973839 : Blo 1981435 2973839 := bstep (se 1 (by rfl) ⟨2230379, by rfl⟩ : syracuseStep 2973839 = 4460759) B4460759
theorem B1982559 : Blo 1981435 1982559 := bstep (se 1 (by rfl) ⟨1486919, by rfl⟩ : syracuseStep 1982559 = 2973839) B2973839
theorem B2973845 : Blo 1981435 2973845 := bbase (se 6 (by rfl) ⟨69699, by rfl⟩ : syracuseStep 2973845 = 139399) (by norm_num)
theorem B1982563 : Blo 1981435 1982563 := bstep (se 1 (by rfl) ⟨1486922, by rfl⟩ : syracuseStep 1982563 = 2973845) B2973845
theorem B3572653 : Blo 1981435 3572653 := bbase (se 3 (by rfl) ⟨669872, by rfl⟩ : syracuseStep 3572653 = 1339745) (by norm_num)
theorem B4763537 : Blo 1981435 4763537 := bstep (se 2 (by rfl) ⟨1786326, by rfl⟩ : syracuseStep 4763537 = 3572653) B3572653
theorem B3175691 : Blo 1981435 3175691 := bstep (se 1 (by rfl) ⟨2381768, by rfl⟩ : syracuseStep 3175691 = 4763537) B4763537
theorem B8468509 : Blo 1981435 8468509 := bstep (se 3 (by rfl) ⟨1587845, by rfl⟩ : syracuseStep 8468509 = 3175691) B3175691
theorem B11291345 : Blo 1981435 11291345 := bstep (se 2 (by rfl) ⟨4234254, by rfl⟩ : syracuseStep 11291345 = 8468509) B8468509
theorem B7527563 : Blo 1981435 7527563 := bstep (se 1 (by rfl) ⟨5645672, by rfl⟩ : syracuseStep 7527563 = 11291345) B11291345
theorem B5018375 : Blo 1981435 5018375 := bstep (se 1 (by rfl) ⟨3763781, by rfl⟩ : syracuseStep 5018375 = 7527563) B7527563
theorem B3345583 : Blo 1981435 3345583 := bstep (se 1 (by rfl) ⟨2509187, by rfl⟩ : syracuseStep 3345583 = 5018375) B5018375
theorem B4460777 : Blo 1981435 4460777 := bstep (se 2 (by rfl) ⟨1672791, by rfl⟩ : syracuseStep 4460777 = 3345583) B3345583
theorem B2973851 : Blo 1981435 2973851 := bstep (se 1 (by rfl) ⟨2230388, by rfl⟩ : syracuseStep 2973851 = 4460777) B4460777
theorem B1982567 : Blo 1981435 1982567 := bstep (se 1 (by rfl) ⟨1486925, by rfl⟩ : syracuseStep 1982567 = 2973851) B2973851
theorem B2230393 : Blo 1981435 2230393 := bbase (se 2 (by rfl) ⟨836397, by rfl⟩ : syracuseStep 2230393 = 1672795) (by norm_num)
theorem B2973857 : Blo 1981435 2973857 := bstep (se 2 (by rfl) ⟨1115196, by rfl⟩ : syracuseStep 2973857 = 2230393) B2230393
theorem B1982571 : Blo 1981435 1982571 := bstep (se 1 (by rfl) ⟨1486928, by rfl⟩ : syracuseStep 1982571 = 2973857) B2973857
theorem B27129941 : Blo 1981435 27129941 := bbase (se 8 (by rfl) ⟨158964, by rfl⟩ : syracuseStep 27129941 = 317929) (by norm_num)
theorem B18086627 : Blo 1981435 18086627 := bstep (se 1 (by rfl) ⟨13564970, by rfl⟩ : syracuseStep 18086627 = 27129941) B27129941
theorem B12057751 : Blo 1981435 12057751 := bstep (se 1 (by rfl) ⟨9043313, by rfl⟩ : syracuseStep 12057751 = 18086627) B18086627
theorem B64308005 : Blo 1981435 64308005 := bstep (se 4 (by rfl) ⟨6028875, by rfl⟩ : syracuseStep 64308005 = 12057751) B12057751
theorem B42872003 : Blo 1981435 42872003 := bstep (se 1 (by rfl) ⟨32154002, by rfl⟩ : syracuseStep 42872003 = 64308005) B64308005
theorem B28581335 : Blo 1981435 28581335 := bstep (se 1 (by rfl) ⟨21436001, by rfl⟩ : syracuseStep 28581335 = 42872003) B42872003
theorem B19054223 : Blo 1981435 19054223 := bstep (se 1 (by rfl) ⟨14290667, by rfl⟩ : syracuseStep 19054223 = 28581335) B28581335
theorem B12702815 : Blo 1981435 12702815 := bstep (se 1 (by rfl) ⟨9527111, by rfl⟩ : syracuseStep 12702815 = 19054223) B19054223
theorem B8468543 : Blo 1981435 8468543 := bstep (se 1 (by rfl) ⟨6351407, by rfl⟩ : syracuseStep 8468543 = 12702815) B12702815
theorem B5645695 : Blo 1981435 5645695 := bstep (se 1 (by rfl) ⟨4234271, by rfl⟩ : syracuseStep 5645695 = 8468543) B8468543
theorem B7527593 : Blo 1981435 7527593 := bstep (se 2 (by rfl) ⟨2822847, by rfl⟩ : syracuseStep 7527593 = 5645695) B5645695
theorem B5018395 : Blo 1981435 5018395 := bstep (se 1 (by rfl) ⟨3763796, by rfl⟩ : syracuseStep 5018395 = 7527593) B7527593
theorem B6691193 : Blo 1981435 6691193 := bstep (se 2 (by rfl) ⟨2509197, by rfl⟩ : syracuseStep 6691193 = 5018395) B5018395
theorem B4460795 : Blo 1981435 4460795 := bstep (se 1 (by rfl) ⟨3345596, by rfl⟩ : syracuseStep 4460795 = 6691193) B6691193
theorem B2973863 : Blo 1981435 2973863 := bstep (se 1 (by rfl) ⟨2230397, by rfl⟩ : syracuseStep 2973863 = 4460795) B4460795
theorem B1982575 : Blo 1981435 1982575 := bstep (se 1 (by rfl) ⟨1486931, by rfl⟩ : syracuseStep 1982575 = 2973863) B2973863
theorem B2973869 : Blo 1981435 2973869 := bbase (se 3 (by rfl) ⟨557600, by rfl⟩ : syracuseStep 2973869 = 1115201) (by norm_num)
theorem B1982579 : Blo 1981435 1982579 := bstep (se 1 (by rfl) ⟨1486934, by rfl⟩ : syracuseStep 1982579 = 2973869) B2973869
theorem B4460813 : Blo 1981435 4460813 := bbase (se 3 (by rfl) ⟨836402, by rfl⟩ : syracuseStep 4460813 = 1672805) (by norm_num)
theorem B2973875 : Blo 1981435 2973875 := bstep (se 1 (by rfl) ⟨2230406, by rfl⟩ : syracuseStep 2973875 = 4460813) B4460813
theorem B1982583 : Blo 1981435 1982583 := bstep (se 1 (by rfl) ⟨1486937, by rfl⟩ : syracuseStep 1982583 = 2973875) B2973875
theorem B2509213 : Blo 1981435 2509213 := bbase (se 3 (by rfl) ⟨470477, by rfl⟩ : syracuseStep 2509213 = 940955) (by norm_num)
theorem B3345617 : Blo 1981435 3345617 := bstep (se 2 (by rfl) ⟨1254606, by rfl⟩ : syracuseStep 3345617 = 2509213) B2509213
theorem B2230411 : Blo 1981435 2230411 := bstep (se 1 (by rfl) ⟨1672808, by rfl⟩ : syracuseStep 2230411 = 3345617) B3345617
theorem B2973881 : Blo 1981435 2973881 := bstep (se 2 (by rfl) ⟨1115205, by rfl⟩ : syracuseStep 2973881 = 2230411) B2230411
theorem B1982587 : Blo 1981435 1982587 := bstep (se 1 (by rfl) ⟨1486940, by rfl⟩ : syracuseStep 1982587 = 2973881) B2973881
theorem B2381797 : Blo 1981435 2381797 := bbase (se 4 (by rfl) ⟨223293, by rfl⟩ : syracuseStep 2381797 = 446587) (by norm_num)
theorem B3175729 : Blo 1981435 3175729 := bstep (se 2 (by rfl) ⟨1190898, by rfl⟩ : syracuseStep 3175729 = 2381797) B2381797
theorem B16937221 : Blo 1981435 16937221 := bstep (se 4 (by rfl) ⟨1587864, by rfl⟩ : syracuseStep 16937221 = 3175729) B3175729
theorem B22582961 : Blo 1981435 22582961 := bstep (se 2 (by rfl) ⟨8468610, by rfl⟩ : syracuseStep 22582961 = 16937221) B16937221
theorem B15055307 : Blo 1981435 15055307 := bstep (se 1 (by rfl) ⟨11291480, by rfl⟩ : syracuseStep 15055307 = 22582961) B22582961
theorem B10036871 : Blo 1981435 10036871 := bstep (se 1 (by rfl) ⟨7527653, by rfl⟩ : syracuseStep 10036871 = 15055307) B15055307
theorem B6691247 : Blo 1981435 6691247 := bstep (se 1 (by rfl) ⟨5018435, by rfl⟩ : syracuseStep 6691247 = 10036871) B10036871
theorem B4460831 : Blo 1981435 4460831 := bstep (se 1 (by rfl) ⟨3345623, by rfl⟩ : syracuseStep 4460831 = 6691247) B6691247
theorem B2973887 : Blo 1981435 2973887 := bstep (se 1 (by rfl) ⟨2230415, by rfl⟩ : syracuseStep 2973887 = 4460831) B4460831
theorem B1982591 : Blo 1981435 1982591 := bstep (se 1 (by rfl) ⟨1486943, by rfl⟩ : syracuseStep 1982591 = 2973887) B2973887
theorem B2973893 : Blo 1981435 2973893 := bbase (se 4 (by rfl) ⟨278802, by rfl⟩ : syracuseStep 2973893 = 557605) (by norm_num)
theorem B1982595 : Blo 1981435 1982595 := bstep (se 1 (by rfl) ⟨1486946, by rfl⟩ : syracuseStep 1982595 = 2973893) B2973893
theorem B3345637 : Blo 1981435 3345637 := bbase (se 4 (by rfl) ⟨313653, by rfl⟩ : syracuseStep 3345637 = 627307) (by norm_num)
theorem B4460849 : Blo 1981435 4460849 := bstep (se 2 (by rfl) ⟨1672818, by rfl⟩ : syracuseStep 4460849 = 3345637) B3345637
theorem B2973899 : Blo 1981435 2973899 := bstep (se 1 (by rfl) ⟨2230424, by rfl⟩ : syracuseStep 2973899 = 4460849) B4460849
theorem B1982599 : Blo 1981435 1982599 := bstep (se 1 (by rfl) ⟨1486949, by rfl⟩ : syracuseStep 1982599 = 2973899) B2973899
theorem B2230429 : Blo 1981435 2230429 := bbase (se 3 (by rfl) ⟨418205, by rfl⟩ : syracuseStep 2230429 = 836411) (by norm_num)
theorem B2973905 : Blo 1981435 2973905 := bstep (se 2 (by rfl) ⟨1115214, by rfl⟩ : syracuseStep 2973905 = 2230429) B2230429
theorem B1982603 : Blo 1981435 1982603 := bstep (se 1 (by rfl) ⟨1486952, by rfl⟩ : syracuseStep 1982603 = 2973905) B2973905
theorem B6691301 : Blo 1981435 6691301 := bbase (se 4 (by rfl) ⟨627309, by rfl⟩ : syracuseStep 6691301 = 1254619) (by norm_num)
theorem B4460867 : Blo 1981435 4460867 := bstep (se 1 (by rfl) ⟨3345650, by rfl⟩ : syracuseStep 4460867 = 6691301) B6691301
theorem B2973911 : Blo 1981435 2973911 := bstep (se 1 (by rfl) ⟨2230433, by rfl⟩ : syracuseStep 2973911 = 4460867) B4460867
theorem B1982607 : Blo 1981435 1982607 := bstep (se 1 (by rfl) ⟨1486955, by rfl⟩ : syracuseStep 1982607 = 2973911) B2973911
theorem B2973917 : Blo 1981435 2973917 := bbase (se 3 (by rfl) ⟨557609, by rfl⟩ : syracuseStep 2973917 = 1115219) (by norm_num)
theorem B1982611 : Blo 1981435 1982611 := bstep (se 1 (by rfl) ⟨1486958, by rfl⟩ : syracuseStep 1982611 = 2973917) B2973917
theorem B4460885 : Blo 1981435 4460885 := bbase (se 10 (by rfl) ⟨6534, by rfl⟩ : syracuseStep 4460885 = 13069) (by norm_num)
theorem B2973923 : Blo 1981435 2973923 := bstep (se 1 (by rfl) ⟨2230442, by rfl⟩ : syracuseStep 2973923 = 4460885) B4460885
theorem B1982615 : Blo 1981435 1982615 := bstep (se 1 (by rfl) ⟨1486961, by rfl⟩ : syracuseStep 1982615 = 2973923) B2973923
theorem B16077365 : Blo 1981435 16077365 := bbase (se 5 (by rfl) ⟨753626, by rfl⟩ : syracuseStep 16077365 = 1507253) (by norm_num)
theorem B10718243 : Blo 1981435 10718243 := bstep (se 1 (by rfl) ⟨8038682, by rfl⟩ : syracuseStep 10718243 = 16077365) B16077365
theorem B7145495 : Blo 1981435 7145495 := bstep (se 1 (by rfl) ⟨5359121, by rfl⟩ : syracuseStep 7145495 = 10718243) B10718243
theorem B4763663 : Blo 1981435 4763663 := bstep (se 1 (by rfl) ⟨3572747, by rfl⟩ : syracuseStep 4763663 = 7145495) B7145495
theorem B3175775 : Blo 1981435 3175775 := bstep (se 1 (by rfl) ⟨2381831, by rfl⟩ : syracuseStep 3175775 = 4763663) B4763663
theorem B2117183 : Blo 1981435 2117183 := bstep (se 1 (by rfl) ⟨1587887, by rfl⟩ : syracuseStep 2117183 = 3175775) B3175775
theorem B5645821 : Blo 1981435 5645821 := bstep (se 3 (by rfl) ⟨1058591, by rfl⟩ : syracuseStep 5645821 = 2117183) B2117183
theorem B7527761 : Blo 1981435 7527761 := bstep (se 2 (by rfl) ⟨2822910, by rfl⟩ : syracuseStep 7527761 = 5645821) B5645821
theorem B5018507 : Blo 1981435 5018507 := bstep (se 1 (by rfl) ⟨3763880, by rfl⟩ : syracuseStep 5018507 = 7527761) B7527761
theorem B3345671 : Blo 1981435 3345671 := bstep (se 1 (by rfl) ⟨2509253, by rfl⟩ : syracuseStep 3345671 = 5018507) B5018507
theorem B2230447 : Blo 1981435 2230447 := bstep (se 1 (by rfl) ⟨1672835, by rfl⟩ : syracuseStep 2230447 = 3345671) B3345671
theorem B2973929 : Blo 1981435 2973929 := bstep (se 2 (by rfl) ⟨1115223, by rfl⟩ : syracuseStep 2973929 = 2230447) B2230447
theorem B1982619 : Blo 1981435 1982619 := bstep (se 1 (by rfl) ⟨1486964, by rfl⟩ : syracuseStep 1982619 = 2973929) B2973929
theorem B2679565 : Blo 1981435 2679565 := bbase (se 3 (by rfl) ⟨502418, by rfl⟩ : syracuseStep 2679565 = 1004837) (by norm_num)
theorem B3572753 : Blo 1981435 3572753 := bstep (se 2 (by rfl) ⟨1339782, by rfl⟩ : syracuseStep 3572753 = 2679565) B2679565
theorem B38109365 : Blo 1981435 38109365 := bstep (se 5 (by rfl) ⟨1786376, by rfl⟩ : syracuseStep 38109365 = 3572753) B3572753
theorem B25406243 : Blo 1981435 25406243 := bstep (se 1 (by rfl) ⟨19054682, by rfl⟩ : syracuseStep 25406243 = 38109365) B38109365
theorem B16937495 : Blo 1981435 16937495 := bstep (se 1 (by rfl) ⟨12703121, by rfl⟩ : syracuseStep 16937495 = 25406243) B25406243
theorem B11291663 : Blo 1981435 11291663 := bstep (se 1 (by rfl) ⟨8468747, by rfl⟩ : syracuseStep 11291663 = 16937495) B16937495
theorem B7527775 : Blo 1981435 7527775 := bstep (se 1 (by rfl) ⟨5645831, by rfl⟩ : syracuseStep 7527775 = 11291663) B11291663
theorem B10037033 : Blo 1981435 10037033 := bstep (se 2 (by rfl) ⟨3763887, by rfl⟩ : syracuseStep 10037033 = 7527775) B7527775
theorem B6691355 : Blo 1981435 6691355 := bstep (se 1 (by rfl) ⟨5018516, by rfl⟩ : syracuseStep 6691355 = 10037033) B10037033
theorem B4460903 : Blo 1981435 4460903 := bstep (se 1 (by rfl) ⟨3345677, by rfl⟩ : syracuseStep 4460903 = 6691355) B6691355
theorem B2973935 : Blo 1981435 2973935 := bstep (se 1 (by rfl) ⟨2230451, by rfl⟩ : syracuseStep 2973935 = 4460903) B4460903
theorem B1982623 : Blo 1981435 1982623 := bstep (se 1 (by rfl) ⟨1486967, by rfl⟩ : syracuseStep 1982623 = 2973935) B2973935
theorem B2973941 : Blo 1981435 2973941 := bbase (se 5 (by rfl) ⟨139403, by rfl⟩ : syracuseStep 2973941 = 278807) (by norm_num)
theorem B1982627 : Blo 1981435 1982627 := bstep (se 1 (by rfl) ⟨1486970, by rfl⟩ : syracuseStep 1982627 = 2973941) B2973941
theorem B4292165 : Blo 1981435 4292165 := bbase (se 4 (by rfl) ⟨402390, by rfl⟩ : syracuseStep 4292165 = 804781) (by norm_num)
theorem B2861443 : Blo 1981435 2861443 := bstep (se 1 (by rfl) ⟨2146082, by rfl⟩ : syracuseStep 2861443 = 4292165) B4292165
theorem B3815257 : Blo 1981435 3815257 := bstep (se 2 (by rfl) ⟨1430721, by rfl⟩ : syracuseStep 3815257 = 2861443) B2861443
theorem B5087009 : Blo 1981435 5087009 := bstep (se 2 (by rfl) ⟨1907628, by rfl⟩ : syracuseStep 5087009 = 3815257) B3815257
theorem B3391339 : Blo 1981435 3391339 := bstep (se 1 (by rfl) ⟨2543504, by rfl⟩ : syracuseStep 3391339 = 5087009) B5087009
theorem B4521785 : Blo 1981435 4521785 := bstep (se 2 (by rfl) ⟨1695669, by rfl⟩ : syracuseStep 4521785 = 3391339) B3391339
theorem B12058093 : Blo 1981435 12058093 := bstep (se 3 (by rfl) ⟨2260892, by rfl⟩ : syracuseStep 12058093 = 4521785) B4521785
theorem B16077457 : Blo 1981435 16077457 := bstep (se 2 (by rfl) ⟨6029046, by rfl⟩ : syracuseStep 16077457 = 12058093) B12058093
theorem B21436609 : Blo 1981435 21436609 := bstep (se 2 (by rfl) ⟨8038728, by rfl⟩ : syracuseStep 21436609 = 16077457) B16077457
theorem B28582145 : Blo 1981435 28582145 := bstep (se 2 (by rfl) ⟨10718304, by rfl⟩ : syracuseStep 28582145 = 21436609) B21436609
theorem B19054763 : Blo 1981435 19054763 := bstep (se 1 (by rfl) ⟨14291072, by rfl⟩ : syracuseStep 19054763 = 28582145) B28582145
theorem B12703175 : Blo 1981435 12703175 := bstep (se 1 (by rfl) ⟨9527381, by rfl⟩ : syracuseStep 12703175 = 19054763) B19054763
theorem B8468783 : Blo 1981435 8468783 := bstep (se 1 (by rfl) ⟨6351587, by rfl⟩ : syracuseStep 8468783 = 12703175) B12703175
theorem B5645855 : Blo 1981435 5645855 := bstep (se 1 (by rfl) ⟨4234391, by rfl⟩ : syracuseStep 5645855 = 8468783) B8468783
theorem B3763903 : Blo 1981435 3763903 := bstep (se 1 (by rfl) ⟨2822927, by rfl⟩ : syracuseStep 3763903 = 5645855) B5645855
theorem B5018537 : Blo 1981435 5018537 := bstep (se 2 (by rfl) ⟨1881951, by rfl⟩ : syracuseStep 5018537 = 3763903) B3763903
theorem B3345691 : Blo 1981435 3345691 := bstep (se 1 (by rfl) ⟨2509268, by rfl⟩ : syracuseStep 3345691 = 5018537) B5018537
theorem B4460921 : Blo 1981435 4460921 := bstep (se 2 (by rfl) ⟨1672845, by rfl⟩ : syracuseStep 4460921 = 3345691) B3345691
theorem B2973947 : Blo 1981435 2973947 := bstep (se 1 (by rfl) ⟨2230460, by rfl⟩ : syracuseStep 2973947 = 4460921) B4460921
theorem B1982631 : Blo 1981435 1982631 := bstep (se 1 (by rfl) ⟨1486973, by rfl⟩ : syracuseStep 1982631 = 2973947) B2973947
theorem B2230465 : Blo 1981435 2230465 := bbase (se 2 (by rfl) ⟨836424, by rfl⟩ : syracuseStep 2230465 = 1672849) (by norm_num)
theorem B2973953 : Blo 1981435 2973953 := bstep (se 2 (by rfl) ⟨1115232, by rfl⟩ : syracuseStep 2973953 = 2230465) B2230465
theorem B1982635 : Blo 1981435 1982635 := bstep (se 1 (by rfl) ⟨1486976, by rfl⟩ : syracuseStep 1982635 = 2973953) B2973953
theorem B5018557 : Blo 1981435 5018557 := bbase (se 3 (by rfl) ⟨940979, by rfl⟩ : syracuseStep 5018557 = 1881959) (by norm_num)
theorem B6691409 : Blo 1981435 6691409 := bstep (se 2 (by rfl) ⟨2509278, by rfl⟩ : syracuseStep 6691409 = 5018557) B5018557
theorem B4460939 : Blo 1981435 4460939 := bstep (se 1 (by rfl) ⟨3345704, by rfl⟩ : syracuseStep 4460939 = 6691409) B6691409
theorem B2973959 : Blo 1981435 2973959 := bstep (se 1 (by rfl) ⟨2230469, by rfl⟩ : syracuseStep 2973959 = 4460939) B4460939
theorem B1982639 : Blo 1981435 1982639 := bstep (se 1 (by rfl) ⟨1486979, by rfl⟩ : syracuseStep 1982639 = 2973959) B2973959
theorem B2973965 : Blo 1981435 2973965 := bbase (se 3 (by rfl) ⟨557618, by rfl⟩ : syracuseStep 2973965 = 1115237) (by norm_num)
theorem B1982643 : Blo 1981435 1982643 := bstep (se 1 (by rfl) ⟨1486982, by rfl⟩ : syracuseStep 1982643 = 2973965) B2973965
theorem B4460957 : Blo 1981435 4460957 := bbase (se 3 (by rfl) ⟨836429, by rfl⟩ : syracuseStep 4460957 = 1672859) (by norm_num)
theorem B2973971 : Blo 1981435 2973971 := bstep (se 1 (by rfl) ⟨2230478, by rfl⟩ : syracuseStep 2973971 = 4460957) B4460957
theorem B1982647 : Blo 1981435 1982647 := bstep (se 1 (by rfl) ⟨1486985, by rfl⟩ : syracuseStep 1982647 = 2973971) B2973971
theorem B3345725 : Blo 1981435 3345725 := bbase (se 3 (by rfl) ⟨627323, by rfl⟩ : syracuseStep 3345725 = 1254647) (by norm_num)
theorem B2230483 : Blo 1981435 2230483 := bstep (se 1 (by rfl) ⟨1672862, by rfl⟩ : syracuseStep 2230483 = 3345725) B3345725
theorem B2973977 : Blo 1981435 2973977 := bstep (se 2 (by rfl) ⟨1115241, by rfl⟩ : syracuseStep 2973977 = 2230483) B2230483
theorem B1982651 : Blo 1981435 1982651 := bstep (se 1 (by rfl) ⟨1486988, by rfl⟩ : syracuseStep 1982651 = 2973977) B2973977
theorem B2117221 : Blo 1981435 2117221 := bbase (se 4 (by rfl) ⟨198489, by rfl⟩ : syracuseStep 2117221 = 396979) (by norm_num)
theorem B11291845 : Blo 1981435 11291845 := bstep (se 4 (by rfl) ⟨1058610, by rfl⟩ : syracuseStep 11291845 = 2117221) B2117221
theorem B15055793 : Blo 1981435 15055793 := bstep (se 2 (by rfl) ⟨5645922, by rfl⟩ : syracuseStep 15055793 = 11291845) B11291845
theorem B10037195 : Blo 1981435 10037195 := bstep (se 1 (by rfl) ⟨7527896, by rfl⟩ : syracuseStep 10037195 = 15055793) B15055793
theorem B6691463 : Blo 1981435 6691463 := bstep (se 1 (by rfl) ⟨5018597, by rfl⟩ : syracuseStep 6691463 = 10037195) B10037195
theorem B4460975 : Blo 1981435 4460975 := bstep (se 1 (by rfl) ⟨3345731, by rfl⟩ : syracuseStep 4460975 = 6691463) B6691463
theorem B2973983 : Blo 1981435 2973983 := bstep (se 1 (by rfl) ⟨2230487, by rfl⟩ : syracuseStep 2973983 = 4460975) B4460975
theorem B1982655 : Blo 1981435 1982655 := bstep (se 1 (by rfl) ⟨1486991, by rfl⟩ : syracuseStep 1982655 = 2973983) B2973983
theorem B2973989 : Blo 1981435 2973989 := bbase (se 4 (by rfl) ⟨278811, by rfl⟩ : syracuseStep 2973989 = 557623) (by norm_num)
theorem B1982659 : Blo 1981435 1982659 := bstep (se 1 (by rfl) ⟨1486994, by rfl⟩ : syracuseStep 1982659 = 2973989) B2973989
theorem B2509309 : Blo 1981435 2509309 := bbase (se 3 (by rfl) ⟨470495, by rfl⟩ : syracuseStep 2509309 = 940991) (by norm_num)
theorem B3345745 : Blo 1981435 3345745 := bstep (se 2 (by rfl) ⟨1254654, by rfl⟩ : syracuseStep 3345745 = 2509309) B2509309
theorem B4460993 : Blo 1981435 4460993 := bstep (se 2 (by rfl) ⟨1672872, by rfl⟩ : syracuseStep 4460993 = 3345745) B3345745
theorem B2973995 : Blo 1981435 2973995 := bstep (se 1 (by rfl) ⟨2230496, by rfl⟩ : syracuseStep 2973995 = 4460993) B4460993
theorem B1982663 : Blo 1981435 1982663 := bstep (se 1 (by rfl) ⟨1486997, by rfl⟩ : syracuseStep 1982663 = 2973995) B2973995
theorem B2230501 : Blo 1981435 2230501 := bbase (se 4 (by rfl) ⟨209109, by rfl⟩ : syracuseStep 2230501 = 418219) (by norm_num)
theorem B2974001 : Blo 1981435 2974001 := bstep (se 2 (by rfl) ⟨1115250, by rfl⟩ : syracuseStep 2974001 = 2230501) B2230501
theorem B1982667 : Blo 1981435 1982667 := bstep (se 1 (by rfl) ⟨1487000, by rfl⟩ : syracuseStep 1982667 = 2974001) B2974001
theorem B4234477 : Blo 1981435 4234477 := bbase (se 3 (by rfl) ⟨793964, by rfl⟩ : syracuseStep 4234477 = 1587929) (by norm_num)
theorem B5645969 : Blo 1981435 5645969 := bstep (se 2 (by rfl) ⟨2117238, by rfl⟩ : syracuseStep 5645969 = 4234477) B4234477
theorem B3763979 : Blo 1981435 3763979 := bstep (se 1 (by rfl) ⟨2822984, by rfl⟩ : syracuseStep 3763979 = 5645969) B5645969
theorem B2509319 : Blo 1981435 2509319 := bstep (se 1 (by rfl) ⟨1881989, by rfl⟩ : syracuseStep 2509319 = 3763979) B3763979
theorem B6691517 : Blo 1981435 6691517 := bstep (se 3 (by rfl) ⟨1254659, by rfl⟩ : syracuseStep 6691517 = 2509319) B2509319
theorem B4461011 : Blo 1981435 4461011 := bstep (se 1 (by rfl) ⟨3345758, by rfl⟩ : syracuseStep 4461011 = 6691517) B6691517
theorem B2974007 : Blo 1981435 2974007 := bstep (se 1 (by rfl) ⟨2230505, by rfl⟩ : syracuseStep 2974007 = 4461011) B4461011
theorem B1982671 : Blo 1981435 1982671 := bstep (se 1 (by rfl) ⟨1487003, by rfl⟩ : syracuseStep 1982671 = 2974007) B2974007
theorem B2974013 : Blo 1981435 2974013 := bbase (se 3 (by rfl) ⟨557627, by rfl⟩ : syracuseStep 2974013 = 1115255) (by norm_num)
theorem B1982675 : Blo 1981435 1982675 := bstep (se 1 (by rfl) ⟨1487006, by rfl⟩ : syracuseStep 1982675 = 2974013) B2974013
theorem B4461029 : Blo 1981435 4461029 := bbase (se 4 (by rfl) ⟨418221, by rfl⟩ : syracuseStep 4461029 = 836443) (by norm_num)
theorem B2974019 : Blo 1981435 2974019 := bstep (se 1 (by rfl) ⟨2230514, by rfl⟩ : syracuseStep 2974019 = 4461029) B4461029
theorem B1982679 : Blo 1981435 1982679 := bstep (se 1 (by rfl) ⟨1487009, by rfl⟩ : syracuseStep 1982679 = 2974019) B2974019
theorem B5018669 : Blo 1981435 5018669 := bbase (se 3 (by rfl) ⟨941000, by rfl⟩ : syracuseStep 5018669 = 1882001) (by norm_num)
theorem B3345779 : Blo 1981435 3345779 := bstep (se 1 (by rfl) ⟨2509334, by rfl⟩ : syracuseStep 3345779 = 5018669) B5018669
theorem B2230519 : Blo 1981435 2230519 := bstep (se 1 (by rfl) ⟨1672889, by rfl⟩ : syracuseStep 2230519 = 3345779) B3345779
theorem B2974025 : Blo 1981435 2974025 := bstep (se 2 (by rfl) ⟨1115259, by rfl⟩ : syracuseStep 2974025 = 2230519) B2230519
theorem B1982683 : Blo 1981435 1982683 := bstep (se 1 (by rfl) ⟨1487012, by rfl⟩ : syracuseStep 1982683 = 2974025) B2974025
theorem B14291477 : Blo 1981435 14291477 := bbase (se 6 (by rfl) ⟨334956, by rfl⟩ : syracuseStep 14291477 = 669913) (by norm_num)
theorem B9527651 : Blo 1981435 9527651 := bstep (se 1 (by rfl) ⟨7145738, by rfl⟩ : syracuseStep 9527651 = 14291477) B14291477
theorem B6351767 : Blo 1981435 6351767 := bstep (se 1 (by rfl) ⟨4763825, by rfl⟩ : syracuseStep 6351767 = 9527651) B9527651
theorem B4234511 : Blo 1981435 4234511 := bstep (se 1 (by rfl) ⟨3175883, by rfl⟩ : syracuseStep 4234511 = 6351767) B6351767
theorem B2823007 : Blo 1981435 2823007 := bstep (se 1 (by rfl) ⟨2117255, by rfl⟩ : syracuseStep 2823007 = 4234511) B4234511
theorem B3764009 : Blo 1981435 3764009 := bstep (se 2 (by rfl) ⟨1411503, by rfl⟩ : syracuseStep 3764009 = 2823007) B2823007
theorem B10037357 : Blo 1981435 10037357 := bstep (se 3 (by rfl) ⟨1882004, by rfl⟩ : syracuseStep 10037357 = 3764009) B3764009
theorem B6691571 : Blo 1981435 6691571 := bstep (se 1 (by rfl) ⟨5018678, by rfl⟩ : syracuseStep 6691571 = 10037357) B10037357
theorem B4461047 : Blo 1981435 4461047 := bstep (se 1 (by rfl) ⟨3345785, by rfl⟩ : syracuseStep 4461047 = 6691571) B6691571
theorem B2974031 : Blo 1981435 2974031 := bstep (se 1 (by rfl) ⟨2230523, by rfl⟩ : syracuseStep 2974031 = 4461047) B4461047
theorem B1982687 : Blo 1981435 1982687 := bstep (se 1 (by rfl) ⟨1487015, by rfl⟩ : syracuseStep 1982687 = 2974031) B2974031
theorem B2974037 : Blo 1981435 2974037 := bbase (se 10 (by rfl) ⟨4356, by rfl⟩ : syracuseStep 2974037 = 8713) (by norm_num)
theorem B1982691 : Blo 1981435 1982691 := bstep (se 1 (by rfl) ⟨1487018, by rfl⟩ : syracuseStep 1982691 = 2974037) B2974037
theorem B5646037 : Blo 1981435 5646037 := bbase (se 7 (by rfl) ⟨66164, by rfl⟩ : syracuseStep 5646037 = 132329) (by norm_num)
theorem B7528049 : Blo 1981435 7528049 := bstep (se 2 (by rfl) ⟨2823018, by rfl⟩ : syracuseStep 7528049 = 5646037) B5646037
theorem B5018699 : Blo 1981435 5018699 := bstep (se 1 (by rfl) ⟨3764024, by rfl⟩ : syracuseStep 5018699 = 7528049) B7528049
theorem B3345799 : Blo 1981435 3345799 := bstep (se 1 (by rfl) ⟨2509349, by rfl⟩ : syracuseStep 3345799 = 5018699) B5018699
theorem B4461065 : Blo 1981435 4461065 := bstep (se 2 (by rfl) ⟨1672899, by rfl⟩ : syracuseStep 4461065 = 3345799) B3345799
theorem B2974043 : Blo 1981435 2974043 := bstep (se 1 (by rfl) ⟨2230532, by rfl⟩ : syracuseStep 2974043 = 4461065) B4461065
theorem B1982695 : Blo 1981435 1982695 := bstep (se 1 (by rfl) ⟨1487021, by rfl⟩ : syracuseStep 1982695 = 2974043) B2974043
theorem B2230537 : Blo 1981435 2230537 := bbase (se 2 (by rfl) ⟨836451, by rfl⟩ : syracuseStep 2230537 = 1672903) (by norm_num)
theorem B2974049 : Blo 1981435 2974049 := bstep (se 2 (by rfl) ⟨1115268, by rfl⟩ : syracuseStep 2974049 = 2230537) B2230537
theorem B1982699 : Blo 1981435 1982699 := bstep (se 1 (by rfl) ⟨1487024, by rfl⟩ : syracuseStep 1982699 = 2974049) B2974049
theorem B12223061 : Blo 1981435 12223061 := bbase (se 8 (by rfl) ⟨71619, by rfl⟩ : syracuseStep 12223061 = 143239) (by norm_num)
theorem B8148707 : Blo 1981435 8148707 := bstep (se 1 (by rfl) ⟨6111530, by rfl⟩ : syracuseStep 8148707 = 12223061) B12223061
theorem B5432471 : Blo 1981435 5432471 := bstep (se 1 (by rfl) ⟨4074353, by rfl⟩ : syracuseStep 5432471 = 8148707) B8148707
theorem B3621647 : Blo 1981435 3621647 := bstep (se 1 (by rfl) ⟨2716235, by rfl⟩ : syracuseStep 3621647 = 5432471) B5432471
theorem B2414431 : Blo 1981435 2414431 := bstep (se 1 (by rfl) ⟨1810823, by rfl⟩ : syracuseStep 2414431 = 3621647) B3621647
theorem B12876965 : Blo 1981435 12876965 := bstep (se 4 (by rfl) ⟨1207215, by rfl⟩ : syracuseStep 12876965 = 2414431) B2414431
theorem B8584643 : Blo 1981435 8584643 := bstep (se 1 (by rfl) ⟨6438482, by rfl⟩ : syracuseStep 8584643 = 12876965) B12876965
theorem B5723095 : Blo 1981435 5723095 := bstep (se 1 (by rfl) ⟨4292321, by rfl⟩ : syracuseStep 5723095 = 8584643) B8584643
theorem B7630793 : Blo 1981435 7630793 := bstep (se 2 (by rfl) ⟨2861547, by rfl⟩ : syracuseStep 7630793 = 5723095) B5723095
theorem B5087195 : Blo 1981435 5087195 := bstep (se 1 (by rfl) ⟨3815396, by rfl⟩ : syracuseStep 5087195 = 7630793) B7630793
theorem B3391463 : Blo 1981435 3391463 := bstep (se 1 (by rfl) ⟨2543597, by rfl⟩ : syracuseStep 3391463 = 5087195) B5087195
theorem B2260975 : Blo 1981435 2260975 := bstep (se 1 (by rfl) ⟨1695731, by rfl⟩ : syracuseStep 2260975 = 3391463) B3391463
theorem B3014633 : Blo 1981435 3014633 := bstep (se 2 (by rfl) ⟨1130487, by rfl⟩ : syracuseStep 3014633 = 2260975) B2260975
theorem B2009755 : Blo 1981435 2009755 := bstep (se 1 (by rfl) ⟨1507316, by rfl⟩ : syracuseStep 2009755 = 3014633) B3014633
theorem B10718693 : Blo 1981435 10718693 := bstep (se 4 (by rfl) ⟨1004877, by rfl⟩ : syracuseStep 10718693 = 2009755) B2009755
theorem B7145795 : Blo 1981435 7145795 := bstep (se 1 (by rfl) ⟨5359346, by rfl⟩ : syracuseStep 7145795 = 10718693) B10718693
theorem B4763863 : Blo 1981435 4763863 := bstep (se 1 (by rfl) ⟨3572897, by rfl⟩ : syracuseStep 4763863 = 7145795) B7145795
theorem B25407269 : Blo 1981435 25407269 := bstep (se 4 (by rfl) ⟨2381931, by rfl⟩ : syracuseStep 25407269 = 4763863) B4763863
theorem B16938179 : Blo 1981435 16938179 := bstep (se 1 (by rfl) ⟨12703634, by rfl⟩ : syracuseStep 16938179 = 25407269) B25407269
theorem B11292119 : Blo 1981435 11292119 := bstep (se 1 (by rfl) ⟨8469089, by rfl⟩ : syracuseStep 11292119 = 16938179) B16938179
theorem B7528079 : Blo 1981435 7528079 := bstep (se 1 (by rfl) ⟨5646059, by rfl⟩ : syracuseStep 7528079 = 11292119) B11292119
theorem B5018719 : Blo 1981435 5018719 := bstep (se 1 (by rfl) ⟨3764039, by rfl⟩ : syracuseStep 5018719 = 7528079) B7528079
theorem B6691625 : Blo 1981435 6691625 := bstep (se 2 (by rfl) ⟨2509359, by rfl⟩ : syracuseStep 6691625 = 5018719) B5018719
theorem B4461083 : Blo 1981435 4461083 := bstep (se 1 (by rfl) ⟨3345812, by rfl⟩ : syracuseStep 4461083 = 6691625) B6691625
theorem B2974055 : Blo 1981435 2974055 := bstep (se 1 (by rfl) ⟨2230541, by rfl⟩ : syracuseStep 2974055 = 4461083) B4461083
theorem B1982703 : Blo 1981435 1982703 := bstep (se 1 (by rfl) ⟨1487027, by rfl⟩ : syracuseStep 1982703 = 2974055) B2974055
theorem B2974061 : Blo 1981435 2974061 := bbase (se 3 (by rfl) ⟨557636, by rfl⟩ : syracuseStep 2974061 = 1115273) (by norm_num)
theorem B1982707 : Blo 1981435 1982707 := bstep (se 1 (by rfl) ⟨1487030, by rfl⟩ : syracuseStep 1982707 = 2974061) B2974061
theorem B4461101 : Blo 1981435 4461101 := bbase (se 3 (by rfl) ⟨836456, by rfl⟩ : syracuseStep 4461101 = 1672913) (by norm_num)
theorem B2974067 : Blo 1981435 2974067 := bstep (se 1 (by rfl) ⟨2230550, by rfl⟩ : syracuseStep 2974067 = 4461101) B4461101
theorem B1982711 : Blo 1981435 1982711 := bstep (se 1 (by rfl) ⟨1487033, by rfl⟩ : syracuseStep 1982711 = 2974067) B2974067
theorem B19055573 : Blo 1981435 19055573 := bbase (se 7 (by rfl) ⟨223307, by rfl⟩ : syracuseStep 19055573 = 446615) (by norm_num)
theorem B12703715 : Blo 1981435 12703715 := bstep (se 1 (by rfl) ⟨9527786, by rfl⟩ : syracuseStep 12703715 = 19055573) B19055573
theorem B8469143 : Blo 1981435 8469143 := bstep (se 1 (by rfl) ⟨6351857, by rfl⟩ : syracuseStep 8469143 = 12703715) B12703715
theorem B5646095 : Blo 1981435 5646095 := bstep (se 1 (by rfl) ⟨4234571, by rfl⟩ : syracuseStep 5646095 = 8469143) B8469143
theorem B3764063 : Blo 1981435 3764063 := bstep (se 1 (by rfl) ⟨2823047, by rfl⟩ : syracuseStep 3764063 = 5646095) B5646095
theorem B2509375 : Blo 1981435 2509375 := bstep (se 1 (by rfl) ⟨1882031, by rfl⟩ : syracuseStep 2509375 = 3764063) B3764063
theorem B3345833 : Blo 1981435 3345833 := bstep (se 2 (by rfl) ⟨1254687, by rfl⟩ : syracuseStep 3345833 = 2509375) B2509375
theorem B2230555 : Blo 1981435 2230555 := bstep (se 1 (by rfl) ⟨1672916, by rfl⟩ : syracuseStep 2230555 = 3345833) B3345833
theorem B2974073 : Blo 1981435 2974073 := bstep (se 2 (by rfl) ⟨1115277, by rfl⟩ : syracuseStep 2974073 = 2230555) B2230555
theorem B1982715 : Blo 1981435 1982715 := bstep (se 1 (by rfl) ⟨1487036, by rfl⟩ : syracuseStep 1982715 = 2974073) B2974073
theorem B33876629 : Blo 1981435 33876629 := bbase (se 6 (by rfl) ⟨793983, by rfl⟩ : syracuseStep 33876629 = 1587967) (by norm_num)
theorem B22584419 : Blo 1981435 22584419 := bstep (se 1 (by rfl) ⟨16938314, by rfl⟩ : syracuseStep 22584419 = 33876629) B33876629
theorem B15056279 : Blo 1981435 15056279 := bstep (se 1 (by rfl) ⟨11292209, by rfl⟩ : syracuseStep 15056279 = 22584419) B22584419
theorem B10037519 : Blo 1981435 10037519 := bstep (se 1 (by rfl) ⟨7528139, by rfl⟩ : syracuseStep 10037519 = 15056279) B15056279
theorem B6691679 : Blo 1981435 6691679 := bstep (se 1 (by rfl) ⟨5018759, by rfl⟩ : syracuseStep 6691679 = 10037519) B10037519
theorem B4461119 : Blo 1981435 4461119 := bstep (se 1 (by rfl) ⟨3345839, by rfl⟩ : syracuseStep 4461119 = 6691679) B6691679
theorem B2974079 : Blo 1981435 2974079 := bstep (se 1 (by rfl) ⟨2230559, by rfl⟩ : syracuseStep 2974079 = 4461119) B4461119
theorem B1982719 : Blo 1981435 1982719 := bstep (se 1 (by rfl) ⟨1487039, by rfl⟩ : syracuseStep 1982719 = 2974079) B2974079
theorem B2974085 : Blo 1981435 2974085 := bbase (se 4 (by rfl) ⟨278820, by rfl⟩ : syracuseStep 2974085 = 557641) (by norm_num)
theorem B1982723 : Blo 1981435 1982723 := bstep (se 1 (by rfl) ⟨1487042, by rfl⟩ : syracuseStep 1982723 = 2974085) B2974085
theorem B3345853 : Blo 1981435 3345853 := bbase (se 3 (by rfl) ⟨627347, by rfl⟩ : syracuseStep 3345853 = 1254695) (by norm_num)
theorem B4461137 : Blo 1981435 4461137 := bstep (se 2 (by rfl) ⟨1672926, by rfl⟩ : syracuseStep 4461137 = 3345853) B3345853
theorem B2974091 : Blo 1981435 2974091 := bstep (se 1 (by rfl) ⟨2230568, by rfl⟩ : syracuseStep 2974091 = 4461137) B4461137
theorem B1982727 : Blo 1981435 1982727 := bstep (se 1 (by rfl) ⟨1487045, by rfl⟩ : syracuseStep 1982727 = 2974091) B2974091
theorem B2230573 : Blo 1981435 2230573 := bbase (se 3 (by rfl) ⟨418232, by rfl⟩ : syracuseStep 2230573 = 836465) (by norm_num)
theorem B2974097 : Blo 1981435 2974097 := bstep (se 2 (by rfl) ⟨1115286, by rfl⟩ : syracuseStep 2974097 = 2230573) B2230573
theorem B1982731 : Blo 1981435 1982731 := bstep (se 1 (by rfl) ⟨1487048, by rfl⟩ : syracuseStep 1982731 = 2974097) B2974097
theorem B6691733 : Blo 1981435 6691733 := bbase (se 6 (by rfl) ⟨156837, by rfl⟩ : syracuseStep 6691733 = 313675) (by norm_num)
theorem B4461155 : Blo 1981435 4461155 := bstep (se 1 (by rfl) ⟨3345866, by rfl⟩ : syracuseStep 4461155 = 6691733) B6691733
theorem B2974103 : Blo 1981435 2974103 := bstep (se 1 (by rfl) ⟨2230577, by rfl⟩ : syracuseStep 2974103 = 4461155) B4461155
theorem B1982735 : Blo 1981435 1982735 := bstep (se 1 (by rfl) ⟨1487051, by rfl⟩ : syracuseStep 1982735 = 2974103) B2974103
theorem B2974109 : Blo 1981435 2974109 := bbase (se 3 (by rfl) ⟨557645, by rfl⟩ : syracuseStep 2974109 = 1115291) (by norm_num)
theorem B1982739 : Blo 1981435 1982739 := bstep (se 1 (by rfl) ⟨1487054, by rfl⟩ : syracuseStep 1982739 = 2974109) B2974109
theorem B4461173 : Blo 1981435 4461173 := bbase (se 5 (by rfl) ⟨209117, by rfl⟩ : syracuseStep 4461173 = 418235) (by norm_num)
theorem B2974115 : Blo 1981435 2974115 := bstep (se 1 (by rfl) ⟨2230586, by rfl⟩ : syracuseStep 2974115 = 4461173) B4461173
theorem B1982743 : Blo 1981435 1982743 := bstep (se 1 (by rfl) ⟨1487057, by rfl⟩ : syracuseStep 1982743 = 2974115) B2974115
theorem B2679733 : Blo 1981435 2679733 := bbase (se 5 (by rfl) ⟨125612, by rfl⟩ : syracuseStep 2679733 = 251225) (by norm_num)
theorem B14291909 : Blo 1981435 14291909 := bstep (se 4 (by rfl) ⟨1339866, by rfl⟩ : syracuseStep 14291909 = 2679733) B2679733
theorem B9527939 : Blo 1981435 9527939 := bstep (se 1 (by rfl) ⟨7145954, by rfl⟩ : syracuseStep 9527939 = 14291909) B14291909
theorem B6351959 : Blo 1981435 6351959 := bstep (se 1 (by rfl) ⟨4763969, by rfl⟩ : syracuseStep 6351959 = 9527939) B9527939
theorem B16938557 : Blo 1981435 16938557 := bstep (se 3 (by rfl) ⟨3175979, by rfl⟩ : syracuseStep 16938557 = 6351959) B6351959
theorem B11292371 : Blo 1981435 11292371 := bstep (se 1 (by rfl) ⟨8469278, by rfl⟩ : syracuseStep 11292371 = 16938557) B16938557
theorem B7528247 : Blo 1981435 7528247 := bstep (se 1 (by rfl) ⟨5646185, by rfl⟩ : syracuseStep 7528247 = 11292371) B11292371
theorem B5018831 : Blo 1981435 5018831 := bstep (se 1 (by rfl) ⟨3764123, by rfl⟩ : syracuseStep 5018831 = 7528247) B7528247
theorem B3345887 : Blo 1981435 3345887 := bstep (se 1 (by rfl) ⟨2509415, by rfl⟩ : syracuseStep 3345887 = 5018831) B5018831
theorem B2230591 : Blo 1981435 2230591 := bstep (se 1 (by rfl) ⟨1672943, by rfl⟩ : syracuseStep 2230591 = 3345887) B3345887
theorem B2974121 : Blo 1981435 2974121 := bstep (se 2 (by rfl) ⟨1115295, by rfl⟩ : syracuseStep 2974121 = 2230591) B2230591
theorem B1982747 : Blo 1981435 1982747 := bstep (se 1 (by rfl) ⟨1487060, by rfl⟩ : syracuseStep 1982747 = 2974121) B2974121
theorem B7528261 : Blo 1981435 7528261 := bbase (se 4 (by rfl) ⟨705774, by rfl⟩ : syracuseStep 7528261 = 1411549) (by norm_num)
theorem B10037681 : Blo 1981435 10037681 := bstep (se 2 (by rfl) ⟨3764130, by rfl⟩ : syracuseStep 10037681 = 7528261) B7528261
theorem B6691787 : Blo 1981435 6691787 := bstep (se 1 (by rfl) ⟨5018840, by rfl⟩ : syracuseStep 6691787 = 10037681) B10037681
theorem B4461191 : Blo 1981435 4461191 := bstep (se 1 (by rfl) ⟨3345893, by rfl⟩ : syracuseStep 4461191 = 6691787) B6691787
theorem B2974127 : Blo 1981435 2974127 := bstep (se 1 (by rfl) ⟨2230595, by rfl⟩ : syracuseStep 2974127 = 4461191) B4461191
theorem B1982751 : Blo 1981435 1982751 := bstep (se 1 (by rfl) ⟨1487063, by rfl⟩ : syracuseStep 1982751 = 2974127) B2974127
theorem B2974133 : Blo 1981435 2974133 := bbase (se 5 (by rfl) ⟨139412, by rfl⟩ : syracuseStep 2974133 = 278825) (by norm_num)
theorem B1982755 : Blo 1981435 1982755 := bstep (se 1 (by rfl) ⟨1487066, by rfl⟩ : syracuseStep 1982755 = 2974133) B2974133
theorem B5018861 : Blo 1981435 5018861 := bbase (se 3 (by rfl) ⟨941036, by rfl⟩ : syracuseStep 5018861 = 1882073) (by norm_num)
theorem B3345907 : Blo 1981435 3345907 := bstep (se 1 (by rfl) ⟨2509430, by rfl⟩ : syracuseStep 3345907 = 5018861) B5018861
theorem B4461209 : Blo 1981435 4461209 := bstep (se 2 (by rfl) ⟨1672953, by rfl⟩ : syracuseStep 4461209 = 3345907) B3345907
theorem B2974139 : Blo 1981435 2974139 := bstep (se 1 (by rfl) ⟨2230604, by rfl⟩ : syracuseStep 2974139 = 4461209) B4461209
theorem B1982759 : Blo 1981435 1982759 := bstep (se 1 (by rfl) ⟨1487069, by rfl⟩ : syracuseStep 1982759 = 2974139) B2974139
theorem B2230609 : Blo 1981435 2230609 := bbase (se 2 (by rfl) ⟨836478, by rfl⟩ : syracuseStep 2230609 = 1672957) (by norm_num)
theorem B2974145 : Blo 1981435 2974145 := bstep (se 2 (by rfl) ⟨1115304, by rfl⟩ : syracuseStep 2974145 = 2230609) B2230609
theorem B1982763 : Blo 1981435 1982763 := bstep (se 1 (by rfl) ⟨1487072, by rfl⟩ : syracuseStep 1982763 = 2974145) B2974145
theorem B2117341 : Blo 1981435 2117341 := bbase (se 3 (by rfl) ⟨397001, by rfl⟩ : syracuseStep 2117341 = 794003) (by norm_num)
theorem B2823121 : Blo 1981435 2823121 := bstep (se 2 (by rfl) ⟨1058670, by rfl⟩ : syracuseStep 2823121 = 2117341) B2117341
theorem B3764161 : Blo 1981435 3764161 := bstep (se 2 (by rfl) ⟨1411560, by rfl⟩ : syracuseStep 3764161 = 2823121) B2823121
theorem B5018881 : Blo 1981435 5018881 := bstep (se 2 (by rfl) ⟨1882080, by rfl⟩ : syracuseStep 5018881 = 3764161) B3764161
theorem B6691841 : Blo 1981435 6691841 := bstep (se 2 (by rfl) ⟨2509440, by rfl⟩ : syracuseStep 6691841 = 5018881) B5018881
theorem B4461227 : Blo 1981435 4461227 := bstep (se 1 (by rfl) ⟨3345920, by rfl⟩ : syracuseStep 4461227 = 6691841) B6691841
theorem B2974151 : Blo 1981435 2974151 := bstep (se 1 (by rfl) ⟨2230613, by rfl⟩ : syracuseStep 2974151 = 4461227) B4461227
theorem B1982767 : Blo 1981435 1982767 := bstep (se 1 (by rfl) ⟨1487075, by rfl⟩ : syracuseStep 1982767 = 2974151) B2974151
theorem B2974157 : Blo 1981435 2974157 := bbase (se 3 (by rfl) ⟨557654, by rfl⟩ : syracuseStep 2974157 = 1115309) (by norm_num)
theorem B1982771 : Blo 1981435 1982771 := bstep (se 1 (by rfl) ⟨1487078, by rfl⟩ : syracuseStep 1982771 = 2974157) B2974157
theorem B4461245 : Blo 1981435 4461245 := bbase (se 3 (by rfl) ⟨836483, by rfl⟩ : syracuseStep 4461245 = 1672967) (by norm_num)
theorem B2974163 : Blo 1981435 2974163 := bstep (se 1 (by rfl) ⟨2230622, by rfl⟩ : syracuseStep 2974163 = 4461245) B4461245
theorem B1982775 : Blo 1981435 1982775 := bstep (se 1 (by rfl) ⟨1487081, by rfl⟩ : syracuseStep 1982775 = 2974163) B2974163
theorem B3345941 : Blo 1981435 3345941 := bbase (se 6 (by rfl) ⟨78420, by rfl⟩ : syracuseStep 3345941 = 156841) (by norm_num)
theorem B2230627 : Blo 1981435 2230627 := bstep (se 1 (by rfl) ⟨1672970, by rfl⟩ : syracuseStep 2230627 = 3345941) B3345941
theorem B2974169 : Blo 1981435 2974169 := bstep (se 2 (by rfl) ⟨1115313, by rfl⟩ : syracuseStep 2974169 = 2230627) B2230627
theorem B1982779 : Blo 1981435 1982779 := bstep (se 1 (by rfl) ⟨1487084, by rfl⟩ : syracuseStep 1982779 = 2974169) B2974169
theorem B10719125 : Blo 1981435 10719125 := bbase (se 6 (by rfl) ⟨251229, by rfl⟩ : syracuseStep 10719125 = 502459) (by norm_num)
theorem B7146083 : Blo 1981435 7146083 := bstep (se 1 (by rfl) ⟨5359562, by rfl⟩ : syracuseStep 7146083 = 10719125) B10719125
theorem B19056221 : Blo 1981435 19056221 := bstep (se 3 (by rfl) ⟨3573041, by rfl⟩ : syracuseStep 19056221 = 7146083) B7146083
theorem B12704147 : Blo 1981435 12704147 := bstep (se 1 (by rfl) ⟨9528110, by rfl⟩ : syracuseStep 12704147 = 19056221) B19056221
theorem B8469431 : Blo 1981435 8469431 := bstep (se 1 (by rfl) ⟨6352073, by rfl⟩ : syracuseStep 8469431 = 12704147) B12704147
theorem B5646287 : Blo 1981435 5646287 := bstep (se 1 (by rfl) ⟨4234715, by rfl⟩ : syracuseStep 5646287 = 8469431) B8469431
theorem B15056765 : Blo 1981435 15056765 := bstep (se 3 (by rfl) ⟨2823143, by rfl⟩ : syracuseStep 15056765 = 5646287) B5646287
theorem B10037843 : Blo 1981435 10037843 := bstep (se 1 (by rfl) ⟨7528382, by rfl⟩ : syracuseStep 10037843 = 15056765) B15056765
theorem B6691895 : Blo 1981435 6691895 := bstep (se 1 (by rfl) ⟨5018921, by rfl⟩ : syracuseStep 6691895 = 10037843) B10037843
theorem B4461263 : Blo 1981435 4461263 := bstep (se 1 (by rfl) ⟨3345947, by rfl⟩ : syracuseStep 4461263 = 6691895) B6691895
theorem B2974175 : Blo 1981435 2974175 := bstep (se 1 (by rfl) ⟨2230631, by rfl⟩ : syracuseStep 2974175 = 4461263) B4461263
theorem B1982783 : Blo 1981435 1982783 := bstep (se 1 (by rfl) ⟨1487087, by rfl⟩ : syracuseStep 1982783 = 2974175) B2974175
theorem B2974181 : Blo 1981435 2974181 := bbase (se 4 (by rfl) ⟨278829, by rfl⟩ : syracuseStep 2974181 = 557659) (by norm_num)
theorem B1982787 : Blo 1981435 1982787 := bstep (se 1 (by rfl) ⟨1487090, by rfl⟩ : syracuseStep 1982787 = 2974181) B2974181
theorem B14684885 : Blo 1981435 14684885 := bbase (se 7 (by rfl) ⟨172088, by rfl⟩ : syracuseStep 14684885 = 344177) (by norm_num)
theorem B9789923 : Blo 1981435 9789923 := bstep (se 1 (by rfl) ⟨7342442, by rfl⟩ : syracuseStep 9789923 = 14684885) B14684885
theorem B26106461 : Blo 1981435 26106461 := bstep (se 3 (by rfl) ⟨4894961, by rfl⟩ : syracuseStep 26106461 = 9789923) B9789923
theorem B17404307 : Blo 1981435 17404307 := bstep (se 1 (by rfl) ⟨13053230, by rfl⟩ : syracuseStep 17404307 = 26106461) B26106461
theorem B11602871 : Blo 1981435 11602871 := bstep (se 1 (by rfl) ⟨8702153, by rfl⟩ : syracuseStep 11602871 = 17404307) B17404307
theorem B7735247 : Blo 1981435 7735247 := bstep (se 1 (by rfl) ⟨5801435, by rfl⟩ : syracuseStep 7735247 = 11602871) B11602871
theorem B5156831 : Blo 1981435 5156831 := bstep (se 1 (by rfl) ⟨3867623, by rfl⟩ : syracuseStep 5156831 = 7735247) B7735247
theorem B13751549 : Blo 1981435 13751549 := bstep (se 3 (by rfl) ⟨2578415, by rfl⟩ : syracuseStep 13751549 = 5156831) B5156831
theorem B9167699 : Blo 1981435 9167699 := bstep (se 1 (by rfl) ⟨6875774, by rfl⟩ : syracuseStep 9167699 = 13751549) B13751549
theorem B24447197 : Blo 1981435 24447197 := bstep (se 3 (by rfl) ⟨4583849, by rfl⟩ : syracuseStep 24447197 = 9167699) B9167699
theorem B65192525 : Blo 1981435 65192525 := bstep (se 3 (by rfl) ⟨12223598, by rfl⟩ : syracuseStep 65192525 = 24447197) B24447197
theorem B43461683 : Blo 1981435 43461683 := bstep (se 1 (by rfl) ⟨32596262, by rfl⟩ : syracuseStep 43461683 = 65192525) B65192525
theorem B28974455 : Blo 1981435 28974455 := bstep (se 1 (by rfl) ⟨21730841, by rfl⟩ : syracuseStep 28974455 = 43461683) B43461683
theorem B19316303 : Blo 1981435 19316303 := bstep (se 1 (by rfl) ⟨14487227, by rfl⟩ : syracuseStep 19316303 = 28974455) B28974455
theorem B12877535 : Blo 1981435 12877535 := bstep (se 1 (by rfl) ⟨9658151, by rfl⟩ : syracuseStep 12877535 = 19316303) B19316303
theorem B8585023 : Blo 1981435 8585023 := bstep (se 1 (by rfl) ⟨6438767, by rfl⟩ : syracuseStep 8585023 = 12877535) B12877535
theorem B11446697 : Blo 1981435 11446697 := bstep (se 2 (by rfl) ⟨4292511, by rfl⟩ : syracuseStep 11446697 = 8585023) B8585023
theorem B7631131 : Blo 1981435 7631131 := bstep (se 1 (by rfl) ⟨5723348, by rfl⟩ : syracuseStep 7631131 = 11446697) B11446697
theorem B10174841 : Blo 1981435 10174841 := bstep (se 2 (by rfl) ⟨3815565, by rfl⟩ : syracuseStep 10174841 = 7631131) B7631131
theorem B6783227 : Blo 1981435 6783227 := bstep (se 1 (by rfl) ⟨5087420, by rfl⟩ : syracuseStep 6783227 = 10174841) B10174841
theorem B4522151 : Blo 1981435 4522151 := bstep (se 1 (by rfl) ⟨3391613, by rfl⟩ : syracuseStep 4522151 = 6783227) B6783227
theorem B3014767 : Blo 1981435 3014767 := bstep (se 1 (by rfl) ⟨2261075, by rfl⟩ : syracuseStep 3014767 = 4522151) B4522151
theorem B4019689 : Blo 1981435 4019689 := bstep (se 2 (by rfl) ⟨1507383, by rfl⟩ : syracuseStep 4019689 = 3014767) B3014767
theorem B21438341 : Blo 1981435 21438341 := bstep (se 4 (by rfl) ⟨2009844, by rfl⟩ : syracuseStep 21438341 = 4019689) B4019689
theorem B14292227 : Blo 1981435 14292227 := bstep (se 1 (by rfl) ⟨10719170, by rfl⟩ : syracuseStep 14292227 = 21438341) B21438341
theorem B9528151 : Blo 1981435 9528151 := bstep (se 1 (by rfl) ⟨7146113, by rfl⟩ : syracuseStep 9528151 = 14292227) B14292227
theorem B12704201 : Blo 1981435 12704201 := bstep (se 2 (by rfl) ⟨4764075, by rfl⟩ : syracuseStep 12704201 = 9528151) B9528151
theorem B8469467 : Blo 1981435 8469467 := bstep (se 1 (by rfl) ⟨6352100, by rfl⟩ : syracuseStep 8469467 = 12704201) B12704201
theorem B5646311 : Blo 1981435 5646311 := bstep (se 1 (by rfl) ⟨4234733, by rfl⟩ : syracuseStep 5646311 = 8469467) B8469467
theorem B3764207 : Blo 1981435 3764207 := bstep (se 1 (by rfl) ⟨2823155, by rfl⟩ : syracuseStep 3764207 = 5646311) B5646311
theorem B2509471 : Blo 1981435 2509471 := bstep (se 1 (by rfl) ⟨1882103, by rfl⟩ : syracuseStep 2509471 = 3764207) B3764207
theorem B3345961 : Blo 1981435 3345961 := bstep (se 2 (by rfl) ⟨1254735, by rfl⟩ : syracuseStep 3345961 = 2509471) B2509471
theorem B4461281 : Blo 1981435 4461281 := bstep (se 2 (by rfl) ⟨1672980, by rfl⟩ : syracuseStep 4461281 = 3345961) B3345961
theorem B2974187 : Blo 1981435 2974187 := bstep (se 1 (by rfl) ⟨2230640, by rfl⟩ : syracuseStep 2974187 = 4461281) B4461281
theorem B1982791 : Blo 1981435 1982791 := bstep (se 1 (by rfl) ⟨1487093, by rfl⟩ : syracuseStep 1982791 = 2974187) B2974187
theorem B2230645 : Blo 1981435 2230645 := bbase (se 5 (by rfl) ⟨104561, by rfl⟩ : syracuseStep 2230645 = 209123) (by norm_num)
theorem B2974193 : Blo 1981435 2974193 := bstep (se 2 (by rfl) ⟨1115322, by rfl⟩ : syracuseStep 2974193 = 2230645) B2230645
theorem B1982795 : Blo 1981435 1982795 := bstep (se 1 (by rfl) ⟨1487096, by rfl⟩ : syracuseStep 1982795 = 2974193) B2974193
theorem B2509481 : Blo 1981435 2509481 := bbase (se 2 (by rfl) ⟨941055, by rfl⟩ : syracuseStep 2509481 = 1882111) (by norm_num)
theorem B6691949 : Blo 1981435 6691949 := bstep (se 3 (by rfl) ⟨1254740, by rfl⟩ : syracuseStep 6691949 = 2509481) B2509481
theorem B4461299 : Blo 1981435 4461299 := bstep (se 1 (by rfl) ⟨3345974, by rfl⟩ : syracuseStep 4461299 = 6691949) B6691949
theorem B2974199 : Blo 1981435 2974199 := bstep (se 1 (by rfl) ⟨2230649, by rfl⟩ : syracuseStep 2974199 = 4461299) B4461299
theorem B1982799 : Blo 1981435 1982799 := bstep (se 1 (by rfl) ⟨1487099, by rfl⟩ : syracuseStep 1982799 = 2974199) B2974199
theorem B2974205 : Blo 1981435 2974205 := bbase (se 3 (by rfl) ⟨557663, by rfl⟩ : syracuseStep 2974205 = 1115327) (by norm_num)
theorem B1982803 : Blo 1981435 1982803 := bstep (se 1 (by rfl) ⟨1487102, by rfl⟩ : syracuseStep 1982803 = 2974205) B2974205
theorem B4461317 : Blo 1981435 4461317 := bbase (se 4 (by rfl) ⟨418248, by rfl⟩ : syracuseStep 4461317 = 836497) (by norm_num)
theorem B2974211 : Blo 1981435 2974211 := bstep (se 1 (by rfl) ⟨2230658, by rfl⟩ : syracuseStep 2974211 = 4461317) B4461317
theorem B1982807 : Blo 1981435 1982807 := bstep (se 1 (by rfl) ⟨1487105, by rfl⟩ : syracuseStep 1982807 = 2974211) B2974211
theorem B3764245 : Blo 1981435 3764245 := bbase (se 6 (by rfl) ⟨88224, by rfl⟩ : syracuseStep 3764245 = 176449) (by norm_num)
theorem B5018993 : Blo 1981435 5018993 := bstep (se 2 (by rfl) ⟨1882122, by rfl⟩ : syracuseStep 5018993 = 3764245) B3764245
theorem B3345995 : Blo 1981435 3345995 := bstep (se 1 (by rfl) ⟨2509496, by rfl⟩ : syracuseStep 3345995 = 5018993) B5018993
theorem B2230663 : Blo 1981435 2230663 := bstep (se 1 (by rfl) ⟨1672997, by rfl⟩ : syracuseStep 2230663 = 3345995) B3345995
theorem B2974217 : Blo 1981435 2974217 := bstep (se 2 (by rfl) ⟨1115331, by rfl⟩ : syracuseStep 2974217 = 2230663) B2230663
theorem B1982811 : Blo 1981435 1982811 := bstep (se 1 (by rfl) ⟨1487108, by rfl⟩ : syracuseStep 1982811 = 2974217) B2974217
theorem B10038005 : Blo 1981435 10038005 := bbase (se 5 (by rfl) ⟨470531, by rfl⟩ : syracuseStep 10038005 = 941063) (by norm_num)
theorem B6692003 : Blo 1981435 6692003 := bstep (se 1 (by rfl) ⟨5019002, by rfl⟩ : syracuseStep 6692003 = 10038005) B10038005
theorem B4461335 : Blo 1981435 4461335 := bstep (se 1 (by rfl) ⟨3346001, by rfl⟩ : syracuseStep 4461335 = 6692003) B6692003
theorem B2974223 : Blo 1981435 2974223 := bstep (se 1 (by rfl) ⟨2230667, by rfl⟩ : syracuseStep 2974223 = 4461335) B4461335
theorem B1982815 : Blo 1981435 1982815 := bstep (se 1 (by rfl) ⟨1487111, by rfl⟩ : syracuseStep 1982815 = 2974223) B2974223
theorem B2974229 : Blo 1981435 2974229 := bbase (se 6 (by rfl) ⟨69708, by rfl⟩ : syracuseStep 2974229 = 139417) (by norm_num)
theorem B1982819 : Blo 1981435 1982819 := bstep (se 1 (by rfl) ⟨1487114, by rfl⟩ : syracuseStep 1982819 = 2974229) B2974229
theorem B3176101 : Blo 1981435 3176101 := bbase (se 4 (by rfl) ⟨297759, by rfl⟩ : syracuseStep 3176101 = 595519) (by norm_num)
theorem B16939205 : Blo 1981435 16939205 := bstep (se 4 (by rfl) ⟨1588050, by rfl⟩ : syracuseStep 16939205 = 3176101) B3176101
theorem B11292803 : Blo 1981435 11292803 := bstep (se 1 (by rfl) ⟨8469602, by rfl⟩ : syracuseStep 11292803 = 16939205) B16939205
theorem B7528535 : Blo 1981435 7528535 := bstep (se 1 (by rfl) ⟨5646401, by rfl⟩ : syracuseStep 7528535 = 11292803) B11292803
theorem B5019023 : Blo 1981435 5019023 := bstep (se 1 (by rfl) ⟨3764267, by rfl⟩ : syracuseStep 5019023 = 7528535) B7528535
theorem B3346015 : Blo 1981435 3346015 := bstep (se 1 (by rfl) ⟨2509511, by rfl⟩ : syracuseStep 3346015 = 5019023) B5019023
theorem B4461353 : Blo 1981435 4461353 := bstep (se 2 (by rfl) ⟨1673007, by rfl⟩ : syracuseStep 4461353 = 3346015) B3346015
theorem B2974235 : Blo 1981435 2974235 := bstep (se 1 (by rfl) ⟨2230676, by rfl⟩ : syracuseStep 2974235 = 4461353) B4461353
theorem B1982823 : Blo 1981435 1982823 := bstep (se 1 (by rfl) ⟨1487117, by rfl⟩ : syracuseStep 1982823 = 2974235) B2974235
theorem B2230681 : Blo 1981435 2230681 := bbase (se 2 (by rfl) ⟨836505, by rfl⟩ : syracuseStep 2230681 = 1673011) (by norm_num)
theorem B2974241 : Blo 1981435 2974241 := bstep (se 2 (by rfl) ⟨1115340, by rfl⟩ : syracuseStep 2974241 = 2230681) B2230681
theorem B1982827 : Blo 1981435 1982827 := bstep (se 1 (by rfl) ⟨1487120, by rfl⟩ : syracuseStep 1982827 = 2974241) B2974241
theorem B7528565 : Blo 1981435 7528565 := bbase (se 5 (by rfl) ⟨352901, by rfl⟩ : syracuseStep 7528565 = 705803) (by norm_num)
theorem B5019043 : Blo 1981435 5019043 := bstep (se 1 (by rfl) ⟨3764282, by rfl⟩ : syracuseStep 5019043 = 7528565) B7528565
theorem B6692057 : Blo 1981435 6692057 := bstep (se 2 (by rfl) ⟨2509521, by rfl⟩ : syracuseStep 6692057 = 5019043) B5019043
theorem B4461371 : Blo 1981435 4461371 := bstep (se 1 (by rfl) ⟨3346028, by rfl⟩ : syracuseStep 4461371 = 6692057) B6692057
theorem B2974247 : Blo 1981435 2974247 := bstep (se 1 (by rfl) ⟨2230685, by rfl⟩ : syracuseStep 2974247 = 4461371) B4461371
theorem B1982831 : Blo 1981435 1982831 := bstep (se 1 (by rfl) ⟨1487123, by rfl⟩ : syracuseStep 1982831 = 2974247) B2974247
theorem B2974253 : Blo 1981435 2974253 := bbase (se 3 (by rfl) ⟨557672, by rfl⟩ : syracuseStep 2974253 = 1115345) (by norm_num)
theorem B1982835 : Blo 1981435 1982835 := bstep (se 1 (by rfl) ⟨1487126, by rfl⟩ : syracuseStep 1982835 = 2974253) B2974253
theorem B4461389 : Blo 1981435 4461389 := bbase (se 3 (by rfl) ⟨836510, by rfl⟩ : syracuseStep 4461389 = 1673021) (by norm_num)
theorem B2974259 : Blo 1981435 2974259 := bstep (se 1 (by rfl) ⟨2230694, by rfl⟩ : syracuseStep 2974259 = 4461389) B4461389
theorem B1982839 : Blo 1981435 1982839 := bstep (se 1 (by rfl) ⟨1487129, by rfl⟩ : syracuseStep 1982839 = 2974259) B2974259
theorem B2509537 : Blo 1981435 2509537 := bbase (se 2 (by rfl) ⟨941076, by rfl⟩ : syracuseStep 2509537 = 1882153) (by norm_num)
theorem B3346049 : Blo 1981435 3346049 := bstep (se 2 (by rfl) ⟨1254768, by rfl⟩ : syracuseStep 3346049 = 2509537) B2509537
theorem B2230699 : Blo 1981435 2230699 := bstep (se 1 (by rfl) ⟨1673024, by rfl⟩ : syracuseStep 2230699 = 3346049) B3346049
theorem B2974265 : Blo 1981435 2974265 := bstep (se 2 (by rfl) ⟨1115349, by rfl⟩ : syracuseStep 2974265 = 2230699) B2230699
theorem B1982843 : Blo 1981435 1982843 := bstep (se 1 (by rfl) ⟨1487132, by rfl⟩ : syracuseStep 1982843 = 2974265) B2974265
theorem B22585877 : Blo 1981435 22585877 := bbase (se 6 (by rfl) ⟨529356, by rfl⟩ : syracuseStep 22585877 = 1058713) (by norm_num)
theorem B15057251 : Blo 1981435 15057251 := bstep (se 1 (by rfl) ⟨11292938, by rfl⟩ : syracuseStep 15057251 = 22585877) B22585877
theorem B10038167 : Blo 1981435 10038167 := bstep (se 1 (by rfl) ⟨7528625, by rfl⟩ : syracuseStep 10038167 = 15057251) B15057251
theorem B6692111 : Blo 1981435 6692111 := bstep (se 1 (by rfl) ⟨5019083, by rfl⟩ : syracuseStep 6692111 = 10038167) B10038167
theorem B4461407 : Blo 1981435 4461407 := bstep (se 1 (by rfl) ⟨3346055, by rfl⟩ : syracuseStep 4461407 = 6692111) B6692111
theorem B2974271 : Blo 1981435 2974271 := bstep (se 1 (by rfl) ⟨2230703, by rfl⟩ : syracuseStep 2974271 = 4461407) B4461407
theorem B1982847 : Blo 1981435 1982847 := bstep (se 1 (by rfl) ⟨1487135, by rfl⟩ : syracuseStep 1982847 = 2974271) B2974271
theorem B2974277 : Blo 1981435 2974277 := bbase (se 4 (by rfl) ⟨278838, by rfl⟩ : syracuseStep 2974277 = 557677) (by norm_num)
theorem B1982851 : Blo 1981435 1982851 := bstep (se 1 (by rfl) ⟨1487138, by rfl⟩ : syracuseStep 1982851 = 2974277) B2974277
theorem B3346069 : Blo 1981435 3346069 := bbase (se 6 (by rfl) ⟨78423, by rfl⟩ : syracuseStep 3346069 = 156847) (by norm_num)
theorem B4461425 : Blo 1981435 4461425 := bstep (se 2 (by rfl) ⟨1673034, by rfl⟩ : syracuseStep 4461425 = 3346069) B3346069
theorem B2974283 : Blo 1981435 2974283 := bstep (se 1 (by rfl) ⟨2230712, by rfl⟩ : syracuseStep 2974283 = 4461425) B4461425
theorem B1982855 : Blo 1981435 1982855 := bstep (se 1 (by rfl) ⟨1487141, by rfl⟩ : syracuseStep 1982855 = 2974283) B2974283
theorem B2230717 : Blo 1981435 2230717 := bbase (se 3 (by rfl) ⟨418259, by rfl⟩ : syracuseStep 2230717 = 836519) (by norm_num)
theorem B2974289 : Blo 1981435 2974289 := bstep (se 2 (by rfl) ⟨1115358, by rfl⟩ : syracuseStep 2974289 = 2230717) B2230717
theorem B1982859 : Blo 1981435 1982859 := bstep (se 1 (by rfl) ⟨1487144, by rfl⟩ : syracuseStep 1982859 = 2974289) B2974289
theorem B6692165 : Blo 1981435 6692165 := bbase (se 4 (by rfl) ⟨627390, by rfl⟩ : syracuseStep 6692165 = 1254781) (by norm_num)
theorem B4461443 : Blo 1981435 4461443 := bstep (se 1 (by rfl) ⟨3346082, by rfl⟩ : syracuseStep 4461443 = 6692165) B6692165
theorem B2974295 : Blo 1981435 2974295 := bstep (se 1 (by rfl) ⟨2230721, by rfl⟩ : syracuseStep 2974295 = 4461443) B4461443
theorem B1982863 : Blo 1981435 1982863 := bstep (se 1 (by rfl) ⟨1487147, by rfl⟩ : syracuseStep 1982863 = 2974295) B2974295
theorem B2974301 : Blo 1981435 2974301 := bbase (se 3 (by rfl) ⟨557681, by rfl⟩ : syracuseStep 2974301 = 1115363) (by norm_num)
theorem B1982867 : Blo 1981435 1982867 := bstep (se 1 (by rfl) ⟨1487150, by rfl⟩ : syracuseStep 1982867 = 2974301) B2974301
theorem B4461461 : Blo 1981435 4461461 := bbase (se 6 (by rfl) ⟨104565, by rfl⟩ : syracuseStep 4461461 = 209131) (by norm_num)
theorem B2974307 : Blo 1981435 2974307 := bstep (se 1 (by rfl) ⟨2230730, by rfl⟩ : syracuseStep 2974307 = 4461461) B4461461
theorem B1982871 : Blo 1981435 1982871 := bstep (se 1 (by rfl) ⟨1487153, by rfl⟩ : syracuseStep 1982871 = 2974307) B2974307
theorem B4019861 : Blo 1981435 4019861 := bbase (se 6 (by rfl) ⟨94215, by rfl⟩ : syracuseStep 4019861 = 188431) (by norm_num)
theorem B2679907 : Blo 1981435 2679907 := bstep (se 1 (by rfl) ⟨2009930, by rfl⟩ : syracuseStep 2679907 = 4019861) B4019861
theorem B3573209 : Blo 1981435 3573209 := bstep (se 2 (by rfl) ⟨1339953, by rfl⟩ : syracuseStep 3573209 = 2679907) B2679907
theorem B2382139 : Blo 1981435 2382139 := bstep (se 1 (by rfl) ⟨1786604, by rfl⟩ : syracuseStep 2382139 = 3573209) B3573209
theorem B3176185 : Blo 1981435 3176185 := bstep (se 2 (by rfl) ⟨1191069, by rfl⟩ : syracuseStep 3176185 = 2382139) B2382139
theorem B4234913 : Blo 1981435 4234913 := bstep (se 2 (by rfl) ⟨1588092, by rfl⟩ : syracuseStep 4234913 = 3176185) B3176185
theorem B2823275 : Blo 1981435 2823275 := bstep (se 1 (by rfl) ⟨2117456, by rfl⟩ : syracuseStep 2823275 = 4234913) B4234913
theorem B7528733 : Blo 1981435 7528733 := bstep (se 3 (by rfl) ⟨1411637, by rfl⟩ : syracuseStep 7528733 = 2823275) B2823275
theorem B5019155 : Blo 1981435 5019155 := bstep (se 1 (by rfl) ⟨3764366, by rfl⟩ : syracuseStep 5019155 = 7528733) B7528733
theorem B3346103 : Blo 1981435 3346103 := bstep (se 1 (by rfl) ⟨2509577, by rfl⟩ : syracuseStep 3346103 = 5019155) B5019155
theorem B2230735 : Blo 1981435 2230735 := bstep (se 1 (by rfl) ⟨1673051, by rfl⟩ : syracuseStep 2230735 = 3346103) B3346103
theorem B2974313 : Blo 1981435 2974313 := bstep (se 2 (by rfl) ⟨1115367, by rfl⟩ : syracuseStep 2974313 = 2230735) B2230735
theorem B1982875 : Blo 1981435 1982875 := bstep (se 1 (by rfl) ⟨1487156, by rfl⟩ : syracuseStep 1982875 = 2974313) B2974313
theorem B17170805 : Blo 1981435 17170805 := bbase (se 5 (by rfl) ⟨804881, by rfl⟩ : syracuseStep 17170805 = 1609763) (by norm_num)
theorem B11447203 : Blo 1981435 11447203 := bstep (se 1 (by rfl) ⟨8585402, by rfl⟩ : syracuseStep 11447203 = 17170805) B17170805
theorem B15262937 : Blo 1981435 15262937 := bstep (se 2 (by rfl) ⟨5723601, by rfl⟩ : syracuseStep 15262937 = 11447203) B11447203
theorem B10175291 : Blo 1981435 10175291 := bstep (se 1 (by rfl) ⟨7631468, by rfl⟩ : syracuseStep 10175291 = 15262937) B15262937
theorem B6783527 : Blo 1981435 6783527 := bstep (se 1 (by rfl) ⟨5087645, by rfl⟩ : syracuseStep 6783527 = 10175291) B10175291
theorem B18089405 : Blo 1981435 18089405 := bstep (se 3 (by rfl) ⟨3391763, by rfl⟩ : syracuseStep 18089405 = 6783527) B6783527
theorem B12059603 : Blo 1981435 12059603 := bstep (se 1 (by rfl) ⟨9044702, by rfl⟩ : syracuseStep 12059603 = 18089405) B18089405
theorem B8039735 : Blo 1981435 8039735 := bstep (se 1 (by rfl) ⟨6029801, by rfl⟩ : syracuseStep 8039735 = 12059603) B12059603
theorem B5359823 : Blo 1981435 5359823 := bstep (se 1 (by rfl) ⟨4019867, by rfl⟩ : syracuseStep 5359823 = 8039735) B8039735
theorem B3573215 : Blo 1981435 3573215 := bstep (se 1 (by rfl) ⟨2679911, by rfl⟩ : syracuseStep 3573215 = 5359823) B5359823
theorem B2382143 : Blo 1981435 2382143 := bstep (se 1 (by rfl) ⟨1786607, by rfl⟩ : syracuseStep 2382143 = 3573215) B3573215
theorem B6352381 : Blo 1981435 6352381 := bstep (se 3 (by rfl) ⟨1191071, by rfl⟩ : syracuseStep 6352381 = 2382143) B2382143
theorem B8469841 : Blo 1981435 8469841 := bstep (se 2 (by rfl) ⟨3176190, by rfl⟩ : syracuseStep 8469841 = 6352381) B6352381
theorem B11293121 : Blo 1981435 11293121 := bstep (se 2 (by rfl) ⟨4234920, by rfl⟩ : syracuseStep 11293121 = 8469841) B8469841
theorem B7528747 : Blo 1981435 7528747 := bstep (se 1 (by rfl) ⟨5646560, by rfl⟩ : syracuseStep 7528747 = 11293121) B11293121
theorem B10038329 : Blo 1981435 10038329 := bstep (se 2 (by rfl) ⟨3764373, by rfl⟩ : syracuseStep 10038329 = 7528747) B7528747
theorem B6692219 : Blo 1981435 6692219 := bstep (se 1 (by rfl) ⟨5019164, by rfl⟩ : syracuseStep 6692219 = 10038329) B10038329
theorem B4461479 : Blo 1981435 4461479 := bstep (se 1 (by rfl) ⟨3346109, by rfl⟩ : syracuseStep 4461479 = 6692219) B6692219
theorem B2974319 : Blo 1981435 2974319 := bstep (se 1 (by rfl) ⟨2230739, by rfl⟩ : syracuseStep 2974319 = 4461479) B4461479
theorem B1982879 : Blo 1981435 1982879 := bstep (se 1 (by rfl) ⟨1487159, by rfl⟩ : syracuseStep 1982879 = 2974319) B2974319
theorem B2974325 : Blo 1981435 2974325 := bbase (se 5 (by rfl) ⟨139421, by rfl⟩ : syracuseStep 2974325 = 278843) (by norm_num)
theorem B1982883 : Blo 1981435 1982883 := bstep (se 1 (by rfl) ⟨1487162, by rfl⟩ : syracuseStep 1982883 = 2974325) B2974325
theorem B3764389 : Blo 1981435 3764389 := bbase (se 4 (by rfl) ⟨352911, by rfl⟩ : syracuseStep 3764389 = 705823) (by norm_num)
theorem B5019185 : Blo 1981435 5019185 := bstep (se 2 (by rfl) ⟨1882194, by rfl⟩ : syracuseStep 5019185 = 3764389) B3764389
theorem B3346123 : Blo 1981435 3346123 := bstep (se 1 (by rfl) ⟨2509592, by rfl⟩ : syracuseStep 3346123 = 5019185) B5019185
theorem B4461497 : Blo 1981435 4461497 := bstep (se 2 (by rfl) ⟨1673061, by rfl⟩ : syracuseStep 4461497 = 3346123) B3346123
theorem B2974331 : Blo 1981435 2974331 := bstep (se 1 (by rfl) ⟨2230748, by rfl⟩ : syracuseStep 2974331 = 4461497) B4461497
theorem B1982887 : Blo 1981435 1982887 := bstep (se 1 (by rfl) ⟨1487165, by rfl⟩ : syracuseStep 1982887 = 2974331) B2974331
theorem B2230753 : Blo 1981435 2230753 := bbase (se 2 (by rfl) ⟨836532, by rfl⟩ : syracuseStep 2230753 = 1673065) (by norm_num)
theorem B2974337 : Blo 1981435 2974337 := bstep (se 2 (by rfl) ⟨1115376, by rfl⟩ : syracuseStep 2974337 = 2230753) B2230753
theorem B1982891 : Blo 1981435 1982891 := bstep (se 1 (by rfl) ⟨1487168, by rfl⟩ : syracuseStep 1982891 = 2974337) B2974337
theorem B5019205 : Blo 1981435 5019205 := bbase (se 4 (by rfl) ⟨470550, by rfl⟩ : syracuseStep 5019205 = 941101) (by norm_num)
theorem B6692273 : Blo 1981435 6692273 := bstep (se 2 (by rfl) ⟨2509602, by rfl⟩ : syracuseStep 6692273 = 5019205) B5019205
theorem B4461515 : Blo 1981435 4461515 := bstep (se 1 (by rfl) ⟨3346136, by rfl⟩ : syracuseStep 4461515 = 6692273) B6692273
theorem B2974343 : Blo 1981435 2974343 := bstep (se 1 (by rfl) ⟨2230757, by rfl⟩ : syracuseStep 2974343 = 4461515) B4461515
theorem B1982895 : Blo 1981435 1982895 := bstep (se 1 (by rfl) ⟨1487171, by rfl⟩ : syracuseStep 1982895 = 2974343) B2974343
theorem B2974349 : Blo 1981435 2974349 := bbase (se 3 (by rfl) ⟨557690, by rfl⟩ : syracuseStep 2974349 = 1115381) (by norm_num)
theorem B1982899 : Blo 1981435 1982899 := bstep (se 1 (by rfl) ⟨1487174, by rfl⟩ : syracuseStep 1982899 = 2974349) B2974349
theorem B4461533 : Blo 1981435 4461533 := bbase (se 3 (by rfl) ⟨836537, by rfl⟩ : syracuseStep 4461533 = 1673075) (by norm_num)
theorem B2974355 : Blo 1981435 2974355 := bstep (se 1 (by rfl) ⟨2230766, by rfl⟩ : syracuseStep 2974355 = 4461533) B4461533
theorem B1982903 : Blo 1981435 1982903 := bstep (se 1 (by rfl) ⟨1487177, by rfl⟩ : syracuseStep 1982903 = 2974355) B2974355
theorem B3346157 : Blo 1981435 3346157 := bbase (se 3 (by rfl) ⟨627404, by rfl⟩ : syracuseStep 3346157 = 1254809) (by norm_num)
theorem B2230771 : Blo 1981435 2230771 := bstep (se 1 (by rfl) ⟨1673078, by rfl⟩ : syracuseStep 2230771 = 3346157) B3346157
theorem B2974361 : Blo 1981435 2974361 := bstep (se 2 (by rfl) ⟨1115385, by rfl⟩ : syracuseStep 2974361 = 2230771) B2230771
theorem B1982907 : Blo 1981435 1982907 := bstep (se 1 (by rfl) ⟨1487180, by rfl⟩ : syracuseStep 1982907 = 2974361) B2974361
theorem B9528725 : Blo 1981435 9528725 := bbase (se 6 (by rfl) ⟨223329, by rfl⟩ : syracuseStep 9528725 = 446659) (by norm_num)
theorem B25409933 : Blo 1981435 25409933 := bstep (se 3 (by rfl) ⟨4764362, by rfl⟩ : syracuseStep 25409933 = 9528725) B9528725
theorem B16939955 : Blo 1981435 16939955 := bstep (se 1 (by rfl) ⟨12704966, by rfl⟩ : syracuseStep 16939955 = 25409933) B25409933
theorem B11293303 : Blo 1981435 11293303 := bstep (se 1 (by rfl) ⟨8469977, by rfl⟩ : syracuseStep 11293303 = 16939955) B16939955
theorem B15057737 : Blo 1981435 15057737 := bstep (se 2 (by rfl) ⟨5646651, by rfl⟩ : syracuseStep 15057737 = 11293303) B11293303
theorem B10038491 : Blo 1981435 10038491 := bstep (se 1 (by rfl) ⟨7528868, by rfl⟩ : syracuseStep 10038491 = 15057737) B15057737
theorem B6692327 : Blo 1981435 6692327 := bstep (se 1 (by rfl) ⟨5019245, by rfl⟩ : syracuseStep 6692327 = 10038491) B10038491
theorem B4461551 : Blo 1981435 4461551 := bstep (se 1 (by rfl) ⟨3346163, by rfl⟩ : syracuseStep 4461551 = 6692327) B6692327
theorem B2974367 : Blo 1981435 2974367 := bstep (se 1 (by rfl) ⟨2230775, by rfl⟩ : syracuseStep 2974367 = 4461551) B4461551
theorem B1982911 : Blo 1981435 1982911 := bstep (se 1 (by rfl) ⟨1487183, by rfl⟩ : syracuseStep 1982911 = 2974367) B2974367
theorem B2974373 : Blo 1981435 2974373 := bbase (se 4 (by rfl) ⟨278847, by rfl⟩ : syracuseStep 2974373 = 557695) (by norm_num)
theorem B1982915 : Blo 1981435 1982915 := bstep (se 1 (by rfl) ⟨1487186, by rfl⟩ : syracuseStep 1982915 = 2974373) B2974373
theorem B2509633 : Blo 1981435 2509633 := bbase (se 2 (by rfl) ⟨941112, by rfl⟩ : syracuseStep 2509633 = 1882225) (by norm_num)
theorem B3346177 : Blo 1981435 3346177 := bstep (se 2 (by rfl) ⟨1254816, by rfl⟩ : syracuseStep 3346177 = 2509633) B2509633
theorem B4461569 : Blo 1981435 4461569 := bstep (se 2 (by rfl) ⟨1673088, by rfl⟩ : syracuseStep 4461569 = 3346177) B3346177
theorem B2974379 : Blo 1981435 2974379 := bstep (se 1 (by rfl) ⟨2230784, by rfl⟩ : syracuseStep 2974379 = 4461569) B4461569
theorem B1982919 : Blo 1981435 1982919 := bstep (se 1 (by rfl) ⟨1487189, by rfl⟩ : syracuseStep 1982919 = 2974379) B2974379
theorem B2230789 : Blo 1981435 2230789 := bbase (se 4 (by rfl) ⟨209136, by rfl⟩ : syracuseStep 2230789 = 418273) (by norm_num)
theorem B2974385 : Blo 1981435 2974385 := bstep (se 2 (by rfl) ⟨1115394, by rfl⟩ : syracuseStep 2974385 = 2230789) B2230789
theorem B1982923 : Blo 1981435 1982923 := bstep (se 1 (by rfl) ⟨1487192, by rfl⟩ : syracuseStep 1982923 = 2974385) B2974385
theorem B2823349 : Blo 1981435 2823349 := bbase (se 5 (by rfl) ⟨132344, by rfl⟩ : syracuseStep 2823349 = 264689) (by norm_num)
theorem B3764465 : Blo 1981435 3764465 := bstep (se 2 (by rfl) ⟨1411674, by rfl⟩ : syracuseStep 3764465 = 2823349) B2823349
theorem B2509643 : Blo 1981435 2509643 := bstep (se 1 (by rfl) ⟨1882232, by rfl⟩ : syracuseStep 2509643 = 3764465) B3764465
theorem B6692381 : Blo 1981435 6692381 := bstep (se 3 (by rfl) ⟨1254821, by rfl⟩ : syracuseStep 6692381 = 2509643) B2509643
theorem B4461587 : Blo 1981435 4461587 := bstep (se 1 (by rfl) ⟨3346190, by rfl⟩ : syracuseStep 4461587 = 6692381) B6692381
theorem B2974391 : Blo 1981435 2974391 := bstep (se 1 (by rfl) ⟨2230793, by rfl⟩ : syracuseStep 2974391 = 4461587) B4461587
theorem B1982927 : Blo 1981435 1982927 := bstep (se 1 (by rfl) ⟨1487195, by rfl⟩ : syracuseStep 1982927 = 2974391) B2974391
theorem B2974397 : Blo 1981435 2974397 := bbase (se 3 (by rfl) ⟨557699, by rfl⟩ : syracuseStep 2974397 = 1115399) (by norm_num)
theorem B1982931 : Blo 1981435 1982931 := bstep (se 1 (by rfl) ⟨1487198, by rfl⟩ : syracuseStep 1982931 = 2974397) B2974397
theorem B4461605 : Blo 1981435 4461605 := bbase (se 4 (by rfl) ⟨418275, by rfl⟩ : syracuseStep 4461605 = 836551) (by norm_num)
theorem B2974403 : Blo 1981435 2974403 := bstep (se 1 (by rfl) ⟨2230802, by rfl⟩ : syracuseStep 2974403 = 4461605) B4461605
theorem B1982935 : Blo 1981435 1982935 := bstep (se 1 (by rfl) ⟨1487201, by rfl⟩ : syracuseStep 1982935 = 2974403) B2974403
theorem B5019317 : Blo 1981435 5019317 := bbase (se 5 (by rfl) ⟨235280, by rfl⟩ : syracuseStep 5019317 = 470561) (by norm_num)
theorem B3346211 : Blo 1981435 3346211 := bstep (se 1 (by rfl) ⟨2509658, by rfl⟩ : syracuseStep 3346211 = 5019317) B5019317
theorem B2230807 : Blo 1981435 2230807 := bstep (se 1 (by rfl) ⟨1673105, by rfl⟩ : syracuseStep 2230807 = 3346211) B3346211
theorem B2974409 : Blo 1981435 2974409 := bstep (se 2 (by rfl) ⟨1115403, by rfl⟩ : syracuseStep 2974409 = 2230807) B2230807
theorem B1982939 : Blo 1981435 1982939 := bstep (se 1 (by rfl) ⟨1487204, by rfl⟩ : syracuseStep 1982939 = 2974409) B2974409
theorem B12705173 : Blo 1981435 12705173 := bbase (se 6 (by rfl) ⟨297777, by rfl⟩ : syracuseStep 12705173 = 595555) (by norm_num)
theorem B8470115 : Blo 1981435 8470115 := bstep (se 1 (by rfl) ⟨6352586, by rfl⟩ : syracuseStep 8470115 = 12705173) B12705173
theorem B5646743 : Blo 1981435 5646743 := bstep (se 1 (by rfl) ⟨4235057, by rfl⟩ : syracuseStep 5646743 = 8470115) B8470115
theorem B3764495 : Blo 1981435 3764495 := bstep (se 1 (by rfl) ⟨2823371, by rfl⟩ : syracuseStep 3764495 = 5646743) B5646743
theorem B10038653 : Blo 1981435 10038653 := bstep (se 3 (by rfl) ⟨1882247, by rfl⟩ : syracuseStep 10038653 = 3764495) B3764495
theorem B6692435 : Blo 1981435 6692435 := bstep (se 1 (by rfl) ⟨5019326, by rfl⟩ : syracuseStep 6692435 = 10038653) B10038653
theorem B4461623 : Blo 1981435 4461623 := bstep (se 1 (by rfl) ⟨3346217, by rfl⟩ : syracuseStep 4461623 = 6692435) B6692435
theorem B2974415 : Blo 1981435 2974415 := bstep (se 1 (by rfl) ⟨2230811, by rfl⟩ : syracuseStep 2974415 = 4461623) B4461623
theorem B1982943 : Blo 1981435 1982943 := bstep (se 1 (by rfl) ⟨1487207, by rfl⟩ : syracuseStep 1982943 = 2974415) B2974415
theorem B2974421 : Blo 1981435 2974421 := bbase (se 7 (by rfl) ⟨34856, by rfl⟩ : syracuseStep 2974421 = 69713) (by norm_num)
theorem B1982947 : Blo 1981435 1982947 := bstep (se 1 (by rfl) ⟨1487210, by rfl⟩ : syracuseStep 1982947 = 2974421) B2974421
theorem B6352613 : Blo 1981435 6352613 := bbase (se 4 (by rfl) ⟨595557, by rfl⟩ : syracuseStep 6352613 = 1191115) (by norm_num)
theorem B4235075 : Blo 1981435 4235075 := bstep (se 1 (by rfl) ⟨3176306, by rfl⟩ : syracuseStep 4235075 = 6352613) B6352613
theorem B2823383 : Blo 1981435 2823383 := bstep (se 1 (by rfl) ⟨2117537, by rfl⟩ : syracuseStep 2823383 = 4235075) B4235075
theorem B7529021 : Blo 1981435 7529021 := bstep (se 3 (by rfl) ⟨1411691, by rfl⟩ : syracuseStep 7529021 = 2823383) B2823383
theorem B5019347 : Blo 1981435 5019347 := bstep (se 1 (by rfl) ⟨3764510, by rfl⟩ : syracuseStep 5019347 = 7529021) B7529021
theorem B3346231 : Blo 1981435 3346231 := bstep (se 1 (by rfl) ⟨2509673, by rfl⟩ : syracuseStep 3346231 = 5019347) B5019347
theorem B4461641 : Blo 1981435 4461641 := bstep (se 2 (by rfl) ⟨1673115, by rfl⟩ : syracuseStep 4461641 = 3346231) B3346231
theorem B2974427 : Blo 1981435 2974427 := bstep (se 1 (by rfl) ⟨2230820, by rfl⟩ : syracuseStep 2974427 = 4461641) B4461641
theorem B1982951 : Blo 1981435 1982951 := bstep (se 1 (by rfl) ⟨1487213, by rfl⟩ : syracuseStep 1982951 = 2974427) B2974427
theorem B2230825 : Blo 1981435 2230825 := bbase (se 2 (by rfl) ⟨836559, by rfl⟩ : syracuseStep 2230825 = 1673119) (by norm_num)
theorem B2974433 : Blo 1981435 2974433 := bstep (se 2 (by rfl) ⟨1115412, by rfl⟩ : syracuseStep 2974433 = 2230825) B2230825
theorem B1982955 : Blo 1981435 1982955 := bstep (se 1 (by rfl) ⟨1487216, by rfl⟩ : syracuseStep 1982955 = 2974433) B2974433
theorem B4074877 : Blo 1981435 4074877 := bbase (se 3 (by rfl) ⟨764039, by rfl⟩ : syracuseStep 4074877 = 1528079) (by norm_num)
theorem B5433169 : Blo 1981435 5433169 := bstep (se 2 (by rfl) ⟨2037438, by rfl⟩ : syracuseStep 5433169 = 4074877) B4074877
theorem B7244225 : Blo 1981435 7244225 := bstep (se 2 (by rfl) ⟨2716584, by rfl⟩ : syracuseStep 7244225 = 5433169) B5433169
theorem B4829483 : Blo 1981435 4829483 := bstep (se 1 (by rfl) ⟨3622112, by rfl⟩ : syracuseStep 4829483 = 7244225) B7244225
theorem B12878621 : Blo 1981435 12878621 := bstep (se 3 (by rfl) ⟨2414741, by rfl⟩ : syracuseStep 12878621 = 4829483) B4829483
theorem B8585747 : Blo 1981435 8585747 := bstep (se 1 (by rfl) ⟨6439310, by rfl⟩ : syracuseStep 8585747 = 12878621) B12878621
theorem B5723831 : Blo 1981435 5723831 := bstep (se 1 (by rfl) ⟨4292873, by rfl⟩ : syracuseStep 5723831 = 8585747) B8585747
theorem B15263549 : Blo 1981435 15263549 := bstep (se 3 (by rfl) ⟨2861915, by rfl⟩ : syracuseStep 15263549 = 5723831) B5723831
theorem B10175699 : Blo 1981435 10175699 := bstep (se 1 (by rfl) ⟨7631774, by rfl⟩ : syracuseStep 10175699 = 15263549) B15263549
theorem B6783799 : Blo 1981435 6783799 := bstep (se 1 (by rfl) ⟨5087849, by rfl⟩ : syracuseStep 6783799 = 10175699) B10175699
theorem B9045065 : Blo 1981435 9045065 := bstep (se 2 (by rfl) ⟨3391899, by rfl⟩ : syracuseStep 9045065 = 6783799) B6783799
theorem B24120173 : Blo 1981435 24120173 := bstep (se 3 (by rfl) ⟨4522532, by rfl⟩ : syracuseStep 24120173 = 9045065) B9045065
theorem B16080115 : Blo 1981435 16080115 := bstep (se 1 (by rfl) ⟨12060086, by rfl⟩ : syracuseStep 16080115 = 24120173) B24120173
theorem B21440153 : Blo 1981435 21440153 := bstep (se 2 (by rfl) ⟨8040057, by rfl⟩ : syracuseStep 21440153 = 16080115) B16080115
theorem B14293435 : Blo 1981435 14293435 := bstep (se 1 (by rfl) ⟨10720076, by rfl⟩ : syracuseStep 14293435 = 21440153) B21440153
theorem B19057913 : Blo 1981435 19057913 := bstep (se 2 (by rfl) ⟨7146717, by rfl⟩ : syracuseStep 19057913 = 14293435) B14293435
theorem B12705275 : Blo 1981435 12705275 := bstep (se 1 (by rfl) ⟨9528956, by rfl⟩ : syracuseStep 12705275 = 19057913) B19057913
theorem B8470183 : Blo 1981435 8470183 := bstep (se 1 (by rfl) ⟨6352637, by rfl⟩ : syracuseStep 8470183 = 12705275) B12705275
theorem B11293577 : Blo 1981435 11293577 := bstep (se 2 (by rfl) ⟨4235091, by rfl⟩ : syracuseStep 11293577 = 8470183) B8470183
theorem B7529051 : Blo 1981435 7529051 := bstep (se 1 (by rfl) ⟨5646788, by rfl⟩ : syracuseStep 7529051 = 11293577) B11293577
theorem B5019367 : Blo 1981435 5019367 := bstep (se 1 (by rfl) ⟨3764525, by rfl⟩ : syracuseStep 5019367 = 7529051) B7529051
theorem B6692489 : Blo 1981435 6692489 := bstep (se 2 (by rfl) ⟨2509683, by rfl⟩ : syracuseStep 6692489 = 5019367) B5019367
theorem B4461659 : Blo 1981435 4461659 := bstep (se 1 (by rfl) ⟨3346244, by rfl⟩ : syracuseStep 4461659 = 6692489) B6692489
theorem B2974439 : Blo 1981435 2974439 := bstep (se 1 (by rfl) ⟨2230829, by rfl⟩ : syracuseStep 2974439 = 4461659) B4461659
theorem B1982959 : Blo 1981435 1982959 := bstep (se 1 (by rfl) ⟨1487219, by rfl⟩ : syracuseStep 1982959 = 2974439) B2974439
theorem B2974445 : Blo 1981435 2974445 := bbase (se 3 (by rfl) ⟨557708, by rfl⟩ : syracuseStep 2974445 = 1115417) (by norm_num)
theorem B1982963 : Blo 1981435 1982963 := bstep (se 1 (by rfl) ⟨1487222, by rfl⟩ : syracuseStep 1982963 = 2974445) B2974445
theorem B4461677 : Blo 1981435 4461677 := bbase (se 3 (by rfl) ⟨836564, by rfl⟩ : syracuseStep 4461677 = 1673129) (by norm_num)
theorem B2974451 : Blo 1981435 2974451 := bstep (se 1 (by rfl) ⟨2230838, by rfl⟩ : syracuseStep 2974451 = 4461677) B4461677
theorem B1982967 : Blo 1981435 1982967 := bstep (se 1 (by rfl) ⟨1487225, by rfl⟩ : syracuseStep 1982967 = 2974451) B2974451
theorem B3764549 : Blo 1981435 3764549 := bbase (se 4 (by rfl) ⟨352926, by rfl⟩ : syracuseStep 3764549 = 705853) (by norm_num)
theorem B2509699 : Blo 1981435 2509699 := bstep (se 1 (by rfl) ⟨1882274, by rfl⟩ : syracuseStep 2509699 = 3764549) B3764549
theorem B3346265 : Blo 1981435 3346265 := bstep (se 2 (by rfl) ⟨1254849, by rfl⟩ : syracuseStep 3346265 = 2509699) B2509699
theorem B2230843 : Blo 1981435 2230843 := bstep (se 1 (by rfl) ⟨1673132, by rfl⟩ : syracuseStep 2230843 = 3346265) B3346265
theorem B2974457 : Blo 1981435 2974457 := bstep (se 2 (by rfl) ⟨1115421, by rfl⟩ : syracuseStep 2974457 = 2230843) B2230843
theorem B1982971 : Blo 1981435 1982971 := bstep (se 1 (by rfl) ⟨1487228, by rfl⟩ : syracuseStep 1982971 = 2974457) B2974457
theorem B2543945 : Blo 1981435 2543945 := bbase (se 2 (by rfl) ⟨953979, by rfl⟩ : syracuseStep 2543945 = 1907959) (by norm_num)
theorem B6783853 : Blo 1981435 6783853 := bstep (se 3 (by rfl) ⟨1271972, by rfl⟩ : syracuseStep 6783853 = 2543945) B2543945
theorem B9045137 : Blo 1981435 9045137 := bstep (se 2 (by rfl) ⟨3391926, by rfl⟩ : syracuseStep 9045137 = 6783853) B6783853
theorem B6030091 : Blo 1981435 6030091 := bstep (se 1 (by rfl) ⟨4522568, by rfl⟩ : syracuseStep 6030091 = 9045137) B9045137
theorem B32160485 : Blo 1981435 32160485 := bstep (se 4 (by rfl) ⟨3015045, by rfl⟩ : syracuseStep 32160485 = 6030091) B6030091
theorem B21440323 : Blo 1981435 21440323 := bstep (se 1 (by rfl) ⟨16080242, by rfl⟩ : syracuseStep 21440323 = 32160485) B32160485
theorem B28587097 : Blo 1981435 28587097 := bstep (se 2 (by rfl) ⟨10720161, by rfl⟩ : syracuseStep 28587097 = 21440323) B21440323
theorem B38116129 : Blo 1981435 38116129 := bstep (se 2 (by rfl) ⟨14293548, by rfl⟩ : syracuseStep 38116129 = 28587097) B28587097
theorem B50821505 : Blo 1981435 50821505 := bstep (se 2 (by rfl) ⟨19058064, by rfl⟩ : syracuseStep 50821505 = 38116129) B38116129
theorem B33881003 : Blo 1981435 33881003 := bstep (se 1 (by rfl) ⟨25410752, by rfl⟩ : syracuseStep 33881003 = 50821505) B50821505
theorem B22587335 : Blo 1981435 22587335 := bstep (se 1 (by rfl) ⟨16940501, by rfl⟩ : syracuseStep 22587335 = 33881003) B33881003
theorem B15058223 : Blo 1981435 15058223 := bstep (se 1 (by rfl) ⟨11293667, by rfl⟩ : syracuseStep 15058223 = 22587335) B22587335
theorem B10038815 : Blo 1981435 10038815 := bstep (se 1 (by rfl) ⟨7529111, by rfl⟩ : syracuseStep 10038815 = 15058223) B15058223
theorem B6692543 : Blo 1981435 6692543 := bstep (se 1 (by rfl) ⟨5019407, by rfl⟩ : syracuseStep 6692543 = 10038815) B10038815
theorem B4461695 : Blo 1981435 4461695 := bstep (se 1 (by rfl) ⟨3346271, by rfl⟩ : syracuseStep 4461695 = 6692543) B6692543
theorem B2974463 : Blo 1981435 2974463 := bstep (se 1 (by rfl) ⟨2230847, by rfl⟩ : syracuseStep 2974463 = 4461695) B4461695
theorem B1982975 : Blo 1981435 1982975 := bstep (se 1 (by rfl) ⟨1487231, by rfl⟩ : syracuseStep 1982975 = 2974463) B2974463
theorem B2974469 : Blo 1981435 2974469 := bbase (se 4 (by rfl) ⟨278856, by rfl⟩ : syracuseStep 2974469 = 557713) (by norm_num)
theorem B1982979 : Blo 1981435 1982979 := bstep (se 1 (by rfl) ⟨1487234, by rfl⟩ : syracuseStep 1982979 = 2974469) B2974469
theorem B3346285 : Blo 1981435 3346285 := bbase (se 3 (by rfl) ⟨627428, by rfl⟩ : syracuseStep 3346285 = 1254857) (by norm_num)
theorem B4461713 : Blo 1981435 4461713 := bstep (se 2 (by rfl) ⟨1673142, by rfl⟩ : syracuseStep 4461713 = 3346285) B3346285
theorem B2974475 : Blo 1981435 2974475 := bstep (se 1 (by rfl) ⟨2230856, by rfl⟩ : syracuseStep 2974475 = 4461713) B4461713
theorem B1982983 : Blo 1981435 1982983 := bstep (se 1 (by rfl) ⟨1487237, by rfl⟩ : syracuseStep 1982983 = 2974475) B2974475
theorem B2230861 : Blo 1981435 2230861 := bbase (se 3 (by rfl) ⟨418286, by rfl⟩ : syracuseStep 2230861 = 836573) (by norm_num)
theorem B2974481 : Blo 1981435 2974481 := bstep (se 2 (by rfl) ⟨1115430, by rfl⟩ : syracuseStep 2974481 = 2230861) B2230861
theorem B1982987 : Blo 1981435 1982987 := bstep (se 1 (by rfl) ⟨1487240, by rfl⟩ : syracuseStep 1982987 = 2974481) B2974481
theorem B6692597 : Blo 1981435 6692597 := bbase (se 5 (by rfl) ⟨313715, by rfl⟩ : syracuseStep 6692597 = 627431) (by norm_num)
theorem B4461731 : Blo 1981435 4461731 := bstep (se 1 (by rfl) ⟨3346298, by rfl⟩ : syracuseStep 4461731 = 6692597) B6692597
theorem B2974487 : Blo 1981435 2974487 := bstep (se 1 (by rfl) ⟨2230865, by rfl⟩ : syracuseStep 2974487 = 4461731) B4461731
theorem B1982991 : Blo 1981435 1982991 := bstep (se 1 (by rfl) ⟨1487243, by rfl⟩ : syracuseStep 1982991 = 2974487) B2974487
theorem B2974493 : Blo 1981435 2974493 := bbase (se 3 (by rfl) ⟨557717, by rfl⟩ : syracuseStep 2974493 = 1115435) (by norm_num)
theorem B1982995 : Blo 1981435 1982995 := bstep (se 1 (by rfl) ⟨1487246, by rfl⟩ : syracuseStep 1982995 = 2974493) B2974493
theorem B4461749 : Blo 1981435 4461749 := bbase (se 5 (by rfl) ⟨209144, by rfl⟩ : syracuseStep 4461749 = 418289) (by norm_num)
theorem B2974499 : Blo 1981435 2974499 := bstep (se 1 (by rfl) ⟨2230874, by rfl⟩ : syracuseStep 2974499 = 4461749) B4461749
theorem B1982999 : Blo 1981435 1982999 := bstep (se 1 (by rfl) ⟨1487249, by rfl⟩ : syracuseStep 1982999 = 2974499) B2974499
theorem B2117593 : Blo 1981435 2117593 := bbase (se 2 (by rfl) ⟨794097, by rfl⟩ : syracuseStep 2117593 = 1588195) (by norm_num)
theorem B11293829 : Blo 1981435 11293829 := bstep (se 4 (by rfl) ⟨1058796, by rfl⟩ : syracuseStep 11293829 = 2117593) B2117593
theorem B7529219 : Blo 1981435 7529219 := bstep (se 1 (by rfl) ⟨5646914, by rfl⟩ : syracuseStep 7529219 = 11293829) B11293829
theorem B5019479 : Blo 1981435 5019479 := bstep (se 1 (by rfl) ⟨3764609, by rfl⟩ : syracuseStep 5019479 = 7529219) B7529219
theorem B3346319 : Blo 1981435 3346319 := bstep (se 1 (by rfl) ⟨2509739, by rfl⟩ : syracuseStep 3346319 = 5019479) B5019479
theorem B2230879 : Blo 1981435 2230879 := bstep (se 1 (by rfl) ⟨1673159, by rfl⟩ : syracuseStep 2230879 = 3346319) B3346319
theorem B2974505 : Blo 1981435 2974505 := bstep (se 2 (by rfl) ⟨1115439, by rfl⟩ : syracuseStep 2974505 = 2230879) B2230879
theorem B1983003 : Blo 1981435 1983003 := bstep (se 1 (by rfl) ⟨1487252, by rfl⟩ : syracuseStep 1983003 = 2974505) B2974505
theorem B2117597 : Blo 1981435 2117597 := bbase (se 3 (by rfl) ⟨397049, by rfl⟩ : syracuseStep 2117597 = 794099) (by norm_num)
theorem B5646925 : Blo 1981435 5646925 := bstep (se 3 (by rfl) ⟨1058798, by rfl⟩ : syracuseStep 5646925 = 2117597) B2117597
theorem B7529233 : Blo 1981435 7529233 := bstep (se 2 (by rfl) ⟨2823462, by rfl⟩ : syracuseStep 7529233 = 5646925) B5646925
theorem B10038977 : Blo 1981435 10038977 := bstep (se 2 (by rfl) ⟨3764616, by rfl⟩ : syracuseStep 10038977 = 7529233) B7529233
theorem B6692651 : Blo 1981435 6692651 := bstep (se 1 (by rfl) ⟨5019488, by rfl⟩ : syracuseStep 6692651 = 10038977) B10038977
theorem B4461767 : Blo 1981435 4461767 := bstep (se 1 (by rfl) ⟨3346325, by rfl⟩ : syracuseStep 4461767 = 6692651) B6692651
theorem B2974511 : Blo 1981435 2974511 := bstep (se 1 (by rfl) ⟨2230883, by rfl⟩ : syracuseStep 2974511 = 4461767) B4461767
theorem B1983007 : Blo 1981435 1983007 := bstep (se 1 (by rfl) ⟨1487255, by rfl⟩ : syracuseStep 1983007 = 2974511) B2974511
theorem B2974517 : Blo 1981435 2974517 := bbase (se 5 (by rfl) ⟨139430, by rfl⟩ : syracuseStep 2974517 = 278861) (by norm_num)
theorem B1983011 : Blo 1981435 1983011 := bstep (se 1 (by rfl) ⟨1487258, by rfl⟩ : syracuseStep 1983011 = 2974517) B2974517
theorem B5019509 : Blo 1981435 5019509 := bbase (se 5 (by rfl) ⟨235289, by rfl⟩ : syracuseStep 5019509 = 470579) (by norm_num)
theorem B3346339 : Blo 1981435 3346339 := bstep (se 1 (by rfl) ⟨2509754, by rfl⟩ : syracuseStep 3346339 = 5019509) B5019509
theorem B4461785 : Blo 1981435 4461785 := bstep (se 2 (by rfl) ⟨1673169, by rfl⟩ : syracuseStep 4461785 = 3346339) B3346339
theorem B2974523 : Blo 1981435 2974523 := bstep (se 1 (by rfl) ⟨2230892, by rfl⟩ : syracuseStep 2974523 = 4461785) B4461785
theorem B1983015 : Blo 1981435 1983015 := bstep (se 1 (by rfl) ⟨1487261, by rfl⟩ : syracuseStep 1983015 = 2974523) B2974523
theorem B2230897 : Blo 1981435 2230897 := bbase (se 2 (by rfl) ⟨836586, by rfl⟩ : syracuseStep 2230897 = 1673173) (by norm_num)
theorem B2974529 : Blo 1981435 2974529 := bstep (se 2 (by rfl) ⟨1115448, by rfl⟩ : syracuseStep 2974529 = 2230897) B2230897
theorem B1983019 : Blo 1981435 1983019 := bstep (se 1 (by rfl) ⟨1487264, by rfl⟩ : syracuseStep 1983019 = 2974529) B2974529
theorem B7146949 : Blo 1981435 7146949 := bbase (se 4 (by rfl) ⟨670026, by rfl⟩ : syracuseStep 7146949 = 1340053) (by norm_num)
theorem B9529265 : Blo 1981435 9529265 := bstep (se 2 (by rfl) ⟨3573474, by rfl⟩ : syracuseStep 9529265 = 7146949) B7146949
theorem B6352843 : Blo 1981435 6352843 := bstep (se 1 (by rfl) ⟨4764632, by rfl⟩ : syracuseStep 6352843 = 9529265) B9529265
theorem B8470457 : Blo 1981435 8470457 := bstep (se 2 (by rfl) ⟨3176421, by rfl⟩ : syracuseStep 8470457 = 6352843) B6352843
theorem B5646971 : Blo 1981435 5646971 := bstep (se 1 (by rfl) ⟨4235228, by rfl⟩ : syracuseStep 5646971 = 8470457) B8470457
theorem B3764647 : Blo 1981435 3764647 := bstep (se 1 (by rfl) ⟨2823485, by rfl⟩ : syracuseStep 3764647 = 5646971) B5646971
theorem B5019529 : Blo 1981435 5019529 := bstep (se 2 (by rfl) ⟨1882323, by rfl⟩ : syracuseStep 5019529 = 3764647) B3764647
theorem B6692705 : Blo 1981435 6692705 := bstep (se 2 (by rfl) ⟨2509764, by rfl⟩ : syracuseStep 6692705 = 5019529) B5019529
theorem B4461803 : Blo 1981435 4461803 := bstep (se 1 (by rfl) ⟨3346352, by rfl⟩ : syracuseStep 4461803 = 6692705) B6692705
theorem B2974535 : Blo 1981435 2974535 := bstep (se 1 (by rfl) ⟨2230901, by rfl⟩ : syracuseStep 2974535 = 4461803) B4461803
theorem B1983023 : Blo 1981435 1983023 := bstep (se 1 (by rfl) ⟨1487267, by rfl⟩ : syracuseStep 1983023 = 2974535) B2974535
theorem B2974541 : Blo 1981435 2974541 := bbase (se 3 (by rfl) ⟨557726, by rfl⟩ : syracuseStep 2974541 = 1115453) (by norm_num)
theorem B1983027 : Blo 1981435 1983027 := bstep (se 1 (by rfl) ⟨1487270, by rfl⟩ : syracuseStep 1983027 = 2974541) B2974541
theorem B4461821 : Blo 1981435 4461821 := bbase (se 3 (by rfl) ⟨836591, by rfl⟩ : syracuseStep 4461821 = 1673183) (by norm_num)
theorem B2974547 : Blo 1981435 2974547 := bstep (se 1 (by rfl) ⟨2230910, by rfl⟩ : syracuseStep 2974547 = 4461821) B4461821
theorem B1983031 : Blo 1981435 1983031 := bstep (se 1 (by rfl) ⟨1487273, by rfl⟩ : syracuseStep 1983031 = 2974547) B2974547
theorem B3346373 : Blo 1981435 3346373 := bbase (se 4 (by rfl) ⟨313722, by rfl⟩ : syracuseStep 3346373 = 627445) (by norm_num)
theorem B2230915 : Blo 1981435 2230915 := bstep (se 1 (by rfl) ⟨1673186, by rfl⟩ : syracuseStep 2230915 = 3346373) B3346373
theorem B2974553 : Blo 1981435 2974553 := bstep (se 2 (by rfl) ⟨1115457, by rfl⟩ : syracuseStep 2974553 = 2230915) B2230915
theorem B1983035 : Blo 1981435 1983035 := bstep (se 1 (by rfl) ⟨1487276, by rfl⟩ : syracuseStep 1983035 = 2974553) B2974553
theorem B15058709 : Blo 1981435 15058709 := bbase (se 6 (by rfl) ⟨352938, by rfl⟩ : syracuseStep 15058709 = 705877) (by norm_num)
theorem B10039139 : Blo 1981435 10039139 := bstep (se 1 (by rfl) ⟨7529354, by rfl⟩ : syracuseStep 10039139 = 15058709) B15058709
theorem B6692759 : Blo 1981435 6692759 := bstep (se 1 (by rfl) ⟨5019569, by rfl⟩ : syracuseStep 6692759 = 10039139) B10039139
theorem B4461839 : Blo 1981435 4461839 := bstep (se 1 (by rfl) ⟨3346379, by rfl⟩ : syracuseStep 4461839 = 6692759) B6692759
theorem B2974559 : Blo 1981435 2974559 := bstep (se 1 (by rfl) ⟨2230919, by rfl⟩ : syracuseStep 2974559 = 4461839) B4461839
theorem B1983039 : Blo 1981435 1983039 := bstep (se 1 (by rfl) ⟨1487279, by rfl⟩ : syracuseStep 1983039 = 2974559) B2974559
theorem B2974565 : Blo 1981435 2974565 := bbase (se 4 (by rfl) ⟨278865, by rfl⟩ : syracuseStep 2974565 = 557731) (by norm_num)
theorem B1983043 : Blo 1981435 1983043 := bstep (se 1 (by rfl) ⟨1487282, by rfl⟩ : syracuseStep 1983043 = 2974565) B2974565
theorem B3764693 : Blo 1981435 3764693 := bbase (se 7 (by rfl) ⟨44117, by rfl⟩ : syracuseStep 3764693 = 88235) (by norm_num)
theorem B2509795 : Blo 1981435 2509795 := bstep (se 1 (by rfl) ⟨1882346, by rfl⟩ : syracuseStep 2509795 = 3764693) B3764693
theorem B3346393 : Blo 1981435 3346393 := bstep (se 2 (by rfl) ⟨1254897, by rfl⟩ : syracuseStep 3346393 = 2509795) B2509795
theorem B4461857 : Blo 1981435 4461857 := bstep (se 2 (by rfl) ⟨1673196, by rfl⟩ : syracuseStep 4461857 = 3346393) B3346393
theorem B2974571 : Blo 1981435 2974571 := bstep (se 1 (by rfl) ⟨2230928, by rfl⟩ : syracuseStep 2974571 = 4461857) B4461857
theorem B1983047 : Blo 1981435 1983047 := bstep (se 1 (by rfl) ⟨1487285, by rfl⟩ : syracuseStep 1983047 = 2974571) B2974571
theorem B2230933 : Blo 1981435 2230933 := bbase (se 6 (by rfl) ⟨52287, by rfl⟩ : syracuseStep 2230933 = 104575) (by norm_num)
theorem B2974577 : Blo 1981435 2974577 := bstep (se 2 (by rfl) ⟨1115466, by rfl⟩ : syracuseStep 2974577 = 2230933) B2230933
theorem B1983051 : Blo 1981435 1983051 := bstep (se 1 (by rfl) ⟨1487288, by rfl⟩ : syracuseStep 1983051 = 2974577) B2974577
theorem B2509805 : Blo 1981435 2509805 := bbase (se 3 (by rfl) ⟨470588, by rfl⟩ : syracuseStep 2509805 = 941177) (by norm_num)
theorem B6692813 : Blo 1981435 6692813 := bstep (se 3 (by rfl) ⟨1254902, by rfl⟩ : syracuseStep 6692813 = 2509805) B2509805
theorem B4461875 : Blo 1981435 4461875 := bstep (se 1 (by rfl) ⟨3346406, by rfl⟩ : syracuseStep 4461875 = 6692813) B6692813
theorem B2974583 : Blo 1981435 2974583 := bstep (se 1 (by rfl) ⟨2230937, by rfl⟩ : syracuseStep 2974583 = 4461875) B4461875
theorem B1983055 : Blo 1981435 1983055 := bstep (se 1 (by rfl) ⟨1487291, by rfl⟩ : syracuseStep 1983055 = 2974583) B2974583
theorem B2974589 : Blo 1981435 2974589 := bbase (se 3 (by rfl) ⟨557735, by rfl⟩ : syracuseStep 2974589 = 1115471) (by norm_num)
theorem B1983059 : Blo 1981435 1983059 := bstep (se 1 (by rfl) ⟨1487294, by rfl⟩ : syracuseStep 1983059 = 2974589) B2974589
theorem B4461893 : Blo 1981435 4461893 := bbase (se 4 (by rfl) ⟨418302, by rfl⟩ : syracuseStep 4461893 = 836605) (by norm_num)
theorem B2974595 : Blo 1981435 2974595 := bstep (se 1 (by rfl) ⟨2230946, by rfl⟩ : syracuseStep 2974595 = 4461893) B4461893
theorem B1983063 : Blo 1981435 1983063 := bstep (se 1 (by rfl) ⟨1487297, by rfl⟩ : syracuseStep 1983063 = 2974595) B2974595
theorem B7147109 : Blo 1981435 7147109 := bbase (se 4 (by rfl) ⟨670041, by rfl⟩ : syracuseStep 7147109 = 1340083) (by norm_num)
theorem B4764739 : Blo 1981435 4764739 := bstep (se 1 (by rfl) ⟨3573554, by rfl⟩ : syracuseStep 4764739 = 7147109) B7147109
theorem B6352985 : Blo 1981435 6352985 := bstep (se 2 (by rfl) ⟨2382369, by rfl⟩ : syracuseStep 6352985 = 4764739) B4764739
theorem B4235323 : Blo 1981435 4235323 := bstep (se 1 (by rfl) ⟨3176492, by rfl⟩ : syracuseStep 4235323 = 6352985) B6352985
theorem B5647097 : Blo 1981435 5647097 := bstep (se 2 (by rfl) ⟨2117661, by rfl⟩ : syracuseStep 5647097 = 4235323) B4235323
theorem B3764731 : Blo 1981435 3764731 := bstep (se 1 (by rfl) ⟨2823548, by rfl⟩ : syracuseStep 3764731 = 5647097) B5647097
theorem B5019641 : Blo 1981435 5019641 := bstep (se 2 (by rfl) ⟨1882365, by rfl⟩ : syracuseStep 5019641 = 3764731) B3764731
theorem B3346427 : Blo 1981435 3346427 := bstep (se 1 (by rfl) ⟨2509820, by rfl⟩ : syracuseStep 3346427 = 5019641) B5019641
theorem B2230951 : Blo 1981435 2230951 := bstep (se 1 (by rfl) ⟨1673213, by rfl⟩ : syracuseStep 2230951 = 3346427) B3346427
theorem B2974601 : Blo 1981435 2974601 := bstep (se 2 (by rfl) ⟨1115475, by rfl⟩ : syracuseStep 2974601 = 2230951) B2230951
theorem B1983067 : Blo 1981435 1983067 := bstep (se 1 (by rfl) ⟨1487300, by rfl⟩ : syracuseStep 1983067 = 2974601) B2974601
theorem B10039301 : Blo 1981435 10039301 := bbase (se 4 (by rfl) ⟨941184, by rfl⟩ : syracuseStep 10039301 = 1882369) (by norm_num)
theorem B6692867 : Blo 1981435 6692867 := bstep (se 1 (by rfl) ⟨5019650, by rfl⟩ : syracuseStep 6692867 = 10039301) B10039301
theorem B4461911 : Blo 1981435 4461911 := bstep (se 1 (by rfl) ⟨3346433, by rfl⟩ : syracuseStep 4461911 = 6692867) B6692867
theorem B2974607 : Blo 1981435 2974607 := bstep (se 1 (by rfl) ⟨2230955, by rfl⟩ : syracuseStep 2974607 = 4461911) B4461911
theorem B1983071 : Blo 1981435 1983071 := bstep (se 1 (by rfl) ⟨1487303, by rfl⟩ : syracuseStep 1983071 = 2974607) B2974607
theorem B2974613 : Blo 1981435 2974613 := bbase (se 6 (by rfl) ⟨69717, by rfl⟩ : syracuseStep 2974613 = 139435) (by norm_num)
theorem B1983075 : Blo 1981435 1983075 := bstep (se 1 (by rfl) ⟨1487306, by rfl⟩ : syracuseStep 1983075 = 2974613) B2974613
theorem B11294261 : Blo 1981435 11294261 := bbase (se 5 (by rfl) ⟨529418, by rfl⟩ : syracuseStep 11294261 = 1058837) (by norm_num)
theorem B7529507 : Blo 1981435 7529507 := bstep (se 1 (by rfl) ⟨5647130, by rfl⟩ : syracuseStep 7529507 = 11294261) B11294261
theorem B5019671 : Blo 1981435 5019671 := bstep (se 1 (by rfl) ⟨3764753, by rfl⟩ : syracuseStep 5019671 = 7529507) B7529507
theorem B3346447 : Blo 1981435 3346447 := bstep (se 1 (by rfl) ⟨2509835, by rfl⟩ : syracuseStep 3346447 = 5019671) B5019671
theorem B4461929 : Blo 1981435 4461929 := bstep (se 2 (by rfl) ⟨1673223, by rfl⟩ : syracuseStep 4461929 = 3346447) B3346447
theorem B2974619 : Blo 1981435 2974619 := bstep (se 1 (by rfl) ⟨2230964, by rfl⟩ : syracuseStep 2974619 = 4461929) B4461929
theorem B1983079 : Blo 1981435 1983079 := bstep (se 1 (by rfl) ⟨1487309, by rfl⟩ : syracuseStep 1983079 = 2974619) B2974619
theorem B2230969 : Blo 1981435 2230969 := bbase (se 2 (by rfl) ⟨836613, by rfl⟩ : syracuseStep 2230969 = 1673227) (by norm_num)
theorem B2974625 : Blo 1981435 2974625 := bstep (se 2 (by rfl) ⟨1115484, by rfl⟩ : syracuseStep 2974625 = 2230969) B2230969
theorem B1983083 : Blo 1981435 1983083 := bstep (se 1 (by rfl) ⟨1487312, by rfl⟩ : syracuseStep 1983083 = 2974625) B2974625
theorem B4235365 : Blo 1981435 4235365 := bbase (se 4 (by rfl) ⟨397065, by rfl⟩ : syracuseStep 4235365 = 794131) (by norm_num)
theorem B5647153 : Blo 1981435 5647153 := bstep (se 2 (by rfl) ⟨2117682, by rfl⟩ : syracuseStep 5647153 = 4235365) B4235365
theorem B7529537 : Blo 1981435 7529537 := bstep (se 2 (by rfl) ⟨2823576, by rfl⟩ : syracuseStep 7529537 = 5647153) B5647153
theorem B5019691 : Blo 1981435 5019691 := bstep (se 1 (by rfl) ⟨3764768, by rfl⟩ : syracuseStep 5019691 = 7529537) B7529537
theorem B6692921 : Blo 1981435 6692921 := bstep (se 2 (by rfl) ⟨2509845, by rfl⟩ : syracuseStep 6692921 = 5019691) B5019691
theorem B4461947 : Blo 1981435 4461947 := bstep (se 1 (by rfl) ⟨3346460, by rfl⟩ : syracuseStep 4461947 = 6692921) B6692921
theorem B2974631 : Blo 1981435 2974631 := bstep (se 1 (by rfl) ⟨2230973, by rfl⟩ : syracuseStep 2974631 = 4461947) B4461947
theorem B1983087 : Blo 1981435 1983087 := bstep (se 1 (by rfl) ⟨1487315, by rfl⟩ : syracuseStep 1983087 = 2974631) B2974631
theorem B2974637 : Blo 1981435 2974637 := bbase (se 3 (by rfl) ⟨557744, by rfl⟩ : syracuseStep 2974637 = 1115489) (by norm_num)
theorem B1983091 : Blo 1981435 1983091 := bstep (se 1 (by rfl) ⟨1487318, by rfl⟩ : syracuseStep 1983091 = 2974637) B2974637
theorem B4461965 : Blo 1981435 4461965 := bbase (se 3 (by rfl) ⟨836618, by rfl⟩ : syracuseStep 4461965 = 1673237) (by norm_num)
theorem B2974643 : Blo 1981435 2974643 := bstep (se 1 (by rfl) ⟨2230982, by rfl⟩ : syracuseStep 2974643 = 4461965) B4461965
theorem B1983095 : Blo 1981435 1983095 := bstep (se 1 (by rfl) ⟨1487321, by rfl⟩ : syracuseStep 1983095 = 2974643) B2974643
theorem B2509861 : Blo 1981435 2509861 := bbase (se 4 (by rfl) ⟨235299, by rfl⟩ : syracuseStep 2509861 = 470599) (by norm_num)
theorem B3346481 : Blo 1981435 3346481 := bstep (se 2 (by rfl) ⟨1254930, by rfl⟩ : syracuseStep 3346481 = 2509861) B2509861
theorem B2230987 : Blo 1981435 2230987 := bstep (se 1 (by rfl) ⟨1673240, by rfl⟩ : syracuseStep 2230987 = 3346481) B3346481
theorem B2974649 : Blo 1981435 2974649 := bstep (se 2 (by rfl) ⟨1115493, by rfl⟩ : syracuseStep 2974649 = 2230987) B2230987
theorem B1983099 : Blo 1981435 1983099 := bstep (se 1 (by rfl) ⟨1487324, by rfl⟩ : syracuseStep 1983099 = 2974649) B2974649
theorem B2544109 : Blo 1981435 2544109 := bbase (se 3 (by rfl) ⟨477020, by rfl⟩ : syracuseStep 2544109 = 954041) (by norm_num)
theorem B13568581 : Blo 1981435 13568581 := bstep (se 4 (by rfl) ⟨1272054, by rfl⟩ : syracuseStep 13568581 = 2544109) B2544109
theorem B18091441 : Blo 1981435 18091441 := bstep (se 2 (by rfl) ⟨6784290, by rfl⟩ : syracuseStep 18091441 = 13568581) B13568581
theorem B96487685 : Blo 1981435 96487685 := bstep (se 4 (by rfl) ⟨9045720, by rfl⟩ : syracuseStep 96487685 = 18091441) B18091441
theorem B64325123 : Blo 1981435 64325123 := bstep (se 1 (by rfl) ⟨48243842, by rfl⟩ : syracuseStep 64325123 = 96487685) B96487685
theorem B42883415 : Blo 1981435 42883415 := bstep (se 1 (by rfl) ⟨32162561, by rfl⟩ : syracuseStep 42883415 = 64325123) B64325123
theorem B28588943 : Blo 1981435 28588943 := bstep (se 1 (by rfl) ⟨21441707, by rfl⟩ : syracuseStep 28588943 = 42883415) B42883415
theorem B19059295 : Blo 1981435 19059295 := bstep (se 1 (by rfl) ⟨14294471, by rfl⟩ : syracuseStep 19059295 = 28588943) B28588943
theorem B25412393 : Blo 1981435 25412393 := bstep (se 2 (by rfl) ⟨9529647, by rfl⟩ : syracuseStep 25412393 = 19059295) B19059295
theorem B16941595 : Blo 1981435 16941595 := bstep (se 1 (by rfl) ⟨12706196, by rfl⟩ : syracuseStep 16941595 = 25412393) B25412393
theorem B22588793 : Blo 1981435 22588793 := bstep (se 2 (by rfl) ⟨8470797, by rfl⟩ : syracuseStep 22588793 = 16941595) B16941595
theorem B15059195 : Blo 1981435 15059195 := bstep (se 1 (by rfl) ⟨11294396, by rfl⟩ : syracuseStep 15059195 = 22588793) B22588793
theorem B10039463 : Blo 1981435 10039463 := bstep (se 1 (by rfl) ⟨7529597, by rfl⟩ : syracuseStep 10039463 = 15059195) B15059195
theorem B6692975 : Blo 1981435 6692975 := bstep (se 1 (by rfl) ⟨5019731, by rfl⟩ : syracuseStep 6692975 = 10039463) B10039463
theorem B4461983 : Blo 1981435 4461983 := bstep (se 1 (by rfl) ⟨3346487, by rfl⟩ : syracuseStep 4461983 = 6692975) B6692975
theorem B2974655 : Blo 1981435 2974655 := bstep (se 1 (by rfl) ⟨2230991, by rfl⟩ : syracuseStep 2974655 = 4461983) B4461983
theorem B1983103 : Blo 1981435 1983103 := bstep (se 1 (by rfl) ⟨1487327, by rfl⟩ : syracuseStep 1983103 = 2974655) B2974655
theorem B2974661 : Blo 1981435 2974661 := bbase (se 4 (by rfl) ⟨278874, by rfl⟩ : syracuseStep 2974661 = 557749) (by norm_num)
theorem B1983107 : Blo 1981435 1983107 := bstep (se 1 (by rfl) ⟨1487330, by rfl⟩ : syracuseStep 1983107 = 2974661) B2974661
theorem B3346501 : Blo 1981435 3346501 := bbase (se 4 (by rfl) ⟨313734, by rfl⟩ : syracuseStep 3346501 = 627469) (by norm_num)
theorem B4462001 : Blo 1981435 4462001 := bstep (se 2 (by rfl) ⟨1673250, by rfl⟩ : syracuseStep 4462001 = 3346501) B3346501
theorem B2974667 : Blo 1981435 2974667 := bstep (se 1 (by rfl) ⟨2231000, by rfl⟩ : syracuseStep 2974667 = 4462001) B4462001
theorem B1983111 : Blo 1981435 1983111 := bstep (se 1 (by rfl) ⟨1487333, by rfl⟩ : syracuseStep 1983111 = 2974667) B2974667
theorem B2231005 : Blo 1981435 2231005 := bbase (se 3 (by rfl) ⟨418313, by rfl⟩ : syracuseStep 2231005 = 836627) (by norm_num)
theorem B2974673 : Blo 1981435 2974673 := bstep (se 2 (by rfl) ⟨1115502, by rfl⟩ : syracuseStep 2974673 = 2231005) B2231005
theorem B1983115 : Blo 1981435 1983115 := bstep (se 1 (by rfl) ⟨1487336, by rfl⟩ : syracuseStep 1983115 = 2974673) B2974673
theorem B6693029 : Blo 1981435 6693029 := bbase (se 4 (by rfl) ⟨627471, by rfl⟩ : syracuseStep 6693029 = 1254943) (by norm_num)
theorem B4462019 : Blo 1981435 4462019 := bstep (se 1 (by rfl) ⟨3346514, by rfl⟩ : syracuseStep 4462019 = 6693029) B6693029
theorem B2974679 : Blo 1981435 2974679 := bstep (se 1 (by rfl) ⟨2231009, by rfl⟩ : syracuseStep 2974679 = 4462019) B4462019
theorem B1983119 : Blo 1981435 1983119 := bstep (se 1 (by rfl) ⟨1487339, by rfl⟩ : syracuseStep 1983119 = 2974679) B2974679
theorem B2974685 : Blo 1981435 2974685 := bbase (se 3 (by rfl) ⟨557753, by rfl⟩ : syracuseStep 2974685 = 1115507) (by norm_num)
theorem B1983123 : Blo 1981435 1983123 := bstep (se 1 (by rfl) ⟨1487342, by rfl⟩ : syracuseStep 1983123 = 2974685) B2974685
theorem B4462037 : Blo 1981435 4462037 := bbase (se 7 (by rfl) ⟨52289, by rfl⟩ : syracuseStep 4462037 = 104579) (by norm_num)
theorem B2974691 : Blo 1981435 2974691 := bstep (se 1 (by rfl) ⟨2231018, by rfl⟩ : syracuseStep 2974691 = 4462037) B4462037
theorem B1983127 : Blo 1981435 1983127 := bstep (se 1 (by rfl) ⟨1487345, by rfl⟩ : syracuseStep 1983127 = 2974691) B2974691
theorem B14294677 : Blo 1981435 14294677 := bbase (se 6 (by rfl) ⟨335031, by rfl⟩ : syracuseStep 14294677 = 670063) (by norm_num)
theorem B19059569 : Blo 1981435 19059569 := bstep (se 2 (by rfl) ⟨7147338, by rfl⟩ : syracuseStep 19059569 = 14294677) B14294677
theorem B12706379 : Blo 1981435 12706379 := bstep (se 1 (by rfl) ⟨9529784, by rfl⟩ : syracuseStep 12706379 = 19059569) B19059569
theorem B8470919 : Blo 1981435 8470919 := bstep (se 1 (by rfl) ⟨6353189, by rfl⟩ : syracuseStep 8470919 = 12706379) B12706379
theorem B5647279 : Blo 1981435 5647279 := bstep (se 1 (by rfl) ⟨4235459, by rfl⟩ : syracuseStep 5647279 = 8470919) B8470919
theorem B7529705 : Blo 1981435 7529705 := bstep (se 2 (by rfl) ⟨2823639, by rfl⟩ : syracuseStep 7529705 = 5647279) B5647279
theorem B5019803 : Blo 1981435 5019803 := bstep (se 1 (by rfl) ⟨3764852, by rfl⟩ : syracuseStep 5019803 = 7529705) B7529705
theorem B3346535 : Blo 1981435 3346535 := bstep (se 1 (by rfl) ⟨2509901, by rfl⟩ : syracuseStep 3346535 = 5019803) B5019803
theorem B2231023 : Blo 1981435 2231023 := bstep (se 1 (by rfl) ⟨1673267, by rfl⟩ : syracuseStep 2231023 = 3346535) B3346535
theorem B2974697 : Blo 1981435 2974697 := bstep (se 2 (by rfl) ⟨1115511, by rfl⟩ : syracuseStep 2974697 = 2231023) B2231023
theorem B1983131 : Blo 1981435 1983131 := bstep (se 1 (by rfl) ⟨1487348, by rfl⟩ : syracuseStep 1983131 = 2974697) B2974697
theorem B4764901 : Blo 1981435 4764901 := bbase (se 4 (by rfl) ⟨446709, by rfl⟩ : syracuseStep 4764901 = 893419) (by norm_num)
theorem B6353201 : Blo 1981435 6353201 := bstep (se 2 (by rfl) ⟨2382450, by rfl⟩ : syracuseStep 6353201 = 4764901) B4764901
theorem B16941869 : Blo 1981435 16941869 := bstep (se 3 (by rfl) ⟨3176600, by rfl⟩ : syracuseStep 16941869 = 6353201) B6353201
theorem B11294579 : Blo 1981435 11294579 := bstep (se 1 (by rfl) ⟨8470934, by rfl⟩ : syracuseStep 11294579 = 16941869) B16941869
theorem B7529719 : Blo 1981435 7529719 := bstep (se 1 (by rfl) ⟨5647289, by rfl⟩ : syracuseStep 7529719 = 11294579) B11294579
theorem B10039625 : Blo 1981435 10039625 := bstep (se 2 (by rfl) ⟨3764859, by rfl⟩ : syracuseStep 10039625 = 7529719) B7529719
theorem B6693083 : Blo 1981435 6693083 := bstep (se 1 (by rfl) ⟨5019812, by rfl⟩ : syracuseStep 6693083 = 10039625) B10039625
theorem B4462055 : Blo 1981435 4462055 := bstep (se 1 (by rfl) ⟨3346541, by rfl⟩ : syracuseStep 4462055 = 6693083) B6693083
theorem B2974703 : Blo 1981435 2974703 := bstep (se 1 (by rfl) ⟨2231027, by rfl⟩ : syracuseStep 2974703 = 4462055) B4462055
theorem B1983135 : Blo 1981435 1983135 := bstep (se 1 (by rfl) ⟨1487351, by rfl⟩ : syracuseStep 1983135 = 2974703) B2974703
theorem B2974709 : Blo 1981435 2974709 := bbase (se 5 (by rfl) ⟨139439, by rfl⟩ : syracuseStep 2974709 = 278879) (by norm_num)
theorem B1983139 : Blo 1981435 1983139 := bstep (se 1 (by rfl) ⟨1487354, by rfl⟩ : syracuseStep 1983139 = 2974709) B2974709
theorem B4235485 : Blo 1981435 4235485 := bbase (se 3 (by rfl) ⟨794153, by rfl⟩ : syracuseStep 4235485 = 1588307) (by norm_num)
theorem B5647313 : Blo 1981435 5647313 := bstep (se 2 (by rfl) ⟨2117742, by rfl⟩ : syracuseStep 5647313 = 4235485) B4235485
theorem B3764875 : Blo 1981435 3764875 := bstep (se 1 (by rfl) ⟨2823656, by rfl⟩ : syracuseStep 3764875 = 5647313) B5647313
theorem B5019833 : Blo 1981435 5019833 := bstep (se 2 (by rfl) ⟨1882437, by rfl⟩ : syracuseStep 5019833 = 3764875) B3764875
theorem B3346555 : Blo 1981435 3346555 := bstep (se 1 (by rfl) ⟨2509916, by rfl⟩ : syracuseStep 3346555 = 5019833) B5019833
theorem B4462073 : Blo 1981435 4462073 := bstep (se 2 (by rfl) ⟨1673277, by rfl⟩ : syracuseStep 4462073 = 3346555) B3346555
theorem B2974715 : Blo 1981435 2974715 := bstep (se 1 (by rfl) ⟨2231036, by rfl⟩ : syracuseStep 2974715 = 4462073) B4462073
theorem B1983143 : Blo 1981435 1983143 := bstep (se 1 (by rfl) ⟨1487357, by rfl⟩ : syracuseStep 1983143 = 2974715) B2974715
theorem B2231041 : Blo 1981435 2231041 := bbase (se 2 (by rfl) ⟨836640, by rfl⟩ : syracuseStep 2231041 = 1673281) (by norm_num)
theorem B2974721 : Blo 1981435 2974721 := bstep (se 2 (by rfl) ⟨1115520, by rfl⟩ : syracuseStep 2974721 = 2231041) B2231041
theorem B1983147 : Blo 1981435 1983147 := bstep (se 1 (by rfl) ⟨1487360, by rfl⟩ : syracuseStep 1983147 = 2974721) B2974721
theorem B5019853 : Blo 1981435 5019853 := bbase (se 3 (by rfl) ⟨941222, by rfl⟩ : syracuseStep 5019853 = 1882445) (by norm_num)
theorem B6693137 : Blo 1981435 6693137 := bstep (se 2 (by rfl) ⟨2509926, by rfl⟩ : syracuseStep 6693137 = 5019853) B5019853
theorem B4462091 : Blo 1981435 4462091 := bstep (se 1 (by rfl) ⟨3346568, by rfl⟩ : syracuseStep 4462091 = 6693137) B6693137
theorem B2974727 : Blo 1981435 2974727 := bstep (se 1 (by rfl) ⟨2231045, by rfl⟩ : syracuseStep 2974727 = 4462091) B4462091
theorem B1983151 : Blo 1981435 1983151 := bstep (se 1 (by rfl) ⟨1487363, by rfl⟩ : syracuseStep 1983151 = 2974727) B2974727
theorem B2974733 : Blo 1981435 2974733 := bbase (se 3 (by rfl) ⟨557762, by rfl⟩ : syracuseStep 2974733 = 1115525) (by norm_num)
theorem B1983155 : Blo 1981435 1983155 := bstep (se 1 (by rfl) ⟨1487366, by rfl⟩ : syracuseStep 1983155 = 2974733) B2974733
theorem B4462109 : Blo 1981435 4462109 := bbase (se 3 (by rfl) ⟨836645, by rfl⟩ : syracuseStep 4462109 = 1673291) (by norm_num)
theorem B2974739 : Blo 1981435 2974739 := bstep (se 1 (by rfl) ⟨2231054, by rfl⟩ : syracuseStep 2974739 = 4462109) B4462109
theorem B1983159 : Blo 1981435 1983159 := bstep (se 1 (by rfl) ⟨1487369, by rfl⟩ : syracuseStep 1983159 = 2974739) B2974739
theorem B3346589 : Blo 1981435 3346589 := bbase (se 3 (by rfl) ⟨627485, by rfl⟩ : syracuseStep 3346589 = 1254971) (by norm_num)
theorem B2231059 : Blo 1981435 2231059 := bstep (se 1 (by rfl) ⟨1673294, by rfl⟩ : syracuseStep 2231059 = 3346589) B3346589
theorem B2974745 : Blo 1981435 2974745 := bstep (se 2 (by rfl) ⟨1115529, by rfl⟩ : syracuseStep 2974745 = 2231059) B2231059
theorem B1983163 : Blo 1981435 1983163 := bstep (se 1 (by rfl) ⟨1487372, by rfl⟩ : syracuseStep 1983163 = 2974745) B2974745
theorem B5802533 : Blo 1981435 5802533 := bbase (se 4 (by rfl) ⟨543987, by rfl⟩ : syracuseStep 5802533 = 1087975) (by norm_num)
theorem B3868355 : Blo 1981435 3868355 := bstep (se 1 (by rfl) ⟨2901266, by rfl⟩ : syracuseStep 3868355 = 5802533) B5802533
theorem B10315613 : Blo 1981435 10315613 := bstep (se 3 (by rfl) ⟨1934177, by rfl⟩ : syracuseStep 10315613 = 3868355) B3868355
theorem B27508301 : Blo 1981435 27508301 := bstep (se 3 (by rfl) ⟨5157806, by rfl⟩ : syracuseStep 27508301 = 10315613) B10315613
theorem B18338867 : Blo 1981435 18338867 := bstep (se 1 (by rfl) ⟨13754150, by rfl⟩ : syracuseStep 18338867 = 27508301) B27508301
theorem B12225911 : Blo 1981435 12225911 := bstep (se 1 (by rfl) ⟨9169433, by rfl⟩ : syracuseStep 12225911 = 18338867) B18338867
theorem B32602429 : Blo 1981435 32602429 := bstep (se 3 (by rfl) ⟨6112955, by rfl⟩ : syracuseStep 32602429 = 12225911) B12225911
theorem B43469905 : Blo 1981435 43469905 := bstep (se 2 (by rfl) ⟨16301214, by rfl⟩ : syracuseStep 43469905 = 32602429) B32602429
theorem B57959873 : Blo 1981435 57959873 := bstep (se 2 (by rfl) ⟨21734952, by rfl⟩ : syracuseStep 57959873 = 43469905) B43469905
theorem B38639915 : Blo 1981435 38639915 := bstep (se 1 (by rfl) ⟨28979936, by rfl⟩ : syracuseStep 38639915 = 57959873) B57959873
theorem B25759943 : Blo 1981435 25759943 := bstep (se 1 (by rfl) ⟨19319957, by rfl⟩ : syracuseStep 25759943 = 38639915) B38639915
theorem B17173295 : Blo 1981435 17173295 := bstep (se 1 (by rfl) ⟨12879971, by rfl⟩ : syracuseStep 17173295 = 25759943) B25759943
theorem B11448863 : Blo 1981435 11448863 := bstep (se 1 (by rfl) ⟨8586647, by rfl⟩ : syracuseStep 11448863 = 17173295) B17173295
theorem B7632575 : Blo 1981435 7632575 := bstep (se 1 (by rfl) ⟨5724431, by rfl⟩ : syracuseStep 7632575 = 11448863) B11448863
theorem B5088383 : Blo 1981435 5088383 := bstep (se 1 (by rfl) ⟨3816287, by rfl⟩ : syracuseStep 5088383 = 7632575) B7632575
theorem B3392255 : Blo 1981435 3392255 := bstep (se 1 (by rfl) ⟨2544191, by rfl⟩ : syracuseStep 3392255 = 5088383) B5088383
theorem B9046013 : Blo 1981435 9046013 := bstep (se 3 (by rfl) ⟨1696127, by rfl⟩ : syracuseStep 9046013 = 3392255) B3392255
theorem B24122701 : Blo 1981435 24122701 := bstep (se 3 (by rfl) ⟨4523006, by rfl⟩ : syracuseStep 24122701 = 9046013) B9046013
theorem B32163601 : Blo 1981435 32163601 := bstep (se 2 (by rfl) ⟨12061350, by rfl⟩ : syracuseStep 32163601 = 24122701) B24122701
theorem B42884801 : Blo 1981435 42884801 := bstep (se 2 (by rfl) ⟨16081800, by rfl⟩ : syracuseStep 42884801 = 32163601) B32163601
theorem B28589867 : Blo 1981435 28589867 := bstep (se 1 (by rfl) ⟨21442400, by rfl⟩ : syracuseStep 28589867 = 42884801) B42884801
theorem B19059911 : Blo 1981435 19059911 := bstep (se 1 (by rfl) ⟨14294933, by rfl⟩ : syracuseStep 19059911 = 28589867) B28589867
theorem B12706607 : Blo 1981435 12706607 := bstep (se 1 (by rfl) ⟨9529955, by rfl⟩ : syracuseStep 12706607 = 19059911) B19059911
theorem B8471071 : Blo 1981435 8471071 := bstep (se 1 (by rfl) ⟨6353303, by rfl⟩ : syracuseStep 8471071 = 12706607) B12706607
theorem B11294761 : Blo 1981435 11294761 := bstep (se 2 (by rfl) ⟨4235535, by rfl⟩ : syracuseStep 11294761 = 8471071) B8471071
theorem B15059681 : Blo 1981435 15059681 := bstep (se 2 (by rfl) ⟨5647380, by rfl⟩ : syracuseStep 15059681 = 11294761) B11294761
theorem B10039787 : Blo 1981435 10039787 := bstep (se 1 (by rfl) ⟨7529840, by rfl⟩ : syracuseStep 10039787 = 15059681) B15059681
theorem B6693191 : Blo 1981435 6693191 := bstep (se 1 (by rfl) ⟨5019893, by rfl⟩ : syracuseStep 6693191 = 10039787) B10039787
theorem B4462127 : Blo 1981435 4462127 := bstep (se 1 (by rfl) ⟨3346595, by rfl⟩ : syracuseStep 4462127 = 6693191) B6693191
theorem B2974751 : Blo 1981435 2974751 := bstep (se 1 (by rfl) ⟨2231063, by rfl⟩ : syracuseStep 2974751 = 4462127) B4462127
theorem B1983167 : Blo 1981435 1983167 := bstep (se 1 (by rfl) ⟨1487375, by rfl⟩ : syracuseStep 1983167 = 2974751) B2974751
theorem B2974757 : Blo 1981435 2974757 := bbase (se 4 (by rfl) ⟨278883, by rfl⟩ : syracuseStep 2974757 = 557767) (by norm_num)
theorem B1983171 : Blo 1981435 1983171 := bstep (se 1 (by rfl) ⟨1487378, by rfl⟩ : syracuseStep 1983171 = 2974757) B2974757
theorem B2509957 : Blo 1981435 2509957 := bbase (se 4 (by rfl) ⟨235308, by rfl⟩ : syracuseStep 2509957 = 470617) (by norm_num)
theorem B3346609 : Blo 1981435 3346609 := bstep (se 2 (by rfl) ⟨1254978, by rfl⟩ : syracuseStep 3346609 = 2509957) B2509957
theorem B4462145 : Blo 1981435 4462145 := bstep (se 2 (by rfl) ⟨1673304, by rfl⟩ : syracuseStep 4462145 = 3346609) B3346609
theorem B2974763 : Blo 1981435 2974763 := bstep (se 1 (by rfl) ⟨2231072, by rfl⟩ : syracuseStep 2974763 = 4462145) B4462145
theorem B1983175 : Blo 1981435 1983175 := bstep (se 1 (by rfl) ⟨1487381, by rfl⟩ : syracuseStep 1983175 = 2974763) B2974763
theorem B2231077 : Blo 1981435 2231077 := bbase (se 4 (by rfl) ⟨209163, by rfl⟩ : syracuseStep 2231077 = 418327) (by norm_num)
theorem B2974769 : Blo 1981435 2974769 := bstep (se 2 (by rfl) ⟨1115538, by rfl⟩ : syracuseStep 2974769 = 2231077) B2231077
theorem B1983179 : Blo 1981435 1983179 := bstep (se 1 (by rfl) ⟨1487384, by rfl⟩ : syracuseStep 1983179 = 2974769) B2974769
theorem B8471141 : Blo 1981435 8471141 := bbase (se 4 (by rfl) ⟨794169, by rfl⟩ : syracuseStep 8471141 = 1588339) (by norm_num)
theorem B5647427 : Blo 1981435 5647427 := bstep (se 1 (by rfl) ⟨4235570, by rfl⟩ : syracuseStep 5647427 = 8471141) B8471141
theorem B3764951 : Blo 1981435 3764951 := bstep (se 1 (by rfl) ⟨2823713, by rfl⟩ : syracuseStep 3764951 = 5647427) B5647427
theorem B2509967 : Blo 1981435 2509967 := bstep (se 1 (by rfl) ⟨1882475, by rfl⟩ : syracuseStep 2509967 = 3764951) B3764951
theorem B6693245 : Blo 1981435 6693245 := bstep (se 3 (by rfl) ⟨1254983, by rfl⟩ : syracuseStep 6693245 = 2509967) B2509967
theorem B4462163 : Blo 1981435 4462163 := bstep (se 1 (by rfl) ⟨3346622, by rfl⟩ : syracuseStep 4462163 = 6693245) B6693245
theorem B2974775 : Blo 1981435 2974775 := bstep (se 1 (by rfl) ⟨2231081, by rfl⟩ : syracuseStep 2974775 = 4462163) B4462163
theorem B1983183 : Blo 1981435 1983183 := bstep (se 1 (by rfl) ⟨1487387, by rfl⟩ : syracuseStep 1983183 = 2974775) B2974775
theorem B2974781 : Blo 1981435 2974781 := bbase (se 3 (by rfl) ⟨557771, by rfl⟩ : syracuseStep 2974781 = 1115543) (by norm_num)
theorem B1983187 : Blo 1981435 1983187 := bstep (se 1 (by rfl) ⟨1487390, by rfl⟩ : syracuseStep 1983187 = 2974781) B2974781
theorem B4462181 : Blo 1981435 4462181 := bbase (se 4 (by rfl) ⟨418329, by rfl⟩ : syracuseStep 4462181 = 836659) (by norm_num)
theorem B2974787 : Blo 1981435 2974787 := bstep (se 1 (by rfl) ⟨2231090, by rfl⟩ : syracuseStep 2974787 = 4462181) B4462181
theorem B1983191 : Blo 1981435 1983191 := bstep (se 1 (by rfl) ⟨1487393, by rfl⟩ : syracuseStep 1983191 = 2974787) B2974787
theorem B5019965 : Blo 1981435 5019965 := bbase (se 3 (by rfl) ⟨941243, by rfl⟩ : syracuseStep 5019965 = 1882487) (by norm_num)
theorem B3346643 : Blo 1981435 3346643 := bstep (se 1 (by rfl) ⟨2509982, by rfl⟩ : syracuseStep 3346643 = 5019965) B5019965
theorem B2231095 : Blo 1981435 2231095 := bstep (se 1 (by rfl) ⟨1673321, by rfl⟩ : syracuseStep 2231095 = 3346643) B3346643
theorem B2974793 : Blo 1981435 2974793 := bstep (se 2 (by rfl) ⟨1115547, by rfl⟩ : syracuseStep 2974793 = 2231095) B2231095
theorem B1983195 : Blo 1981435 1983195 := bstep (se 1 (by rfl) ⟨1487396, by rfl⟩ : syracuseStep 1983195 = 2974793) B2974793
theorem B3764981 : Blo 1981435 3764981 := bbase (se 5 (by rfl) ⟨176483, by rfl⟩ : syracuseStep 3764981 = 352967) (by norm_num)
theorem B10039949 : Blo 1981435 10039949 := bstep (se 3 (by rfl) ⟨1882490, by rfl⟩ : syracuseStep 10039949 = 3764981) B3764981
theorem B6693299 : Blo 1981435 6693299 := bstep (se 1 (by rfl) ⟨5019974, by rfl⟩ : syracuseStep 6693299 = 10039949) B10039949
theorem B4462199 : Blo 1981435 4462199 := bstep (se 1 (by rfl) ⟨3346649, by rfl⟩ : syracuseStep 4462199 = 6693299) B6693299
theorem B2974799 : Blo 1981435 2974799 := bstep (se 1 (by rfl) ⟨2231099, by rfl⟩ : syracuseStep 2974799 = 4462199) B4462199
theorem B1983199 : Blo 1981435 1983199 := bstep (se 1 (by rfl) ⟨1487399, by rfl⟩ : syracuseStep 1983199 = 2974799) B2974799
theorem B2974805 : Blo 1981435 2974805 := bbase (se 8 (by rfl) ⟨17430, by rfl⟩ : syracuseStep 2974805 = 34861) (by norm_num)
theorem B1983203 : Blo 1981435 1983203 := bstep (se 1 (by rfl) ⟨1487402, by rfl⟩ : syracuseStep 1983203 = 2974805) B2974805
theorem B9530149 : Blo 1981435 9530149 := bbase (se 4 (by rfl) ⟨893451, by rfl⟩ : syracuseStep 9530149 = 1786903) (by norm_num)
theorem B12706865 : Blo 1981435 12706865 := bstep (se 2 (by rfl) ⟨4765074, by rfl⟩ : syracuseStep 12706865 = 9530149) B9530149
theorem B8471243 : Blo 1981435 8471243 := bstep (se 1 (by rfl) ⟨6353432, by rfl⟩ : syracuseStep 8471243 = 12706865) B12706865
theorem B5647495 : Blo 1981435 5647495 := bstep (se 1 (by rfl) ⟨4235621, by rfl⟩ : syracuseStep 5647495 = 8471243) B8471243
theorem B7529993 : Blo 1981435 7529993 := bstep (se 2 (by rfl) ⟨2823747, by rfl⟩ : syracuseStep 7529993 = 5647495) B5647495
theorem B5019995 : Blo 1981435 5019995 := bstep (se 1 (by rfl) ⟨3764996, by rfl⟩ : syracuseStep 5019995 = 7529993) B7529993
theorem B3346663 : Blo 1981435 3346663 := bstep (se 1 (by rfl) ⟨2509997, by rfl⟩ : syracuseStep 3346663 = 5019995) B5019995
theorem B4462217 : Blo 1981435 4462217 := bstep (se 2 (by rfl) ⟨1673331, by rfl⟩ : syracuseStep 4462217 = 3346663) B3346663
theorem B2974811 : Blo 1981435 2974811 := bstep (se 1 (by rfl) ⟨2231108, by rfl⟩ : syracuseStep 2974811 = 4462217) B4462217
theorem B1983207 : Blo 1981435 1983207 := bstep (se 1 (by rfl) ⟨1487405, by rfl⟩ : syracuseStep 1983207 = 2974811) B2974811
theorem B2231113 : Blo 1981435 2231113 := bbase (se 2 (by rfl) ⟨836667, by rfl⟩ : syracuseStep 2231113 = 1673335) (by norm_num)
theorem B2974817 : Blo 1981435 2974817 := bstep (se 2 (by rfl) ⟨1115556, by rfl⟩ : syracuseStep 2974817 = 2231113) B2231113
theorem B1983211 : Blo 1981435 1983211 := bstep (se 1 (by rfl) ⟨1487408, by rfl⟩ : syracuseStep 1983211 = 2974817) B2974817
theorem B19060373 : Blo 1981435 19060373 := bbase (se 6 (by rfl) ⟨446727, by rfl⟩ : syracuseStep 19060373 = 893455) (by norm_num)
theorem B12706915 : Blo 1981435 12706915 := bstep (se 1 (by rfl) ⟨9530186, by rfl⟩ : syracuseStep 12706915 = 19060373) B19060373
theorem B16942553 : Blo 1981435 16942553 := bstep (se 2 (by rfl) ⟨6353457, by rfl⟩ : syracuseStep 16942553 = 12706915) B12706915
theorem B11295035 : Blo 1981435 11295035 := bstep (se 1 (by rfl) ⟨8471276, by rfl⟩ : syracuseStep 11295035 = 16942553) B16942553
theorem B7530023 : Blo 1981435 7530023 := bstep (se 1 (by rfl) ⟨5647517, by rfl⟩ : syracuseStep 7530023 = 11295035) B11295035
theorem B5020015 : Blo 1981435 5020015 := bstep (se 1 (by rfl) ⟨3765011, by rfl⟩ : syracuseStep 5020015 = 7530023) B7530023
theorem B6693353 : Blo 1981435 6693353 := bstep (se 2 (by rfl) ⟨2510007, by rfl⟩ : syracuseStep 6693353 = 5020015) B5020015
theorem B4462235 : Blo 1981435 4462235 := bstep (se 1 (by rfl) ⟨3346676, by rfl⟩ : syracuseStep 4462235 = 6693353) B6693353
theorem B2974823 : Blo 1981435 2974823 := bstep (se 1 (by rfl) ⟨2231117, by rfl⟩ : syracuseStep 2974823 = 4462235) B4462235
theorem B1983215 : Blo 1981435 1983215 := bstep (se 1 (by rfl) ⟨1487411, by rfl⟩ : syracuseStep 1983215 = 2974823) B2974823
theorem B2974829 : Blo 1981435 2974829 := bbase (se 3 (by rfl) ⟨557780, by rfl⟩ : syracuseStep 2974829 = 1115561) (by norm_num)
theorem B1983219 : Blo 1981435 1983219 := bstep (se 1 (by rfl) ⟨1487414, by rfl⟩ : syracuseStep 1983219 = 2974829) B2974829
theorem B4462253 : Blo 1981435 4462253 := bbase (se 3 (by rfl) ⟨836672, by rfl⟩ : syracuseStep 4462253 = 1673345) (by norm_num)
theorem B2974835 : Blo 1981435 2974835 := bstep (se 1 (by rfl) ⟨2231126, by rfl⟩ : syracuseStep 2974835 = 4462253) B4462253
theorem B1983223 : Blo 1981435 1983223 := bstep (se 1 (by rfl) ⟨1487417, by rfl⟩ : syracuseStep 1983223 = 2974835) B2974835
theorem B3176749 : Blo 1981435 3176749 := bbase (se 3 (by rfl) ⟨595640, by rfl⟩ : syracuseStep 3176749 = 1191281) (by norm_num)
theorem B4235665 : Blo 1981435 4235665 := bstep (se 2 (by rfl) ⟨1588374, by rfl⟩ : syracuseStep 4235665 = 3176749) B3176749
theorem B5647553 : Blo 1981435 5647553 := bstep (se 2 (by rfl) ⟨2117832, by rfl⟩ : syracuseStep 5647553 = 4235665) B4235665
theorem B3765035 : Blo 1981435 3765035 := bstep (se 1 (by rfl) ⟨2823776, by rfl⟩ : syracuseStep 3765035 = 5647553) B5647553
theorem B2510023 : Blo 1981435 2510023 := bstep (se 1 (by rfl) ⟨1882517, by rfl⟩ : syracuseStep 2510023 = 3765035) B3765035
theorem B3346697 : Blo 1981435 3346697 := bstep (se 2 (by rfl) ⟨1255011, by rfl⟩ : syracuseStep 3346697 = 2510023) B2510023
theorem B2231131 : Blo 1981435 2231131 := bstep (se 1 (by rfl) ⟨1673348, by rfl⟩ : syracuseStep 2231131 = 3346697) B3346697
theorem B2974841 : Blo 1981435 2974841 := bstep (se 2 (by rfl) ⟨1115565, by rfl⟩ : syracuseStep 2974841 = 2231131) B2231131
theorem B1983227 : Blo 1981435 1983227 := bstep (se 1 (by rfl) ⟨1487420, by rfl⟩ : syracuseStep 1983227 = 2974841) B2974841
theorem B5360773 : Blo 1981435 5360773 := bbase (se 4 (by rfl) ⟨502572, by rfl⟩ : syracuseStep 5360773 = 1005145) (by norm_num)
theorem B7147697 : Blo 1981435 7147697 := bstep (se 2 (by rfl) ⟨2680386, by rfl⟩ : syracuseStep 7147697 = 5360773) B5360773
theorem B19060525 : Blo 1981435 19060525 := bstep (se 3 (by rfl) ⟨3573848, by rfl⟩ : syracuseStep 19060525 = 7147697) B7147697
theorem B25414033 : Blo 1981435 25414033 := bstep (se 2 (by rfl) ⟨9530262, by rfl⟩ : syracuseStep 25414033 = 19060525) B19060525
theorem B33885377 : Blo 1981435 33885377 := bstep (se 2 (by rfl) ⟨12707016, by rfl⟩ : syracuseStep 33885377 = 25414033) B25414033
theorem B22590251 : Blo 1981435 22590251 := bstep (se 1 (by rfl) ⟨16942688, by rfl⟩ : syracuseStep 22590251 = 33885377) B33885377
theorem B15060167 : Blo 1981435 15060167 := bstep (se 1 (by rfl) ⟨11295125, by rfl⟩ : syracuseStep 15060167 = 22590251) B22590251
theorem B10040111 : Blo 1981435 10040111 := bstep (se 1 (by rfl) ⟨7530083, by rfl⟩ : syracuseStep 10040111 = 15060167) B15060167
theorem B6693407 : Blo 1981435 6693407 := bstep (se 1 (by rfl) ⟨5020055, by rfl⟩ : syracuseStep 6693407 = 10040111) B10040111
theorem B4462271 : Blo 1981435 4462271 := bstep (se 1 (by rfl) ⟨3346703, by rfl⟩ : syracuseStep 4462271 = 6693407) B6693407
theorem B2974847 : Blo 1981435 2974847 := bstep (se 1 (by rfl) ⟨2231135, by rfl⟩ : syracuseStep 2974847 = 4462271) B4462271
theorem B1983231 : Blo 1981435 1983231 := bstep (se 1 (by rfl) ⟨1487423, by rfl⟩ : syracuseStep 1983231 = 2974847) B2974847
theorem B2974853 : Blo 1981435 2974853 := bbase (se 4 (by rfl) ⟨278892, by rfl⟩ : syracuseStep 2974853 = 557785) (by norm_num)
theorem B1983235 : Blo 1981435 1983235 := bstep (se 1 (by rfl) ⟨1487426, by rfl⟩ : syracuseStep 1983235 = 2974853) B2974853
theorem B3346717 : Blo 1981435 3346717 := bbase (se 3 (by rfl) ⟨627509, by rfl⟩ : syracuseStep 3346717 = 1255019) (by norm_num)
theorem B4462289 : Blo 1981435 4462289 := bstep (se 2 (by rfl) ⟨1673358, by rfl⟩ : syracuseStep 4462289 = 3346717) B3346717
theorem B2974859 : Blo 1981435 2974859 := bstep (se 1 (by rfl) ⟨2231144, by rfl⟩ : syracuseStep 2974859 = 4462289) B4462289
theorem B1983239 : Blo 1981435 1983239 := bstep (se 1 (by rfl) ⟨1487429, by rfl⟩ : syracuseStep 1983239 = 2974859) B2974859
theorem B2231149 : Blo 1981435 2231149 := bbase (se 3 (by rfl) ⟨418340, by rfl⟩ : syracuseStep 2231149 = 836681) (by norm_num)
theorem B2974865 : Blo 1981435 2974865 := bstep (se 2 (by rfl) ⟨1115574, by rfl⟩ : syracuseStep 2974865 = 2231149) B2231149
theorem B1983243 : Blo 1981435 1983243 := bstep (se 1 (by rfl) ⟨1487432, by rfl⟩ : syracuseStep 1983243 = 2974865) B2974865
theorem B6693461 : Blo 1981435 6693461 := bbase (se 8 (by rfl) ⟨39219, by rfl⟩ : syracuseStep 6693461 = 78439) (by norm_num)
theorem B4462307 : Blo 1981435 4462307 := bstep (se 1 (by rfl) ⟨3346730, by rfl⟩ : syracuseStep 4462307 = 6693461) B6693461
theorem B2974871 : Blo 1981435 2974871 := bstep (se 1 (by rfl) ⟨2231153, by rfl⟩ : syracuseStep 2974871 = 4462307) B4462307
theorem B1983247 : Blo 1981435 1983247 := bstep (se 1 (by rfl) ⟨1487435, by rfl⟩ : syracuseStep 1983247 = 2974871) B2974871
theorem B2974877 : Blo 1981435 2974877 := bbase (se 3 (by rfl) ⟨557789, by rfl⟩ : syracuseStep 2974877 = 1115579) (by norm_num)
theorem B1983251 : Blo 1981435 1983251 := bstep (se 1 (by rfl) ⟨1487438, by rfl⟩ : syracuseStep 1983251 = 2974877) B2974877
theorem B4462325 : Blo 1981435 4462325 := bbase (se 5 (by rfl) ⟨209171, by rfl⟩ : syracuseStep 4462325 = 418343) (by norm_num)
theorem B2974883 : Blo 1981435 2974883 := bstep (se 1 (by rfl) ⟨2231162, by rfl⟩ : syracuseStep 2974883 = 4462325) B4462325
theorem B1983255 : Blo 1981435 1983255 := bstep (se 1 (by rfl) ⟨1487441, by rfl⟩ : syracuseStep 1983255 = 2974883) B2974883
theorem B3264077 : Blo 1981435 3264077 := bbase (se 3 (by rfl) ⟨612014, by rfl⟩ : syracuseStep 3264077 = 1224029) (by norm_num)
theorem B8704205 : Blo 1981435 8704205 := bstep (se 3 (by rfl) ⟨1632038, by rfl⟩ : syracuseStep 8704205 = 3264077) B3264077
theorem B5802803 : Blo 1981435 5802803 := bstep (se 1 (by rfl) ⟨4352102, by rfl⟩ : syracuseStep 5802803 = 8704205) B8704205
theorem B3868535 : Blo 1981435 3868535 := bstep (se 1 (by rfl) ⟨2901401, by rfl⟩ : syracuseStep 3868535 = 5802803) B5802803
theorem B2579023 : Blo 1981435 2579023 := bstep (se 1 (by rfl) ⟨1934267, by rfl⟩ : syracuseStep 2579023 = 3868535) B3868535
theorem B3438697 : Blo 1981435 3438697 := bstep (se 2 (by rfl) ⟨1289511, by rfl⟩ : syracuseStep 3438697 = 2579023) B2579023
theorem B4584929 : Blo 1981435 4584929 := bstep (se 2 (by rfl) ⟨1719348, by rfl⟩ : syracuseStep 4584929 = 3438697) B3438697
theorem B48905909 : Blo 1981435 48905909 := bstep (se 5 (by rfl) ⟨2292464, by rfl⟩ : syracuseStep 48905909 = 4584929) B4584929
theorem B32603939 : Blo 1981435 32603939 := bstep (se 1 (by rfl) ⟨24452954, by rfl⟩ : syracuseStep 32603939 = 48905909) B48905909
theorem B21735959 : Blo 1981435 21735959 := bstep (se 1 (by rfl) ⟨16301969, by rfl⟩ : syracuseStep 21735959 = 32603939) B32603939
theorem B57962557 : Blo 1981435 57962557 := bstep (se 3 (by rfl) ⟨10867979, by rfl⟩ : syracuseStep 57962557 = 21735959) B21735959
theorem B77283409 : Blo 1981435 77283409 := bstep (se 2 (by rfl) ⟨28981278, by rfl⟩ : syracuseStep 77283409 = 57962557) B57962557
theorem B103044545 : Blo 1981435 103044545 := bstep (se 2 (by rfl) ⟨38641704, by rfl⟩ : syracuseStep 103044545 = 77283409) B77283409
theorem B68696363 : Blo 1981435 68696363 := bstep (se 1 (by rfl) ⟨51522272, by rfl⟩ : syracuseStep 68696363 = 103044545) B103044545
theorem B45797575 : Blo 1981435 45797575 := bstep (se 1 (by rfl) ⟨34348181, by rfl⟩ : syracuseStep 45797575 = 68696363) B68696363
theorem B61063433 : Blo 1981435 61063433 := bstep (se 2 (by rfl) ⟨22898787, by rfl⟩ : syracuseStep 61063433 = 45797575) B45797575
theorem B40708955 : Blo 1981435 40708955 := bstep (se 1 (by rfl) ⟨30531716, by rfl⟩ : syracuseStep 40708955 = 61063433) B61063433
theorem B27139303 : Blo 1981435 27139303 := bstep (se 1 (by rfl) ⟨20354477, by rfl⟩ : syracuseStep 27139303 = 40708955) B40708955
theorem B36185737 : Blo 1981435 36185737 := bstep (se 2 (by rfl) ⟨13569651, by rfl⟩ : syracuseStep 36185737 = 27139303) B27139303
theorem B48247649 : Blo 1981435 48247649 := bstep (se 2 (by rfl) ⟨18092868, by rfl⟩ : syracuseStep 48247649 = 36185737) B36185737
theorem B32165099 : Blo 1981435 32165099 := bstep (se 1 (by rfl) ⟨24123824, by rfl⟩ : syracuseStep 32165099 = 48247649) B48247649
theorem B21443399 : Blo 1981435 21443399 := bstep (se 1 (by rfl) ⟨16082549, by rfl⟩ : syracuseStep 21443399 = 32165099) B32165099
theorem B14295599 : Blo 1981435 14295599 := bstep (se 1 (by rfl) ⟨10721699, by rfl⟩ : syracuseStep 14295599 = 21443399) B21443399
theorem B9530399 : Blo 1981435 9530399 := bstep (se 1 (by rfl) ⟨7147799, by rfl⟩ : syracuseStep 9530399 = 14295599) B14295599
theorem B25414397 : Blo 1981435 25414397 := bstep (se 3 (by rfl) ⟨4765199, by rfl⟩ : syracuseStep 25414397 = 9530399) B9530399
theorem B16942931 : Blo 1981435 16942931 := bstep (se 1 (by rfl) ⟨12707198, by rfl⟩ : syracuseStep 16942931 = 25414397) B25414397
theorem B11295287 : Blo 1981435 11295287 := bstep (se 1 (by rfl) ⟨8471465, by rfl⟩ : syracuseStep 11295287 = 16942931) B16942931
theorem B7530191 : Blo 1981435 7530191 := bstep (se 1 (by rfl) ⟨5647643, by rfl⟩ : syracuseStep 7530191 = 11295287) B11295287
theorem B5020127 : Blo 1981435 5020127 := bstep (se 1 (by rfl) ⟨3765095, by rfl⟩ : syracuseStep 5020127 = 7530191) B7530191
theorem B3346751 : Blo 1981435 3346751 := bstep (se 1 (by rfl) ⟨2510063, by rfl⟩ : syracuseStep 3346751 = 5020127) B5020127
theorem B2231167 : Blo 1981435 2231167 := bstep (se 1 (by rfl) ⟨1673375, by rfl⟩ : syracuseStep 2231167 = 3346751) B3346751
theorem B2974889 : Blo 1981435 2974889 := bstep (se 2 (by rfl) ⟨1115583, by rfl⟩ : syracuseStep 2974889 = 2231167) B2231167
theorem B1983259 : Blo 1981435 1983259 := bstep (se 1 (by rfl) ⟨1487444, by rfl⟩ : syracuseStep 1983259 = 2974889) B2974889
theorem B4235741 : Blo 1981435 4235741 := bbase (se 3 (by rfl) ⟨794201, by rfl⟩ : syracuseStep 4235741 = 1588403) (by norm_num)
theorem B2823827 : Blo 1981435 2823827 := bstep (se 1 (by rfl) ⟨2117870, by rfl⟩ : syracuseStep 2823827 = 4235741) B4235741
theorem B7530205 : Blo 1981435 7530205 := bstep (se 3 (by rfl) ⟨1411913, by rfl⟩ : syracuseStep 7530205 = 2823827) B2823827
theorem B10040273 : Blo 1981435 10040273 := bstep (se 2 (by rfl) ⟨3765102, by rfl⟩ : syracuseStep 10040273 = 7530205) B7530205
theorem B6693515 : Blo 1981435 6693515 := bstep (se 1 (by rfl) ⟨5020136, by rfl⟩ : syracuseStep 6693515 = 10040273) B10040273
theorem B4462343 : Blo 1981435 4462343 := bstep (se 1 (by rfl) ⟨3346757, by rfl⟩ : syracuseStep 4462343 = 6693515) B6693515
theorem B2974895 : Blo 1981435 2974895 := bstep (se 1 (by rfl) ⟨2231171, by rfl⟩ : syracuseStep 2974895 = 4462343) B4462343
theorem B1983263 : Blo 1981435 1983263 := bstep (se 1 (by rfl) ⟨1487447, by rfl⟩ : syracuseStep 1983263 = 2974895) B2974895
theorem B2974901 : Blo 1981435 2974901 := bbase (se 5 (by rfl) ⟨139448, by rfl⟩ : syracuseStep 2974901 = 278897) (by norm_num)
theorem B1983267 : Blo 1981435 1983267 := bstep (se 1 (by rfl) ⟨1487450, by rfl⟩ : syracuseStep 1983267 = 2974901) B2974901
theorem B5020157 : Blo 1981435 5020157 := bbase (se 3 (by rfl) ⟨941279, by rfl⟩ : syracuseStep 5020157 = 1882559) (by norm_num)
theorem B3346771 : Blo 1981435 3346771 := bstep (se 1 (by rfl) ⟨2510078, by rfl⟩ : syracuseStep 3346771 = 5020157) B5020157
theorem B4462361 : Blo 1981435 4462361 := bstep (se 2 (by rfl) ⟨1673385, by rfl⟩ : syracuseStep 4462361 = 3346771) B3346771
theorem B2974907 : Blo 1981435 2974907 := bstep (se 1 (by rfl) ⟨2231180, by rfl⟩ : syracuseStep 2974907 = 4462361) B4462361
theorem B1983271 : Blo 1981435 1983271 := bstep (se 1 (by rfl) ⟨1487453, by rfl⟩ : syracuseStep 1983271 = 2974907) B2974907
theorem B2231185 : Blo 1981435 2231185 := bbase (se 2 (by rfl) ⟨836694, by rfl⟩ : syracuseStep 2231185 = 1673389) (by norm_num)
theorem B2974913 : Blo 1981435 2974913 := bstep (se 2 (by rfl) ⟨1115592, by rfl⟩ : syracuseStep 2974913 = 2231185) B2231185
theorem B1983275 : Blo 1981435 1983275 := bstep (se 1 (by rfl) ⟨1487456, by rfl⟩ : syracuseStep 1983275 = 2974913) B2974913
theorem B3765133 : Blo 1981435 3765133 := bbase (se 3 (by rfl) ⟨705962, by rfl⟩ : syracuseStep 3765133 = 1411925) (by norm_num)
theorem B5020177 : Blo 1981435 5020177 := bstep (se 2 (by rfl) ⟨1882566, by rfl⟩ : syracuseStep 5020177 = 3765133) B3765133
theorem B6693569 : Blo 1981435 6693569 := bstep (se 2 (by rfl) ⟨2510088, by rfl⟩ : syracuseStep 6693569 = 5020177) B5020177
theorem B4462379 : Blo 1981435 4462379 := bstep (se 1 (by rfl) ⟨3346784, by rfl⟩ : syracuseStep 4462379 = 6693569) B6693569
theorem B2974919 : Blo 1981435 2974919 := bstep (se 1 (by rfl) ⟨2231189, by rfl⟩ : syracuseStep 2974919 = 4462379) B4462379
theorem B1983279 : Blo 1981435 1983279 := bstep (se 1 (by rfl) ⟨1487459, by rfl⟩ : syracuseStep 1983279 = 2974919) B2974919
theorem B2974925 : Blo 1981435 2974925 := bbase (se 3 (by rfl) ⟨557798, by rfl⟩ : syracuseStep 2974925 = 1115597) (by norm_num)
theorem B1983283 : Blo 1981435 1983283 := bstep (se 1 (by rfl) ⟨1487462, by rfl⟩ : syracuseStep 1983283 = 2974925) B2974925
theorem B4462397 : Blo 1981435 4462397 := bbase (se 3 (by rfl) ⟨836699, by rfl⟩ : syracuseStep 4462397 = 1673399) (by norm_num)
theorem B2974931 : Blo 1981435 2974931 := bstep (se 1 (by rfl) ⟨2231198, by rfl⟩ : syracuseStep 2974931 = 4462397) B4462397
theorem B1983287 : Blo 1981435 1983287 := bstep (se 1 (by rfl) ⟨1487465, by rfl⟩ : syracuseStep 1983287 = 2974931) B2974931
theorem B3346805 : Blo 1981435 3346805 := bbase (se 5 (by rfl) ⟨156881, by rfl⟩ : syracuseStep 3346805 = 313763) (by norm_num)
theorem B2231203 : Blo 1981435 2231203 := bstep (se 1 (by rfl) ⟨1673402, by rfl⟩ : syracuseStep 2231203 = 3346805) B3346805
theorem B2974937 : Blo 1981435 2974937 := bstep (se 2 (by rfl) ⟨1115601, by rfl⟩ : syracuseStep 2974937 = 2231203) B2231203
theorem B1983291 : Blo 1981435 1983291 := bstep (se 1 (by rfl) ⟨1487468, by rfl⟩ : syracuseStep 1983291 = 2974937) B2974937
theorem B3573965 : Blo 1981435 3573965 := bbase (se 3 (by rfl) ⟨670118, by rfl⟩ : syracuseStep 3573965 = 1340237) (by norm_num)
theorem B2382643 : Blo 1981435 2382643 := bstep (se 1 (by rfl) ⟨1786982, by rfl⟩ : syracuseStep 2382643 = 3573965) B3573965
theorem B3176857 : Blo 1981435 3176857 := bstep (se 2 (by rfl) ⟨1191321, by rfl⟩ : syracuseStep 3176857 = 2382643) B2382643
theorem B4235809 : Blo 1981435 4235809 := bstep (se 2 (by rfl) ⟨1588428, by rfl⟩ : syracuseStep 4235809 = 3176857) B3176857
theorem B5647745 : Blo 1981435 5647745 := bstep (se 2 (by rfl) ⟨2117904, by rfl⟩ : syracuseStep 5647745 = 4235809) B4235809
theorem B15060653 : Blo 1981435 15060653 := bstep (se 3 (by rfl) ⟨2823872, by rfl⟩ : syracuseStep 15060653 = 5647745) B5647745
theorem B10040435 : Blo 1981435 10040435 := bstep (se 1 (by rfl) ⟨7530326, by rfl⟩ : syracuseStep 10040435 = 15060653) B15060653
theorem B6693623 : Blo 1981435 6693623 := bstep (se 1 (by rfl) ⟨5020217, by rfl⟩ : syracuseStep 6693623 = 10040435) B10040435
theorem B4462415 : Blo 1981435 4462415 := bstep (se 1 (by rfl) ⟨3346811, by rfl⟩ : syracuseStep 4462415 = 6693623) B6693623
theorem B2974943 : Blo 1981435 2974943 := bstep (se 1 (by rfl) ⟨2231207, by rfl⟩ : syracuseStep 2974943 = 4462415) B4462415
theorem B1983295 : Blo 1981435 1983295 := bstep (se 1 (by rfl) ⟨1487471, by rfl⟩ : syracuseStep 1983295 = 2974943) B2974943
theorem B2974949 : Blo 1981435 2974949 := bbase (se 4 (by rfl) ⟨278901, by rfl⟩ : syracuseStep 2974949 = 557803) (by norm_num)
theorem B1983299 : Blo 1981435 1983299 := bstep (se 1 (by rfl) ⟨1487474, by rfl⟩ : syracuseStep 1983299 = 2974949) B2974949
theorem B2382653 : Blo 1981435 2382653 := bbase (se 3 (by rfl) ⟨446747, by rfl⟩ : syracuseStep 2382653 = 893495) (by norm_num)
theorem B6353741 : Blo 1981435 6353741 := bstep (se 3 (by rfl) ⟨1191326, by rfl⟩ : syracuseStep 6353741 = 2382653) B2382653
theorem B4235827 : Blo 1981435 4235827 := bstep (se 1 (by rfl) ⟨3176870, by rfl⟩ : syracuseStep 4235827 = 6353741) B6353741
theorem B5647769 : Blo 1981435 5647769 := bstep (se 2 (by rfl) ⟨2117913, by rfl⟩ : syracuseStep 5647769 = 4235827) B4235827
theorem B3765179 : Blo 1981435 3765179 := bstep (se 1 (by rfl) ⟨2823884, by rfl⟩ : syracuseStep 3765179 = 5647769) B5647769
theorem B2510119 : Blo 1981435 2510119 := bstep (se 1 (by rfl) ⟨1882589, by rfl⟩ : syracuseStep 2510119 = 3765179) B3765179
theorem B3346825 : Blo 1981435 3346825 := bstep (se 2 (by rfl) ⟨1255059, by rfl⟩ : syracuseStep 3346825 = 2510119) B2510119
theorem B4462433 : Blo 1981435 4462433 := bstep (se 2 (by rfl) ⟨1673412, by rfl⟩ : syracuseStep 4462433 = 3346825) B3346825
theorem B2974955 : Blo 1981435 2974955 := bstep (se 1 (by rfl) ⟨2231216, by rfl⟩ : syracuseStep 2974955 = 4462433) B4462433
theorem B1983303 : Blo 1981435 1983303 := bstep (se 1 (by rfl) ⟨1487477, by rfl⟩ : syracuseStep 1983303 = 2974955) B2974955
theorem B2231221 : Blo 1981435 2231221 := bbase (se 5 (by rfl) ⟨104588, by rfl⟩ : syracuseStep 2231221 = 209177) (by norm_num)
theorem B2974961 : Blo 1981435 2974961 := bstep (se 2 (by rfl) ⟨1115610, by rfl⟩ : syracuseStep 2974961 = 2231221) B2231221
theorem B1983307 : Blo 1981435 1983307 := bstep (se 1 (by rfl) ⟨1487480, by rfl⟩ : syracuseStep 1983307 = 2974961) B2974961
theorem B2510129 : Blo 1981435 2510129 := bbase (se 2 (by rfl) ⟨941298, by rfl⟩ : syracuseStep 2510129 = 1882597) (by norm_num)
theorem B6693677 : Blo 1981435 6693677 := bstep (se 3 (by rfl) ⟨1255064, by rfl⟩ : syracuseStep 6693677 = 2510129) B2510129
theorem B4462451 : Blo 1981435 4462451 := bstep (se 1 (by rfl) ⟨3346838, by rfl⟩ : syracuseStep 4462451 = 6693677) B6693677
theorem B2974967 : Blo 1981435 2974967 := bstep (se 1 (by rfl) ⟨2231225, by rfl⟩ : syracuseStep 2974967 = 4462451) B4462451
theorem B1983311 : Blo 1981435 1983311 := bstep (se 1 (by rfl) ⟨1487483, by rfl⟩ : syracuseStep 1983311 = 2974967) B2974967
theorem B2974973 : Blo 1981435 2974973 := bbase (se 3 (by rfl) ⟨557807, by rfl⟩ : syracuseStep 2974973 = 1115615) (by norm_num)
theorem B1983315 : Blo 1981435 1983315 := bstep (se 1 (by rfl) ⟨1487486, by rfl⟩ : syracuseStep 1983315 = 2974973) B2974973
theorem B4462469 : Blo 1981435 4462469 := bbase (se 4 (by rfl) ⟨418356, by rfl⟩ : syracuseStep 4462469 = 836713) (by norm_num)
theorem B2974979 : Blo 1981435 2974979 := bstep (se 1 (by rfl) ⟨2231234, by rfl⟩ : syracuseStep 2974979 = 4462469) B4462469
theorem B1983319 : Blo 1981435 1983319 := bstep (se 1 (by rfl) ⟨1487489, by rfl⟩ : syracuseStep 1983319 = 2974979) B2974979
theorem B3392525 : Blo 1981435 3392525 := bbase (se 3 (by rfl) ⟨636098, by rfl⟩ : syracuseStep 3392525 = 1272197) (by norm_num)
theorem B2261683 : Blo 1981435 2261683 := bstep (se 1 (by rfl) ⟨1696262, by rfl⟩ : syracuseStep 2261683 = 3392525) B3392525
theorem B3015577 : Blo 1981435 3015577 := bstep (se 2 (by rfl) ⟨1130841, by rfl⟩ : syracuseStep 3015577 = 2261683) B2261683
theorem B4020769 : Blo 1981435 4020769 := bstep (se 2 (by rfl) ⟨1507788, by rfl⟩ : syracuseStep 4020769 = 3015577) B3015577
theorem B5361025 : Blo 1981435 5361025 := bstep (se 2 (by rfl) ⟨2010384, by rfl⟩ : syracuseStep 5361025 = 4020769) B4020769
theorem B7148033 : Blo 1981435 7148033 := bstep (se 2 (by rfl) ⟨2680512, by rfl⟩ : syracuseStep 7148033 = 5361025) B5361025
theorem B4765355 : Blo 1981435 4765355 := bstep (se 1 (by rfl) ⟨3574016, by rfl⟩ : syracuseStep 4765355 = 7148033) B7148033
theorem B3176903 : Blo 1981435 3176903 := bstep (se 1 (by rfl) ⟨2382677, by rfl⟩ : syracuseStep 3176903 = 4765355) B4765355
theorem B2117935 : Blo 1981435 2117935 := bstep (se 1 (by rfl) ⟨1588451, by rfl⟩ : syracuseStep 2117935 = 3176903) B3176903
theorem B2823913 : Blo 1981435 2823913 := bstep (se 2 (by rfl) ⟨1058967, by rfl⟩ : syracuseStep 2823913 = 2117935) B2117935
theorem B3765217 : Blo 1981435 3765217 := bstep (se 2 (by rfl) ⟨1411956, by rfl⟩ : syracuseStep 3765217 = 2823913) B2823913
theorem B5020289 : Blo 1981435 5020289 := bstep (se 2 (by rfl) ⟨1882608, by rfl⟩ : syracuseStep 5020289 = 3765217) B3765217
theorem B3346859 : Blo 1981435 3346859 := bstep (se 1 (by rfl) ⟨2510144, by rfl⟩ : syracuseStep 3346859 = 5020289) B5020289
theorem B2231239 : Blo 1981435 2231239 := bstep (se 1 (by rfl) ⟨1673429, by rfl⟩ : syracuseStep 2231239 = 3346859) B3346859
theorem B2974985 : Blo 1981435 2974985 := bstep (se 2 (by rfl) ⟨1115619, by rfl⟩ : syracuseStep 2974985 = 2231239) B2231239
theorem B1983323 : Blo 1981435 1983323 := bstep (se 1 (by rfl) ⟨1487492, by rfl⟩ : syracuseStep 1983323 = 2974985) B2974985
theorem B10040597 : Blo 1981435 10040597 := bbase (se 6 (by rfl) ⟨235326, by rfl⟩ : syracuseStep 10040597 = 470653) (by norm_num)
theorem B6693731 : Blo 1981435 6693731 := bstep (se 1 (by rfl) ⟨5020298, by rfl⟩ : syracuseStep 6693731 = 10040597) B10040597
theorem B4462487 : Blo 1981435 4462487 := bstep (se 1 (by rfl) ⟨3346865, by rfl⟩ : syracuseStep 4462487 = 6693731) B6693731
theorem B2974991 : Blo 1981435 2974991 := bstep (se 1 (by rfl) ⟨2231243, by rfl⟩ : syracuseStep 2974991 = 4462487) B4462487
theorem B1983327 : Blo 1981435 1983327 := bstep (se 1 (by rfl) ⟨1487495, by rfl⟩ : syracuseStep 1983327 = 2974991) B2974991
theorem B2974997 : Blo 1981435 2974997 := bbase (se 6 (by rfl) ⟨69726, by rfl⟩ : syracuseStep 2974997 = 139453) (by norm_num)
theorem B1983331 : Blo 1981435 1983331 := bstep (se 1 (by rfl) ⟨1487498, by rfl⟩ : syracuseStep 1983331 = 2974997) B2974997
theorem B17409077 : Blo 1981435 17409077 := bbase (se 5 (by rfl) ⟨816050, by rfl⟩ : syracuseStep 17409077 = 1632101) (by norm_num)
theorem B11606051 : Blo 1981435 11606051 := bstep (se 1 (by rfl) ⟨8704538, by rfl⟩ : syracuseStep 11606051 = 17409077) B17409077
theorem B7737367 : Blo 1981435 7737367 := bstep (se 1 (by rfl) ⟨5803025, by rfl⟩ : syracuseStep 7737367 = 11606051) B11606051
theorem B10316489 : Blo 1981435 10316489 := bstep (se 2 (by rfl) ⟨3868683, by rfl⟩ : syracuseStep 10316489 = 7737367) B7737367
theorem B110042549 : Blo 1981435 110042549 := bstep (se 5 (by rfl) ⟨5158244, by rfl⟩ : syracuseStep 110042549 = 10316489) B10316489
theorem B73361699 : Blo 1981435 73361699 := bstep (se 1 (by rfl) ⟨55021274, by rfl⟩ : syracuseStep 73361699 = 110042549) B110042549
theorem B48907799 : Blo 1981435 48907799 := bstep (se 1 (by rfl) ⟨36680849, by rfl⟩ : syracuseStep 48907799 = 73361699) B73361699
theorem B32605199 : Blo 1981435 32605199 := bstep (se 1 (by rfl) ⟨24453899, by rfl⟩ : syracuseStep 32605199 = 48907799) B48907799
theorem B21736799 : Blo 1981435 21736799 := bstep (se 1 (by rfl) ⟨16302599, by rfl⟩ : syracuseStep 21736799 = 32605199) B32605199
theorem B14491199 : Blo 1981435 14491199 := bstep (se 1 (by rfl) ⟨10868399, by rfl⟩ : syracuseStep 14491199 = 21736799) B21736799
theorem B9660799 : Blo 1981435 9660799 := bstep (se 1 (by rfl) ⟨7245599, by rfl⟩ : syracuseStep 9660799 = 14491199) B14491199
theorem B12881065 : Blo 1981435 12881065 := bstep (se 2 (by rfl) ⟨4830399, by rfl⟩ : syracuseStep 12881065 = 9660799) B9660799
theorem B17174753 : Blo 1981435 17174753 := bstep (se 2 (by rfl) ⟨6440532, by rfl⟩ : syracuseStep 17174753 = 12881065) B12881065
theorem B11449835 : Blo 1981435 11449835 := bstep (se 1 (by rfl) ⟨8587376, by rfl⟩ : syracuseStep 11449835 = 17174753) B17174753
theorem B7633223 : Blo 1981435 7633223 := bstep (se 1 (by rfl) ⟨5724917, by rfl⟩ : syracuseStep 7633223 = 11449835) B11449835
theorem B5088815 : Blo 1981435 5088815 := bstep (se 1 (by rfl) ⟨3816611, by rfl⟩ : syracuseStep 5088815 = 7633223) B7633223
theorem B3392543 : Blo 1981435 3392543 := bstep (se 1 (by rfl) ⟨2544407, by rfl⟩ : syracuseStep 3392543 = 5088815) B5088815
theorem B9046781 : Blo 1981435 9046781 := bstep (se 3 (by rfl) ⟨1696271, by rfl⟩ : syracuseStep 9046781 = 3392543) B3392543
theorem B6031187 : Blo 1981435 6031187 := bstep (se 1 (by rfl) ⟨4523390, by rfl⟩ : syracuseStep 6031187 = 9046781) B9046781
theorem B4020791 : Blo 1981435 4020791 := bstep (se 1 (by rfl) ⟨3015593, by rfl⟩ : syracuseStep 4020791 = 6031187) B6031187
theorem B42888437 : Blo 1981435 42888437 := bstep (se 5 (by rfl) ⟨2010395, by rfl⟩ : syracuseStep 42888437 = 4020791) B4020791
theorem B28592291 : Blo 1981435 28592291 := bstep (se 1 (by rfl) ⟨21444218, by rfl⟩ : syracuseStep 28592291 = 42888437) B42888437
theorem B19061527 : Blo 1981435 19061527 := bstep (se 1 (by rfl) ⟨14296145, by rfl⟩ : syracuseStep 19061527 = 28592291) B28592291
theorem B25415369 : Blo 1981435 25415369 := bstep (se 2 (by rfl) ⟨9530763, by rfl⟩ : syracuseStep 25415369 = 19061527) B19061527
theorem B16943579 : Blo 1981435 16943579 := bstep (se 1 (by rfl) ⟨12707684, by rfl⟩ : syracuseStep 16943579 = 25415369) B25415369
theorem B11295719 : Blo 1981435 11295719 := bstep (se 1 (by rfl) ⟨8471789, by rfl⟩ : syracuseStep 11295719 = 16943579) B16943579
theorem B7530479 : Blo 1981435 7530479 := bstep (se 1 (by rfl) ⟨5647859, by rfl⟩ : syracuseStep 7530479 = 11295719) B11295719
theorem B5020319 : Blo 1981435 5020319 := bstep (se 1 (by rfl) ⟨3765239, by rfl⟩ : syracuseStep 5020319 = 7530479) B7530479
theorem B3346879 : Blo 1981435 3346879 := bstep (se 1 (by rfl) ⟨2510159, by rfl⟩ : syracuseStep 3346879 = 5020319) B5020319
theorem B4462505 : Blo 1981435 4462505 := bstep (se 2 (by rfl) ⟨1673439, by rfl⟩ : syracuseStep 4462505 = 3346879) B3346879
theorem B2975003 : Blo 1981435 2975003 := bstep (se 1 (by rfl) ⟨2231252, by rfl⟩ : syracuseStep 2975003 = 4462505) B4462505
theorem B1983335 : Blo 1981435 1983335 := bstep (se 1 (by rfl) ⟨1487501, by rfl⟩ : syracuseStep 1983335 = 2975003) B2975003
theorem B2231257 : Blo 1981435 2231257 := bbase (se 2 (by rfl) ⟨836721, by rfl⟩ : syracuseStep 2231257 = 1673443) (by norm_num)
theorem B2975009 : Blo 1981435 2975009 := bstep (se 2 (by rfl) ⟨1115628, by rfl⟩ : syracuseStep 2975009 = 2231257) B2231257
theorem B1983339 : Blo 1981435 1983339 := bstep (se 1 (by rfl) ⟨1487504, by rfl⟩ : syracuseStep 1983339 = 2975009) B2975009
theorem B2823941 : Blo 1981435 2823941 := bbase (se 4 (by rfl) ⟨264744, by rfl⟩ : syracuseStep 2823941 = 529489) (by norm_num)
theorem B7530509 : Blo 1981435 7530509 := bstep (se 3 (by rfl) ⟨1411970, by rfl⟩ : syracuseStep 7530509 = 2823941) B2823941
theorem B5020339 : Blo 1981435 5020339 := bstep (se 1 (by rfl) ⟨3765254, by rfl⟩ : syracuseStep 5020339 = 7530509) B7530509
theorem B6693785 : Blo 1981435 6693785 := bstep (se 2 (by rfl) ⟨2510169, by rfl⟩ : syracuseStep 6693785 = 5020339) B5020339
theorem B4462523 : Blo 1981435 4462523 := bstep (se 1 (by rfl) ⟨3346892, by rfl⟩ : syracuseStep 4462523 = 6693785) B6693785
theorem B2975015 : Blo 1981435 2975015 := bstep (se 1 (by rfl) ⟨2231261, by rfl⟩ : syracuseStep 2975015 = 4462523) B4462523
theorem B1983343 : Blo 1981435 1983343 := bstep (se 1 (by rfl) ⟨1487507, by rfl⟩ : syracuseStep 1983343 = 2975015) B2975015
theorem B2975021 : Blo 1981435 2975021 := bbase (se 3 (by rfl) ⟨557816, by rfl⟩ : syracuseStep 2975021 = 1115633) (by norm_num)
theorem B1983347 : Blo 1981435 1983347 := bstep (se 1 (by rfl) ⟨1487510, by rfl⟩ : syracuseStep 1983347 = 2975021) B2975021
theorem B4462541 : Blo 1981435 4462541 := bbase (se 3 (by rfl) ⟨836726, by rfl⟩ : syracuseStep 4462541 = 1673453) (by norm_num)
theorem B2975027 : Blo 1981435 2975027 := bstep (se 1 (by rfl) ⟨2231270, by rfl⟩ : syracuseStep 2975027 = 4462541) B4462541
theorem B1983351 : Blo 1981435 1983351 := bstep (se 1 (by rfl) ⟨1487513, by rfl⟩ : syracuseStep 1983351 = 2975027) B2975027
theorem B2510185 : Blo 1981435 2510185 := bbase (se 2 (by rfl) ⟨941319, by rfl⟩ : syracuseStep 2510185 = 1882639) (by norm_num)
theorem B3346913 : Blo 1981435 3346913 := bstep (se 2 (by rfl) ⟨1255092, by rfl⟩ : syracuseStep 3346913 = 2510185) B2510185
theorem B2231275 : Blo 1981435 2231275 := bstep (se 1 (by rfl) ⟨1673456, by rfl⟩ : syracuseStep 2231275 = 3346913) B3346913
theorem B2975033 : Blo 1981435 2975033 := bstep (se 2 (by rfl) ⟨1115637, by rfl⟩ : syracuseStep 2975033 = 2231275) B2231275
theorem B1983355 : Blo 1981435 1983355 := bstep (se 1 (by rfl) ⟨1487516, by rfl⟩ : syracuseStep 1983355 = 2975033) B2975033
theorem B2448181 : Blo 1981435 2448181 := bbase (se 5 (by rfl) ⟨114758, by rfl⟩ : syracuseStep 2448181 = 229517) (by norm_num)
theorem B3264241 : Blo 1981435 3264241 := bstep (se 2 (by rfl) ⟨1224090, by rfl⟩ : syracuseStep 3264241 = 2448181) B2448181
theorem B4352321 : Blo 1981435 4352321 := bstep (se 2 (by rfl) ⟨1632120, by rfl⟩ : syracuseStep 4352321 = 3264241) B3264241
theorem B2901547 : Blo 1981435 2901547 := bstep (se 1 (by rfl) ⟨2176160, by rfl⟩ : syracuseStep 2901547 = 4352321) B4352321
theorem B3868729 : Blo 1981435 3868729 := bstep (se 2 (by rfl) ⟨1450773, by rfl⟩ : syracuseStep 3868729 = 2901547) B2901547
theorem B20633221 : Blo 1981435 20633221 := bstep (se 4 (by rfl) ⟨1934364, by rfl⟩ : syracuseStep 20633221 = 3868729) B3868729
theorem B27510961 : Blo 1981435 27510961 := bstep (se 2 (by rfl) ⟨10316610, by rfl⟩ : syracuseStep 27510961 = 20633221) B20633221
theorem B36681281 : Blo 1981435 36681281 := bstep (se 2 (by rfl) ⟨13755480, by rfl⟩ : syracuseStep 36681281 = 27510961) B27510961
theorem B24454187 : Blo 1981435 24454187 := bstep (se 1 (by rfl) ⟨18340640, by rfl⟩ : syracuseStep 24454187 = 36681281) B36681281
theorem B16302791 : Blo 1981435 16302791 := bstep (se 1 (by rfl) ⟨12227093, by rfl⟩ : syracuseStep 16302791 = 24454187) B24454187
theorem B10868527 : Blo 1981435 10868527 := bstep (se 1 (by rfl) ⟨8151395, by rfl⟩ : syracuseStep 10868527 = 16302791) B16302791
theorem B14491369 : Blo 1981435 14491369 := bstep (se 2 (by rfl) ⟨5434263, by rfl⟩ : syracuseStep 14491369 = 10868527) B10868527
theorem B19321825 : Blo 1981435 19321825 := bstep (se 2 (by rfl) ⟨7245684, by rfl⟩ : syracuseStep 19321825 = 14491369) B14491369
theorem B25762433 : Blo 1981435 25762433 := bstep (se 2 (by rfl) ⟨9660912, by rfl⟩ : syracuseStep 25762433 = 19321825) B19321825
theorem B68699821 : Blo 1981435 68699821 := bstep (se 3 (by rfl) ⟨12881216, by rfl⟩ : syracuseStep 68699821 = 25762433) B25762433
theorem B91599761 : Blo 1981435 91599761 := bstep (se 2 (by rfl) ⟨34349910, by rfl⟩ : syracuseStep 91599761 = 68699821) B68699821
theorem B61066507 : Blo 1981435 61066507 := bstep (se 1 (by rfl) ⟨45799880, by rfl⟩ : syracuseStep 61066507 = 91599761) B91599761
theorem B81422009 : Blo 1981435 81422009 := bstep (se 2 (by rfl) ⟨30533253, by rfl⟩ : syracuseStep 81422009 = 61066507) B61066507
theorem B54281339 : Blo 1981435 54281339 := bstep (se 1 (by rfl) ⟨40711004, by rfl⟩ : syracuseStep 54281339 = 81422009) B81422009
theorem B36187559 : Blo 1981435 36187559 := bstep (se 1 (by rfl) ⟨27140669, by rfl⟩ : syracuseStep 36187559 = 54281339) B54281339
theorem B24125039 : Blo 1981435 24125039 := bstep (se 1 (by rfl) ⟨18093779, by rfl⟩ : syracuseStep 24125039 = 36187559) B36187559
theorem B16083359 : Blo 1981435 16083359 := bstep (se 1 (by rfl) ⟨12062519, by rfl⟩ : syracuseStep 16083359 = 24125039) B24125039
theorem B10722239 : Blo 1981435 10722239 := bstep (se 1 (by rfl) ⟨8041679, by rfl⟩ : syracuseStep 10722239 = 16083359) B16083359
theorem B7148159 : Blo 1981435 7148159 := bstep (se 1 (by rfl) ⟨5361119, by rfl⟩ : syracuseStep 7148159 = 10722239) B10722239
theorem B4765439 : Blo 1981435 4765439 := bstep (se 1 (by rfl) ⟨3574079, by rfl⟩ : syracuseStep 4765439 = 7148159) B7148159
theorem B12707837 : Blo 1981435 12707837 := bstep (se 3 (by rfl) ⟨2382719, by rfl⟩ : syracuseStep 12707837 = 4765439) B4765439
theorem B8471891 : Blo 1981435 8471891 := bstep (se 1 (by rfl) ⟨6353918, by rfl⟩ : syracuseStep 8471891 = 12707837) B12707837
theorem B22591709 : Blo 1981435 22591709 := bstep (se 3 (by rfl) ⟨4235945, by rfl⟩ : syracuseStep 22591709 = 8471891) B8471891
theorem B15061139 : Blo 1981435 15061139 := bstep (se 1 (by rfl) ⟨11295854, by rfl⟩ : syracuseStep 15061139 = 22591709) B22591709
theorem B10040759 : Blo 1981435 10040759 := bstep (se 1 (by rfl) ⟨7530569, by rfl⟩ : syracuseStep 10040759 = 15061139) B15061139
theorem B6693839 : Blo 1981435 6693839 := bstep (se 1 (by rfl) ⟨5020379, by rfl⟩ : syracuseStep 6693839 = 10040759) B10040759
theorem B4462559 : Blo 1981435 4462559 := bstep (se 1 (by rfl) ⟨3346919, by rfl⟩ : syracuseStep 4462559 = 6693839) B6693839
theorem B2975039 : Blo 1981435 2975039 := bstep (se 1 (by rfl) ⟨2231279, by rfl⟩ : syracuseStep 2975039 = 4462559) B4462559
theorem B1983359 : Blo 1981435 1983359 := bstep (se 1 (by rfl) ⟨1487519, by rfl⟩ : syracuseStep 1983359 = 2975039) B2975039
theorem B2975045 : Blo 1981435 2975045 := bbase (se 4 (by rfl) ⟨278910, by rfl⟩ : syracuseStep 2975045 = 557821) (by norm_num)
theorem B1983363 : Blo 1981435 1983363 := bstep (se 1 (by rfl) ⟨1487522, by rfl⟩ : syracuseStep 1983363 = 2975045) B2975045
theorem B3346933 : Blo 1981435 3346933 := bbase (se 5 (by rfl) ⟨156887, by rfl⟩ : syracuseStep 3346933 = 313775) (by norm_num)
theorem B4462577 : Blo 1981435 4462577 := bstep (se 2 (by rfl) ⟨1673466, by rfl⟩ : syracuseStep 4462577 = 3346933) B3346933
theorem B2975051 : Blo 1981435 2975051 := bstep (se 1 (by rfl) ⟨2231288, by rfl⟩ : syracuseStep 2975051 = 4462577) B4462577
theorem B1983367 : Blo 1981435 1983367 := bstep (se 1 (by rfl) ⟨1487525, by rfl⟩ : syracuseStep 1983367 = 2975051) B2975051
theorem B2231293 : Blo 1981435 2231293 := bbase (se 3 (by rfl) ⟨418367, by rfl⟩ : syracuseStep 2231293 = 836735) (by norm_num)
theorem B2975057 : Blo 1981435 2975057 := bstep (se 2 (by rfl) ⟨1115646, by rfl⟩ : syracuseStep 2975057 = 2231293) B2231293
theorem B1983371 : Blo 1981435 1983371 := bstep (se 1 (by rfl) ⟨1487528, by rfl⟩ : syracuseStep 1983371 = 2975057) B2975057
theorem B6693893 : Blo 1981435 6693893 := bbase (se 4 (by rfl) ⟨627552, by rfl⟩ : syracuseStep 6693893 = 1255105) (by norm_num)
theorem B4462595 : Blo 1981435 4462595 := bstep (se 1 (by rfl) ⟨3346946, by rfl⟩ : syracuseStep 4462595 = 6693893) B6693893
theorem B2975063 : Blo 1981435 2975063 := bstep (se 1 (by rfl) ⟨2231297, by rfl⟩ : syracuseStep 2975063 = 4462595) B4462595
theorem B1983375 : Blo 1981435 1983375 := bstep (se 1 (by rfl) ⟨1487531, by rfl⟩ : syracuseStep 1983375 = 2975063) B2975063
theorem B2975069 : Blo 1981435 2975069 := bbase (se 3 (by rfl) ⟨557825, by rfl⟩ : syracuseStep 2975069 = 1115651) (by norm_num)
theorem B1983379 : Blo 1981435 1983379 := bstep (se 1 (by rfl) ⟨1487534, by rfl⟩ : syracuseStep 1983379 = 2975069) B2975069
theorem B4462613 : Blo 1981435 4462613 := bbase (se 6 (by rfl) ⟨104592, by rfl⟩ : syracuseStep 4462613 = 209185) (by norm_num)
theorem B2975075 : Blo 1981435 2975075 := bstep (se 1 (by rfl) ⟨2231306, by rfl⟩ : syracuseStep 2975075 = 4462613) B4462613
theorem B1983383 : Blo 1981435 1983383 := bstep (se 1 (by rfl) ⟨1487537, by rfl⟩ : syracuseStep 1983383 = 2975075) B2975075
theorem B7530677 : Blo 1981435 7530677 := bbase (se 5 (by rfl) ⟨353000, by rfl⟩ : syracuseStep 7530677 = 706001) (by norm_num)
theorem B5020451 : Blo 1981435 5020451 := bstep (se 1 (by rfl) ⟨3765338, by rfl⟩ : syracuseStep 5020451 = 7530677) B7530677
theorem B3346967 : Blo 1981435 3346967 := bstep (se 1 (by rfl) ⟨2510225, by rfl⟩ : syracuseStep 3346967 = 5020451) B5020451
theorem B2231311 : Blo 1981435 2231311 := bstep (se 1 (by rfl) ⟨1673483, by rfl⟩ : syracuseStep 2231311 = 3346967) B3346967
theorem B2975081 : Blo 1981435 2975081 := bstep (se 2 (by rfl) ⟨1115655, by rfl⟩ : syracuseStep 2975081 = 2231311) B2231311
theorem B1983387 : Blo 1981435 1983387 := bstep (se 1 (by rfl) ⟨1487540, by rfl⟩ : syracuseStep 1983387 = 2975081) B2975081
theorem B4765517 : Blo 1981435 4765517 := bbase (se 3 (by rfl) ⟨893534, by rfl⟩ : syracuseStep 4765517 = 1787069) (by norm_num)
theorem B3177011 : Blo 1981435 3177011 := bstep (se 1 (by rfl) ⟨2382758, by rfl⟩ : syracuseStep 3177011 = 4765517) B4765517
theorem B2118007 : Blo 1981435 2118007 := bstep (se 1 (by rfl) ⟨1588505, by rfl⟩ : syracuseStep 2118007 = 3177011) B3177011
theorem B11296037 : Blo 1981435 11296037 := bstep (se 4 (by rfl) ⟨1059003, by rfl⟩ : syracuseStep 11296037 = 2118007) B2118007
theorem B7530691 : Blo 1981435 7530691 := bstep (se 1 (by rfl) ⟨5648018, by rfl⟩ : syracuseStep 7530691 = 11296037) B11296037
theorem B10040921 : Blo 1981435 10040921 := bstep (se 2 (by rfl) ⟨3765345, by rfl⟩ : syracuseStep 10040921 = 7530691) B7530691
theorem B6693947 : Blo 1981435 6693947 := bstep (se 1 (by rfl) ⟨5020460, by rfl⟩ : syracuseStep 6693947 = 10040921) B10040921
theorem B4462631 : Blo 1981435 4462631 := bstep (se 1 (by rfl) ⟨3346973, by rfl⟩ : syracuseStep 4462631 = 6693947) B6693947
theorem B2975087 : Blo 1981435 2975087 := bstep (se 1 (by rfl) ⟨2231315, by rfl⟩ : syracuseStep 2975087 = 4462631) B4462631
theorem B1983391 : Blo 1981435 1983391 := bstep (se 1 (by rfl) ⟨1487543, by rfl⟩ : syracuseStep 1983391 = 2975087) B2975087
theorem B2975093 : Blo 1981435 2975093 := bbase (se 5 (by rfl) ⟨139457, by rfl⟩ : syracuseStep 2975093 = 278915) (by norm_num)
theorem B1983395 : Blo 1981435 1983395 := bstep (se 1 (by rfl) ⟨1487546, by rfl⟩ : syracuseStep 1983395 = 2975093) B2975093
theorem B2824021 : Blo 1981435 2824021 := bbase (se 9 (by rfl) ⟨8273, by rfl⟩ : syracuseStep 2824021 = 16547) (by norm_num)
theorem B3765361 : Blo 1981435 3765361 := bstep (se 2 (by rfl) ⟨1412010, by rfl⟩ : syracuseStep 3765361 = 2824021) B2824021
theorem B5020481 : Blo 1981435 5020481 := bstep (se 2 (by rfl) ⟨1882680, by rfl⟩ : syracuseStep 5020481 = 3765361) B3765361
theorem B3346987 : Blo 1981435 3346987 := bstep (se 1 (by rfl) ⟨2510240, by rfl⟩ : syracuseStep 3346987 = 5020481) B5020481
theorem B4462649 : Blo 1981435 4462649 := bstep (se 2 (by rfl) ⟨1673493, by rfl⟩ : syracuseStep 4462649 = 3346987) B3346987
theorem B2975099 : Blo 1981435 2975099 := bstep (se 1 (by rfl) ⟨2231324, by rfl⟩ : syracuseStep 2975099 = 4462649) B4462649
theorem B1983399 : Blo 1981435 1983399 := bstep (se 1 (by rfl) ⟨1487549, by rfl⟩ : syracuseStep 1983399 = 2975099) B2975099
theorem B2231329 : Blo 1981435 2231329 := bbase (se 2 (by rfl) ⟨836748, by rfl⟩ : syracuseStep 2231329 = 1673497) (by norm_num)
theorem B2975105 : Blo 1981435 2975105 := bstep (se 2 (by rfl) ⟨1115664, by rfl⟩ : syracuseStep 2975105 = 2231329) B2231329
theorem B1983403 : Blo 1981435 1983403 := bstep (se 1 (by rfl) ⟨1487552, by rfl⟩ : syracuseStep 1983403 = 2975105) B2975105
theorem B5020501 : Blo 1981435 5020501 := bbase (se 9 (by rfl) ⟨14708, by rfl⟩ : syracuseStep 5020501 = 29417) (by norm_num)
theorem B6694001 : Blo 1981435 6694001 := bstep (se 2 (by rfl) ⟨2510250, by rfl⟩ : syracuseStep 6694001 = 5020501) B5020501
theorem B4462667 : Blo 1981435 4462667 := bstep (se 1 (by rfl) ⟨3347000, by rfl⟩ : syracuseStep 4462667 = 6694001) B6694001
theorem B2975111 : Blo 1981435 2975111 := bstep (se 1 (by rfl) ⟨2231333, by rfl⟩ : syracuseStep 2975111 = 4462667) B4462667
theorem B1983407 : Blo 1981435 1983407 := bstep (se 1 (by rfl) ⟨1487555, by rfl⟩ : syracuseStep 1983407 = 2975111) B2975111
theorem B2975117 : Blo 1981435 2975117 := bbase (se 3 (by rfl) ⟨557834, by rfl⟩ : syracuseStep 2975117 = 1115669) (by norm_num)
theorem B1983411 : Blo 1981435 1983411 := bstep (se 1 (by rfl) ⟨1487558, by rfl⟩ : syracuseStep 1983411 = 2975117) B2975117
theorem B4462685 : Blo 1981435 4462685 := bbase (se 3 (by rfl) ⟨836753, by rfl⟩ : syracuseStep 4462685 = 1673507) (by norm_num)
theorem B2975123 : Blo 1981435 2975123 := bstep (se 1 (by rfl) ⟨2231342, by rfl⟩ : syracuseStep 2975123 = 4462685) B4462685
theorem B1983415 : Blo 1981435 1983415 := bstep (se 1 (by rfl) ⟨1487561, by rfl⟩ : syracuseStep 1983415 = 2975123) B2975123
theorem B3347021 : Blo 1981435 3347021 := bbase (se 3 (by rfl) ⟨627566, by rfl⟩ : syracuseStep 3347021 = 1255133) (by norm_num)
theorem B2231347 : Blo 1981435 2231347 := bstep (se 1 (by rfl) ⟨1673510, by rfl⟩ : syracuseStep 2231347 = 3347021) B3347021
theorem B2975129 : Blo 1981435 2975129 := bstep (se 2 (by rfl) ⟨1115673, by rfl⟩ : syracuseStep 2975129 = 2231347) B2231347
theorem B1983419 : Blo 1981435 1983419 := bstep (se 1 (by rfl) ⟨1487564, by rfl⟩ : syracuseStep 1983419 = 2975129) B2975129
theorem B28593557 : Blo 1981435 28593557 := bbase (se 6 (by rfl) ⟨670161, by rfl⟩ : syracuseStep 28593557 = 1340323) (by norm_num)
theorem B19062371 : Blo 1981435 19062371 := bstep (se 1 (by rfl) ⟨14296778, by rfl⟩ : syracuseStep 19062371 = 28593557) B28593557
theorem B12708247 : Blo 1981435 12708247 := bstep (se 1 (by rfl) ⟨9531185, by rfl⟩ : syracuseStep 12708247 = 19062371) B19062371
theorem B16944329 : Blo 1981435 16944329 := bstep (se 2 (by rfl) ⟨6354123, by rfl⟩ : syracuseStep 16944329 = 12708247) B12708247
theorem B11296219 : Blo 1981435 11296219 := bstep (se 1 (by rfl) ⟨8472164, by rfl⟩ : syracuseStep 11296219 = 16944329) B16944329
theorem B15061625 : Blo 1981435 15061625 := bstep (se 2 (by rfl) ⟨5648109, by rfl⟩ : syracuseStep 15061625 = 11296219) B11296219
theorem B10041083 : Blo 1981435 10041083 := bstep (se 1 (by rfl) ⟨7530812, by rfl⟩ : syracuseStep 10041083 = 15061625) B15061625
theorem B6694055 : Blo 1981435 6694055 := bstep (se 1 (by rfl) ⟨5020541, by rfl⟩ : syracuseStep 6694055 = 10041083) B10041083
theorem B4462703 : Blo 1981435 4462703 := bstep (se 1 (by rfl) ⟨3347027, by rfl⟩ : syracuseStep 4462703 = 6694055) B6694055
theorem B2975135 : Blo 1981435 2975135 := bstep (se 1 (by rfl) ⟨2231351, by rfl⟩ : syracuseStep 2975135 = 4462703) B4462703
theorem B1983423 : Blo 1981435 1983423 := bstep (se 1 (by rfl) ⟨1487567, by rfl⟩ : syracuseStep 1983423 = 2975135) B2975135
theorem B2975141 : Blo 1981435 2975141 := bbase (se 4 (by rfl) ⟨278919, by rfl⟩ : syracuseStep 2975141 = 557839) (by norm_num)
theorem B1983427 : Blo 1981435 1983427 := bstep (se 1 (by rfl) ⟨1487570, by rfl⟩ : syracuseStep 1983427 = 2975141) B2975141
theorem B2510281 : Blo 1981435 2510281 := bbase (se 2 (by rfl) ⟨941355, by rfl⟩ : syracuseStep 2510281 = 1882711) (by norm_num)
theorem B3347041 : Blo 1981435 3347041 := bstep (se 2 (by rfl) ⟨1255140, by rfl⟩ : syracuseStep 3347041 = 2510281) B2510281
theorem B4462721 : Blo 1981435 4462721 := bstep (se 2 (by rfl) ⟨1673520, by rfl⟩ : syracuseStep 4462721 = 3347041) B3347041
theorem B2975147 : Blo 1981435 2975147 := bstep (se 1 (by rfl) ⟨2231360, by rfl⟩ : syracuseStep 2975147 = 4462721) B4462721
theorem B1983431 : Blo 1981435 1983431 := bstep (se 1 (by rfl) ⟨1487573, by rfl⟩ : syracuseStep 1983431 = 2975147) B2975147
theorem B2231365 : Blo 1981435 2231365 := bbase (se 4 (by rfl) ⟨209190, by rfl⟩ : syracuseStep 2231365 = 418381) (by norm_num)
theorem B2975153 : Blo 1981435 2975153 := bstep (se 2 (by rfl) ⟨1115682, by rfl⟩ : syracuseStep 2975153 = 2231365) B2231365
theorem B1983435 : Blo 1981435 1983435 := bstep (se 1 (by rfl) ⟨1487576, by rfl⟩ : syracuseStep 1983435 = 2975153) B2975153
theorem C0 (j : ℕ) (h1 : 495358 ≤ j) (h2 : j ≤ 495858) : Blo 1981435 (4 * j + 3) := by
  interval_cases j
  · exact B1981435
  · exact B1981439
  · exact B1981443
  · exact B1981447
  · exact B1981451
  · exact B1981455
  · exact B1981459
  · exact B1981463
  · exact B1981467
  · exact B1981471
  · exact B1981475
  · exact B1981479
  · exact B1981483
  · exact B1981487
  · exact B1981491
  · exact B1981495
  · exact B1981499
  · exact B1981503
  · exact B1981507
  · exact B1981511
  · exact B1981515
  · exact B1981519
  · exact B1981523
  · exact B1981527
  · exact B1981531
  · exact B1981535
  · exact B1981539
  · exact B1981543
  · exact B1981547
  · exact B1981551
  · exact B1981555
  · exact B1981559
  · exact B1981563
  · exact B1981567
  · exact B1981571
  · exact B1981575
  · exact B1981579
  · exact B1981583
  · exact B1981587
  · exact B1981591
  · exact B1981595
  · exact B1981599
  · exact B1981603
  · exact B1981607
  · exact B1981611
  · exact B1981615
  · exact B1981619
  · exact B1981623
  · exact B1981627
  · exact B1981631
  · exact B1981635
  · exact B1981639
  · exact B1981643
  · exact B1981647
  · exact B1981651
  · exact B1981655
  · exact B1981659
  · exact B1981663
  · exact B1981667
  · exact B1981671
  · exact B1981675
  · exact B1981679
  · exact B1981683
  · exact B1981687
  · exact B1981691
  · exact B1981695
  · exact B1981699
  · exact B1981703
  · exact B1981707
  · exact B1981711
  · exact B1981715
  · exact B1981719
  · exact B1981723
  · exact B1981727
  · exact B1981731
  · exact B1981735
  · exact B1981739
  · exact B1981743
  · exact B1981747
  · exact B1981751
  · exact B1981755
  · exact B1981759
  · exact B1981763
  · exact B1981767
  · exact B1981771
  · exact B1981775
  · exact B1981779
  · exact B1981783
  · exact B1981787
  · exact B1981791
  · exact B1981795
  · exact B1981799
  · exact B1981803
  · exact B1981807
  · exact B1981811
  · exact B1981815
  · exact B1981819
  · exact B1981823
  · exact B1981827
  · exact B1981831
  · exact B1981835
  · exact B1981839
  · exact B1981843
  · exact B1981847
  · exact B1981851
  · exact B1981855
  · exact B1981859
  · exact B1981863
  · exact B1981867
  · exact B1981871
  · exact B1981875
  · exact B1981879
  · exact B1981883
  · exact B1981887
  · exact B1981891
  · exact B1981895
  · exact B1981899
  · exact B1981903
  · exact B1981907
  · exact B1981911
  · exact B1981915
  · exact B1981919
  · exact B1981923
  · exact B1981927
  · exact B1981931
  · exact B1981935
  · exact B1981939
  · exact B1981943
  · exact B1981947
  · exact B1981951
  · exact B1981955
  · exact B1981959
  · exact B1981963
  · exact B1981967
  · exact B1981971
  · exact B1981975
  · exact B1981979
  · exact B1981983
  · exact B1981987
  · exact B1981991
  · exact B1981995
  · exact B1981999
  · exact B1982003
  · exact B1982007
  · exact B1982011
  · exact B1982015
  · exact B1982019
  · exact B1982023
  · exact B1982027
  · exact B1982031
  · exact B1982035
  · exact B1982039
  · exact B1982043
  · exact B1982047
  · exact B1982051
  · exact B1982055
  · exact B1982059
  · exact B1982063
  · exact B1982067
  · exact B1982071
  · exact B1982075
  · exact B1982079
  · exact B1982083
  · exact B1982087
  · exact B1982091
  · exact B1982095
  · exact B1982099
  · exact B1982103
  · exact B1982107
  · exact B1982111
  · exact B1982115
  · exact B1982119
  · exact B1982123
  · exact B1982127
  · exact B1982131
  · exact B1982135
  · exact B1982139
  · exact B1982143
  · exact B1982147
  · exact B1982151
  · exact B1982155
  · exact B1982159
  · exact B1982163
  · exact B1982167
  · exact B1982171
  · exact B1982175
  · exact B1982179
  · exact B1982183
  · exact B1982187
  · exact B1982191
  · exact B1982195
  · exact B1982199
  · exact B1982203
  · exact B1982207
  · exact B1982211
  · exact B1982215
  · exact B1982219
  · exact B1982223
  · exact B1982227
  · exact B1982231
  · exact B1982235
  · exact B1982239
  · exact B1982243
  · exact B1982247
  · exact B1982251
  · exact B1982255
  · exact B1982259
  · exact B1982263
  · exact B1982267
  · exact B1982271
  · exact B1982275
  · exact B1982279
  · exact B1982283
  · exact B1982287
  · exact B1982291
  · exact B1982295
  · exact B1982299
  · exact B1982303
  · exact B1982307
  · exact B1982311
  · exact B1982315
  · exact B1982319
  · exact B1982323
  · exact B1982327
  · exact B1982331
  · exact B1982335
  · exact B1982339
  · exact B1982343
  · exact B1982347
  · exact B1982351
  · exact B1982355
  · exact B1982359
  · exact B1982363
  · exact B1982367
  · exact B1982371
  · exact B1982375
  · exact B1982379
  · exact B1982383
  · exact B1982387
  · exact B1982391
  · exact B1982395
  · exact B1982399
  · exact B1982403
  · exact B1982407
  · exact B1982411
  · exact B1982415
  · exact B1982419
  · exact B1982423
  · exact B1982427
  · exact B1982431
  · exact B1982435
  · exact B1982439
  · exact B1982443
  · exact B1982447
  · exact B1982451
  · exact B1982455
  · exact B1982459
  · exact B1982463
  · exact B1982467
  · exact B1982471
  · exact B1982475
  · exact B1982479
  · exact B1982483
  · exact B1982487
  · exact B1982491
  · exact B1982495
  · exact B1982499
  · exact B1982503
  · exact B1982507
  · exact B1982511
  · exact B1982515
  · exact B1982519
  · exact B1982523
  · exact B1982527
  · exact B1982531
  · exact B1982535
  · exact B1982539
  · exact B1982543
  · exact B1982547
  · exact B1982551
  · exact B1982555
  · exact B1982559
  · exact B1982563
  · exact B1982567
  · exact B1982571
  · exact B1982575
  · exact B1982579
  · exact B1982583
  · exact B1982587
  · exact B1982591
  · exact B1982595
  · exact B1982599
  · exact B1982603
  · exact B1982607
  · exact B1982611
  · exact B1982615
  · exact B1982619
  · exact B1982623
  · exact B1982627
  · exact B1982631
  · exact B1982635
  · exact B1982639
  · exact B1982643
  · exact B1982647
  · exact B1982651
  · exact B1982655
  · exact B1982659
  · exact B1982663
  · exact B1982667
  · exact B1982671
  · exact B1982675
  · exact B1982679
  · exact B1982683
  · exact B1982687
  · exact B1982691
  · exact B1982695
  · exact B1982699
  · exact B1982703
  · exact B1982707
  · exact B1982711
  · exact B1982715
  · exact B1982719
  · exact B1982723
  · exact B1982727
  · exact B1982731
  · exact B1982735
  · exact B1982739
  · exact B1982743
  · exact B1982747
  · exact B1982751
  · exact B1982755
  · exact B1982759
  · exact B1982763
  · exact B1982767
  · exact B1982771
  · exact B1982775
  · exact B1982779
  · exact B1982783
  · exact B1982787
  · exact B1982791
  · exact B1982795
  · exact B1982799
  · exact B1982803
  · exact B1982807
  · exact B1982811
  · exact B1982815
  · exact B1982819
  · exact B1982823
  · exact B1982827
  · exact B1982831
  · exact B1982835
  · exact B1982839
  · exact B1982843
  · exact B1982847
  · exact B1982851
  · exact B1982855
  · exact B1982859
  · exact B1982863
  · exact B1982867
  · exact B1982871
  · exact B1982875
  · exact B1982879
  · exact B1982883
  · exact B1982887
  · exact B1982891
  · exact B1982895
  · exact B1982899
  · exact B1982903
  · exact B1982907
  · exact B1982911
  · exact B1982915
  · exact B1982919
  · exact B1982923
  · exact B1982927
  · exact B1982931
  · exact B1982935
  · exact B1982939
  · exact B1982943
  · exact B1982947
  · exact B1982951
  · exact B1982955
  · exact B1982959
  · exact B1982963
  · exact B1982967
  · exact B1982971
  · exact B1982975
  · exact B1982979
  · exact B1982983
  · exact B1982987
  · exact B1982991
  · exact B1982995
  · exact B1982999
  · exact B1983003
  · exact B1983007
  · exact B1983011
  · exact B1983015
  · exact B1983019
  · exact B1983023
  · exact B1983027
  · exact B1983031
  · exact B1983035
  · exact B1983039
  · exact B1983043
  · exact B1983047
  · exact B1983051
  · exact B1983055
  · exact B1983059
  · exact B1983063
  · exact B1983067
  · exact B1983071
  · exact B1983075
  · exact B1983079
  · exact B1983083
  · exact B1983087
  · exact B1983091
  · exact B1983095
  · exact B1983099
  · exact B1983103
  · exact B1983107
  · exact B1983111
  · exact B1983115
  · exact B1983119
  · exact B1983123
  · exact B1983127
  · exact B1983131
  · exact B1983135
  · exact B1983139
  · exact B1983143
  · exact B1983147
  · exact B1983151
  · exact B1983155
  · exact B1983159
  · exact B1983163
  · exact B1983167
  · exact B1983171
  · exact B1983175
  · exact B1983179
  · exact B1983183
  · exact B1983187
  · exact B1983191
  · exact B1983195
  · exact B1983199
  · exact B1983203
  · exact B1983207
  · exact B1983211
  · exact B1983215
  · exact B1983219
  · exact B1983223
  · exact B1983227
  · exact B1983231
  · exact B1983235
  · exact B1983239
  · exact B1983243
  · exact B1983247
  · exact B1983251
  · exact B1983255
  · exact B1983259
  · exact B1983263
  · exact B1983267
  · exact B1983271
  · exact B1983275
  · exact B1983279
  · exact B1983283
  · exact B1983287
  · exact B1983291
  · exact B1983295
  · exact B1983299
  · exact B1983303
  · exact B1983307
  · exact B1983311
  · exact B1983315
  · exact B1983319
  · exact B1983323
  · exact B1983327
  · exact B1983331
  · exact B1983335
  · exact B1983339
  · exact B1983343
  · exact B1983347
  · exact B1983351
  · exact B1983355
  · exact B1983359
  · exact B1983363
  · exact B1983367
  · exact B1983371
  · exact B1983375
  · exact B1983379
  · exact B1983383
  · exact B1983387
  · exact B1983391
  · exact B1983395
  · exact B1983399
  · exact B1983403
  · exact B1983407
  · exact B1983411
  · exact B1983415
  · exact B1983419
  · exact B1983423
  · exact B1983427
  · exact B1983431
  · exact B1983435
theorem solution (m : ℕ) (hlo : 1981435 ≤ m) (hhi : m ≤ 1983435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 495358 ≤ j := by omega
    have hj2 : j ≤ 495858 := by omega
    have hb : Blo 1981435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
