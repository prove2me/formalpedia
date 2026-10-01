-- Prove2me | solution 1 for syracuse_descends_range_2111435_2113435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:16:47.848247+00:00
-- url     : https://prove2.me/submissions/ef448c49-b2d8-40b9-97d6-b0aabde95c81

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

theorem B2375365 : Blo 2111435 2375365 := bbase (se 4 (by rfl) ⟨222690, by rfl⟩ : syracuseStep 2375365 = 445381) (by norm_num)
theorem B3167153 : Blo 2111435 3167153 := bstep (se 2 (by rfl) ⟨1187682, by rfl⟩ : syracuseStep 3167153 = 2375365) B2375365
theorem B2111435 : Blo 2111435 2111435 := bstep (se 1 (by rfl) ⟨1583576, by rfl⟩ : syracuseStep 2111435 = 3167153) B3167153
theorem B4008437 : Blo 2111435 4008437 := bbase (se 5 (by rfl) ⟨187895, by rfl⟩ : syracuseStep 4008437 = 375791) (by norm_num)
theorem B2672291 : Blo 2111435 2672291 := bstep (se 1 (by rfl) ⟨2004218, by rfl⟩ : syracuseStep 2672291 = 4008437) B4008437
theorem B7126109 : Blo 2111435 7126109 := bstep (se 3 (by rfl) ⟨1336145, by rfl⟩ : syracuseStep 7126109 = 2672291) B2672291
theorem B4750739 : Blo 2111435 4750739 := bstep (se 1 (by rfl) ⟨3563054, by rfl⟩ : syracuseStep 4750739 = 7126109) B7126109
theorem B3167159 : Blo 2111435 3167159 := bstep (se 1 (by rfl) ⟨2375369, by rfl⟩ : syracuseStep 3167159 = 4750739) B4750739
theorem B2111439 : Blo 2111435 2111439 := bstep (se 1 (by rfl) ⟨1583579, by rfl⟩ : syracuseStep 2111439 = 3167159) B3167159
theorem B3167165 : Blo 2111435 3167165 := bbase (se 3 (by rfl) ⟨593843, by rfl⟩ : syracuseStep 3167165 = 1187687) (by norm_num)
theorem B2111443 : Blo 2111435 2111443 := bstep (se 1 (by rfl) ⟨1583582, by rfl⟩ : syracuseStep 2111443 = 3167165) B3167165
theorem B4750757 : Blo 2111435 4750757 := bbase (se 4 (by rfl) ⟨445383, by rfl⟩ : syracuseStep 4750757 = 890767) (by norm_num)
theorem B3167171 : Blo 2111435 3167171 := bstep (se 1 (by rfl) ⟨2375378, by rfl⟩ : syracuseStep 3167171 = 4750757) B4750757
theorem B2111447 : Blo 2111435 2111447 := bstep (se 1 (by rfl) ⟨1583585, by rfl⟩ : syracuseStep 2111447 = 3167171) B3167171
theorem B5344613 : Blo 2111435 5344613 := bbase (se 4 (by rfl) ⟨501057, by rfl⟩ : syracuseStep 5344613 = 1002115) (by norm_num)
theorem B3563075 : Blo 2111435 3563075 := bstep (se 1 (by rfl) ⟨2672306, by rfl⟩ : syracuseStep 3563075 = 5344613) B5344613
theorem B2375383 : Blo 2111435 2375383 := bstep (se 1 (by rfl) ⟨1781537, by rfl⟩ : syracuseStep 2375383 = 3563075) B3563075
theorem B3167177 : Blo 2111435 3167177 := bstep (se 2 (by rfl) ⟨1187691, by rfl⟩ : syracuseStep 3167177 = 2375383) B2375383
theorem B2111451 : Blo 2111435 2111451 := bstep (se 1 (by rfl) ⟨1583588, by rfl⟩ : syracuseStep 2111451 = 3167177) B3167177
theorem B2536609 : Blo 2111435 2536609 := bbase (se 2 (by rfl) ⟨951228, by rfl⟩ : syracuseStep 2536609 = 1902457) (by norm_num)
theorem B3382145 : Blo 2111435 3382145 := bstep (se 2 (by rfl) ⟨1268304, by rfl⟩ : syracuseStep 3382145 = 2536609) B2536609
theorem B2254763 : Blo 2111435 2254763 := bstep (se 1 (by rfl) ⟨1691072, by rfl⟩ : syracuseStep 2254763 = 3382145) B3382145
theorem B6012701 : Blo 2111435 6012701 := bstep (se 3 (by rfl) ⟨1127381, by rfl⟩ : syracuseStep 6012701 = 2254763) B2254763
theorem B4008467 : Blo 2111435 4008467 := bstep (se 1 (by rfl) ⟨3006350, by rfl⟩ : syracuseStep 4008467 = 6012701) B6012701
theorem B10689245 : Blo 2111435 10689245 := bstep (se 3 (by rfl) ⟨2004233, by rfl⟩ : syracuseStep 10689245 = 4008467) B4008467
theorem B7126163 : Blo 2111435 7126163 := bstep (se 1 (by rfl) ⟨5344622, by rfl⟩ : syracuseStep 7126163 = 10689245) B10689245
theorem B4750775 : Blo 2111435 4750775 := bstep (se 1 (by rfl) ⟨3563081, by rfl⟩ : syracuseStep 4750775 = 7126163) B7126163
theorem B3167183 : Blo 2111435 3167183 := bstep (se 1 (by rfl) ⟨2375387, by rfl⟩ : syracuseStep 3167183 = 4750775) B4750775
theorem B2111455 : Blo 2111435 2111455 := bstep (se 1 (by rfl) ⟨1583591, by rfl⟩ : syracuseStep 2111455 = 3167183) B3167183
theorem B3167189 : Blo 2111435 3167189 := bbase (se 7 (by rfl) ⟨37115, by rfl⟩ : syracuseStep 3167189 = 74231) (by norm_num)
theorem B2111459 : Blo 2111435 2111459 := bstep (se 1 (by rfl) ⟨1583594, by rfl⟩ : syracuseStep 2111459 = 3167189) B3167189
theorem B8016965 : Blo 2111435 8016965 := bbase (se 4 (by rfl) ⟨751590, by rfl⟩ : syracuseStep 8016965 = 1503181) (by norm_num)
theorem B5344643 : Blo 2111435 5344643 := bstep (se 1 (by rfl) ⟨4008482, by rfl⟩ : syracuseStep 5344643 = 8016965) B8016965
theorem B3563095 : Blo 2111435 3563095 := bstep (se 1 (by rfl) ⟨2672321, by rfl⟩ : syracuseStep 3563095 = 5344643) B5344643
theorem B4750793 : Blo 2111435 4750793 := bstep (se 2 (by rfl) ⟨1781547, by rfl⟩ : syracuseStep 4750793 = 3563095) B3563095
theorem B3167195 : Blo 2111435 3167195 := bstep (se 1 (by rfl) ⟨2375396, by rfl⟩ : syracuseStep 3167195 = 4750793) B4750793
theorem B2111463 : Blo 2111435 2111463 := bstep (se 1 (by rfl) ⟨1583597, by rfl⟩ : syracuseStep 2111463 = 3167195) B3167195
theorem B2375401 : Blo 2111435 2375401 := bbase (se 2 (by rfl) ⟨890775, by rfl⟩ : syracuseStep 2375401 = 1781551) (by norm_num)
theorem B3167201 : Blo 2111435 3167201 := bstep (se 2 (by rfl) ⟨1187700, by rfl⟩ : syracuseStep 3167201 = 2375401) B2375401
theorem B2111467 : Blo 2111435 2111467 := bstep (se 1 (by rfl) ⟨1583600, by rfl⟩ : syracuseStep 2111467 = 3167201) B3167201
theorem B12025493 : Blo 2111435 12025493 := bbase (se 6 (by rfl) ⟨281847, by rfl⟩ : syracuseStep 12025493 = 563695) (by norm_num)
theorem B8016995 : Blo 2111435 8016995 := bstep (se 1 (by rfl) ⟨6012746, by rfl⟩ : syracuseStep 8016995 = 12025493) B12025493
theorem B5344663 : Blo 2111435 5344663 := bstep (se 1 (by rfl) ⟨4008497, by rfl⟩ : syracuseStep 5344663 = 8016995) B8016995
theorem B7126217 : Blo 2111435 7126217 := bstep (se 2 (by rfl) ⟨2672331, by rfl⟩ : syracuseStep 7126217 = 5344663) B5344663
theorem B4750811 : Blo 2111435 4750811 := bstep (se 1 (by rfl) ⟨3563108, by rfl⟩ : syracuseStep 4750811 = 7126217) B7126217
theorem B3167207 : Blo 2111435 3167207 := bstep (se 1 (by rfl) ⟨2375405, by rfl⟩ : syracuseStep 3167207 = 4750811) B4750811
theorem B2111471 : Blo 2111435 2111471 := bstep (se 1 (by rfl) ⟨1583603, by rfl⟩ : syracuseStep 2111471 = 3167207) B3167207
theorem B3167213 : Blo 2111435 3167213 := bbase (se 3 (by rfl) ⟨593852, by rfl⟩ : syracuseStep 3167213 = 1187705) (by norm_num)
theorem B2111475 : Blo 2111435 2111475 := bstep (se 1 (by rfl) ⟨1583606, by rfl⟩ : syracuseStep 2111475 = 3167213) B3167213
theorem B4750829 : Blo 2111435 4750829 := bbase (se 3 (by rfl) ⟨890780, by rfl⟩ : syracuseStep 4750829 = 1781561) (by norm_num)
theorem B3167219 : Blo 2111435 3167219 := bstep (se 1 (by rfl) ⟨2375414, by rfl⟩ : syracuseStep 3167219 = 4750829) B4750829
theorem B2111479 : Blo 2111435 2111479 := bstep (se 1 (by rfl) ⟨1583609, by rfl⟩ : syracuseStep 2111479 = 3167219) B3167219
theorem B3804965 : Blo 2111435 3804965 := bbase (se 4 (by rfl) ⟨356715, by rfl⟩ : syracuseStep 3804965 = 713431) (by norm_num)
theorem B2536643 : Blo 2111435 2536643 := bstep (se 1 (by rfl) ⟨1902482, by rfl⟩ : syracuseStep 2536643 = 3804965) B3804965
theorem B6764381 : Blo 2111435 6764381 := bstep (se 3 (by rfl) ⟨1268321, by rfl⟩ : syracuseStep 6764381 = 2536643) B2536643
theorem B4509587 : Blo 2111435 4509587 := bstep (se 1 (by rfl) ⟨3382190, by rfl⟩ : syracuseStep 4509587 = 6764381) B6764381
theorem B3006391 : Blo 2111435 3006391 := bstep (se 1 (by rfl) ⟨2254793, by rfl⟩ : syracuseStep 3006391 = 4509587) B4509587
theorem B4008521 : Blo 2111435 4008521 := bstep (se 2 (by rfl) ⟨1503195, by rfl⟩ : syracuseStep 4008521 = 3006391) B3006391
theorem B2672347 : Blo 2111435 2672347 := bstep (se 1 (by rfl) ⟨2004260, by rfl⟩ : syracuseStep 2672347 = 4008521) B4008521
theorem B3563129 : Blo 2111435 3563129 := bstep (se 2 (by rfl) ⟨1336173, by rfl⟩ : syracuseStep 3563129 = 2672347) B2672347
theorem B2375419 : Blo 2111435 2375419 := bstep (se 1 (by rfl) ⟨1781564, by rfl⟩ : syracuseStep 2375419 = 3563129) B3563129
theorem B3167225 : Blo 2111435 3167225 := bstep (se 2 (by rfl) ⟨1187709, by rfl⟩ : syracuseStep 3167225 = 2375419) B2375419
theorem B2111483 : Blo 2111435 2111483 := bstep (se 1 (by rfl) ⟨1583612, by rfl⟩ : syracuseStep 2111483 = 3167225) B3167225
theorem B3435509 : Blo 2111435 3435509 := bbase (se 5 (by rfl) ⟨161039, by rfl⟩ : syracuseStep 3435509 = 322079) (by norm_num)
theorem B2290339 : Blo 2111435 2290339 := bstep (se 1 (by rfl) ⟨1717754, by rfl⟩ : syracuseStep 2290339 = 3435509) B3435509
theorem B3053785 : Blo 2111435 3053785 := bstep (se 2 (by rfl) ⟨1145169, by rfl⟩ : syracuseStep 3053785 = 2290339) B2290339
theorem B4071713 : Blo 2111435 4071713 := bstep (se 2 (by rfl) ⟨1526892, by rfl⟩ : syracuseStep 4071713 = 3053785) B3053785
theorem B10857901 : Blo 2111435 10857901 := bstep (se 3 (by rfl) ⟨2035856, by rfl⟩ : syracuseStep 10857901 = 4071713) B4071713
theorem B14477201 : Blo 2111435 14477201 := bstep (se 2 (by rfl) ⟨5428950, by rfl⟩ : syracuseStep 14477201 = 10857901) B10857901
theorem B9651467 : Blo 2111435 9651467 := bstep (se 1 (by rfl) ⟨7238600, by rfl⟩ : syracuseStep 9651467 = 14477201) B14477201
theorem B6434311 : Blo 2111435 6434311 := bstep (se 1 (by rfl) ⟨4825733, by rfl⟩ : syracuseStep 6434311 = 9651467) B9651467
theorem B8579081 : Blo 2111435 8579081 := bstep (se 2 (by rfl) ⟨3217155, by rfl⟩ : syracuseStep 8579081 = 6434311) B6434311
theorem B22877549 : Blo 2111435 22877549 := bstep (se 3 (by rfl) ⟨4289540, by rfl⟩ : syracuseStep 22877549 = 8579081) B8579081
theorem B15251699 : Blo 2111435 15251699 := bstep (se 1 (by rfl) ⟨11438774, by rfl⟩ : syracuseStep 15251699 = 22877549) B22877549
theorem B40671197 : Blo 2111435 40671197 := bstep (se 3 (by rfl) ⟨7625849, by rfl⟩ : syracuseStep 40671197 = 15251699) B15251699
theorem B27114131 : Blo 2111435 27114131 := bstep (se 1 (by rfl) ⟨20335598, by rfl⟩ : syracuseStep 27114131 = 40671197) B40671197
theorem B18076087 : Blo 2111435 18076087 := bstep (se 1 (by rfl) ⟨13557065, by rfl⟩ : syracuseStep 18076087 = 27114131) B27114131
theorem B96405797 : Blo 2111435 96405797 := bstep (se 4 (by rfl) ⟨9038043, by rfl⟩ : syracuseStep 96405797 = 18076087) B18076087
theorem B64270531 : Blo 2111435 64270531 := bstep (se 1 (by rfl) ⟨48202898, by rfl⟩ : syracuseStep 64270531 = 96405797) B96405797
theorem B85694041 : Blo 2111435 85694041 := bstep (se 2 (by rfl) ⟨32135265, by rfl⟩ : syracuseStep 85694041 = 64270531) B64270531
theorem B457034885 : Blo 2111435 457034885 := bstep (se 4 (by rfl) ⟨42847020, by rfl⟩ : syracuseStep 457034885 = 85694041) B85694041
theorem B304689923 : Blo 2111435 304689923 := bstep (se 1 (by rfl) ⟨228517442, by rfl⟩ : syracuseStep 304689923 = 457034885) B457034885
theorem B203126615 : Blo 2111435 203126615 := bstep (se 1 (by rfl) ⟨152344961, by rfl⟩ : syracuseStep 203126615 = 304689923) B304689923
theorem B135417743 : Blo 2111435 135417743 := bstep (se 1 (by rfl) ⟨101563307, by rfl⟩ : syracuseStep 135417743 = 203126615) B203126615
theorem B90278495 : Blo 2111435 90278495 := bstep (se 1 (by rfl) ⟨67708871, by rfl⟩ : syracuseStep 90278495 = 135417743) B135417743
theorem B60185663 : Blo 2111435 60185663 := bstep (se 1 (by rfl) ⟨45139247, by rfl⟩ : syracuseStep 60185663 = 90278495) B90278495
theorem B40123775 : Blo 2111435 40123775 := bstep (se 1 (by rfl) ⟨30092831, by rfl⟩ : syracuseStep 40123775 = 60185663) B60185663
theorem B106996733 : Blo 2111435 106996733 := bstep (se 3 (by rfl) ⟨20061887, by rfl⟩ : syracuseStep 106996733 = 40123775) B40123775
theorem B71331155 : Blo 2111435 71331155 := bstep (se 1 (by rfl) ⟨53498366, by rfl⟩ : syracuseStep 71331155 = 106996733) B106996733
theorem B47554103 : Blo 2111435 47554103 := bstep (se 1 (by rfl) ⟨35665577, by rfl⟩ : syracuseStep 47554103 = 71331155) B71331155
theorem B31702735 : Blo 2111435 31702735 := bstep (se 1 (by rfl) ⟨23777051, by rfl⟩ : syracuseStep 31702735 = 47554103) B47554103
theorem B169081253 : Blo 2111435 169081253 := bstep (se 4 (by rfl) ⟨15851367, by rfl⟩ : syracuseStep 169081253 = 31702735) B31702735
theorem B112720835 : Blo 2111435 112720835 := bstep (se 1 (by rfl) ⟨84540626, by rfl⟩ : syracuseStep 112720835 = 169081253) B169081253
theorem B75147223 : Blo 2111435 75147223 := bstep (se 1 (by rfl) ⟨56360417, by rfl⟩ : syracuseStep 75147223 = 112720835) B112720835
theorem B100196297 : Blo 2111435 100196297 := bstep (se 2 (by rfl) ⟨37573611, by rfl⟩ : syracuseStep 100196297 = 75147223) B75147223
theorem B66797531 : Blo 2111435 66797531 := bstep (se 1 (by rfl) ⟨50098148, by rfl⟩ : syracuseStep 66797531 = 100196297) B100196297
theorem B44531687 : Blo 2111435 44531687 := bstep (se 1 (by rfl) ⟨33398765, by rfl⟩ : syracuseStep 44531687 = 66797531) B66797531
theorem B29687791 : Blo 2111435 29687791 := bstep (se 1 (by rfl) ⟨22265843, by rfl⟩ : syracuseStep 29687791 = 44531687) B44531687
theorem B39583721 : Blo 2111435 39583721 := bstep (se 2 (by rfl) ⟨14843895, by rfl⟩ : syracuseStep 39583721 = 29687791) B29687791
theorem B26389147 : Blo 2111435 26389147 := bstep (se 1 (by rfl) ⟨19791860, by rfl⟩ : syracuseStep 26389147 = 39583721) B39583721
theorem B35185529 : Blo 2111435 35185529 := bstep (se 2 (by rfl) ⟨13194573, by rfl⟩ : syracuseStep 35185529 = 26389147) B26389147
theorem B93828077 : Blo 2111435 93828077 := bstep (se 3 (by rfl) ⟨17592764, by rfl⟩ : syracuseStep 93828077 = 35185529) B35185529
theorem B62552051 : Blo 2111435 62552051 := bstep (se 1 (by rfl) ⟨46914038, by rfl⟩ : syracuseStep 62552051 = 93828077) B93828077
theorem B41701367 : Blo 2111435 41701367 := bstep (se 1 (by rfl) ⟨31276025, by rfl⟩ : syracuseStep 41701367 = 62552051) B62552051
theorem B27800911 : Blo 2111435 27800911 := bstep (se 1 (by rfl) ⟨20850683, by rfl⟩ : syracuseStep 27800911 = 41701367) B41701367
theorem B37067881 : Blo 2111435 37067881 := bstep (se 2 (by rfl) ⟨13900455, by rfl⟩ : syracuseStep 37067881 = 27800911) B27800911
theorem B49423841 : Blo 2111435 49423841 := bstep (se 2 (by rfl) ⟨18533940, by rfl⟩ : syracuseStep 49423841 = 37067881) B37067881
theorem B32949227 : Blo 2111435 32949227 := bstep (se 1 (by rfl) ⟨24711920, by rfl⟩ : syracuseStep 32949227 = 49423841) B49423841
theorem B87864605 : Blo 2111435 87864605 := bstep (se 3 (by rfl) ⟨16474613, by rfl⟩ : syracuseStep 87864605 = 32949227) B32949227
theorem B58576403 : Blo 2111435 58576403 := bstep (se 1 (by rfl) ⟨43932302, by rfl⟩ : syracuseStep 58576403 = 87864605) B87864605
theorem B156203741 : Blo 2111435 156203741 := bstep (se 3 (by rfl) ⟨29288201, by rfl⟩ : syracuseStep 156203741 = 58576403) B58576403
theorem B104135827 : Blo 2111435 104135827 := bstep (se 1 (by rfl) ⟨78101870, by rfl⟩ : syracuseStep 104135827 = 156203741) B156203741
theorem B138847769 : Blo 2111435 138847769 := bstep (se 2 (by rfl) ⟨52067913, by rfl⟩ : syracuseStep 138847769 = 104135827) B104135827
theorem B92565179 : Blo 2111435 92565179 := bstep (se 1 (by rfl) ⟨69423884, by rfl⟩ : syracuseStep 92565179 = 138847769) B138847769
theorem B61710119 : Blo 2111435 61710119 := bstep (se 1 (by rfl) ⟨46282589, by rfl⟩ : syracuseStep 61710119 = 92565179) B92565179
theorem B41140079 : Blo 2111435 41140079 := bstep (se 1 (by rfl) ⟨30855059, by rfl⟩ : syracuseStep 41140079 = 61710119) B61710119
theorem B27426719 : Blo 2111435 27426719 := bstep (se 1 (by rfl) ⟨20570039, by rfl⟩ : syracuseStep 27426719 = 41140079) B41140079
theorem B73137917 : Blo 2111435 73137917 := bstep (se 3 (by rfl) ⟨13713359, by rfl⟩ : syracuseStep 73137917 = 27426719) B27426719
theorem B48758611 : Blo 2111435 48758611 := bstep (se 1 (by rfl) ⟨36568958, by rfl⟩ : syracuseStep 48758611 = 73137917) B73137917
theorem B65011481 : Blo 2111435 65011481 := bstep (se 2 (by rfl) ⟨24379305, by rfl⟩ : syracuseStep 65011481 = 48758611) B48758611
theorem B43340987 : Blo 2111435 43340987 := bstep (se 1 (by rfl) ⟨32505740, by rfl⟩ : syracuseStep 43340987 = 65011481) B65011481
theorem B28893991 : Blo 2111435 28893991 := bstep (se 1 (by rfl) ⟨21670493, by rfl⟩ : syracuseStep 28893991 = 43340987) B43340987
theorem B38525321 : Blo 2111435 38525321 := bstep (se 2 (by rfl) ⟨14446995, by rfl⟩ : syracuseStep 38525321 = 28893991) B28893991
theorem B102734189 : Blo 2111435 102734189 := bstep (se 3 (by rfl) ⟨19262660, by rfl⟩ : syracuseStep 102734189 = 38525321) B38525321
theorem B68489459 : Blo 2111435 68489459 := bstep (se 1 (by rfl) ⟨51367094, by rfl⟩ : syracuseStep 68489459 = 102734189) B102734189
theorem B45659639 : Blo 2111435 45659639 := bstep (se 1 (by rfl) ⟨34244729, by rfl⟩ : syracuseStep 45659639 = 68489459) B68489459
theorem B121759037 : Blo 2111435 121759037 := bstep (se 3 (by rfl) ⟨22829819, by rfl⟩ : syracuseStep 121759037 = 45659639) B45659639
theorem B81172691 : Blo 2111435 81172691 := bstep (se 1 (by rfl) ⟨60879518, by rfl⟩ : syracuseStep 81172691 = 121759037) B121759037
theorem B54115127 : Blo 2111435 54115127 := bstep (se 1 (by rfl) ⟨40586345, by rfl⟩ : syracuseStep 54115127 = 81172691) B81172691
theorem B36076751 : Blo 2111435 36076751 := bstep (se 1 (by rfl) ⟨27057563, by rfl⟩ : syracuseStep 36076751 = 54115127) B54115127
theorem B24051167 : Blo 2111435 24051167 := bstep (se 1 (by rfl) ⟨18038375, by rfl⟩ : syracuseStep 24051167 = 36076751) B36076751
theorem B16034111 : Blo 2111435 16034111 := bstep (se 1 (by rfl) ⟨12025583, by rfl⟩ : syracuseStep 16034111 = 24051167) B24051167
theorem B10689407 : Blo 2111435 10689407 := bstep (se 1 (by rfl) ⟨8017055, by rfl⟩ : syracuseStep 10689407 = 16034111) B16034111
theorem B7126271 : Blo 2111435 7126271 := bstep (se 1 (by rfl) ⟨5344703, by rfl⟩ : syracuseStep 7126271 = 10689407) B10689407
theorem B4750847 : Blo 2111435 4750847 := bstep (se 1 (by rfl) ⟨3563135, by rfl⟩ : syracuseStep 4750847 = 7126271) B7126271
theorem B3167231 : Blo 2111435 3167231 := bstep (se 1 (by rfl) ⟨2375423, by rfl⟩ : syracuseStep 3167231 = 4750847) B4750847
theorem B2111487 : Blo 2111435 2111487 := bstep (se 1 (by rfl) ⟨1583615, by rfl⟩ : syracuseStep 2111487 = 3167231) B3167231
theorem B3167237 : Blo 2111435 3167237 := bbase (se 4 (by rfl) ⟨296928, by rfl⟩ : syracuseStep 3167237 = 593857) (by norm_num)
theorem B2111491 : Blo 2111435 2111491 := bstep (se 1 (by rfl) ⟨1583618, by rfl⟩ : syracuseStep 2111491 = 3167237) B3167237
theorem B3563149 : Blo 2111435 3563149 := bbase (se 3 (by rfl) ⟨668090, by rfl⟩ : syracuseStep 3563149 = 1336181) (by norm_num)
theorem B4750865 : Blo 2111435 4750865 := bstep (se 2 (by rfl) ⟨1781574, by rfl⟩ : syracuseStep 4750865 = 3563149) B3563149
theorem B3167243 : Blo 2111435 3167243 := bstep (se 1 (by rfl) ⟨2375432, by rfl⟩ : syracuseStep 3167243 = 4750865) B4750865
theorem B2111495 : Blo 2111435 2111495 := bstep (se 1 (by rfl) ⟨1583621, by rfl⟩ : syracuseStep 2111495 = 3167243) B3167243
theorem B2375437 : Blo 2111435 2375437 := bbase (se 3 (by rfl) ⟨445394, by rfl⟩ : syracuseStep 2375437 = 890789) (by norm_num)
theorem B3167249 : Blo 2111435 3167249 := bstep (se 2 (by rfl) ⟨1187718, by rfl⟩ : syracuseStep 3167249 = 2375437) B2375437
theorem B2111499 : Blo 2111435 2111499 := bstep (se 1 (by rfl) ⟨1583624, by rfl⟩ : syracuseStep 2111499 = 3167249) B3167249
theorem B7126325 : Blo 2111435 7126325 := bbase (se 5 (by rfl) ⟨334046, by rfl⟩ : syracuseStep 7126325 = 668093) (by norm_num)
theorem B4750883 : Blo 2111435 4750883 := bstep (se 1 (by rfl) ⟨3563162, by rfl⟩ : syracuseStep 4750883 = 7126325) B7126325
theorem B3167255 : Blo 2111435 3167255 := bstep (se 1 (by rfl) ⟨2375441, by rfl⟩ : syracuseStep 3167255 = 4750883) B4750883
theorem B2111503 : Blo 2111435 2111503 := bstep (se 1 (by rfl) ⟨1583627, by rfl⟩ : syracuseStep 2111503 = 3167255) B3167255
theorem B3167261 : Blo 2111435 3167261 := bbase (se 3 (by rfl) ⟨593861, by rfl⟩ : syracuseStep 3167261 = 1187723) (by norm_num)
theorem B2111507 : Blo 2111435 2111507 := bstep (se 1 (by rfl) ⟨1583630, by rfl⟩ : syracuseStep 2111507 = 3167261) B3167261
theorem B4750901 : Blo 2111435 4750901 := bbase (se 5 (by rfl) ⟨222698, by rfl⟩ : syracuseStep 4750901 = 445397) (by norm_num)
theorem B3167267 : Blo 2111435 3167267 := bstep (se 1 (by rfl) ⟨2375450, by rfl⟩ : syracuseStep 3167267 = 4750901) B4750901
theorem B2111511 : Blo 2111435 2111511 := bstep (se 1 (by rfl) ⟨1583633, by rfl⟩ : syracuseStep 2111511 = 3167267) B3167267
theorem B2536681 : Blo 2111435 2536681 := bbase (se 2 (by rfl) ⟨951255, by rfl⟩ : syracuseStep 2536681 = 1902511) (by norm_num)
theorem B3382241 : Blo 2111435 3382241 := bstep (se 2 (by rfl) ⟨1268340, by rfl⟩ : syracuseStep 3382241 = 2536681) B2536681
theorem B9019309 : Blo 2111435 9019309 := bstep (se 3 (by rfl) ⟨1691120, by rfl⟩ : syracuseStep 9019309 = 3382241) B3382241
theorem B12025745 : Blo 2111435 12025745 := bstep (se 2 (by rfl) ⟨4509654, by rfl⟩ : syracuseStep 12025745 = 9019309) B9019309
theorem B8017163 : Blo 2111435 8017163 := bstep (se 1 (by rfl) ⟨6012872, by rfl⟩ : syracuseStep 8017163 = 12025745) B12025745
theorem B5344775 : Blo 2111435 5344775 := bstep (se 1 (by rfl) ⟨4008581, by rfl⟩ : syracuseStep 5344775 = 8017163) B8017163
theorem B3563183 : Blo 2111435 3563183 := bstep (se 1 (by rfl) ⟨2672387, by rfl⟩ : syracuseStep 3563183 = 5344775) B5344775
theorem B2375455 : Blo 2111435 2375455 := bstep (se 1 (by rfl) ⟨1781591, by rfl⟩ : syracuseStep 2375455 = 3563183) B3563183
theorem B3167273 : Blo 2111435 3167273 := bstep (se 2 (by rfl) ⟨1187727, by rfl⟩ : syracuseStep 3167273 = 2375455) B2375455
theorem B2111515 : Blo 2111435 2111515 := bstep (se 1 (by rfl) ⟨1583636, by rfl⟩ : syracuseStep 2111515 = 3167273) B3167273
theorem B12841973 : Blo 2111435 12841973 := bbase (se 5 (by rfl) ⟨601967, by rfl⟩ : syracuseStep 12841973 = 1203935) (by norm_num)
theorem B8561315 : Blo 2111435 8561315 := bstep (se 1 (by rfl) ⟨6420986, by rfl⟩ : syracuseStep 8561315 = 12841973) B12841973
theorem B5707543 : Blo 2111435 5707543 := bstep (se 1 (by rfl) ⟨4280657, by rfl⟩ : syracuseStep 5707543 = 8561315) B8561315
theorem B7610057 : Blo 2111435 7610057 := bstep (se 2 (by rfl) ⟨2853771, by rfl⟩ : syracuseStep 7610057 = 5707543) B5707543
theorem B5073371 : Blo 2111435 5073371 := bstep (se 1 (by rfl) ⟨3805028, by rfl⟩ : syracuseStep 5073371 = 7610057) B7610057
theorem B3382247 : Blo 2111435 3382247 := bstep (se 1 (by rfl) ⟨2536685, by rfl⟩ : syracuseStep 3382247 = 5073371) B5073371
theorem B9019325 : Blo 2111435 9019325 := bstep (se 3 (by rfl) ⟨1691123, by rfl⟩ : syracuseStep 9019325 = 3382247) B3382247
theorem B6012883 : Blo 2111435 6012883 := bstep (se 1 (by rfl) ⟨4509662, by rfl⟩ : syracuseStep 6012883 = 9019325) B9019325
theorem B8017177 : Blo 2111435 8017177 := bstep (se 2 (by rfl) ⟨3006441, by rfl⟩ : syracuseStep 8017177 = 6012883) B6012883
theorem B10689569 : Blo 2111435 10689569 := bstep (se 2 (by rfl) ⟨4008588, by rfl⟩ : syracuseStep 10689569 = 8017177) B8017177
theorem B7126379 : Blo 2111435 7126379 := bstep (se 1 (by rfl) ⟨5344784, by rfl⟩ : syracuseStep 7126379 = 10689569) B10689569
theorem B4750919 : Blo 2111435 4750919 := bstep (se 1 (by rfl) ⟨3563189, by rfl⟩ : syracuseStep 4750919 = 7126379) B7126379
theorem B3167279 : Blo 2111435 3167279 := bstep (se 1 (by rfl) ⟨2375459, by rfl⟩ : syracuseStep 3167279 = 4750919) B4750919
theorem B2111519 : Blo 2111435 2111519 := bstep (se 1 (by rfl) ⟨1583639, by rfl⟩ : syracuseStep 2111519 = 3167279) B3167279
theorem B3167285 : Blo 2111435 3167285 := bbase (se 5 (by rfl) ⟨148466, by rfl⟩ : syracuseStep 3167285 = 296933) (by norm_num)
theorem B2111523 : Blo 2111435 2111523 := bstep (se 1 (by rfl) ⟨1583642, by rfl⟩ : syracuseStep 2111523 = 3167285) B3167285
theorem B5344805 : Blo 2111435 5344805 := bbase (se 4 (by rfl) ⟨501075, by rfl⟩ : syracuseStep 5344805 = 1002151) (by norm_num)
theorem B3563203 : Blo 2111435 3563203 := bstep (se 1 (by rfl) ⟨2672402, by rfl⟩ : syracuseStep 3563203 = 5344805) B5344805
theorem B4750937 : Blo 2111435 4750937 := bstep (se 2 (by rfl) ⟨1781601, by rfl⟩ : syracuseStep 4750937 = 3563203) B3563203
theorem B3167291 : Blo 2111435 3167291 := bstep (se 1 (by rfl) ⟨2375468, by rfl⟩ : syracuseStep 3167291 = 4750937) B4750937
theorem B2111527 : Blo 2111435 2111527 := bstep (se 1 (by rfl) ⟨1583645, by rfl⟩ : syracuseStep 2111527 = 3167291) B3167291
theorem B2375473 : Blo 2111435 2375473 := bbase (se 2 (by rfl) ⟨890802, by rfl⟩ : syracuseStep 2375473 = 1781605) (by norm_num)
theorem B3167297 : Blo 2111435 3167297 := bstep (se 2 (by rfl) ⟨1187736, by rfl⟩ : syracuseStep 3167297 = 2375473) B2375473
theorem B2111531 : Blo 2111435 2111531 := bstep (se 1 (by rfl) ⟨1583648, by rfl⟩ : syracuseStep 2111531 = 3167297) B3167297
theorem B2536705 : Blo 2111435 2536705 := bbase (se 2 (by rfl) ⟨951264, by rfl⟩ : syracuseStep 2536705 = 1902529) (by norm_num)
theorem B3382273 : Blo 2111435 3382273 := bstep (se 2 (by rfl) ⟨1268352, by rfl⟩ : syracuseStep 3382273 = 2536705) B2536705
theorem B4509697 : Blo 2111435 4509697 := bstep (se 2 (by rfl) ⟨1691136, by rfl⟩ : syracuseStep 4509697 = 3382273) B3382273
theorem B6012929 : Blo 2111435 6012929 := bstep (se 2 (by rfl) ⟨2254848, by rfl⟩ : syracuseStep 6012929 = 4509697) B4509697
theorem B4008619 : Blo 2111435 4008619 := bstep (se 1 (by rfl) ⟨3006464, by rfl⟩ : syracuseStep 4008619 = 6012929) B6012929
theorem B5344825 : Blo 2111435 5344825 := bstep (se 2 (by rfl) ⟨2004309, by rfl⟩ : syracuseStep 5344825 = 4008619) B4008619
theorem B7126433 : Blo 2111435 7126433 := bstep (se 2 (by rfl) ⟨2672412, by rfl⟩ : syracuseStep 7126433 = 5344825) B5344825
theorem B4750955 : Blo 2111435 4750955 := bstep (se 1 (by rfl) ⟨3563216, by rfl⟩ : syracuseStep 4750955 = 7126433) B7126433
theorem B3167303 : Blo 2111435 3167303 := bstep (se 1 (by rfl) ⟨2375477, by rfl⟩ : syracuseStep 3167303 = 4750955) B4750955
theorem B2111535 : Blo 2111435 2111535 := bstep (se 1 (by rfl) ⟨1583651, by rfl⟩ : syracuseStep 2111535 = 3167303) B3167303
theorem B3167309 : Blo 2111435 3167309 := bbase (se 3 (by rfl) ⟨593870, by rfl⟩ : syracuseStep 3167309 = 1187741) (by norm_num)
theorem B2111539 : Blo 2111435 2111539 := bstep (se 1 (by rfl) ⟨1583654, by rfl⟩ : syracuseStep 2111539 = 3167309) B3167309
theorem B4750973 : Blo 2111435 4750973 := bbase (se 3 (by rfl) ⟨890807, by rfl⟩ : syracuseStep 4750973 = 1781615) (by norm_num)
theorem B3167315 : Blo 2111435 3167315 := bstep (se 1 (by rfl) ⟨2375486, by rfl⟩ : syracuseStep 3167315 = 4750973) B4750973
theorem B2111543 : Blo 2111435 2111543 := bstep (se 1 (by rfl) ⟨1583657, by rfl⟩ : syracuseStep 2111543 = 3167315) B3167315
theorem B3563237 : Blo 2111435 3563237 := bbase (se 4 (by rfl) ⟨334053, by rfl⟩ : syracuseStep 3563237 = 668107) (by norm_num)
theorem B2375491 : Blo 2111435 2375491 := bstep (se 1 (by rfl) ⟨1781618, by rfl⟩ : syracuseStep 2375491 = 3563237) B3563237
theorem B3167321 : Blo 2111435 3167321 := bstep (se 2 (by rfl) ⟨1187745, by rfl⟩ : syracuseStep 3167321 = 2375491) B2375491
theorem B2111547 : Blo 2111435 2111547 := bstep (se 1 (by rfl) ⟨1583660, by rfl⟩ : syracuseStep 2111547 = 3167321) B3167321
theorem B6764597 : Blo 2111435 6764597 := bbase (se 5 (by rfl) ⟨317090, by rfl⟩ : syracuseStep 6764597 = 634181) (by norm_num)
theorem B4509731 : Blo 2111435 4509731 := bstep (se 1 (by rfl) ⟨3382298, by rfl⟩ : syracuseStep 4509731 = 6764597) B6764597
theorem B3006487 : Blo 2111435 3006487 := bstep (se 1 (by rfl) ⟨2254865, by rfl⟩ : syracuseStep 3006487 = 4509731) B4509731
theorem B16034597 : Blo 2111435 16034597 := bstep (se 4 (by rfl) ⟨1503243, by rfl⟩ : syracuseStep 16034597 = 3006487) B3006487
theorem B10689731 : Blo 2111435 10689731 := bstep (se 1 (by rfl) ⟨8017298, by rfl⟩ : syracuseStep 10689731 = 16034597) B16034597
theorem B7126487 : Blo 2111435 7126487 := bstep (se 1 (by rfl) ⟨5344865, by rfl⟩ : syracuseStep 7126487 = 10689731) B10689731
theorem B4750991 : Blo 2111435 4750991 := bstep (se 1 (by rfl) ⟨3563243, by rfl⟩ : syracuseStep 4750991 = 7126487) B7126487
theorem B3167327 : Blo 2111435 3167327 := bstep (se 1 (by rfl) ⟨2375495, by rfl⟩ : syracuseStep 3167327 = 4750991) B4750991
theorem B2111551 : Blo 2111435 2111551 := bstep (se 1 (by rfl) ⟨1583663, by rfl⟩ : syracuseStep 2111551 = 3167327) B3167327
theorem B3167333 : Blo 2111435 3167333 := bbase (se 4 (by rfl) ⟨296937, by rfl⟩ : syracuseStep 3167333 = 593875) (by norm_num)
theorem B2111555 : Blo 2111435 2111555 := bstep (se 1 (by rfl) ⟨1583666, by rfl⟩ : syracuseStep 2111555 = 3167333) B3167333
theorem B4509749 : Blo 2111435 4509749 := bbase (se 5 (by rfl) ⟨211394, by rfl⟩ : syracuseStep 4509749 = 422789) (by norm_num)
theorem B3006499 : Blo 2111435 3006499 := bstep (se 1 (by rfl) ⟨2254874, by rfl⟩ : syracuseStep 3006499 = 4509749) B4509749
theorem B4008665 : Blo 2111435 4008665 := bstep (se 2 (by rfl) ⟨1503249, by rfl⟩ : syracuseStep 4008665 = 3006499) B3006499
theorem B2672443 : Blo 2111435 2672443 := bstep (se 1 (by rfl) ⟨2004332, by rfl⟩ : syracuseStep 2672443 = 4008665) B4008665
theorem B3563257 : Blo 2111435 3563257 := bstep (se 2 (by rfl) ⟨1336221, by rfl⟩ : syracuseStep 3563257 = 2672443) B2672443
theorem B4751009 : Blo 2111435 4751009 := bstep (se 2 (by rfl) ⟨1781628, by rfl⟩ : syracuseStep 4751009 = 3563257) B3563257
theorem B3167339 : Blo 2111435 3167339 := bstep (se 1 (by rfl) ⟨2375504, by rfl⟩ : syracuseStep 3167339 = 4751009) B4751009
theorem B2111559 : Blo 2111435 2111559 := bstep (se 1 (by rfl) ⟨1583669, by rfl⟩ : syracuseStep 2111559 = 3167339) B3167339
theorem B2375509 : Blo 2111435 2375509 := bbase (se 9 (by rfl) ⟨6959, by rfl⟩ : syracuseStep 2375509 = 13919) (by norm_num)
theorem B3167345 : Blo 2111435 3167345 := bstep (se 2 (by rfl) ⟨1187754, by rfl⟩ : syracuseStep 3167345 = 2375509) B2375509
theorem B2111563 : Blo 2111435 2111563 := bstep (se 1 (by rfl) ⟨1583672, by rfl⟩ : syracuseStep 2111563 = 3167345) B3167345
theorem B2672453 : Blo 2111435 2672453 := bbase (se 4 (by rfl) ⟨250542, by rfl⟩ : syracuseStep 2672453 = 501085) (by norm_num)
theorem B7126541 : Blo 2111435 7126541 := bstep (se 3 (by rfl) ⟨1336226, by rfl⟩ : syracuseStep 7126541 = 2672453) B2672453
theorem B4751027 : Blo 2111435 4751027 := bstep (se 1 (by rfl) ⟨3563270, by rfl⟩ : syracuseStep 4751027 = 7126541) B7126541
theorem B3167351 : Blo 2111435 3167351 := bstep (se 1 (by rfl) ⟨2375513, by rfl⟩ : syracuseStep 3167351 = 4751027) B4751027
theorem B2111567 : Blo 2111435 2111567 := bstep (se 1 (by rfl) ⟨1583675, by rfl⟩ : syracuseStep 2111567 = 3167351) B3167351
theorem B3167357 : Blo 2111435 3167357 := bbase (se 3 (by rfl) ⟨593879, by rfl⟩ : syracuseStep 3167357 = 1187759) (by norm_num)
theorem B2111571 : Blo 2111435 2111571 := bstep (se 1 (by rfl) ⟨1583678, by rfl⟩ : syracuseStep 2111571 = 3167357) B3167357
theorem B4751045 : Blo 2111435 4751045 := bbase (se 4 (by rfl) ⟨445410, by rfl⟩ : syracuseStep 4751045 = 890821) (by norm_num)
theorem B3167363 : Blo 2111435 3167363 := bstep (se 1 (by rfl) ⟨2375522, by rfl⟩ : syracuseStep 3167363 = 4751045) B4751045
theorem B2111575 : Blo 2111435 2111575 := bstep (se 1 (by rfl) ⟨1583681, by rfl⟩ : syracuseStep 2111575 = 3167363) B3167363
theorem B3857053 : Blo 2111435 3857053 := bbase (se 3 (by rfl) ⟨723197, by rfl⟩ : syracuseStep 3857053 = 1446395) (by norm_num)
theorem B5142737 : Blo 2111435 5142737 := bstep (se 2 (by rfl) ⟨1928526, by rfl⟩ : syracuseStep 5142737 = 3857053) B3857053
theorem B3428491 : Blo 2111435 3428491 := bstep (se 1 (by rfl) ⟨2571368, by rfl⟩ : syracuseStep 3428491 = 5142737) B5142737
theorem B4571321 : Blo 2111435 4571321 := bstep (se 2 (by rfl) ⟨1714245, by rfl⟩ : syracuseStep 4571321 = 3428491) B3428491
theorem B12190189 : Blo 2111435 12190189 := bstep (se 3 (by rfl) ⟨2285660, by rfl⟩ : syracuseStep 12190189 = 4571321) B4571321
theorem B16253585 : Blo 2111435 16253585 := bstep (se 2 (by rfl) ⟨6095094, by rfl⟩ : syracuseStep 16253585 = 12190189) B12190189
theorem B10835723 : Blo 2111435 10835723 := bstep (se 1 (by rfl) ⟨8126792, by rfl⟩ : syracuseStep 10835723 = 16253585) B16253585
theorem B7223815 : Blo 2111435 7223815 := bstep (se 1 (by rfl) ⟨5417861, by rfl⟩ : syracuseStep 7223815 = 10835723) B10835723
theorem B9631753 : Blo 2111435 9631753 := bstep (se 2 (by rfl) ⟨3611907, by rfl⟩ : syracuseStep 9631753 = 7223815) B7223815
theorem B51369349 : Blo 2111435 51369349 := bstep (se 4 (by rfl) ⟨4815876, by rfl⟩ : syracuseStep 51369349 = 9631753) B9631753
theorem B68492465 : Blo 2111435 68492465 := bstep (se 2 (by rfl) ⟨25684674, by rfl⟩ : syracuseStep 68492465 = 51369349) B51369349
theorem B45661643 : Blo 2111435 45661643 := bstep (se 1 (by rfl) ⟨34246232, by rfl⟩ : syracuseStep 45661643 = 68492465) B68492465
theorem B30441095 : Blo 2111435 30441095 := bstep (se 1 (by rfl) ⟨22830821, by rfl⟩ : syracuseStep 30441095 = 45661643) B45661643
theorem B20294063 : Blo 2111435 20294063 := bstep (se 1 (by rfl) ⟨15220547, by rfl⟩ : syracuseStep 20294063 = 30441095) B30441095
theorem B13529375 : Blo 2111435 13529375 := bstep (se 1 (by rfl) ⟨10147031, by rfl⟩ : syracuseStep 13529375 = 20294063) B20294063
theorem B9019583 : Blo 2111435 9019583 := bstep (se 1 (by rfl) ⟨6764687, by rfl⟩ : syracuseStep 9019583 = 13529375) B13529375
theorem B6013055 : Blo 2111435 6013055 := bstep (se 1 (by rfl) ⟨4509791, by rfl⟩ : syracuseStep 6013055 = 9019583) B9019583
theorem B4008703 : Blo 2111435 4008703 := bstep (se 1 (by rfl) ⟨3006527, by rfl⟩ : syracuseStep 4008703 = 6013055) B6013055
theorem B5344937 : Blo 2111435 5344937 := bstep (se 2 (by rfl) ⟨2004351, by rfl⟩ : syracuseStep 5344937 = 4008703) B4008703
theorem B3563291 : Blo 2111435 3563291 := bstep (se 1 (by rfl) ⟨2672468, by rfl⟩ : syracuseStep 3563291 = 5344937) B5344937
theorem B2375527 : Blo 2111435 2375527 := bstep (se 1 (by rfl) ⟨1781645, by rfl⟩ : syracuseStep 2375527 = 3563291) B3563291
theorem B3167369 : Blo 2111435 3167369 := bstep (se 2 (by rfl) ⟨1187763, by rfl⟩ : syracuseStep 3167369 = 2375527) B2375527
theorem B2111579 : Blo 2111435 2111579 := bstep (se 1 (by rfl) ⟨1583684, by rfl⟩ : syracuseStep 2111579 = 3167369) B3167369
theorem B10689893 : Blo 2111435 10689893 := bbase (se 4 (by rfl) ⟨1002177, by rfl⟩ : syracuseStep 10689893 = 2004355) (by norm_num)
theorem B7126595 : Blo 2111435 7126595 := bstep (se 1 (by rfl) ⟨5344946, by rfl⟩ : syracuseStep 7126595 = 10689893) B10689893
theorem B4751063 : Blo 2111435 4751063 := bstep (se 1 (by rfl) ⟨3563297, by rfl⟩ : syracuseStep 4751063 = 7126595) B7126595
theorem B3167375 : Blo 2111435 3167375 := bstep (se 1 (by rfl) ⟨2375531, by rfl⟩ : syracuseStep 3167375 = 4751063) B4751063
theorem B2111583 : Blo 2111435 2111583 := bstep (se 1 (by rfl) ⟨1583687, by rfl⟩ : syracuseStep 2111583 = 3167375) B3167375
theorem B3167381 : Blo 2111435 3167381 := bbase (se 6 (by rfl) ⟨74235, by rfl⟩ : syracuseStep 3167381 = 148471) (by norm_num)
theorem B2111587 : Blo 2111435 2111587 := bstep (se 1 (by rfl) ⟨1583690, by rfl⟩ : syracuseStep 2111587 = 3167381) B3167381
theorem B6764725 : Blo 2111435 6764725 := bbase (se 5 (by rfl) ⟨317096, by rfl⟩ : syracuseStep 6764725 = 634193) (by norm_num)
theorem B9019633 : Blo 2111435 9019633 := bstep (se 2 (by rfl) ⟨3382362, by rfl⟩ : syracuseStep 9019633 = 6764725) B6764725
theorem B12026177 : Blo 2111435 12026177 := bstep (se 2 (by rfl) ⟨4509816, by rfl⟩ : syracuseStep 12026177 = 9019633) B9019633
theorem B8017451 : Blo 2111435 8017451 := bstep (se 1 (by rfl) ⟨6013088, by rfl⟩ : syracuseStep 8017451 = 12026177) B12026177
theorem B5344967 : Blo 2111435 5344967 := bstep (se 1 (by rfl) ⟨4008725, by rfl⟩ : syracuseStep 5344967 = 8017451) B8017451
theorem B3563311 : Blo 2111435 3563311 := bstep (se 1 (by rfl) ⟨2672483, by rfl⟩ : syracuseStep 3563311 = 5344967) B5344967
theorem B4751081 : Blo 2111435 4751081 := bstep (se 2 (by rfl) ⟨1781655, by rfl⟩ : syracuseStep 4751081 = 3563311) B3563311
theorem B3167387 : Blo 2111435 3167387 := bstep (se 1 (by rfl) ⟨2375540, by rfl⟩ : syracuseStep 3167387 = 4751081) B4751081
theorem B2111591 : Blo 2111435 2111591 := bstep (se 1 (by rfl) ⟨1583693, by rfl⟩ : syracuseStep 2111591 = 3167387) B3167387
theorem B2375545 : Blo 2111435 2375545 := bbase (se 2 (by rfl) ⟨890829, by rfl⟩ : syracuseStep 2375545 = 1781659) (by norm_num)
theorem B3167393 : Blo 2111435 3167393 := bstep (se 2 (by rfl) ⟨1187772, by rfl⟩ : syracuseStep 3167393 = 2375545) B2375545
theorem B2111595 : Blo 2111435 2111595 := bstep (se 1 (by rfl) ⟨1583696, by rfl⟩ : syracuseStep 2111595 = 3167393) B3167393
theorem B32507477 : Blo 2111435 32507477 := bbase (se 8 (by rfl) ⟨190473, by rfl⟩ : syracuseStep 32507477 = 380947) (by norm_num)
theorem B21671651 : Blo 2111435 21671651 := bstep (se 1 (by rfl) ⟨16253738, by rfl⟩ : syracuseStep 21671651 = 32507477) B32507477
theorem B14447767 : Blo 2111435 14447767 := bstep (se 1 (by rfl) ⟨10835825, by rfl⟩ : syracuseStep 14447767 = 21671651) B21671651
theorem B19263689 : Blo 2111435 19263689 := bstep (se 2 (by rfl) ⟨7223883, by rfl⟩ : syracuseStep 19263689 = 14447767) B14447767
theorem B12842459 : Blo 2111435 12842459 := bstep (se 1 (by rfl) ⟨9631844, by rfl⟩ : syracuseStep 12842459 = 19263689) B19263689
theorem B8561639 : Blo 2111435 8561639 := bstep (se 1 (by rfl) ⟨6421229, by rfl⟩ : syracuseStep 8561639 = 12842459) B12842459
theorem B5707759 : Blo 2111435 5707759 := bstep (se 1 (by rfl) ⟨4280819, by rfl⟩ : syracuseStep 5707759 = 8561639) B8561639
theorem B7610345 : Blo 2111435 7610345 := bstep (se 2 (by rfl) ⟨2853879, by rfl⟩ : syracuseStep 7610345 = 5707759) B5707759
theorem B5073563 : Blo 2111435 5073563 := bstep (se 1 (by rfl) ⟨3805172, by rfl⟩ : syracuseStep 5073563 = 7610345) B7610345
theorem B13529501 : Blo 2111435 13529501 := bstep (se 3 (by rfl) ⟨2536781, by rfl⟩ : syracuseStep 13529501 = 5073563) B5073563
theorem B9019667 : Blo 2111435 9019667 := bstep (se 1 (by rfl) ⟨6764750, by rfl⟩ : syracuseStep 9019667 = 13529501) B13529501
theorem B6013111 : Blo 2111435 6013111 := bstep (se 1 (by rfl) ⟨4509833, by rfl⟩ : syracuseStep 6013111 = 9019667) B9019667
theorem B8017481 : Blo 2111435 8017481 := bstep (se 2 (by rfl) ⟨3006555, by rfl⟩ : syracuseStep 8017481 = 6013111) B6013111
theorem B5344987 : Blo 2111435 5344987 := bstep (se 1 (by rfl) ⟨4008740, by rfl⟩ : syracuseStep 5344987 = 8017481) B8017481
theorem B7126649 : Blo 2111435 7126649 := bstep (se 2 (by rfl) ⟨2672493, by rfl⟩ : syracuseStep 7126649 = 5344987) B5344987
theorem B4751099 : Blo 2111435 4751099 := bstep (se 1 (by rfl) ⟨3563324, by rfl⟩ : syracuseStep 4751099 = 7126649) B7126649
theorem B3167399 : Blo 2111435 3167399 := bstep (se 1 (by rfl) ⟨2375549, by rfl⟩ : syracuseStep 3167399 = 4751099) B4751099
theorem B2111599 : Blo 2111435 2111599 := bstep (se 1 (by rfl) ⟨1583699, by rfl⟩ : syracuseStep 2111599 = 3167399) B3167399
theorem B3167405 : Blo 2111435 3167405 := bbase (se 3 (by rfl) ⟨593888, by rfl⟩ : syracuseStep 3167405 = 1187777) (by norm_num)
theorem B2111603 : Blo 2111435 2111603 := bstep (se 1 (by rfl) ⟨1583702, by rfl⟩ : syracuseStep 2111603 = 3167405) B3167405
theorem B4751117 : Blo 2111435 4751117 := bbase (se 3 (by rfl) ⟨890834, by rfl⟩ : syracuseStep 4751117 = 1781669) (by norm_num)
theorem B3167411 : Blo 2111435 3167411 := bstep (se 1 (by rfl) ⟨2375558, by rfl⟩ : syracuseStep 3167411 = 4751117) B4751117
theorem B2111607 : Blo 2111435 2111607 := bstep (se 1 (by rfl) ⟨1583705, by rfl⟩ : syracuseStep 2111607 = 3167411) B3167411
theorem B2672509 : Blo 2111435 2672509 := bbase (se 3 (by rfl) ⟨501095, by rfl⟩ : syracuseStep 2672509 = 1002191) (by norm_num)
theorem B3563345 : Blo 2111435 3563345 := bstep (se 2 (by rfl) ⟨1336254, by rfl⟩ : syracuseStep 3563345 = 2672509) B2672509
theorem B2375563 : Blo 2111435 2375563 := bstep (se 1 (by rfl) ⟨1781672, by rfl⟩ : syracuseStep 2375563 = 3563345) B3563345
theorem B3167417 : Blo 2111435 3167417 := bstep (se 2 (by rfl) ⟨1187781, by rfl⟩ : syracuseStep 3167417 = 2375563) B2375563
theorem B2111611 : Blo 2111435 2111611 := bstep (se 1 (by rfl) ⟨1583708, by rfl⟩ : syracuseStep 2111611 = 3167417) B3167417
theorem B2853901 : Blo 2111435 2853901 := bbase (se 3 (by rfl) ⟨535106, by rfl⟩ : syracuseStep 2853901 = 1070213) (by norm_num)
theorem B3805201 : Blo 2111435 3805201 := bstep (se 2 (by rfl) ⟨1426950, by rfl⟩ : syracuseStep 3805201 = 2853901) B2853901
theorem B5073601 : Blo 2111435 5073601 := bstep (se 2 (by rfl) ⟨1902600, by rfl⟩ : syracuseStep 5073601 = 3805201) B3805201
theorem B6764801 : Blo 2111435 6764801 := bstep (se 2 (by rfl) ⟨2536800, by rfl⟩ : syracuseStep 6764801 = 5073601) B5073601
theorem B18039469 : Blo 2111435 18039469 := bstep (se 3 (by rfl) ⟨3382400, by rfl⟩ : syracuseStep 18039469 = 6764801) B6764801
theorem B24052625 : Blo 2111435 24052625 := bstep (se 2 (by rfl) ⟨9019734, by rfl⟩ : syracuseStep 24052625 = 18039469) B18039469
theorem B16035083 : Blo 2111435 16035083 := bstep (se 1 (by rfl) ⟨12026312, by rfl⟩ : syracuseStep 16035083 = 24052625) B24052625
theorem B10690055 : Blo 2111435 10690055 := bstep (se 1 (by rfl) ⟨8017541, by rfl⟩ : syracuseStep 10690055 = 16035083) B16035083
theorem B7126703 : Blo 2111435 7126703 := bstep (se 1 (by rfl) ⟨5345027, by rfl⟩ : syracuseStep 7126703 = 10690055) B10690055
theorem B4751135 : Blo 2111435 4751135 := bstep (se 1 (by rfl) ⟨3563351, by rfl⟩ : syracuseStep 4751135 = 7126703) B7126703
theorem B3167423 : Blo 2111435 3167423 := bstep (se 1 (by rfl) ⟨2375567, by rfl⟩ : syracuseStep 3167423 = 4751135) B4751135
theorem B2111615 : Blo 2111435 2111615 := bstep (se 1 (by rfl) ⟨1583711, by rfl⟩ : syracuseStep 2111615 = 3167423) B3167423
theorem B3167429 : Blo 2111435 3167429 := bbase (se 4 (by rfl) ⟨296946, by rfl⟩ : syracuseStep 3167429 = 593893) (by norm_num)
theorem B2111619 : Blo 2111435 2111619 := bstep (se 1 (by rfl) ⟨1583714, by rfl⟩ : syracuseStep 2111619 = 3167429) B3167429
theorem B3563365 : Blo 2111435 3563365 := bbase (se 4 (by rfl) ⟨334065, by rfl⟩ : syracuseStep 3563365 = 668131) (by norm_num)
theorem B4751153 : Blo 2111435 4751153 := bstep (se 2 (by rfl) ⟨1781682, by rfl⟩ : syracuseStep 4751153 = 3563365) B3563365
theorem B3167435 : Blo 2111435 3167435 := bstep (se 1 (by rfl) ⟨2375576, by rfl⟩ : syracuseStep 3167435 = 4751153) B4751153
theorem B2111623 : Blo 2111435 2111623 := bstep (se 1 (by rfl) ⟨1583717, by rfl⟩ : syracuseStep 2111623 = 3167435) B3167435
theorem B2375581 : Blo 2111435 2375581 := bbase (se 3 (by rfl) ⟨445421, by rfl⟩ : syracuseStep 2375581 = 890843) (by norm_num)
theorem B3167441 : Blo 2111435 3167441 := bstep (se 2 (by rfl) ⟨1187790, by rfl⟩ : syracuseStep 3167441 = 2375581) B2375581
theorem B2111627 : Blo 2111435 2111627 := bstep (se 1 (by rfl) ⟨1583720, by rfl⟩ : syracuseStep 2111627 = 3167441) B3167441
theorem B7126757 : Blo 2111435 7126757 := bbase (se 4 (by rfl) ⟨668133, by rfl⟩ : syracuseStep 7126757 = 1336267) (by norm_num)
theorem B4751171 : Blo 2111435 4751171 := bstep (se 1 (by rfl) ⟨3563378, by rfl⟩ : syracuseStep 4751171 = 7126757) B7126757
theorem B3167447 : Blo 2111435 3167447 := bstep (se 1 (by rfl) ⟨2375585, by rfl⟩ : syracuseStep 3167447 = 4751171) B4751171
theorem B2111631 : Blo 2111435 2111631 := bstep (se 1 (by rfl) ⟨1583723, by rfl⟩ : syracuseStep 2111631 = 3167447) B3167447
theorem B3167453 : Blo 2111435 3167453 := bbase (se 3 (by rfl) ⟨593897, by rfl⟩ : syracuseStep 3167453 = 1187795) (by norm_num)
theorem B2111635 : Blo 2111435 2111635 := bstep (se 1 (by rfl) ⟨1583726, by rfl⟩ : syracuseStep 2111635 = 3167453) B3167453
theorem B4751189 : Blo 2111435 4751189 := bbase (se 9 (by rfl) ⟨13919, by rfl⟩ : syracuseStep 4751189 = 27839) (by norm_num)
theorem B3167459 : Blo 2111435 3167459 := bstep (se 1 (by rfl) ⟨2375594, by rfl⟩ : syracuseStep 3167459 = 4751189) B4751189
theorem B2111639 : Blo 2111435 2111639 := bstep (se 1 (by rfl) ⟨1583729, by rfl⟩ : syracuseStep 2111639 = 3167459) B3167459
theorem B6013237 : Blo 2111435 6013237 := bbase (se 5 (by rfl) ⟨281870, by rfl⟩ : syracuseStep 6013237 = 563741) (by norm_num)
theorem B8017649 : Blo 2111435 8017649 := bstep (se 2 (by rfl) ⟨3006618, by rfl⟩ : syracuseStep 8017649 = 6013237) B6013237
theorem B5345099 : Blo 2111435 5345099 := bstep (se 1 (by rfl) ⟨4008824, by rfl⟩ : syracuseStep 5345099 = 8017649) B8017649
theorem B3563399 : Blo 2111435 3563399 := bstep (se 1 (by rfl) ⟨2672549, by rfl⟩ : syracuseStep 3563399 = 5345099) B5345099
theorem B2375599 : Blo 2111435 2375599 := bstep (se 1 (by rfl) ⟨1781699, by rfl⟩ : syracuseStep 2375599 = 3563399) B3563399
theorem B3167465 : Blo 2111435 3167465 := bstep (se 2 (by rfl) ⟨1187799, by rfl⟩ : syracuseStep 3167465 = 2375599) B2375599
theorem B2111643 : Blo 2111435 2111643 := bstep (se 1 (by rfl) ⟨1583732, by rfl⟩ : syracuseStep 2111643 = 3167465) B3167465
theorem B10426133 : Blo 2111435 10426133 := bbase (se 6 (by rfl) ⟨244362, by rfl⟩ : syracuseStep 10426133 = 488725) (by norm_num)
theorem B6950755 : Blo 2111435 6950755 := bstep (se 1 (by rfl) ⟨5213066, by rfl⟩ : syracuseStep 6950755 = 10426133) B10426133
theorem B37070693 : Blo 2111435 37070693 := bstep (se 4 (by rfl) ⟨3475377, by rfl⟩ : syracuseStep 37070693 = 6950755) B6950755
theorem B24713795 : Blo 2111435 24713795 := bstep (se 1 (by rfl) ⟨18535346, by rfl⟩ : syracuseStep 24713795 = 37070693) B37070693
theorem B65903453 : Blo 2111435 65903453 := bstep (se 3 (by rfl) ⟨12356897, by rfl⟩ : syracuseStep 65903453 = 24713795) B24713795
theorem B43935635 : Blo 2111435 43935635 := bstep (se 1 (by rfl) ⟨32951726, by rfl⟩ : syracuseStep 43935635 = 65903453) B65903453
theorem B29290423 : Blo 2111435 29290423 := bstep (se 1 (by rfl) ⟨21967817, by rfl⟩ : syracuseStep 29290423 = 43935635) B43935635
theorem B39053897 : Blo 2111435 39053897 := bstep (se 2 (by rfl) ⟨14645211, by rfl⟩ : syracuseStep 39053897 = 29290423) B29290423
theorem B26035931 : Blo 2111435 26035931 := bstep (se 1 (by rfl) ⟨19526948, by rfl⟩ : syracuseStep 26035931 = 39053897) B39053897
theorem B69429149 : Blo 2111435 69429149 := bstep (se 3 (by rfl) ⟨13017965, by rfl⟩ : syracuseStep 69429149 = 26035931) B26035931
theorem B46286099 : Blo 2111435 46286099 := bstep (se 1 (by rfl) ⟨34714574, by rfl⟩ : syracuseStep 46286099 = 69429149) B69429149
theorem B30857399 : Blo 2111435 30857399 := bstep (se 1 (by rfl) ⟨23143049, by rfl⟩ : syracuseStep 30857399 = 46286099) B46286099
theorem B20571599 : Blo 2111435 20571599 := bstep (se 1 (by rfl) ⟨15428699, by rfl⟩ : syracuseStep 20571599 = 30857399) B30857399
theorem B13714399 : Blo 2111435 13714399 := bstep (se 1 (by rfl) ⟨10285799, by rfl⟩ : syracuseStep 13714399 = 20571599) B20571599
theorem B73143461 : Blo 2111435 73143461 := bstep (se 4 (by rfl) ⟨6857199, by rfl⟩ : syracuseStep 73143461 = 13714399) B13714399
theorem B48762307 : Blo 2111435 48762307 := bstep (se 1 (by rfl) ⟨36571730, by rfl⟩ : syracuseStep 48762307 = 73143461) B73143461
theorem B260065637 : Blo 2111435 260065637 := bstep (se 4 (by rfl) ⟨24381153, by rfl⟩ : syracuseStep 260065637 = 48762307) B48762307
theorem B173377091 : Blo 2111435 173377091 := bstep (se 1 (by rfl) ⟨130032818, by rfl⟩ : syracuseStep 173377091 = 260065637) B260065637
theorem B115584727 : Blo 2111435 115584727 := bstep (se 1 (by rfl) ⟨86688545, by rfl⟩ : syracuseStep 115584727 = 173377091) B173377091
theorem B154112969 : Blo 2111435 154112969 := bstep (se 2 (by rfl) ⟨57792363, by rfl⟩ : syracuseStep 154112969 = 115584727) B115584727
theorem B102741979 : Blo 2111435 102741979 := bstep (se 1 (by rfl) ⟨77056484, by rfl⟩ : syracuseStep 102741979 = 154112969) B154112969
theorem B136989305 : Blo 2111435 136989305 := bstep (se 2 (by rfl) ⟨51370989, by rfl⟩ : syracuseStep 136989305 = 102741979) B102741979
theorem B91326203 : Blo 2111435 91326203 := bstep (se 1 (by rfl) ⟨68494652, by rfl⟩ : syracuseStep 91326203 = 136989305) B136989305
theorem B60884135 : Blo 2111435 60884135 := bstep (se 1 (by rfl) ⟨45663101, by rfl⟩ : syracuseStep 60884135 = 91326203) B91326203
theorem B40589423 : Blo 2111435 40589423 := bstep (se 1 (by rfl) ⟨30442067, by rfl⟩ : syracuseStep 40589423 = 60884135) B60884135
theorem B27059615 : Blo 2111435 27059615 := bstep (se 1 (by rfl) ⟨20294711, by rfl⟩ : syracuseStep 27059615 = 40589423) B40589423
theorem B18039743 : Blo 2111435 18039743 := bstep (se 1 (by rfl) ⟨13529807, by rfl⟩ : syracuseStep 18039743 = 27059615) B27059615
theorem B12026495 : Blo 2111435 12026495 := bstep (se 1 (by rfl) ⟨9019871, by rfl⟩ : syracuseStep 12026495 = 18039743) B18039743
theorem B8017663 : Blo 2111435 8017663 := bstep (se 1 (by rfl) ⟨6013247, by rfl⟩ : syracuseStep 8017663 = 12026495) B12026495
theorem B10690217 : Blo 2111435 10690217 := bstep (se 2 (by rfl) ⟨4008831, by rfl⟩ : syracuseStep 10690217 = 8017663) B8017663
theorem B7126811 : Blo 2111435 7126811 := bstep (se 1 (by rfl) ⟨5345108, by rfl⟩ : syracuseStep 7126811 = 10690217) B10690217
theorem B4751207 : Blo 2111435 4751207 := bstep (se 1 (by rfl) ⟨3563405, by rfl⟩ : syracuseStep 4751207 = 7126811) B7126811
theorem B3167471 : Blo 2111435 3167471 := bstep (se 1 (by rfl) ⟨2375603, by rfl⟩ : syracuseStep 3167471 = 4751207) B4751207
theorem B2111647 : Blo 2111435 2111647 := bstep (se 1 (by rfl) ⟨1583735, by rfl⟩ : syracuseStep 2111647 = 3167471) B3167471
theorem B3167477 : Blo 2111435 3167477 := bbase (se 5 (by rfl) ⟨148475, by rfl⟩ : syracuseStep 3167477 = 296951) (by norm_num)
theorem B2111651 : Blo 2111435 2111651 := bstep (se 1 (by rfl) ⟨1583738, by rfl⟩ : syracuseStep 2111651 = 3167477) B3167477
theorem B2536849 : Blo 2111435 2536849 := bbase (se 2 (by rfl) ⟨951318, by rfl⟩ : syracuseStep 2536849 = 1902637) (by norm_num)
theorem B13529861 : Blo 2111435 13529861 := bstep (se 4 (by rfl) ⟨1268424, by rfl⟩ : syracuseStep 13529861 = 2536849) B2536849
theorem B9019907 : Blo 2111435 9019907 := bstep (se 1 (by rfl) ⟨6764930, by rfl⟩ : syracuseStep 9019907 = 13529861) B13529861
theorem B6013271 : Blo 2111435 6013271 := bstep (se 1 (by rfl) ⟨4509953, by rfl⟩ : syracuseStep 6013271 = 9019907) B9019907
theorem B4008847 : Blo 2111435 4008847 := bstep (se 1 (by rfl) ⟨3006635, by rfl⟩ : syracuseStep 4008847 = 6013271) B6013271
theorem B5345129 : Blo 2111435 5345129 := bstep (se 2 (by rfl) ⟨2004423, by rfl⟩ : syracuseStep 5345129 = 4008847) B4008847
theorem B3563419 : Blo 2111435 3563419 := bstep (se 1 (by rfl) ⟨2672564, by rfl⟩ : syracuseStep 3563419 = 5345129) B5345129
theorem B4751225 : Blo 2111435 4751225 := bstep (se 2 (by rfl) ⟨1781709, by rfl⟩ : syracuseStep 4751225 = 3563419) B3563419
theorem B3167483 : Blo 2111435 3167483 := bstep (se 1 (by rfl) ⟨2375612, by rfl⟩ : syracuseStep 3167483 = 4751225) B4751225
theorem B2111655 : Blo 2111435 2111655 := bstep (se 1 (by rfl) ⟨1583741, by rfl⟩ : syracuseStep 2111655 = 3167483) B3167483
theorem B2375617 : Blo 2111435 2375617 := bbase (se 2 (by rfl) ⟨890856, by rfl⟩ : syracuseStep 2375617 = 1781713) (by norm_num)
theorem B3167489 : Blo 2111435 3167489 := bstep (se 2 (by rfl) ⟨1187808, by rfl⟩ : syracuseStep 3167489 = 2375617) B2375617
theorem B2111659 : Blo 2111435 2111659 := bstep (se 1 (by rfl) ⟨1583744, by rfl⟩ : syracuseStep 2111659 = 3167489) B3167489
theorem B5345149 : Blo 2111435 5345149 := bbase (se 3 (by rfl) ⟨1002215, by rfl⟩ : syracuseStep 5345149 = 2004431) (by norm_num)
theorem B7126865 : Blo 2111435 7126865 := bstep (se 2 (by rfl) ⟨2672574, by rfl⟩ : syracuseStep 7126865 = 5345149) B5345149
theorem B4751243 : Blo 2111435 4751243 := bstep (se 1 (by rfl) ⟨3563432, by rfl⟩ : syracuseStep 4751243 = 7126865) B7126865
theorem B3167495 : Blo 2111435 3167495 := bstep (se 1 (by rfl) ⟨2375621, by rfl⟩ : syracuseStep 3167495 = 4751243) B4751243
theorem B2111663 : Blo 2111435 2111663 := bstep (se 1 (by rfl) ⟨1583747, by rfl⟩ : syracuseStep 2111663 = 3167495) B3167495
theorem B3167501 : Blo 2111435 3167501 := bbase (se 3 (by rfl) ⟨593906, by rfl⟩ : syracuseStep 3167501 = 1187813) (by norm_num)
theorem B2111667 : Blo 2111435 2111667 := bstep (se 1 (by rfl) ⟨1583750, by rfl⟩ : syracuseStep 2111667 = 3167501) B3167501
theorem B4751261 : Blo 2111435 4751261 := bbase (se 3 (by rfl) ⟨890861, by rfl⟩ : syracuseStep 4751261 = 1781723) (by norm_num)
theorem B3167507 : Blo 2111435 3167507 := bstep (se 1 (by rfl) ⟨2375630, by rfl⟩ : syracuseStep 3167507 = 4751261) B4751261
theorem B2111671 : Blo 2111435 2111671 := bstep (se 1 (by rfl) ⟨1583753, by rfl⟩ : syracuseStep 2111671 = 3167507) B3167507
theorem B3563453 : Blo 2111435 3563453 := bbase (se 3 (by rfl) ⟨668147, by rfl⟩ : syracuseStep 3563453 = 1336295) (by norm_num)
theorem B2375635 : Blo 2111435 2375635 := bstep (se 1 (by rfl) ⟨1781726, by rfl⟩ : syracuseStep 2375635 = 3563453) B3563453
theorem B3167513 : Blo 2111435 3167513 := bstep (se 2 (by rfl) ⟨1187817, by rfl⟩ : syracuseStep 3167513 = 2375635) B2375635
theorem B2111675 : Blo 2111435 2111675 := bstep (se 1 (by rfl) ⟨1583756, by rfl⟩ : syracuseStep 2111675 = 3167513) B3167513
theorem B12026677 : Blo 2111435 12026677 := bbase (se 5 (by rfl) ⟨563750, by rfl⟩ : syracuseStep 12026677 = 1127501) (by norm_num)
theorem B16035569 : Blo 2111435 16035569 := bstep (se 2 (by rfl) ⟨6013338, by rfl⟩ : syracuseStep 16035569 = 12026677) B12026677
theorem B10690379 : Blo 2111435 10690379 := bstep (se 1 (by rfl) ⟨8017784, by rfl⟩ : syracuseStep 10690379 = 16035569) B16035569
theorem B7126919 : Blo 2111435 7126919 := bstep (se 1 (by rfl) ⟨5345189, by rfl⟩ : syracuseStep 7126919 = 10690379) B10690379
theorem B4751279 : Blo 2111435 4751279 := bstep (se 1 (by rfl) ⟨3563459, by rfl⟩ : syracuseStep 4751279 = 7126919) B7126919
theorem B3167519 : Blo 2111435 3167519 := bstep (se 1 (by rfl) ⟨2375639, by rfl⟩ : syracuseStep 3167519 = 4751279) B4751279
theorem B2111679 : Blo 2111435 2111679 := bstep (se 1 (by rfl) ⟨1583759, by rfl⟩ : syracuseStep 2111679 = 3167519) B3167519
theorem B3167525 : Blo 2111435 3167525 := bbase (se 4 (by rfl) ⟨296955, by rfl⟩ : syracuseStep 3167525 = 593911) (by norm_num)
theorem B2111683 : Blo 2111435 2111683 := bstep (se 1 (by rfl) ⟨1583762, by rfl⟩ : syracuseStep 2111683 = 3167525) B3167525
theorem B2672605 : Blo 2111435 2672605 := bbase (se 3 (by rfl) ⟨501113, by rfl⟩ : syracuseStep 2672605 = 1002227) (by norm_num)
theorem B3563473 : Blo 2111435 3563473 := bstep (se 2 (by rfl) ⟨1336302, by rfl⟩ : syracuseStep 3563473 = 2672605) B2672605
theorem B4751297 : Blo 2111435 4751297 := bstep (se 2 (by rfl) ⟨1781736, by rfl⟩ : syracuseStep 4751297 = 3563473) B3563473
theorem B3167531 : Blo 2111435 3167531 := bstep (se 1 (by rfl) ⟨2375648, by rfl⟩ : syracuseStep 3167531 = 4751297) B4751297
theorem B2111687 : Blo 2111435 2111687 := bstep (se 1 (by rfl) ⟨1583765, by rfl⟩ : syracuseStep 2111687 = 3167531) B3167531
theorem B2375653 : Blo 2111435 2375653 := bbase (se 4 (by rfl) ⟨222717, by rfl⟩ : syracuseStep 2375653 = 445435) (by norm_num)
theorem B3167537 : Blo 2111435 3167537 := bstep (se 2 (by rfl) ⟨1187826, by rfl⟩ : syracuseStep 3167537 = 2375653) B2375653
theorem B2111691 : Blo 2111435 2111691 := bstep (se 1 (by rfl) ⟨1583768, by rfl⟩ : syracuseStep 2111691 = 3167537) B3167537
theorem B10147589 : Blo 2111435 10147589 := bbase (se 4 (by rfl) ⟨951336, by rfl⟩ : syracuseStep 10147589 = 1902673) (by norm_num)
theorem B6765059 : Blo 2111435 6765059 := bstep (se 1 (by rfl) ⟨5073794, by rfl⟩ : syracuseStep 6765059 = 10147589) B10147589
theorem B4510039 : Blo 2111435 4510039 := bstep (se 1 (by rfl) ⟨3382529, by rfl⟩ : syracuseStep 4510039 = 6765059) B6765059
theorem B6013385 : Blo 2111435 6013385 := bstep (se 2 (by rfl) ⟨2255019, by rfl⟩ : syracuseStep 6013385 = 4510039) B4510039
theorem B4008923 : Blo 2111435 4008923 := bstep (se 1 (by rfl) ⟨3006692, by rfl⟩ : syracuseStep 4008923 = 6013385) B6013385
theorem B2672615 : Blo 2111435 2672615 := bstep (se 1 (by rfl) ⟨2004461, by rfl⟩ : syracuseStep 2672615 = 4008923) B4008923
theorem B7126973 : Blo 2111435 7126973 := bstep (se 3 (by rfl) ⟨1336307, by rfl⟩ : syracuseStep 7126973 = 2672615) B2672615
theorem B4751315 : Blo 2111435 4751315 := bstep (se 1 (by rfl) ⟨3563486, by rfl⟩ : syracuseStep 4751315 = 7126973) B7126973
theorem B3167543 : Blo 2111435 3167543 := bstep (se 1 (by rfl) ⟨2375657, by rfl⟩ : syracuseStep 3167543 = 4751315) B4751315
theorem B2111695 : Blo 2111435 2111695 := bstep (se 1 (by rfl) ⟨1583771, by rfl⟩ : syracuseStep 2111695 = 3167543) B3167543
theorem B3167549 : Blo 2111435 3167549 := bbase (se 3 (by rfl) ⟨593915, by rfl⟩ : syracuseStep 3167549 = 1187831) (by norm_num)
theorem B2111699 : Blo 2111435 2111699 := bstep (se 1 (by rfl) ⟨1583774, by rfl⟩ : syracuseStep 2111699 = 3167549) B3167549
theorem B4751333 : Blo 2111435 4751333 := bbase (se 4 (by rfl) ⟨445437, by rfl⟩ : syracuseStep 4751333 = 890875) (by norm_num)
theorem B3167555 : Blo 2111435 3167555 := bstep (se 1 (by rfl) ⟨2375666, by rfl⟩ : syracuseStep 3167555 = 4751333) B4751333
theorem B2111703 : Blo 2111435 2111703 := bstep (se 1 (by rfl) ⟨1583777, by rfl⟩ : syracuseStep 2111703 = 3167555) B3167555
theorem B5345261 : Blo 2111435 5345261 := bbase (se 3 (by rfl) ⟨1002236, by rfl⟩ : syracuseStep 5345261 = 2004473) (by norm_num)
theorem B3563507 : Blo 2111435 3563507 := bstep (se 1 (by rfl) ⟨2672630, by rfl⟩ : syracuseStep 3563507 = 5345261) B5345261
theorem B2375671 : Blo 2111435 2375671 := bstep (se 1 (by rfl) ⟨1781753, by rfl⟩ : syracuseStep 2375671 = 3563507) B3563507
theorem B3167561 : Blo 2111435 3167561 := bstep (se 2 (by rfl) ⟨1187835, by rfl⟩ : syracuseStep 3167561 = 2375671) B2375671
theorem B2111707 : Blo 2111435 2111707 := bstep (se 1 (by rfl) ⟨1583780, by rfl⟩ : syracuseStep 2111707 = 3167561) B3167561
theorem B6095477 : Blo 2111435 6095477 := bbase (se 5 (by rfl) ⟨285725, by rfl⟩ : syracuseStep 6095477 = 571451) (by norm_num)
theorem B4063651 : Blo 2111435 4063651 := bstep (se 1 (by rfl) ⟨3047738, by rfl⟩ : syracuseStep 4063651 = 6095477) B6095477
theorem B21672805 : Blo 2111435 21672805 := bstep (se 4 (by rfl) ⟨2031825, by rfl⟩ : syracuseStep 21672805 = 4063651) B4063651
theorem B28897073 : Blo 2111435 28897073 := bstep (se 2 (by rfl) ⟨10836402, by rfl⟩ : syracuseStep 28897073 = 21672805) B21672805
theorem B19264715 : Blo 2111435 19264715 := bstep (se 1 (by rfl) ⟨14448536, by rfl⟩ : syracuseStep 19264715 = 28897073) B28897073
theorem B12843143 : Blo 2111435 12843143 := bstep (se 1 (by rfl) ⟨9632357, by rfl⟩ : syracuseStep 12843143 = 19264715) B19264715
theorem B8562095 : Blo 2111435 8562095 := bstep (se 1 (by rfl) ⟨6421571, by rfl⟩ : syracuseStep 8562095 = 12843143) B12843143
theorem B5708063 : Blo 2111435 5708063 := bstep (se 1 (by rfl) ⟨4281047, by rfl⟩ : syracuseStep 5708063 = 8562095) B8562095
theorem B3805375 : Blo 2111435 3805375 := bstep (se 1 (by rfl) ⟨2854031, by rfl⟩ : syracuseStep 3805375 = 5708063) B5708063
theorem B5073833 : Blo 2111435 5073833 := bstep (se 2 (by rfl) ⟨1902687, by rfl⟩ : syracuseStep 5073833 = 3805375) B3805375
theorem B3382555 : Blo 2111435 3382555 := bstep (se 1 (by rfl) ⟨2536916, by rfl⟩ : syracuseStep 3382555 = 5073833) B5073833
theorem B4510073 : Blo 2111435 4510073 := bstep (se 2 (by rfl) ⟨1691277, by rfl⟩ : syracuseStep 4510073 = 3382555) B3382555
theorem B3006715 : Blo 2111435 3006715 := bstep (se 1 (by rfl) ⟨2255036, by rfl⟩ : syracuseStep 3006715 = 4510073) B4510073
theorem B4008953 : Blo 2111435 4008953 := bstep (se 2 (by rfl) ⟨1503357, by rfl⟩ : syracuseStep 4008953 = 3006715) B3006715
theorem B10690541 : Blo 2111435 10690541 := bstep (se 3 (by rfl) ⟨2004476, by rfl⟩ : syracuseStep 10690541 = 4008953) B4008953
theorem B7127027 : Blo 2111435 7127027 := bstep (se 1 (by rfl) ⟨5345270, by rfl⟩ : syracuseStep 7127027 = 10690541) B10690541
theorem B4751351 : Blo 2111435 4751351 := bstep (se 1 (by rfl) ⟨3563513, by rfl⟩ : syracuseStep 4751351 = 7127027) B7127027
theorem B3167567 : Blo 2111435 3167567 := bstep (se 1 (by rfl) ⟨2375675, by rfl⟩ : syracuseStep 3167567 = 4751351) B4751351
theorem B2111711 : Blo 2111435 2111711 := bstep (se 1 (by rfl) ⟨1583783, by rfl⟩ : syracuseStep 2111711 = 3167567) B3167567
theorem B3167573 : Blo 2111435 3167573 := bbase (se 16 (by rfl) ⟨72, by rfl⟩ : syracuseStep 3167573 = 145) (by norm_num)
theorem B2111715 : Blo 2111435 2111715 := bstep (se 1 (by rfl) ⟨1583786, by rfl⟩ : syracuseStep 2111715 = 3167573) B3167573
theorem B2255045 : Blo 2111435 2255045 := bbase (se 4 (by rfl) ⟨211410, by rfl⟩ : syracuseStep 2255045 = 422821) (by norm_num)
theorem B6013453 : Blo 2111435 6013453 := bstep (se 3 (by rfl) ⟨1127522, by rfl⟩ : syracuseStep 6013453 = 2255045) B2255045
theorem B8017937 : Blo 2111435 8017937 := bstep (se 2 (by rfl) ⟨3006726, by rfl⟩ : syracuseStep 8017937 = 6013453) B6013453
theorem B5345291 : Blo 2111435 5345291 := bstep (se 1 (by rfl) ⟨4008968, by rfl⟩ : syracuseStep 5345291 = 8017937) B8017937
theorem B3563527 : Blo 2111435 3563527 := bstep (se 1 (by rfl) ⟨2672645, by rfl⟩ : syracuseStep 3563527 = 5345291) B5345291
theorem B4751369 : Blo 2111435 4751369 := bstep (se 2 (by rfl) ⟨1781763, by rfl⟩ : syracuseStep 4751369 = 3563527) B3563527
theorem B3167579 : Blo 2111435 3167579 := bstep (se 1 (by rfl) ⟨2375684, by rfl⟩ : syracuseStep 3167579 = 4751369) B4751369
theorem B2111719 : Blo 2111435 2111719 := bstep (se 1 (by rfl) ⟨1583789, by rfl⟩ : syracuseStep 2111719 = 3167579) B3167579
theorem B2375689 : Blo 2111435 2375689 := bbase (se 2 (by rfl) ⟨890883, by rfl⟩ : syracuseStep 2375689 = 1781767) (by norm_num)
theorem B3167585 : Blo 2111435 3167585 := bstep (se 2 (by rfl) ⟨1187844, by rfl⟩ : syracuseStep 3167585 = 2375689) B2375689
theorem B2111723 : Blo 2111435 2111723 := bstep (se 1 (by rfl) ⟨1583792, by rfl⟩ : syracuseStep 2111723 = 3167585) B3167585
theorem B19264853 : Blo 2111435 19264853 := bbase (se 13 (by rfl) ⟨3527, by rfl⟩ : syracuseStep 19264853 = 7055) (by norm_num)
theorem B12843235 : Blo 2111435 12843235 := bstep (se 1 (by rfl) ⟨9632426, by rfl⟩ : syracuseStep 12843235 = 19264853) B19264853
theorem B17124313 : Blo 2111435 17124313 := bstep (se 2 (by rfl) ⟨6421617, by rfl⟩ : syracuseStep 17124313 = 12843235) B12843235
theorem B22832417 : Blo 2111435 22832417 := bstep (se 2 (by rfl) ⟨8562156, by rfl⟩ : syracuseStep 22832417 = 17124313) B17124313
theorem B15221611 : Blo 2111435 15221611 := bstep (se 1 (by rfl) ⟨11416208, by rfl⟩ : syracuseStep 15221611 = 22832417) B22832417
theorem B20295481 : Blo 2111435 20295481 := bstep (se 2 (by rfl) ⟨7610805, by rfl⟩ : syracuseStep 20295481 = 15221611) B15221611
theorem B27060641 : Blo 2111435 27060641 := bstep (se 2 (by rfl) ⟨10147740, by rfl⟩ : syracuseStep 27060641 = 20295481) B20295481
theorem B18040427 : Blo 2111435 18040427 := bstep (se 1 (by rfl) ⟨13530320, by rfl⟩ : syracuseStep 18040427 = 27060641) B27060641
theorem B12026951 : Blo 2111435 12026951 := bstep (se 1 (by rfl) ⟨9020213, by rfl⟩ : syracuseStep 12026951 = 18040427) B18040427
theorem B8017967 : Blo 2111435 8017967 := bstep (se 1 (by rfl) ⟨6013475, by rfl⟩ : syracuseStep 8017967 = 12026951) B12026951
theorem B5345311 : Blo 2111435 5345311 := bstep (se 1 (by rfl) ⟨4008983, by rfl⟩ : syracuseStep 5345311 = 8017967) B8017967
theorem B7127081 : Blo 2111435 7127081 := bstep (se 2 (by rfl) ⟨2672655, by rfl⟩ : syracuseStep 7127081 = 5345311) B5345311
theorem B4751387 : Blo 2111435 4751387 := bstep (se 1 (by rfl) ⟨3563540, by rfl⟩ : syracuseStep 4751387 = 7127081) B7127081
theorem B3167591 : Blo 2111435 3167591 := bstep (se 1 (by rfl) ⟨2375693, by rfl⟩ : syracuseStep 3167591 = 4751387) B4751387
theorem B2111727 : Blo 2111435 2111727 := bstep (se 1 (by rfl) ⟨1583795, by rfl⟩ : syracuseStep 2111727 = 3167591) B3167591
theorem B3167597 : Blo 2111435 3167597 := bbase (se 3 (by rfl) ⟨593924, by rfl⟩ : syracuseStep 3167597 = 1187849) (by norm_num)
theorem B2111731 : Blo 2111435 2111731 := bstep (se 1 (by rfl) ⟨1583798, by rfl⟩ : syracuseStep 2111731 = 3167597) B3167597
theorem B4751405 : Blo 2111435 4751405 := bbase (se 3 (by rfl) ⟨890888, by rfl⟩ : syracuseStep 4751405 = 1781777) (by norm_num)
theorem B3167603 : Blo 2111435 3167603 := bstep (se 1 (by rfl) ⟨2375702, by rfl⟩ : syracuseStep 3167603 = 4751405) B4751405
theorem B2111735 : Blo 2111435 2111735 := bstep (se 1 (by rfl) ⟨1583801, by rfl⟩ : syracuseStep 2111735 = 3167603) B3167603
theorem B11416277 : Blo 2111435 11416277 := bbase (se 7 (by rfl) ⟨133784, by rfl⟩ : syracuseStep 11416277 = 267569) (by norm_num)
theorem B7610851 : Blo 2111435 7610851 := bstep (se 1 (by rfl) ⟨5708138, by rfl⟩ : syracuseStep 7610851 = 11416277) B11416277
theorem B10147801 : Blo 2111435 10147801 := bstep (se 2 (by rfl) ⟨3805425, by rfl⟩ : syracuseStep 10147801 = 7610851) B7610851
theorem B13530401 : Blo 2111435 13530401 := bstep (se 2 (by rfl) ⟨5073900, by rfl⟩ : syracuseStep 13530401 = 10147801) B10147801
theorem B9020267 : Blo 2111435 9020267 := bstep (se 1 (by rfl) ⟨6765200, by rfl⟩ : syracuseStep 9020267 = 13530401) B13530401
theorem B6013511 : Blo 2111435 6013511 := bstep (se 1 (by rfl) ⟨4510133, by rfl⟩ : syracuseStep 6013511 = 9020267) B9020267
theorem B4009007 : Blo 2111435 4009007 := bstep (se 1 (by rfl) ⟨3006755, by rfl⟩ : syracuseStep 4009007 = 6013511) B6013511
theorem B2672671 : Blo 2111435 2672671 := bstep (se 1 (by rfl) ⟨2004503, by rfl⟩ : syracuseStep 2672671 = 4009007) B4009007
theorem B3563561 : Blo 2111435 3563561 := bstep (se 2 (by rfl) ⟨1336335, by rfl⟩ : syracuseStep 3563561 = 2672671) B2672671
theorem B2375707 : Blo 2111435 2375707 := bstep (se 1 (by rfl) ⟨1781780, by rfl⟩ : syracuseStep 2375707 = 3563561) B3563561
theorem B3167609 : Blo 2111435 3167609 := bstep (se 2 (by rfl) ⟨1187853, by rfl⟩ : syracuseStep 3167609 = 2375707) B2375707
theorem B2111739 : Blo 2111435 2111739 := bstep (se 1 (by rfl) ⟨1583804, by rfl⟩ : syracuseStep 2111739 = 3167609) B3167609
theorem B4290061 : Blo 2111435 4290061 := bbase (se 3 (by rfl) ⟨804386, by rfl⟩ : syracuseStep 4290061 = 1608773) (by norm_num)
theorem B5720081 : Blo 2111435 5720081 := bstep (se 2 (by rfl) ⟨2145030, by rfl⟩ : syracuseStep 5720081 = 4290061) B4290061
theorem B61014197 : Blo 2111435 61014197 := bstep (se 5 (by rfl) ⟨2860040, by rfl⟩ : syracuseStep 61014197 = 5720081) B5720081
theorem B40676131 : Blo 2111435 40676131 := bstep (se 1 (by rfl) ⟨30507098, by rfl⟩ : syracuseStep 40676131 = 61014197) B61014197
theorem B54234841 : Blo 2111435 54234841 := bstep (se 2 (by rfl) ⟨20338065, by rfl⟩ : syracuseStep 54234841 = 40676131) B40676131
theorem B72313121 : Blo 2111435 72313121 := bstep (se 2 (by rfl) ⟨27117420, by rfl⟩ : syracuseStep 72313121 = 54234841) B54234841
theorem B192834989 : Blo 2111435 192834989 := bstep (se 3 (by rfl) ⟨36156560, by rfl⟩ : syracuseStep 192834989 = 72313121) B72313121
theorem B128556659 : Blo 2111435 128556659 := bstep (se 1 (by rfl) ⟨96417494, by rfl⟩ : syracuseStep 128556659 = 192834989) B192834989
theorem B342817757 : Blo 2111435 342817757 := bstep (se 3 (by rfl) ⟨64278329, by rfl⟩ : syracuseStep 342817757 = 128556659) B128556659
theorem B228545171 : Blo 2111435 228545171 := bstep (se 1 (by rfl) ⟨171408878, by rfl⟩ : syracuseStep 228545171 = 342817757) B342817757
theorem B152363447 : Blo 2111435 152363447 := bstep (se 1 (by rfl) ⟨114272585, by rfl⟩ : syracuseStep 152363447 = 228545171) B228545171
theorem B101575631 : Blo 2111435 101575631 := bstep (se 1 (by rfl) ⟨76181723, by rfl⟩ : syracuseStep 101575631 = 152363447) B152363447
theorem B67717087 : Blo 2111435 67717087 := bstep (se 1 (by rfl) ⟨50787815, by rfl⟩ : syracuseStep 67717087 = 101575631) B101575631
theorem B361157797 : Blo 2111435 361157797 := bstep (se 4 (by rfl) ⟨33858543, by rfl⟩ : syracuseStep 361157797 = 67717087) B67717087
theorem B1926174917 : Blo 2111435 1926174917 := bstep (se 4 (by rfl) ⟨180578898, by rfl⟩ : syracuseStep 1926174917 = 361157797) B361157797
theorem B1284116611 : Blo 2111435 1284116611 := bstep (se 1 (by rfl) ⟨963087458, by rfl⟩ : syracuseStep 1284116611 = 1926174917) B1926174917
theorem B1712155481 : Blo 2111435 1712155481 := bstep (se 2 (by rfl) ⟨642058305, by rfl⟩ : syracuseStep 1712155481 = 1284116611) B1284116611
theorem B1141436987 : Blo 2111435 1141436987 := bstep (se 1 (by rfl) ⟨856077740, by rfl⟩ : syracuseStep 1141436987 = 1712155481) B1712155481
theorem B760957991 : Blo 2111435 760957991 := bstep (se 1 (by rfl) ⟨570718493, by rfl⟩ : syracuseStep 760957991 = 1141436987) B1141436987
theorem B507305327 : Blo 2111435 507305327 := bstep (se 1 (by rfl) ⟨380478995, by rfl⟩ : syracuseStep 507305327 = 760957991) B760957991
theorem B1352814205 : Blo 2111435 1352814205 := bstep (se 3 (by rfl) ⟨253652663, by rfl⟩ : syracuseStep 1352814205 = 507305327) B507305327
theorem B1803752273 : Blo 2111435 1803752273 := bstep (se 2 (by rfl) ⟨676407102, by rfl⟩ : syracuseStep 1803752273 = 1352814205) B1352814205
theorem B4810006061 : Blo 2111435 4810006061 := bstep (se 3 (by rfl) ⟨901876136, by rfl⟩ : syracuseStep 4810006061 = 1803752273) B1803752273
theorem B3206670707 : Blo 2111435 3206670707 := bstep (se 1 (by rfl) ⟨2405003030, by rfl⟩ : syracuseStep 3206670707 = 4810006061) B4810006061
theorem B2137780471 : Blo 2111435 2137780471 := bstep (se 1 (by rfl) ⟨1603335353, by rfl⟩ : syracuseStep 2137780471 = 3206670707) B3206670707
theorem B2850373961 : Blo 2111435 2850373961 := bstep (se 2 (by rfl) ⟨1068890235, by rfl⟩ : syracuseStep 2850373961 = 2137780471) B2137780471
theorem B1900249307 : Blo 2111435 1900249307 := bstep (se 1 (by rfl) ⟨1425186980, by rfl⟩ : syracuseStep 1900249307 = 2850373961) B2850373961
theorem B1266832871 : Blo 2111435 1266832871 := bstep (se 1 (by rfl) ⟨950124653, by rfl⟩ : syracuseStep 1266832871 = 1900249307) B1900249307
theorem B844555247 : Blo 2111435 844555247 := bstep (se 1 (by rfl) ⟨633416435, by rfl⟩ : syracuseStep 844555247 = 1266832871) B1266832871
theorem B563036831 : Blo 2111435 563036831 := bstep (se 1 (by rfl) ⟨422277623, by rfl⟩ : syracuseStep 563036831 = 844555247) B844555247
theorem B375357887 : Blo 2111435 375357887 := bstep (se 1 (by rfl) ⟨281518415, by rfl⟩ : syracuseStep 375357887 = 563036831) B563036831
theorem B250238591 : Blo 2111435 250238591 := bstep (se 1 (by rfl) ⟨187678943, by rfl⟩ : syracuseStep 250238591 = 375357887) B375357887
theorem B166825727 : Blo 2111435 166825727 := bstep (se 1 (by rfl) ⟨125119295, by rfl⟩ : syracuseStep 166825727 = 250238591) B250238591
theorem B111217151 : Blo 2111435 111217151 := bstep (se 1 (by rfl) ⟨83412863, by rfl⟩ : syracuseStep 111217151 = 166825727) B166825727
theorem B296579069 : Blo 2111435 296579069 := bstep (se 3 (by rfl) ⟨55608575, by rfl⟩ : syracuseStep 296579069 = 111217151) B111217151
theorem B197719379 : Blo 2111435 197719379 := bstep (se 1 (by rfl) ⟨148289534, by rfl⟩ : syracuseStep 197719379 = 296579069) B296579069
theorem B131812919 : Blo 2111435 131812919 := bstep (se 1 (by rfl) ⟨98859689, by rfl⟩ : syracuseStep 131812919 = 197719379) B197719379
theorem B87875279 : Blo 2111435 87875279 := bstep (se 1 (by rfl) ⟨65906459, by rfl⟩ : syracuseStep 87875279 = 131812919) B131812919
theorem B58583519 : Blo 2111435 58583519 := bstep (se 1 (by rfl) ⟨43937639, by rfl⟩ : syracuseStep 58583519 = 87875279) B87875279
theorem B39055679 : Blo 2111435 39055679 := bstep (se 1 (by rfl) ⟨29291759, by rfl⟩ : syracuseStep 39055679 = 58583519) B58583519
theorem B26037119 : Blo 2111435 26037119 := bstep (se 1 (by rfl) ⟨19527839, by rfl⟩ : syracuseStep 26037119 = 39055679) B39055679
theorem B17358079 : Blo 2111435 17358079 := bstep (se 1 (by rfl) ⟨13018559, by rfl⟩ : syracuseStep 17358079 = 26037119) B26037119
theorem B23144105 : Blo 2111435 23144105 := bstep (se 2 (by rfl) ⟨8679039, by rfl⟩ : syracuseStep 23144105 = 17358079) B17358079
theorem B15429403 : Blo 2111435 15429403 := bstep (se 1 (by rfl) ⟨11572052, by rfl⟩ : syracuseStep 15429403 = 23144105) B23144105
theorem B20572537 : Blo 2111435 20572537 := bstep (se 2 (by rfl) ⟨7714701, by rfl⟩ : syracuseStep 20572537 = 15429403) B15429403
theorem B27430049 : Blo 2111435 27430049 := bstep (se 2 (by rfl) ⟨10286268, by rfl⟩ : syracuseStep 27430049 = 20572537) B20572537
theorem B73146797 : Blo 2111435 73146797 := bstep (se 3 (by rfl) ⟨13715024, by rfl⟩ : syracuseStep 73146797 = 27430049) B27430049
theorem B48764531 : Blo 2111435 48764531 := bstep (se 1 (by rfl) ⟨36573398, by rfl⟩ : syracuseStep 48764531 = 73146797) B73146797
theorem B32509687 : Blo 2111435 32509687 := bstep (se 1 (by rfl) ⟨24382265, by rfl⟩ : syracuseStep 32509687 = 48764531) B48764531
theorem B43346249 : Blo 2111435 43346249 := bstep (se 2 (by rfl) ⟨16254843, by rfl⟩ : syracuseStep 43346249 = 32509687) B32509687
theorem B28897499 : Blo 2111435 28897499 := bstep (se 1 (by rfl) ⟨21673124, by rfl⟩ : syracuseStep 28897499 = 43346249) B43346249
theorem B19264999 : Blo 2111435 19264999 := bstep (se 1 (by rfl) ⟨14448749, by rfl⟩ : syracuseStep 19264999 = 28897499) B28897499
theorem B25686665 : Blo 2111435 25686665 := bstep (se 2 (by rfl) ⟨9632499, by rfl⟩ : syracuseStep 25686665 = 19264999) B19264999
theorem B17124443 : Blo 2111435 17124443 := bstep (se 1 (by rfl) ⟨12843332, by rfl⟩ : syracuseStep 17124443 = 25686665) B25686665
theorem B11416295 : Blo 2111435 11416295 := bstep (se 1 (by rfl) ⟨8562221, by rfl⟩ : syracuseStep 11416295 = 17124443) B17124443
theorem B7610863 : Blo 2111435 7610863 := bstep (se 1 (by rfl) ⟨5708147, by rfl⟩ : syracuseStep 7610863 = 11416295) B11416295
theorem B10147817 : Blo 2111435 10147817 := bstep (se 2 (by rfl) ⟨3805431, by rfl⟩ : syracuseStep 10147817 = 7610863) B7610863
theorem B6765211 : Blo 2111435 6765211 := bstep (se 1 (by rfl) ⟨5073908, by rfl⟩ : syracuseStep 6765211 = 10147817) B10147817
theorem B36081125 : Blo 2111435 36081125 := bstep (se 4 (by rfl) ⟨3382605, by rfl⟩ : syracuseStep 36081125 = 6765211) B6765211
theorem B24054083 : Blo 2111435 24054083 := bstep (se 1 (by rfl) ⟨18040562, by rfl⟩ : syracuseStep 24054083 = 36081125) B36081125
theorem B16036055 : Blo 2111435 16036055 := bstep (se 1 (by rfl) ⟨12027041, by rfl⟩ : syracuseStep 16036055 = 24054083) B24054083
theorem B10690703 : Blo 2111435 10690703 := bstep (se 1 (by rfl) ⟨8018027, by rfl⟩ : syracuseStep 10690703 = 16036055) B16036055
theorem B7127135 : Blo 2111435 7127135 := bstep (se 1 (by rfl) ⟨5345351, by rfl⟩ : syracuseStep 7127135 = 10690703) B10690703
theorem B4751423 : Blo 2111435 4751423 := bstep (se 1 (by rfl) ⟨3563567, by rfl⟩ : syracuseStep 4751423 = 7127135) B7127135
theorem B3167615 : Blo 2111435 3167615 := bstep (se 1 (by rfl) ⟨2375711, by rfl⟩ : syracuseStep 3167615 = 4751423) B4751423
theorem B2111743 : Blo 2111435 2111743 := bstep (se 1 (by rfl) ⟨1583807, by rfl⟩ : syracuseStep 2111743 = 3167615) B3167615
theorem B3167621 : Blo 2111435 3167621 := bbase (se 4 (by rfl) ⟨296964, by rfl⟩ : syracuseStep 3167621 = 593929) (by norm_num)
theorem B2111747 : Blo 2111435 2111747 := bstep (se 1 (by rfl) ⟨1583810, by rfl⟩ : syracuseStep 2111747 = 3167621) B3167621
theorem B3563581 : Blo 2111435 3563581 := bbase (se 3 (by rfl) ⟨668171, by rfl⟩ : syracuseStep 3563581 = 1336343) (by norm_num)
theorem B4751441 : Blo 2111435 4751441 := bstep (se 2 (by rfl) ⟨1781790, by rfl⟩ : syracuseStep 4751441 = 3563581) B3563581
theorem B3167627 : Blo 2111435 3167627 := bstep (se 1 (by rfl) ⟨2375720, by rfl⟩ : syracuseStep 3167627 = 4751441) B4751441
theorem B2111751 : Blo 2111435 2111751 := bstep (se 1 (by rfl) ⟨1583813, by rfl⟩ : syracuseStep 2111751 = 3167627) B3167627
theorem B2375725 : Blo 2111435 2375725 := bbase (se 3 (by rfl) ⟨445448, by rfl⟩ : syracuseStep 2375725 = 890897) (by norm_num)
theorem B3167633 : Blo 2111435 3167633 := bstep (se 2 (by rfl) ⟨1187862, by rfl⟩ : syracuseStep 3167633 = 2375725) B2375725
theorem B2111755 : Blo 2111435 2111755 := bstep (se 1 (by rfl) ⟨1583816, by rfl⟩ : syracuseStep 2111755 = 3167633) B3167633
theorem B7127189 : Blo 2111435 7127189 := bbase (se 6 (by rfl) ⟨167043, by rfl⟩ : syracuseStep 7127189 = 334087) (by norm_num)
theorem B4751459 : Blo 2111435 4751459 := bstep (se 1 (by rfl) ⟨3563594, by rfl⟩ : syracuseStep 4751459 = 7127189) B7127189
theorem B3167639 : Blo 2111435 3167639 := bstep (se 1 (by rfl) ⟨2375729, by rfl⟩ : syracuseStep 3167639 = 4751459) B4751459
theorem B2111759 : Blo 2111435 2111759 := bstep (se 1 (by rfl) ⟨1583819, by rfl⟩ : syracuseStep 2111759 = 3167639) B3167639
theorem B3167645 : Blo 2111435 3167645 := bbase (se 3 (by rfl) ⟨593933, by rfl⟩ : syracuseStep 3167645 = 1187867) (by norm_num)
theorem B2111763 : Blo 2111435 2111763 := bstep (se 1 (by rfl) ⟨1583822, by rfl⟩ : syracuseStep 2111763 = 3167645) B3167645
theorem B4751477 : Blo 2111435 4751477 := bbase (se 5 (by rfl) ⟨222725, by rfl⟩ : syracuseStep 4751477 = 445451) (by norm_num)
theorem B3167651 : Blo 2111435 3167651 := bstep (se 1 (by rfl) ⟨2375738, by rfl⟩ : syracuseStep 3167651 = 4751477) B4751477
theorem B2111767 : Blo 2111435 2111767 := bstep (se 1 (by rfl) ⟨1583825, by rfl⟩ : syracuseStep 2111767 = 3167651) B3167651
theorem B3210877 : Blo 2111435 3210877 := bbase (se 3 (by rfl) ⟨602039, by rfl⟩ : syracuseStep 3210877 = 1204079) (by norm_num)
theorem B4281169 : Blo 2111435 4281169 := bstep (se 2 (by rfl) ⟨1605438, by rfl⟩ : syracuseStep 4281169 = 3210877) B3210877
theorem B5708225 : Blo 2111435 5708225 := bstep (se 2 (by rfl) ⟨2140584, by rfl⟩ : syracuseStep 5708225 = 4281169) B4281169
theorem B3805483 : Blo 2111435 3805483 := bstep (se 1 (by rfl) ⟨2854112, by rfl⟩ : syracuseStep 3805483 = 5708225) B5708225
theorem B5073977 : Blo 2111435 5073977 := bstep (se 2 (by rfl) ⟨1902741, by rfl⟩ : syracuseStep 5073977 = 3805483) B3805483
theorem B3382651 : Blo 2111435 3382651 := bstep (se 1 (by rfl) ⟨2536988, by rfl⟩ : syracuseStep 3382651 = 5073977) B5073977
theorem B18040805 : Blo 2111435 18040805 := bstep (se 4 (by rfl) ⟨1691325, by rfl⟩ : syracuseStep 18040805 = 3382651) B3382651
theorem B12027203 : Blo 2111435 12027203 := bstep (se 1 (by rfl) ⟨9020402, by rfl⟩ : syracuseStep 12027203 = 18040805) B18040805
theorem B8018135 : Blo 2111435 8018135 := bstep (se 1 (by rfl) ⟨6013601, by rfl⟩ : syracuseStep 8018135 = 12027203) B12027203
theorem B5345423 : Blo 2111435 5345423 := bstep (se 1 (by rfl) ⟨4009067, by rfl⟩ : syracuseStep 5345423 = 8018135) B8018135
theorem B3563615 : Blo 2111435 3563615 := bstep (se 1 (by rfl) ⟨2672711, by rfl⟩ : syracuseStep 3563615 = 5345423) B5345423
theorem B2375743 : Blo 2111435 2375743 := bstep (se 1 (by rfl) ⟨1781807, by rfl⟩ : syracuseStep 2375743 = 3563615) B3563615
theorem B3167657 : Blo 2111435 3167657 := bstep (se 2 (by rfl) ⟨1187871, by rfl⟩ : syracuseStep 3167657 = 2375743) B2375743
theorem B2111771 : Blo 2111435 2111771 := bstep (se 1 (by rfl) ⟨1583828, by rfl⟩ : syracuseStep 2111771 = 3167657) B3167657
theorem B8018149 : Blo 2111435 8018149 := bbase (se 4 (by rfl) ⟨751701, by rfl⟩ : syracuseStep 8018149 = 1503403) (by norm_num)
theorem B10690865 : Blo 2111435 10690865 := bstep (se 2 (by rfl) ⟨4009074, by rfl⟩ : syracuseStep 10690865 = 8018149) B8018149
theorem B7127243 : Blo 2111435 7127243 := bstep (se 1 (by rfl) ⟨5345432, by rfl⟩ : syracuseStep 7127243 = 10690865) B10690865
theorem B4751495 : Blo 2111435 4751495 := bstep (se 1 (by rfl) ⟨3563621, by rfl⟩ : syracuseStep 4751495 = 7127243) B7127243
theorem B3167663 : Blo 2111435 3167663 := bstep (se 1 (by rfl) ⟨2375747, by rfl⟩ : syracuseStep 3167663 = 4751495) B4751495
theorem B2111775 : Blo 2111435 2111775 := bstep (se 1 (by rfl) ⟨1583831, by rfl⟩ : syracuseStep 2111775 = 3167663) B3167663
theorem B3167669 : Blo 2111435 3167669 := bbase (se 5 (by rfl) ⟨148484, by rfl⟩ : syracuseStep 3167669 = 296969) (by norm_num)
theorem B2111779 : Blo 2111435 2111779 := bstep (se 1 (by rfl) ⟨1583834, by rfl⟩ : syracuseStep 2111779 = 3167669) B3167669
theorem B5345453 : Blo 2111435 5345453 := bbase (se 3 (by rfl) ⟨1002272, by rfl⟩ : syracuseStep 5345453 = 2004545) (by norm_num)
theorem B3563635 : Blo 2111435 3563635 := bstep (se 1 (by rfl) ⟨2672726, by rfl⟩ : syracuseStep 3563635 = 5345453) B5345453
theorem B4751513 : Blo 2111435 4751513 := bstep (se 2 (by rfl) ⟨1781817, by rfl⟩ : syracuseStep 4751513 = 3563635) B3563635
theorem B3167675 : Blo 2111435 3167675 := bstep (se 1 (by rfl) ⟨2375756, by rfl⟩ : syracuseStep 3167675 = 4751513) B4751513
theorem B2111783 : Blo 2111435 2111783 := bstep (se 1 (by rfl) ⟨1583837, by rfl⟩ : syracuseStep 2111783 = 3167675) B3167675
theorem B2375761 : Blo 2111435 2375761 := bbase (se 2 (by rfl) ⟨890910, by rfl⟩ : syracuseStep 2375761 = 1781821) (by norm_num)
theorem B3167681 : Blo 2111435 3167681 := bstep (se 2 (by rfl) ⟨1187880, by rfl⟩ : syracuseStep 3167681 = 2375761) B2375761
theorem B2111787 : Blo 2111435 2111787 := bstep (se 1 (by rfl) ⟨1583840, by rfl⟩ : syracuseStep 2111787 = 3167681) B3167681
theorem B3006829 : Blo 2111435 3006829 := bbase (se 3 (by rfl) ⟨563780, by rfl⟩ : syracuseStep 3006829 = 1127561) (by norm_num)
theorem B4009105 : Blo 2111435 4009105 := bstep (se 2 (by rfl) ⟨1503414, by rfl⟩ : syracuseStep 4009105 = 3006829) B3006829
theorem B5345473 : Blo 2111435 5345473 := bstep (se 2 (by rfl) ⟨2004552, by rfl⟩ : syracuseStep 5345473 = 4009105) B4009105
theorem B7127297 : Blo 2111435 7127297 := bstep (se 2 (by rfl) ⟨2672736, by rfl⟩ : syracuseStep 7127297 = 5345473) B5345473
theorem B4751531 : Blo 2111435 4751531 := bstep (se 1 (by rfl) ⟨3563648, by rfl⟩ : syracuseStep 4751531 = 7127297) B7127297
theorem B3167687 : Blo 2111435 3167687 := bstep (se 1 (by rfl) ⟨2375765, by rfl⟩ : syracuseStep 3167687 = 4751531) B4751531
theorem B2111791 : Blo 2111435 2111791 := bstep (se 1 (by rfl) ⟨1583843, by rfl⟩ : syracuseStep 2111791 = 3167687) B3167687
theorem B3167693 : Blo 2111435 3167693 := bbase (se 3 (by rfl) ⟨593942, by rfl⟩ : syracuseStep 3167693 = 1187885) (by norm_num)
theorem B2111795 : Blo 2111435 2111795 := bstep (se 1 (by rfl) ⟨1583846, by rfl⟩ : syracuseStep 2111795 = 3167693) B3167693
theorem B4751549 : Blo 2111435 4751549 := bbase (se 3 (by rfl) ⟨890915, by rfl⟩ : syracuseStep 4751549 = 1781831) (by norm_num)
theorem B3167699 : Blo 2111435 3167699 := bstep (se 1 (by rfl) ⟨2375774, by rfl⟩ : syracuseStep 3167699 = 4751549) B4751549
theorem B2111799 : Blo 2111435 2111799 := bstep (se 1 (by rfl) ⟨1583849, by rfl⟩ : syracuseStep 2111799 = 3167699) B3167699
theorem B3563669 : Blo 2111435 3563669 := bbase (se 6 (by rfl) ⟨83523, by rfl⟩ : syracuseStep 3563669 = 167047) (by norm_num)
theorem B2375779 : Blo 2111435 2375779 := bstep (se 1 (by rfl) ⟨1781834, by rfl⟩ : syracuseStep 2375779 = 3563669) B3563669
theorem B3167705 : Blo 2111435 3167705 := bstep (se 2 (by rfl) ⟨1187889, by rfl⟩ : syracuseStep 3167705 = 2375779) B2375779
theorem B2111803 : Blo 2111435 2111803 := bstep (se 1 (by rfl) ⟨1583852, by rfl⟩ : syracuseStep 2111803 = 3167705) B3167705
theorem B4816397 : Blo 2111435 4816397 := bbase (se 3 (by rfl) ⟨903074, by rfl⟩ : syracuseStep 4816397 = 1806149) (by norm_num)
theorem B3210931 : Blo 2111435 3210931 := bstep (se 1 (by rfl) ⟨2408198, by rfl⟩ : syracuseStep 3210931 = 4816397) B4816397
theorem B4281241 : Blo 2111435 4281241 := bstep (se 2 (by rfl) ⟨1605465, by rfl⟩ : syracuseStep 4281241 = 3210931) B3210931
theorem B5708321 : Blo 2111435 5708321 := bstep (se 2 (by rfl) ⟨2140620, by rfl⟩ : syracuseStep 5708321 = 4281241) B4281241
theorem B3805547 : Blo 2111435 3805547 := bstep (se 1 (by rfl) ⟨2854160, by rfl⟩ : syracuseStep 3805547 = 5708321) B5708321
theorem B10148125 : Blo 2111435 10148125 := bstep (se 3 (by rfl) ⟨1902773, by rfl⟩ : syracuseStep 10148125 = 3805547) B3805547
theorem B13530833 : Blo 2111435 13530833 := bstep (se 2 (by rfl) ⟨5074062, by rfl⟩ : syracuseStep 13530833 = 10148125) B10148125
theorem B9020555 : Blo 2111435 9020555 := bstep (se 1 (by rfl) ⟨6765416, by rfl⟩ : syracuseStep 9020555 = 13530833) B13530833
theorem B6013703 : Blo 2111435 6013703 := bstep (se 1 (by rfl) ⟨4510277, by rfl⟩ : syracuseStep 6013703 = 9020555) B9020555
theorem B16036541 : Blo 2111435 16036541 := bstep (se 3 (by rfl) ⟨3006851, by rfl⟩ : syracuseStep 16036541 = 6013703) B6013703
theorem B10691027 : Blo 2111435 10691027 := bstep (se 1 (by rfl) ⟨8018270, by rfl⟩ : syracuseStep 10691027 = 16036541) B16036541
theorem B7127351 : Blo 2111435 7127351 := bstep (se 1 (by rfl) ⟨5345513, by rfl⟩ : syracuseStep 7127351 = 10691027) B10691027
theorem B4751567 : Blo 2111435 4751567 := bstep (se 1 (by rfl) ⟨3563675, by rfl⟩ : syracuseStep 4751567 = 7127351) B7127351
theorem B3167711 : Blo 2111435 3167711 := bstep (se 1 (by rfl) ⟨2375783, by rfl⟩ : syracuseStep 3167711 = 4751567) B4751567
theorem B2111807 : Blo 2111435 2111807 := bstep (se 1 (by rfl) ⟨1583855, by rfl⟩ : syracuseStep 2111807 = 3167711) B3167711
theorem B3167717 : Blo 2111435 3167717 := bbase (se 4 (by rfl) ⟨296973, by rfl⟩ : syracuseStep 3167717 = 593947) (by norm_num)
theorem B2111811 : Blo 2111435 2111811 := bstep (se 1 (by rfl) ⟨1583858, by rfl⟩ : syracuseStep 2111811 = 3167717) B3167717
theorem B8580421 : Blo 2111435 8580421 := bbase (se 4 (by rfl) ⟨804414, by rfl⟩ : syracuseStep 8580421 = 1608829) (by norm_num)
theorem B11440561 : Blo 2111435 11440561 := bstep (se 2 (by rfl) ⟨4290210, by rfl⟩ : syracuseStep 11440561 = 8580421) B8580421
theorem B15254081 : Blo 2111435 15254081 := bstep (se 2 (by rfl) ⟨5720280, by rfl⟩ : syracuseStep 15254081 = 11440561) B11440561
theorem B10169387 : Blo 2111435 10169387 := bstep (se 1 (by rfl) ⟨7627040, by rfl⟩ : syracuseStep 10169387 = 15254081) B15254081
theorem B6779591 : Blo 2111435 6779591 := bstep (se 1 (by rfl) ⟨5084693, by rfl⟩ : syracuseStep 6779591 = 10169387) B10169387
theorem B4519727 : Blo 2111435 4519727 := bstep (se 1 (by rfl) ⟨3389795, by rfl⟩ : syracuseStep 4519727 = 6779591) B6779591
theorem B3013151 : Blo 2111435 3013151 := bstep (se 1 (by rfl) ⟨2259863, by rfl⟩ : syracuseStep 3013151 = 4519727) B4519727
theorem B8035069 : Blo 2111435 8035069 := bstep (se 3 (by rfl) ⟨1506575, by rfl⟩ : syracuseStep 8035069 = 3013151) B3013151
theorem B10713425 : Blo 2111435 10713425 := bstep (se 2 (by rfl) ⟨4017534, by rfl⟩ : syracuseStep 10713425 = 8035069) B8035069
theorem B28569133 : Blo 2111435 28569133 := bstep (se 3 (by rfl) ⟨5356712, by rfl⟩ : syracuseStep 28569133 = 10713425) B10713425
theorem B38092177 : Blo 2111435 38092177 := bstep (se 2 (by rfl) ⟨14284566, by rfl⟩ : syracuseStep 38092177 = 28569133) B28569133
theorem B203158277 : Blo 2111435 203158277 := bstep (se 4 (by rfl) ⟨19046088, by rfl⟩ : syracuseStep 203158277 = 38092177) B38092177
theorem B135438851 : Blo 2111435 135438851 := bstep (se 1 (by rfl) ⟨101579138, by rfl⟩ : syracuseStep 135438851 = 203158277) B203158277
theorem B361170269 : Blo 2111435 361170269 := bstep (se 3 (by rfl) ⟨67719425, by rfl⟩ : syracuseStep 361170269 = 135438851) B135438851
theorem B240780179 : Blo 2111435 240780179 := bstep (se 1 (by rfl) ⟨180585134, by rfl⟩ : syracuseStep 240780179 = 361170269) B361170269
theorem B160520119 : Blo 2111435 160520119 := bstep (se 1 (by rfl) ⟨120390089, by rfl⟩ : syracuseStep 160520119 = 240780179) B240780179
theorem B856107301 : Blo 2111435 856107301 := bstep (se 4 (by rfl) ⟨80260059, by rfl⟩ : syracuseStep 856107301 = 160520119) B160520119
theorem B1141476401 : Blo 2111435 1141476401 := bstep (se 2 (by rfl) ⟨428053650, by rfl⟩ : syracuseStep 1141476401 = 856107301) B856107301
theorem B760984267 : Blo 2111435 760984267 := bstep (se 1 (by rfl) ⟨570738200, by rfl⟩ : syracuseStep 760984267 = 1141476401) B1141476401
theorem B1014645689 : Blo 2111435 1014645689 := bstep (se 2 (by rfl) ⟨380492133, by rfl⟩ : syracuseStep 1014645689 = 760984267) B760984267
theorem B676430459 : Blo 2111435 676430459 := bstep (se 1 (by rfl) ⟨507322844, by rfl⟩ : syracuseStep 676430459 = 1014645689) B1014645689
theorem B450953639 : Blo 2111435 450953639 := bstep (se 1 (by rfl) ⟨338215229, by rfl⟩ : syracuseStep 450953639 = 676430459) B676430459
theorem B300635759 : Blo 2111435 300635759 := bstep (se 1 (by rfl) ⟨225476819, by rfl⟩ : syracuseStep 300635759 = 450953639) B450953639
theorem B801695357 : Blo 2111435 801695357 := bstep (se 3 (by rfl) ⟨150317879, by rfl⟩ : syracuseStep 801695357 = 300635759) B300635759
theorem B534463571 : Blo 2111435 534463571 := bstep (se 1 (by rfl) ⟨400847678, by rfl⟩ : syracuseStep 534463571 = 801695357) B801695357
theorem B356309047 : Blo 2111435 356309047 := bstep (se 1 (by rfl) ⟨267231785, by rfl⟩ : syracuseStep 356309047 = 534463571) B534463571
theorem B475078729 : Blo 2111435 475078729 := bstep (se 2 (by rfl) ⟨178154523, by rfl⟩ : syracuseStep 475078729 = 356309047) B356309047
theorem B633438305 : Blo 2111435 633438305 := bstep (se 2 (by rfl) ⟨237539364, by rfl⟩ : syracuseStep 633438305 = 475078729) B475078729
theorem B422292203 : Blo 2111435 422292203 := bstep (se 1 (by rfl) ⟨316719152, by rfl⟩ : syracuseStep 422292203 = 633438305) B633438305
theorem B281528135 : Blo 2111435 281528135 := bstep (se 1 (by rfl) ⟨211146101, by rfl⟩ : syracuseStep 281528135 = 422292203) B422292203
theorem B187685423 : Blo 2111435 187685423 := bstep (se 1 (by rfl) ⟨140764067, by rfl⟩ : syracuseStep 187685423 = 281528135) B281528135
theorem B125123615 : Blo 2111435 125123615 := bstep (se 1 (by rfl) ⟨93842711, by rfl⟩ : syracuseStep 125123615 = 187685423) B187685423
theorem B83415743 : Blo 2111435 83415743 := bstep (se 1 (by rfl) ⟨62561807, by rfl⟩ : syracuseStep 83415743 = 125123615) B125123615
theorem B55610495 : Blo 2111435 55610495 := bstep (se 1 (by rfl) ⟨41707871, by rfl⟩ : syracuseStep 55610495 = 83415743) B83415743
theorem B37073663 : Blo 2111435 37073663 := bstep (se 1 (by rfl) ⟨27805247, by rfl⟩ : syracuseStep 37073663 = 55610495) B55610495
theorem B24715775 : Blo 2111435 24715775 := bstep (se 1 (by rfl) ⟨18536831, by rfl⟩ : syracuseStep 24715775 = 37073663) B37073663
theorem B16477183 : Blo 2111435 16477183 := bstep (se 1 (by rfl) ⟨12357887, by rfl⟩ : syracuseStep 16477183 = 24715775) B24715775
theorem B21969577 : Blo 2111435 21969577 := bstep (se 2 (by rfl) ⟨8238591, by rfl⟩ : syracuseStep 21969577 = 16477183) B16477183
theorem B29292769 : Blo 2111435 29292769 := bstep (se 2 (by rfl) ⟨10984788, by rfl⟩ : syracuseStep 29292769 = 21969577) B21969577
theorem B39057025 : Blo 2111435 39057025 := bstep (se 2 (by rfl) ⟨14646384, by rfl⟩ : syracuseStep 39057025 = 29292769) B29292769
theorem B52076033 : Blo 2111435 52076033 := bstep (se 2 (by rfl) ⟨19528512, by rfl⟩ : syracuseStep 52076033 = 39057025) B39057025
theorem B34717355 : Blo 2111435 34717355 := bstep (se 1 (by rfl) ⟨26038016, by rfl⟩ : syracuseStep 34717355 = 52076033) B52076033
theorem B23144903 : Blo 2111435 23144903 := bstep (se 1 (by rfl) ⟨17358677, by rfl⟩ : syracuseStep 23144903 = 34717355) B34717355
theorem B15429935 : Blo 2111435 15429935 := bstep (se 1 (by rfl) ⟨11572451, by rfl⟩ : syracuseStep 15429935 = 23144903) B23144903
theorem B10286623 : Blo 2111435 10286623 := bstep (se 1 (by rfl) ⟨7714967, by rfl⟩ : syracuseStep 10286623 = 15429935) B15429935
theorem B13715497 : Blo 2111435 13715497 := bstep (se 2 (by rfl) ⟨5143311, by rfl⟩ : syracuseStep 13715497 = 10286623) B10286623
theorem B18287329 : Blo 2111435 18287329 := bstep (se 2 (by rfl) ⟨6857748, by rfl⟩ : syracuseStep 18287329 = 13715497) B13715497
theorem B24383105 : Blo 2111435 24383105 := bstep (se 2 (by rfl) ⟨9143664, by rfl⟩ : syracuseStep 24383105 = 18287329) B18287329
theorem B16255403 : Blo 2111435 16255403 := bstep (se 1 (by rfl) ⟨12191552, by rfl⟩ : syracuseStep 16255403 = 24383105) B24383105
theorem B10836935 : Blo 2111435 10836935 := bstep (se 1 (by rfl) ⟨8127701, by rfl⟩ : syracuseStep 10836935 = 16255403) B16255403
theorem B7224623 : Blo 2111435 7224623 := bstep (se 1 (by rfl) ⟨5418467, by rfl⟩ : syracuseStep 7224623 = 10836935) B10836935
theorem B4816415 : Blo 2111435 4816415 := bstep (se 1 (by rfl) ⟨3612311, by rfl⟩ : syracuseStep 4816415 = 7224623) B7224623
theorem B12843773 : Blo 2111435 12843773 := bstep (se 3 (by rfl) ⟨2408207, by rfl⟩ : syracuseStep 12843773 = 4816415) B4816415
theorem B8562515 : Blo 2111435 8562515 := bstep (se 1 (by rfl) ⟨6421886, by rfl⟩ : syracuseStep 8562515 = 12843773) B12843773
theorem B22833373 : Blo 2111435 22833373 := bstep (se 3 (by rfl) ⟨4281257, by rfl⟩ : syracuseStep 22833373 = 8562515) B8562515
theorem B30444497 : Blo 2111435 30444497 := bstep (se 2 (by rfl) ⟨11416686, by rfl⟩ : syracuseStep 30444497 = 22833373) B22833373
theorem B20296331 : Blo 2111435 20296331 := bstep (se 1 (by rfl) ⟨15222248, by rfl⟩ : syracuseStep 20296331 = 30444497) B30444497
theorem B13530887 : Blo 2111435 13530887 := bstep (se 1 (by rfl) ⟨10148165, by rfl⟩ : syracuseStep 13530887 = 20296331) B20296331
theorem B9020591 : Blo 2111435 9020591 := bstep (se 1 (by rfl) ⟨6765443, by rfl⟩ : syracuseStep 9020591 = 13530887) B13530887
theorem B6013727 : Blo 2111435 6013727 := bstep (se 1 (by rfl) ⟨4510295, by rfl⟩ : syracuseStep 6013727 = 9020591) B9020591
theorem B4009151 : Blo 2111435 4009151 := bstep (se 1 (by rfl) ⟨3006863, by rfl⟩ : syracuseStep 4009151 = 6013727) B6013727
theorem B2672767 : Blo 2111435 2672767 := bstep (se 1 (by rfl) ⟨2004575, by rfl⟩ : syracuseStep 2672767 = 4009151) B4009151
theorem B3563689 : Blo 2111435 3563689 := bstep (se 2 (by rfl) ⟨1336383, by rfl⟩ : syracuseStep 3563689 = 2672767) B2672767
theorem B4751585 : Blo 2111435 4751585 := bstep (se 2 (by rfl) ⟨1781844, by rfl⟩ : syracuseStep 4751585 = 3563689) B3563689
theorem B3167723 : Blo 2111435 3167723 := bstep (se 1 (by rfl) ⟨2375792, by rfl⟩ : syracuseStep 3167723 = 4751585) B4751585
theorem B2111815 : Blo 2111435 2111815 := bstep (se 1 (by rfl) ⟨1583861, by rfl⟩ : syracuseStep 2111815 = 3167723) B3167723
theorem B2375797 : Blo 2111435 2375797 := bbase (se 5 (by rfl) ⟨111365, by rfl⟩ : syracuseStep 2375797 = 222731) (by norm_num)
theorem B3167729 : Blo 2111435 3167729 := bstep (se 2 (by rfl) ⟨1187898, by rfl⟩ : syracuseStep 3167729 = 2375797) B2375797
theorem B2111819 : Blo 2111435 2111819 := bstep (se 1 (by rfl) ⟨1583864, by rfl⟩ : syracuseStep 2111819 = 3167729) B3167729
theorem B2672777 : Blo 2111435 2672777 := bbase (se 2 (by rfl) ⟨1002291, by rfl⟩ : syracuseStep 2672777 = 2004583) (by norm_num)
theorem B7127405 : Blo 2111435 7127405 := bstep (se 3 (by rfl) ⟨1336388, by rfl⟩ : syracuseStep 7127405 = 2672777) B2672777
theorem B4751603 : Blo 2111435 4751603 := bstep (se 1 (by rfl) ⟨3563702, by rfl⟩ : syracuseStep 4751603 = 7127405) B7127405
theorem B3167735 : Blo 2111435 3167735 := bstep (se 1 (by rfl) ⟨2375801, by rfl⟩ : syracuseStep 3167735 = 4751603) B4751603
theorem B2111823 : Blo 2111435 2111823 := bstep (se 1 (by rfl) ⟨1583867, by rfl⟩ : syracuseStep 2111823 = 3167735) B3167735
theorem B3167741 : Blo 2111435 3167741 := bbase (se 3 (by rfl) ⟨593951, by rfl⟩ : syracuseStep 3167741 = 1187903) (by norm_num)
theorem B2111827 : Blo 2111435 2111827 := bstep (se 1 (by rfl) ⟨1583870, by rfl⟩ : syracuseStep 2111827 = 3167741) B3167741
theorem B4751621 : Blo 2111435 4751621 := bbase (se 4 (by rfl) ⟨445464, by rfl⟩ : syracuseStep 4751621 = 890929) (by norm_num)
theorem B3167747 : Blo 2111435 3167747 := bstep (se 1 (by rfl) ⟨2375810, by rfl⟩ : syracuseStep 3167747 = 4751621) B4751621
theorem B2111831 : Blo 2111435 2111831 := bstep (se 1 (by rfl) ⟨1583873, by rfl⟩ : syracuseStep 2111831 = 3167747) B3167747
theorem B4009189 : Blo 2111435 4009189 := bbase (se 4 (by rfl) ⟨375861, by rfl⟩ : syracuseStep 4009189 = 751723) (by norm_num)
theorem B5345585 : Blo 2111435 5345585 := bstep (se 2 (by rfl) ⟨2004594, by rfl⟩ : syracuseStep 5345585 = 4009189) B4009189
theorem B3563723 : Blo 2111435 3563723 := bstep (se 1 (by rfl) ⟨2672792, by rfl⟩ : syracuseStep 3563723 = 5345585) B5345585
theorem B2375815 : Blo 2111435 2375815 := bstep (se 1 (by rfl) ⟨1781861, by rfl⟩ : syracuseStep 2375815 = 3563723) B3563723
theorem B3167753 : Blo 2111435 3167753 := bstep (se 2 (by rfl) ⟨1187907, by rfl⟩ : syracuseStep 3167753 = 2375815) B2375815
theorem B2111835 : Blo 2111435 2111835 := bstep (se 1 (by rfl) ⟨1583876, by rfl⟩ : syracuseStep 2111835 = 3167753) B3167753
theorem B10691189 : Blo 2111435 10691189 := bbase (se 5 (by rfl) ⟨501149, by rfl⟩ : syracuseStep 10691189 = 1002299) (by norm_num)
theorem B7127459 : Blo 2111435 7127459 := bstep (se 1 (by rfl) ⟨5345594, by rfl⟩ : syracuseStep 7127459 = 10691189) B10691189
theorem B4751639 : Blo 2111435 4751639 := bstep (se 1 (by rfl) ⟨3563729, by rfl⟩ : syracuseStep 4751639 = 7127459) B7127459
theorem B3167759 : Blo 2111435 3167759 := bstep (se 1 (by rfl) ⟨2375819, by rfl⟩ : syracuseStep 3167759 = 4751639) B4751639
theorem B2111839 : Blo 2111435 2111839 := bstep (se 1 (by rfl) ⟨1583879, by rfl⟩ : syracuseStep 2111839 = 3167759) B3167759
theorem B3167765 : Blo 2111435 3167765 := bbase (se 6 (by rfl) ⟨74244, by rfl⟩ : syracuseStep 3167765 = 148489) (by norm_num)
theorem B2111843 : Blo 2111435 2111843 := bstep (se 1 (by rfl) ⟨1583882, by rfl⟩ : syracuseStep 2111843 = 3167765) B3167765
theorem B15430165 : Blo 2111435 15430165 := bbase (se 6 (by rfl) ⟨361644, by rfl⟩ : syracuseStep 15430165 = 723289) (by norm_num)
theorem B82294213 : Blo 2111435 82294213 := bstep (se 4 (by rfl) ⟨7715082, by rfl⟩ : syracuseStep 82294213 = 15430165) B15430165
theorem B109725617 : Blo 2111435 109725617 := bstep (se 2 (by rfl) ⟨41147106, by rfl⟩ : syracuseStep 109725617 = 82294213) B82294213
theorem B73150411 : Blo 2111435 73150411 := bstep (se 1 (by rfl) ⟨54862808, by rfl⟩ : syracuseStep 73150411 = 109725617) B109725617
theorem B97533881 : Blo 2111435 97533881 := bstep (se 2 (by rfl) ⟨36575205, by rfl⟩ : syracuseStep 97533881 = 73150411) B73150411
theorem B65022587 : Blo 2111435 65022587 := bstep (se 1 (by rfl) ⟨48766940, by rfl⟩ : syracuseStep 65022587 = 97533881) B97533881
theorem B43348391 : Blo 2111435 43348391 := bstep (se 1 (by rfl) ⟨32511293, by rfl⟩ : syracuseStep 43348391 = 65022587) B65022587
theorem B28898927 : Blo 2111435 28898927 := bstep (se 1 (by rfl) ⟨21674195, by rfl⟩ : syracuseStep 28898927 = 43348391) B43348391
theorem B19265951 : Blo 2111435 19265951 := bstep (se 1 (by rfl) ⟨14449463, by rfl⟩ : syracuseStep 19265951 = 28898927) B28898927
theorem B12843967 : Blo 2111435 12843967 := bstep (se 1 (by rfl) ⟨9632975, by rfl⟩ : syracuseStep 12843967 = 19265951) B19265951
theorem B17125289 : Blo 2111435 17125289 := bstep (se 2 (by rfl) ⟨6421983, by rfl⟩ : syracuseStep 17125289 = 12843967) B12843967
theorem B11416859 : Blo 2111435 11416859 := bstep (se 1 (by rfl) ⟨8562644, by rfl⟩ : syracuseStep 11416859 = 17125289) B17125289
theorem B7611239 : Blo 2111435 7611239 := bstep (se 1 (by rfl) ⟨5708429, by rfl⟩ : syracuseStep 7611239 = 11416859) B11416859
theorem B5074159 : Blo 2111435 5074159 := bstep (se 1 (by rfl) ⟨3805619, by rfl⟩ : syracuseStep 5074159 = 7611239) B7611239
theorem B6765545 : Blo 2111435 6765545 := bstep (se 2 (by rfl) ⟨2537079, by rfl⟩ : syracuseStep 6765545 = 5074159) B5074159
theorem B18041453 : Blo 2111435 18041453 := bstep (se 3 (by rfl) ⟨3382772, by rfl⟩ : syracuseStep 18041453 = 6765545) B6765545
theorem B12027635 : Blo 2111435 12027635 := bstep (se 1 (by rfl) ⟨9020726, by rfl⟩ : syracuseStep 12027635 = 18041453) B18041453
theorem B8018423 : Blo 2111435 8018423 := bstep (se 1 (by rfl) ⟨6013817, by rfl⟩ : syracuseStep 8018423 = 12027635) B12027635
theorem B5345615 : Blo 2111435 5345615 := bstep (se 1 (by rfl) ⟨4009211, by rfl⟩ : syracuseStep 5345615 = 8018423) B8018423
theorem B3563743 : Blo 2111435 3563743 := bstep (se 1 (by rfl) ⟨2672807, by rfl⟩ : syracuseStep 3563743 = 5345615) B5345615
theorem B4751657 : Blo 2111435 4751657 := bstep (se 2 (by rfl) ⟨1781871, by rfl⟩ : syracuseStep 4751657 = 3563743) B3563743
theorem B3167771 : Blo 2111435 3167771 := bstep (se 1 (by rfl) ⟨2375828, by rfl⟩ : syracuseStep 3167771 = 4751657) B4751657
theorem B2111847 : Blo 2111435 2111847 := bstep (se 1 (by rfl) ⟨1583885, by rfl⟩ : syracuseStep 2111847 = 3167771) B3167771
theorem B2375833 : Blo 2111435 2375833 := bbase (se 2 (by rfl) ⟨890937, by rfl⟩ : syracuseStep 2375833 = 1781875) (by norm_num)
theorem B3167777 : Blo 2111435 3167777 := bstep (se 2 (by rfl) ⟨1187916, by rfl⟩ : syracuseStep 3167777 = 2375833) B2375833
theorem B2111851 : Blo 2111435 2111851 := bstep (se 1 (by rfl) ⟨1583888, by rfl⟩ : syracuseStep 2111851 = 3167777) B3167777
theorem B8018453 : Blo 2111435 8018453 := bbase (se 6 (by rfl) ⟨187932, by rfl⟩ : syracuseStep 8018453 = 375865) (by norm_num)
theorem B5345635 : Blo 2111435 5345635 := bstep (se 1 (by rfl) ⟨4009226, by rfl⟩ : syracuseStep 5345635 = 8018453) B8018453
theorem B7127513 : Blo 2111435 7127513 := bstep (se 2 (by rfl) ⟨2672817, by rfl⟩ : syracuseStep 7127513 = 5345635) B5345635
theorem B4751675 : Blo 2111435 4751675 := bstep (se 1 (by rfl) ⟨3563756, by rfl⟩ : syracuseStep 4751675 = 7127513) B7127513
theorem B3167783 : Blo 2111435 3167783 := bstep (se 1 (by rfl) ⟨2375837, by rfl⟩ : syracuseStep 3167783 = 4751675) B4751675
theorem B2111855 : Blo 2111435 2111855 := bstep (se 1 (by rfl) ⟨1583891, by rfl⟩ : syracuseStep 2111855 = 3167783) B3167783
theorem B3167789 : Blo 2111435 3167789 := bbase (se 3 (by rfl) ⟨593960, by rfl⟩ : syracuseStep 3167789 = 1187921) (by norm_num)
theorem B2111859 : Blo 2111435 2111859 := bstep (se 1 (by rfl) ⟨1583894, by rfl⟩ : syracuseStep 2111859 = 3167789) B3167789
theorem B4751693 : Blo 2111435 4751693 := bbase (se 3 (by rfl) ⟨890942, by rfl⟩ : syracuseStep 4751693 = 1781885) (by norm_num)
theorem B3167795 : Blo 2111435 3167795 := bstep (se 1 (by rfl) ⟨2375846, by rfl⟩ : syracuseStep 3167795 = 4751693) B4751693
theorem B2111863 : Blo 2111435 2111863 := bstep (se 1 (by rfl) ⟨1583897, by rfl⟩ : syracuseStep 2111863 = 3167795) B3167795
theorem B2672833 : Blo 2111435 2672833 := bbase (se 2 (by rfl) ⟨1002312, by rfl⟩ : syracuseStep 2672833 = 2004625) (by norm_num)
theorem B3563777 : Blo 2111435 3563777 := bstep (se 2 (by rfl) ⟨1336416, by rfl⟩ : syracuseStep 3563777 = 2672833) B2672833
theorem B2375851 : Blo 2111435 2375851 := bstep (se 1 (by rfl) ⟨1781888, by rfl⟩ : syracuseStep 2375851 = 3563777) B3563777
theorem B3167801 : Blo 2111435 3167801 := bstep (se 2 (by rfl) ⟨1187925, by rfl⟩ : syracuseStep 3167801 = 2375851) B2375851
theorem B2111867 : Blo 2111435 2111867 := bstep (se 1 (by rfl) ⟨1583900, by rfl⟩ : syracuseStep 2111867 = 3167801) B3167801
theorem B2441129 : Blo 2111435 2441129 := bbase (se 2 (by rfl) ⟨915423, by rfl⟩ : syracuseStep 2441129 = 1830847) (by norm_num)
theorem B6509677 : Blo 2111435 6509677 := bstep (se 3 (by rfl) ⟨1220564, by rfl⟩ : syracuseStep 6509677 = 2441129) B2441129
theorem B8679569 : Blo 2111435 8679569 := bstep (se 2 (by rfl) ⟨3254838, by rfl⟩ : syracuseStep 8679569 = 6509677) B6509677
theorem B23145517 : Blo 2111435 23145517 := bstep (se 3 (by rfl) ⟨4339784, by rfl⟩ : syracuseStep 23145517 = 8679569) B8679569
theorem B30860689 : Blo 2111435 30860689 := bstep (se 2 (by rfl) ⟨11572758, by rfl⟩ : syracuseStep 30860689 = 23145517) B23145517
theorem B41147585 : Blo 2111435 41147585 := bstep (se 2 (by rfl) ⟨15430344, by rfl⟩ : syracuseStep 41147585 = 30860689) B30860689
theorem B27431723 : Blo 2111435 27431723 := bstep (se 1 (by rfl) ⟨20573792, by rfl⟩ : syracuseStep 27431723 = 41147585) B41147585
theorem B18287815 : Blo 2111435 18287815 := bstep (se 1 (by rfl) ⟨13715861, by rfl⟩ : syracuseStep 18287815 = 27431723) B27431723
theorem B24383753 : Blo 2111435 24383753 := bstep (se 2 (by rfl) ⟨9143907, by rfl⟩ : syracuseStep 24383753 = 18287815) B18287815
theorem B16255835 : Blo 2111435 16255835 := bstep (se 1 (by rfl) ⟨12191876, by rfl⟩ : syracuseStep 16255835 = 24383753) B24383753
theorem B10837223 : Blo 2111435 10837223 := bstep (se 1 (by rfl) ⟨8127917, by rfl⟩ : syracuseStep 10837223 = 16255835) B16255835
theorem B7224815 : Blo 2111435 7224815 := bstep (se 1 (by rfl) ⟨5418611, by rfl⟩ : syracuseStep 7224815 = 10837223) B10837223
theorem B19266173 : Blo 2111435 19266173 := bstep (se 3 (by rfl) ⟨3612407, by rfl⟩ : syracuseStep 19266173 = 7224815) B7224815
theorem B12844115 : Blo 2111435 12844115 := bstep (se 1 (by rfl) ⟨9633086, by rfl⟩ : syracuseStep 12844115 = 19266173) B19266173
theorem B8562743 : Blo 2111435 8562743 := bstep (se 1 (by rfl) ⟨6422057, by rfl⟩ : syracuseStep 8562743 = 12844115) B12844115
theorem B5708495 : Blo 2111435 5708495 := bstep (se 1 (by rfl) ⟨4281371, by rfl⟩ : syracuseStep 5708495 = 8562743) B8562743
theorem B3805663 : Blo 2111435 3805663 := bstep (se 1 (by rfl) ⟨2854247, by rfl⟩ : syracuseStep 3805663 = 5708495) B5708495
theorem B5074217 : Blo 2111435 5074217 := bstep (se 2 (by rfl) ⟨1902831, by rfl⟩ : syracuseStep 5074217 = 3805663) B3805663
theorem B3382811 : Blo 2111435 3382811 := bstep (se 1 (by rfl) ⟨2537108, by rfl⟩ : syracuseStep 3382811 = 5074217) B5074217
theorem B2255207 : Blo 2111435 2255207 := bstep (se 1 (by rfl) ⟨1691405, by rfl⟩ : syracuseStep 2255207 = 3382811) B3382811
theorem B24055541 : Blo 2111435 24055541 := bstep (se 5 (by rfl) ⟨1127603, by rfl⟩ : syracuseStep 24055541 = 2255207) B2255207
theorem B16037027 : Blo 2111435 16037027 := bstep (se 1 (by rfl) ⟨12027770, by rfl⟩ : syracuseStep 16037027 = 24055541) B24055541
theorem B10691351 : Blo 2111435 10691351 := bstep (se 1 (by rfl) ⟨8018513, by rfl⟩ : syracuseStep 10691351 = 16037027) B16037027
theorem B7127567 : Blo 2111435 7127567 := bstep (se 1 (by rfl) ⟨5345675, by rfl⟩ : syracuseStep 7127567 = 10691351) B10691351
theorem B4751711 : Blo 2111435 4751711 := bstep (se 1 (by rfl) ⟨3563783, by rfl⟩ : syracuseStep 4751711 = 7127567) B7127567
theorem B3167807 : Blo 2111435 3167807 := bstep (se 1 (by rfl) ⟨2375855, by rfl⟩ : syracuseStep 3167807 = 4751711) B4751711
theorem B2111871 : Blo 2111435 2111871 := bstep (se 1 (by rfl) ⟨1583903, by rfl⟩ : syracuseStep 2111871 = 3167807) B3167807
theorem B3167813 : Blo 2111435 3167813 := bbase (se 4 (by rfl) ⟨296982, by rfl⟩ : syracuseStep 3167813 = 593965) (by norm_num)
theorem B2111875 : Blo 2111435 2111875 := bstep (se 1 (by rfl) ⟨1583906, by rfl⟩ : syracuseStep 2111875 = 3167813) B3167813
theorem B3563797 : Blo 2111435 3563797 := bbase (se 6 (by rfl) ⟨83526, by rfl⟩ : syracuseStep 3563797 = 167053) (by norm_num)
theorem B4751729 : Blo 2111435 4751729 := bstep (se 2 (by rfl) ⟨1781898, by rfl⟩ : syracuseStep 4751729 = 3563797) B3563797
theorem B3167819 : Blo 2111435 3167819 := bstep (se 1 (by rfl) ⟨2375864, by rfl⟩ : syracuseStep 3167819 = 4751729) B4751729
theorem B2111879 : Blo 2111435 2111879 := bstep (se 1 (by rfl) ⟨1583909, by rfl⟩ : syracuseStep 2111879 = 3167819) B3167819
theorem B2375869 : Blo 2111435 2375869 := bbase (se 3 (by rfl) ⟨445475, by rfl⟩ : syracuseStep 2375869 = 890951) (by norm_num)
theorem B3167825 : Blo 2111435 3167825 := bstep (se 2 (by rfl) ⟨1187934, by rfl⟩ : syracuseStep 3167825 = 2375869) B2375869
theorem B2111883 : Blo 2111435 2111883 := bstep (se 1 (by rfl) ⟨1583912, by rfl⟩ : syracuseStep 2111883 = 3167825) B3167825
theorem B7127621 : Blo 2111435 7127621 := bbase (se 4 (by rfl) ⟨668214, by rfl⟩ : syracuseStep 7127621 = 1336429) (by norm_num)
theorem B4751747 : Blo 2111435 4751747 := bstep (se 1 (by rfl) ⟨3563810, by rfl⟩ : syracuseStep 4751747 = 7127621) B7127621
theorem B3167831 : Blo 2111435 3167831 := bstep (se 1 (by rfl) ⟨2375873, by rfl⟩ : syracuseStep 3167831 = 4751747) B4751747
theorem B2111887 : Blo 2111435 2111887 := bstep (se 1 (by rfl) ⟨1583915, by rfl⟩ : syracuseStep 2111887 = 3167831) B3167831
theorem B3167837 : Blo 2111435 3167837 := bbase (se 3 (by rfl) ⟨593969, by rfl⟩ : syracuseStep 3167837 = 1187939) (by norm_num)
theorem B2111891 : Blo 2111435 2111891 := bstep (se 1 (by rfl) ⟨1583918, by rfl⟩ : syracuseStep 2111891 = 3167837) B3167837
theorem B4751765 : Blo 2111435 4751765 := bbase (se 6 (by rfl) ⟨111369, by rfl⟩ : syracuseStep 4751765 = 222739) (by norm_num)
theorem B3167843 : Blo 2111435 3167843 := bstep (se 1 (by rfl) ⟨2375882, by rfl⟩ : syracuseStep 3167843 = 4751765) B4751765
theorem B2111895 : Blo 2111435 2111895 := bstep (se 1 (by rfl) ⟨1583921, by rfl⟩ : syracuseStep 2111895 = 3167843) B3167843
theorem B5074285 : Blo 2111435 5074285 := bbase (se 3 (by rfl) ⟨951428, by rfl⟩ : syracuseStep 5074285 = 1902857) (by norm_num)
theorem B6765713 : Blo 2111435 6765713 := bstep (se 2 (by rfl) ⟨2537142, by rfl⟩ : syracuseStep 6765713 = 5074285) B5074285
theorem B4510475 : Blo 2111435 4510475 := bstep (se 1 (by rfl) ⟨3382856, by rfl⟩ : syracuseStep 4510475 = 6765713) B6765713
theorem B3006983 : Blo 2111435 3006983 := bstep (se 1 (by rfl) ⟨2255237, by rfl⟩ : syracuseStep 3006983 = 4510475) B4510475
theorem B8018621 : Blo 2111435 8018621 := bstep (se 3 (by rfl) ⟨1503491, by rfl⟩ : syracuseStep 8018621 = 3006983) B3006983
theorem B5345747 : Blo 2111435 5345747 := bstep (se 1 (by rfl) ⟨4009310, by rfl⟩ : syracuseStep 5345747 = 8018621) B8018621
theorem B3563831 : Blo 2111435 3563831 := bstep (se 1 (by rfl) ⟨2672873, by rfl⟩ : syracuseStep 3563831 = 5345747) B5345747
theorem B2375887 : Blo 2111435 2375887 := bstep (se 1 (by rfl) ⟨1781915, by rfl⟩ : syracuseStep 2375887 = 3563831) B3563831
theorem B3167849 : Blo 2111435 3167849 := bstep (se 2 (by rfl) ⟨1187943, by rfl⟩ : syracuseStep 3167849 = 2375887) B2375887
theorem B2111899 : Blo 2111435 2111899 := bstep (se 1 (by rfl) ⟨1583924, by rfl⟩ : syracuseStep 2111899 = 3167849) B3167849
theorem B9020965 : Blo 2111435 9020965 := bbase (se 4 (by rfl) ⟨845715, by rfl⟩ : syracuseStep 9020965 = 1691431) (by norm_num)
theorem B12027953 : Blo 2111435 12027953 := bstep (se 2 (by rfl) ⟨4510482, by rfl⟩ : syracuseStep 12027953 = 9020965) B9020965
theorem B8018635 : Blo 2111435 8018635 := bstep (se 1 (by rfl) ⟨6013976, by rfl⟩ : syracuseStep 8018635 = 12027953) B12027953
theorem B10691513 : Blo 2111435 10691513 := bstep (se 2 (by rfl) ⟨4009317, by rfl⟩ : syracuseStep 10691513 = 8018635) B8018635
theorem B7127675 : Blo 2111435 7127675 := bstep (se 1 (by rfl) ⟨5345756, by rfl⟩ : syracuseStep 7127675 = 10691513) B10691513
theorem B4751783 : Blo 2111435 4751783 := bstep (se 1 (by rfl) ⟨3563837, by rfl⟩ : syracuseStep 4751783 = 7127675) B7127675
theorem B3167855 : Blo 2111435 3167855 := bstep (se 1 (by rfl) ⟨2375891, by rfl⟩ : syracuseStep 3167855 = 4751783) B4751783
theorem B2111903 : Blo 2111435 2111903 := bstep (se 1 (by rfl) ⟨1583927, by rfl⟩ : syracuseStep 2111903 = 3167855) B3167855
theorem B3167861 : Blo 2111435 3167861 := bbase (se 5 (by rfl) ⟨148493, by rfl⟩ : syracuseStep 3167861 = 296987) (by norm_num)
theorem B2111907 : Blo 2111435 2111907 := bstep (se 1 (by rfl) ⟨1583930, by rfl⟩ : syracuseStep 2111907 = 3167861) B3167861
theorem B4009333 : Blo 2111435 4009333 := bbase (se 5 (by rfl) ⟨187937, by rfl⟩ : syracuseStep 4009333 = 375875) (by norm_num)
theorem B5345777 : Blo 2111435 5345777 := bstep (se 2 (by rfl) ⟨2004666, by rfl⟩ : syracuseStep 5345777 = 4009333) B4009333
theorem B3563851 : Blo 2111435 3563851 := bstep (se 1 (by rfl) ⟨2672888, by rfl⟩ : syracuseStep 3563851 = 5345777) B5345777
theorem B4751801 : Blo 2111435 4751801 := bstep (se 2 (by rfl) ⟨1781925, by rfl⟩ : syracuseStep 4751801 = 3563851) B3563851
theorem B3167867 : Blo 2111435 3167867 := bstep (se 1 (by rfl) ⟨2375900, by rfl⟩ : syracuseStep 3167867 = 4751801) B4751801
theorem B2111911 : Blo 2111435 2111911 := bstep (se 1 (by rfl) ⟨1583933, by rfl⟩ : syracuseStep 2111911 = 3167867) B3167867
theorem B2375905 : Blo 2111435 2375905 := bbase (se 2 (by rfl) ⟨890964, by rfl⟩ : syracuseStep 2375905 = 1781929) (by norm_num)
theorem B3167873 : Blo 2111435 3167873 := bstep (se 2 (by rfl) ⟨1187952, by rfl⟩ : syracuseStep 3167873 = 2375905) B2375905
theorem B2111915 : Blo 2111435 2111915 := bstep (se 1 (by rfl) ⟨1583936, by rfl⟩ : syracuseStep 2111915 = 3167873) B3167873
theorem B5345797 : Blo 2111435 5345797 := bbase (se 4 (by rfl) ⟨501168, by rfl⟩ : syracuseStep 5345797 = 1002337) (by norm_num)
theorem B7127729 : Blo 2111435 7127729 := bstep (se 2 (by rfl) ⟨2672898, by rfl⟩ : syracuseStep 7127729 = 5345797) B5345797
theorem B4751819 : Blo 2111435 4751819 := bstep (se 1 (by rfl) ⟨3563864, by rfl⟩ : syracuseStep 4751819 = 7127729) B7127729
theorem B3167879 : Blo 2111435 3167879 := bstep (se 1 (by rfl) ⟨2375909, by rfl⟩ : syracuseStep 3167879 = 4751819) B4751819
theorem B2111919 : Blo 2111435 2111919 := bstep (se 1 (by rfl) ⟨1583939, by rfl⟩ : syracuseStep 2111919 = 3167879) B3167879
theorem B3167885 : Blo 2111435 3167885 := bbase (se 3 (by rfl) ⟨593978, by rfl⟩ : syracuseStep 3167885 = 1187957) (by norm_num)
theorem B2111923 : Blo 2111435 2111923 := bstep (se 1 (by rfl) ⟨1583942, by rfl⟩ : syracuseStep 2111923 = 3167885) B3167885
theorem B4751837 : Blo 2111435 4751837 := bbase (se 3 (by rfl) ⟨890969, by rfl⟩ : syracuseStep 4751837 = 1781939) (by norm_num)
theorem B3167891 : Blo 2111435 3167891 := bstep (se 1 (by rfl) ⟨2375918, by rfl⟩ : syracuseStep 3167891 = 4751837) B4751837
theorem B2111927 : Blo 2111435 2111927 := bstep (se 1 (by rfl) ⟨1583945, by rfl⟩ : syracuseStep 2111927 = 3167891) B3167891
theorem B3563885 : Blo 2111435 3563885 := bbase (se 3 (by rfl) ⟨668228, by rfl⟩ : syracuseStep 3563885 = 1336457) (by norm_num)
theorem B2375923 : Blo 2111435 2375923 := bstep (se 1 (by rfl) ⟨1781942, by rfl⟩ : syracuseStep 2375923 = 3563885) B3563885
theorem B3167897 : Blo 2111435 3167897 := bstep (se 2 (by rfl) ⟨1187961, by rfl⟩ : syracuseStep 3167897 = 2375923) B2375923
theorem B2111931 : Blo 2111435 2111931 := bstep (se 1 (by rfl) ⟨1583948, by rfl⟩ : syracuseStep 2111931 = 3167897) B3167897
theorem B9144181 : Blo 2111435 9144181 := bbase (se 5 (by rfl) ⟨428633, by rfl⟩ : syracuseStep 9144181 = 857267) (by norm_num)
theorem B12192241 : Blo 2111435 12192241 := bstep (se 2 (by rfl) ⟨4572090, by rfl⟩ : syracuseStep 12192241 = 9144181) B9144181
theorem B16256321 : Blo 2111435 16256321 := bstep (se 2 (by rfl) ⟨6096120, by rfl⟩ : syracuseStep 16256321 = 12192241) B12192241
theorem B10837547 : Blo 2111435 10837547 := bstep (se 1 (by rfl) ⟨8128160, by rfl⟩ : syracuseStep 10837547 = 16256321) B16256321
theorem B7225031 : Blo 2111435 7225031 := bstep (se 1 (by rfl) ⟨5418773, by rfl⟩ : syracuseStep 7225031 = 10837547) B10837547
theorem B19266749 : Blo 2111435 19266749 := bstep (se 3 (by rfl) ⟨3612515, by rfl⟩ : syracuseStep 19266749 = 7225031) B7225031
theorem B12844499 : Blo 2111435 12844499 := bstep (se 1 (by rfl) ⟨9633374, by rfl⟩ : syracuseStep 12844499 = 19266749) B19266749
theorem B34251997 : Blo 2111435 34251997 := bstep (se 3 (by rfl) ⟨6422249, by rfl⟩ : syracuseStep 34251997 = 12844499) B12844499
theorem B45669329 : Blo 2111435 45669329 := bstep (se 2 (by rfl) ⟨17125998, by rfl⟩ : syracuseStep 45669329 = 34251997) B34251997
theorem B30446219 : Blo 2111435 30446219 := bstep (se 1 (by rfl) ⟨22834664, by rfl⟩ : syracuseStep 30446219 = 45669329) B45669329
theorem B20297479 : Blo 2111435 20297479 := bstep (se 1 (by rfl) ⟨15223109, by rfl⟩ : syracuseStep 20297479 = 30446219) B30446219
theorem B27063305 : Blo 2111435 27063305 := bstep (se 2 (by rfl) ⟨10148739, by rfl⟩ : syracuseStep 27063305 = 20297479) B20297479
theorem B18042203 : Blo 2111435 18042203 := bstep (se 1 (by rfl) ⟨13531652, by rfl⟩ : syracuseStep 18042203 = 27063305) B27063305
theorem B12028135 : Blo 2111435 12028135 := bstep (se 1 (by rfl) ⟨9021101, by rfl⟩ : syracuseStep 12028135 = 18042203) B18042203
theorem B16037513 : Blo 2111435 16037513 := bstep (se 2 (by rfl) ⟨6014067, by rfl⟩ : syracuseStep 16037513 = 12028135) B12028135
theorem B10691675 : Blo 2111435 10691675 := bstep (se 1 (by rfl) ⟨8018756, by rfl⟩ : syracuseStep 10691675 = 16037513) B16037513
theorem B7127783 : Blo 2111435 7127783 := bstep (se 1 (by rfl) ⟨5345837, by rfl⟩ : syracuseStep 7127783 = 10691675) B10691675
theorem B4751855 : Blo 2111435 4751855 := bstep (se 1 (by rfl) ⟨3563891, by rfl⟩ : syracuseStep 4751855 = 7127783) B7127783
theorem B3167903 : Blo 2111435 3167903 := bstep (se 1 (by rfl) ⟨2375927, by rfl⟩ : syracuseStep 3167903 = 4751855) B4751855
theorem B2111935 : Blo 2111435 2111935 := bstep (se 1 (by rfl) ⟨1583951, by rfl⟩ : syracuseStep 2111935 = 3167903) B3167903
theorem B3167909 : Blo 2111435 3167909 := bbase (se 4 (by rfl) ⟨296991, by rfl⟩ : syracuseStep 3167909 = 593983) (by norm_num)
theorem B2111939 : Blo 2111435 2111939 := bstep (se 1 (by rfl) ⟨1583954, by rfl⟩ : syracuseStep 2111939 = 3167909) B3167909
theorem B2672929 : Blo 2111435 2672929 := bbase (se 2 (by rfl) ⟨1002348, by rfl⟩ : syracuseStep 2672929 = 2004697) (by norm_num)
theorem B3563905 : Blo 2111435 3563905 := bstep (se 2 (by rfl) ⟨1336464, by rfl⟩ : syracuseStep 3563905 = 2672929) B2672929
theorem B4751873 : Blo 2111435 4751873 := bstep (se 2 (by rfl) ⟨1781952, by rfl⟩ : syracuseStep 4751873 = 3563905) B3563905
theorem B3167915 : Blo 2111435 3167915 := bstep (se 1 (by rfl) ⟨2375936, by rfl⟩ : syracuseStep 3167915 = 4751873) B4751873
theorem B2111943 : Blo 2111435 2111943 := bstep (se 1 (by rfl) ⟨1583957, by rfl⟩ : syracuseStep 2111943 = 3167915) B3167915
theorem B2375941 : Blo 2111435 2375941 := bbase (se 4 (by rfl) ⟨222744, by rfl⟩ : syracuseStep 2375941 = 445489) (by norm_num)
theorem B3167921 : Blo 2111435 3167921 := bstep (se 2 (by rfl) ⟨1187970, by rfl⟩ : syracuseStep 3167921 = 2375941) B2375941
theorem B2111947 : Blo 2111435 2111947 := bstep (se 1 (by rfl) ⟨1583960, by rfl⟩ : syracuseStep 2111947 = 3167921) B3167921
theorem B2255293 : Blo 2111435 2255293 := bbase (se 3 (by rfl) ⟨422867, by rfl⟩ : syracuseStep 2255293 = 845735) (by norm_num)
theorem B3007057 : Blo 2111435 3007057 := bstep (se 2 (by rfl) ⟨1127646, by rfl⟩ : syracuseStep 3007057 = 2255293) B2255293
theorem B4009409 : Blo 2111435 4009409 := bstep (se 2 (by rfl) ⟨1503528, by rfl⟩ : syracuseStep 4009409 = 3007057) B3007057
theorem B2672939 : Blo 2111435 2672939 := bstep (se 1 (by rfl) ⟨2004704, by rfl⟩ : syracuseStep 2672939 = 4009409) B4009409
theorem B7127837 : Blo 2111435 7127837 := bstep (se 3 (by rfl) ⟨1336469, by rfl⟩ : syracuseStep 7127837 = 2672939) B2672939
theorem B4751891 : Blo 2111435 4751891 := bstep (se 1 (by rfl) ⟨3563918, by rfl⟩ : syracuseStep 4751891 = 7127837) B7127837
theorem B3167927 : Blo 2111435 3167927 := bstep (se 1 (by rfl) ⟨2375945, by rfl⟩ : syracuseStep 3167927 = 4751891) B4751891
theorem B2111951 : Blo 2111435 2111951 := bstep (se 1 (by rfl) ⟨1583963, by rfl⟩ : syracuseStep 2111951 = 3167927) B3167927
theorem B3167933 : Blo 2111435 3167933 := bbase (se 3 (by rfl) ⟨593987, by rfl⟩ : syracuseStep 3167933 = 1187975) (by norm_num)
theorem B2111955 : Blo 2111435 2111955 := bstep (se 1 (by rfl) ⟨1583966, by rfl⟩ : syracuseStep 2111955 = 3167933) B3167933
theorem B4751909 : Blo 2111435 4751909 := bbase (se 4 (by rfl) ⟨445491, by rfl⟩ : syracuseStep 4751909 = 890983) (by norm_num)
theorem B3167939 : Blo 2111435 3167939 := bstep (se 1 (by rfl) ⟨2375954, by rfl⟩ : syracuseStep 3167939 = 4751909) B4751909
theorem B2111959 : Blo 2111435 2111959 := bstep (se 1 (by rfl) ⟨1583969, by rfl⟩ : syracuseStep 2111959 = 3167939) B3167939
theorem B5345909 : Blo 2111435 5345909 := bbase (se 5 (by rfl) ⟨250589, by rfl⟩ : syracuseStep 5345909 = 501179) (by norm_num)
theorem B3563939 : Blo 2111435 3563939 := bstep (se 1 (by rfl) ⟨2672954, by rfl⟩ : syracuseStep 3563939 = 5345909) B5345909
theorem B2375959 : Blo 2111435 2375959 := bstep (se 1 (by rfl) ⟨1781969, by rfl⟩ : syracuseStep 2375959 = 3563939) B3563939
theorem B3167945 : Blo 2111435 3167945 := bstep (se 2 (by rfl) ⟨1187979, by rfl⟩ : syracuseStep 3167945 = 2375959) B2375959
theorem B2111963 : Blo 2111435 2111963 := bstep (se 1 (by rfl) ⟨1583972, by rfl⟩ : syracuseStep 2111963 = 3167945) B3167945
theorem B17126261 : Blo 2111435 17126261 := bbase (se 5 (by rfl) ⟨802793, by rfl⟩ : syracuseStep 17126261 = 1605587) (by norm_num)
theorem B11417507 : Blo 2111435 11417507 := bstep (se 1 (by rfl) ⟨8563130, by rfl⟩ : syracuseStep 11417507 = 17126261) B17126261
theorem B7611671 : Blo 2111435 7611671 := bstep (se 1 (by rfl) ⟨5708753, by rfl⟩ : syracuseStep 7611671 = 11417507) B11417507
theorem B20297789 : Blo 2111435 20297789 := bstep (se 3 (by rfl) ⟨3805835, by rfl⟩ : syracuseStep 20297789 = 7611671) B7611671
theorem B13531859 : Blo 2111435 13531859 := bstep (se 1 (by rfl) ⟨10148894, by rfl⟩ : syracuseStep 13531859 = 20297789) B20297789
theorem B9021239 : Blo 2111435 9021239 := bstep (se 1 (by rfl) ⟨6765929, by rfl⟩ : syracuseStep 9021239 = 13531859) B13531859
theorem B6014159 : Blo 2111435 6014159 := bstep (se 1 (by rfl) ⟨4510619, by rfl⟩ : syracuseStep 6014159 = 9021239) B9021239
theorem B4009439 : Blo 2111435 4009439 := bstep (se 1 (by rfl) ⟨3007079, by rfl⟩ : syracuseStep 4009439 = 6014159) B6014159
theorem B10691837 : Blo 2111435 10691837 := bstep (se 3 (by rfl) ⟨2004719, by rfl⟩ : syracuseStep 10691837 = 4009439) B4009439
theorem B7127891 : Blo 2111435 7127891 := bstep (se 1 (by rfl) ⟨5345918, by rfl⟩ : syracuseStep 7127891 = 10691837) B10691837
theorem B4751927 : Blo 2111435 4751927 := bstep (se 1 (by rfl) ⟨3563945, by rfl⟩ : syracuseStep 4751927 = 7127891) B7127891
theorem B3167951 : Blo 2111435 3167951 := bstep (se 1 (by rfl) ⟨2375963, by rfl⟩ : syracuseStep 3167951 = 4751927) B4751927
theorem B2111967 : Blo 2111435 2111967 := bstep (se 1 (by rfl) ⟨1583975, by rfl⟩ : syracuseStep 2111967 = 3167951) B3167951
theorem B3167957 : Blo 2111435 3167957 := bbase (se 7 (by rfl) ⟨37124, by rfl⟩ : syracuseStep 3167957 = 74249) (by norm_num)
theorem B2111971 : Blo 2111435 2111971 := bstep (se 1 (by rfl) ⟨1583978, by rfl⟩ : syracuseStep 2111971 = 3167957) B3167957
theorem B4510637 : Blo 2111435 4510637 := bbase (se 3 (by rfl) ⟨845744, by rfl⟩ : syracuseStep 4510637 = 1691489) (by norm_num)
theorem B3007091 : Blo 2111435 3007091 := bstep (se 1 (by rfl) ⟨2255318, by rfl⟩ : syracuseStep 3007091 = 4510637) B4510637
theorem B8018909 : Blo 2111435 8018909 := bstep (se 3 (by rfl) ⟨1503545, by rfl⟩ : syracuseStep 8018909 = 3007091) B3007091
theorem B5345939 : Blo 2111435 5345939 := bstep (se 1 (by rfl) ⟨4009454, by rfl⟩ : syracuseStep 5345939 = 8018909) B8018909
theorem B3563959 : Blo 2111435 3563959 := bstep (se 1 (by rfl) ⟨2672969, by rfl⟩ : syracuseStep 3563959 = 5345939) B5345939
theorem B4751945 : Blo 2111435 4751945 := bstep (se 2 (by rfl) ⟨1781979, by rfl⟩ : syracuseStep 4751945 = 3563959) B3563959
theorem B3167963 : Blo 2111435 3167963 := bstep (se 1 (by rfl) ⟨2375972, by rfl⟩ : syracuseStep 3167963 = 4751945) B4751945
theorem B2111975 : Blo 2111435 2111975 := bstep (se 1 (by rfl) ⟨1583981, by rfl⟩ : syracuseStep 2111975 = 3167963) B3167963
theorem B2375977 : Blo 2111435 2375977 := bbase (se 2 (by rfl) ⟨890991, by rfl⟩ : syracuseStep 2375977 = 1781983) (by norm_num)
theorem B3167969 : Blo 2111435 3167969 := bstep (se 2 (by rfl) ⟨1187988, by rfl⟩ : syracuseStep 3167969 = 2375977) B2375977
theorem B2111979 : Blo 2111435 2111979 := bstep (se 1 (by rfl) ⟨1583984, by rfl⟩ : syracuseStep 2111979 = 3167969) B3167969
theorem B16256693 : Blo 2111435 16256693 := bbase (se 5 (by rfl) ⟨762032, by rfl⟩ : syracuseStep 16256693 = 1524065) (by norm_num)
theorem B10837795 : Blo 2111435 10837795 := bstep (se 1 (by rfl) ⟨8128346, by rfl⟩ : syracuseStep 10837795 = 16256693) B16256693
theorem B14450393 : Blo 2111435 14450393 := bstep (se 2 (by rfl) ⟨5418897, by rfl⟩ : syracuseStep 14450393 = 10837795) B10837795
theorem B9633595 : Blo 2111435 9633595 := bstep (se 1 (by rfl) ⟨7225196, by rfl⟩ : syracuseStep 9633595 = 14450393) B14450393
theorem B12844793 : Blo 2111435 12844793 := bstep (se 2 (by rfl) ⟨4816797, by rfl⟩ : syracuseStep 12844793 = 9633595) B9633595
theorem B8563195 : Blo 2111435 8563195 := bstep (se 1 (by rfl) ⟨6422396, by rfl⟩ : syracuseStep 8563195 = 12844793) B12844793
theorem B11417593 : Blo 2111435 11417593 := bstep (se 2 (by rfl) ⟨4281597, by rfl⟩ : syracuseStep 11417593 = 8563195) B8563195
theorem B15223457 : Blo 2111435 15223457 := bstep (se 2 (by rfl) ⟨5708796, by rfl⟩ : syracuseStep 15223457 = 11417593) B11417593
theorem B10148971 : Blo 2111435 10148971 := bstep (se 1 (by rfl) ⟨7611728, by rfl⟩ : syracuseStep 10148971 = 15223457) B15223457
theorem B13531961 : Blo 2111435 13531961 := bstep (se 2 (by rfl) ⟨5074485, by rfl⟩ : syracuseStep 13531961 = 10148971) B10148971
theorem B9021307 : Blo 2111435 9021307 := bstep (se 1 (by rfl) ⟨6765980, by rfl⟩ : syracuseStep 9021307 = 13531961) B13531961
theorem B12028409 : Blo 2111435 12028409 := bstep (se 2 (by rfl) ⟨4510653, by rfl⟩ : syracuseStep 12028409 = 9021307) B9021307
theorem B8018939 : Blo 2111435 8018939 := bstep (se 1 (by rfl) ⟨6014204, by rfl⟩ : syracuseStep 8018939 = 12028409) B12028409
theorem B5345959 : Blo 2111435 5345959 := bstep (se 1 (by rfl) ⟨4009469, by rfl⟩ : syracuseStep 5345959 = 8018939) B8018939
theorem B7127945 : Blo 2111435 7127945 := bstep (se 2 (by rfl) ⟨2672979, by rfl⟩ : syracuseStep 7127945 = 5345959) B5345959
theorem B4751963 : Blo 2111435 4751963 := bstep (se 1 (by rfl) ⟨3563972, by rfl⟩ : syracuseStep 4751963 = 7127945) B7127945
theorem B3167975 : Blo 2111435 3167975 := bstep (se 1 (by rfl) ⟨2375981, by rfl⟩ : syracuseStep 3167975 = 4751963) B4751963
theorem B2111983 : Blo 2111435 2111983 := bstep (se 1 (by rfl) ⟨1583987, by rfl⟩ : syracuseStep 2111983 = 3167975) B3167975
theorem B3167981 : Blo 2111435 3167981 := bbase (se 3 (by rfl) ⟨593996, by rfl⟩ : syracuseStep 3167981 = 1187993) (by norm_num)
theorem B2111987 : Blo 2111435 2111987 := bstep (se 1 (by rfl) ⟨1583990, by rfl⟩ : syracuseStep 2111987 = 3167981) B3167981
theorem B4751981 : Blo 2111435 4751981 := bbase (se 3 (by rfl) ⟨890996, by rfl⟩ : syracuseStep 4751981 = 1781993) (by norm_num)
theorem B3167987 : Blo 2111435 3167987 := bstep (se 1 (by rfl) ⟨2375990, by rfl⟩ : syracuseStep 3167987 = 4751981) B4751981
theorem B2111991 : Blo 2111435 2111991 := bstep (se 1 (by rfl) ⟨1583993, by rfl⟩ : syracuseStep 2111991 = 3167987) B3167987
theorem B4009493 : Blo 2111435 4009493 := bbase (se 6 (by rfl) ⟨93972, by rfl⟩ : syracuseStep 4009493 = 187945) (by norm_num)
theorem B2672995 : Blo 2111435 2672995 := bstep (se 1 (by rfl) ⟨2004746, by rfl⟩ : syracuseStep 2672995 = 4009493) B4009493
theorem B3563993 : Blo 2111435 3563993 := bstep (se 2 (by rfl) ⟨1336497, by rfl⟩ : syracuseStep 3563993 = 2672995) B2672995
theorem B2375995 : Blo 2111435 2375995 := bstep (se 1 (by rfl) ⟨1781996, by rfl⟩ : syracuseStep 2375995 = 3563993) B3563993
theorem B3167993 : Blo 2111435 3167993 := bstep (se 2 (by rfl) ⟨1187997, by rfl⟩ : syracuseStep 3167993 = 2375995) B2375995
theorem B2111995 : Blo 2111435 2111995 := bstep (se 1 (by rfl) ⟨1583996, by rfl⟩ : syracuseStep 2111995 = 3167993) B3167993
theorem B5143757 : Blo 2111435 5143757 := bbase (se 3 (by rfl) ⟨964454, by rfl⟩ : syracuseStep 5143757 = 1928909) (by norm_num)
theorem B13716685 : Blo 2111435 13716685 := bstep (se 3 (by rfl) ⟨2571878, by rfl⟩ : syracuseStep 13716685 = 5143757) B5143757
theorem B18288913 : Blo 2111435 18288913 := bstep (se 2 (by rfl) ⟨6858342, by rfl⟩ : syracuseStep 18288913 = 13716685) B13716685
theorem B24385217 : Blo 2111435 24385217 := bstep (se 2 (by rfl) ⟨9144456, by rfl⟩ : syracuseStep 24385217 = 18288913) B18288913
theorem B65027245 : Blo 2111435 65027245 := bstep (se 3 (by rfl) ⟨12192608, by rfl⟩ : syracuseStep 65027245 = 24385217) B24385217
theorem B86702993 : Blo 2111435 86702993 := bstep (se 2 (by rfl) ⟨32513622, by rfl⟩ : syracuseStep 86702993 = 65027245) B65027245
theorem B57801995 : Blo 2111435 57801995 := bstep (se 1 (by rfl) ⟨43351496, by rfl⟩ : syracuseStep 57801995 = 86702993) B86702993
theorem B38534663 : Blo 2111435 38534663 := bstep (se 1 (by rfl) ⟨28900997, by rfl⟩ : syracuseStep 38534663 = 57801995) B57801995
theorem B102759101 : Blo 2111435 102759101 := bstep (se 3 (by rfl) ⟨19267331, by rfl⟩ : syracuseStep 102759101 = 38534663) B38534663
theorem B68506067 : Blo 2111435 68506067 := bstep (se 1 (by rfl) ⟨51379550, by rfl⟩ : syracuseStep 68506067 = 102759101) B102759101
theorem B45670711 : Blo 2111435 45670711 := bstep (se 1 (by rfl) ⟨34253033, by rfl⟩ : syracuseStep 45670711 = 68506067) B68506067
theorem B60894281 : Blo 2111435 60894281 := bstep (se 2 (by rfl) ⟨22835355, by rfl⟩ : syracuseStep 60894281 = 45670711) B45670711
theorem B40596187 : Blo 2111435 40596187 := bstep (se 1 (by rfl) ⟨30447140, by rfl⟩ : syracuseStep 40596187 = 60894281) B60894281
theorem B54128249 : Blo 2111435 54128249 := bstep (se 2 (by rfl) ⟨20298093, by rfl⟩ : syracuseStep 54128249 = 40596187) B40596187
theorem B36085499 : Blo 2111435 36085499 := bstep (se 1 (by rfl) ⟨27064124, by rfl⟩ : syracuseStep 36085499 = 54128249) B54128249
theorem B24056999 : Blo 2111435 24056999 := bstep (se 1 (by rfl) ⟨18042749, by rfl⟩ : syracuseStep 24056999 = 36085499) B36085499
theorem B16037999 : Blo 2111435 16037999 := bstep (se 1 (by rfl) ⟨12028499, by rfl⟩ : syracuseStep 16037999 = 24056999) B24056999
theorem B10691999 : Blo 2111435 10691999 := bstep (se 1 (by rfl) ⟨8018999, by rfl⟩ : syracuseStep 10691999 = 16037999) B16037999
theorem B7127999 : Blo 2111435 7127999 := bstep (se 1 (by rfl) ⟨5345999, by rfl⟩ : syracuseStep 7127999 = 10691999) B10691999
theorem B4751999 : Blo 2111435 4751999 := bstep (se 1 (by rfl) ⟨3563999, by rfl⟩ : syracuseStep 4751999 = 7127999) B7127999
theorem B3167999 : Blo 2111435 3167999 := bstep (se 1 (by rfl) ⟨2375999, by rfl⟩ : syracuseStep 3167999 = 4751999) B4751999
theorem B2111999 : Blo 2111435 2111999 := bstep (se 1 (by rfl) ⟨1583999, by rfl⟩ : syracuseStep 2111999 = 3167999) B3167999
theorem B3168005 : Blo 2111435 3168005 := bbase (se 4 (by rfl) ⟨297000, by rfl⟩ : syracuseStep 3168005 = 594001) (by norm_num)
theorem B2112003 : Blo 2111435 2112003 := bstep (se 1 (by rfl) ⟨1584002, by rfl⟩ : syracuseStep 2112003 = 3168005) B3168005
theorem B3564013 : Blo 2111435 3564013 := bbase (se 3 (by rfl) ⟨668252, by rfl⟩ : syracuseStep 3564013 = 1336505) (by norm_num)
theorem B4752017 : Blo 2111435 4752017 := bstep (se 2 (by rfl) ⟨1782006, by rfl⟩ : syracuseStep 4752017 = 3564013) B3564013
theorem B3168011 : Blo 2111435 3168011 := bstep (se 1 (by rfl) ⟨2376008, by rfl⟩ : syracuseStep 3168011 = 4752017) B4752017
theorem B2112007 : Blo 2111435 2112007 := bstep (se 1 (by rfl) ⟨1584005, by rfl⟩ : syracuseStep 2112007 = 3168011) B3168011
theorem B2376013 : Blo 2111435 2376013 := bbase (se 3 (by rfl) ⟨445502, by rfl⟩ : syracuseStep 2376013 = 891005) (by norm_num)
theorem B3168017 : Blo 2111435 3168017 := bstep (se 2 (by rfl) ⟨1188006, by rfl⟩ : syracuseStep 3168017 = 2376013) B2376013
theorem B2112011 : Blo 2111435 2112011 := bstep (se 1 (by rfl) ⟨1584008, by rfl⟩ : syracuseStep 2112011 = 3168017) B3168017
theorem B7128053 : Blo 2111435 7128053 := bbase (se 5 (by rfl) ⟨334127, by rfl⟩ : syracuseStep 7128053 = 668255) (by norm_num)
theorem B4752035 : Blo 2111435 4752035 := bstep (se 1 (by rfl) ⟨3564026, by rfl⟩ : syracuseStep 4752035 = 7128053) B7128053
theorem B3168023 : Blo 2111435 3168023 := bstep (se 1 (by rfl) ⟨2376017, by rfl⟩ : syracuseStep 3168023 = 4752035) B4752035
theorem B2112015 : Blo 2111435 2112015 := bstep (se 1 (by rfl) ⟨1584011, by rfl⟩ : syracuseStep 2112015 = 3168023) B3168023
theorem B3168029 : Blo 2111435 3168029 := bbase (se 3 (by rfl) ⟨594005, by rfl⟩ : syracuseStep 3168029 = 1188011) (by norm_num)
theorem B2112019 : Blo 2111435 2112019 := bstep (se 1 (by rfl) ⟨1584014, by rfl⟩ : syracuseStep 2112019 = 3168029) B3168029
theorem B4752053 : Blo 2111435 4752053 := bbase (se 5 (by rfl) ⟨222752, by rfl⟩ : syracuseStep 4752053 = 445505) (by norm_num)
theorem B3168035 : Blo 2111435 3168035 := bstep (se 1 (by rfl) ⟨2376026, by rfl⟩ : syracuseStep 3168035 = 4752053) B4752053
theorem B2112023 : Blo 2111435 2112023 := bstep (se 1 (by rfl) ⟨1584017, by rfl⟩ : syracuseStep 2112023 = 3168035) B3168035
theorem B12028661 : Blo 2111435 12028661 := bbase (se 5 (by rfl) ⟨563843, by rfl⟩ : syracuseStep 12028661 = 1127687) (by norm_num)
theorem B8019107 : Blo 2111435 8019107 := bstep (se 1 (by rfl) ⟨6014330, by rfl⟩ : syracuseStep 8019107 = 12028661) B12028661
theorem B5346071 : Blo 2111435 5346071 := bstep (se 1 (by rfl) ⟨4009553, by rfl⟩ : syracuseStep 5346071 = 8019107) B8019107
theorem B3564047 : Blo 2111435 3564047 := bstep (se 1 (by rfl) ⟨2673035, by rfl⟩ : syracuseStep 3564047 = 5346071) B5346071
theorem B2376031 : Blo 2111435 2376031 := bstep (se 1 (by rfl) ⟨1782023, by rfl⟩ : syracuseStep 2376031 = 3564047) B3564047
theorem B3168041 : Blo 2111435 3168041 := bstep (se 2 (by rfl) ⟨1188015, by rfl⟩ : syracuseStep 3168041 = 2376031) B2376031
theorem B2112027 : Blo 2111435 2112027 := bstep (se 1 (by rfl) ⟨1584020, by rfl⟩ : syracuseStep 2112027 = 3168041) B3168041
theorem B6014341 : Blo 2111435 6014341 := bbase (se 4 (by rfl) ⟨563844, by rfl⟩ : syracuseStep 6014341 = 1127689) (by norm_num)
theorem B8019121 : Blo 2111435 8019121 := bstep (se 2 (by rfl) ⟨3007170, by rfl⟩ : syracuseStep 8019121 = 6014341) B6014341
theorem B10692161 : Blo 2111435 10692161 := bstep (se 2 (by rfl) ⟨4009560, by rfl⟩ : syracuseStep 10692161 = 8019121) B8019121
theorem B7128107 : Blo 2111435 7128107 := bstep (se 1 (by rfl) ⟨5346080, by rfl⟩ : syracuseStep 7128107 = 10692161) B10692161
theorem B4752071 : Blo 2111435 4752071 := bstep (se 1 (by rfl) ⟨3564053, by rfl⟩ : syracuseStep 4752071 = 7128107) B7128107
theorem B3168047 : Blo 2111435 3168047 := bstep (se 1 (by rfl) ⟨2376035, by rfl⟩ : syracuseStep 3168047 = 4752071) B4752071
theorem B2112031 : Blo 2111435 2112031 := bstep (se 1 (by rfl) ⟨1584023, by rfl⟩ : syracuseStep 2112031 = 3168047) B3168047
theorem B3168053 : Blo 2111435 3168053 := bbase (se 5 (by rfl) ⟨148502, by rfl⟩ : syracuseStep 3168053 = 297005) (by norm_num)
theorem B2112035 : Blo 2111435 2112035 := bstep (se 1 (by rfl) ⟨1584026, by rfl⟩ : syracuseStep 2112035 = 3168053) B3168053
theorem B5346101 : Blo 2111435 5346101 := bbase (se 5 (by rfl) ⟨250598, by rfl⟩ : syracuseStep 5346101 = 501197) (by norm_num)
theorem B3564067 : Blo 2111435 3564067 := bstep (se 1 (by rfl) ⟨2673050, by rfl⟩ : syracuseStep 3564067 = 5346101) B5346101
theorem B4752089 : Blo 2111435 4752089 := bstep (se 2 (by rfl) ⟨1782033, by rfl⟩ : syracuseStep 4752089 = 3564067) B3564067
theorem B3168059 : Blo 2111435 3168059 := bstep (se 1 (by rfl) ⟨2376044, by rfl⟩ : syracuseStep 3168059 = 4752089) B4752089
theorem B2112039 : Blo 2111435 2112039 := bstep (se 1 (by rfl) ⟨1584029, by rfl⟩ : syracuseStep 2112039 = 3168059) B3168059
theorem B2376049 : Blo 2111435 2376049 := bbase (se 2 (by rfl) ⟨891018, by rfl⟩ : syracuseStep 2376049 = 1782037) (by norm_num)
theorem B3168065 : Blo 2111435 3168065 := bstep (se 2 (by rfl) ⟨1188024, by rfl⟩ : syracuseStep 3168065 = 2376049) B2376049
theorem B2112043 : Blo 2111435 2112043 := bstep (se 1 (by rfl) ⟨1584032, by rfl⟩ : syracuseStep 2112043 = 3168065) B3168065
theorem B3383093 : Blo 2111435 3383093 := bbase (se 5 (by rfl) ⟨158582, by rfl⟩ : syracuseStep 3383093 = 317165) (by norm_num)
theorem B9021581 : Blo 2111435 9021581 := bstep (se 3 (by rfl) ⟨1691546, by rfl⟩ : syracuseStep 9021581 = 3383093) B3383093
theorem B6014387 : Blo 2111435 6014387 := bstep (se 1 (by rfl) ⟨4510790, by rfl⟩ : syracuseStep 6014387 = 9021581) B9021581
theorem B4009591 : Blo 2111435 4009591 := bstep (se 1 (by rfl) ⟨3007193, by rfl⟩ : syracuseStep 4009591 = 6014387) B6014387
theorem B5346121 : Blo 2111435 5346121 := bstep (se 2 (by rfl) ⟨2004795, by rfl⟩ : syracuseStep 5346121 = 4009591) B4009591
theorem B7128161 : Blo 2111435 7128161 := bstep (se 2 (by rfl) ⟨2673060, by rfl⟩ : syracuseStep 7128161 = 5346121) B5346121
theorem B4752107 : Blo 2111435 4752107 := bstep (se 1 (by rfl) ⟨3564080, by rfl⟩ : syracuseStep 4752107 = 7128161) B7128161
theorem B3168071 : Blo 2111435 3168071 := bstep (se 1 (by rfl) ⟨2376053, by rfl⟩ : syracuseStep 3168071 = 4752107) B4752107
theorem B2112047 : Blo 2111435 2112047 := bstep (se 1 (by rfl) ⟨1584035, by rfl⟩ : syracuseStep 2112047 = 3168071) B3168071
theorem B3168077 : Blo 2111435 3168077 := bbase (se 3 (by rfl) ⟨594014, by rfl⟩ : syracuseStep 3168077 = 1188029) (by norm_num)
theorem B2112051 : Blo 2111435 2112051 := bstep (se 1 (by rfl) ⟨1584038, by rfl⟩ : syracuseStep 2112051 = 3168077) B3168077
theorem B4752125 : Blo 2111435 4752125 := bbase (se 3 (by rfl) ⟨891023, by rfl⟩ : syracuseStep 4752125 = 1782047) (by norm_num)
theorem B3168083 : Blo 2111435 3168083 := bstep (se 1 (by rfl) ⟨2376062, by rfl⟩ : syracuseStep 3168083 = 4752125) B4752125
theorem B2112055 : Blo 2111435 2112055 := bstep (se 1 (by rfl) ⟨1584041, by rfl⟩ : syracuseStep 2112055 = 3168083) B3168083
theorem B3564101 : Blo 2111435 3564101 := bbase (se 4 (by rfl) ⟨334134, by rfl⟩ : syracuseStep 3564101 = 668269) (by norm_num)
theorem B2376067 : Blo 2111435 2376067 := bstep (se 1 (by rfl) ⟨1782050, by rfl⟩ : syracuseStep 2376067 = 3564101) B3564101
theorem B3168089 : Blo 2111435 3168089 := bstep (se 2 (by rfl) ⟨1188033, by rfl⟩ : syracuseStep 3168089 = 2376067) B2376067
theorem B2112059 : Blo 2111435 2112059 := bstep (se 1 (by rfl) ⟨1584044, by rfl⟩ : syracuseStep 2112059 = 3168089) B3168089
theorem B16038485 : Blo 2111435 16038485 := bbase (se 8 (by rfl) ⟨93975, by rfl⟩ : syracuseStep 16038485 = 187951) (by norm_num)
theorem B10692323 : Blo 2111435 10692323 := bstep (se 1 (by rfl) ⟨8019242, by rfl⟩ : syracuseStep 10692323 = 16038485) B16038485
theorem B7128215 : Blo 2111435 7128215 := bstep (se 1 (by rfl) ⟨5346161, by rfl⟩ : syracuseStep 7128215 = 10692323) B10692323
theorem B4752143 : Blo 2111435 4752143 := bstep (se 1 (by rfl) ⟨3564107, by rfl⟩ : syracuseStep 4752143 = 7128215) B7128215
theorem B3168095 : Blo 2111435 3168095 := bstep (se 1 (by rfl) ⟨2376071, by rfl⟩ : syracuseStep 3168095 = 4752143) B4752143
theorem B2112063 : Blo 2111435 2112063 := bstep (se 1 (by rfl) ⟨1584047, by rfl⟩ : syracuseStep 2112063 = 3168095) B3168095
theorem B3168101 : Blo 2111435 3168101 := bbase (se 4 (by rfl) ⟨297009, by rfl⟩ : syracuseStep 3168101 = 594019) (by norm_num)
theorem B2112067 : Blo 2111435 2112067 := bstep (se 1 (by rfl) ⟨1584050, by rfl⟩ : syracuseStep 2112067 = 3168101) B3168101
theorem B4009637 : Blo 2111435 4009637 := bbase (se 4 (by rfl) ⟨375903, by rfl⟩ : syracuseStep 4009637 = 751807) (by norm_num)
theorem B2673091 : Blo 2111435 2673091 := bstep (se 1 (by rfl) ⟨2004818, by rfl⟩ : syracuseStep 2673091 = 4009637) B4009637
theorem B3564121 : Blo 2111435 3564121 := bstep (se 2 (by rfl) ⟨1336545, by rfl⟩ : syracuseStep 3564121 = 2673091) B2673091
theorem B4752161 : Blo 2111435 4752161 := bstep (se 2 (by rfl) ⟨1782060, by rfl⟩ : syracuseStep 4752161 = 3564121) B3564121
theorem B3168107 : Blo 2111435 3168107 := bstep (se 1 (by rfl) ⟨2376080, by rfl⟩ : syracuseStep 3168107 = 4752161) B4752161
theorem B2112071 : Blo 2111435 2112071 := bstep (se 1 (by rfl) ⟨1584053, by rfl⟩ : syracuseStep 2112071 = 3168107) B3168107
theorem B2376085 : Blo 2111435 2376085 := bbase (se 6 (by rfl) ⟨55689, by rfl⟩ : syracuseStep 2376085 = 111379) (by norm_num)
theorem B3168113 : Blo 2111435 3168113 := bstep (se 2 (by rfl) ⟨1188042, by rfl⟩ : syracuseStep 3168113 = 2376085) B2376085
theorem B2112075 : Blo 2111435 2112075 := bstep (se 1 (by rfl) ⟨1584056, by rfl⟩ : syracuseStep 2112075 = 3168113) B3168113
theorem B2673101 : Blo 2111435 2673101 := bbase (se 3 (by rfl) ⟨501206, by rfl⟩ : syracuseStep 2673101 = 1002413) (by norm_num)
theorem B7128269 : Blo 2111435 7128269 := bstep (se 3 (by rfl) ⟨1336550, by rfl⟩ : syracuseStep 7128269 = 2673101) B2673101
theorem B4752179 : Blo 2111435 4752179 := bstep (se 1 (by rfl) ⟨3564134, by rfl⟩ : syracuseStep 4752179 = 7128269) B7128269
theorem B3168119 : Blo 2111435 3168119 := bstep (se 1 (by rfl) ⟨2376089, by rfl⟩ : syracuseStep 3168119 = 4752179) B4752179
theorem B2112079 : Blo 2111435 2112079 := bstep (se 1 (by rfl) ⟨1584059, by rfl⟩ : syracuseStep 2112079 = 3168119) B3168119
theorem B3168125 : Blo 2111435 3168125 := bbase (se 3 (by rfl) ⟨594023, by rfl⟩ : syracuseStep 3168125 = 1188047) (by norm_num)
theorem B2112083 : Blo 2111435 2112083 := bstep (se 1 (by rfl) ⟨1584062, by rfl⟩ : syracuseStep 2112083 = 3168125) B3168125
theorem B4752197 : Blo 2111435 4752197 := bbase (se 4 (by rfl) ⟨445518, by rfl⟩ : syracuseStep 4752197 = 891037) (by norm_num)
theorem B3168131 : Blo 2111435 3168131 := bstep (se 1 (by rfl) ⟨2376098, by rfl⟩ : syracuseStep 3168131 = 4752197) B4752197
theorem B2112087 : Blo 2111435 2112087 := bstep (se 1 (by rfl) ⟨1584065, by rfl⟩ : syracuseStep 2112087 = 3168131) B3168131
theorem B4510885 : Blo 2111435 4510885 := bbase (se 4 (by rfl) ⟨422895, by rfl⟩ : syracuseStep 4510885 = 845791) (by norm_num)
theorem B6014513 : Blo 2111435 6014513 := bstep (se 2 (by rfl) ⟨2255442, by rfl⟩ : syracuseStep 6014513 = 4510885) B4510885
theorem B4009675 : Blo 2111435 4009675 := bstep (se 1 (by rfl) ⟨3007256, by rfl⟩ : syracuseStep 4009675 = 6014513) B6014513
theorem B5346233 : Blo 2111435 5346233 := bstep (se 2 (by rfl) ⟨2004837, by rfl⟩ : syracuseStep 5346233 = 4009675) B4009675
theorem B3564155 : Blo 2111435 3564155 := bstep (se 1 (by rfl) ⟨2673116, by rfl⟩ : syracuseStep 3564155 = 5346233) B5346233
theorem B2376103 : Blo 2111435 2376103 := bstep (se 1 (by rfl) ⟨1782077, by rfl⟩ : syracuseStep 2376103 = 3564155) B3564155
theorem B3168137 : Blo 2111435 3168137 := bstep (se 2 (by rfl) ⟨1188051, by rfl⟩ : syracuseStep 3168137 = 2376103) B2376103
theorem B2112091 : Blo 2111435 2112091 := bstep (se 1 (by rfl) ⟨1584068, by rfl⟩ : syracuseStep 2112091 = 3168137) B3168137
theorem B10692485 : Blo 2111435 10692485 := bbase (se 4 (by rfl) ⟨1002420, by rfl⟩ : syracuseStep 10692485 = 2004841) (by norm_num)
theorem B7128323 : Blo 2111435 7128323 := bstep (se 1 (by rfl) ⟨5346242, by rfl⟩ : syracuseStep 7128323 = 10692485) B10692485
theorem B4752215 : Blo 2111435 4752215 := bstep (se 1 (by rfl) ⟨3564161, by rfl⟩ : syracuseStep 4752215 = 7128323) B7128323
theorem B3168143 : Blo 2111435 3168143 := bstep (se 1 (by rfl) ⟨2376107, by rfl⟩ : syracuseStep 3168143 = 4752215) B4752215
theorem B2112095 : Blo 2111435 2112095 := bstep (se 1 (by rfl) ⟨1584071, by rfl⟩ : syracuseStep 2112095 = 3168143) B3168143
theorem B3168149 : Blo 2111435 3168149 := bbase (se 6 (by rfl) ⟨74253, by rfl⟩ : syracuseStep 3168149 = 148507) (by norm_num)
theorem B2112099 : Blo 2111435 2112099 := bstep (se 1 (by rfl) ⟨1584074, by rfl⟩ : syracuseStep 2112099 = 3168149) B3168149
theorem B2140921 : Blo 2111435 2140921 := bbase (se 2 (by rfl) ⟨802845, by rfl⟩ : syracuseStep 2140921 = 1605691) (by norm_num)
theorem B11418245 : Blo 2111435 11418245 := bstep (se 4 (by rfl) ⟨1070460, by rfl⟩ : syracuseStep 11418245 = 2140921) B2140921
theorem B7612163 : Blo 2111435 7612163 := bstep (se 1 (by rfl) ⟨5709122, by rfl⟩ : syracuseStep 7612163 = 11418245) B11418245
theorem B5074775 : Blo 2111435 5074775 := bstep (se 1 (by rfl) ⟨3806081, by rfl⟩ : syracuseStep 5074775 = 7612163) B7612163
theorem B3383183 : Blo 2111435 3383183 := bstep (se 1 (by rfl) ⟨2537387, by rfl⟩ : syracuseStep 3383183 = 5074775) B5074775
theorem B2255455 : Blo 2111435 2255455 := bstep (se 1 (by rfl) ⟨1691591, by rfl⟩ : syracuseStep 2255455 = 3383183) B3383183
theorem B12029093 : Blo 2111435 12029093 := bstep (se 4 (by rfl) ⟨1127727, by rfl⟩ : syracuseStep 12029093 = 2255455) B2255455
theorem B8019395 : Blo 2111435 8019395 := bstep (se 1 (by rfl) ⟨6014546, by rfl⟩ : syracuseStep 8019395 = 12029093) B12029093
theorem B5346263 : Blo 2111435 5346263 := bstep (se 1 (by rfl) ⟨4009697, by rfl⟩ : syracuseStep 5346263 = 8019395) B8019395
theorem B3564175 : Blo 2111435 3564175 := bstep (se 1 (by rfl) ⟨2673131, by rfl⟩ : syracuseStep 3564175 = 5346263) B5346263
theorem B4752233 : Blo 2111435 4752233 := bstep (se 2 (by rfl) ⟨1782087, by rfl⟩ : syracuseStep 4752233 = 3564175) B3564175
theorem B3168155 : Blo 2111435 3168155 := bstep (se 1 (by rfl) ⟨2376116, by rfl⟩ : syracuseStep 3168155 = 4752233) B4752233
theorem B2112103 : Blo 2111435 2112103 := bstep (se 1 (by rfl) ⟨1584077, by rfl⟩ : syracuseStep 2112103 = 3168155) B3168155
theorem B2376121 : Blo 2111435 2376121 := bbase (se 2 (by rfl) ⟨891045, by rfl⟩ : syracuseStep 2376121 = 1782091) (by norm_num)
theorem B3168161 : Blo 2111435 3168161 := bstep (se 2 (by rfl) ⟨1188060, by rfl⟩ : syracuseStep 3168161 = 2376121) B2376121
theorem B2112107 : Blo 2111435 2112107 := bstep (se 1 (by rfl) ⟨1584080, by rfl⟩ : syracuseStep 2112107 = 3168161) B3168161
theorem B2408545 : Blo 2111435 2408545 := bbase (se 2 (by rfl) ⟨903204, by rfl⟩ : syracuseStep 2408545 = 1806409) (by norm_num)
theorem B12845573 : Blo 2111435 12845573 := bstep (se 4 (by rfl) ⟨1204272, by rfl⟩ : syracuseStep 12845573 = 2408545) B2408545
theorem B8563715 : Blo 2111435 8563715 := bstep (se 1 (by rfl) ⟨6422786, by rfl⟩ : syracuseStep 8563715 = 12845573) B12845573
theorem B5709143 : Blo 2111435 5709143 := bstep (se 1 (by rfl) ⟨4281857, by rfl⟩ : syracuseStep 5709143 = 8563715) B8563715
theorem B15224381 : Blo 2111435 15224381 := bstep (se 3 (by rfl) ⟨2854571, by rfl⟩ : syracuseStep 15224381 = 5709143) B5709143
theorem B10149587 : Blo 2111435 10149587 := bstep (se 1 (by rfl) ⟨7612190, by rfl⟩ : syracuseStep 10149587 = 15224381) B15224381
theorem B6766391 : Blo 2111435 6766391 := bstep (se 1 (by rfl) ⟨5074793, by rfl⟩ : syracuseStep 6766391 = 10149587) B10149587
theorem B4510927 : Blo 2111435 4510927 := bstep (se 1 (by rfl) ⟨3383195, by rfl⟩ : syracuseStep 4510927 = 6766391) B6766391
theorem B6014569 : Blo 2111435 6014569 := bstep (se 2 (by rfl) ⟨2255463, by rfl⟩ : syracuseStep 6014569 = 4510927) B4510927
theorem B8019425 : Blo 2111435 8019425 := bstep (se 2 (by rfl) ⟨3007284, by rfl⟩ : syracuseStep 8019425 = 6014569) B6014569
theorem B5346283 : Blo 2111435 5346283 := bstep (se 1 (by rfl) ⟨4009712, by rfl⟩ : syracuseStep 5346283 = 8019425) B8019425
theorem B7128377 : Blo 2111435 7128377 := bstep (se 2 (by rfl) ⟨2673141, by rfl⟩ : syracuseStep 7128377 = 5346283) B5346283
theorem B4752251 : Blo 2111435 4752251 := bstep (se 1 (by rfl) ⟨3564188, by rfl⟩ : syracuseStep 4752251 = 7128377) B7128377
theorem B3168167 : Blo 2111435 3168167 := bstep (se 1 (by rfl) ⟨2376125, by rfl⟩ : syracuseStep 3168167 = 4752251) B4752251
theorem B2112111 : Blo 2111435 2112111 := bstep (se 1 (by rfl) ⟨1584083, by rfl⟩ : syracuseStep 2112111 = 3168167) B3168167
theorem B3168173 : Blo 2111435 3168173 := bbase (se 3 (by rfl) ⟨594032, by rfl⟩ : syracuseStep 3168173 = 1188065) (by norm_num)
theorem B2112115 : Blo 2111435 2112115 := bstep (se 1 (by rfl) ⟨1584086, by rfl⟩ : syracuseStep 2112115 = 3168173) B3168173
theorem B4752269 : Blo 2111435 4752269 := bbase (se 3 (by rfl) ⟨891050, by rfl⟩ : syracuseStep 4752269 = 1782101) (by norm_num)
theorem B3168179 : Blo 2111435 3168179 := bstep (se 1 (by rfl) ⟨2376134, by rfl⟩ : syracuseStep 3168179 = 4752269) B4752269
theorem B2112119 : Blo 2111435 2112119 := bstep (se 1 (by rfl) ⟨1584089, by rfl⟩ : syracuseStep 2112119 = 3168179) B3168179
theorem B2673157 : Blo 2111435 2673157 := bbase (se 4 (by rfl) ⟨250608, by rfl⟩ : syracuseStep 2673157 = 501217) (by norm_num)
theorem B3564209 : Blo 2111435 3564209 := bstep (se 2 (by rfl) ⟨1336578, by rfl⟩ : syracuseStep 3564209 = 2673157) B2673157
theorem B2376139 : Blo 2111435 2376139 := bstep (se 1 (by rfl) ⟨1782104, by rfl⟩ : syracuseStep 2376139 = 3564209) B3564209
theorem B3168185 : Blo 2111435 3168185 := bstep (se 2 (by rfl) ⟨1188069, by rfl⟩ : syracuseStep 3168185 = 2376139) B2376139
theorem B2112123 : Blo 2111435 2112123 := bstep (se 1 (by rfl) ⟨1584092, by rfl⟩ : syracuseStep 2112123 = 3168185) B3168185
theorem B3612845 : Blo 2111435 3612845 := bbase (se 3 (by rfl) ⟨677408, by rfl⟩ : syracuseStep 3612845 = 1354817) (by norm_num)
theorem B2408563 : Blo 2111435 2408563 := bstep (se 1 (by rfl) ⟨1806422, by rfl⟩ : syracuseStep 2408563 = 3612845) B3612845
theorem B3211417 : Blo 2111435 3211417 := bstep (se 2 (by rfl) ⟨1204281, by rfl⟩ : syracuseStep 3211417 = 2408563) B2408563
theorem B17127557 : Blo 2111435 17127557 := bstep (se 4 (by rfl) ⟨1605708, by rfl⟩ : syracuseStep 17127557 = 3211417) B3211417
theorem B11418371 : Blo 2111435 11418371 := bstep (se 1 (by rfl) ⟨8563778, by rfl⟩ : syracuseStep 11418371 = 17127557) B17127557
theorem B7612247 : Blo 2111435 7612247 := bstep (se 1 (by rfl) ⟨5709185, by rfl⟩ : syracuseStep 7612247 = 11418371) B11418371
theorem B5074831 : Blo 2111435 5074831 := bstep (se 1 (by rfl) ⟨3806123, by rfl⟩ : syracuseStep 5074831 = 7612247) B7612247
theorem B27065765 : Blo 2111435 27065765 := bstep (se 4 (by rfl) ⟨2537415, by rfl⟩ : syracuseStep 27065765 = 5074831) B5074831
theorem B18043843 : Blo 2111435 18043843 := bstep (se 1 (by rfl) ⟨13532882, by rfl⟩ : syracuseStep 18043843 = 27065765) B27065765
theorem B24058457 : Blo 2111435 24058457 := bstep (se 2 (by rfl) ⟨9021921, by rfl⟩ : syracuseStep 24058457 = 18043843) B18043843
theorem B16038971 : Blo 2111435 16038971 := bstep (se 1 (by rfl) ⟨12029228, by rfl⟩ : syracuseStep 16038971 = 24058457) B24058457
theorem B10692647 : Blo 2111435 10692647 := bstep (se 1 (by rfl) ⟨8019485, by rfl⟩ : syracuseStep 10692647 = 16038971) B16038971
theorem B7128431 : Blo 2111435 7128431 := bstep (se 1 (by rfl) ⟨5346323, by rfl⟩ : syracuseStep 7128431 = 10692647) B10692647
theorem B4752287 : Blo 2111435 4752287 := bstep (se 1 (by rfl) ⟨3564215, by rfl⟩ : syracuseStep 4752287 = 7128431) B7128431
theorem B3168191 : Blo 2111435 3168191 := bstep (se 1 (by rfl) ⟨2376143, by rfl⟩ : syracuseStep 3168191 = 4752287) B4752287
theorem B2112127 : Blo 2111435 2112127 := bstep (se 1 (by rfl) ⟨1584095, by rfl⟩ : syracuseStep 2112127 = 3168191) B3168191
theorem B3168197 : Blo 2111435 3168197 := bbase (se 4 (by rfl) ⟨297018, by rfl⟩ : syracuseStep 3168197 = 594037) (by norm_num)
theorem B2112131 : Blo 2111435 2112131 := bstep (se 1 (by rfl) ⟨1584098, by rfl⟩ : syracuseStep 2112131 = 3168197) B3168197
theorem B3564229 : Blo 2111435 3564229 := bbase (se 4 (by rfl) ⟨334146, by rfl⟩ : syracuseStep 3564229 = 668293) (by norm_num)
theorem B4752305 : Blo 2111435 4752305 := bstep (se 2 (by rfl) ⟨1782114, by rfl⟩ : syracuseStep 4752305 = 3564229) B3564229
theorem B3168203 : Blo 2111435 3168203 := bstep (se 1 (by rfl) ⟨2376152, by rfl⟩ : syracuseStep 3168203 = 4752305) B4752305
theorem B2112135 : Blo 2111435 2112135 := bstep (se 1 (by rfl) ⟨1584101, by rfl⟩ : syracuseStep 2112135 = 3168203) B3168203
theorem B2376157 : Blo 2111435 2376157 := bbase (se 3 (by rfl) ⟨445529, by rfl⟩ : syracuseStep 2376157 = 891059) (by norm_num)
theorem B3168209 : Blo 2111435 3168209 := bstep (se 2 (by rfl) ⟨1188078, by rfl⟩ : syracuseStep 3168209 = 2376157) B2376157
theorem B2112139 : Blo 2111435 2112139 := bstep (se 1 (by rfl) ⟨1584104, by rfl⟩ : syracuseStep 2112139 = 3168209) B3168209
theorem B7128485 : Blo 2111435 7128485 := bbase (se 4 (by rfl) ⟨668295, by rfl⟩ : syracuseStep 7128485 = 1336591) (by norm_num)
theorem B4752323 : Blo 2111435 4752323 := bstep (se 1 (by rfl) ⟨3564242, by rfl⟩ : syracuseStep 4752323 = 7128485) B7128485
theorem B3168215 : Blo 2111435 3168215 := bstep (se 1 (by rfl) ⟨2376161, by rfl⟩ : syracuseStep 3168215 = 4752323) B4752323
theorem B2112143 : Blo 2111435 2112143 := bstep (se 1 (by rfl) ⟨1584107, by rfl⟩ : syracuseStep 2112143 = 3168215) B3168215
theorem B3168221 : Blo 2111435 3168221 := bbase (se 3 (by rfl) ⟨594041, by rfl⟩ : syracuseStep 3168221 = 1188083) (by norm_num)
theorem B2112147 : Blo 2111435 2112147 := bstep (se 1 (by rfl) ⟨1584110, by rfl⟩ : syracuseStep 2112147 = 3168221) B3168221
theorem B4752341 : Blo 2111435 4752341 := bbase (se 7 (by rfl) ⟨55691, by rfl⟩ : syracuseStep 4752341 = 111383) (by norm_num)
theorem B3168227 : Blo 2111435 3168227 := bstep (se 1 (by rfl) ⟨2376170, by rfl⟩ : syracuseStep 3168227 = 4752341) B4752341
theorem B2112151 : Blo 2111435 2112151 := bstep (se 1 (by rfl) ⟨1584113, by rfl⟩ : syracuseStep 2112151 = 3168227) B3168227
theorem B6096757 : Blo 2111435 6096757 := bbase (se 5 (by rfl) ⟨285785, by rfl⟩ : syracuseStep 6096757 = 571571) (by norm_num)
theorem B8129009 : Blo 2111435 8129009 := bstep (se 2 (by rfl) ⟨3048378, by rfl⟩ : syracuseStep 8129009 = 6096757) B6096757
theorem B21677357 : Blo 2111435 21677357 := bstep (se 3 (by rfl) ⟨4064504, by rfl⟩ : syracuseStep 21677357 = 8129009) B8129009
theorem B14451571 : Blo 2111435 14451571 := bstep (se 1 (by rfl) ⟨10838678, by rfl⟩ : syracuseStep 14451571 = 21677357) B21677357
theorem B19268761 : Blo 2111435 19268761 := bstep (se 2 (by rfl) ⟨7225785, by rfl⟩ : syracuseStep 19268761 = 14451571) B14451571
theorem B25691681 : Blo 2111435 25691681 := bstep (se 2 (by rfl) ⟨9634380, by rfl⟩ : syracuseStep 25691681 = 19268761) B19268761
theorem B17127787 : Blo 2111435 17127787 := bstep (se 1 (by rfl) ⟨12845840, by rfl⟩ : syracuseStep 17127787 = 25691681) B25691681
theorem B22837049 : Blo 2111435 22837049 := bstep (se 2 (by rfl) ⟨8563893, by rfl⟩ : syracuseStep 22837049 = 17127787) B17127787
theorem B15224699 : Blo 2111435 15224699 := bstep (se 1 (by rfl) ⟨11418524, by rfl⟩ : syracuseStep 15224699 = 22837049) B22837049
theorem B10149799 : Blo 2111435 10149799 := bstep (se 1 (by rfl) ⟨7612349, by rfl⟩ : syracuseStep 10149799 = 15224699) B15224699
theorem B13533065 : Blo 2111435 13533065 := bstep (se 2 (by rfl) ⟨5074899, by rfl⟩ : syracuseStep 13533065 = 10149799) B10149799
theorem B9022043 : Blo 2111435 9022043 := bstep (se 1 (by rfl) ⟨6766532, by rfl⟩ : syracuseStep 9022043 = 13533065) B13533065
theorem B6014695 : Blo 2111435 6014695 := bstep (se 1 (by rfl) ⟨4511021, by rfl⟩ : syracuseStep 6014695 = 9022043) B9022043
theorem B8019593 : Blo 2111435 8019593 := bstep (se 2 (by rfl) ⟨3007347, by rfl⟩ : syracuseStep 8019593 = 6014695) B6014695
theorem B5346395 : Blo 2111435 5346395 := bstep (se 1 (by rfl) ⟨4009796, by rfl⟩ : syracuseStep 5346395 = 8019593) B8019593
theorem B3564263 : Blo 2111435 3564263 := bstep (se 1 (by rfl) ⟨2673197, by rfl⟩ : syracuseStep 3564263 = 5346395) B5346395
theorem B2376175 : Blo 2111435 2376175 := bstep (se 1 (by rfl) ⟨1782131, by rfl⟩ : syracuseStep 2376175 = 3564263) B3564263
theorem B3168233 : Blo 2111435 3168233 := bstep (se 2 (by rfl) ⟨1188087, by rfl⟩ : syracuseStep 3168233 = 2376175) B2376175
theorem B2112155 : Blo 2111435 2112155 := bstep (se 1 (by rfl) ⟨1584116, by rfl⟩ : syracuseStep 2112155 = 3168233) B3168233
theorem B18044117 : Blo 2111435 18044117 := bbase (se 7 (by rfl) ⟨211454, by rfl⟩ : syracuseStep 18044117 = 422909) (by norm_num)
theorem B12029411 : Blo 2111435 12029411 := bstep (se 1 (by rfl) ⟨9022058, by rfl⟩ : syracuseStep 12029411 = 18044117) B18044117
theorem B8019607 : Blo 2111435 8019607 := bstep (se 1 (by rfl) ⟨6014705, by rfl⟩ : syracuseStep 8019607 = 12029411) B12029411
theorem B10692809 : Blo 2111435 10692809 := bstep (se 2 (by rfl) ⟨4009803, by rfl⟩ : syracuseStep 10692809 = 8019607) B8019607
theorem B7128539 : Blo 2111435 7128539 := bstep (se 1 (by rfl) ⟨5346404, by rfl⟩ : syracuseStep 7128539 = 10692809) B10692809
theorem B4752359 : Blo 2111435 4752359 := bstep (se 1 (by rfl) ⟨3564269, by rfl⟩ : syracuseStep 4752359 = 7128539) B7128539
theorem B3168239 : Blo 2111435 3168239 := bstep (se 1 (by rfl) ⟨2376179, by rfl⟩ : syracuseStep 3168239 = 4752359) B4752359
theorem B2112159 : Blo 2111435 2112159 := bstep (se 1 (by rfl) ⟨1584119, by rfl⟩ : syracuseStep 2112159 = 3168239) B3168239
theorem B3168245 : Blo 2111435 3168245 := bbase (se 5 (by rfl) ⟨148511, by rfl⟩ : syracuseStep 3168245 = 297023) (by norm_num)
theorem B2112163 : Blo 2111435 2112163 := bstep (se 1 (by rfl) ⟨1584122, by rfl⟩ : syracuseStep 2112163 = 3168245) B3168245
theorem B9396437 : Blo 2111435 9396437 := bbase (se 7 (by rfl) ⟨110114, by rfl⟩ : syracuseStep 9396437 = 220229) (by norm_num)
theorem B100228661 : Blo 2111435 100228661 := bstep (se 5 (by rfl) ⟨4698218, by rfl⟩ : syracuseStep 100228661 = 9396437) B9396437
theorem B66819107 : Blo 2111435 66819107 := bstep (se 1 (by rfl) ⟨50114330, by rfl⟩ : syracuseStep 66819107 = 100228661) B100228661
theorem B44546071 : Blo 2111435 44546071 := bstep (se 1 (by rfl) ⟨33409553, by rfl⟩ : syracuseStep 44546071 = 66819107) B66819107
theorem B59394761 : Blo 2111435 59394761 := bstep (se 2 (by rfl) ⟨22273035, by rfl⟩ : syracuseStep 59394761 = 44546071) B44546071
theorem B39596507 : Blo 2111435 39596507 := bstep (se 1 (by rfl) ⟨29697380, by rfl⟩ : syracuseStep 39596507 = 59394761) B59394761
theorem B26397671 : Blo 2111435 26397671 := bstep (se 1 (by rfl) ⟨19798253, by rfl⟩ : syracuseStep 26397671 = 39596507) B39596507
theorem B70393789 : Blo 2111435 70393789 := bstep (se 3 (by rfl) ⟨13198835, by rfl⟩ : syracuseStep 70393789 = 26397671) B26397671
theorem B93858385 : Blo 2111435 93858385 := bstep (se 2 (by rfl) ⟨35196894, by rfl⟩ : syracuseStep 93858385 = 70393789) B70393789
theorem B125144513 : Blo 2111435 125144513 := bstep (se 2 (by rfl) ⟨46929192, by rfl⟩ : syracuseStep 125144513 = 93858385) B93858385
theorem B83429675 : Blo 2111435 83429675 := bstep (se 1 (by rfl) ⟨62572256, by rfl⟩ : syracuseStep 83429675 = 125144513) B125144513
theorem B55619783 : Blo 2111435 55619783 := bstep (se 1 (by rfl) ⟨41714837, by rfl⟩ : syracuseStep 55619783 = 83429675) B83429675
theorem B37079855 : Blo 2111435 37079855 := bstep (se 1 (by rfl) ⟨27809891, by rfl⟩ : syracuseStep 37079855 = 55619783) B55619783
theorem B24719903 : Blo 2111435 24719903 := bstep (se 1 (by rfl) ⟨18539927, by rfl⟩ : syracuseStep 24719903 = 37079855) B37079855
theorem B16479935 : Blo 2111435 16479935 := bstep (se 1 (by rfl) ⟨12359951, by rfl⟩ : syracuseStep 16479935 = 24719903) B24719903
theorem B10986623 : Blo 2111435 10986623 := bstep (se 1 (by rfl) ⟨8239967, by rfl⟩ : syracuseStep 10986623 = 16479935) B16479935
theorem B7324415 : Blo 2111435 7324415 := bstep (se 1 (by rfl) ⟨5493311, by rfl⟩ : syracuseStep 7324415 = 10986623) B10986623
theorem B4882943 : Blo 2111435 4882943 := bstep (se 1 (by rfl) ⟨3662207, by rfl⟩ : syracuseStep 4882943 = 7324415) B7324415
theorem B3255295 : Blo 2111435 3255295 := bstep (se 1 (by rfl) ⟨2441471, by rfl⟩ : syracuseStep 3255295 = 4882943) B4882943
theorem B4340393 : Blo 2111435 4340393 := bstep (se 2 (by rfl) ⟨1627647, by rfl⟩ : syracuseStep 4340393 = 3255295) B3255295
theorem B2893595 : Blo 2111435 2893595 := bstep (se 1 (by rfl) ⟨2170196, by rfl⟩ : syracuseStep 2893595 = 4340393) B4340393
theorem B30865013 : Blo 2111435 30865013 := bstep (se 5 (by rfl) ⟨1446797, by rfl⟩ : syracuseStep 30865013 = 2893595) B2893595
theorem B20576675 : Blo 2111435 20576675 := bstep (se 1 (by rfl) ⟨15432506, by rfl⟩ : syracuseStep 20576675 = 30865013) B30865013
theorem B13717783 : Blo 2111435 13717783 := bstep (se 1 (by rfl) ⟨10288337, by rfl⟩ : syracuseStep 13717783 = 20576675) B20576675
theorem B18290377 : Blo 2111435 18290377 := bstep (se 2 (by rfl) ⟨6858891, by rfl⟩ : syracuseStep 18290377 = 13717783) B13717783
theorem B24387169 : Blo 2111435 24387169 := bstep (se 2 (by rfl) ⟨9145188, by rfl⟩ : syracuseStep 24387169 = 18290377) B18290377
theorem B32516225 : Blo 2111435 32516225 := bstep (se 2 (by rfl) ⟨12193584, by rfl⟩ : syracuseStep 32516225 = 24387169) B24387169
theorem B21677483 : Blo 2111435 21677483 := bstep (se 1 (by rfl) ⟨16258112, by rfl⟩ : syracuseStep 21677483 = 32516225) B32516225
theorem B14451655 : Blo 2111435 14451655 := bstep (se 1 (by rfl) ⟨10838741, by rfl⟩ : syracuseStep 14451655 = 21677483) B21677483
theorem B19268873 : Blo 2111435 19268873 := bstep (se 2 (by rfl) ⟨7225827, by rfl⟩ : syracuseStep 19268873 = 14451655) B14451655
theorem B12845915 : Blo 2111435 12845915 := bstep (se 1 (by rfl) ⟨9634436, by rfl⟩ : syracuseStep 12845915 = 19268873) B19268873
theorem B8563943 : Blo 2111435 8563943 := bstep (se 1 (by rfl) ⟨6422957, by rfl⟩ : syracuseStep 8563943 = 12845915) B12845915
theorem B5709295 : Blo 2111435 5709295 := bstep (se 1 (by rfl) ⟨4281971, by rfl⟩ : syracuseStep 5709295 = 8563943) B8563943
theorem B7612393 : Blo 2111435 7612393 := bstep (se 2 (by rfl) ⟨2854647, by rfl⟩ : syracuseStep 7612393 = 5709295) B5709295
theorem B10149857 : Blo 2111435 10149857 := bstep (se 2 (by rfl) ⟨3806196, by rfl⟩ : syracuseStep 10149857 = 7612393) B7612393
theorem B6766571 : Blo 2111435 6766571 := bstep (se 1 (by rfl) ⟨5074928, by rfl⟩ : syracuseStep 6766571 = 10149857) B10149857
theorem B4511047 : Blo 2111435 4511047 := bstep (se 1 (by rfl) ⟨3383285, by rfl⟩ : syracuseStep 4511047 = 6766571) B6766571
theorem B6014729 : Blo 2111435 6014729 := bstep (se 2 (by rfl) ⟨2255523, by rfl⟩ : syracuseStep 6014729 = 4511047) B4511047
theorem B4009819 : Blo 2111435 4009819 := bstep (se 1 (by rfl) ⟨3007364, by rfl⟩ : syracuseStep 4009819 = 6014729) B6014729
theorem B5346425 : Blo 2111435 5346425 := bstep (se 2 (by rfl) ⟨2004909, by rfl⟩ : syracuseStep 5346425 = 4009819) B4009819
theorem B3564283 : Blo 2111435 3564283 := bstep (se 1 (by rfl) ⟨2673212, by rfl⟩ : syracuseStep 3564283 = 5346425) B5346425
theorem B4752377 : Blo 2111435 4752377 := bstep (se 2 (by rfl) ⟨1782141, by rfl⟩ : syracuseStep 4752377 = 3564283) B3564283
theorem B3168251 : Blo 2111435 3168251 := bstep (se 1 (by rfl) ⟨2376188, by rfl⟩ : syracuseStep 3168251 = 4752377) B4752377
theorem B2112167 : Blo 2111435 2112167 := bstep (se 1 (by rfl) ⟨1584125, by rfl⟩ : syracuseStep 2112167 = 3168251) B3168251
theorem B2376193 : Blo 2111435 2376193 := bbase (se 2 (by rfl) ⟨891072, by rfl⟩ : syracuseStep 2376193 = 1782145) (by norm_num)
theorem B3168257 : Blo 2111435 3168257 := bstep (se 2 (by rfl) ⟨1188096, by rfl⟩ : syracuseStep 3168257 = 2376193) B2376193
theorem B2112171 : Blo 2111435 2112171 := bstep (se 1 (by rfl) ⟨1584128, by rfl⟩ : syracuseStep 2112171 = 3168257) B3168257
theorem B5346445 : Blo 2111435 5346445 := bbase (se 3 (by rfl) ⟨1002458, by rfl⟩ : syracuseStep 5346445 = 2004917) (by norm_num)
theorem B7128593 : Blo 2111435 7128593 := bstep (se 2 (by rfl) ⟨2673222, by rfl⟩ : syracuseStep 7128593 = 5346445) B5346445
theorem B4752395 : Blo 2111435 4752395 := bstep (se 1 (by rfl) ⟨3564296, by rfl⟩ : syracuseStep 4752395 = 7128593) B7128593
theorem B3168263 : Blo 2111435 3168263 := bstep (se 1 (by rfl) ⟨2376197, by rfl⟩ : syracuseStep 3168263 = 4752395) B4752395
theorem B2112175 : Blo 2111435 2112175 := bstep (se 1 (by rfl) ⟨1584131, by rfl⟩ : syracuseStep 2112175 = 3168263) B3168263
theorem B3168269 : Blo 2111435 3168269 := bbase (se 3 (by rfl) ⟨594050, by rfl⟩ : syracuseStep 3168269 = 1188101) (by norm_num)
theorem B2112179 : Blo 2111435 2112179 := bstep (se 1 (by rfl) ⟨1584134, by rfl⟩ : syracuseStep 2112179 = 3168269) B3168269
theorem B4752413 : Blo 2111435 4752413 := bbase (se 3 (by rfl) ⟨891077, by rfl⟩ : syracuseStep 4752413 = 1782155) (by norm_num)
theorem B3168275 : Blo 2111435 3168275 := bstep (se 1 (by rfl) ⟨2376206, by rfl⟩ : syracuseStep 3168275 = 4752413) B4752413
theorem B2112183 : Blo 2111435 2112183 := bstep (se 1 (by rfl) ⟨1584137, by rfl⟩ : syracuseStep 2112183 = 3168275) B3168275
theorem B3564317 : Blo 2111435 3564317 := bbase (se 3 (by rfl) ⟨668309, by rfl⟩ : syracuseStep 3564317 = 1336619) (by norm_num)
theorem B2376211 : Blo 2111435 2376211 := bstep (se 1 (by rfl) ⟨1782158, by rfl⟩ : syracuseStep 2376211 = 3564317) B3564317
theorem B3168281 : Blo 2111435 3168281 := bstep (se 2 (by rfl) ⟨1188105, by rfl⟩ : syracuseStep 3168281 = 2376211) B2376211
theorem B2112187 : Blo 2111435 2112187 := bstep (se 1 (by rfl) ⟨1584140, by rfl⟩ : syracuseStep 2112187 = 3168281) B3168281
theorem B10288453 : Blo 2111435 10288453 := bbase (se 4 (by rfl) ⟨964542, by rfl⟩ : syracuseStep 10288453 = 1929085) (by norm_num)
theorem B13717937 : Blo 2111435 13717937 := bstep (se 2 (by rfl) ⟨5144226, by rfl⟩ : syracuseStep 13717937 = 10288453) B10288453
theorem B36581165 : Blo 2111435 36581165 := bstep (se 3 (by rfl) ⟨6858968, by rfl⟩ : syracuseStep 36581165 = 13717937) B13717937
theorem B24387443 : Blo 2111435 24387443 := bstep (se 1 (by rfl) ⟨18290582, by rfl⟩ : syracuseStep 24387443 = 36581165) B36581165
theorem B16258295 : Blo 2111435 16258295 := bstep (se 1 (by rfl) ⟨12193721, by rfl⟩ : syracuseStep 16258295 = 24387443) B24387443
theorem B10838863 : Blo 2111435 10838863 := bstep (se 1 (by rfl) ⟨8129147, by rfl⟩ : syracuseStep 10838863 = 16258295) B16258295
theorem B14451817 : Blo 2111435 14451817 := bstep (se 2 (by rfl) ⟨5419431, by rfl⟩ : syracuseStep 14451817 = 10838863) B10838863
theorem B19269089 : Blo 2111435 19269089 := bstep (se 2 (by rfl) ⟨7225908, by rfl⟩ : syracuseStep 19269089 = 14451817) B14451817
theorem B12846059 : Blo 2111435 12846059 := bstep (se 1 (by rfl) ⟨9634544, by rfl⟩ : syracuseStep 12846059 = 19269089) B19269089
theorem B8564039 : Blo 2111435 8564039 := bstep (se 1 (by rfl) ⟨6423029, by rfl⟩ : syracuseStep 8564039 = 12846059) B12846059
theorem B5709359 : Blo 2111435 5709359 := bstep (se 1 (by rfl) ⟨4282019, by rfl⟩ : syracuseStep 5709359 = 8564039) B8564039
theorem B3806239 : Blo 2111435 3806239 := bstep (se 1 (by rfl) ⟨2854679, by rfl⟩ : syracuseStep 3806239 = 5709359) B5709359
theorem B5074985 : Blo 2111435 5074985 := bstep (se 2 (by rfl) ⟨1903119, by rfl⟩ : syracuseStep 5074985 = 3806239) B3806239
theorem B13533293 : Blo 2111435 13533293 := bstep (se 3 (by rfl) ⟨2537492, by rfl⟩ : syracuseStep 13533293 = 5074985) B5074985
theorem B9022195 : Blo 2111435 9022195 := bstep (se 1 (by rfl) ⟨6766646, by rfl⟩ : syracuseStep 9022195 = 13533293) B13533293
theorem B12029593 : Blo 2111435 12029593 := bstep (se 2 (by rfl) ⟨4511097, by rfl⟩ : syracuseStep 12029593 = 9022195) B9022195
theorem B16039457 : Blo 2111435 16039457 := bstep (se 2 (by rfl) ⟨6014796, by rfl⟩ : syracuseStep 16039457 = 12029593) B12029593
theorem B10692971 : Blo 2111435 10692971 := bstep (se 1 (by rfl) ⟨8019728, by rfl⟩ : syracuseStep 10692971 = 16039457) B16039457
theorem B7128647 : Blo 2111435 7128647 := bstep (se 1 (by rfl) ⟨5346485, by rfl⟩ : syracuseStep 7128647 = 10692971) B10692971
theorem B4752431 : Blo 2111435 4752431 := bstep (se 1 (by rfl) ⟨3564323, by rfl⟩ : syracuseStep 4752431 = 7128647) B7128647
theorem B3168287 : Blo 2111435 3168287 := bstep (se 1 (by rfl) ⟨2376215, by rfl⟩ : syracuseStep 3168287 = 4752431) B4752431
theorem B2112191 : Blo 2111435 2112191 := bstep (se 1 (by rfl) ⟨1584143, by rfl⟩ : syracuseStep 2112191 = 3168287) B3168287
theorem B3168293 : Blo 2111435 3168293 := bbase (se 4 (by rfl) ⟨297027, by rfl⟩ : syracuseStep 3168293 = 594055) (by norm_num)
theorem B2112195 : Blo 2111435 2112195 := bstep (se 1 (by rfl) ⟨1584146, by rfl⟩ : syracuseStep 2112195 = 3168293) B3168293
theorem B2673253 : Blo 2111435 2673253 := bbase (se 4 (by rfl) ⟨250617, by rfl⟩ : syracuseStep 2673253 = 501235) (by norm_num)
theorem B3564337 : Blo 2111435 3564337 := bstep (se 2 (by rfl) ⟨1336626, by rfl⟩ : syracuseStep 3564337 = 2673253) B2673253
theorem B4752449 : Blo 2111435 4752449 := bstep (se 2 (by rfl) ⟨1782168, by rfl⟩ : syracuseStep 4752449 = 3564337) B3564337
theorem B3168299 : Blo 2111435 3168299 := bstep (se 1 (by rfl) ⟨2376224, by rfl⟩ : syracuseStep 3168299 = 4752449) B4752449
theorem B2112199 : Blo 2111435 2112199 := bstep (se 1 (by rfl) ⟨1584149, by rfl⟩ : syracuseStep 2112199 = 3168299) B3168299
theorem B2376229 : Blo 2111435 2376229 := bbase (se 4 (by rfl) ⟨222771, by rfl⟩ : syracuseStep 2376229 = 445543) (by norm_num)
theorem B3168305 : Blo 2111435 3168305 := bstep (se 2 (by rfl) ⟨1188114, by rfl⟩ : syracuseStep 3168305 = 2376229) B2376229
theorem B2112203 : Blo 2111435 2112203 := bstep (se 1 (by rfl) ⟨1584152, by rfl⟩ : syracuseStep 2112203 = 3168305) B3168305
theorem B16258421 : Blo 2111435 16258421 := bbase (se 5 (by rfl) ⟨762113, by rfl⟩ : syracuseStep 16258421 = 1524227) (by norm_num)
theorem B10838947 : Blo 2111435 10838947 := bstep (se 1 (by rfl) ⟨8129210, by rfl⟩ : syracuseStep 10838947 = 16258421) B16258421
theorem B14451929 : Blo 2111435 14451929 := bstep (se 2 (by rfl) ⟨5419473, by rfl⟩ : syracuseStep 14451929 = 10838947) B10838947
theorem B9634619 : Blo 2111435 9634619 := bstep (se 1 (by rfl) ⟨7225964, by rfl⟩ : syracuseStep 9634619 = 14451929) B14451929
theorem B6423079 : Blo 2111435 6423079 := bstep (se 1 (by rfl) ⟨4817309, by rfl⟩ : syracuseStep 6423079 = 9634619) B9634619
theorem B8564105 : Blo 2111435 8564105 := bstep (se 2 (by rfl) ⟨3211539, by rfl⟩ : syracuseStep 8564105 = 6423079) B6423079
theorem B5709403 : Blo 2111435 5709403 := bstep (se 1 (by rfl) ⟨4282052, by rfl⟩ : syracuseStep 5709403 = 8564105) B8564105
theorem B7612537 : Blo 2111435 7612537 := bstep (se 2 (by rfl) ⟨2854701, by rfl⟩ : syracuseStep 7612537 = 5709403) B5709403
theorem B10150049 : Blo 2111435 10150049 := bstep (se 2 (by rfl) ⟨3806268, by rfl⟩ : syracuseStep 10150049 = 7612537) B7612537
theorem B6766699 : Blo 2111435 6766699 := bstep (se 1 (by rfl) ⟨5075024, by rfl⟩ : syracuseStep 6766699 = 10150049) B10150049
theorem B9022265 : Blo 2111435 9022265 := bstep (se 2 (by rfl) ⟨3383349, by rfl⟩ : syracuseStep 9022265 = 6766699) B6766699
theorem B6014843 : Blo 2111435 6014843 := bstep (se 1 (by rfl) ⟨4511132, by rfl⟩ : syracuseStep 6014843 = 9022265) B9022265
theorem B4009895 : Blo 2111435 4009895 := bstep (se 1 (by rfl) ⟨3007421, by rfl⟩ : syracuseStep 4009895 = 6014843) B6014843
theorem B2673263 : Blo 2111435 2673263 := bstep (se 1 (by rfl) ⟨2004947, by rfl⟩ : syracuseStep 2673263 = 4009895) B4009895
theorem B7128701 : Blo 2111435 7128701 := bstep (se 3 (by rfl) ⟨1336631, by rfl⟩ : syracuseStep 7128701 = 2673263) B2673263
theorem B4752467 : Blo 2111435 4752467 := bstep (se 1 (by rfl) ⟨3564350, by rfl⟩ : syracuseStep 4752467 = 7128701) B7128701
theorem B3168311 : Blo 2111435 3168311 := bstep (se 1 (by rfl) ⟨2376233, by rfl⟩ : syracuseStep 3168311 = 4752467) B4752467
theorem B2112207 : Blo 2111435 2112207 := bstep (se 1 (by rfl) ⟨1584155, by rfl⟩ : syracuseStep 2112207 = 3168311) B3168311
theorem B3168317 : Blo 2111435 3168317 := bbase (se 3 (by rfl) ⟨594059, by rfl⟩ : syracuseStep 3168317 = 1188119) (by norm_num)
theorem B2112211 : Blo 2111435 2112211 := bstep (se 1 (by rfl) ⟨1584158, by rfl⟩ : syracuseStep 2112211 = 3168317) B3168317
theorem B4752485 : Blo 2111435 4752485 := bbase (se 4 (by rfl) ⟨445545, by rfl⟩ : syracuseStep 4752485 = 891091) (by norm_num)
theorem B3168323 : Blo 2111435 3168323 := bstep (se 1 (by rfl) ⟨2376242, by rfl⟩ : syracuseStep 3168323 = 4752485) B4752485
theorem B2112215 : Blo 2111435 2112215 := bstep (se 1 (by rfl) ⟨1584161, by rfl⟩ : syracuseStep 2112215 = 3168323) B3168323
theorem B5346557 : Blo 2111435 5346557 := bbase (se 3 (by rfl) ⟨1002479, by rfl⟩ : syracuseStep 5346557 = 2004959) (by norm_num)
theorem B3564371 : Blo 2111435 3564371 := bstep (se 1 (by rfl) ⟨2673278, by rfl⟩ : syracuseStep 3564371 = 5346557) B5346557
theorem B2376247 : Blo 2111435 2376247 := bstep (se 1 (by rfl) ⟨1782185, by rfl⟩ : syracuseStep 2376247 = 3564371) B3564371
theorem B3168329 : Blo 2111435 3168329 := bstep (se 2 (by rfl) ⟨1188123, by rfl⟩ : syracuseStep 3168329 = 2376247) B2376247
theorem B2112219 : Blo 2111435 2112219 := bstep (se 1 (by rfl) ⟨1584164, by rfl⟩ : syracuseStep 2112219 = 3168329) B3168329
theorem B4009925 : Blo 2111435 4009925 := bbase (se 4 (by rfl) ⟨375930, by rfl⟩ : syracuseStep 4009925 = 751861) (by norm_num)
theorem B10693133 : Blo 2111435 10693133 := bstep (se 3 (by rfl) ⟨2004962, by rfl⟩ : syracuseStep 10693133 = 4009925) B4009925
theorem B7128755 : Blo 2111435 7128755 := bstep (se 1 (by rfl) ⟨5346566, by rfl⟩ : syracuseStep 7128755 = 10693133) B10693133
theorem B4752503 : Blo 2111435 4752503 := bstep (se 1 (by rfl) ⟨3564377, by rfl⟩ : syracuseStep 4752503 = 7128755) B7128755
theorem B3168335 : Blo 2111435 3168335 := bstep (se 1 (by rfl) ⟨2376251, by rfl⟩ : syracuseStep 3168335 = 4752503) B4752503
theorem B2112223 : Blo 2111435 2112223 := bstep (se 1 (by rfl) ⟨1584167, by rfl⟩ : syracuseStep 2112223 = 3168335) B3168335
theorem B3168341 : Blo 2111435 3168341 := bbase (se 8 (by rfl) ⟨18564, by rfl⟩ : syracuseStep 3168341 = 37129) (by norm_num)
theorem B2112227 : Blo 2111435 2112227 := bstep (se 1 (by rfl) ⟨1584170, by rfl⟩ : syracuseStep 2112227 = 3168341) B3168341
theorem B4572733 : Blo 2111435 4572733 := bbase (se 3 (by rfl) ⟨857387, by rfl⟩ : syracuseStep 4572733 = 1714775) (by norm_num)
theorem B6096977 : Blo 2111435 6096977 := bstep (se 2 (by rfl) ⟨2286366, by rfl⟩ : syracuseStep 6096977 = 4572733) B4572733
theorem B4064651 : Blo 2111435 4064651 := bstep (se 1 (by rfl) ⟨3048488, by rfl⟩ : syracuseStep 4064651 = 6096977) B6096977
theorem B2709767 : Blo 2111435 2709767 := bstep (se 1 (by rfl) ⟨2032325, by rfl⟩ : syracuseStep 2709767 = 4064651) B4064651
theorem B7226045 : Blo 2111435 7226045 := bstep (se 3 (by rfl) ⟨1354883, by rfl⟩ : syracuseStep 7226045 = 2709767) B2709767
theorem B4817363 : Blo 2111435 4817363 := bstep (se 1 (by rfl) ⟨3613022, by rfl⟩ : syracuseStep 4817363 = 7226045) B7226045
theorem B51385205 : Blo 2111435 51385205 := bstep (se 5 (by rfl) ⟨2408681, by rfl⟩ : syracuseStep 51385205 = 4817363) B4817363
theorem B34256803 : Blo 2111435 34256803 := bstep (se 1 (by rfl) ⟨25692602, by rfl⟩ : syracuseStep 34256803 = 51385205) B51385205
theorem B45675737 : Blo 2111435 45675737 := bstep (se 2 (by rfl) ⟨17128401, by rfl⟩ : syracuseStep 45675737 = 34256803) B34256803
theorem B30450491 : Blo 2111435 30450491 := bstep (se 1 (by rfl) ⟨22837868, by rfl⟩ : syracuseStep 30450491 = 45675737) B45675737
theorem B20300327 : Blo 2111435 20300327 := bstep (se 1 (by rfl) ⟨15225245, by rfl⟩ : syracuseStep 20300327 = 30450491) B30450491
theorem B13533551 : Blo 2111435 13533551 := bstep (se 1 (by rfl) ⟨10150163, by rfl⟩ : syracuseStep 13533551 = 20300327) B20300327
theorem B9022367 : Blo 2111435 9022367 := bstep (se 1 (by rfl) ⟨6766775, by rfl⟩ : syracuseStep 9022367 = 13533551) B13533551
theorem B6014911 : Blo 2111435 6014911 := bstep (se 1 (by rfl) ⟨4511183, by rfl⟩ : syracuseStep 6014911 = 9022367) B9022367
theorem B8019881 : Blo 2111435 8019881 := bstep (se 2 (by rfl) ⟨3007455, by rfl⟩ : syracuseStep 8019881 = 6014911) B6014911
theorem B5346587 : Blo 2111435 5346587 := bstep (se 1 (by rfl) ⟨4009940, by rfl⟩ : syracuseStep 5346587 = 8019881) B8019881
theorem B3564391 : Blo 2111435 3564391 := bstep (se 1 (by rfl) ⟨2673293, by rfl⟩ : syracuseStep 3564391 = 5346587) B5346587
theorem B4752521 : Blo 2111435 4752521 := bstep (se 2 (by rfl) ⟨1782195, by rfl⟩ : syracuseStep 4752521 = 3564391) B3564391
theorem B3168347 : Blo 2111435 3168347 := bstep (se 1 (by rfl) ⟨2376260, by rfl⟩ : syracuseStep 3168347 = 4752521) B4752521
theorem B2112231 : Blo 2111435 2112231 := bstep (se 1 (by rfl) ⟨1584173, by rfl⟩ : syracuseStep 2112231 = 3168347) B3168347
theorem B2376265 : Blo 2111435 2376265 := bbase (se 2 (by rfl) ⟨891099, by rfl⟩ : syracuseStep 2376265 = 1782199) (by norm_num)
theorem B3168353 : Blo 2111435 3168353 := bstep (se 2 (by rfl) ⟨1188132, by rfl⟩ : syracuseStep 3168353 = 2376265) B2376265
theorem B2112235 : Blo 2111435 2112235 := bstep (se 1 (by rfl) ⟨1584176, by rfl⟩ : syracuseStep 2112235 = 3168353) B3168353
theorem B10839109 : Blo 2111435 10839109 := bbase (se 4 (by rfl) ⟨1016166, by rfl⟩ : syracuseStep 10839109 = 2032333) (by norm_num)
theorem B14452145 : Blo 2111435 14452145 := bstep (se 2 (by rfl) ⟨5419554, by rfl⟩ : syracuseStep 14452145 = 10839109) B10839109
theorem B9634763 : Blo 2111435 9634763 := bstep (se 1 (by rfl) ⟨7226072, by rfl⟩ : syracuseStep 9634763 = 14452145) B14452145
theorem B6423175 : Blo 2111435 6423175 := bstep (se 1 (by rfl) ⟨4817381, by rfl⟩ : syracuseStep 6423175 = 9634763) B9634763
theorem B8564233 : Blo 2111435 8564233 := bstep (se 2 (by rfl) ⟨3211587, by rfl⟩ : syracuseStep 8564233 = 6423175) B6423175
theorem B11418977 : Blo 2111435 11418977 := bstep (se 2 (by rfl) ⟨4282116, by rfl⟩ : syracuseStep 11418977 = 8564233) B8564233
theorem B7612651 : Blo 2111435 7612651 := bstep (se 1 (by rfl) ⟨5709488, by rfl⟩ : syracuseStep 7612651 = 11418977) B11418977
theorem B10150201 : Blo 2111435 10150201 := bstep (se 2 (by rfl) ⟨3806325, by rfl⟩ : syracuseStep 10150201 = 7612651) B7612651
theorem B13533601 : Blo 2111435 13533601 := bstep (se 2 (by rfl) ⟨5075100, by rfl⟩ : syracuseStep 13533601 = 10150201) B10150201
theorem B18044801 : Blo 2111435 18044801 := bstep (se 2 (by rfl) ⟨6766800, by rfl⟩ : syracuseStep 18044801 = 13533601) B13533601
theorem B12029867 : Blo 2111435 12029867 := bstep (se 1 (by rfl) ⟨9022400, by rfl⟩ : syracuseStep 12029867 = 18044801) B18044801
theorem B8019911 : Blo 2111435 8019911 := bstep (se 1 (by rfl) ⟨6014933, by rfl⟩ : syracuseStep 8019911 = 12029867) B12029867
theorem B5346607 : Blo 2111435 5346607 := bstep (se 1 (by rfl) ⟨4009955, by rfl⟩ : syracuseStep 5346607 = 8019911) B8019911
theorem B7128809 : Blo 2111435 7128809 := bstep (se 2 (by rfl) ⟨2673303, by rfl⟩ : syracuseStep 7128809 = 5346607) B5346607
theorem B4752539 : Blo 2111435 4752539 := bstep (se 1 (by rfl) ⟨3564404, by rfl⟩ : syracuseStep 4752539 = 7128809) B7128809
theorem B3168359 : Blo 2111435 3168359 := bstep (se 1 (by rfl) ⟨2376269, by rfl⟩ : syracuseStep 3168359 = 4752539) B4752539
theorem B2112239 : Blo 2111435 2112239 := bstep (se 1 (by rfl) ⟨1584179, by rfl⟩ : syracuseStep 2112239 = 3168359) B3168359
theorem B3168365 : Blo 2111435 3168365 := bbase (se 3 (by rfl) ⟨594068, by rfl⟩ : syracuseStep 3168365 = 1188137) (by norm_num)
theorem B2112243 : Blo 2111435 2112243 := bstep (se 1 (by rfl) ⟨1584182, by rfl⟩ : syracuseStep 2112243 = 3168365) B3168365
theorem B4752557 : Blo 2111435 4752557 := bbase (se 3 (by rfl) ⟨891104, by rfl⟩ : syracuseStep 4752557 = 1782209) (by norm_num)
theorem B3168371 : Blo 2111435 3168371 := bstep (se 1 (by rfl) ⟨2376278, by rfl⟩ : syracuseStep 3168371 = 4752557) B4752557
theorem B2112247 : Blo 2111435 2112247 := bstep (se 1 (by rfl) ⟨1584185, by rfl⟩ : syracuseStep 2112247 = 3168371) B3168371
theorem B7226117 : Blo 2111435 7226117 := bbase (se 4 (by rfl) ⟨677448, by rfl⟩ : syracuseStep 7226117 = 1354897) (by norm_num)
theorem B4817411 : Blo 2111435 4817411 := bstep (se 1 (by rfl) ⟨3613058, by rfl⟩ : syracuseStep 4817411 = 7226117) B7226117
theorem B3211607 : Blo 2111435 3211607 := bstep (se 1 (by rfl) ⟨2408705, by rfl⟩ : syracuseStep 3211607 = 4817411) B4817411
theorem B8564285 : Blo 2111435 8564285 := bstep (se 3 (by rfl) ⟨1605803, by rfl⟩ : syracuseStep 8564285 = 3211607) B3211607
theorem B5709523 : Blo 2111435 5709523 := bstep (se 1 (by rfl) ⟨4282142, by rfl⟩ : syracuseStep 5709523 = 8564285) B8564285
theorem B7612697 : Blo 2111435 7612697 := bstep (se 2 (by rfl) ⟨2854761, by rfl⟩ : syracuseStep 7612697 = 5709523) B5709523
theorem B5075131 : Blo 2111435 5075131 := bstep (se 1 (by rfl) ⟨3806348, by rfl⟩ : syracuseStep 5075131 = 7612697) B7612697
theorem B6766841 : Blo 2111435 6766841 := bstep (se 2 (by rfl) ⟨2537565, by rfl⟩ : syracuseStep 6766841 = 5075131) B5075131
theorem B4511227 : Blo 2111435 4511227 := bstep (se 1 (by rfl) ⟨3383420, by rfl⟩ : syracuseStep 4511227 = 6766841) B6766841
theorem B6014969 : Blo 2111435 6014969 := bstep (se 2 (by rfl) ⟨2255613, by rfl⟩ : syracuseStep 6014969 = 4511227) B4511227
theorem B4009979 : Blo 2111435 4009979 := bstep (se 1 (by rfl) ⟨3007484, by rfl⟩ : syracuseStep 4009979 = 6014969) B6014969
theorem B2673319 : Blo 2111435 2673319 := bstep (se 1 (by rfl) ⟨2004989, by rfl⟩ : syracuseStep 2673319 = 4009979) B4009979
theorem B3564425 : Blo 2111435 3564425 := bstep (se 2 (by rfl) ⟨1336659, by rfl⟩ : syracuseStep 3564425 = 2673319) B2673319
theorem B2376283 : Blo 2111435 2376283 := bstep (se 1 (by rfl) ⟨1782212, by rfl⟩ : syracuseStep 2376283 = 3564425) B3564425
theorem B3168377 : Blo 2111435 3168377 := bstep (se 2 (by rfl) ⟨1188141, by rfl⟩ : syracuseStep 3168377 = 2376283) B2376283
theorem B2112251 : Blo 2111435 2112251 := bstep (se 1 (by rfl) ⟨1584188, by rfl⟩ : syracuseStep 2112251 = 3168377) B3168377
theorem B10150277 : Blo 2111435 10150277 := bbase (se 4 (by rfl) ⟨951588, by rfl⟩ : syracuseStep 10150277 = 1903177) (by norm_num)
theorem B27067405 : Blo 2111435 27067405 := bstep (se 3 (by rfl) ⟨5075138, by rfl⟩ : syracuseStep 27067405 = 10150277) B10150277
theorem B36089873 : Blo 2111435 36089873 := bstep (se 2 (by rfl) ⟨13533702, by rfl⟩ : syracuseStep 36089873 = 27067405) B27067405
theorem B24059915 : Blo 2111435 24059915 := bstep (se 1 (by rfl) ⟨18044936, by rfl⟩ : syracuseStep 24059915 = 36089873) B36089873
theorem B16039943 : Blo 2111435 16039943 := bstep (se 1 (by rfl) ⟨12029957, by rfl⟩ : syracuseStep 16039943 = 24059915) B24059915
theorem B10693295 : Blo 2111435 10693295 := bstep (se 1 (by rfl) ⟨8019971, by rfl⟩ : syracuseStep 10693295 = 16039943) B16039943
theorem B7128863 : Blo 2111435 7128863 := bstep (se 1 (by rfl) ⟨5346647, by rfl⟩ : syracuseStep 7128863 = 10693295) B10693295
theorem B4752575 : Blo 2111435 4752575 := bstep (se 1 (by rfl) ⟨3564431, by rfl⟩ : syracuseStep 4752575 = 7128863) B7128863
theorem B3168383 : Blo 2111435 3168383 := bstep (se 1 (by rfl) ⟨2376287, by rfl⟩ : syracuseStep 3168383 = 4752575) B4752575
theorem B2112255 : Blo 2111435 2112255 := bstep (se 1 (by rfl) ⟨1584191, by rfl⟩ : syracuseStep 2112255 = 3168383) B3168383
theorem B3168389 : Blo 2111435 3168389 := bbase (se 4 (by rfl) ⟨297036, by rfl⟩ : syracuseStep 3168389 = 594073) (by norm_num)
theorem B2112259 : Blo 2111435 2112259 := bstep (se 1 (by rfl) ⟨1584194, by rfl⟩ : syracuseStep 2112259 = 3168389) B3168389
theorem B3564445 : Blo 2111435 3564445 := bbase (se 3 (by rfl) ⟨668333, by rfl⟩ : syracuseStep 3564445 = 1336667) (by norm_num)
theorem B4752593 : Blo 2111435 4752593 := bstep (se 2 (by rfl) ⟨1782222, by rfl⟩ : syracuseStep 4752593 = 3564445) B3564445
theorem B3168395 : Blo 2111435 3168395 := bstep (se 1 (by rfl) ⟨2376296, by rfl⟩ : syracuseStep 3168395 = 4752593) B4752593
theorem B2112263 : Blo 2111435 2112263 := bstep (se 1 (by rfl) ⟨1584197, by rfl⟩ : syracuseStep 2112263 = 3168395) B3168395
theorem B2376301 : Blo 2111435 2376301 := bbase (se 3 (by rfl) ⟨445556, by rfl⟩ : syracuseStep 2376301 = 891113) (by norm_num)
theorem B3168401 : Blo 2111435 3168401 := bstep (se 2 (by rfl) ⟨1188150, by rfl⟩ : syracuseStep 3168401 = 2376301) B2376301
theorem B2112267 : Blo 2111435 2112267 := bstep (se 1 (by rfl) ⟨1584200, by rfl⟩ : syracuseStep 2112267 = 3168401) B3168401
theorem B7128917 : Blo 2111435 7128917 := bbase (se 9 (by rfl) ⟨20885, by rfl⟩ : syracuseStep 7128917 = 41771) (by norm_num)
theorem B4752611 : Blo 2111435 4752611 := bstep (se 1 (by rfl) ⟨3564458, by rfl⟩ : syracuseStep 4752611 = 7128917) B7128917
theorem B3168407 : Blo 2111435 3168407 := bstep (se 1 (by rfl) ⟨2376305, by rfl⟩ : syracuseStep 3168407 = 4752611) B4752611
theorem B2112271 : Blo 2111435 2112271 := bstep (se 1 (by rfl) ⟨1584203, by rfl⟩ : syracuseStep 2112271 = 3168407) B3168407
theorem B3168413 : Blo 2111435 3168413 := bbase (se 3 (by rfl) ⟨594077, by rfl⟩ : syracuseStep 3168413 = 1188155) (by norm_num)
theorem B2112275 : Blo 2111435 2112275 := bstep (se 1 (by rfl) ⟨1584206, by rfl⟩ : syracuseStep 2112275 = 3168413) B3168413
theorem B4752629 : Blo 2111435 4752629 := bbase (se 5 (by rfl) ⟨222779, by rfl⟩ : syracuseStep 4752629 = 445559) (by norm_num)
theorem B3168419 : Blo 2111435 3168419 := bstep (se 1 (by rfl) ⟨2376314, by rfl⟩ : syracuseStep 3168419 = 4752629) B4752629
theorem B2112279 : Blo 2111435 2112279 := bstep (se 1 (by rfl) ⟨1584209, by rfl⟩ : syracuseStep 2112279 = 3168419) B3168419
theorem B5866469 : Blo 2111435 5866469 := bbase (se 4 (by rfl) ⟨549981, by rfl⟩ : syracuseStep 5866469 = 1099963) (by norm_num)
theorem B3910979 : Blo 2111435 3910979 := bstep (se 1 (by rfl) ⟨2933234, by rfl⟩ : syracuseStep 3910979 = 5866469) B5866469
theorem B2607319 : Blo 2111435 2607319 := bstep (se 1 (by rfl) ⟨1955489, by rfl⟩ : syracuseStep 2607319 = 3910979) B3910979
theorem B13905701 : Blo 2111435 13905701 := bstep (se 4 (by rfl) ⟨1303659, by rfl⟩ : syracuseStep 13905701 = 2607319) B2607319
theorem B9270467 : Blo 2111435 9270467 := bstep (se 1 (by rfl) ⟨6952850, by rfl⟩ : syracuseStep 9270467 = 13905701) B13905701
theorem B6180311 : Blo 2111435 6180311 := bstep (se 1 (by rfl) ⟨4635233, by rfl⟩ : syracuseStep 6180311 = 9270467) B9270467
theorem B4120207 : Blo 2111435 4120207 := bstep (se 1 (by rfl) ⟨3090155, by rfl⟩ : syracuseStep 4120207 = 6180311) B6180311
theorem B21974437 : Blo 2111435 21974437 := bstep (se 4 (by rfl) ⟨2060103, by rfl⟩ : syracuseStep 21974437 = 4120207) B4120207
theorem B29299249 : Blo 2111435 29299249 := bstep (se 2 (by rfl) ⟨10987218, by rfl⟩ : syracuseStep 29299249 = 21974437) B21974437
theorem B39065665 : Blo 2111435 39065665 := bstep (se 2 (by rfl) ⟨14649624, by rfl⟩ : syracuseStep 39065665 = 29299249) B29299249
theorem B52087553 : Blo 2111435 52087553 := bstep (se 2 (by rfl) ⟨19532832, by rfl⟩ : syracuseStep 52087553 = 39065665) B39065665
theorem B34725035 : Blo 2111435 34725035 := bstep (se 1 (by rfl) ⟨26043776, by rfl⟩ : syracuseStep 34725035 = 52087553) B52087553
theorem B23150023 : Blo 2111435 23150023 := bstep (se 1 (by rfl) ⟨17362517, by rfl⟩ : syracuseStep 23150023 = 34725035) B34725035
theorem B123466789 : Blo 2111435 123466789 := bstep (se 4 (by rfl) ⟨11575011, by rfl⟩ : syracuseStep 123466789 = 23150023) B23150023
theorem B164622385 : Blo 2111435 164622385 := bstep (se 2 (by rfl) ⟨61733394, by rfl⟩ : syracuseStep 164622385 = 123466789) B123466789
theorem B219496513 : Blo 2111435 219496513 := bstep (se 2 (by rfl) ⟨82311192, by rfl⟩ : syracuseStep 219496513 = 164622385) B164622385
theorem B292662017 : Blo 2111435 292662017 := bstep (se 2 (by rfl) ⟨109748256, by rfl⟩ : syracuseStep 292662017 = 219496513) B219496513
theorem B195108011 : Blo 2111435 195108011 := bstep (se 1 (by rfl) ⟨146331008, by rfl⟩ : syracuseStep 195108011 = 292662017) B292662017
theorem B130072007 : Blo 2111435 130072007 := bstep (se 1 (by rfl) ⟨97554005, by rfl⟩ : syracuseStep 130072007 = 195108011) B195108011
theorem B86714671 : Blo 2111435 86714671 := bstep (se 1 (by rfl) ⟨65036003, by rfl⟩ : syracuseStep 86714671 = 130072007) B130072007
theorem B115619561 : Blo 2111435 115619561 := bstep (se 2 (by rfl) ⟨43357335, by rfl⟩ : syracuseStep 115619561 = 86714671) B86714671
theorem B77079707 : Blo 2111435 77079707 := bstep (se 1 (by rfl) ⟨57809780, by rfl⟩ : syracuseStep 77079707 = 115619561) B115619561
theorem B51386471 : Blo 2111435 51386471 := bstep (se 1 (by rfl) ⟨38539853, by rfl⟩ : syracuseStep 51386471 = 77079707) B77079707
theorem B34257647 : Blo 2111435 34257647 := bstep (se 1 (by rfl) ⟨25693235, by rfl⟩ : syracuseStep 34257647 = 51386471) B51386471
theorem B22838431 : Blo 2111435 22838431 := bstep (se 1 (by rfl) ⟨17128823, by rfl⟩ : syracuseStep 22838431 = 34257647) B34257647
theorem B30451241 : Blo 2111435 30451241 := bstep (se 2 (by rfl) ⟨11419215, by rfl⟩ : syracuseStep 30451241 = 22838431) B22838431
theorem B20300827 : Blo 2111435 20300827 := bstep (se 1 (by rfl) ⟨15225620, by rfl⟩ : syracuseStep 20300827 = 30451241) B30451241
theorem B27067769 : Blo 2111435 27067769 := bstep (se 2 (by rfl) ⟨10150413, by rfl⟩ : syracuseStep 27067769 = 20300827) B20300827
theorem B18045179 : Blo 2111435 18045179 := bstep (se 1 (by rfl) ⟨13533884, by rfl⟩ : syracuseStep 18045179 = 27067769) B27067769
theorem B12030119 : Blo 2111435 12030119 := bstep (se 1 (by rfl) ⟨9022589, by rfl⟩ : syracuseStep 12030119 = 18045179) B18045179
theorem B8020079 : Blo 2111435 8020079 := bstep (se 1 (by rfl) ⟨6015059, by rfl⟩ : syracuseStep 8020079 = 12030119) B12030119
theorem B5346719 : Blo 2111435 5346719 := bstep (se 1 (by rfl) ⟨4010039, by rfl⟩ : syracuseStep 5346719 = 8020079) B8020079
theorem B3564479 : Blo 2111435 3564479 := bstep (se 1 (by rfl) ⟨2673359, by rfl⟩ : syracuseStep 3564479 = 5346719) B5346719
theorem B2376319 : Blo 2111435 2376319 := bstep (se 1 (by rfl) ⟨1782239, by rfl⟩ : syracuseStep 2376319 = 3564479) B3564479
theorem B3168425 : Blo 2111435 3168425 := bstep (se 2 (by rfl) ⟨1188159, by rfl⟩ : syracuseStep 3168425 = 2376319) B2376319
theorem B2112283 : Blo 2111435 2112283 := bstep (se 1 (by rfl) ⟨1584212, by rfl⟩ : syracuseStep 2112283 = 3168425) B3168425
theorem B3211661 : Blo 2111435 3211661 := bbase (se 3 (by rfl) ⟨602186, by rfl⟩ : syracuseStep 3211661 = 1204373) (by norm_num)
theorem B8564429 : Blo 2111435 8564429 := bstep (se 3 (by rfl) ⟨1605830, by rfl⟩ : syracuseStep 8564429 = 3211661) B3211661
theorem B5709619 : Blo 2111435 5709619 := bstep (se 1 (by rfl) ⟨4282214, by rfl⟩ : syracuseStep 5709619 = 8564429) B8564429
theorem B7612825 : Blo 2111435 7612825 := bstep (se 2 (by rfl) ⟨2854809, by rfl⟩ : syracuseStep 7612825 = 5709619) B5709619
theorem B10150433 : Blo 2111435 10150433 := bstep (se 2 (by rfl) ⟨3806412, by rfl⟩ : syracuseStep 10150433 = 7612825) B7612825
theorem B6766955 : Blo 2111435 6766955 := bstep (se 1 (by rfl) ⟨5075216, by rfl⟩ : syracuseStep 6766955 = 10150433) B10150433
theorem B4511303 : Blo 2111435 4511303 := bstep (se 1 (by rfl) ⟨3383477, by rfl⟩ : syracuseStep 4511303 = 6766955) B6766955
theorem B3007535 : Blo 2111435 3007535 := bstep (se 1 (by rfl) ⟨2255651, by rfl⟩ : syracuseStep 3007535 = 4511303) B4511303
theorem B8020093 : Blo 2111435 8020093 := bstep (se 3 (by rfl) ⟨1503767, by rfl⟩ : syracuseStep 8020093 = 3007535) B3007535
theorem B10693457 : Blo 2111435 10693457 := bstep (se 2 (by rfl) ⟨4010046, by rfl⟩ : syracuseStep 10693457 = 8020093) B8020093
theorem B7128971 : Blo 2111435 7128971 := bstep (se 1 (by rfl) ⟨5346728, by rfl⟩ : syracuseStep 7128971 = 10693457) B10693457
theorem B4752647 : Blo 2111435 4752647 := bstep (se 1 (by rfl) ⟨3564485, by rfl⟩ : syracuseStep 4752647 = 7128971) B7128971
theorem B3168431 : Blo 2111435 3168431 := bstep (se 1 (by rfl) ⟨2376323, by rfl⟩ : syracuseStep 3168431 = 4752647) B4752647
theorem B2112287 : Blo 2111435 2112287 := bstep (se 1 (by rfl) ⟨1584215, by rfl⟩ : syracuseStep 2112287 = 3168431) B3168431
theorem B3168437 : Blo 2111435 3168437 := bbase (se 5 (by rfl) ⟨148520, by rfl⟩ : syracuseStep 3168437 = 297041) (by norm_num)
theorem B2112291 : Blo 2111435 2112291 := bstep (se 1 (by rfl) ⟨1584218, by rfl⟩ : syracuseStep 2112291 = 3168437) B3168437
theorem B5346749 : Blo 2111435 5346749 := bbase (se 3 (by rfl) ⟨1002515, by rfl⟩ : syracuseStep 5346749 = 2005031) (by norm_num)
theorem B3564499 : Blo 2111435 3564499 := bstep (se 1 (by rfl) ⟨2673374, by rfl⟩ : syracuseStep 3564499 = 5346749) B5346749
theorem B4752665 : Blo 2111435 4752665 := bstep (se 2 (by rfl) ⟨1782249, by rfl⟩ : syracuseStep 4752665 = 3564499) B3564499
theorem B3168443 : Blo 2111435 3168443 := bstep (se 1 (by rfl) ⟨2376332, by rfl⟩ : syracuseStep 3168443 = 4752665) B4752665
theorem B2112295 : Blo 2111435 2112295 := bstep (se 1 (by rfl) ⟨1584221, by rfl⟩ : syracuseStep 2112295 = 3168443) B3168443
theorem B2376337 : Blo 2111435 2376337 := bbase (se 2 (by rfl) ⟨891126, by rfl⟩ : syracuseStep 2376337 = 1782253) (by norm_num)
theorem B3168449 : Blo 2111435 3168449 := bstep (se 2 (by rfl) ⟨1188168, by rfl⟩ : syracuseStep 3168449 = 2376337) B2376337
theorem B2112299 : Blo 2111435 2112299 := bstep (se 1 (by rfl) ⟨1584224, by rfl⟩ : syracuseStep 2112299 = 3168449) B3168449
theorem B4010077 : Blo 2111435 4010077 := bbase (se 3 (by rfl) ⟨751889, by rfl⟩ : syracuseStep 4010077 = 1503779) (by norm_num)
theorem B5346769 : Blo 2111435 5346769 := bstep (se 2 (by rfl) ⟨2005038, by rfl⟩ : syracuseStep 5346769 = 4010077) B4010077
theorem B7129025 : Blo 2111435 7129025 := bstep (se 2 (by rfl) ⟨2673384, by rfl⟩ : syracuseStep 7129025 = 5346769) B5346769
theorem B4752683 : Blo 2111435 4752683 := bstep (se 1 (by rfl) ⟨3564512, by rfl⟩ : syracuseStep 4752683 = 7129025) B7129025
theorem B3168455 : Blo 2111435 3168455 := bstep (se 1 (by rfl) ⟨2376341, by rfl⟩ : syracuseStep 3168455 = 4752683) B4752683
theorem B2112303 : Blo 2111435 2112303 := bstep (se 1 (by rfl) ⟨1584227, by rfl⟩ : syracuseStep 2112303 = 3168455) B3168455
theorem B3168461 : Blo 2111435 3168461 := bbase (se 3 (by rfl) ⟨594086, by rfl⟩ : syracuseStep 3168461 = 1188173) (by norm_num)
theorem B2112307 : Blo 2111435 2112307 := bstep (se 1 (by rfl) ⟨1584230, by rfl⟩ : syracuseStep 2112307 = 3168461) B3168461
theorem B4752701 : Blo 2111435 4752701 := bbase (se 3 (by rfl) ⟨891131, by rfl⟩ : syracuseStep 4752701 = 1782263) (by norm_num)
theorem B3168467 : Blo 2111435 3168467 := bstep (se 1 (by rfl) ⟨2376350, by rfl⟩ : syracuseStep 3168467 = 4752701) B4752701
theorem B2112311 : Blo 2111435 2112311 := bstep (se 1 (by rfl) ⟨1584233, by rfl⟩ : syracuseStep 2112311 = 3168467) B3168467
theorem B3564533 : Blo 2111435 3564533 := bbase (se 5 (by rfl) ⟨167087, by rfl⟩ : syracuseStep 3564533 = 334175) (by norm_num)
theorem B2376355 : Blo 2111435 2376355 := bstep (se 1 (by rfl) ⟨1782266, by rfl⟩ : syracuseStep 2376355 = 3564533) B3564533
theorem B3168473 : Blo 2111435 3168473 := bstep (se 2 (by rfl) ⟨1188177, by rfl⟩ : syracuseStep 3168473 = 2376355) B2376355
theorem B2112315 : Blo 2111435 2112315 := bstep (se 1 (by rfl) ⟨1584236, by rfl⟩ : syracuseStep 2112315 = 3168473) B3168473
theorem B5075293 : Blo 2111435 5075293 := bbase (se 3 (by rfl) ⟨951617, by rfl⟩ : syracuseStep 5075293 = 1903235) (by norm_num)
theorem B6767057 : Blo 2111435 6767057 := bstep (se 2 (by rfl) ⟨2537646, by rfl⟩ : syracuseStep 6767057 = 5075293) B5075293
theorem B4511371 : Blo 2111435 4511371 := bstep (se 1 (by rfl) ⟨3383528, by rfl⟩ : syracuseStep 4511371 = 6767057) B6767057
theorem B6015161 : Blo 2111435 6015161 := bstep (se 2 (by rfl) ⟨2255685, by rfl⟩ : syracuseStep 6015161 = 4511371) B4511371
theorem B16040429 : Blo 2111435 16040429 := bstep (se 3 (by rfl) ⟨3007580, by rfl⟩ : syracuseStep 16040429 = 6015161) B6015161
theorem B10693619 : Blo 2111435 10693619 := bstep (se 1 (by rfl) ⟨8020214, by rfl⟩ : syracuseStep 10693619 = 16040429) B16040429
theorem B7129079 : Blo 2111435 7129079 := bstep (se 1 (by rfl) ⟨5346809, by rfl⟩ : syracuseStep 7129079 = 10693619) B10693619
theorem B4752719 : Blo 2111435 4752719 := bstep (se 1 (by rfl) ⟨3564539, by rfl⟩ : syracuseStep 4752719 = 7129079) B7129079
theorem B3168479 : Blo 2111435 3168479 := bstep (se 1 (by rfl) ⟨2376359, by rfl⟩ : syracuseStep 3168479 = 4752719) B4752719
theorem B2112319 : Blo 2111435 2112319 := bstep (se 1 (by rfl) ⟨1584239, by rfl⟩ : syracuseStep 2112319 = 3168479) B3168479
theorem B3168485 : Blo 2111435 3168485 := bbase (se 4 (by rfl) ⟨297045, by rfl⟩ : syracuseStep 3168485 = 594091) (by norm_num)
theorem B2112323 : Blo 2111435 2112323 := bstep (se 1 (by rfl) ⟨1584242, by rfl⟩ : syracuseStep 2112323 = 3168485) B3168485
theorem B4511389 : Blo 2111435 4511389 := bbase (se 3 (by rfl) ⟨845885, by rfl⟩ : syracuseStep 4511389 = 1691771) (by norm_num)
theorem B6015185 : Blo 2111435 6015185 := bstep (se 2 (by rfl) ⟨2255694, by rfl⟩ : syracuseStep 6015185 = 4511389) B4511389
theorem B4010123 : Blo 2111435 4010123 := bstep (se 1 (by rfl) ⟨3007592, by rfl⟩ : syracuseStep 4010123 = 6015185) B6015185
theorem B2673415 : Blo 2111435 2673415 := bstep (se 1 (by rfl) ⟨2005061, by rfl⟩ : syracuseStep 2673415 = 4010123) B4010123
theorem B3564553 : Blo 2111435 3564553 := bstep (se 2 (by rfl) ⟨1336707, by rfl⟩ : syracuseStep 3564553 = 2673415) B2673415
theorem B4752737 : Blo 2111435 4752737 := bstep (se 2 (by rfl) ⟨1782276, by rfl⟩ : syracuseStep 4752737 = 3564553) B3564553
theorem B3168491 : Blo 2111435 3168491 := bstep (se 1 (by rfl) ⟨2376368, by rfl⟩ : syracuseStep 3168491 = 4752737) B4752737
theorem B2112327 : Blo 2111435 2112327 := bstep (se 1 (by rfl) ⟨1584245, by rfl⟩ : syracuseStep 2112327 = 3168491) B3168491
theorem B2376373 : Blo 2111435 2376373 := bbase (se 5 (by rfl) ⟨111392, by rfl⟩ : syracuseStep 2376373 = 222785) (by norm_num)
theorem B3168497 : Blo 2111435 3168497 := bstep (se 2 (by rfl) ⟨1188186, by rfl⟩ : syracuseStep 3168497 = 2376373) B2376373
theorem B2112331 : Blo 2111435 2112331 := bstep (se 1 (by rfl) ⟨1584248, by rfl⟩ : syracuseStep 2112331 = 3168497) B3168497
theorem B2673425 : Blo 2111435 2673425 := bbase (se 2 (by rfl) ⟨1002534, by rfl⟩ : syracuseStep 2673425 = 2005069) (by norm_num)
theorem B7129133 : Blo 2111435 7129133 := bstep (se 3 (by rfl) ⟨1336712, by rfl⟩ : syracuseStep 7129133 = 2673425) B2673425
theorem B4752755 : Blo 2111435 4752755 := bstep (se 1 (by rfl) ⟨3564566, by rfl⟩ : syracuseStep 4752755 = 7129133) B7129133
theorem B3168503 : Blo 2111435 3168503 := bstep (se 1 (by rfl) ⟨2376377, by rfl⟩ : syracuseStep 3168503 = 4752755) B4752755
theorem B2112335 : Blo 2111435 2112335 := bstep (se 1 (by rfl) ⟨1584251, by rfl⟩ : syracuseStep 2112335 = 3168503) B3168503
theorem B3168509 : Blo 2111435 3168509 := bbase (se 3 (by rfl) ⟨594095, by rfl⟩ : syracuseStep 3168509 = 1188191) (by norm_num)
theorem B2112339 : Blo 2111435 2112339 := bstep (se 1 (by rfl) ⟨1584254, by rfl⟩ : syracuseStep 2112339 = 3168509) B3168509
theorem B4752773 : Blo 2111435 4752773 := bbase (se 4 (by rfl) ⟨445572, by rfl⟩ : syracuseStep 4752773 = 891145) (by norm_num)
theorem B3168515 : Blo 2111435 3168515 := bstep (se 1 (by rfl) ⟨2376386, by rfl⟩ : syracuseStep 3168515 = 4752773) B4752773
theorem B2112343 : Blo 2111435 2112343 := bstep (se 1 (by rfl) ⟨1584257, by rfl⟩ : syracuseStep 2112343 = 3168515) B3168515
theorem B3007621 : Blo 2111435 3007621 := bbase (se 4 (by rfl) ⟨281964, by rfl⟩ : syracuseStep 3007621 = 563929) (by norm_num)
theorem B4010161 : Blo 2111435 4010161 := bstep (se 2 (by rfl) ⟨1503810, by rfl⟩ : syracuseStep 4010161 = 3007621) B3007621
theorem B5346881 : Blo 2111435 5346881 := bstep (se 2 (by rfl) ⟨2005080, by rfl⟩ : syracuseStep 5346881 = 4010161) B4010161
theorem B3564587 : Blo 2111435 3564587 := bstep (se 1 (by rfl) ⟨2673440, by rfl⟩ : syracuseStep 3564587 = 5346881) B5346881
theorem B2376391 : Blo 2111435 2376391 := bstep (se 1 (by rfl) ⟨1782293, by rfl⟩ : syracuseStep 2376391 = 3564587) B3564587
theorem B3168521 : Blo 2111435 3168521 := bstep (se 2 (by rfl) ⟨1188195, by rfl⟩ : syracuseStep 3168521 = 2376391) B2376391
theorem B2112347 : Blo 2111435 2112347 := bstep (se 1 (by rfl) ⟨1584260, by rfl⟩ : syracuseStep 2112347 = 3168521) B3168521
theorem B10693781 : Blo 2111435 10693781 := bbase (se 6 (by rfl) ⟨250635, by rfl⟩ : syracuseStep 10693781 = 501271) (by norm_num)
theorem B7129187 : Blo 2111435 7129187 := bstep (se 1 (by rfl) ⟨5346890, by rfl⟩ : syracuseStep 7129187 = 10693781) B10693781
theorem B4752791 : Blo 2111435 4752791 := bstep (se 1 (by rfl) ⟨3564593, by rfl⟩ : syracuseStep 4752791 = 7129187) B7129187
theorem B3168527 : Blo 2111435 3168527 := bstep (se 1 (by rfl) ⟨2376395, by rfl⟩ : syracuseStep 3168527 = 4752791) B4752791
theorem B2112351 : Blo 2111435 2112351 := bstep (se 1 (by rfl) ⟨1584263, by rfl⟩ : syracuseStep 2112351 = 3168527) B3168527
theorem B3168533 : Blo 2111435 3168533 := bbase (se 6 (by rfl) ⟨74262, by rfl⟩ : syracuseStep 3168533 = 148525) (by norm_num)
theorem B2112355 : Blo 2111435 2112355 := bstep (se 1 (by rfl) ⟨1584266, by rfl⟩ : syracuseStep 2112355 = 3168533) B3168533
theorem B5075389 : Blo 2111435 5075389 := bbase (se 3 (by rfl) ⟨951635, by rfl⟩ : syracuseStep 5075389 = 1903271) (by norm_num)
theorem B27068741 : Blo 2111435 27068741 := bstep (se 4 (by rfl) ⟨2537694, by rfl⟩ : syracuseStep 27068741 = 5075389) B5075389
theorem B18045827 : Blo 2111435 18045827 := bstep (se 1 (by rfl) ⟨13534370, by rfl⟩ : syracuseStep 18045827 = 27068741) B27068741
theorem B12030551 : Blo 2111435 12030551 := bstep (se 1 (by rfl) ⟨9022913, by rfl⟩ : syracuseStep 12030551 = 18045827) B18045827
theorem B8020367 : Blo 2111435 8020367 := bstep (se 1 (by rfl) ⟨6015275, by rfl⟩ : syracuseStep 8020367 = 12030551) B12030551
theorem B5346911 : Blo 2111435 5346911 := bstep (se 1 (by rfl) ⟨4010183, by rfl⟩ : syracuseStep 5346911 = 8020367) B8020367
theorem B3564607 : Blo 2111435 3564607 := bstep (se 1 (by rfl) ⟨2673455, by rfl⟩ : syracuseStep 3564607 = 5346911) B5346911
theorem B4752809 : Blo 2111435 4752809 := bstep (se 2 (by rfl) ⟨1782303, by rfl⟩ : syracuseStep 4752809 = 3564607) B3564607
theorem B3168539 : Blo 2111435 3168539 := bstep (se 1 (by rfl) ⟨2376404, by rfl⟩ : syracuseStep 3168539 = 4752809) B4752809
theorem B2112359 : Blo 2111435 2112359 := bstep (se 1 (by rfl) ⟨1584269, by rfl⟩ : syracuseStep 2112359 = 3168539) B3168539
theorem B2376409 : Blo 2111435 2376409 := bbase (se 2 (by rfl) ⟨891153, by rfl⟩ : syracuseStep 2376409 = 1782307) (by norm_num)
theorem B3168545 : Blo 2111435 3168545 := bstep (se 2 (by rfl) ⟨1188204, by rfl⟩ : syracuseStep 3168545 = 2376409) B2376409
theorem B2112363 : Blo 2111435 2112363 := bstep (se 1 (by rfl) ⟨1584272, by rfl⟩ : syracuseStep 2112363 = 3168545) B3168545
theorem B2255737 : Blo 2111435 2255737 := bbase (se 2 (by rfl) ⟨845901, by rfl⟩ : syracuseStep 2255737 = 1691803) (by norm_num)
theorem B3007649 : Blo 2111435 3007649 := bstep (se 2 (by rfl) ⟨1127868, by rfl⟩ : syracuseStep 3007649 = 2255737) B2255737
theorem B8020397 : Blo 2111435 8020397 := bstep (se 3 (by rfl) ⟨1503824, by rfl⟩ : syracuseStep 8020397 = 3007649) B3007649
theorem B5346931 : Blo 2111435 5346931 := bstep (se 1 (by rfl) ⟨4010198, by rfl⟩ : syracuseStep 5346931 = 8020397) B8020397
theorem B7129241 : Blo 2111435 7129241 := bstep (se 2 (by rfl) ⟨2673465, by rfl⟩ : syracuseStep 7129241 = 5346931) B5346931
theorem B4752827 : Blo 2111435 4752827 := bstep (se 1 (by rfl) ⟨3564620, by rfl⟩ : syracuseStep 4752827 = 7129241) B7129241
theorem B3168551 : Blo 2111435 3168551 := bstep (se 1 (by rfl) ⟨2376413, by rfl⟩ : syracuseStep 3168551 = 4752827) B4752827
theorem B2112367 : Blo 2111435 2112367 := bstep (se 1 (by rfl) ⟨1584275, by rfl⟩ : syracuseStep 2112367 = 3168551) B3168551
theorem B3168557 : Blo 2111435 3168557 := bbase (se 3 (by rfl) ⟨594104, by rfl⟩ : syracuseStep 3168557 = 1188209) (by norm_num)
theorem B2112371 : Blo 2111435 2112371 := bstep (se 1 (by rfl) ⟨1584278, by rfl⟩ : syracuseStep 2112371 = 3168557) B3168557
theorem B4752845 : Blo 2111435 4752845 := bbase (se 3 (by rfl) ⟨891158, by rfl⟩ : syracuseStep 4752845 = 1782317) (by norm_num)
theorem B3168563 : Blo 2111435 3168563 := bstep (se 1 (by rfl) ⟨2376422, by rfl⟩ : syracuseStep 3168563 = 4752845) B4752845
theorem B2112375 : Blo 2111435 2112375 := bstep (se 1 (by rfl) ⟨1584281, by rfl⟩ : syracuseStep 2112375 = 3168563) B3168563
theorem B2673481 : Blo 2111435 2673481 := bbase (se 2 (by rfl) ⟨1002555, by rfl⟩ : syracuseStep 2673481 = 2005111) (by norm_num)
theorem B3564641 : Blo 2111435 3564641 := bstep (se 2 (by rfl) ⟨1336740, by rfl⟩ : syracuseStep 3564641 = 2673481) B2673481
theorem B2376427 : Blo 2111435 2376427 := bstep (se 1 (by rfl) ⟨1782320, by rfl⟩ : syracuseStep 2376427 = 3564641) B3564641
theorem B3168569 : Blo 2111435 3168569 := bstep (se 2 (by rfl) ⟨1188213, by rfl⟩ : syracuseStep 3168569 = 2376427) B2376427
theorem B2112379 : Blo 2111435 2112379 := bstep (se 1 (by rfl) ⟨1584284, by rfl⟩ : syracuseStep 2112379 = 3168569) B3168569
theorem B22839509 : Blo 2111435 22839509 := bbase (se 7 (by rfl) ⟨267650, by rfl⟩ : syracuseStep 22839509 = 535301) (by norm_num)
theorem B15226339 : Blo 2111435 15226339 := bstep (se 1 (by rfl) ⟨11419754, by rfl⟩ : syracuseStep 15226339 = 22839509) B22839509
theorem B20301785 : Blo 2111435 20301785 := bstep (se 2 (by rfl) ⟨7613169, by rfl⟩ : syracuseStep 20301785 = 15226339) B15226339
theorem B13534523 : Blo 2111435 13534523 := bstep (se 1 (by rfl) ⟨10150892, by rfl⟩ : syracuseStep 13534523 = 20301785) B20301785
theorem B9023015 : Blo 2111435 9023015 := bstep (se 1 (by rfl) ⟨6767261, by rfl⟩ : syracuseStep 9023015 = 13534523) B13534523
theorem B24061373 : Blo 2111435 24061373 := bstep (se 3 (by rfl) ⟨4511507, by rfl⟩ : syracuseStep 24061373 = 9023015) B9023015
theorem B16040915 : Blo 2111435 16040915 := bstep (se 1 (by rfl) ⟨12030686, by rfl⟩ : syracuseStep 16040915 = 24061373) B24061373
theorem B10693943 : Blo 2111435 10693943 := bstep (se 1 (by rfl) ⟨8020457, by rfl⟩ : syracuseStep 10693943 = 16040915) B16040915
theorem B7129295 : Blo 2111435 7129295 := bstep (se 1 (by rfl) ⟨5346971, by rfl⟩ : syracuseStep 7129295 = 10693943) B10693943
theorem B4752863 : Blo 2111435 4752863 := bstep (se 1 (by rfl) ⟨3564647, by rfl⟩ : syracuseStep 4752863 = 7129295) B7129295
theorem B3168575 : Blo 2111435 3168575 := bstep (se 1 (by rfl) ⟨2376431, by rfl⟩ : syracuseStep 3168575 = 4752863) B4752863
theorem B2112383 : Blo 2111435 2112383 := bstep (se 1 (by rfl) ⟨1584287, by rfl⟩ : syracuseStep 2112383 = 3168575) B3168575
theorem B3168581 : Blo 2111435 3168581 := bbase (se 4 (by rfl) ⟨297054, by rfl⟩ : syracuseStep 3168581 = 594109) (by norm_num)
theorem B2112387 : Blo 2111435 2112387 := bstep (se 1 (by rfl) ⟨1584290, by rfl⟩ : syracuseStep 2112387 = 3168581) B3168581
theorem B3564661 : Blo 2111435 3564661 := bbase (se 5 (by rfl) ⟨167093, by rfl⟩ : syracuseStep 3564661 = 334187) (by norm_num)
theorem B4752881 : Blo 2111435 4752881 := bstep (se 2 (by rfl) ⟨1782330, by rfl⟩ : syracuseStep 4752881 = 3564661) B3564661
theorem B3168587 : Blo 2111435 3168587 := bstep (se 1 (by rfl) ⟨2376440, by rfl⟩ : syracuseStep 3168587 = 4752881) B4752881
theorem B2112391 : Blo 2111435 2112391 := bstep (se 1 (by rfl) ⟨1584293, by rfl⟩ : syracuseStep 2112391 = 3168587) B3168587
theorem B2376445 : Blo 2111435 2376445 := bbase (se 3 (by rfl) ⟨445583, by rfl⟩ : syracuseStep 2376445 = 891167) (by norm_num)
theorem B3168593 : Blo 2111435 3168593 := bstep (se 2 (by rfl) ⟨1188222, by rfl⟩ : syracuseStep 3168593 = 2376445) B2376445
theorem B2112395 : Blo 2111435 2112395 := bstep (se 1 (by rfl) ⟨1584296, by rfl⟩ : syracuseStep 2112395 = 3168593) B3168593
theorem B7129349 : Blo 2111435 7129349 := bbase (se 4 (by rfl) ⟨668376, by rfl⟩ : syracuseStep 7129349 = 1336753) (by norm_num)
theorem B4752899 : Blo 2111435 4752899 := bstep (se 1 (by rfl) ⟨3564674, by rfl⟩ : syracuseStep 4752899 = 7129349) B7129349
theorem B3168599 : Blo 2111435 3168599 := bstep (se 1 (by rfl) ⟨2376449, by rfl⟩ : syracuseStep 3168599 = 4752899) B4752899
theorem B2112399 : Blo 2111435 2112399 := bstep (se 1 (by rfl) ⟨1584299, by rfl⟩ : syracuseStep 2112399 = 3168599) B3168599
theorem B3168605 : Blo 2111435 3168605 := bbase (se 3 (by rfl) ⟨594113, by rfl⟩ : syracuseStep 3168605 = 1188227) (by norm_num)
theorem B2112403 : Blo 2111435 2112403 := bstep (se 1 (by rfl) ⟨1584302, by rfl⟩ : syracuseStep 2112403 = 3168605) B3168605
theorem B4752917 : Blo 2111435 4752917 := bbase (se 6 (by rfl) ⟨111396, by rfl⟩ : syracuseStep 4752917 = 222793) (by norm_num)
theorem B3168611 : Blo 2111435 3168611 := bstep (se 1 (by rfl) ⟨2376458, by rfl⟩ : syracuseStep 3168611 = 4752917) B4752917
theorem B2112407 : Blo 2111435 2112407 := bstep (se 1 (by rfl) ⟨1584305, by rfl⟩ : syracuseStep 2112407 = 3168611) B3168611
theorem B8020565 : Blo 2111435 8020565 := bbase (se 8 (by rfl) ⟨46995, by rfl⟩ : syracuseStep 8020565 = 93991) (by norm_num)
theorem B5347043 : Blo 2111435 5347043 := bstep (se 1 (by rfl) ⟨4010282, by rfl⟩ : syracuseStep 5347043 = 8020565) B8020565
theorem B3564695 : Blo 2111435 3564695 := bstep (se 1 (by rfl) ⟨2673521, by rfl⟩ : syracuseStep 3564695 = 5347043) B5347043
theorem B2376463 : Blo 2111435 2376463 := bstep (se 1 (by rfl) ⟨1782347, by rfl⟩ : syracuseStep 2376463 = 3564695) B3564695
theorem B3168617 : Blo 2111435 3168617 := bstep (se 2 (by rfl) ⟨1188231, by rfl⟩ : syracuseStep 3168617 = 2376463) B2376463
theorem B2112411 : Blo 2111435 2112411 := bstep (se 1 (by rfl) ⟨1584308, by rfl⟩ : syracuseStep 2112411 = 3168617) B3168617
theorem B12030869 : Blo 2111435 12030869 := bbase (se 6 (by rfl) ⟨281973, by rfl⟩ : syracuseStep 12030869 = 563947) (by norm_num)
theorem B8020579 : Blo 2111435 8020579 := bstep (se 1 (by rfl) ⟨6015434, by rfl⟩ : syracuseStep 8020579 = 12030869) B12030869
theorem B10694105 : Blo 2111435 10694105 := bstep (se 2 (by rfl) ⟨4010289, by rfl⟩ : syracuseStep 10694105 = 8020579) B8020579
theorem B7129403 : Blo 2111435 7129403 := bstep (se 1 (by rfl) ⟨5347052, by rfl⟩ : syracuseStep 7129403 = 10694105) B10694105
theorem B4752935 : Blo 2111435 4752935 := bstep (se 1 (by rfl) ⟨3564701, by rfl⟩ : syracuseStep 4752935 = 7129403) B7129403
theorem B3168623 : Blo 2111435 3168623 := bstep (se 1 (by rfl) ⟨2376467, by rfl⟩ : syracuseStep 3168623 = 4752935) B4752935
theorem B2112415 : Blo 2111435 2112415 := bstep (se 1 (by rfl) ⟨1584311, by rfl⟩ : syracuseStep 2112415 = 3168623) B3168623
theorem B3168629 : Blo 2111435 3168629 := bbase (se 5 (by rfl) ⟨148529, by rfl⟩ : syracuseStep 3168629 = 297059) (by norm_num)
theorem B2112419 : Blo 2111435 2112419 := bstep (se 1 (by rfl) ⟨1584314, by rfl⟩ : syracuseStep 2112419 = 3168629) B3168629
theorem B2255797 : Blo 2111435 2255797 := bbase (se 5 (by rfl) ⟨105740, by rfl⟩ : syracuseStep 2255797 = 211481) (by norm_num)
theorem B3007729 : Blo 2111435 3007729 := bstep (se 2 (by rfl) ⟨1127898, by rfl⟩ : syracuseStep 3007729 = 2255797) B2255797
theorem B4010305 : Blo 2111435 4010305 := bstep (se 2 (by rfl) ⟨1503864, by rfl⟩ : syracuseStep 4010305 = 3007729) B3007729
theorem B5347073 : Blo 2111435 5347073 := bstep (se 2 (by rfl) ⟨2005152, by rfl⟩ : syracuseStep 5347073 = 4010305) B4010305
theorem B3564715 : Blo 2111435 3564715 := bstep (se 1 (by rfl) ⟨2673536, by rfl⟩ : syracuseStep 3564715 = 5347073) B5347073
theorem B4752953 : Blo 2111435 4752953 := bstep (se 2 (by rfl) ⟨1782357, by rfl⟩ : syracuseStep 4752953 = 3564715) B3564715
theorem B3168635 : Blo 2111435 3168635 := bstep (se 1 (by rfl) ⟨2376476, by rfl⟩ : syracuseStep 3168635 = 4752953) B4752953
theorem B2112423 : Blo 2111435 2112423 := bstep (se 1 (by rfl) ⟨1584317, by rfl⟩ : syracuseStep 2112423 = 3168635) B3168635
theorem B2376481 : Blo 2111435 2376481 := bbase (se 2 (by rfl) ⟨891180, by rfl⟩ : syracuseStep 2376481 = 1782361) (by norm_num)
theorem B3168641 : Blo 2111435 3168641 := bstep (se 2 (by rfl) ⟨1188240, by rfl⟩ : syracuseStep 3168641 = 2376481) B2376481
theorem B2112427 : Blo 2111435 2112427 := bstep (se 1 (by rfl) ⟨1584320, by rfl⟩ : syracuseStep 2112427 = 3168641) B3168641
theorem B5347093 : Blo 2111435 5347093 := bbase (se 6 (by rfl) ⟨125322, by rfl⟩ : syracuseStep 5347093 = 250645) (by norm_num)
theorem B7129457 : Blo 2111435 7129457 := bstep (se 2 (by rfl) ⟨2673546, by rfl⟩ : syracuseStep 7129457 = 5347093) B5347093
theorem B4752971 : Blo 2111435 4752971 := bstep (se 1 (by rfl) ⟨3564728, by rfl⟩ : syracuseStep 4752971 = 7129457) B7129457
theorem B3168647 : Blo 2111435 3168647 := bstep (se 1 (by rfl) ⟨2376485, by rfl⟩ : syracuseStep 3168647 = 4752971) B4752971
theorem B2112431 : Blo 2111435 2112431 := bstep (se 1 (by rfl) ⟨1584323, by rfl⟩ : syracuseStep 2112431 = 3168647) B3168647
theorem B3168653 : Blo 2111435 3168653 := bbase (se 3 (by rfl) ⟨594122, by rfl⟩ : syracuseStep 3168653 = 1188245) (by norm_num)
theorem B2112435 : Blo 2111435 2112435 := bstep (se 1 (by rfl) ⟨1584326, by rfl⟩ : syracuseStep 2112435 = 3168653) B3168653
theorem B4752989 : Blo 2111435 4752989 := bbase (se 3 (by rfl) ⟨891185, by rfl⟩ : syracuseStep 4752989 = 1782371) (by norm_num)
theorem B3168659 : Blo 2111435 3168659 := bstep (se 1 (by rfl) ⟨2376494, by rfl⟩ : syracuseStep 3168659 = 4752989) B4752989
theorem B2112439 : Blo 2111435 2112439 := bstep (se 1 (by rfl) ⟨1584329, by rfl⟩ : syracuseStep 2112439 = 3168659) B3168659
theorem B3564749 : Blo 2111435 3564749 := bbase (se 3 (by rfl) ⟨668390, by rfl⟩ : syracuseStep 3564749 = 1336781) (by norm_num)
theorem B2376499 : Blo 2111435 2376499 := bstep (se 1 (by rfl) ⟨1782374, by rfl⟩ : syracuseStep 2376499 = 3564749) B3564749
theorem B3168665 : Blo 2111435 3168665 := bstep (se 2 (by rfl) ⟨1188249, by rfl⟩ : syracuseStep 3168665 = 2376499) B2376499
theorem B2112443 : Blo 2111435 2112443 := bstep (se 1 (by rfl) ⟨1584332, by rfl⟩ : syracuseStep 2112443 = 3168665) B3168665
theorem B13534933 : Blo 2111435 13534933 := bbase (se 7 (by rfl) ⟨158612, by rfl⟩ : syracuseStep 13534933 = 317225) (by norm_num)
theorem B18046577 : Blo 2111435 18046577 := bstep (se 2 (by rfl) ⟨6767466, by rfl⟩ : syracuseStep 18046577 = 13534933) B13534933
theorem B12031051 : Blo 2111435 12031051 := bstep (se 1 (by rfl) ⟨9023288, by rfl⟩ : syracuseStep 12031051 = 18046577) B18046577
theorem B16041401 : Blo 2111435 16041401 := bstep (se 2 (by rfl) ⟨6015525, by rfl⟩ : syracuseStep 16041401 = 12031051) B12031051
theorem B10694267 : Blo 2111435 10694267 := bstep (se 1 (by rfl) ⟨8020700, by rfl⟩ : syracuseStep 10694267 = 16041401) B16041401
theorem B7129511 : Blo 2111435 7129511 := bstep (se 1 (by rfl) ⟨5347133, by rfl⟩ : syracuseStep 7129511 = 10694267) B10694267
theorem B4753007 : Blo 2111435 4753007 := bstep (se 1 (by rfl) ⟨3564755, by rfl⟩ : syracuseStep 4753007 = 7129511) B7129511
theorem B3168671 : Blo 2111435 3168671 := bstep (se 1 (by rfl) ⟨2376503, by rfl⟩ : syracuseStep 3168671 = 4753007) B4753007
theorem B2112447 : Blo 2111435 2112447 := bstep (se 1 (by rfl) ⟨1584335, by rfl⟩ : syracuseStep 2112447 = 3168671) B3168671
theorem B3168677 : Blo 2111435 3168677 := bbase (se 4 (by rfl) ⟨297063, by rfl⟩ : syracuseStep 3168677 = 594127) (by norm_num)
theorem B2112451 : Blo 2111435 2112451 := bstep (se 1 (by rfl) ⟨1584338, by rfl⟩ : syracuseStep 2112451 = 3168677) B3168677
theorem B2673577 : Blo 2111435 2673577 := bbase (se 2 (by rfl) ⟨1002591, by rfl⟩ : syracuseStep 2673577 = 2005183) (by norm_num)
theorem B3564769 : Blo 2111435 3564769 := bstep (se 2 (by rfl) ⟨1336788, by rfl⟩ : syracuseStep 3564769 = 2673577) B2673577
theorem B4753025 : Blo 2111435 4753025 := bstep (se 2 (by rfl) ⟨1782384, by rfl⟩ : syracuseStep 4753025 = 3564769) B3564769
theorem B3168683 : Blo 2111435 3168683 := bstep (se 1 (by rfl) ⟨2376512, by rfl⟩ : syracuseStep 3168683 = 4753025) B4753025
theorem B2112455 : Blo 2111435 2112455 := bstep (se 1 (by rfl) ⟨1584341, by rfl⟩ : syracuseStep 2112455 = 3168683) B3168683
theorem B2376517 : Blo 2111435 2376517 := bbase (se 4 (by rfl) ⟨222798, by rfl⟩ : syracuseStep 2376517 = 445597) (by norm_num)
theorem B3168689 : Blo 2111435 3168689 := bstep (se 2 (by rfl) ⟨1188258, by rfl⟩ : syracuseStep 3168689 = 2376517) B2376517
theorem B2112459 : Blo 2111435 2112459 := bstep (se 1 (by rfl) ⟨1584344, by rfl⟩ : syracuseStep 2112459 = 3168689) B3168689
theorem B4010381 : Blo 2111435 4010381 := bbase (se 3 (by rfl) ⟨751946, by rfl⟩ : syracuseStep 4010381 = 1503893) (by norm_num)
theorem B2673587 : Blo 2111435 2673587 := bstep (se 1 (by rfl) ⟨2005190, by rfl⟩ : syracuseStep 2673587 = 4010381) B4010381
theorem B7129565 : Blo 2111435 7129565 := bstep (se 3 (by rfl) ⟨1336793, by rfl⟩ : syracuseStep 7129565 = 2673587) B2673587
theorem B4753043 : Blo 2111435 4753043 := bstep (se 1 (by rfl) ⟨3564782, by rfl⟩ : syracuseStep 4753043 = 7129565) B7129565
theorem B3168695 : Blo 2111435 3168695 := bstep (se 1 (by rfl) ⟨2376521, by rfl⟩ : syracuseStep 3168695 = 4753043) B4753043
theorem B2112463 : Blo 2111435 2112463 := bstep (se 1 (by rfl) ⟨1584347, by rfl⟩ : syracuseStep 2112463 = 3168695) B3168695
theorem B3168701 : Blo 2111435 3168701 := bbase (se 3 (by rfl) ⟨594131, by rfl⟩ : syracuseStep 3168701 = 1188263) (by norm_num)
theorem B2112467 : Blo 2111435 2112467 := bstep (se 1 (by rfl) ⟨1584350, by rfl⟩ : syracuseStep 2112467 = 3168701) B3168701
theorem B4753061 : Blo 2111435 4753061 := bbase (se 4 (by rfl) ⟨445599, by rfl⟩ : syracuseStep 4753061 = 891199) (by norm_num)
theorem B3168707 : Blo 2111435 3168707 := bstep (se 1 (by rfl) ⟨2376530, by rfl⟩ : syracuseStep 3168707 = 4753061) B4753061
theorem B2112471 : Blo 2111435 2112471 := bstep (se 1 (by rfl) ⟨1584353, by rfl⟩ : syracuseStep 2112471 = 3168707) B3168707
theorem B5347205 : Blo 2111435 5347205 := bbase (se 4 (by rfl) ⟨501300, by rfl⟩ : syracuseStep 5347205 = 1002601) (by norm_num)
theorem B3564803 : Blo 2111435 3564803 := bstep (se 1 (by rfl) ⟨2673602, by rfl⟩ : syracuseStep 3564803 = 5347205) B5347205
theorem B2376535 : Blo 2111435 2376535 := bstep (se 1 (by rfl) ⟨1782401, by rfl⟩ : syracuseStep 2376535 = 3564803) B3564803
theorem B3168713 : Blo 2111435 3168713 := bstep (se 2 (by rfl) ⟨1188267, by rfl⟩ : syracuseStep 3168713 = 2376535) B2376535
theorem B2112475 : Blo 2111435 2112475 := bstep (se 1 (by rfl) ⟨1584356, by rfl⟩ : syracuseStep 2112475 = 3168713) B3168713
theorem B9635861 : Blo 2111435 9635861 := bbase (se 6 (by rfl) ⟨225840, by rfl⟩ : syracuseStep 9635861 = 451681) (by norm_num)
theorem B6423907 : Blo 2111435 6423907 := bstep (se 1 (by rfl) ⟨4817930, by rfl⟩ : syracuseStep 6423907 = 9635861) B9635861
theorem B8565209 : Blo 2111435 8565209 := bstep (se 2 (by rfl) ⟨3211953, by rfl⟩ : syracuseStep 8565209 = 6423907) B6423907
theorem B5710139 : Blo 2111435 5710139 := bstep (se 1 (by rfl) ⟨4282604, by rfl⟩ : syracuseStep 5710139 = 8565209) B8565209
theorem B3806759 : Blo 2111435 3806759 := bstep (se 1 (by rfl) ⟨2855069, by rfl⟩ : syracuseStep 3806759 = 5710139) B5710139
theorem B2537839 : Blo 2111435 2537839 := bstep (se 1 (by rfl) ⟨1903379, by rfl⟩ : syracuseStep 2537839 = 3806759) B3806759
theorem B3383785 : Blo 2111435 3383785 := bstep (se 2 (by rfl) ⟨1268919, by rfl⟩ : syracuseStep 3383785 = 2537839) B2537839
theorem B4511713 : Blo 2111435 4511713 := bstep (se 2 (by rfl) ⟨1691892, by rfl⟩ : syracuseStep 4511713 = 3383785) B3383785
theorem B6015617 : Blo 2111435 6015617 := bstep (se 2 (by rfl) ⟨2255856, by rfl⟩ : syracuseStep 6015617 = 4511713) B4511713
theorem B4010411 : Blo 2111435 4010411 := bstep (se 1 (by rfl) ⟨3007808, by rfl⟩ : syracuseStep 4010411 = 6015617) B6015617
theorem B10694429 : Blo 2111435 10694429 := bstep (se 3 (by rfl) ⟨2005205, by rfl⟩ : syracuseStep 10694429 = 4010411) B4010411
theorem B7129619 : Blo 2111435 7129619 := bstep (se 1 (by rfl) ⟨5347214, by rfl⟩ : syracuseStep 7129619 = 10694429) B10694429
theorem B4753079 : Blo 2111435 4753079 := bstep (se 1 (by rfl) ⟨3564809, by rfl⟩ : syracuseStep 4753079 = 7129619) B7129619
theorem B3168719 : Blo 2111435 3168719 := bstep (se 1 (by rfl) ⟨2376539, by rfl⟩ : syracuseStep 3168719 = 4753079) B4753079
theorem B2112479 : Blo 2111435 2112479 := bstep (se 1 (by rfl) ⟨1584359, by rfl⟩ : syracuseStep 2112479 = 3168719) B3168719
theorem B3168725 : Blo 2111435 3168725 := bbase (se 7 (by rfl) ⟨37133, by rfl⟩ : syracuseStep 3168725 = 74267) (by norm_num)
theorem B2112483 : Blo 2111435 2112483 := bstep (se 1 (by rfl) ⟨1584362, by rfl⟩ : syracuseStep 2112483 = 3168725) B3168725
theorem B8020853 : Blo 2111435 8020853 := bbase (se 5 (by rfl) ⟨375977, by rfl⟩ : syracuseStep 8020853 = 751955) (by norm_num)
theorem B5347235 : Blo 2111435 5347235 := bstep (se 1 (by rfl) ⟨4010426, by rfl⟩ : syracuseStep 5347235 = 8020853) B8020853
theorem B3564823 : Blo 2111435 3564823 := bstep (se 1 (by rfl) ⟨2673617, by rfl⟩ : syracuseStep 3564823 = 5347235) B5347235
theorem B4753097 : Blo 2111435 4753097 := bstep (se 2 (by rfl) ⟨1782411, by rfl⟩ : syracuseStep 4753097 = 3564823) B3564823
theorem B3168731 : Blo 2111435 3168731 := bstep (se 1 (by rfl) ⟨2376548, by rfl⟩ : syracuseStep 3168731 = 4753097) B4753097
theorem B2112487 : Blo 2111435 2112487 := bstep (se 1 (by rfl) ⟨1584365, by rfl⟩ : syracuseStep 2112487 = 3168731) B3168731
theorem B2376553 : Blo 2111435 2376553 := bbase (se 2 (by rfl) ⟨891207, by rfl⟩ : syracuseStep 2376553 = 1782415) (by norm_num)
theorem B3168737 : Blo 2111435 3168737 := bstep (se 2 (by rfl) ⟨1188276, by rfl⟩ : syracuseStep 3168737 = 2376553) B2376553
theorem B2112491 : Blo 2111435 2112491 := bstep (se 1 (by rfl) ⟨1584368, by rfl⟩ : syracuseStep 2112491 = 3168737) B3168737
theorem B6767621 : Blo 2111435 6767621 := bbase (se 4 (by rfl) ⟨634464, by rfl⟩ : syracuseStep 6767621 = 1268929) (by norm_num)
theorem B4511747 : Blo 2111435 4511747 := bstep (se 1 (by rfl) ⟨3383810, by rfl⟩ : syracuseStep 4511747 = 6767621) B6767621
theorem B12031325 : Blo 2111435 12031325 := bstep (se 3 (by rfl) ⟨2255873, by rfl⟩ : syracuseStep 12031325 = 4511747) B4511747
theorem B8020883 : Blo 2111435 8020883 := bstep (se 1 (by rfl) ⟨6015662, by rfl⟩ : syracuseStep 8020883 = 12031325) B12031325
theorem B5347255 : Blo 2111435 5347255 := bstep (se 1 (by rfl) ⟨4010441, by rfl⟩ : syracuseStep 5347255 = 8020883) B8020883
theorem B7129673 : Blo 2111435 7129673 := bstep (se 2 (by rfl) ⟨2673627, by rfl⟩ : syracuseStep 7129673 = 5347255) B5347255
theorem B4753115 : Blo 2111435 4753115 := bstep (se 1 (by rfl) ⟨3564836, by rfl⟩ : syracuseStep 4753115 = 7129673) B7129673
theorem B3168743 : Blo 2111435 3168743 := bstep (se 1 (by rfl) ⟨2376557, by rfl⟩ : syracuseStep 3168743 = 4753115) B4753115
theorem B2112495 : Blo 2111435 2112495 := bstep (se 1 (by rfl) ⟨1584371, by rfl⟩ : syracuseStep 2112495 = 3168743) B3168743
theorem B3168749 : Blo 2111435 3168749 := bbase (se 3 (by rfl) ⟨594140, by rfl⟩ : syracuseStep 3168749 = 1188281) (by norm_num)
theorem B2112499 : Blo 2111435 2112499 := bstep (se 1 (by rfl) ⟨1584374, by rfl⟩ : syracuseStep 2112499 = 3168749) B3168749
theorem B4753133 : Blo 2111435 4753133 := bbase (se 3 (by rfl) ⟨891212, by rfl⟩ : syracuseStep 4753133 = 1782425) (by norm_num)
theorem B3168755 : Blo 2111435 3168755 := bstep (se 1 (by rfl) ⟨2376566, by rfl⟩ : syracuseStep 3168755 = 4753133) B4753133
theorem B2112503 : Blo 2111435 2112503 := bstep (se 1 (by rfl) ⟨1584377, by rfl⟩ : syracuseStep 2112503 = 3168755) B3168755
theorem B7613621 : Blo 2111435 7613621 := bbase (se 5 (by rfl) ⟨356888, by rfl⟩ : syracuseStep 7613621 = 713777) (by norm_num)
theorem B5075747 : Blo 2111435 5075747 := bstep (se 1 (by rfl) ⟨3806810, by rfl⟩ : syracuseStep 5075747 = 7613621) B7613621
theorem B3383831 : Blo 2111435 3383831 := bstep (se 1 (by rfl) ⟨2537873, by rfl⟩ : syracuseStep 3383831 = 5075747) B5075747
theorem B2255887 : Blo 2111435 2255887 := bstep (se 1 (by rfl) ⟨1691915, by rfl⟩ : syracuseStep 2255887 = 3383831) B3383831
theorem B3007849 : Blo 2111435 3007849 := bstep (se 2 (by rfl) ⟨1127943, by rfl⟩ : syracuseStep 3007849 = 2255887) B2255887
theorem B4010465 : Blo 2111435 4010465 := bstep (se 2 (by rfl) ⟨1503924, by rfl⟩ : syracuseStep 4010465 = 3007849) B3007849
theorem B2673643 : Blo 2111435 2673643 := bstep (se 1 (by rfl) ⟨2005232, by rfl⟩ : syracuseStep 2673643 = 4010465) B4010465
theorem B3564857 : Blo 2111435 3564857 := bstep (se 2 (by rfl) ⟨1336821, by rfl⟩ : syracuseStep 3564857 = 2673643) B2673643
theorem B2376571 : Blo 2111435 2376571 := bstep (se 1 (by rfl) ⟨1782428, by rfl⟩ : syracuseStep 2376571 = 3564857) B3564857
theorem B3168761 : Blo 2111435 3168761 := bstep (se 2 (by rfl) ⟨1188285, by rfl⟩ : syracuseStep 3168761 = 2376571) B2376571
theorem B2112507 : Blo 2111435 2112507 := bstep (se 1 (by rfl) ⟨1584380, by rfl⟩ : syracuseStep 2112507 = 3168761) B3168761
theorem B5145005 : Blo 2111435 5145005 := bbase (se 3 (by rfl) ⟨964688, by rfl⟩ : syracuseStep 5145005 = 1929377) (by norm_num)
theorem B13720013 : Blo 2111435 13720013 := bstep (se 3 (by rfl) ⟨2572502, by rfl⟩ : syracuseStep 13720013 = 5145005) B5145005
theorem B9146675 : Blo 2111435 9146675 := bstep (se 1 (by rfl) ⟨6860006, by rfl⟩ : syracuseStep 9146675 = 13720013) B13720013
theorem B6097783 : Blo 2111435 6097783 := bstep (se 1 (by rfl) ⟨4573337, by rfl⟩ : syracuseStep 6097783 = 9146675) B9146675
theorem B8130377 : Blo 2111435 8130377 := bstep (se 2 (by rfl) ⟨3048891, by rfl⟩ : syracuseStep 8130377 = 6097783) B6097783
theorem B5420251 : Blo 2111435 5420251 := bstep (se 1 (by rfl) ⟨4065188, by rfl⟩ : syracuseStep 5420251 = 8130377) B8130377
theorem B7227001 : Blo 2111435 7227001 := bstep (se 2 (by rfl) ⟨2710125, by rfl⟩ : syracuseStep 7227001 = 5420251) B5420251
theorem B38544005 : Blo 2111435 38544005 := bstep (se 4 (by rfl) ⟨3613500, by rfl⟩ : syracuseStep 38544005 = 7227001) B7227001
theorem B25696003 : Blo 2111435 25696003 := bstep (se 1 (by rfl) ⟨19272002, by rfl⟩ : syracuseStep 25696003 = 38544005) B38544005
theorem B34261337 : Blo 2111435 34261337 := bstep (se 2 (by rfl) ⟨12848001, by rfl⟩ : syracuseStep 34261337 = 25696003) B25696003
theorem B91363565 : Blo 2111435 91363565 := bstep (se 3 (by rfl) ⟨17130668, by rfl⟩ : syracuseStep 91363565 = 34261337) B34261337
theorem B60909043 : Blo 2111435 60909043 := bstep (se 1 (by rfl) ⟨45681782, by rfl⟩ : syracuseStep 60909043 = 91363565) B91363565
theorem B81212057 : Blo 2111435 81212057 := bstep (se 2 (by rfl) ⟨30454521, by rfl⟩ : syracuseStep 81212057 = 60909043) B60909043
theorem B54141371 : Blo 2111435 54141371 := bstep (se 1 (by rfl) ⟨40606028, by rfl⟩ : syracuseStep 54141371 = 81212057) B81212057
theorem B36094247 : Blo 2111435 36094247 := bstep (se 1 (by rfl) ⟨27070685, by rfl⟩ : syracuseStep 36094247 = 54141371) B54141371
theorem B24062831 : Blo 2111435 24062831 := bstep (se 1 (by rfl) ⟨18047123, by rfl⟩ : syracuseStep 24062831 = 36094247) B36094247
theorem B16041887 : Blo 2111435 16041887 := bstep (se 1 (by rfl) ⟨12031415, by rfl⟩ : syracuseStep 16041887 = 24062831) B24062831
theorem B10694591 : Blo 2111435 10694591 := bstep (se 1 (by rfl) ⟨8020943, by rfl⟩ : syracuseStep 10694591 = 16041887) B16041887
theorem B7129727 : Blo 2111435 7129727 := bstep (se 1 (by rfl) ⟨5347295, by rfl⟩ : syracuseStep 7129727 = 10694591) B10694591
theorem B4753151 : Blo 2111435 4753151 := bstep (se 1 (by rfl) ⟨3564863, by rfl⟩ : syracuseStep 4753151 = 7129727) B7129727
theorem B3168767 : Blo 2111435 3168767 := bstep (se 1 (by rfl) ⟨2376575, by rfl⟩ : syracuseStep 3168767 = 4753151) B4753151
theorem B2112511 : Blo 2111435 2112511 := bstep (se 1 (by rfl) ⟨1584383, by rfl⟩ : syracuseStep 2112511 = 3168767) B3168767
theorem B3168773 : Blo 2111435 3168773 := bbase (se 4 (by rfl) ⟨297072, by rfl⟩ : syracuseStep 3168773 = 594145) (by norm_num)
theorem B2112515 : Blo 2111435 2112515 := bstep (se 1 (by rfl) ⟨1584386, by rfl⟩ : syracuseStep 2112515 = 3168773) B3168773
theorem B3564877 : Blo 2111435 3564877 := bbase (se 3 (by rfl) ⟨668414, by rfl⟩ : syracuseStep 3564877 = 1336829) (by norm_num)
theorem B4753169 : Blo 2111435 4753169 := bstep (se 2 (by rfl) ⟨1782438, by rfl⟩ : syracuseStep 4753169 = 3564877) B3564877
theorem B3168779 : Blo 2111435 3168779 := bstep (se 1 (by rfl) ⟨2376584, by rfl⟩ : syracuseStep 3168779 = 4753169) B4753169
theorem B2112519 : Blo 2111435 2112519 := bstep (se 1 (by rfl) ⟨1584389, by rfl⟩ : syracuseStep 2112519 = 3168779) B3168779
theorem B2376589 : Blo 2111435 2376589 := bbase (se 3 (by rfl) ⟨445610, by rfl⟩ : syracuseStep 2376589 = 891221) (by norm_num)
theorem B3168785 : Blo 2111435 3168785 := bstep (se 2 (by rfl) ⟨1188294, by rfl⟩ : syracuseStep 3168785 = 2376589) B2376589
theorem B2112523 : Blo 2111435 2112523 := bstep (se 1 (by rfl) ⟨1584392, by rfl⟩ : syracuseStep 2112523 = 3168785) B3168785
theorem B7129781 : Blo 2111435 7129781 := bbase (se 5 (by rfl) ⟨334208, by rfl⟩ : syracuseStep 7129781 = 668417) (by norm_num)
theorem B4753187 : Blo 2111435 4753187 := bstep (se 1 (by rfl) ⟨3564890, by rfl⟩ : syracuseStep 4753187 = 7129781) B7129781
theorem B3168791 : Blo 2111435 3168791 := bstep (se 1 (by rfl) ⟨2376593, by rfl⟩ : syracuseStep 3168791 = 4753187) B4753187
theorem B2112527 : Blo 2111435 2112527 := bstep (se 1 (by rfl) ⟨1584395, by rfl⟩ : syracuseStep 2112527 = 3168791) B3168791
theorem B3168797 : Blo 2111435 3168797 := bbase (se 3 (by rfl) ⟨594149, by rfl⟩ : syracuseStep 3168797 = 1188299) (by norm_num)
theorem B2112531 : Blo 2111435 2112531 := bstep (se 1 (by rfl) ⟨1584398, by rfl⟩ : syracuseStep 2112531 = 3168797) B3168797
theorem B4753205 : Blo 2111435 4753205 := bbase (se 5 (by rfl) ⟨222806, by rfl⟩ : syracuseStep 4753205 = 445613) (by norm_num)
theorem B3168803 : Blo 2111435 3168803 := bstep (se 1 (by rfl) ⟨2376602, by rfl⟩ : syracuseStep 3168803 = 4753205) B4753205
theorem B2112535 : Blo 2111435 2112535 := bstep (se 1 (by rfl) ⟨1584401, by rfl⟩ : syracuseStep 2112535 = 3168803) B3168803
theorem B3212045 : Blo 2111435 3212045 := bbase (se 3 (by rfl) ⟨602258, by rfl⟩ : syracuseStep 3212045 = 1204517) (by norm_num)
theorem B2141363 : Blo 2111435 2141363 := bstep (se 1 (by rfl) ⟨1606022, by rfl⟩ : syracuseStep 2141363 = 3212045) B3212045
theorem B5710301 : Blo 2111435 5710301 := bstep (se 3 (by rfl) ⟨1070681, by rfl⟩ : syracuseStep 5710301 = 2141363) B2141363
theorem B3806867 : Blo 2111435 3806867 := bstep (se 1 (by rfl) ⟨2855150, by rfl⟩ : syracuseStep 3806867 = 5710301) B5710301
theorem B2537911 : Blo 2111435 2537911 := bstep (se 1 (by rfl) ⟨1903433, by rfl⟩ : syracuseStep 2537911 = 3806867) B3806867
theorem B13535525 : Blo 2111435 13535525 := bstep (se 4 (by rfl) ⟨1268955, by rfl⟩ : syracuseStep 13535525 = 2537911) B2537911
theorem B9023683 : Blo 2111435 9023683 := bstep (se 1 (by rfl) ⟨6767762, by rfl⟩ : syracuseStep 9023683 = 13535525) B13535525
theorem B12031577 : Blo 2111435 12031577 := bstep (se 2 (by rfl) ⟨4511841, by rfl⟩ : syracuseStep 12031577 = 9023683) B9023683
theorem B8021051 : Blo 2111435 8021051 := bstep (se 1 (by rfl) ⟨6015788, by rfl⟩ : syracuseStep 8021051 = 12031577) B12031577
theorem B5347367 : Blo 2111435 5347367 := bstep (se 1 (by rfl) ⟨4010525, by rfl⟩ : syracuseStep 5347367 = 8021051) B8021051
theorem B3564911 : Blo 2111435 3564911 := bstep (se 1 (by rfl) ⟨2673683, by rfl⟩ : syracuseStep 3564911 = 5347367) B5347367
theorem B2376607 : Blo 2111435 2376607 := bstep (se 1 (by rfl) ⟨1782455, by rfl⟩ : syracuseStep 2376607 = 3564911) B3564911
theorem B3168809 : Blo 2111435 3168809 := bstep (se 2 (by rfl) ⟨1188303, by rfl⟩ : syracuseStep 3168809 = 2376607) B2376607
theorem B2112539 : Blo 2111435 2112539 := bstep (se 1 (by rfl) ⟨1584404, by rfl⟩ : syracuseStep 2112539 = 3168809) B3168809
theorem B4282733 : Blo 2111435 4282733 := bbase (se 3 (by rfl) ⟨803012, by rfl⟩ : syracuseStep 4282733 = 1606025) (by norm_num)
theorem B11420621 : Blo 2111435 11420621 := bstep (se 3 (by rfl) ⟨2141366, by rfl⟩ : syracuseStep 11420621 = 4282733) B4282733
theorem B7613747 : Blo 2111435 7613747 := bstep (se 1 (by rfl) ⟨5710310, by rfl⟩ : syracuseStep 7613747 = 11420621) B11420621
theorem B5075831 : Blo 2111435 5075831 := bstep (se 1 (by rfl) ⟨3806873, by rfl⟩ : syracuseStep 5075831 = 7613747) B7613747
theorem B13535549 : Blo 2111435 13535549 := bstep (se 3 (by rfl) ⟨2537915, by rfl⟩ : syracuseStep 13535549 = 5075831) B5075831
theorem B9023699 : Blo 2111435 9023699 := bstep (se 1 (by rfl) ⟨6767774, by rfl⟩ : syracuseStep 9023699 = 13535549) B13535549
theorem B6015799 : Blo 2111435 6015799 := bstep (se 1 (by rfl) ⟨4511849, by rfl⟩ : syracuseStep 6015799 = 9023699) B9023699
theorem B8021065 : Blo 2111435 8021065 := bstep (se 2 (by rfl) ⟨3007899, by rfl⟩ : syracuseStep 8021065 = 6015799) B6015799
theorem B10694753 : Blo 2111435 10694753 := bstep (se 2 (by rfl) ⟨4010532, by rfl⟩ : syracuseStep 10694753 = 8021065) B8021065
theorem B7129835 : Blo 2111435 7129835 := bstep (se 1 (by rfl) ⟨5347376, by rfl⟩ : syracuseStep 7129835 = 10694753) B10694753
theorem B4753223 : Blo 2111435 4753223 := bstep (se 1 (by rfl) ⟨3564917, by rfl⟩ : syracuseStep 4753223 = 7129835) B7129835
theorem B3168815 : Blo 2111435 3168815 := bstep (se 1 (by rfl) ⟨2376611, by rfl⟩ : syracuseStep 3168815 = 4753223) B4753223
theorem B2112543 : Blo 2111435 2112543 := bstep (se 1 (by rfl) ⟨1584407, by rfl⟩ : syracuseStep 2112543 = 3168815) B3168815
theorem B3168821 : Blo 2111435 3168821 := bbase (se 5 (by rfl) ⟨148538, by rfl⟩ : syracuseStep 3168821 = 297077) (by norm_num)
theorem B2112547 : Blo 2111435 2112547 := bstep (se 1 (by rfl) ⟨1584410, by rfl⟩ : syracuseStep 2112547 = 3168821) B3168821
theorem B5347397 : Blo 2111435 5347397 := bbase (se 4 (by rfl) ⟨501318, by rfl⟩ : syracuseStep 5347397 = 1002637) (by norm_num)
theorem B3564931 : Blo 2111435 3564931 := bstep (se 1 (by rfl) ⟨2673698, by rfl⟩ : syracuseStep 3564931 = 5347397) B5347397
theorem B4753241 : Blo 2111435 4753241 := bstep (se 2 (by rfl) ⟨1782465, by rfl⟩ : syracuseStep 4753241 = 3564931) B3564931
theorem B3168827 : Blo 2111435 3168827 := bstep (se 1 (by rfl) ⟨2376620, by rfl⟩ : syracuseStep 3168827 = 4753241) B4753241
theorem B2112551 : Blo 2111435 2112551 := bstep (se 1 (by rfl) ⟨1584413, by rfl⟩ : syracuseStep 2112551 = 3168827) B3168827
theorem B2376625 : Blo 2111435 2376625 := bbase (se 2 (by rfl) ⟨891234, by rfl⟩ : syracuseStep 2376625 = 1782469) (by norm_num)
theorem B3168833 : Blo 2111435 3168833 := bstep (se 2 (by rfl) ⟨1188312, by rfl⟩ : syracuseStep 3168833 = 2376625) B2376625
theorem B2112555 : Blo 2111435 2112555 := bstep (se 1 (by rfl) ⟨1584416, by rfl⟩ : syracuseStep 2112555 = 3168833) B3168833
theorem B6015845 : Blo 2111435 6015845 := bbase (se 4 (by rfl) ⟨563985, by rfl⟩ : syracuseStep 6015845 = 1127971) (by norm_num)
theorem B4010563 : Blo 2111435 4010563 := bstep (se 1 (by rfl) ⟨3007922, by rfl⟩ : syracuseStep 4010563 = 6015845) B6015845
theorem B5347417 : Blo 2111435 5347417 := bstep (se 2 (by rfl) ⟨2005281, by rfl⟩ : syracuseStep 5347417 = 4010563) B4010563
theorem B7129889 : Blo 2111435 7129889 := bstep (se 2 (by rfl) ⟨2673708, by rfl⟩ : syracuseStep 7129889 = 5347417) B5347417
theorem B4753259 : Blo 2111435 4753259 := bstep (se 1 (by rfl) ⟨3564944, by rfl⟩ : syracuseStep 4753259 = 7129889) B7129889
theorem B3168839 : Blo 2111435 3168839 := bstep (se 1 (by rfl) ⟨2376629, by rfl⟩ : syracuseStep 3168839 = 4753259) B4753259
theorem B2112559 : Blo 2111435 2112559 := bstep (se 1 (by rfl) ⟨1584419, by rfl⟩ : syracuseStep 2112559 = 3168839) B3168839
theorem B3168845 : Blo 2111435 3168845 := bbase (se 3 (by rfl) ⟨594158, by rfl⟩ : syracuseStep 3168845 = 1188317) (by norm_num)
theorem B2112563 : Blo 2111435 2112563 := bstep (se 1 (by rfl) ⟨1584422, by rfl⟩ : syracuseStep 2112563 = 3168845) B3168845
theorem B4753277 : Blo 2111435 4753277 := bbase (se 3 (by rfl) ⟨891239, by rfl⟩ : syracuseStep 4753277 = 1782479) (by norm_num)
theorem B3168851 : Blo 2111435 3168851 := bstep (se 1 (by rfl) ⟨2376638, by rfl⟩ : syracuseStep 3168851 = 4753277) B4753277
theorem B2112567 : Blo 2111435 2112567 := bstep (se 1 (by rfl) ⟨1584425, by rfl⟩ : syracuseStep 2112567 = 3168851) B3168851
theorem B3564965 : Blo 2111435 3564965 := bbase (se 4 (by rfl) ⟨334215, by rfl⟩ : syracuseStep 3564965 = 668431) (by norm_num)
theorem B2376643 : Blo 2111435 2376643 := bstep (se 1 (by rfl) ⟨1782482, by rfl⟩ : syracuseStep 2376643 = 3564965) B3564965
theorem B3168857 : Blo 2111435 3168857 := bstep (se 2 (by rfl) ⟨1188321, by rfl⟩ : syracuseStep 3168857 = 2376643) B2376643
theorem B2112571 : Blo 2111435 2112571 := bstep (se 1 (by rfl) ⟨1584428, by rfl⟩ : syracuseStep 2112571 = 3168857) B3168857
theorem B5075909 : Blo 2111435 5075909 := bbase (se 4 (by rfl) ⟨475866, by rfl⟩ : syracuseStep 5075909 = 951733) (by norm_num)
theorem B3383939 : Blo 2111435 3383939 := bstep (se 1 (by rfl) ⟨2537954, by rfl⟩ : syracuseStep 3383939 = 5075909) B5075909
theorem B2255959 : Blo 2111435 2255959 := bstep (se 1 (by rfl) ⟨1691969, by rfl⟩ : syracuseStep 2255959 = 3383939) B3383939
theorem B3007945 : Blo 2111435 3007945 := bstep (se 2 (by rfl) ⟨1127979, by rfl⟩ : syracuseStep 3007945 = 2255959) B2255959
theorem B16042373 : Blo 2111435 16042373 := bstep (se 4 (by rfl) ⟨1503972, by rfl⟩ : syracuseStep 16042373 = 3007945) B3007945
theorem B10694915 : Blo 2111435 10694915 := bstep (se 1 (by rfl) ⟨8021186, by rfl⟩ : syracuseStep 10694915 = 16042373) B16042373
theorem B7129943 : Blo 2111435 7129943 := bstep (se 1 (by rfl) ⟨5347457, by rfl⟩ : syracuseStep 7129943 = 10694915) B10694915
theorem B4753295 : Blo 2111435 4753295 := bstep (se 1 (by rfl) ⟨3564971, by rfl⟩ : syracuseStep 4753295 = 7129943) B7129943
theorem B3168863 : Blo 2111435 3168863 := bstep (se 1 (by rfl) ⟨2376647, by rfl⟩ : syracuseStep 3168863 = 4753295) B4753295
theorem B2112575 : Blo 2111435 2112575 := bstep (se 1 (by rfl) ⟨1584431, by rfl⟩ : syracuseStep 2112575 = 3168863) B3168863
theorem B3168869 : Blo 2111435 3168869 := bbase (se 4 (by rfl) ⟨297081, by rfl⟩ : syracuseStep 3168869 = 594163) (by norm_num)
theorem B2112579 : Blo 2111435 2112579 := bstep (se 1 (by rfl) ⟨1584434, by rfl⟩ : syracuseStep 2112579 = 3168869) B3168869
theorem B3007957 : Blo 2111435 3007957 := bbase (se 7 (by rfl) ⟨35249, by rfl⟩ : syracuseStep 3007957 = 70499) (by norm_num)
theorem B4010609 : Blo 2111435 4010609 := bstep (se 2 (by rfl) ⟨1503978, by rfl⟩ : syracuseStep 4010609 = 3007957) B3007957
theorem B2673739 : Blo 2111435 2673739 := bstep (se 1 (by rfl) ⟨2005304, by rfl⟩ : syracuseStep 2673739 = 4010609) B4010609
theorem B3564985 : Blo 2111435 3564985 := bstep (se 2 (by rfl) ⟨1336869, by rfl⟩ : syracuseStep 3564985 = 2673739) B2673739
theorem B4753313 : Blo 2111435 4753313 := bstep (se 2 (by rfl) ⟨1782492, by rfl⟩ : syracuseStep 4753313 = 3564985) B3564985
theorem B3168875 : Blo 2111435 3168875 := bstep (se 1 (by rfl) ⟨2376656, by rfl⟩ : syracuseStep 3168875 = 4753313) B4753313
theorem B2112583 : Blo 2111435 2112583 := bstep (se 1 (by rfl) ⟨1584437, by rfl⟩ : syracuseStep 2112583 = 3168875) B3168875
theorem B2376661 : Blo 2111435 2376661 := bbase (se 7 (by rfl) ⟨27851, by rfl⟩ : syracuseStep 2376661 = 55703) (by norm_num)
theorem B3168881 : Blo 2111435 3168881 := bstep (se 2 (by rfl) ⟨1188330, by rfl⟩ : syracuseStep 3168881 = 2376661) B2376661
theorem B2112587 : Blo 2111435 2112587 := bstep (se 1 (by rfl) ⟨1584440, by rfl⟩ : syracuseStep 2112587 = 3168881) B3168881
theorem B2673749 : Blo 2111435 2673749 := bbase (se 8 (by rfl) ⟨15666, by rfl⟩ : syracuseStep 2673749 = 31333) (by norm_num)
theorem B7129997 : Blo 2111435 7129997 := bstep (se 3 (by rfl) ⟨1336874, by rfl⟩ : syracuseStep 7129997 = 2673749) B2673749
theorem B4753331 : Blo 2111435 4753331 := bstep (se 1 (by rfl) ⟨3564998, by rfl⟩ : syracuseStep 4753331 = 7129997) B7129997
theorem B3168887 : Blo 2111435 3168887 := bstep (se 1 (by rfl) ⟨2376665, by rfl⟩ : syracuseStep 3168887 = 4753331) B4753331
theorem B2112591 : Blo 2111435 2112591 := bstep (se 1 (by rfl) ⟨1584443, by rfl⟩ : syracuseStep 2112591 = 3168887) B3168887
theorem B3168893 : Blo 2111435 3168893 := bbase (se 3 (by rfl) ⟨594167, by rfl⟩ : syracuseStep 3168893 = 1188335) (by norm_num)
theorem B2112595 : Blo 2111435 2112595 := bstep (se 1 (by rfl) ⟨1584446, by rfl⟩ : syracuseStep 2112595 = 3168893) B3168893
theorem B4753349 : Blo 2111435 4753349 := bbase (se 4 (by rfl) ⟨445626, by rfl⟩ : syracuseStep 4753349 = 891253) (by norm_num)
theorem B3168899 : Blo 2111435 3168899 := bstep (se 1 (by rfl) ⟨2376674, by rfl⟩ : syracuseStep 3168899 = 4753349) B4753349
theorem B2112599 : Blo 2111435 2112599 := bstep (se 1 (by rfl) ⟨1584449, by rfl⟩ : syracuseStep 2112599 = 3168899) B3168899
theorem B9023957 : Blo 2111435 9023957 := bbase (se 7 (by rfl) ⟨105749, by rfl⟩ : syracuseStep 9023957 = 211499) (by norm_num)
theorem B6015971 : Blo 2111435 6015971 := bstep (se 1 (by rfl) ⟨4511978, by rfl⟩ : syracuseStep 6015971 = 9023957) B9023957
theorem B4010647 : Blo 2111435 4010647 := bstep (se 1 (by rfl) ⟨3007985, by rfl⟩ : syracuseStep 4010647 = 6015971) B6015971
theorem B5347529 : Blo 2111435 5347529 := bstep (se 2 (by rfl) ⟨2005323, by rfl⟩ : syracuseStep 5347529 = 4010647) B4010647
theorem B3565019 : Blo 2111435 3565019 := bstep (se 1 (by rfl) ⟨2673764, by rfl⟩ : syracuseStep 3565019 = 5347529) B5347529
theorem B2376679 : Blo 2111435 2376679 := bstep (se 1 (by rfl) ⟨1782509, by rfl⟩ : syracuseStep 2376679 = 3565019) B3565019
theorem B3168905 : Blo 2111435 3168905 := bstep (se 2 (by rfl) ⟨1188339, by rfl⟩ : syracuseStep 3168905 = 2376679) B2376679
theorem B2112603 : Blo 2111435 2112603 := bstep (se 1 (by rfl) ⟨1584452, by rfl⟩ : syracuseStep 2112603 = 3168905) B3168905
theorem B10695077 : Blo 2111435 10695077 := bbase (se 4 (by rfl) ⟨1002663, by rfl⟩ : syracuseStep 10695077 = 2005327) (by norm_num)
theorem B7130051 : Blo 2111435 7130051 := bstep (se 1 (by rfl) ⟨5347538, by rfl⟩ : syracuseStep 7130051 = 10695077) B10695077
theorem B4753367 : Blo 2111435 4753367 := bstep (se 1 (by rfl) ⟨3565025, by rfl⟩ : syracuseStep 4753367 = 7130051) B7130051
theorem B3168911 : Blo 2111435 3168911 := bstep (se 1 (by rfl) ⟨2376683, by rfl⟩ : syracuseStep 3168911 = 4753367) B4753367
theorem B2112607 : Blo 2111435 2112607 := bstep (se 1 (by rfl) ⟨1584455, by rfl⟩ : syracuseStep 2112607 = 3168911) B3168911
theorem B3168917 : Blo 2111435 3168917 := bbase (se 6 (by rfl) ⟨74271, by rfl⟩ : syracuseStep 3168917 = 148543) (by norm_num)
theorem B2112611 : Blo 2111435 2112611 := bstep (se 1 (by rfl) ⟨1584458, by rfl⟩ : syracuseStep 2112611 = 3168917) B3168917
theorem B6181285 : Blo 2111435 6181285 := bbase (se 4 (by rfl) ⟨579495, by rfl⟩ : syracuseStep 6181285 = 1158991) (by norm_num)
theorem B8241713 : Blo 2111435 8241713 := bstep (se 2 (by rfl) ⟨3090642, by rfl⟩ : syracuseStep 8241713 = 6181285) B6181285
theorem B5494475 : Blo 2111435 5494475 := bstep (se 1 (by rfl) ⟨4120856, by rfl⟩ : syracuseStep 5494475 = 8241713) B8241713
theorem B3662983 : Blo 2111435 3662983 := bstep (se 1 (by rfl) ⟨2747237, by rfl⟩ : syracuseStep 3662983 = 5494475) B5494475
theorem B4883977 : Blo 2111435 4883977 := bstep (se 2 (by rfl) ⟨1831491, by rfl⟩ : syracuseStep 4883977 = 3662983) B3662983
theorem B6511969 : Blo 2111435 6511969 := bstep (se 2 (by rfl) ⟨2441988, by rfl⟩ : syracuseStep 6511969 = 4883977) B4883977
theorem B8682625 : Blo 2111435 8682625 := bstep (se 2 (by rfl) ⟨3255984, by rfl⟩ : syracuseStep 8682625 = 6511969) B6511969
theorem B46307333 : Blo 2111435 46307333 := bstep (se 4 (by rfl) ⟨4341312, by rfl⟩ : syracuseStep 46307333 = 8682625) B8682625
theorem B123486221 : Blo 2111435 123486221 := bstep (se 3 (by rfl) ⟨23153666, by rfl⟩ : syracuseStep 123486221 = 46307333) B46307333
theorem B82324147 : Blo 2111435 82324147 := bstep (se 1 (by rfl) ⟨61743110, by rfl⟩ : syracuseStep 82324147 = 123486221) B123486221
theorem B109765529 : Blo 2111435 109765529 := bstep (se 2 (by rfl) ⟨41162073, by rfl⟩ : syracuseStep 109765529 = 82324147) B82324147
theorem B73177019 : Blo 2111435 73177019 := bstep (se 1 (by rfl) ⟨54882764, by rfl⟩ : syracuseStep 73177019 = 109765529) B109765529
theorem B48784679 : Blo 2111435 48784679 := bstep (se 1 (by rfl) ⟨36588509, by rfl⟩ : syracuseStep 48784679 = 73177019) B73177019
theorem B32523119 : Blo 2111435 32523119 := bstep (se 1 (by rfl) ⟨24392339, by rfl⟩ : syracuseStep 32523119 = 48784679) B48784679
theorem B21682079 : Blo 2111435 21682079 := bstep (se 1 (by rfl) ⟨16261559, by rfl⟩ : syracuseStep 21682079 = 32523119) B32523119
theorem B14454719 : Blo 2111435 14454719 := bstep (se 1 (by rfl) ⟨10841039, by rfl⟩ : syracuseStep 14454719 = 21682079) B21682079
theorem B9636479 : Blo 2111435 9636479 := bstep (se 1 (by rfl) ⟨7227359, by rfl⟩ : syracuseStep 9636479 = 14454719) B14454719
theorem B6424319 : Blo 2111435 6424319 := bstep (se 1 (by rfl) ⟨4818239, by rfl⟩ : syracuseStep 6424319 = 9636479) B9636479
theorem B4282879 : Blo 2111435 4282879 := bstep (se 1 (by rfl) ⟨3212159, by rfl⟩ : syracuseStep 4282879 = 6424319) B6424319
theorem B5710505 : Blo 2111435 5710505 := bstep (se 2 (by rfl) ⟨2141439, by rfl⟩ : syracuseStep 5710505 = 4282879) B4282879
theorem B15228013 : Blo 2111435 15228013 := bstep (se 3 (by rfl) ⟨2855252, by rfl⟩ : syracuseStep 15228013 = 5710505) B5710505
theorem B20304017 : Blo 2111435 20304017 := bstep (se 2 (by rfl) ⟨7614006, by rfl⟩ : syracuseStep 20304017 = 15228013) B15228013
theorem B13536011 : Blo 2111435 13536011 := bstep (se 1 (by rfl) ⟨10152008, by rfl⟩ : syracuseStep 13536011 = 20304017) B20304017
theorem B9024007 : Blo 2111435 9024007 := bstep (se 1 (by rfl) ⟨6768005, by rfl⟩ : syracuseStep 9024007 = 13536011) B13536011
theorem B12032009 : Blo 2111435 12032009 := bstep (se 2 (by rfl) ⟨4512003, by rfl⟩ : syracuseStep 12032009 = 9024007) B9024007
theorem B8021339 : Blo 2111435 8021339 := bstep (se 1 (by rfl) ⟨6016004, by rfl⟩ : syracuseStep 8021339 = 12032009) B12032009
theorem B5347559 : Blo 2111435 5347559 := bstep (se 1 (by rfl) ⟨4010669, by rfl⟩ : syracuseStep 5347559 = 8021339) B8021339
theorem B3565039 : Blo 2111435 3565039 := bstep (se 1 (by rfl) ⟨2673779, by rfl⟩ : syracuseStep 3565039 = 5347559) B5347559
theorem B4753385 : Blo 2111435 4753385 := bstep (se 2 (by rfl) ⟨1782519, by rfl⟩ : syracuseStep 4753385 = 3565039) B3565039
theorem B3168923 : Blo 2111435 3168923 := bstep (se 1 (by rfl) ⟨2376692, by rfl⟩ : syracuseStep 3168923 = 4753385) B4753385
theorem B2112615 : Blo 2111435 2112615 := bstep (se 1 (by rfl) ⟨1584461, by rfl⟩ : syracuseStep 2112615 = 3168923) B3168923
theorem B2376697 : Blo 2111435 2376697 := bbase (se 2 (by rfl) ⟨891261, by rfl⟩ : syracuseStep 2376697 = 1782523) (by norm_num)
theorem B3168929 : Blo 2111435 3168929 := bstep (se 2 (by rfl) ⟨1188348, by rfl⟩ : syracuseStep 3168929 = 2376697) B2376697
theorem B2112619 : Blo 2111435 2112619 := bstep (se 1 (by rfl) ⟨1584464, by rfl⟩ : syracuseStep 2112619 = 3168929) B3168929
theorem B9767989 : Blo 2111435 9767989 := bbase (se 5 (by rfl) ⟨457874, by rfl⟩ : syracuseStep 9767989 = 915749) (by norm_num)
theorem B13023985 : Blo 2111435 13023985 := bstep (se 2 (by rfl) ⟨4883994, by rfl⟩ : syracuseStep 13023985 = 9767989) B9767989
theorem B17365313 : Blo 2111435 17365313 := bstep (se 2 (by rfl) ⟨6511992, by rfl⟩ : syracuseStep 17365313 = 13023985) B13023985
theorem B46307501 : Blo 2111435 46307501 := bstep (se 3 (by rfl) ⟨8682656, by rfl⟩ : syracuseStep 46307501 = 17365313) B17365313
theorem B30871667 : Blo 2111435 30871667 := bstep (se 1 (by rfl) ⟨23153750, by rfl⟩ : syracuseStep 30871667 = 46307501) B46307501
theorem B20581111 : Blo 2111435 20581111 := bstep (se 1 (by rfl) ⟨15435833, by rfl⟩ : syracuseStep 20581111 = 30871667) B30871667
theorem B109765925 : Blo 2111435 109765925 := bstep (se 4 (by rfl) ⟨10290555, by rfl⟩ : syracuseStep 109765925 = 20581111) B20581111
theorem B73177283 : Blo 2111435 73177283 := bstep (se 1 (by rfl) ⟨54882962, by rfl⟩ : syracuseStep 73177283 = 109765925) B109765925
theorem B48784855 : Blo 2111435 48784855 := bstep (se 1 (by rfl) ⟨36588641, by rfl⟩ : syracuseStep 48784855 = 73177283) B73177283
theorem B65046473 : Blo 2111435 65046473 := bstep (se 2 (by rfl) ⟨24392427, by rfl⟩ : syracuseStep 65046473 = 48784855) B48784855
theorem B43364315 : Blo 2111435 43364315 := bstep (se 1 (by rfl) ⟨32523236, by rfl⟩ : syracuseStep 43364315 = 65046473) B65046473
theorem B28909543 : Blo 2111435 28909543 := bstep (se 1 (by rfl) ⟨21682157, by rfl⟩ : syracuseStep 28909543 = 43364315) B43364315
theorem B38546057 : Blo 2111435 38546057 := bstep (se 2 (by rfl) ⟨14454771, by rfl⟩ : syracuseStep 38546057 = 28909543) B28909543
theorem B25697371 : Blo 2111435 25697371 := bstep (se 1 (by rfl) ⟨19273028, by rfl⟩ : syracuseStep 25697371 = 38546057) B38546057
theorem B34263161 : Blo 2111435 34263161 := bstep (se 2 (by rfl) ⟨12848685, by rfl⟩ : syracuseStep 34263161 = 25697371) B25697371
theorem B22842107 : Blo 2111435 22842107 := bstep (se 1 (by rfl) ⟨17131580, by rfl⟩ : syracuseStep 22842107 = 34263161) B34263161
theorem B15228071 : Blo 2111435 15228071 := bstep (se 1 (by rfl) ⟨11421053, by rfl⟩ : syracuseStep 15228071 = 22842107) B22842107
theorem B10152047 : Blo 2111435 10152047 := bstep (se 1 (by rfl) ⟨7614035, by rfl⟩ : syracuseStep 10152047 = 15228071) B15228071
theorem B6768031 : Blo 2111435 6768031 := bstep (se 1 (by rfl) ⟨5076023, by rfl⟩ : syracuseStep 6768031 = 10152047) B10152047
theorem B9024041 : Blo 2111435 9024041 := bstep (se 2 (by rfl) ⟨3384015, by rfl⟩ : syracuseStep 9024041 = 6768031) B6768031
theorem B6016027 : Blo 2111435 6016027 := bstep (se 1 (by rfl) ⟨4512020, by rfl⟩ : syracuseStep 6016027 = 9024041) B9024041
theorem B8021369 : Blo 2111435 8021369 := bstep (se 2 (by rfl) ⟨3008013, by rfl⟩ : syracuseStep 8021369 = 6016027) B6016027
theorem B5347579 : Blo 2111435 5347579 := bstep (se 1 (by rfl) ⟨4010684, by rfl⟩ : syracuseStep 5347579 = 8021369) B8021369
theorem B7130105 : Blo 2111435 7130105 := bstep (se 2 (by rfl) ⟨2673789, by rfl⟩ : syracuseStep 7130105 = 5347579) B5347579
theorem B4753403 : Blo 2111435 4753403 := bstep (se 1 (by rfl) ⟨3565052, by rfl⟩ : syracuseStep 4753403 = 7130105) B7130105
theorem B3168935 : Blo 2111435 3168935 := bstep (se 1 (by rfl) ⟨2376701, by rfl⟩ : syracuseStep 3168935 = 4753403) B4753403
theorem B2112623 : Blo 2111435 2112623 := bstep (se 1 (by rfl) ⟨1584467, by rfl⟩ : syracuseStep 2112623 = 3168935) B3168935
theorem B3168941 : Blo 2111435 3168941 := bbase (se 3 (by rfl) ⟨594176, by rfl⟩ : syracuseStep 3168941 = 1188353) (by norm_num)
theorem B2112627 : Blo 2111435 2112627 := bstep (se 1 (by rfl) ⟨1584470, by rfl⟩ : syracuseStep 2112627 = 3168941) B3168941
theorem B4753421 : Blo 2111435 4753421 := bbase (se 3 (by rfl) ⟨891266, by rfl⟩ : syracuseStep 4753421 = 1782533) (by norm_num)
theorem B3168947 : Blo 2111435 3168947 := bstep (se 1 (by rfl) ⟨2376710, by rfl⟩ : syracuseStep 3168947 = 4753421) B4753421
theorem B2112631 : Blo 2111435 2112631 := bstep (se 1 (by rfl) ⟨1584473, by rfl⟩ : syracuseStep 2112631 = 3168947) B3168947
theorem B2673805 : Blo 2111435 2673805 := bbase (se 3 (by rfl) ⟨501338, by rfl⟩ : syracuseStep 2673805 = 1002677) (by norm_num)
theorem B3565073 : Blo 2111435 3565073 := bstep (se 2 (by rfl) ⟨1336902, by rfl⟩ : syracuseStep 3565073 = 2673805) B2673805
theorem B2376715 : Blo 2111435 2376715 := bstep (se 1 (by rfl) ⟨1782536, by rfl⟩ : syracuseStep 2376715 = 3565073) B3565073
theorem B3168953 : Blo 2111435 3168953 := bstep (se 2 (by rfl) ⟨1188357, by rfl⟩ : syracuseStep 3168953 = 2376715) B2376715
theorem B2112635 : Blo 2111435 2112635 := bstep (se 1 (by rfl) ⟨1584476, by rfl⟩ : syracuseStep 2112635 = 3168953) B3168953
theorem B20304245 : Blo 2111435 20304245 := bbase (se 5 (by rfl) ⟨951761, by rfl⟩ : syracuseStep 20304245 = 1903523) (by norm_num)
theorem B13536163 : Blo 2111435 13536163 := bstep (se 1 (by rfl) ⟨10152122, by rfl⟩ : syracuseStep 13536163 = 20304245) B20304245
theorem B18048217 : Blo 2111435 18048217 := bstep (se 2 (by rfl) ⟨6768081, by rfl⟩ : syracuseStep 18048217 = 13536163) B13536163
theorem B24064289 : Blo 2111435 24064289 := bstep (se 2 (by rfl) ⟨9024108, by rfl⟩ : syracuseStep 24064289 = 18048217) B18048217
theorem B16042859 : Blo 2111435 16042859 := bstep (se 1 (by rfl) ⟨12032144, by rfl⟩ : syracuseStep 16042859 = 24064289) B24064289
theorem B10695239 : Blo 2111435 10695239 := bstep (se 1 (by rfl) ⟨8021429, by rfl⟩ : syracuseStep 10695239 = 16042859) B16042859
theorem B7130159 : Blo 2111435 7130159 := bstep (se 1 (by rfl) ⟨5347619, by rfl⟩ : syracuseStep 7130159 = 10695239) B10695239
theorem B4753439 : Blo 2111435 4753439 := bstep (se 1 (by rfl) ⟨3565079, by rfl⟩ : syracuseStep 4753439 = 7130159) B7130159
theorem B3168959 : Blo 2111435 3168959 := bstep (se 1 (by rfl) ⟨2376719, by rfl⟩ : syracuseStep 3168959 = 4753439) B4753439
theorem B2112639 : Blo 2111435 2112639 := bstep (se 1 (by rfl) ⟨1584479, by rfl⟩ : syracuseStep 2112639 = 3168959) B3168959
theorem B3168965 : Blo 2111435 3168965 := bbase (se 4 (by rfl) ⟨297090, by rfl⟩ : syracuseStep 3168965 = 594181) (by norm_num)
theorem B2112643 : Blo 2111435 2112643 := bstep (se 1 (by rfl) ⟨1584482, by rfl⟩ : syracuseStep 2112643 = 3168965) B3168965
theorem B3565093 : Blo 2111435 3565093 := bbase (se 4 (by rfl) ⟨334227, by rfl⟩ : syracuseStep 3565093 = 668455) (by norm_num)
theorem B4753457 : Blo 2111435 4753457 := bstep (se 2 (by rfl) ⟨1782546, by rfl⟩ : syracuseStep 4753457 = 3565093) B3565093
theorem B3168971 : Blo 2111435 3168971 := bstep (se 1 (by rfl) ⟨2376728, by rfl⟩ : syracuseStep 3168971 = 4753457) B4753457
theorem B2112647 : Blo 2111435 2112647 := bstep (se 1 (by rfl) ⟨1584485, by rfl⟩ : syracuseStep 2112647 = 3168971) B3168971
theorem B2376733 : Blo 2111435 2376733 := bbase (se 3 (by rfl) ⟨445637, by rfl⟩ : syracuseStep 2376733 = 891275) (by norm_num)
theorem B3168977 : Blo 2111435 3168977 := bstep (se 2 (by rfl) ⟨1188366, by rfl⟩ : syracuseStep 3168977 = 2376733) B2376733
theorem B2112651 : Blo 2111435 2112651 := bstep (se 1 (by rfl) ⟨1584488, by rfl⟩ : syracuseStep 2112651 = 3168977) B3168977
theorem B7130213 : Blo 2111435 7130213 := bbase (se 4 (by rfl) ⟨668457, by rfl⟩ : syracuseStep 7130213 = 1336915) (by norm_num)
theorem B4753475 : Blo 2111435 4753475 := bstep (se 1 (by rfl) ⟨3565106, by rfl⟩ : syracuseStep 4753475 = 7130213) B7130213
theorem B3168983 : Blo 2111435 3168983 := bstep (se 1 (by rfl) ⟨2376737, by rfl⟩ : syracuseStep 3168983 = 4753475) B4753475
theorem B2112655 : Blo 2111435 2112655 := bstep (se 1 (by rfl) ⟨1584491, by rfl⟩ : syracuseStep 2112655 = 3168983) B3168983
theorem B3168989 : Blo 2111435 3168989 := bbase (se 3 (by rfl) ⟨594185, by rfl⟩ : syracuseStep 3168989 = 1188371) (by norm_num)
theorem B2112659 : Blo 2111435 2112659 := bstep (se 1 (by rfl) ⟨1584494, by rfl⟩ : syracuseStep 2112659 = 3168989) B3168989
theorem B4753493 : Blo 2111435 4753493 := bbase (se 8 (by rfl) ⟨27852, by rfl⟩ : syracuseStep 4753493 = 55705) (by norm_num)
theorem B3168995 : Blo 2111435 3168995 := bstep (se 1 (by rfl) ⟨2376746, by rfl⟩ : syracuseStep 3168995 = 4753493) B4753493
theorem B2112663 : Blo 2111435 2112663 := bstep (se 1 (by rfl) ⟨1584497, by rfl⟩ : syracuseStep 2112663 = 3168995) B3168995
theorem B2538065 : Blo 2111435 2538065 := bbase (se 2 (by rfl) ⟨951774, by rfl⟩ : syracuseStep 2538065 = 1903549) (by norm_num)
theorem B6768173 : Blo 2111435 6768173 := bstep (se 3 (by rfl) ⟨1269032, by rfl⟩ : syracuseStep 6768173 = 2538065) B2538065
theorem B4512115 : Blo 2111435 4512115 := bstep (se 1 (by rfl) ⟨3384086, by rfl⟩ : syracuseStep 4512115 = 6768173) B6768173
theorem B6016153 : Blo 2111435 6016153 := bstep (se 2 (by rfl) ⟨2256057, by rfl⟩ : syracuseStep 6016153 = 4512115) B4512115
theorem B8021537 : Blo 2111435 8021537 := bstep (se 2 (by rfl) ⟨3008076, by rfl⟩ : syracuseStep 8021537 = 6016153) B6016153
theorem B5347691 : Blo 2111435 5347691 := bstep (se 1 (by rfl) ⟨4010768, by rfl⟩ : syracuseStep 5347691 = 8021537) B8021537
theorem B3565127 : Blo 2111435 3565127 := bstep (se 1 (by rfl) ⟨2673845, by rfl⟩ : syracuseStep 3565127 = 5347691) B5347691
theorem B2376751 : Blo 2111435 2376751 := bstep (se 1 (by rfl) ⟨1782563, by rfl⟩ : syracuseStep 2376751 = 3565127) B3565127
theorem B3169001 : Blo 2111435 3169001 := bstep (se 2 (by rfl) ⟨1188375, by rfl⟩ : syracuseStep 3169001 = 2376751) B2376751
theorem B2112667 : Blo 2111435 2112667 := bstep (se 1 (by rfl) ⟨1584500, by rfl⟩ : syracuseStep 2112667 = 3169001) B3169001
theorem B6181445 : Blo 2111435 6181445 := bbase (se 4 (by rfl) ⟨579510, by rfl⟩ : syracuseStep 6181445 = 1159021) (by norm_num)
theorem B16483853 : Blo 2111435 16483853 := bstep (se 3 (by rfl) ⟨3090722, by rfl⟩ : syracuseStep 16483853 = 6181445) B6181445
theorem B10989235 : Blo 2111435 10989235 := bstep (se 1 (by rfl) ⟨8241926, by rfl⟩ : syracuseStep 10989235 = 16483853) B16483853
theorem B14652313 : Blo 2111435 14652313 := bstep (se 2 (by rfl) ⟨5494617, by rfl⟩ : syracuseStep 14652313 = 10989235) B10989235
theorem B78145669 : Blo 2111435 78145669 := bstep (se 4 (by rfl) ⟨7326156, by rfl⟩ : syracuseStep 78145669 = 14652313) B14652313
theorem B104194225 : Blo 2111435 104194225 := bstep (se 2 (by rfl) ⟨39072834, by rfl⟩ : syracuseStep 104194225 = 78145669) B78145669
theorem B138925633 : Blo 2111435 138925633 := bstep (se 2 (by rfl) ⟨52097112, by rfl⟩ : syracuseStep 138925633 = 104194225) B104194225
theorem B185234177 : Blo 2111435 185234177 := bstep (se 2 (by rfl) ⟨69462816, by rfl⟩ : syracuseStep 185234177 = 138925633) B138925633
theorem B123489451 : Blo 2111435 123489451 := bstep (se 1 (by rfl) ⟨92617088, by rfl⟩ : syracuseStep 123489451 = 185234177) B185234177
theorem B164652601 : Blo 2111435 164652601 := bstep (se 2 (by rfl) ⟨61744725, by rfl⟩ : syracuseStep 164652601 = 123489451) B123489451
theorem B219536801 : Blo 2111435 219536801 := bstep (se 2 (by rfl) ⟨82326300, by rfl⟩ : syracuseStep 219536801 = 164652601) B164652601
theorem B146357867 : Blo 2111435 146357867 := bstep (se 1 (by rfl) ⟨109768400, by rfl⟩ : syracuseStep 146357867 = 219536801) B219536801
theorem B390287645 : Blo 2111435 390287645 := bstep (se 3 (by rfl) ⟨73178933, by rfl⟩ : syracuseStep 390287645 = 146357867) B146357867
theorem B260191763 : Blo 2111435 260191763 := bstep (se 1 (by rfl) ⟨195143822, by rfl⟩ : syracuseStep 260191763 = 390287645) B390287645
theorem B173461175 : Blo 2111435 173461175 := bstep (se 1 (by rfl) ⟨130095881, by rfl⟩ : syracuseStep 173461175 = 260191763) B260191763
theorem B115640783 : Blo 2111435 115640783 := bstep (se 1 (by rfl) ⟨86730587, by rfl⟩ : syracuseStep 115640783 = 173461175) B173461175
theorem B77093855 : Blo 2111435 77093855 := bstep (se 1 (by rfl) ⟨57820391, by rfl⟩ : syracuseStep 77093855 = 115640783) B115640783
theorem B51395903 : Blo 2111435 51395903 := bstep (se 1 (by rfl) ⟨38546927, by rfl⟩ : syracuseStep 51395903 = 77093855) B77093855
theorem B34263935 : Blo 2111435 34263935 := bstep (se 1 (by rfl) ⟨25697951, by rfl⟩ : syracuseStep 34263935 = 51395903) B51395903
theorem B22842623 : Blo 2111435 22842623 := bstep (se 1 (by rfl) ⟨17131967, by rfl⟩ : syracuseStep 22842623 = 34263935) B34263935
theorem B15228415 : Blo 2111435 15228415 := bstep (se 1 (by rfl) ⟨11421311, by rfl⟩ : syracuseStep 15228415 = 22842623) B22842623
theorem B20304553 : Blo 2111435 20304553 := bstep (se 2 (by rfl) ⟨7614207, by rfl⟩ : syracuseStep 20304553 = 15228415) B15228415
theorem B27072737 : Blo 2111435 27072737 := bstep (se 2 (by rfl) ⟨10152276, by rfl⟩ : syracuseStep 27072737 = 20304553) B20304553
theorem B18048491 : Blo 2111435 18048491 := bstep (se 1 (by rfl) ⟨13536368, by rfl⟩ : syracuseStep 18048491 = 27072737) B27072737
theorem B12032327 : Blo 2111435 12032327 := bstep (se 1 (by rfl) ⟨9024245, by rfl⟩ : syracuseStep 12032327 = 18048491) B18048491
theorem B8021551 : Blo 2111435 8021551 := bstep (se 1 (by rfl) ⟨6016163, by rfl⟩ : syracuseStep 8021551 = 12032327) B12032327
theorem B10695401 : Blo 2111435 10695401 := bstep (se 2 (by rfl) ⟨4010775, by rfl⟩ : syracuseStep 10695401 = 8021551) B8021551
theorem B7130267 : Blo 2111435 7130267 := bstep (se 1 (by rfl) ⟨5347700, by rfl⟩ : syracuseStep 7130267 = 10695401) B10695401
theorem B4753511 : Blo 2111435 4753511 := bstep (se 1 (by rfl) ⟨3565133, by rfl⟩ : syracuseStep 4753511 = 7130267) B7130267
theorem B3169007 : Blo 2111435 3169007 := bstep (se 1 (by rfl) ⟨2376755, by rfl⟩ : syracuseStep 3169007 = 4753511) B4753511
theorem B2112671 : Blo 2111435 2112671 := bstep (se 1 (by rfl) ⟨1584503, by rfl⟩ : syracuseStep 2112671 = 3169007) B3169007
theorem B3169013 : Blo 2111435 3169013 := bbase (se 5 (by rfl) ⟨148547, by rfl⟩ : syracuseStep 3169013 = 297095) (by norm_num)
theorem B2112675 : Blo 2111435 2112675 := bstep (se 1 (by rfl) ⟨1584506, by rfl⟩ : syracuseStep 2112675 = 3169013) B3169013
theorem B2409193 : Blo 2111435 2409193 := bbase (se 2 (by rfl) ⟨903447, by rfl⟩ : syracuseStep 2409193 = 1806895) (by norm_num)
theorem B12849029 : Blo 2111435 12849029 := bstep (se 4 (by rfl) ⟨1204596, by rfl⟩ : syracuseStep 12849029 = 2409193) B2409193
theorem B8566019 : Blo 2111435 8566019 := bstep (se 1 (by rfl) ⟨6424514, by rfl⟩ : syracuseStep 8566019 = 12849029) B12849029
theorem B5710679 : Blo 2111435 5710679 := bstep (se 1 (by rfl) ⟨4283009, by rfl⟩ : syracuseStep 5710679 = 8566019) B8566019
theorem B3807119 : Blo 2111435 3807119 := bstep (se 1 (by rfl) ⟨2855339, by rfl⟩ : syracuseStep 3807119 = 5710679) B5710679
theorem B10152317 : Blo 2111435 10152317 := bstep (se 3 (by rfl) ⟨1903559, by rfl⟩ : syracuseStep 10152317 = 3807119) B3807119
theorem B6768211 : Blo 2111435 6768211 := bstep (se 1 (by rfl) ⟨5076158, by rfl⟩ : syracuseStep 6768211 = 10152317) B10152317
theorem B9024281 : Blo 2111435 9024281 := bstep (se 2 (by rfl) ⟨3384105, by rfl⟩ : syracuseStep 9024281 = 6768211) B6768211
theorem B6016187 : Blo 2111435 6016187 := bstep (se 1 (by rfl) ⟨4512140, by rfl⟩ : syracuseStep 6016187 = 9024281) B9024281
theorem B4010791 : Blo 2111435 4010791 := bstep (se 1 (by rfl) ⟨3008093, by rfl⟩ : syracuseStep 4010791 = 6016187) B6016187
theorem B5347721 : Blo 2111435 5347721 := bstep (se 2 (by rfl) ⟨2005395, by rfl⟩ : syracuseStep 5347721 = 4010791) B4010791
theorem B3565147 : Blo 2111435 3565147 := bstep (se 1 (by rfl) ⟨2673860, by rfl⟩ : syracuseStep 3565147 = 5347721) B5347721
theorem B4753529 : Blo 2111435 4753529 := bstep (se 2 (by rfl) ⟨1782573, by rfl⟩ : syracuseStep 4753529 = 3565147) B3565147
theorem B3169019 : Blo 2111435 3169019 := bstep (se 1 (by rfl) ⟨2376764, by rfl⟩ : syracuseStep 3169019 = 4753529) B4753529
theorem B2112679 : Blo 2111435 2112679 := bstep (se 1 (by rfl) ⟨1584509, by rfl⟩ : syracuseStep 2112679 = 3169019) B3169019
theorem B2376769 : Blo 2111435 2376769 := bbase (se 2 (by rfl) ⟨891288, by rfl⟩ : syracuseStep 2376769 = 1782577) (by norm_num)
theorem B3169025 : Blo 2111435 3169025 := bstep (se 2 (by rfl) ⟨1188384, by rfl⟩ : syracuseStep 3169025 = 2376769) B2376769
theorem B2112683 : Blo 2111435 2112683 := bstep (se 1 (by rfl) ⟨1584512, by rfl⟩ : syracuseStep 2112683 = 3169025) B3169025
theorem B5347741 : Blo 2111435 5347741 := bbase (se 3 (by rfl) ⟨1002701, by rfl⟩ : syracuseStep 5347741 = 2005403) (by norm_num)
theorem B7130321 : Blo 2111435 7130321 := bstep (se 2 (by rfl) ⟨2673870, by rfl⟩ : syracuseStep 7130321 = 5347741) B5347741
theorem B4753547 : Blo 2111435 4753547 := bstep (se 1 (by rfl) ⟨3565160, by rfl⟩ : syracuseStep 4753547 = 7130321) B7130321
theorem B3169031 : Blo 2111435 3169031 := bstep (se 1 (by rfl) ⟨2376773, by rfl⟩ : syracuseStep 3169031 = 4753547) B4753547
theorem B2112687 : Blo 2111435 2112687 := bstep (se 1 (by rfl) ⟨1584515, by rfl⟩ : syracuseStep 2112687 = 3169031) B3169031
theorem B3169037 : Blo 2111435 3169037 := bbase (se 3 (by rfl) ⟨594194, by rfl⟩ : syracuseStep 3169037 = 1188389) (by norm_num)
theorem B2112691 : Blo 2111435 2112691 := bstep (se 1 (by rfl) ⟨1584518, by rfl⟩ : syracuseStep 2112691 = 3169037) B3169037
theorem B4753565 : Blo 2111435 4753565 := bbase (se 3 (by rfl) ⟨891293, by rfl⟩ : syracuseStep 4753565 = 1782587) (by norm_num)
theorem B3169043 : Blo 2111435 3169043 := bstep (se 1 (by rfl) ⟨2376782, by rfl⟩ : syracuseStep 3169043 = 4753565) B4753565
theorem B2112695 : Blo 2111435 2112695 := bstep (se 1 (by rfl) ⟨1584521, by rfl⟩ : syracuseStep 2112695 = 3169043) B3169043
theorem B3565181 : Blo 2111435 3565181 := bbase (se 3 (by rfl) ⟨668471, by rfl⟩ : syracuseStep 3565181 = 1336943) (by norm_num)
theorem B2376787 : Blo 2111435 2376787 := bstep (se 1 (by rfl) ⟨1782590, by rfl⟩ : syracuseStep 2376787 = 3565181) B3565181
theorem B3169049 : Blo 2111435 3169049 := bstep (se 2 (by rfl) ⟨1188393, by rfl⟩ : syracuseStep 3169049 = 2376787) B2376787
theorem B2112699 : Blo 2111435 2112699 := bstep (se 1 (by rfl) ⟨1584524, by rfl⟩ : syracuseStep 2112699 = 3169049) B3169049
theorem B2747353 : Blo 2111435 2747353 := bbase (se 2 (by rfl) ⟨1030257, by rfl⟩ : syracuseStep 2747353 = 2060515) (by norm_num)
theorem B3663137 : Blo 2111435 3663137 := bstep (se 2 (by rfl) ⟨1373676, by rfl⟩ : syracuseStep 3663137 = 2747353) B2747353
theorem B2442091 : Blo 2111435 2442091 := bstep (se 1 (by rfl) ⟨1831568, by rfl⟩ : syracuseStep 2442091 = 3663137) B3663137
theorem B3256121 : Blo 2111435 3256121 := bstep (se 2 (by rfl) ⟨1221045, by rfl⟩ : syracuseStep 3256121 = 2442091) B2442091
theorem B2170747 : Blo 2111435 2170747 := bstep (se 1 (by rfl) ⟨1628060, by rfl⟩ : syracuseStep 2170747 = 3256121) B3256121
theorem B2894329 : Blo 2111435 2894329 := bstep (se 2 (by rfl) ⟨1085373, by rfl⟩ : syracuseStep 2894329 = 2170747) B2170747
theorem B3859105 : Blo 2111435 3859105 := bstep (se 2 (by rfl) ⟨1447164, by rfl⟩ : syracuseStep 3859105 = 2894329) B2894329
theorem B5145473 : Blo 2111435 5145473 := bstep (se 2 (by rfl) ⟨1929552, by rfl⟩ : syracuseStep 5145473 = 3859105) B3859105
theorem B3430315 : Blo 2111435 3430315 := bstep (se 1 (by rfl) ⟨2572736, by rfl⟩ : syracuseStep 3430315 = 5145473) B5145473
theorem B18295013 : Blo 2111435 18295013 := bstep (se 4 (by rfl) ⟨1715157, by rfl⟩ : syracuseStep 18295013 = 3430315) B3430315
theorem B12196675 : Blo 2111435 12196675 := bstep (se 1 (by rfl) ⟨9147506, by rfl⟩ : syracuseStep 12196675 = 18295013) B18295013
theorem B65048933 : Blo 2111435 65048933 := bstep (se 4 (by rfl) ⟨6098337, by rfl⟩ : syracuseStep 65048933 = 12196675) B12196675
theorem B43365955 : Blo 2111435 43365955 := bstep (se 1 (by rfl) ⟨32524466, by rfl⟩ : syracuseStep 43365955 = 65048933) B65048933
theorem B57821273 : Blo 2111435 57821273 := bstep (se 2 (by rfl) ⟨21682977, by rfl⟩ : syracuseStep 57821273 = 43365955) B43365955
theorem B38547515 : Blo 2111435 38547515 := bstep (se 1 (by rfl) ⟨28910636, by rfl⟩ : syracuseStep 38547515 = 57821273) B57821273
theorem B25698343 : Blo 2111435 25698343 := bstep (se 1 (by rfl) ⟨19273757, by rfl⟩ : syracuseStep 25698343 = 38547515) B38547515
theorem B34264457 : Blo 2111435 34264457 := bstep (se 2 (by rfl) ⟨12849171, by rfl⟩ : syracuseStep 34264457 = 25698343) B25698343
theorem B22842971 : Blo 2111435 22842971 := bstep (se 1 (by rfl) ⟨17132228, by rfl⟩ : syracuseStep 22842971 = 34264457) B34264457
theorem B15228647 : Blo 2111435 15228647 := bstep (se 1 (by rfl) ⟨11421485, by rfl⟩ : syracuseStep 15228647 = 22842971) B22842971
theorem B10152431 : Blo 2111435 10152431 := bstep (se 1 (by rfl) ⟨7614323, by rfl⟩ : syracuseStep 10152431 = 15228647) B15228647
theorem B6768287 : Blo 2111435 6768287 := bstep (se 1 (by rfl) ⟨5076215, by rfl⟩ : syracuseStep 6768287 = 10152431) B10152431
theorem B4512191 : Blo 2111435 4512191 := bstep (se 1 (by rfl) ⟨3384143, by rfl⟩ : syracuseStep 4512191 = 6768287) B6768287
theorem B12032509 : Blo 2111435 12032509 := bstep (se 3 (by rfl) ⟨2256095, by rfl⟩ : syracuseStep 12032509 = 4512191) B4512191
theorem B16043345 : Blo 2111435 16043345 := bstep (se 2 (by rfl) ⟨6016254, by rfl⟩ : syracuseStep 16043345 = 12032509) B12032509
theorem B10695563 : Blo 2111435 10695563 := bstep (se 1 (by rfl) ⟨8021672, by rfl⟩ : syracuseStep 10695563 = 16043345) B16043345
theorem B7130375 : Blo 2111435 7130375 := bstep (se 1 (by rfl) ⟨5347781, by rfl⟩ : syracuseStep 7130375 = 10695563) B10695563
theorem B4753583 : Blo 2111435 4753583 := bstep (se 1 (by rfl) ⟨3565187, by rfl⟩ : syracuseStep 4753583 = 7130375) B7130375
theorem B3169055 : Blo 2111435 3169055 := bstep (se 1 (by rfl) ⟨2376791, by rfl⟩ : syracuseStep 3169055 = 4753583) B4753583
theorem B2112703 : Blo 2111435 2112703 := bstep (se 1 (by rfl) ⟨1584527, by rfl⟩ : syracuseStep 2112703 = 3169055) B3169055
theorem B3169061 : Blo 2111435 3169061 := bbase (se 4 (by rfl) ⟨297099, by rfl⟩ : syracuseStep 3169061 = 594199) (by norm_num)
theorem B2112707 : Blo 2111435 2112707 := bstep (se 1 (by rfl) ⟨1584530, by rfl⟩ : syracuseStep 2112707 = 3169061) B3169061
theorem B2673901 : Blo 2111435 2673901 := bbase (se 3 (by rfl) ⟨501356, by rfl⟩ : syracuseStep 2673901 = 1002713) (by norm_num)
theorem B3565201 : Blo 2111435 3565201 := bstep (se 2 (by rfl) ⟨1336950, by rfl⟩ : syracuseStep 3565201 = 2673901) B2673901
theorem B4753601 : Blo 2111435 4753601 := bstep (se 2 (by rfl) ⟨1782600, by rfl⟩ : syracuseStep 4753601 = 3565201) B3565201
theorem B3169067 : Blo 2111435 3169067 := bstep (se 1 (by rfl) ⟨2376800, by rfl⟩ : syracuseStep 3169067 = 4753601) B4753601
theorem B2112711 : Blo 2111435 2112711 := bstep (se 1 (by rfl) ⟨1584533, by rfl⟩ : syracuseStep 2112711 = 3169067) B3169067
theorem B2376805 : Blo 2111435 2376805 := bbase (se 4 (by rfl) ⟨222825, by rfl⟩ : syracuseStep 2376805 = 445651) (by norm_num)
theorem B3169073 : Blo 2111435 3169073 := bstep (se 2 (by rfl) ⟨1188402, by rfl⟩ : syracuseStep 3169073 = 2376805) B2376805
theorem B2112715 : Blo 2111435 2112715 := bstep (se 1 (by rfl) ⟨1584536, by rfl⟩ : syracuseStep 2112715 = 3169073) B3169073
theorem B2256113 : Blo 2111435 2256113 := bbase (se 2 (by rfl) ⟨846042, by rfl⟩ : syracuseStep 2256113 = 1692085) (by norm_num)
theorem B6016301 : Blo 2111435 6016301 := bstep (se 3 (by rfl) ⟨1128056, by rfl⟩ : syracuseStep 6016301 = 2256113) B2256113
theorem B4010867 : Blo 2111435 4010867 := bstep (se 1 (by rfl) ⟨3008150, by rfl⟩ : syracuseStep 4010867 = 6016301) B6016301
theorem B2673911 : Blo 2111435 2673911 := bstep (se 1 (by rfl) ⟨2005433, by rfl⟩ : syracuseStep 2673911 = 4010867) B4010867
theorem B7130429 : Blo 2111435 7130429 := bstep (se 3 (by rfl) ⟨1336955, by rfl⟩ : syracuseStep 7130429 = 2673911) B2673911
theorem B4753619 : Blo 2111435 4753619 := bstep (se 1 (by rfl) ⟨3565214, by rfl⟩ : syracuseStep 4753619 = 7130429) B7130429
theorem B3169079 : Blo 2111435 3169079 := bstep (se 1 (by rfl) ⟨2376809, by rfl⟩ : syracuseStep 3169079 = 4753619) B4753619
theorem B2112719 : Blo 2111435 2112719 := bstep (se 1 (by rfl) ⟨1584539, by rfl⟩ : syracuseStep 2112719 = 3169079) B3169079
theorem B3169085 : Blo 2111435 3169085 := bbase (se 3 (by rfl) ⟨594203, by rfl⟩ : syracuseStep 3169085 = 1188407) (by norm_num)
theorem B2112723 : Blo 2111435 2112723 := bstep (se 1 (by rfl) ⟨1584542, by rfl⟩ : syracuseStep 2112723 = 3169085) B3169085
theorem B4753637 : Blo 2111435 4753637 := bbase (se 4 (by rfl) ⟨445653, by rfl⟩ : syracuseStep 4753637 = 891307) (by norm_num)
theorem B3169091 : Blo 2111435 3169091 := bstep (se 1 (by rfl) ⟨2376818, by rfl⟩ : syracuseStep 3169091 = 4753637) B4753637
theorem B2112727 : Blo 2111435 2112727 := bstep (se 1 (by rfl) ⟨1584545, by rfl⟩ : syracuseStep 2112727 = 3169091) B3169091
theorem B5347853 : Blo 2111435 5347853 := bbase (se 3 (by rfl) ⟨1002722, by rfl⟩ : syracuseStep 5347853 = 2005445) (by norm_num)
theorem B3565235 : Blo 2111435 3565235 := bstep (se 1 (by rfl) ⟨2673926, by rfl⟩ : syracuseStep 3565235 = 5347853) B5347853
theorem B2376823 : Blo 2111435 2376823 := bstep (se 1 (by rfl) ⟨1782617, by rfl⟩ : syracuseStep 2376823 = 3565235) B3565235
theorem B3169097 : Blo 2111435 3169097 := bstep (se 2 (by rfl) ⟨1188411, by rfl⟩ : syracuseStep 3169097 = 2376823) B2376823
theorem B2112731 : Blo 2111435 2112731 := bstep (se 1 (by rfl) ⟨1584548, by rfl⟩ : syracuseStep 2112731 = 3169097) B3169097
theorem B3008173 : Blo 2111435 3008173 := bbase (se 3 (by rfl) ⟨564032, by rfl⟩ : syracuseStep 3008173 = 1128065) (by norm_num)
theorem B4010897 : Blo 2111435 4010897 := bstep (se 2 (by rfl) ⟨1504086, by rfl⟩ : syracuseStep 4010897 = 3008173) B3008173
theorem B10695725 : Blo 2111435 10695725 := bstep (se 3 (by rfl) ⟨2005448, by rfl⟩ : syracuseStep 10695725 = 4010897) B4010897
theorem B7130483 : Blo 2111435 7130483 := bstep (se 1 (by rfl) ⟨5347862, by rfl⟩ : syracuseStep 7130483 = 10695725) B10695725
theorem B4753655 : Blo 2111435 4753655 := bstep (se 1 (by rfl) ⟨3565241, by rfl⟩ : syracuseStep 4753655 = 7130483) B7130483
theorem B3169103 : Blo 2111435 3169103 := bstep (se 1 (by rfl) ⟨2376827, by rfl⟩ : syracuseStep 3169103 = 4753655) B4753655
theorem B2112735 : Blo 2111435 2112735 := bstep (se 1 (by rfl) ⟨1584551, by rfl⟩ : syracuseStep 2112735 = 3169103) B3169103
theorem B3169109 : Blo 2111435 3169109 := bbase (se 9 (by rfl) ⟨9284, by rfl⟩ : syracuseStep 3169109 = 18569) (by norm_num)
theorem B2112739 : Blo 2111435 2112739 := bstep (se 1 (by rfl) ⟨1584554, by rfl⟩ : syracuseStep 2112739 = 3169109) B3169109
theorem B4512277 : Blo 2111435 4512277 := bbase (se 6 (by rfl) ⟨105756, by rfl⟩ : syracuseStep 4512277 = 211513) (by norm_num)
theorem B6016369 : Blo 2111435 6016369 := bstep (se 2 (by rfl) ⟨2256138, by rfl⟩ : syracuseStep 6016369 = 4512277) B4512277
theorem B8021825 : Blo 2111435 8021825 := bstep (se 2 (by rfl) ⟨3008184, by rfl⟩ : syracuseStep 8021825 = 6016369) B6016369
theorem B5347883 : Blo 2111435 5347883 := bstep (se 1 (by rfl) ⟨4010912, by rfl⟩ : syracuseStep 5347883 = 8021825) B8021825
theorem B3565255 : Blo 2111435 3565255 := bstep (se 1 (by rfl) ⟨2673941, by rfl⟩ : syracuseStep 3565255 = 5347883) B5347883
theorem B4753673 : Blo 2111435 4753673 := bstep (se 2 (by rfl) ⟨1782627, by rfl⟩ : syracuseStep 4753673 = 3565255) B3565255
theorem B3169115 : Blo 2111435 3169115 := bstep (se 1 (by rfl) ⟨2376836, by rfl⟩ : syracuseStep 3169115 = 4753673) B4753673
theorem B2112743 : Blo 2111435 2112743 := bstep (se 1 (by rfl) ⟨1584557, by rfl⟩ : syracuseStep 2112743 = 3169115) B3169115
theorem B2376841 : Blo 2111435 2376841 := bbase (se 2 (by rfl) ⟨891315, by rfl⟩ : syracuseStep 2376841 = 1782631) (by norm_num)
theorem B3169121 : Blo 2111435 3169121 := bstep (se 2 (by rfl) ⟨1188420, by rfl⟩ : syracuseStep 3169121 = 2376841) B2376841
theorem B2112747 : Blo 2111435 2112747 := bstep (se 1 (by rfl) ⟨1584560, by rfl⟩ : syracuseStep 2112747 = 3169121) B3169121
theorem B40610645 : Blo 2111435 40610645 := bbase (se 9 (by rfl) ⟨118976, by rfl⟩ : syracuseStep 40610645 = 237953) (by norm_num)
theorem B27073763 : Blo 2111435 27073763 := bstep (se 1 (by rfl) ⟨20305322, by rfl⟩ : syracuseStep 27073763 = 40610645) B40610645
theorem B18049175 : Blo 2111435 18049175 := bstep (se 1 (by rfl) ⟨13536881, by rfl⟩ : syracuseStep 18049175 = 27073763) B27073763
theorem B12032783 : Blo 2111435 12032783 := bstep (se 1 (by rfl) ⟨9024587, by rfl⟩ : syracuseStep 12032783 = 18049175) B18049175
theorem B8021855 : Blo 2111435 8021855 := bstep (se 1 (by rfl) ⟨6016391, by rfl⟩ : syracuseStep 8021855 = 12032783) B12032783
theorem B5347903 : Blo 2111435 5347903 := bstep (se 1 (by rfl) ⟨4010927, by rfl⟩ : syracuseStep 5347903 = 8021855) B8021855
theorem B7130537 : Blo 2111435 7130537 := bstep (se 2 (by rfl) ⟨2673951, by rfl⟩ : syracuseStep 7130537 = 5347903) B5347903
theorem B4753691 : Blo 2111435 4753691 := bstep (se 1 (by rfl) ⟨3565268, by rfl⟩ : syracuseStep 4753691 = 7130537) B7130537
theorem B3169127 : Blo 2111435 3169127 := bstep (se 1 (by rfl) ⟨2376845, by rfl⟩ : syracuseStep 3169127 = 4753691) B4753691
theorem B2112751 : Blo 2111435 2112751 := bstep (se 1 (by rfl) ⟨1584563, by rfl⟩ : syracuseStep 2112751 = 3169127) B3169127
theorem B3169133 : Blo 2111435 3169133 := bbase (se 3 (by rfl) ⟨594212, by rfl⟩ : syracuseStep 3169133 = 1188425) (by norm_num)
theorem B2112755 : Blo 2111435 2112755 := bstep (se 1 (by rfl) ⟨1584566, by rfl⟩ : syracuseStep 2112755 = 3169133) B3169133
theorem B4753709 : Blo 2111435 4753709 := bbase (se 3 (by rfl) ⟨891320, by rfl⟩ : syracuseStep 4753709 = 1782641) (by norm_num)
theorem B3169139 : Blo 2111435 3169139 := bstep (se 1 (by rfl) ⟨2376854, by rfl⟩ : syracuseStep 3169139 = 4753709) B4753709
theorem B2112759 : Blo 2111435 2112759 := bstep (se 1 (by rfl) ⟨1584569, by rfl⟩ : syracuseStep 2112759 = 3169139) B3169139
theorem B9637157 : Blo 2111435 9637157 := bbase (se 4 (by rfl) ⟨903483, by rfl⟩ : syracuseStep 9637157 = 1806967) (by norm_num)
theorem B6424771 : Blo 2111435 6424771 := bstep (se 1 (by rfl) ⟨4818578, by rfl⟩ : syracuseStep 6424771 = 9637157) B9637157
theorem B8566361 : Blo 2111435 8566361 := bstep (se 2 (by rfl) ⟨3212385, by rfl⟩ : syracuseStep 8566361 = 6424771) B6424771
theorem B5710907 : Blo 2111435 5710907 := bstep (se 1 (by rfl) ⟨4283180, by rfl⟩ : syracuseStep 5710907 = 8566361) B8566361
theorem B3807271 : Blo 2111435 3807271 := bstep (se 1 (by rfl) ⟨2855453, by rfl⟩ : syracuseStep 3807271 = 5710907) B5710907
theorem B5076361 : Blo 2111435 5076361 := bstep (se 2 (by rfl) ⟨1903635, by rfl⟩ : syracuseStep 5076361 = 3807271) B3807271
theorem B6768481 : Blo 2111435 6768481 := bstep (se 2 (by rfl) ⟨2538180, by rfl⟩ : syracuseStep 6768481 = 5076361) B5076361
theorem B9024641 : Blo 2111435 9024641 := bstep (se 2 (by rfl) ⟨3384240, by rfl⟩ : syracuseStep 9024641 = 6768481) B6768481
theorem B6016427 : Blo 2111435 6016427 := bstep (se 1 (by rfl) ⟨4512320, by rfl⟩ : syracuseStep 6016427 = 9024641) B9024641
theorem B4010951 : Blo 2111435 4010951 := bstep (se 1 (by rfl) ⟨3008213, by rfl⟩ : syracuseStep 4010951 = 6016427) B6016427
theorem B2673967 : Blo 2111435 2673967 := bstep (se 1 (by rfl) ⟨2005475, by rfl⟩ : syracuseStep 2673967 = 4010951) B4010951
theorem B3565289 : Blo 2111435 3565289 := bstep (se 2 (by rfl) ⟨1336983, by rfl⟩ : syracuseStep 3565289 = 2673967) B2673967
theorem B2376859 : Blo 2111435 2376859 := bstep (se 1 (by rfl) ⟨1782644, by rfl⟩ : syracuseStep 2376859 = 3565289) B3565289
theorem B3169145 : Blo 2111435 3169145 := bstep (se 2 (by rfl) ⟨1188429, by rfl⟩ : syracuseStep 3169145 = 2376859) B2376859
theorem B2112763 : Blo 2111435 2112763 := bstep (se 1 (by rfl) ⟨1584572, by rfl⟩ : syracuseStep 2112763 = 3169145) B3169145
theorem B8566373 : Blo 2111435 8566373 := bbase (se 4 (by rfl) ⟨803097, by rfl⟩ : syracuseStep 8566373 = 1606195) (by norm_num)
theorem B5710915 : Blo 2111435 5710915 := bstep (se 1 (by rfl) ⟨4283186, by rfl⟩ : syracuseStep 5710915 = 8566373) B8566373
theorem B30458213 : Blo 2111435 30458213 := bstep (se 4 (by rfl) ⟨2855457, by rfl⟩ : syracuseStep 30458213 = 5710915) B5710915
theorem B20305475 : Blo 2111435 20305475 := bstep (se 1 (by rfl) ⟨15229106, by rfl⟩ : syracuseStep 20305475 = 30458213) B30458213
theorem B13536983 : Blo 2111435 13536983 := bstep (se 1 (by rfl) ⟨10152737, by rfl⟩ : syracuseStep 13536983 = 20305475) B20305475
theorem B36098621 : Blo 2111435 36098621 := bstep (se 3 (by rfl) ⟨6768491, by rfl⟩ : syracuseStep 36098621 = 13536983) B13536983
theorem B24065747 : Blo 2111435 24065747 := bstep (se 1 (by rfl) ⟨18049310, by rfl⟩ : syracuseStep 24065747 = 36098621) B36098621
theorem B16043831 : Blo 2111435 16043831 := bstep (se 1 (by rfl) ⟨12032873, by rfl⟩ : syracuseStep 16043831 = 24065747) B24065747
theorem B10695887 : Blo 2111435 10695887 := bstep (se 1 (by rfl) ⟨8021915, by rfl⟩ : syracuseStep 10695887 = 16043831) B16043831
theorem B7130591 : Blo 2111435 7130591 := bstep (se 1 (by rfl) ⟨5347943, by rfl⟩ : syracuseStep 7130591 = 10695887) B10695887
theorem B4753727 : Blo 2111435 4753727 := bstep (se 1 (by rfl) ⟨3565295, by rfl⟩ : syracuseStep 4753727 = 7130591) B7130591
theorem B3169151 : Blo 2111435 3169151 := bstep (se 1 (by rfl) ⟨2376863, by rfl⟩ : syracuseStep 3169151 = 4753727) B4753727
theorem B2112767 : Blo 2111435 2112767 := bstep (se 1 (by rfl) ⟨1584575, by rfl⟩ : syracuseStep 2112767 = 3169151) B3169151
theorem B3169157 : Blo 2111435 3169157 := bbase (se 4 (by rfl) ⟨297108, by rfl⟩ : syracuseStep 3169157 = 594217) (by norm_num)
theorem B2112771 : Blo 2111435 2112771 := bstep (se 1 (by rfl) ⟨1584578, by rfl⟩ : syracuseStep 2112771 = 3169157) B3169157
theorem B3565309 : Blo 2111435 3565309 := bbase (se 3 (by rfl) ⟨668495, by rfl⟩ : syracuseStep 3565309 = 1336991) (by norm_num)
theorem B4753745 : Blo 2111435 4753745 := bstep (se 2 (by rfl) ⟨1782654, by rfl⟩ : syracuseStep 4753745 = 3565309) B3565309
theorem B3169163 : Blo 2111435 3169163 := bstep (se 1 (by rfl) ⟨2376872, by rfl⟩ : syracuseStep 3169163 = 4753745) B4753745
theorem B2112775 : Blo 2111435 2112775 := bstep (se 1 (by rfl) ⟨1584581, by rfl⟩ : syracuseStep 2112775 = 3169163) B3169163
theorem B2376877 : Blo 2111435 2376877 := bbase (se 3 (by rfl) ⟨445664, by rfl⟩ : syracuseStep 2376877 = 891329) (by norm_num)
theorem B3169169 : Blo 2111435 3169169 := bstep (se 2 (by rfl) ⟨1188438, by rfl⟩ : syracuseStep 3169169 = 2376877) B2376877
theorem B2112779 : Blo 2111435 2112779 := bstep (se 1 (by rfl) ⟨1584584, by rfl⟩ : syracuseStep 2112779 = 3169169) B3169169
theorem B7130645 : Blo 2111435 7130645 := bbase (se 6 (by rfl) ⟨167124, by rfl⟩ : syracuseStep 7130645 = 334249) (by norm_num)
theorem B4753763 : Blo 2111435 4753763 := bstep (se 1 (by rfl) ⟨3565322, by rfl⟩ : syracuseStep 4753763 = 7130645) B7130645
theorem B3169175 : Blo 2111435 3169175 := bstep (se 1 (by rfl) ⟨2376881, by rfl⟩ : syracuseStep 3169175 = 4753763) B4753763
theorem B2112783 : Blo 2111435 2112783 := bstep (se 1 (by rfl) ⟨1584587, by rfl⟩ : syracuseStep 2112783 = 3169175) B3169175
theorem B3169181 : Blo 2111435 3169181 := bbase (se 3 (by rfl) ⟨594221, by rfl⟩ : syracuseStep 3169181 = 1188443) (by norm_num)
theorem B2112787 : Blo 2111435 2112787 := bstep (se 1 (by rfl) ⟨1584590, by rfl⟩ : syracuseStep 2112787 = 3169181) B3169181
theorem B4753781 : Blo 2111435 4753781 := bbase (se 5 (by rfl) ⟨222833, by rfl⟩ : syracuseStep 4753781 = 445667) (by norm_num)
theorem B3169187 : Blo 2111435 3169187 := bstep (se 1 (by rfl) ⟨2376890, by rfl⟩ : syracuseStep 3169187 = 4753781) B4753781
theorem B2112791 : Blo 2111435 2112791 := bstep (se 1 (by rfl) ⟨1584593, by rfl⟩ : syracuseStep 2112791 = 3169187) B3169187
theorem B5076437 : Blo 2111435 5076437 := bbase (se 7 (by rfl) ⟨59489, by rfl⟩ : syracuseStep 5076437 = 118979) (by norm_num)
theorem B13537165 : Blo 2111435 13537165 := bstep (se 3 (by rfl) ⟨2538218, by rfl⟩ : syracuseStep 13537165 = 5076437) B5076437
theorem B18049553 : Blo 2111435 18049553 := bstep (se 2 (by rfl) ⟨6768582, by rfl⟩ : syracuseStep 18049553 = 13537165) B13537165
theorem B12033035 : Blo 2111435 12033035 := bstep (se 1 (by rfl) ⟨9024776, by rfl⟩ : syracuseStep 12033035 = 18049553) B18049553
theorem B8022023 : Blo 2111435 8022023 := bstep (se 1 (by rfl) ⟨6016517, by rfl⟩ : syracuseStep 8022023 = 12033035) B12033035
theorem B5348015 : Blo 2111435 5348015 := bstep (se 1 (by rfl) ⟨4011011, by rfl⟩ : syracuseStep 5348015 = 8022023) B8022023
theorem B3565343 : Blo 2111435 3565343 := bstep (se 1 (by rfl) ⟨2674007, by rfl⟩ : syracuseStep 3565343 = 5348015) B5348015
theorem B2376895 : Blo 2111435 2376895 := bstep (se 1 (by rfl) ⟨1782671, by rfl⟩ : syracuseStep 2376895 = 3565343) B3565343
theorem B3169193 : Blo 2111435 3169193 := bstep (se 2 (by rfl) ⟨1188447, by rfl⟩ : syracuseStep 3169193 = 2376895) B2376895
theorem B2112795 : Blo 2111435 2112795 := bstep (se 1 (by rfl) ⟨1584596, by rfl⟩ : syracuseStep 2112795 = 3169193) B3169193
theorem B8022037 : Blo 2111435 8022037 := bbase (se 6 (by rfl) ⟨188016, by rfl⟩ : syracuseStep 8022037 = 376033) (by norm_num)
theorem B10696049 : Blo 2111435 10696049 := bstep (se 2 (by rfl) ⟨4011018, by rfl⟩ : syracuseStep 10696049 = 8022037) B8022037
theorem B7130699 : Blo 2111435 7130699 := bstep (se 1 (by rfl) ⟨5348024, by rfl⟩ : syracuseStep 7130699 = 10696049) B10696049
theorem B4753799 : Blo 2111435 4753799 := bstep (se 1 (by rfl) ⟨3565349, by rfl⟩ : syracuseStep 4753799 = 7130699) B7130699
theorem B3169199 : Blo 2111435 3169199 := bstep (se 1 (by rfl) ⟨2376899, by rfl⟩ : syracuseStep 3169199 = 4753799) B4753799
theorem B2112799 : Blo 2111435 2112799 := bstep (se 1 (by rfl) ⟨1584599, by rfl⟩ : syracuseStep 2112799 = 3169199) B3169199
theorem B3169205 : Blo 2111435 3169205 := bbase (se 5 (by rfl) ⟨148556, by rfl⟩ : syracuseStep 3169205 = 297113) (by norm_num)
theorem B2112803 : Blo 2111435 2112803 := bstep (se 1 (by rfl) ⟨1584602, by rfl⟩ : syracuseStep 2112803 = 3169205) B3169205
theorem B5348045 : Blo 2111435 5348045 := bbase (se 3 (by rfl) ⟨1002758, by rfl⟩ : syracuseStep 5348045 = 2005517) (by norm_num)
theorem B3565363 : Blo 2111435 3565363 := bstep (se 1 (by rfl) ⟨2674022, by rfl⟩ : syracuseStep 3565363 = 5348045) B5348045
theorem B4753817 : Blo 2111435 4753817 := bstep (se 2 (by rfl) ⟨1782681, by rfl⟩ : syracuseStep 4753817 = 3565363) B3565363
theorem B3169211 : Blo 2111435 3169211 := bstep (se 1 (by rfl) ⟨2376908, by rfl⟩ : syracuseStep 3169211 = 4753817) B4753817
theorem B2112807 : Blo 2111435 2112807 := bstep (se 1 (by rfl) ⟨1584605, by rfl⟩ : syracuseStep 2112807 = 3169211) B3169211
theorem B2376913 : Blo 2111435 2376913 := bbase (se 2 (by rfl) ⟨891342, by rfl⟩ : syracuseStep 2376913 = 1782685) (by norm_num)
theorem B3169217 : Blo 2111435 3169217 := bstep (se 2 (by rfl) ⟨1188456, by rfl⟩ : syracuseStep 3169217 = 2376913) B2376913
theorem B2112811 : Blo 2111435 2112811 := bstep (se 1 (by rfl) ⟨1584608, by rfl⟩ : syracuseStep 2112811 = 3169217) B3169217
theorem B4283285 : Blo 2111435 4283285 := bbase (se 6 (by rfl) ⟨100389, by rfl⟩ : syracuseStep 4283285 = 200779) (by norm_num)
theorem B11422093 : Blo 2111435 11422093 := bstep (se 3 (by rfl) ⟨2141642, by rfl⟩ : syracuseStep 11422093 = 4283285) B4283285
theorem B15229457 : Blo 2111435 15229457 := bstep (se 2 (by rfl) ⟨5711046, by rfl⟩ : syracuseStep 15229457 = 11422093) B11422093
theorem B10152971 : Blo 2111435 10152971 := bstep (se 1 (by rfl) ⟨7614728, by rfl⟩ : syracuseStep 10152971 = 15229457) B15229457
theorem B6768647 : Blo 2111435 6768647 := bstep (se 1 (by rfl) ⟨5076485, by rfl⟩ : syracuseStep 6768647 = 10152971) B10152971
theorem B4512431 : Blo 2111435 4512431 := bstep (se 1 (by rfl) ⟨3384323, by rfl⟩ : syracuseStep 4512431 = 6768647) B6768647
theorem B3008287 : Blo 2111435 3008287 := bstep (se 1 (by rfl) ⟨2256215, by rfl⟩ : syracuseStep 3008287 = 4512431) B4512431
theorem B4011049 : Blo 2111435 4011049 := bstep (se 2 (by rfl) ⟨1504143, by rfl⟩ : syracuseStep 4011049 = 3008287) B3008287
theorem B5348065 : Blo 2111435 5348065 := bstep (se 2 (by rfl) ⟨2005524, by rfl⟩ : syracuseStep 5348065 = 4011049) B4011049
theorem B7130753 : Blo 2111435 7130753 := bstep (se 2 (by rfl) ⟨2674032, by rfl⟩ : syracuseStep 7130753 = 5348065) B5348065
theorem B4753835 : Blo 2111435 4753835 := bstep (se 1 (by rfl) ⟨3565376, by rfl⟩ : syracuseStep 4753835 = 7130753) B7130753
theorem B3169223 : Blo 2111435 3169223 := bstep (se 1 (by rfl) ⟨2376917, by rfl⟩ : syracuseStep 3169223 = 4753835) B4753835
theorem B2112815 : Blo 2111435 2112815 := bstep (se 1 (by rfl) ⟨1584611, by rfl⟩ : syracuseStep 2112815 = 3169223) B3169223
theorem B3169229 : Blo 2111435 3169229 := bbase (se 3 (by rfl) ⟨594230, by rfl⟩ : syracuseStep 3169229 = 1188461) (by norm_num)
theorem B2112819 : Blo 2111435 2112819 := bstep (se 1 (by rfl) ⟨1584614, by rfl⟩ : syracuseStep 2112819 = 3169229) B3169229
theorem B4753853 : Blo 2111435 4753853 := bbase (se 3 (by rfl) ⟨891347, by rfl⟩ : syracuseStep 4753853 = 1782695) (by norm_num)
theorem B3169235 : Blo 2111435 3169235 := bstep (se 1 (by rfl) ⟨2376926, by rfl⟩ : syracuseStep 3169235 = 4753853) B4753853
theorem B2112823 : Blo 2111435 2112823 := bstep (se 1 (by rfl) ⟨1584617, by rfl⟩ : syracuseStep 2112823 = 3169235) B3169235
theorem B3565397 : Blo 2111435 3565397 := bbase (se 9 (by rfl) ⟨10445, by rfl⟩ : syracuseStep 3565397 = 20891) (by norm_num)
theorem B2376931 : Blo 2111435 2376931 := bstep (se 1 (by rfl) ⟨1782698, by rfl⟩ : syracuseStep 2376931 = 3565397) B3565397
theorem B3169241 : Blo 2111435 3169241 := bstep (se 2 (by rfl) ⟨1188465, by rfl⟩ : syracuseStep 3169241 = 2376931) B2376931
theorem B2112827 : Blo 2111435 2112827 := bstep (se 1 (by rfl) ⟨1584620, by rfl⟩ : syracuseStep 2112827 = 3169241) B3169241
theorem B4283317 : Blo 2111435 4283317 := bbase (se 5 (by rfl) ⟨200780, by rfl⟩ : syracuseStep 4283317 = 401561) (by norm_num)
theorem B5711089 : Blo 2111435 5711089 := bstep (se 2 (by rfl) ⟨2141658, by rfl⟩ : syracuseStep 5711089 = 4283317) B4283317
theorem B7614785 : Blo 2111435 7614785 := bstep (se 2 (by rfl) ⟨2855544, by rfl⟩ : syracuseStep 7614785 = 5711089) B5711089
theorem B5076523 : Blo 2111435 5076523 := bstep (se 1 (by rfl) ⟨3807392, by rfl⟩ : syracuseStep 5076523 = 7614785) B7614785
theorem B6768697 : Blo 2111435 6768697 := bstep (se 2 (by rfl) ⟨2538261, by rfl⟩ : syracuseStep 6768697 = 5076523) B5076523
theorem B9024929 : Blo 2111435 9024929 := bstep (se 2 (by rfl) ⟨3384348, by rfl⟩ : syracuseStep 9024929 = 6768697) B6768697
theorem B6016619 : Blo 2111435 6016619 := bstep (se 1 (by rfl) ⟨4512464, by rfl⟩ : syracuseStep 6016619 = 9024929) B9024929
theorem B16044317 : Blo 2111435 16044317 := bstep (se 3 (by rfl) ⟨3008309, by rfl⟩ : syracuseStep 16044317 = 6016619) B6016619
theorem B10696211 : Blo 2111435 10696211 := bstep (se 1 (by rfl) ⟨8022158, by rfl⟩ : syracuseStep 10696211 = 16044317) B16044317
theorem B7130807 : Blo 2111435 7130807 := bstep (se 1 (by rfl) ⟨5348105, by rfl⟩ : syracuseStep 7130807 = 10696211) B10696211
theorem B4753871 : Blo 2111435 4753871 := bstep (se 1 (by rfl) ⟨3565403, by rfl⟩ : syracuseStep 4753871 = 7130807) B7130807
theorem B3169247 : Blo 2111435 3169247 := bstep (se 1 (by rfl) ⟨2376935, by rfl⟩ : syracuseStep 3169247 = 4753871) B4753871
theorem B2112831 : Blo 2111435 2112831 := bstep (se 1 (by rfl) ⟨1584623, by rfl⟩ : syracuseStep 2112831 = 3169247) B3169247
theorem B3169253 : Blo 2111435 3169253 := bbase (se 4 (by rfl) ⟨297117, by rfl⟩ : syracuseStep 3169253 = 594235) (by norm_num)
theorem B2112835 : Blo 2111435 2112835 := bstep (se 1 (by rfl) ⟨1584626, by rfl⟩ : syracuseStep 2112835 = 3169253) B3169253
theorem B9024965 : Blo 2111435 9024965 := bbase (se 4 (by rfl) ⟨846090, by rfl⟩ : syracuseStep 9024965 = 1692181) (by norm_num)
theorem B6016643 : Blo 2111435 6016643 := bstep (se 1 (by rfl) ⟨4512482, by rfl⟩ : syracuseStep 6016643 = 9024965) B9024965
theorem B4011095 : Blo 2111435 4011095 := bstep (se 1 (by rfl) ⟨3008321, by rfl⟩ : syracuseStep 4011095 = 6016643) B6016643
theorem B2674063 : Blo 2111435 2674063 := bstep (se 1 (by rfl) ⟨2005547, by rfl⟩ : syracuseStep 2674063 = 4011095) B4011095
theorem B3565417 : Blo 2111435 3565417 := bstep (se 2 (by rfl) ⟨1337031, by rfl⟩ : syracuseStep 3565417 = 2674063) B2674063
theorem B4753889 : Blo 2111435 4753889 := bstep (se 2 (by rfl) ⟨1782708, by rfl⟩ : syracuseStep 4753889 = 3565417) B3565417
theorem B3169259 : Blo 2111435 3169259 := bstep (se 1 (by rfl) ⟨2376944, by rfl⟩ : syracuseStep 3169259 = 4753889) B4753889
theorem B2112839 : Blo 2111435 2112839 := bstep (se 1 (by rfl) ⟨1584629, by rfl⟩ : syracuseStep 2112839 = 3169259) B3169259
theorem B2376949 : Blo 2111435 2376949 := bbase (se 5 (by rfl) ⟨111419, by rfl⟩ : syracuseStep 2376949 = 222839) (by norm_num)
theorem B3169265 : Blo 2111435 3169265 := bstep (se 2 (by rfl) ⟨1188474, by rfl⟩ : syracuseStep 3169265 = 2376949) B2376949
theorem B2112843 : Blo 2111435 2112843 := bstep (se 1 (by rfl) ⟨1584632, by rfl⟩ : syracuseStep 2112843 = 3169265) B3169265
theorem B2674073 : Blo 2111435 2674073 := bbase (se 2 (by rfl) ⟨1002777, by rfl⟩ : syracuseStep 2674073 = 2005555) (by norm_num)
theorem B7130861 : Blo 2111435 7130861 := bstep (se 3 (by rfl) ⟨1337036, by rfl⟩ : syracuseStep 7130861 = 2674073) B2674073
theorem B4753907 : Blo 2111435 4753907 := bstep (se 1 (by rfl) ⟨3565430, by rfl⟩ : syracuseStep 4753907 = 7130861) B7130861
theorem B3169271 : Blo 2111435 3169271 := bstep (se 1 (by rfl) ⟨2376953, by rfl⟩ : syracuseStep 3169271 = 4753907) B4753907
theorem B2112847 : Blo 2111435 2112847 := bstep (se 1 (by rfl) ⟨1584635, by rfl⟩ : syracuseStep 2112847 = 3169271) B3169271
theorem B3169277 : Blo 2111435 3169277 := bbase (se 3 (by rfl) ⟨594239, by rfl⟩ : syracuseStep 3169277 = 1188479) (by norm_num)
theorem B2112851 : Blo 2111435 2112851 := bstep (se 1 (by rfl) ⟨1584638, by rfl⟩ : syracuseStep 2112851 = 3169277) B3169277
theorem B4753925 : Blo 2111435 4753925 := bbase (se 4 (by rfl) ⟨445680, by rfl⟩ : syracuseStep 4753925 = 891361) (by norm_num)
theorem B3169283 : Blo 2111435 3169283 := bstep (se 1 (by rfl) ⟨2376962, by rfl⟩ : syracuseStep 3169283 = 4753925) B4753925
theorem B2112855 : Blo 2111435 2112855 := bstep (se 1 (by rfl) ⟨1584641, by rfl⟩ : syracuseStep 2112855 = 3169283) B3169283
theorem B4011133 : Blo 2111435 4011133 := bbase (se 3 (by rfl) ⟨752087, by rfl⟩ : syracuseStep 4011133 = 1504175) (by norm_num)
theorem B5348177 : Blo 2111435 5348177 := bstep (se 2 (by rfl) ⟨2005566, by rfl⟩ : syracuseStep 5348177 = 4011133) B4011133
theorem B3565451 : Blo 2111435 3565451 := bstep (se 1 (by rfl) ⟨2674088, by rfl⟩ : syracuseStep 3565451 = 5348177) B5348177
theorem B2376967 : Blo 2111435 2376967 := bstep (se 1 (by rfl) ⟨1782725, by rfl⟩ : syracuseStep 2376967 = 3565451) B3565451
theorem B3169289 : Blo 2111435 3169289 := bstep (se 2 (by rfl) ⟨1188483, by rfl⟩ : syracuseStep 3169289 = 2376967) B2376967
theorem B2112859 : Blo 2111435 2112859 := bstep (se 1 (by rfl) ⟨1584644, by rfl⟩ : syracuseStep 2112859 = 3169289) B3169289
theorem B10696373 : Blo 2111435 10696373 := bbase (se 5 (by rfl) ⟨501392, by rfl⟩ : syracuseStep 10696373 = 1002785) (by norm_num)
theorem B7130915 : Blo 2111435 7130915 := bstep (se 1 (by rfl) ⟨5348186, by rfl⟩ : syracuseStep 7130915 = 10696373) B10696373
theorem B4753943 : Blo 2111435 4753943 := bstep (se 1 (by rfl) ⟨3565457, by rfl⟩ : syracuseStep 4753943 = 7130915) B7130915
theorem B3169295 : Blo 2111435 3169295 := bstep (se 1 (by rfl) ⟨2376971, by rfl⟩ : syracuseStep 3169295 = 4753943) B4753943
theorem B2112863 : Blo 2111435 2112863 := bstep (se 1 (by rfl) ⟨1584647, by rfl⟩ : syracuseStep 2112863 = 3169295) B3169295
theorem B3169301 : Blo 2111435 3169301 := bbase (se 6 (by rfl) ⟨74280, by rfl⟩ : syracuseStep 3169301 = 148561) (by norm_num)
theorem B2112867 : Blo 2111435 2112867 := bstep (se 1 (by rfl) ⟨1584650, by rfl⟩ : syracuseStep 2112867 = 3169301) B3169301
theorem B3212549 : Blo 2111435 3212549 := bbase (se 4 (by rfl) ⟨301176, by rfl⟩ : syracuseStep 3212549 = 602353) (by norm_num)
theorem B2141699 : Blo 2111435 2141699 := bstep (se 1 (by rfl) ⟨1606274, by rfl⟩ : syracuseStep 2141699 = 3212549) B3212549
theorem B5711197 : Blo 2111435 5711197 := bstep (se 3 (by rfl) ⟨1070849, by rfl⟩ : syracuseStep 5711197 = 2141699) B2141699
theorem B7614929 : Blo 2111435 7614929 := bstep (se 2 (by rfl) ⟨2855598, by rfl⟩ : syracuseStep 7614929 = 5711197) B5711197
theorem B20306477 : Blo 2111435 20306477 := bstep (se 3 (by rfl) ⟨3807464, by rfl⟩ : syracuseStep 20306477 = 7614929) B7614929
theorem B13537651 : Blo 2111435 13537651 := bstep (se 1 (by rfl) ⟨10153238, by rfl⟩ : syracuseStep 13537651 = 20306477) B20306477
theorem B18050201 : Blo 2111435 18050201 := bstep (se 2 (by rfl) ⟨6768825, by rfl⟩ : syracuseStep 18050201 = 13537651) B13537651
theorem B12033467 : Blo 2111435 12033467 := bstep (se 1 (by rfl) ⟨9025100, by rfl⟩ : syracuseStep 12033467 = 18050201) B18050201
theorem B8022311 : Blo 2111435 8022311 := bstep (se 1 (by rfl) ⟨6016733, by rfl⟩ : syracuseStep 8022311 = 12033467) B12033467
theorem B5348207 : Blo 2111435 5348207 := bstep (se 1 (by rfl) ⟨4011155, by rfl⟩ : syracuseStep 5348207 = 8022311) B8022311
theorem B3565471 : Blo 2111435 3565471 := bstep (se 1 (by rfl) ⟨2674103, by rfl⟩ : syracuseStep 3565471 = 5348207) B5348207
theorem B4753961 : Blo 2111435 4753961 := bstep (se 2 (by rfl) ⟨1782735, by rfl⟩ : syracuseStep 4753961 = 3565471) B3565471
theorem B3169307 : Blo 2111435 3169307 := bstep (se 1 (by rfl) ⟨2376980, by rfl⟩ : syracuseStep 3169307 = 4753961) B4753961
theorem B2112871 : Blo 2111435 2112871 := bstep (se 1 (by rfl) ⟨1584653, by rfl⟩ : syracuseStep 2112871 = 3169307) B3169307
theorem B2376985 : Blo 2111435 2376985 := bbase (se 2 (by rfl) ⟨891369, by rfl⟩ : syracuseStep 2376985 = 1782739) (by norm_num)
theorem B3169313 : Blo 2111435 3169313 := bstep (se 2 (by rfl) ⟨1188492, by rfl⟩ : syracuseStep 3169313 = 2376985) B2376985
theorem B2112875 : Blo 2111435 2112875 := bstep (se 1 (by rfl) ⟨1584656, by rfl⟩ : syracuseStep 2112875 = 3169313) B3169313
theorem B8022341 : Blo 2111435 8022341 := bbase (se 4 (by rfl) ⟨752094, by rfl⟩ : syracuseStep 8022341 = 1504189) (by norm_num)
theorem B5348227 : Blo 2111435 5348227 := bstep (se 1 (by rfl) ⟨4011170, by rfl⟩ : syracuseStep 5348227 = 8022341) B8022341
theorem B7130969 : Blo 2111435 7130969 := bstep (se 2 (by rfl) ⟨2674113, by rfl⟩ : syracuseStep 7130969 = 5348227) B5348227
theorem B4753979 : Blo 2111435 4753979 := bstep (se 1 (by rfl) ⟨3565484, by rfl⟩ : syracuseStep 4753979 = 7130969) B7130969
theorem B3169319 : Blo 2111435 3169319 := bstep (se 1 (by rfl) ⟨2376989, by rfl⟩ : syracuseStep 3169319 = 4753979) B4753979
theorem B2112879 : Blo 2111435 2112879 := bstep (se 1 (by rfl) ⟨1584659, by rfl⟩ : syracuseStep 2112879 = 3169319) B3169319
theorem B3169325 : Blo 2111435 3169325 := bbase (se 3 (by rfl) ⟨594248, by rfl⟩ : syracuseStep 3169325 = 1188497) (by norm_num)
theorem B2112883 : Blo 2111435 2112883 := bstep (se 1 (by rfl) ⟨1584662, by rfl⟩ : syracuseStep 2112883 = 3169325) B3169325
theorem B4753997 : Blo 2111435 4753997 := bbase (se 3 (by rfl) ⟨891374, by rfl⟩ : syracuseStep 4753997 = 1782749) (by norm_num)
theorem B3169331 : Blo 2111435 3169331 := bstep (se 1 (by rfl) ⟨2376998, by rfl⟩ : syracuseStep 3169331 = 4753997) B4753997
theorem B2112887 : Blo 2111435 2112887 := bstep (se 1 (by rfl) ⟨1584665, by rfl⟩ : syracuseStep 2112887 = 3169331) B3169331
theorem B2674129 : Blo 2111435 2674129 := bbase (se 2 (by rfl) ⟨1002798, by rfl⟩ : syracuseStep 2674129 = 2005597) (by norm_num)
theorem B3565505 : Blo 2111435 3565505 := bstep (se 2 (by rfl) ⟨1337064, by rfl⟩ : syracuseStep 3565505 = 2674129) B2674129
theorem B2377003 : Blo 2111435 2377003 := bstep (se 1 (by rfl) ⟨1782752, by rfl⟩ : syracuseStep 2377003 = 3565505) B3565505
theorem B3169337 : Blo 2111435 3169337 := bstep (se 2 (by rfl) ⟨1188501, by rfl⟩ : syracuseStep 3169337 = 2377003) B2377003
theorem B2112891 : Blo 2111435 2112891 := bstep (se 1 (by rfl) ⟨1584668, by rfl⟩ : syracuseStep 2112891 = 3169337) B3169337
theorem B5076677 : Blo 2111435 5076677 := bbase (se 4 (by rfl) ⟨475938, by rfl⟩ : syracuseStep 5076677 = 951877) (by norm_num)
theorem B3384451 : Blo 2111435 3384451 := bstep (se 1 (by rfl) ⟨2538338, by rfl⟩ : syracuseStep 3384451 = 5076677) B5076677
theorem B4512601 : Blo 2111435 4512601 := bstep (se 2 (by rfl) ⟨1692225, by rfl⟩ : syracuseStep 4512601 = 3384451) B3384451
theorem B24067205 : Blo 2111435 24067205 := bstep (se 4 (by rfl) ⟨2256300, by rfl⟩ : syracuseStep 24067205 = 4512601) B4512601
theorem B16044803 : Blo 2111435 16044803 := bstep (se 1 (by rfl) ⟨12033602, by rfl⟩ : syracuseStep 16044803 = 24067205) B24067205
theorem B10696535 : Blo 2111435 10696535 := bstep (se 1 (by rfl) ⟨8022401, by rfl⟩ : syracuseStep 10696535 = 16044803) B16044803
theorem B7131023 : Blo 2111435 7131023 := bstep (se 1 (by rfl) ⟨5348267, by rfl⟩ : syracuseStep 7131023 = 10696535) B10696535
theorem B4754015 : Blo 2111435 4754015 := bstep (se 1 (by rfl) ⟨3565511, by rfl⟩ : syracuseStep 4754015 = 7131023) B7131023
theorem B3169343 : Blo 2111435 3169343 := bstep (se 1 (by rfl) ⟨2377007, by rfl⟩ : syracuseStep 3169343 = 4754015) B4754015
theorem B2112895 : Blo 2111435 2112895 := bstep (se 1 (by rfl) ⟨1584671, by rfl⟩ : syracuseStep 2112895 = 3169343) B3169343
theorem B3169349 : Blo 2111435 3169349 := bbase (se 4 (by rfl) ⟨297126, by rfl⟩ : syracuseStep 3169349 = 594253) (by norm_num)
theorem B2112899 : Blo 2111435 2112899 := bstep (se 1 (by rfl) ⟨1584674, by rfl⟩ : syracuseStep 2112899 = 3169349) B3169349
theorem B3565525 : Blo 2111435 3565525 := bbase (se 7 (by rfl) ⟨41783, by rfl⟩ : syracuseStep 3565525 = 83567) (by norm_num)
theorem B4754033 : Blo 2111435 4754033 := bstep (se 2 (by rfl) ⟨1782762, by rfl⟩ : syracuseStep 4754033 = 3565525) B3565525
theorem B3169355 : Blo 2111435 3169355 := bstep (se 1 (by rfl) ⟨2377016, by rfl⟩ : syracuseStep 3169355 = 4754033) B4754033
theorem B2112903 : Blo 2111435 2112903 := bstep (se 1 (by rfl) ⟨1584677, by rfl⟩ : syracuseStep 2112903 = 3169355) B3169355
theorem B2377021 : Blo 2111435 2377021 := bbase (se 3 (by rfl) ⟨445691, by rfl⟩ : syracuseStep 2377021 = 891383) (by norm_num)
theorem B3169361 : Blo 2111435 3169361 := bstep (se 2 (by rfl) ⟨1188510, by rfl⟩ : syracuseStep 3169361 = 2377021) B2377021
theorem B2112907 : Blo 2111435 2112907 := bstep (se 1 (by rfl) ⟨1584680, by rfl⟩ : syracuseStep 2112907 = 3169361) B3169361
theorem B7131077 : Blo 2111435 7131077 := bbase (se 4 (by rfl) ⟨668538, by rfl⟩ : syracuseStep 7131077 = 1337077) (by norm_num)
theorem B4754051 : Blo 2111435 4754051 := bstep (se 1 (by rfl) ⟨3565538, by rfl⟩ : syracuseStep 4754051 = 7131077) B7131077
theorem B3169367 : Blo 2111435 3169367 := bstep (se 1 (by rfl) ⟨2377025, by rfl⟩ : syracuseStep 3169367 = 4754051) B4754051
theorem B2112911 : Blo 2111435 2112911 := bstep (se 1 (by rfl) ⟨1584683, by rfl⟩ : syracuseStep 2112911 = 3169367) B3169367
theorem B3169373 : Blo 2111435 3169373 := bbase (se 3 (by rfl) ⟨594257, by rfl⟩ : syracuseStep 3169373 = 1188515) (by norm_num)
theorem B2112915 : Blo 2111435 2112915 := bstep (se 1 (by rfl) ⟨1584686, by rfl⟩ : syracuseStep 2112915 = 3169373) B3169373
theorem B4754069 : Blo 2111435 4754069 := bbase (se 6 (by rfl) ⟨111423, by rfl⟩ : syracuseStep 4754069 = 222847) (by norm_num)
theorem B3169379 : Blo 2111435 3169379 := bstep (se 1 (by rfl) ⟨2377034, by rfl⟩ : syracuseStep 3169379 = 4754069) B4754069
theorem B2112919 : Blo 2111435 2112919 := bstep (se 1 (by rfl) ⟨1584689, by rfl⟩ : syracuseStep 2112919 = 3169379) B3169379
theorem B2538373 : Blo 2111435 2538373 := bbase (se 4 (by rfl) ⟨237972, by rfl⟩ : syracuseStep 2538373 = 475945) (by norm_num)
theorem B3384497 : Blo 2111435 3384497 := bstep (se 2 (by rfl) ⟨1269186, by rfl⟩ : syracuseStep 3384497 = 2538373) B2538373
theorem B2256331 : Blo 2111435 2256331 := bstep (se 1 (by rfl) ⟨1692248, by rfl⟩ : syracuseStep 2256331 = 3384497) B3384497
theorem B3008441 : Blo 2111435 3008441 := bstep (se 2 (by rfl) ⟨1128165, by rfl⟩ : syracuseStep 3008441 = 2256331) B2256331
theorem B8022509 : Blo 2111435 8022509 := bstep (se 3 (by rfl) ⟨1504220, by rfl⟩ : syracuseStep 8022509 = 3008441) B3008441
theorem B5348339 : Blo 2111435 5348339 := bstep (se 1 (by rfl) ⟨4011254, by rfl⟩ : syracuseStep 5348339 = 8022509) B8022509
theorem B3565559 : Blo 2111435 3565559 := bstep (se 1 (by rfl) ⟨2674169, by rfl⟩ : syracuseStep 3565559 = 5348339) B5348339
theorem B2377039 : Blo 2111435 2377039 := bstep (se 1 (by rfl) ⟨1782779, by rfl⟩ : syracuseStep 2377039 = 3565559) B3565559
theorem B3169385 : Blo 2111435 3169385 := bstep (se 2 (by rfl) ⟨1188519, by rfl⟩ : syracuseStep 3169385 = 2377039) B2377039
theorem B2112923 : Blo 2111435 2112923 := bstep (se 1 (by rfl) ⟨1584692, by rfl⟩ : syracuseStep 2112923 = 3169385) B3169385
theorem B15230261 : Blo 2111435 15230261 := bbase (se 5 (by rfl) ⟨713918, by rfl⟩ : syracuseStep 15230261 = 1427837) (by norm_num)
theorem B10153507 : Blo 2111435 10153507 := bstep (se 1 (by rfl) ⟨7615130, by rfl⟩ : syracuseStep 10153507 = 15230261) B15230261
theorem B13538009 : Blo 2111435 13538009 := bstep (se 2 (by rfl) ⟨5076753, by rfl⟩ : syracuseStep 13538009 = 10153507) B10153507
theorem B9025339 : Blo 2111435 9025339 := bstep (se 1 (by rfl) ⟨6769004, by rfl⟩ : syracuseStep 9025339 = 13538009) B13538009
theorem B12033785 : Blo 2111435 12033785 := bstep (se 2 (by rfl) ⟨4512669, by rfl⟩ : syracuseStep 12033785 = 9025339) B9025339
theorem B8022523 : Blo 2111435 8022523 := bstep (se 1 (by rfl) ⟨6016892, by rfl⟩ : syracuseStep 8022523 = 12033785) B12033785
theorem B10696697 : Blo 2111435 10696697 := bstep (se 2 (by rfl) ⟨4011261, by rfl⟩ : syracuseStep 10696697 = 8022523) B8022523
theorem B7131131 : Blo 2111435 7131131 := bstep (se 1 (by rfl) ⟨5348348, by rfl⟩ : syracuseStep 7131131 = 10696697) B10696697
theorem B4754087 : Blo 2111435 4754087 := bstep (se 1 (by rfl) ⟨3565565, by rfl⟩ : syracuseStep 4754087 = 7131131) B7131131
theorem B3169391 : Blo 2111435 3169391 := bstep (se 1 (by rfl) ⟨2377043, by rfl⟩ : syracuseStep 3169391 = 4754087) B4754087
theorem B2112927 : Blo 2111435 2112927 := bstep (se 1 (by rfl) ⟨1584695, by rfl⟩ : syracuseStep 2112927 = 3169391) B3169391
theorem B3169397 : Blo 2111435 3169397 := bbase (se 5 (by rfl) ⟨148565, by rfl⟩ : syracuseStep 3169397 = 297131) (by norm_num)
theorem B2112931 : Blo 2111435 2112931 := bstep (se 1 (by rfl) ⟨1584698, by rfl⟩ : syracuseStep 2112931 = 3169397) B3169397
theorem B4011277 : Blo 2111435 4011277 := bbase (se 3 (by rfl) ⟨752114, by rfl⟩ : syracuseStep 4011277 = 1504229) (by norm_num)
theorem B5348369 : Blo 2111435 5348369 := bstep (se 2 (by rfl) ⟨2005638, by rfl⟩ : syracuseStep 5348369 = 4011277) B4011277
theorem B3565579 : Blo 2111435 3565579 := bstep (se 1 (by rfl) ⟨2674184, by rfl⟩ : syracuseStep 3565579 = 5348369) B5348369
theorem B4754105 : Blo 2111435 4754105 := bstep (se 2 (by rfl) ⟨1782789, by rfl⟩ : syracuseStep 4754105 = 3565579) B3565579
theorem B3169403 : Blo 2111435 3169403 := bstep (se 1 (by rfl) ⟨2377052, by rfl⟩ : syracuseStep 3169403 = 4754105) B4754105
theorem B2112935 : Blo 2111435 2112935 := bstep (se 1 (by rfl) ⟨1584701, by rfl⟩ : syracuseStep 2112935 = 3169403) B3169403
theorem B2377057 : Blo 2111435 2377057 := bbase (se 2 (by rfl) ⟨891396, by rfl⟩ : syracuseStep 2377057 = 1782793) (by norm_num)
theorem B3169409 : Blo 2111435 3169409 := bstep (se 2 (by rfl) ⟨1188528, by rfl⟩ : syracuseStep 3169409 = 2377057) B2377057
theorem B2112939 : Blo 2111435 2112939 := bstep (se 1 (by rfl) ⟨1584704, by rfl⟩ : syracuseStep 2112939 = 3169409) B3169409
theorem B5348389 : Blo 2111435 5348389 := bbase (se 4 (by rfl) ⟨501411, by rfl⟩ : syracuseStep 5348389 = 1002823) (by norm_num)
theorem B7131185 : Blo 2111435 7131185 := bstep (se 2 (by rfl) ⟨2674194, by rfl⟩ : syracuseStep 7131185 = 5348389) B5348389
theorem B4754123 : Blo 2111435 4754123 := bstep (se 1 (by rfl) ⟨3565592, by rfl⟩ : syracuseStep 4754123 = 7131185) B7131185
theorem B3169415 : Blo 2111435 3169415 := bstep (se 1 (by rfl) ⟨2377061, by rfl⟩ : syracuseStep 3169415 = 4754123) B4754123
theorem B2112943 : Blo 2111435 2112943 := bstep (se 1 (by rfl) ⟨1584707, by rfl⟩ : syracuseStep 2112943 = 3169415) B3169415
theorem B3169421 : Blo 2111435 3169421 := bbase (se 3 (by rfl) ⟨594266, by rfl⟩ : syracuseStep 3169421 = 1188533) (by norm_num)
theorem B2112947 : Blo 2111435 2112947 := bstep (se 1 (by rfl) ⟨1584710, by rfl⟩ : syracuseStep 2112947 = 3169421) B3169421
theorem B4754141 : Blo 2111435 4754141 := bbase (se 3 (by rfl) ⟨891401, by rfl⟩ : syracuseStep 4754141 = 1782803) (by norm_num)
theorem B3169427 : Blo 2111435 3169427 := bstep (se 1 (by rfl) ⟨2377070, by rfl⟩ : syracuseStep 3169427 = 4754141) B4754141
theorem B2112951 : Blo 2111435 2112951 := bstep (se 1 (by rfl) ⟨1584713, by rfl⟩ : syracuseStep 2112951 = 3169427) B3169427
theorem B3565613 : Blo 2111435 3565613 := bbase (se 3 (by rfl) ⟨668552, by rfl⟩ : syracuseStep 3565613 = 1337105) (by norm_num)
theorem B2377075 : Blo 2111435 2377075 := bstep (se 1 (by rfl) ⟨1782806, by rfl⟩ : syracuseStep 2377075 = 3565613) B3565613
theorem B3169433 : Blo 2111435 3169433 := bstep (se 2 (by rfl) ⟨1188537, by rfl⟩ : syracuseStep 3169433 = 2377075) B2377075
theorem B2112955 : Blo 2111435 2112955 := bstep (se 1 (by rfl) ⟨1584716, by rfl⟩ : syracuseStep 2112955 = 3169433) B3169433
theorem B2855717 : Blo 2111435 2855717 := bbase (se 4 (by rfl) ⟨267723, by rfl⟩ : syracuseStep 2855717 = 535447) (by norm_num)
theorem B30460981 : Blo 2111435 30460981 := bstep (se 5 (by rfl) ⟨1427858, by rfl⟩ : syracuseStep 30460981 = 2855717) B2855717
theorem B40614641 : Blo 2111435 40614641 := bstep (se 2 (by rfl) ⟨15230490, by rfl⟩ : syracuseStep 40614641 = 30460981) B30460981
theorem B27076427 : Blo 2111435 27076427 := bstep (se 1 (by rfl) ⟨20307320, by rfl⟩ : syracuseStep 27076427 = 40614641) B40614641
theorem B18050951 : Blo 2111435 18050951 := bstep (se 1 (by rfl) ⟨13538213, by rfl⟩ : syracuseStep 18050951 = 27076427) B27076427
theorem B12033967 : Blo 2111435 12033967 := bstep (se 1 (by rfl) ⟨9025475, by rfl⟩ : syracuseStep 12033967 = 18050951) B18050951
theorem B16045289 : Blo 2111435 16045289 := bstep (se 2 (by rfl) ⟨6016983, by rfl⟩ : syracuseStep 16045289 = 12033967) B12033967
theorem B10696859 : Blo 2111435 10696859 := bstep (se 1 (by rfl) ⟨8022644, by rfl⟩ : syracuseStep 10696859 = 16045289) B16045289
theorem B7131239 : Blo 2111435 7131239 := bstep (se 1 (by rfl) ⟨5348429, by rfl⟩ : syracuseStep 7131239 = 10696859) B10696859
theorem B4754159 : Blo 2111435 4754159 := bstep (se 1 (by rfl) ⟨3565619, by rfl⟩ : syracuseStep 4754159 = 7131239) B7131239
theorem B3169439 : Blo 2111435 3169439 := bstep (se 1 (by rfl) ⟨2377079, by rfl⟩ : syracuseStep 3169439 = 4754159) B4754159
theorem B2112959 : Blo 2111435 2112959 := bstep (se 1 (by rfl) ⟨1584719, by rfl⟩ : syracuseStep 2112959 = 3169439) B3169439
theorem B3169445 : Blo 2111435 3169445 := bbase (se 4 (by rfl) ⟨297135, by rfl⟩ : syracuseStep 3169445 = 594271) (by norm_num)
theorem B2112963 : Blo 2111435 2112963 := bstep (se 1 (by rfl) ⟨1584722, by rfl⟩ : syracuseStep 2112963 = 3169445) B3169445
theorem B2674225 : Blo 2111435 2674225 := bbase (se 2 (by rfl) ⟨1002834, by rfl⟩ : syracuseStep 2674225 = 2005669) (by norm_num)
theorem B3565633 : Blo 2111435 3565633 := bstep (se 2 (by rfl) ⟨1337112, by rfl⟩ : syracuseStep 3565633 = 2674225) B2674225
theorem B4754177 : Blo 2111435 4754177 := bstep (se 2 (by rfl) ⟨1782816, by rfl⟩ : syracuseStep 4754177 = 3565633) B3565633
theorem B3169451 : Blo 2111435 3169451 := bstep (se 1 (by rfl) ⟨2377088, by rfl⟩ : syracuseStep 3169451 = 4754177) B4754177
theorem B2112967 : Blo 2111435 2112967 := bstep (se 1 (by rfl) ⟨1584725, by rfl⟩ : syracuseStep 2112967 = 3169451) B3169451
theorem B2377093 : Blo 2111435 2377093 := bbase (se 4 (by rfl) ⟨222852, by rfl⟩ : syracuseStep 2377093 = 445705) (by norm_num)
theorem B3169457 : Blo 2111435 3169457 := bstep (se 2 (by rfl) ⟨1188546, by rfl⟩ : syracuseStep 3169457 = 2377093) B2377093
theorem B2112971 : Blo 2111435 2112971 := bstep (se 1 (by rfl) ⟨1584728, by rfl⟩ : syracuseStep 2112971 = 3169457) B3169457
theorem B4512773 : Blo 2111435 4512773 := bbase (se 4 (by rfl) ⟨423072, by rfl⟩ : syracuseStep 4512773 = 846145) (by norm_num)
theorem B3008515 : Blo 2111435 3008515 := bstep (se 1 (by rfl) ⟨2256386, by rfl⟩ : syracuseStep 3008515 = 4512773) B4512773
theorem B4011353 : Blo 2111435 4011353 := bstep (se 2 (by rfl) ⟨1504257, by rfl⟩ : syracuseStep 4011353 = 3008515) B3008515
theorem B2674235 : Blo 2111435 2674235 := bstep (se 1 (by rfl) ⟨2005676, by rfl⟩ : syracuseStep 2674235 = 4011353) B4011353
theorem B7131293 : Blo 2111435 7131293 := bstep (se 3 (by rfl) ⟨1337117, by rfl⟩ : syracuseStep 7131293 = 2674235) B2674235
theorem B4754195 : Blo 2111435 4754195 := bstep (se 1 (by rfl) ⟨3565646, by rfl⟩ : syracuseStep 4754195 = 7131293) B7131293
theorem B3169463 : Blo 2111435 3169463 := bstep (se 1 (by rfl) ⟨2377097, by rfl⟩ : syracuseStep 3169463 = 4754195) B4754195
theorem B2112975 : Blo 2111435 2112975 := bstep (se 1 (by rfl) ⟨1584731, by rfl⟩ : syracuseStep 2112975 = 3169463) B3169463
theorem B3169469 : Blo 2111435 3169469 := bbase (se 3 (by rfl) ⟨594275, by rfl⟩ : syracuseStep 3169469 = 1188551) (by norm_num)
theorem B2112979 : Blo 2111435 2112979 := bstep (se 1 (by rfl) ⟨1584734, by rfl⟩ : syracuseStep 2112979 = 3169469) B3169469
theorem B4754213 : Blo 2111435 4754213 := bbase (se 4 (by rfl) ⟨445707, by rfl⟩ : syracuseStep 4754213 = 891415) (by norm_num)
theorem B3169475 : Blo 2111435 3169475 := bstep (se 1 (by rfl) ⟨2377106, by rfl⟩ : syracuseStep 3169475 = 4754213) B4754213
theorem B2112983 : Blo 2111435 2112983 := bstep (se 1 (by rfl) ⟨1584737, by rfl⟩ : syracuseStep 2112983 = 3169475) B3169475
theorem B5348501 : Blo 2111435 5348501 := bbase (se 6 (by rfl) ⟨125355, by rfl⟩ : syracuseStep 5348501 = 250711) (by norm_num)
theorem B3565667 : Blo 2111435 3565667 := bstep (se 1 (by rfl) ⟨2674250, by rfl⟩ : syracuseStep 3565667 = 5348501) B5348501
theorem B2377111 : Blo 2111435 2377111 := bstep (se 1 (by rfl) ⟨1782833, by rfl⟩ : syracuseStep 2377111 = 3565667) B3565667
theorem B3169481 : Blo 2111435 3169481 := bstep (se 2 (by rfl) ⟨1188555, by rfl⟩ : syracuseStep 3169481 = 2377111) B2377111
theorem B2112987 : Blo 2111435 2112987 := bstep (se 1 (by rfl) ⟨1584740, by rfl⟩ : syracuseStep 2112987 = 3169481) B3169481
theorem B3384605 : Blo 2111435 3384605 := bbase (se 3 (by rfl) ⟨634613, by rfl⟩ : syracuseStep 3384605 = 1269227) (by norm_num)
theorem B9025613 : Blo 2111435 9025613 := bstep (se 3 (by rfl) ⟨1692302, by rfl⟩ : syracuseStep 9025613 = 3384605) B3384605
theorem B6017075 : Blo 2111435 6017075 := bstep (se 1 (by rfl) ⟨4512806, by rfl⟩ : syracuseStep 6017075 = 9025613) B9025613
theorem B4011383 : Blo 2111435 4011383 := bstep (se 1 (by rfl) ⟨3008537, by rfl⟩ : syracuseStep 4011383 = 6017075) B6017075
theorem B10697021 : Blo 2111435 10697021 := bstep (se 3 (by rfl) ⟨2005691, by rfl⟩ : syracuseStep 10697021 = 4011383) B4011383
theorem B7131347 : Blo 2111435 7131347 := bstep (se 1 (by rfl) ⟨5348510, by rfl⟩ : syracuseStep 7131347 = 10697021) B10697021
theorem B4754231 : Blo 2111435 4754231 := bstep (se 1 (by rfl) ⟨3565673, by rfl⟩ : syracuseStep 4754231 = 7131347) B7131347
theorem B3169487 : Blo 2111435 3169487 := bstep (se 1 (by rfl) ⟨2377115, by rfl⟩ : syracuseStep 3169487 = 4754231) B4754231
theorem B2112991 : Blo 2111435 2112991 := bstep (se 1 (by rfl) ⟨1584743, by rfl⟩ : syracuseStep 2112991 = 3169487) B3169487
theorem B3169493 : Blo 2111435 3169493 := bbase (se 7 (by rfl) ⟨37142, by rfl⟩ : syracuseStep 3169493 = 74285) (by norm_num)
theorem B2112995 : Blo 2111435 2112995 := bstep (se 1 (by rfl) ⟨1584746, by rfl⟩ : syracuseStep 2112995 = 3169493) B3169493
theorem B3008549 : Blo 2111435 3008549 := bbase (se 4 (by rfl) ⟨282051, by rfl⟩ : syracuseStep 3008549 = 564103) (by norm_num)
theorem B8022797 : Blo 2111435 8022797 := bstep (se 3 (by rfl) ⟨1504274, by rfl⟩ : syracuseStep 8022797 = 3008549) B3008549
theorem B5348531 : Blo 2111435 5348531 := bstep (se 1 (by rfl) ⟨4011398, by rfl⟩ : syracuseStep 5348531 = 8022797) B8022797
theorem B3565687 : Blo 2111435 3565687 := bstep (se 1 (by rfl) ⟨2674265, by rfl⟩ : syracuseStep 3565687 = 5348531) B5348531
theorem B4754249 : Blo 2111435 4754249 := bstep (se 2 (by rfl) ⟨1782843, by rfl⟩ : syracuseStep 4754249 = 3565687) B3565687
theorem B3169499 : Blo 2111435 3169499 := bstep (se 1 (by rfl) ⟨2377124, by rfl⟩ : syracuseStep 3169499 = 4754249) B4754249
theorem B2112999 : Blo 2111435 2112999 := bstep (se 1 (by rfl) ⟨1584749, by rfl⟩ : syracuseStep 2112999 = 3169499) B3169499
theorem B2377129 : Blo 2111435 2377129 := bbase (se 2 (by rfl) ⟨891423, by rfl⟩ : syracuseStep 2377129 = 1782847) (by norm_num)
theorem B3169505 : Blo 2111435 3169505 := bstep (se 2 (by rfl) ⟨1188564, by rfl⟩ : syracuseStep 3169505 = 2377129) B2377129
theorem B2113003 : Blo 2111435 2113003 := bstep (se 1 (by rfl) ⟨1584752, by rfl⟩ : syracuseStep 2113003 = 3169505) B3169505
theorem B2538473 : Blo 2111435 2538473 := bbase (se 2 (by rfl) ⟨951927, by rfl⟩ : syracuseStep 2538473 = 1903855) (by norm_num)
theorem B6769261 : Blo 2111435 6769261 := bstep (se 3 (by rfl) ⟨1269236, by rfl⟩ : syracuseStep 6769261 = 2538473) B2538473
theorem B9025681 : Blo 2111435 9025681 := bstep (se 2 (by rfl) ⟨3384630, by rfl⟩ : syracuseStep 9025681 = 6769261) B6769261
theorem B12034241 : Blo 2111435 12034241 := bstep (se 2 (by rfl) ⟨4512840, by rfl⟩ : syracuseStep 12034241 = 9025681) B9025681
theorem B8022827 : Blo 2111435 8022827 := bstep (se 1 (by rfl) ⟨6017120, by rfl⟩ : syracuseStep 8022827 = 12034241) B12034241
theorem B5348551 : Blo 2111435 5348551 := bstep (se 1 (by rfl) ⟨4011413, by rfl⟩ : syracuseStep 5348551 = 8022827) B8022827
theorem B7131401 : Blo 2111435 7131401 := bstep (se 2 (by rfl) ⟨2674275, by rfl⟩ : syracuseStep 7131401 = 5348551) B5348551
theorem B4754267 : Blo 2111435 4754267 := bstep (se 1 (by rfl) ⟨3565700, by rfl⟩ : syracuseStep 4754267 = 7131401) B7131401
theorem B3169511 : Blo 2111435 3169511 := bstep (se 1 (by rfl) ⟨2377133, by rfl⟩ : syracuseStep 3169511 = 4754267) B4754267
theorem B2113007 : Blo 2111435 2113007 := bstep (se 1 (by rfl) ⟨1584755, by rfl⟩ : syracuseStep 2113007 = 3169511) B3169511
theorem B3169517 : Blo 2111435 3169517 := bbase (se 3 (by rfl) ⟨594284, by rfl⟩ : syracuseStep 3169517 = 1188569) (by norm_num)
theorem B2113011 : Blo 2111435 2113011 := bstep (se 1 (by rfl) ⟨1584758, by rfl⟩ : syracuseStep 2113011 = 3169517) B3169517
theorem B4754285 : Blo 2111435 4754285 := bbase (se 3 (by rfl) ⟨891428, by rfl⟩ : syracuseStep 4754285 = 1782857) (by norm_num)
theorem B3169523 : Blo 2111435 3169523 := bstep (se 1 (by rfl) ⟨2377142, by rfl⟩ : syracuseStep 3169523 = 4754285) B4754285
theorem B2113015 : Blo 2111435 2113015 := bstep (se 1 (by rfl) ⟨1584761, by rfl⟩ : syracuseStep 2113015 = 3169523) B3169523
theorem B4011437 : Blo 2111435 4011437 := bbase (se 3 (by rfl) ⟨752144, by rfl⟩ : syracuseStep 4011437 = 1504289) (by norm_num)
theorem B2674291 : Blo 2111435 2674291 := bstep (se 1 (by rfl) ⟨2005718, by rfl⟩ : syracuseStep 2674291 = 4011437) B4011437
theorem B3565721 : Blo 2111435 3565721 := bstep (se 2 (by rfl) ⟨1337145, by rfl⟩ : syracuseStep 3565721 = 2674291) B2674291
theorem B2377147 : Blo 2111435 2377147 := bstep (se 1 (by rfl) ⟨1782860, by rfl⟩ : syracuseStep 2377147 = 3565721) B3565721
theorem B3169529 : Blo 2111435 3169529 := bstep (se 2 (by rfl) ⟨1188573, by rfl⟩ : syracuseStep 3169529 = 2377147) B2377147
theorem B2113019 : Blo 2111435 2113019 := bstep (se 1 (by rfl) ⟨1584764, by rfl⟩ : syracuseStep 2113019 = 3169529) B3169529
theorem B3256613 : Blo 2111435 3256613 := bbase (se 4 (by rfl) ⟨305307, by rfl⟩ : syracuseStep 3256613 = 610615) (by norm_num)
theorem B2171075 : Blo 2111435 2171075 := bstep (se 1 (by rfl) ⟨1628306, by rfl⟩ : syracuseStep 2171075 = 3256613) B3256613
theorem B23158133 : Blo 2111435 23158133 := bstep (se 5 (by rfl) ⟨1085537, by rfl⟩ : syracuseStep 23158133 = 2171075) B2171075
theorem B15438755 : Blo 2111435 15438755 := bstep (se 1 (by rfl) ⟨11579066, by rfl⟩ : syracuseStep 15438755 = 23158133) B23158133
theorem B10292503 : Blo 2111435 10292503 := bstep (se 1 (by rfl) ⟨7719377, by rfl⟩ : syracuseStep 10292503 = 15438755) B15438755
theorem B13723337 : Blo 2111435 13723337 := bstep (se 2 (by rfl) ⟨5146251, by rfl⟩ : syracuseStep 13723337 = 10292503) B10292503
theorem B9148891 : Blo 2111435 9148891 := bstep (se 1 (by rfl) ⟨6861668, by rfl⟩ : syracuseStep 9148891 = 13723337) B13723337
theorem B12198521 : Blo 2111435 12198521 := bstep (se 2 (by rfl) ⟨4574445, by rfl⟩ : syracuseStep 12198521 = 9148891) B9148891
theorem B8132347 : Blo 2111435 8132347 := bstep (se 1 (by rfl) ⟨6099260, by rfl⟩ : syracuseStep 8132347 = 12198521) B12198521
theorem B10843129 : Blo 2111435 10843129 := bstep (se 2 (by rfl) ⟨4066173, by rfl⟩ : syracuseStep 10843129 = 8132347) B8132347
theorem B57830021 : Blo 2111435 57830021 := bstep (se 4 (by rfl) ⟨5421564, by rfl⟩ : syracuseStep 57830021 = 10843129) B10843129
theorem B38553347 : Blo 2111435 38553347 := bstep (se 1 (by rfl) ⟨28915010, by rfl⟩ : syracuseStep 38553347 = 57830021) B57830021
theorem B102808925 : Blo 2111435 102808925 := bstep (se 3 (by rfl) ⟨19276673, by rfl⟩ : syracuseStep 102808925 = 38553347) B38553347
theorem B68539283 : Blo 2111435 68539283 := bstep (se 1 (by rfl) ⟨51404462, by rfl⟩ : syracuseStep 68539283 = 102808925) B102808925
theorem B45692855 : Blo 2111435 45692855 := bstep (se 1 (by rfl) ⟨34269641, by rfl⟩ : syracuseStep 45692855 = 68539283) B68539283
theorem B30461903 : Blo 2111435 30461903 := bstep (se 1 (by rfl) ⟨22846427, by rfl⟩ : syracuseStep 30461903 = 45692855) B45692855
theorem B20307935 : Blo 2111435 20307935 := bstep (se 1 (by rfl) ⟨15230951, by rfl⟩ : syracuseStep 20307935 = 30461903) B30461903
theorem B54154493 : Blo 2111435 54154493 := bstep (se 3 (by rfl) ⟨10153967, by rfl⟩ : syracuseStep 54154493 = 20307935) B20307935
theorem B36102995 : Blo 2111435 36102995 := bstep (se 1 (by rfl) ⟨27077246, by rfl⟩ : syracuseStep 36102995 = 54154493) B54154493
theorem B24068663 : Blo 2111435 24068663 := bstep (se 1 (by rfl) ⟨18051497, by rfl⟩ : syracuseStep 24068663 = 36102995) B36102995
theorem B16045775 : Blo 2111435 16045775 := bstep (se 1 (by rfl) ⟨12034331, by rfl⟩ : syracuseStep 16045775 = 24068663) B24068663
theorem B10697183 : Blo 2111435 10697183 := bstep (se 1 (by rfl) ⟨8022887, by rfl⟩ : syracuseStep 10697183 = 16045775) B16045775
theorem B7131455 : Blo 2111435 7131455 := bstep (se 1 (by rfl) ⟨5348591, by rfl⟩ : syracuseStep 7131455 = 10697183) B10697183
theorem B4754303 : Blo 2111435 4754303 := bstep (se 1 (by rfl) ⟨3565727, by rfl⟩ : syracuseStep 4754303 = 7131455) B7131455
theorem B3169535 : Blo 2111435 3169535 := bstep (se 1 (by rfl) ⟨2377151, by rfl⟩ : syracuseStep 3169535 = 4754303) B4754303
theorem B2113023 : Blo 2111435 2113023 := bstep (se 1 (by rfl) ⟨1584767, by rfl⟩ : syracuseStep 2113023 = 3169535) B3169535
theorem B3169541 : Blo 2111435 3169541 := bbase (se 4 (by rfl) ⟨297144, by rfl⟩ : syracuseStep 3169541 = 594289) (by norm_num)
theorem B2113027 : Blo 2111435 2113027 := bstep (se 1 (by rfl) ⟨1584770, by rfl⟩ : syracuseStep 2113027 = 3169541) B3169541
theorem B3565741 : Blo 2111435 3565741 := bbase (se 3 (by rfl) ⟨668576, by rfl⟩ : syracuseStep 3565741 = 1337153) (by norm_num)
theorem B4754321 : Blo 2111435 4754321 := bstep (se 2 (by rfl) ⟨1782870, by rfl⟩ : syracuseStep 4754321 = 3565741) B3565741
theorem B3169547 : Blo 2111435 3169547 := bstep (se 1 (by rfl) ⟨2377160, by rfl⟩ : syracuseStep 3169547 = 4754321) B4754321
theorem B2113031 : Blo 2111435 2113031 := bstep (se 1 (by rfl) ⟨1584773, by rfl⟩ : syracuseStep 2113031 = 3169547) B3169547
theorem B2377165 : Blo 2111435 2377165 := bbase (se 3 (by rfl) ⟨445718, by rfl⟩ : syracuseStep 2377165 = 891437) (by norm_num)
theorem B3169553 : Blo 2111435 3169553 := bstep (se 2 (by rfl) ⟨1188582, by rfl⟩ : syracuseStep 3169553 = 2377165) B2377165
theorem B2113035 : Blo 2111435 2113035 := bstep (se 1 (by rfl) ⟨1584776, by rfl⟩ : syracuseStep 2113035 = 3169553) B3169553
theorem B7131509 : Blo 2111435 7131509 := bbase (se 5 (by rfl) ⟨334289, by rfl⟩ : syracuseStep 7131509 = 668579) (by norm_num)
theorem B4754339 : Blo 2111435 4754339 := bstep (se 1 (by rfl) ⟨3565754, by rfl⟩ : syracuseStep 4754339 = 7131509) B7131509
theorem B3169559 : Blo 2111435 3169559 := bstep (se 1 (by rfl) ⟨2377169, by rfl⟩ : syracuseStep 3169559 = 4754339) B4754339
theorem B2113039 : Blo 2111435 2113039 := bstep (se 1 (by rfl) ⟨1584779, by rfl⟩ : syracuseStep 2113039 = 3169559) B3169559
theorem B3169565 : Blo 2111435 3169565 := bbase (se 3 (by rfl) ⟨594293, by rfl⟩ : syracuseStep 3169565 = 1188587) (by norm_num)
theorem B2113043 : Blo 2111435 2113043 := bstep (se 1 (by rfl) ⟨1584782, by rfl⟩ : syracuseStep 2113043 = 3169565) B3169565
theorem B4754357 : Blo 2111435 4754357 := bbase (se 5 (by rfl) ⟨222860, by rfl⟩ : syracuseStep 4754357 = 445721) (by norm_num)
theorem B3169571 : Blo 2111435 3169571 := bstep (se 1 (by rfl) ⟨2377178, by rfl⟩ : syracuseStep 3169571 = 4754357) B4754357
theorem B2113047 : Blo 2111435 2113047 := bstep (se 1 (by rfl) ⟨1584785, by rfl⟩ : syracuseStep 2113047 = 3169571) B3169571
theorem B4951637 : Blo 2111435 4951637 := bbase (se 8 (by rfl) ⟨29013, by rfl⟩ : syracuseStep 4951637 = 58027) (by norm_num)
theorem B3301091 : Blo 2111435 3301091 := bstep (se 1 (by rfl) ⟨2475818, by rfl⟩ : syracuseStep 3301091 = 4951637) B4951637
theorem B2200727 : Blo 2111435 2200727 := bstep (se 1 (by rfl) ⟨1650545, by rfl⟩ : syracuseStep 2200727 = 3301091) B3301091
theorem B5868605 : Blo 2111435 5868605 := bstep (se 3 (by rfl) ⟨1100363, by rfl⟩ : syracuseStep 5868605 = 2200727) B2200727
theorem B3912403 : Blo 2111435 3912403 := bstep (se 1 (by rfl) ⟨2934302, by rfl⟩ : syracuseStep 3912403 = 5868605) B5868605
theorem B5216537 : Blo 2111435 5216537 := bstep (se 2 (by rfl) ⟨1956201, by rfl⟩ : syracuseStep 5216537 = 3912403) B3912403
theorem B3477691 : Blo 2111435 3477691 := bstep (se 1 (by rfl) ⟨2608268, by rfl⟩ : syracuseStep 3477691 = 5216537) B5216537
theorem B4636921 : Blo 2111435 4636921 := bstep (se 2 (by rfl) ⟨1738845, by rfl⟩ : syracuseStep 4636921 = 3477691) B3477691
theorem B6182561 : Blo 2111435 6182561 := bstep (se 2 (by rfl) ⟨2318460, by rfl⟩ : syracuseStep 6182561 = 4636921) B4636921
theorem B4121707 : Blo 2111435 4121707 := bstep (se 1 (by rfl) ⟨3091280, by rfl⟩ : syracuseStep 4121707 = 6182561) B6182561
theorem B5495609 : Blo 2111435 5495609 := bstep (se 2 (by rfl) ⟨2060853, by rfl⟩ : syracuseStep 5495609 = 4121707) B4121707
theorem B3663739 : Blo 2111435 3663739 := bstep (se 1 (by rfl) ⟨2747804, by rfl⟩ : syracuseStep 3663739 = 5495609) B5495609
theorem B4884985 : Blo 2111435 4884985 := bstep (se 2 (by rfl) ⟨1831869, by rfl⟩ : syracuseStep 4884985 = 3663739) B3663739
theorem B26053253 : Blo 2111435 26053253 := bstep (se 4 (by rfl) ⟨2442492, by rfl⟩ : syracuseStep 26053253 = 4884985) B4884985
theorem B17368835 : Blo 2111435 17368835 := bstep (se 1 (by rfl) ⟨13026626, by rfl⟩ : syracuseStep 17368835 = 26053253) B26053253
theorem B185267573 : Blo 2111435 185267573 := bstep (se 5 (by rfl) ⟨8684417, by rfl⟩ : syracuseStep 185267573 = 17368835) B17368835
theorem B123511715 : Blo 2111435 123511715 := bstep (se 1 (by rfl) ⟨92633786, by rfl⟩ : syracuseStep 123511715 = 185267573) B185267573
theorem B82341143 : Blo 2111435 82341143 := bstep (se 1 (by rfl) ⟨61755857, by rfl⟩ : syracuseStep 82341143 = 123511715) B123511715
theorem B54894095 : Blo 2111435 54894095 := bstep (se 1 (by rfl) ⟨41170571, by rfl⟩ : syracuseStep 54894095 = 82341143) B82341143
theorem B36596063 : Blo 2111435 36596063 := bstep (se 1 (by rfl) ⟨27447047, by rfl⟩ : syracuseStep 36596063 = 54894095) B54894095
theorem B24397375 : Blo 2111435 24397375 := bstep (se 1 (by rfl) ⟨18298031, by rfl⟩ : syracuseStep 24397375 = 36596063) B36596063
theorem B32529833 : Blo 2111435 32529833 := bstep (se 2 (by rfl) ⟨12198687, by rfl⟩ : syracuseStep 32529833 = 24397375) B24397375
theorem B21686555 : Blo 2111435 21686555 := bstep (se 1 (by rfl) ⟨16264916, by rfl⟩ : syracuseStep 21686555 = 32529833) B32529833
theorem B14457703 : Blo 2111435 14457703 := bstep (se 1 (by rfl) ⟨10843277, by rfl⟩ : syracuseStep 14457703 = 21686555) B21686555
theorem B19276937 : Blo 2111435 19276937 := bstep (se 2 (by rfl) ⟨7228851, by rfl⟩ : syracuseStep 19276937 = 14457703) B14457703
theorem B12851291 : Blo 2111435 12851291 := bstep (se 1 (by rfl) ⟨9638468, by rfl⟩ : syracuseStep 12851291 = 19276937) B19276937
theorem B8567527 : Blo 2111435 8567527 := bstep (se 1 (by rfl) ⟨6425645, by rfl⟩ : syracuseStep 8567527 = 12851291) B12851291
theorem B11423369 : Blo 2111435 11423369 := bstep (se 2 (by rfl) ⟨4283763, by rfl⟩ : syracuseStep 11423369 = 8567527) B8567527
theorem B7615579 : Blo 2111435 7615579 := bstep (se 1 (by rfl) ⟨5711684, by rfl⟩ : syracuseStep 7615579 = 11423369) B11423369
theorem B10154105 : Blo 2111435 10154105 := bstep (se 2 (by rfl) ⟨3807789, by rfl⟩ : syracuseStep 10154105 = 7615579) B7615579
theorem B6769403 : Blo 2111435 6769403 := bstep (se 1 (by rfl) ⟨5077052, by rfl⟩ : syracuseStep 6769403 = 10154105) B10154105
theorem B4512935 : Blo 2111435 4512935 := bstep (se 1 (by rfl) ⟨3384701, by rfl⟩ : syracuseStep 4512935 = 6769403) B6769403
theorem B12034493 : Blo 2111435 12034493 := bstep (se 3 (by rfl) ⟨2256467, by rfl⟩ : syracuseStep 12034493 = 4512935) B4512935
theorem B8022995 : Blo 2111435 8022995 := bstep (se 1 (by rfl) ⟨6017246, by rfl⟩ : syracuseStep 8022995 = 12034493) B12034493
theorem B5348663 : Blo 2111435 5348663 := bstep (se 1 (by rfl) ⟨4011497, by rfl⟩ : syracuseStep 5348663 = 8022995) B8022995
theorem B3565775 : Blo 2111435 3565775 := bstep (se 1 (by rfl) ⟨2674331, by rfl⟩ : syracuseStep 3565775 = 5348663) B5348663
theorem B2377183 : Blo 2111435 2377183 := bstep (se 1 (by rfl) ⟨1782887, by rfl⟩ : syracuseStep 2377183 = 3565775) B3565775
theorem B3169577 : Blo 2111435 3169577 := bstep (se 2 (by rfl) ⟨1188591, by rfl⟩ : syracuseStep 3169577 = 2377183) B2377183
theorem B2113051 : Blo 2111435 2113051 := bstep (se 1 (by rfl) ⟨1584788, by rfl⟩ : syracuseStep 2113051 = 3169577) B3169577
theorem B4066237 : Blo 2111435 4066237 := bbase (se 3 (by rfl) ⟨762419, by rfl⟩ : syracuseStep 4066237 = 1524839) (by norm_num)
theorem B5421649 : Blo 2111435 5421649 := bstep (se 2 (by rfl) ⟨2033118, by rfl⟩ : syracuseStep 5421649 = 4066237) B4066237
theorem B7228865 : Blo 2111435 7228865 := bstep (se 2 (by rfl) ⟨2710824, by rfl⟩ : syracuseStep 7228865 = 5421649) B5421649
theorem B4819243 : Blo 2111435 4819243 := bstep (se 1 (by rfl) ⟨3614432, by rfl⟩ : syracuseStep 4819243 = 7228865) B7228865
theorem B6425657 : Blo 2111435 6425657 := bstep (se 2 (by rfl) ⟨2409621, by rfl⟩ : syracuseStep 6425657 = 4819243) B4819243
theorem B4283771 : Blo 2111435 4283771 := bstep (se 1 (by rfl) ⟨3212828, by rfl⟩ : syracuseStep 4283771 = 6425657) B6425657
theorem B11423389 : Blo 2111435 11423389 := bstep (se 3 (by rfl) ⟨2141885, by rfl⟩ : syracuseStep 11423389 = 4283771) B4283771
theorem B15231185 : Blo 2111435 15231185 := bstep (se 2 (by rfl) ⟨5711694, by rfl⟩ : syracuseStep 15231185 = 11423389) B11423389
theorem B10154123 : Blo 2111435 10154123 := bstep (se 1 (by rfl) ⟨7615592, by rfl⟩ : syracuseStep 10154123 = 15231185) B15231185
theorem B6769415 : Blo 2111435 6769415 := bstep (se 1 (by rfl) ⟨5077061, by rfl⟩ : syracuseStep 6769415 = 10154123) B10154123
theorem B4512943 : Blo 2111435 4512943 := bstep (se 1 (by rfl) ⟨3384707, by rfl⟩ : syracuseStep 4512943 = 6769415) B6769415
theorem B6017257 : Blo 2111435 6017257 := bstep (se 2 (by rfl) ⟨2256471, by rfl⟩ : syracuseStep 6017257 = 4512943) B4512943
theorem B8023009 : Blo 2111435 8023009 := bstep (se 2 (by rfl) ⟨3008628, by rfl⟩ : syracuseStep 8023009 = 6017257) B6017257
theorem B10697345 : Blo 2111435 10697345 := bstep (se 2 (by rfl) ⟨4011504, by rfl⟩ : syracuseStep 10697345 = 8023009) B8023009
theorem B7131563 : Blo 2111435 7131563 := bstep (se 1 (by rfl) ⟨5348672, by rfl⟩ : syracuseStep 7131563 = 10697345) B10697345
theorem B4754375 : Blo 2111435 4754375 := bstep (se 1 (by rfl) ⟨3565781, by rfl⟩ : syracuseStep 4754375 = 7131563) B7131563
theorem B3169583 : Blo 2111435 3169583 := bstep (se 1 (by rfl) ⟨2377187, by rfl⟩ : syracuseStep 3169583 = 4754375) B4754375
theorem B2113055 : Blo 2111435 2113055 := bstep (se 1 (by rfl) ⟨1584791, by rfl⟩ : syracuseStep 2113055 = 3169583) B3169583
theorem B3169589 : Blo 2111435 3169589 := bbase (se 5 (by rfl) ⟨148574, by rfl⟩ : syracuseStep 3169589 = 297149) (by norm_num)
theorem B2113059 : Blo 2111435 2113059 := bstep (se 1 (by rfl) ⟨1584794, by rfl⟩ : syracuseStep 2113059 = 3169589) B3169589
theorem B5348693 : Blo 2111435 5348693 := bbase (se 11 (by rfl) ⟨3917, by rfl⟩ : syracuseStep 5348693 = 7835) (by norm_num)
theorem B3565795 : Blo 2111435 3565795 := bstep (se 1 (by rfl) ⟨2674346, by rfl⟩ : syracuseStep 3565795 = 5348693) B5348693
theorem B4754393 : Blo 2111435 4754393 := bstep (se 2 (by rfl) ⟨1782897, by rfl⟩ : syracuseStep 4754393 = 3565795) B3565795
theorem B3169595 : Blo 2111435 3169595 := bstep (se 1 (by rfl) ⟨2377196, by rfl⟩ : syracuseStep 3169595 = 4754393) B4754393
theorem B2113063 : Blo 2111435 2113063 := bstep (se 1 (by rfl) ⟨1584797, by rfl⟩ : syracuseStep 2113063 = 3169595) B3169595
theorem B2377201 : Blo 2111435 2377201 := bbase (se 2 (by rfl) ⟨891450, by rfl⟩ : syracuseStep 2377201 = 1782901) (by norm_num)
theorem B3169601 : Blo 2111435 3169601 := bstep (se 2 (by rfl) ⟨1188600, by rfl⟩ : syracuseStep 3169601 = 2377201) B2377201
theorem B2113067 : Blo 2111435 2113067 := bstep (se 1 (by rfl) ⟨1584800, by rfl⟩ : syracuseStep 2113067 = 3169601) B3169601
theorem B13538933 : Blo 2111435 13538933 := bbase (se 5 (by rfl) ⟨634637, by rfl⟩ : syracuseStep 13538933 = 1269275) (by norm_num)
theorem B9025955 : Blo 2111435 9025955 := bstep (se 1 (by rfl) ⟨6769466, by rfl⟩ : syracuseStep 9025955 = 13538933) B13538933
theorem B6017303 : Blo 2111435 6017303 := bstep (se 1 (by rfl) ⟨4512977, by rfl⟩ : syracuseStep 6017303 = 9025955) B9025955
theorem B4011535 : Blo 2111435 4011535 := bstep (se 1 (by rfl) ⟨3008651, by rfl⟩ : syracuseStep 4011535 = 6017303) B6017303
theorem B5348713 : Blo 2111435 5348713 := bstep (se 2 (by rfl) ⟨2005767, by rfl⟩ : syracuseStep 5348713 = 4011535) B4011535
theorem B7131617 : Blo 2111435 7131617 := bstep (se 2 (by rfl) ⟨2674356, by rfl⟩ : syracuseStep 7131617 = 5348713) B5348713
theorem B4754411 : Blo 2111435 4754411 := bstep (se 1 (by rfl) ⟨3565808, by rfl⟩ : syracuseStep 4754411 = 7131617) B7131617
theorem B3169607 : Blo 2111435 3169607 := bstep (se 1 (by rfl) ⟨2377205, by rfl⟩ : syracuseStep 3169607 = 4754411) B4754411
theorem B2113071 : Blo 2111435 2113071 := bstep (se 1 (by rfl) ⟨1584803, by rfl⟩ : syracuseStep 2113071 = 3169607) B3169607
theorem B3169613 : Blo 2111435 3169613 := bbase (se 3 (by rfl) ⟨594302, by rfl⟩ : syracuseStep 3169613 = 1188605) (by norm_num)
theorem B2113075 : Blo 2111435 2113075 := bstep (se 1 (by rfl) ⟨1584806, by rfl⟩ : syracuseStep 2113075 = 3169613) B3169613
theorem B4754429 : Blo 2111435 4754429 := bbase (se 3 (by rfl) ⟨891455, by rfl⟩ : syracuseStep 4754429 = 1782911) (by norm_num)
theorem B3169619 : Blo 2111435 3169619 := bstep (se 1 (by rfl) ⟨2377214, by rfl⟩ : syracuseStep 3169619 = 4754429) B4754429
theorem B2113079 : Blo 2111435 2113079 := bstep (se 1 (by rfl) ⟨1584809, by rfl⟩ : syracuseStep 2113079 = 3169619) B3169619
theorem B3565829 : Blo 2111435 3565829 := bbase (se 4 (by rfl) ⟨334296, by rfl⟩ : syracuseStep 3565829 = 668593) (by norm_num)
theorem B2377219 : Blo 2111435 2377219 := bstep (se 1 (by rfl) ⟨1782914, by rfl⟩ : syracuseStep 2377219 = 3565829) B3565829
theorem B3169625 : Blo 2111435 3169625 := bstep (se 2 (by rfl) ⟨1188609, by rfl⟩ : syracuseStep 3169625 = 2377219) B2377219
theorem B2113083 : Blo 2111435 2113083 := bstep (se 1 (by rfl) ⟨1584812, by rfl⟩ : syracuseStep 2113083 = 3169625) B3169625
theorem B16046261 : Blo 2111435 16046261 := bbase (se 5 (by rfl) ⟨752168, by rfl⟩ : syracuseStep 16046261 = 1504337) (by norm_num)
theorem B10697507 : Blo 2111435 10697507 := bstep (se 1 (by rfl) ⟨8023130, by rfl⟩ : syracuseStep 10697507 = 16046261) B16046261
theorem B7131671 : Blo 2111435 7131671 := bstep (se 1 (by rfl) ⟨5348753, by rfl⟩ : syracuseStep 7131671 = 10697507) B10697507
theorem B4754447 : Blo 2111435 4754447 := bstep (se 1 (by rfl) ⟨3565835, by rfl⟩ : syracuseStep 4754447 = 7131671) B7131671
theorem B3169631 : Blo 2111435 3169631 := bstep (se 1 (by rfl) ⟨2377223, by rfl⟩ : syracuseStep 3169631 = 4754447) B4754447
theorem B2113087 : Blo 2111435 2113087 := bstep (se 1 (by rfl) ⟨1584815, by rfl⟩ : syracuseStep 2113087 = 3169631) B3169631
theorem B3169637 : Blo 2111435 3169637 := bbase (se 4 (by rfl) ⟨297153, by rfl⟩ : syracuseStep 3169637 = 594307) (by norm_num)
theorem B2113091 : Blo 2111435 2113091 := bstep (se 1 (by rfl) ⟨1584818, by rfl⟩ : syracuseStep 2113091 = 3169637) B3169637
theorem B4011581 : Blo 2111435 4011581 := bbase (se 3 (by rfl) ⟨752171, by rfl⟩ : syracuseStep 4011581 = 1504343) (by norm_num)
theorem B2674387 : Blo 2111435 2674387 := bstep (se 1 (by rfl) ⟨2005790, by rfl⟩ : syracuseStep 2674387 = 4011581) B4011581
theorem B3565849 : Blo 2111435 3565849 := bstep (se 2 (by rfl) ⟨1337193, by rfl⟩ : syracuseStep 3565849 = 2674387) B2674387
theorem B4754465 : Blo 2111435 4754465 := bstep (se 2 (by rfl) ⟨1782924, by rfl⟩ : syracuseStep 4754465 = 3565849) B3565849
theorem B3169643 : Blo 2111435 3169643 := bstep (se 1 (by rfl) ⟨2377232, by rfl⟩ : syracuseStep 3169643 = 4754465) B4754465
theorem B2113095 : Blo 2111435 2113095 := bstep (se 1 (by rfl) ⟨1584821, by rfl⟩ : syracuseStep 2113095 = 3169643) B3169643
theorem B2377237 : Blo 2111435 2377237 := bbase (se 6 (by rfl) ⟨55716, by rfl⟩ : syracuseStep 2377237 = 111433) (by norm_num)
theorem B3169649 : Blo 2111435 3169649 := bstep (se 2 (by rfl) ⟨1188618, by rfl⟩ : syracuseStep 3169649 = 2377237) B2377237
theorem B2113099 : Blo 2111435 2113099 := bstep (se 1 (by rfl) ⟨1584824, by rfl⟩ : syracuseStep 2113099 = 3169649) B3169649
theorem B2674397 : Blo 2111435 2674397 := bbase (se 3 (by rfl) ⟨501449, by rfl⟩ : syracuseStep 2674397 = 1002899) (by norm_num)
theorem B7131725 : Blo 2111435 7131725 := bstep (se 3 (by rfl) ⟨1337198, by rfl⟩ : syracuseStep 7131725 = 2674397) B2674397
theorem B4754483 : Blo 2111435 4754483 := bstep (se 1 (by rfl) ⟨3565862, by rfl⟩ : syracuseStep 4754483 = 7131725) B7131725
theorem B3169655 : Blo 2111435 3169655 := bstep (se 1 (by rfl) ⟨2377241, by rfl⟩ : syracuseStep 3169655 = 4754483) B4754483
theorem B2113103 : Blo 2111435 2113103 := bstep (se 1 (by rfl) ⟨1584827, by rfl⟩ : syracuseStep 2113103 = 3169655) B3169655
theorem B3169661 : Blo 2111435 3169661 := bbase (se 3 (by rfl) ⟨594311, by rfl⟩ : syracuseStep 3169661 = 1188623) (by norm_num)
theorem B2113107 : Blo 2111435 2113107 := bstep (se 1 (by rfl) ⟨1584830, by rfl⟩ : syracuseStep 2113107 = 3169661) B3169661
theorem B4754501 : Blo 2111435 4754501 := bbase (se 4 (by rfl) ⟨445734, by rfl⟩ : syracuseStep 4754501 = 891469) (by norm_num)
theorem B3169667 : Blo 2111435 3169667 := bstep (se 1 (by rfl) ⟨2377250, by rfl⟩ : syracuseStep 3169667 = 4754501) B4754501
theorem B2113111 : Blo 2111435 2113111 := bstep (se 1 (by rfl) ⟨1584833, by rfl⟩ : syracuseStep 2113111 = 3169667) B3169667
theorem B6017429 : Blo 2111435 6017429 := bbase (se 6 (by rfl) ⟨141033, by rfl⟩ : syracuseStep 6017429 = 282067) (by norm_num)
theorem B4011619 : Blo 2111435 4011619 := bstep (se 1 (by rfl) ⟨3008714, by rfl⟩ : syracuseStep 4011619 = 6017429) B6017429
theorem B5348825 : Blo 2111435 5348825 := bstep (se 2 (by rfl) ⟨2005809, by rfl⟩ : syracuseStep 5348825 = 4011619) B4011619
theorem B3565883 : Blo 2111435 3565883 := bstep (se 1 (by rfl) ⟨2674412, by rfl⟩ : syracuseStep 3565883 = 5348825) B5348825
theorem B2377255 : Blo 2111435 2377255 := bstep (se 1 (by rfl) ⟨1782941, by rfl⟩ : syracuseStep 2377255 = 3565883) B3565883
theorem B3169673 : Blo 2111435 3169673 := bstep (se 2 (by rfl) ⟨1188627, by rfl⟩ : syracuseStep 3169673 = 2377255) B2377255
theorem B2113115 : Blo 2111435 2113115 := bstep (se 1 (by rfl) ⟨1584836, by rfl⟩ : syracuseStep 2113115 = 3169673) B3169673
theorem B10697669 : Blo 2111435 10697669 := bbase (se 4 (by rfl) ⟨1002906, by rfl⟩ : syracuseStep 10697669 = 2005813) (by norm_num)
theorem B7131779 : Blo 2111435 7131779 := bstep (se 1 (by rfl) ⟨5348834, by rfl⟩ : syracuseStep 7131779 = 10697669) B10697669
theorem B4754519 : Blo 2111435 4754519 := bstep (se 1 (by rfl) ⟨3565889, by rfl⟩ : syracuseStep 4754519 = 7131779) B7131779
theorem B3169679 : Blo 2111435 3169679 := bstep (se 1 (by rfl) ⟨2377259, by rfl⟩ : syracuseStep 3169679 = 4754519) B4754519
theorem B2113119 : Blo 2111435 2113119 := bstep (se 1 (by rfl) ⟨1584839, by rfl⟩ : syracuseStep 2113119 = 3169679) B3169679
theorem B3169685 : Blo 2111435 3169685 := bbase (se 6 (by rfl) ⟨74289, by rfl⟩ : syracuseStep 3169685 = 148579) (by norm_num)
theorem B2113123 : Blo 2111435 2113123 := bstep (se 1 (by rfl) ⟨1584842, by rfl⟩ : syracuseStep 2113123 = 3169685) B3169685
theorem B3614557 : Blo 2111435 3614557 := bbase (se 3 (by rfl) ⟨677729, by rfl⟩ : syracuseStep 3614557 = 1355459) (by norm_num)
theorem B4819409 : Blo 2111435 4819409 := bstep (se 2 (by rfl) ⟨1807278, by rfl⟩ : syracuseStep 4819409 = 3614557) B3614557
theorem B3212939 : Blo 2111435 3212939 := bstep (se 1 (by rfl) ⟨2409704, by rfl⟩ : syracuseStep 3212939 = 4819409) B4819409
theorem B2141959 : Blo 2111435 2141959 := bstep (se 1 (by rfl) ⟨1606469, by rfl⟩ : syracuseStep 2141959 = 3212939) B3212939
theorem B2855945 : Blo 2111435 2855945 := bstep (se 2 (by rfl) ⟨1070979, by rfl⟩ : syracuseStep 2855945 = 2141959) B2141959
theorem B7615853 : Blo 2111435 7615853 := bstep (se 3 (by rfl) ⟨1427972, by rfl⟩ : syracuseStep 7615853 = 2855945) B2855945
theorem B5077235 : Blo 2111435 5077235 := bstep (se 1 (by rfl) ⟨3807926, by rfl⟩ : syracuseStep 5077235 = 7615853) B7615853
theorem B3384823 : Blo 2111435 3384823 := bstep (se 1 (by rfl) ⟨2538617, by rfl⟩ : syracuseStep 3384823 = 5077235) B5077235
theorem B4513097 : Blo 2111435 4513097 := bstep (se 2 (by rfl) ⟨1692411, by rfl⟩ : syracuseStep 4513097 = 3384823) B3384823
theorem B12034925 : Blo 2111435 12034925 := bstep (se 3 (by rfl) ⟨2256548, by rfl⟩ : syracuseStep 12034925 = 4513097) B4513097
theorem B8023283 : Blo 2111435 8023283 := bstep (se 1 (by rfl) ⟨6017462, by rfl⟩ : syracuseStep 8023283 = 12034925) B12034925
theorem B5348855 : Blo 2111435 5348855 := bstep (se 1 (by rfl) ⟨4011641, by rfl⟩ : syracuseStep 5348855 = 8023283) B8023283
theorem B3565903 : Blo 2111435 3565903 := bstep (se 1 (by rfl) ⟨2674427, by rfl⟩ : syracuseStep 3565903 = 5348855) B5348855
theorem B4754537 : Blo 2111435 4754537 := bstep (se 2 (by rfl) ⟨1782951, by rfl⟩ : syracuseStep 4754537 = 3565903) B3565903
theorem B3169691 : Blo 2111435 3169691 := bstep (se 1 (by rfl) ⟨2377268, by rfl⟩ : syracuseStep 3169691 = 4754537) B4754537
theorem B2113127 : Blo 2111435 2113127 := bstep (se 1 (by rfl) ⟨1584845, by rfl⟩ : syracuseStep 2113127 = 3169691) B3169691
theorem B2377273 : Blo 2111435 2377273 := bbase (se 2 (by rfl) ⟨891477, by rfl⟩ : syracuseStep 2377273 = 1782955) (by norm_num)
theorem B3169697 : Blo 2111435 3169697 := bstep (se 2 (by rfl) ⟨1188636, by rfl⟩ : syracuseStep 3169697 = 2377273) B2377273
theorem B2113131 : Blo 2111435 2113131 := bstep (se 1 (by rfl) ⟨1584848, by rfl⟩ : syracuseStep 2113131 = 3169697) B3169697
theorem B2256557 : Blo 2111435 2256557 := bbase (se 3 (by rfl) ⟨423104, by rfl⟩ : syracuseStep 2256557 = 846209) (by norm_num)
theorem B6017485 : Blo 2111435 6017485 := bstep (se 3 (by rfl) ⟨1128278, by rfl⟩ : syracuseStep 6017485 = 2256557) B2256557
theorem B8023313 : Blo 2111435 8023313 := bstep (se 2 (by rfl) ⟨3008742, by rfl⟩ : syracuseStep 8023313 = 6017485) B6017485
theorem B5348875 : Blo 2111435 5348875 := bstep (se 1 (by rfl) ⟨4011656, by rfl⟩ : syracuseStep 5348875 = 8023313) B8023313
theorem B7131833 : Blo 2111435 7131833 := bstep (se 2 (by rfl) ⟨2674437, by rfl⟩ : syracuseStep 7131833 = 5348875) B5348875
theorem B4754555 : Blo 2111435 4754555 := bstep (se 1 (by rfl) ⟨3565916, by rfl⟩ : syracuseStep 4754555 = 7131833) B7131833
theorem B3169703 : Blo 2111435 3169703 := bstep (se 1 (by rfl) ⟨2377277, by rfl⟩ : syracuseStep 3169703 = 4754555) B4754555
theorem B2113135 : Blo 2111435 2113135 := bstep (se 1 (by rfl) ⟨1584851, by rfl⟩ : syracuseStep 2113135 = 3169703) B3169703
theorem B3169709 : Blo 2111435 3169709 := bbase (se 3 (by rfl) ⟨594320, by rfl⟩ : syracuseStep 3169709 = 1188641) (by norm_num)
theorem B2113139 : Blo 2111435 2113139 := bstep (se 1 (by rfl) ⟨1584854, by rfl⟩ : syracuseStep 2113139 = 3169709) B3169709
theorem B4754573 : Blo 2111435 4754573 := bbase (se 3 (by rfl) ⟨891482, by rfl⟩ : syracuseStep 4754573 = 1782965) (by norm_num)
theorem B3169715 : Blo 2111435 3169715 := bstep (se 1 (by rfl) ⟨2377286, by rfl⟩ : syracuseStep 3169715 = 4754573) B4754573
theorem B2113143 : Blo 2111435 2113143 := bstep (se 1 (by rfl) ⟨1584857, by rfl⟩ : syracuseStep 2113143 = 3169715) B3169715
theorem B2674453 : Blo 2111435 2674453 := bbase (se 6 (by rfl) ⟨62682, by rfl⟩ : syracuseStep 2674453 = 125365) (by norm_num)
theorem B3565937 : Blo 2111435 3565937 := bstep (se 2 (by rfl) ⟨1337226, by rfl⟩ : syracuseStep 3565937 = 2674453) B2674453
theorem B2377291 : Blo 2111435 2377291 := bstep (se 1 (by rfl) ⟨1782968, by rfl⟩ : syracuseStep 2377291 = 3565937) B3565937
theorem B3169721 : Blo 2111435 3169721 := bstep (se 2 (by rfl) ⟨1188645, by rfl⟩ : syracuseStep 3169721 = 2377291) B2377291
theorem B2113147 : Blo 2111435 2113147 := bstep (se 1 (by rfl) ⟨1584860, by rfl⟩ : syracuseStep 2113147 = 3169721) B3169721
theorem B5421893 : Blo 2111435 5421893 := bbase (se 4 (by rfl) ⟨508302, by rfl⟩ : syracuseStep 5421893 = 1016605) (by norm_num)
theorem B14458381 : Blo 2111435 14458381 := bstep (se 3 (by rfl) ⟨2710946, by rfl⟩ : syracuseStep 14458381 = 5421893) B5421893
theorem B77111365 : Blo 2111435 77111365 := bstep (se 4 (by rfl) ⟨7229190, by rfl⟩ : syracuseStep 77111365 = 14458381) B14458381
theorem B102815153 : Blo 2111435 102815153 := bstep (se 2 (by rfl) ⟨38555682, by rfl⟩ : syracuseStep 102815153 = 77111365) B77111365
theorem B68543435 : Blo 2111435 68543435 := bstep (se 1 (by rfl) ⟨51407576, by rfl⟩ : syracuseStep 68543435 = 102815153) B102815153
theorem B45695623 : Blo 2111435 45695623 := bstep (se 1 (by rfl) ⟨34271717, by rfl⟩ : syracuseStep 45695623 = 68543435) B68543435
theorem B60927497 : Blo 2111435 60927497 := bstep (se 2 (by rfl) ⟨22847811, by rfl⟩ : syracuseStep 60927497 = 45695623) B45695623
theorem B40618331 : Blo 2111435 40618331 := bstep (se 1 (by rfl) ⟨30463748, by rfl⟩ : syracuseStep 40618331 = 60927497) B60927497
theorem B27078887 : Blo 2111435 27078887 := bstep (se 1 (by rfl) ⟨20309165, by rfl⟩ : syracuseStep 27078887 = 40618331) B40618331
theorem B18052591 : Blo 2111435 18052591 := bstep (se 1 (by rfl) ⟨13539443, by rfl⟩ : syracuseStep 18052591 = 27078887) B27078887
theorem B24070121 : Blo 2111435 24070121 := bstep (se 2 (by rfl) ⟨9026295, by rfl⟩ : syracuseStep 24070121 = 18052591) B18052591
theorem B16046747 : Blo 2111435 16046747 := bstep (se 1 (by rfl) ⟨12035060, by rfl⟩ : syracuseStep 16046747 = 24070121) B24070121
theorem B10697831 : Blo 2111435 10697831 := bstep (se 1 (by rfl) ⟨8023373, by rfl⟩ : syracuseStep 10697831 = 16046747) B16046747
theorem B7131887 : Blo 2111435 7131887 := bstep (se 1 (by rfl) ⟨5348915, by rfl⟩ : syracuseStep 7131887 = 10697831) B10697831
theorem B4754591 : Blo 2111435 4754591 := bstep (se 1 (by rfl) ⟨3565943, by rfl⟩ : syracuseStep 4754591 = 7131887) B7131887
theorem B3169727 : Blo 2111435 3169727 := bstep (se 1 (by rfl) ⟨2377295, by rfl⟩ : syracuseStep 3169727 = 4754591) B4754591
theorem B2113151 : Blo 2111435 2113151 := bstep (se 1 (by rfl) ⟨1584863, by rfl⟩ : syracuseStep 2113151 = 3169727) B3169727
theorem B3169733 : Blo 2111435 3169733 := bbase (se 4 (by rfl) ⟨297162, by rfl⟩ : syracuseStep 3169733 = 594325) (by norm_num)
theorem B2113155 : Blo 2111435 2113155 := bstep (se 1 (by rfl) ⟨1584866, by rfl⟩ : syracuseStep 2113155 = 3169733) B3169733
theorem B3565957 : Blo 2111435 3565957 := bbase (se 4 (by rfl) ⟨334308, by rfl⟩ : syracuseStep 3565957 = 668617) (by norm_num)
theorem B4754609 : Blo 2111435 4754609 := bstep (se 2 (by rfl) ⟨1782978, by rfl⟩ : syracuseStep 4754609 = 3565957) B3565957
theorem B3169739 : Blo 2111435 3169739 := bstep (se 1 (by rfl) ⟨2377304, by rfl⟩ : syracuseStep 3169739 = 4754609) B4754609
theorem B2113159 : Blo 2111435 2113159 := bstep (se 1 (by rfl) ⟨1584869, by rfl⟩ : syracuseStep 2113159 = 3169739) B3169739
theorem B2377309 : Blo 2111435 2377309 := bbase (se 3 (by rfl) ⟨445745, by rfl⟩ : syracuseStep 2377309 = 891491) (by norm_num)
theorem B3169745 : Blo 2111435 3169745 := bstep (se 2 (by rfl) ⟨1188654, by rfl⟩ : syracuseStep 3169745 = 2377309) B2377309
theorem B2113163 : Blo 2111435 2113163 := bstep (se 1 (by rfl) ⟨1584872, by rfl⟩ : syracuseStep 2113163 = 3169745) B3169745
theorem B7131941 : Blo 2111435 7131941 := bbase (se 4 (by rfl) ⟨668619, by rfl⟩ : syracuseStep 7131941 = 1337239) (by norm_num)
theorem B4754627 : Blo 2111435 4754627 := bstep (se 1 (by rfl) ⟨3565970, by rfl⟩ : syracuseStep 4754627 = 7131941) B7131941
theorem B3169751 : Blo 2111435 3169751 := bstep (se 1 (by rfl) ⟨2377313, by rfl⟩ : syracuseStep 3169751 = 4754627) B4754627
theorem B2113167 : Blo 2111435 2113167 := bstep (se 1 (by rfl) ⟨1584875, by rfl⟩ : syracuseStep 2113167 = 3169751) B3169751
theorem B3169757 : Blo 2111435 3169757 := bbase (se 3 (by rfl) ⟨594329, by rfl⟩ : syracuseStep 3169757 = 1188659) (by norm_num)
theorem B2113171 : Blo 2111435 2113171 := bstep (se 1 (by rfl) ⟨1584878, by rfl⟩ : syracuseStep 2113171 = 3169757) B3169757
theorem B4754645 : Blo 2111435 4754645 := bbase (se 7 (by rfl) ⟨55718, by rfl⟩ : syracuseStep 4754645 = 111437) (by norm_num)
theorem B3169763 : Blo 2111435 3169763 := bstep (se 1 (by rfl) ⟨2377322, by rfl⟩ : syracuseStep 3169763 = 4754645) B4754645
theorem B2113175 : Blo 2111435 2113175 := bstep (se 1 (by rfl) ⟨1584881, by rfl⟩ : syracuseStep 2113175 = 3169763) B3169763
theorem B6769813 : Blo 2111435 6769813 := bbase (se 6 (by rfl) ⟨158667, by rfl⟩ : syracuseStep 6769813 = 317335) (by norm_num)
theorem B9026417 : Blo 2111435 9026417 := bstep (se 2 (by rfl) ⟨3384906, by rfl⟩ : syracuseStep 9026417 = 6769813) B6769813
theorem B6017611 : Blo 2111435 6017611 := bstep (se 1 (by rfl) ⟨4513208, by rfl⟩ : syracuseStep 6017611 = 9026417) B9026417
theorem B8023481 : Blo 2111435 8023481 := bstep (se 2 (by rfl) ⟨3008805, by rfl⟩ : syracuseStep 8023481 = 6017611) B6017611
theorem B5348987 : Blo 2111435 5348987 := bstep (se 1 (by rfl) ⟨4011740, by rfl⟩ : syracuseStep 5348987 = 8023481) B8023481
theorem B3565991 : Blo 2111435 3565991 := bstep (se 1 (by rfl) ⟨2674493, by rfl⟩ : syracuseStep 3565991 = 5348987) B5348987
theorem B2377327 : Blo 2111435 2377327 := bstep (se 1 (by rfl) ⟨1782995, by rfl⟩ : syracuseStep 2377327 = 3565991) B3565991
theorem B3169769 : Blo 2111435 3169769 := bstep (se 2 (by rfl) ⟨1188663, by rfl⟩ : syracuseStep 3169769 = 2377327) B2377327
theorem B2113179 : Blo 2111435 2113179 := bstep (se 1 (by rfl) ⟨1584884, by rfl⟩ : syracuseStep 2113179 = 3169769) B3169769
theorem B7616053 : Blo 2111435 7616053 := bbase (se 5 (by rfl) ⟨357002, by rfl⟩ : syracuseStep 7616053 = 714005) (by norm_num)
theorem B10154737 : Blo 2111435 10154737 := bstep (se 2 (by rfl) ⟨3808026, by rfl⟩ : syracuseStep 10154737 = 7616053) B7616053
theorem B13539649 : Blo 2111435 13539649 := bstep (se 2 (by rfl) ⟨5077368, by rfl⟩ : syracuseStep 13539649 = 10154737) B10154737
theorem B18052865 : Blo 2111435 18052865 := bstep (se 2 (by rfl) ⟨6769824, by rfl⟩ : syracuseStep 18052865 = 13539649) B13539649
theorem B12035243 : Blo 2111435 12035243 := bstep (se 1 (by rfl) ⟨9026432, by rfl⟩ : syracuseStep 12035243 = 18052865) B18052865
theorem B8023495 : Blo 2111435 8023495 := bstep (se 1 (by rfl) ⟨6017621, by rfl⟩ : syracuseStep 8023495 = 12035243) B12035243
theorem B10697993 : Blo 2111435 10697993 := bstep (se 2 (by rfl) ⟨4011747, by rfl⟩ : syracuseStep 10697993 = 8023495) B8023495
theorem B7131995 : Blo 2111435 7131995 := bstep (se 1 (by rfl) ⟨5348996, by rfl⟩ : syracuseStep 7131995 = 10697993) B10697993
theorem B4754663 : Blo 2111435 4754663 := bstep (se 1 (by rfl) ⟨3565997, by rfl⟩ : syracuseStep 4754663 = 7131995) B7131995
theorem B3169775 : Blo 2111435 3169775 := bstep (se 1 (by rfl) ⟨2377331, by rfl⟩ : syracuseStep 3169775 = 4754663) B4754663
theorem B2113183 : Blo 2111435 2113183 := bstep (se 1 (by rfl) ⟨1584887, by rfl⟩ : syracuseStep 2113183 = 3169775) B3169775
theorem B3169781 : Blo 2111435 3169781 := bbase (se 5 (by rfl) ⟨148583, by rfl⟩ : syracuseStep 3169781 = 297167) (by norm_num)
theorem B2113187 : Blo 2111435 2113187 := bstep (se 1 (by rfl) ⟨1584890, by rfl⟩ : syracuseStep 2113187 = 3169781) B3169781
theorem B2256617 : Blo 2111435 2256617 := bbase (se 2 (by rfl) ⟨846231, by rfl⟩ : syracuseStep 2256617 = 1692463) (by norm_num)
theorem B6017645 : Blo 2111435 6017645 := bstep (se 3 (by rfl) ⟨1128308, by rfl⟩ : syracuseStep 6017645 = 2256617) B2256617
theorem B4011763 : Blo 2111435 4011763 := bstep (se 1 (by rfl) ⟨3008822, by rfl⟩ : syracuseStep 4011763 = 6017645) B6017645
theorem B5349017 : Blo 2111435 5349017 := bstep (se 2 (by rfl) ⟨2005881, by rfl⟩ : syracuseStep 5349017 = 4011763) B4011763
theorem B3566011 : Blo 2111435 3566011 := bstep (se 1 (by rfl) ⟨2674508, by rfl⟩ : syracuseStep 3566011 = 5349017) B5349017
theorem B4754681 : Blo 2111435 4754681 := bstep (se 2 (by rfl) ⟨1783005, by rfl⟩ : syracuseStep 4754681 = 3566011) B3566011
theorem B3169787 : Blo 2111435 3169787 := bstep (se 1 (by rfl) ⟨2377340, by rfl⟩ : syracuseStep 3169787 = 4754681) B4754681
theorem B2113191 : Blo 2111435 2113191 := bstep (se 1 (by rfl) ⟨1584893, by rfl⟩ : syracuseStep 2113191 = 3169787) B3169787
theorem B2377345 : Blo 2111435 2377345 := bbase (se 2 (by rfl) ⟨891504, by rfl⟩ : syracuseStep 2377345 = 1783009) (by norm_num)
theorem B3169793 : Blo 2111435 3169793 := bstep (se 2 (by rfl) ⟨1188672, by rfl⟩ : syracuseStep 3169793 = 2377345) B2377345
theorem B2113195 : Blo 2111435 2113195 := bstep (se 1 (by rfl) ⟨1584896, by rfl⟩ : syracuseStep 2113195 = 3169793) B3169793
theorem B5349037 : Blo 2111435 5349037 := bbase (se 3 (by rfl) ⟨1002944, by rfl⟩ : syracuseStep 5349037 = 2005889) (by norm_num)
theorem B7132049 : Blo 2111435 7132049 := bstep (se 2 (by rfl) ⟨2674518, by rfl⟩ : syracuseStep 7132049 = 5349037) B5349037
theorem B4754699 : Blo 2111435 4754699 := bstep (se 1 (by rfl) ⟨3566024, by rfl⟩ : syracuseStep 4754699 = 7132049) B7132049
theorem B3169799 : Blo 2111435 3169799 := bstep (se 1 (by rfl) ⟨2377349, by rfl⟩ : syracuseStep 3169799 = 4754699) B4754699
theorem B2113199 : Blo 2111435 2113199 := bstep (se 1 (by rfl) ⟨1584899, by rfl⟩ : syracuseStep 2113199 = 3169799) B3169799
theorem B3169805 : Blo 2111435 3169805 := bbase (se 3 (by rfl) ⟨594338, by rfl⟩ : syracuseStep 3169805 = 1188677) (by norm_num)
theorem B2113203 : Blo 2111435 2113203 := bstep (se 1 (by rfl) ⟨1584902, by rfl⟩ : syracuseStep 2113203 = 3169805) B3169805
theorem B4754717 : Blo 2111435 4754717 := bbase (se 3 (by rfl) ⟨891509, by rfl⟩ : syracuseStep 4754717 = 1783019) (by norm_num)
theorem B3169811 : Blo 2111435 3169811 := bstep (se 1 (by rfl) ⟨2377358, by rfl⟩ : syracuseStep 3169811 = 4754717) B4754717
theorem B2113207 : Blo 2111435 2113207 := bstep (se 1 (by rfl) ⟨1584905, by rfl⟩ : syracuseStep 2113207 = 3169811) B3169811
theorem B3566045 : Blo 2111435 3566045 := bbase (se 3 (by rfl) ⟨668633, by rfl⟩ : syracuseStep 3566045 = 1337267) (by norm_num)
theorem B2377363 : Blo 2111435 2377363 := bstep (se 1 (by rfl) ⟨1783022, by rfl⟩ : syracuseStep 2377363 = 3566045) B3566045
theorem B3169817 : Blo 2111435 3169817 := bstep (se 2 (by rfl) ⟨1188681, by rfl⟩ : syracuseStep 3169817 = 2377363) B2377363
theorem B2113211 : Blo 2111435 2113211 := bstep (se 1 (by rfl) ⟨1584908, by rfl⟩ : syracuseStep 2113211 = 3169817) B3169817
theorem B13027637 : Blo 2111435 13027637 := bbase (se 5 (by rfl) ⟨610670, by rfl⟩ : syracuseStep 13027637 = 1221341) (by norm_num)
theorem B8685091 : Blo 2111435 8685091 := bstep (se 1 (by rfl) ⟨6513818, by rfl⟩ : syracuseStep 8685091 = 13027637) B13027637
theorem B11580121 : Blo 2111435 11580121 := bstep (se 2 (by rfl) ⟨4342545, by rfl⟩ : syracuseStep 11580121 = 8685091) B8685091
theorem B15440161 : Blo 2111435 15440161 := bstep (se 2 (by rfl) ⟨5790060, by rfl⟩ : syracuseStep 15440161 = 11580121) B11580121
theorem B20586881 : Blo 2111435 20586881 := bstep (se 2 (by rfl) ⟨7720080, by rfl⟩ : syracuseStep 20586881 = 15440161) B15440161
theorem B13724587 : Blo 2111435 13724587 := bstep (se 1 (by rfl) ⟨10293440, by rfl⟩ : syracuseStep 13724587 = 20586881) B20586881
theorem B18299449 : Blo 2111435 18299449 := bstep (se 2 (by rfl) ⟨6862293, by rfl⟩ : syracuseStep 18299449 = 13724587) B13724587
theorem B24399265 : Blo 2111435 24399265 := bstep (se 2 (by rfl) ⟨9149724, by rfl⟩ : syracuseStep 24399265 = 18299449) B18299449
theorem B32532353 : Blo 2111435 32532353 := bstep (se 2 (by rfl) ⟨12199632, by rfl⟩ : syracuseStep 32532353 = 24399265) B24399265
theorem B21688235 : Blo 2111435 21688235 := bstep (se 1 (by rfl) ⟨16266176, by rfl⟩ : syracuseStep 21688235 = 32532353) B32532353
theorem B14458823 : Blo 2111435 14458823 := bstep (se 1 (by rfl) ⟨10844117, by rfl⟩ : syracuseStep 14458823 = 21688235) B21688235
theorem B9639215 : Blo 2111435 9639215 := bstep (se 1 (by rfl) ⟨7229411, by rfl⟩ : syracuseStep 9639215 = 14458823) B14458823
theorem B6426143 : Blo 2111435 6426143 := bstep (se 1 (by rfl) ⟨4819607, by rfl⟩ : syracuseStep 6426143 = 9639215) B9639215
theorem B4284095 : Blo 2111435 4284095 := bstep (se 1 (by rfl) ⟨3213071, by rfl⟩ : syracuseStep 4284095 = 6426143) B6426143
theorem B11424253 : Blo 2111435 11424253 := bstep (se 3 (by rfl) ⟨2142047, by rfl⟩ : syracuseStep 11424253 = 4284095) B4284095
theorem B15232337 : Blo 2111435 15232337 := bstep (se 2 (by rfl) ⟨5712126, by rfl⟩ : syracuseStep 15232337 = 11424253) B11424253
theorem B10154891 : Blo 2111435 10154891 := bstep (se 1 (by rfl) ⟨7616168, by rfl⟩ : syracuseStep 10154891 = 15232337) B15232337
theorem B6769927 : Blo 2111435 6769927 := bstep (se 1 (by rfl) ⟨5077445, by rfl⟩ : syracuseStep 6769927 = 10154891) B10154891
theorem B9026569 : Blo 2111435 9026569 := bstep (se 2 (by rfl) ⟨3384963, by rfl⟩ : syracuseStep 9026569 = 6769927) B6769927
theorem B12035425 : Blo 2111435 12035425 := bstep (se 2 (by rfl) ⟨4513284, by rfl⟩ : syracuseStep 12035425 = 9026569) B9026569
theorem B16047233 : Blo 2111435 16047233 := bstep (se 2 (by rfl) ⟨6017712, by rfl⟩ : syracuseStep 16047233 = 12035425) B12035425
theorem B10698155 : Blo 2111435 10698155 := bstep (se 1 (by rfl) ⟨8023616, by rfl⟩ : syracuseStep 10698155 = 16047233) B16047233
theorem B7132103 : Blo 2111435 7132103 := bstep (se 1 (by rfl) ⟨5349077, by rfl⟩ : syracuseStep 7132103 = 10698155) B10698155
theorem B4754735 : Blo 2111435 4754735 := bstep (se 1 (by rfl) ⟨3566051, by rfl⟩ : syracuseStep 4754735 = 7132103) B7132103
theorem B3169823 : Blo 2111435 3169823 := bstep (se 1 (by rfl) ⟨2377367, by rfl⟩ : syracuseStep 3169823 = 4754735) B4754735
theorem B2113215 : Blo 2111435 2113215 := bstep (se 1 (by rfl) ⟨1584911, by rfl⟩ : syracuseStep 2113215 = 3169823) B3169823
theorem B3169829 : Blo 2111435 3169829 := bbase (se 4 (by rfl) ⟨297171, by rfl⟩ : syracuseStep 3169829 = 594343) (by norm_num)
theorem B2113219 : Blo 2111435 2113219 := bstep (se 1 (by rfl) ⟨1584914, by rfl⟩ : syracuseStep 2113219 = 3169829) B3169829
theorem B2674549 : Blo 2111435 2674549 := bbase (se 5 (by rfl) ⟨125369, by rfl⟩ : syracuseStep 2674549 = 250739) (by norm_num)
theorem B3566065 : Blo 2111435 3566065 := bstep (se 2 (by rfl) ⟨1337274, by rfl⟩ : syracuseStep 3566065 = 2674549) B2674549
theorem B4754753 : Blo 2111435 4754753 := bstep (se 2 (by rfl) ⟨1783032, by rfl⟩ : syracuseStep 4754753 = 3566065) B3566065
theorem B3169835 : Blo 2111435 3169835 := bstep (se 1 (by rfl) ⟨2377376, by rfl⟩ : syracuseStep 3169835 = 4754753) B4754753
theorem B2113223 : Blo 2111435 2113223 := bstep (se 1 (by rfl) ⟨1584917, by rfl⟩ : syracuseStep 2113223 = 3169835) B3169835
theorem B2377381 : Blo 2111435 2377381 := bbase (se 4 (by rfl) ⟨222879, by rfl⟩ : syracuseStep 2377381 = 445759) (by norm_num)
theorem B3169841 : Blo 2111435 3169841 := bstep (se 2 (by rfl) ⟨1188690, by rfl⟩ : syracuseStep 3169841 = 2377381) B2377381
theorem B2113227 : Blo 2111435 2113227 := bstep (se 1 (by rfl) ⟨1584920, by rfl⟩ : syracuseStep 2113227 = 3169841) B3169841
theorem B11424341 : Blo 2111435 11424341 := bbase (se 8 (by rfl) ⟨66939, by rfl⟩ : syracuseStep 11424341 = 133879) (by norm_num)
theorem B30464909 : Blo 2111435 30464909 := bstep (se 3 (by rfl) ⟨5712170, by rfl⟩ : syracuseStep 30464909 = 11424341) B11424341
theorem B20309939 : Blo 2111435 20309939 := bstep (se 1 (by rfl) ⟨15232454, by rfl⟩ : syracuseStep 20309939 = 30464909) B30464909
theorem B13539959 : Blo 2111435 13539959 := bstep (se 1 (by rfl) ⟨10154969, by rfl⟩ : syracuseStep 13539959 = 20309939) B20309939
theorem B9026639 : Blo 2111435 9026639 := bstep (se 1 (by rfl) ⟨6769979, by rfl⟩ : syracuseStep 9026639 = 13539959) B13539959
theorem B6017759 : Blo 2111435 6017759 := bstep (se 1 (by rfl) ⟨4513319, by rfl⟩ : syracuseStep 6017759 = 9026639) B9026639
theorem B4011839 : Blo 2111435 4011839 := bstep (se 1 (by rfl) ⟨3008879, by rfl⟩ : syracuseStep 4011839 = 6017759) B6017759
theorem B2674559 : Blo 2111435 2674559 := bstep (se 1 (by rfl) ⟨2005919, by rfl⟩ : syracuseStep 2674559 = 4011839) B4011839
theorem B7132157 : Blo 2111435 7132157 := bstep (se 3 (by rfl) ⟨1337279, by rfl⟩ : syracuseStep 7132157 = 2674559) B2674559
theorem B4754771 : Blo 2111435 4754771 := bstep (se 1 (by rfl) ⟨3566078, by rfl⟩ : syracuseStep 4754771 = 7132157) B7132157
theorem B3169847 : Blo 2111435 3169847 := bstep (se 1 (by rfl) ⟨2377385, by rfl⟩ : syracuseStep 3169847 = 4754771) B4754771
theorem B2113231 : Blo 2111435 2113231 := bstep (se 1 (by rfl) ⟨1584923, by rfl⟩ : syracuseStep 2113231 = 3169847) B3169847
theorem B3169853 : Blo 2111435 3169853 := bbase (se 3 (by rfl) ⟨594347, by rfl⟩ : syracuseStep 3169853 = 1188695) (by norm_num)
theorem B2113235 : Blo 2111435 2113235 := bstep (se 1 (by rfl) ⟨1584926, by rfl⟩ : syracuseStep 2113235 = 3169853) B3169853
theorem B4754789 : Blo 2111435 4754789 := bbase (se 4 (by rfl) ⟨445761, by rfl⟩ : syracuseStep 4754789 = 891523) (by norm_num)
theorem B3169859 : Blo 2111435 3169859 := bstep (se 1 (by rfl) ⟨2377394, by rfl⟩ : syracuseStep 3169859 = 4754789) B4754789
theorem B2113239 : Blo 2111435 2113239 := bstep (se 1 (by rfl) ⟨1584929, by rfl⟩ : syracuseStep 2113239 = 3169859) B3169859
theorem B5349149 : Blo 2111435 5349149 := bbase (se 3 (by rfl) ⟨1002965, by rfl⟩ : syracuseStep 5349149 = 2005931) (by norm_num)
theorem B3566099 : Blo 2111435 3566099 := bstep (se 1 (by rfl) ⟨2674574, by rfl⟩ : syracuseStep 3566099 = 5349149) B5349149
theorem B2377399 : Blo 2111435 2377399 := bstep (se 1 (by rfl) ⟨1783049, by rfl⟩ : syracuseStep 2377399 = 3566099) B3566099
theorem B3169865 : Blo 2111435 3169865 := bstep (se 2 (by rfl) ⟨1188699, by rfl⟩ : syracuseStep 3169865 = 2377399) B2377399
theorem B2113243 : Blo 2111435 2113243 := bstep (se 1 (by rfl) ⟨1584932, by rfl⟩ : syracuseStep 2113243 = 3169865) B3169865
theorem B4011869 : Blo 2111435 4011869 := bbase (se 3 (by rfl) ⟨752225, by rfl⟩ : syracuseStep 4011869 = 1504451) (by norm_num)
theorem B10698317 : Blo 2111435 10698317 := bstep (se 3 (by rfl) ⟨2005934, by rfl⟩ : syracuseStep 10698317 = 4011869) B4011869
theorem B7132211 : Blo 2111435 7132211 := bstep (se 1 (by rfl) ⟨5349158, by rfl⟩ : syracuseStep 7132211 = 10698317) B10698317
theorem B4754807 : Blo 2111435 4754807 := bstep (se 1 (by rfl) ⟨3566105, by rfl⟩ : syracuseStep 4754807 = 7132211) B7132211
theorem B3169871 : Blo 2111435 3169871 := bstep (se 1 (by rfl) ⟨2377403, by rfl⟩ : syracuseStep 3169871 = 4754807) B4754807
theorem B2113247 : Blo 2111435 2113247 := bstep (se 1 (by rfl) ⟨1584935, by rfl⟩ : syracuseStep 2113247 = 3169871) B3169871
theorem B3169877 : Blo 2111435 3169877 := bbase (se 8 (by rfl) ⟨18573, by rfl⟩ : syracuseStep 3169877 = 37147) (by norm_num)
theorem B2113251 : Blo 2111435 2113251 := bstep (se 1 (by rfl) ⟨1584938, by rfl⟩ : syracuseStep 2113251 = 3169877) B3169877
theorem B9026741 : Blo 2111435 9026741 := bbase (se 5 (by rfl) ⟨423128, by rfl⟩ : syracuseStep 9026741 = 846257) (by norm_num)
theorem B6017827 : Blo 2111435 6017827 := bstep (se 1 (by rfl) ⟨4513370, by rfl⟩ : syracuseStep 6017827 = 9026741) B9026741
theorem B8023769 : Blo 2111435 8023769 := bstep (se 2 (by rfl) ⟨3008913, by rfl⟩ : syracuseStep 8023769 = 6017827) B6017827
theorem B5349179 : Blo 2111435 5349179 := bstep (se 1 (by rfl) ⟨4011884, by rfl⟩ : syracuseStep 5349179 = 8023769) B8023769
theorem B3566119 : Blo 2111435 3566119 := bstep (se 1 (by rfl) ⟨2674589, by rfl⟩ : syracuseStep 3566119 = 5349179) B5349179
theorem B4754825 : Blo 2111435 4754825 := bstep (se 2 (by rfl) ⟨1783059, by rfl⟩ : syracuseStep 4754825 = 3566119) B3566119
theorem B3169883 : Blo 2111435 3169883 := bstep (se 1 (by rfl) ⟨2377412, by rfl⟩ : syracuseStep 3169883 = 4754825) B4754825
theorem B2113255 : Blo 2111435 2113255 := bstep (se 1 (by rfl) ⟨1584941, by rfl⟩ : syracuseStep 2113255 = 3169883) B3169883
theorem B2377417 : Blo 2111435 2377417 := bbase (se 2 (by rfl) ⟨891531, by rfl⟩ : syracuseStep 2377417 = 1783063) (by norm_num)
theorem B3169889 : Blo 2111435 3169889 := bstep (se 2 (by rfl) ⟨1188708, by rfl⟩ : syracuseStep 3169889 = 2377417) B2377417
theorem B2113259 : Blo 2111435 2113259 := bstep (se 1 (by rfl) ⟨1584944, by rfl⟩ : syracuseStep 2113259 = 3169889) B3169889
theorem B3614789 : Blo 2111435 3614789 := bbase (se 4 (by rfl) ⟨338886, by rfl⟩ : syracuseStep 3614789 = 677773) (by norm_num)
theorem B2409859 : Blo 2111435 2409859 := bstep (se 1 (by rfl) ⟨1807394, by rfl⟩ : syracuseStep 2409859 = 3614789) B3614789
theorem B3213145 : Blo 2111435 3213145 := bstep (se 2 (by rfl) ⟨1204929, by rfl⟩ : syracuseStep 3213145 = 2409859) B2409859
theorem B4284193 : Blo 2111435 4284193 := bstep (se 2 (by rfl) ⟨1606572, by rfl⟩ : syracuseStep 4284193 = 3213145) B3213145
theorem B5712257 : Blo 2111435 5712257 := bstep (se 2 (by rfl) ⟨2142096, by rfl⟩ : syracuseStep 5712257 = 4284193) B4284193
theorem B3808171 : Blo 2111435 3808171 := bstep (se 1 (by rfl) ⟨2856128, by rfl⟩ : syracuseStep 3808171 = 5712257) B5712257
theorem B5077561 : Blo 2111435 5077561 := bstep (se 2 (by rfl) ⟨1904085, by rfl⟩ : syracuseStep 5077561 = 3808171) B3808171
theorem B6770081 : Blo 2111435 6770081 := bstep (se 2 (by rfl) ⟨2538780, by rfl⟩ : syracuseStep 6770081 = 5077561) B5077561
theorem B18053549 : Blo 2111435 18053549 := bstep (se 3 (by rfl) ⟨3385040, by rfl⟩ : syracuseStep 18053549 = 6770081) B6770081
theorem B12035699 : Blo 2111435 12035699 := bstep (se 1 (by rfl) ⟨9026774, by rfl⟩ : syracuseStep 12035699 = 18053549) B18053549
theorem B8023799 : Blo 2111435 8023799 := bstep (se 1 (by rfl) ⟨6017849, by rfl⟩ : syracuseStep 8023799 = 12035699) B12035699
theorem B5349199 : Blo 2111435 5349199 := bstep (se 1 (by rfl) ⟨4011899, by rfl⟩ : syracuseStep 5349199 = 8023799) B8023799
theorem B7132265 : Blo 2111435 7132265 := bstep (se 2 (by rfl) ⟨2674599, by rfl⟩ : syracuseStep 7132265 = 5349199) B5349199
theorem B4754843 : Blo 2111435 4754843 := bstep (se 1 (by rfl) ⟨3566132, by rfl⟩ : syracuseStep 4754843 = 7132265) B7132265
theorem B3169895 : Blo 2111435 3169895 := bstep (se 1 (by rfl) ⟨2377421, by rfl⟩ : syracuseStep 3169895 = 4754843) B4754843
theorem B2113263 : Blo 2111435 2113263 := bstep (se 1 (by rfl) ⟨1584947, by rfl⟩ : syracuseStep 2113263 = 3169895) B3169895
theorem B3169901 : Blo 2111435 3169901 := bbase (se 3 (by rfl) ⟨594356, by rfl⟩ : syracuseStep 3169901 = 1188713) (by norm_num)
theorem B2113267 : Blo 2111435 2113267 := bstep (se 1 (by rfl) ⟨1584950, by rfl⟩ : syracuseStep 2113267 = 3169901) B3169901
theorem B4754861 : Blo 2111435 4754861 := bbase (se 3 (by rfl) ⟨891536, by rfl⟩ : syracuseStep 4754861 = 1783073) (by norm_num)
theorem B3169907 : Blo 2111435 3169907 := bstep (se 1 (by rfl) ⟨2377430, by rfl⟩ : syracuseStep 3169907 = 4754861) B4754861
theorem B2113271 : Blo 2111435 2113271 := bstep (se 1 (by rfl) ⟨1584953, by rfl⟩ : syracuseStep 2113271 = 3169907) B3169907
theorem B3385061 : Blo 2111435 3385061 := bbase (se 4 (by rfl) ⟨317349, by rfl⟩ : syracuseStep 3385061 = 634699) (by norm_num)
theorem B2256707 : Blo 2111435 2256707 := bstep (se 1 (by rfl) ⟨1692530, by rfl⟩ : syracuseStep 2256707 = 3385061) B3385061
theorem B6017885 : Blo 2111435 6017885 := bstep (se 3 (by rfl) ⟨1128353, by rfl⟩ : syracuseStep 6017885 = 2256707) B2256707
theorem B4011923 : Blo 2111435 4011923 := bstep (se 1 (by rfl) ⟨3008942, by rfl⟩ : syracuseStep 4011923 = 6017885) B6017885
theorem B2674615 : Blo 2111435 2674615 := bstep (se 1 (by rfl) ⟨2005961, by rfl⟩ : syracuseStep 2674615 = 4011923) B4011923
theorem B3566153 : Blo 2111435 3566153 := bstep (se 2 (by rfl) ⟨1337307, by rfl⟩ : syracuseStep 3566153 = 2674615) B2674615
theorem B2377435 : Blo 2111435 2377435 := bstep (se 1 (by rfl) ⟨1783076, by rfl⟩ : syracuseStep 2377435 = 3566153) B3566153
theorem B3169913 : Blo 2111435 3169913 := bstep (se 2 (by rfl) ⟨1188717, by rfl⟩ : syracuseStep 3169913 = 2377435) B2377435
theorem B2113275 : Blo 2111435 2113275 := bstep (se 1 (by rfl) ⟨1584956, by rfl⟩ : syracuseStep 2113275 = 3169913) B3169913
theorem B9274837 : Blo 2111435 9274837 := bbase (se 7 (by rfl) ⟨108689, by rfl⟩ : syracuseStep 9274837 = 217379) (by norm_num)
theorem B12366449 : Blo 2111435 12366449 := bstep (se 2 (by rfl) ⟨4637418, by rfl⟩ : syracuseStep 12366449 = 9274837) B9274837
theorem B8244299 : Blo 2111435 8244299 := bstep (se 1 (by rfl) ⟨6183224, by rfl⟩ : syracuseStep 8244299 = 12366449) B12366449
theorem B21984797 : Blo 2111435 21984797 := bstep (se 3 (by rfl) ⟨4122149, by rfl⟩ : syracuseStep 21984797 = 8244299) B8244299
theorem B58626125 : Blo 2111435 58626125 := bstep (se 3 (by rfl) ⟨10992398, by rfl⟩ : syracuseStep 58626125 = 21984797) B21984797
theorem B39084083 : Blo 2111435 39084083 := bstep (se 1 (by rfl) ⟨29313062, by rfl⟩ : syracuseStep 39084083 = 58626125) B58626125
theorem B26056055 : Blo 2111435 26056055 := bstep (se 1 (by rfl) ⟨19542041, by rfl⟩ : syracuseStep 26056055 = 39084083) B39084083
theorem B17370703 : Blo 2111435 17370703 := bstep (se 1 (by rfl) ⟨13028027, by rfl⟩ : syracuseStep 17370703 = 26056055) B26056055
theorem B92643749 : Blo 2111435 92643749 := bstep (se 4 (by rfl) ⟨8685351, by rfl⟩ : syracuseStep 92643749 = 17370703) B17370703
theorem B61762499 : Blo 2111435 61762499 := bstep (se 1 (by rfl) ⟨46321874, by rfl⟩ : syracuseStep 61762499 = 92643749) B92643749
theorem B41174999 : Blo 2111435 41174999 := bstep (se 1 (by rfl) ⟨30881249, by rfl⟩ : syracuseStep 41174999 = 61762499) B61762499
theorem B27449999 : Blo 2111435 27449999 := bstep (se 1 (by rfl) ⟨20587499, by rfl⟩ : syracuseStep 27449999 = 41174999) B41174999
theorem B18299999 : Blo 2111435 18299999 := bstep (se 1 (by rfl) ⟨13724999, by rfl⟩ : syracuseStep 18299999 = 27449999) B27449999
theorem B12199999 : Blo 2111435 12199999 := bstep (se 1 (by rfl) ⟨9149999, by rfl⟩ : syracuseStep 12199999 = 18299999) B18299999
theorem B16266665 : Blo 2111435 16266665 := bstep (se 2 (by rfl) ⟨6099999, by rfl⟩ : syracuseStep 16266665 = 12199999) B12199999
theorem B10844443 : Blo 2111435 10844443 := bstep (se 1 (by rfl) ⟨8133332, by rfl⟩ : syracuseStep 10844443 = 16266665) B16266665
theorem B14459257 : Blo 2111435 14459257 := bstep (se 2 (by rfl) ⟨5422221, by rfl⟩ : syracuseStep 14459257 = 10844443) B10844443
theorem B19279009 : Blo 2111435 19279009 := bstep (se 2 (by rfl) ⟨7229628, by rfl⟩ : syracuseStep 19279009 = 14459257) B14459257
theorem B25705345 : Blo 2111435 25705345 := bstep (se 2 (by rfl) ⟨9639504, by rfl⟩ : syracuseStep 25705345 = 19279009) B19279009
theorem B34273793 : Blo 2111435 34273793 := bstep (se 2 (by rfl) ⟨12852672, by rfl⟩ : syracuseStep 34273793 = 25705345) B25705345
theorem B91396781 : Blo 2111435 91396781 := bstep (se 3 (by rfl) ⟨17136896, by rfl⟩ : syracuseStep 91396781 = 34273793) B34273793
theorem B60931187 : Blo 2111435 60931187 := bstep (se 1 (by rfl) ⟨45698390, by rfl⟩ : syracuseStep 60931187 = 91396781) B91396781
theorem B40620791 : Blo 2111435 40620791 := bstep (se 1 (by rfl) ⟨30465593, by rfl⟩ : syracuseStep 40620791 = 60931187) B60931187
theorem B27080527 : Blo 2111435 27080527 := bstep (se 1 (by rfl) ⟨20310395, by rfl⟩ : syracuseStep 27080527 = 40620791) B40620791
theorem B36107369 : Blo 2111435 36107369 := bstep (se 2 (by rfl) ⟨13540263, by rfl⟩ : syracuseStep 36107369 = 27080527) B27080527
theorem B24071579 : Blo 2111435 24071579 := bstep (se 1 (by rfl) ⟨18053684, by rfl⟩ : syracuseStep 24071579 = 36107369) B36107369
theorem B16047719 : Blo 2111435 16047719 := bstep (se 1 (by rfl) ⟨12035789, by rfl⟩ : syracuseStep 16047719 = 24071579) B24071579
theorem B10698479 : Blo 2111435 10698479 := bstep (se 1 (by rfl) ⟨8023859, by rfl⟩ : syracuseStep 10698479 = 16047719) B16047719
theorem B7132319 : Blo 2111435 7132319 := bstep (se 1 (by rfl) ⟨5349239, by rfl⟩ : syracuseStep 7132319 = 10698479) B10698479
theorem B4754879 : Blo 2111435 4754879 := bstep (se 1 (by rfl) ⟨3566159, by rfl⟩ : syracuseStep 4754879 = 7132319) B7132319
theorem B3169919 : Blo 2111435 3169919 := bstep (se 1 (by rfl) ⟨2377439, by rfl⟩ : syracuseStep 3169919 = 4754879) B4754879
theorem B2113279 : Blo 2111435 2113279 := bstep (se 1 (by rfl) ⟨1584959, by rfl⟩ : syracuseStep 2113279 = 3169919) B3169919
theorem B3169925 : Blo 2111435 3169925 := bbase (se 4 (by rfl) ⟨297180, by rfl⟩ : syracuseStep 3169925 = 594361) (by norm_num)
theorem B2113283 : Blo 2111435 2113283 := bstep (se 1 (by rfl) ⟨1584962, by rfl⟩ : syracuseStep 2113283 = 3169925) B3169925
theorem B3566173 : Blo 2111435 3566173 := bbase (se 3 (by rfl) ⟨668657, by rfl⟩ : syracuseStep 3566173 = 1337315) (by norm_num)
theorem B4754897 : Blo 2111435 4754897 := bstep (se 2 (by rfl) ⟨1783086, by rfl⟩ : syracuseStep 4754897 = 3566173) B3566173
theorem B3169931 : Blo 2111435 3169931 := bstep (se 1 (by rfl) ⟨2377448, by rfl⟩ : syracuseStep 3169931 = 4754897) B4754897
theorem B2113287 : Blo 2111435 2113287 := bstep (se 1 (by rfl) ⟨1584965, by rfl⟩ : syracuseStep 2113287 = 3169931) B3169931
theorem B2377453 : Blo 2111435 2377453 := bbase (se 3 (by rfl) ⟨445772, by rfl⟩ : syracuseStep 2377453 = 891545) (by norm_num)
theorem B3169937 : Blo 2111435 3169937 := bstep (se 2 (by rfl) ⟨1188726, by rfl⟩ : syracuseStep 3169937 = 2377453) B2377453
theorem B2113291 : Blo 2111435 2113291 := bstep (se 1 (by rfl) ⟨1584968, by rfl⟩ : syracuseStep 2113291 = 3169937) B3169937
theorem B7132373 : Blo 2111435 7132373 := bbase (se 7 (by rfl) ⟨83582, by rfl⟩ : syracuseStep 7132373 = 167165) (by norm_num)
theorem B4754915 : Blo 2111435 4754915 := bstep (se 1 (by rfl) ⟨3566186, by rfl⟩ : syracuseStep 4754915 = 7132373) B7132373
theorem B3169943 : Blo 2111435 3169943 := bstep (se 1 (by rfl) ⟨2377457, by rfl⟩ : syracuseStep 3169943 = 4754915) B4754915
theorem B2113295 : Blo 2111435 2113295 := bstep (se 1 (by rfl) ⟨1584971, by rfl⟩ : syracuseStep 2113295 = 3169943) B3169943
theorem B3169949 : Blo 2111435 3169949 := bbase (se 3 (by rfl) ⟨594365, by rfl⟩ : syracuseStep 3169949 = 1188731) (by norm_num)
theorem B2113299 : Blo 2111435 2113299 := bstep (se 1 (by rfl) ⟨1584974, by rfl⟩ : syracuseStep 2113299 = 3169949) B3169949
theorem B4754933 : Blo 2111435 4754933 := bbase (se 5 (by rfl) ⟨222887, by rfl⟩ : syracuseStep 4754933 = 445775) (by norm_num)
theorem B3169955 : Blo 2111435 3169955 := bstep (se 1 (by rfl) ⟨2377466, by rfl⟩ : syracuseStep 3169955 = 4754933) B4754933
theorem B2113303 : Blo 2111435 2113303 := bstep (se 1 (by rfl) ⟨1584977, by rfl⟩ : syracuseStep 2113303 = 3169955) B3169955
theorem B4575061 : Blo 2111435 4575061 := bbase (se 9 (by rfl) ⟨13403, by rfl⟩ : syracuseStep 4575061 = 26807) (by norm_num)
theorem B24400325 : Blo 2111435 24400325 := bstep (se 4 (by rfl) ⟨2287530, by rfl⟩ : syracuseStep 24400325 = 4575061) B4575061
theorem B65067533 : Blo 2111435 65067533 := bstep (se 3 (by rfl) ⟨12200162, by rfl⟩ : syracuseStep 65067533 = 24400325) B24400325
theorem B43378355 : Blo 2111435 43378355 := bstep (se 1 (by rfl) ⟨32533766, by rfl⟩ : syracuseStep 43378355 = 65067533) B65067533
theorem B28918903 : Blo 2111435 28918903 := bstep (se 1 (by rfl) ⟨21689177, by rfl⟩ : syracuseStep 28918903 = 43378355) B43378355
theorem B38558537 : Blo 2111435 38558537 := bstep (se 2 (by rfl) ⟨14459451, by rfl⟩ : syracuseStep 38558537 = 28918903) B28918903
theorem B25705691 : Blo 2111435 25705691 := bstep (se 1 (by rfl) ⟨19279268, by rfl⟩ : syracuseStep 25705691 = 38558537) B38558537
theorem B17137127 : Blo 2111435 17137127 := bstep (se 1 (by rfl) ⟨12852845, by rfl⟩ : syracuseStep 17137127 = 25705691) B25705691
theorem B45699005 : Blo 2111435 45699005 := bstep (se 3 (by rfl) ⟨8568563, by rfl⟩ : syracuseStep 45699005 = 17137127) B17137127
theorem B30466003 : Blo 2111435 30466003 := bstep (se 1 (by rfl) ⟨22849502, by rfl⟩ : syracuseStep 30466003 = 45699005) B45699005
theorem B40621337 : Blo 2111435 40621337 := bstep (se 2 (by rfl) ⟨15233001, by rfl⟩ : syracuseStep 40621337 = 30466003) B30466003
theorem B27080891 : Blo 2111435 27080891 := bstep (se 1 (by rfl) ⟨20310668, by rfl⟩ : syracuseStep 27080891 = 40621337) B40621337
theorem B18053927 : Blo 2111435 18053927 := bstep (se 1 (by rfl) ⟨13540445, by rfl⟩ : syracuseStep 18053927 = 27080891) B27080891
theorem B12035951 : Blo 2111435 12035951 := bstep (se 1 (by rfl) ⟨9026963, by rfl⟩ : syracuseStep 12035951 = 18053927) B18053927
theorem B8023967 : Blo 2111435 8023967 := bstep (se 1 (by rfl) ⟨6017975, by rfl⟩ : syracuseStep 8023967 = 12035951) B12035951
theorem B5349311 : Blo 2111435 5349311 := bstep (se 1 (by rfl) ⟨4011983, by rfl⟩ : syracuseStep 5349311 = 8023967) B8023967
theorem B3566207 : Blo 2111435 3566207 := bstep (se 1 (by rfl) ⟨2674655, by rfl⟩ : syracuseStep 3566207 = 5349311) B5349311
theorem B2377471 : Blo 2111435 2377471 := bstep (se 1 (by rfl) ⟨1783103, by rfl⟩ : syracuseStep 2377471 = 3566207) B3566207
theorem B3169961 : Blo 2111435 3169961 := bstep (se 2 (by rfl) ⟨1188735, by rfl⟩ : syracuseStep 3169961 = 2377471) B2377471
theorem B2113307 : Blo 2111435 2113307 := bstep (se 1 (by rfl) ⟨1584980, by rfl⟩ : syracuseStep 2113307 = 3169961) B3169961
theorem B2256745 : Blo 2111435 2256745 := bbase (se 2 (by rfl) ⟨846279, by rfl⟩ : syracuseStep 2256745 = 1692559) (by norm_num)
theorem B3008993 : Blo 2111435 3008993 := bstep (se 2 (by rfl) ⟨1128372, by rfl⟩ : syracuseStep 3008993 = 2256745) B2256745
theorem B8023981 : Blo 2111435 8023981 := bstep (se 3 (by rfl) ⟨1504496, by rfl⟩ : syracuseStep 8023981 = 3008993) B3008993
theorem B10698641 : Blo 2111435 10698641 := bstep (se 2 (by rfl) ⟨4011990, by rfl⟩ : syracuseStep 10698641 = 8023981) B8023981
theorem B7132427 : Blo 2111435 7132427 := bstep (se 1 (by rfl) ⟨5349320, by rfl⟩ : syracuseStep 7132427 = 10698641) B10698641
theorem B4754951 : Blo 2111435 4754951 := bstep (se 1 (by rfl) ⟨3566213, by rfl⟩ : syracuseStep 4754951 = 7132427) B7132427
theorem B3169967 : Blo 2111435 3169967 := bstep (se 1 (by rfl) ⟨2377475, by rfl⟩ : syracuseStep 3169967 = 4754951) B4754951
theorem B2113311 : Blo 2111435 2113311 := bstep (se 1 (by rfl) ⟨1584983, by rfl⟩ : syracuseStep 2113311 = 3169967) B3169967
theorem B3169973 : Blo 2111435 3169973 := bbase (se 5 (by rfl) ⟨148592, by rfl⟩ : syracuseStep 3169973 = 297185) (by norm_num)
theorem B2113315 : Blo 2111435 2113315 := bstep (se 1 (by rfl) ⟨1584986, by rfl⟩ : syracuseStep 2113315 = 3169973) B3169973
theorem B5349341 : Blo 2111435 5349341 := bbase (se 3 (by rfl) ⟨1003001, by rfl⟩ : syracuseStep 5349341 = 2006003) (by norm_num)
theorem B3566227 : Blo 2111435 3566227 := bstep (se 1 (by rfl) ⟨2674670, by rfl⟩ : syracuseStep 3566227 = 5349341) B5349341
theorem B4754969 : Blo 2111435 4754969 := bstep (se 2 (by rfl) ⟨1783113, by rfl⟩ : syracuseStep 4754969 = 3566227) B3566227
theorem B3169979 : Blo 2111435 3169979 := bstep (se 1 (by rfl) ⟨2377484, by rfl⟩ : syracuseStep 3169979 = 4754969) B4754969
theorem B2113319 : Blo 2111435 2113319 := bstep (se 1 (by rfl) ⟨1584989, by rfl⟩ : syracuseStep 2113319 = 3169979) B3169979
theorem B2377489 : Blo 2111435 2377489 := bbase (se 2 (by rfl) ⟨891558, by rfl⟩ : syracuseStep 2377489 = 1783117) (by norm_num)
theorem B3169985 : Blo 2111435 3169985 := bstep (se 2 (by rfl) ⟨1188744, by rfl⟩ : syracuseStep 3169985 = 2377489) B2377489
theorem B2113323 : Blo 2111435 2113323 := bstep (se 1 (by rfl) ⟨1584992, by rfl⟩ : syracuseStep 2113323 = 3169985) B3169985
theorem B4012021 : Blo 2111435 4012021 := bbase (se 5 (by rfl) ⟨188063, by rfl⟩ : syracuseStep 4012021 = 376127) (by norm_num)
theorem B5349361 : Blo 2111435 5349361 := bstep (se 2 (by rfl) ⟨2006010, by rfl⟩ : syracuseStep 5349361 = 4012021) B4012021
theorem B7132481 : Blo 2111435 7132481 := bstep (se 2 (by rfl) ⟨2674680, by rfl⟩ : syracuseStep 7132481 = 5349361) B5349361
theorem B4754987 : Blo 2111435 4754987 := bstep (se 1 (by rfl) ⟨3566240, by rfl⟩ : syracuseStep 4754987 = 7132481) B7132481
theorem B3169991 : Blo 2111435 3169991 := bstep (se 1 (by rfl) ⟨2377493, by rfl⟩ : syracuseStep 3169991 = 4754987) B4754987
theorem B2113327 : Blo 2111435 2113327 := bstep (se 1 (by rfl) ⟨1584995, by rfl⟩ : syracuseStep 2113327 = 3169991) B3169991
theorem B3169997 : Blo 2111435 3169997 := bbase (se 3 (by rfl) ⟨594374, by rfl⟩ : syracuseStep 3169997 = 1188749) (by norm_num)
theorem B2113331 : Blo 2111435 2113331 := bstep (se 1 (by rfl) ⟨1584998, by rfl⟩ : syracuseStep 2113331 = 3169997) B3169997
theorem B4755005 : Blo 2111435 4755005 := bbase (se 3 (by rfl) ⟨891563, by rfl⟩ : syracuseStep 4755005 = 1783127) (by norm_num)
theorem B3170003 : Blo 2111435 3170003 := bstep (se 1 (by rfl) ⟨2377502, by rfl⟩ : syracuseStep 3170003 = 4755005) B4755005
theorem B2113335 : Blo 2111435 2113335 := bstep (se 1 (by rfl) ⟨1585001, by rfl⟩ : syracuseStep 2113335 = 3170003) B3170003
theorem B3566261 : Blo 2111435 3566261 := bbase (se 5 (by rfl) ⟨167168, by rfl⟩ : syracuseStep 3566261 = 334337) (by norm_num)
theorem B2377507 : Blo 2111435 2377507 := bstep (se 1 (by rfl) ⟨1783130, by rfl⟩ : syracuseStep 2377507 = 3566261) B3566261
theorem B3170009 : Blo 2111435 3170009 := bstep (se 2 (by rfl) ⟨1188753, by rfl⟩ : syracuseStep 3170009 = 2377507) B2377507
theorem B2113339 : Blo 2111435 2113339 := bstep (se 1 (by rfl) ⟨1585004, by rfl⟩ : syracuseStep 2113339 = 3170009) B3170009
theorem B2538877 : Blo 2111435 2538877 := bbase (se 3 (by rfl) ⟨476039, by rfl⟩ : syracuseStep 2538877 = 952079) (by norm_num)
theorem B3385169 : Blo 2111435 3385169 := bstep (se 2 (by rfl) ⟨1269438, by rfl⟩ : syracuseStep 3385169 = 2538877) B2538877
theorem B2256779 : Blo 2111435 2256779 := bstep (se 1 (by rfl) ⟨1692584, by rfl⟩ : syracuseStep 2256779 = 3385169) B3385169
theorem B6018077 : Blo 2111435 6018077 := bstep (se 3 (by rfl) ⟨1128389, by rfl⟩ : syracuseStep 6018077 = 2256779) B2256779
theorem B16048205 : Blo 2111435 16048205 := bstep (se 3 (by rfl) ⟨3009038, by rfl⟩ : syracuseStep 16048205 = 6018077) B6018077
theorem B10698803 : Blo 2111435 10698803 := bstep (se 1 (by rfl) ⟨8024102, by rfl⟩ : syracuseStep 10698803 = 16048205) B16048205
theorem B7132535 : Blo 2111435 7132535 := bstep (se 1 (by rfl) ⟨5349401, by rfl⟩ : syracuseStep 7132535 = 10698803) B10698803
theorem B4755023 : Blo 2111435 4755023 := bstep (se 1 (by rfl) ⟨3566267, by rfl⟩ : syracuseStep 4755023 = 7132535) B7132535
theorem B3170015 : Blo 2111435 3170015 := bstep (se 1 (by rfl) ⟨2377511, by rfl⟩ : syracuseStep 3170015 = 4755023) B4755023
theorem B2113343 : Blo 2111435 2113343 := bstep (se 1 (by rfl) ⟨1585007, by rfl⟩ : syracuseStep 2113343 = 3170015) B3170015
theorem B3170021 : Blo 2111435 3170021 := bbase (se 4 (by rfl) ⟨297189, by rfl⟩ : syracuseStep 3170021 = 594379) (by norm_num)
theorem B2113347 : Blo 2111435 2113347 := bstep (se 1 (by rfl) ⟨1585010, by rfl⟩ : syracuseStep 2113347 = 3170021) B3170021
theorem B6018101 : Blo 2111435 6018101 := bbase (se 5 (by rfl) ⟨282098, by rfl⟩ : syracuseStep 6018101 = 564197) (by norm_num)
theorem B4012067 : Blo 2111435 4012067 := bstep (se 1 (by rfl) ⟨3009050, by rfl⟩ : syracuseStep 4012067 = 6018101) B6018101
theorem B2674711 : Blo 2111435 2674711 := bstep (se 1 (by rfl) ⟨2006033, by rfl⟩ : syracuseStep 2674711 = 4012067) B4012067
theorem B3566281 : Blo 2111435 3566281 := bstep (se 2 (by rfl) ⟨1337355, by rfl⟩ : syracuseStep 3566281 = 2674711) B2674711
theorem B4755041 : Blo 2111435 4755041 := bstep (se 2 (by rfl) ⟨1783140, by rfl⟩ : syracuseStep 4755041 = 3566281) B3566281
theorem B3170027 : Blo 2111435 3170027 := bstep (se 1 (by rfl) ⟨2377520, by rfl⟩ : syracuseStep 3170027 = 4755041) B4755041
theorem B2113351 : Blo 2111435 2113351 := bstep (se 1 (by rfl) ⟨1585013, by rfl⟩ : syracuseStep 2113351 = 3170027) B3170027
theorem B2377525 : Blo 2111435 2377525 := bbase (se 5 (by rfl) ⟨111446, by rfl⟩ : syracuseStep 2377525 = 222893) (by norm_num)
theorem B3170033 : Blo 2111435 3170033 := bstep (se 2 (by rfl) ⟨1188762, by rfl⟩ : syracuseStep 3170033 = 2377525) B2377525
theorem B2113355 : Blo 2111435 2113355 := bstep (se 1 (by rfl) ⟨1585016, by rfl⟩ : syracuseStep 2113355 = 3170033) B3170033
theorem B2674721 : Blo 2111435 2674721 := bbase (se 2 (by rfl) ⟨1003020, by rfl⟩ : syracuseStep 2674721 = 2006041) (by norm_num)
theorem B7132589 : Blo 2111435 7132589 := bstep (se 3 (by rfl) ⟨1337360, by rfl⟩ : syracuseStep 7132589 = 2674721) B2674721
theorem B4755059 : Blo 2111435 4755059 := bstep (se 1 (by rfl) ⟨3566294, by rfl⟩ : syracuseStep 4755059 = 7132589) B7132589
theorem B3170039 : Blo 2111435 3170039 := bstep (se 1 (by rfl) ⟨2377529, by rfl⟩ : syracuseStep 3170039 = 4755059) B4755059
theorem B2113359 : Blo 2111435 2113359 := bstep (se 1 (by rfl) ⟨1585019, by rfl⟩ : syracuseStep 2113359 = 3170039) B3170039
theorem B3170045 : Blo 2111435 3170045 := bbase (se 3 (by rfl) ⟨594383, by rfl⟩ : syracuseStep 3170045 = 1188767) (by norm_num)
theorem B2113363 : Blo 2111435 2113363 := bstep (se 1 (by rfl) ⟨1585022, by rfl⟩ : syracuseStep 2113363 = 3170045) B3170045
theorem B4755077 : Blo 2111435 4755077 := bbase (se 4 (by rfl) ⟨445788, by rfl⟩ : syracuseStep 4755077 = 891577) (by norm_num)
theorem B3170051 : Blo 2111435 3170051 := bstep (se 1 (by rfl) ⟨2377538, by rfl⟩ : syracuseStep 3170051 = 4755077) B4755077
theorem B2113367 : Blo 2111435 2113367 := bstep (se 1 (by rfl) ⟨1585025, by rfl⟩ : syracuseStep 2113367 = 3170051) B3170051
theorem B10039909 : Blo 2111435 10039909 := bbase (se 4 (by rfl) ⟨941241, by rfl⟩ : syracuseStep 10039909 = 1882483) (by norm_num)
theorem B13386545 : Blo 2111435 13386545 := bstep (se 2 (by rfl) ⟨5019954, by rfl⟩ : syracuseStep 13386545 = 10039909) B10039909
theorem B8924363 : Blo 2111435 8924363 := bstep (se 1 (by rfl) ⟨6693272, by rfl⟩ : syracuseStep 8924363 = 13386545) B13386545
theorem B5949575 : Blo 2111435 5949575 := bstep (se 1 (by rfl) ⟨4462181, by rfl⟩ : syracuseStep 5949575 = 8924363) B8924363
theorem B3966383 : Blo 2111435 3966383 := bstep (se 1 (by rfl) ⟨2974787, by rfl⟩ : syracuseStep 3966383 = 5949575) B5949575
theorem B2644255 : Blo 2111435 2644255 := bstep (se 1 (by rfl) ⟨1983191, by rfl⟩ : syracuseStep 2644255 = 3966383) B3966383
theorem B14102693 : Blo 2111435 14102693 := bstep (se 4 (by rfl) ⟨1322127, by rfl⟩ : syracuseStep 14102693 = 2644255) B2644255
theorem B9401795 : Blo 2111435 9401795 := bstep (se 1 (by rfl) ⟨7051346, by rfl⟩ : syracuseStep 9401795 = 14102693) B14102693
theorem B6267863 : Blo 2111435 6267863 := bstep (se 1 (by rfl) ⟨4700897, by rfl⟩ : syracuseStep 6267863 = 9401795) B9401795
theorem B4178575 : Blo 2111435 4178575 := bstep (se 1 (by rfl) ⟨3133931, by rfl⟩ : syracuseStep 4178575 = 6267863) B6267863
theorem B5571433 : Blo 2111435 5571433 := bstep (se 2 (by rfl) ⟨2089287, by rfl⟩ : syracuseStep 5571433 = 4178575) B4178575
theorem B29714309 : Blo 2111435 29714309 := bstep (se 4 (by rfl) ⟨2785716, by rfl⟩ : syracuseStep 29714309 = 5571433) B5571433
theorem B19809539 : Blo 2111435 19809539 := bstep (se 1 (by rfl) ⟨14857154, by rfl⟩ : syracuseStep 19809539 = 29714309) B29714309
theorem B13206359 : Blo 2111435 13206359 := bstep (se 1 (by rfl) ⟨9904769, by rfl⟩ : syracuseStep 13206359 = 19809539) B19809539
theorem B35216957 : Blo 2111435 35216957 := bstep (se 3 (by rfl) ⟨6603179, by rfl⟩ : syracuseStep 35216957 = 13206359) B13206359
theorem B93911885 : Blo 2111435 93911885 := bstep (se 3 (by rfl) ⟨17608478, by rfl⟩ : syracuseStep 93911885 = 35216957) B35216957
theorem B62607923 : Blo 2111435 62607923 := bstep (se 1 (by rfl) ⟨46955942, by rfl⟩ : syracuseStep 62607923 = 93911885) B93911885
theorem B41738615 : Blo 2111435 41738615 := bstep (se 1 (by rfl) ⟨31303961, by rfl⟩ : syracuseStep 41738615 = 62607923) B62607923
theorem B27825743 : Blo 2111435 27825743 := bstep (se 1 (by rfl) ⟨20869307, by rfl⟩ : syracuseStep 27825743 = 41738615) B41738615
theorem B18550495 : Blo 2111435 18550495 := bstep (se 1 (by rfl) ⟨13912871, by rfl⟩ : syracuseStep 18550495 = 27825743) B27825743
theorem B24733993 : Blo 2111435 24733993 := bstep (se 2 (by rfl) ⟨9275247, by rfl⟩ : syracuseStep 24733993 = 18550495) B18550495
theorem B32978657 : Blo 2111435 32978657 := bstep (se 2 (by rfl) ⟨12366996, by rfl⟩ : syracuseStep 32978657 = 24733993) B24733993
theorem B21985771 : Blo 2111435 21985771 := bstep (se 1 (by rfl) ⟨16489328, by rfl⟩ : syracuseStep 21985771 = 32978657) B32978657
theorem B29314361 : Blo 2111435 29314361 := bstep (se 2 (by rfl) ⟨10992885, by rfl⟩ : syracuseStep 29314361 = 21985771) B21985771
theorem B19542907 : Blo 2111435 19542907 := bstep (se 1 (by rfl) ⟨14657180, by rfl⟩ : syracuseStep 19542907 = 29314361) B29314361
theorem B26057209 : Blo 2111435 26057209 := bstep (se 2 (by rfl) ⟨9771453, by rfl⟩ : syracuseStep 26057209 = 19542907) B19542907
theorem B34742945 : Blo 2111435 34742945 := bstep (se 2 (by rfl) ⟨13028604, by rfl⟩ : syracuseStep 34742945 = 26057209) B26057209
theorem B23161963 : Blo 2111435 23161963 := bstep (se 1 (by rfl) ⟨17371472, by rfl⟩ : syracuseStep 23161963 = 34742945) B34742945
theorem B30882617 : Blo 2111435 30882617 := bstep (se 2 (by rfl) ⟨11580981, by rfl⟩ : syracuseStep 30882617 = 23161963) B23161963
theorem B20588411 : Blo 2111435 20588411 := bstep (se 1 (by rfl) ⟨15441308, by rfl⟩ : syracuseStep 20588411 = 30882617) B30882617
theorem B13725607 : Blo 2111435 13725607 := bstep (se 1 (by rfl) ⟨10294205, by rfl⟩ : syracuseStep 13725607 = 20588411) B20588411
theorem B18300809 : Blo 2111435 18300809 := bstep (se 2 (by rfl) ⟨6862803, by rfl⟩ : syracuseStep 18300809 = 13725607) B13725607
theorem B12200539 : Blo 2111435 12200539 := bstep (se 1 (by rfl) ⟨9150404, by rfl⟩ : syracuseStep 12200539 = 18300809) B18300809
theorem B16267385 : Blo 2111435 16267385 := bstep (se 2 (by rfl) ⟨6100269, by rfl⟩ : syracuseStep 16267385 = 12200539) B12200539
theorem B10844923 : Blo 2111435 10844923 := bstep (se 1 (by rfl) ⟨8133692, by rfl⟩ : syracuseStep 10844923 = 16267385) B16267385
theorem B14459897 : Blo 2111435 14459897 := bstep (se 2 (by rfl) ⟨5422461, by rfl⟩ : syracuseStep 14459897 = 10844923) B10844923
theorem B9639931 : Blo 2111435 9639931 := bstep (se 1 (by rfl) ⟨7229948, by rfl⟩ : syracuseStep 9639931 = 14459897) B14459897
theorem B12853241 : Blo 2111435 12853241 := bstep (se 2 (by rfl) ⟨4819965, by rfl⟩ : syracuseStep 12853241 = 9639931) B9639931
theorem B8568827 : Blo 2111435 8568827 := bstep (se 1 (by rfl) ⟨6426620, by rfl⟩ : syracuseStep 8568827 = 12853241) B12853241
theorem B5712551 : Blo 2111435 5712551 := bstep (se 1 (by rfl) ⟨4284413, by rfl⟩ : syracuseStep 5712551 = 8568827) B8568827
theorem B3808367 : Blo 2111435 3808367 := bstep (se 1 (by rfl) ⟨2856275, by rfl⟩ : syracuseStep 3808367 = 5712551) B5712551
theorem B2538911 : Blo 2111435 2538911 := bstep (se 1 (by rfl) ⟨1904183, by rfl⟩ : syracuseStep 2538911 = 3808367) B3808367
theorem B6770429 : Blo 2111435 6770429 := bstep (se 3 (by rfl) ⟨1269455, by rfl⟩ : syracuseStep 6770429 = 2538911) B2538911
theorem B4513619 : Blo 2111435 4513619 := bstep (se 1 (by rfl) ⟨3385214, by rfl⟩ : syracuseStep 4513619 = 6770429) B6770429
theorem B3009079 : Blo 2111435 3009079 := bstep (se 1 (by rfl) ⟨2256809, by rfl⟩ : syracuseStep 3009079 = 4513619) B4513619
theorem B4012105 : Blo 2111435 4012105 := bstep (se 2 (by rfl) ⟨1504539, by rfl⟩ : syracuseStep 4012105 = 3009079) B3009079
theorem B5349473 : Blo 2111435 5349473 := bstep (se 2 (by rfl) ⟨2006052, by rfl⟩ : syracuseStep 5349473 = 4012105) B4012105
theorem B3566315 : Blo 2111435 3566315 := bstep (se 1 (by rfl) ⟨2674736, by rfl⟩ : syracuseStep 3566315 = 5349473) B5349473
theorem B2377543 : Blo 2111435 2377543 := bstep (se 1 (by rfl) ⟨1783157, by rfl⟩ : syracuseStep 2377543 = 3566315) B3566315
theorem B3170057 : Blo 2111435 3170057 := bstep (se 2 (by rfl) ⟨1188771, by rfl⟩ : syracuseStep 3170057 = 2377543) B2377543
theorem B2113371 : Blo 2111435 2113371 := bstep (se 1 (by rfl) ⟨1585028, by rfl⟩ : syracuseStep 2113371 = 3170057) B3170057
theorem B10698965 : Blo 2111435 10698965 := bbase (se 7 (by rfl) ⟨125378, by rfl⟩ : syracuseStep 10698965 = 250757) (by norm_num)
theorem B7132643 : Blo 2111435 7132643 := bstep (se 1 (by rfl) ⟨5349482, by rfl⟩ : syracuseStep 7132643 = 10698965) B10698965
theorem B4755095 : Blo 2111435 4755095 := bstep (se 1 (by rfl) ⟨3566321, by rfl⟩ : syracuseStep 4755095 = 7132643) B7132643
theorem B3170063 : Blo 2111435 3170063 := bstep (se 1 (by rfl) ⟨2377547, by rfl⟩ : syracuseStep 3170063 = 4755095) B4755095
theorem B2113375 : Blo 2111435 2113375 := bstep (se 1 (by rfl) ⟨1585031, by rfl⟩ : syracuseStep 2113375 = 3170063) B3170063
theorem B3170069 : Blo 2111435 3170069 := bbase (se 6 (by rfl) ⟨74298, by rfl⟩ : syracuseStep 3170069 = 148597) (by norm_num)
theorem B2113379 : Blo 2111435 2113379 := bstep (se 1 (by rfl) ⟨1585034, by rfl⟩ : syracuseStep 2113379 = 3170069) B3170069
theorem B2287613 : Blo 2111435 2287613 := bbase (se 3 (by rfl) ⟨428927, by rfl⟩ : syracuseStep 2287613 = 857855) (by norm_num)
theorem B6100301 : Blo 2111435 6100301 := bstep (se 3 (by rfl) ⟨1143806, by rfl⟩ : syracuseStep 6100301 = 2287613) B2287613
theorem B4066867 : Blo 2111435 4066867 := bstep (se 1 (by rfl) ⟨3050150, by rfl⟩ : syracuseStep 4066867 = 6100301) B6100301
theorem B21689957 : Blo 2111435 21689957 := bstep (se 4 (by rfl) ⟨2033433, by rfl⟩ : syracuseStep 21689957 = 4066867) B4066867
theorem B14459971 : Blo 2111435 14459971 := bstep (se 1 (by rfl) ⟨10844978, by rfl⟩ : syracuseStep 14459971 = 21689957) B21689957
theorem B19279961 : Blo 2111435 19279961 := bstep (se 2 (by rfl) ⟨7229985, by rfl⟩ : syracuseStep 19279961 = 14459971) B14459971
theorem B12853307 : Blo 2111435 12853307 := bstep (se 1 (by rfl) ⟨9639980, by rfl⟩ : syracuseStep 12853307 = 19279961) B19279961
theorem B8568871 : Blo 2111435 8568871 := bstep (se 1 (by rfl) ⟨6426653, by rfl⟩ : syracuseStep 8568871 = 12853307) B12853307
theorem B45700645 : Blo 2111435 45700645 := bstep (se 4 (by rfl) ⟨4284435, by rfl⟩ : syracuseStep 45700645 = 8568871) B8568871
theorem B60934193 : Blo 2111435 60934193 := bstep (se 2 (by rfl) ⟨22850322, by rfl⟩ : syracuseStep 60934193 = 45700645) B45700645
theorem B40622795 : Blo 2111435 40622795 := bstep (se 1 (by rfl) ⟨30467096, by rfl⟩ : syracuseStep 40622795 = 60934193) B60934193
theorem B27081863 : Blo 2111435 27081863 := bstep (se 1 (by rfl) ⟨20311397, by rfl⟩ : syracuseStep 27081863 = 40622795) B40622795
theorem B18054575 : Blo 2111435 18054575 := bstep (se 1 (by rfl) ⟨13540931, by rfl⟩ : syracuseStep 18054575 = 27081863) B27081863
theorem B12036383 : Blo 2111435 12036383 := bstep (se 1 (by rfl) ⟨9027287, by rfl⟩ : syracuseStep 12036383 = 18054575) B18054575
theorem B8024255 : Blo 2111435 8024255 := bstep (se 1 (by rfl) ⟨6018191, by rfl⟩ : syracuseStep 8024255 = 12036383) B12036383
theorem B5349503 : Blo 2111435 5349503 := bstep (se 1 (by rfl) ⟨4012127, by rfl⟩ : syracuseStep 5349503 = 8024255) B8024255
theorem B3566335 : Blo 2111435 3566335 := bstep (se 1 (by rfl) ⟨2674751, by rfl⟩ : syracuseStep 3566335 = 5349503) B5349503
theorem B4755113 : Blo 2111435 4755113 := bstep (se 2 (by rfl) ⟨1783167, by rfl⟩ : syracuseStep 4755113 = 3566335) B3566335
theorem B3170075 : Blo 2111435 3170075 := bstep (se 1 (by rfl) ⟨2377556, by rfl⟩ : syracuseStep 3170075 = 4755113) B4755113
theorem B2113383 : Blo 2111435 2113383 := bstep (se 1 (by rfl) ⟨1585037, by rfl⟩ : syracuseStep 2113383 = 3170075) B3170075
theorem B2377561 : Blo 2111435 2377561 := bbase (se 2 (by rfl) ⟨891585, by rfl⟩ : syracuseStep 2377561 = 1783171) (by norm_num)
theorem B3170081 : Blo 2111435 3170081 := bstep (se 2 (by rfl) ⟨1188780, by rfl⟩ : syracuseStep 3170081 = 2377561) B2377561
theorem B2113387 : Blo 2111435 2113387 := bstep (se 1 (by rfl) ⟨1585040, by rfl⟩ : syracuseStep 2113387 = 3170081) B3170081
theorem B4513661 : Blo 2111435 4513661 := bbase (se 3 (by rfl) ⟨846311, by rfl⟩ : syracuseStep 4513661 = 1692623) (by norm_num)
theorem B3009107 : Blo 2111435 3009107 := bstep (se 1 (by rfl) ⟨2256830, by rfl⟩ : syracuseStep 3009107 = 4513661) B4513661
theorem B8024285 : Blo 2111435 8024285 := bstep (se 3 (by rfl) ⟨1504553, by rfl⟩ : syracuseStep 8024285 = 3009107) B3009107
theorem B5349523 : Blo 2111435 5349523 := bstep (se 1 (by rfl) ⟨4012142, by rfl⟩ : syracuseStep 5349523 = 8024285) B8024285
theorem B7132697 : Blo 2111435 7132697 := bstep (se 2 (by rfl) ⟨2674761, by rfl⟩ : syracuseStep 7132697 = 5349523) B5349523
theorem B4755131 : Blo 2111435 4755131 := bstep (se 1 (by rfl) ⟨3566348, by rfl⟩ : syracuseStep 4755131 = 7132697) B7132697
theorem B3170087 : Blo 2111435 3170087 := bstep (se 1 (by rfl) ⟨2377565, by rfl⟩ : syracuseStep 3170087 = 4755131) B4755131
theorem B2113391 : Blo 2111435 2113391 := bstep (se 1 (by rfl) ⟨1585043, by rfl⟩ : syracuseStep 2113391 = 3170087) B3170087
theorem B3170093 : Blo 2111435 3170093 := bbase (se 3 (by rfl) ⟨594392, by rfl⟩ : syracuseStep 3170093 = 1188785) (by norm_num)
theorem B2113395 : Blo 2111435 2113395 := bstep (se 1 (by rfl) ⟨1585046, by rfl⟩ : syracuseStep 2113395 = 3170093) B3170093
theorem B4755149 : Blo 2111435 4755149 := bbase (se 3 (by rfl) ⟨891590, by rfl⟩ : syracuseStep 4755149 = 1783181) (by norm_num)
theorem B3170099 : Blo 2111435 3170099 := bstep (se 1 (by rfl) ⟨2377574, by rfl⟩ : syracuseStep 3170099 = 4755149) B4755149
theorem B2113399 : Blo 2111435 2113399 := bstep (se 1 (by rfl) ⟨1585049, by rfl⟩ : syracuseStep 2113399 = 3170099) B3170099
theorem B2674777 : Blo 2111435 2674777 := bbase (se 2 (by rfl) ⟨1003041, by rfl⟩ : syracuseStep 2674777 = 2006083) (by norm_num)
theorem B3566369 : Blo 2111435 3566369 := bstep (se 2 (by rfl) ⟨1337388, by rfl⟩ : syracuseStep 3566369 = 2674777) B2674777
theorem B2377579 : Blo 2111435 2377579 := bstep (se 1 (by rfl) ⟨1783184, by rfl⟩ : syracuseStep 2377579 = 3566369) B3566369
theorem B3170105 : Blo 2111435 3170105 := bstep (se 2 (by rfl) ⟨1188789, by rfl⟩ : syracuseStep 3170105 = 2377579) B2377579
theorem B2113403 : Blo 2111435 2113403 := bstep (se 1 (by rfl) ⟨1585052, by rfl⟩ : syracuseStep 2113403 = 3170105) B3170105
theorem B4284485 : Blo 2111435 4284485 := bbase (se 4 (by rfl) ⟨401670, by rfl⟩ : syracuseStep 4284485 = 803341) (by norm_num)
theorem B2856323 : Blo 2111435 2856323 := bstep (se 1 (by rfl) ⟨2142242, by rfl⟩ : syracuseStep 2856323 = 4284485) B4284485
theorem B7616861 : Blo 2111435 7616861 := bstep (se 3 (by rfl) ⟨1428161, by rfl⟩ : syracuseStep 7616861 = 2856323) B2856323
theorem B5077907 : Blo 2111435 5077907 := bstep (se 1 (by rfl) ⟨3808430, by rfl⟩ : syracuseStep 5077907 = 7616861) B7616861
theorem B3385271 : Blo 2111435 3385271 := bstep (se 1 (by rfl) ⟨2538953, by rfl⟩ : syracuseStep 3385271 = 5077907) B5077907
theorem B9027389 : Blo 2111435 9027389 := bstep (se 3 (by rfl) ⟨1692635, by rfl⟩ : syracuseStep 9027389 = 3385271) B3385271
theorem B24073037 : Blo 2111435 24073037 := bstep (se 3 (by rfl) ⟨4513694, by rfl⟩ : syracuseStep 24073037 = 9027389) B9027389
theorem B16048691 : Blo 2111435 16048691 := bstep (se 1 (by rfl) ⟨12036518, by rfl⟩ : syracuseStep 16048691 = 24073037) B24073037
theorem B10699127 : Blo 2111435 10699127 := bstep (se 1 (by rfl) ⟨8024345, by rfl⟩ : syracuseStep 10699127 = 16048691) B16048691
theorem B7132751 : Blo 2111435 7132751 := bstep (se 1 (by rfl) ⟨5349563, by rfl⟩ : syracuseStep 7132751 = 10699127) B10699127
theorem B4755167 : Blo 2111435 4755167 := bstep (se 1 (by rfl) ⟨3566375, by rfl⟩ : syracuseStep 4755167 = 7132751) B7132751
theorem B3170111 : Blo 2111435 3170111 := bstep (se 1 (by rfl) ⟨2377583, by rfl⟩ : syracuseStep 3170111 = 4755167) B4755167
theorem B2113407 : Blo 2111435 2113407 := bstep (se 1 (by rfl) ⟨1585055, by rfl⟩ : syracuseStep 2113407 = 3170111) B3170111
theorem B3170117 : Blo 2111435 3170117 := bbase (se 4 (by rfl) ⟨297198, by rfl⟩ : syracuseStep 3170117 = 594397) (by norm_num)
theorem B2113411 : Blo 2111435 2113411 := bstep (se 1 (by rfl) ⟨1585058, by rfl⟩ : syracuseStep 2113411 = 3170117) B3170117
theorem B3566389 : Blo 2111435 3566389 := bbase (se 5 (by rfl) ⟨167174, by rfl⟩ : syracuseStep 3566389 = 334349) (by norm_num)
theorem B4755185 : Blo 2111435 4755185 := bstep (se 2 (by rfl) ⟨1783194, by rfl⟩ : syracuseStep 4755185 = 3566389) B3566389
theorem B3170123 : Blo 2111435 3170123 := bstep (se 1 (by rfl) ⟨2377592, by rfl⟩ : syracuseStep 3170123 = 4755185) B4755185
theorem B2113415 : Blo 2111435 2113415 := bstep (se 1 (by rfl) ⟨1585061, by rfl⟩ : syracuseStep 2113415 = 3170123) B3170123
theorem B2377597 : Blo 2111435 2377597 := bbase (se 3 (by rfl) ⟨445799, by rfl⟩ : syracuseStep 2377597 = 891599) (by norm_num)
theorem B3170129 : Blo 2111435 3170129 := bstep (se 2 (by rfl) ⟨1188798, by rfl⟩ : syracuseStep 3170129 = 2377597) B2377597
theorem B2113419 : Blo 2111435 2113419 := bstep (se 1 (by rfl) ⟨1585064, by rfl⟩ : syracuseStep 2113419 = 3170129) B3170129
theorem B7132805 : Blo 2111435 7132805 := bbase (se 4 (by rfl) ⟨668700, by rfl⟩ : syracuseStep 7132805 = 1337401) (by norm_num)
theorem B4755203 : Blo 2111435 4755203 := bstep (se 1 (by rfl) ⟨3566402, by rfl⟩ : syracuseStep 4755203 = 7132805) B7132805
theorem B3170135 : Blo 2111435 3170135 := bstep (se 1 (by rfl) ⟨2377601, by rfl⟩ : syracuseStep 3170135 = 4755203) B4755203
theorem B2113423 : Blo 2111435 2113423 := bstep (se 1 (by rfl) ⟨1585067, by rfl⟩ : syracuseStep 2113423 = 3170135) B3170135
theorem B3170141 : Blo 2111435 3170141 := bbase (se 3 (by rfl) ⟨594401, by rfl⟩ : syracuseStep 3170141 = 1188803) (by norm_num)
theorem B2113427 : Blo 2111435 2113427 := bstep (se 1 (by rfl) ⟨1585070, by rfl⟩ : syracuseStep 2113427 = 3170141) B3170141
theorem B4755221 : Blo 2111435 4755221 := bbase (se 6 (by rfl) ⟨111450, by rfl⟩ : syracuseStep 4755221 = 222901) (by norm_num)
theorem B3170147 : Blo 2111435 3170147 := bstep (se 1 (by rfl) ⟨2377610, by rfl⟩ : syracuseStep 3170147 = 4755221) B4755221
theorem B2113431 : Blo 2111435 2113431 := bstep (se 1 (by rfl) ⟨1585073, by rfl⟩ : syracuseStep 2113431 = 3170147) B3170147
theorem B8024453 : Blo 2111435 8024453 := bbase (se 4 (by rfl) ⟨752292, by rfl⟩ : syracuseStep 8024453 = 1504585) (by norm_num)
theorem B5349635 : Blo 2111435 5349635 := bstep (se 1 (by rfl) ⟨4012226, by rfl⟩ : syracuseStep 5349635 = 8024453) B8024453
theorem B3566423 : Blo 2111435 3566423 := bstep (se 1 (by rfl) ⟨2674817, by rfl⟩ : syracuseStep 3566423 = 5349635) B5349635
theorem B2377615 : Blo 2111435 2377615 := bstep (se 1 (by rfl) ⟨1783211, by rfl⟩ : syracuseStep 2377615 = 3566423) B3566423
theorem B3170153 : Blo 2111435 3170153 := bstep (se 2 (by rfl) ⟨1188807, by rfl⟩ : syracuseStep 3170153 = 2377615) B2377615
theorem B2113435 : Blo 2111435 2113435 := bstep (se 1 (by rfl) ⟨1585076, by rfl⟩ : syracuseStep 2113435 = 3170153) B3170153
theorem C0 (j : ℕ) (h1 : 527858 ≤ j) (h2 : j ≤ 528358) : Blo 2111435 (4 * j + 3) := by
  interval_cases j
  · exact B2111435
  · exact B2111439
  · exact B2111443
  · exact B2111447
  · exact B2111451
  · exact B2111455
  · exact B2111459
  · exact B2111463
  · exact B2111467
  · exact B2111471
  · exact B2111475
  · exact B2111479
  · exact B2111483
  · exact B2111487
  · exact B2111491
  · exact B2111495
  · exact B2111499
  · exact B2111503
  · exact B2111507
  · exact B2111511
  · exact B2111515
  · exact B2111519
  · exact B2111523
  · exact B2111527
  · exact B2111531
  · exact B2111535
  · exact B2111539
  · exact B2111543
  · exact B2111547
  · exact B2111551
  · exact B2111555
  · exact B2111559
  · exact B2111563
  · exact B2111567
  · exact B2111571
  · exact B2111575
  · exact B2111579
  · exact B2111583
  · exact B2111587
  · exact B2111591
  · exact B2111595
  · exact B2111599
  · exact B2111603
  · exact B2111607
  · exact B2111611
  · exact B2111615
  · exact B2111619
  · exact B2111623
  · exact B2111627
  · exact B2111631
  · exact B2111635
  · exact B2111639
  · exact B2111643
  · exact B2111647
  · exact B2111651
  · exact B2111655
  · exact B2111659
  · exact B2111663
  · exact B2111667
  · exact B2111671
  · exact B2111675
  · exact B2111679
  · exact B2111683
  · exact B2111687
  · exact B2111691
  · exact B2111695
  · exact B2111699
  · exact B2111703
  · exact B2111707
  · exact B2111711
  · exact B2111715
  · exact B2111719
  · exact B2111723
  · exact B2111727
  · exact B2111731
  · exact B2111735
  · exact B2111739
  · exact B2111743
  · exact B2111747
  · exact B2111751
  · exact B2111755
  · exact B2111759
  · exact B2111763
  · exact B2111767
  · exact B2111771
  · exact B2111775
  · exact B2111779
  · exact B2111783
  · exact B2111787
  · exact B2111791
  · exact B2111795
  · exact B2111799
  · exact B2111803
  · exact B2111807
  · exact B2111811
  · exact B2111815
  · exact B2111819
  · exact B2111823
  · exact B2111827
  · exact B2111831
  · exact B2111835
  · exact B2111839
  · exact B2111843
  · exact B2111847
  · exact B2111851
  · exact B2111855
  · exact B2111859
  · exact B2111863
  · exact B2111867
  · exact B2111871
  · exact B2111875
  · exact B2111879
  · exact B2111883
  · exact B2111887
  · exact B2111891
  · exact B2111895
  · exact B2111899
  · exact B2111903
  · exact B2111907
  · exact B2111911
  · exact B2111915
  · exact B2111919
  · exact B2111923
  · exact B2111927
  · exact B2111931
  · exact B2111935
  · exact B2111939
  · exact B2111943
  · exact B2111947
  · exact B2111951
  · exact B2111955
  · exact B2111959
  · exact B2111963
  · exact B2111967
  · exact B2111971
  · exact B2111975
  · exact B2111979
  · exact B2111983
  · exact B2111987
  · exact B2111991
  · exact B2111995
  · exact B2111999
  · exact B2112003
  · exact B2112007
  · exact B2112011
  · exact B2112015
  · exact B2112019
  · exact B2112023
  · exact B2112027
  · exact B2112031
  · exact B2112035
  · exact B2112039
  · exact B2112043
  · exact B2112047
  · exact B2112051
  · exact B2112055
  · exact B2112059
  · exact B2112063
  · exact B2112067
  · exact B2112071
  · exact B2112075
  · exact B2112079
  · exact B2112083
  · exact B2112087
  · exact B2112091
  · exact B2112095
  · exact B2112099
  · exact B2112103
  · exact B2112107
  · exact B2112111
  · exact B2112115
  · exact B2112119
  · exact B2112123
  · exact B2112127
  · exact B2112131
  · exact B2112135
  · exact B2112139
  · exact B2112143
  · exact B2112147
  · exact B2112151
  · exact B2112155
  · exact B2112159
  · exact B2112163
  · exact B2112167
  · exact B2112171
  · exact B2112175
  · exact B2112179
  · exact B2112183
  · exact B2112187
  · exact B2112191
  · exact B2112195
  · exact B2112199
  · exact B2112203
  · exact B2112207
  · exact B2112211
  · exact B2112215
  · exact B2112219
  · exact B2112223
  · exact B2112227
  · exact B2112231
  · exact B2112235
  · exact B2112239
  · exact B2112243
  · exact B2112247
  · exact B2112251
  · exact B2112255
  · exact B2112259
  · exact B2112263
  · exact B2112267
  · exact B2112271
  · exact B2112275
  · exact B2112279
  · exact B2112283
  · exact B2112287
  · exact B2112291
  · exact B2112295
  · exact B2112299
  · exact B2112303
  · exact B2112307
  · exact B2112311
  · exact B2112315
  · exact B2112319
  · exact B2112323
  · exact B2112327
  · exact B2112331
  · exact B2112335
  · exact B2112339
  · exact B2112343
  · exact B2112347
  · exact B2112351
  · exact B2112355
  · exact B2112359
  · exact B2112363
  · exact B2112367
  · exact B2112371
  · exact B2112375
  · exact B2112379
  · exact B2112383
  · exact B2112387
  · exact B2112391
  · exact B2112395
  · exact B2112399
  · exact B2112403
  · exact B2112407
  · exact B2112411
  · exact B2112415
  · exact B2112419
  · exact B2112423
  · exact B2112427
  · exact B2112431
  · exact B2112435
  · exact B2112439
  · exact B2112443
  · exact B2112447
  · exact B2112451
  · exact B2112455
  · exact B2112459
  · exact B2112463
  · exact B2112467
  · exact B2112471
  · exact B2112475
  · exact B2112479
  · exact B2112483
  · exact B2112487
  · exact B2112491
  · exact B2112495
  · exact B2112499
  · exact B2112503
  · exact B2112507
  · exact B2112511
  · exact B2112515
  · exact B2112519
  · exact B2112523
  · exact B2112527
  · exact B2112531
  · exact B2112535
  · exact B2112539
  · exact B2112543
  · exact B2112547
  · exact B2112551
  · exact B2112555
  · exact B2112559
  · exact B2112563
  · exact B2112567
  · exact B2112571
  · exact B2112575
  · exact B2112579
  · exact B2112583
  · exact B2112587
  · exact B2112591
  · exact B2112595
  · exact B2112599
  · exact B2112603
  · exact B2112607
  · exact B2112611
  · exact B2112615
  · exact B2112619
  · exact B2112623
  · exact B2112627
  · exact B2112631
  · exact B2112635
  · exact B2112639
  · exact B2112643
  · exact B2112647
  · exact B2112651
  · exact B2112655
  · exact B2112659
  · exact B2112663
  · exact B2112667
  · exact B2112671
  · exact B2112675
  · exact B2112679
  · exact B2112683
  · exact B2112687
  · exact B2112691
  · exact B2112695
  · exact B2112699
  · exact B2112703
  · exact B2112707
  · exact B2112711
  · exact B2112715
  · exact B2112719
  · exact B2112723
  · exact B2112727
  · exact B2112731
  · exact B2112735
  · exact B2112739
  · exact B2112743
  · exact B2112747
  · exact B2112751
  · exact B2112755
  · exact B2112759
  · exact B2112763
  · exact B2112767
  · exact B2112771
  · exact B2112775
  · exact B2112779
  · exact B2112783
  · exact B2112787
  · exact B2112791
  · exact B2112795
  · exact B2112799
  · exact B2112803
  · exact B2112807
  · exact B2112811
  · exact B2112815
  · exact B2112819
  · exact B2112823
  · exact B2112827
  · exact B2112831
  · exact B2112835
  · exact B2112839
  · exact B2112843
  · exact B2112847
  · exact B2112851
  · exact B2112855
  · exact B2112859
  · exact B2112863
  · exact B2112867
  · exact B2112871
  · exact B2112875
  · exact B2112879
  · exact B2112883
  · exact B2112887
  · exact B2112891
  · exact B2112895
  · exact B2112899
  · exact B2112903
  · exact B2112907
  · exact B2112911
  · exact B2112915
  · exact B2112919
  · exact B2112923
  · exact B2112927
  · exact B2112931
  · exact B2112935
  · exact B2112939
  · exact B2112943
  · exact B2112947
  · exact B2112951
  · exact B2112955
  · exact B2112959
  · exact B2112963
  · exact B2112967
  · exact B2112971
  · exact B2112975
  · exact B2112979
  · exact B2112983
  · exact B2112987
  · exact B2112991
  · exact B2112995
  · exact B2112999
  · exact B2113003
  · exact B2113007
  · exact B2113011
  · exact B2113015
  · exact B2113019
  · exact B2113023
  · exact B2113027
  · exact B2113031
  · exact B2113035
  · exact B2113039
  · exact B2113043
  · exact B2113047
  · exact B2113051
  · exact B2113055
  · exact B2113059
  · exact B2113063
  · exact B2113067
  · exact B2113071
  · exact B2113075
  · exact B2113079
  · exact B2113083
  · exact B2113087
  · exact B2113091
  · exact B2113095
  · exact B2113099
  · exact B2113103
  · exact B2113107
  · exact B2113111
  · exact B2113115
  · exact B2113119
  · exact B2113123
  · exact B2113127
  · exact B2113131
  · exact B2113135
  · exact B2113139
  · exact B2113143
  · exact B2113147
  · exact B2113151
  · exact B2113155
  · exact B2113159
  · exact B2113163
  · exact B2113167
  · exact B2113171
  · exact B2113175
  · exact B2113179
  · exact B2113183
  · exact B2113187
  · exact B2113191
  · exact B2113195
  · exact B2113199
  · exact B2113203
  · exact B2113207
  · exact B2113211
  · exact B2113215
  · exact B2113219
  · exact B2113223
  · exact B2113227
  · exact B2113231
  · exact B2113235
  · exact B2113239
  · exact B2113243
  · exact B2113247
  · exact B2113251
  · exact B2113255
  · exact B2113259
  · exact B2113263
  · exact B2113267
  · exact B2113271
  · exact B2113275
  · exact B2113279
  · exact B2113283
  · exact B2113287
  · exact B2113291
  · exact B2113295
  · exact B2113299
  · exact B2113303
  · exact B2113307
  · exact B2113311
  · exact B2113315
  · exact B2113319
  · exact B2113323
  · exact B2113327
  · exact B2113331
  · exact B2113335
  · exact B2113339
  · exact B2113343
  · exact B2113347
  · exact B2113351
  · exact B2113355
  · exact B2113359
  · exact B2113363
  · exact B2113367
  · exact B2113371
  · exact B2113375
  · exact B2113379
  · exact B2113383
  · exact B2113387
  · exact B2113391
  · exact B2113395
  · exact B2113399
  · exact B2113403
  · exact B2113407
  · exact B2113411
  · exact B2113415
  · exact B2113419
  · exact B2113423
  · exact B2113427
  · exact B2113431
  · exact B2113435
theorem solution (m : ℕ) (hlo : 2111435 ≤ m) (hhi : m ≤ 2113435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 527858 ≤ j := by omega
    have hj2 : j ≤ 528358 := by omega
    have hb : Blo 2111435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
