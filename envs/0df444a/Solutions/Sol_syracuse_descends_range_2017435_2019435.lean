-- Prove2me | solution 1 for syracuse_descends_range_2017435_2019435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:48:48.611816+00:00
-- url     : https://prove2.me/submissions/5d053849-bcdb-409a-85f4-83e9b40f1d36

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

theorem B5744965 : Blo 2017435 5744965 := bbase (se 4 (by rfl) ⟨538590, by rfl⟩ : syracuseStep 5744965 = 1077181) (by norm_num)
theorem B7659953 : Blo 2017435 7659953 := bstep (se 2 (by rfl) ⟨2872482, by rfl⟩ : syracuseStep 7659953 = 5744965) B5744965
theorem B5106635 : Blo 2017435 5106635 := bstep (se 1 (by rfl) ⟨3829976, by rfl⟩ : syracuseStep 5106635 = 7659953) B7659953
theorem B3404423 : Blo 2017435 3404423 := bstep (se 1 (by rfl) ⟨2553317, by rfl⟩ : syracuseStep 3404423 = 5106635) B5106635
theorem B2269615 : Blo 2017435 2269615 := bstep (se 1 (by rfl) ⟨1702211, by rfl⟩ : syracuseStep 2269615 = 3404423) B3404423
theorem B3026153 : Blo 2017435 3026153 := bstep (se 2 (by rfl) ⟨1134807, by rfl⟩ : syracuseStep 3026153 = 2269615) B2269615
theorem B2017435 : Blo 2017435 2017435 := bstep (se 1 (by rfl) ⟨1513076, by rfl⟩ : syracuseStep 2017435 = 3026153) B3026153
theorem B14740373 : Blo 2017435 14740373 := bbase (se 6 (by rfl) ⟨345477, by rfl⟩ : syracuseStep 14740373 = 690955) (by norm_num)
theorem B9826915 : Blo 2017435 9826915 := bstep (se 1 (by rfl) ⟨7370186, by rfl⟩ : syracuseStep 9826915 = 14740373) B14740373
theorem B13102553 : Blo 2017435 13102553 := bstep (se 2 (by rfl) ⟨4913457, by rfl⟩ : syracuseStep 13102553 = 9826915) B9826915
theorem B8735035 : Blo 2017435 8735035 := bstep (se 1 (by rfl) ⟨6551276, by rfl⟩ : syracuseStep 8735035 = 13102553) B13102553
theorem B11646713 : Blo 2017435 11646713 := bstep (se 2 (by rfl) ⟨4367517, by rfl⟩ : syracuseStep 11646713 = 8735035) B8735035
theorem B31057901 : Blo 2017435 31057901 := bstep (se 3 (by rfl) ⟨5823356, by rfl⟩ : syracuseStep 31057901 = 11646713) B11646713
theorem B20705267 : Blo 2017435 20705267 := bstep (se 1 (by rfl) ⟨15528950, by rfl⟩ : syracuseStep 20705267 = 31057901) B31057901
theorem B55214045 : Blo 2017435 55214045 := bstep (se 3 (by rfl) ⟨10352633, by rfl⟩ : syracuseStep 55214045 = 20705267) B20705267
theorem B36809363 : Blo 2017435 36809363 := bstep (se 1 (by rfl) ⟨27607022, by rfl⟩ : syracuseStep 36809363 = 55214045) B55214045
theorem B98158301 : Blo 2017435 98158301 := bstep (se 3 (by rfl) ⟨18404681, by rfl⟩ : syracuseStep 98158301 = 36809363) B36809363
theorem B65438867 : Blo 2017435 65438867 := bstep (se 1 (by rfl) ⟨49079150, by rfl⟩ : syracuseStep 65438867 = 98158301) B98158301
theorem B43625911 : Blo 2017435 43625911 := bstep (se 1 (by rfl) ⟨32719433, by rfl⟩ : syracuseStep 43625911 = 65438867) B65438867
theorem B58167881 : Blo 2017435 58167881 := bstep (se 2 (by rfl) ⟨21812955, by rfl⟩ : syracuseStep 58167881 = 43625911) B43625911
theorem B38778587 : Blo 2017435 38778587 := bstep (se 1 (by rfl) ⟨29083940, by rfl⟩ : syracuseStep 38778587 = 58167881) B58167881
theorem B25852391 : Blo 2017435 25852391 := bstep (se 1 (by rfl) ⟨19389293, by rfl⟩ : syracuseStep 25852391 = 38778587) B38778587
theorem B17234927 : Blo 2017435 17234927 := bstep (se 1 (by rfl) ⟨12926195, by rfl⟩ : syracuseStep 17234927 = 25852391) B25852391
theorem B11489951 : Blo 2017435 11489951 := bstep (se 1 (by rfl) ⟨8617463, by rfl⟩ : syracuseStep 11489951 = 17234927) B17234927
theorem B7659967 : Blo 2017435 7659967 := bstep (se 1 (by rfl) ⟨5744975, by rfl⟩ : syracuseStep 7659967 = 11489951) B11489951
theorem B10213289 : Blo 2017435 10213289 := bstep (se 2 (by rfl) ⟨3829983, by rfl⟩ : syracuseStep 10213289 = 7659967) B7659967
theorem B6808859 : Blo 2017435 6808859 := bstep (se 1 (by rfl) ⟨5106644, by rfl⟩ : syracuseStep 6808859 = 10213289) B10213289
theorem B4539239 : Blo 2017435 4539239 := bstep (se 1 (by rfl) ⟨3404429, by rfl⟩ : syracuseStep 4539239 = 6808859) B6808859
theorem B3026159 : Blo 2017435 3026159 := bstep (se 1 (by rfl) ⟨2269619, by rfl⟩ : syracuseStep 3026159 = 4539239) B4539239
theorem B2017439 : Blo 2017435 2017439 := bstep (se 1 (by rfl) ⟨1513079, by rfl⟩ : syracuseStep 2017439 = 3026159) B3026159
theorem B3026165 : Blo 2017435 3026165 := bbase (se 5 (by rfl) ⟨141851, by rfl⟩ : syracuseStep 3026165 = 283703) (by norm_num)
theorem B2017443 : Blo 2017435 2017443 := bstep (se 1 (by rfl) ⟨1513082, by rfl⟩ : syracuseStep 2017443 = 3026165) B3026165
theorem B41410709 : Blo 2017435 41410709 := bbase (se 6 (by rfl) ⟨970563, by rfl⟩ : syracuseStep 41410709 = 1941127) (by norm_num)
theorem B27607139 : Blo 2017435 27607139 := bstep (se 1 (by rfl) ⟨20705354, by rfl⟩ : syracuseStep 27607139 = 41410709) B41410709
theorem B18404759 : Blo 2017435 18404759 := bstep (se 1 (by rfl) ⟨13803569, by rfl⟩ : syracuseStep 18404759 = 27607139) B27607139
theorem B49079357 : Blo 2017435 49079357 := bstep (se 3 (by rfl) ⟨9202379, by rfl⟩ : syracuseStep 49079357 = 18404759) B18404759
theorem B32719571 : Blo 2017435 32719571 := bstep (se 1 (by rfl) ⟨24539678, by rfl⟩ : syracuseStep 32719571 = 49079357) B49079357
theorem B21813047 : Blo 2017435 21813047 := bstep (se 1 (by rfl) ⟨16359785, by rfl⟩ : syracuseStep 21813047 = 32719571) B32719571
theorem B14542031 : Blo 2017435 14542031 := bstep (se 1 (by rfl) ⟨10906523, by rfl⟩ : syracuseStep 14542031 = 21813047) B21813047
theorem B9694687 : Blo 2017435 9694687 := bstep (se 1 (by rfl) ⟨7271015, by rfl⟩ : syracuseStep 9694687 = 14542031) B14542031
theorem B12926249 : Blo 2017435 12926249 := bstep (se 2 (by rfl) ⟨4847343, by rfl⟩ : syracuseStep 12926249 = 9694687) B9694687
theorem B8617499 : Blo 2017435 8617499 := bstep (se 1 (by rfl) ⟨6463124, by rfl⟩ : syracuseStep 8617499 = 12926249) B12926249
theorem B5744999 : Blo 2017435 5744999 := bstep (se 1 (by rfl) ⟨4308749, by rfl⟩ : syracuseStep 5744999 = 8617499) B8617499
theorem B3829999 : Blo 2017435 3829999 := bstep (se 1 (by rfl) ⟨2872499, by rfl⟩ : syracuseStep 3829999 = 5744999) B5744999
theorem B5106665 : Blo 2017435 5106665 := bstep (se 2 (by rfl) ⟨1914999, by rfl⟩ : syracuseStep 5106665 = 3829999) B3829999
theorem B3404443 : Blo 2017435 3404443 := bstep (se 1 (by rfl) ⟨2553332, by rfl⟩ : syracuseStep 3404443 = 5106665) B5106665
theorem B4539257 : Blo 2017435 4539257 := bstep (se 2 (by rfl) ⟨1702221, by rfl⟩ : syracuseStep 4539257 = 3404443) B3404443
theorem B3026171 : Blo 2017435 3026171 := bstep (se 1 (by rfl) ⟨2269628, by rfl⟩ : syracuseStep 3026171 = 4539257) B4539257
theorem B2017447 : Blo 2017435 2017447 := bstep (se 1 (by rfl) ⟨1513085, by rfl⟩ : syracuseStep 2017447 = 3026171) B3026171
theorem B2269633 : Blo 2017435 2269633 := bbase (se 2 (by rfl) ⟨851112, by rfl⟩ : syracuseStep 2269633 = 1702225) (by norm_num)
theorem B3026177 : Blo 2017435 3026177 := bstep (se 2 (by rfl) ⟨1134816, by rfl⟩ : syracuseStep 3026177 = 2269633) B2269633
theorem B2017451 : Blo 2017435 2017451 := bstep (se 1 (by rfl) ⟨1513088, by rfl⟩ : syracuseStep 2017451 = 3026177) B3026177
theorem B5106685 : Blo 2017435 5106685 := bbase (se 3 (by rfl) ⟨957503, by rfl⟩ : syracuseStep 5106685 = 1915007) (by norm_num)
theorem B6808913 : Blo 2017435 6808913 := bstep (se 2 (by rfl) ⟨2553342, by rfl⟩ : syracuseStep 6808913 = 5106685) B5106685
theorem B4539275 : Blo 2017435 4539275 := bstep (se 1 (by rfl) ⟨3404456, by rfl⟩ : syracuseStep 4539275 = 6808913) B6808913
theorem B3026183 : Blo 2017435 3026183 := bstep (se 1 (by rfl) ⟨2269637, by rfl⟩ : syracuseStep 3026183 = 4539275) B4539275
theorem B2017455 : Blo 2017435 2017455 := bstep (se 1 (by rfl) ⟨1513091, by rfl⟩ : syracuseStep 2017455 = 3026183) B3026183
theorem B3026189 : Blo 2017435 3026189 := bbase (se 3 (by rfl) ⟨567410, by rfl⟩ : syracuseStep 3026189 = 1134821) (by norm_num)
theorem B2017459 : Blo 2017435 2017459 := bstep (se 1 (by rfl) ⟨1513094, by rfl⟩ : syracuseStep 2017459 = 3026189) B3026189
theorem B4539293 : Blo 2017435 4539293 := bbase (se 3 (by rfl) ⟨851117, by rfl⟩ : syracuseStep 4539293 = 1702235) (by norm_num)
theorem B3026195 : Blo 2017435 3026195 := bstep (se 1 (by rfl) ⟨2269646, by rfl⟩ : syracuseStep 3026195 = 4539293) B4539293
theorem B2017463 : Blo 2017435 2017463 := bstep (se 1 (by rfl) ⟨1513097, by rfl⟩ : syracuseStep 2017463 = 3026195) B3026195
theorem B3404477 : Blo 2017435 3404477 := bbase (se 3 (by rfl) ⟨638339, by rfl⟩ : syracuseStep 3404477 = 1276679) (by norm_num)
theorem B2269651 : Blo 2017435 2269651 := bstep (se 1 (by rfl) ⟨1702238, by rfl⟩ : syracuseStep 2269651 = 3404477) B3404477
theorem B3026201 : Blo 2017435 3026201 := bstep (se 2 (by rfl) ⟨1134825, by rfl⟩ : syracuseStep 3026201 = 2269651) B2269651
theorem B2017467 : Blo 2017435 2017467 := bstep (se 1 (by rfl) ⟨1513100, by rfl⟩ : syracuseStep 2017467 = 3026201) B3026201
theorem B11490133 : Blo 2017435 11490133 := bbase (se 9 (by rfl) ⟨33662, by rfl⟩ : syracuseStep 11490133 = 67325) (by norm_num)
theorem B15320177 : Blo 2017435 15320177 := bstep (se 2 (by rfl) ⟨5745066, by rfl⟩ : syracuseStep 15320177 = 11490133) B11490133
theorem B10213451 : Blo 2017435 10213451 := bstep (se 1 (by rfl) ⟨7660088, by rfl⟩ : syracuseStep 10213451 = 15320177) B15320177
theorem B6808967 : Blo 2017435 6808967 := bstep (se 1 (by rfl) ⟨5106725, by rfl⟩ : syracuseStep 6808967 = 10213451) B10213451
theorem B4539311 : Blo 2017435 4539311 := bstep (se 1 (by rfl) ⟨3404483, by rfl⟩ : syracuseStep 4539311 = 6808967) B6808967
theorem B3026207 : Blo 2017435 3026207 := bstep (se 1 (by rfl) ⟨2269655, by rfl⟩ : syracuseStep 3026207 = 4539311) B4539311
theorem B2017471 : Blo 2017435 2017471 := bstep (se 1 (by rfl) ⟨1513103, by rfl⟩ : syracuseStep 2017471 = 3026207) B3026207
theorem B3026213 : Blo 2017435 3026213 := bbase (se 4 (by rfl) ⟨283707, by rfl⟩ : syracuseStep 3026213 = 567415) (by norm_num)
theorem B2017475 : Blo 2017435 2017475 := bstep (se 1 (by rfl) ⟨1513106, by rfl⟩ : syracuseStep 2017475 = 3026213) B3026213
theorem B2553373 : Blo 2017435 2553373 := bbase (se 3 (by rfl) ⟨478757, by rfl⟩ : syracuseStep 2553373 = 957515) (by norm_num)
theorem B3404497 : Blo 2017435 3404497 := bstep (se 2 (by rfl) ⟨1276686, by rfl⟩ : syracuseStep 3404497 = 2553373) B2553373
theorem B4539329 : Blo 2017435 4539329 := bstep (se 2 (by rfl) ⟨1702248, by rfl⟩ : syracuseStep 4539329 = 3404497) B3404497
theorem B3026219 : Blo 2017435 3026219 := bstep (se 1 (by rfl) ⟨2269664, by rfl⟩ : syracuseStep 3026219 = 4539329) B4539329
theorem B2017479 : Blo 2017435 2017479 := bstep (se 1 (by rfl) ⟨1513109, by rfl⟩ : syracuseStep 2017479 = 3026219) B3026219
theorem B2269669 : Blo 2017435 2269669 := bbase (se 4 (by rfl) ⟨212781, by rfl⟩ : syracuseStep 2269669 = 425563) (by norm_num)
theorem B3026225 : Blo 2017435 3026225 := bstep (se 2 (by rfl) ⟨1134834, by rfl⟩ : syracuseStep 3026225 = 2269669) B2269669
theorem B2017483 : Blo 2017435 2017483 := bstep (se 1 (by rfl) ⟨1513112, by rfl⟩ : syracuseStep 2017483 = 3026225) B3026225
theorem B6463253 : Blo 2017435 6463253 := bbase (se 6 (by rfl) ⟨151482, by rfl⟩ : syracuseStep 6463253 = 302965) (by norm_num)
theorem B4308835 : Blo 2017435 4308835 := bstep (se 1 (by rfl) ⟨3231626, by rfl⟩ : syracuseStep 4308835 = 6463253) B6463253
theorem B5745113 : Blo 2017435 5745113 := bstep (se 2 (by rfl) ⟨2154417, by rfl⟩ : syracuseStep 5745113 = 4308835) B4308835
theorem B3830075 : Blo 2017435 3830075 := bstep (se 1 (by rfl) ⟨2872556, by rfl⟩ : syracuseStep 3830075 = 5745113) B5745113
theorem B2553383 : Blo 2017435 2553383 := bstep (se 1 (by rfl) ⟨1915037, by rfl⟩ : syracuseStep 2553383 = 3830075) B3830075
theorem B6809021 : Blo 2017435 6809021 := bstep (se 3 (by rfl) ⟨1276691, by rfl⟩ : syracuseStep 6809021 = 2553383) B2553383
theorem B4539347 : Blo 2017435 4539347 := bstep (se 1 (by rfl) ⟨3404510, by rfl⟩ : syracuseStep 4539347 = 6809021) B6809021
theorem B3026231 : Blo 2017435 3026231 := bstep (se 1 (by rfl) ⟨2269673, by rfl⟩ : syracuseStep 3026231 = 4539347) B4539347
theorem B2017487 : Blo 2017435 2017487 := bstep (se 1 (by rfl) ⟨1513115, by rfl⟩ : syracuseStep 2017487 = 3026231) B3026231
theorem B3026237 : Blo 2017435 3026237 := bbase (se 3 (by rfl) ⟨567419, by rfl⟩ : syracuseStep 3026237 = 1134839) (by norm_num)
theorem B2017491 : Blo 2017435 2017491 := bstep (se 1 (by rfl) ⟨1513118, by rfl⟩ : syracuseStep 2017491 = 3026237) B3026237
theorem B4539365 : Blo 2017435 4539365 := bbase (se 4 (by rfl) ⟨425565, by rfl⟩ : syracuseStep 4539365 = 851131) (by norm_num)
theorem B3026243 : Blo 2017435 3026243 := bstep (se 1 (by rfl) ⟨2269682, by rfl⟩ : syracuseStep 3026243 = 4539365) B4539365
theorem B2017495 : Blo 2017435 2017495 := bstep (se 1 (by rfl) ⟨1513121, by rfl⟩ : syracuseStep 2017495 = 3026243) B3026243
theorem B5106797 : Blo 2017435 5106797 := bbase (se 3 (by rfl) ⟨957524, by rfl⟩ : syracuseStep 5106797 = 1915049) (by norm_num)
theorem B3404531 : Blo 2017435 3404531 := bstep (se 1 (by rfl) ⟨2553398, by rfl⟩ : syracuseStep 3404531 = 5106797) B5106797
theorem B2269687 : Blo 2017435 2269687 := bstep (se 1 (by rfl) ⟨1702265, by rfl⟩ : syracuseStep 2269687 = 3404531) B3404531
theorem B3026249 : Blo 2017435 3026249 := bstep (se 2 (by rfl) ⟨1134843, by rfl⟩ : syracuseStep 3026249 = 2269687) B2269687
theorem B2017499 : Blo 2017435 2017499 := bstep (se 1 (by rfl) ⟨1513124, by rfl⟩ : syracuseStep 2017499 = 3026249) B3026249
theorem B4308869 : Blo 2017435 4308869 := bbase (se 4 (by rfl) ⟨403956, by rfl⟩ : syracuseStep 4308869 = 807913) (by norm_num)
theorem B2872579 : Blo 2017435 2872579 := bstep (se 1 (by rfl) ⟨2154434, by rfl⟩ : syracuseStep 2872579 = 4308869) B4308869
theorem B3830105 : Blo 2017435 3830105 := bstep (se 2 (by rfl) ⟨1436289, by rfl⟩ : syracuseStep 3830105 = 2872579) B2872579
theorem B10213613 : Blo 2017435 10213613 := bstep (se 3 (by rfl) ⟨1915052, by rfl⟩ : syracuseStep 10213613 = 3830105) B3830105
theorem B6809075 : Blo 2017435 6809075 := bstep (se 1 (by rfl) ⟨5106806, by rfl⟩ : syracuseStep 6809075 = 10213613) B10213613
theorem B4539383 : Blo 2017435 4539383 := bstep (se 1 (by rfl) ⟨3404537, by rfl⟩ : syracuseStep 4539383 = 6809075) B6809075
theorem B3026255 : Blo 2017435 3026255 := bstep (se 1 (by rfl) ⟨2269691, by rfl⟩ : syracuseStep 3026255 = 4539383) B4539383
theorem B2017503 : Blo 2017435 2017503 := bstep (se 1 (by rfl) ⟨1513127, by rfl⟩ : syracuseStep 2017503 = 3026255) B3026255
theorem B3026261 : Blo 2017435 3026261 := bbase (se 11 (by rfl) ⟨2216, by rfl⟩ : syracuseStep 3026261 = 4433) (by norm_num)
theorem B2017507 : Blo 2017435 2017507 := bstep (se 1 (by rfl) ⟨1513130, by rfl⟩ : syracuseStep 2017507 = 3026261) B3026261
theorem B2423749 : Blo 2017435 2423749 := bbase (se 4 (by rfl) ⟨227226, by rfl⟩ : syracuseStep 2423749 = 454453) (by norm_num)
theorem B3231665 : Blo 2017435 3231665 := bstep (se 2 (by rfl) ⟨1211874, by rfl⟩ : syracuseStep 3231665 = 2423749) B2423749
theorem B2154443 : Blo 2017435 2154443 := bstep (se 1 (by rfl) ⟨1615832, by rfl⟩ : syracuseStep 2154443 = 3231665) B3231665
theorem B5745181 : Blo 2017435 5745181 := bstep (se 3 (by rfl) ⟨1077221, by rfl⟩ : syracuseStep 5745181 = 2154443) B2154443
theorem B7660241 : Blo 2017435 7660241 := bstep (se 2 (by rfl) ⟨2872590, by rfl⟩ : syracuseStep 7660241 = 5745181) B5745181
theorem B5106827 : Blo 2017435 5106827 := bstep (se 1 (by rfl) ⟨3830120, by rfl⟩ : syracuseStep 5106827 = 7660241) B7660241
theorem B3404551 : Blo 2017435 3404551 := bstep (se 1 (by rfl) ⟨2553413, by rfl⟩ : syracuseStep 3404551 = 5106827) B5106827
theorem B4539401 : Blo 2017435 4539401 := bstep (se 2 (by rfl) ⟨1702275, by rfl⟩ : syracuseStep 4539401 = 3404551) B3404551
theorem B3026267 : Blo 2017435 3026267 := bstep (se 1 (by rfl) ⟨2269700, by rfl⟩ : syracuseStep 3026267 = 4539401) B4539401
theorem B2017511 : Blo 2017435 2017511 := bstep (se 1 (by rfl) ⟨1513133, by rfl⟩ : syracuseStep 2017511 = 3026267) B3026267
theorem B2269705 : Blo 2017435 2269705 := bbase (se 2 (by rfl) ⟨851139, by rfl⟩ : syracuseStep 2269705 = 1702279) (by norm_num)
theorem B3026273 : Blo 2017435 3026273 := bstep (se 2 (by rfl) ⟨1134852, by rfl⟩ : syracuseStep 3026273 = 2269705) B2269705
theorem B2017515 : Blo 2017435 2017515 := bstep (se 1 (by rfl) ⟨1513136, by rfl⟩ : syracuseStep 2017515 = 3026273) B3026273
theorem B3109421 : Blo 2017435 3109421 := bbase (se 3 (by rfl) ⟨583016, by rfl⟩ : syracuseStep 3109421 = 1166033) (by norm_num)
theorem B8291789 : Blo 2017435 8291789 := bstep (se 3 (by rfl) ⟨1554710, by rfl⟩ : syracuseStep 8291789 = 3109421) B3109421
theorem B5527859 : Blo 2017435 5527859 := bstep (se 1 (by rfl) ⟨4145894, by rfl⟩ : syracuseStep 5527859 = 8291789) B8291789
theorem B14740957 : Blo 2017435 14740957 := bstep (se 3 (by rfl) ⟨2763929, by rfl⟩ : syracuseStep 14740957 = 5527859) B5527859
theorem B78618437 : Blo 2017435 78618437 := bstep (se 4 (by rfl) ⟨7370478, by rfl⟩ : syracuseStep 78618437 = 14740957) B14740957
theorem B52412291 : Blo 2017435 52412291 := bstep (se 1 (by rfl) ⟨39309218, by rfl⟩ : syracuseStep 52412291 = 78618437) B78618437
theorem B34941527 : Blo 2017435 34941527 := bstep (se 1 (by rfl) ⟨26206145, by rfl⟩ : syracuseStep 34941527 = 52412291) B52412291
theorem B23294351 : Blo 2017435 23294351 := bstep (se 1 (by rfl) ⟨17470763, by rfl⟩ : syracuseStep 23294351 = 34941527) B34941527
theorem B15529567 : Blo 2017435 15529567 := bstep (se 1 (by rfl) ⟨11647175, by rfl⟩ : syracuseStep 15529567 = 23294351) B23294351
theorem B20706089 : Blo 2017435 20706089 := bstep (se 2 (by rfl) ⟨7764783, by rfl⟩ : syracuseStep 20706089 = 15529567) B15529567
theorem B55216237 : Blo 2017435 55216237 := bstep (se 3 (by rfl) ⟨10353044, by rfl⟩ : syracuseStep 55216237 = 20706089) B20706089
theorem B73621649 : Blo 2017435 73621649 := bstep (se 2 (by rfl) ⟨27608118, by rfl⟩ : syracuseStep 73621649 = 55216237) B55216237
theorem B49081099 : Blo 2017435 49081099 := bstep (se 1 (by rfl) ⟨36810824, by rfl⟩ : syracuseStep 49081099 = 73621649) B73621649
theorem B65441465 : Blo 2017435 65441465 := bstep (se 2 (by rfl) ⟨24540549, by rfl⟩ : syracuseStep 65441465 = 49081099) B49081099
theorem B43627643 : Blo 2017435 43627643 := bstep (se 1 (by rfl) ⟨32720732, by rfl⟩ : syracuseStep 43627643 = 65441465) B65441465
theorem B29085095 : Blo 2017435 29085095 := bstep (se 1 (by rfl) ⟨21813821, by rfl⟩ : syracuseStep 29085095 = 43627643) B43627643
theorem B19390063 : Blo 2017435 19390063 := bstep (se 1 (by rfl) ⟨14542547, by rfl⟩ : syracuseStep 19390063 = 29085095) B29085095
theorem B25853417 : Blo 2017435 25853417 := bstep (se 2 (by rfl) ⟨9695031, by rfl⟩ : syracuseStep 25853417 = 19390063) B19390063
theorem B17235611 : Blo 2017435 17235611 := bstep (se 1 (by rfl) ⟨12926708, by rfl⟩ : syracuseStep 17235611 = 25853417) B25853417
theorem B11490407 : Blo 2017435 11490407 := bstep (se 1 (by rfl) ⟨8617805, by rfl⟩ : syracuseStep 11490407 = 17235611) B17235611
theorem B7660271 : Blo 2017435 7660271 := bstep (se 1 (by rfl) ⟨5745203, by rfl⟩ : syracuseStep 7660271 = 11490407) B11490407
theorem B5106847 : Blo 2017435 5106847 := bstep (se 1 (by rfl) ⟨3830135, by rfl⟩ : syracuseStep 5106847 = 7660271) B7660271
theorem B6809129 : Blo 2017435 6809129 := bstep (se 2 (by rfl) ⟨2553423, by rfl⟩ : syracuseStep 6809129 = 5106847) B5106847
theorem B4539419 : Blo 2017435 4539419 := bstep (se 1 (by rfl) ⟨3404564, by rfl⟩ : syracuseStep 4539419 = 6809129) B6809129
theorem B3026279 : Blo 2017435 3026279 := bstep (se 1 (by rfl) ⟨2269709, by rfl⟩ : syracuseStep 3026279 = 4539419) B4539419
theorem B2017519 : Blo 2017435 2017519 := bstep (se 1 (by rfl) ⟨1513139, by rfl⟩ : syracuseStep 2017519 = 3026279) B3026279
theorem B3026285 : Blo 2017435 3026285 := bbase (se 3 (by rfl) ⟨567428, by rfl⟩ : syracuseStep 3026285 = 1134857) (by norm_num)
theorem B2017523 : Blo 2017435 2017523 := bstep (se 1 (by rfl) ⟨1513142, by rfl⟩ : syracuseStep 2017523 = 3026285) B3026285
theorem B4539437 : Blo 2017435 4539437 := bbase (se 3 (by rfl) ⟨851144, by rfl⟩ : syracuseStep 4539437 = 1702289) (by norm_num)
theorem B3026291 : Blo 2017435 3026291 := bstep (se 1 (by rfl) ⟨2269718, by rfl⟩ : syracuseStep 3026291 = 4539437) B4539437
theorem B2017527 : Blo 2017435 2017527 := bstep (se 1 (by rfl) ⟨1513145, by rfl⟩ : syracuseStep 2017527 = 3026291) B3026291
theorem B2423773 : Blo 2017435 2423773 := bbase (se 3 (by rfl) ⟨454457, by rfl⟩ : syracuseStep 2423773 = 908915) (by norm_num)
theorem B12926789 : Blo 2017435 12926789 := bstep (se 4 (by rfl) ⟨1211886, by rfl⟩ : syracuseStep 12926789 = 2423773) B2423773
theorem B8617859 : Blo 2017435 8617859 := bstep (se 1 (by rfl) ⟨6463394, by rfl⟩ : syracuseStep 8617859 = 12926789) B12926789
theorem B5745239 : Blo 2017435 5745239 := bstep (se 1 (by rfl) ⟨4308929, by rfl⟩ : syracuseStep 5745239 = 8617859) B8617859
theorem B3830159 : Blo 2017435 3830159 := bstep (se 1 (by rfl) ⟨2872619, by rfl⟩ : syracuseStep 3830159 = 5745239) B5745239
theorem B2553439 : Blo 2017435 2553439 := bstep (se 1 (by rfl) ⟨1915079, by rfl⟩ : syracuseStep 2553439 = 3830159) B3830159
theorem B3404585 : Blo 2017435 3404585 := bstep (se 2 (by rfl) ⟨1276719, by rfl⟩ : syracuseStep 3404585 = 2553439) B2553439
theorem B2269723 : Blo 2017435 2269723 := bstep (se 1 (by rfl) ⟨1702292, by rfl⟩ : syracuseStep 2269723 = 3404585) B3404585
theorem B3026297 : Blo 2017435 3026297 := bstep (se 2 (by rfl) ⟨1134861, by rfl⟩ : syracuseStep 3026297 = 2269723) B2269723
theorem B2017531 : Blo 2017435 2017531 := bstep (se 1 (by rfl) ⟨1513148, by rfl⟩ : syracuseStep 2017531 = 3026297) B3026297
theorem B2423777 : Blo 2017435 2423777 := bbase (se 2 (by rfl) ⟨908916, by rfl⟩ : syracuseStep 2423777 = 1817833) (by norm_num)
theorem B6463405 : Blo 2017435 6463405 := bstep (se 3 (by rfl) ⟨1211888, by rfl⟩ : syracuseStep 6463405 = 2423777) B2423777
theorem B34471493 : Blo 2017435 34471493 := bstep (se 4 (by rfl) ⟨3231702, by rfl⟩ : syracuseStep 34471493 = 6463405) B6463405
theorem B22980995 : Blo 2017435 22980995 := bstep (se 1 (by rfl) ⟨17235746, by rfl⟩ : syracuseStep 22980995 = 34471493) B34471493
theorem B15320663 : Blo 2017435 15320663 := bstep (se 1 (by rfl) ⟨11490497, by rfl⟩ : syracuseStep 15320663 = 22980995) B22980995
theorem B10213775 : Blo 2017435 10213775 := bstep (se 1 (by rfl) ⟨7660331, by rfl⟩ : syracuseStep 10213775 = 15320663) B15320663
theorem B6809183 : Blo 2017435 6809183 := bstep (se 1 (by rfl) ⟨5106887, by rfl⟩ : syracuseStep 6809183 = 10213775) B10213775
theorem B4539455 : Blo 2017435 4539455 := bstep (se 1 (by rfl) ⟨3404591, by rfl⟩ : syracuseStep 4539455 = 6809183) B6809183
theorem B3026303 : Blo 2017435 3026303 := bstep (se 1 (by rfl) ⟨2269727, by rfl⟩ : syracuseStep 3026303 = 4539455) B4539455
theorem B2017535 : Blo 2017435 2017535 := bstep (se 1 (by rfl) ⟨1513151, by rfl⟩ : syracuseStep 2017535 = 3026303) B3026303
theorem B3026309 : Blo 2017435 3026309 := bbase (se 4 (by rfl) ⟨283716, by rfl⟩ : syracuseStep 3026309 = 567433) (by norm_num)
theorem B2017539 : Blo 2017435 2017539 := bstep (se 1 (by rfl) ⟨1513154, by rfl⟩ : syracuseStep 2017539 = 3026309) B3026309
theorem B3404605 : Blo 2017435 3404605 := bbase (se 3 (by rfl) ⟨638363, by rfl⟩ : syracuseStep 3404605 = 1276727) (by norm_num)
theorem B4539473 : Blo 2017435 4539473 := bstep (se 2 (by rfl) ⟨1702302, by rfl⟩ : syracuseStep 4539473 = 3404605) B3404605
theorem B3026315 : Blo 2017435 3026315 := bstep (se 1 (by rfl) ⟨2269736, by rfl⟩ : syracuseStep 3026315 = 4539473) B4539473
theorem B2017543 : Blo 2017435 2017543 := bstep (se 1 (by rfl) ⟨1513157, by rfl⟩ : syracuseStep 2017543 = 3026315) B3026315
theorem B2269741 : Blo 2017435 2269741 := bbase (se 3 (by rfl) ⟨425576, by rfl⟩ : syracuseStep 2269741 = 851153) (by norm_num)
theorem B3026321 : Blo 2017435 3026321 := bstep (se 2 (by rfl) ⟨1134870, by rfl⟩ : syracuseStep 3026321 = 2269741) B2269741
theorem B2017547 : Blo 2017435 2017547 := bstep (se 1 (by rfl) ⟨1513160, by rfl⟩ : syracuseStep 2017547 = 3026321) B3026321
theorem B6809237 : Blo 2017435 6809237 := bbase (se 6 (by rfl) ⟨159591, by rfl⟩ : syracuseStep 6809237 = 319183) (by norm_num)
theorem B4539491 : Blo 2017435 4539491 := bstep (se 1 (by rfl) ⟨3404618, by rfl⟩ : syracuseStep 4539491 = 6809237) B6809237
theorem B3026327 : Blo 2017435 3026327 := bstep (se 1 (by rfl) ⟨2269745, by rfl⟩ : syracuseStep 3026327 = 4539491) B4539491
theorem B2017551 : Blo 2017435 2017551 := bstep (se 1 (by rfl) ⟨1513163, by rfl⟩ : syracuseStep 2017551 = 3026327) B3026327
theorem B3026333 : Blo 2017435 3026333 := bbase (se 3 (by rfl) ⟨567437, by rfl⟩ : syracuseStep 3026333 = 1134875) (by norm_num)
theorem B2017555 : Blo 2017435 2017555 := bstep (se 1 (by rfl) ⟨1513166, by rfl⟩ : syracuseStep 2017555 = 3026333) B3026333
theorem B4539509 : Blo 2017435 4539509 := bbase (se 5 (by rfl) ⟨212789, by rfl⟩ : syracuseStep 4539509 = 425579) (by norm_num)
theorem B3026339 : Blo 2017435 3026339 := bstep (se 1 (by rfl) ⟨2269754, by rfl⟩ : syracuseStep 3026339 = 4539509) B4539509
theorem B2017559 : Blo 2017435 2017559 := bstep (se 1 (by rfl) ⟨1513169, by rfl⟩ : syracuseStep 2017559 = 3026339) B3026339
theorem B17235989 : Blo 2017435 17235989 := bbase (se 6 (by rfl) ⟨403968, by rfl⟩ : syracuseStep 17235989 = 807937) (by norm_num)
theorem B11490659 : Blo 2017435 11490659 := bstep (se 1 (by rfl) ⟨8617994, by rfl⟩ : syracuseStep 11490659 = 17235989) B17235989
theorem B7660439 : Blo 2017435 7660439 := bstep (se 1 (by rfl) ⟨5745329, by rfl⟩ : syracuseStep 7660439 = 11490659) B11490659
theorem B5106959 : Blo 2017435 5106959 := bstep (se 1 (by rfl) ⟨3830219, by rfl⟩ : syracuseStep 5106959 = 7660439) B7660439
theorem B3404639 : Blo 2017435 3404639 := bstep (se 1 (by rfl) ⟨2553479, by rfl⟩ : syracuseStep 3404639 = 5106959) B5106959
theorem B2269759 : Blo 2017435 2269759 := bstep (se 1 (by rfl) ⟨1702319, by rfl⟩ : syracuseStep 2269759 = 3404639) B3404639
theorem B3026345 : Blo 2017435 3026345 := bstep (se 2 (by rfl) ⟨1134879, by rfl⟩ : syracuseStep 3026345 = 2269759) B2269759
theorem B2017563 : Blo 2017435 2017563 := bstep (se 1 (by rfl) ⟨1513172, by rfl⟩ : syracuseStep 2017563 = 3026345) B3026345
theorem B7660453 : Blo 2017435 7660453 := bbase (se 4 (by rfl) ⟨718167, by rfl⟩ : syracuseStep 7660453 = 1436335) (by norm_num)
theorem B10213937 : Blo 2017435 10213937 := bstep (se 2 (by rfl) ⟨3830226, by rfl⟩ : syracuseStep 10213937 = 7660453) B7660453
theorem B6809291 : Blo 2017435 6809291 := bstep (se 1 (by rfl) ⟨5106968, by rfl⟩ : syracuseStep 6809291 = 10213937) B10213937
theorem B4539527 : Blo 2017435 4539527 := bstep (se 1 (by rfl) ⟨3404645, by rfl⟩ : syracuseStep 4539527 = 6809291) B6809291
theorem B3026351 : Blo 2017435 3026351 := bstep (se 1 (by rfl) ⟨2269763, by rfl⟩ : syracuseStep 3026351 = 4539527) B4539527
theorem B2017567 : Blo 2017435 2017567 := bstep (se 1 (by rfl) ⟨1513175, by rfl⟩ : syracuseStep 2017567 = 3026351) B3026351
theorem B3026357 : Blo 2017435 3026357 := bbase (se 5 (by rfl) ⟨141860, by rfl⟩ : syracuseStep 3026357 = 283721) (by norm_num)
theorem B2017571 : Blo 2017435 2017571 := bstep (se 1 (by rfl) ⟨1513178, by rfl⟩ : syracuseStep 2017571 = 3026357) B3026357
theorem B5106989 : Blo 2017435 5106989 := bbase (se 3 (by rfl) ⟨957560, by rfl⟩ : syracuseStep 5106989 = 1915121) (by norm_num)
theorem B3404659 : Blo 2017435 3404659 := bstep (se 1 (by rfl) ⟨2553494, by rfl⟩ : syracuseStep 3404659 = 5106989) B5106989
theorem B4539545 : Blo 2017435 4539545 := bstep (se 2 (by rfl) ⟨1702329, by rfl⟩ : syracuseStep 4539545 = 3404659) B3404659
theorem B3026363 : Blo 2017435 3026363 := bstep (se 1 (by rfl) ⟨2269772, by rfl⟩ : syracuseStep 3026363 = 4539545) B4539545
theorem B2017575 : Blo 2017435 2017575 := bstep (se 1 (by rfl) ⟨1513181, by rfl⟩ : syracuseStep 2017575 = 3026363) B3026363
theorem B2269777 : Blo 2017435 2269777 := bbase (se 2 (by rfl) ⟨851166, by rfl⟩ : syracuseStep 2269777 = 1702333) (by norm_num)
theorem B3026369 : Blo 2017435 3026369 := bstep (se 2 (by rfl) ⟨1134888, by rfl⟩ : syracuseStep 3026369 = 2269777) B2269777
theorem B2017579 : Blo 2017435 2017579 := bstep (se 1 (by rfl) ⟨1513184, by rfl⟩ : syracuseStep 2017579 = 3026369) B3026369
theorem B2872693 : Blo 2017435 2872693 := bbase (se 5 (by rfl) ⟨134657, by rfl⟩ : syracuseStep 2872693 = 269315) (by norm_num)
theorem B3830257 : Blo 2017435 3830257 := bstep (se 2 (by rfl) ⟨1436346, by rfl⟩ : syracuseStep 3830257 = 2872693) B2872693
theorem B5107009 : Blo 2017435 5107009 := bstep (se 2 (by rfl) ⟨1915128, by rfl⟩ : syracuseStep 5107009 = 3830257) B3830257
theorem B6809345 : Blo 2017435 6809345 := bstep (se 2 (by rfl) ⟨2553504, by rfl⟩ : syracuseStep 6809345 = 5107009) B5107009
theorem B4539563 : Blo 2017435 4539563 := bstep (se 1 (by rfl) ⟨3404672, by rfl⟩ : syracuseStep 4539563 = 6809345) B6809345
theorem B3026375 : Blo 2017435 3026375 := bstep (se 1 (by rfl) ⟨2269781, by rfl⟩ : syracuseStep 3026375 = 4539563) B4539563
theorem B2017583 : Blo 2017435 2017583 := bstep (se 1 (by rfl) ⟨1513187, by rfl⟩ : syracuseStep 2017583 = 3026375) B3026375
theorem B3026381 : Blo 2017435 3026381 := bbase (se 3 (by rfl) ⟨567446, by rfl⟩ : syracuseStep 3026381 = 1134893) (by norm_num)
theorem B2017587 : Blo 2017435 2017587 := bstep (se 1 (by rfl) ⟨1513190, by rfl⟩ : syracuseStep 2017587 = 3026381) B3026381
theorem B4539581 : Blo 2017435 4539581 := bbase (se 3 (by rfl) ⟨851171, by rfl⟩ : syracuseStep 4539581 = 1702343) (by norm_num)
theorem B3026387 : Blo 2017435 3026387 := bstep (se 1 (by rfl) ⟨2269790, by rfl⟩ : syracuseStep 3026387 = 4539581) B4539581
theorem B2017591 : Blo 2017435 2017591 := bstep (se 1 (by rfl) ⟨1513193, by rfl⟩ : syracuseStep 2017591 = 3026387) B3026387
theorem B3404693 : Blo 2017435 3404693 := bbase (se 6 (by rfl) ⟨79797, by rfl⟩ : syracuseStep 3404693 = 159595) (by norm_num)
theorem B2269795 : Blo 2017435 2269795 := bstep (se 1 (by rfl) ⟨1702346, by rfl⟩ : syracuseStep 2269795 = 3404693) B3404693
theorem B3026393 : Blo 2017435 3026393 := bstep (se 2 (by rfl) ⟨1134897, by rfl⟩ : syracuseStep 3026393 = 2269795) B2269795
theorem B2017595 : Blo 2017435 2017595 := bstep (se 1 (by rfl) ⟨1513196, by rfl⟩ : syracuseStep 2017595 = 3026393) B3026393
theorem B12927221 : Blo 2017435 12927221 := bbase (se 5 (by rfl) ⟨605963, by rfl⟩ : syracuseStep 12927221 = 1211927) (by norm_num)
theorem B8618147 : Blo 2017435 8618147 := bstep (se 1 (by rfl) ⟨6463610, by rfl⟩ : syracuseStep 8618147 = 12927221) B12927221
theorem B5745431 : Blo 2017435 5745431 := bstep (se 1 (by rfl) ⟨4309073, by rfl⟩ : syracuseStep 5745431 = 8618147) B8618147
theorem B15321149 : Blo 2017435 15321149 := bstep (se 3 (by rfl) ⟨2872715, by rfl⟩ : syracuseStep 15321149 = 5745431) B5745431
theorem B10214099 : Blo 2017435 10214099 := bstep (se 1 (by rfl) ⟨7660574, by rfl⟩ : syracuseStep 10214099 = 15321149) B15321149
theorem B6809399 : Blo 2017435 6809399 := bstep (se 1 (by rfl) ⟨5107049, by rfl⟩ : syracuseStep 6809399 = 10214099) B10214099
theorem B4539599 : Blo 2017435 4539599 := bstep (se 1 (by rfl) ⟨3404699, by rfl⟩ : syracuseStep 4539599 = 6809399) B6809399
theorem B3026399 : Blo 2017435 3026399 := bstep (se 1 (by rfl) ⟨2269799, by rfl⟩ : syracuseStep 3026399 = 4539599) B4539599
theorem B2017599 : Blo 2017435 2017599 := bstep (se 1 (by rfl) ⟨1513199, by rfl⟩ : syracuseStep 2017599 = 3026399) B3026399
theorem B3026405 : Blo 2017435 3026405 := bbase (se 4 (by rfl) ⟨283725, by rfl⟩ : syracuseStep 3026405 = 567451) (by norm_num)
theorem B2017603 : Blo 2017435 2017603 := bstep (se 1 (by rfl) ⟨1513202, by rfl⟩ : syracuseStep 2017603 = 3026405) B3026405
theorem B4913869 : Blo 2017435 4913869 := bbase (se 3 (by rfl) ⟨921350, by rfl⟩ : syracuseStep 4913869 = 1842701) (by norm_num)
theorem B6551825 : Blo 2017435 6551825 := bstep (se 2 (by rfl) ⟨2456934, by rfl⟩ : syracuseStep 6551825 = 4913869) B4913869
theorem B17471533 : Blo 2017435 17471533 := bstep (se 3 (by rfl) ⟨3275912, by rfl⟩ : syracuseStep 17471533 = 6551825) B6551825
theorem B23295377 : Blo 2017435 23295377 := bstep (se 2 (by rfl) ⟨8735766, by rfl⟩ : syracuseStep 23295377 = 17471533) B17471533
theorem B15530251 : Blo 2017435 15530251 := bstep (se 1 (by rfl) ⟨11647688, by rfl⟩ : syracuseStep 15530251 = 23295377) B23295377
theorem B20707001 : Blo 2017435 20707001 := bstep (se 2 (by rfl) ⟨7765125, by rfl⟩ : syracuseStep 20707001 = 15530251) B15530251
theorem B13804667 : Blo 2017435 13804667 := bstep (se 1 (by rfl) ⟨10353500, by rfl⟩ : syracuseStep 13804667 = 20707001) B20707001
theorem B9203111 : Blo 2017435 9203111 := bstep (se 1 (by rfl) ⟨6902333, by rfl⟩ : syracuseStep 9203111 = 13804667) B13804667
theorem B6135407 : Blo 2017435 6135407 := bstep (se 1 (by rfl) ⟨4601555, by rfl⟩ : syracuseStep 6135407 = 9203111) B9203111
theorem B4090271 : Blo 2017435 4090271 := bstep (se 1 (by rfl) ⟨3067703, by rfl⟩ : syracuseStep 4090271 = 6135407) B6135407
theorem B10907389 : Blo 2017435 10907389 := bstep (se 3 (by rfl) ⟨2045135, by rfl⟩ : syracuseStep 10907389 = 4090271) B4090271
theorem B14543185 : Blo 2017435 14543185 := bstep (se 2 (by rfl) ⟨5453694, by rfl⟩ : syracuseStep 14543185 = 10907389) B10907389
theorem B19390913 : Blo 2017435 19390913 := bstep (se 2 (by rfl) ⟨7271592, by rfl⟩ : syracuseStep 19390913 = 14543185) B14543185
theorem B12927275 : Blo 2017435 12927275 := bstep (se 1 (by rfl) ⟨9695456, by rfl⟩ : syracuseStep 12927275 = 19390913) B19390913
theorem B8618183 : Blo 2017435 8618183 := bstep (se 1 (by rfl) ⟨6463637, by rfl⟩ : syracuseStep 8618183 = 12927275) B12927275
theorem B5745455 : Blo 2017435 5745455 := bstep (se 1 (by rfl) ⟨4309091, by rfl⟩ : syracuseStep 5745455 = 8618183) B8618183
theorem B3830303 : Blo 2017435 3830303 := bstep (se 1 (by rfl) ⟨2872727, by rfl⟩ : syracuseStep 3830303 = 5745455) B5745455
theorem B2553535 : Blo 2017435 2553535 := bstep (se 1 (by rfl) ⟨1915151, by rfl⟩ : syracuseStep 2553535 = 3830303) B3830303
theorem B3404713 : Blo 2017435 3404713 := bstep (se 2 (by rfl) ⟨1276767, by rfl⟩ : syracuseStep 3404713 = 2553535) B2553535
theorem B4539617 : Blo 2017435 4539617 := bstep (se 2 (by rfl) ⟨1702356, by rfl⟩ : syracuseStep 4539617 = 3404713) B3404713
theorem B3026411 : Blo 2017435 3026411 := bstep (se 1 (by rfl) ⟨2269808, by rfl⟩ : syracuseStep 3026411 = 4539617) B4539617
theorem B2017607 : Blo 2017435 2017607 := bstep (se 1 (by rfl) ⟨1513205, by rfl⟩ : syracuseStep 2017607 = 3026411) B3026411
theorem B2269813 : Blo 2017435 2269813 := bbase (se 5 (by rfl) ⟨106397, by rfl⟩ : syracuseStep 2269813 = 212795) (by norm_num)
theorem B3026417 : Blo 2017435 3026417 := bstep (se 2 (by rfl) ⟨1134906, by rfl⟩ : syracuseStep 3026417 = 2269813) B2269813
theorem B2017611 : Blo 2017435 2017611 := bstep (se 1 (by rfl) ⟨1513208, by rfl⟩ : syracuseStep 2017611 = 3026417) B3026417
theorem B2553545 : Blo 2017435 2553545 := bbase (se 2 (by rfl) ⟨957579, by rfl⟩ : syracuseStep 2553545 = 1915159) (by norm_num)
theorem B6809453 : Blo 2017435 6809453 := bstep (se 3 (by rfl) ⟨1276772, by rfl⟩ : syracuseStep 6809453 = 2553545) B2553545
theorem B4539635 : Blo 2017435 4539635 := bstep (se 1 (by rfl) ⟨3404726, by rfl⟩ : syracuseStep 4539635 = 6809453) B6809453
theorem B3026423 : Blo 2017435 3026423 := bstep (se 1 (by rfl) ⟨2269817, by rfl⟩ : syracuseStep 3026423 = 4539635) B4539635
theorem B2017615 : Blo 2017435 2017615 := bstep (se 1 (by rfl) ⟨1513211, by rfl⟩ : syracuseStep 2017615 = 3026423) B3026423
theorem B3026429 : Blo 2017435 3026429 := bbase (se 3 (by rfl) ⟨567455, by rfl⟩ : syracuseStep 3026429 = 1134911) (by norm_num)
theorem B2017619 : Blo 2017435 2017619 := bstep (se 1 (by rfl) ⟨1513214, by rfl⟩ : syracuseStep 2017619 = 3026429) B3026429
theorem B4539653 : Blo 2017435 4539653 := bbase (se 4 (by rfl) ⟨425592, by rfl⟩ : syracuseStep 4539653 = 851185) (by norm_num)
theorem B3026435 : Blo 2017435 3026435 := bstep (se 1 (by rfl) ⟨2269826, by rfl⟩ : syracuseStep 3026435 = 4539653) B4539653
theorem B2017623 : Blo 2017435 2017623 := bstep (se 1 (by rfl) ⟨1513217, by rfl⟩ : syracuseStep 2017623 = 3026435) B3026435
theorem B3830341 : Blo 2017435 3830341 := bbase (se 4 (by rfl) ⟨359094, by rfl⟩ : syracuseStep 3830341 = 718189) (by norm_num)
theorem B5107121 : Blo 2017435 5107121 := bstep (se 2 (by rfl) ⟨1915170, by rfl⟩ : syracuseStep 5107121 = 3830341) B3830341
theorem B3404747 : Blo 2017435 3404747 := bstep (se 1 (by rfl) ⟨2553560, by rfl⟩ : syracuseStep 3404747 = 5107121) B5107121
theorem B2269831 : Blo 2017435 2269831 := bstep (se 1 (by rfl) ⟨1702373, by rfl⟩ : syracuseStep 2269831 = 3404747) B3404747
theorem B3026441 : Blo 2017435 3026441 := bstep (se 2 (by rfl) ⟨1134915, by rfl⟩ : syracuseStep 3026441 = 2269831) B2269831
theorem B2017627 : Blo 2017435 2017627 := bstep (se 1 (by rfl) ⟨1513220, by rfl⟩ : syracuseStep 2017627 = 3026441) B3026441
theorem B10214261 : Blo 2017435 10214261 := bbase (se 5 (by rfl) ⟨478793, by rfl⟩ : syracuseStep 10214261 = 957587) (by norm_num)
theorem B6809507 : Blo 2017435 6809507 := bstep (se 1 (by rfl) ⟨5107130, by rfl⟩ : syracuseStep 6809507 = 10214261) B10214261
theorem B4539671 : Blo 2017435 4539671 := bstep (se 1 (by rfl) ⟨3404753, by rfl⟩ : syracuseStep 4539671 = 6809507) B6809507
theorem B3026447 : Blo 2017435 3026447 := bstep (se 1 (by rfl) ⟨2269835, by rfl⟩ : syracuseStep 3026447 = 4539671) B4539671
theorem B2017631 : Blo 2017435 2017631 := bstep (se 1 (by rfl) ⟨1513223, by rfl⟩ : syracuseStep 2017631 = 3026447) B3026447
theorem B3026453 : Blo 2017435 3026453 := bbase (se 6 (by rfl) ⟨70932, by rfl⟩ : syracuseStep 3026453 = 141865) (by norm_num)
theorem B2017635 : Blo 2017435 2017635 := bstep (se 1 (by rfl) ⟨1513226, by rfl⟩ : syracuseStep 2017635 = 3026453) B3026453
theorem B5247461 : Blo 2017435 5247461 := bbase (se 4 (by rfl) ⟨491949, by rfl⟩ : syracuseStep 5247461 = 983899) (by norm_num)
theorem B13993229 : Blo 2017435 13993229 := bstep (se 3 (by rfl) ⟨2623730, by rfl⟩ : syracuseStep 13993229 = 5247461) B5247461
theorem B9328819 : Blo 2017435 9328819 := bstep (se 1 (by rfl) ⟨6996614, by rfl⟩ : syracuseStep 9328819 = 13993229) B13993229
theorem B12438425 : Blo 2017435 12438425 := bstep (se 2 (by rfl) ⟨4664409, by rfl⟩ : syracuseStep 12438425 = 9328819) B9328819
theorem B33169133 : Blo 2017435 33169133 := bstep (se 3 (by rfl) ⟨6219212, by rfl⟩ : syracuseStep 33169133 = 12438425) B12438425
theorem B88451021 : Blo 2017435 88451021 := bstep (se 3 (by rfl) ⟨16584566, by rfl⟩ : syracuseStep 88451021 = 33169133) B33169133
theorem B58967347 : Blo 2017435 58967347 := bstep (se 1 (by rfl) ⟨44225510, by rfl⟩ : syracuseStep 58967347 = 88451021) B88451021
theorem B78623129 : Blo 2017435 78623129 := bstep (se 2 (by rfl) ⟨29483673, by rfl⟩ : syracuseStep 78623129 = 58967347) B58967347
theorem B52415419 : Blo 2017435 52415419 := bstep (se 1 (by rfl) ⟨39311564, by rfl⟩ : syracuseStep 52415419 = 78623129) B78623129
theorem B69887225 : Blo 2017435 69887225 := bstep (se 2 (by rfl) ⟨26207709, by rfl⟩ : syracuseStep 69887225 = 52415419) B52415419
theorem B46591483 : Blo 2017435 46591483 := bstep (se 1 (by rfl) ⟨34943612, by rfl⟩ : syracuseStep 46591483 = 69887225) B69887225
theorem B62121977 : Blo 2017435 62121977 := bstep (se 2 (by rfl) ⟨23295741, by rfl⟩ : syracuseStep 62121977 = 46591483) B46591483
theorem B41414651 : Blo 2017435 41414651 := bstep (se 1 (by rfl) ⟨31060988, by rfl⟩ : syracuseStep 41414651 = 62121977) B62121977
theorem B27609767 : Blo 2017435 27609767 := bstep (se 1 (by rfl) ⟨20707325, by rfl⟩ : syracuseStep 27609767 = 41414651) B41414651
theorem B18406511 : Blo 2017435 18406511 := bstep (se 1 (by rfl) ⟨13804883, by rfl⟩ : syracuseStep 18406511 = 27609767) B27609767
theorem B12271007 : Blo 2017435 12271007 := bstep (se 1 (by rfl) ⟨9203255, by rfl⟩ : syracuseStep 12271007 = 18406511) B18406511
theorem B8180671 : Blo 2017435 8180671 := bstep (se 1 (by rfl) ⟨6135503, by rfl⟩ : syracuseStep 8180671 = 12271007) B12271007
theorem B10907561 : Blo 2017435 10907561 := bstep (se 2 (by rfl) ⟨4090335, by rfl⟩ : syracuseStep 10907561 = 8180671) B8180671
theorem B7271707 : Blo 2017435 7271707 := bstep (se 1 (by rfl) ⟨5453780, by rfl⟩ : syracuseStep 7271707 = 10907561) B10907561
theorem B9695609 : Blo 2017435 9695609 := bstep (se 2 (by rfl) ⟨3635853, by rfl⟩ : syracuseStep 9695609 = 7271707) B7271707
theorem B6463739 : Blo 2017435 6463739 := bstep (se 1 (by rfl) ⟨4847804, by rfl⟩ : syracuseStep 6463739 = 9695609) B9695609
theorem B17236637 : Blo 2017435 17236637 := bstep (se 3 (by rfl) ⟨3231869, by rfl⟩ : syracuseStep 17236637 = 6463739) B6463739
theorem B11491091 : Blo 2017435 11491091 := bstep (se 1 (by rfl) ⟨8618318, by rfl⟩ : syracuseStep 11491091 = 17236637) B17236637
theorem B7660727 : Blo 2017435 7660727 := bstep (se 1 (by rfl) ⟨5745545, by rfl⟩ : syracuseStep 7660727 = 11491091) B11491091
theorem B5107151 : Blo 2017435 5107151 := bstep (se 1 (by rfl) ⟨3830363, by rfl⟩ : syracuseStep 5107151 = 7660727) B7660727
theorem B3404767 : Blo 2017435 3404767 := bstep (se 1 (by rfl) ⟨2553575, by rfl⟩ : syracuseStep 3404767 = 5107151) B5107151
theorem B4539689 : Blo 2017435 4539689 := bstep (se 2 (by rfl) ⟨1702383, by rfl⟩ : syracuseStep 4539689 = 3404767) B3404767
theorem B3026459 : Blo 2017435 3026459 := bstep (se 1 (by rfl) ⟨2269844, by rfl⟩ : syracuseStep 3026459 = 4539689) B4539689
theorem B2017639 : Blo 2017435 2017639 := bstep (se 1 (by rfl) ⟨1513229, by rfl⟩ : syracuseStep 2017639 = 3026459) B3026459
theorem B2269849 : Blo 2017435 2269849 := bbase (se 2 (by rfl) ⟨851193, by rfl⟩ : syracuseStep 2269849 = 1702387) (by norm_num)
theorem B3026465 : Blo 2017435 3026465 := bstep (se 2 (by rfl) ⟨1134924, by rfl⟩ : syracuseStep 3026465 = 2269849) B2269849
theorem B2017643 : Blo 2017435 2017643 := bstep (se 1 (by rfl) ⟨1513232, by rfl⟩ : syracuseStep 2017643 = 3026465) B3026465
theorem B7660757 : Blo 2017435 7660757 := bbase (se 7 (by rfl) ⟨89774, by rfl⟩ : syracuseStep 7660757 = 179549) (by norm_num)
theorem B5107171 : Blo 2017435 5107171 := bstep (se 1 (by rfl) ⟨3830378, by rfl⟩ : syracuseStep 5107171 = 7660757) B7660757
theorem B6809561 : Blo 2017435 6809561 := bstep (se 2 (by rfl) ⟨2553585, by rfl⟩ : syracuseStep 6809561 = 5107171) B5107171
theorem B4539707 : Blo 2017435 4539707 := bstep (se 1 (by rfl) ⟨3404780, by rfl⟩ : syracuseStep 4539707 = 6809561) B6809561
theorem B3026471 : Blo 2017435 3026471 := bstep (se 1 (by rfl) ⟨2269853, by rfl⟩ : syracuseStep 3026471 = 4539707) B4539707
theorem B2017647 : Blo 2017435 2017647 := bstep (se 1 (by rfl) ⟨1513235, by rfl⟩ : syracuseStep 2017647 = 3026471) B3026471
theorem B3026477 : Blo 2017435 3026477 := bbase (se 3 (by rfl) ⟨567464, by rfl⟩ : syracuseStep 3026477 = 1134929) (by norm_num)
theorem B2017651 : Blo 2017435 2017651 := bstep (se 1 (by rfl) ⟨1513238, by rfl⟩ : syracuseStep 2017651 = 3026477) B3026477
theorem B4539725 : Blo 2017435 4539725 := bbase (se 3 (by rfl) ⟨851198, by rfl⟩ : syracuseStep 4539725 = 1702397) (by norm_num)
theorem B3026483 : Blo 2017435 3026483 := bstep (se 1 (by rfl) ⟨2269862, by rfl⟩ : syracuseStep 3026483 = 4539725) B4539725
theorem B2017655 : Blo 2017435 2017655 := bstep (se 1 (by rfl) ⟨1513241, by rfl⟩ : syracuseStep 2017655 = 3026483) B3026483
theorem B2553601 : Blo 2017435 2553601 := bbase (se 2 (by rfl) ⟨957600, by rfl⟩ : syracuseStep 2553601 = 1915201) (by norm_num)
theorem B3404801 : Blo 2017435 3404801 := bstep (se 2 (by rfl) ⟨1276800, by rfl⟩ : syracuseStep 3404801 = 2553601) B2553601
theorem B2269867 : Blo 2017435 2269867 := bstep (se 1 (by rfl) ⟨1702400, by rfl⟩ : syracuseStep 2269867 = 3404801) B3404801
theorem B3026489 : Blo 2017435 3026489 := bstep (se 2 (by rfl) ⟨1134933, by rfl⟩ : syracuseStep 3026489 = 2269867) B2269867
theorem B2017659 : Blo 2017435 2017659 := bstep (se 1 (by rfl) ⟨1513244, by rfl⟩ : syracuseStep 2017659 = 3026489) B3026489
theorem B2154605 : Blo 2017435 2154605 := bbase (se 3 (by rfl) ⟨403988, by rfl⟩ : syracuseStep 2154605 = 807977) (by norm_num)
theorem B22982453 : Blo 2017435 22982453 := bstep (se 5 (by rfl) ⟨1077302, by rfl⟩ : syracuseStep 22982453 = 2154605) B2154605
theorem B15321635 : Blo 2017435 15321635 := bstep (se 1 (by rfl) ⟨11491226, by rfl⟩ : syracuseStep 15321635 = 22982453) B22982453
theorem B10214423 : Blo 2017435 10214423 := bstep (se 1 (by rfl) ⟨7660817, by rfl⟩ : syracuseStep 10214423 = 15321635) B15321635
theorem B6809615 : Blo 2017435 6809615 := bstep (se 1 (by rfl) ⟨5107211, by rfl⟩ : syracuseStep 6809615 = 10214423) B10214423
theorem B4539743 : Blo 2017435 4539743 := bstep (se 1 (by rfl) ⟨3404807, by rfl⟩ : syracuseStep 4539743 = 6809615) B6809615
theorem B3026495 : Blo 2017435 3026495 := bstep (se 1 (by rfl) ⟨2269871, by rfl⟩ : syracuseStep 3026495 = 4539743) B4539743
theorem B2017663 : Blo 2017435 2017663 := bstep (se 1 (by rfl) ⟨1513247, by rfl⟩ : syracuseStep 2017663 = 3026495) B3026495
theorem B3026501 : Blo 2017435 3026501 := bbase (se 4 (by rfl) ⟨283734, by rfl⟩ : syracuseStep 3026501 = 567469) (by norm_num)
theorem B2017667 : Blo 2017435 2017667 := bstep (se 1 (by rfl) ⟨1513250, by rfl⟩ : syracuseStep 2017667 = 3026501) B3026501
theorem B3404821 : Blo 2017435 3404821 := bbase (se 6 (by rfl) ⟨79800, by rfl⟩ : syracuseStep 3404821 = 159601) (by norm_num)
theorem B4539761 : Blo 2017435 4539761 := bstep (se 2 (by rfl) ⟨1702410, by rfl⟩ : syracuseStep 4539761 = 3404821) B3404821
theorem B3026507 : Blo 2017435 3026507 := bstep (se 1 (by rfl) ⟨2269880, by rfl⟩ : syracuseStep 3026507 = 4539761) B4539761
theorem B2017671 : Blo 2017435 2017671 := bstep (se 1 (by rfl) ⟨1513253, by rfl⟩ : syracuseStep 2017671 = 3026507) B3026507
theorem B2269885 : Blo 2017435 2269885 := bbase (se 3 (by rfl) ⟨425603, by rfl⟩ : syracuseStep 2269885 = 851207) (by norm_num)
theorem B3026513 : Blo 2017435 3026513 := bstep (se 2 (by rfl) ⟨1134942, by rfl⟩ : syracuseStep 3026513 = 2269885) B2269885
theorem B2017675 : Blo 2017435 2017675 := bstep (se 1 (by rfl) ⟨1513256, by rfl⟩ : syracuseStep 2017675 = 3026513) B3026513
theorem B6809669 : Blo 2017435 6809669 := bbase (se 4 (by rfl) ⟨638406, by rfl⟩ : syracuseStep 6809669 = 1276813) (by norm_num)
theorem B4539779 : Blo 2017435 4539779 := bstep (se 1 (by rfl) ⟨3404834, by rfl⟩ : syracuseStep 4539779 = 6809669) B6809669
theorem B3026519 : Blo 2017435 3026519 := bstep (se 1 (by rfl) ⟨2269889, by rfl⟩ : syracuseStep 3026519 = 4539779) B4539779
theorem B2017679 : Blo 2017435 2017679 := bstep (se 1 (by rfl) ⟨1513259, by rfl⟩ : syracuseStep 2017679 = 3026519) B3026519
theorem B3026525 : Blo 2017435 3026525 := bbase (se 3 (by rfl) ⟨567473, by rfl⟩ : syracuseStep 3026525 = 1134947) (by norm_num)
theorem B2017683 : Blo 2017435 2017683 := bstep (se 1 (by rfl) ⟨1513262, by rfl⟩ : syracuseStep 2017683 = 3026525) B3026525
theorem B4539797 : Blo 2017435 4539797 := bbase (se 6 (by rfl) ⟨106401, by rfl⟩ : syracuseStep 4539797 = 212803) (by norm_num)
theorem B3026531 : Blo 2017435 3026531 := bstep (se 1 (by rfl) ⟨2269898, by rfl⟩ : syracuseStep 3026531 = 4539797) B4539797
theorem B2017687 : Blo 2017435 2017687 := bstep (se 1 (by rfl) ⟨1513265, by rfl⟩ : syracuseStep 2017687 = 3026531) B3026531
theorem B9695861 : Blo 2017435 9695861 := bbase (se 5 (by rfl) ⟨454493, by rfl⟩ : syracuseStep 9695861 = 908987) (by norm_num)
theorem B6463907 : Blo 2017435 6463907 := bstep (se 1 (by rfl) ⟨4847930, by rfl⟩ : syracuseStep 6463907 = 9695861) B9695861
theorem B4309271 : Blo 2017435 4309271 := bstep (se 1 (by rfl) ⟨3231953, by rfl⟩ : syracuseStep 4309271 = 6463907) B6463907
theorem B2872847 : Blo 2017435 2872847 := bstep (se 1 (by rfl) ⟨2154635, by rfl⟩ : syracuseStep 2872847 = 4309271) B4309271
theorem B7660925 : Blo 2017435 7660925 := bstep (se 3 (by rfl) ⟨1436423, by rfl⟩ : syracuseStep 7660925 = 2872847) B2872847
theorem B5107283 : Blo 2017435 5107283 := bstep (se 1 (by rfl) ⟨3830462, by rfl⟩ : syracuseStep 5107283 = 7660925) B7660925
theorem B3404855 : Blo 2017435 3404855 := bstep (se 1 (by rfl) ⟨2553641, by rfl⟩ : syracuseStep 3404855 = 5107283) B5107283
theorem B2269903 : Blo 2017435 2269903 := bstep (se 1 (by rfl) ⟨1702427, by rfl⟩ : syracuseStep 2269903 = 3404855) B3404855
theorem B3026537 : Blo 2017435 3026537 := bstep (se 2 (by rfl) ⟨1134951, by rfl⟩ : syracuseStep 3026537 = 2269903) B2269903
theorem B2017691 : Blo 2017435 2017691 := bstep (se 1 (by rfl) ⟨1513268, by rfl⟩ : syracuseStep 2017691 = 3026537) B3026537
theorem B7271909 : Blo 2017435 7271909 := bbase (se 4 (by rfl) ⟨681741, by rfl⟩ : syracuseStep 7271909 = 1363483) (by norm_num)
theorem B4847939 : Blo 2017435 4847939 := bstep (se 1 (by rfl) ⟨3635954, by rfl⟩ : syracuseStep 4847939 = 7271909) B7271909
theorem B3231959 : Blo 2017435 3231959 := bstep (se 1 (by rfl) ⟨2423969, by rfl⟩ : syracuseStep 3231959 = 4847939) B4847939
theorem B8618557 : Blo 2017435 8618557 := bstep (se 3 (by rfl) ⟨1615979, by rfl⟩ : syracuseStep 8618557 = 3231959) B3231959
theorem B11491409 : Blo 2017435 11491409 := bstep (se 2 (by rfl) ⟨4309278, by rfl⟩ : syracuseStep 11491409 = 8618557) B8618557
theorem B7660939 : Blo 2017435 7660939 := bstep (se 1 (by rfl) ⟨5745704, by rfl⟩ : syracuseStep 7660939 = 11491409) B11491409
theorem B10214585 : Blo 2017435 10214585 := bstep (se 2 (by rfl) ⟨3830469, by rfl⟩ : syracuseStep 10214585 = 7660939) B7660939
theorem B6809723 : Blo 2017435 6809723 := bstep (se 1 (by rfl) ⟨5107292, by rfl⟩ : syracuseStep 6809723 = 10214585) B10214585
theorem B4539815 : Blo 2017435 4539815 := bstep (se 1 (by rfl) ⟨3404861, by rfl⟩ : syracuseStep 4539815 = 6809723) B6809723
theorem B3026543 : Blo 2017435 3026543 := bstep (se 1 (by rfl) ⟨2269907, by rfl⟩ : syracuseStep 3026543 = 4539815) B4539815
theorem B2017695 : Blo 2017435 2017695 := bstep (se 1 (by rfl) ⟨1513271, by rfl⟩ : syracuseStep 2017695 = 3026543) B3026543
theorem B3026549 : Blo 2017435 3026549 := bbase (se 5 (by rfl) ⟨141869, by rfl⟩ : syracuseStep 3026549 = 283739) (by norm_num)
theorem B2017699 : Blo 2017435 2017699 := bstep (se 1 (by rfl) ⟨1513274, by rfl⟩ : syracuseStep 2017699 = 3026549) B3026549
theorem B3830485 : Blo 2017435 3830485 := bbase (se 7 (by rfl) ⟨44888, by rfl⟩ : syracuseStep 3830485 = 89777) (by norm_num)
theorem B5107313 : Blo 2017435 5107313 := bstep (se 2 (by rfl) ⟨1915242, by rfl⟩ : syracuseStep 5107313 = 3830485) B3830485
theorem B3404875 : Blo 2017435 3404875 := bstep (se 1 (by rfl) ⟨2553656, by rfl⟩ : syracuseStep 3404875 = 5107313) B5107313
theorem B4539833 : Blo 2017435 4539833 := bstep (se 2 (by rfl) ⟨1702437, by rfl⟩ : syracuseStep 4539833 = 3404875) B3404875
theorem B3026555 : Blo 2017435 3026555 := bstep (se 1 (by rfl) ⟨2269916, by rfl⟩ : syracuseStep 3026555 = 4539833) B4539833
theorem B2017703 : Blo 2017435 2017703 := bstep (se 1 (by rfl) ⟨1513277, by rfl⟩ : syracuseStep 2017703 = 3026555) B3026555
theorem B2269921 : Blo 2017435 2269921 := bbase (se 2 (by rfl) ⟨851220, by rfl⟩ : syracuseStep 2269921 = 1702441) (by norm_num)
theorem B3026561 : Blo 2017435 3026561 := bstep (se 2 (by rfl) ⟨1134960, by rfl⟩ : syracuseStep 3026561 = 2269921) B2269921
theorem B2017707 : Blo 2017435 2017707 := bstep (se 1 (by rfl) ⟨1513280, by rfl⟩ : syracuseStep 2017707 = 3026561) B3026561
theorem B5107333 : Blo 2017435 5107333 := bbase (se 4 (by rfl) ⟨478812, by rfl⟩ : syracuseStep 5107333 = 957625) (by norm_num)
theorem B6809777 : Blo 2017435 6809777 := bstep (se 2 (by rfl) ⟨2553666, by rfl⟩ : syracuseStep 6809777 = 5107333) B5107333
theorem B4539851 : Blo 2017435 4539851 := bstep (se 1 (by rfl) ⟨3404888, by rfl⟩ : syracuseStep 4539851 = 6809777) B6809777
theorem B3026567 : Blo 2017435 3026567 := bstep (se 1 (by rfl) ⟨2269925, by rfl⟩ : syracuseStep 3026567 = 4539851) B4539851
theorem B2017711 : Blo 2017435 2017711 := bstep (se 1 (by rfl) ⟨1513283, by rfl⟩ : syracuseStep 2017711 = 3026567) B3026567
theorem B3026573 : Blo 2017435 3026573 := bbase (se 3 (by rfl) ⟨567482, by rfl⟩ : syracuseStep 3026573 = 1134965) (by norm_num)
theorem B2017715 : Blo 2017435 2017715 := bstep (se 1 (by rfl) ⟨1513286, by rfl⟩ : syracuseStep 2017715 = 3026573) B3026573
theorem B4539869 : Blo 2017435 4539869 := bbase (se 3 (by rfl) ⟨851225, by rfl⟩ : syracuseStep 4539869 = 1702451) (by norm_num)
theorem B3026579 : Blo 2017435 3026579 := bstep (se 1 (by rfl) ⟨2269934, by rfl⟩ : syracuseStep 3026579 = 4539869) B4539869
theorem B2017719 : Blo 2017435 2017719 := bstep (se 1 (by rfl) ⟨1513289, by rfl⟩ : syracuseStep 2017719 = 3026579) B3026579
theorem B3404909 : Blo 2017435 3404909 := bbase (se 3 (by rfl) ⟨638420, by rfl⟩ : syracuseStep 3404909 = 1276841) (by norm_num)
theorem B2269939 : Blo 2017435 2269939 := bstep (se 1 (by rfl) ⟨1702454, by rfl⟩ : syracuseStep 2269939 = 3404909) B3404909
theorem B3026585 : Blo 2017435 3026585 := bstep (se 2 (by rfl) ⟨1134969, by rfl⟩ : syracuseStep 3026585 = 2269939) B2269939
theorem B2017723 : Blo 2017435 2017723 := bstep (se 1 (by rfl) ⟨1513292, by rfl⟩ : syracuseStep 2017723 = 3026585) B3026585
theorem B3067885 : Blo 2017435 3067885 := bbase (se 3 (by rfl) ⟨575228, by rfl⟩ : syracuseStep 3067885 = 1150457) (by norm_num)
theorem B16362053 : Blo 2017435 16362053 := bstep (se 4 (by rfl) ⟨1533942, by rfl⟩ : syracuseStep 16362053 = 3067885) B3067885
theorem B10908035 : Blo 2017435 10908035 := bstep (se 1 (by rfl) ⟨8181026, by rfl⟩ : syracuseStep 10908035 = 16362053) B16362053
theorem B7272023 : Blo 2017435 7272023 := bstep (se 1 (by rfl) ⟨5454017, by rfl⟩ : syracuseStep 7272023 = 10908035) B10908035
theorem B19392061 : Blo 2017435 19392061 := bstep (se 3 (by rfl) ⟨3636011, by rfl⟩ : syracuseStep 19392061 = 7272023) B7272023
theorem B25856081 : Blo 2017435 25856081 := bstep (se 2 (by rfl) ⟨9696030, by rfl⟩ : syracuseStep 25856081 = 19392061) B19392061
theorem B17237387 : Blo 2017435 17237387 := bstep (se 1 (by rfl) ⟨12928040, by rfl⟩ : syracuseStep 17237387 = 25856081) B25856081
theorem B11491591 : Blo 2017435 11491591 := bstep (se 1 (by rfl) ⟨8618693, by rfl⟩ : syracuseStep 11491591 = 17237387) B17237387
theorem B15322121 : Blo 2017435 15322121 := bstep (se 2 (by rfl) ⟨5745795, by rfl⟩ : syracuseStep 15322121 = 11491591) B11491591
theorem B10214747 : Blo 2017435 10214747 := bstep (se 1 (by rfl) ⟨7661060, by rfl⟩ : syracuseStep 10214747 = 15322121) B15322121
theorem B6809831 : Blo 2017435 6809831 := bstep (se 1 (by rfl) ⟨5107373, by rfl⟩ : syracuseStep 6809831 = 10214747) B10214747
theorem B4539887 : Blo 2017435 4539887 := bstep (se 1 (by rfl) ⟨3404915, by rfl⟩ : syracuseStep 4539887 = 6809831) B6809831
theorem B3026591 : Blo 2017435 3026591 := bstep (se 1 (by rfl) ⟨2269943, by rfl⟩ : syracuseStep 3026591 = 4539887) B4539887
theorem B2017727 : Blo 2017435 2017727 := bstep (se 1 (by rfl) ⟨1513295, by rfl⟩ : syracuseStep 2017727 = 3026591) B3026591
theorem B3026597 : Blo 2017435 3026597 := bbase (se 4 (by rfl) ⟨283743, by rfl⟩ : syracuseStep 3026597 = 567487) (by norm_num)
theorem B2017731 : Blo 2017435 2017731 := bstep (se 1 (by rfl) ⟨1513298, by rfl⟩ : syracuseStep 2017731 = 3026597) B3026597
theorem B2553697 : Blo 2017435 2553697 := bbase (se 2 (by rfl) ⟨957636, by rfl⟩ : syracuseStep 2553697 = 1915273) (by norm_num)
theorem B3404929 : Blo 2017435 3404929 := bstep (se 2 (by rfl) ⟨1276848, by rfl⟩ : syracuseStep 3404929 = 2553697) B2553697
theorem B4539905 : Blo 2017435 4539905 := bstep (se 2 (by rfl) ⟨1702464, by rfl⟩ : syracuseStep 4539905 = 3404929) B3404929
theorem B3026603 : Blo 2017435 3026603 := bstep (se 1 (by rfl) ⟨2269952, by rfl⟩ : syracuseStep 3026603 = 4539905) B4539905
theorem B2017735 : Blo 2017435 2017735 := bstep (se 1 (by rfl) ⟨1513301, by rfl⟩ : syracuseStep 2017735 = 3026603) B3026603
theorem B2269957 : Blo 2017435 2269957 := bbase (se 4 (by rfl) ⟨212808, by rfl⟩ : syracuseStep 2269957 = 425617) (by norm_num)
theorem B3026609 : Blo 2017435 3026609 := bstep (se 2 (by rfl) ⟨1134978, by rfl⟩ : syracuseStep 3026609 = 2269957) B2269957
theorem B2017739 : Blo 2017435 2017739 := bstep (se 1 (by rfl) ⟨1513304, by rfl⟩ : syracuseStep 2017739 = 3026609) B3026609
theorem B3232037 : Blo 2017435 3232037 := bbase (se 4 (by rfl) ⟨303003, by rfl⟩ : syracuseStep 3232037 = 606007) (by norm_num)
theorem B2154691 : Blo 2017435 2154691 := bstep (se 1 (by rfl) ⟨1616018, by rfl⟩ : syracuseStep 2154691 = 3232037) B3232037
theorem B2872921 : Blo 2017435 2872921 := bstep (se 2 (by rfl) ⟨1077345, by rfl⟩ : syracuseStep 2872921 = 2154691) B2154691
theorem B3830561 : Blo 2017435 3830561 := bstep (se 2 (by rfl) ⟨1436460, by rfl⟩ : syracuseStep 3830561 = 2872921) B2872921
theorem B2553707 : Blo 2017435 2553707 := bstep (se 1 (by rfl) ⟨1915280, by rfl⟩ : syracuseStep 2553707 = 3830561) B3830561
theorem B6809885 : Blo 2017435 6809885 := bstep (se 3 (by rfl) ⟨1276853, by rfl⟩ : syracuseStep 6809885 = 2553707) B2553707
theorem B4539923 : Blo 2017435 4539923 := bstep (se 1 (by rfl) ⟨3404942, by rfl⟩ : syracuseStep 4539923 = 6809885) B6809885
theorem B3026615 : Blo 2017435 3026615 := bstep (se 1 (by rfl) ⟨2269961, by rfl⟩ : syracuseStep 3026615 = 4539923) B4539923
theorem B2017743 : Blo 2017435 2017743 := bstep (se 1 (by rfl) ⟨1513307, by rfl⟩ : syracuseStep 2017743 = 3026615) B3026615
theorem B3026621 : Blo 2017435 3026621 := bbase (se 3 (by rfl) ⟨567491, by rfl⟩ : syracuseStep 3026621 = 1134983) (by norm_num)
theorem B2017747 : Blo 2017435 2017747 := bstep (se 1 (by rfl) ⟨1513310, by rfl⟩ : syracuseStep 2017747 = 3026621) B3026621
theorem B4539941 : Blo 2017435 4539941 := bbase (se 4 (by rfl) ⟨425619, by rfl⟩ : syracuseStep 4539941 = 851239) (by norm_num)
theorem B3026627 : Blo 2017435 3026627 := bstep (se 1 (by rfl) ⟨2269970, by rfl⟩ : syracuseStep 3026627 = 4539941) B4539941
theorem B2017751 : Blo 2017435 2017751 := bstep (se 1 (by rfl) ⟨1513313, by rfl⟩ : syracuseStep 2017751 = 3026627) B3026627
theorem B5107445 : Blo 2017435 5107445 := bbase (se 5 (by rfl) ⟨239411, by rfl⟩ : syracuseStep 5107445 = 478823) (by norm_num)
theorem B3404963 : Blo 2017435 3404963 := bstep (se 1 (by rfl) ⟨2553722, by rfl⟩ : syracuseStep 3404963 = 5107445) B5107445
theorem B2269975 : Blo 2017435 2269975 := bstep (se 1 (by rfl) ⟨1702481, by rfl⟩ : syracuseStep 2269975 = 3404963) B3404963
theorem B3026633 : Blo 2017435 3026633 := bstep (se 2 (by rfl) ⟨1134987, by rfl⟩ : syracuseStep 3026633 = 2269975) B2269975
theorem B2017755 : Blo 2017435 2017755 := bstep (se 1 (by rfl) ⟨1513316, by rfl⟩ : syracuseStep 2017755 = 3026633) B3026633
theorem B8181157 : Blo 2017435 8181157 := bbase (se 4 (by rfl) ⟨766983, by rfl⟩ : syracuseStep 8181157 = 1533967) (by norm_num)
theorem B10908209 : Blo 2017435 10908209 := bstep (se 2 (by rfl) ⟨4090578, by rfl⟩ : syracuseStep 10908209 = 8181157) B8181157
theorem B29088557 : Blo 2017435 29088557 := bstep (se 3 (by rfl) ⟨5454104, by rfl⟩ : syracuseStep 29088557 = 10908209) B10908209
theorem B19392371 : Blo 2017435 19392371 := bstep (se 1 (by rfl) ⟨14544278, by rfl⟩ : syracuseStep 19392371 = 29088557) B29088557
theorem B12928247 : Blo 2017435 12928247 := bstep (se 1 (by rfl) ⟨9696185, by rfl⟩ : syracuseStep 12928247 = 19392371) B19392371
theorem B8618831 : Blo 2017435 8618831 := bstep (se 1 (by rfl) ⟨6464123, by rfl⟩ : syracuseStep 8618831 = 12928247) B12928247
theorem B5745887 : Blo 2017435 5745887 := bstep (se 1 (by rfl) ⟨4309415, by rfl⟩ : syracuseStep 5745887 = 8618831) B8618831
theorem B3830591 : Blo 2017435 3830591 := bstep (se 1 (by rfl) ⟨2872943, by rfl⟩ : syracuseStep 3830591 = 5745887) B5745887
theorem B10214909 : Blo 2017435 10214909 := bstep (se 3 (by rfl) ⟨1915295, by rfl⟩ : syracuseStep 10214909 = 3830591) B3830591
theorem B6809939 : Blo 2017435 6809939 := bstep (se 1 (by rfl) ⟨5107454, by rfl⟩ : syracuseStep 6809939 = 10214909) B10214909
theorem B4539959 : Blo 2017435 4539959 := bstep (se 1 (by rfl) ⟨3404969, by rfl⟩ : syracuseStep 4539959 = 6809939) B6809939
theorem B3026639 : Blo 2017435 3026639 := bstep (se 1 (by rfl) ⟨2269979, by rfl⟩ : syracuseStep 3026639 = 4539959) B4539959
theorem B2017759 : Blo 2017435 2017759 := bstep (se 1 (by rfl) ⟨1513319, by rfl⟩ : syracuseStep 2017759 = 3026639) B3026639
theorem B3026645 : Blo 2017435 3026645 := bbase (se 7 (by rfl) ⟨35468, by rfl⟩ : syracuseStep 3026645 = 70937) (by norm_num)
theorem B2017763 : Blo 2017435 2017763 := bstep (se 1 (by rfl) ⟨1513322, by rfl⟩ : syracuseStep 2017763 = 3026645) B3026645
theorem B3636085 : Blo 2017435 3636085 := bbase (se 5 (by rfl) ⟨170441, by rfl⟩ : syracuseStep 3636085 = 340883) (by norm_num)
theorem B4848113 : Blo 2017435 4848113 := bstep (se 2 (by rfl) ⟨1818042, by rfl⟩ : syracuseStep 4848113 = 3636085) B3636085
theorem B3232075 : Blo 2017435 3232075 := bstep (se 1 (by rfl) ⟨2424056, by rfl⟩ : syracuseStep 3232075 = 4848113) B4848113
theorem B4309433 : Blo 2017435 4309433 := bstep (se 2 (by rfl) ⟨1616037, by rfl⟩ : syracuseStep 4309433 = 3232075) B3232075
theorem B2872955 : Blo 2017435 2872955 := bstep (se 1 (by rfl) ⟨2154716, by rfl⟩ : syracuseStep 2872955 = 4309433) B4309433
theorem B7661213 : Blo 2017435 7661213 := bstep (se 3 (by rfl) ⟨1436477, by rfl⟩ : syracuseStep 7661213 = 2872955) B2872955
theorem B5107475 : Blo 2017435 5107475 := bstep (se 1 (by rfl) ⟨3830606, by rfl⟩ : syracuseStep 5107475 = 7661213) B7661213
theorem B3404983 : Blo 2017435 3404983 := bstep (se 1 (by rfl) ⟨2553737, by rfl⟩ : syracuseStep 3404983 = 5107475) B5107475
theorem B4539977 : Blo 2017435 4539977 := bstep (se 2 (by rfl) ⟨1702491, by rfl⟩ : syracuseStep 4539977 = 3404983) B3404983
theorem B3026651 : Blo 2017435 3026651 := bstep (se 1 (by rfl) ⟨2269988, by rfl⟩ : syracuseStep 3026651 = 4539977) B4539977
theorem B2017767 : Blo 2017435 2017767 := bstep (se 1 (by rfl) ⟨1513325, by rfl⟩ : syracuseStep 2017767 = 3026651) B3026651
theorem B2269993 : Blo 2017435 2269993 := bbase (se 2 (by rfl) ⟨851247, by rfl⟩ : syracuseStep 2269993 = 1702495) (by norm_num)
theorem B3026657 : Blo 2017435 3026657 := bstep (se 2 (by rfl) ⟨1134996, by rfl⟩ : syracuseStep 3026657 = 2269993) B2269993
theorem B2017771 : Blo 2017435 2017771 := bstep (se 1 (by rfl) ⟨1513328, by rfl⟩ : syracuseStep 2017771 = 3026657) B3026657
theorem B7272197 : Blo 2017435 7272197 := bbase (se 4 (by rfl) ⟨681768, by rfl⟩ : syracuseStep 7272197 = 1363537) (by norm_num)
theorem B4848131 : Blo 2017435 4848131 := bstep (se 1 (by rfl) ⟨3636098, by rfl⟩ : syracuseStep 4848131 = 7272197) B7272197
theorem B12928349 : Blo 2017435 12928349 := bstep (se 3 (by rfl) ⟨2424065, by rfl⟩ : syracuseStep 12928349 = 4848131) B4848131
theorem B8618899 : Blo 2017435 8618899 := bstep (se 1 (by rfl) ⟨6464174, by rfl⟩ : syracuseStep 8618899 = 12928349) B12928349
theorem B11491865 : Blo 2017435 11491865 := bstep (se 2 (by rfl) ⟨4309449, by rfl⟩ : syracuseStep 11491865 = 8618899) B8618899
theorem B7661243 : Blo 2017435 7661243 := bstep (se 1 (by rfl) ⟨5745932, by rfl⟩ : syracuseStep 7661243 = 11491865) B11491865
theorem B5107495 : Blo 2017435 5107495 := bstep (se 1 (by rfl) ⟨3830621, by rfl⟩ : syracuseStep 5107495 = 7661243) B7661243
theorem B6809993 : Blo 2017435 6809993 := bstep (se 2 (by rfl) ⟨2553747, by rfl⟩ : syracuseStep 6809993 = 5107495) B5107495
theorem B4539995 : Blo 2017435 4539995 := bstep (se 1 (by rfl) ⟨3404996, by rfl⟩ : syracuseStep 4539995 = 6809993) B6809993
theorem B3026663 : Blo 2017435 3026663 := bstep (se 1 (by rfl) ⟨2269997, by rfl⟩ : syracuseStep 3026663 = 4539995) B4539995
theorem B2017775 : Blo 2017435 2017775 := bstep (se 1 (by rfl) ⟨1513331, by rfl⟩ : syracuseStep 2017775 = 3026663) B3026663
theorem B3026669 : Blo 2017435 3026669 := bbase (se 3 (by rfl) ⟨567500, by rfl⟩ : syracuseStep 3026669 = 1135001) (by norm_num)
theorem B2017779 : Blo 2017435 2017779 := bstep (se 1 (by rfl) ⟨1513334, by rfl⟩ : syracuseStep 2017779 = 3026669) B3026669
theorem B4540013 : Blo 2017435 4540013 := bbase (se 3 (by rfl) ⟨851252, by rfl⟩ : syracuseStep 4540013 = 1702505) (by norm_num)
theorem B3026675 : Blo 2017435 3026675 := bstep (se 1 (by rfl) ⟨2270006, by rfl⟩ : syracuseStep 3026675 = 4540013) B4540013
theorem B2017783 : Blo 2017435 2017783 := bstep (se 1 (by rfl) ⟨1513337, by rfl⟩ : syracuseStep 2017783 = 3026675) B3026675
theorem B3830645 : Blo 2017435 3830645 := bbase (se 5 (by rfl) ⟨179561, by rfl⟩ : syracuseStep 3830645 = 359123) (by norm_num)
theorem B2553763 : Blo 2017435 2553763 := bstep (se 1 (by rfl) ⟨1915322, by rfl⟩ : syracuseStep 2553763 = 3830645) B3830645
theorem B3405017 : Blo 2017435 3405017 := bstep (se 2 (by rfl) ⟨1276881, by rfl⟩ : syracuseStep 3405017 = 2553763) B2553763
theorem B2270011 : Blo 2017435 2270011 := bstep (se 1 (by rfl) ⟨1702508, by rfl⟩ : syracuseStep 2270011 = 3405017) B3405017
theorem B3026681 : Blo 2017435 3026681 := bstep (se 2 (by rfl) ⟨1135005, by rfl⟩ : syracuseStep 3026681 = 2270011) B2270011
theorem B2017787 : Blo 2017435 2017787 := bstep (se 1 (by rfl) ⟨1513340, by rfl⟩ : syracuseStep 2017787 = 3026681) B3026681
theorem B2457157 : Blo 2017435 2457157 := bbase (se 4 (by rfl) ⟨230358, by rfl⟩ : syracuseStep 2457157 = 460717) (by norm_num)
theorem B52419349 : Blo 2017435 52419349 := bstep (se 6 (by rfl) ⟨1228578, by rfl⟩ : syracuseStep 52419349 = 2457157) B2457157
theorem B69892465 : Blo 2017435 69892465 := bstep (se 2 (by rfl) ⟨26209674, by rfl⟩ : syracuseStep 69892465 = 52419349) B52419349
theorem B93189953 : Blo 2017435 93189953 := bstep (se 2 (by rfl) ⟨34946232, by rfl⟩ : syracuseStep 93189953 = 69892465) B69892465
theorem B248506541 : Blo 2017435 248506541 := bstep (se 3 (by rfl) ⟨46594976, by rfl⟩ : syracuseStep 248506541 = 93189953) B93189953
theorem B165671027 : Blo 2017435 165671027 := bstep (se 1 (by rfl) ⟨124253270, by rfl⟩ : syracuseStep 165671027 = 248506541) B248506541
theorem B110447351 : Blo 2017435 110447351 := bstep (se 1 (by rfl) ⟨82835513, by rfl⟩ : syracuseStep 110447351 = 165671027) B165671027
theorem B73631567 : Blo 2017435 73631567 := bstep (se 1 (by rfl) ⟨55223675, by rfl⟩ : syracuseStep 73631567 = 110447351) B110447351
theorem B49087711 : Blo 2017435 49087711 := bstep (se 1 (by rfl) ⟨36815783, by rfl⟩ : syracuseStep 49087711 = 73631567) B73631567
theorem B65450281 : Blo 2017435 65450281 := bstep (se 2 (by rfl) ⟨24543855, by rfl⟩ : syracuseStep 65450281 = 49087711) B49087711
theorem B87267041 : Blo 2017435 87267041 := bstep (se 2 (by rfl) ⟨32725140, by rfl⟩ : syracuseStep 87267041 = 65450281) B65450281
theorem B58178027 : Blo 2017435 58178027 := bstep (se 1 (by rfl) ⟨43633520, by rfl⟩ : syracuseStep 58178027 = 87267041) B87267041
theorem B38785351 : Blo 2017435 38785351 := bstep (se 1 (by rfl) ⟨29089013, by rfl⟩ : syracuseStep 38785351 = 58178027) B58178027
theorem B51713801 : Blo 2017435 51713801 := bstep (se 2 (by rfl) ⟨19392675, by rfl⟩ : syracuseStep 51713801 = 38785351) B38785351
theorem B34475867 : Blo 2017435 34475867 := bstep (se 1 (by rfl) ⟨25856900, by rfl⟩ : syracuseStep 34475867 = 51713801) B51713801
theorem B22983911 : Blo 2017435 22983911 := bstep (se 1 (by rfl) ⟨17237933, by rfl⟩ : syracuseStep 22983911 = 34475867) B34475867
theorem B15322607 : Blo 2017435 15322607 := bstep (se 1 (by rfl) ⟨11491955, by rfl⟩ : syracuseStep 15322607 = 22983911) B22983911
theorem B10215071 : Blo 2017435 10215071 := bstep (se 1 (by rfl) ⟨7661303, by rfl⟩ : syracuseStep 10215071 = 15322607) B15322607
theorem B6810047 : Blo 2017435 6810047 := bstep (se 1 (by rfl) ⟨5107535, by rfl⟩ : syracuseStep 6810047 = 10215071) B10215071
theorem B4540031 : Blo 2017435 4540031 := bstep (se 1 (by rfl) ⟨3405023, by rfl⟩ : syracuseStep 4540031 = 6810047) B6810047
theorem B3026687 : Blo 2017435 3026687 := bstep (se 1 (by rfl) ⟨2270015, by rfl⟩ : syracuseStep 3026687 = 4540031) B4540031
theorem B2017791 : Blo 2017435 2017791 := bstep (se 1 (by rfl) ⟨1513343, by rfl⟩ : syracuseStep 2017791 = 3026687) B3026687
theorem B3026693 : Blo 2017435 3026693 := bbase (se 4 (by rfl) ⟨283752, by rfl⟩ : syracuseStep 3026693 = 567505) (by norm_num)
theorem B2017795 : Blo 2017435 2017795 := bstep (se 1 (by rfl) ⟨1513346, by rfl⟩ : syracuseStep 2017795 = 3026693) B3026693
theorem B3405037 : Blo 2017435 3405037 := bbase (se 3 (by rfl) ⟨638444, by rfl⟩ : syracuseStep 3405037 = 1276889) (by norm_num)
theorem B4540049 : Blo 2017435 4540049 := bstep (se 2 (by rfl) ⟨1702518, by rfl⟩ : syracuseStep 4540049 = 3405037) B3405037
theorem B3026699 : Blo 2017435 3026699 := bstep (se 1 (by rfl) ⟨2270024, by rfl⟩ : syracuseStep 3026699 = 4540049) B4540049
theorem B2017799 : Blo 2017435 2017799 := bstep (se 1 (by rfl) ⟨1513349, by rfl⟩ : syracuseStep 2017799 = 3026699) B3026699
theorem B2270029 : Blo 2017435 2270029 := bbase (se 3 (by rfl) ⟨425630, by rfl⟩ : syracuseStep 2270029 = 851261) (by norm_num)
theorem B3026705 : Blo 2017435 3026705 := bstep (se 2 (by rfl) ⟨1135014, by rfl⟩ : syracuseStep 3026705 = 2270029) B2270029
theorem B2017803 : Blo 2017435 2017803 := bstep (se 1 (by rfl) ⟨1513352, by rfl⟩ : syracuseStep 2017803 = 3026705) B3026705
theorem B6810101 : Blo 2017435 6810101 := bbase (se 5 (by rfl) ⟨319223, by rfl⟩ : syracuseStep 6810101 = 638447) (by norm_num)
theorem B4540067 : Blo 2017435 4540067 := bstep (se 1 (by rfl) ⟨3405050, by rfl⟩ : syracuseStep 4540067 = 6810101) B6810101
theorem B3026711 : Blo 2017435 3026711 := bstep (se 1 (by rfl) ⟨2270033, by rfl⟩ : syracuseStep 3026711 = 4540067) B4540067
theorem B2017807 : Blo 2017435 2017807 := bstep (se 1 (by rfl) ⟨1513355, by rfl⟩ : syracuseStep 2017807 = 3026711) B3026711
theorem B3026717 : Blo 2017435 3026717 := bbase (se 3 (by rfl) ⟨567509, by rfl⟩ : syracuseStep 3026717 = 1135019) (by norm_num)
theorem B2017811 : Blo 2017435 2017811 := bstep (se 1 (by rfl) ⟨1513358, by rfl⟩ : syracuseStep 2017811 = 3026717) B3026717
theorem B4540085 : Blo 2017435 4540085 := bbase (se 5 (by rfl) ⟨212816, by rfl⟩ : syracuseStep 4540085 = 425633) (by norm_num)
theorem B3026723 : Blo 2017435 3026723 := bstep (se 1 (by rfl) ⟨2270042, by rfl⟩ : syracuseStep 3026723 = 4540085) B4540085
theorem B2017815 : Blo 2017435 2017815 := bstep (se 1 (by rfl) ⟨1513361, by rfl⟩ : syracuseStep 2017815 = 3026723) B3026723
theorem B11492117 : Blo 2017435 11492117 := bbase (se 6 (by rfl) ⟨269346, by rfl⟩ : syracuseStep 11492117 = 538693) (by norm_num)
theorem B7661411 : Blo 2017435 7661411 := bstep (se 1 (by rfl) ⟨5746058, by rfl⟩ : syracuseStep 7661411 = 11492117) B11492117
theorem B5107607 : Blo 2017435 5107607 := bstep (se 1 (by rfl) ⟨3830705, by rfl⟩ : syracuseStep 5107607 = 7661411) B7661411
theorem B3405071 : Blo 2017435 3405071 := bstep (se 1 (by rfl) ⟨2553803, by rfl⟩ : syracuseStep 3405071 = 5107607) B5107607
theorem B2270047 : Blo 2017435 2270047 := bstep (se 1 (by rfl) ⟨1702535, by rfl⟩ : syracuseStep 2270047 = 3405071) B3405071
theorem B3026729 : Blo 2017435 3026729 := bstep (se 2 (by rfl) ⟨1135023, by rfl⟩ : syracuseStep 3026729 = 2270047) B2270047
theorem B2017819 : Blo 2017435 2017819 := bstep (se 1 (by rfl) ⟨1513364, by rfl⟩ : syracuseStep 2017819 = 3026729) B3026729
theorem B5746069 : Blo 2017435 5746069 := bbase (se 6 (by rfl) ⟨134673, by rfl⟩ : syracuseStep 5746069 = 269347) (by norm_num)
theorem B7661425 : Blo 2017435 7661425 := bstep (se 2 (by rfl) ⟨2873034, by rfl⟩ : syracuseStep 7661425 = 5746069) B5746069
theorem B10215233 : Blo 2017435 10215233 := bstep (se 2 (by rfl) ⟨3830712, by rfl⟩ : syracuseStep 10215233 = 7661425) B7661425
theorem B6810155 : Blo 2017435 6810155 := bstep (se 1 (by rfl) ⟨5107616, by rfl⟩ : syracuseStep 6810155 = 10215233) B10215233
theorem B4540103 : Blo 2017435 4540103 := bstep (se 1 (by rfl) ⟨3405077, by rfl⟩ : syracuseStep 4540103 = 6810155) B6810155
theorem B3026735 : Blo 2017435 3026735 := bstep (se 1 (by rfl) ⟨2270051, by rfl⟩ : syracuseStep 3026735 = 4540103) B4540103
theorem B2017823 : Blo 2017435 2017823 := bstep (se 1 (by rfl) ⟨1513367, by rfl⟩ : syracuseStep 2017823 = 3026735) B3026735
theorem B3026741 : Blo 2017435 3026741 := bbase (se 5 (by rfl) ⟨141878, by rfl⟩ : syracuseStep 3026741 = 283757) (by norm_num)
theorem B2017827 : Blo 2017435 2017827 := bstep (se 1 (by rfl) ⟨1513370, by rfl⟩ : syracuseStep 2017827 = 3026741) B3026741
theorem B5107637 : Blo 2017435 5107637 := bbase (se 5 (by rfl) ⟨239420, by rfl⟩ : syracuseStep 5107637 = 478841) (by norm_num)
theorem B3405091 : Blo 2017435 3405091 := bstep (se 1 (by rfl) ⟨2553818, by rfl⟩ : syracuseStep 3405091 = 5107637) B5107637
theorem B4540121 : Blo 2017435 4540121 := bstep (se 2 (by rfl) ⟨1702545, by rfl⟩ : syracuseStep 4540121 = 3405091) B3405091
theorem B3026747 : Blo 2017435 3026747 := bstep (se 1 (by rfl) ⟨2270060, by rfl⟩ : syracuseStep 3026747 = 4540121) B4540121
theorem B2017831 : Blo 2017435 2017831 := bstep (se 1 (by rfl) ⟨1513373, by rfl⟩ : syracuseStep 2017831 = 3026747) B3026747
theorem B2270065 : Blo 2017435 2270065 := bbase (se 2 (by rfl) ⟨851274, by rfl⟩ : syracuseStep 2270065 = 1702549) (by norm_num)
theorem B3026753 : Blo 2017435 3026753 := bstep (se 2 (by rfl) ⟨1135032, by rfl⟩ : syracuseStep 3026753 = 2270065) B2270065
theorem B2017835 : Blo 2017435 2017835 := bstep (se 1 (by rfl) ⟨1513376, by rfl⟩ : syracuseStep 2017835 = 3026753) B3026753
theorem B8619173 : Blo 2017435 8619173 := bbase (se 4 (by rfl) ⟨808047, by rfl⟩ : syracuseStep 8619173 = 1616095) (by norm_num)
theorem B5746115 : Blo 2017435 5746115 := bstep (se 1 (by rfl) ⟨4309586, by rfl⟩ : syracuseStep 5746115 = 8619173) B8619173
theorem B3830743 : Blo 2017435 3830743 := bstep (se 1 (by rfl) ⟨2873057, by rfl⟩ : syracuseStep 3830743 = 5746115) B5746115
theorem B5107657 : Blo 2017435 5107657 := bstep (se 2 (by rfl) ⟨1915371, by rfl⟩ : syracuseStep 5107657 = 3830743) B3830743
theorem B6810209 : Blo 2017435 6810209 := bstep (se 2 (by rfl) ⟨2553828, by rfl⟩ : syracuseStep 6810209 = 5107657) B5107657
theorem B4540139 : Blo 2017435 4540139 := bstep (se 1 (by rfl) ⟨3405104, by rfl⟩ : syracuseStep 4540139 = 6810209) B6810209
theorem B3026759 : Blo 2017435 3026759 := bstep (se 1 (by rfl) ⟨2270069, by rfl⟩ : syracuseStep 3026759 = 4540139) B4540139
theorem B2017839 : Blo 2017435 2017839 := bstep (se 1 (by rfl) ⟨1513379, by rfl⟩ : syracuseStep 2017839 = 3026759) B3026759
theorem B3026765 : Blo 2017435 3026765 := bbase (se 3 (by rfl) ⟨567518, by rfl⟩ : syracuseStep 3026765 = 1135037) (by norm_num)
theorem B2017843 : Blo 2017435 2017843 := bstep (se 1 (by rfl) ⟨1513382, by rfl⟩ : syracuseStep 2017843 = 3026765) B3026765
theorem B4540157 : Blo 2017435 4540157 := bbase (se 3 (by rfl) ⟨851279, by rfl⟩ : syracuseStep 4540157 = 1702559) (by norm_num)
theorem B3026771 : Blo 2017435 3026771 := bstep (se 1 (by rfl) ⟨2270078, by rfl⟩ : syracuseStep 3026771 = 4540157) B4540157
theorem B2017847 : Blo 2017435 2017847 := bstep (se 1 (by rfl) ⟨1513385, by rfl⟩ : syracuseStep 2017847 = 3026771) B3026771
theorem B3405125 : Blo 2017435 3405125 := bbase (se 4 (by rfl) ⟨319230, by rfl⟩ : syracuseStep 3405125 = 638461) (by norm_num)
theorem B2270083 : Blo 2017435 2270083 := bstep (se 1 (by rfl) ⟨1702562, by rfl⟩ : syracuseStep 2270083 = 3405125) B3405125
theorem B3026777 : Blo 2017435 3026777 := bstep (se 2 (by rfl) ⟨1135041, by rfl⟩ : syracuseStep 3026777 = 2270083) B2270083
theorem B2017851 : Blo 2017435 2017851 := bstep (se 1 (by rfl) ⟨1513388, by rfl⟩ : syracuseStep 2017851 = 3026777) B3026777
theorem B15323093 : Blo 2017435 15323093 := bbase (se 7 (by rfl) ⟨179567, by rfl⟩ : syracuseStep 15323093 = 359135) (by norm_num)
theorem B10215395 : Blo 2017435 10215395 := bstep (se 1 (by rfl) ⟨7661546, by rfl⟩ : syracuseStep 10215395 = 15323093) B15323093
theorem B6810263 : Blo 2017435 6810263 := bstep (se 1 (by rfl) ⟨5107697, by rfl⟩ : syracuseStep 6810263 = 10215395) B10215395
theorem B4540175 : Blo 2017435 4540175 := bstep (se 1 (by rfl) ⟨3405131, by rfl⟩ : syracuseStep 4540175 = 6810263) B6810263
theorem B3026783 : Blo 2017435 3026783 := bstep (se 1 (by rfl) ⟨2270087, by rfl⟩ : syracuseStep 3026783 = 4540175) B4540175
theorem B2017855 : Blo 2017435 2017855 := bstep (se 1 (by rfl) ⟨1513391, by rfl⟩ : syracuseStep 2017855 = 3026783) B3026783
theorem B3026789 : Blo 2017435 3026789 := bbase (se 4 (by rfl) ⟨283761, by rfl⟩ : syracuseStep 3026789 = 567523) (by norm_num)
theorem B2017859 : Blo 2017435 2017859 := bstep (se 1 (by rfl) ⟨1513394, by rfl⟩ : syracuseStep 2017859 = 3026789) B3026789
theorem B3830789 : Blo 2017435 3830789 := bbase (se 4 (by rfl) ⟨359136, by rfl⟩ : syracuseStep 3830789 = 718273) (by norm_num)
theorem B2553859 : Blo 2017435 2553859 := bstep (se 1 (by rfl) ⟨1915394, by rfl⟩ : syracuseStep 2553859 = 3830789) B3830789
theorem B3405145 : Blo 2017435 3405145 := bstep (se 2 (by rfl) ⟨1276929, by rfl⟩ : syracuseStep 3405145 = 2553859) B2553859
theorem B4540193 : Blo 2017435 4540193 := bstep (se 2 (by rfl) ⟨1702572, by rfl⟩ : syracuseStep 4540193 = 3405145) B3405145
theorem B3026795 : Blo 2017435 3026795 := bstep (se 1 (by rfl) ⟨2270096, by rfl⟩ : syracuseStep 3026795 = 4540193) B4540193
theorem B2017863 : Blo 2017435 2017863 := bstep (se 1 (by rfl) ⟨1513397, by rfl⟩ : syracuseStep 2017863 = 3026795) B3026795
theorem B2270101 : Blo 2017435 2270101 := bbase (se 6 (by rfl) ⟨53205, by rfl⟩ : syracuseStep 2270101 = 106411) (by norm_num)
theorem B3026801 : Blo 2017435 3026801 := bstep (se 2 (by rfl) ⟨1135050, by rfl⟩ : syracuseStep 3026801 = 2270101) B2270101
theorem B2017867 : Blo 2017435 2017867 := bstep (se 1 (by rfl) ⟨1513400, by rfl⟩ : syracuseStep 2017867 = 3026801) B3026801
theorem B2553869 : Blo 2017435 2553869 := bbase (se 3 (by rfl) ⟨478850, by rfl⟩ : syracuseStep 2553869 = 957701) (by norm_num)
theorem B6810317 : Blo 2017435 6810317 := bstep (se 3 (by rfl) ⟨1276934, by rfl⟩ : syracuseStep 6810317 = 2553869) B2553869
theorem B4540211 : Blo 2017435 4540211 := bstep (se 1 (by rfl) ⟨3405158, by rfl⟩ : syracuseStep 4540211 = 6810317) B6810317
theorem B3026807 : Blo 2017435 3026807 := bstep (se 1 (by rfl) ⟨2270105, by rfl⟩ : syracuseStep 3026807 = 4540211) B4540211
theorem B2017871 : Blo 2017435 2017871 := bstep (se 1 (by rfl) ⟨1513403, by rfl⟩ : syracuseStep 2017871 = 3026807) B3026807
theorem B3026813 : Blo 2017435 3026813 := bbase (se 3 (by rfl) ⟨567527, by rfl⟩ : syracuseStep 3026813 = 1135055) (by norm_num)
theorem B2017875 : Blo 2017435 2017875 := bstep (se 1 (by rfl) ⟨1513406, by rfl⟩ : syracuseStep 2017875 = 3026813) B3026813
theorem B4540229 : Blo 2017435 4540229 := bbase (se 4 (by rfl) ⟨425646, by rfl⟩ : syracuseStep 4540229 = 851293) (by norm_num)
theorem B3026819 : Blo 2017435 3026819 := bstep (se 1 (by rfl) ⟨2270114, by rfl⟩ : syracuseStep 3026819 = 4540229) B4540229
theorem B2017879 : Blo 2017435 2017879 := bstep (se 1 (by rfl) ⟨1513409, by rfl⟩ : syracuseStep 2017879 = 3026819) B3026819
theorem B3232261 : Blo 2017435 3232261 := bbase (se 4 (by rfl) ⟨303024, by rfl⟩ : syracuseStep 3232261 = 606049) (by norm_num)
theorem B4309681 : Blo 2017435 4309681 := bstep (se 2 (by rfl) ⟨1616130, by rfl⟩ : syracuseStep 4309681 = 3232261) B3232261
theorem B5746241 : Blo 2017435 5746241 := bstep (se 2 (by rfl) ⟨2154840, by rfl⟩ : syracuseStep 5746241 = 4309681) B4309681
theorem B3830827 : Blo 2017435 3830827 := bstep (se 1 (by rfl) ⟨2873120, by rfl⟩ : syracuseStep 3830827 = 5746241) B5746241
theorem B5107769 : Blo 2017435 5107769 := bstep (se 2 (by rfl) ⟨1915413, by rfl⟩ : syracuseStep 5107769 = 3830827) B3830827
theorem B3405179 : Blo 2017435 3405179 := bstep (se 1 (by rfl) ⟨2553884, by rfl⟩ : syracuseStep 3405179 = 5107769) B5107769
theorem B2270119 : Blo 2017435 2270119 := bstep (se 1 (by rfl) ⟨1702589, by rfl⟩ : syracuseStep 2270119 = 3405179) B3405179
theorem B3026825 : Blo 2017435 3026825 := bstep (se 2 (by rfl) ⟨1135059, by rfl⟩ : syracuseStep 3026825 = 2270119) B2270119
theorem B2017883 : Blo 2017435 2017883 := bstep (se 1 (by rfl) ⟨1513412, by rfl⟩ : syracuseStep 2017883 = 3026825) B3026825
theorem B10215557 : Blo 2017435 10215557 := bbase (se 4 (by rfl) ⟨957708, by rfl⟩ : syracuseStep 10215557 = 1915417) (by norm_num)
theorem B6810371 : Blo 2017435 6810371 := bstep (se 1 (by rfl) ⟨5107778, by rfl⟩ : syracuseStep 6810371 = 10215557) B10215557
theorem B4540247 : Blo 2017435 4540247 := bstep (se 1 (by rfl) ⟨3405185, by rfl⟩ : syracuseStep 4540247 = 6810371) B6810371
theorem B3026831 : Blo 2017435 3026831 := bstep (se 1 (by rfl) ⟨2270123, by rfl⟩ : syracuseStep 3026831 = 4540247) B4540247
theorem B2017887 : Blo 2017435 2017887 := bstep (se 1 (by rfl) ⟨1513415, by rfl⟩ : syracuseStep 2017887 = 3026831) B3026831
theorem B3026837 : Blo 2017435 3026837 := bbase (se 6 (by rfl) ⟨70941, by rfl⟩ : syracuseStep 3026837 = 141883) (by norm_num)
theorem B2017891 : Blo 2017435 2017891 := bstep (se 1 (by rfl) ⟨1513418, by rfl⟩ : syracuseStep 2017891 = 3026837) B3026837
theorem B2154853 : Blo 2017435 2154853 := bbase (se 4 (by rfl) ⟨202017, by rfl⟩ : syracuseStep 2154853 = 404035) (by norm_num)
theorem B11492549 : Blo 2017435 11492549 := bstep (se 4 (by rfl) ⟨1077426, by rfl⟩ : syracuseStep 11492549 = 2154853) B2154853
theorem B7661699 : Blo 2017435 7661699 := bstep (se 1 (by rfl) ⟨5746274, by rfl⟩ : syracuseStep 7661699 = 11492549) B11492549
theorem B5107799 : Blo 2017435 5107799 := bstep (se 1 (by rfl) ⟨3830849, by rfl⟩ : syracuseStep 5107799 = 7661699) B7661699
theorem B3405199 : Blo 2017435 3405199 := bstep (se 1 (by rfl) ⟨2553899, by rfl⟩ : syracuseStep 3405199 = 5107799) B5107799
theorem B4540265 : Blo 2017435 4540265 := bstep (se 2 (by rfl) ⟨1702599, by rfl⟩ : syracuseStep 4540265 = 3405199) B3405199
theorem B3026843 : Blo 2017435 3026843 := bstep (se 1 (by rfl) ⟨2270132, by rfl⟩ : syracuseStep 3026843 = 4540265) B4540265
theorem B2017895 : Blo 2017435 2017895 := bstep (se 1 (by rfl) ⟨1513421, by rfl⟩ : syracuseStep 2017895 = 3026843) B3026843
theorem B2270137 : Blo 2017435 2270137 := bbase (se 2 (by rfl) ⟨851301, by rfl⟩ : syracuseStep 2270137 = 1702603) (by norm_num)
theorem B3026849 : Blo 2017435 3026849 := bstep (se 2 (by rfl) ⟨1135068, by rfl⟩ : syracuseStep 3026849 = 2270137) B2270137
theorem B2017899 : Blo 2017435 2017899 := bstep (se 1 (by rfl) ⟨1513424, by rfl⟩ : syracuseStep 2017899 = 3026849) B3026849
theorem B3883133 : Blo 2017435 3883133 := bbase (se 3 (by rfl) ⟨728087, by rfl⟩ : syracuseStep 3883133 = 1456175) (by norm_num)
theorem B2588755 : Blo 2017435 2588755 := bstep (se 1 (by rfl) ⟨1941566, by rfl⟩ : syracuseStep 2588755 = 3883133) B3883133
theorem B3451673 : Blo 2017435 3451673 := bstep (se 2 (by rfl) ⟨1294377, by rfl⟩ : syracuseStep 3451673 = 2588755) B2588755
theorem B9204461 : Blo 2017435 9204461 := bstep (se 3 (by rfl) ⟨1725836, by rfl⟩ : syracuseStep 9204461 = 3451673) B3451673
theorem B6136307 : Blo 2017435 6136307 := bstep (se 1 (by rfl) ⟨4602230, by rfl⟩ : syracuseStep 6136307 = 9204461) B9204461
theorem B4090871 : Blo 2017435 4090871 := bstep (se 1 (by rfl) ⟨3068153, by rfl⟩ : syracuseStep 4090871 = 6136307) B6136307
theorem B10908989 : Blo 2017435 10908989 := bstep (se 3 (by rfl) ⟨2045435, by rfl⟩ : syracuseStep 10908989 = 4090871) B4090871
theorem B7272659 : Blo 2017435 7272659 := bstep (se 1 (by rfl) ⟨5454494, by rfl⟩ : syracuseStep 7272659 = 10908989) B10908989
theorem B4848439 : Blo 2017435 4848439 := bstep (se 1 (by rfl) ⟨3636329, by rfl⟩ : syracuseStep 4848439 = 7272659) B7272659
theorem B6464585 : Blo 2017435 6464585 := bstep (se 2 (by rfl) ⟨2424219, by rfl⟩ : syracuseStep 6464585 = 4848439) B4848439
theorem B4309723 : Blo 2017435 4309723 := bstep (se 1 (by rfl) ⟨3232292, by rfl⟩ : syracuseStep 4309723 = 6464585) B6464585
theorem B5746297 : Blo 2017435 5746297 := bstep (se 2 (by rfl) ⟨2154861, by rfl⟩ : syracuseStep 5746297 = 4309723) B4309723
theorem B7661729 : Blo 2017435 7661729 := bstep (se 2 (by rfl) ⟨2873148, by rfl⟩ : syracuseStep 7661729 = 5746297) B5746297
theorem B5107819 : Blo 2017435 5107819 := bstep (se 1 (by rfl) ⟨3830864, by rfl⟩ : syracuseStep 5107819 = 7661729) B7661729
theorem B6810425 : Blo 2017435 6810425 := bstep (se 2 (by rfl) ⟨2553909, by rfl⟩ : syracuseStep 6810425 = 5107819) B5107819
theorem B4540283 : Blo 2017435 4540283 := bstep (se 1 (by rfl) ⟨3405212, by rfl⟩ : syracuseStep 4540283 = 6810425) B6810425
theorem B3026855 : Blo 2017435 3026855 := bstep (se 1 (by rfl) ⟨2270141, by rfl⟩ : syracuseStep 3026855 = 4540283) B4540283
theorem B2017903 : Blo 2017435 2017903 := bstep (se 1 (by rfl) ⟨1513427, by rfl⟩ : syracuseStep 2017903 = 3026855) B3026855
theorem B3026861 : Blo 2017435 3026861 := bbase (se 3 (by rfl) ⟨567536, by rfl⟩ : syracuseStep 3026861 = 1135073) (by norm_num)
theorem B2017907 : Blo 2017435 2017907 := bstep (se 1 (by rfl) ⟨1513430, by rfl⟩ : syracuseStep 2017907 = 3026861) B3026861
theorem B4540301 : Blo 2017435 4540301 := bbase (se 3 (by rfl) ⟨851306, by rfl⟩ : syracuseStep 4540301 = 1702613) (by norm_num)
theorem B3026867 : Blo 2017435 3026867 := bstep (se 1 (by rfl) ⟨2270150, by rfl⟩ : syracuseStep 3026867 = 4540301) B4540301
theorem B2017911 : Blo 2017435 2017911 := bstep (se 1 (by rfl) ⟨1513433, by rfl⟩ : syracuseStep 2017911 = 3026867) B3026867
theorem B2553925 : Blo 2017435 2553925 := bbase (se 4 (by rfl) ⟨239430, by rfl⟩ : syracuseStep 2553925 = 478861) (by norm_num)
theorem B3405233 : Blo 2017435 3405233 := bstep (se 2 (by rfl) ⟨1276962, by rfl⟩ : syracuseStep 3405233 = 2553925) B2553925
theorem B2270155 : Blo 2017435 2270155 := bstep (se 1 (by rfl) ⟨1702616, by rfl⟩ : syracuseStep 2270155 = 3405233) B3405233
theorem B3026873 : Blo 2017435 3026873 := bstep (se 2 (by rfl) ⟨1135077, by rfl⟩ : syracuseStep 3026873 = 2270155) B2270155
theorem B2017915 : Blo 2017435 2017915 := bstep (se 1 (by rfl) ⟨1513436, by rfl⟩ : syracuseStep 2017915 = 3026873) B3026873
theorem B2301133 : Blo 2017435 2301133 := bbase (se 3 (by rfl) ⟨431462, by rfl⟩ : syracuseStep 2301133 = 862925) (by norm_num)
theorem B3068177 : Blo 2017435 3068177 := bstep (se 2 (by rfl) ⟨1150566, by rfl⟩ : syracuseStep 3068177 = 2301133) B2301133
theorem B8181805 : Blo 2017435 8181805 := bstep (se 3 (by rfl) ⟨1534088, by rfl⟩ : syracuseStep 8181805 = 3068177) B3068177
theorem B10909073 : Blo 2017435 10909073 := bstep (se 2 (by rfl) ⟨4090902, by rfl⟩ : syracuseStep 10909073 = 8181805) B8181805
theorem B7272715 : Blo 2017435 7272715 := bstep (se 1 (by rfl) ⟨5454536, by rfl⟩ : syracuseStep 7272715 = 10909073) B10909073
theorem B9696953 : Blo 2017435 9696953 := bstep (se 2 (by rfl) ⟨3636357, by rfl⟩ : syracuseStep 9696953 = 7272715) B7272715
theorem B25858541 : Blo 2017435 25858541 := bstep (se 3 (by rfl) ⟨4848476, by rfl⟩ : syracuseStep 25858541 = 9696953) B9696953
theorem B17239027 : Blo 2017435 17239027 := bstep (se 1 (by rfl) ⟨12929270, by rfl⟩ : syracuseStep 17239027 = 25858541) B25858541
theorem B22985369 : Blo 2017435 22985369 := bstep (se 2 (by rfl) ⟨8619513, by rfl⟩ : syracuseStep 22985369 = 17239027) B17239027
theorem B15323579 : Blo 2017435 15323579 := bstep (se 1 (by rfl) ⟨11492684, by rfl⟩ : syracuseStep 15323579 = 22985369) B22985369
theorem B10215719 : Blo 2017435 10215719 := bstep (se 1 (by rfl) ⟨7661789, by rfl⟩ : syracuseStep 10215719 = 15323579) B15323579
theorem B6810479 : Blo 2017435 6810479 := bstep (se 1 (by rfl) ⟨5107859, by rfl⟩ : syracuseStep 6810479 = 10215719) B10215719
theorem B4540319 : Blo 2017435 4540319 := bstep (se 1 (by rfl) ⟨3405239, by rfl⟩ : syracuseStep 4540319 = 6810479) B6810479
theorem B3026879 : Blo 2017435 3026879 := bstep (se 1 (by rfl) ⟨2270159, by rfl⟩ : syracuseStep 3026879 = 4540319) B4540319
theorem B2017919 : Blo 2017435 2017919 := bstep (se 1 (by rfl) ⟨1513439, by rfl⟩ : syracuseStep 2017919 = 3026879) B3026879
theorem B3026885 : Blo 2017435 3026885 := bbase (se 4 (by rfl) ⟨283770, by rfl⟩ : syracuseStep 3026885 = 567541) (by norm_num)
theorem B2017923 : Blo 2017435 2017923 := bstep (se 1 (by rfl) ⟨1513442, by rfl⟩ : syracuseStep 2017923 = 3026885) B3026885
theorem B3405253 : Blo 2017435 3405253 := bbase (se 4 (by rfl) ⟨319242, by rfl⟩ : syracuseStep 3405253 = 638485) (by norm_num)
theorem B4540337 : Blo 2017435 4540337 := bstep (se 2 (by rfl) ⟨1702626, by rfl⟩ : syracuseStep 4540337 = 3405253) B3405253
theorem B3026891 : Blo 2017435 3026891 := bstep (se 1 (by rfl) ⟨2270168, by rfl⟩ : syracuseStep 3026891 = 4540337) B4540337
theorem B2017927 : Blo 2017435 2017927 := bstep (se 1 (by rfl) ⟨1513445, by rfl⟩ : syracuseStep 2017927 = 3026891) B3026891
theorem B2270173 : Blo 2017435 2270173 := bbase (se 3 (by rfl) ⟨425657, by rfl⟩ : syracuseStep 2270173 = 851315) (by norm_num)
theorem B3026897 : Blo 2017435 3026897 := bstep (se 2 (by rfl) ⟨1135086, by rfl⟩ : syracuseStep 3026897 = 2270173) B2270173
theorem B2017931 : Blo 2017435 2017931 := bstep (se 1 (by rfl) ⟨1513448, by rfl⟩ : syracuseStep 2017931 = 3026897) B3026897
theorem B6810533 : Blo 2017435 6810533 := bbase (se 4 (by rfl) ⟨638487, by rfl⟩ : syracuseStep 6810533 = 1276975) (by norm_num)
theorem B4540355 : Blo 2017435 4540355 := bstep (se 1 (by rfl) ⟨3405266, by rfl⟩ : syracuseStep 4540355 = 6810533) B6810533
theorem B3026903 : Blo 2017435 3026903 := bstep (se 1 (by rfl) ⟨2270177, by rfl⟩ : syracuseStep 3026903 = 4540355) B4540355
theorem B2017935 : Blo 2017435 2017935 := bstep (se 1 (by rfl) ⟨1513451, by rfl⟩ : syracuseStep 2017935 = 3026903) B3026903
theorem B3026909 : Blo 2017435 3026909 := bbase (se 3 (by rfl) ⟨567545, by rfl⟩ : syracuseStep 3026909 = 1135091) (by norm_num)
theorem B2017939 : Blo 2017435 2017939 := bstep (se 1 (by rfl) ⟨1513454, by rfl⟩ : syracuseStep 2017939 = 3026909) B3026909
theorem B4540373 : Blo 2017435 4540373 := bbase (se 7 (by rfl) ⟨53207, by rfl⟩ : syracuseStep 4540373 = 106415) (by norm_num)
theorem B3026915 : Blo 2017435 3026915 := bstep (se 1 (by rfl) ⟨2270186, by rfl⟩ : syracuseStep 3026915 = 4540373) B4540373
theorem B2017943 : Blo 2017435 2017943 := bstep (se 1 (by rfl) ⟨1513457, by rfl⟩ : syracuseStep 2017943 = 3026915) B3026915
theorem B3068221 : Blo 2017435 3068221 := bbase (se 3 (by rfl) ⟨575291, by rfl⟩ : syracuseStep 3068221 = 1150583) (by norm_num)
theorem B4090961 : Blo 2017435 4090961 := bstep (se 2 (by rfl) ⟨1534110, by rfl⟩ : syracuseStep 4090961 = 3068221) B3068221
theorem B2727307 : Blo 2017435 2727307 := bstep (se 1 (by rfl) ⟨2045480, by rfl⟩ : syracuseStep 2727307 = 4090961) B4090961
theorem B3636409 : Blo 2017435 3636409 := bstep (se 2 (by rfl) ⟨1363653, by rfl⟩ : syracuseStep 3636409 = 2727307) B2727307
theorem B4848545 : Blo 2017435 4848545 := bstep (se 2 (by rfl) ⟨1818204, by rfl⟩ : syracuseStep 4848545 = 3636409) B3636409
theorem B12929453 : Blo 2017435 12929453 := bstep (se 3 (by rfl) ⟨2424272, by rfl⟩ : syracuseStep 12929453 = 4848545) B4848545
theorem B8619635 : Blo 2017435 8619635 := bstep (se 1 (by rfl) ⟨6464726, by rfl⟩ : syracuseStep 8619635 = 12929453) B12929453
theorem B5746423 : Blo 2017435 5746423 := bstep (se 1 (by rfl) ⟨4309817, by rfl⟩ : syracuseStep 5746423 = 8619635) B8619635
theorem B7661897 : Blo 2017435 7661897 := bstep (se 2 (by rfl) ⟨2873211, by rfl⟩ : syracuseStep 7661897 = 5746423) B5746423
theorem B5107931 : Blo 2017435 5107931 := bstep (se 1 (by rfl) ⟨3830948, by rfl⟩ : syracuseStep 5107931 = 7661897) B7661897
theorem B3405287 : Blo 2017435 3405287 := bstep (se 1 (by rfl) ⟨2553965, by rfl⟩ : syracuseStep 3405287 = 5107931) B5107931
theorem B2270191 : Blo 2017435 2270191 := bstep (se 1 (by rfl) ⟨1702643, by rfl⟩ : syracuseStep 2270191 = 3405287) B3405287
theorem B3026921 : Blo 2017435 3026921 := bstep (se 2 (by rfl) ⟨1135095, by rfl⟩ : syracuseStep 3026921 = 2270191) B2270191
theorem B2017947 : Blo 2017435 2017947 := bstep (se 1 (by rfl) ⟨1513460, by rfl⟩ : syracuseStep 2017947 = 3026921) B3026921
theorem B2424277 : Blo 2017435 2424277 := bbase (se 7 (by rfl) ⟨28409, by rfl⟩ : syracuseStep 2424277 = 56819) (by norm_num)
theorem B3232369 : Blo 2017435 3232369 := bstep (se 2 (by rfl) ⟨1212138, by rfl⟩ : syracuseStep 3232369 = 2424277) B2424277
theorem B17239301 : Blo 2017435 17239301 := bstep (se 4 (by rfl) ⟨1616184, by rfl⟩ : syracuseStep 17239301 = 3232369) B3232369
theorem B11492867 : Blo 2017435 11492867 := bstep (se 1 (by rfl) ⟨8619650, by rfl⟩ : syracuseStep 11492867 = 17239301) B17239301
theorem B7661911 : Blo 2017435 7661911 := bstep (se 1 (by rfl) ⟨5746433, by rfl⟩ : syracuseStep 7661911 = 11492867) B11492867
theorem B10215881 : Blo 2017435 10215881 := bstep (se 2 (by rfl) ⟨3830955, by rfl⟩ : syracuseStep 10215881 = 7661911) B7661911
theorem B6810587 : Blo 2017435 6810587 := bstep (se 1 (by rfl) ⟨5107940, by rfl⟩ : syracuseStep 6810587 = 10215881) B10215881
theorem B4540391 : Blo 2017435 4540391 := bstep (se 1 (by rfl) ⟨3405293, by rfl⟩ : syracuseStep 4540391 = 6810587) B6810587
theorem B3026927 : Blo 2017435 3026927 := bstep (se 1 (by rfl) ⟨2270195, by rfl⟩ : syracuseStep 3026927 = 4540391) B4540391
theorem B2017951 : Blo 2017435 2017951 := bstep (se 1 (by rfl) ⟨1513463, by rfl⟩ : syracuseStep 2017951 = 3026927) B3026927
theorem B3026933 : Blo 2017435 3026933 := bbase (se 5 (by rfl) ⟨141887, by rfl⟩ : syracuseStep 3026933 = 283775) (by norm_num)
theorem B2017955 : Blo 2017435 2017955 := bstep (se 1 (by rfl) ⟨1513466, by rfl⟩ : syracuseStep 2017955 = 3026933) B3026933
theorem B2332577 : Blo 2017435 2332577 := bbase (se 2 (by rfl) ⟨874716, by rfl⟩ : syracuseStep 2332577 = 1749433) (by norm_num)
theorem B6220205 : Blo 2017435 6220205 := bstep (se 3 (by rfl) ⟨1166288, by rfl⟩ : syracuseStep 6220205 = 2332577) B2332577
theorem B4146803 : Blo 2017435 4146803 := bstep (se 1 (by rfl) ⟨3110102, by rfl⟩ : syracuseStep 4146803 = 6220205) B6220205
theorem B2764535 : Blo 2017435 2764535 := bstep (se 1 (by rfl) ⟨2073401, by rfl⟩ : syracuseStep 2764535 = 4146803) B4146803
theorem B7372093 : Blo 2017435 7372093 := bstep (se 3 (by rfl) ⟨1382267, by rfl⟩ : syracuseStep 7372093 = 2764535) B2764535
theorem B9829457 : Blo 2017435 9829457 := bstep (se 2 (by rfl) ⟨3686046, by rfl⟩ : syracuseStep 9829457 = 7372093) B7372093
theorem B6552971 : Blo 2017435 6552971 := bstep (se 1 (by rfl) ⟨4914728, by rfl⟩ : syracuseStep 6552971 = 9829457) B9829457
theorem B4368647 : Blo 2017435 4368647 := bstep (se 1 (by rfl) ⟨3276485, by rfl⟩ : syracuseStep 4368647 = 6552971) B6552971
theorem B2912431 : Blo 2017435 2912431 := bstep (se 1 (by rfl) ⟨2184323, by rfl⟩ : syracuseStep 2912431 = 4368647) B4368647
theorem B3883241 : Blo 2017435 3883241 := bstep (se 2 (by rfl) ⟨1456215, by rfl⟩ : syracuseStep 3883241 = 2912431) B2912431
theorem B10355309 : Blo 2017435 10355309 := bstep (se 3 (by rfl) ⟨1941620, by rfl⟩ : syracuseStep 10355309 = 3883241) B3883241
theorem B6903539 : Blo 2017435 6903539 := bstep (se 1 (by rfl) ⟨5177654, by rfl⟩ : syracuseStep 6903539 = 10355309) B10355309
theorem B4602359 : Blo 2017435 4602359 := bstep (se 1 (by rfl) ⟨3451769, by rfl⟩ : syracuseStep 4602359 = 6903539) B6903539
theorem B12272957 : Blo 2017435 12272957 := bstep (se 3 (by rfl) ⟨2301179, by rfl⟩ : syracuseStep 12272957 = 4602359) B4602359
theorem B8181971 : Blo 2017435 8181971 := bstep (se 1 (by rfl) ⟨6136478, by rfl⟩ : syracuseStep 8181971 = 12272957) B12272957
theorem B5454647 : Blo 2017435 5454647 := bstep (se 1 (by rfl) ⟨4090985, by rfl⟩ : syracuseStep 5454647 = 8181971) B8181971
theorem B3636431 : Blo 2017435 3636431 := bstep (se 1 (by rfl) ⟨2727323, by rfl⟩ : syracuseStep 3636431 = 5454647) B5454647
theorem B2424287 : Blo 2017435 2424287 := bstep (se 1 (by rfl) ⟨1818215, by rfl⟩ : syracuseStep 2424287 = 3636431) B3636431
theorem B6464765 : Blo 2017435 6464765 := bstep (se 3 (by rfl) ⟨1212143, by rfl⟩ : syracuseStep 6464765 = 2424287) B2424287
theorem B4309843 : Blo 2017435 4309843 := bstep (se 1 (by rfl) ⟨3232382, by rfl⟩ : syracuseStep 4309843 = 6464765) B6464765
theorem B5746457 : Blo 2017435 5746457 := bstep (se 2 (by rfl) ⟨2154921, by rfl⟩ : syracuseStep 5746457 = 4309843) B4309843
theorem B3830971 : Blo 2017435 3830971 := bstep (se 1 (by rfl) ⟨2873228, by rfl⟩ : syracuseStep 3830971 = 5746457) B5746457
theorem B5107961 : Blo 2017435 5107961 := bstep (se 2 (by rfl) ⟨1915485, by rfl⟩ : syracuseStep 5107961 = 3830971) B3830971
theorem B3405307 : Blo 2017435 3405307 := bstep (se 1 (by rfl) ⟨2553980, by rfl⟩ : syracuseStep 3405307 = 5107961) B5107961
theorem B4540409 : Blo 2017435 4540409 := bstep (se 2 (by rfl) ⟨1702653, by rfl⟩ : syracuseStep 4540409 = 3405307) B3405307
theorem B3026939 : Blo 2017435 3026939 := bstep (se 1 (by rfl) ⟨2270204, by rfl⟩ : syracuseStep 3026939 = 4540409) B4540409
theorem B2017959 : Blo 2017435 2017959 := bstep (se 1 (by rfl) ⟨1513469, by rfl⟩ : syracuseStep 2017959 = 3026939) B3026939
theorem B2270209 : Blo 2017435 2270209 := bbase (se 2 (by rfl) ⟨851328, by rfl⟩ : syracuseStep 2270209 = 1702657) (by norm_num)
theorem B3026945 : Blo 2017435 3026945 := bstep (se 2 (by rfl) ⟨1135104, by rfl⟩ : syracuseStep 3026945 = 2270209) B2270209
theorem B2017963 : Blo 2017435 2017963 := bstep (se 1 (by rfl) ⟨1513472, by rfl⟩ : syracuseStep 2017963 = 3026945) B3026945
theorem B5107981 : Blo 2017435 5107981 := bbase (se 3 (by rfl) ⟨957746, by rfl⟩ : syracuseStep 5107981 = 1915493) (by norm_num)
theorem B6810641 : Blo 2017435 6810641 := bstep (se 2 (by rfl) ⟨2553990, by rfl⟩ : syracuseStep 6810641 = 5107981) B5107981
theorem B4540427 : Blo 2017435 4540427 := bstep (se 1 (by rfl) ⟨3405320, by rfl⟩ : syracuseStep 4540427 = 6810641) B6810641
theorem B3026951 : Blo 2017435 3026951 := bstep (se 1 (by rfl) ⟨2270213, by rfl⟩ : syracuseStep 3026951 = 4540427) B4540427
theorem B2017967 : Blo 2017435 2017967 := bstep (se 1 (by rfl) ⟨1513475, by rfl⟩ : syracuseStep 2017967 = 3026951) B3026951
theorem B3026957 : Blo 2017435 3026957 := bbase (se 3 (by rfl) ⟨567554, by rfl⟩ : syracuseStep 3026957 = 1135109) (by norm_num)
theorem B2017971 : Blo 2017435 2017971 := bstep (se 1 (by rfl) ⟨1513478, by rfl⟩ : syracuseStep 2017971 = 3026957) B3026957
theorem B4540445 : Blo 2017435 4540445 := bbase (se 3 (by rfl) ⟨851333, by rfl⟩ : syracuseStep 4540445 = 1702667) (by norm_num)
theorem B3026963 : Blo 2017435 3026963 := bstep (se 1 (by rfl) ⟨2270222, by rfl⟩ : syracuseStep 3026963 = 4540445) B4540445
theorem B2017975 : Blo 2017435 2017975 := bstep (se 1 (by rfl) ⟨1513481, by rfl⟩ : syracuseStep 2017975 = 3026963) B3026963
theorem B3405341 : Blo 2017435 3405341 := bbase (se 3 (by rfl) ⟨638501, by rfl⟩ : syracuseStep 3405341 = 1277003) (by norm_num)
theorem B2270227 : Blo 2017435 2270227 := bstep (se 1 (by rfl) ⟨1702670, by rfl⟩ : syracuseStep 2270227 = 3405341) B3405341
theorem B3026969 : Blo 2017435 3026969 := bstep (se 2 (by rfl) ⟨1135113, by rfl⟩ : syracuseStep 3026969 = 2270227) B2270227
theorem B2017979 : Blo 2017435 2017979 := bstep (se 1 (by rfl) ⟨1513484, by rfl⟩ : syracuseStep 2017979 = 3026969) B3026969
theorem B4602413 : Blo 2017435 4602413 := bbase (se 3 (by rfl) ⟨862952, by rfl⟩ : syracuseStep 4602413 = 1725905) (by norm_num)
theorem B3068275 : Blo 2017435 3068275 := bstep (se 1 (by rfl) ⟨2301206, by rfl⟩ : syracuseStep 3068275 = 4602413) B4602413
theorem B4091033 : Blo 2017435 4091033 := bstep (se 2 (by rfl) ⟨1534137, by rfl⟩ : syracuseStep 4091033 = 3068275) B3068275
theorem B2727355 : Blo 2017435 2727355 := bstep (se 1 (by rfl) ⟨2045516, by rfl⟩ : syracuseStep 2727355 = 4091033) B4091033
theorem B3636473 : Blo 2017435 3636473 := bstep (se 2 (by rfl) ⟨1363677, by rfl⟩ : syracuseStep 3636473 = 2727355) B2727355
theorem B9697261 : Blo 2017435 9697261 := bstep (se 3 (by rfl) ⟨1818236, by rfl⟩ : syracuseStep 9697261 = 3636473) B3636473
theorem B12929681 : Blo 2017435 12929681 := bstep (se 2 (by rfl) ⟨4848630, by rfl⟩ : syracuseStep 12929681 = 9697261) B9697261
theorem B8619787 : Blo 2017435 8619787 := bstep (se 1 (by rfl) ⟨6464840, by rfl⟩ : syracuseStep 8619787 = 12929681) B12929681
theorem B11493049 : Blo 2017435 11493049 := bstep (se 2 (by rfl) ⟨4309893, by rfl⟩ : syracuseStep 11493049 = 8619787) B8619787
theorem B15324065 : Blo 2017435 15324065 := bstep (se 2 (by rfl) ⟨5746524, by rfl⟩ : syracuseStep 15324065 = 11493049) B11493049
theorem B10216043 : Blo 2017435 10216043 := bstep (se 1 (by rfl) ⟨7662032, by rfl⟩ : syracuseStep 10216043 = 15324065) B15324065
theorem B6810695 : Blo 2017435 6810695 := bstep (se 1 (by rfl) ⟨5108021, by rfl⟩ : syracuseStep 6810695 = 10216043) B10216043
theorem B4540463 : Blo 2017435 4540463 := bstep (se 1 (by rfl) ⟨3405347, by rfl⟩ : syracuseStep 4540463 = 6810695) B6810695
theorem B3026975 : Blo 2017435 3026975 := bstep (se 1 (by rfl) ⟨2270231, by rfl⟩ : syracuseStep 3026975 = 4540463) B4540463
theorem B2017983 : Blo 2017435 2017983 := bstep (se 1 (by rfl) ⟨1513487, by rfl⟩ : syracuseStep 2017983 = 3026975) B3026975
theorem B3026981 : Blo 2017435 3026981 := bbase (se 4 (by rfl) ⟨283779, by rfl⟩ : syracuseStep 3026981 = 567559) (by norm_num)
theorem B2017987 : Blo 2017435 2017987 := bstep (se 1 (by rfl) ⟨1513490, by rfl⟩ : syracuseStep 2017987 = 3026981) B3026981
theorem B2554021 : Blo 2017435 2554021 := bbase (se 4 (by rfl) ⟨239439, by rfl⟩ : syracuseStep 2554021 = 478879) (by norm_num)
theorem B3405361 : Blo 2017435 3405361 := bstep (se 2 (by rfl) ⟨1277010, by rfl⟩ : syracuseStep 3405361 = 2554021) B2554021
theorem B4540481 : Blo 2017435 4540481 := bstep (se 2 (by rfl) ⟨1702680, by rfl⟩ : syracuseStep 4540481 = 3405361) B3405361
theorem B3026987 : Blo 2017435 3026987 := bstep (se 1 (by rfl) ⟨2270240, by rfl⟩ : syracuseStep 3026987 = 4540481) B4540481
theorem B2017991 : Blo 2017435 2017991 := bstep (se 1 (by rfl) ⟨1513493, by rfl⟩ : syracuseStep 2017991 = 3026987) B3026987
theorem B2270245 : Blo 2017435 2270245 := bbase (se 4 (by rfl) ⟨212835, by rfl⟩ : syracuseStep 2270245 = 425671) (by norm_num)
theorem B3026993 : Blo 2017435 3026993 := bstep (se 2 (by rfl) ⟨1135122, by rfl⟩ : syracuseStep 3026993 = 2270245) B2270245
theorem B2017995 : Blo 2017435 2017995 := bstep (se 1 (by rfl) ⟨1513496, by rfl⟩ : syracuseStep 2017995 = 3026993) B3026993
theorem B8182133 : Blo 2017435 8182133 := bbase (se 5 (by rfl) ⟨383537, by rfl⟩ : syracuseStep 8182133 = 767075) (by norm_num)
theorem B5454755 : Blo 2017435 5454755 := bstep (se 1 (by rfl) ⟨4091066, by rfl⟩ : syracuseStep 5454755 = 8182133) B8182133
theorem B3636503 : Blo 2017435 3636503 := bstep (se 1 (by rfl) ⟨2727377, by rfl⟩ : syracuseStep 3636503 = 5454755) B5454755
theorem B2424335 : Blo 2017435 2424335 := bstep (se 1 (by rfl) ⟨1818251, by rfl⟩ : syracuseStep 2424335 = 3636503) B3636503
theorem B6464893 : Blo 2017435 6464893 := bstep (se 3 (by rfl) ⟨1212167, by rfl⟩ : syracuseStep 6464893 = 2424335) B2424335
theorem B8619857 : Blo 2017435 8619857 := bstep (se 2 (by rfl) ⟨3232446, by rfl⟩ : syracuseStep 8619857 = 6464893) B6464893
theorem B5746571 : Blo 2017435 5746571 := bstep (se 1 (by rfl) ⟨4309928, by rfl⟩ : syracuseStep 5746571 = 8619857) B8619857
theorem B3831047 : Blo 2017435 3831047 := bstep (se 1 (by rfl) ⟨2873285, by rfl⟩ : syracuseStep 3831047 = 5746571) B5746571
theorem B2554031 : Blo 2017435 2554031 := bstep (se 1 (by rfl) ⟨1915523, by rfl⟩ : syracuseStep 2554031 = 3831047) B3831047
theorem B6810749 : Blo 2017435 6810749 := bstep (se 3 (by rfl) ⟨1277015, by rfl⟩ : syracuseStep 6810749 = 2554031) B2554031
theorem B4540499 : Blo 2017435 4540499 := bstep (se 1 (by rfl) ⟨3405374, by rfl⟩ : syracuseStep 4540499 = 6810749) B6810749
theorem B3026999 : Blo 2017435 3026999 := bstep (se 1 (by rfl) ⟨2270249, by rfl⟩ : syracuseStep 3026999 = 4540499) B4540499
theorem B2017999 : Blo 2017435 2017999 := bstep (se 1 (by rfl) ⟨1513499, by rfl⟩ : syracuseStep 2017999 = 3026999) B3026999
theorem B3027005 : Blo 2017435 3027005 := bbase (se 3 (by rfl) ⟨567563, by rfl⟩ : syracuseStep 3027005 = 1135127) (by norm_num)
theorem B2018003 : Blo 2017435 2018003 := bstep (se 1 (by rfl) ⟨1513502, by rfl⟩ : syracuseStep 2018003 = 3027005) B3027005
theorem B4540517 : Blo 2017435 4540517 := bbase (se 4 (by rfl) ⟨425673, by rfl⟩ : syracuseStep 4540517 = 851347) (by norm_num)
theorem B3027011 : Blo 2017435 3027011 := bstep (se 1 (by rfl) ⟨2270258, by rfl⟩ : syracuseStep 3027011 = 4540517) B4540517
theorem B2018007 : Blo 2017435 2018007 := bstep (se 1 (by rfl) ⟨1513505, by rfl⟩ : syracuseStep 2018007 = 3027011) B3027011
theorem B5108093 : Blo 2017435 5108093 := bbase (se 3 (by rfl) ⟨957767, by rfl⟩ : syracuseStep 5108093 = 1915535) (by norm_num)
theorem B3405395 : Blo 2017435 3405395 := bstep (se 1 (by rfl) ⟨2554046, by rfl⟩ : syracuseStep 3405395 = 5108093) B5108093
theorem B2270263 : Blo 2017435 2270263 := bstep (se 1 (by rfl) ⟨1702697, by rfl⟩ : syracuseStep 2270263 = 3405395) B3405395
theorem B3027017 : Blo 2017435 3027017 := bstep (se 2 (by rfl) ⟨1135131, by rfl⟩ : syracuseStep 3027017 = 2270263) B2270263
theorem B2018011 : Blo 2017435 2018011 := bstep (se 1 (by rfl) ⟨1513508, by rfl⟩ : syracuseStep 2018011 = 3027017) B3027017
theorem B3831077 : Blo 2017435 3831077 := bbase (se 4 (by rfl) ⟨359163, by rfl⟩ : syracuseStep 3831077 = 718327) (by norm_num)
theorem B10216205 : Blo 2017435 10216205 := bstep (se 3 (by rfl) ⟨1915538, by rfl⟩ : syracuseStep 10216205 = 3831077) B3831077
theorem B6810803 : Blo 2017435 6810803 := bstep (se 1 (by rfl) ⟨5108102, by rfl⟩ : syracuseStep 6810803 = 10216205) B10216205
theorem B4540535 : Blo 2017435 4540535 := bstep (se 1 (by rfl) ⟨3405401, by rfl⟩ : syracuseStep 4540535 = 6810803) B6810803
theorem B3027023 : Blo 2017435 3027023 := bstep (se 1 (by rfl) ⟨2270267, by rfl⟩ : syracuseStep 3027023 = 4540535) B4540535
theorem B2018015 : Blo 2017435 2018015 := bstep (se 1 (by rfl) ⟨1513511, by rfl⟩ : syracuseStep 2018015 = 3027023) B3027023
theorem B3027029 : Blo 2017435 3027029 := bbase (se 8 (by rfl) ⟨17736, by rfl⟩ : syracuseStep 3027029 = 35473) (by norm_num)
theorem B2018019 : Blo 2017435 2018019 := bstep (se 1 (by rfl) ⟨1513514, by rfl⟩ : syracuseStep 2018019 = 3027029) B3027029
theorem B2045557 : Blo 2017435 2045557 := bbase (se 5 (by rfl) ⟨95885, by rfl⟩ : syracuseStep 2045557 = 191771) (by norm_num)
theorem B10909637 : Blo 2017435 10909637 := bstep (se 4 (by rfl) ⟨1022778, by rfl⟩ : syracuseStep 10909637 = 2045557) B2045557
theorem B7273091 : Blo 2017435 7273091 := bstep (se 1 (by rfl) ⟨5454818, by rfl⟩ : syracuseStep 7273091 = 10909637) B10909637
theorem B19394909 : Blo 2017435 19394909 := bstep (se 3 (by rfl) ⟨3636545, by rfl⟩ : syracuseStep 19394909 = 7273091) B7273091
theorem B12929939 : Blo 2017435 12929939 := bstep (se 1 (by rfl) ⟨9697454, by rfl⟩ : syracuseStep 12929939 = 19394909) B19394909
theorem B8619959 : Blo 2017435 8619959 := bstep (se 1 (by rfl) ⟨6464969, by rfl⟩ : syracuseStep 8619959 = 12929939) B12929939
theorem B5746639 : Blo 2017435 5746639 := bstep (se 1 (by rfl) ⟨4309979, by rfl⟩ : syracuseStep 5746639 = 8619959) B8619959
theorem B7662185 : Blo 2017435 7662185 := bstep (se 2 (by rfl) ⟨2873319, by rfl⟩ : syracuseStep 7662185 = 5746639) B5746639
theorem B5108123 : Blo 2017435 5108123 := bstep (se 1 (by rfl) ⟨3831092, by rfl⟩ : syracuseStep 5108123 = 7662185) B7662185
theorem B3405415 : Blo 2017435 3405415 := bstep (se 1 (by rfl) ⟨2554061, by rfl⟩ : syracuseStep 3405415 = 5108123) B5108123
theorem B4540553 : Blo 2017435 4540553 := bstep (se 2 (by rfl) ⟨1702707, by rfl⟩ : syracuseStep 4540553 = 3405415) B3405415
theorem B3027035 : Blo 2017435 3027035 := bstep (se 1 (by rfl) ⟨2270276, by rfl⟩ : syracuseStep 3027035 = 4540553) B4540553
theorem B2018023 : Blo 2017435 2018023 := bstep (se 1 (by rfl) ⟨1513517, by rfl⟩ : syracuseStep 2018023 = 3027035) B3027035
theorem B2270281 : Blo 2017435 2270281 := bbase (se 2 (by rfl) ⟨851355, by rfl⟩ : syracuseStep 2270281 = 1702711) (by norm_num)
theorem B3027041 : Blo 2017435 3027041 := bstep (se 2 (by rfl) ⟨1135140, by rfl⟩ : syracuseStep 3027041 = 2270281) B2270281
theorem B2018027 : Blo 2017435 2018027 := bstep (se 1 (by rfl) ⟨1513520, by rfl⟩ : syracuseStep 2018027 = 3027041) B3027041
theorem B2424373 : Blo 2017435 2424373 := bbase (se 5 (by rfl) ⟨113642, by rfl⟩ : syracuseStep 2424373 = 227285) (by norm_num)
theorem B12929989 : Blo 2017435 12929989 := bstep (se 4 (by rfl) ⟨1212186, by rfl⟩ : syracuseStep 12929989 = 2424373) B2424373
theorem B17239985 : Blo 2017435 17239985 := bstep (se 2 (by rfl) ⟨6464994, by rfl⟩ : syracuseStep 17239985 = 12929989) B12929989
theorem B11493323 : Blo 2017435 11493323 := bstep (se 1 (by rfl) ⟨8619992, by rfl⟩ : syracuseStep 11493323 = 17239985) B17239985
theorem B7662215 : Blo 2017435 7662215 := bstep (se 1 (by rfl) ⟨5746661, by rfl⟩ : syracuseStep 7662215 = 11493323) B11493323
theorem B5108143 : Blo 2017435 5108143 := bstep (se 1 (by rfl) ⟨3831107, by rfl⟩ : syracuseStep 5108143 = 7662215) B7662215
theorem B6810857 : Blo 2017435 6810857 := bstep (se 2 (by rfl) ⟨2554071, by rfl⟩ : syracuseStep 6810857 = 5108143) B5108143
theorem B4540571 : Blo 2017435 4540571 := bstep (se 1 (by rfl) ⟨3405428, by rfl⟩ : syracuseStep 4540571 = 6810857) B6810857
theorem B3027047 : Blo 2017435 3027047 := bstep (se 1 (by rfl) ⟨2270285, by rfl⟩ : syracuseStep 3027047 = 4540571) B4540571
theorem B2018031 : Blo 2017435 2018031 := bstep (se 1 (by rfl) ⟨1513523, by rfl⟩ : syracuseStep 2018031 = 3027047) B3027047
theorem B3027053 : Blo 2017435 3027053 := bbase (se 3 (by rfl) ⟨567572, by rfl⟩ : syracuseStep 3027053 = 1135145) (by norm_num)
theorem B2018035 : Blo 2017435 2018035 := bstep (se 1 (by rfl) ⟨1513526, by rfl⟩ : syracuseStep 2018035 = 3027053) B3027053
theorem B4540589 : Blo 2017435 4540589 := bbase (se 3 (by rfl) ⟨851360, by rfl⟩ : syracuseStep 4540589 = 1702721) (by norm_num)
theorem B3027059 : Blo 2017435 3027059 := bstep (se 1 (by rfl) ⟨2270294, by rfl⟩ : syracuseStep 3027059 = 4540589) B4540589
theorem B2018039 : Blo 2017435 2018039 := bstep (se 1 (by rfl) ⟨1513529, by rfl⟩ : syracuseStep 2018039 = 3027059) B3027059
theorem B2727437 : Blo 2017435 2727437 := bbase (se 3 (by rfl) ⟨511394, by rfl⟩ : syracuseStep 2727437 = 1022789) (by norm_num)
theorem B7273165 : Blo 2017435 7273165 := bstep (se 3 (by rfl) ⟨1363718, by rfl⟩ : syracuseStep 7273165 = 2727437) B2727437
theorem B9697553 : Blo 2017435 9697553 := bstep (se 2 (by rfl) ⟨3636582, by rfl⟩ : syracuseStep 9697553 = 7273165) B7273165
theorem B6465035 : Blo 2017435 6465035 := bstep (se 1 (by rfl) ⟨4848776, by rfl⟩ : syracuseStep 6465035 = 9697553) B9697553
theorem B4310023 : Blo 2017435 4310023 := bstep (se 1 (by rfl) ⟨3232517, by rfl⟩ : syracuseStep 4310023 = 6465035) B6465035
theorem B5746697 : Blo 2017435 5746697 := bstep (se 2 (by rfl) ⟨2155011, by rfl⟩ : syracuseStep 5746697 = 4310023) B4310023
theorem B3831131 : Blo 2017435 3831131 := bstep (se 1 (by rfl) ⟨2873348, by rfl⟩ : syracuseStep 3831131 = 5746697) B5746697
theorem B2554087 : Blo 2017435 2554087 := bstep (se 1 (by rfl) ⟨1915565, by rfl⟩ : syracuseStep 2554087 = 3831131) B3831131
theorem B3405449 : Blo 2017435 3405449 := bstep (se 2 (by rfl) ⟨1277043, by rfl⟩ : syracuseStep 3405449 = 2554087) B2554087
theorem B2270299 : Blo 2017435 2270299 := bstep (se 1 (by rfl) ⟨1702724, by rfl⟩ : syracuseStep 2270299 = 3405449) B3405449
theorem B3027065 : Blo 2017435 3027065 := bstep (se 2 (by rfl) ⟨1135149, by rfl⟩ : syracuseStep 3027065 = 2270299) B2270299
theorem B2018043 : Blo 2017435 2018043 := bstep (se 1 (by rfl) ⟨1513532, by rfl⟩ : syracuseStep 2018043 = 3027065) B3027065
theorem B25860181 : Blo 2017435 25860181 := bbase (se 8 (by rfl) ⟨151524, by rfl⟩ : syracuseStep 25860181 = 303049) (by norm_num)
theorem B34480241 : Blo 2017435 34480241 := bstep (se 2 (by rfl) ⟨12930090, by rfl⟩ : syracuseStep 34480241 = 25860181) B25860181
theorem B22986827 : Blo 2017435 22986827 := bstep (se 1 (by rfl) ⟨17240120, by rfl⟩ : syracuseStep 22986827 = 34480241) B34480241
theorem B15324551 : Blo 2017435 15324551 := bstep (se 1 (by rfl) ⟨11493413, by rfl⟩ : syracuseStep 15324551 = 22986827) B22986827
theorem B10216367 : Blo 2017435 10216367 := bstep (se 1 (by rfl) ⟨7662275, by rfl⟩ : syracuseStep 10216367 = 15324551) B15324551
theorem B6810911 : Blo 2017435 6810911 := bstep (se 1 (by rfl) ⟨5108183, by rfl⟩ : syracuseStep 6810911 = 10216367) B10216367
theorem B4540607 : Blo 2017435 4540607 := bstep (se 1 (by rfl) ⟨3405455, by rfl⟩ : syracuseStep 4540607 = 6810911) B6810911
theorem B3027071 : Blo 2017435 3027071 := bstep (se 1 (by rfl) ⟨2270303, by rfl⟩ : syracuseStep 3027071 = 4540607) B4540607
theorem B2018047 : Blo 2017435 2018047 := bstep (se 1 (by rfl) ⟨1513535, by rfl⟩ : syracuseStep 2018047 = 3027071) B3027071
theorem B3027077 : Blo 2017435 3027077 := bbase (se 4 (by rfl) ⟨283788, by rfl⟩ : syracuseStep 3027077 = 567577) (by norm_num)
theorem B2018051 : Blo 2017435 2018051 := bstep (se 1 (by rfl) ⟨1513538, by rfl⟩ : syracuseStep 2018051 = 3027077) B3027077
theorem B3405469 : Blo 2017435 3405469 := bbase (se 3 (by rfl) ⟨638525, by rfl⟩ : syracuseStep 3405469 = 1277051) (by norm_num)
theorem B4540625 : Blo 2017435 4540625 := bstep (se 2 (by rfl) ⟨1702734, by rfl⟩ : syracuseStep 4540625 = 3405469) B3405469
theorem B3027083 : Blo 2017435 3027083 := bstep (se 1 (by rfl) ⟨2270312, by rfl⟩ : syracuseStep 3027083 = 4540625) B4540625
theorem B2018055 : Blo 2017435 2018055 := bstep (se 1 (by rfl) ⟨1513541, by rfl⟩ : syracuseStep 2018055 = 3027083) B3027083
theorem B2270317 : Blo 2017435 2270317 := bbase (se 3 (by rfl) ⟨425684, by rfl⟩ : syracuseStep 2270317 = 851369) (by norm_num)
theorem B3027089 : Blo 2017435 3027089 := bstep (se 2 (by rfl) ⟨1135158, by rfl⟩ : syracuseStep 3027089 = 2270317) B2270317
theorem B2018059 : Blo 2017435 2018059 := bstep (se 1 (by rfl) ⟨1513544, by rfl⟩ : syracuseStep 2018059 = 3027089) B3027089
theorem B6810965 : Blo 2017435 6810965 := bbase (se 11 (by rfl) ⟨4988, by rfl⟩ : syracuseStep 6810965 = 9977) (by norm_num)
theorem B4540643 : Blo 2017435 4540643 := bstep (se 1 (by rfl) ⟨3405482, by rfl⟩ : syracuseStep 4540643 = 6810965) B6810965
theorem B3027095 : Blo 2017435 3027095 := bstep (se 1 (by rfl) ⟨2270321, by rfl⟩ : syracuseStep 3027095 = 4540643) B4540643
theorem B2018063 : Blo 2017435 2018063 := bstep (se 1 (by rfl) ⟨1513547, by rfl⟩ : syracuseStep 2018063 = 3027095) B3027095
theorem B3027101 : Blo 2017435 3027101 := bbase (se 3 (by rfl) ⟨567581, by rfl⟩ : syracuseStep 3027101 = 1135163) (by norm_num)
theorem B2018067 : Blo 2017435 2018067 := bstep (se 1 (by rfl) ⟨1513550, by rfl⟩ : syracuseStep 2018067 = 3027101) B3027101
theorem B4540661 : Blo 2017435 4540661 := bbase (se 5 (by rfl) ⟨212843, by rfl⟩ : syracuseStep 4540661 = 425687) (by norm_num)
theorem B3027107 : Blo 2017435 3027107 := bstep (se 1 (by rfl) ⟨2270330, by rfl⟩ : syracuseStep 3027107 = 4540661) B4540661
theorem B2018071 : Blo 2017435 2018071 := bstep (se 1 (by rfl) ⟨1513553, by rfl⟩ : syracuseStep 2018071 = 3027107) B3027107
theorem B18238709 : Blo 2017435 18238709 := bbase (se 5 (by rfl) ⟨854939, by rfl⟩ : syracuseStep 18238709 = 1709879) (by norm_num)
theorem B48636557 : Blo 2017435 48636557 := bstep (se 3 (by rfl) ⟨9119354, by rfl⟩ : syracuseStep 48636557 = 18238709) B18238709
theorem B32424371 : Blo 2017435 32424371 := bstep (se 1 (by rfl) ⟨24318278, by rfl⟩ : syracuseStep 32424371 = 48636557) B48636557
theorem B21616247 : Blo 2017435 21616247 := bstep (se 1 (by rfl) ⟨16212185, by rfl⟩ : syracuseStep 21616247 = 32424371) B32424371
theorem B57643325 : Blo 2017435 57643325 := bstep (se 3 (by rfl) ⟨10808123, by rfl⟩ : syracuseStep 57643325 = 21616247) B21616247
theorem B38428883 : Blo 2017435 38428883 := bstep (se 1 (by rfl) ⟨28821662, by rfl⟩ : syracuseStep 38428883 = 57643325) B57643325
theorem B25619255 : Blo 2017435 25619255 := bstep (se 1 (by rfl) ⟨19214441, by rfl⟩ : syracuseStep 25619255 = 38428883) B38428883
theorem B17079503 : Blo 2017435 17079503 := bstep (se 1 (by rfl) ⟨12809627, by rfl⟩ : syracuseStep 17079503 = 25619255) B25619255
theorem B45545341 : Blo 2017435 45545341 := bstep (se 3 (by rfl) ⟨8539751, by rfl⟩ : syracuseStep 45545341 = 17079503) B17079503
theorem B60727121 : Blo 2017435 60727121 := bstep (se 2 (by rfl) ⟨22772670, by rfl⟩ : syracuseStep 60727121 = 45545341) B45545341
theorem B40484747 : Blo 2017435 40484747 := bstep (se 1 (by rfl) ⟨30363560, by rfl⟩ : syracuseStep 40484747 = 60727121) B60727121
theorem B107959325 : Blo 2017435 107959325 := bstep (se 3 (by rfl) ⟨20242373, by rfl⟩ : syracuseStep 107959325 = 40484747) B40484747
theorem B287891533 : Blo 2017435 287891533 := bstep (se 3 (by rfl) ⟨53979662, by rfl⟩ : syracuseStep 287891533 = 107959325) B107959325
theorem B383855377 : Blo 2017435 383855377 := bstep (se 2 (by rfl) ⟨143945766, by rfl⟩ : syracuseStep 383855377 = 287891533) B287891533
theorem B511807169 : Blo 2017435 511807169 := bstep (se 2 (by rfl) ⟨191927688, by rfl⟩ : syracuseStep 511807169 = 383855377) B383855377
theorem B341204779 : Blo 2017435 341204779 := bstep (se 1 (by rfl) ⟨255903584, by rfl⟩ : syracuseStep 341204779 = 511807169) B511807169
theorem B454939705 : Blo 2017435 454939705 := bstep (se 2 (by rfl) ⟨170602389, by rfl⟩ : syracuseStep 454939705 = 341204779) B341204779
theorem B2426345093 : Blo 2017435 2426345093 := bstep (se 4 (by rfl) ⟨227469852, by rfl⟩ : syracuseStep 2426345093 = 454939705) B454939705
theorem B1617563395 : Blo 2017435 1617563395 := bstep (se 1 (by rfl) ⟨1213172546, by rfl⟩ : syracuseStep 1617563395 = 2426345093) B2426345093
theorem B2156751193 : Blo 2017435 2156751193 := bstep (se 2 (by rfl) ⟨808781697, by rfl⟩ : syracuseStep 2156751193 = 1617563395) B1617563395
theorem B2875668257 : Blo 2017435 2875668257 := bstep (se 2 (by rfl) ⟨1078375596, by rfl⟩ : syracuseStep 2875668257 = 2156751193) B2156751193
theorem B1917112171 : Blo 2017435 1917112171 := bstep (se 1 (by rfl) ⟨1437834128, by rfl⟩ : syracuseStep 1917112171 = 2875668257) B2875668257
theorem B2556149561 : Blo 2017435 2556149561 := bstep (se 2 (by rfl) ⟨958556085, by rfl⟩ : syracuseStep 2556149561 = 1917112171) B1917112171
theorem B1704099707 : Blo 2017435 1704099707 := bstep (se 1 (by rfl) ⟨1278074780, by rfl⟩ : syracuseStep 1704099707 = 2556149561) B2556149561
theorem B1136066471 : Blo 2017435 1136066471 := bstep (se 1 (by rfl) ⟨852049853, by rfl⟩ : syracuseStep 1136066471 = 1704099707) B1704099707
theorem B757377647 : Blo 2017435 757377647 := bstep (se 1 (by rfl) ⟨568033235, by rfl⟩ : syracuseStep 757377647 = 1136066471) B1136066471
theorem B504918431 : Blo 2017435 504918431 := bstep (se 1 (by rfl) ⟨378688823, by rfl⟩ : syracuseStep 504918431 = 757377647) B757377647
theorem B336612287 : Blo 2017435 336612287 := bstep (se 1 (by rfl) ⟨252459215, by rfl⟩ : syracuseStep 336612287 = 504918431) B504918431
theorem B224408191 : Blo 2017435 224408191 := bstep (se 1 (by rfl) ⟨168306143, by rfl⟩ : syracuseStep 224408191 = 336612287) B336612287
theorem B299210921 : Blo 2017435 299210921 := bstep (se 2 (by rfl) ⟨112204095, by rfl⟩ : syracuseStep 299210921 = 224408191) B224408191
theorem B199473947 : Blo 2017435 199473947 := bstep (se 1 (by rfl) ⟨149605460, by rfl⟩ : syracuseStep 199473947 = 299210921) B299210921
theorem B132982631 : Blo 2017435 132982631 := bstep (se 1 (by rfl) ⟨99736973, by rfl⟩ : syracuseStep 132982631 = 199473947) B199473947
theorem B88655087 : Blo 2017435 88655087 := bstep (se 1 (by rfl) ⟨66491315, by rfl⟩ : syracuseStep 88655087 = 132982631) B132982631
theorem B59103391 : Blo 2017435 59103391 := bstep (se 1 (by rfl) ⟨44327543, by rfl⟩ : syracuseStep 59103391 = 88655087) B88655087
theorem B78804521 : Blo 2017435 78804521 := bstep (se 2 (by rfl) ⟨29551695, by rfl⟩ : syracuseStep 78804521 = 59103391) B59103391
theorem B52536347 : Blo 2017435 52536347 := bstep (se 1 (by rfl) ⟨39402260, by rfl⟩ : syracuseStep 52536347 = 78804521) B78804521
theorem B35024231 : Blo 2017435 35024231 := bstep (se 1 (by rfl) ⟨26268173, by rfl⟩ : syracuseStep 35024231 = 52536347) B52536347
theorem B23349487 : Blo 2017435 23349487 := bstep (se 1 (by rfl) ⟨17512115, by rfl⟩ : syracuseStep 23349487 = 35024231) B35024231
theorem B31132649 : Blo 2017435 31132649 := bstep (se 2 (by rfl) ⟨11674743, by rfl⟩ : syracuseStep 31132649 = 23349487) B23349487
theorem B20755099 : Blo 2017435 20755099 := bstep (se 1 (by rfl) ⟨15566324, by rfl⟩ : syracuseStep 20755099 = 31132649) B31132649
theorem B110693861 : Blo 2017435 110693861 := bstep (se 4 (by rfl) ⟨10377549, by rfl⟩ : syracuseStep 110693861 = 20755099) B20755099
theorem B73795907 : Blo 2017435 73795907 := bstep (se 1 (by rfl) ⟨55346930, by rfl⟩ : syracuseStep 73795907 = 110693861) B110693861
theorem B196789085 : Blo 2017435 196789085 := bstep (se 3 (by rfl) ⟨36897953, by rfl⟩ : syracuseStep 196789085 = 73795907) B73795907
theorem B131192723 : Blo 2017435 131192723 := bstep (se 1 (by rfl) ⟨98394542, by rfl⟩ : syracuseStep 131192723 = 196789085) B196789085
theorem B349847261 : Blo 2017435 349847261 := bstep (se 3 (by rfl) ⟨65596361, by rfl⟩ : syracuseStep 349847261 = 131192723) B131192723
theorem B233231507 : Blo 2017435 233231507 := bstep (se 1 (by rfl) ⟨174923630, by rfl⟩ : syracuseStep 233231507 = 349847261) B349847261
theorem B155487671 : Blo 2017435 155487671 := bstep (se 1 (by rfl) ⟨116615753, by rfl⟩ : syracuseStep 155487671 = 233231507) B233231507
theorem B103658447 : Blo 2017435 103658447 := bstep (se 1 (by rfl) ⟨77743835, by rfl⟩ : syracuseStep 103658447 = 155487671) B155487671
theorem B69105631 : Blo 2017435 69105631 := bstep (se 1 (by rfl) ⟨51829223, by rfl⟩ : syracuseStep 69105631 = 103658447) B103658447
theorem B92140841 : Blo 2017435 92140841 := bstep (se 2 (by rfl) ⟨34552815, by rfl⟩ : syracuseStep 92140841 = 69105631) B69105631
theorem B245708909 : Blo 2017435 245708909 := bstep (se 3 (by rfl) ⟨46070420, by rfl⟩ : syracuseStep 245708909 = 92140841) B92140841
theorem B163805939 : Blo 2017435 163805939 := bstep (se 1 (by rfl) ⟨122854454, by rfl⟩ : syracuseStep 163805939 = 245708909) B245708909
theorem B109203959 : Blo 2017435 109203959 := bstep (se 1 (by rfl) ⟨81902969, by rfl⟩ : syracuseStep 109203959 = 163805939) B163805939
theorem B72802639 : Blo 2017435 72802639 := bstep (se 1 (by rfl) ⟨54601979, by rfl⟩ : syracuseStep 72802639 = 109203959) B109203959
theorem B97070185 : Blo 2017435 97070185 := bstep (se 2 (by rfl) ⟨36401319, by rfl⟩ : syracuseStep 97070185 = 72802639) B72802639
theorem B129426913 : Blo 2017435 129426913 := bstep (se 2 (by rfl) ⟨48535092, by rfl⟩ : syracuseStep 129426913 = 97070185) B97070185
theorem B172569217 : Blo 2017435 172569217 := bstep (se 2 (by rfl) ⟨64713456, by rfl⟩ : syracuseStep 172569217 = 129426913) B129426913
theorem B230092289 : Blo 2017435 230092289 := bstep (se 2 (by rfl) ⟨86284608, by rfl⟩ : syracuseStep 230092289 = 172569217) B172569217
theorem B153394859 : Blo 2017435 153394859 := bstep (se 1 (by rfl) ⟨115046144, by rfl⟩ : syracuseStep 153394859 = 230092289) B230092289
theorem B102263239 : Blo 2017435 102263239 := bstep (se 1 (by rfl) ⟨76697429, by rfl⟩ : syracuseStep 102263239 = 153394859) B153394859
theorem B136350985 : Blo 2017435 136350985 := bstep (se 2 (by rfl) ⟨51131619, by rfl⟩ : syracuseStep 136350985 = 102263239) B102263239
theorem B181801313 : Blo 2017435 181801313 := bstep (se 2 (by rfl) ⟨68175492, by rfl⟩ : syracuseStep 181801313 = 136350985) B136350985
theorem B121200875 : Blo 2017435 121200875 := bstep (se 1 (by rfl) ⟨90900656, by rfl⟩ : syracuseStep 121200875 = 181801313) B181801313
theorem B80800583 : Blo 2017435 80800583 := bstep (se 1 (by rfl) ⟨60600437, by rfl⟩ : syracuseStep 80800583 = 121200875) B121200875
theorem B861872885 : Blo 2017435 861872885 := bstep (se 5 (by rfl) ⟨40400291, by rfl⟩ : syracuseStep 861872885 = 80800583) B80800583
theorem B574581923 : Blo 2017435 574581923 := bstep (se 1 (by rfl) ⟨430936442, by rfl⟩ : syracuseStep 574581923 = 861872885) B861872885
theorem B383054615 : Blo 2017435 383054615 := bstep (se 1 (by rfl) ⟨287290961, by rfl⟩ : syracuseStep 383054615 = 574581923) B574581923
theorem B255369743 : Blo 2017435 255369743 := bstep (se 1 (by rfl) ⟨191527307, by rfl⟩ : syracuseStep 255369743 = 383054615) B383054615
theorem B170246495 : Blo 2017435 170246495 := bstep (se 1 (by rfl) ⟨127684871, by rfl⟩ : syracuseStep 170246495 = 255369743) B255369743
theorem B453990653 : Blo 2017435 453990653 := bstep (se 3 (by rfl) ⟨85123247, by rfl⟩ : syracuseStep 453990653 = 170246495) B170246495
theorem B302660435 : Blo 2017435 302660435 := bstep (se 1 (by rfl) ⟨226995326, by rfl⟩ : syracuseStep 302660435 = 453990653) B453990653
theorem B807094493 : Blo 2017435 807094493 := bstep (se 3 (by rfl) ⟨151330217, by rfl⟩ : syracuseStep 807094493 = 302660435) B302660435
theorem B538062995 : Blo 2017435 538062995 := bstep (se 1 (by rfl) ⟨403547246, by rfl⟩ : syracuseStep 538062995 = 807094493) B807094493
theorem B358708663 : Blo 2017435 358708663 := bstep (se 1 (by rfl) ⟨269031497, by rfl⟩ : syracuseStep 358708663 = 538062995) B538062995
theorem B478278217 : Blo 2017435 478278217 := bstep (se 2 (by rfl) ⟨179354331, by rfl⟩ : syracuseStep 478278217 = 358708663) B358708663
theorem B637704289 : Blo 2017435 637704289 := bstep (se 2 (by rfl) ⟨239139108, by rfl⟩ : syracuseStep 637704289 = 478278217) B478278217
theorem B850272385 : Blo 2017435 850272385 := bstep (se 2 (by rfl) ⟨318852144, by rfl⟩ : syracuseStep 850272385 = 637704289) B637704289
theorem B1133696513 : Blo 2017435 1133696513 := bstep (se 2 (by rfl) ⟨425136192, by rfl⟩ : syracuseStep 1133696513 = 850272385) B850272385
theorem B755797675 : Blo 2017435 755797675 := bstep (se 1 (by rfl) ⟨566848256, by rfl⟩ : syracuseStep 755797675 = 1133696513) B1133696513
theorem B1007730233 : Blo 2017435 1007730233 := bstep (se 2 (by rfl) ⟨377898837, by rfl⟩ : syracuseStep 1007730233 = 755797675) B755797675
theorem B671820155 : Blo 2017435 671820155 := bstep (se 1 (by rfl) ⟨503865116, by rfl⟩ : syracuseStep 671820155 = 1007730233) B1007730233
theorem B447880103 : Blo 2017435 447880103 := bstep (se 1 (by rfl) ⟨335910077, by rfl⟩ : syracuseStep 447880103 = 671820155) B671820155
theorem B298586735 : Blo 2017435 298586735 := bstep (se 1 (by rfl) ⟨223940051, by rfl⟩ : syracuseStep 298586735 = 447880103) B447880103
theorem B199057823 : Blo 2017435 199057823 := bstep (se 1 (by rfl) ⟨149293367, by rfl⟩ : syracuseStep 199057823 = 298586735) B298586735
theorem B132705215 : Blo 2017435 132705215 := bstep (se 1 (by rfl) ⟨99528911, by rfl⟩ : syracuseStep 132705215 = 199057823) B199057823
theorem B88470143 : Blo 2017435 88470143 := bstep (se 1 (by rfl) ⟨66352607, by rfl⟩ : syracuseStep 88470143 = 132705215) B132705215
theorem B58980095 : Blo 2017435 58980095 := bstep (se 1 (by rfl) ⟨44235071, by rfl⟩ : syracuseStep 58980095 = 88470143) B88470143
theorem B39320063 : Blo 2017435 39320063 := bstep (se 1 (by rfl) ⟨29490047, by rfl⟩ : syracuseStep 39320063 = 58980095) B58980095
theorem B26213375 : Blo 2017435 26213375 := bstep (se 1 (by rfl) ⟨19660031, by rfl⟩ : syracuseStep 26213375 = 39320063) B39320063
theorem B17475583 : Blo 2017435 17475583 := bstep (se 1 (by rfl) ⟨13106687, by rfl⟩ : syracuseStep 17475583 = 26213375) B26213375
theorem B23300777 : Blo 2017435 23300777 := bstep (se 2 (by rfl) ⟨8737791, by rfl⟩ : syracuseStep 23300777 = 17475583) B17475583
theorem B15533851 : Blo 2017435 15533851 := bstep (se 1 (by rfl) ⟨11650388, by rfl⟩ : syracuseStep 15533851 = 23300777) B23300777
theorem B20711801 : Blo 2017435 20711801 := bstep (se 2 (by rfl) ⟨7766925, by rfl⟩ : syracuseStep 20711801 = 15533851) B15533851
theorem B13807867 : Blo 2017435 13807867 := bstep (se 1 (by rfl) ⟨10355900, by rfl⟩ : syracuseStep 13807867 = 20711801) B20711801
theorem B18410489 : Blo 2017435 18410489 := bstep (se 2 (by rfl) ⟨6903933, by rfl⟩ : syracuseStep 18410489 = 13807867) B13807867
theorem B12273659 : Blo 2017435 12273659 := bstep (se 1 (by rfl) ⟨9205244, by rfl⟩ : syracuseStep 12273659 = 18410489) B18410489
theorem B8182439 : Blo 2017435 8182439 := bstep (se 1 (by rfl) ⟨6136829, by rfl⟩ : syracuseStep 8182439 = 12273659) B12273659
theorem B5454959 : Blo 2017435 5454959 := bstep (se 1 (by rfl) ⟨4091219, by rfl⟩ : syracuseStep 5454959 = 8182439) B8182439
theorem B14546557 : Blo 2017435 14546557 := bstep (se 3 (by rfl) ⟨2727479, by rfl⟩ : syracuseStep 14546557 = 5454959) B5454959
theorem B19395409 : Blo 2017435 19395409 := bstep (se 2 (by rfl) ⟨7273278, by rfl⟩ : syracuseStep 19395409 = 14546557) B14546557
theorem B25860545 : Blo 2017435 25860545 := bstep (se 2 (by rfl) ⟨9697704, by rfl⟩ : syracuseStep 25860545 = 19395409) B19395409
theorem B17240363 : Blo 2017435 17240363 := bstep (se 1 (by rfl) ⟨12930272, by rfl⟩ : syracuseStep 17240363 = 25860545) B25860545
theorem B11493575 : Blo 2017435 11493575 := bstep (se 1 (by rfl) ⟨8620181, by rfl⟩ : syracuseStep 11493575 = 17240363) B17240363
theorem B7662383 : Blo 2017435 7662383 := bstep (se 1 (by rfl) ⟨5746787, by rfl⟩ : syracuseStep 7662383 = 11493575) B11493575
theorem B5108255 : Blo 2017435 5108255 := bstep (se 1 (by rfl) ⟨3831191, by rfl⟩ : syracuseStep 5108255 = 7662383) B7662383
theorem B3405503 : Blo 2017435 3405503 := bstep (se 1 (by rfl) ⟨2554127, by rfl⟩ : syracuseStep 3405503 = 5108255) B5108255
theorem B2270335 : Blo 2017435 2270335 := bstep (se 1 (by rfl) ⟨1702751, by rfl⟩ : syracuseStep 2270335 = 3405503) B3405503
theorem B3027113 : Blo 2017435 3027113 := bstep (se 2 (by rfl) ⟨1135167, by rfl⟩ : syracuseStep 3027113 = 2270335) B2270335
theorem B2018075 : Blo 2017435 2018075 := bstep (se 1 (by rfl) ⟨1513556, by rfl⟩ : syracuseStep 2018075 = 3027113) B3027113
theorem B2588981 : Blo 2017435 2588981 := bbase (se 5 (by rfl) ⟨121358, by rfl⟩ : syracuseStep 2588981 = 242717) (by norm_num)
theorem B6903949 : Blo 2017435 6903949 := bstep (se 3 (by rfl) ⟨1294490, by rfl⟩ : syracuseStep 6903949 = 2588981) B2588981
theorem B9205265 : Blo 2017435 9205265 := bstep (se 2 (by rfl) ⟨3451974, by rfl⟩ : syracuseStep 9205265 = 6903949) B6903949
theorem B6136843 : Blo 2017435 6136843 := bstep (se 1 (by rfl) ⟨4602632, by rfl⟩ : syracuseStep 6136843 = 9205265) B9205265
theorem B8182457 : Blo 2017435 8182457 := bstep (se 2 (by rfl) ⟨3068421, by rfl⟩ : syracuseStep 8182457 = 6136843) B6136843
theorem B5454971 : Blo 2017435 5454971 := bstep (se 1 (by rfl) ⟨4091228, by rfl⟩ : syracuseStep 5454971 = 8182457) B8182457
theorem B3636647 : Blo 2017435 3636647 := bstep (se 1 (by rfl) ⟨2727485, by rfl⟩ : syracuseStep 3636647 = 5454971) B5454971
theorem B2424431 : Blo 2017435 2424431 := bstep (se 1 (by rfl) ⟨1818323, by rfl⟩ : syracuseStep 2424431 = 3636647) B3636647
theorem B6465149 : Blo 2017435 6465149 := bstep (se 3 (by rfl) ⟨1212215, by rfl⟩ : syracuseStep 6465149 = 2424431) B2424431
theorem B4310099 : Blo 2017435 4310099 := bstep (se 1 (by rfl) ⟨3232574, by rfl⟩ : syracuseStep 4310099 = 6465149) B6465149
theorem B2873399 : Blo 2017435 2873399 := bstep (se 1 (by rfl) ⟨2155049, by rfl⟩ : syracuseStep 2873399 = 4310099) B4310099
theorem B7662397 : Blo 2017435 7662397 := bstep (se 3 (by rfl) ⟨1436699, by rfl⟩ : syracuseStep 7662397 = 2873399) B2873399
theorem B10216529 : Blo 2017435 10216529 := bstep (se 2 (by rfl) ⟨3831198, by rfl⟩ : syracuseStep 10216529 = 7662397) B7662397
theorem B6811019 : Blo 2017435 6811019 := bstep (se 1 (by rfl) ⟨5108264, by rfl⟩ : syracuseStep 6811019 = 10216529) B10216529
theorem B4540679 : Blo 2017435 4540679 := bstep (se 1 (by rfl) ⟨3405509, by rfl⟩ : syracuseStep 4540679 = 6811019) B6811019
theorem B3027119 : Blo 2017435 3027119 := bstep (se 1 (by rfl) ⟨2270339, by rfl⟩ : syracuseStep 3027119 = 4540679) B4540679
theorem B2018079 : Blo 2017435 2018079 := bstep (se 1 (by rfl) ⟨1513559, by rfl⟩ : syracuseStep 2018079 = 3027119) B3027119
theorem B3027125 : Blo 2017435 3027125 := bbase (se 5 (by rfl) ⟨141896, by rfl⟩ : syracuseStep 3027125 = 283793) (by norm_num)
theorem B2018083 : Blo 2017435 2018083 := bstep (se 1 (by rfl) ⟨1513562, by rfl⟩ : syracuseStep 2018083 = 3027125) B3027125
theorem B5108285 : Blo 2017435 5108285 := bbase (se 3 (by rfl) ⟨957803, by rfl⟩ : syracuseStep 5108285 = 1915607) (by norm_num)
theorem B3405523 : Blo 2017435 3405523 := bstep (se 1 (by rfl) ⟨2554142, by rfl⟩ : syracuseStep 3405523 = 5108285) B5108285
theorem B4540697 : Blo 2017435 4540697 := bstep (se 2 (by rfl) ⟨1702761, by rfl⟩ : syracuseStep 4540697 = 3405523) B3405523
theorem B3027131 : Blo 2017435 3027131 := bstep (se 1 (by rfl) ⟨2270348, by rfl⟩ : syracuseStep 3027131 = 4540697) B4540697
theorem B2018087 : Blo 2017435 2018087 := bstep (se 1 (by rfl) ⟨1513565, by rfl⟩ : syracuseStep 2018087 = 3027131) B3027131
theorem B2270353 : Blo 2017435 2270353 := bbase (se 2 (by rfl) ⟨851382, by rfl⟩ : syracuseStep 2270353 = 1702765) (by norm_num)
theorem B3027137 : Blo 2017435 3027137 := bstep (se 2 (by rfl) ⟨1135176, by rfl⟩ : syracuseStep 3027137 = 2270353) B2270353
theorem B2018091 : Blo 2017435 2018091 := bstep (se 1 (by rfl) ⟨1513568, by rfl⟩ : syracuseStep 2018091 = 3027137) B3027137
theorem B3831229 : Blo 2017435 3831229 := bbase (se 3 (by rfl) ⟨718355, by rfl⟩ : syracuseStep 3831229 = 1436711) (by norm_num)
theorem B5108305 : Blo 2017435 5108305 := bstep (se 2 (by rfl) ⟨1915614, by rfl⟩ : syracuseStep 5108305 = 3831229) B3831229
theorem B6811073 : Blo 2017435 6811073 := bstep (se 2 (by rfl) ⟨2554152, by rfl⟩ : syracuseStep 6811073 = 5108305) B5108305
theorem B4540715 : Blo 2017435 4540715 := bstep (se 1 (by rfl) ⟨3405536, by rfl⟩ : syracuseStep 4540715 = 6811073) B6811073
theorem B3027143 : Blo 2017435 3027143 := bstep (se 1 (by rfl) ⟨2270357, by rfl⟩ : syracuseStep 3027143 = 4540715) B4540715
theorem B2018095 : Blo 2017435 2018095 := bstep (se 1 (by rfl) ⟨1513571, by rfl⟩ : syracuseStep 2018095 = 3027143) B3027143
theorem B3027149 : Blo 2017435 3027149 := bbase (se 3 (by rfl) ⟨567590, by rfl⟩ : syracuseStep 3027149 = 1135181) (by norm_num)
theorem B2018099 : Blo 2017435 2018099 := bstep (se 1 (by rfl) ⟨1513574, by rfl⟩ : syracuseStep 2018099 = 3027149) B3027149
theorem B4540733 : Blo 2017435 4540733 := bbase (se 3 (by rfl) ⟨851387, by rfl⟩ : syracuseStep 4540733 = 1702775) (by norm_num)
theorem B3027155 : Blo 2017435 3027155 := bstep (se 1 (by rfl) ⟨2270366, by rfl⟩ : syracuseStep 3027155 = 4540733) B4540733
theorem B2018103 : Blo 2017435 2018103 := bstep (se 1 (by rfl) ⟨1513577, by rfl⟩ : syracuseStep 2018103 = 3027155) B3027155
theorem B3405557 : Blo 2017435 3405557 := bbase (se 5 (by rfl) ⟨159635, by rfl⟩ : syracuseStep 3405557 = 319271) (by norm_num)
theorem B2270371 : Blo 2017435 2270371 := bstep (se 1 (by rfl) ⟨1702778, by rfl⟩ : syracuseStep 2270371 = 3405557) B3405557
theorem B3027161 : Blo 2017435 3027161 := bstep (se 2 (by rfl) ⟨1135185, by rfl⟩ : syracuseStep 3027161 = 2270371) B2270371
theorem B2018107 : Blo 2017435 2018107 := bstep (se 1 (by rfl) ⟨1513580, by rfl⟩ : syracuseStep 2018107 = 3027161) B3027161
theorem B9697877 : Blo 2017435 9697877 := bbase (se 8 (by rfl) ⟨56823, by rfl⟩ : syracuseStep 9697877 = 113647) (by norm_num)
theorem B6465251 : Blo 2017435 6465251 := bstep (se 1 (by rfl) ⟨4848938, by rfl⟩ : syracuseStep 6465251 = 9697877) B9697877
theorem B4310167 : Blo 2017435 4310167 := bstep (se 1 (by rfl) ⟨3232625, by rfl⟩ : syracuseStep 4310167 = 6465251) B6465251
theorem B5746889 : Blo 2017435 5746889 := bstep (se 2 (by rfl) ⟨2155083, by rfl⟩ : syracuseStep 5746889 = 4310167) B4310167
theorem B15325037 : Blo 2017435 15325037 := bstep (se 3 (by rfl) ⟨2873444, by rfl⟩ : syracuseStep 15325037 = 5746889) B5746889
theorem B10216691 : Blo 2017435 10216691 := bstep (se 1 (by rfl) ⟨7662518, by rfl⟩ : syracuseStep 10216691 = 15325037) B15325037
theorem B6811127 : Blo 2017435 6811127 := bstep (se 1 (by rfl) ⟨5108345, by rfl⟩ : syracuseStep 6811127 = 10216691) B10216691
theorem B4540751 : Blo 2017435 4540751 := bstep (se 1 (by rfl) ⟨3405563, by rfl⟩ : syracuseStep 4540751 = 6811127) B6811127
theorem B3027167 : Blo 2017435 3027167 := bstep (se 1 (by rfl) ⟨2270375, by rfl⟩ : syracuseStep 3027167 = 4540751) B4540751
theorem B2018111 : Blo 2017435 2018111 := bstep (se 1 (by rfl) ⟨1513583, by rfl⟩ : syracuseStep 2018111 = 3027167) B3027167
theorem B3027173 : Blo 2017435 3027173 := bbase (se 4 (by rfl) ⟨283797, by rfl⟩ : syracuseStep 3027173 = 567595) (by norm_num)
theorem B2018115 : Blo 2017435 2018115 := bstep (se 1 (by rfl) ⟨1513586, by rfl⟩ : syracuseStep 2018115 = 3027173) B3027173
theorem B11650645 : Blo 2017435 11650645 := bbase (se 8 (by rfl) ⟨68265, by rfl⟩ : syracuseStep 11650645 = 136531) (by norm_num)
theorem B15534193 : Blo 2017435 15534193 := bstep (se 2 (by rfl) ⟨5825322, by rfl⟩ : syracuseStep 15534193 = 11650645) B11650645
theorem B20712257 : Blo 2017435 20712257 := bstep (se 2 (by rfl) ⟨7767096, by rfl⟩ : syracuseStep 20712257 = 15534193) B15534193
theorem B13808171 : Blo 2017435 13808171 := bstep (se 1 (by rfl) ⟨10356128, by rfl⟩ : syracuseStep 13808171 = 20712257) B20712257
theorem B36821789 : Blo 2017435 36821789 := bstep (se 3 (by rfl) ⟨6904085, by rfl⟩ : syracuseStep 36821789 = 13808171) B13808171
theorem B24547859 : Blo 2017435 24547859 := bstep (se 1 (by rfl) ⟨18410894, by rfl⟩ : syracuseStep 24547859 = 36821789) B36821789
theorem B16365239 : Blo 2017435 16365239 := bstep (se 1 (by rfl) ⟨12273929, by rfl⟩ : syracuseStep 16365239 = 24547859) B24547859
theorem B10910159 : Blo 2017435 10910159 := bstep (se 1 (by rfl) ⟨8182619, by rfl⟩ : syracuseStep 10910159 = 16365239) B16365239
theorem B7273439 : Blo 2017435 7273439 := bstep (se 1 (by rfl) ⟨5455079, by rfl⟩ : syracuseStep 7273439 = 10910159) B10910159
theorem B4848959 : Blo 2017435 4848959 := bstep (se 1 (by rfl) ⟨3636719, by rfl⟩ : syracuseStep 4848959 = 7273439) B7273439
theorem B3232639 : Blo 2017435 3232639 := bstep (se 1 (by rfl) ⟨2424479, by rfl⟩ : syracuseStep 3232639 = 4848959) B4848959
theorem B4310185 : Blo 2017435 4310185 := bstep (se 2 (by rfl) ⟨1616319, by rfl⟩ : syracuseStep 4310185 = 3232639) B3232639
theorem B5746913 : Blo 2017435 5746913 := bstep (se 2 (by rfl) ⟨2155092, by rfl⟩ : syracuseStep 5746913 = 4310185) B4310185
theorem B3831275 : Blo 2017435 3831275 := bstep (se 1 (by rfl) ⟨2873456, by rfl⟩ : syracuseStep 3831275 = 5746913) B5746913
theorem B2554183 : Blo 2017435 2554183 := bstep (se 1 (by rfl) ⟨1915637, by rfl⟩ : syracuseStep 2554183 = 3831275) B3831275
theorem B3405577 : Blo 2017435 3405577 := bstep (se 2 (by rfl) ⟨1277091, by rfl⟩ : syracuseStep 3405577 = 2554183) B2554183
theorem B4540769 : Blo 2017435 4540769 := bstep (se 2 (by rfl) ⟨1702788, by rfl⟩ : syracuseStep 4540769 = 3405577) B3405577
theorem B3027179 : Blo 2017435 3027179 := bstep (se 1 (by rfl) ⟨2270384, by rfl⟩ : syracuseStep 3027179 = 4540769) B4540769
theorem B2018119 : Blo 2017435 2018119 := bstep (se 1 (by rfl) ⟨1513589, by rfl⟩ : syracuseStep 2018119 = 3027179) B3027179
theorem B2270389 : Blo 2017435 2270389 := bbase (se 5 (by rfl) ⟨106424, by rfl⟩ : syracuseStep 2270389 = 212849) (by norm_num)
theorem B3027185 : Blo 2017435 3027185 := bstep (se 2 (by rfl) ⟨1135194, by rfl⟩ : syracuseStep 3027185 = 2270389) B2270389
theorem B2018123 : Blo 2017435 2018123 := bstep (se 1 (by rfl) ⟨1513592, by rfl⟩ : syracuseStep 2018123 = 3027185) B3027185
theorem B2554193 : Blo 2017435 2554193 := bbase (se 2 (by rfl) ⟨957822, by rfl⟩ : syracuseStep 2554193 = 1915645) (by norm_num)
theorem B6811181 : Blo 2017435 6811181 := bstep (se 3 (by rfl) ⟨1277096, by rfl⟩ : syracuseStep 6811181 = 2554193) B2554193
theorem B4540787 : Blo 2017435 4540787 := bstep (se 1 (by rfl) ⟨3405590, by rfl⟩ : syracuseStep 4540787 = 6811181) B6811181
theorem B3027191 : Blo 2017435 3027191 := bstep (se 1 (by rfl) ⟨2270393, by rfl⟩ : syracuseStep 3027191 = 4540787) B4540787
theorem B2018127 : Blo 2017435 2018127 := bstep (se 1 (by rfl) ⟨1513595, by rfl⟩ : syracuseStep 2018127 = 3027191) B3027191
theorem B3027197 : Blo 2017435 3027197 := bbase (se 3 (by rfl) ⟨567599, by rfl⟩ : syracuseStep 3027197 = 1135199) (by norm_num)
theorem B2018131 : Blo 2017435 2018131 := bstep (se 1 (by rfl) ⟨1513598, by rfl⟩ : syracuseStep 2018131 = 3027197) B3027197
theorem B4540805 : Blo 2017435 4540805 := bbase (se 4 (by rfl) ⟨425700, by rfl⟩ : syracuseStep 4540805 = 851401) (by norm_num)
theorem B3027203 : Blo 2017435 3027203 := bstep (se 1 (by rfl) ⟨2270402, by rfl⟩ : syracuseStep 3027203 = 4540805) B4540805
theorem B2018135 : Blo 2017435 2018135 := bstep (se 1 (by rfl) ⟨1513601, by rfl⟩ : syracuseStep 2018135 = 3027203) B3027203
theorem B2873485 : Blo 2017435 2873485 := bbase (se 3 (by rfl) ⟨538778, by rfl⟩ : syracuseStep 2873485 = 1077557) (by norm_num)
theorem B3831313 : Blo 2017435 3831313 := bstep (se 2 (by rfl) ⟨1436742, by rfl⟩ : syracuseStep 3831313 = 2873485) B2873485
theorem B5108417 : Blo 2017435 5108417 := bstep (se 2 (by rfl) ⟨1915656, by rfl⟩ : syracuseStep 5108417 = 3831313) B3831313
theorem B3405611 : Blo 2017435 3405611 := bstep (se 1 (by rfl) ⟨2554208, by rfl⟩ : syracuseStep 3405611 = 5108417) B5108417
theorem B2270407 : Blo 2017435 2270407 := bstep (se 1 (by rfl) ⟨1702805, by rfl⟩ : syracuseStep 2270407 = 3405611) B3405611
theorem B3027209 : Blo 2017435 3027209 := bstep (se 2 (by rfl) ⟨1135203, by rfl⟩ : syracuseStep 3027209 = 2270407) B2270407
theorem B2018139 : Blo 2017435 2018139 := bstep (se 1 (by rfl) ⟨1513604, by rfl⟩ : syracuseStep 2018139 = 3027209) B3027209
theorem B10216853 : Blo 2017435 10216853 := bbase (se 6 (by rfl) ⟨239457, by rfl⟩ : syracuseStep 10216853 = 478915) (by norm_num)
theorem B6811235 : Blo 2017435 6811235 := bstep (se 1 (by rfl) ⟨5108426, by rfl⟩ : syracuseStep 6811235 = 10216853) B10216853
theorem B4540823 : Blo 2017435 4540823 := bstep (se 1 (by rfl) ⟨3405617, by rfl⟩ : syracuseStep 4540823 = 6811235) B6811235
theorem B3027215 : Blo 2017435 3027215 := bstep (se 1 (by rfl) ⟨2270411, by rfl⟩ : syracuseStep 3027215 = 4540823) B4540823
theorem B2018143 : Blo 2017435 2018143 := bstep (se 1 (by rfl) ⟨1513607, by rfl⟩ : syracuseStep 2018143 = 3027215) B3027215
theorem B3027221 : Blo 2017435 3027221 := bbase (se 6 (by rfl) ⟨70950, by rfl⟩ : syracuseStep 3027221 = 141901) (by norm_num)
theorem B2018147 : Blo 2017435 2018147 := bstep (se 1 (by rfl) ⟨1513610, by rfl⟩ : syracuseStep 2018147 = 3027221) B3027221
theorem B9698069 : Blo 2017435 9698069 := bbase (se 6 (by rfl) ⟨227298, by rfl⟩ : syracuseStep 9698069 = 454597) (by norm_num)
theorem B25861517 : Blo 2017435 25861517 := bstep (se 3 (by rfl) ⟨4849034, by rfl⟩ : syracuseStep 25861517 = 9698069) B9698069
theorem B17241011 : Blo 2017435 17241011 := bstep (se 1 (by rfl) ⟨12930758, by rfl⟩ : syracuseStep 17241011 = 25861517) B25861517
theorem B11494007 : Blo 2017435 11494007 := bstep (se 1 (by rfl) ⟨8620505, by rfl⟩ : syracuseStep 11494007 = 17241011) B17241011
theorem B7662671 : Blo 2017435 7662671 := bstep (se 1 (by rfl) ⟨5747003, by rfl⟩ : syracuseStep 7662671 = 11494007) B11494007
theorem B5108447 : Blo 2017435 5108447 := bstep (se 1 (by rfl) ⟨3831335, by rfl⟩ : syracuseStep 5108447 = 7662671) B7662671
theorem B3405631 : Blo 2017435 3405631 := bstep (se 1 (by rfl) ⟨2554223, by rfl⟩ : syracuseStep 3405631 = 5108447) B5108447
theorem B4540841 : Blo 2017435 4540841 := bstep (se 2 (by rfl) ⟨1702815, by rfl⟩ : syracuseStep 4540841 = 3405631) B3405631
theorem B3027227 : Blo 2017435 3027227 := bstep (se 1 (by rfl) ⟨2270420, by rfl⟩ : syracuseStep 3027227 = 4540841) B4540841
theorem B2018151 : Blo 2017435 2018151 := bstep (se 1 (by rfl) ⟨1513613, by rfl⟩ : syracuseStep 2018151 = 3027227) B3027227
theorem B2270425 : Blo 2017435 2270425 := bbase (se 2 (by rfl) ⟨851409, by rfl⟩ : syracuseStep 2270425 = 1702819) (by norm_num)
theorem B3027233 : Blo 2017435 3027233 := bstep (se 2 (by rfl) ⟨1135212, by rfl⟩ : syracuseStep 3027233 = 2270425) B2270425
theorem B2018155 : Blo 2017435 2018155 := bstep (se 1 (by rfl) ⟨1513616, by rfl⟩ : syracuseStep 2018155 = 3027233) B3027233
theorem B19660853 : Blo 2017435 19660853 := bbase (se 5 (by rfl) ⟨921602, by rfl⟩ : syracuseStep 19660853 = 1843205) (by norm_num)
theorem B52428941 : Blo 2017435 52428941 := bstep (se 3 (by rfl) ⟨9830426, by rfl⟩ : syracuseStep 52428941 = 19660853) B19660853
theorem B34952627 : Blo 2017435 34952627 := bstep (se 1 (by rfl) ⟨26214470, by rfl⟩ : syracuseStep 34952627 = 52428941) B52428941
theorem B23301751 : Blo 2017435 23301751 := bstep (se 1 (by rfl) ⟨17476313, by rfl⟩ : syracuseStep 23301751 = 34952627) B34952627
theorem B31069001 : Blo 2017435 31069001 := bstep (se 2 (by rfl) ⟨11650875, by rfl⟩ : syracuseStep 31069001 = 23301751) B23301751
theorem B20712667 : Blo 2017435 20712667 := bstep (se 1 (by rfl) ⟨15534500, by rfl⟩ : syracuseStep 20712667 = 31069001) B31069001
theorem B27616889 : Blo 2017435 27616889 := bstep (se 2 (by rfl) ⟨10356333, by rfl⟩ : syracuseStep 27616889 = 20712667) B20712667
theorem B18411259 : Blo 2017435 18411259 := bstep (se 1 (by rfl) ⟨13808444, by rfl⟩ : syracuseStep 18411259 = 27616889) B27616889
theorem B24548345 : Blo 2017435 24548345 := bstep (se 2 (by rfl) ⟨9205629, by rfl⟩ : syracuseStep 24548345 = 18411259) B18411259
theorem B16365563 : Blo 2017435 16365563 := bstep (se 1 (by rfl) ⟨12274172, by rfl⟩ : syracuseStep 16365563 = 24548345) B24548345
theorem B10910375 : Blo 2017435 10910375 := bstep (se 1 (by rfl) ⟨8182781, by rfl⟩ : syracuseStep 10910375 = 16365563) B16365563
theorem B7273583 : Blo 2017435 7273583 := bstep (se 1 (by rfl) ⟨5455187, by rfl⟩ : syracuseStep 7273583 = 10910375) B10910375
theorem B4849055 : Blo 2017435 4849055 := bstep (se 1 (by rfl) ⟨3636791, by rfl⟩ : syracuseStep 4849055 = 7273583) B7273583
theorem B3232703 : Blo 2017435 3232703 := bstep (se 1 (by rfl) ⟨2424527, by rfl⟩ : syracuseStep 3232703 = 4849055) B4849055
theorem B2155135 : Blo 2017435 2155135 := bstep (se 1 (by rfl) ⟨1616351, by rfl⟩ : syracuseStep 2155135 = 3232703) B3232703
theorem B2873513 : Blo 2017435 2873513 := bstep (se 2 (by rfl) ⟨1077567, by rfl⟩ : syracuseStep 2873513 = 2155135) B2155135
theorem B7662701 : Blo 2017435 7662701 := bstep (se 3 (by rfl) ⟨1436756, by rfl⟩ : syracuseStep 7662701 = 2873513) B2873513
theorem B5108467 : Blo 2017435 5108467 := bstep (se 1 (by rfl) ⟨3831350, by rfl⟩ : syracuseStep 5108467 = 7662701) B7662701
theorem B6811289 : Blo 2017435 6811289 := bstep (se 2 (by rfl) ⟨2554233, by rfl⟩ : syracuseStep 6811289 = 5108467) B5108467
theorem B4540859 : Blo 2017435 4540859 := bstep (se 1 (by rfl) ⟨3405644, by rfl⟩ : syracuseStep 4540859 = 6811289) B6811289
theorem B3027239 : Blo 2017435 3027239 := bstep (se 1 (by rfl) ⟨2270429, by rfl⟩ : syracuseStep 3027239 = 4540859) B4540859
theorem B2018159 : Blo 2017435 2018159 := bstep (se 1 (by rfl) ⟨1513619, by rfl⟩ : syracuseStep 2018159 = 3027239) B3027239
theorem B3027245 : Blo 2017435 3027245 := bbase (se 3 (by rfl) ⟨567608, by rfl⟩ : syracuseStep 3027245 = 1135217) (by norm_num)
theorem B2018163 : Blo 2017435 2018163 := bstep (se 1 (by rfl) ⟨1513622, by rfl⟩ : syracuseStep 2018163 = 3027245) B3027245
theorem B4540877 : Blo 2017435 4540877 := bbase (se 3 (by rfl) ⟨851414, by rfl⟩ : syracuseStep 4540877 = 1702829) (by norm_num)
theorem B3027251 : Blo 2017435 3027251 := bstep (se 1 (by rfl) ⟨2270438, by rfl⟩ : syracuseStep 3027251 = 4540877) B4540877
theorem B2018167 : Blo 2017435 2018167 := bstep (se 1 (by rfl) ⟨1513625, by rfl⟩ : syracuseStep 2018167 = 3027251) B3027251
theorem B2554249 : Blo 2017435 2554249 := bbase (se 2 (by rfl) ⟨957843, by rfl⟩ : syracuseStep 2554249 = 1915687) (by norm_num)
theorem B3405665 : Blo 2017435 3405665 := bstep (se 2 (by rfl) ⟨1277124, by rfl⟩ : syracuseStep 3405665 = 2554249) B2554249
theorem B2270443 : Blo 2017435 2270443 := bstep (se 1 (by rfl) ⟨1702832, by rfl⟩ : syracuseStep 2270443 = 3405665) B3405665
theorem B3027257 : Blo 2017435 3027257 := bstep (se 2 (by rfl) ⟨1135221, by rfl⟩ : syracuseStep 3027257 = 2270443) B2270443
theorem B2018171 : Blo 2017435 2018171 := bstep (se 1 (by rfl) ⟨1513628, by rfl⟩ : syracuseStep 2018171 = 3027257) B3027257
theorem B65462741 : Blo 2017435 65462741 := bbase (se 7 (by rfl) ⟨767141, by rfl⟩ : syracuseStep 65462741 = 1534283) (by norm_num)
theorem B43641827 : Blo 2017435 43641827 := bstep (se 1 (by rfl) ⟨32731370, by rfl⟩ : syracuseStep 43641827 = 65462741) B65462741
theorem B29094551 : Blo 2017435 29094551 := bstep (se 1 (by rfl) ⟨21820913, by rfl⟩ : syracuseStep 29094551 = 43641827) B43641827
theorem B19396367 : Blo 2017435 19396367 := bstep (se 1 (by rfl) ⟨14547275, by rfl⟩ : syracuseStep 19396367 = 29094551) B29094551
theorem B12930911 : Blo 2017435 12930911 := bstep (se 1 (by rfl) ⟨9698183, by rfl⟩ : syracuseStep 12930911 = 19396367) B19396367
theorem B8620607 : Blo 2017435 8620607 := bstep (se 1 (by rfl) ⟨6465455, by rfl⟩ : syracuseStep 8620607 = 12930911) B12930911
theorem B22988285 : Blo 2017435 22988285 := bstep (se 3 (by rfl) ⟨4310303, by rfl⟩ : syracuseStep 22988285 = 8620607) B8620607
theorem B15325523 : Blo 2017435 15325523 := bstep (se 1 (by rfl) ⟨11494142, by rfl⟩ : syracuseStep 15325523 = 22988285) B22988285
theorem B10217015 : Blo 2017435 10217015 := bstep (se 1 (by rfl) ⟨7662761, by rfl⟩ : syracuseStep 10217015 = 15325523) B15325523
theorem B6811343 : Blo 2017435 6811343 := bstep (se 1 (by rfl) ⟨5108507, by rfl⟩ : syracuseStep 6811343 = 10217015) B10217015
theorem B4540895 : Blo 2017435 4540895 := bstep (se 1 (by rfl) ⟨3405671, by rfl⟩ : syracuseStep 4540895 = 6811343) B6811343
theorem B3027263 : Blo 2017435 3027263 := bstep (se 1 (by rfl) ⟨2270447, by rfl⟩ : syracuseStep 3027263 = 4540895) B4540895
theorem B2018175 : Blo 2017435 2018175 := bstep (se 1 (by rfl) ⟨1513631, by rfl⟩ : syracuseStep 2018175 = 3027263) B3027263
theorem B3027269 : Blo 2017435 3027269 := bbase (se 4 (by rfl) ⟨283806, by rfl⟩ : syracuseStep 3027269 = 567613) (by norm_num)
theorem B2018179 : Blo 2017435 2018179 := bstep (se 1 (by rfl) ⟨1513634, by rfl⟩ : syracuseStep 2018179 = 3027269) B3027269
theorem B3405685 : Blo 2017435 3405685 := bbase (se 5 (by rfl) ⟨159641, by rfl⟩ : syracuseStep 3405685 = 319283) (by norm_num)
theorem B4540913 : Blo 2017435 4540913 := bstep (se 2 (by rfl) ⟨1702842, by rfl⟩ : syracuseStep 4540913 = 3405685) B3405685
theorem B3027275 : Blo 2017435 3027275 := bstep (se 1 (by rfl) ⟨2270456, by rfl⟩ : syracuseStep 3027275 = 4540913) B4540913
theorem B2018183 : Blo 2017435 2018183 := bstep (se 1 (by rfl) ⟨1513637, by rfl⟩ : syracuseStep 2018183 = 3027275) B3027275
theorem B2270461 : Blo 2017435 2270461 := bbase (se 3 (by rfl) ⟨425711, by rfl⟩ : syracuseStep 2270461 = 851423) (by norm_num)
theorem B3027281 : Blo 2017435 3027281 := bstep (se 2 (by rfl) ⟨1135230, by rfl⟩ : syracuseStep 3027281 = 2270461) B2270461
theorem B2018187 : Blo 2017435 2018187 := bstep (se 1 (by rfl) ⟨1513640, by rfl⟩ : syracuseStep 2018187 = 3027281) B3027281
theorem B6811397 : Blo 2017435 6811397 := bbase (se 4 (by rfl) ⟨638568, by rfl⟩ : syracuseStep 6811397 = 1277137) (by norm_num)
theorem B4540931 : Blo 2017435 4540931 := bstep (se 1 (by rfl) ⟨3405698, by rfl⟩ : syracuseStep 4540931 = 6811397) B6811397
theorem B3027287 : Blo 2017435 3027287 := bstep (se 1 (by rfl) ⟨2270465, by rfl⟩ : syracuseStep 3027287 = 4540931) B4540931
theorem B2018191 : Blo 2017435 2018191 := bstep (se 1 (by rfl) ⟨1513643, by rfl⟩ : syracuseStep 2018191 = 3027287) B3027287
theorem B3027293 : Blo 2017435 3027293 := bbase (se 3 (by rfl) ⟨567617, by rfl⟩ : syracuseStep 3027293 = 1135235) (by norm_num)
theorem B2018195 : Blo 2017435 2018195 := bstep (se 1 (by rfl) ⟨1513646, by rfl⟩ : syracuseStep 2018195 = 3027293) B3027293
theorem B4540949 : Blo 2017435 4540949 := bbase (se 6 (by rfl) ⟨106428, by rfl⟩ : syracuseStep 4540949 = 212857) (by norm_num)
theorem B3027299 : Blo 2017435 3027299 := bstep (se 1 (by rfl) ⟨2270474, by rfl⟩ : syracuseStep 3027299 = 4540949) B4540949
theorem B2018199 : Blo 2017435 2018199 := bstep (se 1 (by rfl) ⟨1513649, by rfl⟩ : syracuseStep 2018199 = 3027299) B3027299
theorem B7662869 : Blo 2017435 7662869 := bbase (se 6 (by rfl) ⟨179598, by rfl⟩ : syracuseStep 7662869 = 359197) (by norm_num)
theorem B5108579 : Blo 2017435 5108579 := bstep (se 1 (by rfl) ⟨3831434, by rfl⟩ : syracuseStep 5108579 = 7662869) B7662869
theorem B3405719 : Blo 2017435 3405719 := bstep (se 1 (by rfl) ⟨2554289, by rfl⟩ : syracuseStep 3405719 = 5108579) B5108579
theorem B2270479 : Blo 2017435 2270479 := bstep (se 1 (by rfl) ⟨1702859, by rfl⟩ : syracuseStep 2270479 = 3405719) B3405719
theorem B3027305 : Blo 2017435 3027305 := bstep (se 2 (by rfl) ⟨1135239, by rfl⟩ : syracuseStep 3027305 = 2270479) B2270479
theorem B2018203 : Blo 2017435 2018203 := bstep (se 1 (by rfl) ⟨1513652, by rfl⟩ : syracuseStep 2018203 = 3027305) B3027305
theorem B11494325 : Blo 2017435 11494325 := bbase (se 5 (by rfl) ⟨538796, by rfl⟩ : syracuseStep 11494325 = 1077593) (by norm_num)
theorem B7662883 : Blo 2017435 7662883 := bstep (se 1 (by rfl) ⟨5747162, by rfl⟩ : syracuseStep 7662883 = 11494325) B11494325
theorem B10217177 : Blo 2017435 10217177 := bstep (se 2 (by rfl) ⟨3831441, by rfl⟩ : syracuseStep 10217177 = 7662883) B7662883
theorem B6811451 : Blo 2017435 6811451 := bstep (se 1 (by rfl) ⟨5108588, by rfl⟩ : syracuseStep 6811451 = 10217177) B10217177
theorem B4540967 : Blo 2017435 4540967 := bstep (se 1 (by rfl) ⟨3405725, by rfl⟩ : syracuseStep 4540967 = 6811451) B6811451
theorem B3027311 : Blo 2017435 3027311 := bstep (se 1 (by rfl) ⟨2270483, by rfl⟩ : syracuseStep 3027311 = 4540967) B4540967
theorem B2018207 : Blo 2017435 2018207 := bstep (se 1 (by rfl) ⟨1513655, by rfl⟩ : syracuseStep 2018207 = 3027311) B3027311
theorem B3027317 : Blo 2017435 3027317 := bbase (se 5 (by rfl) ⟨141905, by rfl⟩ : syracuseStep 3027317 = 283811) (by norm_num)
theorem B2018211 : Blo 2017435 2018211 := bstep (se 1 (by rfl) ⟨1513658, by rfl⟩ : syracuseStep 2018211 = 3027317) B3027317
theorem B3636893 : Blo 2017435 3636893 := bbase (se 3 (by rfl) ⟨681917, by rfl⟩ : syracuseStep 3636893 = 1363835) (by norm_num)
theorem B2424595 : Blo 2017435 2424595 := bstep (se 1 (by rfl) ⟨1818446, by rfl⟩ : syracuseStep 2424595 = 3636893) B3636893
theorem B3232793 : Blo 2017435 3232793 := bstep (se 2 (by rfl) ⟨1212297, by rfl⟩ : syracuseStep 3232793 = 2424595) B2424595
theorem B2155195 : Blo 2017435 2155195 := bstep (se 1 (by rfl) ⟨1616396, by rfl⟩ : syracuseStep 2155195 = 3232793) B3232793
theorem B2873593 : Blo 2017435 2873593 := bstep (se 2 (by rfl) ⟨1077597, by rfl⟩ : syracuseStep 2873593 = 2155195) B2155195
theorem B3831457 : Blo 2017435 3831457 := bstep (se 2 (by rfl) ⟨1436796, by rfl⟩ : syracuseStep 3831457 = 2873593) B2873593
theorem B5108609 : Blo 2017435 5108609 := bstep (se 2 (by rfl) ⟨1915728, by rfl⟩ : syracuseStep 5108609 = 3831457) B3831457
theorem B3405739 : Blo 2017435 3405739 := bstep (se 1 (by rfl) ⟨2554304, by rfl⟩ : syracuseStep 3405739 = 5108609) B5108609
theorem B4540985 : Blo 2017435 4540985 := bstep (se 2 (by rfl) ⟨1702869, by rfl⟩ : syracuseStep 4540985 = 3405739) B3405739
theorem B3027323 : Blo 2017435 3027323 := bstep (se 1 (by rfl) ⟨2270492, by rfl⟩ : syracuseStep 3027323 = 4540985) B4540985
theorem B2018215 : Blo 2017435 2018215 := bstep (se 1 (by rfl) ⟨1513661, by rfl⟩ : syracuseStep 2018215 = 3027323) B3027323
theorem B2270497 : Blo 2017435 2270497 := bbase (se 2 (by rfl) ⟨851436, by rfl⟩ : syracuseStep 2270497 = 1702873) (by norm_num)
theorem B3027329 : Blo 2017435 3027329 := bstep (se 2 (by rfl) ⟨1135248, by rfl⟩ : syracuseStep 3027329 = 2270497) B2270497
theorem B2018219 : Blo 2017435 2018219 := bstep (se 1 (by rfl) ⟨1513664, by rfl⟩ : syracuseStep 2018219 = 3027329) B3027329
theorem B5108629 : Blo 2017435 5108629 := bbase (se 6 (by rfl) ⟨119733, by rfl⟩ : syracuseStep 5108629 = 239467) (by norm_num)
theorem B6811505 : Blo 2017435 6811505 := bstep (se 2 (by rfl) ⟨2554314, by rfl⟩ : syracuseStep 6811505 = 5108629) B5108629
theorem B4541003 : Blo 2017435 4541003 := bstep (se 1 (by rfl) ⟨3405752, by rfl⟩ : syracuseStep 4541003 = 6811505) B6811505
theorem B3027335 : Blo 2017435 3027335 := bstep (se 1 (by rfl) ⟨2270501, by rfl⟩ : syracuseStep 3027335 = 4541003) B4541003
theorem B2018223 : Blo 2017435 2018223 := bstep (se 1 (by rfl) ⟨1513667, by rfl⟩ : syracuseStep 2018223 = 3027335) B3027335
theorem B3027341 : Blo 2017435 3027341 := bbase (se 3 (by rfl) ⟨567626, by rfl⟩ : syracuseStep 3027341 = 1135253) (by norm_num)
theorem B2018227 : Blo 2017435 2018227 := bstep (se 1 (by rfl) ⟨1513670, by rfl⟩ : syracuseStep 2018227 = 3027341) B3027341
theorem B4541021 : Blo 2017435 4541021 := bbase (se 3 (by rfl) ⟨851441, by rfl⟩ : syracuseStep 4541021 = 1702883) (by norm_num)
theorem B3027347 : Blo 2017435 3027347 := bstep (se 1 (by rfl) ⟨2270510, by rfl⟩ : syracuseStep 3027347 = 4541021) B4541021
theorem B2018231 : Blo 2017435 2018231 := bstep (se 1 (by rfl) ⟨1513673, by rfl⟩ : syracuseStep 2018231 = 3027347) B3027347
theorem B3405773 : Blo 2017435 3405773 := bbase (se 3 (by rfl) ⟨638582, by rfl⟩ : syracuseStep 3405773 = 1277165) (by norm_num)
theorem B2270515 : Blo 2017435 2270515 := bstep (se 1 (by rfl) ⟨1702886, by rfl⟩ : syracuseStep 2270515 = 3405773) B3405773
theorem B3027353 : Blo 2017435 3027353 := bstep (se 2 (by rfl) ⟨1135257, by rfl⟩ : syracuseStep 3027353 = 2270515) B2270515
theorem B2018235 : Blo 2017435 2018235 := bstep (se 1 (by rfl) ⟨1513676, by rfl⟩ : syracuseStep 2018235 = 3027353) B3027353
theorem B46074197 : Blo 2017435 46074197 := bbase (se 10 (by rfl) ⟨67491, by rfl⟩ : syracuseStep 46074197 = 134983) (by norm_num)
theorem B30716131 : Blo 2017435 30716131 := bstep (se 1 (by rfl) ⟨23037098, by rfl⟩ : syracuseStep 30716131 = 46074197) B46074197
theorem B40954841 : Blo 2017435 40954841 := bstep (se 2 (by rfl) ⟨15358065, by rfl⟩ : syracuseStep 40954841 = 30716131) B30716131
theorem B27303227 : Blo 2017435 27303227 := bstep (se 1 (by rfl) ⟨20477420, by rfl⟩ : syracuseStep 27303227 = 40954841) B40954841
theorem B18202151 : Blo 2017435 18202151 := bstep (se 1 (by rfl) ⟨13651613, by rfl⟩ : syracuseStep 18202151 = 27303227) B27303227
theorem B12134767 : Blo 2017435 12134767 := bstep (se 1 (by rfl) ⟨9101075, by rfl⟩ : syracuseStep 12134767 = 18202151) B18202151
theorem B16179689 : Blo 2017435 16179689 := bstep (se 2 (by rfl) ⟨6067383, by rfl⟩ : syracuseStep 16179689 = 12134767) B12134767
theorem B10786459 : Blo 2017435 10786459 := bstep (se 1 (by rfl) ⟨8089844, by rfl⟩ : syracuseStep 10786459 = 16179689) B16179689
theorem B14381945 : Blo 2017435 14381945 := bstep (se 2 (by rfl) ⟨5393229, by rfl⟩ : syracuseStep 14381945 = 10786459) B10786459
theorem B9587963 : Blo 2017435 9587963 := bstep (se 1 (by rfl) ⟨7190972, by rfl⟩ : syracuseStep 9587963 = 14381945) B14381945
theorem B6391975 : Blo 2017435 6391975 := bstep (se 1 (by rfl) ⟨4793981, by rfl⟩ : syracuseStep 6391975 = 9587963) B9587963
theorem B136362133 : Blo 2017435 136362133 := bstep (se 6 (by rfl) ⟨3195987, by rfl⟩ : syracuseStep 136362133 = 6391975) B6391975
theorem B181816177 : Blo 2017435 181816177 := bstep (se 2 (by rfl) ⟨68181066, by rfl⟩ : syracuseStep 181816177 = 136362133) B136362133
theorem B242421569 : Blo 2017435 242421569 := bstep (se 2 (by rfl) ⟨90908088, by rfl⟩ : syracuseStep 242421569 = 181816177) B181816177
theorem B161614379 : Blo 2017435 161614379 := bstep (se 1 (by rfl) ⟨121210784, by rfl⟩ : syracuseStep 161614379 = 242421569) B242421569
theorem B107742919 : Blo 2017435 107742919 := bstep (se 1 (by rfl) ⟨80807189, by rfl⟩ : syracuseStep 107742919 = 161614379) B161614379
theorem B143657225 : Blo 2017435 143657225 := bstep (se 2 (by rfl) ⟨53871459, by rfl⟩ : syracuseStep 143657225 = 107742919) B107742919
theorem B95771483 : Blo 2017435 95771483 := bstep (se 1 (by rfl) ⟨71828612, by rfl⟩ : syracuseStep 95771483 = 143657225) B143657225
theorem B63847655 : Blo 2017435 63847655 := bstep (se 1 (by rfl) ⟨47885741, by rfl⟩ : syracuseStep 63847655 = 95771483) B95771483
theorem B42565103 : Blo 2017435 42565103 := bstep (se 1 (by rfl) ⟨31923827, by rfl⟩ : syracuseStep 42565103 = 63847655) B63847655
theorem B28376735 : Blo 2017435 28376735 := bstep (se 1 (by rfl) ⟨21282551, by rfl⟩ : syracuseStep 28376735 = 42565103) B42565103
theorem B75671293 : Blo 2017435 75671293 := bstep (se 3 (by rfl) ⟨14188367, by rfl⟩ : syracuseStep 75671293 = 28376735) B28376735
theorem B100895057 : Blo 2017435 100895057 := bstep (se 2 (by rfl) ⟨37835646, by rfl⟩ : syracuseStep 100895057 = 75671293) B75671293
theorem B67263371 : Blo 2017435 67263371 := bstep (se 1 (by rfl) ⟨50447528, by rfl⟩ : syracuseStep 67263371 = 100895057) B100895057
theorem B44842247 : Blo 2017435 44842247 := bstep (se 1 (by rfl) ⟨33631685, by rfl⟩ : syracuseStep 44842247 = 67263371) B67263371
theorem B29894831 : Blo 2017435 29894831 := bstep (se 1 (by rfl) ⟨22421123, by rfl⟩ : syracuseStep 29894831 = 44842247) B44842247
theorem B19929887 : Blo 2017435 19929887 := bstep (se 1 (by rfl) ⟨14947415, by rfl⟩ : syracuseStep 19929887 = 29894831) B29894831
theorem B13286591 : Blo 2017435 13286591 := bstep (se 1 (by rfl) ⟨9964943, by rfl⟩ : syracuseStep 13286591 = 19929887) B19929887
theorem B8857727 : Blo 2017435 8857727 := bstep (se 1 (by rfl) ⟨6643295, by rfl⟩ : syracuseStep 8857727 = 13286591) B13286591
theorem B5905151 : Blo 2017435 5905151 := bstep (se 1 (by rfl) ⟨4428863, by rfl⟩ : syracuseStep 5905151 = 8857727) B8857727
theorem B3936767 : Blo 2017435 3936767 := bstep (se 1 (by rfl) ⟨2952575, by rfl⟩ : syracuseStep 3936767 = 5905151) B5905151
theorem B10498045 : Blo 2017435 10498045 := bstep (se 3 (by rfl) ⟨1968383, by rfl⟩ : syracuseStep 10498045 = 3936767) B3936767
theorem B13997393 : Blo 2017435 13997393 := bstep (se 2 (by rfl) ⟨5249022, by rfl⟩ : syracuseStep 13997393 = 10498045) B10498045
theorem B9331595 : Blo 2017435 9331595 := bstep (se 1 (by rfl) ⟨6998696, by rfl⟩ : syracuseStep 9331595 = 13997393) B13997393
theorem B6221063 : Blo 2017435 6221063 := bstep (se 1 (by rfl) ⟨4665797, by rfl⟩ : syracuseStep 6221063 = 9331595) B9331595
theorem B4147375 : Blo 2017435 4147375 := bstep (se 1 (by rfl) ⟨3110531, by rfl⟩ : syracuseStep 4147375 = 6221063) B6221063
theorem B5529833 : Blo 2017435 5529833 := bstep (se 2 (by rfl) ⟨2073687, by rfl⟩ : syracuseStep 5529833 = 4147375) B4147375
theorem B3686555 : Blo 2017435 3686555 := bstep (se 1 (by rfl) ⟨2764916, by rfl⟩ : syracuseStep 3686555 = 5529833) B5529833
theorem B9830813 : Blo 2017435 9830813 := bstep (se 3 (by rfl) ⟨1843277, by rfl⟩ : syracuseStep 9830813 = 3686555) B3686555
theorem B26215501 : Blo 2017435 26215501 := bstep (se 3 (by rfl) ⟨4915406, by rfl⟩ : syracuseStep 26215501 = 9830813) B9830813
theorem B34954001 : Blo 2017435 34954001 := bstep (se 2 (by rfl) ⟨13107750, by rfl⟩ : syracuseStep 34954001 = 26215501) B26215501
theorem B23302667 : Blo 2017435 23302667 := bstep (se 1 (by rfl) ⟨17477000, by rfl⟩ : syracuseStep 23302667 = 34954001) B34954001
theorem B15535111 : Blo 2017435 15535111 := bstep (se 1 (by rfl) ⟨11651333, by rfl⟩ : syracuseStep 15535111 = 23302667) B23302667
theorem B20713481 : Blo 2017435 20713481 := bstep (se 2 (by rfl) ⟨7767555, by rfl⟩ : syracuseStep 20713481 = 15535111) B15535111
theorem B13808987 : Blo 2017435 13808987 := bstep (se 1 (by rfl) ⟨10356740, by rfl⟩ : syracuseStep 13808987 = 20713481) B20713481
theorem B9205991 : Blo 2017435 9205991 := bstep (se 1 (by rfl) ⟨6904493, by rfl⟩ : syracuseStep 9205991 = 13808987) B13808987
theorem B6137327 : Blo 2017435 6137327 := bstep (se 1 (by rfl) ⟨4602995, by rfl⟩ : syracuseStep 6137327 = 9205991) B9205991
theorem B16366205 : Blo 2017435 16366205 := bstep (se 3 (by rfl) ⟨3068663, by rfl⟩ : syracuseStep 16366205 = 6137327) B6137327
theorem B10910803 : Blo 2017435 10910803 := bstep (se 1 (by rfl) ⟨8183102, by rfl⟩ : syracuseStep 10910803 = 16366205) B16366205
theorem B14547737 : Blo 2017435 14547737 := bstep (se 2 (by rfl) ⟨5455401, by rfl⟩ : syracuseStep 14547737 = 10910803) B10910803
theorem B9698491 : Blo 2017435 9698491 := bstep (se 1 (by rfl) ⟨7273868, by rfl⟩ : syracuseStep 9698491 = 14547737) B14547737
theorem B12931321 : Blo 2017435 12931321 := bstep (se 2 (by rfl) ⟨4849245, by rfl⟩ : syracuseStep 12931321 = 9698491) B9698491
theorem B17241761 : Blo 2017435 17241761 := bstep (se 2 (by rfl) ⟨6465660, by rfl⟩ : syracuseStep 17241761 = 12931321) B12931321
theorem B11494507 : Blo 2017435 11494507 := bstep (se 1 (by rfl) ⟨8620880, by rfl⟩ : syracuseStep 11494507 = 17241761) B17241761
theorem B15326009 : Blo 2017435 15326009 := bstep (se 2 (by rfl) ⟨5747253, by rfl⟩ : syracuseStep 15326009 = 11494507) B11494507
theorem B10217339 : Blo 2017435 10217339 := bstep (se 1 (by rfl) ⟨7663004, by rfl⟩ : syracuseStep 10217339 = 15326009) B15326009
theorem B6811559 : Blo 2017435 6811559 := bstep (se 1 (by rfl) ⟨5108669, by rfl⟩ : syracuseStep 6811559 = 10217339) B10217339
theorem B4541039 : Blo 2017435 4541039 := bstep (se 1 (by rfl) ⟨3405779, by rfl⟩ : syracuseStep 4541039 = 6811559) B6811559
theorem B3027359 : Blo 2017435 3027359 := bstep (se 1 (by rfl) ⟨2270519, by rfl⟩ : syracuseStep 3027359 = 4541039) B4541039
theorem B2018239 : Blo 2017435 2018239 := bstep (se 1 (by rfl) ⟨1513679, by rfl⟩ : syracuseStep 2018239 = 3027359) B3027359
theorem B3027365 : Blo 2017435 3027365 := bbase (se 4 (by rfl) ⟨283815, by rfl⟩ : syracuseStep 3027365 = 567631) (by norm_num)
theorem B2018243 : Blo 2017435 2018243 := bstep (se 1 (by rfl) ⟨1513682, by rfl⟩ : syracuseStep 2018243 = 3027365) B3027365
theorem B2554345 : Blo 2017435 2554345 := bbase (se 2 (by rfl) ⟨957879, by rfl⟩ : syracuseStep 2554345 = 1915759) (by norm_num)
theorem B3405793 : Blo 2017435 3405793 := bstep (se 2 (by rfl) ⟨1277172, by rfl⟩ : syracuseStep 3405793 = 2554345) B2554345
theorem B4541057 : Blo 2017435 4541057 := bstep (se 2 (by rfl) ⟨1702896, by rfl⟩ : syracuseStep 4541057 = 3405793) B3405793
theorem B3027371 : Blo 2017435 3027371 := bstep (se 1 (by rfl) ⟨2270528, by rfl⟩ : syracuseStep 3027371 = 4541057) B4541057
theorem B2018247 : Blo 2017435 2018247 := bstep (se 1 (by rfl) ⟨1513685, by rfl⟩ : syracuseStep 2018247 = 3027371) B3027371
theorem B2270533 : Blo 2017435 2270533 := bbase (se 4 (by rfl) ⟨212862, by rfl⟩ : syracuseStep 2270533 = 425725) (by norm_num)
theorem B3027377 : Blo 2017435 3027377 := bstep (se 2 (by rfl) ⟨1135266, by rfl⟩ : syracuseStep 3027377 = 2270533) B2270533
theorem B2018251 : Blo 2017435 2018251 := bstep (se 1 (by rfl) ⟨1513688, by rfl⟩ : syracuseStep 2018251 = 3027377) B3027377
theorem B3831533 : Blo 2017435 3831533 := bbase (se 3 (by rfl) ⟨718412, by rfl⟩ : syracuseStep 3831533 = 1436825) (by norm_num)
theorem B2554355 : Blo 2017435 2554355 := bstep (se 1 (by rfl) ⟨1915766, by rfl⟩ : syracuseStep 2554355 = 3831533) B3831533
theorem B6811613 : Blo 2017435 6811613 := bstep (se 3 (by rfl) ⟨1277177, by rfl⟩ : syracuseStep 6811613 = 2554355) B2554355
theorem B4541075 : Blo 2017435 4541075 := bstep (se 1 (by rfl) ⟨3405806, by rfl⟩ : syracuseStep 4541075 = 6811613) B6811613
theorem B3027383 : Blo 2017435 3027383 := bstep (se 1 (by rfl) ⟨2270537, by rfl⟩ : syracuseStep 3027383 = 4541075) B4541075
theorem B2018255 : Blo 2017435 2018255 := bstep (se 1 (by rfl) ⟨1513691, by rfl⟩ : syracuseStep 2018255 = 3027383) B3027383
theorem B3027389 : Blo 2017435 3027389 := bbase (se 3 (by rfl) ⟨567635, by rfl⟩ : syracuseStep 3027389 = 1135271) (by norm_num)
theorem B2018259 : Blo 2017435 2018259 := bstep (se 1 (by rfl) ⟨1513694, by rfl⟩ : syracuseStep 2018259 = 3027389) B3027389
theorem B4541093 : Blo 2017435 4541093 := bbase (se 4 (by rfl) ⟨425727, by rfl⟩ : syracuseStep 4541093 = 851455) (by norm_num)
theorem B3027395 : Blo 2017435 3027395 := bstep (se 1 (by rfl) ⟨2270546, by rfl⟩ : syracuseStep 3027395 = 4541093) B4541093
theorem B2018263 : Blo 2017435 2018263 := bstep (se 1 (by rfl) ⟨1513697, by rfl⟩ : syracuseStep 2018263 = 3027395) B3027395
theorem B5108741 : Blo 2017435 5108741 := bbase (se 4 (by rfl) ⟨478944, by rfl⟩ : syracuseStep 5108741 = 957889) (by norm_num)
theorem B3405827 : Blo 2017435 3405827 := bstep (se 1 (by rfl) ⟨2554370, by rfl⟩ : syracuseStep 3405827 = 5108741) B5108741
theorem B2270551 : Blo 2017435 2270551 := bstep (se 1 (by rfl) ⟨1702913, by rfl⟩ : syracuseStep 2270551 = 3405827) B3405827
theorem B3027401 : Blo 2017435 3027401 := bstep (se 2 (by rfl) ⟨1135275, by rfl⟩ : syracuseStep 3027401 = 2270551) B2270551
theorem B2018267 : Blo 2017435 2018267 := bstep (se 1 (by rfl) ⟨1513700, by rfl⟩ : syracuseStep 2018267 = 3027401) B3027401
theorem B4310509 : Blo 2017435 4310509 := bbase (se 3 (by rfl) ⟨808220, by rfl⟩ : syracuseStep 4310509 = 1616441) (by norm_num)
theorem B5747345 : Blo 2017435 5747345 := bstep (se 2 (by rfl) ⟨2155254, by rfl⟩ : syracuseStep 5747345 = 4310509) B4310509
theorem B3831563 : Blo 2017435 3831563 := bstep (se 1 (by rfl) ⟨2873672, by rfl⟩ : syracuseStep 3831563 = 5747345) B5747345
theorem B10217501 : Blo 2017435 10217501 := bstep (se 3 (by rfl) ⟨1915781, by rfl⟩ : syracuseStep 10217501 = 3831563) B3831563
theorem B6811667 : Blo 2017435 6811667 := bstep (se 1 (by rfl) ⟨5108750, by rfl⟩ : syracuseStep 6811667 = 10217501) B10217501
theorem B4541111 : Blo 2017435 4541111 := bstep (se 1 (by rfl) ⟨3405833, by rfl⟩ : syracuseStep 4541111 = 6811667) B6811667
theorem B3027407 : Blo 2017435 3027407 := bstep (se 1 (by rfl) ⟨2270555, by rfl⟩ : syracuseStep 3027407 = 4541111) B4541111
theorem B2018271 : Blo 2017435 2018271 := bstep (se 1 (by rfl) ⟨1513703, by rfl⟩ : syracuseStep 2018271 = 3027407) B3027407
theorem B3027413 : Blo 2017435 3027413 := bbase (se 7 (by rfl) ⟨35477, by rfl⟩ : syracuseStep 3027413 = 70955) (by norm_num)
theorem B2018275 : Blo 2017435 2018275 := bstep (se 1 (by rfl) ⟨1513706, by rfl⟩ : syracuseStep 2018275 = 3027413) B3027413
theorem B7663157 : Blo 2017435 7663157 := bbase (se 5 (by rfl) ⟨359210, by rfl⟩ : syracuseStep 7663157 = 718421) (by norm_num)
theorem B5108771 : Blo 2017435 5108771 := bstep (se 1 (by rfl) ⟨3831578, by rfl⟩ : syracuseStep 5108771 = 7663157) B7663157
theorem B3405847 : Blo 2017435 3405847 := bstep (se 1 (by rfl) ⟨2554385, by rfl⟩ : syracuseStep 3405847 = 5108771) B5108771
theorem B4541129 : Blo 2017435 4541129 := bstep (se 2 (by rfl) ⟨1702923, by rfl⟩ : syracuseStep 4541129 = 3405847) B3405847
theorem B3027419 : Blo 2017435 3027419 := bstep (se 1 (by rfl) ⟨2270564, by rfl⟩ : syracuseStep 3027419 = 4541129) B4541129
theorem B2018279 : Blo 2017435 2018279 := bstep (se 1 (by rfl) ⟨1513709, by rfl⟩ : syracuseStep 2018279 = 3027419) B3027419
theorem B2270569 : Blo 2017435 2270569 := bbase (se 2 (by rfl) ⟨851463, by rfl⟩ : syracuseStep 2270569 = 1702927) (by norm_num)
theorem B3027425 : Blo 2017435 3027425 := bstep (se 2 (by rfl) ⟨1135284, by rfl⟩ : syracuseStep 3027425 = 2270569) B2270569
theorem B2018283 : Blo 2017435 2018283 := bstep (se 1 (by rfl) ⟨1513712, by rfl⟩ : syracuseStep 2018283 = 3027425) B3027425
theorem B14548085 : Blo 2017435 14548085 := bbase (se 5 (by rfl) ⟨681941, by rfl⟩ : syracuseStep 14548085 = 1363883) (by norm_num)
theorem B9698723 : Blo 2017435 9698723 := bstep (se 1 (by rfl) ⟨7274042, by rfl⟩ : syracuseStep 9698723 = 14548085) B14548085
theorem B6465815 : Blo 2017435 6465815 := bstep (se 1 (by rfl) ⟨4849361, by rfl⟩ : syracuseStep 6465815 = 9698723) B9698723
theorem B4310543 : Blo 2017435 4310543 := bstep (se 1 (by rfl) ⟨3232907, by rfl⟩ : syracuseStep 4310543 = 6465815) B6465815
theorem B11494781 : Blo 2017435 11494781 := bstep (se 3 (by rfl) ⟨2155271, by rfl⟩ : syracuseStep 11494781 = 4310543) B4310543
theorem B7663187 : Blo 2017435 7663187 := bstep (se 1 (by rfl) ⟨5747390, by rfl⟩ : syracuseStep 7663187 = 11494781) B11494781
theorem B5108791 : Blo 2017435 5108791 := bstep (se 1 (by rfl) ⟨3831593, by rfl⟩ : syracuseStep 5108791 = 7663187) B7663187
theorem B6811721 : Blo 2017435 6811721 := bstep (se 2 (by rfl) ⟨2554395, by rfl⟩ : syracuseStep 6811721 = 5108791) B5108791
theorem B4541147 : Blo 2017435 4541147 := bstep (se 1 (by rfl) ⟨3405860, by rfl⟩ : syracuseStep 4541147 = 6811721) B6811721
theorem B3027431 : Blo 2017435 3027431 := bstep (se 1 (by rfl) ⟨2270573, by rfl⟩ : syracuseStep 3027431 = 4541147) B4541147
theorem B2018287 : Blo 2017435 2018287 := bstep (se 1 (by rfl) ⟨1513715, by rfl⟩ : syracuseStep 2018287 = 3027431) B3027431
theorem B3027437 : Blo 2017435 3027437 := bbase (se 3 (by rfl) ⟨567644, by rfl⟩ : syracuseStep 3027437 = 1135289) (by norm_num)
theorem B2018291 : Blo 2017435 2018291 := bstep (se 1 (by rfl) ⟨1513718, by rfl⟩ : syracuseStep 2018291 = 3027437) B3027437
theorem B4541165 : Blo 2017435 4541165 := bbase (se 3 (by rfl) ⟨851468, by rfl⟩ : syracuseStep 4541165 = 1702937) (by norm_num)
theorem B3027443 : Blo 2017435 3027443 := bstep (se 1 (by rfl) ⟨2270582, by rfl⟩ : syracuseStep 3027443 = 4541165) B4541165
theorem B2018295 : Blo 2017435 2018295 := bstep (se 1 (by rfl) ⟨1513721, by rfl⟩ : syracuseStep 2018295 = 3027443) B3027443
theorem B2155285 : Blo 2017435 2155285 := bbase (se 6 (by rfl) ⟨50514, by rfl⟩ : syracuseStep 2155285 = 101029) (by norm_num)
theorem B2873713 : Blo 2017435 2873713 := bstep (se 2 (by rfl) ⟨1077642, by rfl⟩ : syracuseStep 2873713 = 2155285) B2155285
theorem B3831617 : Blo 2017435 3831617 := bstep (se 2 (by rfl) ⟨1436856, by rfl⟩ : syracuseStep 3831617 = 2873713) B2873713
theorem B2554411 : Blo 2017435 2554411 := bstep (se 1 (by rfl) ⟨1915808, by rfl⟩ : syracuseStep 2554411 = 3831617) B3831617
theorem B3405881 : Blo 2017435 3405881 := bstep (se 2 (by rfl) ⟨1277205, by rfl⟩ : syracuseStep 3405881 = 2554411) B2554411
theorem B2270587 : Blo 2017435 2270587 := bstep (se 1 (by rfl) ⟨1702940, by rfl⟩ : syracuseStep 2270587 = 3405881) B3405881
theorem B3027449 : Blo 2017435 3027449 := bstep (se 2 (by rfl) ⟨1135293, by rfl⟩ : syracuseStep 3027449 = 2270587) B2270587
theorem B2018299 : Blo 2017435 2018299 := bstep (se 1 (by rfl) ⟨1513724, by rfl⟩ : syracuseStep 2018299 = 3027449) B3027449
theorem B3452357 : Blo 2017435 3452357 := bbase (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) (by norm_num)
theorem B2301571 : Blo 2017435 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B3068761 : Blo 2017435 3068761 := bstep (se 2 (by rfl) ⟨1150785, by rfl⟩ : syracuseStep 3068761 = 2301571) B2301571
theorem B4091681 : Blo 2017435 4091681 := bstep (se 2 (by rfl) ⟨1534380, by rfl⟩ : syracuseStep 4091681 = 3068761) B3068761
theorem B2727787 : Blo 2017435 2727787 := bstep (se 1 (by rfl) ⟨2045840, by rfl⟩ : syracuseStep 2727787 = 4091681) B4091681
theorem B58192789 : Blo 2017435 58192789 := bstep (se 6 (by rfl) ⟨1363893, by rfl⟩ : syracuseStep 58192789 = 2727787) B2727787
theorem B77590385 : Blo 2017435 77590385 := bstep (se 2 (by rfl) ⟨29096394, by rfl⟩ : syracuseStep 77590385 = 58192789) B58192789
theorem B51726923 : Blo 2017435 51726923 := bstep (se 1 (by rfl) ⟨38795192, by rfl⟩ : syracuseStep 51726923 = 77590385) B77590385
theorem B34484615 : Blo 2017435 34484615 := bstep (se 1 (by rfl) ⟨25863461, by rfl⟩ : syracuseStep 34484615 = 51726923) B51726923
theorem B22989743 : Blo 2017435 22989743 := bstep (se 1 (by rfl) ⟨17242307, by rfl⟩ : syracuseStep 22989743 = 34484615) B34484615
theorem B15326495 : Blo 2017435 15326495 := bstep (se 1 (by rfl) ⟨11494871, by rfl⟩ : syracuseStep 15326495 = 22989743) B22989743
theorem B10217663 : Blo 2017435 10217663 := bstep (se 1 (by rfl) ⟨7663247, by rfl⟩ : syracuseStep 10217663 = 15326495) B15326495
theorem B6811775 : Blo 2017435 6811775 := bstep (se 1 (by rfl) ⟨5108831, by rfl⟩ : syracuseStep 6811775 = 10217663) B10217663
theorem B4541183 : Blo 2017435 4541183 := bstep (se 1 (by rfl) ⟨3405887, by rfl⟩ : syracuseStep 4541183 = 6811775) B6811775
theorem B3027455 : Blo 2017435 3027455 := bstep (se 1 (by rfl) ⟨2270591, by rfl⟩ : syracuseStep 3027455 = 4541183) B4541183
theorem B2018303 : Blo 2017435 2018303 := bstep (se 1 (by rfl) ⟨1513727, by rfl⟩ : syracuseStep 2018303 = 3027455) B3027455
theorem B3027461 : Blo 2017435 3027461 := bbase (se 4 (by rfl) ⟨283824, by rfl⟩ : syracuseStep 3027461 = 567649) (by norm_num)
theorem B2018307 : Blo 2017435 2018307 := bstep (se 1 (by rfl) ⟨1513730, by rfl⟩ : syracuseStep 2018307 = 3027461) B3027461
theorem B3405901 : Blo 2017435 3405901 := bbase (se 3 (by rfl) ⟨638606, by rfl⟩ : syracuseStep 3405901 = 1277213) (by norm_num)
theorem B4541201 : Blo 2017435 4541201 := bstep (se 2 (by rfl) ⟨1702950, by rfl⟩ : syracuseStep 4541201 = 3405901) B3405901
theorem B3027467 : Blo 2017435 3027467 := bstep (se 1 (by rfl) ⟨2270600, by rfl⟩ : syracuseStep 3027467 = 4541201) B4541201
theorem B2018311 : Blo 2017435 2018311 := bstep (se 1 (by rfl) ⟨1513733, by rfl⟩ : syracuseStep 2018311 = 3027467) B3027467
theorem B2270605 : Blo 2017435 2270605 := bbase (se 3 (by rfl) ⟨425738, by rfl⟩ : syracuseStep 2270605 = 851477) (by norm_num)
theorem B3027473 : Blo 2017435 3027473 := bstep (se 2 (by rfl) ⟨1135302, by rfl⟩ : syracuseStep 3027473 = 2270605) B2270605
theorem B2018315 : Blo 2017435 2018315 := bstep (se 1 (by rfl) ⟨1513736, by rfl⟩ : syracuseStep 2018315 = 3027473) B3027473
theorem B6811829 : Blo 2017435 6811829 := bbase (se 5 (by rfl) ⟨319304, by rfl⟩ : syracuseStep 6811829 = 638609) (by norm_num)
theorem B4541219 : Blo 2017435 4541219 := bstep (se 1 (by rfl) ⟨3405914, by rfl⟩ : syracuseStep 4541219 = 6811829) B6811829
theorem B3027479 : Blo 2017435 3027479 := bstep (se 1 (by rfl) ⟨2270609, by rfl⟩ : syracuseStep 3027479 = 4541219) B4541219
theorem B2018319 : Blo 2017435 2018319 := bstep (se 1 (by rfl) ⟨1513739, by rfl⟩ : syracuseStep 2018319 = 3027479) B3027479
theorem B3027485 : Blo 2017435 3027485 := bbase (se 3 (by rfl) ⟨567653, by rfl⟩ : syracuseStep 3027485 = 1135307) (by norm_num)
theorem B2018323 : Blo 2017435 2018323 := bstep (se 1 (by rfl) ⟨1513742, by rfl⟩ : syracuseStep 2018323 = 3027485) B3027485
theorem B4541237 : Blo 2017435 4541237 := bbase (se 5 (by rfl) ⟨212870, by rfl⟩ : syracuseStep 4541237 = 425741) (by norm_num)
theorem B3027491 : Blo 2017435 3027491 := bstep (se 1 (by rfl) ⟨2270618, by rfl⟩ : syracuseStep 3027491 = 4541237) B4541237
theorem B2018327 : Blo 2017435 2018327 := bstep (se 1 (by rfl) ⟨1513745, by rfl⟩ : syracuseStep 2018327 = 3027491) B3027491
theorem B8183477 : Blo 2017435 8183477 := bbase (se 5 (by rfl) ⟨383600, by rfl⟩ : syracuseStep 8183477 = 767201) (by norm_num)
theorem B21822605 : Blo 2017435 21822605 := bstep (se 3 (by rfl) ⟨4091738, by rfl⟩ : syracuseStep 21822605 = 8183477) B8183477
theorem B14548403 : Blo 2017435 14548403 := bstep (se 1 (by rfl) ⟨10911302, by rfl⟩ : syracuseStep 14548403 = 21822605) B21822605
theorem B9698935 : Blo 2017435 9698935 := bstep (se 1 (by rfl) ⟨7274201, by rfl⟩ : syracuseStep 9698935 = 14548403) B14548403
theorem B12931913 : Blo 2017435 12931913 := bstep (se 2 (by rfl) ⟨4849467, by rfl⟩ : syracuseStep 12931913 = 9698935) B9698935
theorem B8621275 : Blo 2017435 8621275 := bstep (se 1 (by rfl) ⟨6465956, by rfl⟩ : syracuseStep 8621275 = 12931913) B12931913
theorem B11495033 : Blo 2017435 11495033 := bstep (se 2 (by rfl) ⟨4310637, by rfl⟩ : syracuseStep 11495033 = 8621275) B8621275
theorem B7663355 : Blo 2017435 7663355 := bstep (se 1 (by rfl) ⟨5747516, by rfl⟩ : syracuseStep 7663355 = 11495033) B11495033
theorem B5108903 : Blo 2017435 5108903 := bstep (se 1 (by rfl) ⟨3831677, by rfl⟩ : syracuseStep 5108903 = 7663355) B7663355
theorem B3405935 : Blo 2017435 3405935 := bstep (se 1 (by rfl) ⟨2554451, by rfl⟩ : syracuseStep 3405935 = 5108903) B5108903
theorem B2270623 : Blo 2017435 2270623 := bstep (se 1 (by rfl) ⟨1702967, by rfl⟩ : syracuseStep 2270623 = 3405935) B3405935
theorem B3027497 : Blo 2017435 3027497 := bstep (se 2 (by rfl) ⟨1135311, by rfl⟩ : syracuseStep 3027497 = 2270623) B2270623
theorem B2018331 : Blo 2017435 2018331 := bstep (se 1 (by rfl) ⟨1513748, by rfl⟩ : syracuseStep 2018331 = 3027497) B3027497
theorem B31071701 : Blo 2017435 31071701 := bbase (se 7 (by rfl) ⟨364121, by rfl⟩ : syracuseStep 31071701 = 728243) (by norm_num)
theorem B20714467 : Blo 2017435 20714467 := bstep (se 1 (by rfl) ⟨15535850, by rfl⟩ : syracuseStep 20714467 = 31071701) B31071701
theorem B27619289 : Blo 2017435 27619289 := bstep (se 2 (by rfl) ⟨10357233, by rfl⟩ : syracuseStep 27619289 = 20714467) B20714467
theorem B18412859 : Blo 2017435 18412859 := bstep (se 1 (by rfl) ⟨13809644, by rfl⟩ : syracuseStep 18412859 = 27619289) B27619289
theorem B12275239 : Blo 2017435 12275239 := bstep (se 1 (by rfl) ⟨9206429, by rfl⟩ : syracuseStep 12275239 = 18412859) B18412859
theorem B16366985 : Blo 2017435 16366985 := bstep (se 2 (by rfl) ⟨6137619, by rfl⟩ : syracuseStep 16366985 = 12275239) B12275239
theorem B10911323 : Blo 2017435 10911323 := bstep (se 1 (by rfl) ⟨8183492, by rfl⟩ : syracuseStep 10911323 = 16366985) B16366985
theorem B7274215 : Blo 2017435 7274215 := bstep (se 1 (by rfl) ⟨5455661, by rfl⟩ : syracuseStep 7274215 = 10911323) B10911323
theorem B9698953 : Blo 2017435 9698953 := bstep (se 2 (by rfl) ⟨3637107, by rfl⟩ : syracuseStep 9698953 = 7274215) B7274215
theorem B12931937 : Blo 2017435 12931937 := bstep (se 2 (by rfl) ⟨4849476, by rfl⟩ : syracuseStep 12931937 = 9698953) B9698953
theorem B8621291 : Blo 2017435 8621291 := bstep (se 1 (by rfl) ⟨6465968, by rfl⟩ : syracuseStep 8621291 = 12931937) B12931937
theorem B5747527 : Blo 2017435 5747527 := bstep (se 1 (by rfl) ⟨4310645, by rfl⟩ : syracuseStep 5747527 = 8621291) B8621291
theorem B7663369 : Blo 2017435 7663369 := bstep (se 2 (by rfl) ⟨2873763, by rfl⟩ : syracuseStep 7663369 = 5747527) B5747527
theorem B10217825 : Blo 2017435 10217825 := bstep (se 2 (by rfl) ⟨3831684, by rfl⟩ : syracuseStep 10217825 = 7663369) B7663369
theorem B6811883 : Blo 2017435 6811883 := bstep (se 1 (by rfl) ⟨5108912, by rfl⟩ : syracuseStep 6811883 = 10217825) B10217825
theorem B4541255 : Blo 2017435 4541255 := bstep (se 1 (by rfl) ⟨3405941, by rfl⟩ : syracuseStep 4541255 = 6811883) B6811883
theorem B3027503 : Blo 2017435 3027503 := bstep (se 1 (by rfl) ⟨2270627, by rfl⟩ : syracuseStep 3027503 = 4541255) B4541255
theorem B2018335 : Blo 2017435 2018335 := bstep (se 1 (by rfl) ⟨1513751, by rfl⟩ : syracuseStep 2018335 = 3027503) B3027503
theorem B3027509 : Blo 2017435 3027509 := bbase (se 5 (by rfl) ⟨141914, by rfl⟩ : syracuseStep 3027509 = 283829) (by norm_num)
theorem B2018339 : Blo 2017435 2018339 := bstep (se 1 (by rfl) ⟨1513754, by rfl⟩ : syracuseStep 2018339 = 3027509) B3027509
theorem B5108933 : Blo 2017435 5108933 := bbase (se 4 (by rfl) ⟨478962, by rfl⟩ : syracuseStep 5108933 = 957925) (by norm_num)
theorem B3405955 : Blo 2017435 3405955 := bstep (se 1 (by rfl) ⟨2554466, by rfl⟩ : syracuseStep 3405955 = 5108933) B5108933
theorem B4541273 : Blo 2017435 4541273 := bstep (se 2 (by rfl) ⟨1702977, by rfl⟩ : syracuseStep 4541273 = 3405955) B3405955
theorem B3027515 : Blo 2017435 3027515 := bstep (se 1 (by rfl) ⟨2270636, by rfl⟩ : syracuseStep 3027515 = 4541273) B4541273
theorem B2018343 : Blo 2017435 2018343 := bstep (se 1 (by rfl) ⟨1513757, by rfl⟩ : syracuseStep 2018343 = 3027515) B3027515
theorem B2270641 : Blo 2017435 2270641 := bbase (se 2 (by rfl) ⟨851490, by rfl⟩ : syracuseStep 2270641 = 1702981) (by norm_num)
theorem B3027521 : Blo 2017435 3027521 := bstep (se 2 (by rfl) ⟨1135320, by rfl⟩ : syracuseStep 3027521 = 2270641) B2270641
theorem B2018347 : Blo 2017435 2018347 := bstep (se 1 (by rfl) ⟨1513760, by rfl⟩ : syracuseStep 2018347 = 3027521) B3027521
theorem B5747573 : Blo 2017435 5747573 := bbase (se 5 (by rfl) ⟨269417, by rfl⟩ : syracuseStep 5747573 = 538835) (by norm_num)
theorem B3831715 : Blo 2017435 3831715 := bstep (se 1 (by rfl) ⟨2873786, by rfl⟩ : syracuseStep 3831715 = 5747573) B5747573
theorem B5108953 : Blo 2017435 5108953 := bstep (se 2 (by rfl) ⟨1915857, by rfl⟩ : syracuseStep 5108953 = 3831715) B3831715
theorem B6811937 : Blo 2017435 6811937 := bstep (se 2 (by rfl) ⟨2554476, by rfl⟩ : syracuseStep 6811937 = 5108953) B5108953
theorem B4541291 : Blo 2017435 4541291 := bstep (se 1 (by rfl) ⟨3405968, by rfl⟩ : syracuseStep 4541291 = 6811937) B6811937
theorem B3027527 : Blo 2017435 3027527 := bstep (se 1 (by rfl) ⟨2270645, by rfl⟩ : syracuseStep 3027527 = 4541291) B4541291
theorem B2018351 : Blo 2017435 2018351 := bstep (se 1 (by rfl) ⟨1513763, by rfl⟩ : syracuseStep 2018351 = 3027527) B3027527
theorem B3027533 : Blo 2017435 3027533 := bbase (se 3 (by rfl) ⟨567662, by rfl⟩ : syracuseStep 3027533 = 1135325) (by norm_num)
theorem B2018355 : Blo 2017435 2018355 := bstep (se 1 (by rfl) ⟨1513766, by rfl⟩ : syracuseStep 2018355 = 3027533) B3027533
theorem B4541309 : Blo 2017435 4541309 := bbase (se 3 (by rfl) ⟨851495, by rfl⟩ : syracuseStep 4541309 = 1702991) (by norm_num)
theorem B3027539 : Blo 2017435 3027539 := bstep (se 1 (by rfl) ⟨2270654, by rfl⟩ : syracuseStep 3027539 = 4541309) B4541309
theorem B2018359 : Blo 2017435 2018359 := bstep (se 1 (by rfl) ⟨1513769, by rfl⟩ : syracuseStep 2018359 = 3027539) B3027539
theorem B3405989 : Blo 2017435 3405989 := bbase (se 4 (by rfl) ⟨319311, by rfl⟩ : syracuseStep 3405989 = 638623) (by norm_num)
theorem B2270659 : Blo 2017435 2270659 := bstep (se 1 (by rfl) ⟨1702994, by rfl⟩ : syracuseStep 2270659 = 3405989) B3405989
theorem B3027545 : Blo 2017435 3027545 := bstep (se 2 (by rfl) ⟨1135329, by rfl⟩ : syracuseStep 3027545 = 2270659) B2270659
theorem B2018363 : Blo 2017435 2018363 := bstep (se 1 (by rfl) ⟨1513772, by rfl⟩ : syracuseStep 2018363 = 3027545) B3027545
theorem B2155357 : Blo 2017435 2155357 := bbase (se 3 (by rfl) ⟨404129, by rfl⟩ : syracuseStep 2155357 = 808259) (by norm_num)
theorem B2873809 : Blo 2017435 2873809 := bstep (se 2 (by rfl) ⟨1077678, by rfl⟩ : syracuseStep 2873809 = 2155357) B2155357
theorem B15326981 : Blo 2017435 15326981 := bstep (se 4 (by rfl) ⟨1436904, by rfl⟩ : syracuseStep 15326981 = 2873809) B2873809
theorem B10217987 : Blo 2017435 10217987 := bstep (se 1 (by rfl) ⟨7663490, by rfl⟩ : syracuseStep 10217987 = 15326981) B15326981
theorem B6811991 : Blo 2017435 6811991 := bstep (se 1 (by rfl) ⟨5108993, by rfl⟩ : syracuseStep 6811991 = 10217987) B10217987
theorem B4541327 : Blo 2017435 4541327 := bstep (se 1 (by rfl) ⟨3405995, by rfl⟩ : syracuseStep 4541327 = 6811991) B6811991
theorem B3027551 : Blo 2017435 3027551 := bstep (se 1 (by rfl) ⟨2270663, by rfl⟩ : syracuseStep 3027551 = 4541327) B4541327
theorem B2018367 : Blo 2017435 2018367 := bstep (se 1 (by rfl) ⟨1513775, by rfl⟩ : syracuseStep 2018367 = 3027551) B3027551
theorem B3027557 : Blo 2017435 3027557 := bbase (se 4 (by rfl) ⟨283833, by rfl⟩ : syracuseStep 3027557 = 567667) (by norm_num)
theorem B2018371 : Blo 2017435 2018371 := bstep (se 1 (by rfl) ⟨1513778, by rfl⟩ : syracuseStep 2018371 = 3027557) B3027557
theorem B2873821 : Blo 2017435 2873821 := bbase (se 3 (by rfl) ⟨538841, by rfl⟩ : syracuseStep 2873821 = 1077683) (by norm_num)
theorem B3831761 : Blo 2017435 3831761 := bstep (se 2 (by rfl) ⟨1436910, by rfl⟩ : syracuseStep 3831761 = 2873821) B2873821
theorem B2554507 : Blo 2017435 2554507 := bstep (se 1 (by rfl) ⟨1915880, by rfl⟩ : syracuseStep 2554507 = 3831761) B3831761
theorem B3406009 : Blo 2017435 3406009 := bstep (se 2 (by rfl) ⟨1277253, by rfl⟩ : syracuseStep 3406009 = 2554507) B2554507
theorem B4541345 : Blo 2017435 4541345 := bstep (se 2 (by rfl) ⟨1703004, by rfl⟩ : syracuseStep 4541345 = 3406009) B3406009
theorem B3027563 : Blo 2017435 3027563 := bstep (se 1 (by rfl) ⟨2270672, by rfl⟩ : syracuseStep 3027563 = 4541345) B4541345
theorem B2018375 : Blo 2017435 2018375 := bstep (se 1 (by rfl) ⟨1513781, by rfl⟩ : syracuseStep 2018375 = 3027563) B3027563
theorem B2270677 : Blo 2017435 2270677 := bbase (se 7 (by rfl) ⟨26609, by rfl⟩ : syracuseStep 2270677 = 53219) (by norm_num)
theorem B3027569 : Blo 2017435 3027569 := bstep (se 2 (by rfl) ⟨1135338, by rfl⟩ : syracuseStep 3027569 = 2270677) B2270677
theorem B2018379 : Blo 2017435 2018379 := bstep (se 1 (by rfl) ⟨1513784, by rfl⟩ : syracuseStep 2018379 = 3027569) B3027569
theorem B2554517 : Blo 2017435 2554517 := bbase (se 6 (by rfl) ⟨59871, by rfl⟩ : syracuseStep 2554517 = 119743) (by norm_num)
theorem B6812045 : Blo 2017435 6812045 := bstep (se 3 (by rfl) ⟨1277258, by rfl⟩ : syracuseStep 6812045 = 2554517) B2554517
theorem B4541363 : Blo 2017435 4541363 := bstep (se 1 (by rfl) ⟨3406022, by rfl⟩ : syracuseStep 4541363 = 6812045) B6812045
theorem B3027575 : Blo 2017435 3027575 := bstep (se 1 (by rfl) ⟨2270681, by rfl⟩ : syracuseStep 3027575 = 4541363) B4541363
theorem B2018383 : Blo 2017435 2018383 := bstep (se 1 (by rfl) ⟨1513787, by rfl⟩ : syracuseStep 2018383 = 3027575) B3027575
theorem B3027581 : Blo 2017435 3027581 := bbase (se 3 (by rfl) ⟨567671, by rfl⟩ : syracuseStep 3027581 = 1135343) (by norm_num)
theorem B2018387 : Blo 2017435 2018387 := bstep (se 1 (by rfl) ⟨1513790, by rfl⟩ : syracuseStep 2018387 = 3027581) B3027581
theorem B4541381 : Blo 2017435 4541381 := bbase (se 4 (by rfl) ⟨425754, by rfl⟩ : syracuseStep 4541381 = 851509) (by norm_num)
theorem B3027587 : Blo 2017435 3027587 := bstep (se 1 (by rfl) ⟨2270690, by rfl⟩ : syracuseStep 3027587 = 4541381) B4541381
theorem B2018391 : Blo 2017435 2018391 := bstep (se 1 (by rfl) ⟨1513793, by rfl⟩ : syracuseStep 2018391 = 3027587) B3027587
theorem B11652245 : Blo 2017435 11652245 := bbase (se 6 (by rfl) ⟨273099, by rfl⟩ : syracuseStep 11652245 = 546199) (by norm_num)
theorem B7768163 : Blo 2017435 7768163 := bstep (se 1 (by rfl) ⟨5826122, by rfl⟩ : syracuseStep 7768163 = 11652245) B11652245
theorem B5178775 : Blo 2017435 5178775 := bstep (se 1 (by rfl) ⟨3884081, by rfl⟩ : syracuseStep 5178775 = 7768163) B7768163
theorem B6905033 : Blo 2017435 6905033 := bstep (se 2 (by rfl) ⟨2589387, by rfl⟩ : syracuseStep 6905033 = 5178775) B5178775
theorem B4603355 : Blo 2017435 4603355 := bstep (se 1 (by rfl) ⟨3452516, by rfl⟩ : syracuseStep 4603355 = 6905033) B6905033
theorem B3068903 : Blo 2017435 3068903 := bstep (se 1 (by rfl) ⟨2301677, by rfl⟩ : syracuseStep 3068903 = 4603355) B4603355
theorem B2045935 : Blo 2017435 2045935 := bstep (se 1 (by rfl) ⟨1534451, by rfl⟩ : syracuseStep 2045935 = 3068903) B3068903
theorem B2727913 : Blo 2017435 2727913 := bstep (se 2 (by rfl) ⟨1022967, by rfl⟩ : syracuseStep 2727913 = 2045935) B2045935
theorem B3637217 : Blo 2017435 3637217 := bstep (se 2 (by rfl) ⟨1363956, by rfl⟩ : syracuseStep 3637217 = 2727913) B2727913
theorem B2424811 : Blo 2017435 2424811 := bstep (se 1 (by rfl) ⟨1818608, by rfl⟩ : syracuseStep 2424811 = 3637217) B3637217
theorem B3233081 : Blo 2017435 3233081 := bstep (se 2 (by rfl) ⟨1212405, by rfl⟩ : syracuseStep 3233081 = 2424811) B2424811
theorem B8621549 : Blo 2017435 8621549 := bstep (se 3 (by rfl) ⟨1616540, by rfl⟩ : syracuseStep 8621549 = 3233081) B3233081
theorem B5747699 : Blo 2017435 5747699 := bstep (se 1 (by rfl) ⟨4310774, by rfl⟩ : syracuseStep 5747699 = 8621549) B8621549
theorem B3831799 : Blo 2017435 3831799 := bstep (se 1 (by rfl) ⟨2873849, by rfl⟩ : syracuseStep 3831799 = 5747699) B5747699
theorem B5109065 : Blo 2017435 5109065 := bstep (se 2 (by rfl) ⟨1915899, by rfl⟩ : syracuseStep 5109065 = 3831799) B3831799
theorem B3406043 : Blo 2017435 3406043 := bstep (se 1 (by rfl) ⟨2554532, by rfl⟩ : syracuseStep 3406043 = 5109065) B5109065
theorem B2270695 : Blo 2017435 2270695 := bstep (se 1 (by rfl) ⟨1703021, by rfl⟩ : syracuseStep 2270695 = 3406043) B3406043
theorem B3027593 : Blo 2017435 3027593 := bstep (se 2 (by rfl) ⟨1135347, by rfl⟩ : syracuseStep 3027593 = 2270695) B2270695
theorem B2018395 : Blo 2017435 2018395 := bstep (se 1 (by rfl) ⟨1513796, by rfl⟩ : syracuseStep 2018395 = 3027593) B3027593
theorem B10218149 : Blo 2017435 10218149 := bbase (se 4 (by rfl) ⟨957951, by rfl⟩ : syracuseStep 10218149 = 1915903) (by norm_num)
theorem B6812099 : Blo 2017435 6812099 := bstep (se 1 (by rfl) ⟨5109074, by rfl⟩ : syracuseStep 6812099 = 10218149) B10218149
theorem B4541399 : Blo 2017435 4541399 := bstep (se 1 (by rfl) ⟨3406049, by rfl⟩ : syracuseStep 4541399 = 6812099) B6812099
theorem B3027599 : Blo 2017435 3027599 := bstep (se 1 (by rfl) ⟨2270699, by rfl⟩ : syracuseStep 3027599 = 4541399) B4541399
theorem B2018399 : Blo 2017435 2018399 := bstep (se 1 (by rfl) ⟨1513799, by rfl⟩ : syracuseStep 2018399 = 3027599) B3027599
theorem B3027605 : Blo 2017435 3027605 := bbase (se 6 (by rfl) ⟨70959, by rfl⟩ : syracuseStep 3027605 = 141919) (by norm_num)
theorem B2018403 : Blo 2017435 2018403 := bstep (se 1 (by rfl) ⟨1513802, by rfl⟩ : syracuseStep 2018403 = 3027605) B3027605
theorem B3884101 : Blo 2017435 3884101 := bbase (se 4 (by rfl) ⟨364134, by rfl⟩ : syracuseStep 3884101 = 728269) (by norm_num)
theorem B20715205 : Blo 2017435 20715205 := bstep (se 4 (by rfl) ⟨1942050, by rfl⟩ : syracuseStep 20715205 = 3884101) B3884101
theorem B27620273 : Blo 2017435 27620273 := bstep (se 2 (by rfl) ⟨10357602, by rfl⟩ : syracuseStep 27620273 = 20715205) B20715205
theorem B18413515 : Blo 2017435 18413515 := bstep (se 1 (by rfl) ⟨13810136, by rfl⟩ : syracuseStep 18413515 = 27620273) B27620273
theorem B24551353 : Blo 2017435 24551353 := bstep (se 2 (by rfl) ⟨9206757, by rfl⟩ : syracuseStep 24551353 = 18413515) B18413515
theorem B32735137 : Blo 2017435 32735137 := bstep (se 2 (by rfl) ⟨12275676, by rfl⟩ : syracuseStep 32735137 = 24551353) B24551353
theorem B43646849 : Blo 2017435 43646849 := bstep (se 2 (by rfl) ⟨16367568, by rfl⟩ : syracuseStep 43646849 = 32735137) B32735137
theorem B29097899 : Blo 2017435 29097899 := bstep (se 1 (by rfl) ⟨21823424, by rfl⟩ : syracuseStep 29097899 = 43646849) B43646849
theorem B19398599 : Blo 2017435 19398599 := bstep (se 1 (by rfl) ⟨14548949, by rfl⟩ : syracuseStep 19398599 = 29097899) B29097899
theorem B12932399 : Blo 2017435 12932399 := bstep (se 1 (by rfl) ⟨9699299, by rfl⟩ : syracuseStep 12932399 = 19398599) B19398599
theorem B8621599 : Blo 2017435 8621599 := bstep (se 1 (by rfl) ⟨6466199, by rfl⟩ : syracuseStep 8621599 = 12932399) B12932399
theorem B11495465 : Blo 2017435 11495465 := bstep (se 2 (by rfl) ⟨4310799, by rfl⟩ : syracuseStep 11495465 = 8621599) B8621599
theorem B7663643 : Blo 2017435 7663643 := bstep (se 1 (by rfl) ⟨5747732, by rfl⟩ : syracuseStep 7663643 = 11495465) B11495465
theorem B5109095 : Blo 2017435 5109095 := bstep (se 1 (by rfl) ⟨3831821, by rfl⟩ : syracuseStep 5109095 = 7663643) B7663643
theorem B3406063 : Blo 2017435 3406063 := bstep (se 1 (by rfl) ⟨2554547, by rfl⟩ : syracuseStep 3406063 = 5109095) B5109095
theorem B4541417 : Blo 2017435 4541417 := bstep (se 2 (by rfl) ⟨1703031, by rfl⟩ : syracuseStep 4541417 = 3406063) B3406063
theorem B3027611 : Blo 2017435 3027611 := bstep (se 1 (by rfl) ⟨2270708, by rfl⟩ : syracuseStep 3027611 = 4541417) B4541417
theorem B2018407 : Blo 2017435 2018407 := bstep (se 1 (by rfl) ⟨1513805, by rfl⟩ : syracuseStep 2018407 = 3027611) B3027611
theorem B2270713 : Blo 2017435 2270713 := bbase (se 2 (by rfl) ⟨851517, by rfl⟩ : syracuseStep 2270713 = 1703035) (by norm_num)
theorem B3027617 : Blo 2017435 3027617 := bstep (se 2 (by rfl) ⟨1135356, by rfl⟩ : syracuseStep 3027617 = 2270713) B2270713
theorem B2018411 : Blo 2017435 2018411 := bstep (se 1 (by rfl) ⟨1513808, by rfl⟩ : syracuseStep 2018411 = 3027617) B3027617
theorem B4849669 : Blo 2017435 4849669 := bbase (se 4 (by rfl) ⟨454656, by rfl⟩ : syracuseStep 4849669 = 909313) (by norm_num)
theorem B6466225 : Blo 2017435 6466225 := bstep (se 2 (by rfl) ⟨2424834, by rfl⟩ : syracuseStep 6466225 = 4849669) B4849669
theorem B8621633 : Blo 2017435 8621633 := bstep (se 2 (by rfl) ⟨3233112, by rfl⟩ : syracuseStep 8621633 = 6466225) B6466225
theorem B5747755 : Blo 2017435 5747755 := bstep (se 1 (by rfl) ⟨4310816, by rfl⟩ : syracuseStep 5747755 = 8621633) B8621633
theorem B7663673 : Blo 2017435 7663673 := bstep (se 2 (by rfl) ⟨2873877, by rfl⟩ : syracuseStep 7663673 = 5747755) B5747755
theorem B5109115 : Blo 2017435 5109115 := bstep (se 1 (by rfl) ⟨3831836, by rfl⟩ : syracuseStep 5109115 = 7663673) B7663673
theorem B6812153 : Blo 2017435 6812153 := bstep (se 2 (by rfl) ⟨2554557, by rfl⟩ : syracuseStep 6812153 = 5109115) B5109115
theorem B4541435 : Blo 2017435 4541435 := bstep (se 1 (by rfl) ⟨3406076, by rfl⟩ : syracuseStep 4541435 = 6812153) B6812153
theorem B3027623 : Blo 2017435 3027623 := bstep (se 1 (by rfl) ⟨2270717, by rfl⟩ : syracuseStep 3027623 = 4541435) B4541435
theorem B2018415 : Blo 2017435 2018415 := bstep (se 1 (by rfl) ⟨1513811, by rfl⟩ : syracuseStep 2018415 = 3027623) B3027623
theorem B3027629 : Blo 2017435 3027629 := bbase (se 3 (by rfl) ⟨567680, by rfl⟩ : syracuseStep 3027629 = 1135361) (by norm_num)
theorem B2018419 : Blo 2017435 2018419 := bstep (se 1 (by rfl) ⟨1513814, by rfl⟩ : syracuseStep 2018419 = 3027629) B3027629
theorem B4541453 : Blo 2017435 4541453 := bbase (se 3 (by rfl) ⟨851522, by rfl⟩ : syracuseStep 4541453 = 1703045) (by norm_num)
theorem B3027635 : Blo 2017435 3027635 := bstep (se 1 (by rfl) ⟨2270726, by rfl⟩ : syracuseStep 3027635 = 4541453) B4541453
theorem B2018423 : Blo 2017435 2018423 := bstep (se 1 (by rfl) ⟨1513817, by rfl⟩ : syracuseStep 2018423 = 3027635) B3027635
theorem B2554573 : Blo 2017435 2554573 := bbase (se 3 (by rfl) ⟨478982, by rfl⟩ : syracuseStep 2554573 = 957965) (by norm_num)
theorem B3406097 : Blo 2017435 3406097 := bstep (se 2 (by rfl) ⟨1277286, by rfl⟩ : syracuseStep 3406097 = 2554573) B2554573
theorem B2270731 : Blo 2017435 2270731 := bstep (se 1 (by rfl) ⟨1703048, by rfl⟩ : syracuseStep 2270731 = 3406097) B3406097
theorem B3027641 : Blo 2017435 3027641 := bstep (se 2 (by rfl) ⟨1135365, by rfl⟩ : syracuseStep 3027641 = 2270731) B2270731
theorem B2018427 : Blo 2017435 2018427 := bstep (se 1 (by rfl) ⟨1513820, by rfl⟩ : syracuseStep 2018427 = 3027641) B3027641
theorem B2624761 : Blo 2017435 2624761 := bbase (se 2 (by rfl) ⟨984285, by rfl⟩ : syracuseStep 2624761 = 1968571) (by norm_num)
theorem B3499681 : Blo 2017435 3499681 := bstep (se 2 (by rfl) ⟨1312380, by rfl⟩ : syracuseStep 3499681 = 2624761) B2624761
theorem B4666241 : Blo 2017435 4666241 := bstep (se 2 (by rfl) ⟨1749840, by rfl⟩ : syracuseStep 4666241 = 3499681) B3499681
theorem B12443309 : Blo 2017435 12443309 := bstep (se 3 (by rfl) ⟨2333120, by rfl⟩ : syracuseStep 12443309 = 4666241) B4666241
theorem B8295539 : Blo 2017435 8295539 := bstep (se 1 (by rfl) ⟨6221654, by rfl⟩ : syracuseStep 8295539 = 12443309) B12443309
theorem B22121437 : Blo 2017435 22121437 := bstep (se 3 (by rfl) ⟨4147769, by rfl⟩ : syracuseStep 22121437 = 8295539) B8295539
theorem B29495249 : Blo 2017435 29495249 := bstep (se 2 (by rfl) ⟨11060718, by rfl⟩ : syracuseStep 29495249 = 22121437) B22121437
theorem B19663499 : Blo 2017435 19663499 := bstep (se 1 (by rfl) ⟨14747624, by rfl⟩ : syracuseStep 19663499 = 29495249) B29495249
theorem B13108999 : Blo 2017435 13108999 := bstep (se 1 (by rfl) ⟨9831749, by rfl⟩ : syracuseStep 13108999 = 19663499) B19663499
theorem B17478665 : Blo 2017435 17478665 := bstep (se 2 (by rfl) ⟨6554499, by rfl⟩ : syracuseStep 17478665 = 13108999) B13108999
theorem B11652443 : Blo 2017435 11652443 := bstep (se 1 (by rfl) ⟨8739332, by rfl⟩ : syracuseStep 11652443 = 17478665) B17478665
theorem B7768295 : Blo 2017435 7768295 := bstep (se 1 (by rfl) ⟨5826221, by rfl⟩ : syracuseStep 7768295 = 11652443) B11652443
theorem B5178863 : Blo 2017435 5178863 := bstep (se 1 (by rfl) ⟨3884147, by rfl⟩ : syracuseStep 5178863 = 7768295) B7768295
theorem B3452575 : Blo 2017435 3452575 := bstep (se 1 (by rfl) ⟨2589431, by rfl⟩ : syracuseStep 3452575 = 5178863) B5178863
theorem B4603433 : Blo 2017435 4603433 := bstep (se 2 (by rfl) ⟨1726287, by rfl⟩ : syracuseStep 4603433 = 3452575) B3452575
theorem B12275821 : Blo 2017435 12275821 := bstep (se 3 (by rfl) ⟨2301716, by rfl⟩ : syracuseStep 12275821 = 4603433) B4603433
theorem B16367761 : Blo 2017435 16367761 := bstep (se 2 (by rfl) ⟨6137910, by rfl⟩ : syracuseStep 16367761 = 12275821) B12275821
theorem B21823681 : Blo 2017435 21823681 := bstep (se 2 (by rfl) ⟨8183880, by rfl⟩ : syracuseStep 21823681 = 16367761) B16367761
theorem B29098241 : Blo 2017435 29098241 := bstep (se 2 (by rfl) ⟨10911840, by rfl⟩ : syracuseStep 29098241 = 21823681) B21823681
theorem B19398827 : Blo 2017435 19398827 := bstep (se 1 (by rfl) ⟨14549120, by rfl⟩ : syracuseStep 19398827 = 29098241) B29098241
theorem B12932551 : Blo 2017435 12932551 := bstep (se 1 (by rfl) ⟨9699413, by rfl⟩ : syracuseStep 12932551 = 19398827) B19398827
theorem B17243401 : Blo 2017435 17243401 := bstep (se 2 (by rfl) ⟨6466275, by rfl⟩ : syracuseStep 17243401 = 12932551) B12932551
theorem B22991201 : Blo 2017435 22991201 := bstep (se 2 (by rfl) ⟨8621700, by rfl⟩ : syracuseStep 22991201 = 17243401) B17243401
theorem B15327467 : Blo 2017435 15327467 := bstep (se 1 (by rfl) ⟨11495600, by rfl⟩ : syracuseStep 15327467 = 22991201) B22991201
theorem B10218311 : Blo 2017435 10218311 := bstep (se 1 (by rfl) ⟨7663733, by rfl⟩ : syracuseStep 10218311 = 15327467) B15327467
theorem B6812207 : Blo 2017435 6812207 := bstep (se 1 (by rfl) ⟨5109155, by rfl⟩ : syracuseStep 6812207 = 10218311) B10218311
theorem B4541471 : Blo 2017435 4541471 := bstep (se 1 (by rfl) ⟨3406103, by rfl⟩ : syracuseStep 4541471 = 6812207) B6812207
theorem B3027647 : Blo 2017435 3027647 := bstep (se 1 (by rfl) ⟨2270735, by rfl⟩ : syracuseStep 3027647 = 4541471) B4541471
theorem B2018431 : Blo 2017435 2018431 := bstep (se 1 (by rfl) ⟨1513823, by rfl⟩ : syracuseStep 2018431 = 3027647) B3027647
theorem B3027653 : Blo 2017435 3027653 := bbase (se 4 (by rfl) ⟨283842, by rfl⟩ : syracuseStep 3027653 = 567685) (by norm_num)
theorem B2018435 : Blo 2017435 2018435 := bstep (se 1 (by rfl) ⟨1513826, by rfl⟩ : syracuseStep 2018435 = 3027653) B3027653
theorem B3406117 : Blo 2017435 3406117 := bbase (se 4 (by rfl) ⟨319323, by rfl⟩ : syracuseStep 3406117 = 638647) (by norm_num)
theorem B4541489 : Blo 2017435 4541489 := bstep (se 2 (by rfl) ⟨1703058, by rfl⟩ : syracuseStep 4541489 = 3406117) B3406117
theorem B3027659 : Blo 2017435 3027659 := bstep (se 1 (by rfl) ⟨2270744, by rfl⟩ : syracuseStep 3027659 = 4541489) B4541489
theorem B2018439 : Blo 2017435 2018439 := bstep (se 1 (by rfl) ⟨1513829, by rfl⟩ : syracuseStep 2018439 = 3027659) B3027659
theorem B2270749 : Blo 2017435 2270749 := bbase (se 3 (by rfl) ⟨425765, by rfl⟩ : syracuseStep 2270749 = 851531) (by norm_num)
theorem B3027665 : Blo 2017435 3027665 := bstep (se 2 (by rfl) ⟨1135374, by rfl⟩ : syracuseStep 3027665 = 2270749) B2270749
theorem B2018443 : Blo 2017435 2018443 := bstep (se 1 (by rfl) ⟨1513832, by rfl⟩ : syracuseStep 2018443 = 3027665) B3027665
theorem B6812261 : Blo 2017435 6812261 := bbase (se 4 (by rfl) ⟨638649, by rfl⟩ : syracuseStep 6812261 = 1277299) (by norm_num)
theorem B4541507 : Blo 2017435 4541507 := bstep (se 1 (by rfl) ⟨3406130, by rfl⟩ : syracuseStep 4541507 = 6812261) B6812261
theorem B3027671 : Blo 2017435 3027671 := bstep (se 1 (by rfl) ⟨2270753, by rfl⟩ : syracuseStep 3027671 = 4541507) B4541507
theorem B2018447 : Blo 2017435 2018447 := bstep (se 1 (by rfl) ⟨1513835, by rfl⟩ : syracuseStep 2018447 = 3027671) B3027671
theorem B3027677 : Blo 2017435 3027677 := bbase (se 3 (by rfl) ⟨567689, by rfl⟩ : syracuseStep 3027677 = 1135379) (by norm_num)
theorem B2018451 : Blo 2017435 2018451 := bstep (se 1 (by rfl) ⟨1513838, by rfl⟩ : syracuseStep 2018451 = 3027677) B3027677
theorem B4541525 : Blo 2017435 4541525 := bbase (se 8 (by rfl) ⟨26610, by rfl⟩ : syracuseStep 4541525 = 53221) (by norm_num)
theorem B3027683 : Blo 2017435 3027683 := bstep (se 1 (by rfl) ⟨2270762, by rfl⟩ : syracuseStep 3027683 = 4541525) B4541525
theorem B2018455 : Blo 2017435 2018455 := bstep (se 1 (by rfl) ⟨1513841, by rfl⟩ : syracuseStep 2018455 = 3027683) B3027683
theorem B2624797 : Blo 2017435 2624797 := bbase (se 3 (by rfl) ⟨492149, by rfl⟩ : syracuseStep 2624797 = 984299) (by norm_num)
theorem B13998917 : Blo 2017435 13998917 := bstep (se 4 (by rfl) ⟨1312398, by rfl⟩ : syracuseStep 13998917 = 2624797) B2624797
theorem B37330445 : Blo 2017435 37330445 := bstep (se 3 (by rfl) ⟨6999458, by rfl⟩ : syracuseStep 37330445 = 13998917) B13998917
theorem B24886963 : Blo 2017435 24886963 := bstep (se 1 (by rfl) ⟨18665222, by rfl⟩ : syracuseStep 24886963 = 37330445) B37330445
theorem B33182617 : Blo 2017435 33182617 := bstep (se 2 (by rfl) ⟨12443481, by rfl⟩ : syracuseStep 33182617 = 24886963) B24886963
theorem B44243489 : Blo 2017435 44243489 := bstep (se 2 (by rfl) ⟨16591308, by rfl⟩ : syracuseStep 44243489 = 33182617) B33182617
theorem B29495659 : Blo 2017435 29495659 := bstep (se 1 (by rfl) ⟨22121744, by rfl⟩ : syracuseStep 29495659 = 44243489) B44243489
theorem B39327545 : Blo 2017435 39327545 := bstep (se 2 (by rfl) ⟨14747829, by rfl⟩ : syracuseStep 39327545 = 29495659) B29495659
theorem B104873453 : Blo 2017435 104873453 := bstep (se 3 (by rfl) ⟨19663772, by rfl⟩ : syracuseStep 104873453 = 39327545) B39327545
theorem B69915635 : Blo 2017435 69915635 := bstep (se 1 (by rfl) ⟨52436726, by rfl⟩ : syracuseStep 69915635 = 104873453) B104873453
theorem B46610423 : Blo 2017435 46610423 := bstep (se 1 (by rfl) ⟨34957817, by rfl⟩ : syracuseStep 46610423 = 69915635) B69915635
theorem B31073615 : Blo 2017435 31073615 := bstep (se 1 (by rfl) ⟨23305211, by rfl⟩ : syracuseStep 31073615 = 46610423) B46610423
theorem B20715743 : Blo 2017435 20715743 := bstep (se 1 (by rfl) ⟨15536807, by rfl⟩ : syracuseStep 20715743 = 31073615) B31073615
theorem B13810495 : Blo 2017435 13810495 := bstep (se 1 (by rfl) ⟨10357871, by rfl⟩ : syracuseStep 13810495 = 20715743) B20715743
theorem B18413993 : Blo 2017435 18413993 := bstep (se 2 (by rfl) ⟨6905247, by rfl⟩ : syracuseStep 18413993 = 13810495) B13810495
theorem B49103981 : Blo 2017435 49103981 := bstep (se 3 (by rfl) ⟨9206996, by rfl⟩ : syracuseStep 49103981 = 18413993) B18413993
theorem B32735987 : Blo 2017435 32735987 := bstep (se 1 (by rfl) ⟨24551990, by rfl⟩ : syracuseStep 32735987 = 49103981) B49103981
theorem B21823991 : Blo 2017435 21823991 := bstep (se 1 (by rfl) ⟨16367993, by rfl⟩ : syracuseStep 21823991 = 32735987) B32735987
theorem B14549327 : Blo 2017435 14549327 := bstep (se 1 (by rfl) ⟨10911995, by rfl⟩ : syracuseStep 14549327 = 21823991) B21823991
theorem B9699551 : Blo 2017435 9699551 := bstep (se 1 (by rfl) ⟨7274663, by rfl⟩ : syracuseStep 9699551 = 14549327) B14549327
theorem B6466367 : Blo 2017435 6466367 := bstep (se 1 (by rfl) ⟨4849775, by rfl⟩ : syracuseStep 6466367 = 9699551) B9699551
theorem B4310911 : Blo 2017435 4310911 := bstep (se 1 (by rfl) ⟨3233183, by rfl⟩ : syracuseStep 4310911 = 6466367) B6466367
theorem B5747881 : Blo 2017435 5747881 := bstep (se 2 (by rfl) ⟨2155455, by rfl⟩ : syracuseStep 5747881 = 4310911) B4310911
theorem B7663841 : Blo 2017435 7663841 := bstep (se 2 (by rfl) ⟨2873940, by rfl⟩ : syracuseStep 7663841 = 5747881) B5747881
theorem B5109227 : Blo 2017435 5109227 := bstep (se 1 (by rfl) ⟨3831920, by rfl⟩ : syracuseStep 5109227 = 7663841) B7663841
theorem B3406151 : Blo 2017435 3406151 := bstep (se 1 (by rfl) ⟨2554613, by rfl⟩ : syracuseStep 3406151 = 5109227) B5109227
theorem B2270767 : Blo 2017435 2270767 := bstep (se 1 (by rfl) ⟨1703075, by rfl⟩ : syracuseStep 2270767 = 3406151) B3406151
theorem B3027689 : Blo 2017435 3027689 := bstep (se 2 (by rfl) ⟨1135383, by rfl⟩ : syracuseStep 3027689 = 2270767) B2270767
theorem B2018459 : Blo 2017435 2018459 := bstep (se 1 (by rfl) ⟨1513844, by rfl⟩ : syracuseStep 2018459 = 3027689) B3027689
theorem B2102213 : Blo 2017435 2102213 := bbase (se 4 (by rfl) ⟨197082, by rfl⟩ : syracuseStep 2102213 = 394165) (by norm_num)
theorem B5605901 : Blo 2017435 5605901 := bstep (se 3 (by rfl) ⟨1051106, by rfl⟩ : syracuseStep 5605901 = 2102213) B2102213
theorem B3737267 : Blo 2017435 3737267 := bstep (se 1 (by rfl) ⟨2802950, by rfl⟩ : syracuseStep 3737267 = 5605901) B5605901
theorem B2491511 : Blo 2017435 2491511 := bstep (se 1 (by rfl) ⟨1868633, by rfl⟩ : syracuseStep 2491511 = 3737267) B3737267
theorem B26576117 : Blo 2017435 26576117 := bstep (se 5 (by rfl) ⟨1245755, by rfl⟩ : syracuseStep 26576117 = 2491511) B2491511
theorem B17717411 : Blo 2017435 17717411 := bstep (se 1 (by rfl) ⟨13288058, by rfl⟩ : syracuseStep 17717411 = 26576117) B26576117
theorem B47246429 : Blo 2017435 47246429 := bstep (se 3 (by rfl) ⟨8858705, by rfl⟩ : syracuseStep 47246429 = 17717411) B17717411
theorem B31497619 : Blo 2017435 31497619 := bstep (se 1 (by rfl) ⟨23623214, by rfl⟩ : syracuseStep 31497619 = 47246429) B47246429
theorem B41996825 : Blo 2017435 41996825 := bstep (se 2 (by rfl) ⟨15748809, by rfl⟩ : syracuseStep 41996825 = 31497619) B31497619
theorem B27997883 : Blo 2017435 27997883 := bstep (se 1 (by rfl) ⟨20998412, by rfl⟩ : syracuseStep 27997883 = 41996825) B41996825
theorem B18665255 : Blo 2017435 18665255 := bstep (se 1 (by rfl) ⟨13998941, by rfl⟩ : syracuseStep 18665255 = 27997883) B27997883
theorem B12443503 : Blo 2017435 12443503 := bstep (se 1 (by rfl) ⟨9332627, by rfl⟩ : syracuseStep 12443503 = 18665255) B18665255
theorem B16591337 : Blo 2017435 16591337 := bstep (se 2 (by rfl) ⟨6221751, by rfl⟩ : syracuseStep 16591337 = 12443503) B12443503
theorem B11060891 : Blo 2017435 11060891 := bstep (se 1 (by rfl) ⟨8295668, by rfl⟩ : syracuseStep 11060891 = 16591337) B16591337
theorem B7373927 : Blo 2017435 7373927 := bstep (se 1 (by rfl) ⟨5530445, by rfl⟩ : syracuseStep 7373927 = 11060891) B11060891
theorem B19663805 : Blo 2017435 19663805 := bstep (se 3 (by rfl) ⟨3686963, by rfl⟩ : syracuseStep 19663805 = 7373927) B7373927
theorem B13109203 : Blo 2017435 13109203 := bstep (se 1 (by rfl) ⟨9831902, by rfl⟩ : syracuseStep 13109203 = 19663805) B19663805
theorem B17478937 : Blo 2017435 17478937 := bstep (se 2 (by rfl) ⟨6554601, by rfl⟩ : syracuseStep 17478937 = 13109203) B13109203
theorem B23305249 : Blo 2017435 23305249 := bstep (se 2 (by rfl) ⟨8739468, by rfl⟩ : syracuseStep 23305249 = 17478937) B17478937
theorem B124294661 : Blo 2017435 124294661 := bstep (se 4 (by rfl) ⟨11652624, by rfl⟩ : syracuseStep 124294661 = 23305249) B23305249
theorem B82863107 : Blo 2017435 82863107 := bstep (se 1 (by rfl) ⟨62147330, by rfl⟩ : syracuseStep 82863107 = 124294661) B124294661
theorem B55242071 : Blo 2017435 55242071 := bstep (se 1 (by rfl) ⟨41431553, by rfl⟩ : syracuseStep 55242071 = 82863107) B82863107
theorem B36828047 : Blo 2017435 36828047 := bstep (se 1 (by rfl) ⟨27621035, by rfl⟩ : syracuseStep 36828047 = 55242071) B55242071
theorem B98208125 : Blo 2017435 98208125 := bstep (se 3 (by rfl) ⟨18414023, by rfl⟩ : syracuseStep 98208125 = 36828047) B36828047
theorem B65472083 : Blo 2017435 65472083 := bstep (se 1 (by rfl) ⟨49104062, by rfl⟩ : syracuseStep 65472083 = 98208125) B98208125
theorem B43648055 : Blo 2017435 43648055 := bstep (se 1 (by rfl) ⟨32736041, by rfl⟩ : syracuseStep 43648055 = 65472083) B65472083
theorem B29098703 : Blo 2017435 29098703 := bstep (se 1 (by rfl) ⟨21824027, by rfl⟩ : syracuseStep 29098703 = 43648055) B43648055
theorem B19399135 : Blo 2017435 19399135 := bstep (se 1 (by rfl) ⟨14549351, by rfl⟩ : syracuseStep 19399135 = 29098703) B29098703
theorem B25865513 : Blo 2017435 25865513 := bstep (se 2 (by rfl) ⟨9699567, by rfl⟩ : syracuseStep 25865513 = 19399135) B19399135
theorem B17243675 : Blo 2017435 17243675 := bstep (se 1 (by rfl) ⟨12932756, by rfl⟩ : syracuseStep 17243675 = 25865513) B25865513
theorem B11495783 : Blo 2017435 11495783 := bstep (se 1 (by rfl) ⟨8621837, by rfl⟩ : syracuseStep 11495783 = 17243675) B17243675
theorem B7663855 : Blo 2017435 7663855 := bstep (se 1 (by rfl) ⟨5747891, by rfl⟩ : syracuseStep 7663855 = 11495783) B11495783
theorem B10218473 : Blo 2017435 10218473 := bstep (se 2 (by rfl) ⟨3831927, by rfl⟩ : syracuseStep 10218473 = 7663855) B7663855
theorem B6812315 : Blo 2017435 6812315 := bstep (se 1 (by rfl) ⟨5109236, by rfl⟩ : syracuseStep 6812315 = 10218473) B10218473
theorem B4541543 : Blo 2017435 4541543 := bstep (se 1 (by rfl) ⟨3406157, by rfl⟩ : syracuseStep 4541543 = 6812315) B6812315
theorem B3027695 : Blo 2017435 3027695 := bstep (se 1 (by rfl) ⟨2270771, by rfl⟩ : syracuseStep 3027695 = 4541543) B4541543
theorem B2018463 : Blo 2017435 2018463 := bstep (se 1 (by rfl) ⟨1513847, by rfl⟩ : syracuseStep 2018463 = 3027695) B3027695
theorem B3027701 : Blo 2017435 3027701 := bbase (se 5 (by rfl) ⟨141923, by rfl⟩ : syracuseStep 3027701 = 283847) (by norm_num)
theorem B2018467 : Blo 2017435 2018467 := bstep (se 1 (by rfl) ⟨1513850, by rfl⟩ : syracuseStep 2018467 = 3027701) B3027701
theorem B6466405 : Blo 2017435 6466405 := bbase (se 4 (by rfl) ⟨606225, by rfl⟩ : syracuseStep 6466405 = 1212451) (by norm_num)
theorem B8621873 : Blo 2017435 8621873 := bstep (se 2 (by rfl) ⟨3233202, by rfl⟩ : syracuseStep 8621873 = 6466405) B6466405
theorem B5747915 : Blo 2017435 5747915 := bstep (se 1 (by rfl) ⟨4310936, by rfl⟩ : syracuseStep 5747915 = 8621873) B8621873
theorem B3831943 : Blo 2017435 3831943 := bstep (se 1 (by rfl) ⟨2873957, by rfl⟩ : syracuseStep 3831943 = 5747915) B5747915
theorem B5109257 : Blo 2017435 5109257 := bstep (se 2 (by rfl) ⟨1915971, by rfl⟩ : syracuseStep 5109257 = 3831943) B3831943
theorem B3406171 : Blo 2017435 3406171 := bstep (se 1 (by rfl) ⟨2554628, by rfl⟩ : syracuseStep 3406171 = 5109257) B5109257
theorem B4541561 : Blo 2017435 4541561 := bstep (se 2 (by rfl) ⟨1703085, by rfl⟩ : syracuseStep 4541561 = 3406171) B3406171
theorem B3027707 : Blo 2017435 3027707 := bstep (se 1 (by rfl) ⟨2270780, by rfl⟩ : syracuseStep 3027707 = 4541561) B4541561
theorem B2018471 : Blo 2017435 2018471 := bstep (se 1 (by rfl) ⟨1513853, by rfl⟩ : syracuseStep 2018471 = 3027707) B3027707
theorem B2270785 : Blo 2017435 2270785 := bbase (se 2 (by rfl) ⟨851544, by rfl⟩ : syracuseStep 2270785 = 1703089) (by norm_num)
theorem B3027713 : Blo 2017435 3027713 := bstep (se 2 (by rfl) ⟨1135392, by rfl⟩ : syracuseStep 3027713 = 2270785) B2270785
theorem B2018475 : Blo 2017435 2018475 := bstep (se 1 (by rfl) ⟨1513856, by rfl⟩ : syracuseStep 2018475 = 3027713) B3027713
theorem B5109277 : Blo 2017435 5109277 := bbase (se 3 (by rfl) ⟨957989, by rfl⟩ : syracuseStep 5109277 = 1915979) (by norm_num)
theorem B6812369 : Blo 2017435 6812369 := bstep (se 2 (by rfl) ⟨2554638, by rfl⟩ : syracuseStep 6812369 = 5109277) B5109277
theorem B4541579 : Blo 2017435 4541579 := bstep (se 1 (by rfl) ⟨3406184, by rfl⟩ : syracuseStep 4541579 = 6812369) B6812369
theorem B3027719 : Blo 2017435 3027719 := bstep (se 1 (by rfl) ⟨2270789, by rfl⟩ : syracuseStep 3027719 = 4541579) B4541579
theorem B2018479 : Blo 2017435 2018479 := bstep (se 1 (by rfl) ⟨1513859, by rfl⟩ : syracuseStep 2018479 = 3027719) B3027719
theorem B3027725 : Blo 2017435 3027725 := bbase (se 3 (by rfl) ⟨567698, by rfl⟩ : syracuseStep 3027725 = 1135397) (by norm_num)
theorem B2018483 : Blo 2017435 2018483 := bstep (se 1 (by rfl) ⟨1513862, by rfl⟩ : syracuseStep 2018483 = 3027725) B3027725
theorem B4541597 : Blo 2017435 4541597 := bbase (se 3 (by rfl) ⟨851549, by rfl⟩ : syracuseStep 4541597 = 1703099) (by norm_num)
theorem B3027731 : Blo 2017435 3027731 := bstep (se 1 (by rfl) ⟨2270798, by rfl⟩ : syracuseStep 3027731 = 4541597) B4541597
theorem B2018487 : Blo 2017435 2018487 := bstep (se 1 (by rfl) ⟨1513865, by rfl⟩ : syracuseStep 2018487 = 3027731) B3027731
theorem B3406205 : Blo 2017435 3406205 := bbase (se 3 (by rfl) ⟨638663, by rfl⟩ : syracuseStep 3406205 = 1277327) (by norm_num)
theorem B2270803 : Blo 2017435 2270803 := bstep (se 1 (by rfl) ⟨1703102, by rfl⟩ : syracuseStep 2270803 = 3406205) B3406205
theorem B3027737 : Blo 2017435 3027737 := bstep (se 2 (by rfl) ⟨1135401, by rfl⟩ : syracuseStep 3027737 = 2270803) B2270803
theorem B2018491 : Blo 2017435 2018491 := bstep (se 1 (by rfl) ⟨1513868, by rfl⟩ : syracuseStep 2018491 = 3027737) B3027737
theorem B4849861 : Blo 2017435 4849861 := bbase (se 4 (by rfl) ⟨454674, by rfl⟩ : syracuseStep 4849861 = 909349) (by norm_num)
theorem B6466481 : Blo 2017435 6466481 := bstep (se 2 (by rfl) ⟨2424930, by rfl⟩ : syracuseStep 6466481 = 4849861) B4849861
theorem B4310987 : Blo 2017435 4310987 := bstep (se 1 (by rfl) ⟨3233240, by rfl⟩ : syracuseStep 4310987 = 6466481) B6466481
theorem B11495965 : Blo 2017435 11495965 := bstep (se 3 (by rfl) ⟨2155493, by rfl⟩ : syracuseStep 11495965 = 4310987) B4310987
theorem B15327953 : Blo 2017435 15327953 := bstep (se 2 (by rfl) ⟨5747982, by rfl⟩ : syracuseStep 15327953 = 11495965) B11495965
theorem B10218635 : Blo 2017435 10218635 := bstep (se 1 (by rfl) ⟨7663976, by rfl⟩ : syracuseStep 10218635 = 15327953) B15327953
theorem B6812423 : Blo 2017435 6812423 := bstep (se 1 (by rfl) ⟨5109317, by rfl⟩ : syracuseStep 6812423 = 10218635) B10218635
theorem B4541615 : Blo 2017435 4541615 := bstep (se 1 (by rfl) ⟨3406211, by rfl⟩ : syracuseStep 4541615 = 6812423) B6812423
theorem B3027743 : Blo 2017435 3027743 := bstep (se 1 (by rfl) ⟨2270807, by rfl⟩ : syracuseStep 3027743 = 4541615) B4541615
theorem B2018495 : Blo 2017435 2018495 := bstep (se 1 (by rfl) ⟨1513871, by rfl⟩ : syracuseStep 2018495 = 3027743) B3027743
theorem B3027749 : Blo 2017435 3027749 := bbase (se 4 (by rfl) ⟨283851, by rfl⟩ : syracuseStep 3027749 = 567703) (by norm_num)
theorem B2018499 : Blo 2017435 2018499 := bstep (se 1 (by rfl) ⟨1513874, by rfl⟩ : syracuseStep 2018499 = 3027749) B3027749
theorem B2554669 : Blo 2017435 2554669 := bbase (se 3 (by rfl) ⟨479000, by rfl⟩ : syracuseStep 2554669 = 958001) (by norm_num)
theorem B3406225 : Blo 2017435 3406225 := bstep (se 2 (by rfl) ⟨1277334, by rfl⟩ : syracuseStep 3406225 = 2554669) B2554669
theorem B4541633 : Blo 2017435 4541633 := bstep (se 2 (by rfl) ⟨1703112, by rfl⟩ : syracuseStep 4541633 = 3406225) B3406225
theorem B3027755 : Blo 2017435 3027755 := bstep (se 1 (by rfl) ⟨2270816, by rfl⟩ : syracuseStep 3027755 = 4541633) B4541633
theorem B2018503 : Blo 2017435 2018503 := bstep (se 1 (by rfl) ⟨1513877, by rfl⟩ : syracuseStep 2018503 = 3027755) B3027755
theorem B2270821 : Blo 2017435 2270821 := bbase (se 4 (by rfl) ⟨212889, by rfl⟩ : syracuseStep 2270821 = 425779) (by norm_num)
theorem B3027761 : Blo 2017435 3027761 := bstep (se 2 (by rfl) ⟨1135410, by rfl⟩ : syracuseStep 3027761 = 2270821) B2270821
theorem B2018507 : Blo 2017435 2018507 := bstep (se 1 (by rfl) ⟨1513880, by rfl⟩ : syracuseStep 2018507 = 3027761) B3027761
theorem B4849901 : Blo 2017435 4849901 := bbase (se 3 (by rfl) ⟨909356, by rfl⟩ : syracuseStep 4849901 = 1818713) (by norm_num)
theorem B3233267 : Blo 2017435 3233267 := bstep (se 1 (by rfl) ⟨2424950, by rfl⟩ : syracuseStep 3233267 = 4849901) B4849901
theorem B2155511 : Blo 2017435 2155511 := bstep (se 1 (by rfl) ⟨1616633, by rfl⟩ : syracuseStep 2155511 = 3233267) B3233267
theorem B5748029 : Blo 2017435 5748029 := bstep (se 3 (by rfl) ⟨1077755, by rfl⟩ : syracuseStep 5748029 = 2155511) B2155511
theorem B3832019 : Blo 2017435 3832019 := bstep (se 1 (by rfl) ⟨2874014, by rfl⟩ : syracuseStep 3832019 = 5748029) B5748029
theorem B2554679 : Blo 2017435 2554679 := bstep (se 1 (by rfl) ⟨1916009, by rfl⟩ : syracuseStep 2554679 = 3832019) B3832019
theorem B6812477 : Blo 2017435 6812477 := bstep (se 3 (by rfl) ⟨1277339, by rfl⟩ : syracuseStep 6812477 = 2554679) B2554679
theorem B4541651 : Blo 2017435 4541651 := bstep (se 1 (by rfl) ⟨3406238, by rfl⟩ : syracuseStep 4541651 = 6812477) B6812477
theorem B3027767 : Blo 2017435 3027767 := bstep (se 1 (by rfl) ⟨2270825, by rfl⟩ : syracuseStep 3027767 = 4541651) B4541651
theorem B2018511 : Blo 2017435 2018511 := bstep (se 1 (by rfl) ⟨1513883, by rfl⟩ : syracuseStep 2018511 = 3027767) B3027767
theorem B3027773 : Blo 2017435 3027773 := bbase (se 3 (by rfl) ⟨567707, by rfl⟩ : syracuseStep 3027773 = 1135415) (by norm_num)
theorem B2018515 : Blo 2017435 2018515 := bstep (se 1 (by rfl) ⟨1513886, by rfl⟩ : syracuseStep 2018515 = 3027773) B3027773
theorem B4541669 : Blo 2017435 4541669 := bbase (se 4 (by rfl) ⟨425781, by rfl⟩ : syracuseStep 4541669 = 851563) (by norm_num)
theorem B3027779 : Blo 2017435 3027779 := bstep (se 1 (by rfl) ⟨2270834, by rfl⟩ : syracuseStep 3027779 = 4541669) B4541669
theorem B2018519 : Blo 2017435 2018519 := bstep (se 1 (by rfl) ⟨1513889, by rfl⟩ : syracuseStep 2018519 = 3027779) B3027779
theorem B5109389 : Blo 2017435 5109389 := bbase (se 3 (by rfl) ⟨958010, by rfl⟩ : syracuseStep 5109389 = 1916021) (by norm_num)
theorem B3406259 : Blo 2017435 3406259 := bstep (se 1 (by rfl) ⟨2554694, by rfl⟩ : syracuseStep 3406259 = 5109389) B5109389
theorem B2270839 : Blo 2017435 2270839 := bstep (se 1 (by rfl) ⟨1703129, by rfl⟩ : syracuseStep 2270839 = 3406259) B3406259
theorem B3027785 : Blo 2017435 3027785 := bstep (se 2 (by rfl) ⟨1135419, by rfl⟩ : syracuseStep 3027785 = 2270839) B2270839
theorem B2018523 : Blo 2017435 2018523 := bstep (se 1 (by rfl) ⟨1513892, by rfl⟩ : syracuseStep 2018523 = 3027785) B3027785
theorem B2874037 : Blo 2017435 2874037 := bbase (se 5 (by rfl) ⟨134720, by rfl⟩ : syracuseStep 2874037 = 269441) (by norm_num)
theorem B3832049 : Blo 2017435 3832049 := bstep (se 2 (by rfl) ⟨1437018, by rfl⟩ : syracuseStep 3832049 = 2874037) B2874037
theorem B10218797 : Blo 2017435 10218797 := bstep (se 3 (by rfl) ⟨1916024, by rfl⟩ : syracuseStep 10218797 = 3832049) B3832049
theorem B6812531 : Blo 2017435 6812531 := bstep (se 1 (by rfl) ⟨5109398, by rfl⟩ : syracuseStep 6812531 = 10218797) B10218797
theorem B4541687 : Blo 2017435 4541687 := bstep (se 1 (by rfl) ⟨3406265, by rfl⟩ : syracuseStep 4541687 = 6812531) B6812531
theorem B3027791 : Blo 2017435 3027791 := bstep (se 1 (by rfl) ⟨2270843, by rfl⟩ : syracuseStep 3027791 = 4541687) B4541687
theorem B2018527 : Blo 2017435 2018527 := bstep (se 1 (by rfl) ⟨1513895, by rfl⟩ : syracuseStep 2018527 = 3027791) B3027791
theorem B3027797 : Blo 2017435 3027797 := bbase (se 9 (by rfl) ⟨8870, by rfl⟩ : syracuseStep 3027797 = 17741) (by norm_num)
theorem B2018531 : Blo 2017435 2018531 := bstep (se 1 (by rfl) ⟨1513898, by rfl⟩ : syracuseStep 2018531 = 3027797) B3027797
theorem B3637469 : Blo 2017435 3637469 := bbase (se 3 (by rfl) ⟨682025, by rfl⟩ : syracuseStep 3637469 = 1364051) (by norm_num)
theorem B2424979 : Blo 2017435 2424979 := bstep (se 1 (by rfl) ⟨1818734, by rfl⟩ : syracuseStep 2424979 = 3637469) B3637469
theorem B3233305 : Blo 2017435 3233305 := bstep (se 2 (by rfl) ⟨1212489, by rfl⟩ : syracuseStep 3233305 = 2424979) B2424979
theorem B4311073 : Blo 2017435 4311073 := bstep (se 2 (by rfl) ⟨1616652, by rfl⟩ : syracuseStep 4311073 = 3233305) B3233305
theorem B5748097 : Blo 2017435 5748097 := bstep (se 2 (by rfl) ⟨2155536, by rfl⟩ : syracuseStep 5748097 = 4311073) B4311073
theorem B7664129 : Blo 2017435 7664129 := bstep (se 2 (by rfl) ⟨2874048, by rfl⟩ : syracuseStep 7664129 = 5748097) B5748097
theorem B5109419 : Blo 2017435 5109419 := bstep (se 1 (by rfl) ⟨3832064, by rfl⟩ : syracuseStep 5109419 = 7664129) B7664129
theorem B3406279 : Blo 2017435 3406279 := bstep (se 1 (by rfl) ⟨2554709, by rfl⟩ : syracuseStep 3406279 = 5109419) B5109419
theorem B4541705 : Blo 2017435 4541705 := bstep (se 2 (by rfl) ⟨1703139, by rfl⟩ : syracuseStep 4541705 = 3406279) B3406279
theorem B3027803 : Blo 2017435 3027803 := bstep (se 1 (by rfl) ⟨2270852, by rfl⟩ : syracuseStep 3027803 = 4541705) B4541705
theorem B2018535 : Blo 2017435 2018535 := bstep (se 1 (by rfl) ⟨1513901, by rfl⟩ : syracuseStep 2018535 = 3027803) B3027803
theorem B2270857 : Blo 2017435 2270857 := bbase (se 2 (by rfl) ⟨851571, by rfl⟩ : syracuseStep 2270857 = 1703143) (by norm_num)
theorem B3027809 : Blo 2017435 3027809 := bstep (se 2 (by rfl) ⟨1135428, by rfl⟩ : syracuseStep 3027809 = 2270857) B2270857
theorem B2018539 : Blo 2017435 2018539 := bstep (se 1 (by rfl) ⟨1513904, by rfl⟩ : syracuseStep 2018539 = 3027809) B3027809
theorem B4369909 : Blo 2017435 4369909 := bbase (se 5 (by rfl) ⟨204839, by rfl⟩ : syracuseStep 4369909 = 409679) (by norm_num)
theorem B5826545 : Blo 2017435 5826545 := bstep (se 2 (by rfl) ⟨2184954, by rfl⟩ : syracuseStep 5826545 = 4369909) B4369909
theorem B3884363 : Blo 2017435 3884363 := bstep (se 1 (by rfl) ⟨2913272, by rfl⟩ : syracuseStep 3884363 = 5826545) B5826545
theorem B2589575 : Blo 2017435 2589575 := bstep (se 1 (by rfl) ⟨1942181, by rfl⟩ : syracuseStep 2589575 = 3884363) B3884363
theorem B27622133 : Blo 2017435 27622133 := bstep (se 5 (by rfl) ⟨1294787, by rfl⟩ : syracuseStep 27622133 = 2589575) B2589575
theorem B18414755 : Blo 2017435 18414755 := bstep (se 1 (by rfl) ⟨13811066, by rfl⟩ : syracuseStep 18414755 = 27622133) B27622133
theorem B12276503 : Blo 2017435 12276503 := bstep (se 1 (by rfl) ⟨9207377, by rfl⟩ : syracuseStep 12276503 = 18414755) B18414755
theorem B8184335 : Blo 2017435 8184335 := bstep (se 1 (by rfl) ⟨6138251, by rfl⟩ : syracuseStep 8184335 = 12276503) B12276503
theorem B21824893 : Blo 2017435 21824893 := bstep (se 3 (by rfl) ⟨4092167, by rfl⟩ : syracuseStep 21824893 = 8184335) B8184335
theorem B29099857 : Blo 2017435 29099857 := bstep (se 2 (by rfl) ⟨10912446, by rfl⟩ : syracuseStep 29099857 = 21824893) B21824893
theorem B38799809 : Blo 2017435 38799809 := bstep (se 2 (by rfl) ⟨14549928, by rfl⟩ : syracuseStep 38799809 = 29099857) B29099857
theorem B25866539 : Blo 2017435 25866539 := bstep (se 1 (by rfl) ⟨19399904, by rfl⟩ : syracuseStep 25866539 = 38799809) B38799809
theorem B17244359 : Blo 2017435 17244359 := bstep (se 1 (by rfl) ⟨12933269, by rfl⟩ : syracuseStep 17244359 = 25866539) B25866539
theorem B11496239 : Blo 2017435 11496239 := bstep (se 1 (by rfl) ⟨8622179, by rfl⟩ : syracuseStep 11496239 = 17244359) B17244359
theorem B7664159 : Blo 2017435 7664159 := bstep (se 1 (by rfl) ⟨5748119, by rfl⟩ : syracuseStep 7664159 = 11496239) B11496239
theorem B5109439 : Blo 2017435 5109439 := bstep (se 1 (by rfl) ⟨3832079, by rfl⟩ : syracuseStep 5109439 = 7664159) B7664159
theorem B6812585 : Blo 2017435 6812585 := bstep (se 2 (by rfl) ⟨2554719, by rfl⟩ : syracuseStep 6812585 = 5109439) B5109439
theorem B4541723 : Blo 2017435 4541723 := bstep (se 1 (by rfl) ⟨3406292, by rfl⟩ : syracuseStep 4541723 = 6812585) B6812585
theorem B3027815 : Blo 2017435 3027815 := bstep (se 1 (by rfl) ⟨2270861, by rfl⟩ : syracuseStep 3027815 = 4541723) B4541723
theorem B2018543 : Blo 2017435 2018543 := bstep (se 1 (by rfl) ⟨1513907, by rfl⟩ : syracuseStep 2018543 = 3027815) B3027815
theorem B3027821 : Blo 2017435 3027821 := bbase (se 3 (by rfl) ⟨567716, by rfl⟩ : syracuseStep 3027821 = 1135433) (by norm_num)
theorem B2018547 : Blo 2017435 2018547 := bstep (se 1 (by rfl) ⟨1513910, by rfl⟩ : syracuseStep 2018547 = 3027821) B3027821
theorem B4541741 : Blo 2017435 4541741 := bbase (se 3 (by rfl) ⟨851576, by rfl⟩ : syracuseStep 4541741 = 1703153) (by norm_num)
theorem B3027827 : Blo 2017435 3027827 := bstep (se 1 (by rfl) ⟨2270870, by rfl⟩ : syracuseStep 3027827 = 4541741) B4541741
theorem B2018551 : Blo 2017435 2018551 := bstep (se 1 (by rfl) ⟨1513913, by rfl⟩ : syracuseStep 2018551 = 3027827) B3027827
theorem B2046097 : Blo 2017435 2046097 := bbase (se 2 (by rfl) ⟨767286, by rfl⟩ : syracuseStep 2046097 = 1534573) (by norm_num)
theorem B2728129 : Blo 2017435 2728129 := bstep (se 2 (by rfl) ⟨1023048, by rfl⟩ : syracuseStep 2728129 = 2046097) B2046097
theorem B3637505 : Blo 2017435 3637505 := bstep (se 2 (by rfl) ⟨1364064, by rfl⟩ : syracuseStep 3637505 = 2728129) B2728129
theorem B9700013 : Blo 2017435 9700013 := bstep (se 3 (by rfl) ⟨1818752, by rfl⟩ : syracuseStep 9700013 = 3637505) B3637505
theorem B6466675 : Blo 2017435 6466675 := bstep (se 1 (by rfl) ⟨4850006, by rfl⟩ : syracuseStep 6466675 = 9700013) B9700013
theorem B8622233 : Blo 2017435 8622233 := bstep (se 2 (by rfl) ⟨3233337, by rfl⟩ : syracuseStep 8622233 = 6466675) B6466675
theorem B5748155 : Blo 2017435 5748155 := bstep (se 1 (by rfl) ⟨4311116, by rfl⟩ : syracuseStep 5748155 = 8622233) B8622233
theorem B3832103 : Blo 2017435 3832103 := bstep (se 1 (by rfl) ⟨2874077, by rfl⟩ : syracuseStep 3832103 = 5748155) B5748155
theorem B2554735 : Blo 2017435 2554735 := bstep (se 1 (by rfl) ⟨1916051, by rfl⟩ : syracuseStep 2554735 = 3832103) B3832103
theorem B3406313 : Blo 2017435 3406313 := bstep (se 2 (by rfl) ⟨1277367, by rfl⟩ : syracuseStep 3406313 = 2554735) B2554735
theorem B2270875 : Blo 2017435 2270875 := bstep (se 1 (by rfl) ⟨1703156, by rfl⟩ : syracuseStep 2270875 = 3406313) B3406313
theorem B3027833 : Blo 2017435 3027833 := bstep (se 2 (by rfl) ⟨1135437, by rfl⟩ : syracuseStep 3027833 = 2270875) B2270875
theorem B2018555 : Blo 2017435 2018555 := bstep (se 1 (by rfl) ⟨1513916, by rfl⟩ : syracuseStep 2018555 = 3027833) B3027833
theorem B12613877 : Blo 2017435 12613877 := bbase (se 5 (by rfl) ⟨591275, by rfl⟩ : syracuseStep 12613877 = 1182551) (by norm_num)
theorem B8409251 : Blo 2017435 8409251 := bstep (se 1 (by rfl) ⟨6306938, by rfl⟩ : syracuseStep 8409251 = 12613877) B12613877
theorem B5606167 : Blo 2017435 5606167 := bstep (se 1 (by rfl) ⟨4204625, by rfl⟩ : syracuseStep 5606167 = 8409251) B8409251
theorem B7474889 : Blo 2017435 7474889 := bstep (se 2 (by rfl) ⟨2803083, by rfl⟩ : syracuseStep 7474889 = 5606167) B5606167
theorem B19933037 : Blo 2017435 19933037 := bstep (se 3 (by rfl) ⟨3737444, by rfl⟩ : syracuseStep 19933037 = 7474889) B7474889
theorem B13288691 : Blo 2017435 13288691 := bstep (se 1 (by rfl) ⟨9966518, by rfl⟩ : syracuseStep 13288691 = 19933037) B19933037
theorem B8859127 : Blo 2017435 8859127 := bstep (se 1 (by rfl) ⟨6644345, by rfl⟩ : syracuseStep 8859127 = 13288691) B13288691
theorem B11812169 : Blo 2017435 11812169 := bstep (se 2 (by rfl) ⟨4429563, by rfl⟩ : syracuseStep 11812169 = 8859127) B8859127
theorem B7874779 : Blo 2017435 7874779 := bstep (se 1 (by rfl) ⟨5906084, by rfl⟩ : syracuseStep 7874779 = 11812169) B11812169
theorem B10499705 : Blo 2017435 10499705 := bstep (se 2 (by rfl) ⟨3937389, by rfl⟩ : syracuseStep 10499705 = 7874779) B7874779
theorem B6999803 : Blo 2017435 6999803 := bstep (se 1 (by rfl) ⟨5249852, by rfl⟩ : syracuseStep 6999803 = 10499705) B10499705
theorem B4666535 : Blo 2017435 4666535 := bstep (se 1 (by rfl) ⟨3499901, by rfl⟩ : syracuseStep 4666535 = 6999803) B6999803
theorem B49776373 : Blo 2017435 49776373 := bstep (se 5 (by rfl) ⟨2333267, by rfl⟩ : syracuseStep 49776373 = 4666535) B4666535
theorem B66368497 : Blo 2017435 66368497 := bstep (se 2 (by rfl) ⟨24888186, by rfl⟩ : syracuseStep 66368497 = 49776373) B49776373
theorem B88491329 : Blo 2017435 88491329 := bstep (se 2 (by rfl) ⟨33184248, by rfl⟩ : syracuseStep 88491329 = 66368497) B66368497
theorem B58994219 : Blo 2017435 58994219 := bstep (se 1 (by rfl) ⟨44245664, by rfl⟩ : syracuseStep 58994219 = 88491329) B88491329
theorem B39329479 : Blo 2017435 39329479 := bstep (se 1 (by rfl) ⟨29497109, by rfl⟩ : syracuseStep 39329479 = 58994219) B58994219
theorem B209757221 : Blo 2017435 209757221 := bstep (se 4 (by rfl) ⟨19664739, by rfl⟩ : syracuseStep 209757221 = 39329479) B39329479
theorem B139838147 : Blo 2017435 139838147 := bstep (se 1 (by rfl) ⟨104878610, by rfl⟩ : syracuseStep 139838147 = 209757221) B209757221
theorem B93225431 : Blo 2017435 93225431 := bstep (se 1 (by rfl) ⟨69919073, by rfl⟩ : syracuseStep 93225431 = 139838147) B139838147
theorem B62150287 : Blo 2017435 62150287 := bstep (se 1 (by rfl) ⟨46612715, by rfl⟩ : syracuseStep 62150287 = 93225431) B93225431
theorem B82867049 : Blo 2017435 82867049 := bstep (se 2 (by rfl) ⟨31075143, by rfl⟩ : syracuseStep 82867049 = 62150287) B62150287
theorem B55244699 : Blo 2017435 55244699 := bstep (se 1 (by rfl) ⟨41433524, by rfl⟩ : syracuseStep 55244699 = 82867049) B82867049
theorem B36829799 : Blo 2017435 36829799 := bstep (se 1 (by rfl) ⟨27622349, by rfl⟩ : syracuseStep 36829799 = 55244699) B55244699
theorem B24553199 : Blo 2017435 24553199 := bstep (se 1 (by rfl) ⟨18414899, by rfl⟩ : syracuseStep 24553199 = 36829799) B36829799
theorem B16368799 : Blo 2017435 16368799 := bstep (se 1 (by rfl) ⟨12276599, by rfl⟩ : syracuseStep 16368799 = 24553199) B24553199
theorem B21825065 : Blo 2017435 21825065 := bstep (se 2 (by rfl) ⟨8184399, by rfl⟩ : syracuseStep 21825065 = 16368799) B16368799
theorem B14550043 : Blo 2017435 14550043 := bstep (se 1 (by rfl) ⟨10912532, by rfl⟩ : syracuseStep 14550043 = 21825065) B21825065
theorem B19400057 : Blo 2017435 19400057 := bstep (se 2 (by rfl) ⟨7275021, by rfl⟩ : syracuseStep 19400057 = 14550043) B14550043
theorem B12933371 : Blo 2017435 12933371 := bstep (se 1 (by rfl) ⟨9700028, by rfl⟩ : syracuseStep 12933371 = 19400057) B19400057
theorem B34488989 : Blo 2017435 34488989 := bstep (se 3 (by rfl) ⟨6466685, by rfl⟩ : syracuseStep 34488989 = 12933371) B12933371
theorem B22992659 : Blo 2017435 22992659 := bstep (se 1 (by rfl) ⟨17244494, by rfl⟩ : syracuseStep 22992659 = 34488989) B34488989
theorem B15328439 : Blo 2017435 15328439 := bstep (se 1 (by rfl) ⟨11496329, by rfl⟩ : syracuseStep 15328439 = 22992659) B22992659
theorem B10218959 : Blo 2017435 10218959 := bstep (se 1 (by rfl) ⟨7664219, by rfl⟩ : syracuseStep 10218959 = 15328439) B15328439
theorem B6812639 : Blo 2017435 6812639 := bstep (se 1 (by rfl) ⟨5109479, by rfl⟩ : syracuseStep 6812639 = 10218959) B10218959
theorem B4541759 : Blo 2017435 4541759 := bstep (se 1 (by rfl) ⟨3406319, by rfl⟩ : syracuseStep 4541759 = 6812639) B6812639
theorem B3027839 : Blo 2017435 3027839 := bstep (se 1 (by rfl) ⟨2270879, by rfl⟩ : syracuseStep 3027839 = 4541759) B4541759
theorem B2018559 : Blo 2017435 2018559 := bstep (se 1 (by rfl) ⟨1513919, by rfl⟩ : syracuseStep 2018559 = 3027839) B3027839
theorem B3027845 : Blo 2017435 3027845 := bbase (se 4 (by rfl) ⟨283860, by rfl⟩ : syracuseStep 3027845 = 567721) (by norm_num)
theorem B2018563 : Blo 2017435 2018563 := bstep (se 1 (by rfl) ⟨1513922, by rfl⟩ : syracuseStep 2018563 = 3027845) B3027845
theorem B3406333 : Blo 2017435 3406333 := bbase (se 3 (by rfl) ⟨638687, by rfl⟩ : syracuseStep 3406333 = 1277375) (by norm_num)
theorem B4541777 : Blo 2017435 4541777 := bstep (se 2 (by rfl) ⟨1703166, by rfl⟩ : syracuseStep 4541777 = 3406333) B3406333
theorem B3027851 : Blo 2017435 3027851 := bstep (se 1 (by rfl) ⟨2270888, by rfl⟩ : syracuseStep 3027851 = 4541777) B4541777
theorem B2018567 : Blo 2017435 2018567 := bstep (se 1 (by rfl) ⟨1513925, by rfl⟩ : syracuseStep 2018567 = 3027851) B3027851
theorem B2270893 : Blo 2017435 2270893 := bbase (se 3 (by rfl) ⟨425792, by rfl⟩ : syracuseStep 2270893 = 851585) (by norm_num)
theorem B3027857 : Blo 2017435 3027857 := bstep (se 2 (by rfl) ⟨1135446, by rfl⟩ : syracuseStep 3027857 = 2270893) B2270893
theorem B2018571 : Blo 2017435 2018571 := bstep (se 1 (by rfl) ⟨1513928, by rfl⟩ : syracuseStep 2018571 = 3027857) B3027857
theorem B6812693 : Blo 2017435 6812693 := bbase (se 6 (by rfl) ⟨159672, by rfl⟩ : syracuseStep 6812693 = 319345) (by norm_num)
theorem B4541795 : Blo 2017435 4541795 := bstep (se 1 (by rfl) ⟨3406346, by rfl⟩ : syracuseStep 4541795 = 6812693) B6812693
theorem B3027863 : Blo 2017435 3027863 := bstep (se 1 (by rfl) ⟨2270897, by rfl⟩ : syracuseStep 3027863 = 4541795) B4541795
theorem B2018575 : Blo 2017435 2018575 := bstep (se 1 (by rfl) ⟨1513931, by rfl⟩ : syracuseStep 2018575 = 3027863) B3027863
theorem B3027869 : Blo 2017435 3027869 := bbase (se 3 (by rfl) ⟨567725, by rfl⟩ : syracuseStep 3027869 = 1135451) (by norm_num)
theorem B2018579 : Blo 2017435 2018579 := bstep (se 1 (by rfl) ⟨1513934, by rfl⟩ : syracuseStep 2018579 = 3027869) B3027869
theorem B4541813 : Blo 2017435 4541813 := bbase (se 5 (by rfl) ⟨212897, by rfl⟩ : syracuseStep 4541813 = 425795) (by norm_num)
theorem B3027875 : Blo 2017435 3027875 := bstep (se 1 (by rfl) ⟨2270906, by rfl⟩ : syracuseStep 3027875 = 4541813) B4541813
theorem B2018583 : Blo 2017435 2018583 := bstep (se 1 (by rfl) ⟨1513937, by rfl⟩ : syracuseStep 2018583 = 3027875) B3027875
theorem B9700165 : Blo 2017435 9700165 := bbase (se 4 (by rfl) ⟨909390, by rfl⟩ : syracuseStep 9700165 = 1818781) (by norm_num)
theorem B12933553 : Blo 2017435 12933553 := bstep (se 2 (by rfl) ⟨4850082, by rfl⟩ : syracuseStep 12933553 = 9700165) B9700165
theorem B17244737 : Blo 2017435 17244737 := bstep (se 2 (by rfl) ⟨6466776, by rfl⟩ : syracuseStep 17244737 = 12933553) B12933553
theorem B11496491 : Blo 2017435 11496491 := bstep (se 1 (by rfl) ⟨8622368, by rfl⟩ : syracuseStep 11496491 = 17244737) B17244737
theorem B7664327 : Blo 2017435 7664327 := bstep (se 1 (by rfl) ⟨5748245, by rfl⟩ : syracuseStep 7664327 = 11496491) B11496491
theorem B5109551 : Blo 2017435 5109551 := bstep (se 1 (by rfl) ⟨3832163, by rfl⟩ : syracuseStep 5109551 = 7664327) B7664327
theorem B3406367 : Blo 2017435 3406367 := bstep (se 1 (by rfl) ⟨2554775, by rfl⟩ : syracuseStep 3406367 = 5109551) B5109551
theorem B2270911 : Blo 2017435 2270911 := bstep (se 1 (by rfl) ⟨1703183, by rfl⟩ : syracuseStep 2270911 = 3406367) B3406367
theorem B3027881 : Blo 2017435 3027881 := bstep (se 2 (by rfl) ⟨1135455, by rfl⟩ : syracuseStep 3027881 = 2270911) B2270911
theorem B2018587 : Blo 2017435 2018587 := bstep (se 1 (by rfl) ⟨1513940, by rfl⟩ : syracuseStep 2018587 = 3027881) B3027881
theorem B7664341 : Blo 2017435 7664341 := bbase (se 7 (by rfl) ⟨89816, by rfl⟩ : syracuseStep 7664341 = 179633) (by norm_num)
theorem B10219121 : Blo 2017435 10219121 := bstep (se 2 (by rfl) ⟨3832170, by rfl⟩ : syracuseStep 10219121 = 7664341) B7664341
theorem B6812747 : Blo 2017435 6812747 := bstep (se 1 (by rfl) ⟨5109560, by rfl⟩ : syracuseStep 6812747 = 10219121) B10219121
theorem B4541831 : Blo 2017435 4541831 := bstep (se 1 (by rfl) ⟨3406373, by rfl⟩ : syracuseStep 4541831 = 6812747) B6812747
theorem B3027887 : Blo 2017435 3027887 := bstep (se 1 (by rfl) ⟨2270915, by rfl⟩ : syracuseStep 3027887 = 4541831) B4541831
theorem B2018591 : Blo 2017435 2018591 := bstep (se 1 (by rfl) ⟨1513943, by rfl⟩ : syracuseStep 2018591 = 3027887) B3027887
theorem B3027893 : Blo 2017435 3027893 := bbase (se 5 (by rfl) ⟨141932, by rfl⟩ : syracuseStep 3027893 = 283865) (by norm_num)
theorem B2018595 : Blo 2017435 2018595 := bstep (se 1 (by rfl) ⟨1513946, by rfl⟩ : syracuseStep 2018595 = 3027893) B3027893
theorem B5109581 : Blo 2017435 5109581 := bbase (se 3 (by rfl) ⟨958046, by rfl⟩ : syracuseStep 5109581 = 1916093) (by norm_num)
theorem B3406387 : Blo 2017435 3406387 := bstep (se 1 (by rfl) ⟨2554790, by rfl⟩ : syracuseStep 3406387 = 5109581) B5109581
theorem B4541849 : Blo 2017435 4541849 := bstep (se 2 (by rfl) ⟨1703193, by rfl⟩ : syracuseStep 4541849 = 3406387) B3406387
theorem B3027899 : Blo 2017435 3027899 := bstep (se 1 (by rfl) ⟨2270924, by rfl⟩ : syracuseStep 3027899 = 4541849) B4541849
theorem B2018599 : Blo 2017435 2018599 := bstep (se 1 (by rfl) ⟨1513949, by rfl⟩ : syracuseStep 2018599 = 3027899) B3027899
theorem B2270929 : Blo 2017435 2270929 := bbase (se 2 (by rfl) ⟨851598, by rfl⟩ : syracuseStep 2270929 = 1703197) (by norm_num)
theorem B3027905 : Blo 2017435 3027905 := bstep (se 2 (by rfl) ⟨1135464, by rfl⟩ : syracuseStep 3027905 = 2270929) B2270929
theorem B2018603 : Blo 2017435 2018603 := bstep (se 1 (by rfl) ⟨1513952, by rfl⟩ : syracuseStep 2018603 = 3027905) B3027905
theorem B4603837 : Blo 2017435 4603837 := bbase (se 3 (by rfl) ⟨863219, by rfl⟩ : syracuseStep 4603837 = 1726439) (by norm_num)
theorem B6138449 : Blo 2017435 6138449 := bstep (se 2 (by rfl) ⟨2301918, by rfl⟩ : syracuseStep 6138449 = 4603837) B4603837
theorem B4092299 : Blo 2017435 4092299 := bstep (se 1 (by rfl) ⟨3069224, by rfl⟩ : syracuseStep 4092299 = 6138449) B6138449
theorem B2728199 : Blo 2017435 2728199 := bstep (se 1 (by rfl) ⟨2046149, by rfl⟩ : syracuseStep 2728199 = 4092299) B4092299
theorem B7275197 : Blo 2017435 7275197 := bstep (se 3 (by rfl) ⟨1364099, by rfl⟩ : syracuseStep 7275197 = 2728199) B2728199
theorem B4850131 : Blo 2017435 4850131 := bstep (se 1 (by rfl) ⟨3637598, by rfl⟩ : syracuseStep 4850131 = 7275197) B7275197
theorem B6466841 : Blo 2017435 6466841 := bstep (se 2 (by rfl) ⟨2425065, by rfl⟩ : syracuseStep 6466841 = 4850131) B4850131
theorem B4311227 : Blo 2017435 4311227 := bstep (se 1 (by rfl) ⟨3233420, by rfl⟩ : syracuseStep 4311227 = 6466841) B6466841
theorem B2874151 : Blo 2017435 2874151 := bstep (se 1 (by rfl) ⟨2155613, by rfl⟩ : syracuseStep 2874151 = 4311227) B4311227
theorem B3832201 : Blo 2017435 3832201 := bstep (se 2 (by rfl) ⟨1437075, by rfl⟩ : syracuseStep 3832201 = 2874151) B2874151
theorem B5109601 : Blo 2017435 5109601 := bstep (se 2 (by rfl) ⟨1916100, by rfl⟩ : syracuseStep 5109601 = 3832201) B3832201
theorem B6812801 : Blo 2017435 6812801 := bstep (se 2 (by rfl) ⟨2554800, by rfl⟩ : syracuseStep 6812801 = 5109601) B5109601
theorem B4541867 : Blo 2017435 4541867 := bstep (se 1 (by rfl) ⟨3406400, by rfl⟩ : syracuseStep 4541867 = 6812801) B6812801
theorem B3027911 : Blo 2017435 3027911 := bstep (se 1 (by rfl) ⟨2270933, by rfl⟩ : syracuseStep 3027911 = 4541867) B4541867
theorem B2018607 : Blo 2017435 2018607 := bstep (se 1 (by rfl) ⟨1513955, by rfl⟩ : syracuseStep 2018607 = 3027911) B3027911
theorem B3027917 : Blo 2017435 3027917 := bbase (se 3 (by rfl) ⟨567734, by rfl⟩ : syracuseStep 3027917 = 1135469) (by norm_num)
theorem B2018611 : Blo 2017435 2018611 := bstep (se 1 (by rfl) ⟨1513958, by rfl⟩ : syracuseStep 2018611 = 3027917) B3027917
theorem B4541885 : Blo 2017435 4541885 := bbase (se 3 (by rfl) ⟨851603, by rfl⟩ : syracuseStep 4541885 = 1703207) (by norm_num)
theorem B3027923 : Blo 2017435 3027923 := bstep (se 1 (by rfl) ⟨2270942, by rfl⟩ : syracuseStep 3027923 = 4541885) B4541885
theorem B2018615 : Blo 2017435 2018615 := bstep (se 1 (by rfl) ⟨1513961, by rfl⟩ : syracuseStep 2018615 = 3027923) B3027923
theorem B3406421 : Blo 2017435 3406421 := bbase (se 8 (by rfl) ⟨19959, by rfl⟩ : syracuseStep 3406421 = 39919) (by norm_num)
theorem B2270947 : Blo 2017435 2270947 := bstep (se 1 (by rfl) ⟨1703210, by rfl⟩ : syracuseStep 2270947 = 3406421) B3406421
theorem B3027929 : Blo 2017435 3027929 := bstep (se 2 (by rfl) ⟨1135473, by rfl⟩ : syracuseStep 3027929 = 2270947) B2270947
theorem B2018619 : Blo 2017435 2018619 := bstep (se 1 (by rfl) ⟨1513964, by rfl⟩ : syracuseStep 2018619 = 3027929) B3027929
theorem B7275253 : Blo 2017435 7275253 := bbase (se 5 (by rfl) ⟨341027, by rfl⟩ : syracuseStep 7275253 = 682055) (by norm_num)
theorem B9700337 : Blo 2017435 9700337 := bstep (se 2 (by rfl) ⟨3637626, by rfl⟩ : syracuseStep 9700337 = 7275253) B7275253
theorem B6466891 : Blo 2017435 6466891 := bstep (se 1 (by rfl) ⟨4850168, by rfl⟩ : syracuseStep 6466891 = 9700337) B9700337
theorem B8622521 : Blo 2017435 8622521 := bstep (se 2 (by rfl) ⟨3233445, by rfl⟩ : syracuseStep 8622521 = 6466891) B6466891
theorem B5748347 : Blo 2017435 5748347 := bstep (se 1 (by rfl) ⟨4311260, by rfl⟩ : syracuseStep 5748347 = 8622521) B8622521
theorem B15328925 : Blo 2017435 15328925 := bstep (se 3 (by rfl) ⟨2874173, by rfl⟩ : syracuseStep 15328925 = 5748347) B5748347
theorem B10219283 : Blo 2017435 10219283 := bstep (se 1 (by rfl) ⟨7664462, by rfl⟩ : syracuseStep 10219283 = 15328925) B15328925
theorem B6812855 : Blo 2017435 6812855 := bstep (se 1 (by rfl) ⟨5109641, by rfl⟩ : syracuseStep 6812855 = 10219283) B10219283
theorem B4541903 : Blo 2017435 4541903 := bstep (se 1 (by rfl) ⟨3406427, by rfl⟩ : syracuseStep 4541903 = 6812855) B6812855
theorem B3027935 : Blo 2017435 3027935 := bstep (se 1 (by rfl) ⟨2270951, by rfl⟩ : syracuseStep 3027935 = 4541903) B4541903
theorem B2018623 : Blo 2017435 2018623 := bstep (se 1 (by rfl) ⟨1513967, by rfl⟩ : syracuseStep 2018623 = 3027935) B3027935
theorem B3027941 : Blo 2017435 3027941 := bbase (se 4 (by rfl) ⟨283869, by rfl⟩ : syracuseStep 3027941 = 567739) (by norm_num)
theorem B2018627 : Blo 2017435 2018627 := bstep (se 1 (by rfl) ⟨1513970, by rfl⟩ : syracuseStep 2018627 = 3027941) B3027941
theorem B4850189 : Blo 2017435 4850189 := bbase (se 3 (by rfl) ⟨909410, by rfl⟩ : syracuseStep 4850189 = 1818821) (by norm_num)
theorem B3233459 : Blo 2017435 3233459 := bstep (se 1 (by rfl) ⟨2425094, by rfl⟩ : syracuseStep 3233459 = 4850189) B4850189
theorem B8622557 : Blo 2017435 8622557 := bstep (se 3 (by rfl) ⟨1616729, by rfl⟩ : syracuseStep 8622557 = 3233459) B3233459
theorem B5748371 : Blo 2017435 5748371 := bstep (se 1 (by rfl) ⟨4311278, by rfl⟩ : syracuseStep 5748371 = 8622557) B8622557
theorem B3832247 : Blo 2017435 3832247 := bstep (se 1 (by rfl) ⟨2874185, by rfl⟩ : syracuseStep 3832247 = 5748371) B5748371
theorem B2554831 : Blo 2017435 2554831 := bstep (se 1 (by rfl) ⟨1916123, by rfl⟩ : syracuseStep 2554831 = 3832247) B3832247
theorem B3406441 : Blo 2017435 3406441 := bstep (se 2 (by rfl) ⟨1277415, by rfl⟩ : syracuseStep 3406441 = 2554831) B2554831
theorem B4541921 : Blo 2017435 4541921 := bstep (se 2 (by rfl) ⟨1703220, by rfl⟩ : syracuseStep 4541921 = 3406441) B3406441
theorem B3027947 : Blo 2017435 3027947 := bstep (se 1 (by rfl) ⟨2270960, by rfl⟩ : syracuseStep 3027947 = 4541921) B4541921
theorem B2018631 : Blo 2017435 2018631 := bstep (se 1 (by rfl) ⟨1513973, by rfl⟩ : syracuseStep 2018631 = 3027947) B3027947
theorem B2270965 : Blo 2017435 2270965 := bbase (se 5 (by rfl) ⟨106451, by rfl⟩ : syracuseStep 2270965 = 212903) (by norm_num)
theorem B3027953 : Blo 2017435 3027953 := bstep (se 2 (by rfl) ⟨1135482, by rfl⟩ : syracuseStep 3027953 = 2270965) B2270965
theorem B2018635 : Blo 2017435 2018635 := bstep (se 1 (by rfl) ⟨1513976, by rfl⟩ : syracuseStep 2018635 = 3027953) B3027953
theorem B2554841 : Blo 2017435 2554841 := bbase (se 2 (by rfl) ⟨958065, by rfl⟩ : syracuseStep 2554841 = 1916131) (by norm_num)
theorem B6812909 : Blo 2017435 6812909 := bstep (se 3 (by rfl) ⟨1277420, by rfl⟩ : syracuseStep 6812909 = 2554841) B2554841
theorem B4541939 : Blo 2017435 4541939 := bstep (se 1 (by rfl) ⟨3406454, by rfl⟩ : syracuseStep 4541939 = 6812909) B6812909
theorem B3027959 : Blo 2017435 3027959 := bstep (se 1 (by rfl) ⟨2270969, by rfl⟩ : syracuseStep 3027959 = 4541939) B4541939
theorem B2018639 : Blo 2017435 2018639 := bstep (se 1 (by rfl) ⟨1513979, by rfl⟩ : syracuseStep 2018639 = 3027959) B3027959
theorem B3027965 : Blo 2017435 3027965 := bbase (se 3 (by rfl) ⟨567743, by rfl⟩ : syracuseStep 3027965 = 1135487) (by norm_num)
theorem B2018643 : Blo 2017435 2018643 := bstep (se 1 (by rfl) ⟨1513982, by rfl⟩ : syracuseStep 2018643 = 3027965) B3027965
theorem B4541957 : Blo 2017435 4541957 := bbase (se 4 (by rfl) ⟨425808, by rfl⟩ : syracuseStep 4541957 = 851617) (by norm_num)
theorem B3027971 : Blo 2017435 3027971 := bstep (se 1 (by rfl) ⟨2270978, by rfl⟩ : syracuseStep 3027971 = 4541957) B4541957
theorem B2018647 : Blo 2017435 2018647 := bstep (se 1 (by rfl) ⟨1513985, by rfl⟩ : syracuseStep 2018647 = 3027971) B3027971
theorem B3832285 : Blo 2017435 3832285 := bbase (se 3 (by rfl) ⟨718553, by rfl⟩ : syracuseStep 3832285 = 1437107) (by norm_num)
theorem B5109713 : Blo 2017435 5109713 := bstep (se 2 (by rfl) ⟨1916142, by rfl⟩ : syracuseStep 5109713 = 3832285) B3832285
theorem B3406475 : Blo 2017435 3406475 := bstep (se 1 (by rfl) ⟨2554856, by rfl⟩ : syracuseStep 3406475 = 5109713) B5109713
theorem B2270983 : Blo 2017435 2270983 := bstep (se 1 (by rfl) ⟨1703237, by rfl⟩ : syracuseStep 2270983 = 3406475) B3406475
theorem B3027977 : Blo 2017435 3027977 := bstep (se 2 (by rfl) ⟨1135491, by rfl⟩ : syracuseStep 3027977 = 2270983) B2270983
theorem B2018651 : Blo 2017435 2018651 := bstep (se 1 (by rfl) ⟨1513988, by rfl⟩ : syracuseStep 2018651 = 3027977) B3027977
theorem B10219445 : Blo 2017435 10219445 := bbase (se 5 (by rfl) ⟨479036, by rfl⟩ : syracuseStep 10219445 = 958073) (by norm_num)
theorem B6812963 : Blo 2017435 6812963 := bstep (se 1 (by rfl) ⟨5109722, by rfl⟩ : syracuseStep 6812963 = 10219445) B10219445
theorem B4541975 : Blo 2017435 4541975 := bstep (se 1 (by rfl) ⟨3406481, by rfl⟩ : syracuseStep 4541975 = 6812963) B6812963
theorem B3027983 : Blo 2017435 3027983 := bstep (se 1 (by rfl) ⟨2270987, by rfl⟩ : syracuseStep 3027983 = 4541975) B4541975
theorem B2018655 : Blo 2017435 2018655 := bstep (se 1 (by rfl) ⟨1513991, by rfl⟩ : syracuseStep 2018655 = 3027983) B3027983
theorem B3027989 : Blo 2017435 3027989 := bbase (se 6 (by rfl) ⟨70968, by rfl⟩ : syracuseStep 3027989 = 141937) (by norm_num)
theorem B2018659 : Blo 2017435 2018659 := bstep (se 1 (by rfl) ⟨1513994, by rfl⟩ : syracuseStep 2018659 = 3027989) B3027989
theorem B29101589 : Blo 2017435 29101589 := bbase (se 6 (by rfl) ⟨682068, by rfl⟩ : syracuseStep 29101589 = 1364137) (by norm_num)
theorem B19401059 : Blo 2017435 19401059 := bstep (se 1 (by rfl) ⟨14550794, by rfl⟩ : syracuseStep 19401059 = 29101589) B29101589
theorem B12934039 : Blo 2017435 12934039 := bstep (se 1 (by rfl) ⟨9700529, by rfl⟩ : syracuseStep 12934039 = 19401059) B19401059
theorem B17245385 : Blo 2017435 17245385 := bstep (se 2 (by rfl) ⟨6467019, by rfl⟩ : syracuseStep 17245385 = 12934039) B12934039
theorem B11496923 : Blo 2017435 11496923 := bstep (se 1 (by rfl) ⟨8622692, by rfl⟩ : syracuseStep 11496923 = 17245385) B17245385
theorem B7664615 : Blo 2017435 7664615 := bstep (se 1 (by rfl) ⟨5748461, by rfl⟩ : syracuseStep 7664615 = 11496923) B11496923
theorem B5109743 : Blo 2017435 5109743 := bstep (se 1 (by rfl) ⟨3832307, by rfl⟩ : syracuseStep 5109743 = 7664615) B7664615
theorem B3406495 : Blo 2017435 3406495 := bstep (se 1 (by rfl) ⟨2554871, by rfl⟩ : syracuseStep 3406495 = 5109743) B5109743
theorem B4541993 : Blo 2017435 4541993 := bstep (se 2 (by rfl) ⟨1703247, by rfl⟩ : syracuseStep 4541993 = 3406495) B3406495
theorem B3027995 : Blo 2017435 3027995 := bstep (se 1 (by rfl) ⟨2270996, by rfl⟩ : syracuseStep 3027995 = 4541993) B4541993
theorem B2018663 : Blo 2017435 2018663 := bstep (se 1 (by rfl) ⟨1513997, by rfl⟩ : syracuseStep 2018663 = 3027995) B3027995
theorem B2271001 : Blo 2017435 2271001 := bbase (se 2 (by rfl) ⟨851625, by rfl⟩ : syracuseStep 2271001 = 1703251) (by norm_num)
theorem B3028001 : Blo 2017435 3028001 := bstep (se 2 (by rfl) ⟨1135500, by rfl⟩ : syracuseStep 3028001 = 2271001) B2271001
theorem B2018667 : Blo 2017435 2018667 := bstep (se 1 (by rfl) ⟨1514000, by rfl⟩ : syracuseStep 2018667 = 3028001) B3028001
theorem B7664645 : Blo 2017435 7664645 := bbase (se 4 (by rfl) ⟨718560, by rfl⟩ : syracuseStep 7664645 = 1437121) (by norm_num)
theorem B5109763 : Blo 2017435 5109763 := bstep (se 1 (by rfl) ⟨3832322, by rfl⟩ : syracuseStep 5109763 = 7664645) B7664645
theorem B6813017 : Blo 2017435 6813017 := bstep (se 2 (by rfl) ⟨2554881, by rfl⟩ : syracuseStep 6813017 = 5109763) B5109763
theorem B4542011 : Blo 2017435 4542011 := bstep (se 1 (by rfl) ⟨3406508, by rfl⟩ : syracuseStep 4542011 = 6813017) B6813017
theorem B3028007 : Blo 2017435 3028007 := bstep (se 1 (by rfl) ⟨2271005, by rfl⟩ : syracuseStep 3028007 = 4542011) B4542011
theorem B2018671 : Blo 2017435 2018671 := bstep (se 1 (by rfl) ⟨1514003, by rfl⟩ : syracuseStep 2018671 = 3028007) B3028007
theorem B3028013 : Blo 2017435 3028013 := bbase (se 3 (by rfl) ⟨567752, by rfl⟩ : syracuseStep 3028013 = 1135505) (by norm_num)
theorem B2018675 : Blo 2017435 2018675 := bstep (se 1 (by rfl) ⟨1514006, by rfl⟩ : syracuseStep 2018675 = 3028013) B3028013
theorem B4542029 : Blo 2017435 4542029 := bbase (se 3 (by rfl) ⟨851630, by rfl⟩ : syracuseStep 4542029 = 1703261) (by norm_num)
theorem B3028019 : Blo 2017435 3028019 := bstep (se 1 (by rfl) ⟨2271014, by rfl⟩ : syracuseStep 3028019 = 4542029) B4542029
theorem B2018679 : Blo 2017435 2018679 := bstep (se 1 (by rfl) ⟨1514009, by rfl⟩ : syracuseStep 2018679 = 3028019) B3028019
theorem B2554897 : Blo 2017435 2554897 := bbase (se 2 (by rfl) ⟨958086, by rfl⟩ : syracuseStep 2554897 = 1916173) (by norm_num)
theorem B3406529 : Blo 2017435 3406529 := bstep (se 2 (by rfl) ⟨1277448, by rfl⟩ : syracuseStep 3406529 = 2554897) B2554897
theorem B2271019 : Blo 2017435 2271019 := bstep (se 1 (by rfl) ⟨1703264, by rfl⟩ : syracuseStep 2271019 = 3406529) B3406529
theorem B3028025 : Blo 2017435 3028025 := bstep (se 2 (by rfl) ⟨1135509, by rfl⟩ : syracuseStep 3028025 = 2271019) B2271019
theorem B2018683 : Blo 2017435 2018683 := bstep (se 1 (by rfl) ⟨1514012, by rfl⟩ : syracuseStep 2018683 = 3028025) B3028025
theorem B4311397 : Blo 2017435 4311397 := bbase (se 4 (by rfl) ⟨404193, by rfl⟩ : syracuseStep 4311397 = 808387) (by norm_num)
theorem B22994117 : Blo 2017435 22994117 := bstep (se 4 (by rfl) ⟨2155698, by rfl⟩ : syracuseStep 22994117 = 4311397) B4311397
theorem B15329411 : Blo 2017435 15329411 := bstep (se 1 (by rfl) ⟨11497058, by rfl⟩ : syracuseStep 15329411 = 22994117) B22994117
theorem B10219607 : Blo 2017435 10219607 := bstep (se 1 (by rfl) ⟨7664705, by rfl⟩ : syracuseStep 10219607 = 15329411) B15329411
theorem B6813071 : Blo 2017435 6813071 := bstep (se 1 (by rfl) ⟨5109803, by rfl⟩ : syracuseStep 6813071 = 10219607) B10219607
theorem B4542047 : Blo 2017435 4542047 := bstep (se 1 (by rfl) ⟨3406535, by rfl⟩ : syracuseStep 4542047 = 6813071) B6813071
theorem B3028031 : Blo 2017435 3028031 := bstep (se 1 (by rfl) ⟨2271023, by rfl⟩ : syracuseStep 3028031 = 4542047) B4542047
theorem B2018687 : Blo 2017435 2018687 := bstep (se 1 (by rfl) ⟨1514015, by rfl⟩ : syracuseStep 2018687 = 3028031) B3028031
theorem B3028037 : Blo 2017435 3028037 := bbase (se 4 (by rfl) ⟨283878, by rfl⟩ : syracuseStep 3028037 = 567757) (by norm_num)
theorem B2018691 : Blo 2017435 2018691 := bstep (se 1 (by rfl) ⟨1514018, by rfl⟩ : syracuseStep 2018691 = 3028037) B3028037
theorem B3406549 : Blo 2017435 3406549 := bbase (se 7 (by rfl) ⟨39920, by rfl⟩ : syracuseStep 3406549 = 79841) (by norm_num)
theorem B4542065 : Blo 2017435 4542065 := bstep (se 2 (by rfl) ⟨1703274, by rfl⟩ : syracuseStep 4542065 = 3406549) B3406549
theorem B3028043 : Blo 2017435 3028043 := bstep (se 1 (by rfl) ⟨2271032, by rfl⟩ : syracuseStep 3028043 = 4542065) B4542065
theorem B2018695 : Blo 2017435 2018695 := bstep (se 1 (by rfl) ⟨1514021, by rfl⟩ : syracuseStep 2018695 = 3028043) B3028043
theorem B2271037 : Blo 2017435 2271037 := bbase (se 3 (by rfl) ⟨425819, by rfl⟩ : syracuseStep 2271037 = 851639) (by norm_num)
theorem B3028049 : Blo 2017435 3028049 := bstep (se 2 (by rfl) ⟨1135518, by rfl⟩ : syracuseStep 3028049 = 2271037) B2271037
theorem B2018699 : Blo 2017435 2018699 := bstep (se 1 (by rfl) ⟨1514024, by rfl⟩ : syracuseStep 2018699 = 3028049) B3028049
theorem B6813125 : Blo 2017435 6813125 := bbase (se 4 (by rfl) ⟨638730, by rfl⟩ : syracuseStep 6813125 = 1277461) (by norm_num)
theorem B4542083 : Blo 2017435 4542083 := bstep (se 1 (by rfl) ⟨3406562, by rfl⟩ : syracuseStep 4542083 = 6813125) B6813125
theorem B3028055 : Blo 2017435 3028055 := bstep (se 1 (by rfl) ⟨2271041, by rfl⟩ : syracuseStep 3028055 = 4542083) B4542083
theorem B2018703 : Blo 2017435 2018703 := bstep (se 1 (by rfl) ⟨1514027, by rfl⟩ : syracuseStep 2018703 = 3028055) B3028055
theorem B3028061 : Blo 2017435 3028061 := bbase (se 3 (by rfl) ⟨567761, by rfl⟩ : syracuseStep 3028061 = 1135523) (by norm_num)
theorem B2018707 : Blo 2017435 2018707 := bstep (se 1 (by rfl) ⟨1514030, by rfl⟩ : syracuseStep 2018707 = 3028061) B3028061
theorem B4542101 : Blo 2017435 4542101 := bbase (se 6 (by rfl) ⟨106455, by rfl⟩ : syracuseStep 4542101 = 212911) (by norm_num)
theorem B3028067 : Blo 2017435 3028067 := bstep (se 1 (by rfl) ⟨2271050, by rfl⟩ : syracuseStep 3028067 = 4542101) B4542101
theorem B2018711 : Blo 2017435 2018711 := bstep (se 1 (by rfl) ⟨1514033, by rfl⟩ : syracuseStep 2018711 = 3028067) B3028067
theorem B2155729 : Blo 2017435 2155729 := bbase (se 2 (by rfl) ⟨808398, by rfl⟩ : syracuseStep 2155729 = 1616797) (by norm_num)
theorem B2874305 : Blo 2017435 2874305 := bstep (se 2 (by rfl) ⟨1077864, by rfl⟩ : syracuseStep 2874305 = 2155729) B2155729
theorem B7664813 : Blo 2017435 7664813 := bstep (se 3 (by rfl) ⟨1437152, by rfl⟩ : syracuseStep 7664813 = 2874305) B2874305
theorem B5109875 : Blo 2017435 5109875 := bstep (se 1 (by rfl) ⟨3832406, by rfl⟩ : syracuseStep 5109875 = 7664813) B7664813
theorem B3406583 : Blo 2017435 3406583 := bstep (se 1 (by rfl) ⟨2554937, by rfl⟩ : syracuseStep 3406583 = 5109875) B5109875
theorem B2271055 : Blo 2017435 2271055 := bstep (se 1 (by rfl) ⟨1703291, by rfl⟩ : syracuseStep 2271055 = 3406583) B3406583
theorem B3028073 : Blo 2017435 3028073 := bstep (se 2 (by rfl) ⟨1135527, by rfl⟩ : syracuseStep 3028073 = 2271055) B2271055
theorem B2018715 : Blo 2017435 2018715 := bstep (se 1 (by rfl) ⟨1514036, by rfl⟩ : syracuseStep 2018715 = 3028073) B3028073
theorem B9208181 : Blo 2017435 9208181 := bbase (se 5 (by rfl) ⟨431633, by rfl⟩ : syracuseStep 9208181 = 863267) (by norm_num)
theorem B24555149 : Blo 2017435 24555149 := bstep (se 3 (by rfl) ⟨4604090, by rfl⟩ : syracuseStep 24555149 = 9208181) B9208181
theorem B16370099 : Blo 2017435 16370099 := bstep (se 1 (by rfl) ⟨12277574, by rfl⟩ : syracuseStep 16370099 = 24555149) B24555149
theorem B10913399 : Blo 2017435 10913399 := bstep (se 1 (by rfl) ⟨8185049, by rfl⟩ : syracuseStep 10913399 = 16370099) B16370099
theorem B7275599 : Blo 2017435 7275599 := bstep (se 1 (by rfl) ⟨5456699, by rfl⟩ : syracuseStep 7275599 = 10913399) B10913399
theorem B4850399 : Blo 2017435 4850399 := bstep (se 1 (by rfl) ⟨3637799, by rfl⟩ : syracuseStep 4850399 = 7275599) B7275599
theorem B12934397 : Blo 2017435 12934397 := bstep (se 3 (by rfl) ⟨2425199, by rfl⟩ : syracuseStep 12934397 = 4850399) B4850399
theorem B8622931 : Blo 2017435 8622931 := bstep (se 1 (by rfl) ⟨6467198, by rfl⟩ : syracuseStep 8622931 = 12934397) B12934397
theorem B11497241 : Blo 2017435 11497241 := bstep (se 2 (by rfl) ⟨4311465, by rfl⟩ : syracuseStep 11497241 = 8622931) B8622931
theorem B7664827 : Blo 2017435 7664827 := bstep (se 1 (by rfl) ⟨5748620, by rfl⟩ : syracuseStep 7664827 = 11497241) B11497241
theorem B10219769 : Blo 2017435 10219769 := bstep (se 2 (by rfl) ⟨3832413, by rfl⟩ : syracuseStep 10219769 = 7664827) B7664827
theorem B6813179 : Blo 2017435 6813179 := bstep (se 1 (by rfl) ⟨5109884, by rfl⟩ : syracuseStep 6813179 = 10219769) B10219769
theorem B4542119 : Blo 2017435 4542119 := bstep (se 1 (by rfl) ⟨3406589, by rfl⟩ : syracuseStep 4542119 = 6813179) B6813179
theorem B3028079 : Blo 2017435 3028079 := bstep (se 1 (by rfl) ⟨2271059, by rfl⟩ : syracuseStep 3028079 = 4542119) B4542119
theorem B2018719 : Blo 2017435 2018719 := bstep (se 1 (by rfl) ⟨1514039, by rfl⟩ : syracuseStep 2018719 = 3028079) B3028079
theorem B3028085 : Blo 2017435 3028085 := bbase (se 5 (by rfl) ⟨141941, by rfl⟩ : syracuseStep 3028085 = 283883) (by norm_num)
theorem B2018723 : Blo 2017435 2018723 := bstep (se 1 (by rfl) ⟨1514042, by rfl⟩ : syracuseStep 2018723 = 3028085) B3028085
theorem B3832429 : Blo 2017435 3832429 := bbase (se 3 (by rfl) ⟨718580, by rfl⟩ : syracuseStep 3832429 = 1437161) (by norm_num)
theorem B5109905 : Blo 2017435 5109905 := bstep (se 2 (by rfl) ⟨1916214, by rfl⟩ : syracuseStep 5109905 = 3832429) B3832429
theorem B3406603 : Blo 2017435 3406603 := bstep (se 1 (by rfl) ⟨2554952, by rfl⟩ : syracuseStep 3406603 = 5109905) B5109905
theorem B4542137 : Blo 2017435 4542137 := bstep (se 2 (by rfl) ⟨1703301, by rfl⟩ : syracuseStep 4542137 = 3406603) B3406603
theorem B3028091 : Blo 2017435 3028091 := bstep (se 1 (by rfl) ⟨2271068, by rfl⟩ : syracuseStep 3028091 = 4542137) B4542137
theorem B2018727 : Blo 2017435 2018727 := bstep (se 1 (by rfl) ⟨1514045, by rfl⟩ : syracuseStep 2018727 = 3028091) B3028091
theorem B2271073 : Blo 2017435 2271073 := bbase (se 2 (by rfl) ⟨851652, by rfl⟩ : syracuseStep 2271073 = 1703305) (by norm_num)
theorem B3028097 : Blo 2017435 3028097 := bstep (se 2 (by rfl) ⟨1135536, by rfl⟩ : syracuseStep 3028097 = 2271073) B2271073
theorem B2018731 : Blo 2017435 2018731 := bstep (se 1 (by rfl) ⟨1514048, by rfl⟩ : syracuseStep 2018731 = 3028097) B3028097
theorem B5109925 : Blo 2017435 5109925 := bbase (se 4 (by rfl) ⟨479055, by rfl⟩ : syracuseStep 5109925 = 958111) (by norm_num)
theorem B6813233 : Blo 2017435 6813233 := bstep (se 2 (by rfl) ⟨2554962, by rfl⟩ : syracuseStep 6813233 = 5109925) B5109925
theorem B4542155 : Blo 2017435 4542155 := bstep (se 1 (by rfl) ⟨3406616, by rfl⟩ : syracuseStep 4542155 = 6813233) B6813233
theorem B3028103 : Blo 2017435 3028103 := bstep (se 1 (by rfl) ⟨2271077, by rfl⟩ : syracuseStep 3028103 = 4542155) B4542155
theorem B2018735 : Blo 2017435 2018735 := bstep (se 1 (by rfl) ⟨1514051, by rfl⟩ : syracuseStep 2018735 = 3028103) B3028103
theorem B3028109 : Blo 2017435 3028109 := bbase (se 3 (by rfl) ⟨567770, by rfl⟩ : syracuseStep 3028109 = 1135541) (by norm_num)
theorem B2018739 : Blo 2017435 2018739 := bstep (se 1 (by rfl) ⟨1514054, by rfl⟩ : syracuseStep 2018739 = 3028109) B3028109
theorem B4542173 : Blo 2017435 4542173 := bbase (se 3 (by rfl) ⟨851657, by rfl⟩ : syracuseStep 4542173 = 1703315) (by norm_num)
theorem B3028115 : Blo 2017435 3028115 := bstep (se 1 (by rfl) ⟨2271086, by rfl⟩ : syracuseStep 3028115 = 4542173) B4542173
theorem B2018743 : Blo 2017435 2018743 := bstep (se 1 (by rfl) ⟨1514057, by rfl⟩ : syracuseStep 2018743 = 3028115) B3028115
theorem B3406637 : Blo 2017435 3406637 := bbase (se 3 (by rfl) ⟨638744, by rfl⟩ : syracuseStep 3406637 = 1277489) (by norm_num)
theorem B2271091 : Blo 2017435 2271091 := bstep (se 1 (by rfl) ⟨1703318, by rfl⟩ : syracuseStep 2271091 = 3406637) B3406637
theorem B3028121 : Blo 2017435 3028121 := bstep (se 2 (by rfl) ⟨1135545, by rfl⟩ : syracuseStep 3028121 = 2271091) B2271091
theorem B2018747 : Blo 2017435 2018747 := bstep (se 1 (by rfl) ⟨1514060, by rfl⟩ : syracuseStep 2018747 = 3028121) B3028121
theorem B4092589 : Blo 2017435 4092589 := bbase (se 3 (by rfl) ⟨767360, by rfl⟩ : syracuseStep 4092589 = 1534721) (by norm_num)
theorem B21827141 : Blo 2017435 21827141 := bstep (se 4 (by rfl) ⟨2046294, by rfl⟩ : syracuseStep 21827141 = 4092589) B4092589
theorem B14551427 : Blo 2017435 14551427 := bstep (se 1 (by rfl) ⟨10913570, by rfl⟩ : syracuseStep 14551427 = 21827141) B21827141
theorem B38803805 : Blo 2017435 38803805 := bstep (se 3 (by rfl) ⟨7275713, by rfl⟩ : syracuseStep 38803805 = 14551427) B14551427
theorem B25869203 : Blo 2017435 25869203 := bstep (se 1 (by rfl) ⟨19401902, by rfl⟩ : syracuseStep 25869203 = 38803805) B38803805
theorem B17246135 : Blo 2017435 17246135 := bstep (se 1 (by rfl) ⟨12934601, by rfl⟩ : syracuseStep 17246135 = 25869203) B25869203
theorem B11497423 : Blo 2017435 11497423 := bstep (se 1 (by rfl) ⟨8623067, by rfl⟩ : syracuseStep 11497423 = 17246135) B17246135
theorem B15329897 : Blo 2017435 15329897 := bstep (se 2 (by rfl) ⟨5748711, by rfl⟩ : syracuseStep 15329897 = 11497423) B11497423
theorem B10219931 : Blo 2017435 10219931 := bstep (se 1 (by rfl) ⟨7664948, by rfl⟩ : syracuseStep 10219931 = 15329897) B15329897
theorem B6813287 : Blo 2017435 6813287 := bstep (se 1 (by rfl) ⟨5109965, by rfl⟩ : syracuseStep 6813287 = 10219931) B10219931
theorem B4542191 : Blo 2017435 4542191 := bstep (se 1 (by rfl) ⟨3406643, by rfl⟩ : syracuseStep 4542191 = 6813287) B6813287
theorem B3028127 : Blo 2017435 3028127 := bstep (se 1 (by rfl) ⟨2271095, by rfl⟩ : syracuseStep 3028127 = 4542191) B4542191
theorem B2018751 : Blo 2017435 2018751 := bstep (se 1 (by rfl) ⟨1514063, by rfl⟩ : syracuseStep 2018751 = 3028127) B3028127
theorem B3028133 : Blo 2017435 3028133 := bbase (se 4 (by rfl) ⟨283887, by rfl⟩ : syracuseStep 3028133 = 567775) (by norm_num)
theorem B2018755 : Blo 2017435 2018755 := bstep (se 1 (by rfl) ⟨1514066, by rfl⟩ : syracuseStep 2018755 = 3028133) B3028133
theorem B2554993 : Blo 2017435 2554993 := bbase (se 2 (by rfl) ⟨958122, by rfl⟩ : syracuseStep 2554993 = 1916245) (by norm_num)
theorem B3406657 : Blo 2017435 3406657 := bstep (se 2 (by rfl) ⟨1277496, by rfl⟩ : syracuseStep 3406657 = 2554993) B2554993
theorem B4542209 : Blo 2017435 4542209 := bstep (se 2 (by rfl) ⟨1703328, by rfl⟩ : syracuseStep 4542209 = 3406657) B3406657
theorem B3028139 : Blo 2017435 3028139 := bstep (se 1 (by rfl) ⟨2271104, by rfl⟩ : syracuseStep 3028139 = 4542209) B4542209
theorem B2018759 : Blo 2017435 2018759 := bstep (se 1 (by rfl) ⟨1514069, by rfl⟩ : syracuseStep 2018759 = 3028139) B3028139
theorem B2271109 : Blo 2017435 2271109 := bbase (se 4 (by rfl) ⟨212916, by rfl⟩ : syracuseStep 2271109 = 425833) (by norm_num)
theorem B3028145 : Blo 2017435 3028145 := bstep (se 2 (by rfl) ⟨1135554, by rfl⟩ : syracuseStep 3028145 = 2271109) B2271109
theorem B2018763 : Blo 2017435 2018763 := bstep (se 1 (by rfl) ⟨1514072, by rfl⟩ : syracuseStep 2018763 = 3028145) B3028145
theorem B3233677 : Blo 2017435 3233677 := bbase (se 3 (by rfl) ⟨606314, by rfl⟩ : syracuseStep 3233677 = 1212629) (by norm_num)
theorem B4311569 : Blo 2017435 4311569 := bstep (se 2 (by rfl) ⟨1616838, by rfl⟩ : syracuseStep 4311569 = 3233677) B3233677
theorem B2874379 : Blo 2017435 2874379 := bstep (se 1 (by rfl) ⟨2155784, by rfl⟩ : syracuseStep 2874379 = 4311569) B4311569
theorem B3832505 : Blo 2017435 3832505 := bstep (se 2 (by rfl) ⟨1437189, by rfl⟩ : syracuseStep 3832505 = 2874379) B2874379
theorem B2555003 : Blo 2017435 2555003 := bstep (se 1 (by rfl) ⟨1916252, by rfl⟩ : syracuseStep 2555003 = 3832505) B3832505
theorem B6813341 : Blo 2017435 6813341 := bstep (se 3 (by rfl) ⟨1277501, by rfl⟩ : syracuseStep 6813341 = 2555003) B2555003
theorem B4542227 : Blo 2017435 4542227 := bstep (se 1 (by rfl) ⟨3406670, by rfl⟩ : syracuseStep 4542227 = 6813341) B6813341
theorem B3028151 : Blo 2017435 3028151 := bstep (se 1 (by rfl) ⟨2271113, by rfl⟩ : syracuseStep 3028151 = 4542227) B4542227
theorem B2018767 : Blo 2017435 2018767 := bstep (se 1 (by rfl) ⟨1514075, by rfl⟩ : syracuseStep 2018767 = 3028151) B3028151
theorem B3028157 : Blo 2017435 3028157 := bbase (se 3 (by rfl) ⟨567779, by rfl⟩ : syracuseStep 3028157 = 1135559) (by norm_num)
theorem B2018771 : Blo 2017435 2018771 := bstep (se 1 (by rfl) ⟨1514078, by rfl⟩ : syracuseStep 2018771 = 3028157) B3028157
theorem B4542245 : Blo 2017435 4542245 := bbase (se 4 (by rfl) ⟨425835, by rfl⟩ : syracuseStep 4542245 = 851671) (by norm_num)
theorem B3028163 : Blo 2017435 3028163 := bstep (se 1 (by rfl) ⟨2271122, by rfl⟩ : syracuseStep 3028163 = 4542245) B4542245
theorem B2018775 : Blo 2017435 2018775 := bstep (se 1 (by rfl) ⟨1514081, by rfl⟩ : syracuseStep 2018775 = 3028163) B3028163
theorem B5110037 : Blo 2017435 5110037 := bbase (se 6 (by rfl) ⟨119766, by rfl⟩ : syracuseStep 5110037 = 239533) (by norm_num)
theorem B3406691 : Blo 2017435 3406691 := bstep (se 1 (by rfl) ⟨2555018, by rfl⟩ : syracuseStep 3406691 = 5110037) B5110037
theorem B2271127 : Blo 2017435 2271127 := bstep (se 1 (by rfl) ⟨1703345, by rfl⟩ : syracuseStep 2271127 = 3406691) B3406691
theorem B3028169 : Blo 2017435 3028169 := bstep (se 2 (by rfl) ⟨1135563, by rfl⟩ : syracuseStep 3028169 = 2271127) B2271127
theorem B2018779 : Blo 2017435 2018779 := bstep (se 1 (by rfl) ⟨1514084, by rfl⟩ : syracuseStep 2018779 = 3028169) B3028169
theorem B8623205 : Blo 2017435 8623205 := bbase (se 4 (by rfl) ⟨808425, by rfl⟩ : syracuseStep 8623205 = 1616851) (by norm_num)
theorem B5748803 : Blo 2017435 5748803 := bstep (se 1 (by rfl) ⟨4311602, by rfl⟩ : syracuseStep 5748803 = 8623205) B8623205
theorem B3832535 : Blo 2017435 3832535 := bstep (se 1 (by rfl) ⟨2874401, by rfl⟩ : syracuseStep 3832535 = 5748803) B5748803
theorem B10220093 : Blo 2017435 10220093 := bstep (se 3 (by rfl) ⟨1916267, by rfl⟩ : syracuseStep 10220093 = 3832535) B3832535
theorem B6813395 : Blo 2017435 6813395 := bstep (se 1 (by rfl) ⟨5110046, by rfl⟩ : syracuseStep 6813395 = 10220093) B10220093
theorem B4542263 : Blo 2017435 4542263 := bstep (se 1 (by rfl) ⟨3406697, by rfl⟩ : syracuseStep 4542263 = 6813395) B6813395
theorem B3028175 : Blo 2017435 3028175 := bstep (se 1 (by rfl) ⟨2271131, by rfl⟩ : syracuseStep 3028175 = 4542263) B4542263
theorem B2018783 : Blo 2017435 2018783 := bstep (se 1 (by rfl) ⟨1514087, by rfl⟩ : syracuseStep 2018783 = 3028175) B3028175
theorem B3028181 : Blo 2017435 3028181 := bbase (se 7 (by rfl) ⟨35486, by rfl⟩ : syracuseStep 3028181 = 70973) (by norm_num)
theorem B2018787 : Blo 2017435 2018787 := bstep (se 1 (by rfl) ⟨1514090, by rfl⟩ : syracuseStep 2018787 = 3028181) B3028181
theorem B2874413 : Blo 2017435 2874413 := bbase (se 3 (by rfl) ⟨538952, by rfl⟩ : syracuseStep 2874413 = 1077905) (by norm_num)
theorem B7665101 : Blo 2017435 7665101 := bstep (se 3 (by rfl) ⟨1437206, by rfl⟩ : syracuseStep 7665101 = 2874413) B2874413
theorem B5110067 : Blo 2017435 5110067 := bstep (se 1 (by rfl) ⟨3832550, by rfl⟩ : syracuseStep 5110067 = 7665101) B7665101
theorem B3406711 : Blo 2017435 3406711 := bstep (se 1 (by rfl) ⟨2555033, by rfl⟩ : syracuseStep 3406711 = 5110067) B5110067
theorem B4542281 : Blo 2017435 4542281 := bstep (se 2 (by rfl) ⟨1703355, by rfl⟩ : syracuseStep 4542281 = 3406711) B3406711
theorem B3028187 : Blo 2017435 3028187 := bstep (se 1 (by rfl) ⟨2271140, by rfl⟩ : syracuseStep 3028187 = 4542281) B4542281
theorem B2018791 : Blo 2017435 2018791 := bstep (se 1 (by rfl) ⟨1514093, by rfl⟩ : syracuseStep 2018791 = 3028187) B3028187
theorem B2271145 : Blo 2017435 2271145 := bbase (se 2 (by rfl) ⟨851679, by rfl⟩ : syracuseStep 2271145 = 1703359) (by norm_num)
theorem B3028193 : Blo 2017435 3028193 := bstep (se 2 (by rfl) ⟨1135572, by rfl⟩ : syracuseStep 3028193 = 2271145) B2271145
theorem B2018795 : Blo 2017435 2018795 := bstep (se 1 (by rfl) ⟨1514096, by rfl⟩ : syracuseStep 2018795 = 3028193) B3028193
theorem B4983853 : Blo 2017435 4983853 := bbase (se 3 (by rfl) ⟨934472, by rfl⟩ : syracuseStep 4983853 = 1868945) (by norm_num)
theorem B6645137 : Blo 2017435 6645137 := bstep (se 2 (by rfl) ⟨2491926, by rfl⟩ : syracuseStep 6645137 = 4983853) B4983853
theorem B17720365 : Blo 2017435 17720365 := bstep (se 3 (by rfl) ⟨3322568, by rfl⟩ : syracuseStep 17720365 = 6645137) B6645137
theorem B23627153 : Blo 2017435 23627153 := bstep (se 2 (by rfl) ⟨8860182, by rfl⟩ : syracuseStep 23627153 = 17720365) B17720365
theorem B15751435 : Blo 2017435 15751435 := bstep (se 1 (by rfl) ⟨11813576, by rfl⟩ : syracuseStep 15751435 = 23627153) B23627153
theorem B21001913 : Blo 2017435 21001913 := bstep (se 2 (by rfl) ⟨7875717, by rfl⟩ : syracuseStep 21001913 = 15751435) B15751435
theorem B14001275 : Blo 2017435 14001275 := bstep (se 1 (by rfl) ⟨10500956, by rfl⟩ : syracuseStep 14001275 = 21001913) B21001913
theorem B9334183 : Blo 2017435 9334183 := bstep (se 1 (by rfl) ⟨7000637, by rfl⟩ : syracuseStep 9334183 = 14001275) B14001275
theorem B12445577 : Blo 2017435 12445577 := bstep (se 2 (by rfl) ⟨4667091, by rfl⟩ : syracuseStep 12445577 = 9334183) B9334183
theorem B8297051 : Blo 2017435 8297051 := bstep (se 1 (by rfl) ⟨6222788, by rfl⟩ : syracuseStep 8297051 = 12445577) B12445577
theorem B22125469 : Blo 2017435 22125469 := bstep (se 3 (by rfl) ⟨4148525, by rfl⟩ : syracuseStep 22125469 = 8297051) B8297051
theorem B29500625 : Blo 2017435 29500625 := bstep (se 2 (by rfl) ⟨11062734, by rfl⟩ : syracuseStep 29500625 = 22125469) B22125469
theorem B19667083 : Blo 2017435 19667083 := bstep (se 1 (by rfl) ⟨14750312, by rfl⟩ : syracuseStep 19667083 = 29500625) B29500625
theorem B26222777 : Blo 2017435 26222777 := bstep (se 2 (by rfl) ⟨9833541, by rfl⟩ : syracuseStep 26222777 = 19667083) B19667083
theorem B17481851 : Blo 2017435 17481851 := bstep (se 1 (by rfl) ⟨13111388, by rfl⟩ : syracuseStep 17481851 = 26222777) B26222777
theorem B11654567 : Blo 2017435 11654567 := bstep (se 1 (by rfl) ⟨8740925, by rfl⟩ : syracuseStep 11654567 = 17481851) B17481851
theorem B7769711 : Blo 2017435 7769711 := bstep (se 1 (by rfl) ⟨5827283, by rfl⟩ : syracuseStep 7769711 = 11654567) B11654567
theorem B5179807 : Blo 2017435 5179807 := bstep (se 1 (by rfl) ⟨3884855, by rfl⟩ : syracuseStep 5179807 = 7769711) B7769711
theorem B27625637 : Blo 2017435 27625637 := bstep (se 4 (by rfl) ⟨2589903, by rfl⟩ : syracuseStep 27625637 = 5179807) B5179807
theorem B73668365 : Blo 2017435 73668365 := bstep (se 3 (by rfl) ⟨13812818, by rfl⟩ : syracuseStep 73668365 = 27625637) B27625637
theorem B49112243 : Blo 2017435 49112243 := bstep (se 1 (by rfl) ⟨36834182, by rfl⟩ : syracuseStep 49112243 = 73668365) B73668365
theorem B32741495 : Blo 2017435 32741495 := bstep (se 1 (by rfl) ⟨24556121, by rfl⟩ : syracuseStep 32741495 = 49112243) B49112243
theorem B21827663 : Blo 2017435 21827663 := bstep (se 1 (by rfl) ⟨16370747, by rfl⟩ : syracuseStep 21827663 = 32741495) B32741495
theorem B14551775 : Blo 2017435 14551775 := bstep (se 1 (by rfl) ⟨10913831, by rfl⟩ : syracuseStep 14551775 = 21827663) B21827663
theorem B9701183 : Blo 2017435 9701183 := bstep (se 1 (by rfl) ⟨7275887, by rfl⟩ : syracuseStep 9701183 = 14551775) B14551775
theorem B6467455 : Blo 2017435 6467455 := bstep (se 1 (by rfl) ⟨4850591, by rfl⟩ : syracuseStep 6467455 = 9701183) B9701183
theorem B8623273 : Blo 2017435 8623273 := bstep (se 2 (by rfl) ⟨3233727, by rfl⟩ : syracuseStep 8623273 = 6467455) B6467455
theorem B11497697 : Blo 2017435 11497697 := bstep (se 2 (by rfl) ⟨4311636, by rfl⟩ : syracuseStep 11497697 = 8623273) B8623273
theorem B7665131 : Blo 2017435 7665131 := bstep (se 1 (by rfl) ⟨5748848, by rfl⟩ : syracuseStep 7665131 = 11497697) B11497697
theorem B5110087 : Blo 2017435 5110087 := bstep (se 1 (by rfl) ⟨3832565, by rfl⟩ : syracuseStep 5110087 = 7665131) B7665131
theorem B6813449 : Blo 2017435 6813449 := bstep (se 2 (by rfl) ⟨2555043, by rfl⟩ : syracuseStep 6813449 = 5110087) B5110087
theorem B4542299 : Blo 2017435 4542299 := bstep (se 1 (by rfl) ⟨3406724, by rfl⟩ : syracuseStep 4542299 = 6813449) B6813449
theorem B3028199 : Blo 2017435 3028199 := bstep (se 1 (by rfl) ⟨2271149, by rfl⟩ : syracuseStep 3028199 = 4542299) B4542299
theorem B2018799 : Blo 2017435 2018799 := bstep (se 1 (by rfl) ⟨1514099, by rfl⟩ : syracuseStep 2018799 = 3028199) B3028199
theorem B3028205 : Blo 2017435 3028205 := bbase (se 3 (by rfl) ⟨567788, by rfl⟩ : syracuseStep 3028205 = 1135577) (by norm_num)
theorem B2018803 : Blo 2017435 2018803 := bstep (se 1 (by rfl) ⟨1514102, by rfl⟩ : syracuseStep 2018803 = 3028205) B3028205
theorem B4542317 : Blo 2017435 4542317 := bbase (se 3 (by rfl) ⟨851684, by rfl⟩ : syracuseStep 4542317 = 1703369) (by norm_num)
theorem B3028211 : Blo 2017435 3028211 := bstep (se 1 (by rfl) ⟨2271158, by rfl⟩ : syracuseStep 3028211 = 4542317) B4542317
theorem B2018807 : Blo 2017435 2018807 := bstep (se 1 (by rfl) ⟨1514105, by rfl⟩ : syracuseStep 2018807 = 3028211) B3028211
theorem B3832589 : Blo 2017435 3832589 := bbase (se 3 (by rfl) ⟨718610, by rfl⟩ : syracuseStep 3832589 = 1437221) (by norm_num)
theorem B2555059 : Blo 2017435 2555059 := bstep (se 1 (by rfl) ⟨1916294, by rfl⟩ : syracuseStep 2555059 = 3832589) B3832589
theorem B3406745 : Blo 2017435 3406745 := bstep (se 2 (by rfl) ⟨1277529, by rfl⟩ : syracuseStep 3406745 = 2555059) B2555059
theorem B2271163 : Blo 2017435 2271163 := bstep (se 1 (by rfl) ⟨1703372, by rfl⟩ : syracuseStep 2271163 = 3406745) B3406745
theorem B3028217 : Blo 2017435 3028217 := bstep (se 2 (by rfl) ⟨1135581, by rfl⟩ : syracuseStep 3028217 = 2271163) B2271163
theorem B2018811 : Blo 2017435 2018811 := bstep (se 1 (by rfl) ⟨1514108, by rfl⟩ : syracuseStep 2018811 = 3028217) B3028217
theorem B19402517 : Blo 2017435 19402517 := bbase (se 6 (by rfl) ⟨454746, by rfl⟩ : syracuseStep 19402517 = 909493) (by norm_num)
theorem B51740045 : Blo 2017435 51740045 := bstep (se 3 (by rfl) ⟨9701258, by rfl⟩ : syracuseStep 51740045 = 19402517) B19402517
theorem B34493363 : Blo 2017435 34493363 := bstep (se 1 (by rfl) ⟨25870022, by rfl⟩ : syracuseStep 34493363 = 51740045) B51740045
theorem B22995575 : Blo 2017435 22995575 := bstep (se 1 (by rfl) ⟨17246681, by rfl⟩ : syracuseStep 22995575 = 34493363) B34493363
theorem B15330383 : Blo 2017435 15330383 := bstep (se 1 (by rfl) ⟨11497787, by rfl⟩ : syracuseStep 15330383 = 22995575) B22995575
theorem B10220255 : Blo 2017435 10220255 := bstep (se 1 (by rfl) ⟨7665191, by rfl⟩ : syracuseStep 10220255 = 15330383) B15330383
theorem B6813503 : Blo 2017435 6813503 := bstep (se 1 (by rfl) ⟨5110127, by rfl⟩ : syracuseStep 6813503 = 10220255) B10220255
theorem B4542335 : Blo 2017435 4542335 := bstep (se 1 (by rfl) ⟨3406751, by rfl⟩ : syracuseStep 4542335 = 6813503) B6813503
theorem B3028223 : Blo 2017435 3028223 := bstep (se 1 (by rfl) ⟨2271167, by rfl⟩ : syracuseStep 3028223 = 4542335) B4542335
theorem B2018815 : Blo 2017435 2018815 := bstep (se 1 (by rfl) ⟨1514111, by rfl⟩ : syracuseStep 2018815 = 3028223) B3028223
theorem B3028229 : Blo 2017435 3028229 := bbase (se 4 (by rfl) ⟨283896, by rfl⟩ : syracuseStep 3028229 = 567793) (by norm_num)
theorem B2018819 : Blo 2017435 2018819 := bstep (se 1 (by rfl) ⟨1514114, by rfl⟩ : syracuseStep 2018819 = 3028229) B3028229
theorem B3406765 : Blo 2017435 3406765 := bbase (se 3 (by rfl) ⟨638768, by rfl⟩ : syracuseStep 3406765 = 1277537) (by norm_num)
theorem B4542353 : Blo 2017435 4542353 := bstep (se 2 (by rfl) ⟨1703382, by rfl⟩ : syracuseStep 4542353 = 3406765) B3406765
theorem B3028235 : Blo 2017435 3028235 := bstep (se 1 (by rfl) ⟨2271176, by rfl⟩ : syracuseStep 3028235 = 4542353) B4542353
theorem B2018823 : Blo 2017435 2018823 := bstep (se 1 (by rfl) ⟨1514117, by rfl⟩ : syracuseStep 2018823 = 3028235) B3028235
theorem B2271181 : Blo 2017435 2271181 := bbase (se 3 (by rfl) ⟨425846, by rfl⟩ : syracuseStep 2271181 = 851693) (by norm_num)
theorem B3028241 : Blo 2017435 3028241 := bstep (se 2 (by rfl) ⟨1135590, by rfl⟩ : syracuseStep 3028241 = 2271181) B2271181
theorem B2018827 : Blo 2017435 2018827 := bstep (se 1 (by rfl) ⟨1514120, by rfl⟩ : syracuseStep 2018827 = 3028241) B3028241
theorem B6813557 : Blo 2017435 6813557 := bbase (se 5 (by rfl) ⟨319385, by rfl⟩ : syracuseStep 6813557 = 638771) (by norm_num)
theorem B4542371 : Blo 2017435 4542371 := bstep (se 1 (by rfl) ⟨3406778, by rfl⟩ : syracuseStep 4542371 = 6813557) B6813557
theorem B3028247 : Blo 2017435 3028247 := bstep (se 1 (by rfl) ⟨2271185, by rfl⟩ : syracuseStep 3028247 = 4542371) B4542371
theorem B2018831 : Blo 2017435 2018831 := bstep (se 1 (by rfl) ⟨1514123, by rfl⟩ : syracuseStep 2018831 = 3028247) B3028247
theorem B3028253 : Blo 2017435 3028253 := bbase (se 3 (by rfl) ⟨567797, by rfl⟩ : syracuseStep 3028253 = 1135595) (by norm_num)
theorem B2018835 : Blo 2017435 2018835 := bstep (se 1 (by rfl) ⟨1514126, by rfl⟩ : syracuseStep 2018835 = 3028253) B3028253
theorem B4542389 : Blo 2017435 4542389 := bbase (se 5 (by rfl) ⟨212924, by rfl⟩ : syracuseStep 4542389 = 425849) (by norm_num)
theorem B3028259 : Blo 2017435 3028259 := bstep (se 1 (by rfl) ⟨2271194, by rfl⟩ : syracuseStep 3028259 = 4542389) B4542389
theorem B2018839 : Blo 2017435 2018839 := bstep (se 1 (by rfl) ⟨1514129, by rfl⟩ : syracuseStep 2018839 = 3028259) B3028259
theorem B2425349 : Blo 2017435 2425349 := bbase (se 4 (by rfl) ⟨227376, by rfl⟩ : syracuseStep 2425349 = 454753) (by norm_num)
theorem B6467597 : Blo 2017435 6467597 := bstep (se 3 (by rfl) ⟨1212674, by rfl⟩ : syracuseStep 6467597 = 2425349) B2425349
theorem B4311731 : Blo 2017435 4311731 := bstep (se 1 (by rfl) ⟨3233798, by rfl⟩ : syracuseStep 4311731 = 6467597) B6467597
theorem B11497949 : Blo 2017435 11497949 := bstep (se 3 (by rfl) ⟨2155865, by rfl⟩ : syracuseStep 11497949 = 4311731) B4311731
theorem B7665299 : Blo 2017435 7665299 := bstep (se 1 (by rfl) ⟨5748974, by rfl⟩ : syracuseStep 7665299 = 11497949) B11497949
theorem B5110199 : Blo 2017435 5110199 := bstep (se 1 (by rfl) ⟨3832649, by rfl⟩ : syracuseStep 5110199 = 7665299) B7665299
theorem B3406799 : Blo 2017435 3406799 := bstep (se 1 (by rfl) ⟨2555099, by rfl⟩ : syracuseStep 3406799 = 5110199) B5110199
theorem B2271199 : Blo 2017435 2271199 := bstep (se 1 (by rfl) ⟨1703399, by rfl⟩ : syracuseStep 2271199 = 3406799) B3406799
theorem B3028265 : Blo 2017435 3028265 := bstep (se 2 (by rfl) ⟨1135599, by rfl⟩ : syracuseStep 3028265 = 2271199) B2271199
theorem B2018843 : Blo 2017435 2018843 := bstep (se 1 (by rfl) ⟨1514132, by rfl⟩ : syracuseStep 2018843 = 3028265) B3028265
theorem B3069589 : Blo 2017435 3069589 := bbase (se 6 (by rfl) ⟨71943, by rfl⟩ : syracuseStep 3069589 = 143887) (by norm_num)
theorem B4092785 : Blo 2017435 4092785 := bstep (se 2 (by rfl) ⟨1534794, by rfl⟩ : syracuseStep 4092785 = 3069589) B3069589
theorem B2728523 : Blo 2017435 2728523 := bstep (se 1 (by rfl) ⟨2046392, by rfl⟩ : syracuseStep 2728523 = 4092785) B4092785
theorem B7276061 : Blo 2017435 7276061 := bstep (se 3 (by rfl) ⟨1364261, by rfl⟩ : syracuseStep 7276061 = 2728523) B2728523
theorem B4850707 : Blo 2017435 4850707 := bstep (se 1 (by rfl) ⟨3638030, by rfl⟩ : syracuseStep 4850707 = 7276061) B7276061
theorem B6467609 : Blo 2017435 6467609 := bstep (se 2 (by rfl) ⟨2425353, by rfl⟩ : syracuseStep 6467609 = 4850707) B4850707
theorem B4311739 : Blo 2017435 4311739 := bstep (se 1 (by rfl) ⟨3233804, by rfl⟩ : syracuseStep 4311739 = 6467609) B6467609
theorem B5748985 : Blo 2017435 5748985 := bstep (se 2 (by rfl) ⟨2155869, by rfl⟩ : syracuseStep 5748985 = 4311739) B4311739
theorem B7665313 : Blo 2017435 7665313 := bstep (se 2 (by rfl) ⟨2874492, by rfl⟩ : syracuseStep 7665313 = 5748985) B5748985
theorem B10220417 : Blo 2017435 10220417 := bstep (se 2 (by rfl) ⟨3832656, by rfl⟩ : syracuseStep 10220417 = 7665313) B7665313
theorem B6813611 : Blo 2017435 6813611 := bstep (se 1 (by rfl) ⟨5110208, by rfl⟩ : syracuseStep 6813611 = 10220417) B10220417
theorem B4542407 : Blo 2017435 4542407 := bstep (se 1 (by rfl) ⟨3406805, by rfl⟩ : syracuseStep 4542407 = 6813611) B6813611
theorem B3028271 : Blo 2017435 3028271 := bstep (se 1 (by rfl) ⟨2271203, by rfl⟩ : syracuseStep 3028271 = 4542407) B4542407
theorem B2018847 : Blo 2017435 2018847 := bstep (se 1 (by rfl) ⟨1514135, by rfl⟩ : syracuseStep 2018847 = 3028271) B3028271
theorem B3028277 : Blo 2017435 3028277 := bbase (se 5 (by rfl) ⟨141950, by rfl⟩ : syracuseStep 3028277 = 283901) (by norm_num)
theorem B2018851 : Blo 2017435 2018851 := bstep (se 1 (by rfl) ⟨1514138, by rfl⟩ : syracuseStep 2018851 = 3028277) B3028277
theorem B5110229 : Blo 2017435 5110229 := bbase (se 7 (by rfl) ⟨59885, by rfl⟩ : syracuseStep 5110229 = 119771) (by norm_num)
theorem B3406819 : Blo 2017435 3406819 := bstep (se 1 (by rfl) ⟨2555114, by rfl⟩ : syracuseStep 3406819 = 5110229) B5110229
theorem B4542425 : Blo 2017435 4542425 := bstep (se 2 (by rfl) ⟨1703409, by rfl⟩ : syracuseStep 4542425 = 3406819) B3406819
theorem B3028283 : Blo 2017435 3028283 := bstep (se 1 (by rfl) ⟨2271212, by rfl⟩ : syracuseStep 3028283 = 4542425) B4542425
theorem B2018855 : Blo 2017435 2018855 := bstep (se 1 (by rfl) ⟨1514141, by rfl⟩ : syracuseStep 2018855 = 3028283) B3028283
theorem B2271217 : Blo 2017435 2271217 := bbase (se 2 (by rfl) ⟨851706, by rfl⟩ : syracuseStep 2271217 = 1703413) (by norm_num)
theorem B3028289 : Blo 2017435 3028289 := bstep (se 2 (by rfl) ⟨1135608, by rfl⟩ : syracuseStep 3028289 = 2271217) B2271217
theorem B2018859 : Blo 2017435 2018859 := bstep (se 1 (by rfl) ⟨1514144, by rfl⟩ : syracuseStep 2018859 = 3028289) B3028289
theorem B3069613 : Blo 2017435 3069613 := bbase (se 3 (by rfl) ⟨575552, by rfl⟩ : syracuseStep 3069613 = 1151105) (by norm_num)
theorem B4092817 : Blo 2017435 4092817 := bstep (se 2 (by rfl) ⟨1534806, by rfl⟩ : syracuseStep 4092817 = 3069613) B3069613
theorem B5457089 : Blo 2017435 5457089 := bstep (se 2 (by rfl) ⟨2046408, by rfl⟩ : syracuseStep 5457089 = 4092817) B4092817
theorem B14552237 : Blo 2017435 14552237 := bstep (se 3 (by rfl) ⟨2728544, by rfl⟩ : syracuseStep 14552237 = 5457089) B5457089
theorem B9701491 : Blo 2017435 9701491 := bstep (se 1 (by rfl) ⟨7276118, by rfl⟩ : syracuseStep 9701491 = 14552237) B14552237
theorem B12935321 : Blo 2017435 12935321 := bstep (se 2 (by rfl) ⟨4850745, by rfl⟩ : syracuseStep 12935321 = 9701491) B9701491
theorem B8623547 : Blo 2017435 8623547 := bstep (se 1 (by rfl) ⟨6467660, by rfl⟩ : syracuseStep 8623547 = 12935321) B12935321
theorem B5749031 : Blo 2017435 5749031 := bstep (se 1 (by rfl) ⟨4311773, by rfl⟩ : syracuseStep 5749031 = 8623547) B8623547
theorem B3832687 : Blo 2017435 3832687 := bstep (se 1 (by rfl) ⟨2874515, by rfl⟩ : syracuseStep 3832687 = 5749031) B5749031
theorem B5110249 : Blo 2017435 5110249 := bstep (se 2 (by rfl) ⟨1916343, by rfl⟩ : syracuseStep 5110249 = 3832687) B3832687
theorem B6813665 : Blo 2017435 6813665 := bstep (se 2 (by rfl) ⟨2555124, by rfl⟩ : syracuseStep 6813665 = 5110249) B5110249
theorem B4542443 : Blo 2017435 4542443 := bstep (se 1 (by rfl) ⟨3406832, by rfl⟩ : syracuseStep 4542443 = 6813665) B6813665
theorem B3028295 : Blo 2017435 3028295 := bstep (se 1 (by rfl) ⟨2271221, by rfl⟩ : syracuseStep 3028295 = 4542443) B4542443
theorem B2018863 : Blo 2017435 2018863 := bstep (se 1 (by rfl) ⟨1514147, by rfl⟩ : syracuseStep 2018863 = 3028295) B3028295
theorem B3028301 : Blo 2017435 3028301 := bbase (se 3 (by rfl) ⟨567806, by rfl⟩ : syracuseStep 3028301 = 1135613) (by norm_num)
theorem B2018867 : Blo 2017435 2018867 := bstep (se 1 (by rfl) ⟨1514150, by rfl⟩ : syracuseStep 2018867 = 3028301) B3028301
theorem B4542461 : Blo 2017435 4542461 := bbase (se 3 (by rfl) ⟨851711, by rfl⟩ : syracuseStep 4542461 = 1703423) (by norm_num)
theorem B3028307 : Blo 2017435 3028307 := bstep (se 1 (by rfl) ⟨2271230, by rfl⟩ : syracuseStep 3028307 = 4542461) B4542461
theorem B2018871 : Blo 2017435 2018871 := bstep (se 1 (by rfl) ⟨1514153, by rfl⟩ : syracuseStep 2018871 = 3028307) B3028307
theorem B3406853 : Blo 2017435 3406853 := bbase (se 4 (by rfl) ⟨319392, by rfl⟩ : syracuseStep 3406853 = 638785) (by norm_num)
theorem B2271235 : Blo 2017435 2271235 := bstep (se 1 (by rfl) ⟨1703426, by rfl⟩ : syracuseStep 2271235 = 3406853) B3406853
theorem B3028313 : Blo 2017435 3028313 := bstep (se 2 (by rfl) ⟨1135617, by rfl⟩ : syracuseStep 3028313 = 2271235) B2271235
theorem B2018875 : Blo 2017435 2018875 := bstep (se 1 (by rfl) ⟨1514156, by rfl⟩ : syracuseStep 2018875 = 3028313) B3028313
theorem B15330869 : Blo 2017435 15330869 := bbase (se 5 (by rfl) ⟨718634, by rfl⟩ : syracuseStep 15330869 = 1437269) (by norm_num)
theorem B10220579 : Blo 2017435 10220579 := bstep (se 1 (by rfl) ⟨7665434, by rfl⟩ : syracuseStep 10220579 = 15330869) B15330869
theorem B6813719 : Blo 2017435 6813719 := bstep (se 1 (by rfl) ⟨5110289, by rfl⟩ : syracuseStep 6813719 = 10220579) B10220579
theorem B4542479 : Blo 2017435 4542479 := bstep (se 1 (by rfl) ⟨3406859, by rfl⟩ : syracuseStep 4542479 = 6813719) B6813719
theorem B3028319 : Blo 2017435 3028319 := bstep (se 1 (by rfl) ⟨2271239, by rfl⟩ : syracuseStep 3028319 = 4542479) B4542479
theorem B2018879 : Blo 2017435 2018879 := bstep (se 1 (by rfl) ⟨1514159, by rfl⟩ : syracuseStep 2018879 = 3028319) B3028319
theorem B3028325 : Blo 2017435 3028325 := bbase (se 4 (by rfl) ⟨283905, by rfl⟩ : syracuseStep 3028325 = 567811) (by norm_num)
theorem B2018883 : Blo 2017435 2018883 := bstep (se 1 (by rfl) ⟨1514162, by rfl⟩ : syracuseStep 2018883 = 3028325) B3028325
theorem B3832733 : Blo 2017435 3832733 := bbase (se 3 (by rfl) ⟨718637, by rfl⟩ : syracuseStep 3832733 = 1437275) (by norm_num)
theorem B2555155 : Blo 2017435 2555155 := bstep (se 1 (by rfl) ⟨1916366, by rfl⟩ : syracuseStep 2555155 = 3832733) B3832733
theorem B3406873 : Blo 2017435 3406873 := bstep (se 2 (by rfl) ⟨1277577, by rfl⟩ : syracuseStep 3406873 = 2555155) B2555155
theorem B4542497 : Blo 2017435 4542497 := bstep (se 2 (by rfl) ⟨1703436, by rfl⟩ : syracuseStep 4542497 = 3406873) B3406873
theorem B3028331 : Blo 2017435 3028331 := bstep (se 1 (by rfl) ⟨2271248, by rfl⟩ : syracuseStep 3028331 = 4542497) B4542497
theorem B2018887 : Blo 2017435 2018887 := bstep (se 1 (by rfl) ⟨1514165, by rfl⟩ : syracuseStep 2018887 = 3028331) B3028331
theorem B2271253 : Blo 2017435 2271253 := bbase (se 6 (by rfl) ⟨53232, by rfl⟩ : syracuseStep 2271253 = 106465) (by norm_num)
theorem B3028337 : Blo 2017435 3028337 := bstep (se 2 (by rfl) ⟨1135626, by rfl⟩ : syracuseStep 3028337 = 2271253) B2271253
theorem B2018891 : Blo 2017435 2018891 := bstep (se 1 (by rfl) ⟨1514168, by rfl⟩ : syracuseStep 2018891 = 3028337) B3028337
theorem B2555165 : Blo 2017435 2555165 := bbase (se 3 (by rfl) ⟨479093, by rfl⟩ : syracuseStep 2555165 = 958187) (by norm_num)
theorem B6813773 : Blo 2017435 6813773 := bstep (se 3 (by rfl) ⟨1277582, by rfl⟩ : syracuseStep 6813773 = 2555165) B2555165
theorem B4542515 : Blo 2017435 4542515 := bstep (se 1 (by rfl) ⟨3406886, by rfl⟩ : syracuseStep 4542515 = 6813773) B6813773
theorem B3028343 : Blo 2017435 3028343 := bstep (se 1 (by rfl) ⟨2271257, by rfl⟩ : syracuseStep 3028343 = 4542515) B4542515
theorem B2018895 : Blo 2017435 2018895 := bstep (se 1 (by rfl) ⟨1514171, by rfl⟩ : syracuseStep 2018895 = 3028343) B3028343
theorem B3028349 : Blo 2017435 3028349 := bbase (se 3 (by rfl) ⟨567815, by rfl⟩ : syracuseStep 3028349 = 1135631) (by norm_num)
theorem B2018899 : Blo 2017435 2018899 := bstep (se 1 (by rfl) ⟨1514174, by rfl⟩ : syracuseStep 2018899 = 3028349) B3028349
theorem B4542533 : Blo 2017435 4542533 := bbase (se 4 (by rfl) ⟨425862, by rfl⟩ : syracuseStep 4542533 = 851725) (by norm_num)
theorem B3028355 : Blo 2017435 3028355 := bstep (se 1 (by rfl) ⟨2271266, by rfl⟩ : syracuseStep 3028355 = 4542533) B4542533
theorem B2018903 : Blo 2017435 2018903 := bstep (se 1 (by rfl) ⟨1514177, by rfl⟩ : syracuseStep 2018903 = 3028355) B3028355
theorem B5749157 : Blo 2017435 5749157 := bbase (se 4 (by rfl) ⟨538983, by rfl⟩ : syracuseStep 5749157 = 1077967) (by norm_num)
theorem B3832771 : Blo 2017435 3832771 := bstep (se 1 (by rfl) ⟨2874578, by rfl⟩ : syracuseStep 3832771 = 5749157) B5749157
theorem B5110361 : Blo 2017435 5110361 := bstep (se 2 (by rfl) ⟨1916385, by rfl⟩ : syracuseStep 5110361 = 3832771) B3832771
theorem B3406907 : Blo 2017435 3406907 := bstep (se 1 (by rfl) ⟨2555180, by rfl⟩ : syracuseStep 3406907 = 5110361) B5110361
theorem B2271271 : Blo 2017435 2271271 := bstep (se 1 (by rfl) ⟨1703453, by rfl⟩ : syracuseStep 2271271 = 3406907) B3406907
theorem B3028361 : Blo 2017435 3028361 := bstep (se 2 (by rfl) ⟨1135635, by rfl⟩ : syracuseStep 3028361 = 2271271) B2271271
theorem B2018907 : Blo 2017435 2018907 := bstep (se 1 (by rfl) ⟨1514180, by rfl⟩ : syracuseStep 2018907 = 3028361) B3028361
theorem B10220741 : Blo 2017435 10220741 := bbase (se 4 (by rfl) ⟨958194, by rfl⟩ : syracuseStep 10220741 = 1916389) (by norm_num)
theorem B6813827 : Blo 2017435 6813827 := bstep (se 1 (by rfl) ⟨5110370, by rfl⟩ : syracuseStep 6813827 = 10220741) B10220741
theorem B4542551 : Blo 2017435 4542551 := bstep (se 1 (by rfl) ⟨3406913, by rfl⟩ : syracuseStep 4542551 = 6813827) B6813827
theorem B3028367 : Blo 2017435 3028367 := bstep (se 1 (by rfl) ⟨2271275, by rfl⟩ : syracuseStep 3028367 = 4542551) B4542551
theorem B2018911 : Blo 2017435 2018911 := bstep (se 1 (by rfl) ⟨1514183, by rfl⟩ : syracuseStep 2018911 = 3028367) B3028367
theorem B3028373 : Blo 2017435 3028373 := bbase (se 6 (by rfl) ⟨70977, by rfl⟩ : syracuseStep 3028373 = 141955) (by norm_num)
theorem B2018915 : Blo 2017435 2018915 := bstep (se 1 (by rfl) ⟨1514186, by rfl⟩ : syracuseStep 2018915 = 3028373) B3028373
theorem B4311893 : Blo 2017435 4311893 := bbase (se 9 (by rfl) ⟨12632, by rfl⟩ : syracuseStep 4311893 = 25265) (by norm_num)
theorem B11498381 : Blo 2017435 11498381 := bstep (se 3 (by rfl) ⟨2155946, by rfl⟩ : syracuseStep 11498381 = 4311893) B4311893
theorem B7665587 : Blo 2017435 7665587 := bstep (se 1 (by rfl) ⟨5749190, by rfl⟩ : syracuseStep 7665587 = 11498381) B11498381
theorem B5110391 : Blo 2017435 5110391 := bstep (se 1 (by rfl) ⟨3832793, by rfl⟩ : syracuseStep 5110391 = 7665587) B7665587
theorem B3406927 : Blo 2017435 3406927 := bstep (se 1 (by rfl) ⟨2555195, by rfl⟩ : syracuseStep 3406927 = 5110391) B5110391
theorem B4542569 : Blo 2017435 4542569 := bstep (se 2 (by rfl) ⟨1703463, by rfl⟩ : syracuseStep 4542569 = 3406927) B3406927
theorem B3028379 : Blo 2017435 3028379 := bstep (se 1 (by rfl) ⟨2271284, by rfl⟩ : syracuseStep 3028379 = 4542569) B4542569
theorem B2018919 : Blo 2017435 2018919 := bstep (se 1 (by rfl) ⟨1514189, by rfl⟩ : syracuseStep 2018919 = 3028379) B3028379
theorem B2271289 : Blo 2017435 2271289 := bbase (se 2 (by rfl) ⟨851733, by rfl⟩ : syracuseStep 2271289 = 1703467) (by norm_num)
theorem B3028385 : Blo 2017435 3028385 := bstep (se 2 (by rfl) ⟨1135644, by rfl⟩ : syracuseStep 3028385 = 2271289) B2271289
theorem B2018923 : Blo 2017435 2018923 := bstep (se 1 (by rfl) ⟨1514192, by rfl⟩ : syracuseStep 2018923 = 3028385) B3028385
theorem B3233933 : Blo 2017435 3233933 := bbase (se 3 (by rfl) ⟨606362, by rfl⟩ : syracuseStep 3233933 = 1212725) (by norm_num)
theorem B2155955 : Blo 2017435 2155955 := bstep (se 1 (by rfl) ⟨1616966, by rfl⟩ : syracuseStep 2155955 = 3233933) B3233933
theorem B5749213 : Blo 2017435 5749213 := bstep (se 3 (by rfl) ⟨1077977, by rfl⟩ : syracuseStep 5749213 = 2155955) B2155955
theorem B7665617 : Blo 2017435 7665617 := bstep (se 2 (by rfl) ⟨2874606, by rfl⟩ : syracuseStep 7665617 = 5749213) B5749213
theorem B5110411 : Blo 2017435 5110411 := bstep (se 1 (by rfl) ⟨3832808, by rfl⟩ : syracuseStep 5110411 = 7665617) B7665617
theorem B6813881 : Blo 2017435 6813881 := bstep (se 2 (by rfl) ⟨2555205, by rfl⟩ : syracuseStep 6813881 = 5110411) B5110411
theorem B4542587 : Blo 2017435 4542587 := bstep (se 1 (by rfl) ⟨3406940, by rfl⟩ : syracuseStep 4542587 = 6813881) B6813881
theorem B3028391 : Blo 2017435 3028391 := bstep (se 1 (by rfl) ⟨2271293, by rfl⟩ : syracuseStep 3028391 = 4542587) B4542587
theorem B2018927 : Blo 2017435 2018927 := bstep (se 1 (by rfl) ⟨1514195, by rfl⟩ : syracuseStep 2018927 = 3028391) B3028391
theorem B3028397 : Blo 2017435 3028397 := bbase (se 3 (by rfl) ⟨567824, by rfl⟩ : syracuseStep 3028397 = 1135649) (by norm_num)
theorem B2018931 : Blo 2017435 2018931 := bstep (se 1 (by rfl) ⟨1514198, by rfl⟩ : syracuseStep 2018931 = 3028397) B3028397
theorem B4542605 : Blo 2017435 4542605 := bbase (se 3 (by rfl) ⟨851738, by rfl⟩ : syracuseStep 4542605 = 1703477) (by norm_num)
theorem B3028403 : Blo 2017435 3028403 := bstep (se 1 (by rfl) ⟨2271302, by rfl⟩ : syracuseStep 3028403 = 4542605) B4542605
theorem B2018935 : Blo 2017435 2018935 := bstep (se 1 (by rfl) ⟨1514201, by rfl⟩ : syracuseStep 2018935 = 3028403) B3028403
theorem B2555221 : Blo 2017435 2555221 := bbase (se 11 (by rfl) ⟨1871, by rfl⟩ : syracuseStep 2555221 = 3743) (by norm_num)
theorem B3406961 : Blo 2017435 3406961 := bstep (se 2 (by rfl) ⟨1277610, by rfl⟩ : syracuseStep 3406961 = 2555221) B2555221
theorem B2271307 : Blo 2017435 2271307 := bstep (se 1 (by rfl) ⟨1703480, by rfl⟩ : syracuseStep 2271307 = 3406961) B3406961
theorem B3028409 : Blo 2017435 3028409 := bstep (se 2 (by rfl) ⟨1135653, by rfl⟩ : syracuseStep 3028409 = 2271307) B2271307
theorem B2018939 : Blo 2017435 2018939 := bstep (se 1 (by rfl) ⟨1514204, by rfl⟩ : syracuseStep 2018939 = 3028409) B3028409
theorem B3154069 : Blo 2017435 3154069 := bbase (se 6 (by rfl) ⟨73923, by rfl⟩ : syracuseStep 3154069 = 147847) (by norm_num)
theorem B16821701 : Blo 2017435 16821701 := bstep (se 4 (by rfl) ⟨1577034, by rfl⟩ : syracuseStep 16821701 = 3154069) B3154069
theorem B11214467 : Blo 2017435 11214467 := bstep (se 1 (by rfl) ⟨8410850, by rfl⟩ : syracuseStep 11214467 = 16821701) B16821701
theorem B7476311 : Blo 2017435 7476311 := bstep (se 1 (by rfl) ⟨5607233, by rfl⟩ : syracuseStep 7476311 = 11214467) B11214467
theorem B19936829 : Blo 2017435 19936829 := bstep (se 3 (by rfl) ⟨3738155, by rfl⟩ : syracuseStep 19936829 = 7476311) B7476311
theorem B13291219 : Blo 2017435 13291219 := bstep (se 1 (by rfl) ⟨9968414, by rfl⟩ : syracuseStep 13291219 = 19936829) B19936829
theorem B17721625 : Blo 2017435 17721625 := bstep (se 2 (by rfl) ⟨6645609, by rfl⟩ : syracuseStep 17721625 = 13291219) B13291219
theorem B23628833 : Blo 2017435 23628833 := bstep (se 2 (by rfl) ⟨8860812, by rfl⟩ : syracuseStep 23628833 = 17721625) B17721625
theorem B15752555 : Blo 2017435 15752555 := bstep (se 1 (by rfl) ⟨11814416, by rfl⟩ : syracuseStep 15752555 = 23628833) B23628833
theorem B10501703 : Blo 2017435 10501703 := bstep (se 1 (by rfl) ⟨7876277, by rfl⟩ : syracuseStep 10501703 = 15752555) B15752555
theorem B7001135 : Blo 2017435 7001135 := bstep (se 1 (by rfl) ⟨5250851, by rfl⟩ : syracuseStep 7001135 = 10501703) B10501703
theorem B4667423 : Blo 2017435 4667423 := bstep (se 1 (by rfl) ⟨3500567, by rfl⟩ : syracuseStep 4667423 = 7001135) B7001135
theorem B12446461 : Blo 2017435 12446461 := bstep (se 3 (by rfl) ⟨2333711, by rfl⟩ : syracuseStep 12446461 = 4667423) B4667423
theorem B16595281 : Blo 2017435 16595281 := bstep (se 2 (by rfl) ⟨6223230, by rfl⟩ : syracuseStep 16595281 = 12446461) B12446461
theorem B22127041 : Blo 2017435 22127041 := bstep (se 2 (by rfl) ⟨8297640, by rfl⟩ : syracuseStep 22127041 = 16595281) B16595281
theorem B29502721 : Blo 2017435 29502721 := bstep (se 2 (by rfl) ⟨11063520, by rfl⟩ : syracuseStep 29502721 = 22127041) B22127041
theorem B39336961 : Blo 2017435 39336961 := bstep (se 2 (by rfl) ⟨14751360, by rfl⟩ : syracuseStep 39336961 = 29502721) B29502721
theorem B52449281 : Blo 2017435 52449281 := bstep (se 2 (by rfl) ⟨19668480, by rfl⟩ : syracuseStep 52449281 = 39336961) B39336961
theorem B34966187 : Blo 2017435 34966187 := bstep (se 1 (by rfl) ⟨26224640, by rfl⟩ : syracuseStep 34966187 = 52449281) B52449281
theorem B23310791 : Blo 2017435 23310791 := bstep (se 1 (by rfl) ⟨17483093, by rfl⟩ : syracuseStep 23310791 = 34966187) B34966187
theorem B15540527 : Blo 2017435 15540527 := bstep (se 1 (by rfl) ⟨11655395, by rfl⟩ : syracuseStep 15540527 = 23310791) B23310791
theorem B10360351 : Blo 2017435 10360351 := bstep (se 1 (by rfl) ⟨7770263, by rfl⟩ : syracuseStep 10360351 = 15540527) B15540527
theorem B55255205 : Blo 2017435 55255205 := bstep (se 4 (by rfl) ⟨5180175, by rfl⟩ : syracuseStep 55255205 = 10360351) B10360351
theorem B36836803 : Blo 2017435 36836803 := bstep (se 1 (by rfl) ⟨27627602, by rfl⟩ : syracuseStep 36836803 = 55255205) B55255205
theorem B49115737 : Blo 2017435 49115737 := bstep (se 2 (by rfl) ⟨18418401, by rfl⟩ : syracuseStep 49115737 = 36836803) B36836803
theorem B65487649 : Blo 2017435 65487649 := bstep (se 2 (by rfl) ⟨24557868, by rfl⟩ : syracuseStep 65487649 = 49115737) B49115737
theorem B87316865 : Blo 2017435 87316865 := bstep (se 2 (by rfl) ⟨32743824, by rfl⟩ : syracuseStep 87316865 = 65487649) B65487649
theorem B58211243 : Blo 2017435 58211243 := bstep (se 1 (by rfl) ⟨43658432, by rfl⟩ : syracuseStep 58211243 = 87316865) B87316865
theorem B38807495 : Blo 2017435 38807495 := bstep (se 1 (by rfl) ⟨29105621, by rfl⟩ : syracuseStep 38807495 = 58211243) B58211243
theorem B25871663 : Blo 2017435 25871663 := bstep (se 1 (by rfl) ⟨19403747, by rfl⟩ : syracuseStep 25871663 = 38807495) B38807495
theorem B17247775 : Blo 2017435 17247775 := bstep (se 1 (by rfl) ⟨12935831, by rfl⟩ : syracuseStep 17247775 = 25871663) B25871663
theorem B22997033 : Blo 2017435 22997033 := bstep (se 2 (by rfl) ⟨8623887, by rfl⟩ : syracuseStep 22997033 = 17247775) B17247775
theorem B15331355 : Blo 2017435 15331355 := bstep (se 1 (by rfl) ⟨11498516, by rfl⟩ : syracuseStep 15331355 = 22997033) B22997033
theorem B10220903 : Blo 2017435 10220903 := bstep (se 1 (by rfl) ⟨7665677, by rfl⟩ : syracuseStep 10220903 = 15331355) B15331355
theorem B6813935 : Blo 2017435 6813935 := bstep (se 1 (by rfl) ⟨5110451, by rfl⟩ : syracuseStep 6813935 = 10220903) B10220903
theorem B4542623 : Blo 2017435 4542623 := bstep (se 1 (by rfl) ⟨3406967, by rfl⟩ : syracuseStep 4542623 = 6813935) B6813935
theorem B3028415 : Blo 2017435 3028415 := bstep (se 1 (by rfl) ⟨2271311, by rfl⟩ : syracuseStep 3028415 = 4542623) B4542623
theorem B2018943 : Blo 2017435 2018943 := bstep (se 1 (by rfl) ⟨1514207, by rfl⟩ : syracuseStep 2018943 = 3028415) B3028415
theorem B3028421 : Blo 2017435 3028421 := bbase (se 4 (by rfl) ⟨283914, by rfl⟩ : syracuseStep 3028421 = 567829) (by norm_num)
theorem B2018947 : Blo 2017435 2018947 := bstep (se 1 (by rfl) ⟨1514210, by rfl⟩ : syracuseStep 2018947 = 3028421) B3028421
theorem B3406981 : Blo 2017435 3406981 := bbase (se 4 (by rfl) ⟨319404, by rfl⟩ : syracuseStep 3406981 = 638809) (by norm_num)
theorem B4542641 : Blo 2017435 4542641 := bstep (se 2 (by rfl) ⟨1703490, by rfl⟩ : syracuseStep 4542641 = 3406981) B3406981
theorem B3028427 : Blo 2017435 3028427 := bstep (se 1 (by rfl) ⟨2271320, by rfl⟩ : syracuseStep 3028427 = 4542641) B4542641
theorem B2018951 : Blo 2017435 2018951 := bstep (se 1 (by rfl) ⟨1514213, by rfl⟩ : syracuseStep 2018951 = 3028427) B3028427
theorem B2271325 : Blo 2017435 2271325 := bbase (se 3 (by rfl) ⟨425873, by rfl⟩ : syracuseStep 2271325 = 851747) (by norm_num)
theorem B3028433 : Blo 2017435 3028433 := bstep (se 2 (by rfl) ⟨1135662, by rfl⟩ : syracuseStep 3028433 = 2271325) B2271325
theorem B2018955 : Blo 2017435 2018955 := bstep (se 1 (by rfl) ⟨1514216, by rfl⟩ : syracuseStep 2018955 = 3028433) B3028433
theorem B6813989 : Blo 2017435 6813989 := bbase (se 4 (by rfl) ⟨638811, by rfl⟩ : syracuseStep 6813989 = 1277623) (by norm_num)
theorem B4542659 : Blo 2017435 4542659 := bstep (se 1 (by rfl) ⟨3406994, by rfl⟩ : syracuseStep 4542659 = 6813989) B6813989
theorem B3028439 : Blo 2017435 3028439 := bstep (se 1 (by rfl) ⟨2271329, by rfl⟩ : syracuseStep 3028439 = 4542659) B4542659
theorem B2018959 : Blo 2017435 2018959 := bstep (se 1 (by rfl) ⟨1514219, by rfl⟩ : syracuseStep 2018959 = 3028439) B3028439
theorem B3028445 : Blo 2017435 3028445 := bbase (se 3 (by rfl) ⟨567833, by rfl⟩ : syracuseStep 3028445 = 1135667) (by norm_num)
theorem B2018963 : Blo 2017435 2018963 := bstep (se 1 (by rfl) ⟨1514222, by rfl⟩ : syracuseStep 2018963 = 3028445) B3028445
theorem B4542677 : Blo 2017435 4542677 := bbase (se 7 (by rfl) ⟨53234, by rfl⟩ : syracuseStep 4542677 = 106469) (by norm_num)
theorem B3028451 : Blo 2017435 3028451 := bstep (se 1 (by rfl) ⟨2271338, by rfl⟩ : syracuseStep 3028451 = 4542677) B4542677
theorem B2018967 : Blo 2017435 2018967 := bstep (se 1 (by rfl) ⟨1514225, by rfl⟩ : syracuseStep 2018967 = 3028451) B3028451
theorem B2302333 : Blo 2017435 2302333 := bbase (se 3 (by rfl) ⟨431687, by rfl⟩ : syracuseStep 2302333 = 863375) (by norm_num)
theorem B12279109 : Blo 2017435 12279109 := bstep (se 4 (by rfl) ⟨1151166, by rfl⟩ : syracuseStep 12279109 = 2302333) B2302333
theorem B16372145 : Blo 2017435 16372145 := bstep (se 2 (by rfl) ⟨6139554, by rfl⟩ : syracuseStep 16372145 = 12279109) B12279109
theorem B10914763 : Blo 2017435 10914763 := bstep (se 1 (by rfl) ⟨8186072, by rfl⟩ : syracuseStep 10914763 = 16372145) B16372145
theorem B14553017 : Blo 2017435 14553017 := bstep (se 2 (by rfl) ⟨5457381, by rfl⟩ : syracuseStep 14553017 = 10914763) B10914763
theorem B9702011 : Blo 2017435 9702011 := bstep (se 1 (by rfl) ⟨7276508, by rfl⟩ : syracuseStep 9702011 = 14553017) B14553017
theorem B6468007 : Blo 2017435 6468007 := bstep (se 1 (by rfl) ⟨4851005, by rfl⟩ : syracuseStep 6468007 = 9702011) B9702011
theorem B8624009 : Blo 2017435 8624009 := bstep (se 2 (by rfl) ⟨3234003, by rfl⟩ : syracuseStep 8624009 = 6468007) B6468007
theorem B5749339 : Blo 2017435 5749339 := bstep (se 1 (by rfl) ⟨4312004, by rfl⟩ : syracuseStep 5749339 = 8624009) B8624009
theorem B7665785 : Blo 2017435 7665785 := bstep (se 2 (by rfl) ⟨2874669, by rfl⟩ : syracuseStep 7665785 = 5749339) B5749339
theorem B5110523 : Blo 2017435 5110523 := bstep (se 1 (by rfl) ⟨3832892, by rfl⟩ : syracuseStep 5110523 = 7665785) B7665785
theorem B3407015 : Blo 2017435 3407015 := bstep (se 1 (by rfl) ⟨2555261, by rfl⟩ : syracuseStep 3407015 = 5110523) B5110523
theorem B2271343 : Blo 2017435 2271343 := bstep (se 1 (by rfl) ⟨1703507, by rfl⟩ : syracuseStep 2271343 = 3407015) B3407015
theorem B3028457 : Blo 2017435 3028457 := bstep (se 2 (by rfl) ⟨1135671, by rfl⟩ : syracuseStep 3028457 = 2271343) B2271343
theorem B2018971 : Blo 2017435 2018971 := bstep (se 1 (by rfl) ⟨1514228, by rfl⟩ : syracuseStep 2018971 = 3028457) B3028457
theorem B3638261 : Blo 2017435 3638261 := bbase (se 5 (by rfl) ⟨170543, by rfl⟩ : syracuseStep 3638261 = 341087) (by norm_num)
theorem B2425507 : Blo 2017435 2425507 := bstep (se 1 (by rfl) ⟨1819130, by rfl⟩ : syracuseStep 2425507 = 3638261) B3638261
theorem B12936037 : Blo 2017435 12936037 := bstep (se 4 (by rfl) ⟨1212753, by rfl⟩ : syracuseStep 12936037 = 2425507) B2425507
theorem B17248049 : Blo 2017435 17248049 := bstep (se 2 (by rfl) ⟨6468018, by rfl⟩ : syracuseStep 17248049 = 12936037) B12936037
theorem B11498699 : Blo 2017435 11498699 := bstep (se 1 (by rfl) ⟨8624024, by rfl⟩ : syracuseStep 11498699 = 17248049) B17248049
theorem B7665799 : Blo 2017435 7665799 := bstep (se 1 (by rfl) ⟨5749349, by rfl⟩ : syracuseStep 7665799 = 11498699) B11498699
theorem B10221065 : Blo 2017435 10221065 := bstep (se 2 (by rfl) ⟨3832899, by rfl⟩ : syracuseStep 10221065 = 7665799) B7665799
theorem B6814043 : Blo 2017435 6814043 := bstep (se 1 (by rfl) ⟨5110532, by rfl⟩ : syracuseStep 6814043 = 10221065) B10221065
theorem B4542695 : Blo 2017435 4542695 := bstep (se 1 (by rfl) ⟨3407021, by rfl⟩ : syracuseStep 4542695 = 6814043) B6814043
theorem B3028463 : Blo 2017435 3028463 := bstep (se 1 (by rfl) ⟨2271347, by rfl⟩ : syracuseStep 3028463 = 4542695) B4542695
theorem B2018975 : Blo 2017435 2018975 := bstep (se 1 (by rfl) ⟨1514231, by rfl⟩ : syracuseStep 2018975 = 3028463) B3028463
theorem B3028469 : Blo 2017435 3028469 := bbase (se 5 (by rfl) ⟨141959, by rfl⟩ : syracuseStep 3028469 = 283919) (by norm_num)
theorem B2018979 : Blo 2017435 2018979 := bstep (se 1 (by rfl) ⟨1514234, by rfl⟩ : syracuseStep 2018979 = 3028469) B3028469
theorem B2590141 : Blo 2017435 2590141 := bbase (se 3 (by rfl) ⟨485651, by rfl⟩ : syracuseStep 2590141 = 971303) (by norm_num)
theorem B3453521 : Blo 2017435 3453521 := bstep (se 2 (by rfl) ⟨1295070, by rfl⟩ : syracuseStep 3453521 = 2590141) B2590141
theorem B9209389 : Blo 2017435 9209389 := bstep (se 3 (by rfl) ⟨1726760, by rfl⟩ : syracuseStep 9209389 = 3453521) B3453521
theorem B12279185 : Blo 2017435 12279185 := bstep (se 2 (by rfl) ⟨4604694, by rfl⟩ : syracuseStep 12279185 = 9209389) B9209389
theorem B8186123 : Blo 2017435 8186123 := bstep (se 1 (by rfl) ⟨6139592, by rfl⟩ : syracuseStep 8186123 = 12279185) B12279185
theorem B5457415 : Blo 2017435 5457415 := bstep (se 1 (by rfl) ⟨4093061, by rfl⟩ : syracuseStep 5457415 = 8186123) B8186123
theorem B7276553 : Blo 2017435 7276553 := bstep (se 2 (by rfl) ⟨2728707, by rfl⟩ : syracuseStep 7276553 = 5457415) B5457415
theorem B4851035 : Blo 2017435 4851035 := bstep (se 1 (by rfl) ⟨3638276, by rfl⟩ : syracuseStep 4851035 = 7276553) B7276553
theorem B3234023 : Blo 2017435 3234023 := bstep (se 1 (by rfl) ⟨2425517, by rfl⟩ : syracuseStep 3234023 = 4851035) B4851035
theorem B2156015 : Blo 2017435 2156015 := bstep (se 1 (by rfl) ⟨1617011, by rfl⟩ : syracuseStep 2156015 = 3234023) B3234023
theorem B5749373 : Blo 2017435 5749373 := bstep (se 3 (by rfl) ⟨1078007, by rfl⟩ : syracuseStep 5749373 = 2156015) B2156015
theorem B3832915 : Blo 2017435 3832915 := bstep (se 1 (by rfl) ⟨2874686, by rfl⟩ : syracuseStep 3832915 = 5749373) B5749373
theorem B5110553 : Blo 2017435 5110553 := bstep (se 2 (by rfl) ⟨1916457, by rfl⟩ : syracuseStep 5110553 = 3832915) B3832915
theorem B3407035 : Blo 2017435 3407035 := bstep (se 1 (by rfl) ⟨2555276, by rfl⟩ : syracuseStep 3407035 = 5110553) B5110553
theorem B4542713 : Blo 2017435 4542713 := bstep (se 2 (by rfl) ⟨1703517, by rfl⟩ : syracuseStep 4542713 = 3407035) B3407035
theorem B3028475 : Blo 2017435 3028475 := bstep (se 1 (by rfl) ⟨2271356, by rfl⟩ : syracuseStep 3028475 = 4542713) B4542713
theorem B2018983 : Blo 2017435 2018983 := bstep (se 1 (by rfl) ⟨1514237, by rfl⟩ : syracuseStep 2018983 = 3028475) B3028475
theorem B2271361 : Blo 2017435 2271361 := bbase (se 2 (by rfl) ⟨851760, by rfl⟩ : syracuseStep 2271361 = 1703521) (by norm_num)
theorem B3028481 : Blo 2017435 3028481 := bstep (se 2 (by rfl) ⟨1135680, by rfl⟩ : syracuseStep 3028481 = 2271361) B2271361
theorem B2018987 : Blo 2017435 2018987 := bstep (se 1 (by rfl) ⟨1514240, by rfl⟩ : syracuseStep 2018987 = 3028481) B3028481
theorem B5110573 : Blo 2017435 5110573 := bbase (se 3 (by rfl) ⟨958232, by rfl⟩ : syracuseStep 5110573 = 1916465) (by norm_num)
theorem B6814097 : Blo 2017435 6814097 := bstep (se 2 (by rfl) ⟨2555286, by rfl⟩ : syracuseStep 6814097 = 5110573) B5110573
theorem B4542731 : Blo 2017435 4542731 := bstep (se 1 (by rfl) ⟨3407048, by rfl⟩ : syracuseStep 4542731 = 6814097) B6814097
theorem B3028487 : Blo 2017435 3028487 := bstep (se 1 (by rfl) ⟨2271365, by rfl⟩ : syracuseStep 3028487 = 4542731) B4542731
theorem B2018991 : Blo 2017435 2018991 := bstep (se 1 (by rfl) ⟨1514243, by rfl⟩ : syracuseStep 2018991 = 3028487) B3028487
theorem B3028493 : Blo 2017435 3028493 := bbase (se 3 (by rfl) ⟨567842, by rfl⟩ : syracuseStep 3028493 = 1135685) (by norm_num)
theorem B2018995 : Blo 2017435 2018995 := bstep (se 1 (by rfl) ⟨1514246, by rfl⟩ : syracuseStep 2018995 = 3028493) B3028493
theorem B4542749 : Blo 2017435 4542749 := bbase (se 3 (by rfl) ⟨851765, by rfl⟩ : syracuseStep 4542749 = 1703531) (by norm_num)
theorem B3028499 : Blo 2017435 3028499 := bstep (se 1 (by rfl) ⟨2271374, by rfl⟩ : syracuseStep 3028499 = 4542749) B4542749
theorem B2018999 : Blo 2017435 2018999 := bstep (se 1 (by rfl) ⟨1514249, by rfl⟩ : syracuseStep 2018999 = 3028499) B3028499
theorem B3407069 : Blo 2017435 3407069 := bbase (se 3 (by rfl) ⟨638825, by rfl⟩ : syracuseStep 3407069 = 1277651) (by norm_num)
theorem B2271379 : Blo 2017435 2271379 := bstep (se 1 (by rfl) ⟨1703534, by rfl⟩ : syracuseStep 2271379 = 3407069) B3407069
theorem B3028505 : Blo 2017435 3028505 := bstep (se 2 (by rfl) ⟨1135689, by rfl⟩ : syracuseStep 3028505 = 2271379) B2271379
theorem B2019003 : Blo 2017435 2019003 := bstep (se 1 (by rfl) ⟨1514252, by rfl⟩ : syracuseStep 2019003 = 3028505) B3028505
theorem B4093109 : Blo 2017435 4093109 := bbase (se 5 (by rfl) ⟨191864, by rfl⟩ : syracuseStep 4093109 = 383729) (by norm_num)
theorem B2728739 : Blo 2017435 2728739 := bstep (se 1 (by rfl) ⟨2046554, by rfl⟩ : syracuseStep 2728739 = 4093109) B4093109
theorem B7276637 : Blo 2017435 7276637 := bstep (se 3 (by rfl) ⟨1364369, by rfl⟩ : syracuseStep 7276637 = 2728739) B2728739
theorem B4851091 : Blo 2017435 4851091 := bstep (se 1 (by rfl) ⟨3638318, by rfl⟩ : syracuseStep 4851091 = 7276637) B7276637
theorem B6468121 : Blo 2017435 6468121 := bstep (se 2 (by rfl) ⟨2425545, by rfl⟩ : syracuseStep 6468121 = 4851091) B4851091
theorem B8624161 : Blo 2017435 8624161 := bstep (se 2 (by rfl) ⟨3234060, by rfl⟩ : syracuseStep 8624161 = 6468121) B6468121
theorem B11498881 : Blo 2017435 11498881 := bstep (se 2 (by rfl) ⟨4312080, by rfl⟩ : syracuseStep 11498881 = 8624161) B8624161
theorem B15331841 : Blo 2017435 15331841 := bstep (se 2 (by rfl) ⟨5749440, by rfl⟩ : syracuseStep 15331841 = 11498881) B11498881
theorem B10221227 : Blo 2017435 10221227 := bstep (se 1 (by rfl) ⟨7665920, by rfl⟩ : syracuseStep 10221227 = 15331841) B15331841
theorem B6814151 : Blo 2017435 6814151 := bstep (se 1 (by rfl) ⟨5110613, by rfl⟩ : syracuseStep 6814151 = 10221227) B10221227
theorem B4542767 : Blo 2017435 4542767 := bstep (se 1 (by rfl) ⟨3407075, by rfl⟩ : syracuseStep 4542767 = 6814151) B6814151
theorem B3028511 : Blo 2017435 3028511 := bstep (se 1 (by rfl) ⟨2271383, by rfl⟩ : syracuseStep 3028511 = 4542767) B4542767
theorem B2019007 : Blo 2017435 2019007 := bstep (se 1 (by rfl) ⟨1514255, by rfl⟩ : syracuseStep 2019007 = 3028511) B3028511
theorem B3028517 : Blo 2017435 3028517 := bbase (se 4 (by rfl) ⟨283923, by rfl⟩ : syracuseStep 3028517 = 567847) (by norm_num)
theorem B2019011 : Blo 2017435 2019011 := bstep (se 1 (by rfl) ⟨1514258, by rfl⟩ : syracuseStep 2019011 = 3028517) B3028517
theorem B2555317 : Blo 2017435 2555317 := bbase (se 5 (by rfl) ⟨119780, by rfl⟩ : syracuseStep 2555317 = 239561) (by norm_num)
theorem B3407089 : Blo 2017435 3407089 := bstep (se 2 (by rfl) ⟨1277658, by rfl⟩ : syracuseStep 3407089 = 2555317) B2555317
theorem B4542785 : Blo 2017435 4542785 := bstep (se 2 (by rfl) ⟨1703544, by rfl⟩ : syracuseStep 4542785 = 3407089) B3407089
theorem B3028523 : Blo 2017435 3028523 := bstep (se 1 (by rfl) ⟨2271392, by rfl⟩ : syracuseStep 3028523 = 4542785) B4542785
theorem B2019015 : Blo 2017435 2019015 := bstep (se 1 (by rfl) ⟨1514261, by rfl⟩ : syracuseStep 2019015 = 3028523) B3028523
theorem B2271397 : Blo 2017435 2271397 := bbase (se 4 (by rfl) ⟨212943, by rfl⟩ : syracuseStep 2271397 = 425887) (by norm_num)
theorem B3028529 : Blo 2017435 3028529 := bstep (se 2 (by rfl) ⟨1135698, by rfl⟩ : syracuseStep 3028529 = 2271397) B2271397
theorem B2019019 : Blo 2017435 2019019 := bstep (se 1 (by rfl) ⟨1514264, by rfl⟩ : syracuseStep 2019019 = 3028529) B3028529
theorem B2074493 : Blo 2017435 2074493 := bbase (se 3 (by rfl) ⟨388967, by rfl⟩ : syracuseStep 2074493 = 777935) (by norm_num)
theorem B5531981 : Blo 2017435 5531981 := bstep (se 3 (by rfl) ⟨1037246, by rfl⟩ : syracuseStep 5531981 = 2074493) B2074493
theorem B59007797 : Blo 2017435 59007797 := bstep (se 5 (by rfl) ⟨2765990, by rfl⟩ : syracuseStep 59007797 = 5531981) B5531981
theorem B39338531 : Blo 2017435 39338531 := bstep (se 1 (by rfl) ⟨29503898, by rfl⟩ : syracuseStep 39338531 = 59007797) B59007797
theorem B26225687 : Blo 2017435 26225687 := bstep (se 1 (by rfl) ⟨19669265, by rfl⟩ : syracuseStep 26225687 = 39338531) B39338531
theorem B17483791 : Blo 2017435 17483791 := bstep (se 1 (by rfl) ⟨13112843, by rfl⟩ : syracuseStep 17483791 = 26225687) B26225687
theorem B23311721 : Blo 2017435 23311721 := bstep (se 2 (by rfl) ⟨8741895, by rfl⟩ : syracuseStep 23311721 = 17483791) B17483791
theorem B15541147 : Blo 2017435 15541147 := bstep (se 1 (by rfl) ⟨11655860, by rfl⟩ : syracuseStep 15541147 = 23311721) B23311721
theorem B20721529 : Blo 2017435 20721529 := bstep (se 2 (by rfl) ⟨7770573, by rfl⟩ : syracuseStep 20721529 = 15541147) B15541147
theorem B27628705 : Blo 2017435 27628705 := bstep (se 2 (by rfl) ⟨10360764, by rfl⟩ : syracuseStep 27628705 = 20721529) B20721529
theorem B36838273 : Blo 2017435 36838273 := bstep (se 2 (by rfl) ⟨13814352, by rfl⟩ : syracuseStep 36838273 = 27628705) B27628705
theorem B49117697 : Blo 2017435 49117697 := bstep (se 2 (by rfl) ⟨18419136, by rfl⟩ : syracuseStep 49117697 = 36838273) B36838273
theorem B32745131 : Blo 2017435 32745131 := bstep (se 1 (by rfl) ⟨24558848, by rfl⟩ : syracuseStep 32745131 = 49117697) B49117697
theorem B21830087 : Blo 2017435 21830087 := bstep (se 1 (by rfl) ⟨16372565, by rfl⟩ : syracuseStep 21830087 = 32745131) B32745131
theorem B14553391 : Blo 2017435 14553391 := bstep (se 1 (by rfl) ⟨10915043, by rfl⟩ : syracuseStep 14553391 = 21830087) B21830087
theorem B19404521 : Blo 2017435 19404521 := bstep (se 2 (by rfl) ⟨7276695, by rfl⟩ : syracuseStep 19404521 = 14553391) B14553391
theorem B12936347 : Blo 2017435 12936347 := bstep (se 1 (by rfl) ⟨9702260, by rfl⟩ : syracuseStep 12936347 = 19404521) B19404521
theorem B8624231 : Blo 2017435 8624231 := bstep (se 1 (by rfl) ⟨6468173, by rfl⟩ : syracuseStep 8624231 = 12936347) B12936347
theorem B5749487 : Blo 2017435 5749487 := bstep (se 1 (by rfl) ⟨4312115, by rfl⟩ : syracuseStep 5749487 = 8624231) B8624231
theorem B3832991 : Blo 2017435 3832991 := bstep (se 1 (by rfl) ⟨2874743, by rfl⟩ : syracuseStep 3832991 = 5749487) B5749487
theorem B2555327 : Blo 2017435 2555327 := bstep (se 1 (by rfl) ⟨1916495, by rfl⟩ : syracuseStep 2555327 = 3832991) B3832991
theorem B6814205 : Blo 2017435 6814205 := bstep (se 3 (by rfl) ⟨1277663, by rfl⟩ : syracuseStep 6814205 = 2555327) B2555327
theorem B4542803 : Blo 2017435 4542803 := bstep (se 1 (by rfl) ⟨3407102, by rfl⟩ : syracuseStep 4542803 = 6814205) B6814205
theorem B3028535 : Blo 2017435 3028535 := bstep (se 1 (by rfl) ⟨2271401, by rfl⟩ : syracuseStep 3028535 = 4542803) B4542803
theorem B2019023 : Blo 2017435 2019023 := bstep (se 1 (by rfl) ⟨1514267, by rfl⟩ : syracuseStep 2019023 = 3028535) B3028535
theorem B3028541 : Blo 2017435 3028541 := bbase (se 3 (by rfl) ⟨567851, by rfl⟩ : syracuseStep 3028541 = 1135703) (by norm_num)
theorem B2019027 : Blo 2017435 2019027 := bstep (se 1 (by rfl) ⟨1514270, by rfl⟩ : syracuseStep 2019027 = 3028541) B3028541
theorem B4542821 : Blo 2017435 4542821 := bbase (se 4 (by rfl) ⟨425889, by rfl⟩ : syracuseStep 4542821 = 851779) (by norm_num)
theorem B3028547 : Blo 2017435 3028547 := bstep (se 1 (by rfl) ⟨2271410, by rfl⟩ : syracuseStep 3028547 = 4542821) B4542821
theorem B2019031 : Blo 2017435 2019031 := bstep (se 1 (by rfl) ⟨1514273, by rfl⟩ : syracuseStep 2019031 = 3028547) B3028547
theorem B5110685 : Blo 2017435 5110685 := bbase (se 3 (by rfl) ⟨958253, by rfl⟩ : syracuseStep 5110685 = 1916507) (by norm_num)
theorem B3407123 : Blo 2017435 3407123 := bstep (se 1 (by rfl) ⟨2555342, by rfl⟩ : syracuseStep 3407123 = 5110685) B5110685
theorem B2271415 : Blo 2017435 2271415 := bstep (se 1 (by rfl) ⟨1703561, by rfl⟩ : syracuseStep 2271415 = 3407123) B3407123
theorem B3028553 : Blo 2017435 3028553 := bstep (se 2 (by rfl) ⟨1135707, by rfl⟩ : syracuseStep 3028553 = 2271415) B2271415
theorem B2019035 : Blo 2017435 2019035 := bstep (se 1 (by rfl) ⟨1514276, by rfl⟩ : syracuseStep 2019035 = 3028553) B3028553
theorem B3833021 : Blo 2017435 3833021 := bbase (se 3 (by rfl) ⟨718691, by rfl⟩ : syracuseStep 3833021 = 1437383) (by norm_num)
theorem B10221389 : Blo 2017435 10221389 := bstep (se 3 (by rfl) ⟨1916510, by rfl⟩ : syracuseStep 10221389 = 3833021) B3833021
theorem B6814259 : Blo 2017435 6814259 := bstep (se 1 (by rfl) ⟨5110694, by rfl⟩ : syracuseStep 6814259 = 10221389) B10221389
theorem B4542839 : Blo 2017435 4542839 := bstep (se 1 (by rfl) ⟨3407129, by rfl⟩ : syracuseStep 4542839 = 6814259) B6814259
theorem B3028559 : Blo 2017435 3028559 := bstep (se 1 (by rfl) ⟨2271419, by rfl⟩ : syracuseStep 3028559 = 4542839) B4542839
theorem B2019039 : Blo 2017435 2019039 := bstep (se 1 (by rfl) ⟨1514279, by rfl⟩ : syracuseStep 2019039 = 3028559) B3028559
theorem B3028565 : Blo 2017435 3028565 := bbase (se 8 (by rfl) ⟨17745, by rfl⟩ : syracuseStep 3028565 = 35491) (by norm_num)
theorem B2019043 : Blo 2017435 2019043 := bstep (se 1 (by rfl) ⟨1514282, by rfl⟩ : syracuseStep 2019043 = 3028565) B3028565
theorem B3234125 : Blo 2017435 3234125 := bbase (se 3 (by rfl) ⟨606398, by rfl⟩ : syracuseStep 3234125 = 1212797) (by norm_num)
theorem B8624333 : Blo 2017435 8624333 := bstep (se 3 (by rfl) ⟨1617062, by rfl⟩ : syracuseStep 8624333 = 3234125) B3234125
theorem B5749555 : Blo 2017435 5749555 := bstep (se 1 (by rfl) ⟨4312166, by rfl⟩ : syracuseStep 5749555 = 8624333) B8624333
theorem B7666073 : Blo 2017435 7666073 := bstep (se 2 (by rfl) ⟨2874777, by rfl⟩ : syracuseStep 7666073 = 5749555) B5749555
theorem B5110715 : Blo 2017435 5110715 := bstep (se 1 (by rfl) ⟨3833036, by rfl⟩ : syracuseStep 5110715 = 7666073) B7666073
theorem B3407143 : Blo 2017435 3407143 := bstep (se 1 (by rfl) ⟨2555357, by rfl⟩ : syracuseStep 3407143 = 5110715) B5110715
theorem B4542857 : Blo 2017435 4542857 := bstep (se 2 (by rfl) ⟨1703571, by rfl⟩ : syracuseStep 4542857 = 3407143) B3407143
theorem B3028571 : Blo 2017435 3028571 := bstep (se 1 (by rfl) ⟨2271428, by rfl⟩ : syracuseStep 3028571 = 4542857) B4542857
theorem B2019047 : Blo 2017435 2019047 := bstep (se 1 (by rfl) ⟨1514285, by rfl⟩ : syracuseStep 2019047 = 3028571) B3028571
theorem B2271433 : Blo 2017435 2271433 := bbase (se 2 (by rfl) ⟨851787, by rfl⟩ : syracuseStep 2271433 = 1703575) (by norm_num)
theorem B3028577 : Blo 2017435 3028577 := bstep (se 2 (by rfl) ⟨1135716, by rfl⟩ : syracuseStep 3028577 = 2271433) B2271433
theorem B2019051 : Blo 2017435 2019051 := bstep (se 1 (by rfl) ⟨1514288, by rfl⟩ : syracuseStep 2019051 = 3028577) B3028577
theorem B3638405 : Blo 2017435 3638405 := bbase (se 4 (by rfl) ⟨341100, by rfl⟩ : syracuseStep 3638405 = 682201) (by norm_num)
theorem B9702413 : Blo 2017435 9702413 := bstep (se 3 (by rfl) ⟨1819202, by rfl⟩ : syracuseStep 9702413 = 3638405) B3638405
theorem B6468275 : Blo 2017435 6468275 := bstep (se 1 (by rfl) ⟨4851206, by rfl⟩ : syracuseStep 6468275 = 9702413) B9702413
theorem B17248733 : Blo 2017435 17248733 := bstep (se 3 (by rfl) ⟨3234137, by rfl⟩ : syracuseStep 17248733 = 6468275) B6468275
theorem B11499155 : Blo 2017435 11499155 := bstep (se 1 (by rfl) ⟨8624366, by rfl⟩ : syracuseStep 11499155 = 17248733) B17248733
theorem B7666103 : Blo 2017435 7666103 := bstep (se 1 (by rfl) ⟨5749577, by rfl⟩ : syracuseStep 7666103 = 11499155) B11499155
theorem B5110735 : Blo 2017435 5110735 := bstep (se 1 (by rfl) ⟨3833051, by rfl⟩ : syracuseStep 5110735 = 7666103) B7666103
theorem B6814313 : Blo 2017435 6814313 := bstep (se 2 (by rfl) ⟨2555367, by rfl⟩ : syracuseStep 6814313 = 5110735) B5110735
theorem B4542875 : Blo 2017435 4542875 := bstep (se 1 (by rfl) ⟨3407156, by rfl⟩ : syracuseStep 4542875 = 6814313) B6814313
theorem B3028583 : Blo 2017435 3028583 := bstep (se 1 (by rfl) ⟨2271437, by rfl⟩ : syracuseStep 3028583 = 4542875) B4542875
theorem B2019055 : Blo 2017435 2019055 := bstep (se 1 (by rfl) ⟨1514291, by rfl⟩ : syracuseStep 2019055 = 3028583) B3028583
theorem B3028589 : Blo 2017435 3028589 := bbase (se 3 (by rfl) ⟨567860, by rfl⟩ : syracuseStep 3028589 = 1135721) (by norm_num)
theorem B2019059 : Blo 2017435 2019059 := bstep (se 1 (by rfl) ⟨1514294, by rfl⟩ : syracuseStep 2019059 = 3028589) B3028589
theorem B4542893 : Blo 2017435 4542893 := bbase (se 3 (by rfl) ⟨851792, by rfl⟩ : syracuseStep 4542893 = 1703585) (by norm_num)
theorem B3028595 : Blo 2017435 3028595 := bstep (se 1 (by rfl) ⟨2271446, by rfl⟩ : syracuseStep 3028595 = 4542893) B4542893
theorem B2019063 : Blo 2017435 2019063 := bstep (se 1 (by rfl) ⟨1514297, by rfl⟩ : syracuseStep 2019063 = 3028595) B3028595
theorem B2156105 : Blo 2017435 2156105 := bbase (se 2 (by rfl) ⟨808539, by rfl⟩ : syracuseStep 2156105 = 1617079) (by norm_num)
theorem B5749613 : Blo 2017435 5749613 := bstep (se 3 (by rfl) ⟨1078052, by rfl⟩ : syracuseStep 5749613 = 2156105) B2156105
theorem B3833075 : Blo 2017435 3833075 := bstep (se 1 (by rfl) ⟨2874806, by rfl⟩ : syracuseStep 3833075 = 5749613) B5749613
theorem B2555383 : Blo 2017435 2555383 := bstep (se 1 (by rfl) ⟨1916537, by rfl⟩ : syracuseStep 2555383 = 3833075) B3833075
theorem B3407177 : Blo 2017435 3407177 := bstep (se 2 (by rfl) ⟨1277691, by rfl⟩ : syracuseStep 3407177 = 2555383) B2555383
theorem B2271451 : Blo 2017435 2271451 := bstep (se 1 (by rfl) ⟨1703588, by rfl⟩ : syracuseStep 2271451 = 3407177) B3407177
theorem B3028601 : Blo 2017435 3028601 := bstep (se 2 (by rfl) ⟨1135725, by rfl⟩ : syracuseStep 3028601 = 2271451) B2271451
theorem B2019067 : Blo 2017435 2019067 := bstep (se 1 (by rfl) ⟨1514300, by rfl⟩ : syracuseStep 2019067 = 3028601) B3028601
theorem B5251189 : Blo 2017435 5251189 := bbase (se 5 (by rfl) ⟨246149, by rfl⟩ : syracuseStep 5251189 = 492299) (by norm_num)
theorem B7001585 : Blo 2017435 7001585 := bstep (se 2 (by rfl) ⟨2625594, by rfl⟩ : syracuseStep 7001585 = 5251189) B5251189
theorem B4667723 : Blo 2017435 4667723 := bstep (se 1 (by rfl) ⟨3500792, by rfl⟩ : syracuseStep 4667723 = 7001585) B7001585
theorem B3111815 : Blo 2017435 3111815 := bstep (se 1 (by rfl) ⟨2333861, by rfl⟩ : syracuseStep 3111815 = 4667723) B4667723
theorem B8298173 : Blo 2017435 8298173 := bstep (se 3 (by rfl) ⟨1555907, by rfl⟩ : syracuseStep 8298173 = 3111815) B3111815
theorem B22128461 : Blo 2017435 22128461 := bstep (se 3 (by rfl) ⟨4149086, by rfl⟩ : syracuseStep 22128461 = 8298173) B8298173
theorem B14752307 : Blo 2017435 14752307 := bstep (se 1 (by rfl) ⟨11064230, by rfl⟩ : syracuseStep 14752307 = 22128461) B22128461
theorem B9834871 : Blo 2017435 9834871 := bstep (se 1 (by rfl) ⟨7376153, by rfl⟩ : syracuseStep 9834871 = 14752307) B14752307
theorem B13113161 : Blo 2017435 13113161 := bstep (se 2 (by rfl) ⟨4917435, by rfl⟩ : syracuseStep 13113161 = 9834871) B9834871
theorem B8742107 : Blo 2017435 8742107 := bstep (se 1 (by rfl) ⟨6556580, by rfl⟩ : syracuseStep 8742107 = 13113161) B13113161
theorem B5828071 : Blo 2017435 5828071 := bstep (se 1 (by rfl) ⟨4371053, by rfl⟩ : syracuseStep 5828071 = 8742107) B8742107
theorem B7770761 : Blo 2017435 7770761 := bstep (se 2 (by rfl) ⟨2914035, by rfl⟩ : syracuseStep 7770761 = 5828071) B5828071
theorem B5180507 : Blo 2017435 5180507 := bstep (se 1 (by rfl) ⟨3885380, by rfl⟩ : syracuseStep 5180507 = 7770761) B7770761
theorem B3453671 : Blo 2017435 3453671 := bstep (se 1 (by rfl) ⟨2590253, by rfl⟩ : syracuseStep 3453671 = 5180507) B5180507
theorem B2302447 : Blo 2017435 2302447 := bstep (se 1 (by rfl) ⟨1726835, by rfl⟩ : syracuseStep 2302447 = 3453671) B3453671
theorem B3069929 : Blo 2017435 3069929 := bstep (se 2 (by rfl) ⟨1151223, by rfl⟩ : syracuseStep 3069929 = 2302447) B2302447
theorem B2046619 : Blo 2017435 2046619 := bstep (se 1 (by rfl) ⟨1534964, by rfl⟩ : syracuseStep 2046619 = 3069929) B3069929
theorem B2728825 : Blo 2017435 2728825 := bstep (se 2 (by rfl) ⟨1023309, by rfl⟩ : syracuseStep 2728825 = 2046619) B2046619
theorem B58214933 : Blo 2017435 58214933 := bstep (se 6 (by rfl) ⟨1364412, by rfl⟩ : syracuseStep 58214933 = 2728825) B2728825
theorem B38809955 : Blo 2017435 38809955 := bstep (se 1 (by rfl) ⟨29107466, by rfl⟩ : syracuseStep 38809955 = 58214933) B58214933
theorem B25873303 : Blo 2017435 25873303 := bstep (se 1 (by rfl) ⟨19404977, by rfl⟩ : syracuseStep 25873303 = 38809955) B38809955
theorem B34497737 : Blo 2017435 34497737 := bstep (se 2 (by rfl) ⟨12936651, by rfl⟩ : syracuseStep 34497737 = 25873303) B25873303
theorem B22998491 : Blo 2017435 22998491 := bstep (se 1 (by rfl) ⟨17248868, by rfl⟩ : syracuseStep 22998491 = 34497737) B34497737
theorem B15332327 : Blo 2017435 15332327 := bstep (se 1 (by rfl) ⟨11499245, by rfl⟩ : syracuseStep 15332327 = 22998491) B22998491
theorem B10221551 : Blo 2017435 10221551 := bstep (se 1 (by rfl) ⟨7666163, by rfl⟩ : syracuseStep 10221551 = 15332327) B15332327
theorem B6814367 : Blo 2017435 6814367 := bstep (se 1 (by rfl) ⟨5110775, by rfl⟩ : syracuseStep 6814367 = 10221551) B10221551
theorem B4542911 : Blo 2017435 4542911 := bstep (se 1 (by rfl) ⟨3407183, by rfl⟩ : syracuseStep 4542911 = 6814367) B6814367
theorem B3028607 : Blo 2017435 3028607 := bstep (se 1 (by rfl) ⟨2271455, by rfl⟩ : syracuseStep 3028607 = 4542911) B4542911
theorem B2019071 : Blo 2017435 2019071 := bstep (se 1 (by rfl) ⟨1514303, by rfl⟩ : syracuseStep 2019071 = 3028607) B3028607
theorem B3028613 : Blo 2017435 3028613 := bbase (se 4 (by rfl) ⟨283932, by rfl⟩ : syracuseStep 3028613 = 567865) (by norm_num)
theorem B2019075 : Blo 2017435 2019075 := bstep (se 1 (by rfl) ⟨1514306, by rfl⟩ : syracuseStep 2019075 = 3028613) B3028613
theorem B3407197 : Blo 2017435 3407197 := bbase (se 3 (by rfl) ⟨638849, by rfl⟩ : syracuseStep 3407197 = 1277699) (by norm_num)
theorem B4542929 : Blo 2017435 4542929 := bstep (se 2 (by rfl) ⟨1703598, by rfl⟩ : syracuseStep 4542929 = 3407197) B3407197
theorem B3028619 : Blo 2017435 3028619 := bstep (se 1 (by rfl) ⟨2271464, by rfl⟩ : syracuseStep 3028619 = 4542929) B4542929
theorem B2019079 : Blo 2017435 2019079 := bstep (se 1 (by rfl) ⟨1514309, by rfl⟩ : syracuseStep 2019079 = 3028619) B3028619
theorem B2271469 : Blo 2017435 2271469 := bbase (se 3 (by rfl) ⟨425900, by rfl⟩ : syracuseStep 2271469 = 851801) (by norm_num)
theorem B3028625 : Blo 2017435 3028625 := bstep (se 2 (by rfl) ⟨1135734, by rfl⟩ : syracuseStep 3028625 = 2271469) B2271469
theorem B2019083 : Blo 2017435 2019083 := bstep (se 1 (by rfl) ⟨1514312, by rfl⟩ : syracuseStep 2019083 = 3028625) B3028625
theorem B6814421 : Blo 2017435 6814421 := bbase (se 7 (by rfl) ⟨79856, by rfl⟩ : syracuseStep 6814421 = 159713) (by norm_num)
theorem B4542947 : Blo 2017435 4542947 := bstep (se 1 (by rfl) ⟨3407210, by rfl⟩ : syracuseStep 4542947 = 6814421) B6814421
theorem B3028631 : Blo 2017435 3028631 := bstep (se 1 (by rfl) ⟨2271473, by rfl⟩ : syracuseStep 3028631 = 4542947) B4542947
theorem B2019087 : Blo 2017435 2019087 := bstep (se 1 (by rfl) ⟨1514315, by rfl⟩ : syracuseStep 2019087 = 3028631) B3028631
theorem B3028637 : Blo 2017435 3028637 := bbase (se 3 (by rfl) ⟨567869, by rfl⟩ : syracuseStep 3028637 = 1135739) (by norm_num)
theorem B2019091 : Blo 2017435 2019091 := bstep (se 1 (by rfl) ⟨1514318, by rfl⟩ : syracuseStep 2019091 = 3028637) B3028637
theorem B4542965 : Blo 2017435 4542965 := bbase (se 5 (by rfl) ⟨212951, by rfl⟩ : syracuseStep 4542965 = 425903) (by norm_num)
theorem B3028643 : Blo 2017435 3028643 := bstep (se 1 (by rfl) ⟨2271482, by rfl⟩ : syracuseStep 3028643 = 4542965) B4542965
theorem B2019095 : Blo 2017435 2019095 := bstep (se 1 (by rfl) ⟨1514321, by rfl⟩ : syracuseStep 2019095 = 3028643) B3028643
theorem B15753781 : Blo 2017435 15753781 := bbase (se 5 (by rfl) ⟨738458, by rfl⟩ : syracuseStep 15753781 = 1476917) (by norm_num)
theorem B84020165 : Blo 2017435 84020165 := bstep (se 4 (by rfl) ⟨7876890, by rfl⟩ : syracuseStep 84020165 = 15753781) B15753781
theorem B56013443 : Blo 2017435 56013443 := bstep (se 1 (by rfl) ⟨42010082, by rfl⟩ : syracuseStep 56013443 = 84020165) B84020165
theorem B37342295 : Blo 2017435 37342295 := bstep (se 1 (by rfl) ⟨28006721, by rfl⟩ : syracuseStep 37342295 = 56013443) B56013443
theorem B24894863 : Blo 2017435 24894863 := bstep (se 1 (by rfl) ⟨18671147, by rfl⟩ : syracuseStep 24894863 = 37342295) B37342295
theorem B16596575 : Blo 2017435 16596575 := bstep (se 1 (by rfl) ⟨12447431, by rfl⟩ : syracuseStep 16596575 = 24894863) B24894863
theorem B11064383 : Blo 2017435 11064383 := bstep (se 1 (by rfl) ⟨8298287, by rfl⟩ : syracuseStep 11064383 = 16596575) B16596575
theorem B7376255 : Blo 2017435 7376255 := bstep (se 1 (by rfl) ⟨5532191, by rfl⟩ : syracuseStep 7376255 = 11064383) B11064383
theorem B4917503 : Blo 2017435 4917503 := bstep (se 1 (by rfl) ⟨3688127, by rfl⟩ : syracuseStep 4917503 = 7376255) B7376255
theorem B3278335 : Blo 2017435 3278335 := bstep (se 1 (by rfl) ⟨2458751, by rfl⟩ : syracuseStep 3278335 = 4917503) B4917503
theorem B4371113 : Blo 2017435 4371113 := bstep (se 2 (by rfl) ⟨1639167, by rfl⟩ : syracuseStep 4371113 = 3278335) B3278335
theorem B2914075 : Blo 2017435 2914075 := bstep (se 1 (by rfl) ⟨2185556, by rfl⟩ : syracuseStep 2914075 = 4371113) B4371113
theorem B15541733 : Blo 2017435 15541733 := bstep (se 4 (by rfl) ⟨1457037, by rfl⟩ : syracuseStep 15541733 = 2914075) B2914075
theorem B41444621 : Blo 2017435 41444621 := bstep (se 3 (by rfl) ⟨7770866, by rfl⟩ : syracuseStep 41444621 = 15541733) B15541733
theorem B27629747 : Blo 2017435 27629747 := bstep (se 1 (by rfl) ⟨20722310, by rfl⟩ : syracuseStep 27629747 = 41444621) B41444621
theorem B18419831 : Blo 2017435 18419831 := bstep (se 1 (by rfl) ⟨13814873, by rfl⟩ : syracuseStep 18419831 = 27629747) B27629747
theorem B12279887 : Blo 2017435 12279887 := bstep (se 1 (by rfl) ⟨9209915, by rfl⟩ : syracuseStep 12279887 = 18419831) B18419831
theorem B8186591 : Blo 2017435 8186591 := bstep (se 1 (by rfl) ⟨6139943, by rfl⟩ : syracuseStep 8186591 = 12279887) B12279887
theorem B5457727 : Blo 2017435 5457727 := bstep (se 1 (by rfl) ⟨4093295, by rfl⟩ : syracuseStep 5457727 = 8186591) B8186591
theorem B7276969 : Blo 2017435 7276969 := bstep (se 2 (by rfl) ⟨2728863, by rfl⟩ : syracuseStep 7276969 = 5457727) B5457727
theorem B38810501 : Blo 2017435 38810501 := bstep (se 4 (by rfl) ⟨3638484, by rfl⟩ : syracuseStep 38810501 = 7276969) B7276969
theorem B25873667 : Blo 2017435 25873667 := bstep (se 1 (by rfl) ⟨19405250, by rfl⟩ : syracuseStep 25873667 = 38810501) B38810501
theorem B17249111 : Blo 2017435 17249111 := bstep (se 1 (by rfl) ⟨12936833, by rfl⟩ : syracuseStep 17249111 = 25873667) B25873667
theorem B11499407 : Blo 2017435 11499407 := bstep (se 1 (by rfl) ⟨8624555, by rfl⟩ : syracuseStep 11499407 = 17249111) B17249111
theorem B7666271 : Blo 2017435 7666271 := bstep (se 1 (by rfl) ⟨5749703, by rfl⟩ : syracuseStep 7666271 = 11499407) B11499407
theorem B5110847 : Blo 2017435 5110847 := bstep (se 1 (by rfl) ⟨3833135, by rfl⟩ : syracuseStep 5110847 = 7666271) B7666271
theorem B3407231 : Blo 2017435 3407231 := bstep (se 1 (by rfl) ⟨2555423, by rfl⟩ : syracuseStep 3407231 = 5110847) B5110847
theorem B2271487 : Blo 2017435 2271487 := bstep (se 1 (by rfl) ⟨1703615, by rfl⟩ : syracuseStep 2271487 = 3407231) B3407231
theorem B3028649 : Blo 2017435 3028649 := bstep (se 2 (by rfl) ⟨1135743, by rfl⟩ : syracuseStep 3028649 = 2271487) B2271487
theorem B2019099 : Blo 2017435 2019099 := bstep (se 1 (by rfl) ⟨1514324, by rfl⟩ : syracuseStep 2019099 = 3028649) B3028649
theorem B6139957 : Blo 2017435 6139957 := bbase (se 5 (by rfl) ⟨287810, by rfl⟩ : syracuseStep 6139957 = 575621) (by norm_num)
theorem B8186609 : Blo 2017435 8186609 := bstep (se 2 (by rfl) ⟨3069978, by rfl⟩ : syracuseStep 8186609 = 6139957) B6139957
theorem B5457739 : Blo 2017435 5457739 := bstep (se 1 (by rfl) ⟨4093304, by rfl⟩ : syracuseStep 5457739 = 8186609) B8186609
theorem B7276985 : Blo 2017435 7276985 := bstep (se 2 (by rfl) ⟨2728869, by rfl⟩ : syracuseStep 7276985 = 5457739) B5457739
theorem B4851323 : Blo 2017435 4851323 := bstep (se 1 (by rfl) ⟨3638492, by rfl⟩ : syracuseStep 4851323 = 7276985) B7276985
theorem B3234215 : Blo 2017435 3234215 := bstep (se 1 (by rfl) ⟨2425661, by rfl⟩ : syracuseStep 3234215 = 4851323) B4851323
theorem B2156143 : Blo 2017435 2156143 := bstep (se 1 (by rfl) ⟨1617107, by rfl⟩ : syracuseStep 2156143 = 3234215) B3234215
theorem B2874857 : Blo 2017435 2874857 := bstep (se 2 (by rfl) ⟨1078071, by rfl⟩ : syracuseStep 2874857 = 2156143) B2156143
theorem B7666285 : Blo 2017435 7666285 := bstep (se 3 (by rfl) ⟨1437428, by rfl⟩ : syracuseStep 7666285 = 2874857) B2874857
theorem B10221713 : Blo 2017435 10221713 := bstep (se 2 (by rfl) ⟨3833142, by rfl⟩ : syracuseStep 10221713 = 7666285) B7666285
theorem B6814475 : Blo 2017435 6814475 := bstep (se 1 (by rfl) ⟨5110856, by rfl⟩ : syracuseStep 6814475 = 10221713) B10221713
theorem B4542983 : Blo 2017435 4542983 := bstep (se 1 (by rfl) ⟨3407237, by rfl⟩ : syracuseStep 4542983 = 6814475) B6814475
theorem B3028655 : Blo 2017435 3028655 := bstep (se 1 (by rfl) ⟨2271491, by rfl⟩ : syracuseStep 3028655 = 4542983) B4542983
theorem B2019103 : Blo 2017435 2019103 := bstep (se 1 (by rfl) ⟨1514327, by rfl⟩ : syracuseStep 2019103 = 3028655) B3028655
theorem B3028661 : Blo 2017435 3028661 := bbase (se 5 (by rfl) ⟨141968, by rfl⟩ : syracuseStep 3028661 = 283937) (by norm_num)
theorem B2019107 : Blo 2017435 2019107 := bstep (se 1 (by rfl) ⟨1514330, by rfl⟩ : syracuseStep 2019107 = 3028661) B3028661
theorem B5110877 : Blo 2017435 5110877 := bbase (se 3 (by rfl) ⟨958289, by rfl⟩ : syracuseStep 5110877 = 1916579) (by norm_num)
theorem B3407251 : Blo 2017435 3407251 := bstep (se 1 (by rfl) ⟨2555438, by rfl⟩ : syracuseStep 3407251 = 5110877) B5110877
theorem B4543001 : Blo 2017435 4543001 := bstep (se 2 (by rfl) ⟨1703625, by rfl⟩ : syracuseStep 4543001 = 3407251) B3407251
theorem B3028667 : Blo 2017435 3028667 := bstep (se 1 (by rfl) ⟨2271500, by rfl⟩ : syracuseStep 3028667 = 4543001) B4543001
theorem B2019111 : Blo 2017435 2019111 := bstep (se 1 (by rfl) ⟨1514333, by rfl⟩ : syracuseStep 2019111 = 3028667) B3028667
theorem B2271505 : Blo 2017435 2271505 := bbase (se 2 (by rfl) ⟨851814, by rfl⟩ : syracuseStep 2271505 = 1703629) (by norm_num)
theorem B3028673 : Blo 2017435 3028673 := bstep (se 2 (by rfl) ⟨1135752, by rfl⟩ : syracuseStep 3028673 = 2271505) B2271505
theorem B2019115 : Blo 2017435 2019115 := bstep (se 1 (by rfl) ⟨1514336, by rfl⟩ : syracuseStep 2019115 = 3028673) B3028673
theorem B3833173 : Blo 2017435 3833173 := bbase (se 11 (by rfl) ⟨2807, by rfl⟩ : syracuseStep 3833173 = 5615) (by norm_num)
theorem B5110897 : Blo 2017435 5110897 := bstep (se 2 (by rfl) ⟨1916586, by rfl⟩ : syracuseStep 5110897 = 3833173) B3833173
theorem B6814529 : Blo 2017435 6814529 := bstep (se 2 (by rfl) ⟨2555448, by rfl⟩ : syracuseStep 6814529 = 5110897) B5110897
theorem B4543019 : Blo 2017435 4543019 := bstep (se 1 (by rfl) ⟨3407264, by rfl⟩ : syracuseStep 4543019 = 6814529) B6814529
theorem B3028679 : Blo 2017435 3028679 := bstep (se 1 (by rfl) ⟨2271509, by rfl⟩ : syracuseStep 3028679 = 4543019) B4543019
theorem B2019119 : Blo 2017435 2019119 := bstep (se 1 (by rfl) ⟨1514339, by rfl⟩ : syracuseStep 2019119 = 3028679) B3028679
theorem B3028685 : Blo 2017435 3028685 := bbase (se 3 (by rfl) ⟨567878, by rfl⟩ : syracuseStep 3028685 = 1135757) (by norm_num)
theorem B2019123 : Blo 2017435 2019123 := bstep (se 1 (by rfl) ⟨1514342, by rfl⟩ : syracuseStep 2019123 = 3028685) B3028685
theorem B4543037 : Blo 2017435 4543037 := bbase (se 3 (by rfl) ⟨851819, by rfl⟩ : syracuseStep 4543037 = 1703639) (by norm_num)
theorem B3028691 : Blo 2017435 3028691 := bstep (se 1 (by rfl) ⟨2271518, by rfl⟩ : syracuseStep 3028691 = 4543037) B4543037
theorem B2019127 : Blo 2017435 2019127 := bstep (se 1 (by rfl) ⟨1514345, by rfl⟩ : syracuseStep 2019127 = 3028691) B3028691
theorem B3407285 : Blo 2017435 3407285 := bbase (se 5 (by rfl) ⟨159716, by rfl⟩ : syracuseStep 3407285 = 319433) (by norm_num)
theorem B2271523 : Blo 2017435 2271523 := bstep (se 1 (by rfl) ⟨1703642, by rfl⟩ : syracuseStep 2271523 = 3407285) B3407285
theorem B3028697 : Blo 2017435 3028697 := bstep (se 2 (by rfl) ⟨1135761, by rfl⟩ : syracuseStep 3028697 = 2271523) B2271523
theorem B2019131 : Blo 2017435 2019131 := bstep (se 1 (by rfl) ⟨1514348, by rfl⟩ : syracuseStep 2019131 = 3028697) B3028697
theorem B2156177 : Blo 2017435 2156177 := bbase (se 2 (by rfl) ⟨808566, by rfl⟩ : syracuseStep 2156177 = 1617133) (by norm_num)
theorem B5749805 : Blo 2017435 5749805 := bstep (se 3 (by rfl) ⟨1078088, by rfl⟩ : syracuseStep 5749805 = 2156177) B2156177
theorem B15332813 : Blo 2017435 15332813 := bstep (se 3 (by rfl) ⟨2874902, by rfl⟩ : syracuseStep 15332813 = 5749805) B5749805
theorem B10221875 : Blo 2017435 10221875 := bstep (se 1 (by rfl) ⟨7666406, by rfl⟩ : syracuseStep 10221875 = 15332813) B15332813
theorem B6814583 : Blo 2017435 6814583 := bstep (se 1 (by rfl) ⟨5110937, by rfl⟩ : syracuseStep 6814583 = 10221875) B10221875
theorem B4543055 : Blo 2017435 4543055 := bstep (se 1 (by rfl) ⟨3407291, by rfl⟩ : syracuseStep 4543055 = 6814583) B6814583
theorem B3028703 : Blo 2017435 3028703 := bstep (se 1 (by rfl) ⟨2271527, by rfl⟩ : syracuseStep 3028703 = 4543055) B4543055
theorem B2019135 : Blo 2017435 2019135 := bstep (se 1 (by rfl) ⟨1514351, by rfl⟩ : syracuseStep 2019135 = 3028703) B3028703
theorem B3028709 : Blo 2017435 3028709 := bbase (se 4 (by rfl) ⟨283941, by rfl⟩ : syracuseStep 3028709 = 567883) (by norm_num)
theorem B2019139 : Blo 2017435 2019139 := bstep (se 1 (by rfl) ⟨1514354, by rfl⟩ : syracuseStep 2019139 = 3028709) B3028709
theorem B5749829 : Blo 2017435 5749829 := bbase (se 4 (by rfl) ⟨539046, by rfl⟩ : syracuseStep 5749829 = 1078093) (by norm_num)
theorem B3833219 : Blo 2017435 3833219 := bstep (se 1 (by rfl) ⟨2874914, by rfl⟩ : syracuseStep 3833219 = 5749829) B5749829
theorem B2555479 : Blo 2017435 2555479 := bstep (se 1 (by rfl) ⟨1916609, by rfl⟩ : syracuseStep 2555479 = 3833219) B3833219
theorem B3407305 : Blo 2017435 3407305 := bstep (se 2 (by rfl) ⟨1277739, by rfl⟩ : syracuseStep 3407305 = 2555479) B2555479
theorem B4543073 : Blo 2017435 4543073 := bstep (se 2 (by rfl) ⟨1703652, by rfl⟩ : syracuseStep 4543073 = 3407305) B3407305
theorem B3028715 : Blo 2017435 3028715 := bstep (se 1 (by rfl) ⟨2271536, by rfl⟩ : syracuseStep 3028715 = 4543073) B4543073
theorem B2019143 : Blo 2017435 2019143 := bstep (se 1 (by rfl) ⟨1514357, by rfl⟩ : syracuseStep 2019143 = 3028715) B3028715
theorem B2271541 : Blo 2017435 2271541 := bbase (se 5 (by rfl) ⟨106478, by rfl⟩ : syracuseStep 2271541 = 212957) (by norm_num)
theorem B3028721 : Blo 2017435 3028721 := bstep (se 2 (by rfl) ⟨1135770, by rfl⟩ : syracuseStep 3028721 = 2271541) B2271541
theorem B2019147 : Blo 2017435 2019147 := bstep (se 1 (by rfl) ⟨1514360, by rfl⟩ : syracuseStep 2019147 = 3028721) B3028721
theorem B2555489 : Blo 2017435 2555489 := bbase (se 2 (by rfl) ⟨958308, by rfl⟩ : syracuseStep 2555489 = 1916617) (by norm_num)
theorem B6814637 : Blo 2017435 6814637 := bstep (se 3 (by rfl) ⟨1277744, by rfl⟩ : syracuseStep 6814637 = 2555489) B2555489
theorem B4543091 : Blo 2017435 4543091 := bstep (se 1 (by rfl) ⟨3407318, by rfl⟩ : syracuseStep 4543091 = 6814637) B6814637
theorem B3028727 : Blo 2017435 3028727 := bstep (se 1 (by rfl) ⟨2271545, by rfl⟩ : syracuseStep 3028727 = 4543091) B4543091
theorem B2019151 : Blo 2017435 2019151 := bstep (se 1 (by rfl) ⟨1514363, by rfl⟩ : syracuseStep 2019151 = 3028727) B3028727
theorem B3028733 : Blo 2017435 3028733 := bbase (se 3 (by rfl) ⟨567887, by rfl⟩ : syracuseStep 3028733 = 1135775) (by norm_num)
theorem B2019155 : Blo 2017435 2019155 := bstep (se 1 (by rfl) ⟨1514366, by rfl⟩ : syracuseStep 2019155 = 3028733) B3028733
theorem B4543109 : Blo 2017435 4543109 := bbase (se 4 (by rfl) ⟨425916, by rfl⟩ : syracuseStep 4543109 = 851833) (by norm_num)
theorem B3028739 : Blo 2017435 3028739 := bstep (se 1 (by rfl) ⟨2271554, by rfl⟩ : syracuseStep 3028739 = 4543109) B4543109
theorem B2019159 : Blo 2017435 2019159 := bstep (se 1 (by rfl) ⟨1514369, by rfl⟩ : syracuseStep 2019159 = 3028739) B3028739
theorem B2046713 : Blo 2017435 2046713 := bbase (se 2 (by rfl) ⟨767517, by rfl⟩ : syracuseStep 2046713 = 1535035) (by norm_num)
theorem B21831605 : Blo 2017435 21831605 := bstep (se 5 (by rfl) ⟨1023356, by rfl⟩ : syracuseStep 21831605 = 2046713) B2046713
theorem B14554403 : Blo 2017435 14554403 := bstep (se 1 (by rfl) ⟨10915802, by rfl⟩ : syracuseStep 14554403 = 21831605) B21831605
theorem B9702935 : Blo 2017435 9702935 := bstep (se 1 (by rfl) ⟨7277201, by rfl⟩ : syracuseStep 9702935 = 14554403) B14554403
theorem B6468623 : Blo 2017435 6468623 := bstep (se 1 (by rfl) ⟨4851467, by rfl⟩ : syracuseStep 6468623 = 9702935) B9702935
theorem B4312415 : Blo 2017435 4312415 := bstep (se 1 (by rfl) ⟨3234311, by rfl⟩ : syracuseStep 4312415 = 6468623) B6468623
theorem B2874943 : Blo 2017435 2874943 := bstep (se 1 (by rfl) ⟨2156207, by rfl⟩ : syracuseStep 2874943 = 4312415) B4312415
theorem B3833257 : Blo 2017435 3833257 := bstep (se 2 (by rfl) ⟨1437471, by rfl⟩ : syracuseStep 3833257 = 2874943) B2874943
theorem B5111009 : Blo 2017435 5111009 := bstep (se 2 (by rfl) ⟨1916628, by rfl⟩ : syracuseStep 5111009 = 3833257) B3833257
theorem B3407339 : Blo 2017435 3407339 := bstep (se 1 (by rfl) ⟨2555504, by rfl⟩ : syracuseStep 3407339 = 5111009) B5111009
theorem B2271559 : Blo 2017435 2271559 := bstep (se 1 (by rfl) ⟨1703669, by rfl⟩ : syracuseStep 2271559 = 3407339) B3407339
theorem B3028745 : Blo 2017435 3028745 := bstep (se 2 (by rfl) ⟨1135779, by rfl⟩ : syracuseStep 3028745 = 2271559) B2271559
theorem B2019163 : Blo 2017435 2019163 := bstep (se 1 (by rfl) ⟨1514372, by rfl⟩ : syracuseStep 2019163 = 3028745) B3028745
theorem B10222037 : Blo 2017435 10222037 := bbase (se 7 (by rfl) ⟨119789, by rfl⟩ : syracuseStep 10222037 = 239579) (by norm_num)
theorem B6814691 : Blo 2017435 6814691 := bstep (se 1 (by rfl) ⟨5111018, by rfl⟩ : syracuseStep 6814691 = 10222037) B10222037
theorem B4543127 : Blo 2017435 4543127 := bstep (se 1 (by rfl) ⟨3407345, by rfl⟩ : syracuseStep 4543127 = 6814691) B6814691
theorem B3028751 : Blo 2017435 3028751 := bstep (se 1 (by rfl) ⟨2271563, by rfl⟩ : syracuseStep 3028751 = 4543127) B4543127
theorem B2019167 : Blo 2017435 2019167 := bstep (se 1 (by rfl) ⟨1514375, by rfl⟩ : syracuseStep 2019167 = 3028751) B3028751
theorem B3028757 : Blo 2017435 3028757 := bbase (se 6 (by rfl) ⟨70986, by rfl⟩ : syracuseStep 3028757 = 141973) (by norm_num)
theorem B2019171 : Blo 2017435 2019171 := bstep (se 1 (by rfl) ⟨1514378, by rfl⟩ : syracuseStep 2019171 = 3028757) B3028757
theorem B85169621 : Blo 2017435 85169621 := bbase (se 7 (by rfl) ⟨998081, by rfl⟩ : syracuseStep 85169621 = 1996163) (by norm_num)
theorem B56779747 : Blo 2017435 56779747 := bstep (se 1 (by rfl) ⟨42584810, by rfl⟩ : syracuseStep 56779747 = 85169621) B85169621
theorem B302825317 : Blo 2017435 302825317 := bstep (se 4 (by rfl) ⟨28389873, by rfl⟩ : syracuseStep 302825317 = 56779747) B56779747
theorem B403767089 : Blo 2017435 403767089 := bstep (se 2 (by rfl) ⟨151412658, by rfl⟩ : syracuseStep 403767089 = 302825317) B302825317
theorem B269178059 : Blo 2017435 269178059 := bstep (se 1 (by rfl) ⟨201883544, by rfl⟩ : syracuseStep 269178059 = 403767089) B403767089
theorem B179452039 : Blo 2017435 179452039 := bstep (se 1 (by rfl) ⟨134589029, by rfl⟩ : syracuseStep 179452039 = 269178059) B269178059
theorem B239269385 : Blo 2017435 239269385 := bstep (se 2 (by rfl) ⟨89726019, by rfl⟩ : syracuseStep 239269385 = 179452039) B179452039
theorem B159512923 : Blo 2017435 159512923 := bstep (se 1 (by rfl) ⟨119634692, by rfl⟩ : syracuseStep 159512923 = 239269385) B239269385
theorem B212683897 : Blo 2017435 212683897 := bstep (se 2 (by rfl) ⟨79756461, by rfl⟩ : syracuseStep 212683897 = 159512923) B159512923
theorem B283578529 : Blo 2017435 283578529 := bstep (se 2 (by rfl) ⟨106341948, by rfl⟩ : syracuseStep 283578529 = 212683897) B212683897
theorem B378104705 : Blo 2017435 378104705 := bstep (se 2 (by rfl) ⟨141789264, by rfl⟩ : syracuseStep 378104705 = 283578529) B283578529
theorem B252069803 : Blo 2017435 252069803 := bstep (se 1 (by rfl) ⟨189052352, by rfl⟩ : syracuseStep 252069803 = 378104705) B378104705
theorem B168046535 : Blo 2017435 168046535 := bstep (se 1 (by rfl) ⟨126034901, by rfl⟩ : syracuseStep 168046535 = 252069803) B252069803
theorem B112031023 : Blo 2017435 112031023 := bstep (se 1 (by rfl) ⟨84023267, by rfl⟩ : syracuseStep 112031023 = 168046535) B168046535
theorem B149374697 : Blo 2017435 149374697 := bstep (se 2 (by rfl) ⟨56015511, by rfl⟩ : syracuseStep 149374697 = 112031023) B112031023
theorem B398332525 : Blo 2017435 398332525 := bstep (se 3 (by rfl) ⟨74687348, by rfl⟩ : syracuseStep 398332525 = 149374697) B149374697
theorem B531110033 : Blo 2017435 531110033 := bstep (se 2 (by rfl) ⟨199166262, by rfl⟩ : syracuseStep 531110033 = 398332525) B398332525
theorem B354073355 : Blo 2017435 354073355 := bstep (se 1 (by rfl) ⟨265555016, by rfl⟩ : syracuseStep 354073355 = 531110033) B531110033
theorem B236048903 : Blo 2017435 236048903 := bstep (se 1 (by rfl) ⟨177036677, by rfl⟩ : syracuseStep 236048903 = 354073355) B354073355
theorem B157365935 : Blo 2017435 157365935 := bstep (se 1 (by rfl) ⟨118024451, by rfl⟩ : syracuseStep 157365935 = 236048903) B236048903
theorem B104910623 : Blo 2017435 104910623 := bstep (se 1 (by rfl) ⟨78682967, by rfl⟩ : syracuseStep 104910623 = 157365935) B157365935
theorem B69940415 : Blo 2017435 69940415 := bstep (se 1 (by rfl) ⟨52455311, by rfl⟩ : syracuseStep 69940415 = 104910623) B104910623
theorem B46626943 : Blo 2017435 46626943 := bstep (se 1 (by rfl) ⟨34970207, by rfl⟩ : syracuseStep 46626943 = 69940415) B69940415
theorem B62169257 : Blo 2017435 62169257 := bstep (se 2 (by rfl) ⟨23313471, by rfl⟩ : syracuseStep 62169257 = 46626943) B46626943
theorem B41446171 : Blo 2017435 41446171 := bstep (se 1 (by rfl) ⟨31084628, by rfl⟩ : syracuseStep 41446171 = 62169257) B62169257
theorem B55261561 : Blo 2017435 55261561 := bstep (se 2 (by rfl) ⟨20723085, by rfl⟩ : syracuseStep 55261561 = 41446171) B41446171
theorem B73682081 : Blo 2017435 73682081 := bstep (se 2 (by rfl) ⟨27630780, by rfl⟩ : syracuseStep 73682081 = 55261561) B55261561
theorem B49121387 : Blo 2017435 49121387 := bstep (se 1 (by rfl) ⟨36841040, by rfl⟩ : syracuseStep 49121387 = 73682081) B73682081
theorem B32747591 : Blo 2017435 32747591 := bstep (se 1 (by rfl) ⟨24560693, by rfl⟩ : syracuseStep 32747591 = 49121387) B49121387
theorem B87326909 : Blo 2017435 87326909 := bstep (se 3 (by rfl) ⟨16373795, by rfl⟩ : syracuseStep 87326909 = 32747591) B32747591
theorem B58217939 : Blo 2017435 58217939 := bstep (se 1 (by rfl) ⟨43663454, by rfl⟩ : syracuseStep 58217939 = 87326909) B87326909
theorem B38811959 : Blo 2017435 38811959 := bstep (se 1 (by rfl) ⟨29108969, by rfl⟩ : syracuseStep 38811959 = 58217939) B58217939
theorem B25874639 : Blo 2017435 25874639 := bstep (se 1 (by rfl) ⟨19405979, by rfl⟩ : syracuseStep 25874639 = 38811959) B38811959
theorem B17249759 : Blo 2017435 17249759 := bstep (se 1 (by rfl) ⟨12937319, by rfl⟩ : syracuseStep 17249759 = 25874639) B25874639
theorem B11499839 : Blo 2017435 11499839 := bstep (se 1 (by rfl) ⟨8624879, by rfl⟩ : syracuseStep 11499839 = 17249759) B17249759
theorem B7666559 : Blo 2017435 7666559 := bstep (se 1 (by rfl) ⟨5749919, by rfl⟩ : syracuseStep 7666559 = 11499839) B11499839
theorem B5111039 : Blo 2017435 5111039 := bstep (se 1 (by rfl) ⟨3833279, by rfl⟩ : syracuseStep 5111039 = 7666559) B7666559
theorem B3407359 : Blo 2017435 3407359 := bstep (se 1 (by rfl) ⟨2555519, by rfl⟩ : syracuseStep 3407359 = 5111039) B5111039
theorem B4543145 : Blo 2017435 4543145 := bstep (se 2 (by rfl) ⟨1703679, by rfl⟩ : syracuseStep 4543145 = 3407359) B3407359
theorem B3028763 : Blo 2017435 3028763 := bstep (se 1 (by rfl) ⟨2271572, by rfl⟩ : syracuseStep 3028763 = 4543145) B4543145
theorem B2019175 : Blo 2017435 2019175 := bstep (se 1 (by rfl) ⟨1514381, by rfl⟩ : syracuseStep 2019175 = 3028763) B3028763
theorem B2271577 : Blo 2017435 2271577 := bbase (se 2 (by rfl) ⟨851841, by rfl⟩ : syracuseStep 2271577 = 1703683) (by norm_num)
theorem B3028769 : Blo 2017435 3028769 := bstep (se 2 (by rfl) ⟨1135788, by rfl⟩ : syracuseStep 3028769 = 2271577) B2271577
theorem B2019179 : Blo 2017435 2019179 := bstep (se 1 (by rfl) ⟨1514384, by rfl⟩ : syracuseStep 2019179 = 3028769) B3028769
theorem B8186933 : Blo 2017435 8186933 := bbase (se 5 (by rfl) ⟨383762, by rfl⟩ : syracuseStep 8186933 = 767525) (by norm_num)
theorem B5457955 : Blo 2017435 5457955 := bstep (se 1 (by rfl) ⟨4093466, by rfl⟩ : syracuseStep 5457955 = 8186933) B8186933
theorem B7277273 : Blo 2017435 7277273 := bstep (se 2 (by rfl) ⟨2728977, by rfl⟩ : syracuseStep 7277273 = 5457955) B5457955
theorem B4851515 : Blo 2017435 4851515 := bstep (se 1 (by rfl) ⟨3638636, by rfl⟩ : syracuseStep 4851515 = 7277273) B7277273
theorem B3234343 : Blo 2017435 3234343 := bstep (se 1 (by rfl) ⟨2425757, by rfl⟩ : syracuseStep 3234343 = 4851515) B4851515
theorem B4312457 : Blo 2017435 4312457 := bstep (se 2 (by rfl) ⟨1617171, by rfl⟩ : syracuseStep 4312457 = 3234343) B3234343
theorem B2874971 : Blo 2017435 2874971 := bstep (se 1 (by rfl) ⟨2156228, by rfl⟩ : syracuseStep 2874971 = 4312457) B4312457
theorem B7666589 : Blo 2017435 7666589 := bstep (se 3 (by rfl) ⟨1437485, by rfl⟩ : syracuseStep 7666589 = 2874971) B2874971
theorem B5111059 : Blo 2017435 5111059 := bstep (se 1 (by rfl) ⟨3833294, by rfl⟩ : syracuseStep 5111059 = 7666589) B7666589
theorem B6814745 : Blo 2017435 6814745 := bstep (se 2 (by rfl) ⟨2555529, by rfl⟩ : syracuseStep 6814745 = 5111059) B5111059
theorem B4543163 : Blo 2017435 4543163 := bstep (se 1 (by rfl) ⟨3407372, by rfl⟩ : syracuseStep 4543163 = 6814745) B6814745
theorem B3028775 : Blo 2017435 3028775 := bstep (se 1 (by rfl) ⟨2271581, by rfl⟩ : syracuseStep 3028775 = 4543163) B4543163
theorem B2019183 : Blo 2017435 2019183 := bstep (se 1 (by rfl) ⟨1514387, by rfl⟩ : syracuseStep 2019183 = 3028775) B3028775
theorem B3028781 : Blo 2017435 3028781 := bbase (se 3 (by rfl) ⟨567896, by rfl⟩ : syracuseStep 3028781 = 1135793) (by norm_num)
theorem B2019187 : Blo 2017435 2019187 := bstep (se 1 (by rfl) ⟨1514390, by rfl⟩ : syracuseStep 2019187 = 3028781) B3028781
theorem B4543181 : Blo 2017435 4543181 := bbase (se 3 (by rfl) ⟨851846, by rfl⟩ : syracuseStep 4543181 = 1703693) (by norm_num)
theorem B3028787 : Blo 2017435 3028787 := bstep (se 1 (by rfl) ⟨2271590, by rfl⟩ : syracuseStep 3028787 = 4543181) B4543181
theorem B2019191 : Blo 2017435 2019191 := bstep (se 1 (by rfl) ⟨1514393, by rfl⟩ : syracuseStep 2019191 = 3028787) B3028787
theorem B2555545 : Blo 2017435 2555545 := bbase (se 2 (by rfl) ⟨958329, by rfl⟩ : syracuseStep 2555545 = 1916659) (by norm_num)
theorem B3407393 : Blo 2017435 3407393 := bstep (se 2 (by rfl) ⟨1277772, by rfl⟩ : syracuseStep 3407393 = 2555545) B2555545
theorem B2271595 : Blo 2017435 2271595 := bstep (se 1 (by rfl) ⟨1703696, by rfl⟩ : syracuseStep 2271595 = 3407393) B3407393
theorem B3028793 : Blo 2017435 3028793 := bstep (se 2 (by rfl) ⟨1135797, by rfl⟩ : syracuseStep 3028793 = 2271595) B2271595
theorem B2019195 : Blo 2017435 2019195 := bstep (se 1 (by rfl) ⟨1514396, by rfl⟩ : syracuseStep 2019195 = 3028793) B3028793
theorem B8624981 : Blo 2017435 8624981 := bbase (se 9 (by rfl) ⟨25268, by rfl⟩ : syracuseStep 8624981 = 50537) (by norm_num)
theorem B22999949 : Blo 2017435 22999949 := bstep (se 3 (by rfl) ⟨4312490, by rfl⟩ : syracuseStep 22999949 = 8624981) B8624981
theorem B15333299 : Blo 2017435 15333299 := bstep (se 1 (by rfl) ⟨11499974, by rfl⟩ : syracuseStep 15333299 = 22999949) B22999949
theorem B10222199 : Blo 2017435 10222199 := bstep (se 1 (by rfl) ⟨7666649, by rfl⟩ : syracuseStep 10222199 = 15333299) B15333299
theorem B6814799 : Blo 2017435 6814799 := bstep (se 1 (by rfl) ⟨5111099, by rfl⟩ : syracuseStep 6814799 = 10222199) B10222199
theorem B4543199 : Blo 2017435 4543199 := bstep (se 1 (by rfl) ⟨3407399, by rfl⟩ : syracuseStep 4543199 = 6814799) B6814799
theorem B3028799 : Blo 2017435 3028799 := bstep (se 1 (by rfl) ⟨2271599, by rfl⟩ : syracuseStep 3028799 = 4543199) B4543199
theorem B2019199 : Blo 2017435 2019199 := bstep (se 1 (by rfl) ⟨1514399, by rfl⟩ : syracuseStep 2019199 = 3028799) B3028799
theorem B3028805 : Blo 2017435 3028805 := bbase (se 4 (by rfl) ⟨283950, by rfl⟩ : syracuseStep 3028805 = 567901) (by norm_num)
theorem B2019203 : Blo 2017435 2019203 := bstep (se 1 (by rfl) ⟨1514402, by rfl⟩ : syracuseStep 2019203 = 3028805) B3028805
theorem B3407413 : Blo 2017435 3407413 := bbase (se 5 (by rfl) ⟨159722, by rfl⟩ : syracuseStep 3407413 = 319445) (by norm_num)
theorem B4543217 : Blo 2017435 4543217 := bstep (se 2 (by rfl) ⟨1703706, by rfl⟩ : syracuseStep 4543217 = 3407413) B3407413
theorem B3028811 : Blo 2017435 3028811 := bstep (se 1 (by rfl) ⟨2271608, by rfl⟩ : syracuseStep 3028811 = 4543217) B4543217
theorem B2019207 : Blo 2017435 2019207 := bstep (se 1 (by rfl) ⟨1514405, by rfl⟩ : syracuseStep 2019207 = 3028811) B3028811
theorem B2271613 : Blo 2017435 2271613 := bbase (se 3 (by rfl) ⟨425927, by rfl⟩ : syracuseStep 2271613 = 851855) (by norm_num)
theorem B3028817 : Blo 2017435 3028817 := bstep (se 2 (by rfl) ⟨1135806, by rfl⟩ : syracuseStep 3028817 = 2271613) B2271613
theorem B2019211 : Blo 2017435 2019211 := bstep (se 1 (by rfl) ⟨1514408, by rfl⟩ : syracuseStep 2019211 = 3028817) B3028817
theorem B6814853 : Blo 2017435 6814853 := bbase (se 4 (by rfl) ⟨638892, by rfl⟩ : syracuseStep 6814853 = 1277785) (by norm_num)
theorem B4543235 : Blo 2017435 4543235 := bstep (se 1 (by rfl) ⟨3407426, by rfl⟩ : syracuseStep 4543235 = 6814853) B6814853
theorem B3028823 : Blo 2017435 3028823 := bstep (se 1 (by rfl) ⟨2271617, by rfl⟩ : syracuseStep 3028823 = 4543235) B4543235
theorem B2019215 : Blo 2017435 2019215 := bstep (se 1 (by rfl) ⟨1514411, by rfl⟩ : syracuseStep 2019215 = 3028823) B3028823
theorem B3028829 : Blo 2017435 3028829 := bbase (se 3 (by rfl) ⟨567905, by rfl⟩ : syracuseStep 3028829 = 1135811) (by norm_num)
theorem B2019219 : Blo 2017435 2019219 := bstep (se 1 (by rfl) ⟨1514414, by rfl⟩ : syracuseStep 2019219 = 3028829) B3028829
theorem B4543253 : Blo 2017435 4543253 := bbase (se 6 (by rfl) ⟨106482, by rfl⟩ : syracuseStep 4543253 = 212965) (by norm_num)
theorem B3028835 : Blo 2017435 3028835 := bstep (se 1 (by rfl) ⟨2271626, by rfl⟩ : syracuseStep 3028835 = 4543253) B4543253
theorem B2019223 : Blo 2017435 2019223 := bstep (se 1 (by rfl) ⟨1514417, by rfl⟩ : syracuseStep 2019223 = 3028835) B3028835
theorem B7666757 : Blo 2017435 7666757 := bbase (se 4 (by rfl) ⟨718758, by rfl⟩ : syracuseStep 7666757 = 1437517) (by norm_num)
theorem B5111171 : Blo 2017435 5111171 := bstep (se 1 (by rfl) ⟨3833378, by rfl⟩ : syracuseStep 5111171 = 7666757) B7666757
theorem B3407447 : Blo 2017435 3407447 := bstep (se 1 (by rfl) ⟨2555585, by rfl⟩ : syracuseStep 3407447 = 5111171) B5111171
theorem B2271631 : Blo 2017435 2271631 := bstep (se 1 (by rfl) ⟨1703723, by rfl⟩ : syracuseStep 2271631 = 3407447) B3407447
theorem B3028841 : Blo 2017435 3028841 := bstep (se 2 (by rfl) ⟨1135815, by rfl⟩ : syracuseStep 3028841 = 2271631) B2271631
theorem B2019227 : Blo 2017435 2019227 := bstep (se 1 (by rfl) ⟨1514420, by rfl⟩ : syracuseStep 2019227 = 3028841) B3028841
theorem B9336181 : Blo 2017435 9336181 := bbase (se 5 (by rfl) ⟨437633, by rfl⟩ : syracuseStep 9336181 = 875267) (by norm_num)
theorem B12448241 : Blo 2017435 12448241 := bstep (se 2 (by rfl) ⟨4668090, by rfl⟩ : syracuseStep 12448241 = 9336181) B9336181
theorem B8298827 : Blo 2017435 8298827 := bstep (se 1 (by rfl) ⟨6224120, by rfl⟩ : syracuseStep 8298827 = 12448241) B12448241
theorem B5532551 : Blo 2017435 5532551 := bstep (se 1 (by rfl) ⟨4149413, by rfl⟩ : syracuseStep 5532551 = 8298827) B8298827
theorem B3688367 : Blo 2017435 3688367 := bstep (se 1 (by rfl) ⟨2766275, by rfl⟩ : syracuseStep 3688367 = 5532551) B5532551
theorem B39342581 : Blo 2017435 39342581 := bstep (se 5 (by rfl) ⟨1844183, by rfl⟩ : syracuseStep 39342581 = 3688367) B3688367
theorem B26228387 : Blo 2017435 26228387 := bstep (se 1 (by rfl) ⟨19671290, by rfl⟩ : syracuseStep 26228387 = 39342581) B39342581
theorem B69942365 : Blo 2017435 69942365 := bstep (se 3 (by rfl) ⟨13114193, by rfl⟩ : syracuseStep 69942365 = 26228387) B26228387
theorem B46628243 : Blo 2017435 46628243 := bstep (se 1 (by rfl) ⟨34971182, by rfl⟩ : syracuseStep 46628243 = 69942365) B69942365
theorem B31085495 : Blo 2017435 31085495 := bstep (se 1 (by rfl) ⟨23314121, by rfl⟩ : syracuseStep 31085495 = 46628243) B46628243
theorem B20723663 : Blo 2017435 20723663 := bstep (se 1 (by rfl) ⟨15542747, by rfl⟩ : syracuseStep 20723663 = 31085495) B31085495
theorem B13815775 : Blo 2017435 13815775 := bstep (se 1 (by rfl) ⟨10361831, by rfl⟩ : syracuseStep 13815775 = 20723663) B20723663
theorem B18421033 : Blo 2017435 18421033 := bstep (se 2 (by rfl) ⟨6907887, by rfl⟩ : syracuseStep 18421033 = 13815775) B13815775
theorem B24561377 : Blo 2017435 24561377 := bstep (se 2 (by rfl) ⟨9210516, by rfl⟩ : syracuseStep 24561377 = 18421033) B18421033
theorem B16374251 : Blo 2017435 16374251 := bstep (se 1 (by rfl) ⟨12280688, by rfl⟩ : syracuseStep 16374251 = 24561377) B24561377
theorem B10916167 : Blo 2017435 10916167 := bstep (se 1 (by rfl) ⟨8187125, by rfl⟩ : syracuseStep 10916167 = 16374251) B16374251
theorem B14554889 : Blo 2017435 14554889 := bstep (se 2 (by rfl) ⟨5458083, by rfl⟩ : syracuseStep 14554889 = 10916167) B10916167
theorem B9703259 : Blo 2017435 9703259 := bstep (se 1 (by rfl) ⟨7277444, by rfl⟩ : syracuseStep 9703259 = 14554889) B14554889
theorem B6468839 : Blo 2017435 6468839 := bstep (se 1 (by rfl) ⟨4851629, by rfl⟩ : syracuseStep 6468839 = 9703259) B9703259
theorem B4312559 : Blo 2017435 4312559 := bstep (se 1 (by rfl) ⟨3234419, by rfl⟩ : syracuseStep 4312559 = 6468839) B6468839
theorem B11500157 : Blo 2017435 11500157 := bstep (se 3 (by rfl) ⟨2156279, by rfl⟩ : syracuseStep 11500157 = 4312559) B4312559
theorem B7666771 : Blo 2017435 7666771 := bstep (se 1 (by rfl) ⟨5750078, by rfl⟩ : syracuseStep 7666771 = 11500157) B11500157
theorem B10222361 : Blo 2017435 10222361 := bstep (se 2 (by rfl) ⟨3833385, by rfl⟩ : syracuseStep 10222361 = 7666771) B7666771
theorem B6814907 : Blo 2017435 6814907 := bstep (se 1 (by rfl) ⟨5111180, by rfl⟩ : syracuseStep 6814907 = 10222361) B10222361
theorem B4543271 : Blo 2017435 4543271 := bstep (se 1 (by rfl) ⟨3407453, by rfl⟩ : syracuseStep 4543271 = 6814907) B6814907
theorem B3028847 : Blo 2017435 3028847 := bstep (se 1 (by rfl) ⟨2271635, by rfl⟩ : syracuseStep 3028847 = 4543271) B4543271
theorem B2019231 : Blo 2017435 2019231 := bstep (se 1 (by rfl) ⟨1514423, by rfl⟩ : syracuseStep 2019231 = 3028847) B3028847
theorem B3028853 : Blo 2017435 3028853 := bbase (se 5 (by rfl) ⟨141977, by rfl⟩ : syracuseStep 3028853 = 283955) (by norm_num)
theorem B2019235 : Blo 2017435 2019235 := bstep (se 1 (by rfl) ⟨1514426, by rfl⟩ : syracuseStep 2019235 = 3028853) B3028853
theorem B2425825 : Blo 2017435 2425825 := bbase (se 2 (by rfl) ⟨909684, by rfl⟩ : syracuseStep 2425825 = 1819369) (by norm_num)
theorem B3234433 : Blo 2017435 3234433 := bstep (se 2 (by rfl) ⟨1212912, by rfl⟩ : syracuseStep 3234433 = 2425825) B2425825
theorem B4312577 : Blo 2017435 4312577 := bstep (se 2 (by rfl) ⟨1617216, by rfl⟩ : syracuseStep 4312577 = 3234433) B3234433
theorem B2875051 : Blo 2017435 2875051 := bstep (se 1 (by rfl) ⟨2156288, by rfl⟩ : syracuseStep 2875051 = 4312577) B4312577
theorem B3833401 : Blo 2017435 3833401 := bstep (se 2 (by rfl) ⟨1437525, by rfl⟩ : syracuseStep 3833401 = 2875051) B2875051
theorem B5111201 : Blo 2017435 5111201 := bstep (se 2 (by rfl) ⟨1916700, by rfl⟩ : syracuseStep 5111201 = 3833401) B3833401
theorem B3407467 : Blo 2017435 3407467 := bstep (se 1 (by rfl) ⟨2555600, by rfl⟩ : syracuseStep 3407467 = 5111201) B5111201
theorem B4543289 : Blo 2017435 4543289 := bstep (se 2 (by rfl) ⟨1703733, by rfl⟩ : syracuseStep 4543289 = 3407467) B3407467
theorem B3028859 : Blo 2017435 3028859 := bstep (se 1 (by rfl) ⟨2271644, by rfl⟩ : syracuseStep 3028859 = 4543289) B4543289
theorem B2019239 : Blo 2017435 2019239 := bstep (se 1 (by rfl) ⟨1514429, by rfl⟩ : syracuseStep 2019239 = 3028859) B3028859
theorem B2271649 : Blo 2017435 2271649 := bbase (se 2 (by rfl) ⟨851868, by rfl⟩ : syracuseStep 2271649 = 1703737) (by norm_num)
theorem B3028865 : Blo 2017435 3028865 := bstep (se 2 (by rfl) ⟨1135824, by rfl⟩ : syracuseStep 3028865 = 2271649) B2271649
theorem B2019243 : Blo 2017435 2019243 := bstep (se 1 (by rfl) ⟨1514432, by rfl⟩ : syracuseStep 2019243 = 3028865) B3028865
theorem B5111221 : Blo 2017435 5111221 := bbase (se 5 (by rfl) ⟨239588, by rfl⟩ : syracuseStep 5111221 = 479177) (by norm_num)
theorem B6814961 : Blo 2017435 6814961 := bstep (se 2 (by rfl) ⟨2555610, by rfl⟩ : syracuseStep 6814961 = 5111221) B5111221
theorem B4543307 : Blo 2017435 4543307 := bstep (se 1 (by rfl) ⟨3407480, by rfl⟩ : syracuseStep 4543307 = 6814961) B6814961
theorem B3028871 : Blo 2017435 3028871 := bstep (se 1 (by rfl) ⟨2271653, by rfl⟩ : syracuseStep 3028871 = 4543307) B4543307
theorem B2019247 : Blo 2017435 2019247 := bstep (se 1 (by rfl) ⟨1514435, by rfl⟩ : syracuseStep 2019247 = 3028871) B3028871
theorem B3028877 : Blo 2017435 3028877 := bbase (se 3 (by rfl) ⟨567914, by rfl⟩ : syracuseStep 3028877 = 1135829) (by norm_num)
theorem B2019251 : Blo 2017435 2019251 := bstep (se 1 (by rfl) ⟨1514438, by rfl⟩ : syracuseStep 2019251 = 3028877) B3028877
theorem B4543325 : Blo 2017435 4543325 := bbase (se 3 (by rfl) ⟨851873, by rfl⟩ : syracuseStep 4543325 = 1703747) (by norm_num)
theorem B3028883 : Blo 2017435 3028883 := bstep (se 1 (by rfl) ⟨2271662, by rfl⟩ : syracuseStep 3028883 = 4543325) B4543325
theorem B2019255 : Blo 2017435 2019255 := bstep (se 1 (by rfl) ⟨1514441, by rfl⟩ : syracuseStep 2019255 = 3028883) B3028883
theorem B3407501 : Blo 2017435 3407501 := bbase (se 3 (by rfl) ⟨638906, by rfl⟩ : syracuseStep 3407501 = 1277813) (by norm_num)
theorem B2271667 : Blo 2017435 2271667 := bstep (se 1 (by rfl) ⟨1703750, by rfl⟩ : syracuseStep 2271667 = 3407501) B3407501
theorem B3028889 : Blo 2017435 3028889 := bstep (se 2 (by rfl) ⟨1135833, by rfl⟩ : syracuseStep 3028889 = 2271667) B2271667
theorem B2019259 : Blo 2017435 2019259 := bstep (se 1 (by rfl) ⟨1514444, by rfl⟩ : syracuseStep 2019259 = 3028889) B3028889
theorem B2425853 : Blo 2017435 2425853 := bbase (se 3 (by rfl) ⟨454847, by rfl⟩ : syracuseStep 2425853 = 909695) (by norm_num)
theorem B6468941 : Blo 2017435 6468941 := bstep (se 3 (by rfl) ⟨1212926, by rfl⟩ : syracuseStep 6468941 = 2425853) B2425853
theorem B17250509 : Blo 2017435 17250509 := bstep (se 3 (by rfl) ⟨3234470, by rfl⟩ : syracuseStep 17250509 = 6468941) B6468941
theorem B11500339 : Blo 2017435 11500339 := bstep (se 1 (by rfl) ⟨8625254, by rfl⟩ : syracuseStep 11500339 = 17250509) B17250509
theorem B15333785 : Blo 2017435 15333785 := bstep (se 2 (by rfl) ⟨5750169, by rfl⟩ : syracuseStep 15333785 = 11500339) B11500339
theorem B10222523 : Blo 2017435 10222523 := bstep (se 1 (by rfl) ⟨7666892, by rfl⟩ : syracuseStep 10222523 = 15333785) B15333785
theorem B6815015 : Blo 2017435 6815015 := bstep (se 1 (by rfl) ⟨5111261, by rfl⟩ : syracuseStep 6815015 = 10222523) B10222523
theorem B4543343 : Blo 2017435 4543343 := bstep (se 1 (by rfl) ⟨3407507, by rfl⟩ : syracuseStep 4543343 = 6815015) B6815015
theorem B3028895 : Blo 2017435 3028895 := bstep (se 1 (by rfl) ⟨2271671, by rfl⟩ : syracuseStep 3028895 = 4543343) B4543343
theorem B2019263 : Blo 2017435 2019263 := bstep (se 1 (by rfl) ⟨1514447, by rfl⟩ : syracuseStep 2019263 = 3028895) B3028895
theorem B3028901 : Blo 2017435 3028901 := bbase (se 4 (by rfl) ⟨283959, by rfl⟩ : syracuseStep 3028901 = 567919) (by norm_num)
theorem B2019267 : Blo 2017435 2019267 := bstep (se 1 (by rfl) ⟨1514450, by rfl⟩ : syracuseStep 2019267 = 3028901) B3028901
theorem B2555641 : Blo 2017435 2555641 := bbase (se 2 (by rfl) ⟨958365, by rfl⟩ : syracuseStep 2555641 = 1916731) (by norm_num)
theorem B3407521 : Blo 2017435 3407521 := bstep (se 2 (by rfl) ⟨1277820, by rfl⟩ : syracuseStep 3407521 = 2555641) B2555641
theorem B4543361 : Blo 2017435 4543361 := bstep (se 2 (by rfl) ⟨1703760, by rfl⟩ : syracuseStep 4543361 = 3407521) B3407521
theorem B3028907 : Blo 2017435 3028907 := bstep (se 1 (by rfl) ⟨2271680, by rfl⟩ : syracuseStep 3028907 = 4543361) B4543361
theorem B2019271 : Blo 2017435 2019271 := bstep (se 1 (by rfl) ⟨1514453, by rfl⟩ : syracuseStep 2019271 = 3028907) B3028907
theorem B2271685 : Blo 2017435 2271685 := bbase (se 4 (by rfl) ⟨212970, by rfl⟩ : syracuseStep 2271685 = 425941) (by norm_num)
theorem B3028913 : Blo 2017435 3028913 := bstep (se 2 (by rfl) ⟨1135842, by rfl⟩ : syracuseStep 3028913 = 2271685) B2271685
theorem B2019275 : Blo 2017435 2019275 := bstep (se 1 (by rfl) ⟨1514456, by rfl⟩ : syracuseStep 2019275 = 3028913) B3028913
theorem B3833477 : Blo 2017435 3833477 := bbase (se 4 (by rfl) ⟨359388, by rfl⟩ : syracuseStep 3833477 = 718777) (by norm_num)
theorem B2555651 : Blo 2017435 2555651 := bstep (se 1 (by rfl) ⟨1916738, by rfl⟩ : syracuseStep 2555651 = 3833477) B3833477
theorem B6815069 : Blo 2017435 6815069 := bstep (se 3 (by rfl) ⟨1277825, by rfl⟩ : syracuseStep 6815069 = 2555651) B2555651
theorem B4543379 : Blo 2017435 4543379 := bstep (se 1 (by rfl) ⟨3407534, by rfl⟩ : syracuseStep 4543379 = 6815069) B6815069
theorem B3028919 : Blo 2017435 3028919 := bstep (se 1 (by rfl) ⟨2271689, by rfl⟩ : syracuseStep 3028919 = 4543379) B4543379
theorem B2019279 : Blo 2017435 2019279 := bstep (se 1 (by rfl) ⟨1514459, by rfl⟩ : syracuseStep 2019279 = 3028919) B3028919
theorem B3028925 : Blo 2017435 3028925 := bbase (se 3 (by rfl) ⟨567923, by rfl⟩ : syracuseStep 3028925 = 1135847) (by norm_num)
theorem B2019283 : Blo 2017435 2019283 := bstep (se 1 (by rfl) ⟨1514462, by rfl⟩ : syracuseStep 2019283 = 3028925) B3028925
theorem B4543397 : Blo 2017435 4543397 := bbase (se 4 (by rfl) ⟨425943, by rfl⟩ : syracuseStep 4543397 = 851887) (by norm_num)
theorem B3028931 : Blo 2017435 3028931 := bstep (se 1 (by rfl) ⟨2271698, by rfl⟩ : syracuseStep 3028931 = 4543397) B4543397
theorem B2019287 : Blo 2017435 2019287 := bstep (se 1 (by rfl) ⟨1514465, by rfl⟩ : syracuseStep 2019287 = 3028931) B3028931
theorem B5111333 : Blo 2017435 5111333 := bbase (se 4 (by rfl) ⟨479187, by rfl⟩ : syracuseStep 5111333 = 958375) (by norm_num)
theorem B3407555 : Blo 2017435 3407555 := bstep (se 1 (by rfl) ⟨2555666, by rfl⟩ : syracuseStep 3407555 = 5111333) B5111333
theorem B2271703 : Blo 2017435 2271703 := bstep (se 1 (by rfl) ⟨1703777, by rfl⟩ : syracuseStep 2271703 = 3407555) B3407555
theorem B3028937 : Blo 2017435 3028937 := bstep (se 2 (by rfl) ⟨1135851, by rfl⟩ : syracuseStep 3028937 = 2271703) B2271703
theorem B2019291 : Blo 2017435 2019291 := bstep (se 1 (by rfl) ⟨1514468, by rfl⟩ : syracuseStep 2019291 = 3028937) B3028937
theorem B5750261 : Blo 2017435 5750261 := bbase (se 5 (by rfl) ⟨269543, by rfl⟩ : syracuseStep 5750261 = 539087) (by norm_num)
theorem B3833507 : Blo 2017435 3833507 := bstep (se 1 (by rfl) ⟨2875130, by rfl⟩ : syracuseStep 3833507 = 5750261) B5750261
theorem B10222685 : Blo 2017435 10222685 := bstep (se 3 (by rfl) ⟨1916753, by rfl⟩ : syracuseStep 10222685 = 3833507) B3833507
theorem B6815123 : Blo 2017435 6815123 := bstep (se 1 (by rfl) ⟨5111342, by rfl⟩ : syracuseStep 6815123 = 10222685) B10222685
theorem B4543415 : Blo 2017435 4543415 := bstep (se 1 (by rfl) ⟨3407561, by rfl⟩ : syracuseStep 4543415 = 6815123) B6815123
theorem B3028943 : Blo 2017435 3028943 := bstep (se 1 (by rfl) ⟨2271707, by rfl⟩ : syracuseStep 3028943 = 4543415) B4543415
theorem B2019295 : Blo 2017435 2019295 := bstep (se 1 (by rfl) ⟨1514471, by rfl⟩ : syracuseStep 2019295 = 3028943) B3028943
theorem B3028949 : Blo 2017435 3028949 := bbase (se 7 (by rfl) ⟨35495, by rfl⟩ : syracuseStep 3028949 = 70991) (by norm_num)
theorem B2019299 : Blo 2017435 2019299 := bstep (se 1 (by rfl) ⟨1514474, by rfl⟩ : syracuseStep 2019299 = 3028949) B3028949
theorem B7667045 : Blo 2017435 7667045 := bbase (se 4 (by rfl) ⟨718785, by rfl⟩ : syracuseStep 7667045 = 1437571) (by norm_num)
theorem B5111363 : Blo 2017435 5111363 := bstep (se 1 (by rfl) ⟨3833522, by rfl⟩ : syracuseStep 5111363 = 7667045) B7667045
theorem B3407575 : Blo 2017435 3407575 := bstep (se 1 (by rfl) ⟨2555681, by rfl⟩ : syracuseStep 3407575 = 5111363) B5111363
theorem B4543433 : Blo 2017435 4543433 := bstep (se 2 (by rfl) ⟨1703787, by rfl⟩ : syracuseStep 4543433 = 3407575) B3407575
theorem B3028955 : Blo 2017435 3028955 := bstep (se 1 (by rfl) ⟨2271716, by rfl⟩ : syracuseStep 3028955 = 4543433) B4543433
theorem B2019303 : Blo 2017435 2019303 := bstep (se 1 (by rfl) ⟨1514477, by rfl⟩ : syracuseStep 2019303 = 3028955) B3028955
theorem B2271721 : Blo 2017435 2271721 := bbase (se 2 (by rfl) ⟨851895, by rfl⟩ : syracuseStep 2271721 = 1703791) (by norm_num)
theorem B3028961 : Blo 2017435 3028961 := bstep (se 2 (by rfl) ⟨1135860, by rfl⟩ : syracuseStep 3028961 = 2271721) B2271721
theorem B2019307 : Blo 2017435 2019307 := bstep (se 1 (by rfl) ⟨1514480, by rfl⟩ : syracuseStep 2019307 = 3028961) B3028961
theorem B2156365 : Blo 2017435 2156365 := bbase (se 3 (by rfl) ⟨404318, by rfl⟩ : syracuseStep 2156365 = 808637) (by norm_num)
theorem B11500613 : Blo 2017435 11500613 := bstep (se 4 (by rfl) ⟨1078182, by rfl⟩ : syracuseStep 11500613 = 2156365) B2156365
theorem B7667075 : Blo 2017435 7667075 := bstep (se 1 (by rfl) ⟨5750306, by rfl⟩ : syracuseStep 7667075 = 11500613) B11500613
theorem B5111383 : Blo 2017435 5111383 := bstep (se 1 (by rfl) ⟨3833537, by rfl⟩ : syracuseStep 5111383 = 7667075) B7667075
theorem B6815177 : Blo 2017435 6815177 := bstep (se 2 (by rfl) ⟨2555691, by rfl⟩ : syracuseStep 6815177 = 5111383) B5111383
theorem B4543451 : Blo 2017435 4543451 := bstep (se 1 (by rfl) ⟨3407588, by rfl⟩ : syracuseStep 4543451 = 6815177) B6815177
theorem B3028967 : Blo 2017435 3028967 := bstep (se 1 (by rfl) ⟨2271725, by rfl⟩ : syracuseStep 3028967 = 4543451) B4543451
theorem B2019311 : Blo 2017435 2019311 := bstep (se 1 (by rfl) ⟨1514483, by rfl⟩ : syracuseStep 2019311 = 3028967) B3028967
theorem B3028973 : Blo 2017435 3028973 := bbase (se 3 (by rfl) ⟨567932, by rfl⟩ : syracuseStep 3028973 = 1135865) (by norm_num)
theorem B2019315 : Blo 2017435 2019315 := bstep (se 1 (by rfl) ⟨1514486, by rfl⟩ : syracuseStep 2019315 = 3028973) B3028973
theorem B4543469 : Blo 2017435 4543469 := bbase (se 3 (by rfl) ⟨851900, by rfl⟩ : syracuseStep 4543469 = 1703801) (by norm_num)
theorem B3028979 : Blo 2017435 3028979 := bstep (se 1 (by rfl) ⟨2271734, by rfl⟩ : syracuseStep 3028979 = 4543469) B4543469
theorem B2019319 : Blo 2017435 2019319 := bstep (se 1 (by rfl) ⟨1514489, by rfl⟩ : syracuseStep 2019319 = 3028979) B3028979
theorem B4312757 : Blo 2017435 4312757 := bbase (se 5 (by rfl) ⟨202160, by rfl⟩ : syracuseStep 4312757 = 404321) (by norm_num)
theorem B2875171 : Blo 2017435 2875171 := bstep (se 1 (by rfl) ⟨2156378, by rfl⟩ : syracuseStep 2875171 = 4312757) B4312757
theorem B3833561 : Blo 2017435 3833561 := bstep (se 2 (by rfl) ⟨1437585, by rfl⟩ : syracuseStep 3833561 = 2875171) B2875171
theorem B2555707 : Blo 2017435 2555707 := bstep (se 1 (by rfl) ⟨1916780, by rfl⟩ : syracuseStep 2555707 = 3833561) B3833561
theorem B3407609 : Blo 2017435 3407609 := bstep (se 2 (by rfl) ⟨1277853, by rfl⟩ : syracuseStep 3407609 = 2555707) B2555707
theorem B2271739 : Blo 2017435 2271739 := bstep (se 1 (by rfl) ⟨1703804, by rfl⟩ : syracuseStep 2271739 = 3407609) B3407609
theorem B3028985 : Blo 2017435 3028985 := bstep (se 2 (by rfl) ⟨1135869, by rfl⟩ : syracuseStep 3028985 = 2271739) B2271739
theorem B2019323 : Blo 2017435 2019323 := bstep (se 1 (by rfl) ⟨1514492, by rfl⟩ : syracuseStep 2019323 = 3028985) B3028985
theorem B2245853 : Blo 2017435 2245853 := bbase (se 3 (by rfl) ⟨421097, by rfl⟩ : syracuseStep 2245853 = 842195) (by norm_num)
theorem B5988941 : Blo 2017435 5988941 := bstep (se 3 (by rfl) ⟨1122926, by rfl⟩ : syracuseStep 5988941 = 2245853) B2245853
theorem B3992627 : Blo 2017435 3992627 := bstep (se 1 (by rfl) ⟨2994470, by rfl⟩ : syracuseStep 3992627 = 5988941) B5988941
theorem B2661751 : Blo 2017435 2661751 := bstep (se 1 (by rfl) ⟨1996313, by rfl⟩ : syracuseStep 2661751 = 3992627) B3992627
theorem B14196005 : Blo 2017435 14196005 := bstep (se 4 (by rfl) ⟨1330875, by rfl⟩ : syracuseStep 14196005 = 2661751) B2661751
theorem B9464003 : Blo 2017435 9464003 := bstep (se 1 (by rfl) ⟨7098002, by rfl⟩ : syracuseStep 9464003 = 14196005) B14196005
theorem B6309335 : Blo 2017435 6309335 := bstep (se 1 (by rfl) ⟨4732001, by rfl⟩ : syracuseStep 6309335 = 9464003) B9464003
theorem B16824893 : Blo 2017435 16824893 := bstep (se 3 (by rfl) ⟨3154667, by rfl⟩ : syracuseStep 16824893 = 6309335) B6309335
theorem B44866381 : Blo 2017435 44866381 := bstep (se 3 (by rfl) ⟨8412446, by rfl⟩ : syracuseStep 44866381 = 16824893) B16824893
theorem B59821841 : Blo 2017435 59821841 := bstep (se 2 (by rfl) ⟨22433190, by rfl⟩ : syracuseStep 59821841 = 44866381) B44866381
theorem B39881227 : Blo 2017435 39881227 := bstep (se 1 (by rfl) ⟨29910920, by rfl⟩ : syracuseStep 39881227 = 59821841) B59821841
theorem B53174969 : Blo 2017435 53174969 := bstep (se 2 (by rfl) ⟨19940613, by rfl⟩ : syracuseStep 53174969 = 39881227) B39881227
theorem B35449979 : Blo 2017435 35449979 := bstep (se 1 (by rfl) ⟨26587484, by rfl⟩ : syracuseStep 35449979 = 53174969) B53174969
theorem B94533277 : Blo 2017435 94533277 := bstep (se 3 (by rfl) ⟨17724989, by rfl⟩ : syracuseStep 94533277 = 35449979) B35449979
theorem B126044369 : Blo 2017435 126044369 := bstep (se 2 (by rfl) ⟨47266638, by rfl⟩ : syracuseStep 126044369 = 94533277) B94533277
theorem B84029579 : Blo 2017435 84029579 := bstep (se 1 (by rfl) ⟨63022184, by rfl⟩ : syracuseStep 84029579 = 126044369) B126044369
theorem B56019719 : Blo 2017435 56019719 := bstep (se 1 (by rfl) ⟨42014789, by rfl⟩ : syracuseStep 56019719 = 84029579) B84029579
theorem B149385917 : Blo 2017435 149385917 := bstep (se 3 (by rfl) ⟨28009859, by rfl⟩ : syracuseStep 149385917 = 56019719) B56019719
theorem B398362445 : Blo 2017435 398362445 := bstep (se 3 (by rfl) ⟨74692958, by rfl⟩ : syracuseStep 398362445 = 149385917) B149385917
theorem B265574963 : Blo 2017435 265574963 := bstep (se 1 (by rfl) ⟨199181222, by rfl⟩ : syracuseStep 265574963 = 398362445) B398362445
theorem B177049975 : Blo 2017435 177049975 := bstep (se 1 (by rfl) ⟨132787481, by rfl⟩ : syracuseStep 177049975 = 265574963) B265574963
theorem B236066633 : Blo 2017435 236066633 := bstep (se 2 (by rfl) ⟨88524987, by rfl⟩ : syracuseStep 236066633 = 177049975) B177049975
theorem B157377755 : Blo 2017435 157377755 := bstep (se 1 (by rfl) ⟨118033316, by rfl⟩ : syracuseStep 157377755 = 236066633) B236066633
theorem B104918503 : Blo 2017435 104918503 := bstep (se 1 (by rfl) ⟨78688877, by rfl⟩ : syracuseStep 104918503 = 157377755) B157377755
theorem B139891337 : Blo 2017435 139891337 := bstep (se 2 (by rfl) ⟨52459251, by rfl⟩ : syracuseStep 139891337 = 104918503) B104918503
theorem B93260891 : Blo 2017435 93260891 := bstep (se 1 (by rfl) ⟨69945668, by rfl⟩ : syracuseStep 93260891 = 139891337) B139891337
theorem B62173927 : Blo 2017435 62173927 := bstep (se 1 (by rfl) ⟨46630445, by rfl⟩ : syracuseStep 62173927 = 93260891) B93260891
theorem B82898569 : Blo 2017435 82898569 := bstep (se 2 (by rfl) ⟨31086963, by rfl⟩ : syracuseStep 82898569 = 62173927) B62173927
theorem B110531425 : Blo 2017435 110531425 := bstep (se 2 (by rfl) ⟨41449284, by rfl⟩ : syracuseStep 110531425 = 82898569) B82898569
theorem B147375233 : Blo 2017435 147375233 := bstep (se 2 (by rfl) ⟨55265712, by rfl⟩ : syracuseStep 147375233 = 110531425) B110531425
theorem B98250155 : Blo 2017435 98250155 := bstep (se 1 (by rfl) ⟨73687616, by rfl⟩ : syracuseStep 98250155 = 147375233) B147375233
theorem B65500103 : Blo 2017435 65500103 := bstep (se 1 (by rfl) ⟨49125077, by rfl⟩ : syracuseStep 65500103 = 98250155) B98250155
theorem B174666941 : Blo 2017435 174666941 := bstep (se 3 (by rfl) ⟨32750051, by rfl⟩ : syracuseStep 174666941 = 65500103) B65500103
theorem B116444627 : Blo 2017435 116444627 := bstep (se 1 (by rfl) ⟨87333470, by rfl⟩ : syracuseStep 116444627 = 174666941) B174666941
theorem B77629751 : Blo 2017435 77629751 := bstep (se 1 (by rfl) ⟨58222313, by rfl⟩ : syracuseStep 77629751 = 116444627) B116444627
theorem B51753167 : Blo 2017435 51753167 := bstep (se 1 (by rfl) ⟨38814875, by rfl⟩ : syracuseStep 51753167 = 77629751) B77629751
theorem B34502111 : Blo 2017435 34502111 := bstep (se 1 (by rfl) ⟨25876583, by rfl⟩ : syracuseStep 34502111 = 51753167) B51753167
theorem B23001407 : Blo 2017435 23001407 := bstep (se 1 (by rfl) ⟨17251055, by rfl⟩ : syracuseStep 23001407 = 34502111) B34502111
theorem B15334271 : Blo 2017435 15334271 := bstep (se 1 (by rfl) ⟨11500703, by rfl⟩ : syracuseStep 15334271 = 23001407) B23001407
theorem B10222847 : Blo 2017435 10222847 := bstep (se 1 (by rfl) ⟨7667135, by rfl⟩ : syracuseStep 10222847 = 15334271) B15334271
theorem B6815231 : Blo 2017435 6815231 := bstep (se 1 (by rfl) ⟨5111423, by rfl⟩ : syracuseStep 6815231 = 10222847) B10222847
theorem B4543487 : Blo 2017435 4543487 := bstep (se 1 (by rfl) ⟨3407615, by rfl⟩ : syracuseStep 4543487 = 6815231) B6815231
theorem B3028991 : Blo 2017435 3028991 := bstep (se 1 (by rfl) ⟨2271743, by rfl⟩ : syracuseStep 3028991 = 4543487) B4543487
theorem B2019327 : Blo 2017435 2019327 := bstep (se 1 (by rfl) ⟨1514495, by rfl⟩ : syracuseStep 2019327 = 3028991) B3028991
theorem B3028997 : Blo 2017435 3028997 := bbase (se 4 (by rfl) ⟨283968, by rfl⟩ : syracuseStep 3028997 = 567937) (by norm_num)
theorem B2019331 : Blo 2017435 2019331 := bstep (se 1 (by rfl) ⟨1514498, by rfl⟩ : syracuseStep 2019331 = 3028997) B3028997
theorem B3407629 : Blo 2017435 3407629 := bbase (se 3 (by rfl) ⟨638930, by rfl⟩ : syracuseStep 3407629 = 1277861) (by norm_num)
theorem B4543505 : Blo 2017435 4543505 := bstep (se 2 (by rfl) ⟨1703814, by rfl⟩ : syracuseStep 4543505 = 3407629) B3407629
theorem B3029003 : Blo 2017435 3029003 := bstep (se 1 (by rfl) ⟨2271752, by rfl⟩ : syracuseStep 3029003 = 4543505) B4543505
theorem B2019335 : Blo 2017435 2019335 := bstep (se 1 (by rfl) ⟨1514501, by rfl⟩ : syracuseStep 2019335 = 3029003) B3029003
theorem B2271757 : Blo 2017435 2271757 := bbase (se 3 (by rfl) ⟨425954, by rfl⟩ : syracuseStep 2271757 = 851909) (by norm_num)
theorem B3029009 : Blo 2017435 3029009 := bstep (se 2 (by rfl) ⟨1135878, by rfl⟩ : syracuseStep 3029009 = 2271757) B2271757
theorem B2019339 : Blo 2017435 2019339 := bstep (se 1 (by rfl) ⟨1514504, by rfl⟩ : syracuseStep 2019339 = 3029009) B3029009
theorem B6815285 : Blo 2017435 6815285 := bbase (se 5 (by rfl) ⟨319466, by rfl⟩ : syracuseStep 6815285 = 638933) (by norm_num)
theorem B4543523 : Blo 2017435 4543523 := bstep (se 1 (by rfl) ⟨3407642, by rfl⟩ : syracuseStep 4543523 = 6815285) B6815285
theorem B3029015 : Blo 2017435 3029015 := bstep (se 1 (by rfl) ⟨2271761, by rfl⟩ : syracuseStep 3029015 = 4543523) B4543523
theorem B2019343 : Blo 2017435 2019343 := bstep (se 1 (by rfl) ⟨1514507, by rfl⟩ : syracuseStep 2019343 = 3029015) B3029015
theorem B3029021 : Blo 2017435 3029021 := bbase (se 3 (by rfl) ⟨567941, by rfl⟩ : syracuseStep 3029021 = 1135883) (by norm_num)
theorem B2019347 : Blo 2017435 2019347 := bstep (se 1 (by rfl) ⟨1514510, by rfl⟩ : syracuseStep 2019347 = 3029021) B3029021
theorem B4543541 : Blo 2017435 4543541 := bbase (se 5 (by rfl) ⟨212978, by rfl⟩ : syracuseStep 4543541 = 425957) (by norm_num)
theorem B3029027 : Blo 2017435 3029027 := bstep (se 1 (by rfl) ⟨2271770, by rfl⟩ : syracuseStep 3029027 = 4543541) B4543541
theorem B2019351 : Blo 2017435 2019351 := bstep (se 1 (by rfl) ⟨1514513, by rfl⟩ : syracuseStep 2019351 = 3029027) B3029027
theorem B6469237 : Blo 2017435 6469237 := bbase (se 5 (by rfl) ⟨303245, by rfl⟩ : syracuseStep 6469237 = 606491) (by norm_num)
theorem B8625649 : Blo 2017435 8625649 := bstep (se 2 (by rfl) ⟨3234618, by rfl⟩ : syracuseStep 8625649 = 6469237) B6469237
theorem B11500865 : Blo 2017435 11500865 := bstep (se 2 (by rfl) ⟨4312824, by rfl⟩ : syracuseStep 11500865 = 8625649) B8625649
theorem B7667243 : Blo 2017435 7667243 := bstep (se 1 (by rfl) ⟨5750432, by rfl⟩ : syracuseStep 7667243 = 11500865) B11500865
theorem B5111495 : Blo 2017435 5111495 := bstep (se 1 (by rfl) ⟨3833621, by rfl⟩ : syracuseStep 5111495 = 7667243) B7667243
theorem B3407663 : Blo 2017435 3407663 := bstep (se 1 (by rfl) ⟨2555747, by rfl⟩ : syracuseStep 3407663 = 5111495) B5111495
theorem B2271775 : Blo 2017435 2271775 := bstep (se 1 (by rfl) ⟨1703831, by rfl⟩ : syracuseStep 2271775 = 3407663) B3407663
theorem B3029033 : Blo 2017435 3029033 := bstep (se 2 (by rfl) ⟨1135887, by rfl⟩ : syracuseStep 3029033 = 2271775) B2271775
theorem B2019355 : Blo 2017435 2019355 := bstep (se 1 (by rfl) ⟨1514516, by rfl⟩ : syracuseStep 2019355 = 3029033) B3029033
theorem B13115029 : Blo 2017435 13115029 := bbase (se 6 (by rfl) ⟨307383, by rfl⟩ : syracuseStep 13115029 = 614767) (by norm_num)
theorem B17486705 : Blo 2017435 17486705 := bstep (se 2 (by rfl) ⟨6557514, by rfl⟩ : syracuseStep 17486705 = 13115029) B13115029
theorem B46631213 : Blo 2017435 46631213 := bstep (se 3 (by rfl) ⟨8743352, by rfl⟩ : syracuseStep 46631213 = 17486705) B17486705
theorem B31087475 : Blo 2017435 31087475 := bstep (se 1 (by rfl) ⟨23315606, by rfl⟩ : syracuseStep 31087475 = 46631213) B46631213
theorem B20724983 : Blo 2017435 20724983 := bstep (se 1 (by rfl) ⟨15543737, by rfl⟩ : syracuseStep 20724983 = 31087475) B31087475
theorem B13816655 : Blo 2017435 13816655 := bstep (se 1 (by rfl) ⟨10362491, by rfl⟩ : syracuseStep 13816655 = 20724983) B20724983
theorem B9211103 : Blo 2017435 9211103 := bstep (se 1 (by rfl) ⟨6908327, by rfl⟩ : syracuseStep 9211103 = 13816655) B13816655
theorem B6140735 : Blo 2017435 6140735 := bstep (se 1 (by rfl) ⟨4605551, by rfl⟩ : syracuseStep 6140735 = 9211103) B9211103
theorem B4093823 : Blo 2017435 4093823 := bstep (se 1 (by rfl) ⟨3070367, by rfl⟩ : syracuseStep 4093823 = 6140735) B6140735
theorem B2729215 : Blo 2017435 2729215 := bstep (se 1 (by rfl) ⟨2046911, by rfl⟩ : syracuseStep 2729215 = 4093823) B4093823
theorem B3638953 : Blo 2017435 3638953 := bstep (se 2 (by rfl) ⟨1364607, by rfl⟩ : syracuseStep 3638953 = 2729215) B2729215
theorem B4851937 : Blo 2017435 4851937 := bstep (se 2 (by rfl) ⟨1819476, by rfl⟩ : syracuseStep 4851937 = 3638953) B3638953
theorem B6469249 : Blo 2017435 6469249 := bstep (se 2 (by rfl) ⟨2425968, by rfl⟩ : syracuseStep 6469249 = 4851937) B4851937
theorem B8625665 : Blo 2017435 8625665 := bstep (se 2 (by rfl) ⟨3234624, by rfl⟩ : syracuseStep 8625665 = 6469249) B6469249
theorem B5750443 : Blo 2017435 5750443 := bstep (se 1 (by rfl) ⟨4312832, by rfl⟩ : syracuseStep 5750443 = 8625665) B8625665
theorem B7667257 : Blo 2017435 7667257 := bstep (se 2 (by rfl) ⟨2875221, by rfl⟩ : syracuseStep 7667257 = 5750443) B5750443
theorem B10223009 : Blo 2017435 10223009 := bstep (se 2 (by rfl) ⟨3833628, by rfl⟩ : syracuseStep 10223009 = 7667257) B7667257
theorem B6815339 : Blo 2017435 6815339 := bstep (se 1 (by rfl) ⟨5111504, by rfl⟩ : syracuseStep 6815339 = 10223009) B10223009
theorem B4543559 : Blo 2017435 4543559 := bstep (se 1 (by rfl) ⟨3407669, by rfl⟩ : syracuseStep 4543559 = 6815339) B6815339
theorem B3029039 : Blo 2017435 3029039 := bstep (se 1 (by rfl) ⟨2271779, by rfl⟩ : syracuseStep 3029039 = 4543559) B4543559
theorem B2019359 : Blo 2017435 2019359 := bstep (se 1 (by rfl) ⟨1514519, by rfl⟩ : syracuseStep 2019359 = 3029039) B3029039
theorem B3029045 : Blo 2017435 3029045 := bbase (se 5 (by rfl) ⟨141986, by rfl⟩ : syracuseStep 3029045 = 283973) (by norm_num)
theorem B2019363 : Blo 2017435 2019363 := bstep (se 1 (by rfl) ⟨1514522, by rfl⟩ : syracuseStep 2019363 = 3029045) B3029045
theorem B5111525 : Blo 2017435 5111525 := bbase (se 4 (by rfl) ⟨479205, by rfl⟩ : syracuseStep 5111525 = 958411) (by norm_num)
theorem B3407683 : Blo 2017435 3407683 := bstep (se 1 (by rfl) ⟨2555762, by rfl⟩ : syracuseStep 3407683 = 5111525) B5111525
theorem B4543577 : Blo 2017435 4543577 := bstep (se 2 (by rfl) ⟨1703841, by rfl⟩ : syracuseStep 4543577 = 3407683) B3407683
theorem B3029051 : Blo 2017435 3029051 := bstep (se 1 (by rfl) ⟨2271788, by rfl⟩ : syracuseStep 3029051 = 4543577) B4543577
theorem B2019367 : Blo 2017435 2019367 := bstep (se 1 (by rfl) ⟨1514525, by rfl⟩ : syracuseStep 2019367 = 3029051) B3029051
theorem B2271793 : Blo 2017435 2271793 := bbase (se 2 (by rfl) ⟨851922, by rfl⟩ : syracuseStep 2271793 = 1703845) (by norm_num)
theorem B3029057 : Blo 2017435 3029057 := bstep (se 2 (by rfl) ⟨1135896, by rfl⟩ : syracuseStep 3029057 = 2271793) B2271793
theorem B2019371 : Blo 2017435 2019371 := bstep (se 1 (by rfl) ⟨1514528, by rfl⟩ : syracuseStep 2019371 = 3029057) B3029057
theorem B6469301 : Blo 2017435 6469301 := bbase (se 5 (by rfl) ⟨303248, by rfl⟩ : syracuseStep 6469301 = 606497) (by norm_num)
theorem B4312867 : Blo 2017435 4312867 := bstep (se 1 (by rfl) ⟨3234650, by rfl⟩ : syracuseStep 4312867 = 6469301) B6469301
theorem B5750489 : Blo 2017435 5750489 := bstep (se 2 (by rfl) ⟨2156433, by rfl⟩ : syracuseStep 5750489 = 4312867) B4312867
theorem B3833659 : Blo 2017435 3833659 := bstep (se 1 (by rfl) ⟨2875244, by rfl⟩ : syracuseStep 3833659 = 5750489) B5750489
theorem B5111545 : Blo 2017435 5111545 := bstep (se 2 (by rfl) ⟨1916829, by rfl⟩ : syracuseStep 5111545 = 3833659) B3833659
theorem B6815393 : Blo 2017435 6815393 := bstep (se 2 (by rfl) ⟨2555772, by rfl⟩ : syracuseStep 6815393 = 5111545) B5111545
theorem B4543595 : Blo 2017435 4543595 := bstep (se 1 (by rfl) ⟨3407696, by rfl⟩ : syracuseStep 4543595 = 6815393) B6815393
theorem B3029063 : Blo 2017435 3029063 := bstep (se 1 (by rfl) ⟨2271797, by rfl⟩ : syracuseStep 3029063 = 4543595) B4543595
theorem B2019375 : Blo 2017435 2019375 := bstep (se 1 (by rfl) ⟨1514531, by rfl⟩ : syracuseStep 2019375 = 3029063) B3029063
theorem B3029069 : Blo 2017435 3029069 := bbase (se 3 (by rfl) ⟨567950, by rfl⟩ : syracuseStep 3029069 = 1135901) (by norm_num)
theorem B2019379 : Blo 2017435 2019379 := bstep (se 1 (by rfl) ⟨1514534, by rfl⟩ : syracuseStep 2019379 = 3029069) B3029069
theorem B4543613 : Blo 2017435 4543613 := bbase (se 3 (by rfl) ⟨851927, by rfl⟩ : syracuseStep 4543613 = 1703855) (by norm_num)
theorem B3029075 : Blo 2017435 3029075 := bstep (se 1 (by rfl) ⟨2271806, by rfl⟩ : syracuseStep 3029075 = 4543613) B4543613
theorem B2019383 : Blo 2017435 2019383 := bstep (se 1 (by rfl) ⟨1514537, by rfl⟩ : syracuseStep 2019383 = 3029075) B3029075
theorem B3407717 : Blo 2017435 3407717 := bbase (se 4 (by rfl) ⟨319473, by rfl⟩ : syracuseStep 3407717 = 638947) (by norm_num)
theorem B2271811 : Blo 2017435 2271811 := bstep (se 1 (by rfl) ⟨1703858, by rfl⟩ : syracuseStep 2271811 = 3407717) B3407717
theorem B3029081 : Blo 2017435 3029081 := bstep (se 2 (by rfl) ⟨1135905, by rfl⟩ : syracuseStep 3029081 = 2271811) B2271811
theorem B2019387 : Blo 2017435 2019387 := bstep (se 1 (by rfl) ⟨1514540, by rfl⟩ : syracuseStep 2019387 = 3029081) B3029081
theorem B4312901 : Blo 2017435 4312901 := bbase (se 4 (by rfl) ⟨404334, by rfl⟩ : syracuseStep 4312901 = 808669) (by norm_num)
theorem B2875267 : Blo 2017435 2875267 := bstep (se 1 (by rfl) ⟨2156450, by rfl⟩ : syracuseStep 2875267 = 4312901) B4312901
theorem B15334757 : Blo 2017435 15334757 := bstep (se 4 (by rfl) ⟨1437633, by rfl⟩ : syracuseStep 15334757 = 2875267) B2875267
theorem B10223171 : Blo 2017435 10223171 := bstep (se 1 (by rfl) ⟨7667378, by rfl⟩ : syracuseStep 10223171 = 15334757) B15334757
theorem B6815447 : Blo 2017435 6815447 := bstep (se 1 (by rfl) ⟨5111585, by rfl⟩ : syracuseStep 6815447 = 10223171) B10223171
theorem B4543631 : Blo 2017435 4543631 := bstep (se 1 (by rfl) ⟨3407723, by rfl⟩ : syracuseStep 4543631 = 6815447) B6815447
theorem B3029087 : Blo 2017435 3029087 := bstep (se 1 (by rfl) ⟨2271815, by rfl⟩ : syracuseStep 3029087 = 4543631) B4543631
theorem B2019391 : Blo 2017435 2019391 := bstep (se 1 (by rfl) ⟨1514543, by rfl⟩ : syracuseStep 2019391 = 3029087) B3029087
theorem B3029093 : Blo 2017435 3029093 := bbase (se 4 (by rfl) ⟨283977, by rfl⟩ : syracuseStep 3029093 = 567955) (by norm_num)
theorem B2019395 : Blo 2017435 2019395 := bstep (se 1 (by rfl) ⟨1514546, by rfl⟩ : syracuseStep 2019395 = 3029093) B3029093
theorem B9704069 : Blo 2017435 9704069 := bbase (se 4 (by rfl) ⟨909756, by rfl⟩ : syracuseStep 9704069 = 1819513) (by norm_num)
theorem B6469379 : Blo 2017435 6469379 := bstep (se 1 (by rfl) ⟨4852034, by rfl⟩ : syracuseStep 6469379 = 9704069) B9704069
theorem B4312919 : Blo 2017435 4312919 := bstep (se 1 (by rfl) ⟨3234689, by rfl⟩ : syracuseStep 4312919 = 6469379) B6469379
theorem B2875279 : Blo 2017435 2875279 := bstep (se 1 (by rfl) ⟨2156459, by rfl⟩ : syracuseStep 2875279 = 4312919) B4312919
theorem B3833705 : Blo 2017435 3833705 := bstep (se 2 (by rfl) ⟨1437639, by rfl⟩ : syracuseStep 3833705 = 2875279) B2875279
theorem B2555803 : Blo 2017435 2555803 := bstep (se 1 (by rfl) ⟨1916852, by rfl⟩ : syracuseStep 2555803 = 3833705) B3833705
theorem B3407737 : Blo 2017435 3407737 := bstep (se 2 (by rfl) ⟨1277901, by rfl⟩ : syracuseStep 3407737 = 2555803) B2555803
theorem B4543649 : Blo 2017435 4543649 := bstep (se 2 (by rfl) ⟨1703868, by rfl⟩ : syracuseStep 4543649 = 3407737) B3407737
theorem B3029099 : Blo 2017435 3029099 := bstep (se 1 (by rfl) ⟨2271824, by rfl⟩ : syracuseStep 3029099 = 4543649) B4543649
theorem B2019399 : Blo 2017435 2019399 := bstep (se 1 (by rfl) ⟨1514549, by rfl⟩ : syracuseStep 2019399 = 3029099) B3029099
theorem B2271829 : Blo 2017435 2271829 := bbase (se 8 (by rfl) ⟨13311, by rfl⟩ : syracuseStep 2271829 = 26623) (by norm_num)
theorem B3029105 : Blo 2017435 3029105 := bstep (se 2 (by rfl) ⟨1135914, by rfl⟩ : syracuseStep 3029105 = 2271829) B2271829
theorem B2019403 : Blo 2017435 2019403 := bstep (se 1 (by rfl) ⟨1514552, by rfl⟩ : syracuseStep 2019403 = 3029105) B3029105
theorem B2555813 : Blo 2017435 2555813 := bbase (se 4 (by rfl) ⟨239607, by rfl⟩ : syracuseStep 2555813 = 479215) (by norm_num)
theorem B6815501 : Blo 2017435 6815501 := bstep (se 3 (by rfl) ⟨1277906, by rfl⟩ : syracuseStep 6815501 = 2555813) B2555813
theorem B4543667 : Blo 2017435 4543667 := bstep (se 1 (by rfl) ⟨3407750, by rfl⟩ : syracuseStep 4543667 = 6815501) B6815501
theorem B3029111 : Blo 2017435 3029111 := bstep (se 1 (by rfl) ⟨2271833, by rfl⟩ : syracuseStep 3029111 = 4543667) B4543667
theorem B2019407 : Blo 2017435 2019407 := bstep (se 1 (by rfl) ⟨1514555, by rfl⟩ : syracuseStep 2019407 = 3029111) B3029111
theorem B3029117 : Blo 2017435 3029117 := bbase (se 3 (by rfl) ⟨567959, by rfl⟩ : syracuseStep 3029117 = 1135919) (by norm_num)
theorem B2019411 : Blo 2017435 2019411 := bstep (se 1 (by rfl) ⟨1514558, by rfl⟩ : syracuseStep 2019411 = 3029117) B3029117
theorem B4543685 : Blo 2017435 4543685 := bbase (se 4 (by rfl) ⟨425970, by rfl⟩ : syracuseStep 4543685 = 851941) (by norm_num)
theorem B3029123 : Blo 2017435 3029123 := bstep (se 1 (by rfl) ⟨2271842, by rfl⟩ : syracuseStep 3029123 = 4543685) B4543685
theorem B2019415 : Blo 2017435 2019415 := bstep (se 1 (by rfl) ⟨1514561, by rfl⟩ : syracuseStep 2019415 = 3029123) B3029123
theorem B2426041 : Blo 2017435 2426041 := bbase (se 2 (by rfl) ⟨909765, by rfl⟩ : syracuseStep 2426041 = 1819531) (by norm_num)
theorem B12938885 : Blo 2017435 12938885 := bstep (se 4 (by rfl) ⟨1213020, by rfl⟩ : syracuseStep 12938885 = 2426041) B2426041
theorem B8625923 : Blo 2017435 8625923 := bstep (se 1 (by rfl) ⟨6469442, by rfl⟩ : syracuseStep 8625923 = 12938885) B12938885
theorem B5750615 : Blo 2017435 5750615 := bstep (se 1 (by rfl) ⟨4312961, by rfl⟩ : syracuseStep 5750615 = 8625923) B8625923
theorem B3833743 : Blo 2017435 3833743 := bstep (se 1 (by rfl) ⟨2875307, by rfl⟩ : syracuseStep 3833743 = 5750615) B5750615
theorem B5111657 : Blo 2017435 5111657 := bstep (se 2 (by rfl) ⟨1916871, by rfl⟩ : syracuseStep 5111657 = 3833743) B3833743
theorem B3407771 : Blo 2017435 3407771 := bstep (se 1 (by rfl) ⟨2555828, by rfl⟩ : syracuseStep 3407771 = 5111657) B5111657
theorem B2271847 : Blo 2017435 2271847 := bstep (se 1 (by rfl) ⟨1703885, by rfl⟩ : syracuseStep 2271847 = 3407771) B3407771
theorem B3029129 : Blo 2017435 3029129 := bstep (se 2 (by rfl) ⟨1135923, by rfl⟩ : syracuseStep 3029129 = 2271847) B2271847
theorem B2019419 : Blo 2017435 2019419 := bstep (se 1 (by rfl) ⟨1514564, by rfl⟩ : syracuseStep 2019419 = 3029129) B3029129
theorem B10223333 : Blo 2017435 10223333 := bbase (se 4 (by rfl) ⟨958437, by rfl⟩ : syracuseStep 10223333 = 1916875) (by norm_num)
theorem B6815555 : Blo 2017435 6815555 := bstep (se 1 (by rfl) ⟨5111666, by rfl⟩ : syracuseStep 6815555 = 10223333) B10223333
theorem B4543703 : Blo 2017435 4543703 := bstep (se 1 (by rfl) ⟨3407777, by rfl⟩ : syracuseStep 4543703 = 6815555) B6815555
theorem B3029135 : Blo 2017435 3029135 := bstep (se 1 (by rfl) ⟨2271851, by rfl⟩ : syracuseStep 3029135 = 4543703) B4543703
theorem B2019423 : Blo 2017435 2019423 := bstep (se 1 (by rfl) ⟨1514567, by rfl⟩ : syracuseStep 2019423 = 3029135) B3029135
theorem B3029141 : Blo 2017435 3029141 := bbase (se 6 (by rfl) ⟨70995, by rfl⟩ : syracuseStep 3029141 = 141991) (by norm_num)
theorem B2019427 : Blo 2017435 2019427 := bstep (se 1 (by rfl) ⟨1514570, by rfl⟩ : syracuseStep 2019427 = 3029141) B3029141
theorem B8625973 : Blo 2017435 8625973 := bbase (se 5 (by rfl) ⟨404342, by rfl⟩ : syracuseStep 8625973 = 808685) (by norm_num)
theorem B11501297 : Blo 2017435 11501297 := bstep (se 2 (by rfl) ⟨4312986, by rfl⟩ : syracuseStep 11501297 = 8625973) B8625973
theorem B7667531 : Blo 2017435 7667531 := bstep (se 1 (by rfl) ⟨5750648, by rfl⟩ : syracuseStep 7667531 = 11501297) B11501297
theorem B5111687 : Blo 2017435 5111687 := bstep (se 1 (by rfl) ⟨3833765, by rfl⟩ : syracuseStep 5111687 = 7667531) B7667531
theorem B3407791 : Blo 2017435 3407791 := bstep (se 1 (by rfl) ⟨2555843, by rfl⟩ : syracuseStep 3407791 = 5111687) B5111687
theorem B4543721 : Blo 2017435 4543721 := bstep (se 2 (by rfl) ⟨1703895, by rfl⟩ : syracuseStep 4543721 = 3407791) B3407791
theorem B3029147 : Blo 2017435 3029147 := bstep (se 1 (by rfl) ⟨2271860, by rfl⟩ : syracuseStep 3029147 = 4543721) B4543721
theorem B2019431 : Blo 2017435 2019431 := bstep (se 1 (by rfl) ⟨1514573, by rfl⟩ : syracuseStep 2019431 = 3029147) B3029147
theorem B2271865 : Blo 2017435 2271865 := bbase (se 2 (by rfl) ⟨851949, by rfl⟩ : syracuseStep 2271865 = 1703899) (by norm_num)
theorem B3029153 : Blo 2017435 3029153 := bstep (se 2 (by rfl) ⟨1135932, by rfl⟩ : syracuseStep 3029153 = 2271865) B2271865
theorem B2019435 : Blo 2017435 2019435 := bstep (se 1 (by rfl) ⟨1514576, by rfl⟩ : syracuseStep 2019435 = 3029153) B3029153
theorem C0 (j : ℕ) (h1 : 504358 ≤ j) (h2 : j ≤ 504858) : Blo 2017435 (4 * j + 3) := by
  interval_cases j
  · exact B2017435
  · exact B2017439
  · exact B2017443
  · exact B2017447
  · exact B2017451
  · exact B2017455
  · exact B2017459
  · exact B2017463
  · exact B2017467
  · exact B2017471
  · exact B2017475
  · exact B2017479
  · exact B2017483
  · exact B2017487
  · exact B2017491
  · exact B2017495
  · exact B2017499
  · exact B2017503
  · exact B2017507
  · exact B2017511
  · exact B2017515
  · exact B2017519
  · exact B2017523
  · exact B2017527
  · exact B2017531
  · exact B2017535
  · exact B2017539
  · exact B2017543
  · exact B2017547
  · exact B2017551
  · exact B2017555
  · exact B2017559
  · exact B2017563
  · exact B2017567
  · exact B2017571
  · exact B2017575
  · exact B2017579
  · exact B2017583
  · exact B2017587
  · exact B2017591
  · exact B2017595
  · exact B2017599
  · exact B2017603
  · exact B2017607
  · exact B2017611
  · exact B2017615
  · exact B2017619
  · exact B2017623
  · exact B2017627
  · exact B2017631
  · exact B2017635
  · exact B2017639
  · exact B2017643
  · exact B2017647
  · exact B2017651
  · exact B2017655
  · exact B2017659
  · exact B2017663
  · exact B2017667
  · exact B2017671
  · exact B2017675
  · exact B2017679
  · exact B2017683
  · exact B2017687
  · exact B2017691
  · exact B2017695
  · exact B2017699
  · exact B2017703
  · exact B2017707
  · exact B2017711
  · exact B2017715
  · exact B2017719
  · exact B2017723
  · exact B2017727
  · exact B2017731
  · exact B2017735
  · exact B2017739
  · exact B2017743
  · exact B2017747
  · exact B2017751
  · exact B2017755
  · exact B2017759
  · exact B2017763
  · exact B2017767
  · exact B2017771
  · exact B2017775
  · exact B2017779
  · exact B2017783
  · exact B2017787
  · exact B2017791
  · exact B2017795
  · exact B2017799
  · exact B2017803
  · exact B2017807
  · exact B2017811
  · exact B2017815
  · exact B2017819
  · exact B2017823
  · exact B2017827
  · exact B2017831
  · exact B2017835
  · exact B2017839
  · exact B2017843
  · exact B2017847
  · exact B2017851
  · exact B2017855
  · exact B2017859
  · exact B2017863
  · exact B2017867
  · exact B2017871
  · exact B2017875
  · exact B2017879
  · exact B2017883
  · exact B2017887
  · exact B2017891
  · exact B2017895
  · exact B2017899
  · exact B2017903
  · exact B2017907
  · exact B2017911
  · exact B2017915
  · exact B2017919
  · exact B2017923
  · exact B2017927
  · exact B2017931
  · exact B2017935
  · exact B2017939
  · exact B2017943
  · exact B2017947
  · exact B2017951
  · exact B2017955
  · exact B2017959
  · exact B2017963
  · exact B2017967
  · exact B2017971
  · exact B2017975
  · exact B2017979
  · exact B2017983
  · exact B2017987
  · exact B2017991
  · exact B2017995
  · exact B2017999
  · exact B2018003
  · exact B2018007
  · exact B2018011
  · exact B2018015
  · exact B2018019
  · exact B2018023
  · exact B2018027
  · exact B2018031
  · exact B2018035
  · exact B2018039
  · exact B2018043
  · exact B2018047
  · exact B2018051
  · exact B2018055
  · exact B2018059
  · exact B2018063
  · exact B2018067
  · exact B2018071
  · exact B2018075
  · exact B2018079
  · exact B2018083
  · exact B2018087
  · exact B2018091
  · exact B2018095
  · exact B2018099
  · exact B2018103
  · exact B2018107
  · exact B2018111
  · exact B2018115
  · exact B2018119
  · exact B2018123
  · exact B2018127
  · exact B2018131
  · exact B2018135
  · exact B2018139
  · exact B2018143
  · exact B2018147
  · exact B2018151
  · exact B2018155
  · exact B2018159
  · exact B2018163
  · exact B2018167
  · exact B2018171
  · exact B2018175
  · exact B2018179
  · exact B2018183
  · exact B2018187
  · exact B2018191
  · exact B2018195
  · exact B2018199
  · exact B2018203
  · exact B2018207
  · exact B2018211
  · exact B2018215
  · exact B2018219
  · exact B2018223
  · exact B2018227
  · exact B2018231
  · exact B2018235
  · exact B2018239
  · exact B2018243
  · exact B2018247
  · exact B2018251
  · exact B2018255
  · exact B2018259
  · exact B2018263
  · exact B2018267
  · exact B2018271
  · exact B2018275
  · exact B2018279
  · exact B2018283
  · exact B2018287
  · exact B2018291
  · exact B2018295
  · exact B2018299
  · exact B2018303
  · exact B2018307
  · exact B2018311
  · exact B2018315
  · exact B2018319
  · exact B2018323
  · exact B2018327
  · exact B2018331
  · exact B2018335
  · exact B2018339
  · exact B2018343
  · exact B2018347
  · exact B2018351
  · exact B2018355
  · exact B2018359
  · exact B2018363
  · exact B2018367
  · exact B2018371
  · exact B2018375
  · exact B2018379
  · exact B2018383
  · exact B2018387
  · exact B2018391
  · exact B2018395
  · exact B2018399
  · exact B2018403
  · exact B2018407
  · exact B2018411
  · exact B2018415
  · exact B2018419
  · exact B2018423
  · exact B2018427
  · exact B2018431
  · exact B2018435
  · exact B2018439
  · exact B2018443
  · exact B2018447
  · exact B2018451
  · exact B2018455
  · exact B2018459
  · exact B2018463
  · exact B2018467
  · exact B2018471
  · exact B2018475
  · exact B2018479
  · exact B2018483
  · exact B2018487
  · exact B2018491
  · exact B2018495
  · exact B2018499
  · exact B2018503
  · exact B2018507
  · exact B2018511
  · exact B2018515
  · exact B2018519
  · exact B2018523
  · exact B2018527
  · exact B2018531
  · exact B2018535
  · exact B2018539
  · exact B2018543
  · exact B2018547
  · exact B2018551
  · exact B2018555
  · exact B2018559
  · exact B2018563
  · exact B2018567
  · exact B2018571
  · exact B2018575
  · exact B2018579
  · exact B2018583
  · exact B2018587
  · exact B2018591
  · exact B2018595
  · exact B2018599
  · exact B2018603
  · exact B2018607
  · exact B2018611
  · exact B2018615
  · exact B2018619
  · exact B2018623
  · exact B2018627
  · exact B2018631
  · exact B2018635
  · exact B2018639
  · exact B2018643
  · exact B2018647
  · exact B2018651
  · exact B2018655
  · exact B2018659
  · exact B2018663
  · exact B2018667
  · exact B2018671
  · exact B2018675
  · exact B2018679
  · exact B2018683
  · exact B2018687
  · exact B2018691
  · exact B2018695
  · exact B2018699
  · exact B2018703
  · exact B2018707
  · exact B2018711
  · exact B2018715
  · exact B2018719
  · exact B2018723
  · exact B2018727
  · exact B2018731
  · exact B2018735
  · exact B2018739
  · exact B2018743
  · exact B2018747
  · exact B2018751
  · exact B2018755
  · exact B2018759
  · exact B2018763
  · exact B2018767
  · exact B2018771
  · exact B2018775
  · exact B2018779
  · exact B2018783
  · exact B2018787
  · exact B2018791
  · exact B2018795
  · exact B2018799
  · exact B2018803
  · exact B2018807
  · exact B2018811
  · exact B2018815
  · exact B2018819
  · exact B2018823
  · exact B2018827
  · exact B2018831
  · exact B2018835
  · exact B2018839
  · exact B2018843
  · exact B2018847
  · exact B2018851
  · exact B2018855
  · exact B2018859
  · exact B2018863
  · exact B2018867
  · exact B2018871
  · exact B2018875
  · exact B2018879
  · exact B2018883
  · exact B2018887
  · exact B2018891
  · exact B2018895
  · exact B2018899
  · exact B2018903
  · exact B2018907
  · exact B2018911
  · exact B2018915
  · exact B2018919
  · exact B2018923
  · exact B2018927
  · exact B2018931
  · exact B2018935
  · exact B2018939
  · exact B2018943
  · exact B2018947
  · exact B2018951
  · exact B2018955
  · exact B2018959
  · exact B2018963
  · exact B2018967
  · exact B2018971
  · exact B2018975
  · exact B2018979
  · exact B2018983
  · exact B2018987
  · exact B2018991
  · exact B2018995
  · exact B2018999
  · exact B2019003
  · exact B2019007
  · exact B2019011
  · exact B2019015
  · exact B2019019
  · exact B2019023
  · exact B2019027
  · exact B2019031
  · exact B2019035
  · exact B2019039
  · exact B2019043
  · exact B2019047
  · exact B2019051
  · exact B2019055
  · exact B2019059
  · exact B2019063
  · exact B2019067
  · exact B2019071
  · exact B2019075
  · exact B2019079
  · exact B2019083
  · exact B2019087
  · exact B2019091
  · exact B2019095
  · exact B2019099
  · exact B2019103
  · exact B2019107
  · exact B2019111
  · exact B2019115
  · exact B2019119
  · exact B2019123
  · exact B2019127
  · exact B2019131
  · exact B2019135
  · exact B2019139
  · exact B2019143
  · exact B2019147
  · exact B2019151
  · exact B2019155
  · exact B2019159
  · exact B2019163
  · exact B2019167
  · exact B2019171
  · exact B2019175
  · exact B2019179
  · exact B2019183
  · exact B2019187
  · exact B2019191
  · exact B2019195
  · exact B2019199
  · exact B2019203
  · exact B2019207
  · exact B2019211
  · exact B2019215
  · exact B2019219
  · exact B2019223
  · exact B2019227
  · exact B2019231
  · exact B2019235
  · exact B2019239
  · exact B2019243
  · exact B2019247
  · exact B2019251
  · exact B2019255
  · exact B2019259
  · exact B2019263
  · exact B2019267
  · exact B2019271
  · exact B2019275
  · exact B2019279
  · exact B2019283
  · exact B2019287
  · exact B2019291
  · exact B2019295
  · exact B2019299
  · exact B2019303
  · exact B2019307
  · exact B2019311
  · exact B2019315
  · exact B2019319
  · exact B2019323
  · exact B2019327
  · exact B2019331
  · exact B2019335
  · exact B2019339
  · exact B2019343
  · exact B2019347
  · exact B2019351
  · exact B2019355
  · exact B2019359
  · exact B2019363
  · exact B2019367
  · exact B2019371
  · exact B2019375
  · exact B2019379
  · exact B2019383
  · exact B2019387
  · exact B2019391
  · exact B2019395
  · exact B2019399
  · exact B2019403
  · exact B2019407
  · exact B2019411
  · exact B2019415
  · exact B2019419
  · exact B2019423
  · exact B2019427
  · exact B2019431
  · exact B2019435
theorem solution (m : ℕ) (hlo : 2017435 ≤ m) (hhi : m ≤ 2019435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 504358 ≤ j := by omega
    have hj2 : j ≤ 504858 := by omega
    have hb : Blo 2017435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
