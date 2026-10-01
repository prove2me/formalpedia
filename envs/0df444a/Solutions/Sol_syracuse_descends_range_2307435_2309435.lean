-- Prove2me | solution 1 for syracuse_descends_range_2307435_2309435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:50:07.993828+00:00
-- url     : https://prove2.me/submissions/9ca5ac2c-837d-4e95-84c9-587066cfe3b4

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

theorem B2595865 : Blo 2307435 2595865 := bbase (se 2 (by rfl) ⟨973449, by rfl⟩ : syracuseStep 2595865 = 1946899) (by norm_num)
theorem B3461153 : Blo 2307435 3461153 := bstep (se 2 (by rfl) ⟨1297932, by rfl⟩ : syracuseStep 3461153 = 2595865) B2595865
theorem B2307435 : Blo 2307435 2307435 := bstep (se 1 (by rfl) ⟨1730576, by rfl⟩ : syracuseStep 2307435 = 3461153) B3461153
theorem B8761061 : Blo 2307435 8761061 := bbase (se 4 (by rfl) ⟨821349, by rfl⟩ : syracuseStep 8761061 = 1642699) (by norm_num)
theorem B5840707 : Blo 2307435 5840707 := bstep (se 1 (by rfl) ⟨4380530, by rfl⟩ : syracuseStep 5840707 = 8761061) B8761061
theorem B7787609 : Blo 2307435 7787609 := bstep (se 2 (by rfl) ⟨2920353, by rfl⟩ : syracuseStep 7787609 = 5840707) B5840707
theorem B5191739 : Blo 2307435 5191739 := bstep (se 1 (by rfl) ⟨3893804, by rfl⟩ : syracuseStep 5191739 = 7787609) B7787609
theorem B3461159 : Blo 2307435 3461159 := bstep (se 1 (by rfl) ⟨2595869, by rfl⟩ : syracuseStep 3461159 = 5191739) B5191739
theorem B2307439 : Blo 2307435 2307439 := bstep (se 1 (by rfl) ⟨1730579, by rfl⟩ : syracuseStep 2307439 = 3461159) B3461159
theorem B3461165 : Blo 2307435 3461165 := bbase (se 3 (by rfl) ⟨648968, by rfl⟩ : syracuseStep 3461165 = 1297937) (by norm_num)
theorem B2307443 : Blo 2307435 2307443 := bstep (se 1 (by rfl) ⟨1730582, by rfl⟩ : syracuseStep 2307443 = 3461165) B3461165
theorem B5191757 : Blo 2307435 5191757 := bbase (se 3 (by rfl) ⟨973454, by rfl⟩ : syracuseStep 5191757 = 1946909) (by norm_num)
theorem B3461171 : Blo 2307435 3461171 := bstep (se 1 (by rfl) ⟨2595878, by rfl⟩ : syracuseStep 3461171 = 5191757) B5191757
theorem B2307447 : Blo 2307435 2307447 := bstep (se 1 (by rfl) ⟨1730585, by rfl⟩ : syracuseStep 2307447 = 3461171) B3461171
theorem B2920369 : Blo 2307435 2920369 := bbase (se 2 (by rfl) ⟨1095138, by rfl⟩ : syracuseStep 2920369 = 2190277) (by norm_num)
theorem B3893825 : Blo 2307435 3893825 := bstep (se 2 (by rfl) ⟨1460184, by rfl⟩ : syracuseStep 3893825 = 2920369) B2920369
theorem B2595883 : Blo 2307435 2595883 := bstep (se 1 (by rfl) ⟨1946912, by rfl⟩ : syracuseStep 2595883 = 3893825) B3893825
theorem B3461177 : Blo 2307435 3461177 := bstep (se 2 (by rfl) ⟨1297941, by rfl⟩ : syracuseStep 3461177 = 2595883) B2595883
theorem B2307451 : Blo 2307435 2307451 := bstep (se 1 (by rfl) ⟨1730588, by rfl⟩ : syracuseStep 2307451 = 3461177) B3461177
theorem B7392197 : Blo 2307435 7392197 := bbase (se 4 (by rfl) ⟨693018, by rfl⟩ : syracuseStep 7392197 = 1386037) (by norm_num)
theorem B4928131 : Blo 2307435 4928131 := bstep (se 1 (by rfl) ⟨3696098, by rfl⟩ : syracuseStep 4928131 = 7392197) B7392197
theorem B26283365 : Blo 2307435 26283365 := bstep (se 4 (by rfl) ⟨2464065, by rfl⟩ : syracuseStep 26283365 = 4928131) B4928131
theorem B17522243 : Blo 2307435 17522243 := bstep (se 1 (by rfl) ⟨13141682, by rfl⟩ : syracuseStep 17522243 = 26283365) B26283365
theorem B11681495 : Blo 2307435 11681495 := bstep (se 1 (by rfl) ⟨8761121, by rfl⟩ : syracuseStep 11681495 = 17522243) B17522243
theorem B7787663 : Blo 2307435 7787663 := bstep (se 1 (by rfl) ⟨5840747, by rfl⟩ : syracuseStep 7787663 = 11681495) B11681495
theorem B5191775 : Blo 2307435 5191775 := bstep (se 1 (by rfl) ⟨3893831, by rfl⟩ : syracuseStep 5191775 = 7787663) B7787663
theorem B3461183 : Blo 2307435 3461183 := bstep (se 1 (by rfl) ⟨2595887, by rfl⟩ : syracuseStep 3461183 = 5191775) B5191775
theorem B2307455 : Blo 2307435 2307455 := bstep (se 1 (by rfl) ⟨1730591, by rfl⟩ : syracuseStep 2307455 = 3461183) B3461183
theorem B3461189 : Blo 2307435 3461189 := bbase (se 4 (by rfl) ⟨324486, by rfl⟩ : syracuseStep 3461189 = 648973) (by norm_num)
theorem B2307459 : Blo 2307435 2307459 := bstep (se 1 (by rfl) ⟨1730594, by rfl⟩ : syracuseStep 2307459 = 3461189) B3461189
theorem B3893845 : Blo 2307435 3893845 := bbase (se 8 (by rfl) ⟨22815, by rfl⟩ : syracuseStep 3893845 = 45631) (by norm_num)
theorem B5191793 : Blo 2307435 5191793 := bstep (se 2 (by rfl) ⟨1946922, by rfl⟩ : syracuseStep 5191793 = 3893845) B3893845
theorem B3461195 : Blo 2307435 3461195 := bstep (se 1 (by rfl) ⟨2595896, by rfl⟩ : syracuseStep 3461195 = 5191793) B5191793
theorem B2307463 : Blo 2307435 2307463 := bstep (se 1 (by rfl) ⟨1730597, by rfl⟩ : syracuseStep 2307463 = 3461195) B3461195
theorem B2595901 : Blo 2307435 2595901 := bbase (se 3 (by rfl) ⟨486731, by rfl⟩ : syracuseStep 2595901 = 973463) (by norm_num)
theorem B3461201 : Blo 2307435 3461201 := bstep (se 2 (by rfl) ⟨1297950, by rfl⟩ : syracuseStep 3461201 = 2595901) B2595901
theorem B2307467 : Blo 2307435 2307467 := bstep (se 1 (by rfl) ⟨1730600, by rfl⟩ : syracuseStep 2307467 = 3461201) B3461201
theorem B7787717 : Blo 2307435 7787717 := bbase (se 4 (by rfl) ⟨730098, by rfl⟩ : syracuseStep 7787717 = 1460197) (by norm_num)
theorem B5191811 : Blo 2307435 5191811 := bstep (se 1 (by rfl) ⟨3893858, by rfl⟩ : syracuseStep 5191811 = 7787717) B7787717
theorem B3461207 : Blo 2307435 3461207 := bstep (se 1 (by rfl) ⟨2595905, by rfl⟩ : syracuseStep 3461207 = 5191811) B5191811
theorem B2307471 : Blo 2307435 2307471 := bstep (se 1 (by rfl) ⟨1730603, by rfl⟩ : syracuseStep 2307471 = 3461207) B3461207
theorem B3461213 : Blo 2307435 3461213 := bbase (se 3 (by rfl) ⟨648977, by rfl⟩ : syracuseStep 3461213 = 1297955) (by norm_num)
theorem B2307475 : Blo 2307435 2307475 := bstep (se 1 (by rfl) ⟨1730606, by rfl⟩ : syracuseStep 2307475 = 3461213) B3461213
theorem B5191829 : Blo 2307435 5191829 := bbase (se 6 (by rfl) ⟨121683, by rfl⟩ : syracuseStep 5191829 = 243367) (by norm_num)
theorem B3461219 : Blo 2307435 3461219 := bstep (se 1 (by rfl) ⟨2595914, by rfl⟩ : syracuseStep 3461219 = 5191829) B5191829
theorem B2307479 : Blo 2307435 2307479 := bstep (se 1 (by rfl) ⟨1730609, by rfl⟩ : syracuseStep 2307479 = 3461219) B3461219
theorem B3285461 : Blo 2307435 3285461 := bbase (se 7 (by rfl) ⟨38501, by rfl⟩ : syracuseStep 3285461 = 77003) (by norm_num)
theorem B8761229 : Blo 2307435 8761229 := bstep (se 3 (by rfl) ⟨1642730, by rfl⟩ : syracuseStep 8761229 = 3285461) B3285461
theorem B5840819 : Blo 2307435 5840819 := bstep (se 1 (by rfl) ⟨4380614, by rfl⟩ : syracuseStep 5840819 = 8761229) B8761229
theorem B3893879 : Blo 2307435 3893879 := bstep (se 1 (by rfl) ⟨2920409, by rfl⟩ : syracuseStep 3893879 = 5840819) B5840819
theorem B2595919 : Blo 2307435 2595919 := bstep (se 1 (by rfl) ⟨1946939, by rfl⟩ : syracuseStep 2595919 = 3893879) B3893879
theorem B3461225 : Blo 2307435 3461225 := bstep (se 2 (by rfl) ⟨1297959, by rfl⟩ : syracuseStep 3461225 = 2595919) B2595919
theorem B2307483 : Blo 2307435 2307483 := bstep (se 1 (by rfl) ⟨1730612, by rfl⟩ : syracuseStep 2307483 = 3461225) B3461225
theorem B6237253 : Blo 2307435 6237253 := bbase (se 4 (by rfl) ⟨584742, by rfl⟩ : syracuseStep 6237253 = 1169485) (by norm_num)
theorem B33265349 : Blo 2307435 33265349 := bstep (se 4 (by rfl) ⟨3118626, by rfl⟩ : syracuseStep 33265349 = 6237253) B6237253
theorem B22176899 : Blo 2307435 22176899 := bstep (se 1 (by rfl) ⟨16632674, by rfl⟩ : syracuseStep 22176899 = 33265349) B33265349
theorem B14784599 : Blo 2307435 14784599 := bstep (se 1 (by rfl) ⟨11088449, by rfl⟩ : syracuseStep 14784599 = 22176899) B22176899
theorem B9856399 : Blo 2307435 9856399 := bstep (se 1 (by rfl) ⟨7392299, by rfl⟩ : syracuseStep 9856399 = 14784599) B14784599
theorem B13141865 : Blo 2307435 13141865 := bstep (se 2 (by rfl) ⟨4928199, by rfl⟩ : syracuseStep 13141865 = 9856399) B9856399
theorem B8761243 : Blo 2307435 8761243 := bstep (se 1 (by rfl) ⟨6570932, by rfl⟩ : syracuseStep 8761243 = 13141865) B13141865
theorem B11681657 : Blo 2307435 11681657 := bstep (se 2 (by rfl) ⟨4380621, by rfl⟩ : syracuseStep 11681657 = 8761243) B8761243
theorem B7787771 : Blo 2307435 7787771 := bstep (se 1 (by rfl) ⟨5840828, by rfl⟩ : syracuseStep 7787771 = 11681657) B11681657
theorem B5191847 : Blo 2307435 5191847 := bstep (se 1 (by rfl) ⟨3893885, by rfl⟩ : syracuseStep 5191847 = 7787771) B7787771
theorem B3461231 : Blo 2307435 3461231 := bstep (se 1 (by rfl) ⟨2595923, by rfl⟩ : syracuseStep 3461231 = 5191847) B5191847
theorem B2307487 : Blo 2307435 2307487 := bstep (se 1 (by rfl) ⟨1730615, by rfl⟩ : syracuseStep 2307487 = 3461231) B3461231
theorem B3461237 : Blo 2307435 3461237 := bbase (se 5 (by rfl) ⟨162245, by rfl⟩ : syracuseStep 3461237 = 324491) (by norm_num)
theorem B2307491 : Blo 2307435 2307491 := bstep (se 1 (by rfl) ⟨1730618, by rfl⟩ : syracuseStep 2307491 = 3461237) B3461237
theorem B4380637 : Blo 2307435 4380637 := bbase (se 3 (by rfl) ⟨821369, by rfl⟩ : syracuseStep 4380637 = 1642739) (by norm_num)
theorem B5840849 : Blo 2307435 5840849 := bstep (se 2 (by rfl) ⟨2190318, by rfl⟩ : syracuseStep 5840849 = 4380637) B4380637
theorem B3893899 : Blo 2307435 3893899 := bstep (se 1 (by rfl) ⟨2920424, by rfl⟩ : syracuseStep 3893899 = 5840849) B5840849
theorem B5191865 : Blo 2307435 5191865 := bstep (se 2 (by rfl) ⟨1946949, by rfl⟩ : syracuseStep 5191865 = 3893899) B3893899
theorem B3461243 : Blo 2307435 3461243 := bstep (se 1 (by rfl) ⟨2595932, by rfl⟩ : syracuseStep 3461243 = 5191865) B5191865
theorem B2307495 : Blo 2307435 2307495 := bstep (se 1 (by rfl) ⟨1730621, by rfl⟩ : syracuseStep 2307495 = 3461243) B3461243
theorem B2595937 : Blo 2307435 2595937 := bbase (se 2 (by rfl) ⟨973476, by rfl⟩ : syracuseStep 2595937 = 1946953) (by norm_num)
theorem B3461249 : Blo 2307435 3461249 := bstep (se 2 (by rfl) ⟨1297968, by rfl⟩ : syracuseStep 3461249 = 2595937) B2595937
theorem B2307499 : Blo 2307435 2307499 := bstep (se 1 (by rfl) ⟨1730624, by rfl⟩ : syracuseStep 2307499 = 3461249) B3461249
theorem B5840869 : Blo 2307435 5840869 := bbase (se 4 (by rfl) ⟨547581, by rfl⟩ : syracuseStep 5840869 = 1095163) (by norm_num)
theorem B7787825 : Blo 2307435 7787825 := bstep (se 2 (by rfl) ⟨2920434, by rfl⟩ : syracuseStep 7787825 = 5840869) B5840869
theorem B5191883 : Blo 2307435 5191883 := bstep (se 1 (by rfl) ⟨3893912, by rfl⟩ : syracuseStep 5191883 = 7787825) B7787825
theorem B3461255 : Blo 2307435 3461255 := bstep (se 1 (by rfl) ⟨2595941, by rfl⟩ : syracuseStep 3461255 = 5191883) B5191883
theorem B2307503 : Blo 2307435 2307503 := bstep (se 1 (by rfl) ⟨1730627, by rfl⟩ : syracuseStep 2307503 = 3461255) B3461255
theorem B3461261 : Blo 2307435 3461261 := bbase (se 3 (by rfl) ⟨648986, by rfl⟩ : syracuseStep 3461261 = 1297973) (by norm_num)
theorem B2307507 : Blo 2307435 2307507 := bstep (se 1 (by rfl) ⟨1730630, by rfl⟩ : syracuseStep 2307507 = 3461261) B3461261
theorem B5191901 : Blo 2307435 5191901 := bbase (se 3 (by rfl) ⟨973481, by rfl⟩ : syracuseStep 5191901 = 1946963) (by norm_num)
theorem B3461267 : Blo 2307435 3461267 := bstep (se 1 (by rfl) ⟨2595950, by rfl⟩ : syracuseStep 3461267 = 5191901) B5191901
theorem B2307511 : Blo 2307435 2307511 := bstep (se 1 (by rfl) ⟨1730633, by rfl⟩ : syracuseStep 2307511 = 3461267) B3461267
theorem B3893933 : Blo 2307435 3893933 := bbase (se 3 (by rfl) ⟨730112, by rfl⟩ : syracuseStep 3893933 = 1460225) (by norm_num)
theorem B2595955 : Blo 2307435 2595955 := bstep (se 1 (by rfl) ⟨1946966, by rfl⟩ : syracuseStep 2595955 = 3893933) B3893933
theorem B3461273 : Blo 2307435 3461273 := bstep (se 2 (by rfl) ⟨1297977, by rfl⟩ : syracuseStep 3461273 = 2595955) B2595955
theorem B2307515 : Blo 2307435 2307515 := bstep (se 1 (by rfl) ⟨1730636, by rfl⟩ : syracuseStep 2307515 = 3461273) B3461273
theorem B7894133 : Blo 2307435 7894133 := bbase (se 5 (by rfl) ⟨370037, by rfl⟩ : syracuseStep 7894133 = 740075) (by norm_num)
theorem B5262755 : Blo 2307435 5262755 := bstep (se 1 (by rfl) ⟨3947066, by rfl⟩ : syracuseStep 5262755 = 7894133) B7894133
theorem B56136053 : Blo 2307435 56136053 := bstep (se 5 (by rfl) ⟨2631377, by rfl⟩ : syracuseStep 56136053 = 5262755) B5262755
theorem B37424035 : Blo 2307435 37424035 := bstep (se 1 (by rfl) ⟨28068026, by rfl⟩ : syracuseStep 37424035 = 56136053) B56136053
theorem B49898713 : Blo 2307435 49898713 := bstep (se 2 (by rfl) ⟨18712017, by rfl⟩ : syracuseStep 49898713 = 37424035) B37424035
theorem B66531617 : Blo 2307435 66531617 := bstep (se 2 (by rfl) ⟨24949356, by rfl⟩ : syracuseStep 66531617 = 49898713) B49898713
theorem B44354411 : Blo 2307435 44354411 := bstep (se 1 (by rfl) ⟨33265808, by rfl⟩ : syracuseStep 44354411 = 66531617) B66531617
theorem B29569607 : Blo 2307435 29569607 := bstep (se 1 (by rfl) ⟨22177205, by rfl⟩ : syracuseStep 29569607 = 44354411) B44354411
theorem B19713071 : Blo 2307435 19713071 := bstep (se 1 (by rfl) ⟨14784803, by rfl⟩ : syracuseStep 19713071 = 29569607) B29569607
theorem B13142047 : Blo 2307435 13142047 := bstep (se 1 (by rfl) ⟨9856535, by rfl⟩ : syracuseStep 13142047 = 19713071) B19713071
theorem B17522729 : Blo 2307435 17522729 := bstep (se 2 (by rfl) ⟨6571023, by rfl⟩ : syracuseStep 17522729 = 13142047) B13142047
theorem B11681819 : Blo 2307435 11681819 := bstep (se 1 (by rfl) ⟨8761364, by rfl⟩ : syracuseStep 11681819 = 17522729) B17522729
theorem B7787879 : Blo 2307435 7787879 := bstep (se 1 (by rfl) ⟨5840909, by rfl⟩ : syracuseStep 7787879 = 11681819) B11681819
theorem B5191919 : Blo 2307435 5191919 := bstep (se 1 (by rfl) ⟨3893939, by rfl⟩ : syracuseStep 5191919 = 7787879) B7787879
theorem B3461279 : Blo 2307435 3461279 := bstep (se 1 (by rfl) ⟨2595959, by rfl⟩ : syracuseStep 3461279 = 5191919) B5191919
theorem B2307519 : Blo 2307435 2307519 := bstep (se 1 (by rfl) ⟨1730639, by rfl⟩ : syracuseStep 2307519 = 3461279) B3461279
theorem B3461285 : Blo 2307435 3461285 := bbase (se 4 (by rfl) ⟨324495, by rfl⟩ : syracuseStep 3461285 = 648991) (by norm_num)
theorem B2307523 : Blo 2307435 2307523 := bstep (se 1 (by rfl) ⟨1730642, by rfl⟩ : syracuseStep 2307523 = 3461285) B3461285
theorem B2920465 : Blo 2307435 2920465 := bbase (se 2 (by rfl) ⟨1095174, by rfl⟩ : syracuseStep 2920465 = 2190349) (by norm_num)
theorem B3893953 : Blo 2307435 3893953 := bstep (se 2 (by rfl) ⟨1460232, by rfl⟩ : syracuseStep 3893953 = 2920465) B2920465
theorem B5191937 : Blo 2307435 5191937 := bstep (se 2 (by rfl) ⟨1946976, by rfl⟩ : syracuseStep 5191937 = 3893953) B3893953
theorem B3461291 : Blo 2307435 3461291 := bstep (se 1 (by rfl) ⟨2595968, by rfl⟩ : syracuseStep 3461291 = 5191937) B5191937
theorem B2307527 : Blo 2307435 2307527 := bstep (se 1 (by rfl) ⟨1730645, by rfl⟩ : syracuseStep 2307527 = 3461291) B3461291
theorem B2595973 : Blo 2307435 2595973 := bbase (se 4 (by rfl) ⟨243372, by rfl⟩ : syracuseStep 2595973 = 486745) (by norm_num)
theorem B3461297 : Blo 2307435 3461297 := bstep (se 2 (by rfl) ⟨1297986, by rfl⟩ : syracuseStep 3461297 = 2595973) B2595973
theorem B2307531 : Blo 2307435 2307531 := bstep (se 1 (by rfl) ⟨1730648, by rfl⟩ : syracuseStep 2307531 = 3461297) B3461297
theorem B2631397 : Blo 2307435 2631397 := bbase (se 4 (by rfl) ⟨246693, by rfl⟩ : syracuseStep 2631397 = 493387) (by norm_num)
theorem B3508529 : Blo 2307435 3508529 := bstep (se 2 (by rfl) ⟨1315698, by rfl⟩ : syracuseStep 3508529 = 2631397) B2631397
theorem B9356077 : Blo 2307435 9356077 := bstep (se 3 (by rfl) ⟨1754264, by rfl⟩ : syracuseStep 9356077 = 3508529) B3508529
theorem B12474769 : Blo 2307435 12474769 := bstep (se 2 (by rfl) ⟨4678038, by rfl⟩ : syracuseStep 12474769 = 9356077) B9356077
theorem B16633025 : Blo 2307435 16633025 := bstep (se 2 (by rfl) ⟨6237384, by rfl⟩ : syracuseStep 16633025 = 12474769) B12474769
theorem B11088683 : Blo 2307435 11088683 := bstep (se 1 (by rfl) ⟨8316512, by rfl⟩ : syracuseStep 11088683 = 16633025) B16633025
theorem B7392455 : Blo 2307435 7392455 := bstep (se 1 (by rfl) ⟨5544341, by rfl⟩ : syracuseStep 7392455 = 11088683) B11088683
theorem B4928303 : Blo 2307435 4928303 := bstep (se 1 (by rfl) ⟨3696227, by rfl⟩ : syracuseStep 4928303 = 7392455) B7392455
theorem B3285535 : Blo 2307435 3285535 := bstep (se 1 (by rfl) ⟨2464151, by rfl⟩ : syracuseStep 3285535 = 4928303) B4928303
theorem B4380713 : Blo 2307435 4380713 := bstep (se 2 (by rfl) ⟨1642767, by rfl⟩ : syracuseStep 4380713 = 3285535) B3285535
theorem B2920475 : Blo 2307435 2920475 := bstep (se 1 (by rfl) ⟨2190356, by rfl⟩ : syracuseStep 2920475 = 4380713) B4380713
theorem B7787933 : Blo 2307435 7787933 := bstep (se 3 (by rfl) ⟨1460237, by rfl⟩ : syracuseStep 7787933 = 2920475) B2920475
theorem B5191955 : Blo 2307435 5191955 := bstep (se 1 (by rfl) ⟨3893966, by rfl⟩ : syracuseStep 5191955 = 7787933) B7787933
theorem B3461303 : Blo 2307435 3461303 := bstep (se 1 (by rfl) ⟨2595977, by rfl⟩ : syracuseStep 3461303 = 5191955) B5191955
theorem B2307535 : Blo 2307435 2307535 := bstep (se 1 (by rfl) ⟨1730651, by rfl⟩ : syracuseStep 2307535 = 3461303) B3461303
theorem B3461309 : Blo 2307435 3461309 := bbase (se 3 (by rfl) ⟨648995, by rfl⟩ : syracuseStep 3461309 = 1297991) (by norm_num)
theorem B2307539 : Blo 2307435 2307539 := bstep (se 1 (by rfl) ⟨1730654, by rfl⟩ : syracuseStep 2307539 = 3461309) B3461309
theorem B5191973 : Blo 2307435 5191973 := bbase (se 4 (by rfl) ⟨486747, by rfl⟩ : syracuseStep 5191973 = 973495) (by norm_num)
theorem B3461315 : Blo 2307435 3461315 := bstep (se 1 (by rfl) ⟨2595986, by rfl⟩ : syracuseStep 3461315 = 5191973) B5191973
theorem B2307543 : Blo 2307435 2307543 := bstep (se 1 (by rfl) ⟨1730657, by rfl⟩ : syracuseStep 2307543 = 3461315) B3461315
theorem B5840981 : Blo 2307435 5840981 := bbase (se 8 (by rfl) ⟨34224, by rfl⟩ : syracuseStep 5840981 = 68449) (by norm_num)
theorem B3893987 : Blo 2307435 3893987 := bstep (se 1 (by rfl) ⟨2920490, by rfl⟩ : syracuseStep 3893987 = 5840981) B5840981
theorem B2595991 : Blo 2307435 2595991 := bstep (se 1 (by rfl) ⟨1946993, by rfl⟩ : syracuseStep 2595991 = 3893987) B3893987
theorem B3461321 : Blo 2307435 3461321 := bstep (se 2 (by rfl) ⟨1297995, by rfl⟩ : syracuseStep 3461321 = 2595991) B2595991
theorem B2307547 : Blo 2307435 2307547 := bstep (se 1 (by rfl) ⟨1730660, by rfl⟩ : syracuseStep 2307547 = 3461321) B3461321
theorem B5920685 : Blo 2307435 5920685 := bbase (se 3 (by rfl) ⟨1110128, by rfl⟩ : syracuseStep 5920685 = 2220257) (by norm_num)
theorem B3947123 : Blo 2307435 3947123 := bstep (se 1 (by rfl) ⟨2960342, by rfl⟩ : syracuseStep 3947123 = 5920685) B5920685
theorem B2631415 : Blo 2307435 2631415 := bstep (se 1 (by rfl) ⟨1973561, by rfl⟩ : syracuseStep 2631415 = 3947123) B3947123
theorem B3508553 : Blo 2307435 3508553 := bstep (se 2 (by rfl) ⟨1315707, by rfl⟩ : syracuseStep 3508553 = 2631415) B2631415
theorem B9356141 : Blo 2307435 9356141 := bstep (se 3 (by rfl) ⟨1754276, by rfl⟩ : syracuseStep 9356141 = 3508553) B3508553
theorem B6237427 : Blo 2307435 6237427 := bstep (se 1 (by rfl) ⟨4678070, by rfl⟩ : syracuseStep 6237427 = 9356141) B9356141
theorem B8316569 : Blo 2307435 8316569 := bstep (se 2 (by rfl) ⟨3118713, by rfl⟩ : syracuseStep 8316569 = 6237427) B6237427
theorem B5544379 : Blo 2307435 5544379 := bstep (se 1 (by rfl) ⟨4158284, by rfl⟩ : syracuseStep 5544379 = 8316569) B8316569
theorem B7392505 : Blo 2307435 7392505 := bstep (se 2 (by rfl) ⟨2772189, by rfl⟩ : syracuseStep 7392505 = 5544379) B5544379
theorem B9856673 : Blo 2307435 9856673 := bstep (se 2 (by rfl) ⟨3696252, by rfl⟩ : syracuseStep 9856673 = 7392505) B7392505
theorem B6571115 : Blo 2307435 6571115 := bstep (se 1 (by rfl) ⟨4928336, by rfl⟩ : syracuseStep 6571115 = 9856673) B9856673
theorem B4380743 : Blo 2307435 4380743 := bstep (se 1 (by rfl) ⟨3285557, by rfl⟩ : syracuseStep 4380743 = 6571115) B6571115
theorem B11681981 : Blo 2307435 11681981 := bstep (se 3 (by rfl) ⟨2190371, by rfl⟩ : syracuseStep 11681981 = 4380743) B4380743
theorem B7787987 : Blo 2307435 7787987 := bstep (se 1 (by rfl) ⟨5840990, by rfl⟩ : syracuseStep 7787987 = 11681981) B11681981
theorem B5191991 : Blo 2307435 5191991 := bstep (se 1 (by rfl) ⟨3893993, by rfl⟩ : syracuseStep 5191991 = 7787987) B7787987
theorem B3461327 : Blo 2307435 3461327 := bstep (se 1 (by rfl) ⟨2595995, by rfl⟩ : syracuseStep 3461327 = 5191991) B5191991
theorem B2307551 : Blo 2307435 2307551 := bstep (se 1 (by rfl) ⟨1730663, by rfl⟩ : syracuseStep 2307551 = 3461327) B3461327
theorem B3461333 : Blo 2307435 3461333 := bbase (se 7 (by rfl) ⟨40562, by rfl⟩ : syracuseStep 3461333 = 81125) (by norm_num)
theorem B2307555 : Blo 2307435 2307555 := bstep (se 1 (by rfl) ⟨1730666, by rfl⟩ : syracuseStep 2307555 = 3461333) B3461333
theorem B2464177 : Blo 2307435 2464177 := bbase (se 2 (by rfl) ⟨924066, by rfl⟩ : syracuseStep 2464177 = 1848133) (by norm_num)
theorem B3285569 : Blo 2307435 3285569 := bstep (se 2 (by rfl) ⟨1232088, by rfl⟩ : syracuseStep 3285569 = 2464177) B2464177
theorem B8761517 : Blo 2307435 8761517 := bstep (se 3 (by rfl) ⟨1642784, by rfl⟩ : syracuseStep 8761517 = 3285569) B3285569
theorem B5841011 : Blo 2307435 5841011 := bstep (se 1 (by rfl) ⟨4380758, by rfl⟩ : syracuseStep 5841011 = 8761517) B8761517
theorem B3894007 : Blo 2307435 3894007 := bstep (se 1 (by rfl) ⟨2920505, by rfl⟩ : syracuseStep 3894007 = 5841011) B5841011
theorem B5192009 : Blo 2307435 5192009 := bstep (se 2 (by rfl) ⟨1947003, by rfl⟩ : syracuseStep 5192009 = 3894007) B3894007
theorem B3461339 : Blo 2307435 3461339 := bstep (se 1 (by rfl) ⟨2596004, by rfl⟩ : syracuseStep 3461339 = 5192009) B5192009
theorem B2307559 : Blo 2307435 2307559 := bstep (se 1 (by rfl) ⟨1730669, by rfl⟩ : syracuseStep 2307559 = 3461339) B3461339
theorem B2596009 : Blo 2307435 2596009 := bbase (se 2 (by rfl) ⟨973503, by rfl⟩ : syracuseStep 2596009 = 1947007) (by norm_num)
theorem B3461345 : Blo 2307435 3461345 := bstep (se 2 (by rfl) ⟨1298004, by rfl⟩ : syracuseStep 3461345 = 2596009) B2596009
theorem B2307563 : Blo 2307435 2307563 := bstep (se 1 (by rfl) ⟨1730672, by rfl⟩ : syracuseStep 2307563 = 3461345) B3461345
theorem B9856741 : Blo 2307435 9856741 := bbase (se 4 (by rfl) ⟨924069, by rfl⟩ : syracuseStep 9856741 = 1848139) (by norm_num)
theorem B13142321 : Blo 2307435 13142321 := bstep (se 2 (by rfl) ⟨4928370, by rfl⟩ : syracuseStep 13142321 = 9856741) B9856741
theorem B8761547 : Blo 2307435 8761547 := bstep (se 1 (by rfl) ⟨6571160, by rfl⟩ : syracuseStep 8761547 = 13142321) B13142321
theorem B5841031 : Blo 2307435 5841031 := bstep (se 1 (by rfl) ⟨4380773, by rfl⟩ : syracuseStep 5841031 = 8761547) B8761547
theorem B7788041 : Blo 2307435 7788041 := bstep (se 2 (by rfl) ⟨2920515, by rfl⟩ : syracuseStep 7788041 = 5841031) B5841031
theorem B5192027 : Blo 2307435 5192027 := bstep (se 1 (by rfl) ⟨3894020, by rfl⟩ : syracuseStep 5192027 = 7788041) B7788041
theorem B3461351 : Blo 2307435 3461351 := bstep (se 1 (by rfl) ⟨2596013, by rfl⟩ : syracuseStep 3461351 = 5192027) B5192027
theorem B2307567 : Blo 2307435 2307567 := bstep (se 1 (by rfl) ⟨1730675, by rfl⟩ : syracuseStep 2307567 = 3461351) B3461351
theorem B3461357 : Blo 2307435 3461357 := bbase (se 3 (by rfl) ⟨649004, by rfl⟩ : syracuseStep 3461357 = 1298009) (by norm_num)
theorem B2307571 : Blo 2307435 2307571 := bstep (se 1 (by rfl) ⟨1730678, by rfl⟩ : syracuseStep 2307571 = 3461357) B3461357
theorem B5192045 : Blo 2307435 5192045 := bbase (se 3 (by rfl) ⟨973508, by rfl⟩ : syracuseStep 5192045 = 1947017) (by norm_num)
theorem B3461363 : Blo 2307435 3461363 := bstep (se 1 (by rfl) ⟨2596022, by rfl⟩ : syracuseStep 3461363 = 5192045) B5192045
theorem B2307575 : Blo 2307435 2307575 := bstep (se 1 (by rfl) ⟨1730681, by rfl⟩ : syracuseStep 2307575 = 3461363) B3461363
theorem B4380797 : Blo 2307435 4380797 := bbase (se 3 (by rfl) ⟨821399, by rfl⟩ : syracuseStep 4380797 = 1642799) (by norm_num)
theorem B2920531 : Blo 2307435 2920531 := bstep (se 1 (by rfl) ⟨2190398, by rfl⟩ : syracuseStep 2920531 = 4380797) B4380797
theorem B3894041 : Blo 2307435 3894041 := bstep (se 2 (by rfl) ⟨1460265, by rfl⟩ : syracuseStep 3894041 = 2920531) B2920531
theorem B2596027 : Blo 2307435 2596027 := bstep (se 1 (by rfl) ⟨1947020, by rfl⟩ : syracuseStep 2596027 = 3894041) B3894041
theorem B3461369 : Blo 2307435 3461369 := bstep (se 2 (by rfl) ⟨1298013, by rfl⟩ : syracuseStep 3461369 = 2596027) B2596027
theorem B2307579 : Blo 2307435 2307579 := bstep (se 1 (by rfl) ⟨1730684, by rfl⟩ : syracuseStep 2307579 = 3461369) B3461369
theorem B48012373 : Blo 2307435 48012373 := bbase (se 8 (by rfl) ⟨281322, by rfl⟩ : syracuseStep 48012373 = 562645) (by norm_num)
theorem B64016497 : Blo 2307435 64016497 := bstep (se 2 (by rfl) ⟨24006186, by rfl⟩ : syracuseStep 64016497 = 48012373) B48012373
theorem B85355329 : Blo 2307435 85355329 := bstep (se 2 (by rfl) ⟨32008248, by rfl⟩ : syracuseStep 85355329 = 64016497) B64016497
theorem B113807105 : Blo 2307435 113807105 := bstep (se 2 (by rfl) ⟨42677664, by rfl⟩ : syracuseStep 113807105 = 85355329) B85355329
theorem B75871403 : Blo 2307435 75871403 := bstep (se 1 (by rfl) ⟨56903552, by rfl⟩ : syracuseStep 75871403 = 113807105) B113807105
theorem B50580935 : Blo 2307435 50580935 := bstep (se 1 (by rfl) ⟨37935701, by rfl⟩ : syracuseStep 50580935 = 75871403) B75871403
theorem B33720623 : Blo 2307435 33720623 := bstep (se 1 (by rfl) ⟨25290467, by rfl⟩ : syracuseStep 33720623 = 50580935) B50580935
theorem B22480415 : Blo 2307435 22480415 := bstep (se 1 (by rfl) ⟨16860311, by rfl⟩ : syracuseStep 22480415 = 33720623) B33720623
theorem B14986943 : Blo 2307435 14986943 := bstep (se 1 (by rfl) ⟨11240207, by rfl⟩ : syracuseStep 14986943 = 22480415) B22480415
theorem B9991295 : Blo 2307435 9991295 := bstep (se 1 (by rfl) ⟨7493471, by rfl⟩ : syracuseStep 9991295 = 14986943) B14986943
theorem B6660863 : Blo 2307435 6660863 := bstep (se 1 (by rfl) ⟨4995647, by rfl⟩ : syracuseStep 6660863 = 9991295) B9991295
theorem B4440575 : Blo 2307435 4440575 := bstep (se 1 (by rfl) ⟨3330431, by rfl⟩ : syracuseStep 4440575 = 6660863) B6660863
theorem B2960383 : Blo 2307435 2960383 := bstep (se 1 (by rfl) ⟨2220287, by rfl⟩ : syracuseStep 2960383 = 4440575) B4440575
theorem B3947177 : Blo 2307435 3947177 := bstep (se 2 (by rfl) ⟨1480191, by rfl⟩ : syracuseStep 3947177 = 2960383) B2960383
theorem B2631451 : Blo 2307435 2631451 := bstep (se 1 (by rfl) ⟨1973588, by rfl⟩ : syracuseStep 2631451 = 3947177) B3947177
theorem B3508601 : Blo 2307435 3508601 := bstep (se 2 (by rfl) ⟨1315725, by rfl⟩ : syracuseStep 3508601 = 2631451) B2631451
theorem B9356269 : Blo 2307435 9356269 := bstep (se 3 (by rfl) ⟨1754300, by rfl⟩ : syracuseStep 9356269 = 3508601) B3508601
theorem B12475025 : Blo 2307435 12475025 := bstep (se 2 (by rfl) ⟨4678134, by rfl⟩ : syracuseStep 12475025 = 9356269) B9356269
theorem B8316683 : Blo 2307435 8316683 := bstep (se 1 (by rfl) ⟨6237512, by rfl⟩ : syracuseStep 8316683 = 12475025) B12475025
theorem B5544455 : Blo 2307435 5544455 := bstep (se 1 (by rfl) ⟨4158341, by rfl⟩ : syracuseStep 5544455 = 8316683) B8316683
theorem B59140853 : Blo 2307435 59140853 := bstep (se 5 (by rfl) ⟨2772227, by rfl⟩ : syracuseStep 59140853 = 5544455) B5544455
theorem B39427235 : Blo 2307435 39427235 := bstep (se 1 (by rfl) ⟨29570426, by rfl⟩ : syracuseStep 39427235 = 59140853) B59140853
theorem B26284823 : Blo 2307435 26284823 := bstep (se 1 (by rfl) ⟨19713617, by rfl⟩ : syracuseStep 26284823 = 39427235) B39427235
theorem B17523215 : Blo 2307435 17523215 := bstep (se 1 (by rfl) ⟨13142411, by rfl⟩ : syracuseStep 17523215 = 26284823) B26284823
theorem B11682143 : Blo 2307435 11682143 := bstep (se 1 (by rfl) ⟨8761607, by rfl⟩ : syracuseStep 11682143 = 17523215) B17523215
theorem B7788095 : Blo 2307435 7788095 := bstep (se 1 (by rfl) ⟨5841071, by rfl⟩ : syracuseStep 7788095 = 11682143) B11682143
theorem B5192063 : Blo 2307435 5192063 := bstep (se 1 (by rfl) ⟨3894047, by rfl⟩ : syracuseStep 5192063 = 7788095) B7788095
theorem B3461375 : Blo 2307435 3461375 := bstep (se 1 (by rfl) ⟨2596031, by rfl⟩ : syracuseStep 3461375 = 5192063) B5192063
theorem B2307583 : Blo 2307435 2307583 := bstep (se 1 (by rfl) ⟨1730687, by rfl⟩ : syracuseStep 2307583 = 3461375) B3461375
theorem B3461381 : Blo 2307435 3461381 := bbase (se 4 (by rfl) ⟨324504, by rfl⟩ : syracuseStep 3461381 = 649009) (by norm_num)
theorem B2307587 : Blo 2307435 2307587 := bstep (se 1 (by rfl) ⟨1730690, by rfl⟩ : syracuseStep 2307587 = 3461381) B3461381
theorem B3894061 : Blo 2307435 3894061 := bbase (se 3 (by rfl) ⟨730136, by rfl⟩ : syracuseStep 3894061 = 1460273) (by norm_num)
theorem B5192081 : Blo 2307435 5192081 := bstep (se 2 (by rfl) ⟨1947030, by rfl⟩ : syracuseStep 5192081 = 3894061) B3894061
theorem B3461387 : Blo 2307435 3461387 := bstep (se 1 (by rfl) ⟨2596040, by rfl⟩ : syracuseStep 3461387 = 5192081) B5192081
theorem B2307591 : Blo 2307435 2307591 := bstep (se 1 (by rfl) ⟨1730693, by rfl⟩ : syracuseStep 2307591 = 3461387) B3461387
theorem B2596045 : Blo 2307435 2596045 := bbase (se 3 (by rfl) ⟨486758, by rfl⟩ : syracuseStep 2596045 = 973517) (by norm_num)
theorem B3461393 : Blo 2307435 3461393 := bstep (se 2 (by rfl) ⟨1298022, by rfl⟩ : syracuseStep 3461393 = 2596045) B2596045
theorem B2307595 : Blo 2307435 2307595 := bstep (se 1 (by rfl) ⟨1730696, by rfl⟩ : syracuseStep 2307595 = 3461393) B3461393
theorem B7788149 : Blo 2307435 7788149 := bbase (se 5 (by rfl) ⟨365069, by rfl⟩ : syracuseStep 7788149 = 730139) (by norm_num)
theorem B5192099 : Blo 2307435 5192099 := bstep (se 1 (by rfl) ⟨3894074, by rfl⟩ : syracuseStep 5192099 = 7788149) B7788149
theorem B3461399 : Blo 2307435 3461399 := bstep (se 1 (by rfl) ⟨2596049, by rfl⟩ : syracuseStep 3461399 = 5192099) B5192099
theorem B2307599 : Blo 2307435 2307599 := bstep (se 1 (by rfl) ⟨1730699, by rfl⟩ : syracuseStep 2307599 = 3461399) B3461399
theorem B3461405 : Blo 2307435 3461405 := bbase (se 3 (by rfl) ⟨649013, by rfl⟩ : syracuseStep 3461405 = 1298027) (by norm_num)
theorem B2307603 : Blo 2307435 2307603 := bstep (se 1 (by rfl) ⟨1730702, by rfl⟩ : syracuseStep 2307603 = 3461405) B3461405
theorem B5192117 : Blo 2307435 5192117 := bbase (se 5 (by rfl) ⟨243380, by rfl⟩ : syracuseStep 5192117 = 486761) (by norm_num)
theorem B3461411 : Blo 2307435 3461411 := bstep (se 1 (by rfl) ⟨2596058, by rfl⟩ : syracuseStep 3461411 = 5192117) B5192117
theorem B2307607 : Blo 2307435 2307607 := bstep (se 1 (by rfl) ⟨1730705, by rfl⟩ : syracuseStep 2307607 = 3461411) B3461411
theorem B3696349 : Blo 2307435 3696349 := bbase (se 3 (by rfl) ⟨693065, by rfl⟩ : syracuseStep 3696349 = 1386131) (by norm_num)
theorem B4928465 : Blo 2307435 4928465 := bstep (se 2 (by rfl) ⟨1848174, by rfl⟩ : syracuseStep 4928465 = 3696349) B3696349
theorem B13142573 : Blo 2307435 13142573 := bstep (se 3 (by rfl) ⟨2464232, by rfl⟩ : syracuseStep 13142573 = 4928465) B4928465
theorem B8761715 : Blo 2307435 8761715 := bstep (se 1 (by rfl) ⟨6571286, by rfl⟩ : syracuseStep 8761715 = 13142573) B13142573
theorem B5841143 : Blo 2307435 5841143 := bstep (se 1 (by rfl) ⟨4380857, by rfl⟩ : syracuseStep 5841143 = 8761715) B8761715
theorem B3894095 : Blo 2307435 3894095 := bstep (se 1 (by rfl) ⟨2920571, by rfl⟩ : syracuseStep 3894095 = 5841143) B5841143
theorem B2596063 : Blo 2307435 2596063 := bstep (se 1 (by rfl) ⟨1947047, by rfl⟩ : syracuseStep 2596063 = 3894095) B3894095
theorem B3461417 : Blo 2307435 3461417 := bstep (se 2 (by rfl) ⟨1298031, by rfl⟩ : syracuseStep 3461417 = 2596063) B2596063
theorem B2307611 : Blo 2307435 2307611 := bstep (se 1 (by rfl) ⟨1730708, by rfl⟩ : syracuseStep 2307611 = 3461417) B3461417
theorem B5544533 : Blo 2307435 5544533 := bbase (se 8 (by rfl) ⟨32487, by rfl⟩ : syracuseStep 5544533 = 64975) (by norm_num)
theorem B3696355 : Blo 2307435 3696355 := bstep (se 1 (by rfl) ⟨2772266, by rfl⟩ : syracuseStep 3696355 = 5544533) B5544533
theorem B4928473 : Blo 2307435 4928473 := bstep (se 2 (by rfl) ⟨1848177, by rfl⟩ : syracuseStep 4928473 = 3696355) B3696355
theorem B6571297 : Blo 2307435 6571297 := bstep (se 2 (by rfl) ⟨2464236, by rfl⟩ : syracuseStep 6571297 = 4928473) B4928473
theorem B8761729 : Blo 2307435 8761729 := bstep (se 2 (by rfl) ⟨3285648, by rfl⟩ : syracuseStep 8761729 = 6571297) B6571297
theorem B11682305 : Blo 2307435 11682305 := bstep (se 2 (by rfl) ⟨4380864, by rfl⟩ : syracuseStep 11682305 = 8761729) B8761729
theorem B7788203 : Blo 2307435 7788203 := bstep (se 1 (by rfl) ⟨5841152, by rfl⟩ : syracuseStep 7788203 = 11682305) B11682305
theorem B5192135 : Blo 2307435 5192135 := bstep (se 1 (by rfl) ⟨3894101, by rfl⟩ : syracuseStep 5192135 = 7788203) B7788203
theorem B3461423 : Blo 2307435 3461423 := bstep (se 1 (by rfl) ⟨2596067, by rfl⟩ : syracuseStep 3461423 = 5192135) B5192135
theorem B2307615 : Blo 2307435 2307615 := bstep (se 1 (by rfl) ⟨1730711, by rfl⟩ : syracuseStep 2307615 = 3461423) B3461423
theorem B3461429 : Blo 2307435 3461429 := bbase (se 5 (by rfl) ⟨162254, by rfl⟩ : syracuseStep 3461429 = 324509) (by norm_num)
theorem B2307619 : Blo 2307435 2307619 := bstep (se 1 (by rfl) ⟨1730714, by rfl⟩ : syracuseStep 2307619 = 3461429) B3461429
theorem B5841173 : Blo 2307435 5841173 := bbase (se 6 (by rfl) ⟨136902, by rfl⟩ : syracuseStep 5841173 = 273805) (by norm_num)
theorem B3894115 : Blo 2307435 3894115 := bstep (se 1 (by rfl) ⟨2920586, by rfl⟩ : syracuseStep 3894115 = 5841173) B5841173
theorem B5192153 : Blo 2307435 5192153 := bstep (se 2 (by rfl) ⟨1947057, by rfl⟩ : syracuseStep 5192153 = 3894115) B3894115
theorem B3461435 : Blo 2307435 3461435 := bstep (se 1 (by rfl) ⟨2596076, by rfl⟩ : syracuseStep 3461435 = 5192153) B5192153
theorem B2307623 : Blo 2307435 2307623 := bstep (se 1 (by rfl) ⟨1730717, by rfl⟩ : syracuseStep 2307623 = 3461435) B3461435
theorem B2596081 : Blo 2307435 2596081 := bbase (se 2 (by rfl) ⟨973530, by rfl⟩ : syracuseStep 2596081 = 1947061) (by norm_num)
theorem B3461441 : Blo 2307435 3461441 := bstep (se 2 (by rfl) ⟨1298040, by rfl⟩ : syracuseStep 3461441 = 2596081) B2596081
theorem B2307627 : Blo 2307435 2307627 := bstep (se 1 (by rfl) ⟨1730720, by rfl⟩ : syracuseStep 2307627 = 3461441) B3461441
theorem B7017349 : Blo 2307435 7017349 := bbase (se 4 (by rfl) ⟨657876, by rfl⟩ : syracuseStep 7017349 = 1315753) (by norm_num)
theorem B9356465 : Blo 2307435 9356465 := bstep (se 2 (by rfl) ⟨3508674, by rfl⟩ : syracuseStep 9356465 = 7017349) B7017349
theorem B6237643 : Blo 2307435 6237643 := bstep (se 1 (by rfl) ⟨4678232, by rfl⟩ : syracuseStep 6237643 = 9356465) B9356465
theorem B8316857 : Blo 2307435 8316857 := bstep (se 2 (by rfl) ⟨3118821, by rfl⟩ : syracuseStep 8316857 = 6237643) B6237643
theorem B22178285 : Blo 2307435 22178285 := bstep (se 3 (by rfl) ⟨4158428, by rfl⟩ : syracuseStep 22178285 = 8316857) B8316857
theorem B14785523 : Blo 2307435 14785523 := bstep (se 1 (by rfl) ⟨11089142, by rfl⟩ : syracuseStep 14785523 = 22178285) B22178285
theorem B9857015 : Blo 2307435 9857015 := bstep (se 1 (by rfl) ⟨7392761, by rfl⟩ : syracuseStep 9857015 = 14785523) B14785523
theorem B6571343 : Blo 2307435 6571343 := bstep (se 1 (by rfl) ⟨4928507, by rfl⟩ : syracuseStep 6571343 = 9857015) B9857015
theorem B4380895 : Blo 2307435 4380895 := bstep (se 1 (by rfl) ⟨3285671, by rfl⟩ : syracuseStep 4380895 = 6571343) B6571343
theorem B5841193 : Blo 2307435 5841193 := bstep (se 2 (by rfl) ⟨2190447, by rfl⟩ : syracuseStep 5841193 = 4380895) B4380895
theorem B7788257 : Blo 2307435 7788257 := bstep (se 2 (by rfl) ⟨2920596, by rfl⟩ : syracuseStep 7788257 = 5841193) B5841193
theorem B5192171 : Blo 2307435 5192171 := bstep (se 1 (by rfl) ⟨3894128, by rfl⟩ : syracuseStep 5192171 = 7788257) B7788257
theorem B3461447 : Blo 2307435 3461447 := bstep (se 1 (by rfl) ⟨2596085, by rfl⟩ : syracuseStep 3461447 = 5192171) B5192171
theorem B2307631 : Blo 2307435 2307631 := bstep (se 1 (by rfl) ⟨1730723, by rfl⟩ : syracuseStep 2307631 = 3461447) B3461447
theorem B3461453 : Blo 2307435 3461453 := bbase (se 3 (by rfl) ⟨649022, by rfl⟩ : syracuseStep 3461453 = 1298045) (by norm_num)
theorem B2307635 : Blo 2307435 2307635 := bstep (se 1 (by rfl) ⟨1730726, by rfl⟩ : syracuseStep 2307635 = 3461453) B3461453
theorem B5192189 : Blo 2307435 5192189 := bbase (se 3 (by rfl) ⟨973535, by rfl⟩ : syracuseStep 5192189 = 1947071) (by norm_num)
theorem B3461459 : Blo 2307435 3461459 := bstep (se 1 (by rfl) ⟨2596094, by rfl⟩ : syracuseStep 3461459 = 5192189) B5192189
theorem B2307639 : Blo 2307435 2307639 := bstep (se 1 (by rfl) ⟨1730729, by rfl⟩ : syracuseStep 2307639 = 3461459) B3461459
theorem B3894149 : Blo 2307435 3894149 := bbase (se 4 (by rfl) ⟨365076, by rfl⟩ : syracuseStep 3894149 = 730153) (by norm_num)
theorem B2596099 : Blo 2307435 2596099 := bstep (se 1 (by rfl) ⟨1947074, by rfl⟩ : syracuseStep 2596099 = 3894149) B3894149
theorem B3461465 : Blo 2307435 3461465 := bstep (se 2 (by rfl) ⟨1298049, by rfl⟩ : syracuseStep 3461465 = 2596099) B2596099
theorem B2307643 : Blo 2307435 2307643 := bstep (se 1 (by rfl) ⟨1730732, by rfl⟩ : syracuseStep 2307643 = 3461465) B3461465
theorem B17523701 : Blo 2307435 17523701 := bbase (se 5 (by rfl) ⟨821423, by rfl⟩ : syracuseStep 17523701 = 1642847) (by norm_num)
theorem B11682467 : Blo 2307435 11682467 := bstep (se 1 (by rfl) ⟨8761850, by rfl⟩ : syracuseStep 11682467 = 17523701) B17523701
theorem B7788311 : Blo 2307435 7788311 := bstep (se 1 (by rfl) ⟨5841233, by rfl⟩ : syracuseStep 7788311 = 11682467) B11682467
theorem B5192207 : Blo 2307435 5192207 := bstep (se 1 (by rfl) ⟨3894155, by rfl⟩ : syracuseStep 5192207 = 7788311) B7788311
theorem B3461471 : Blo 2307435 3461471 := bstep (se 1 (by rfl) ⟨2596103, by rfl⟩ : syracuseStep 3461471 = 5192207) B5192207
theorem B2307647 : Blo 2307435 2307647 := bstep (se 1 (by rfl) ⟨1730735, by rfl⟩ : syracuseStep 2307647 = 3461471) B3461471
theorem B3461477 : Blo 2307435 3461477 := bbase (se 4 (by rfl) ⟨324513, by rfl⟩ : syracuseStep 3461477 = 649027) (by norm_num)
theorem B2307651 : Blo 2307435 2307651 := bstep (se 1 (by rfl) ⟨1730738, by rfl⟩ : syracuseStep 2307651 = 3461477) B3461477
theorem B4380941 : Blo 2307435 4380941 := bbase (se 3 (by rfl) ⟨821426, by rfl⟩ : syracuseStep 4380941 = 1642853) (by norm_num)
theorem B2920627 : Blo 2307435 2920627 := bstep (se 1 (by rfl) ⟨2190470, by rfl⟩ : syracuseStep 2920627 = 4380941) B4380941
theorem B3894169 : Blo 2307435 3894169 := bstep (se 2 (by rfl) ⟨1460313, by rfl⟩ : syracuseStep 3894169 = 2920627) B2920627
theorem B5192225 : Blo 2307435 5192225 := bstep (se 2 (by rfl) ⟨1947084, by rfl⟩ : syracuseStep 5192225 = 3894169) B3894169
theorem B3461483 : Blo 2307435 3461483 := bstep (se 1 (by rfl) ⟨2596112, by rfl⟩ : syracuseStep 3461483 = 5192225) B5192225
theorem B2307655 : Blo 2307435 2307655 := bstep (se 1 (by rfl) ⟨1730741, by rfl⟩ : syracuseStep 2307655 = 3461483) B3461483
theorem B2596117 : Blo 2307435 2596117 := bbase (se 6 (by rfl) ⟨60846, by rfl⟩ : syracuseStep 2596117 = 121693) (by norm_num)
theorem B3461489 : Blo 2307435 3461489 := bstep (se 2 (by rfl) ⟨1298058, by rfl⟩ : syracuseStep 3461489 = 2596117) B2596117
theorem B2307659 : Blo 2307435 2307659 := bstep (se 1 (by rfl) ⟨1730744, by rfl⟩ : syracuseStep 2307659 = 3461489) B3461489
theorem B2920637 : Blo 2307435 2920637 := bbase (se 3 (by rfl) ⟨547619, by rfl⟩ : syracuseStep 2920637 = 1095239) (by norm_num)
theorem B7788365 : Blo 2307435 7788365 := bstep (se 3 (by rfl) ⟨1460318, by rfl⟩ : syracuseStep 7788365 = 2920637) B2920637
theorem B5192243 : Blo 2307435 5192243 := bstep (se 1 (by rfl) ⟨3894182, by rfl⟩ : syracuseStep 5192243 = 7788365) B7788365
theorem B3461495 : Blo 2307435 3461495 := bstep (se 1 (by rfl) ⟨2596121, by rfl⟩ : syracuseStep 3461495 = 5192243) B5192243
theorem B2307663 : Blo 2307435 2307663 := bstep (se 1 (by rfl) ⟨1730747, by rfl⟩ : syracuseStep 2307663 = 3461495) B3461495
theorem B3461501 : Blo 2307435 3461501 := bbase (se 3 (by rfl) ⟨649031, by rfl⟩ : syracuseStep 3461501 = 1298063) (by norm_num)
theorem B2307667 : Blo 2307435 2307667 := bstep (se 1 (by rfl) ⟨1730750, by rfl⟩ : syracuseStep 2307667 = 3461501) B3461501
theorem B5192261 : Blo 2307435 5192261 := bbase (se 4 (by rfl) ⟨486774, by rfl⟩ : syracuseStep 5192261 = 973549) (by norm_num)
theorem B3461507 : Blo 2307435 3461507 := bstep (se 1 (by rfl) ⟨2596130, by rfl⟩ : syracuseStep 3461507 = 5192261) B5192261
theorem B2307671 : Blo 2307435 2307671 := bstep (se 1 (by rfl) ⟨1730753, by rfl⟩ : syracuseStep 2307671 = 3461507) B3461507
theorem B2464301 : Blo 2307435 2464301 := bbase (se 3 (by rfl) ⟨462056, by rfl⟩ : syracuseStep 2464301 = 924113) (by norm_num)
theorem B6571469 : Blo 2307435 6571469 := bstep (se 3 (by rfl) ⟨1232150, by rfl⟩ : syracuseStep 6571469 = 2464301) B2464301
theorem B4380979 : Blo 2307435 4380979 := bstep (se 1 (by rfl) ⟨3285734, by rfl⟩ : syracuseStep 4380979 = 6571469) B6571469
theorem B5841305 : Blo 2307435 5841305 := bstep (se 2 (by rfl) ⟨2190489, by rfl⟩ : syracuseStep 5841305 = 4380979) B4380979
theorem B3894203 : Blo 2307435 3894203 := bstep (se 1 (by rfl) ⟨2920652, by rfl⟩ : syracuseStep 3894203 = 5841305) B5841305
theorem B2596135 : Blo 2307435 2596135 := bstep (se 1 (by rfl) ⟨1947101, by rfl⟩ : syracuseStep 2596135 = 3894203) B3894203
theorem B3461513 : Blo 2307435 3461513 := bstep (se 2 (by rfl) ⟨1298067, by rfl⟩ : syracuseStep 3461513 = 2596135) B2596135
theorem B2307675 : Blo 2307435 2307675 := bstep (se 1 (by rfl) ⟨1730756, by rfl⟩ : syracuseStep 2307675 = 3461513) B3461513
theorem B11682629 : Blo 2307435 11682629 := bbase (se 4 (by rfl) ⟨1095246, by rfl⟩ : syracuseStep 11682629 = 2190493) (by norm_num)
theorem B7788419 : Blo 2307435 7788419 := bstep (se 1 (by rfl) ⟨5841314, by rfl⟩ : syracuseStep 7788419 = 11682629) B11682629
theorem B5192279 : Blo 2307435 5192279 := bstep (se 1 (by rfl) ⟨3894209, by rfl⟩ : syracuseStep 5192279 = 7788419) B7788419
theorem B3461519 : Blo 2307435 3461519 := bstep (se 1 (by rfl) ⟨2596139, by rfl⟩ : syracuseStep 3461519 = 5192279) B5192279
theorem B2307679 : Blo 2307435 2307679 := bstep (se 1 (by rfl) ⟨1730759, by rfl⟩ : syracuseStep 2307679 = 3461519) B3461519
theorem B3461525 : Blo 2307435 3461525 := bbase (se 6 (by rfl) ⟨81129, by rfl⟩ : syracuseStep 3461525 = 162259) (by norm_num)
theorem B2307683 : Blo 2307435 2307683 := bstep (se 1 (by rfl) ⟨1730762, by rfl⟩ : syracuseStep 2307683 = 3461525) B3461525
theorem B2772353 : Blo 2307435 2772353 := bbase (se 2 (by rfl) ⟨1039632, by rfl⟩ : syracuseStep 2772353 = 2079265) (by norm_num)
theorem B7392941 : Blo 2307435 7392941 := bstep (se 3 (by rfl) ⟨1386176, by rfl⟩ : syracuseStep 7392941 = 2772353) B2772353
theorem B4928627 : Blo 2307435 4928627 := bstep (se 1 (by rfl) ⟨3696470, by rfl⟩ : syracuseStep 4928627 = 7392941) B7392941
theorem B13143005 : Blo 2307435 13143005 := bstep (se 3 (by rfl) ⟨2464313, by rfl⟩ : syracuseStep 13143005 = 4928627) B4928627
theorem B8762003 : Blo 2307435 8762003 := bstep (se 1 (by rfl) ⟨6571502, by rfl⟩ : syracuseStep 8762003 = 13143005) B13143005
theorem B5841335 : Blo 2307435 5841335 := bstep (se 1 (by rfl) ⟨4381001, by rfl⟩ : syracuseStep 5841335 = 8762003) B8762003
theorem B3894223 : Blo 2307435 3894223 := bstep (se 1 (by rfl) ⟨2920667, by rfl⟩ : syracuseStep 3894223 = 5841335) B5841335
theorem B5192297 : Blo 2307435 5192297 := bstep (se 2 (by rfl) ⟨1947111, by rfl⟩ : syracuseStep 5192297 = 3894223) B3894223
theorem B3461531 : Blo 2307435 3461531 := bstep (se 1 (by rfl) ⟨2596148, by rfl⟩ : syracuseStep 3461531 = 5192297) B5192297
theorem B2307687 : Blo 2307435 2307687 := bstep (se 1 (by rfl) ⟨1730765, by rfl⟩ : syracuseStep 2307687 = 3461531) B3461531
theorem B2596153 : Blo 2307435 2596153 := bbase (se 2 (by rfl) ⟨973557, by rfl⟩ : syracuseStep 2596153 = 1947115) (by norm_num)
theorem B3461537 : Blo 2307435 3461537 := bstep (se 2 (by rfl) ⟨1298076, by rfl⟩ : syracuseStep 3461537 = 2596153) B2596153
theorem B2307691 : Blo 2307435 2307691 := bstep (se 1 (by rfl) ⟨1730768, by rfl⟩ : syracuseStep 2307691 = 3461537) B3461537
theorem B6571525 : Blo 2307435 6571525 := bbase (se 4 (by rfl) ⟨616080, by rfl⟩ : syracuseStep 6571525 = 1232161) (by norm_num)
theorem B8762033 : Blo 2307435 8762033 := bstep (se 2 (by rfl) ⟨3285762, by rfl⟩ : syracuseStep 8762033 = 6571525) B6571525
theorem B5841355 : Blo 2307435 5841355 := bstep (se 1 (by rfl) ⟨4381016, by rfl⟩ : syracuseStep 5841355 = 8762033) B8762033
theorem B7788473 : Blo 2307435 7788473 := bstep (se 2 (by rfl) ⟨2920677, by rfl⟩ : syracuseStep 7788473 = 5841355) B5841355
theorem B5192315 : Blo 2307435 5192315 := bstep (se 1 (by rfl) ⟨3894236, by rfl⟩ : syracuseStep 5192315 = 7788473) B7788473
theorem B3461543 : Blo 2307435 3461543 := bstep (se 1 (by rfl) ⟨2596157, by rfl⟩ : syracuseStep 3461543 = 5192315) B5192315
theorem B2307695 : Blo 2307435 2307695 := bstep (se 1 (by rfl) ⟨1730771, by rfl⟩ : syracuseStep 2307695 = 3461543) B3461543
theorem B3461549 : Blo 2307435 3461549 := bbase (se 3 (by rfl) ⟨649040, by rfl⟩ : syracuseStep 3461549 = 1298081) (by norm_num)
theorem B2307699 : Blo 2307435 2307699 := bstep (se 1 (by rfl) ⟨1730774, by rfl⟩ : syracuseStep 2307699 = 3461549) B3461549
theorem B5192333 : Blo 2307435 5192333 := bbase (se 3 (by rfl) ⟨973562, by rfl⟩ : syracuseStep 5192333 = 1947125) (by norm_num)
theorem B3461555 : Blo 2307435 3461555 := bstep (se 1 (by rfl) ⟨2596166, by rfl⟩ : syracuseStep 3461555 = 5192333) B5192333
theorem B2307703 : Blo 2307435 2307703 := bstep (se 1 (by rfl) ⟨1730777, by rfl⟩ : syracuseStep 2307703 = 3461555) B3461555
theorem B2920693 : Blo 2307435 2920693 := bbase (se 5 (by rfl) ⟨136907, by rfl⟩ : syracuseStep 2920693 = 273815) (by norm_num)
theorem B3894257 : Blo 2307435 3894257 := bstep (se 2 (by rfl) ⟨1460346, by rfl⟩ : syracuseStep 3894257 = 2920693) B2920693
theorem B2596171 : Blo 2307435 2596171 := bstep (se 1 (by rfl) ⟨1947128, by rfl⟩ : syracuseStep 2596171 = 3894257) B3894257
theorem B3461561 : Blo 2307435 3461561 := bstep (se 2 (by rfl) ⟨1298085, by rfl⟩ : syracuseStep 3461561 = 2596171) B2596171
theorem B2307707 : Blo 2307435 2307707 := bstep (se 1 (by rfl) ⟨1730780, by rfl⟩ : syracuseStep 2307707 = 3461561) B3461561
theorem B44358101 : Blo 2307435 44358101 := bbase (se 7 (by rfl) ⟨519821, by rfl⟩ : syracuseStep 44358101 = 1039643) (by norm_num)
theorem B29572067 : Blo 2307435 29572067 := bstep (se 1 (by rfl) ⟨22179050, by rfl⟩ : syracuseStep 29572067 = 44358101) B44358101
theorem B19714711 : Blo 2307435 19714711 := bstep (se 1 (by rfl) ⟨14786033, by rfl⟩ : syracuseStep 19714711 = 29572067) B29572067
theorem B26286281 : Blo 2307435 26286281 := bstep (se 2 (by rfl) ⟨9857355, by rfl⟩ : syracuseStep 26286281 = 19714711) B19714711
theorem B17524187 : Blo 2307435 17524187 := bstep (se 1 (by rfl) ⟨13143140, by rfl⟩ : syracuseStep 17524187 = 26286281) B26286281
theorem B11682791 : Blo 2307435 11682791 := bstep (se 1 (by rfl) ⟨8762093, by rfl⟩ : syracuseStep 11682791 = 17524187) B17524187
theorem B7788527 : Blo 2307435 7788527 := bstep (se 1 (by rfl) ⟨5841395, by rfl⟩ : syracuseStep 7788527 = 11682791) B11682791
theorem B5192351 : Blo 2307435 5192351 := bstep (se 1 (by rfl) ⟨3894263, by rfl⟩ : syracuseStep 5192351 = 7788527) B7788527
theorem B3461567 : Blo 2307435 3461567 := bstep (se 1 (by rfl) ⟨2596175, by rfl⟩ : syracuseStep 3461567 = 5192351) B5192351
theorem B2307711 : Blo 2307435 2307711 := bstep (se 1 (by rfl) ⟨1730783, by rfl⟩ : syracuseStep 2307711 = 3461567) B3461567
theorem B3461573 : Blo 2307435 3461573 := bbase (se 4 (by rfl) ⟨324522, by rfl⟩ : syracuseStep 3461573 = 649045) (by norm_num)
theorem B2307715 : Blo 2307435 2307715 := bstep (se 1 (by rfl) ⟨1730786, by rfl⟩ : syracuseStep 2307715 = 3461573) B3461573
theorem B3894277 : Blo 2307435 3894277 := bbase (se 4 (by rfl) ⟨365088, by rfl⟩ : syracuseStep 3894277 = 730177) (by norm_num)
theorem B5192369 : Blo 2307435 5192369 := bstep (se 2 (by rfl) ⟨1947138, by rfl⟩ : syracuseStep 5192369 = 3894277) B3894277
theorem B3461579 : Blo 2307435 3461579 := bstep (se 1 (by rfl) ⟨2596184, by rfl⟩ : syracuseStep 3461579 = 5192369) B5192369
theorem B2307719 : Blo 2307435 2307719 := bstep (se 1 (by rfl) ⟨1730789, by rfl⟩ : syracuseStep 2307719 = 3461579) B3461579
theorem B2596189 : Blo 2307435 2596189 := bbase (se 3 (by rfl) ⟨486785, by rfl⟩ : syracuseStep 2596189 = 973571) (by norm_num)
theorem B3461585 : Blo 2307435 3461585 := bstep (se 2 (by rfl) ⟨1298094, by rfl⟩ : syracuseStep 3461585 = 2596189) B2596189
theorem B2307723 : Blo 2307435 2307723 := bstep (se 1 (by rfl) ⟨1730792, by rfl⟩ : syracuseStep 2307723 = 3461585) B3461585
theorem B7788581 : Blo 2307435 7788581 := bbase (se 4 (by rfl) ⟨730179, by rfl⟩ : syracuseStep 7788581 = 1460359) (by norm_num)
theorem B5192387 : Blo 2307435 5192387 := bstep (se 1 (by rfl) ⟨3894290, by rfl⟩ : syracuseStep 5192387 = 7788581) B7788581
theorem B3461591 : Blo 2307435 3461591 := bstep (se 1 (by rfl) ⟨2596193, by rfl⟩ : syracuseStep 3461591 = 5192387) B5192387
theorem B2307727 : Blo 2307435 2307727 := bstep (se 1 (by rfl) ⟨1730795, by rfl⟩ : syracuseStep 2307727 = 3461591) B3461591
theorem B3461597 : Blo 2307435 3461597 := bbase (se 3 (by rfl) ⟨649049, by rfl⟩ : syracuseStep 3461597 = 1298099) (by norm_num)
theorem B2307731 : Blo 2307435 2307731 := bstep (se 1 (by rfl) ⟨1730798, by rfl⟩ : syracuseStep 2307731 = 3461597) B3461597
theorem B5192405 : Blo 2307435 5192405 := bbase (se 7 (by rfl) ⟨60848, by rfl⟩ : syracuseStep 5192405 = 121697) (by norm_num)
theorem B3461603 : Blo 2307435 3461603 := bstep (se 1 (by rfl) ⟨2596202, by rfl⟩ : syracuseStep 3461603 = 5192405) B5192405
theorem B2307735 : Blo 2307435 2307735 := bstep (se 1 (by rfl) ⟨1730801, by rfl⟩ : syracuseStep 2307735 = 3461603) B3461603
theorem B9857477 : Blo 2307435 9857477 := bbase (se 4 (by rfl) ⟨924138, by rfl⟩ : syracuseStep 9857477 = 1848277) (by norm_num)
theorem B6571651 : Blo 2307435 6571651 := bstep (se 1 (by rfl) ⟨4928738, by rfl⟩ : syracuseStep 6571651 = 9857477) B9857477
theorem B8762201 : Blo 2307435 8762201 := bstep (se 2 (by rfl) ⟨3285825, by rfl⟩ : syracuseStep 8762201 = 6571651) B6571651
theorem B5841467 : Blo 2307435 5841467 := bstep (se 1 (by rfl) ⟨4381100, by rfl⟩ : syracuseStep 5841467 = 8762201) B8762201
theorem B3894311 : Blo 2307435 3894311 := bstep (se 1 (by rfl) ⟨2920733, by rfl⟩ : syracuseStep 3894311 = 5841467) B5841467
theorem B2596207 : Blo 2307435 2596207 := bstep (se 1 (by rfl) ⟨1947155, by rfl⟩ : syracuseStep 2596207 = 3894311) B3894311
theorem B3461609 : Blo 2307435 3461609 := bstep (se 2 (by rfl) ⟨1298103, by rfl⟩ : syracuseStep 3461609 = 2596207) B2596207
theorem B2307739 : Blo 2307435 2307739 := bstep (se 1 (by rfl) ⟨1730804, by rfl⟩ : syracuseStep 2307739 = 3461609) B3461609
theorem B11240981 : Blo 2307435 11240981 := bbase (se 6 (by rfl) ⟨263460, by rfl⟩ : syracuseStep 11240981 = 526921) (by norm_num)
theorem B7493987 : Blo 2307435 7493987 := bstep (se 1 (by rfl) ⟨5620490, by rfl⟩ : syracuseStep 7493987 = 11240981) B11240981
theorem B4995991 : Blo 2307435 4995991 := bstep (se 1 (by rfl) ⟨3746993, by rfl⟩ : syracuseStep 4995991 = 7493987) B7493987
theorem B26645285 : Blo 2307435 26645285 := bstep (se 4 (by rfl) ⟨2497995, by rfl⟩ : syracuseStep 26645285 = 4995991) B4995991
theorem B71054093 : Blo 2307435 71054093 := bstep (se 3 (by rfl) ⟨13322642, by rfl⟩ : syracuseStep 71054093 = 26645285) B26645285
theorem B47369395 : Blo 2307435 47369395 := bstep (se 1 (by rfl) ⟨35527046, by rfl⟩ : syracuseStep 47369395 = 71054093) B71054093
theorem B63159193 : Blo 2307435 63159193 := bstep (se 2 (by rfl) ⟨23684697, by rfl⟩ : syracuseStep 63159193 = 47369395) B47369395
theorem B84212257 : Blo 2307435 84212257 := bstep (se 2 (by rfl) ⟨31579596, by rfl⟩ : syracuseStep 84212257 = 63159193) B63159193
theorem B112283009 : Blo 2307435 112283009 := bstep (se 2 (by rfl) ⟨42106128, by rfl⟩ : syracuseStep 112283009 = 84212257) B84212257
theorem B74855339 : Blo 2307435 74855339 := bstep (se 1 (by rfl) ⟨56141504, by rfl⟩ : syracuseStep 74855339 = 112283009) B112283009
theorem B49903559 : Blo 2307435 49903559 := bstep (se 1 (by rfl) ⟨37427669, by rfl⟩ : syracuseStep 49903559 = 74855339) B74855339
theorem B33269039 : Blo 2307435 33269039 := bstep (se 1 (by rfl) ⟨24951779, by rfl⟩ : syracuseStep 33269039 = 49903559) B49903559
theorem B22179359 : Blo 2307435 22179359 := bstep (se 1 (by rfl) ⟨16634519, by rfl⟩ : syracuseStep 22179359 = 33269039) B33269039
theorem B14786239 : Blo 2307435 14786239 := bstep (se 1 (by rfl) ⟨11089679, by rfl⟩ : syracuseStep 14786239 = 22179359) B22179359
theorem B19714985 : Blo 2307435 19714985 := bstep (se 2 (by rfl) ⟨7393119, by rfl⟩ : syracuseStep 19714985 = 14786239) B14786239
theorem B13143323 : Blo 2307435 13143323 := bstep (se 1 (by rfl) ⟨9857492, by rfl⟩ : syracuseStep 13143323 = 19714985) B19714985
theorem B8762215 : Blo 2307435 8762215 := bstep (se 1 (by rfl) ⟨6571661, by rfl⟩ : syracuseStep 8762215 = 13143323) B13143323
theorem B11682953 : Blo 2307435 11682953 := bstep (se 2 (by rfl) ⟨4381107, by rfl⟩ : syracuseStep 11682953 = 8762215) B8762215
theorem B7788635 : Blo 2307435 7788635 := bstep (se 1 (by rfl) ⟨5841476, by rfl⟩ : syracuseStep 7788635 = 11682953) B11682953
theorem B5192423 : Blo 2307435 5192423 := bstep (se 1 (by rfl) ⟨3894317, by rfl⟩ : syracuseStep 5192423 = 7788635) B7788635
theorem B3461615 : Blo 2307435 3461615 := bstep (se 1 (by rfl) ⟨2596211, by rfl⟩ : syracuseStep 3461615 = 5192423) B5192423
theorem B2307743 : Blo 2307435 2307743 := bstep (se 1 (by rfl) ⟨1730807, by rfl⟩ : syracuseStep 2307743 = 3461615) B3461615
theorem B3461621 : Blo 2307435 3461621 := bbase (se 5 (by rfl) ⟨162263, by rfl⟩ : syracuseStep 3461621 = 324527) (by norm_num)
theorem B2307747 : Blo 2307435 2307747 := bstep (se 1 (by rfl) ⟨1730810, by rfl⟩ : syracuseStep 2307747 = 3461621) B3461621
theorem B6571685 : Blo 2307435 6571685 := bbase (se 4 (by rfl) ⟨616095, by rfl⟩ : syracuseStep 6571685 = 1232191) (by norm_num)
theorem B4381123 : Blo 2307435 4381123 := bstep (se 1 (by rfl) ⟨3285842, by rfl⟩ : syracuseStep 4381123 = 6571685) B6571685
theorem B5841497 : Blo 2307435 5841497 := bstep (se 2 (by rfl) ⟨2190561, by rfl⟩ : syracuseStep 5841497 = 4381123) B4381123
theorem B3894331 : Blo 2307435 3894331 := bstep (se 1 (by rfl) ⟨2920748, by rfl⟩ : syracuseStep 3894331 = 5841497) B5841497
theorem B5192441 : Blo 2307435 5192441 := bstep (se 2 (by rfl) ⟨1947165, by rfl⟩ : syracuseStep 5192441 = 3894331) B3894331
theorem B3461627 : Blo 2307435 3461627 := bstep (se 1 (by rfl) ⟨2596220, by rfl⟩ : syracuseStep 3461627 = 5192441) B5192441
theorem B2307751 : Blo 2307435 2307751 := bstep (se 1 (by rfl) ⟨1730813, by rfl⟩ : syracuseStep 2307751 = 3461627) B3461627
theorem B2596225 : Blo 2307435 2596225 := bbase (se 2 (by rfl) ⟨973584, by rfl⟩ : syracuseStep 2596225 = 1947169) (by norm_num)
theorem B3461633 : Blo 2307435 3461633 := bstep (se 2 (by rfl) ⟨1298112, by rfl⟩ : syracuseStep 3461633 = 2596225) B2596225
theorem B2307755 : Blo 2307435 2307755 := bstep (se 1 (by rfl) ⟨1730816, by rfl⟩ : syracuseStep 2307755 = 3461633) B3461633
theorem B5841517 : Blo 2307435 5841517 := bbase (se 3 (by rfl) ⟨1095284, by rfl⟩ : syracuseStep 5841517 = 2190569) (by norm_num)
theorem B7788689 : Blo 2307435 7788689 := bstep (se 2 (by rfl) ⟨2920758, by rfl⟩ : syracuseStep 7788689 = 5841517) B5841517
theorem B5192459 : Blo 2307435 5192459 := bstep (se 1 (by rfl) ⟨3894344, by rfl⟩ : syracuseStep 5192459 = 7788689) B7788689
theorem B3461639 : Blo 2307435 3461639 := bstep (se 1 (by rfl) ⟨2596229, by rfl⟩ : syracuseStep 3461639 = 5192459) B5192459
theorem B2307759 : Blo 2307435 2307759 := bstep (se 1 (by rfl) ⟨1730819, by rfl⟩ : syracuseStep 2307759 = 3461639) B3461639
theorem B3461645 : Blo 2307435 3461645 := bbase (se 3 (by rfl) ⟨649058, by rfl⟩ : syracuseStep 3461645 = 1298117) (by norm_num)
theorem B2307763 : Blo 2307435 2307763 := bstep (se 1 (by rfl) ⟨1730822, by rfl⟩ : syracuseStep 2307763 = 3461645) B3461645
theorem B5192477 : Blo 2307435 5192477 := bbase (se 3 (by rfl) ⟨973589, by rfl⟩ : syracuseStep 5192477 = 1947179) (by norm_num)
theorem B3461651 : Blo 2307435 3461651 := bstep (se 1 (by rfl) ⟨2596238, by rfl⟩ : syracuseStep 3461651 = 5192477) B5192477
theorem B2307767 : Blo 2307435 2307767 := bstep (se 1 (by rfl) ⟨1730825, by rfl⟩ : syracuseStep 2307767 = 3461651) B3461651
theorem B3894365 : Blo 2307435 3894365 := bbase (se 3 (by rfl) ⟨730193, by rfl⟩ : syracuseStep 3894365 = 1460387) (by norm_num)
theorem B2596243 : Blo 2307435 2596243 := bstep (se 1 (by rfl) ⟨1947182, by rfl⟩ : syracuseStep 2596243 = 3894365) B3894365
theorem B3461657 : Blo 2307435 3461657 := bstep (se 2 (by rfl) ⟨1298121, by rfl⟩ : syracuseStep 3461657 = 2596243) B2596243
theorem B2307771 : Blo 2307435 2307771 := bstep (se 1 (by rfl) ⟨1730828, by rfl⟩ : syracuseStep 2307771 = 3461657) B3461657
theorem B5544917 : Blo 2307435 5544917 := bbase (se 7 (by rfl) ⟨64979, by rfl⟩ : syracuseStep 5544917 = 129959) (by norm_num)
theorem B3696611 : Blo 2307435 3696611 := bstep (se 1 (by rfl) ⟨2772458, by rfl⟩ : syracuseStep 3696611 = 5544917) B5544917
theorem B9857629 : Blo 2307435 9857629 := bstep (se 3 (by rfl) ⟨1848305, by rfl⟩ : syracuseStep 9857629 = 3696611) B3696611
theorem B13143505 : Blo 2307435 13143505 := bstep (se 2 (by rfl) ⟨4928814, by rfl⟩ : syracuseStep 13143505 = 9857629) B9857629
theorem B17524673 : Blo 2307435 17524673 := bstep (se 2 (by rfl) ⟨6571752, by rfl⟩ : syracuseStep 17524673 = 13143505) B13143505
theorem B11683115 : Blo 2307435 11683115 := bstep (se 1 (by rfl) ⟨8762336, by rfl⟩ : syracuseStep 11683115 = 17524673) B17524673
theorem B7788743 : Blo 2307435 7788743 := bstep (se 1 (by rfl) ⟨5841557, by rfl⟩ : syracuseStep 7788743 = 11683115) B11683115
theorem B5192495 : Blo 2307435 5192495 := bstep (se 1 (by rfl) ⟨3894371, by rfl⟩ : syracuseStep 5192495 = 7788743) B7788743
theorem B3461663 : Blo 2307435 3461663 := bstep (se 1 (by rfl) ⟨2596247, by rfl⟩ : syracuseStep 3461663 = 5192495) B5192495
theorem B2307775 : Blo 2307435 2307775 := bstep (se 1 (by rfl) ⟨1730831, by rfl⟩ : syracuseStep 2307775 = 3461663) B3461663
theorem B3461669 : Blo 2307435 3461669 := bbase (se 4 (by rfl) ⟨324531, by rfl⟩ : syracuseStep 3461669 = 649063) (by norm_num)
theorem B2307779 : Blo 2307435 2307779 := bstep (se 1 (by rfl) ⟨1730834, by rfl⟩ : syracuseStep 2307779 = 3461669) B3461669
theorem B2920789 : Blo 2307435 2920789 := bbase (se 10 (by rfl) ⟨4278, by rfl⟩ : syracuseStep 2920789 = 8557) (by norm_num)
theorem B3894385 : Blo 2307435 3894385 := bstep (se 2 (by rfl) ⟨1460394, by rfl⟩ : syracuseStep 3894385 = 2920789) B2920789
theorem B5192513 : Blo 2307435 5192513 := bstep (se 2 (by rfl) ⟨1947192, by rfl⟩ : syracuseStep 5192513 = 3894385) B3894385
theorem B3461675 : Blo 2307435 3461675 := bstep (se 1 (by rfl) ⟨2596256, by rfl⟩ : syracuseStep 3461675 = 5192513) B5192513
theorem B2307783 : Blo 2307435 2307783 := bstep (se 1 (by rfl) ⟨1730837, by rfl⟩ : syracuseStep 2307783 = 3461675) B3461675
theorem B2596261 : Blo 2307435 2596261 := bbase (se 4 (by rfl) ⟨243399, by rfl⟩ : syracuseStep 2596261 = 486799) (by norm_num)
theorem B3461681 : Blo 2307435 3461681 := bstep (se 2 (by rfl) ⟨1298130, by rfl⟩ : syracuseStep 3461681 = 2596261) B2596261
theorem B2307787 : Blo 2307435 2307787 := bstep (se 1 (by rfl) ⟨1730840, by rfl⟩ : syracuseStep 2307787 = 3461681) B3461681
theorem B14786549 : Blo 2307435 14786549 := bbase (se 5 (by rfl) ⟨693119, by rfl⟩ : syracuseStep 14786549 = 1386239) (by norm_num)
theorem B9857699 : Blo 2307435 9857699 := bstep (se 1 (by rfl) ⟨7393274, by rfl⟩ : syracuseStep 9857699 = 14786549) B14786549
theorem B6571799 : Blo 2307435 6571799 := bstep (se 1 (by rfl) ⟨4928849, by rfl⟩ : syracuseStep 6571799 = 9857699) B9857699
theorem B4381199 : Blo 2307435 4381199 := bstep (se 1 (by rfl) ⟨3285899, by rfl⟩ : syracuseStep 4381199 = 6571799) B6571799
theorem B2920799 : Blo 2307435 2920799 := bstep (se 1 (by rfl) ⟨2190599, by rfl⟩ : syracuseStep 2920799 = 4381199) B4381199
theorem B7788797 : Blo 2307435 7788797 := bstep (se 3 (by rfl) ⟨1460399, by rfl⟩ : syracuseStep 7788797 = 2920799) B2920799
theorem B5192531 : Blo 2307435 5192531 := bstep (se 1 (by rfl) ⟨3894398, by rfl⟩ : syracuseStep 5192531 = 7788797) B7788797
theorem B3461687 : Blo 2307435 3461687 := bstep (se 1 (by rfl) ⟨2596265, by rfl⟩ : syracuseStep 3461687 = 5192531) B5192531
theorem B2307791 : Blo 2307435 2307791 := bstep (se 1 (by rfl) ⟨1730843, by rfl⟩ : syracuseStep 2307791 = 3461687) B3461687
theorem B3461693 : Blo 2307435 3461693 := bbase (se 3 (by rfl) ⟨649067, by rfl⟩ : syracuseStep 3461693 = 1298135) (by norm_num)
theorem B2307795 : Blo 2307435 2307795 := bstep (se 1 (by rfl) ⟨1730846, by rfl⟩ : syracuseStep 2307795 = 3461693) B3461693
theorem B5192549 : Blo 2307435 5192549 := bbase (se 4 (by rfl) ⟨486801, by rfl⟩ : syracuseStep 5192549 = 973603) (by norm_num)
theorem B3461699 : Blo 2307435 3461699 := bstep (se 1 (by rfl) ⟨2596274, by rfl⟩ : syracuseStep 3461699 = 5192549) B5192549
theorem B2307799 : Blo 2307435 2307799 := bstep (se 1 (by rfl) ⟨1730849, by rfl⟩ : syracuseStep 2307799 = 3461699) B3461699
theorem B5841629 : Blo 2307435 5841629 := bbase (se 3 (by rfl) ⟨1095305, by rfl⟩ : syracuseStep 5841629 = 2190611) (by norm_num)
theorem B3894419 : Blo 2307435 3894419 := bstep (se 1 (by rfl) ⟨2920814, by rfl⟩ : syracuseStep 3894419 = 5841629) B5841629
theorem B2596279 : Blo 2307435 2596279 := bstep (se 1 (by rfl) ⟨1947209, by rfl⟩ : syracuseStep 2596279 = 3894419) B3894419
theorem B3461705 : Blo 2307435 3461705 := bstep (se 2 (by rfl) ⟨1298139, by rfl⟩ : syracuseStep 3461705 = 2596279) B2596279
theorem B2307803 : Blo 2307435 2307803 := bstep (se 1 (by rfl) ⟨1730852, by rfl⟩ : syracuseStep 2307803 = 3461705) B3461705
theorem B4381229 : Blo 2307435 4381229 := bbase (se 3 (by rfl) ⟨821480, by rfl⟩ : syracuseStep 4381229 = 1642961) (by norm_num)
theorem B11683277 : Blo 2307435 11683277 := bstep (se 3 (by rfl) ⟨2190614, by rfl⟩ : syracuseStep 11683277 = 4381229) B4381229
theorem B7788851 : Blo 2307435 7788851 := bstep (se 1 (by rfl) ⟨5841638, by rfl⟩ : syracuseStep 7788851 = 11683277) B11683277
theorem B5192567 : Blo 2307435 5192567 := bstep (se 1 (by rfl) ⟨3894425, by rfl⟩ : syracuseStep 5192567 = 7788851) B7788851
theorem B3461711 : Blo 2307435 3461711 := bstep (se 1 (by rfl) ⟨2596283, by rfl⟩ : syracuseStep 3461711 = 5192567) B5192567
theorem B2307807 : Blo 2307435 2307807 := bstep (se 1 (by rfl) ⟨1730855, by rfl⟩ : syracuseStep 2307807 = 3461711) B3461711
theorem B3461717 : Blo 2307435 3461717 := bbase (se 8 (by rfl) ⟨20283, by rfl⟩ : syracuseStep 3461717 = 40567) (by norm_num)
theorem B2307811 : Blo 2307435 2307811 := bstep (se 1 (by rfl) ⟨1730858, by rfl⟩ : syracuseStep 2307811 = 3461717) B3461717
theorem B3556829 : Blo 2307435 3556829 := bbase (se 3 (by rfl) ⟨666905, by rfl⟩ : syracuseStep 3556829 = 1333811) (by norm_num)
theorem B9484877 : Blo 2307435 9484877 := bstep (se 3 (by rfl) ⟨1778414, by rfl⟩ : syracuseStep 9484877 = 3556829) B3556829
theorem B25293005 : Blo 2307435 25293005 := bstep (se 3 (by rfl) ⟨4742438, by rfl⟩ : syracuseStep 25293005 = 9484877) B9484877
theorem B16862003 : Blo 2307435 16862003 := bstep (se 1 (by rfl) ⟨12646502, by rfl⟩ : syracuseStep 16862003 = 25293005) B25293005
theorem B11241335 : Blo 2307435 11241335 := bstep (se 1 (by rfl) ⟨8431001, by rfl⟩ : syracuseStep 11241335 = 16862003) B16862003
theorem B7494223 : Blo 2307435 7494223 := bstep (se 1 (by rfl) ⟨5620667, by rfl⟩ : syracuseStep 7494223 = 11241335) B11241335
theorem B9992297 : Blo 2307435 9992297 := bstep (se 2 (by rfl) ⟨3747111, by rfl⟩ : syracuseStep 9992297 = 7494223) B7494223
theorem B6661531 : Blo 2307435 6661531 := bstep (se 1 (by rfl) ⟨4996148, by rfl⟩ : syracuseStep 6661531 = 9992297) B9992297
theorem B35528165 : Blo 2307435 35528165 := bstep (se 4 (by rfl) ⟨3330765, by rfl⟩ : syracuseStep 35528165 = 6661531) B6661531
theorem B23685443 : Blo 2307435 23685443 := bstep (se 1 (by rfl) ⟨17764082, by rfl⟩ : syracuseStep 23685443 = 35528165) B35528165
theorem B15790295 : Blo 2307435 15790295 := bstep (se 1 (by rfl) ⟨11842721, by rfl⟩ : syracuseStep 15790295 = 23685443) B23685443
theorem B10526863 : Blo 2307435 10526863 := bstep (se 1 (by rfl) ⟨7895147, by rfl⟩ : syracuseStep 10526863 = 15790295) B15790295
theorem B14035817 : Blo 2307435 14035817 := bstep (se 2 (by rfl) ⟨5263431, by rfl⟩ : syracuseStep 14035817 = 10526863) B10526863
theorem B9357211 : Blo 2307435 9357211 := bstep (se 1 (by rfl) ⟨7017908, by rfl⟩ : syracuseStep 9357211 = 14035817) B14035817
theorem B12476281 : Blo 2307435 12476281 := bstep (se 2 (by rfl) ⟨4678605, by rfl⟩ : syracuseStep 12476281 = 9357211) B9357211
theorem B16635041 : Blo 2307435 16635041 := bstep (se 2 (by rfl) ⟨6238140, by rfl⟩ : syracuseStep 16635041 = 12476281) B12476281
theorem B11090027 : Blo 2307435 11090027 := bstep (se 1 (by rfl) ⟨8317520, by rfl⟩ : syracuseStep 11090027 = 16635041) B16635041
theorem B7393351 : Blo 2307435 7393351 := bstep (se 1 (by rfl) ⟨5545013, by rfl⟩ : syracuseStep 7393351 = 11090027) B11090027
theorem B9857801 : Blo 2307435 9857801 := bstep (se 2 (by rfl) ⟨3696675, by rfl⟩ : syracuseStep 9857801 = 7393351) B7393351
theorem B6571867 : Blo 2307435 6571867 := bstep (se 1 (by rfl) ⟨4928900, by rfl⟩ : syracuseStep 6571867 = 9857801) B9857801
theorem B8762489 : Blo 2307435 8762489 := bstep (se 2 (by rfl) ⟨3285933, by rfl⟩ : syracuseStep 8762489 = 6571867) B6571867
theorem B5841659 : Blo 2307435 5841659 := bstep (se 1 (by rfl) ⟨4381244, by rfl⟩ : syracuseStep 5841659 = 8762489) B8762489
theorem B3894439 : Blo 2307435 3894439 := bstep (se 1 (by rfl) ⟨2920829, by rfl⟩ : syracuseStep 3894439 = 5841659) B5841659
theorem B5192585 : Blo 2307435 5192585 := bstep (se 2 (by rfl) ⟨1947219, by rfl⟩ : syracuseStep 5192585 = 3894439) B3894439
theorem B3461723 : Blo 2307435 3461723 := bstep (se 1 (by rfl) ⟨2596292, by rfl⟩ : syracuseStep 3461723 = 5192585) B5192585
theorem B2307815 : Blo 2307435 2307815 := bstep (se 1 (by rfl) ⟨1730861, by rfl⟩ : syracuseStep 2307815 = 3461723) B3461723
theorem B2596297 : Blo 2307435 2596297 := bbase (se 2 (by rfl) ⟨973611, by rfl⟩ : syracuseStep 2596297 = 1947223) (by norm_num)
theorem B3461729 : Blo 2307435 3461729 := bstep (se 2 (by rfl) ⟨1298148, by rfl⟩ : syracuseStep 3461729 = 2596297) B2596297
theorem B2307819 : Blo 2307435 2307819 := bstep (se 1 (by rfl) ⟨1730864, by rfl⟩ : syracuseStep 2307819 = 3461729) B3461729
theorem B19715669 : Blo 2307435 19715669 := bbase (se 8 (by rfl) ⟨115521, by rfl⟩ : syracuseStep 19715669 = 231043) (by norm_num)
theorem B13143779 : Blo 2307435 13143779 := bstep (se 1 (by rfl) ⟨9857834, by rfl⟩ : syracuseStep 13143779 = 19715669) B19715669
theorem B8762519 : Blo 2307435 8762519 := bstep (se 1 (by rfl) ⟨6571889, by rfl⟩ : syracuseStep 8762519 = 13143779) B13143779
theorem B5841679 : Blo 2307435 5841679 := bstep (se 1 (by rfl) ⟨4381259, by rfl⟩ : syracuseStep 5841679 = 8762519) B8762519
theorem B7788905 : Blo 2307435 7788905 := bstep (se 2 (by rfl) ⟨2920839, by rfl⟩ : syracuseStep 7788905 = 5841679) B5841679
theorem B5192603 : Blo 2307435 5192603 := bstep (se 1 (by rfl) ⟨3894452, by rfl⟩ : syracuseStep 5192603 = 7788905) B7788905
theorem B3461735 : Blo 2307435 3461735 := bstep (se 1 (by rfl) ⟨2596301, by rfl⟩ : syracuseStep 3461735 = 5192603) B5192603
theorem B2307823 : Blo 2307435 2307823 := bstep (se 1 (by rfl) ⟨1730867, by rfl⟩ : syracuseStep 2307823 = 3461735) B3461735
theorem B3461741 : Blo 2307435 3461741 := bbase (se 3 (by rfl) ⟨649076, by rfl⟩ : syracuseStep 3461741 = 1298153) (by norm_num)
theorem B2307827 : Blo 2307435 2307827 := bstep (se 1 (by rfl) ⟨1730870, by rfl⟩ : syracuseStep 2307827 = 3461741) B3461741
theorem B5192621 : Blo 2307435 5192621 := bbase (se 3 (by rfl) ⟨973616, by rfl⟩ : syracuseStep 5192621 = 1947233) (by norm_num)
theorem B3461747 : Blo 2307435 3461747 := bstep (se 1 (by rfl) ⟨2596310, by rfl⟩ : syracuseStep 3461747 = 5192621) B5192621
theorem B2307831 : Blo 2307435 2307831 := bstep (se 1 (by rfl) ⟨1730873, by rfl⟩ : syracuseStep 2307831 = 3461747) B3461747
theorem B6571925 : Blo 2307435 6571925 := bbase (se 6 (by rfl) ⟨154029, by rfl⟩ : syracuseStep 6571925 = 308059) (by norm_num)
theorem B4381283 : Blo 2307435 4381283 := bstep (se 1 (by rfl) ⟨3285962, by rfl⟩ : syracuseStep 4381283 = 6571925) B6571925
theorem B2920855 : Blo 2307435 2920855 := bstep (se 1 (by rfl) ⟨2190641, by rfl⟩ : syracuseStep 2920855 = 4381283) B4381283
theorem B3894473 : Blo 2307435 3894473 := bstep (se 2 (by rfl) ⟨1460427, by rfl⟩ : syracuseStep 3894473 = 2920855) B2920855
theorem B2596315 : Blo 2307435 2596315 := bstep (se 1 (by rfl) ⟨1947236, by rfl⟩ : syracuseStep 2596315 = 3894473) B3894473
theorem B3461753 : Blo 2307435 3461753 := bstep (se 2 (by rfl) ⟨1298157, by rfl⟩ : syracuseStep 3461753 = 2596315) B2596315
theorem B2307835 : Blo 2307435 2307835 := bstep (se 1 (by rfl) ⟨1730876, by rfl⟩ : syracuseStep 2307835 = 3461753) B3461753
theorem B33270421 : Blo 2307435 33270421 := bbase (se 6 (by rfl) ⟨779775, by rfl⟩ : syracuseStep 33270421 = 1559551) (by norm_num)
theorem B44360561 : Blo 2307435 44360561 := bstep (se 2 (by rfl) ⟨16635210, by rfl⟩ : syracuseStep 44360561 = 33270421) B33270421
theorem B29573707 : Blo 2307435 29573707 := bstep (se 1 (by rfl) ⟨22180280, by rfl⟩ : syracuseStep 29573707 = 44360561) B44360561
theorem B39431609 : Blo 2307435 39431609 := bstep (se 2 (by rfl) ⟨14786853, by rfl⟩ : syracuseStep 39431609 = 29573707) B29573707
theorem B26287739 : Blo 2307435 26287739 := bstep (se 1 (by rfl) ⟨19715804, by rfl⟩ : syracuseStep 26287739 = 39431609) B39431609
theorem B17525159 : Blo 2307435 17525159 := bstep (se 1 (by rfl) ⟨13143869, by rfl⟩ : syracuseStep 17525159 = 26287739) B26287739
theorem B11683439 : Blo 2307435 11683439 := bstep (se 1 (by rfl) ⟨8762579, by rfl⟩ : syracuseStep 11683439 = 17525159) B17525159
theorem B7788959 : Blo 2307435 7788959 := bstep (se 1 (by rfl) ⟨5841719, by rfl⟩ : syracuseStep 7788959 = 11683439) B11683439
theorem B5192639 : Blo 2307435 5192639 := bstep (se 1 (by rfl) ⟨3894479, by rfl⟩ : syracuseStep 5192639 = 7788959) B7788959
theorem B3461759 : Blo 2307435 3461759 := bstep (se 1 (by rfl) ⟨2596319, by rfl⟩ : syracuseStep 3461759 = 5192639) B5192639
theorem B2307839 : Blo 2307435 2307839 := bstep (se 1 (by rfl) ⟨1730879, by rfl⟩ : syracuseStep 2307839 = 3461759) B3461759
theorem B3461765 : Blo 2307435 3461765 := bbase (se 4 (by rfl) ⟨324540, by rfl⟩ : syracuseStep 3461765 = 649081) (by norm_num)
theorem B2307843 : Blo 2307435 2307843 := bstep (se 1 (by rfl) ⟨1730882, by rfl⟩ : syracuseStep 2307843 = 3461765) B3461765
theorem B3894493 : Blo 2307435 3894493 := bbase (se 3 (by rfl) ⟨730217, by rfl⟩ : syracuseStep 3894493 = 1460435) (by norm_num)
theorem B5192657 : Blo 2307435 5192657 := bstep (se 2 (by rfl) ⟨1947246, by rfl⟩ : syracuseStep 5192657 = 3894493) B3894493
theorem B3461771 : Blo 2307435 3461771 := bstep (se 1 (by rfl) ⟨2596328, by rfl⟩ : syracuseStep 3461771 = 5192657) B5192657
theorem B2307847 : Blo 2307435 2307847 := bstep (se 1 (by rfl) ⟨1730885, by rfl⟩ : syracuseStep 2307847 = 3461771) B3461771
theorem B2596333 : Blo 2307435 2596333 := bbase (se 3 (by rfl) ⟨486812, by rfl⟩ : syracuseStep 2596333 = 973625) (by norm_num)
theorem B3461777 : Blo 2307435 3461777 := bstep (se 2 (by rfl) ⟨1298166, by rfl⟩ : syracuseStep 3461777 = 2596333) B2596333
theorem B2307851 : Blo 2307435 2307851 := bstep (se 1 (by rfl) ⟨1730888, by rfl⟩ : syracuseStep 2307851 = 3461777) B3461777
theorem B7789013 : Blo 2307435 7789013 := bbase (se 7 (by rfl) ⟨91277, by rfl⟩ : syracuseStep 7789013 = 182555) (by norm_num)
theorem B5192675 : Blo 2307435 5192675 := bstep (se 1 (by rfl) ⟨3894506, by rfl⟩ : syracuseStep 5192675 = 7789013) B7789013
theorem B3461783 : Blo 2307435 3461783 := bstep (se 1 (by rfl) ⟨2596337, by rfl⟩ : syracuseStep 3461783 = 5192675) B5192675
theorem B2307855 : Blo 2307435 2307855 := bstep (se 1 (by rfl) ⟨1730891, by rfl⟩ : syracuseStep 2307855 = 3461783) B3461783
theorem B3461789 : Blo 2307435 3461789 := bbase (se 3 (by rfl) ⟨649085, by rfl⟩ : syracuseStep 3461789 = 1298171) (by norm_num)
theorem B2307859 : Blo 2307435 2307859 := bstep (se 1 (by rfl) ⟨1730894, by rfl⟩ : syracuseStep 2307859 = 3461789) B3461789
theorem B5192693 : Blo 2307435 5192693 := bbase (se 5 (by rfl) ⟨243407, by rfl⟩ : syracuseStep 5192693 = 486815) (by norm_num)
theorem B3461795 : Blo 2307435 3461795 := bstep (se 1 (by rfl) ⟨2596346, by rfl⟩ : syracuseStep 3461795 = 5192693) B5192693
theorem B2307863 : Blo 2307435 2307863 := bstep (se 1 (by rfl) ⟨1730897, by rfl⟩ : syracuseStep 2307863 = 3461795) B3461795
theorem B3747197 : Blo 2307435 3747197 := bbase (se 3 (by rfl) ⟨702599, by rfl⟩ : syracuseStep 3747197 = 1405199) (by norm_num)
theorem B2498131 : Blo 2307435 2498131 := bstep (se 1 (by rfl) ⟨1873598, by rfl⟩ : syracuseStep 2498131 = 3747197) B3747197
theorem B13323365 : Blo 2307435 13323365 := bstep (se 4 (by rfl) ⟨1249065, by rfl⟩ : syracuseStep 13323365 = 2498131) B2498131
theorem B8882243 : Blo 2307435 8882243 := bstep (se 1 (by rfl) ⟨6661682, by rfl⟩ : syracuseStep 8882243 = 13323365) B13323365
theorem B5921495 : Blo 2307435 5921495 := bstep (se 1 (by rfl) ⟨4441121, by rfl⟩ : syracuseStep 5921495 = 8882243) B8882243
theorem B3947663 : Blo 2307435 3947663 := bstep (se 1 (by rfl) ⟨2960747, by rfl⟩ : syracuseStep 3947663 = 5921495) B5921495
theorem B2631775 : Blo 2307435 2631775 := bstep (se 1 (by rfl) ⟨1973831, by rfl⟩ : syracuseStep 2631775 = 3947663) B3947663
theorem B3509033 : Blo 2307435 3509033 := bstep (se 2 (by rfl) ⟨1315887, by rfl⟩ : syracuseStep 3509033 = 2631775) B2631775
theorem B37429685 : Blo 2307435 37429685 := bstep (se 5 (by rfl) ⟨1754516, by rfl⟩ : syracuseStep 37429685 = 3509033) B3509033
theorem B24953123 : Blo 2307435 24953123 := bstep (se 1 (by rfl) ⟨18714842, by rfl⟩ : syracuseStep 24953123 = 37429685) B37429685
theorem B66541661 : Blo 2307435 66541661 := bstep (se 3 (by rfl) ⟨12476561, by rfl⟩ : syracuseStep 66541661 = 24953123) B24953123
theorem B44361107 : Blo 2307435 44361107 := bstep (se 1 (by rfl) ⟨33270830, by rfl⟩ : syracuseStep 44361107 = 66541661) B66541661
theorem B29574071 : Blo 2307435 29574071 := bstep (se 1 (by rfl) ⟨22180553, by rfl⟩ : syracuseStep 29574071 = 44361107) B44361107
theorem B19716047 : Blo 2307435 19716047 := bstep (se 1 (by rfl) ⟨14787035, by rfl⟩ : syracuseStep 19716047 = 29574071) B29574071
theorem B13144031 : Blo 2307435 13144031 := bstep (se 1 (by rfl) ⟨9858023, by rfl⟩ : syracuseStep 13144031 = 19716047) B19716047
theorem B8762687 : Blo 2307435 8762687 := bstep (se 1 (by rfl) ⟨6572015, by rfl⟩ : syracuseStep 8762687 = 13144031) B13144031
theorem B5841791 : Blo 2307435 5841791 := bstep (se 1 (by rfl) ⟨4381343, by rfl⟩ : syracuseStep 5841791 = 8762687) B8762687
theorem B3894527 : Blo 2307435 3894527 := bstep (se 1 (by rfl) ⟨2920895, by rfl⟩ : syracuseStep 3894527 = 5841791) B5841791
theorem B2596351 : Blo 2307435 2596351 := bstep (se 1 (by rfl) ⟨1947263, by rfl⟩ : syracuseStep 2596351 = 3894527) B3894527
theorem B3461801 : Blo 2307435 3461801 := bstep (se 2 (by rfl) ⟨1298175, by rfl⟩ : syracuseStep 3461801 = 2596351) B2596351
theorem B2307867 : Blo 2307435 2307867 := bstep (se 1 (by rfl) ⟨1730900, by rfl⟩ : syracuseStep 2307867 = 3461801) B3461801
theorem B3286013 : Blo 2307435 3286013 := bbase (se 3 (by rfl) ⟨616127, by rfl⟩ : syracuseStep 3286013 = 1232255) (by norm_num)
theorem B8762701 : Blo 2307435 8762701 := bstep (se 3 (by rfl) ⟨1643006, by rfl⟩ : syracuseStep 8762701 = 3286013) B3286013
theorem B11683601 : Blo 2307435 11683601 := bstep (se 2 (by rfl) ⟨4381350, by rfl⟩ : syracuseStep 11683601 = 8762701) B8762701
theorem B7789067 : Blo 2307435 7789067 := bstep (se 1 (by rfl) ⟨5841800, by rfl⟩ : syracuseStep 7789067 = 11683601) B11683601
theorem B5192711 : Blo 2307435 5192711 := bstep (se 1 (by rfl) ⟨3894533, by rfl⟩ : syracuseStep 5192711 = 7789067) B7789067
theorem B3461807 : Blo 2307435 3461807 := bstep (se 1 (by rfl) ⟨2596355, by rfl⟩ : syracuseStep 3461807 = 5192711) B5192711
theorem B2307871 : Blo 2307435 2307871 := bstep (se 1 (by rfl) ⟨1730903, by rfl⟩ : syracuseStep 2307871 = 3461807) B3461807
theorem B3461813 : Blo 2307435 3461813 := bbase (se 5 (by rfl) ⟨162272, by rfl⟩ : syracuseStep 3461813 = 324545) (by norm_num)
theorem B2307875 : Blo 2307435 2307875 := bstep (se 1 (by rfl) ⟨1730906, by rfl⟩ : syracuseStep 2307875 = 3461813) B3461813
theorem B5841821 : Blo 2307435 5841821 := bbase (se 3 (by rfl) ⟨1095341, by rfl⟩ : syracuseStep 5841821 = 2190683) (by norm_num)
theorem B3894547 : Blo 2307435 3894547 := bstep (se 1 (by rfl) ⟨2920910, by rfl⟩ : syracuseStep 3894547 = 5841821) B5841821
theorem B5192729 : Blo 2307435 5192729 := bstep (se 2 (by rfl) ⟨1947273, by rfl⟩ : syracuseStep 5192729 = 3894547) B3894547
theorem B3461819 : Blo 2307435 3461819 := bstep (se 1 (by rfl) ⟨2596364, by rfl⟩ : syracuseStep 3461819 = 5192729) B5192729
theorem B2307879 : Blo 2307435 2307879 := bstep (se 1 (by rfl) ⟨1730909, by rfl⟩ : syracuseStep 2307879 = 3461819) B3461819
theorem B2596369 : Blo 2307435 2596369 := bbase (se 2 (by rfl) ⟨973638, by rfl⟩ : syracuseStep 2596369 = 1947277) (by norm_num)
theorem B3461825 : Blo 2307435 3461825 := bstep (se 2 (by rfl) ⟨1298184, by rfl⟩ : syracuseStep 3461825 = 2596369) B2596369
theorem B2307883 : Blo 2307435 2307883 := bstep (se 1 (by rfl) ⟨1730912, by rfl⟩ : syracuseStep 2307883 = 3461825) B3461825
theorem B4381381 : Blo 2307435 4381381 := bbase (se 4 (by rfl) ⟨410754, by rfl⟩ : syracuseStep 4381381 = 821509) (by norm_num)
theorem B5841841 : Blo 2307435 5841841 := bstep (se 2 (by rfl) ⟨2190690, by rfl⟩ : syracuseStep 5841841 = 4381381) B4381381
theorem B7789121 : Blo 2307435 7789121 := bstep (se 2 (by rfl) ⟨2920920, by rfl⟩ : syracuseStep 7789121 = 5841841) B5841841
theorem B5192747 : Blo 2307435 5192747 := bstep (se 1 (by rfl) ⟨3894560, by rfl⟩ : syracuseStep 5192747 = 7789121) B7789121
theorem B3461831 : Blo 2307435 3461831 := bstep (se 1 (by rfl) ⟨2596373, by rfl⟩ : syracuseStep 3461831 = 5192747) B5192747
theorem B2307887 : Blo 2307435 2307887 := bstep (se 1 (by rfl) ⟨1730915, by rfl⟩ : syracuseStep 2307887 = 3461831) B3461831
theorem B3461837 : Blo 2307435 3461837 := bbase (se 3 (by rfl) ⟨649094, by rfl⟩ : syracuseStep 3461837 = 1298189) (by norm_num)
theorem B2307891 : Blo 2307435 2307891 := bstep (se 1 (by rfl) ⟨1730918, by rfl⟩ : syracuseStep 2307891 = 3461837) B3461837
theorem B5192765 : Blo 2307435 5192765 := bbase (se 3 (by rfl) ⟨973643, by rfl⟩ : syracuseStep 5192765 = 1947287) (by norm_num)
theorem B3461843 : Blo 2307435 3461843 := bstep (se 1 (by rfl) ⟨2596382, by rfl⟩ : syracuseStep 3461843 = 5192765) B5192765
theorem B2307895 : Blo 2307435 2307895 := bstep (se 1 (by rfl) ⟨1730921, by rfl⟩ : syracuseStep 2307895 = 3461843) B3461843
theorem B3894581 : Blo 2307435 3894581 := bbase (se 5 (by rfl) ⟨182558, by rfl⟩ : syracuseStep 3894581 = 365117) (by norm_num)
theorem B2596387 : Blo 2307435 2596387 := bstep (se 1 (by rfl) ⟨1947290, by rfl⟩ : syracuseStep 2596387 = 3894581) B3894581
theorem B3461849 : Blo 2307435 3461849 := bstep (se 2 (by rfl) ⟨1298193, by rfl⟩ : syracuseStep 3461849 = 2596387) B2596387
theorem B2307899 : Blo 2307435 2307899 := bstep (se 1 (by rfl) ⟨1730924, by rfl⟩ : syracuseStep 2307899 = 3461849) B3461849
theorem B6572117 : Blo 2307435 6572117 := bbase (se 8 (by rfl) ⟨38508, by rfl⟩ : syracuseStep 6572117 = 77017) (by norm_num)
theorem B17525645 : Blo 2307435 17525645 := bstep (se 3 (by rfl) ⟨3286058, by rfl⟩ : syracuseStep 17525645 = 6572117) B6572117
theorem B11683763 : Blo 2307435 11683763 := bstep (se 1 (by rfl) ⟨8762822, by rfl⟩ : syracuseStep 11683763 = 17525645) B17525645
theorem B7789175 : Blo 2307435 7789175 := bstep (se 1 (by rfl) ⟨5841881, by rfl⟩ : syracuseStep 7789175 = 11683763) B11683763
theorem B5192783 : Blo 2307435 5192783 := bstep (se 1 (by rfl) ⟨3894587, by rfl⟩ : syracuseStep 5192783 = 7789175) B7789175
theorem B3461855 : Blo 2307435 3461855 := bstep (se 1 (by rfl) ⟨2596391, by rfl⟩ : syracuseStep 3461855 = 5192783) B5192783
theorem B2307903 : Blo 2307435 2307903 := bstep (se 1 (by rfl) ⟨1730927, by rfl⟩ : syracuseStep 2307903 = 3461855) B3461855
theorem B3461861 : Blo 2307435 3461861 := bbase (se 4 (by rfl) ⟨324549, by rfl⟩ : syracuseStep 3461861 = 649099) (by norm_num)
theorem B2307907 : Blo 2307435 2307907 := bstep (se 1 (by rfl) ⟨1730930, by rfl⟩ : syracuseStep 2307907 = 3461861) B3461861
theorem B2464553 : Blo 2307435 2464553 := bbase (se 2 (by rfl) ⟨924207, by rfl⟩ : syracuseStep 2464553 = 1848415) (by norm_num)
theorem B6572141 : Blo 2307435 6572141 := bstep (se 3 (by rfl) ⟨1232276, by rfl⟩ : syracuseStep 6572141 = 2464553) B2464553
theorem B4381427 : Blo 2307435 4381427 := bstep (se 1 (by rfl) ⟨3286070, by rfl⟩ : syracuseStep 4381427 = 6572141) B6572141
theorem B2920951 : Blo 2307435 2920951 := bstep (se 1 (by rfl) ⟨2190713, by rfl⟩ : syracuseStep 2920951 = 4381427) B4381427
theorem B3894601 : Blo 2307435 3894601 := bstep (se 2 (by rfl) ⟨1460475, by rfl⟩ : syracuseStep 3894601 = 2920951) B2920951
theorem B5192801 : Blo 2307435 5192801 := bstep (se 2 (by rfl) ⟨1947300, by rfl⟩ : syracuseStep 5192801 = 3894601) B3894601
theorem B3461867 : Blo 2307435 3461867 := bstep (se 1 (by rfl) ⟨2596400, by rfl⟩ : syracuseStep 3461867 = 5192801) B5192801
theorem B2307911 : Blo 2307435 2307911 := bstep (se 1 (by rfl) ⟨1730933, by rfl⟩ : syracuseStep 2307911 = 3461867) B3461867
theorem B2596405 : Blo 2307435 2596405 := bbase (se 5 (by rfl) ⟨121706, by rfl⟩ : syracuseStep 2596405 = 243413) (by norm_num)
theorem B3461873 : Blo 2307435 3461873 := bstep (se 2 (by rfl) ⟨1298202, by rfl⟩ : syracuseStep 3461873 = 2596405) B2596405
theorem B2307915 : Blo 2307435 2307915 := bstep (se 1 (by rfl) ⟨1730936, by rfl⟩ : syracuseStep 2307915 = 3461873) B3461873
theorem B2920961 : Blo 2307435 2920961 := bbase (se 2 (by rfl) ⟨1095360, by rfl⟩ : syracuseStep 2920961 = 2190721) (by norm_num)
theorem B7789229 : Blo 2307435 7789229 := bstep (se 3 (by rfl) ⟨1460480, by rfl⟩ : syracuseStep 7789229 = 2920961) B2920961
theorem B5192819 : Blo 2307435 5192819 := bstep (se 1 (by rfl) ⟨3894614, by rfl⟩ : syracuseStep 5192819 = 7789229) B7789229
theorem B3461879 : Blo 2307435 3461879 := bstep (se 1 (by rfl) ⟨2596409, by rfl⟩ : syracuseStep 3461879 = 5192819) B5192819
theorem B2307919 : Blo 2307435 2307919 := bstep (se 1 (by rfl) ⟨1730939, by rfl⟩ : syracuseStep 2307919 = 3461879) B3461879
theorem B3461885 : Blo 2307435 3461885 := bbase (se 3 (by rfl) ⟨649103, by rfl⟩ : syracuseStep 3461885 = 1298207) (by norm_num)
theorem B2307923 : Blo 2307435 2307923 := bstep (se 1 (by rfl) ⟨1730942, by rfl⟩ : syracuseStep 2307923 = 3461885) B3461885
theorem B5192837 : Blo 2307435 5192837 := bbase (se 4 (by rfl) ⟨486828, by rfl⟩ : syracuseStep 5192837 = 973657) (by norm_num)
theorem B3461891 : Blo 2307435 3461891 := bstep (se 1 (by rfl) ⟨2596418, by rfl⟩ : syracuseStep 3461891 = 5192837) B5192837
theorem B2307927 : Blo 2307435 2307927 := bstep (se 1 (by rfl) ⟨1730945, by rfl⟩ : syracuseStep 2307927 = 3461891) B3461891
theorem B4929149 : Blo 2307435 4929149 := bbase (se 3 (by rfl) ⟨924215, by rfl⟩ : syracuseStep 4929149 = 1848431) (by norm_num)
theorem B3286099 : Blo 2307435 3286099 := bstep (se 1 (by rfl) ⟨2464574, by rfl⟩ : syracuseStep 3286099 = 4929149) B4929149
theorem B4381465 : Blo 2307435 4381465 := bstep (se 2 (by rfl) ⟨1643049, by rfl⟩ : syracuseStep 4381465 = 3286099) B3286099
theorem B5841953 : Blo 2307435 5841953 := bstep (se 2 (by rfl) ⟨2190732, by rfl⟩ : syracuseStep 5841953 = 4381465) B4381465
theorem B3894635 : Blo 2307435 3894635 := bstep (se 1 (by rfl) ⟨2920976, by rfl⟩ : syracuseStep 3894635 = 5841953) B5841953
theorem B2596423 : Blo 2307435 2596423 := bstep (se 1 (by rfl) ⟨1947317, by rfl⟩ : syracuseStep 2596423 = 3894635) B3894635
theorem B3461897 : Blo 2307435 3461897 := bstep (se 2 (by rfl) ⟨1298211, by rfl⟩ : syracuseStep 3461897 = 2596423) B2596423
theorem B2307931 : Blo 2307435 2307931 := bstep (se 1 (by rfl) ⟨1730948, by rfl⟩ : syracuseStep 2307931 = 3461897) B3461897
theorem B11683925 : Blo 2307435 11683925 := bbase (se 8 (by rfl) ⟨68460, by rfl⟩ : syracuseStep 11683925 = 136921) (by norm_num)
theorem B7789283 : Blo 2307435 7789283 := bstep (se 1 (by rfl) ⟨5841962, by rfl⟩ : syracuseStep 7789283 = 11683925) B11683925
theorem B5192855 : Blo 2307435 5192855 := bstep (se 1 (by rfl) ⟨3894641, by rfl⟩ : syracuseStep 5192855 = 7789283) B7789283
theorem B3461903 : Blo 2307435 3461903 := bstep (se 1 (by rfl) ⟨2596427, by rfl⟩ : syracuseStep 3461903 = 5192855) B5192855
theorem B2307935 : Blo 2307435 2307935 := bstep (se 1 (by rfl) ⟨1730951, by rfl⟩ : syracuseStep 2307935 = 3461903) B3461903
theorem B3461909 : Blo 2307435 3461909 := bbase (se 6 (by rfl) ⟨81138, by rfl⟩ : syracuseStep 3461909 = 162277) (by norm_num)
theorem B2307939 : Blo 2307435 2307939 := bstep (se 1 (by rfl) ⟨1730954, by rfl⟩ : syracuseStep 2307939 = 3461909) B3461909
theorem B3509149 : Blo 2307435 3509149 := bbase (se 3 (by rfl) ⟨657965, by rfl⟩ : syracuseStep 3509149 = 1315931) (by norm_num)
theorem B4678865 : Blo 2307435 4678865 := bstep (se 2 (by rfl) ⟨1754574, by rfl⟩ : syracuseStep 4678865 = 3509149) B3509149
theorem B3119243 : Blo 2307435 3119243 := bstep (se 1 (by rfl) ⟨2339432, by rfl⟩ : syracuseStep 3119243 = 4678865) B4678865
theorem B8317981 : Blo 2307435 8317981 := bstep (se 3 (by rfl) ⟨1559621, by rfl⟩ : syracuseStep 8317981 = 3119243) B3119243
theorem B44362565 : Blo 2307435 44362565 := bstep (se 4 (by rfl) ⟨4158990, by rfl⟩ : syracuseStep 44362565 = 8317981) B8317981
theorem B29575043 : Blo 2307435 29575043 := bstep (se 1 (by rfl) ⟨22181282, by rfl⟩ : syracuseStep 29575043 = 44362565) B44362565
theorem B19716695 : Blo 2307435 19716695 := bstep (se 1 (by rfl) ⟨14787521, by rfl⟩ : syracuseStep 19716695 = 29575043) B29575043
theorem B13144463 : Blo 2307435 13144463 := bstep (se 1 (by rfl) ⟨9858347, by rfl⟩ : syracuseStep 13144463 = 19716695) B19716695
theorem B8762975 : Blo 2307435 8762975 := bstep (se 1 (by rfl) ⟨6572231, by rfl⟩ : syracuseStep 8762975 = 13144463) B13144463
theorem B5841983 : Blo 2307435 5841983 := bstep (se 1 (by rfl) ⟨4381487, by rfl⟩ : syracuseStep 5841983 = 8762975) B8762975
theorem B3894655 : Blo 2307435 3894655 := bstep (se 1 (by rfl) ⟨2920991, by rfl⟩ : syracuseStep 3894655 = 5841983) B5841983
theorem B5192873 : Blo 2307435 5192873 := bstep (se 2 (by rfl) ⟨1947327, by rfl⟩ : syracuseStep 5192873 = 3894655) B3894655
theorem B3461915 : Blo 2307435 3461915 := bstep (se 1 (by rfl) ⟨2596436, by rfl⟩ : syracuseStep 3461915 = 5192873) B5192873
theorem B2307943 : Blo 2307435 2307943 := bstep (se 1 (by rfl) ⟨1730957, by rfl⟩ : syracuseStep 2307943 = 3461915) B3461915
theorem B2596441 : Blo 2307435 2596441 := bbase (se 2 (by rfl) ⟨973665, by rfl⟩ : syracuseStep 2596441 = 1947331) (by norm_num)
theorem B3461921 : Blo 2307435 3461921 := bstep (se 2 (by rfl) ⟨1298220, by rfl⟩ : syracuseStep 3461921 = 2596441) B2596441
theorem B2307947 : Blo 2307435 2307947 := bstep (se 1 (by rfl) ⟨1730960, by rfl⟩ : syracuseStep 2307947 = 3461921) B3461921
theorem B14989333 : Blo 2307435 14989333 := bbase (se 6 (by rfl) ⟨351312, by rfl⟩ : syracuseStep 14989333 = 702625) (by norm_num)
theorem B19985777 : Blo 2307435 19985777 := bstep (se 2 (by rfl) ⟨7494666, by rfl⟩ : syracuseStep 19985777 = 14989333) B14989333
theorem B13323851 : Blo 2307435 13323851 := bstep (se 1 (by rfl) ⟨9992888, by rfl⟩ : syracuseStep 13323851 = 19985777) B19985777
theorem B8882567 : Blo 2307435 8882567 := bstep (se 1 (by rfl) ⟨6661925, by rfl⟩ : syracuseStep 8882567 = 13323851) B13323851
theorem B5921711 : Blo 2307435 5921711 := bstep (se 1 (by rfl) ⟨4441283, by rfl⟩ : syracuseStep 5921711 = 8882567) B8882567
theorem B3947807 : Blo 2307435 3947807 := bstep (se 1 (by rfl) ⟨2960855, by rfl⟩ : syracuseStep 3947807 = 5921711) B5921711
theorem B2631871 : Blo 2307435 2631871 := bstep (se 1 (by rfl) ⟨1973903, by rfl⟩ : syracuseStep 2631871 = 3947807) B3947807
theorem B14036645 : Blo 2307435 14036645 := bstep (se 4 (by rfl) ⟨1315935, by rfl⟩ : syracuseStep 14036645 = 2631871) B2631871
theorem B9357763 : Blo 2307435 9357763 := bstep (se 1 (by rfl) ⟨7018322, by rfl⟩ : syracuseStep 9357763 = 14036645) B14036645
theorem B12477017 : Blo 2307435 12477017 := bstep (se 2 (by rfl) ⟨4678881, by rfl⟩ : syracuseStep 12477017 = 9357763) B9357763
theorem B8318011 : Blo 2307435 8318011 := bstep (se 1 (by rfl) ⟨6238508, by rfl⟩ : syracuseStep 8318011 = 12477017) B12477017
theorem B11090681 : Blo 2307435 11090681 := bstep (se 2 (by rfl) ⟨4159005, by rfl⟩ : syracuseStep 11090681 = 8318011) B8318011
theorem B7393787 : Blo 2307435 7393787 := bstep (se 1 (by rfl) ⟨5545340, by rfl⟩ : syracuseStep 7393787 = 11090681) B11090681
theorem B4929191 : Blo 2307435 4929191 := bstep (se 1 (by rfl) ⟨3696893, by rfl⟩ : syracuseStep 4929191 = 7393787) B7393787
theorem B3286127 : Blo 2307435 3286127 := bstep (se 1 (by rfl) ⟨2464595, by rfl⟩ : syracuseStep 3286127 = 4929191) B4929191
theorem B8763005 : Blo 2307435 8763005 := bstep (se 3 (by rfl) ⟨1643063, by rfl⟩ : syracuseStep 8763005 = 3286127) B3286127
theorem B5842003 : Blo 2307435 5842003 := bstep (se 1 (by rfl) ⟨4381502, by rfl⟩ : syracuseStep 5842003 = 8763005) B8763005
theorem B7789337 : Blo 2307435 7789337 := bstep (se 2 (by rfl) ⟨2921001, by rfl⟩ : syracuseStep 7789337 = 5842003) B5842003
theorem B5192891 : Blo 2307435 5192891 := bstep (se 1 (by rfl) ⟨3894668, by rfl⟩ : syracuseStep 5192891 = 7789337) B7789337
theorem B3461927 : Blo 2307435 3461927 := bstep (se 1 (by rfl) ⟨2596445, by rfl⟩ : syracuseStep 3461927 = 5192891) B5192891
theorem B2307951 : Blo 2307435 2307951 := bstep (se 1 (by rfl) ⟨1730963, by rfl⟩ : syracuseStep 2307951 = 3461927) B3461927
theorem B3461933 : Blo 2307435 3461933 := bbase (se 3 (by rfl) ⟨649112, by rfl⟩ : syracuseStep 3461933 = 1298225) (by norm_num)
theorem B2307955 : Blo 2307435 2307955 := bstep (se 1 (by rfl) ⟨1730966, by rfl⟩ : syracuseStep 2307955 = 3461933) B3461933
theorem B5192909 : Blo 2307435 5192909 := bbase (se 3 (by rfl) ⟨973670, by rfl⟩ : syracuseStep 5192909 = 1947341) (by norm_num)
theorem B3461939 : Blo 2307435 3461939 := bstep (se 1 (by rfl) ⟨2596454, by rfl⟩ : syracuseStep 3461939 = 5192909) B5192909
theorem B2307959 : Blo 2307435 2307959 := bstep (se 1 (by rfl) ⟨1730969, by rfl⟩ : syracuseStep 2307959 = 3461939) B3461939
theorem B2921017 : Blo 2307435 2921017 := bbase (se 2 (by rfl) ⟨1095381, by rfl⟩ : syracuseStep 2921017 = 2190763) (by norm_num)
theorem B3894689 : Blo 2307435 3894689 := bstep (se 2 (by rfl) ⟨1460508, by rfl⟩ : syracuseStep 3894689 = 2921017) B2921017
theorem B2596459 : Blo 2307435 2596459 := bstep (se 1 (by rfl) ⟨1947344, by rfl⟩ : syracuseStep 2596459 = 3894689) B3894689
theorem B3461945 : Blo 2307435 3461945 := bstep (se 2 (by rfl) ⟨1298229, by rfl⟩ : syracuseStep 3461945 = 2596459) B2596459
theorem B2307963 : Blo 2307435 2307963 := bstep (se 1 (by rfl) ⟨1730972, by rfl⟩ : syracuseStep 2307963 = 3461945) B3461945
theorem B2772689 : Blo 2307435 2772689 := bbase (se 2 (by rfl) ⟨1039758, by rfl⟩ : syracuseStep 2772689 = 2079517) (by norm_num)
theorem B7393837 : Blo 2307435 7393837 := bstep (se 3 (by rfl) ⟨1386344, by rfl⟩ : syracuseStep 7393837 = 2772689) B2772689
theorem B9858449 : Blo 2307435 9858449 := bstep (se 2 (by rfl) ⟨3696918, by rfl⟩ : syracuseStep 9858449 = 7393837) B7393837
theorem B26289197 : Blo 2307435 26289197 := bstep (se 3 (by rfl) ⟨4929224, by rfl⟩ : syracuseStep 26289197 = 9858449) B9858449
theorem B17526131 : Blo 2307435 17526131 := bstep (se 1 (by rfl) ⟨13144598, by rfl⟩ : syracuseStep 17526131 = 26289197) B26289197
theorem B11684087 : Blo 2307435 11684087 := bstep (se 1 (by rfl) ⟨8763065, by rfl⟩ : syracuseStep 11684087 = 17526131) B17526131
theorem B7789391 : Blo 2307435 7789391 := bstep (se 1 (by rfl) ⟨5842043, by rfl⟩ : syracuseStep 7789391 = 11684087) B11684087
theorem B5192927 : Blo 2307435 5192927 := bstep (se 1 (by rfl) ⟨3894695, by rfl⟩ : syracuseStep 5192927 = 7789391) B7789391
theorem B3461951 : Blo 2307435 3461951 := bstep (se 1 (by rfl) ⟨2596463, by rfl⟩ : syracuseStep 3461951 = 5192927) B5192927
theorem B2307967 : Blo 2307435 2307967 := bstep (se 1 (by rfl) ⟨1730975, by rfl⟩ : syracuseStep 2307967 = 3461951) B3461951
theorem B3461957 : Blo 2307435 3461957 := bbase (se 4 (by rfl) ⟨324558, by rfl⟩ : syracuseStep 3461957 = 649117) (by norm_num)
theorem B2307971 : Blo 2307435 2307971 := bstep (se 1 (by rfl) ⟨1730978, by rfl⟩ : syracuseStep 2307971 = 3461957) B3461957
theorem B3894709 : Blo 2307435 3894709 := bbase (se 5 (by rfl) ⟨182564, by rfl⟩ : syracuseStep 3894709 = 365129) (by norm_num)
theorem B5192945 : Blo 2307435 5192945 := bstep (se 2 (by rfl) ⟨1947354, by rfl⟩ : syracuseStep 5192945 = 3894709) B3894709
theorem B3461963 : Blo 2307435 3461963 := bstep (se 1 (by rfl) ⟨2596472, by rfl⟩ : syracuseStep 3461963 = 5192945) B5192945
theorem B2307975 : Blo 2307435 2307975 := bstep (se 1 (by rfl) ⟨1730981, by rfl⟩ : syracuseStep 2307975 = 3461963) B3461963
theorem B2596477 : Blo 2307435 2596477 := bbase (se 3 (by rfl) ⟨486839, by rfl⟩ : syracuseStep 2596477 = 973679) (by norm_num)
theorem B3461969 : Blo 2307435 3461969 := bstep (se 2 (by rfl) ⟨1298238, by rfl⟩ : syracuseStep 3461969 = 2596477) B2596477
theorem B2307979 : Blo 2307435 2307979 := bstep (se 1 (by rfl) ⟨1730984, by rfl⟩ : syracuseStep 2307979 = 3461969) B3461969
theorem B7789445 : Blo 2307435 7789445 := bbase (se 4 (by rfl) ⟨730260, by rfl⟩ : syracuseStep 7789445 = 1460521) (by norm_num)
theorem B5192963 : Blo 2307435 5192963 := bstep (se 1 (by rfl) ⟨3894722, by rfl⟩ : syracuseStep 5192963 = 7789445) B7789445
theorem B3461975 : Blo 2307435 3461975 := bstep (se 1 (by rfl) ⟨2596481, by rfl⟩ : syracuseStep 3461975 = 5192963) B5192963
theorem B2307983 : Blo 2307435 2307983 := bstep (se 1 (by rfl) ⟨1730987, by rfl⟩ : syracuseStep 2307983 = 3461975) B3461975
theorem B3461981 : Blo 2307435 3461981 := bbase (se 3 (by rfl) ⟨649121, by rfl⟩ : syracuseStep 3461981 = 1298243) (by norm_num)
theorem B2307987 : Blo 2307435 2307987 := bstep (se 1 (by rfl) ⟨1730990, by rfl⟩ : syracuseStep 2307987 = 3461981) B3461981
theorem B5192981 : Blo 2307435 5192981 := bbase (se 6 (by rfl) ⟨121710, by rfl⟩ : syracuseStep 5192981 = 243421) (by norm_num)
theorem B3461987 : Blo 2307435 3461987 := bstep (se 1 (by rfl) ⟨2596490, by rfl⟩ : syracuseStep 3461987 = 5192981) B5192981
theorem B2307991 : Blo 2307435 2307991 := bstep (se 1 (by rfl) ⟨1730993, by rfl⟩ : syracuseStep 2307991 = 3461987) B3461987
theorem B8763173 : Blo 2307435 8763173 := bbase (se 4 (by rfl) ⟨821547, by rfl⟩ : syracuseStep 8763173 = 1643095) (by norm_num)
theorem B5842115 : Blo 2307435 5842115 := bstep (se 1 (by rfl) ⟨4381586, by rfl⟩ : syracuseStep 5842115 = 8763173) B8763173
theorem B3894743 : Blo 2307435 3894743 := bstep (se 1 (by rfl) ⟨2921057, by rfl⟩ : syracuseStep 3894743 = 5842115) B5842115
theorem B2596495 : Blo 2307435 2596495 := bstep (se 1 (by rfl) ⟨1947371, by rfl⟩ : syracuseStep 2596495 = 3894743) B3894743
theorem B3461993 : Blo 2307435 3461993 := bstep (se 2 (by rfl) ⟨1298247, by rfl⟩ : syracuseStep 3461993 = 2596495) B2596495
theorem B2307995 : Blo 2307435 2307995 := bstep (se 1 (by rfl) ⟨1730996, by rfl⟩ : syracuseStep 2307995 = 3461993) B3461993
theorem B4929293 : Blo 2307435 4929293 := bbase (se 3 (by rfl) ⟨924242, by rfl⟩ : syracuseStep 4929293 = 1848485) (by norm_num)
theorem B13144781 : Blo 2307435 13144781 := bstep (se 3 (by rfl) ⟨2464646, by rfl⟩ : syracuseStep 13144781 = 4929293) B4929293
theorem B8763187 : Blo 2307435 8763187 := bstep (se 1 (by rfl) ⟨6572390, by rfl⟩ : syracuseStep 8763187 = 13144781) B13144781
theorem B11684249 : Blo 2307435 11684249 := bstep (se 2 (by rfl) ⟨4381593, by rfl⟩ : syracuseStep 11684249 = 8763187) B8763187
theorem B7789499 : Blo 2307435 7789499 := bstep (se 1 (by rfl) ⟨5842124, by rfl⟩ : syracuseStep 7789499 = 11684249) B11684249
theorem B5192999 : Blo 2307435 5192999 := bstep (se 1 (by rfl) ⟨3894749, by rfl⟩ : syracuseStep 5192999 = 7789499) B7789499
theorem B3461999 : Blo 2307435 3461999 := bstep (se 1 (by rfl) ⟨2596499, by rfl⟩ : syracuseStep 3461999 = 5192999) B5192999
theorem B2307999 : Blo 2307435 2307999 := bstep (se 1 (by rfl) ⟨1730999, by rfl⟩ : syracuseStep 2307999 = 3461999) B3461999
theorem B3462005 : Blo 2307435 3462005 := bbase (se 5 (by rfl) ⟨162281, by rfl⟩ : syracuseStep 3462005 = 324563) (by norm_num)
theorem B2308003 : Blo 2307435 2308003 := bstep (se 1 (by rfl) ⟨1731002, by rfl⟩ : syracuseStep 2308003 = 3462005) B3462005
theorem B9485669 : Blo 2307435 9485669 := bbase (se 4 (by rfl) ⟨889281, by rfl⟩ : syracuseStep 9485669 = 1778563) (by norm_num)
theorem B6323779 : Blo 2307435 6323779 := bstep (se 1 (by rfl) ⟨4742834, by rfl⟩ : syracuseStep 6323779 = 9485669) B9485669
theorem B8431705 : Blo 2307435 8431705 := bstep (se 2 (by rfl) ⟨3161889, by rfl⟩ : syracuseStep 8431705 = 6323779) B6323779
theorem B44969093 : Blo 2307435 44969093 := bstep (se 4 (by rfl) ⟨4215852, by rfl⟩ : syracuseStep 44969093 = 8431705) B8431705
theorem B29979395 : Blo 2307435 29979395 := bstep (se 1 (by rfl) ⟨22484546, by rfl⟩ : syracuseStep 29979395 = 44969093) B44969093
theorem B19986263 : Blo 2307435 19986263 := bstep (se 1 (by rfl) ⟨14989697, by rfl⟩ : syracuseStep 19986263 = 29979395) B29979395
theorem B13324175 : Blo 2307435 13324175 := bstep (se 1 (by rfl) ⟨9993131, by rfl⟩ : syracuseStep 13324175 = 19986263) B19986263
theorem B8882783 : Blo 2307435 8882783 := bstep (se 1 (by rfl) ⟨6662087, by rfl⟩ : syracuseStep 8882783 = 13324175) B13324175
theorem B5921855 : Blo 2307435 5921855 := bstep (se 1 (by rfl) ⟨4441391, by rfl⟩ : syracuseStep 5921855 = 8882783) B8882783
theorem B3947903 : Blo 2307435 3947903 := bstep (se 1 (by rfl) ⟨2960927, by rfl⟩ : syracuseStep 3947903 = 5921855) B5921855
theorem B2631935 : Blo 2307435 2631935 := bstep (se 1 (by rfl) ⟨1973951, by rfl⟩ : syracuseStep 2631935 = 3947903) B3947903
theorem B7018493 : Blo 2307435 7018493 := bstep (se 3 (by rfl) ⟨1315967, by rfl⟩ : syracuseStep 7018493 = 2631935) B2631935
theorem B18715981 : Blo 2307435 18715981 := bstep (se 3 (by rfl) ⟨3509246, by rfl⟩ : syracuseStep 18715981 = 7018493) B7018493
theorem B24954641 : Blo 2307435 24954641 := bstep (se 2 (by rfl) ⟨9357990, by rfl⟩ : syracuseStep 24954641 = 18715981) B18715981
theorem B16636427 : Blo 2307435 16636427 := bstep (se 1 (by rfl) ⟨12477320, by rfl⟩ : syracuseStep 16636427 = 24954641) B24954641
theorem B11090951 : Blo 2307435 11090951 := bstep (se 1 (by rfl) ⟨8318213, by rfl⟩ : syracuseStep 11090951 = 16636427) B16636427
theorem B7393967 : Blo 2307435 7393967 := bstep (se 1 (by rfl) ⟨5545475, by rfl⟩ : syracuseStep 7393967 = 11090951) B11090951
theorem B4929311 : Blo 2307435 4929311 := bstep (se 1 (by rfl) ⟨3696983, by rfl⟩ : syracuseStep 4929311 = 7393967) B7393967
theorem B3286207 : Blo 2307435 3286207 := bstep (se 1 (by rfl) ⟨2464655, by rfl⟩ : syracuseStep 3286207 = 4929311) B4929311
theorem B4381609 : Blo 2307435 4381609 := bstep (se 2 (by rfl) ⟨1643103, by rfl⟩ : syracuseStep 4381609 = 3286207) B3286207
theorem B5842145 : Blo 2307435 5842145 := bstep (se 2 (by rfl) ⟨2190804, by rfl⟩ : syracuseStep 5842145 = 4381609) B4381609
theorem B3894763 : Blo 2307435 3894763 := bstep (se 1 (by rfl) ⟨2921072, by rfl⟩ : syracuseStep 3894763 = 5842145) B5842145
theorem B5193017 : Blo 2307435 5193017 := bstep (se 2 (by rfl) ⟨1947381, by rfl⟩ : syracuseStep 5193017 = 3894763) B3894763
theorem B3462011 : Blo 2307435 3462011 := bstep (se 1 (by rfl) ⟨2596508, by rfl⟩ : syracuseStep 3462011 = 5193017) B5193017
theorem B2308007 : Blo 2307435 2308007 := bstep (se 1 (by rfl) ⟨1731005, by rfl⟩ : syracuseStep 2308007 = 3462011) B3462011
theorem B2596513 : Blo 2307435 2596513 := bbase (se 2 (by rfl) ⟨973692, by rfl⟩ : syracuseStep 2596513 = 1947385) (by norm_num)
theorem B3462017 : Blo 2307435 3462017 := bstep (se 2 (by rfl) ⟨1298256, by rfl⟩ : syracuseStep 3462017 = 2596513) B2596513
theorem B2308011 : Blo 2307435 2308011 := bstep (se 1 (by rfl) ⟨1731008, by rfl⟩ : syracuseStep 2308011 = 3462017) B3462017
theorem B5842165 : Blo 2307435 5842165 := bbase (se 5 (by rfl) ⟨273851, by rfl⟩ : syracuseStep 5842165 = 547703) (by norm_num)
theorem B7789553 : Blo 2307435 7789553 := bstep (se 2 (by rfl) ⟨2921082, by rfl⟩ : syracuseStep 7789553 = 5842165) B5842165
theorem B5193035 : Blo 2307435 5193035 := bstep (se 1 (by rfl) ⟨3894776, by rfl⟩ : syracuseStep 5193035 = 7789553) B7789553
theorem B3462023 : Blo 2307435 3462023 := bstep (se 1 (by rfl) ⟨2596517, by rfl⟩ : syracuseStep 3462023 = 5193035) B5193035
theorem B2308015 : Blo 2307435 2308015 := bstep (se 1 (by rfl) ⟨1731011, by rfl⟩ : syracuseStep 2308015 = 3462023) B3462023
theorem B3462029 : Blo 2307435 3462029 := bbase (se 3 (by rfl) ⟨649130, by rfl⟩ : syracuseStep 3462029 = 1298261) (by norm_num)
theorem B2308019 : Blo 2307435 2308019 := bstep (se 1 (by rfl) ⟨1731014, by rfl⟩ : syracuseStep 2308019 = 3462029) B3462029
theorem B5193053 : Blo 2307435 5193053 := bbase (se 3 (by rfl) ⟨973697, by rfl⟩ : syracuseStep 5193053 = 1947395) (by norm_num)
theorem B3462035 : Blo 2307435 3462035 := bstep (se 1 (by rfl) ⟨2596526, by rfl⟩ : syracuseStep 3462035 = 5193053) B5193053
theorem B2308023 : Blo 2307435 2308023 := bstep (se 1 (by rfl) ⟨1731017, by rfl⟩ : syracuseStep 2308023 = 3462035) B3462035
theorem B3894797 : Blo 2307435 3894797 := bbase (se 3 (by rfl) ⟨730274, by rfl⟩ : syracuseStep 3894797 = 1460549) (by norm_num)
theorem B2596531 : Blo 2307435 2596531 := bstep (se 1 (by rfl) ⟨1947398, by rfl⟩ : syracuseStep 2596531 = 3894797) B3894797
theorem B3462041 : Blo 2307435 3462041 := bstep (se 2 (by rfl) ⟨1298265, by rfl⟩ : syracuseStep 3462041 = 2596531) B2596531
theorem B2308027 : Blo 2307435 2308027 := bstep (se 1 (by rfl) ⟨1731020, by rfl⟩ : syracuseStep 2308027 = 3462041) B3462041
theorem B3697021 : Blo 2307435 3697021 := bbase (se 3 (by rfl) ⟨693191, by rfl⟩ : syracuseStep 3697021 = 1386383) (by norm_num)
theorem B19717445 : Blo 2307435 19717445 := bstep (se 4 (by rfl) ⟨1848510, by rfl⟩ : syracuseStep 19717445 = 3697021) B3697021
theorem B13144963 : Blo 2307435 13144963 := bstep (se 1 (by rfl) ⟨9858722, by rfl⟩ : syracuseStep 13144963 = 19717445) B19717445
theorem B17526617 : Blo 2307435 17526617 := bstep (se 2 (by rfl) ⟨6572481, by rfl⟩ : syracuseStep 17526617 = 13144963) B13144963
theorem B11684411 : Blo 2307435 11684411 := bstep (se 1 (by rfl) ⟨8763308, by rfl⟩ : syracuseStep 11684411 = 17526617) B17526617
theorem B7789607 : Blo 2307435 7789607 := bstep (se 1 (by rfl) ⟨5842205, by rfl⟩ : syracuseStep 7789607 = 11684411) B11684411
theorem B5193071 : Blo 2307435 5193071 := bstep (se 1 (by rfl) ⟨3894803, by rfl⟩ : syracuseStep 5193071 = 7789607) B7789607
theorem B3462047 : Blo 2307435 3462047 := bstep (se 1 (by rfl) ⟨2596535, by rfl⟩ : syracuseStep 3462047 = 5193071) B5193071
theorem B2308031 : Blo 2307435 2308031 := bstep (se 1 (by rfl) ⟨1731023, by rfl⟩ : syracuseStep 2308031 = 3462047) B3462047
theorem B3462053 : Blo 2307435 3462053 := bbase (se 4 (by rfl) ⟨324567, by rfl⟩ : syracuseStep 3462053 = 649135) (by norm_num)
theorem B2308035 : Blo 2307435 2308035 := bstep (se 1 (by rfl) ⟨1731026, by rfl⟩ : syracuseStep 2308035 = 3462053) B3462053
theorem B2921113 : Blo 2307435 2921113 := bbase (se 2 (by rfl) ⟨1095417, by rfl⟩ : syracuseStep 2921113 = 2190835) (by norm_num)
theorem B3894817 : Blo 2307435 3894817 := bstep (se 2 (by rfl) ⟨1460556, by rfl⟩ : syracuseStep 3894817 = 2921113) B2921113
theorem B5193089 : Blo 2307435 5193089 := bstep (se 2 (by rfl) ⟨1947408, by rfl⟩ : syracuseStep 5193089 = 3894817) B3894817
theorem B3462059 : Blo 2307435 3462059 := bstep (se 1 (by rfl) ⟨2596544, by rfl⟩ : syracuseStep 3462059 = 5193089) B5193089
theorem B2308039 : Blo 2307435 2308039 := bstep (se 1 (by rfl) ⟨1731029, by rfl⟩ : syracuseStep 2308039 = 3462059) B3462059
theorem B2596549 : Blo 2307435 2596549 := bbase (se 4 (by rfl) ⟨243426, by rfl⟩ : syracuseStep 2596549 = 486853) (by norm_num)
theorem B3462065 : Blo 2307435 3462065 := bstep (se 2 (by rfl) ⟨1298274, by rfl⟩ : syracuseStep 3462065 = 2596549) B2596549
theorem B2308043 : Blo 2307435 2308043 := bstep (se 1 (by rfl) ⟨1731032, by rfl⟩ : syracuseStep 2308043 = 3462065) B3462065
theorem B4381685 : Blo 2307435 4381685 := bbase (se 5 (by rfl) ⟨205391, by rfl⟩ : syracuseStep 4381685 = 410783) (by norm_num)
theorem B2921123 : Blo 2307435 2921123 := bstep (se 1 (by rfl) ⟨2190842, by rfl⟩ : syracuseStep 2921123 = 4381685) B4381685
theorem B7789661 : Blo 2307435 7789661 := bstep (se 3 (by rfl) ⟨1460561, by rfl⟩ : syracuseStep 7789661 = 2921123) B2921123
theorem B5193107 : Blo 2307435 5193107 := bstep (se 1 (by rfl) ⟨3894830, by rfl⟩ : syracuseStep 5193107 = 7789661) B7789661
theorem B3462071 : Blo 2307435 3462071 := bstep (se 1 (by rfl) ⟨2596553, by rfl⟩ : syracuseStep 3462071 = 5193107) B5193107
theorem B2308047 : Blo 2307435 2308047 := bstep (se 1 (by rfl) ⟨1731035, by rfl⟩ : syracuseStep 2308047 = 3462071) B3462071
theorem B3462077 : Blo 2307435 3462077 := bbase (se 3 (by rfl) ⟨649139, by rfl⟩ : syracuseStep 3462077 = 1298279) (by norm_num)
theorem B2308051 : Blo 2307435 2308051 := bstep (se 1 (by rfl) ⟨1731038, by rfl⟩ : syracuseStep 2308051 = 3462077) B3462077
theorem B5193125 : Blo 2307435 5193125 := bbase (se 4 (by rfl) ⟨486855, by rfl⟩ : syracuseStep 5193125 = 973711) (by norm_num)
theorem B3462083 : Blo 2307435 3462083 := bstep (se 1 (by rfl) ⟨2596562, by rfl⟩ : syracuseStep 3462083 = 5193125) B5193125
theorem B2308055 : Blo 2307435 2308055 := bstep (se 1 (by rfl) ⟨1731041, by rfl⟩ : syracuseStep 2308055 = 3462083) B3462083
theorem B5842277 : Blo 2307435 5842277 := bbase (se 4 (by rfl) ⟨547713, by rfl⟩ : syracuseStep 5842277 = 1095427) (by norm_num)
theorem B3894851 : Blo 2307435 3894851 := bstep (se 1 (by rfl) ⟨2921138, by rfl⟩ : syracuseStep 3894851 = 5842277) B5842277
theorem B2596567 : Blo 2307435 2596567 := bstep (se 1 (by rfl) ⟨1947425, by rfl⟩ : syracuseStep 2596567 = 3894851) B3894851
theorem B3462089 : Blo 2307435 3462089 := bstep (se 2 (by rfl) ⟨1298283, by rfl⟩ : syracuseStep 3462089 = 2596567) B2596567
theorem B2308059 : Blo 2307435 2308059 := bstep (se 1 (by rfl) ⟨1731044, by rfl⟩ : syracuseStep 2308059 = 3462089) B3462089
theorem B2772805 : Blo 2307435 2772805 := bbase (se 4 (by rfl) ⟨259950, by rfl⟩ : syracuseStep 2772805 = 519901) (by norm_num)
theorem B3697073 : Blo 2307435 3697073 := bstep (se 2 (by rfl) ⟨1386402, by rfl⟩ : syracuseStep 3697073 = 2772805) B2772805
theorem B2464715 : Blo 2307435 2464715 := bstep (se 1 (by rfl) ⟨1848536, by rfl⟩ : syracuseStep 2464715 = 3697073) B3697073
theorem B6572573 : Blo 2307435 6572573 := bstep (se 3 (by rfl) ⟨1232357, by rfl⟩ : syracuseStep 6572573 = 2464715) B2464715
theorem B4381715 : Blo 2307435 4381715 := bstep (se 1 (by rfl) ⟨3286286, by rfl⟩ : syracuseStep 4381715 = 6572573) B6572573
theorem B11684573 : Blo 2307435 11684573 := bstep (se 3 (by rfl) ⟨2190857, by rfl⟩ : syracuseStep 11684573 = 4381715) B4381715
theorem B7789715 : Blo 2307435 7789715 := bstep (se 1 (by rfl) ⟨5842286, by rfl⟩ : syracuseStep 7789715 = 11684573) B11684573
theorem B5193143 : Blo 2307435 5193143 := bstep (se 1 (by rfl) ⟨3894857, by rfl⟩ : syracuseStep 5193143 = 7789715) B7789715
theorem B3462095 : Blo 2307435 3462095 := bstep (se 1 (by rfl) ⟨2596571, by rfl⟩ : syracuseStep 3462095 = 5193143) B5193143
theorem B2308063 : Blo 2307435 2308063 := bstep (se 1 (by rfl) ⟨1731047, by rfl⟩ : syracuseStep 2308063 = 3462095) B3462095
theorem B3462101 : Blo 2307435 3462101 := bbase (se 7 (by rfl) ⟨40571, by rfl⟩ : syracuseStep 3462101 = 81143) (by norm_num)
theorem B2308067 : Blo 2307435 2308067 := bstep (se 1 (by rfl) ⟨1731050, by rfl⟩ : syracuseStep 2308067 = 3462101) B3462101
theorem B8763461 : Blo 2307435 8763461 := bbase (se 4 (by rfl) ⟨821574, by rfl⟩ : syracuseStep 8763461 = 1643149) (by norm_num)
theorem B5842307 : Blo 2307435 5842307 := bstep (se 1 (by rfl) ⟨4381730, by rfl⟩ : syracuseStep 5842307 = 8763461) B8763461
theorem B3894871 : Blo 2307435 3894871 := bstep (se 1 (by rfl) ⟨2921153, by rfl⟩ : syracuseStep 3894871 = 5842307) B5842307
theorem B5193161 : Blo 2307435 5193161 := bstep (se 2 (by rfl) ⟨1947435, by rfl⟩ : syracuseStep 5193161 = 3894871) B3894871
theorem B3462107 : Blo 2307435 3462107 := bstep (se 1 (by rfl) ⟨2596580, by rfl⟩ : syracuseStep 3462107 = 5193161) B5193161
theorem B2308071 : Blo 2307435 2308071 := bstep (se 1 (by rfl) ⟨1731053, by rfl⟩ : syracuseStep 2308071 = 3462107) B3462107
theorem B2596585 : Blo 2307435 2596585 := bbase (se 2 (by rfl) ⟨973719, by rfl⟩ : syracuseStep 2596585 = 1947439) (by norm_num)
theorem B3462113 : Blo 2307435 3462113 := bstep (se 2 (by rfl) ⟨1298292, by rfl⟩ : syracuseStep 3462113 = 2596585) B2596585
theorem B2308075 : Blo 2307435 2308075 := bstep (se 1 (by rfl) ⟨1731056, by rfl⟩ : syracuseStep 2308075 = 3462113) B3462113
theorem B13145237 : Blo 2307435 13145237 := bbase (se 6 (by rfl) ⟨308091, by rfl⟩ : syracuseStep 13145237 = 616183) (by norm_num)
theorem B8763491 : Blo 2307435 8763491 := bstep (se 1 (by rfl) ⟨6572618, by rfl⟩ : syracuseStep 8763491 = 13145237) B13145237
theorem B5842327 : Blo 2307435 5842327 := bstep (se 1 (by rfl) ⟨4381745, by rfl⟩ : syracuseStep 5842327 = 8763491) B8763491
theorem B7789769 : Blo 2307435 7789769 := bstep (se 2 (by rfl) ⟨2921163, by rfl⟩ : syracuseStep 7789769 = 5842327) B5842327
theorem B5193179 : Blo 2307435 5193179 := bstep (se 1 (by rfl) ⟨3894884, by rfl⟩ : syracuseStep 5193179 = 7789769) B7789769
theorem B3462119 : Blo 2307435 3462119 := bstep (se 1 (by rfl) ⟨2596589, by rfl⟩ : syracuseStep 3462119 = 5193179) B5193179
theorem B2308079 : Blo 2307435 2308079 := bstep (se 1 (by rfl) ⟨1731059, by rfl⟩ : syracuseStep 2308079 = 3462119) B3462119
theorem B3462125 : Blo 2307435 3462125 := bbase (se 3 (by rfl) ⟨649148, by rfl⟩ : syracuseStep 3462125 = 1298297) (by norm_num)
theorem B2308083 : Blo 2307435 2308083 := bstep (se 1 (by rfl) ⟨1731062, by rfl⟩ : syracuseStep 2308083 = 3462125) B3462125
theorem B5193197 : Blo 2307435 5193197 := bbase (se 3 (by rfl) ⟨973724, by rfl⟩ : syracuseStep 5193197 = 1947449) (by norm_num)
theorem B3462131 : Blo 2307435 3462131 := bstep (se 1 (by rfl) ⟨2596598, by rfl⟩ : syracuseStep 3462131 = 5193197) B5193197
theorem B2308087 : Blo 2307435 2308087 := bstep (se 1 (by rfl) ⟨1731065, by rfl⟩ : syracuseStep 2308087 = 3462131) B3462131
theorem B24011477 : Blo 2307435 24011477 := bbase (se 7 (by rfl) ⟨281384, by rfl⟩ : syracuseStep 24011477 = 562769) (by norm_num)
theorem B16007651 : Blo 2307435 16007651 := bstep (se 1 (by rfl) ⟨12005738, by rfl⟩ : syracuseStep 16007651 = 24011477) B24011477
theorem B10671767 : Blo 2307435 10671767 := bstep (se 1 (by rfl) ⟨8003825, by rfl⟩ : syracuseStep 10671767 = 16007651) B16007651
theorem B7114511 : Blo 2307435 7114511 := bstep (se 1 (by rfl) ⟨5335883, by rfl⟩ : syracuseStep 7114511 = 10671767) B10671767
theorem B18972029 : Blo 2307435 18972029 := bstep (se 3 (by rfl) ⟨3557255, by rfl⟩ : syracuseStep 18972029 = 7114511) B7114511
theorem B50592077 : Blo 2307435 50592077 := bstep (se 3 (by rfl) ⟨9486014, by rfl⟩ : syracuseStep 50592077 = 18972029) B18972029
theorem B33728051 : Blo 2307435 33728051 := bstep (se 1 (by rfl) ⟨25296038, by rfl⟩ : syracuseStep 33728051 = 50592077) B50592077
theorem B22485367 : Blo 2307435 22485367 := bstep (se 1 (by rfl) ⟨16864025, by rfl⟩ : syracuseStep 22485367 = 33728051) B33728051
theorem B119921957 : Blo 2307435 119921957 := bstep (se 4 (by rfl) ⟨11242683, by rfl⟩ : syracuseStep 119921957 = 22485367) B22485367
theorem B79947971 : Blo 2307435 79947971 := bstep (se 1 (by rfl) ⟨59960978, by rfl⟩ : syracuseStep 79947971 = 119921957) B119921957
theorem B53298647 : Blo 2307435 53298647 := bstep (se 1 (by rfl) ⟨39973985, by rfl⟩ : syracuseStep 53298647 = 79947971) B79947971
theorem B35532431 : Blo 2307435 35532431 := bstep (se 1 (by rfl) ⟨26649323, by rfl⟩ : syracuseStep 35532431 = 53298647) B53298647
theorem B23688287 : Blo 2307435 23688287 := bstep (se 1 (by rfl) ⟨17766215, by rfl⟩ : syracuseStep 23688287 = 35532431) B35532431
theorem B15792191 : Blo 2307435 15792191 := bstep (se 1 (by rfl) ⟨11844143, by rfl⟩ : syracuseStep 15792191 = 23688287) B23688287
theorem B10528127 : Blo 2307435 10528127 := bstep (se 1 (by rfl) ⟨7896095, by rfl⟩ : syracuseStep 10528127 = 15792191) B15792191
theorem B7018751 : Blo 2307435 7018751 := bstep (se 1 (by rfl) ⟨5264063, by rfl⟩ : syracuseStep 7018751 = 10528127) B10528127
theorem B4679167 : Blo 2307435 4679167 := bstep (se 1 (by rfl) ⟨3509375, by rfl⟩ : syracuseStep 4679167 = 7018751) B7018751
theorem B6238889 : Blo 2307435 6238889 := bstep (se 2 (by rfl) ⟨2339583, by rfl⟩ : syracuseStep 6238889 = 4679167) B4679167
theorem B4159259 : Blo 2307435 4159259 := bstep (se 1 (by rfl) ⟨3119444, by rfl⟩ : syracuseStep 4159259 = 6238889) B6238889
theorem B2772839 : Blo 2307435 2772839 := bstep (se 1 (by rfl) ⟨2079629, by rfl⟩ : syracuseStep 2772839 = 4159259) B4159259
theorem B7394237 : Blo 2307435 7394237 := bstep (se 3 (by rfl) ⟨1386419, by rfl⟩ : syracuseStep 7394237 = 2772839) B2772839
theorem B4929491 : Blo 2307435 4929491 := bstep (se 1 (by rfl) ⟨3697118, by rfl⟩ : syracuseStep 4929491 = 7394237) B7394237
theorem B3286327 : Blo 2307435 3286327 := bstep (se 1 (by rfl) ⟨2464745, by rfl⟩ : syracuseStep 3286327 = 4929491) B4929491
theorem B4381769 : Blo 2307435 4381769 := bstep (se 2 (by rfl) ⟨1643163, by rfl⟩ : syracuseStep 4381769 = 3286327) B3286327
theorem B2921179 : Blo 2307435 2921179 := bstep (se 1 (by rfl) ⟨2190884, by rfl⟩ : syracuseStep 2921179 = 4381769) B4381769
theorem B3894905 : Blo 2307435 3894905 := bstep (se 2 (by rfl) ⟨1460589, by rfl⟩ : syracuseStep 3894905 = 2921179) B2921179
theorem B2596603 : Blo 2307435 2596603 := bstep (se 1 (by rfl) ⟨1947452, by rfl⟩ : syracuseStep 2596603 = 3894905) B3894905
theorem B3462137 : Blo 2307435 3462137 := bstep (se 2 (by rfl) ⟨1298301, by rfl⟩ : syracuseStep 3462137 = 2596603) B2596603
theorem B2308091 : Blo 2307435 2308091 := bstep (se 1 (by rfl) ⟨1731068, by rfl⟩ : syracuseStep 2308091 = 3462137) B3462137
theorem B44970773 : Blo 2307435 44970773 := bbase (se 6 (by rfl) ⟨1054002, by rfl⟩ : syracuseStep 44970773 = 2108005) (by norm_num)
theorem B119922061 : Blo 2307435 119922061 := bstep (se 3 (by rfl) ⟨22485386, by rfl⟩ : syracuseStep 119922061 = 44970773) B44970773
theorem B159896081 : Blo 2307435 159896081 := bstep (se 2 (by rfl) ⟨59961030, by rfl⟩ : syracuseStep 159896081 = 119922061) B119922061
theorem B106597387 : Blo 2307435 106597387 := bstep (se 1 (by rfl) ⟨79948040, by rfl⟩ : syracuseStep 106597387 = 159896081) B159896081
theorem B568519397 : Blo 2307435 568519397 := bstep (se 4 (by rfl) ⟨53298693, by rfl⟩ : syracuseStep 568519397 = 106597387) B106597387
theorem B379012931 : Blo 2307435 379012931 := bstep (se 1 (by rfl) ⟨284259698, by rfl⟩ : syracuseStep 379012931 = 568519397) B568519397
theorem B252675287 : Blo 2307435 252675287 := bstep (se 1 (by rfl) ⟨189506465, by rfl⟩ : syracuseStep 252675287 = 379012931) B379012931
theorem B168450191 : Blo 2307435 168450191 := bstep (se 1 (by rfl) ⟨126337643, by rfl⟩ : syracuseStep 168450191 = 252675287) B252675287
theorem B112300127 : Blo 2307435 112300127 := bstep (se 1 (by rfl) ⟨84225095, by rfl⟩ : syracuseStep 112300127 = 168450191) B168450191
theorem B74866751 : Blo 2307435 74866751 := bstep (se 1 (by rfl) ⟨56150063, by rfl⟩ : syracuseStep 74866751 = 112300127) B112300127
theorem B49911167 : Blo 2307435 49911167 := bstep (se 1 (by rfl) ⟨37433375, by rfl⟩ : syracuseStep 49911167 = 74866751) B74866751
theorem B133096445 : Blo 2307435 133096445 := bstep (se 3 (by rfl) ⟨24955583, by rfl⟩ : syracuseStep 133096445 = 49911167) B49911167
theorem B88730963 : Blo 2307435 88730963 := bstep (se 1 (by rfl) ⟨66548222, by rfl⟩ : syracuseStep 88730963 = 133096445) B133096445
theorem B59153975 : Blo 2307435 59153975 := bstep (se 1 (by rfl) ⟨44365481, by rfl⟩ : syracuseStep 59153975 = 88730963) B88730963
theorem B39435983 : Blo 2307435 39435983 := bstep (se 1 (by rfl) ⟨29576987, by rfl⟩ : syracuseStep 39435983 = 59153975) B59153975
theorem B26290655 : Blo 2307435 26290655 := bstep (se 1 (by rfl) ⟨19717991, by rfl⟩ : syracuseStep 26290655 = 39435983) B39435983
theorem B17527103 : Blo 2307435 17527103 := bstep (se 1 (by rfl) ⟨13145327, by rfl⟩ : syracuseStep 17527103 = 26290655) B26290655
theorem B11684735 : Blo 2307435 11684735 := bstep (se 1 (by rfl) ⟨8763551, by rfl⟩ : syracuseStep 11684735 = 17527103) B17527103
theorem B7789823 : Blo 2307435 7789823 := bstep (se 1 (by rfl) ⟨5842367, by rfl⟩ : syracuseStep 7789823 = 11684735) B11684735
theorem B5193215 : Blo 2307435 5193215 := bstep (se 1 (by rfl) ⟨3894911, by rfl⟩ : syracuseStep 5193215 = 7789823) B7789823
theorem B3462143 : Blo 2307435 3462143 := bstep (se 1 (by rfl) ⟨2596607, by rfl⟩ : syracuseStep 3462143 = 5193215) B5193215
theorem B2308095 : Blo 2307435 2308095 := bstep (se 1 (by rfl) ⟨1731071, by rfl⟩ : syracuseStep 2308095 = 3462143) B3462143
theorem B3462149 : Blo 2307435 3462149 := bbase (se 4 (by rfl) ⟨324576, by rfl⟩ : syracuseStep 3462149 = 649153) (by norm_num)
theorem B2308099 : Blo 2307435 2308099 := bstep (se 1 (by rfl) ⟨1731074, by rfl⟩ : syracuseStep 2308099 = 3462149) B3462149
theorem B3894925 : Blo 2307435 3894925 := bbase (se 3 (by rfl) ⟨730298, by rfl⟩ : syracuseStep 3894925 = 1460597) (by norm_num)
theorem B5193233 : Blo 2307435 5193233 := bstep (se 2 (by rfl) ⟨1947462, by rfl⟩ : syracuseStep 5193233 = 3894925) B3894925
theorem B3462155 : Blo 2307435 3462155 := bstep (se 1 (by rfl) ⟨2596616, by rfl⟩ : syracuseStep 3462155 = 5193233) B5193233
theorem B2308103 : Blo 2307435 2308103 := bstep (se 1 (by rfl) ⟨1731077, by rfl⟩ : syracuseStep 2308103 = 3462155) B3462155
theorem B2596621 : Blo 2307435 2596621 := bbase (se 3 (by rfl) ⟨486866, by rfl⟩ : syracuseStep 2596621 = 973733) (by norm_num)
theorem B3462161 : Blo 2307435 3462161 := bstep (se 2 (by rfl) ⟨1298310, by rfl⟩ : syracuseStep 3462161 = 2596621) B2596621
theorem B2308107 : Blo 2307435 2308107 := bstep (se 1 (by rfl) ⟨1731080, by rfl⟩ : syracuseStep 2308107 = 3462161) B3462161
theorem B7789877 : Blo 2307435 7789877 := bbase (se 5 (by rfl) ⟨365150, by rfl⟩ : syracuseStep 7789877 = 730301) (by norm_num)
theorem B5193251 : Blo 2307435 5193251 := bstep (se 1 (by rfl) ⟨3894938, by rfl⟩ : syracuseStep 5193251 = 7789877) B7789877
theorem B3462167 : Blo 2307435 3462167 := bstep (se 1 (by rfl) ⟨2596625, by rfl⟩ : syracuseStep 3462167 = 5193251) B5193251
theorem B2308111 : Blo 2307435 2308111 := bstep (se 1 (by rfl) ⟨1731083, by rfl⟩ : syracuseStep 2308111 = 3462167) B3462167
theorem B3462173 : Blo 2307435 3462173 := bbase (se 3 (by rfl) ⟨649157, by rfl⟩ : syracuseStep 3462173 = 1298315) (by norm_num)
theorem B2308115 : Blo 2307435 2308115 := bstep (se 1 (by rfl) ⟨1731086, by rfl⟩ : syracuseStep 2308115 = 3462173) B3462173
theorem B5193269 : Blo 2307435 5193269 := bbase (se 5 (by rfl) ⟨243434, by rfl⟩ : syracuseStep 5193269 = 486869) (by norm_num)
theorem B3462179 : Blo 2307435 3462179 := bstep (se 1 (by rfl) ⟨2596634, by rfl⟩ : syracuseStep 3462179 = 5193269) B5193269
theorem B2308119 : Blo 2307435 2308119 := bstep (se 1 (by rfl) ⟨1731089, by rfl⟩ : syracuseStep 2308119 = 3462179) B3462179
theorem B2772877 : Blo 2307435 2772877 := bbase (se 3 (by rfl) ⟨519914, by rfl⟩ : syracuseStep 2772877 = 1039829) (by norm_num)
theorem B3697169 : Blo 2307435 3697169 := bstep (se 2 (by rfl) ⟨1386438, by rfl⟩ : syracuseStep 3697169 = 2772877) B2772877
theorem B9859117 : Blo 2307435 9859117 := bstep (se 3 (by rfl) ⟨1848584, by rfl⟩ : syracuseStep 9859117 = 3697169) B3697169
theorem B13145489 : Blo 2307435 13145489 := bstep (se 2 (by rfl) ⟨4929558, by rfl⟩ : syracuseStep 13145489 = 9859117) B9859117
theorem B8763659 : Blo 2307435 8763659 := bstep (se 1 (by rfl) ⟨6572744, by rfl⟩ : syracuseStep 8763659 = 13145489) B13145489
theorem B5842439 : Blo 2307435 5842439 := bstep (se 1 (by rfl) ⟨4381829, by rfl⟩ : syracuseStep 5842439 = 8763659) B8763659
theorem B3894959 : Blo 2307435 3894959 := bstep (se 1 (by rfl) ⟨2921219, by rfl⟩ : syracuseStep 3894959 = 5842439) B5842439
theorem B2596639 : Blo 2307435 2596639 := bstep (se 1 (by rfl) ⟨1947479, by rfl⟩ : syracuseStep 2596639 = 3894959) B3894959
theorem B3462185 : Blo 2307435 3462185 := bstep (se 2 (by rfl) ⟨1298319, by rfl⟩ : syracuseStep 3462185 = 2596639) B2596639
theorem B2308123 : Blo 2307435 2308123 := bstep (se 1 (by rfl) ⟨1731092, by rfl⟩ : syracuseStep 2308123 = 3462185) B3462185
theorem B8318645 : Blo 2307435 8318645 := bbase (se 5 (by rfl) ⟨389936, by rfl⟩ : syracuseStep 8318645 = 779873) (by norm_num)
theorem B5545763 : Blo 2307435 5545763 := bstep (se 1 (by rfl) ⟨4159322, by rfl⟩ : syracuseStep 5545763 = 8318645) B8318645
theorem B3697175 : Blo 2307435 3697175 := bstep (se 1 (by rfl) ⟨2772881, by rfl⟩ : syracuseStep 3697175 = 5545763) B5545763
theorem B9859133 : Blo 2307435 9859133 := bstep (se 3 (by rfl) ⟨1848587, by rfl⟩ : syracuseStep 9859133 = 3697175) B3697175
theorem B6572755 : Blo 2307435 6572755 := bstep (se 1 (by rfl) ⟨4929566, by rfl⟩ : syracuseStep 6572755 = 9859133) B9859133
theorem B8763673 : Blo 2307435 8763673 := bstep (se 2 (by rfl) ⟨3286377, by rfl⟩ : syracuseStep 8763673 = 6572755) B6572755
theorem B11684897 : Blo 2307435 11684897 := bstep (se 2 (by rfl) ⟨4381836, by rfl⟩ : syracuseStep 11684897 = 8763673) B8763673
theorem B7789931 : Blo 2307435 7789931 := bstep (se 1 (by rfl) ⟨5842448, by rfl⟩ : syracuseStep 7789931 = 11684897) B11684897
theorem B5193287 : Blo 2307435 5193287 := bstep (se 1 (by rfl) ⟨3894965, by rfl⟩ : syracuseStep 5193287 = 7789931) B7789931
theorem B3462191 : Blo 2307435 3462191 := bstep (se 1 (by rfl) ⟨2596643, by rfl⟩ : syracuseStep 3462191 = 5193287) B5193287
theorem B2308127 : Blo 2307435 2308127 := bstep (se 1 (by rfl) ⟨1731095, by rfl⟩ : syracuseStep 2308127 = 3462191) B3462191
theorem B3462197 : Blo 2307435 3462197 := bbase (se 5 (by rfl) ⟨162290, by rfl⟩ : syracuseStep 3462197 = 324581) (by norm_num)
theorem B2308131 : Blo 2307435 2308131 := bstep (se 1 (by rfl) ⟨1731098, by rfl⟩ : syracuseStep 2308131 = 3462197) B3462197
theorem B5842469 : Blo 2307435 5842469 := bbase (se 4 (by rfl) ⟨547731, by rfl⟩ : syracuseStep 5842469 = 1095463) (by norm_num)
theorem B3894979 : Blo 2307435 3894979 := bstep (se 1 (by rfl) ⟨2921234, by rfl⟩ : syracuseStep 3894979 = 5842469) B5842469
theorem B5193305 : Blo 2307435 5193305 := bstep (se 2 (by rfl) ⟨1947489, by rfl⟩ : syracuseStep 5193305 = 3894979) B3894979
theorem B3462203 : Blo 2307435 3462203 := bstep (se 1 (by rfl) ⟨2596652, by rfl⟩ : syracuseStep 3462203 = 5193305) B5193305
theorem B2308135 : Blo 2307435 2308135 := bstep (se 1 (by rfl) ⟨1731101, by rfl⟩ : syracuseStep 2308135 = 3462203) B3462203
theorem B2596657 : Blo 2307435 2596657 := bbase (se 2 (by rfl) ⟨973746, by rfl⟩ : syracuseStep 2596657 = 1947493) (by norm_num)
theorem B3462209 : Blo 2307435 3462209 := bstep (se 2 (by rfl) ⟨1298328, by rfl⟩ : syracuseStep 3462209 = 2596657) B2596657
theorem B2308139 : Blo 2307435 2308139 := bstep (se 1 (by rfl) ⟨1731104, by rfl⟩ : syracuseStep 2308139 = 3462209) B3462209
theorem B2772901 : Blo 2307435 2772901 := bbase (se 4 (by rfl) ⟨259959, by rfl⟩ : syracuseStep 2772901 = 519919) (by norm_num)
theorem B3697201 : Blo 2307435 3697201 := bstep (se 2 (by rfl) ⟨1386450, by rfl⟩ : syracuseStep 3697201 = 2772901) B2772901
theorem B4929601 : Blo 2307435 4929601 := bstep (se 2 (by rfl) ⟨1848600, by rfl⟩ : syracuseStep 4929601 = 3697201) B3697201
theorem B6572801 : Blo 2307435 6572801 := bstep (se 2 (by rfl) ⟨2464800, by rfl⟩ : syracuseStep 6572801 = 4929601) B4929601
theorem B4381867 : Blo 2307435 4381867 := bstep (se 1 (by rfl) ⟨3286400, by rfl⟩ : syracuseStep 4381867 = 6572801) B6572801
theorem B5842489 : Blo 2307435 5842489 := bstep (se 2 (by rfl) ⟨2190933, by rfl⟩ : syracuseStep 5842489 = 4381867) B4381867
theorem B7789985 : Blo 2307435 7789985 := bstep (se 2 (by rfl) ⟨2921244, by rfl⟩ : syracuseStep 7789985 = 5842489) B5842489
theorem B5193323 : Blo 2307435 5193323 := bstep (se 1 (by rfl) ⟨3894992, by rfl⟩ : syracuseStep 5193323 = 7789985) B7789985
theorem B3462215 : Blo 2307435 3462215 := bstep (se 1 (by rfl) ⟨2596661, by rfl⟩ : syracuseStep 3462215 = 5193323) B5193323
theorem B2308143 : Blo 2307435 2308143 := bstep (se 1 (by rfl) ⟨1731107, by rfl⟩ : syracuseStep 2308143 = 3462215) B3462215
theorem B3462221 : Blo 2307435 3462221 := bbase (se 3 (by rfl) ⟨649166, by rfl⟩ : syracuseStep 3462221 = 1298333) (by norm_num)
theorem B2308147 : Blo 2307435 2308147 := bstep (se 1 (by rfl) ⟨1731110, by rfl⟩ : syracuseStep 2308147 = 3462221) B3462221
theorem B5193341 : Blo 2307435 5193341 := bbase (se 3 (by rfl) ⟨973751, by rfl⟩ : syracuseStep 5193341 = 1947503) (by norm_num)
theorem B3462227 : Blo 2307435 3462227 := bstep (se 1 (by rfl) ⟨2596670, by rfl⟩ : syracuseStep 3462227 = 5193341) B5193341
theorem B2308151 : Blo 2307435 2308151 := bstep (se 1 (by rfl) ⟨1731113, by rfl⟩ : syracuseStep 2308151 = 3462227) B3462227
theorem B3895013 : Blo 2307435 3895013 := bbase (se 4 (by rfl) ⟨365157, by rfl⟩ : syracuseStep 3895013 = 730315) (by norm_num)
theorem B2596675 : Blo 2307435 2596675 := bstep (se 1 (by rfl) ⟨1947506, by rfl⟩ : syracuseStep 2596675 = 3895013) B3895013
theorem B3462233 : Blo 2307435 3462233 := bstep (se 2 (by rfl) ⟨1298337, by rfl⟩ : syracuseStep 3462233 = 2596675) B2596675
theorem B2308155 : Blo 2307435 2308155 := bstep (se 1 (by rfl) ⟨1731116, by rfl⟩ : syracuseStep 2308155 = 3462233) B3462233
theorem B7394453 : Blo 2307435 7394453 := bbase (se 6 (by rfl) ⟨173307, by rfl⟩ : syracuseStep 7394453 = 346615) (by norm_num)
theorem B4929635 : Blo 2307435 4929635 := bstep (se 1 (by rfl) ⟨3697226, by rfl⟩ : syracuseStep 4929635 = 7394453) B7394453
theorem B3286423 : Blo 2307435 3286423 := bstep (se 1 (by rfl) ⟨2464817, by rfl⟩ : syracuseStep 3286423 = 4929635) B4929635
theorem B17527589 : Blo 2307435 17527589 := bstep (se 4 (by rfl) ⟨1643211, by rfl⟩ : syracuseStep 17527589 = 3286423) B3286423
theorem B11685059 : Blo 2307435 11685059 := bstep (se 1 (by rfl) ⟨8763794, by rfl⟩ : syracuseStep 11685059 = 17527589) B17527589
theorem B7790039 : Blo 2307435 7790039 := bstep (se 1 (by rfl) ⟨5842529, by rfl⟩ : syracuseStep 7790039 = 11685059) B11685059
theorem B5193359 : Blo 2307435 5193359 := bstep (se 1 (by rfl) ⟨3895019, by rfl⟩ : syracuseStep 5193359 = 7790039) B7790039
theorem B3462239 : Blo 2307435 3462239 := bstep (se 1 (by rfl) ⟨2596679, by rfl⟩ : syracuseStep 3462239 = 5193359) B5193359
theorem B2308159 : Blo 2307435 2308159 := bstep (se 1 (by rfl) ⟨1731119, by rfl⟩ : syracuseStep 2308159 = 3462239) B3462239
theorem B3462245 : Blo 2307435 3462245 := bbase (se 4 (by rfl) ⟨324585, by rfl⟩ : syracuseStep 3462245 = 649171) (by norm_num)
theorem B2308163 : Blo 2307435 2308163 := bstep (se 1 (by rfl) ⟨1731122, by rfl⟩ : syracuseStep 2308163 = 3462245) B3462245
theorem B4929653 : Blo 2307435 4929653 := bbase (se 5 (by rfl) ⟨231077, by rfl⟩ : syracuseStep 4929653 = 462155) (by norm_num)
theorem B3286435 : Blo 2307435 3286435 := bstep (se 1 (by rfl) ⟨2464826, by rfl⟩ : syracuseStep 3286435 = 4929653) B4929653
theorem B4381913 : Blo 2307435 4381913 := bstep (se 2 (by rfl) ⟨1643217, by rfl⟩ : syracuseStep 4381913 = 3286435) B3286435
theorem B2921275 : Blo 2307435 2921275 := bstep (se 1 (by rfl) ⟨2190956, by rfl⟩ : syracuseStep 2921275 = 4381913) B4381913
theorem B3895033 : Blo 2307435 3895033 := bstep (se 2 (by rfl) ⟨1460637, by rfl⟩ : syracuseStep 3895033 = 2921275) B2921275
theorem B5193377 : Blo 2307435 5193377 := bstep (se 2 (by rfl) ⟨1947516, by rfl⟩ : syracuseStep 5193377 = 3895033) B3895033
theorem B3462251 : Blo 2307435 3462251 := bstep (se 1 (by rfl) ⟨2596688, by rfl⟩ : syracuseStep 3462251 = 5193377) B5193377
theorem B2308167 : Blo 2307435 2308167 := bstep (se 1 (by rfl) ⟨1731125, by rfl⟩ : syracuseStep 2308167 = 3462251) B3462251
theorem B2596693 : Blo 2307435 2596693 := bbase (se 9 (by rfl) ⟨7607, by rfl⟩ : syracuseStep 2596693 = 15215) (by norm_num)
theorem B3462257 : Blo 2307435 3462257 := bstep (se 2 (by rfl) ⟨1298346, by rfl⟩ : syracuseStep 3462257 = 2596693) B2596693
theorem B2308171 : Blo 2307435 2308171 := bstep (se 1 (by rfl) ⟨1731128, by rfl⟩ : syracuseStep 2308171 = 3462257) B3462257
theorem B2921285 : Blo 2307435 2921285 := bbase (se 4 (by rfl) ⟨273870, by rfl⟩ : syracuseStep 2921285 = 547741) (by norm_num)
theorem B7790093 : Blo 2307435 7790093 := bstep (se 3 (by rfl) ⟨1460642, by rfl⟩ : syracuseStep 7790093 = 2921285) B2921285
theorem B5193395 : Blo 2307435 5193395 := bstep (se 1 (by rfl) ⟨3895046, by rfl⟩ : syracuseStep 5193395 = 7790093) B7790093
theorem B3462263 : Blo 2307435 3462263 := bstep (se 1 (by rfl) ⟨2596697, by rfl⟩ : syracuseStep 3462263 = 5193395) B5193395
theorem B2308175 : Blo 2307435 2308175 := bstep (se 1 (by rfl) ⟨1731131, by rfl⟩ : syracuseStep 2308175 = 3462263) B3462263
theorem B3462269 : Blo 2307435 3462269 := bbase (se 3 (by rfl) ⟨649175, by rfl⟩ : syracuseStep 3462269 = 1298351) (by norm_num)
theorem B2308179 : Blo 2307435 2308179 := bstep (se 1 (by rfl) ⟨1731134, by rfl⟩ : syracuseStep 2308179 = 3462269) B3462269
theorem B5193413 : Blo 2307435 5193413 := bbase (se 4 (by rfl) ⟨486882, by rfl⟩ : syracuseStep 5193413 = 973765) (by norm_num)
theorem B3462275 : Blo 2307435 3462275 := bstep (se 1 (by rfl) ⟨2596706, by rfl⟩ : syracuseStep 3462275 = 5193413) B5193413
theorem B2308183 : Blo 2307435 2308183 := bstep (se 1 (by rfl) ⟨1731137, by rfl⟩ : syracuseStep 2308183 = 3462275) B3462275
theorem B3705005 : Blo 2307435 3705005 := bbase (se 3 (by rfl) ⟨694688, by rfl⟩ : syracuseStep 3705005 = 1389377) (by norm_num)
theorem B2470003 : Blo 2307435 2470003 := bstep (se 1 (by rfl) ⟨1852502, by rfl⟩ : syracuseStep 2470003 = 3705005) B3705005
theorem B13173349 : Blo 2307435 13173349 := bstep (se 4 (by rfl) ⟨1235001, by rfl⟩ : syracuseStep 13173349 = 2470003) B2470003
theorem B17564465 : Blo 2307435 17564465 := bstep (se 2 (by rfl) ⟨6586674, by rfl⟩ : syracuseStep 17564465 = 13173349) B13173349
theorem B11709643 : Blo 2307435 11709643 := bstep (se 1 (by rfl) ⟨8782232, by rfl⟩ : syracuseStep 11709643 = 17564465) B17564465
theorem B15612857 : Blo 2307435 15612857 := bstep (se 2 (by rfl) ⟨5854821, by rfl⟩ : syracuseStep 15612857 = 11709643) B11709643
theorem B10408571 : Blo 2307435 10408571 := bstep (se 1 (by rfl) ⟨7806428, by rfl⟩ : syracuseStep 10408571 = 15612857) B15612857
theorem B6939047 : Blo 2307435 6939047 := bstep (se 1 (by rfl) ⟨5204285, by rfl⟩ : syracuseStep 6939047 = 10408571) B10408571
theorem B18504125 : Blo 2307435 18504125 := bstep (se 3 (by rfl) ⟨3469523, by rfl⟩ : syracuseStep 18504125 = 6939047) B6939047
theorem B12336083 : Blo 2307435 12336083 := bstep (se 1 (by rfl) ⟨9252062, by rfl⟩ : syracuseStep 12336083 = 18504125) B18504125
theorem B8224055 : Blo 2307435 8224055 := bstep (se 1 (by rfl) ⟨6168041, by rfl⟩ : syracuseStep 8224055 = 12336083) B12336083
theorem B5482703 : Blo 2307435 5482703 := bstep (se 1 (by rfl) ⟨4112027, by rfl⟩ : syracuseStep 5482703 = 8224055) B8224055
theorem B3655135 : Blo 2307435 3655135 := bstep (se 1 (by rfl) ⟨2741351, by rfl⟩ : syracuseStep 3655135 = 5482703) B5482703
theorem B19494053 : Blo 2307435 19494053 := bstep (se 4 (by rfl) ⟨1827567, by rfl⟩ : syracuseStep 19494053 = 3655135) B3655135
theorem B12996035 : Blo 2307435 12996035 := bstep (se 1 (by rfl) ⟨9747026, by rfl⟩ : syracuseStep 12996035 = 19494053) B19494053
theorem B8664023 : Blo 2307435 8664023 := bstep (se 1 (by rfl) ⟨6498017, by rfl⟩ : syracuseStep 8664023 = 12996035) B12996035
theorem B23104061 : Blo 2307435 23104061 := bstep (se 3 (by rfl) ⟨4332011, by rfl⟩ : syracuseStep 23104061 = 8664023) B8664023
theorem B15402707 : Blo 2307435 15402707 := bstep (se 1 (by rfl) ⟨11552030, by rfl⟩ : syracuseStep 15402707 = 23104061) B23104061
theorem B10268471 : Blo 2307435 10268471 := bstep (se 1 (by rfl) ⟨7701353, by rfl⟩ : syracuseStep 10268471 = 15402707) B15402707
theorem B6845647 : Blo 2307435 6845647 := bstep (se 1 (by rfl) ⟨5134235, by rfl⟩ : syracuseStep 6845647 = 10268471) B10268471
theorem B9127529 : Blo 2307435 9127529 := bstep (se 2 (by rfl) ⟨3422823, by rfl⟩ : syracuseStep 9127529 = 6845647) B6845647
theorem B6085019 : Blo 2307435 6085019 := bstep (se 1 (by rfl) ⟨4563764, by rfl⟩ : syracuseStep 6085019 = 9127529) B9127529
theorem B4056679 : Blo 2307435 4056679 := bstep (se 1 (by rfl) ⟨3042509, by rfl⟩ : syracuseStep 4056679 = 6085019) B6085019
theorem B5408905 : Blo 2307435 5408905 := bstep (se 2 (by rfl) ⟨2028339, by rfl⟩ : syracuseStep 5408905 = 4056679) B4056679
theorem B7211873 : Blo 2307435 7211873 := bstep (se 2 (by rfl) ⟨2704452, by rfl⟩ : syracuseStep 7211873 = 5408905) B5408905
theorem B19231661 : Blo 2307435 19231661 := bstep (se 3 (by rfl) ⟨3605936, by rfl⟩ : syracuseStep 19231661 = 7211873) B7211873
theorem B12821107 : Blo 2307435 12821107 := bstep (se 1 (by rfl) ⟨9615830, by rfl⟩ : syracuseStep 12821107 = 19231661) B19231661
theorem B17094809 : Blo 2307435 17094809 := bstep (se 2 (by rfl) ⟨6410553, by rfl⟩ : syracuseStep 17094809 = 12821107) B12821107
theorem B11396539 : Blo 2307435 11396539 := bstep (se 1 (by rfl) ⟨8547404, by rfl⟩ : syracuseStep 11396539 = 17094809) B17094809
theorem B15195385 : Blo 2307435 15195385 := bstep (se 2 (by rfl) ⟨5698269, by rfl⟩ : syracuseStep 15195385 = 11396539) B11396539
theorem B20260513 : Blo 2307435 20260513 := bstep (se 2 (by rfl) ⟨7597692, by rfl⟩ : syracuseStep 20260513 = 15195385) B15195385
theorem B27014017 : Blo 2307435 27014017 := bstep (se 2 (by rfl) ⟨10130256, by rfl⟩ : syracuseStep 27014017 = 20260513) B20260513
theorem B36018689 : Blo 2307435 36018689 := bstep (se 2 (by rfl) ⟨13507008, by rfl⟩ : syracuseStep 36018689 = 27014017) B27014017
theorem B96049837 : Blo 2307435 96049837 := bstep (se 3 (by rfl) ⟨18009344, by rfl⟩ : syracuseStep 96049837 = 36018689) B36018689
theorem B128066449 : Blo 2307435 128066449 := bstep (se 2 (by rfl) ⟨48024918, by rfl⟩ : syracuseStep 128066449 = 96049837) B96049837
theorem B170755265 : Blo 2307435 170755265 := bstep (se 2 (by rfl) ⟨64033224, by rfl⟩ : syracuseStep 170755265 = 128066449) B128066449
theorem B113836843 : Blo 2307435 113836843 := bstep (se 1 (by rfl) ⟨85377632, by rfl⟩ : syracuseStep 113836843 = 170755265) B170755265
theorem B151782457 : Blo 2307435 151782457 := bstep (se 2 (by rfl) ⟨56918421, by rfl⟩ : syracuseStep 151782457 = 113836843) B113836843
theorem B202376609 : Blo 2307435 202376609 := bstep (se 2 (by rfl) ⟨75891228, by rfl⟩ : syracuseStep 202376609 = 151782457) B151782457
theorem B134917739 : Blo 2307435 134917739 := bstep (se 1 (by rfl) ⟨101188304, by rfl⟩ : syracuseStep 134917739 = 202376609) B202376609
theorem B89945159 : Blo 2307435 89945159 := bstep (se 1 (by rfl) ⟨67458869, by rfl⟩ : syracuseStep 89945159 = 134917739) B134917739
theorem B239853757 : Blo 2307435 239853757 := bstep (se 3 (by rfl) ⟨44972579, by rfl⟩ : syracuseStep 239853757 = 89945159) B89945159
theorem B319805009 : Blo 2307435 319805009 := bstep (se 2 (by rfl) ⟨119926878, by rfl⟩ : syracuseStep 319805009 = 239853757) B239853757
theorem B213203339 : Blo 2307435 213203339 := bstep (se 1 (by rfl) ⟨159902504, by rfl⟩ : syracuseStep 213203339 = 319805009) B319805009
theorem B142135559 : Blo 2307435 142135559 := bstep (se 1 (by rfl) ⟨106601669, by rfl⟩ : syracuseStep 142135559 = 213203339) B213203339
theorem B94757039 : Blo 2307435 94757039 := bstep (se 1 (by rfl) ⟨71067779, by rfl⟩ : syracuseStep 94757039 = 142135559) B142135559
theorem B63171359 : Blo 2307435 63171359 := bstep (se 1 (by rfl) ⟨47378519, by rfl⟩ : syracuseStep 63171359 = 94757039) B94757039
theorem B42114239 : Blo 2307435 42114239 := bstep (se 1 (by rfl) ⟨31585679, by rfl⟩ : syracuseStep 42114239 = 63171359) B63171359
theorem B28076159 : Blo 2307435 28076159 := bstep (se 1 (by rfl) ⟨21057119, by rfl⟩ : syracuseStep 28076159 = 42114239) B42114239
theorem B74869757 : Blo 2307435 74869757 := bstep (se 3 (by rfl) ⟨14038079, by rfl⟩ : syracuseStep 74869757 = 28076159) B28076159
theorem B49913171 : Blo 2307435 49913171 := bstep (se 1 (by rfl) ⟨37434878, by rfl⟩ : syracuseStep 49913171 = 74869757) B74869757
theorem B33275447 : Blo 2307435 33275447 := bstep (se 1 (by rfl) ⟨24956585, by rfl⟩ : syracuseStep 33275447 = 49913171) B49913171
theorem B22183631 : Blo 2307435 22183631 := bstep (se 1 (by rfl) ⟨16637723, by rfl⟩ : syracuseStep 22183631 = 33275447) B33275447
theorem B14789087 : Blo 2307435 14789087 := bstep (se 1 (by rfl) ⟨11091815, by rfl⟩ : syracuseStep 14789087 = 22183631) B22183631
theorem B9859391 : Blo 2307435 9859391 := bstep (se 1 (by rfl) ⟨7394543, by rfl⟩ : syracuseStep 9859391 = 14789087) B14789087
theorem B6572927 : Blo 2307435 6572927 := bstep (se 1 (by rfl) ⟨4929695, by rfl⟩ : syracuseStep 6572927 = 9859391) B9859391
theorem B4381951 : Blo 2307435 4381951 := bstep (se 1 (by rfl) ⟨3286463, by rfl⟩ : syracuseStep 4381951 = 6572927) B6572927
theorem B5842601 : Blo 2307435 5842601 := bstep (se 2 (by rfl) ⟨2190975, by rfl⟩ : syracuseStep 5842601 = 4381951) B4381951
theorem B3895067 : Blo 2307435 3895067 := bstep (se 1 (by rfl) ⟨2921300, by rfl⟩ : syracuseStep 3895067 = 5842601) B5842601
theorem B2596711 : Blo 2307435 2596711 := bstep (se 1 (by rfl) ⟨1947533, by rfl⟩ : syracuseStep 2596711 = 3895067) B3895067
theorem B3462281 : Blo 2307435 3462281 := bstep (se 2 (by rfl) ⟨1298355, by rfl⟩ : syracuseStep 3462281 = 2596711) B2596711
theorem B2308187 : Blo 2307435 2308187 := bstep (se 1 (by rfl) ⟨1731140, by rfl⟩ : syracuseStep 2308187 = 3462281) B3462281
theorem B11685221 : Blo 2307435 11685221 := bbase (se 4 (by rfl) ⟨1095489, by rfl⟩ : syracuseStep 11685221 = 2190979) (by norm_num)
theorem B7790147 : Blo 2307435 7790147 := bstep (se 1 (by rfl) ⟨5842610, by rfl⟩ : syracuseStep 7790147 = 11685221) B11685221
theorem B5193431 : Blo 2307435 5193431 := bstep (se 1 (by rfl) ⟨3895073, by rfl⟩ : syracuseStep 5193431 = 7790147) B7790147
theorem B3462287 : Blo 2307435 3462287 := bstep (se 1 (by rfl) ⟨2596715, by rfl⟩ : syracuseStep 3462287 = 5193431) B5193431
theorem B2308191 : Blo 2307435 2308191 := bstep (se 1 (by rfl) ⟨1731143, by rfl⟩ : syracuseStep 2308191 = 3462287) B3462287
theorem B3462293 : Blo 2307435 3462293 := bbase (se 6 (by rfl) ⟨81147, by rfl⟩ : syracuseStep 3462293 = 162295) (by norm_num)
theorem B2308195 : Blo 2307435 2308195 := bstep (se 1 (by rfl) ⟨1731146, by rfl⟩ : syracuseStep 2308195 = 3462293) B3462293
theorem B7394581 : Blo 2307435 7394581 := bbase (se 6 (by rfl) ⟨173310, by rfl⟩ : syracuseStep 7394581 = 346621) (by norm_num)
theorem B9859441 : Blo 2307435 9859441 := bstep (se 2 (by rfl) ⟨3697290, by rfl⟩ : syracuseStep 9859441 = 7394581) B7394581
theorem B13145921 : Blo 2307435 13145921 := bstep (se 2 (by rfl) ⟨4929720, by rfl⟩ : syracuseStep 13145921 = 9859441) B9859441
theorem B8763947 : Blo 2307435 8763947 := bstep (se 1 (by rfl) ⟨6572960, by rfl⟩ : syracuseStep 8763947 = 13145921) B13145921
theorem B5842631 : Blo 2307435 5842631 := bstep (se 1 (by rfl) ⟨4381973, by rfl⟩ : syracuseStep 5842631 = 8763947) B8763947
theorem B3895087 : Blo 2307435 3895087 := bstep (se 1 (by rfl) ⟨2921315, by rfl⟩ : syracuseStep 3895087 = 5842631) B5842631
theorem B5193449 : Blo 2307435 5193449 := bstep (se 2 (by rfl) ⟨1947543, by rfl⟩ : syracuseStep 5193449 = 3895087) B3895087
theorem B3462299 : Blo 2307435 3462299 := bstep (se 1 (by rfl) ⟨2596724, by rfl⟩ : syracuseStep 3462299 = 5193449) B5193449
theorem B2308199 : Blo 2307435 2308199 := bstep (se 1 (by rfl) ⟨1731149, by rfl⟩ : syracuseStep 2308199 = 3462299) B3462299
theorem B2596729 : Blo 2307435 2596729 := bbase (se 2 (by rfl) ⟨973773, by rfl⟩ : syracuseStep 2596729 = 1947547) (by norm_num)
theorem B3462305 : Blo 2307435 3462305 := bstep (se 2 (by rfl) ⟨1298364, by rfl⟩ : syracuseStep 3462305 = 2596729) B2596729
theorem B2308203 : Blo 2307435 2308203 := bstep (se 1 (by rfl) ⟨1731152, by rfl⟩ : syracuseStep 2308203 = 3462305) B3462305
theorem B8318933 : Blo 2307435 8318933 := bbase (se 7 (by rfl) ⟨97487, by rfl⟩ : syracuseStep 8318933 = 194975) (by norm_num)
theorem B5545955 : Blo 2307435 5545955 := bstep (se 1 (by rfl) ⟨4159466, by rfl⟩ : syracuseStep 5545955 = 8318933) B8318933
theorem B14789213 : Blo 2307435 14789213 := bstep (se 3 (by rfl) ⟨2772977, by rfl⟩ : syracuseStep 14789213 = 5545955) B5545955
theorem B9859475 : Blo 2307435 9859475 := bstep (se 1 (by rfl) ⟨7394606, by rfl⟩ : syracuseStep 9859475 = 14789213) B14789213
theorem B6572983 : Blo 2307435 6572983 := bstep (se 1 (by rfl) ⟨4929737, by rfl⟩ : syracuseStep 6572983 = 9859475) B9859475
theorem B8763977 : Blo 2307435 8763977 := bstep (se 2 (by rfl) ⟨3286491, by rfl⟩ : syracuseStep 8763977 = 6572983) B6572983
theorem B5842651 : Blo 2307435 5842651 := bstep (se 1 (by rfl) ⟨4381988, by rfl⟩ : syracuseStep 5842651 = 8763977) B8763977
theorem B7790201 : Blo 2307435 7790201 := bstep (se 2 (by rfl) ⟨2921325, by rfl⟩ : syracuseStep 7790201 = 5842651) B5842651
theorem B5193467 : Blo 2307435 5193467 := bstep (se 1 (by rfl) ⟨3895100, by rfl⟩ : syracuseStep 5193467 = 7790201) B7790201
theorem B3462311 : Blo 2307435 3462311 := bstep (se 1 (by rfl) ⟨2596733, by rfl⟩ : syracuseStep 3462311 = 5193467) B5193467
theorem B2308207 : Blo 2307435 2308207 := bstep (se 1 (by rfl) ⟨1731155, by rfl⟩ : syracuseStep 2308207 = 3462311) B3462311
theorem B3462317 : Blo 2307435 3462317 := bbase (se 3 (by rfl) ⟨649184, by rfl⟩ : syracuseStep 3462317 = 1298369) (by norm_num)
theorem B2308211 : Blo 2307435 2308211 := bstep (se 1 (by rfl) ⟨1731158, by rfl⟩ : syracuseStep 2308211 = 3462317) B3462317
theorem B5193485 : Blo 2307435 5193485 := bbase (se 3 (by rfl) ⟨973778, by rfl⟩ : syracuseStep 5193485 = 1947557) (by norm_num)
theorem B3462323 : Blo 2307435 3462323 := bstep (se 1 (by rfl) ⟨2596742, by rfl⟩ : syracuseStep 3462323 = 5193485) B5193485
theorem B2308215 : Blo 2307435 2308215 := bstep (se 1 (by rfl) ⟨1731161, by rfl⟩ : syracuseStep 2308215 = 3462323) B3462323
theorem B2921341 : Blo 2307435 2921341 := bbase (se 3 (by rfl) ⟨547751, by rfl⟩ : syracuseStep 2921341 = 1095503) (by norm_num)
theorem B3895121 : Blo 2307435 3895121 := bstep (se 2 (by rfl) ⟨1460670, by rfl⟩ : syracuseStep 3895121 = 2921341) B2921341
theorem B2596747 : Blo 2307435 2596747 := bstep (se 1 (by rfl) ⟨1947560, by rfl⟩ : syracuseStep 2596747 = 3895121) B3895121
theorem B3462329 : Blo 2307435 3462329 := bstep (se 2 (by rfl) ⟨1298373, by rfl⟩ : syracuseStep 3462329 = 2596747) B2596747
theorem B2308219 : Blo 2307435 2308219 := bstep (se 1 (by rfl) ⟨1731164, by rfl⟩ : syracuseStep 2308219 = 3462329) B3462329
theorem B2632181 : Blo 2307435 2632181 := bbase (se 5 (by rfl) ⟨123383, by rfl⟩ : syracuseStep 2632181 = 246767) (by norm_num)
theorem B7019149 : Blo 2307435 7019149 := bstep (se 3 (by rfl) ⟨1316090, by rfl⟩ : syracuseStep 7019149 = 2632181) B2632181
theorem B9358865 : Blo 2307435 9358865 := bstep (se 2 (by rfl) ⟨3509574, by rfl⟩ : syracuseStep 9358865 = 7019149) B7019149
theorem B6239243 : Blo 2307435 6239243 := bstep (se 1 (by rfl) ⟨4679432, by rfl⟩ : syracuseStep 6239243 = 9358865) B9358865
theorem B4159495 : Blo 2307435 4159495 := bstep (se 1 (by rfl) ⟨3119621, by rfl⟩ : syracuseStep 4159495 = 6239243) B6239243
theorem B5545993 : Blo 2307435 5545993 := bstep (se 2 (by rfl) ⟨2079747, by rfl⟩ : syracuseStep 5545993 = 4159495) B4159495
theorem B7394657 : Blo 2307435 7394657 := bstep (se 2 (by rfl) ⟨2772996, by rfl⟩ : syracuseStep 7394657 = 5545993) B5545993
theorem B19719085 : Blo 2307435 19719085 := bstep (se 3 (by rfl) ⟨3697328, by rfl⟩ : syracuseStep 19719085 = 7394657) B7394657
theorem B26292113 : Blo 2307435 26292113 := bstep (se 2 (by rfl) ⟨9859542, by rfl⟩ : syracuseStep 26292113 = 19719085) B19719085
theorem B17528075 : Blo 2307435 17528075 := bstep (se 1 (by rfl) ⟨13146056, by rfl⟩ : syracuseStep 17528075 = 26292113) B26292113
theorem B11685383 : Blo 2307435 11685383 := bstep (se 1 (by rfl) ⟨8764037, by rfl⟩ : syracuseStep 11685383 = 17528075) B17528075
theorem B7790255 : Blo 2307435 7790255 := bstep (se 1 (by rfl) ⟨5842691, by rfl⟩ : syracuseStep 7790255 = 11685383) B11685383
theorem B5193503 : Blo 2307435 5193503 := bstep (se 1 (by rfl) ⟨3895127, by rfl⟩ : syracuseStep 5193503 = 7790255) B7790255
theorem B3462335 : Blo 2307435 3462335 := bstep (se 1 (by rfl) ⟨2596751, by rfl⟩ : syracuseStep 3462335 = 5193503) B5193503
theorem B2308223 : Blo 2307435 2308223 := bstep (se 1 (by rfl) ⟨1731167, by rfl⟩ : syracuseStep 2308223 = 3462335) B3462335
theorem B3462341 : Blo 2307435 3462341 := bbase (se 4 (by rfl) ⟨324594, by rfl⟩ : syracuseStep 3462341 = 649189) (by norm_num)
theorem B2308227 : Blo 2307435 2308227 := bstep (se 1 (by rfl) ⟨1731170, by rfl⟩ : syracuseStep 2308227 = 3462341) B3462341
theorem B3895141 : Blo 2307435 3895141 := bbase (se 4 (by rfl) ⟨365169, by rfl⟩ : syracuseStep 3895141 = 730339) (by norm_num)
theorem B5193521 : Blo 2307435 5193521 := bstep (se 2 (by rfl) ⟨1947570, by rfl⟩ : syracuseStep 5193521 = 3895141) B3895141
theorem B3462347 : Blo 2307435 3462347 := bstep (se 1 (by rfl) ⟨2596760, by rfl⟩ : syracuseStep 3462347 = 5193521) B5193521
theorem B2308231 : Blo 2307435 2308231 := bstep (se 1 (by rfl) ⟨1731173, by rfl⟩ : syracuseStep 2308231 = 3462347) B3462347
theorem B2596765 : Blo 2307435 2596765 := bbase (se 3 (by rfl) ⟨486893, by rfl⟩ : syracuseStep 2596765 = 973787) (by norm_num)
theorem B3462353 : Blo 2307435 3462353 := bstep (se 2 (by rfl) ⟨1298382, by rfl⟩ : syracuseStep 3462353 = 2596765) B2596765
theorem B2308235 : Blo 2307435 2308235 := bstep (se 1 (by rfl) ⟨1731176, by rfl⟩ : syracuseStep 2308235 = 3462353) B3462353
theorem B7790309 : Blo 2307435 7790309 := bbase (se 4 (by rfl) ⟨730341, by rfl⟩ : syracuseStep 7790309 = 1460683) (by norm_num)
theorem B5193539 : Blo 2307435 5193539 := bstep (se 1 (by rfl) ⟨3895154, by rfl⟩ : syracuseStep 5193539 = 7790309) B7790309
theorem B3462359 : Blo 2307435 3462359 := bstep (se 1 (by rfl) ⟨2596769, by rfl⟩ : syracuseStep 3462359 = 5193539) B5193539
theorem B2308239 : Blo 2307435 2308239 := bstep (se 1 (by rfl) ⟨1731179, by rfl⟩ : syracuseStep 2308239 = 3462359) B3462359
theorem B3462365 : Blo 2307435 3462365 := bbase (se 3 (by rfl) ⟨649193, by rfl⟩ : syracuseStep 3462365 = 1298387) (by norm_num)
theorem B2308243 : Blo 2307435 2308243 := bstep (se 1 (by rfl) ⟨1731182, by rfl⟩ : syracuseStep 2308243 = 3462365) B3462365
theorem B5193557 : Blo 2307435 5193557 := bbase (se 9 (by rfl) ⟨15215, by rfl⟩ : syracuseStep 5193557 = 30431) (by norm_num)
theorem B3462371 : Blo 2307435 3462371 := bstep (se 1 (by rfl) ⟨2596778, by rfl⟩ : syracuseStep 3462371 = 5193557) B5193557
theorem B2308247 : Blo 2307435 2308247 := bstep (se 1 (by rfl) ⟨1731185, by rfl⟩ : syracuseStep 2308247 = 3462371) B3462371
theorem B6573109 : Blo 2307435 6573109 := bbase (se 5 (by rfl) ⟨308114, by rfl⟩ : syracuseStep 6573109 = 616229) (by norm_num)
theorem B8764145 : Blo 2307435 8764145 := bstep (se 2 (by rfl) ⟨3286554, by rfl⟩ : syracuseStep 8764145 = 6573109) B6573109
theorem B5842763 : Blo 2307435 5842763 := bstep (se 1 (by rfl) ⟨4382072, by rfl⟩ : syracuseStep 5842763 = 8764145) B8764145
theorem B3895175 : Blo 2307435 3895175 := bstep (se 1 (by rfl) ⟨2921381, by rfl⟩ : syracuseStep 3895175 = 5842763) B5842763
theorem B2596783 : Blo 2307435 2596783 := bstep (se 1 (by rfl) ⟨1947587, by rfl⟩ : syracuseStep 2596783 = 3895175) B3895175
theorem B3462377 : Blo 2307435 3462377 := bstep (se 2 (by rfl) ⟨1298391, by rfl⟩ : syracuseStep 3462377 = 2596783) B2596783
theorem B2308251 : Blo 2307435 2308251 := bstep (se 1 (by rfl) ⟨1731188, by rfl⟩ : syracuseStep 2308251 = 3462377) B3462377
theorem B15793301 : Blo 2307435 15793301 := bbase (se 6 (by rfl) ⟨370155, by rfl⟩ : syracuseStep 15793301 = 740311) (by norm_num)
theorem B42115469 : Blo 2307435 42115469 := bstep (se 3 (by rfl) ⟨7896650, by rfl⟩ : syracuseStep 42115469 = 15793301) B15793301
theorem B112307917 : Blo 2307435 112307917 := bstep (se 3 (by rfl) ⟨21057734, by rfl⟩ : syracuseStep 112307917 = 42115469) B42115469
theorem B149743889 : Blo 2307435 149743889 := bstep (se 2 (by rfl) ⟨56153958, by rfl⟩ : syracuseStep 149743889 = 112307917) B112307917
theorem B99829259 : Blo 2307435 99829259 := bstep (se 1 (by rfl) ⟨74871944, by rfl⟩ : syracuseStep 99829259 = 149743889) B149743889
theorem B66552839 : Blo 2307435 66552839 := bstep (se 1 (by rfl) ⟨49914629, by rfl⟩ : syracuseStep 66552839 = 99829259) B99829259
theorem B44368559 : Blo 2307435 44368559 := bstep (se 1 (by rfl) ⟨33276419, by rfl⟩ : syracuseStep 44368559 = 66552839) B66552839
theorem B29579039 : Blo 2307435 29579039 := bstep (se 1 (by rfl) ⟨22184279, by rfl⟩ : syracuseStep 29579039 = 44368559) B44368559
theorem B19719359 : Blo 2307435 19719359 := bstep (se 1 (by rfl) ⟨14789519, by rfl⟩ : syracuseStep 19719359 = 29579039) B29579039
theorem B13146239 : Blo 2307435 13146239 := bstep (se 1 (by rfl) ⟨9859679, by rfl⟩ : syracuseStep 13146239 = 19719359) B19719359
theorem B8764159 : Blo 2307435 8764159 := bstep (se 1 (by rfl) ⟨6573119, by rfl⟩ : syracuseStep 8764159 = 13146239) B13146239
theorem B11685545 : Blo 2307435 11685545 := bstep (se 2 (by rfl) ⟨4382079, by rfl⟩ : syracuseStep 11685545 = 8764159) B8764159
theorem B7790363 : Blo 2307435 7790363 := bstep (se 1 (by rfl) ⟨5842772, by rfl⟩ : syracuseStep 7790363 = 11685545) B11685545
theorem B5193575 : Blo 2307435 5193575 := bstep (se 1 (by rfl) ⟨3895181, by rfl⟩ : syracuseStep 5193575 = 7790363) B7790363
theorem B3462383 : Blo 2307435 3462383 := bstep (se 1 (by rfl) ⟨2596787, by rfl⟩ : syracuseStep 3462383 = 5193575) B5193575
theorem B2308255 : Blo 2307435 2308255 := bstep (se 1 (by rfl) ⟨1731191, by rfl⟩ : syracuseStep 2308255 = 3462383) B3462383
theorem B3462389 : Blo 2307435 3462389 := bbase (se 5 (by rfl) ⟨162299, by rfl⟩ : syracuseStep 3462389 = 324599) (by norm_num)
theorem B2308259 : Blo 2307435 2308259 := bstep (se 1 (by rfl) ⟨1731194, by rfl⟩ : syracuseStep 2308259 = 3462389) B3462389
theorem B2773045 : Blo 2307435 2773045 := bbase (se 5 (by rfl) ⟨129986, by rfl⟩ : syracuseStep 2773045 = 259973) (by norm_num)
theorem B14789573 : Blo 2307435 14789573 := bstep (se 4 (by rfl) ⟨1386522, by rfl⟩ : syracuseStep 14789573 = 2773045) B2773045
theorem B9859715 : Blo 2307435 9859715 := bstep (se 1 (by rfl) ⟨7394786, by rfl⟩ : syracuseStep 9859715 = 14789573) B14789573
theorem B6573143 : Blo 2307435 6573143 := bstep (se 1 (by rfl) ⟨4929857, by rfl⟩ : syracuseStep 6573143 = 9859715) B9859715
theorem B4382095 : Blo 2307435 4382095 := bstep (se 1 (by rfl) ⟨3286571, by rfl⟩ : syracuseStep 4382095 = 6573143) B6573143
theorem B5842793 : Blo 2307435 5842793 := bstep (se 2 (by rfl) ⟨2191047, by rfl⟩ : syracuseStep 5842793 = 4382095) B4382095
theorem B3895195 : Blo 2307435 3895195 := bstep (se 1 (by rfl) ⟨2921396, by rfl⟩ : syracuseStep 3895195 = 5842793) B5842793
theorem B5193593 : Blo 2307435 5193593 := bstep (se 2 (by rfl) ⟨1947597, by rfl⟩ : syracuseStep 5193593 = 3895195) B3895195
theorem B3462395 : Blo 2307435 3462395 := bstep (se 1 (by rfl) ⟨2596796, by rfl⟩ : syracuseStep 3462395 = 5193593) B5193593
theorem B2308263 : Blo 2307435 2308263 := bstep (se 1 (by rfl) ⟨1731197, by rfl⟩ : syracuseStep 2308263 = 3462395) B3462395
theorem B2596801 : Blo 2307435 2596801 := bbase (se 2 (by rfl) ⟨973800, by rfl⟩ : syracuseStep 2596801 = 1947601) (by norm_num)
theorem B3462401 : Blo 2307435 3462401 := bstep (se 2 (by rfl) ⟨1298400, by rfl⟩ : syracuseStep 3462401 = 2596801) B2596801
theorem B2308267 : Blo 2307435 2308267 := bstep (se 1 (by rfl) ⟨1731200, by rfl⟩ : syracuseStep 2308267 = 3462401) B3462401
theorem B5842813 : Blo 2307435 5842813 := bbase (se 3 (by rfl) ⟨1095527, by rfl⟩ : syracuseStep 5842813 = 2191055) (by norm_num)
theorem B7790417 : Blo 2307435 7790417 := bstep (se 2 (by rfl) ⟨2921406, by rfl⟩ : syracuseStep 7790417 = 5842813) B5842813
theorem B5193611 : Blo 2307435 5193611 := bstep (se 1 (by rfl) ⟨3895208, by rfl⟩ : syracuseStep 5193611 = 7790417) B7790417
theorem B3462407 : Blo 2307435 3462407 := bstep (se 1 (by rfl) ⟨2596805, by rfl⟩ : syracuseStep 3462407 = 5193611) B5193611
theorem B2308271 : Blo 2307435 2308271 := bstep (se 1 (by rfl) ⟨1731203, by rfl⟩ : syracuseStep 2308271 = 3462407) B3462407
theorem B3462413 : Blo 2307435 3462413 := bbase (se 3 (by rfl) ⟨649202, by rfl⟩ : syracuseStep 3462413 = 1298405) (by norm_num)
theorem B2308275 : Blo 2307435 2308275 := bstep (se 1 (by rfl) ⟨1731206, by rfl⟩ : syracuseStep 2308275 = 3462413) B3462413
theorem B5193629 : Blo 2307435 5193629 := bbase (se 3 (by rfl) ⟨973805, by rfl⟩ : syracuseStep 5193629 = 1947611) (by norm_num)
theorem B3462419 : Blo 2307435 3462419 := bstep (se 1 (by rfl) ⟨2596814, by rfl⟩ : syracuseStep 3462419 = 5193629) B5193629
theorem B2308279 : Blo 2307435 2308279 := bstep (se 1 (by rfl) ⟨1731209, by rfl⟩ : syracuseStep 2308279 = 3462419) B3462419
theorem B3895229 : Blo 2307435 3895229 := bbase (se 3 (by rfl) ⟨730355, by rfl⟩ : syracuseStep 3895229 = 1460711) (by norm_num)
theorem B2596819 : Blo 2307435 2596819 := bstep (se 1 (by rfl) ⟨1947614, by rfl⟩ : syracuseStep 2596819 = 3895229) B3895229
theorem B3462425 : Blo 2307435 3462425 := bstep (se 2 (by rfl) ⟨1298409, by rfl⟩ : syracuseStep 3462425 = 2596819) B2596819
theorem B2308283 : Blo 2307435 2308283 := bstep (se 1 (by rfl) ⟨1731212, by rfl⟩ : syracuseStep 2308283 = 3462425) B3462425
theorem B13146421 : Blo 2307435 13146421 := bbase (se 5 (by rfl) ⟨616238, by rfl⟩ : syracuseStep 13146421 = 1232477) (by norm_num)
theorem B17528561 : Blo 2307435 17528561 := bstep (se 2 (by rfl) ⟨6573210, by rfl⟩ : syracuseStep 17528561 = 13146421) B13146421
theorem B11685707 : Blo 2307435 11685707 := bstep (se 1 (by rfl) ⟨8764280, by rfl⟩ : syracuseStep 11685707 = 17528561) B17528561
theorem B7790471 : Blo 2307435 7790471 := bstep (se 1 (by rfl) ⟨5842853, by rfl⟩ : syracuseStep 7790471 = 11685707) B11685707
theorem B5193647 : Blo 2307435 5193647 := bstep (se 1 (by rfl) ⟨3895235, by rfl⟩ : syracuseStep 5193647 = 7790471) B7790471
theorem B3462431 : Blo 2307435 3462431 := bstep (se 1 (by rfl) ⟨2596823, by rfl⟩ : syracuseStep 3462431 = 5193647) B5193647
theorem B2308287 : Blo 2307435 2308287 := bstep (se 1 (by rfl) ⟨1731215, by rfl⟩ : syracuseStep 2308287 = 3462431) B3462431
theorem B3462437 : Blo 2307435 3462437 := bbase (se 4 (by rfl) ⟨324603, by rfl⟩ : syracuseStep 3462437 = 649207) (by norm_num)
theorem B2308291 : Blo 2307435 2308291 := bstep (se 1 (by rfl) ⟨1731218, by rfl⟩ : syracuseStep 2308291 = 3462437) B3462437
theorem B2921437 : Blo 2307435 2921437 := bbase (se 3 (by rfl) ⟨547769, by rfl⟩ : syracuseStep 2921437 = 1095539) (by norm_num)
theorem B3895249 : Blo 2307435 3895249 := bstep (se 2 (by rfl) ⟨1460718, by rfl⟩ : syracuseStep 3895249 = 2921437) B2921437
theorem B5193665 : Blo 2307435 5193665 := bstep (se 2 (by rfl) ⟨1947624, by rfl⟩ : syracuseStep 5193665 = 3895249) B3895249
theorem B3462443 : Blo 2307435 3462443 := bstep (se 1 (by rfl) ⟨2596832, by rfl⟩ : syracuseStep 3462443 = 5193665) B5193665
theorem B2308295 : Blo 2307435 2308295 := bstep (se 1 (by rfl) ⟨1731221, by rfl⟩ : syracuseStep 2308295 = 3462443) B3462443
theorem B2596837 : Blo 2307435 2596837 := bbase (se 4 (by rfl) ⟨243453, by rfl⟩ : syracuseStep 2596837 = 486907) (by norm_num)
theorem B3462449 : Blo 2307435 3462449 := bstep (se 2 (by rfl) ⟨1298418, by rfl⟩ : syracuseStep 3462449 = 2596837) B2596837
theorem B2308299 : Blo 2307435 2308299 := bstep (se 1 (by rfl) ⟨1731224, by rfl⟩ : syracuseStep 2308299 = 3462449) B3462449
theorem B11092373 : Blo 2307435 11092373 := bbase (se 6 (by rfl) ⟨259977, by rfl⟩ : syracuseStep 11092373 = 519955) (by norm_num)
theorem B7394915 : Blo 2307435 7394915 := bstep (se 1 (by rfl) ⟨5546186, by rfl⟩ : syracuseStep 7394915 = 11092373) B11092373
theorem B4929943 : Blo 2307435 4929943 := bstep (se 1 (by rfl) ⟨3697457, by rfl⟩ : syracuseStep 4929943 = 7394915) B7394915
theorem B6573257 : Blo 2307435 6573257 := bstep (se 2 (by rfl) ⟨2464971, by rfl⟩ : syracuseStep 6573257 = 4929943) B4929943
theorem B4382171 : Blo 2307435 4382171 := bstep (se 1 (by rfl) ⟨3286628, by rfl⟩ : syracuseStep 4382171 = 6573257) B6573257
theorem B2921447 : Blo 2307435 2921447 := bstep (se 1 (by rfl) ⟨2191085, by rfl⟩ : syracuseStep 2921447 = 4382171) B4382171
theorem B7790525 : Blo 2307435 7790525 := bstep (se 3 (by rfl) ⟨1460723, by rfl⟩ : syracuseStep 7790525 = 2921447) B2921447
theorem B5193683 : Blo 2307435 5193683 := bstep (se 1 (by rfl) ⟨3895262, by rfl⟩ : syracuseStep 5193683 = 7790525) B7790525
theorem B3462455 : Blo 2307435 3462455 := bstep (se 1 (by rfl) ⟨2596841, by rfl⟩ : syracuseStep 3462455 = 5193683) B5193683
theorem B2308303 : Blo 2307435 2308303 := bstep (se 1 (by rfl) ⟨1731227, by rfl⟩ : syracuseStep 2308303 = 3462455) B3462455
theorem B3462461 : Blo 2307435 3462461 := bbase (se 3 (by rfl) ⟨649211, by rfl⟩ : syracuseStep 3462461 = 1298423) (by norm_num)
theorem B2308307 : Blo 2307435 2308307 := bstep (se 1 (by rfl) ⟨1731230, by rfl⟩ : syracuseStep 2308307 = 3462461) B3462461
theorem B5193701 : Blo 2307435 5193701 := bbase (se 4 (by rfl) ⟨486909, by rfl⟩ : syracuseStep 5193701 = 973819) (by norm_num)
theorem B3462467 : Blo 2307435 3462467 := bstep (se 1 (by rfl) ⟨2596850, by rfl⟩ : syracuseStep 3462467 = 5193701) B5193701
theorem B2308311 : Blo 2307435 2308311 := bstep (se 1 (by rfl) ⟨1731233, by rfl⟩ : syracuseStep 2308311 = 3462467) B3462467
theorem B5842925 : Blo 2307435 5842925 := bbase (se 3 (by rfl) ⟨1095548, by rfl⟩ : syracuseStep 5842925 = 2191097) (by norm_num)
theorem B3895283 : Blo 2307435 3895283 := bstep (se 1 (by rfl) ⟨2921462, by rfl⟩ : syracuseStep 3895283 = 5842925) B5842925
theorem B2596855 : Blo 2307435 2596855 := bstep (se 1 (by rfl) ⟨1947641, by rfl⟩ : syracuseStep 2596855 = 3895283) B3895283
theorem B3462473 : Blo 2307435 3462473 := bstep (se 2 (by rfl) ⟨1298427, by rfl⟩ : syracuseStep 3462473 = 2596855) B2596855
theorem B2308315 : Blo 2307435 2308315 := bstep (se 1 (by rfl) ⟨1731236, by rfl⟩ : syracuseStep 2308315 = 3462473) B3462473
theorem B4159669 : Blo 2307435 4159669 := bbase (se 5 (by rfl) ⟨194984, by rfl⟩ : syracuseStep 4159669 = 389969) (by norm_num)
theorem B5546225 : Blo 2307435 5546225 := bstep (se 2 (by rfl) ⟨2079834, by rfl⟩ : syracuseStep 5546225 = 4159669) B4159669
theorem B3697483 : Blo 2307435 3697483 := bstep (se 1 (by rfl) ⟨2773112, by rfl⟩ : syracuseStep 3697483 = 5546225) B5546225
theorem B4929977 : Blo 2307435 4929977 := bstep (se 2 (by rfl) ⟨1848741, by rfl⟩ : syracuseStep 4929977 = 3697483) B3697483
theorem B3286651 : Blo 2307435 3286651 := bstep (se 1 (by rfl) ⟨2464988, by rfl⟩ : syracuseStep 3286651 = 4929977) B4929977
theorem B4382201 : Blo 2307435 4382201 := bstep (se 2 (by rfl) ⟨1643325, by rfl⟩ : syracuseStep 4382201 = 3286651) B3286651
theorem B11685869 : Blo 2307435 11685869 := bstep (se 3 (by rfl) ⟨2191100, by rfl⟩ : syracuseStep 11685869 = 4382201) B4382201
theorem B7790579 : Blo 2307435 7790579 := bstep (se 1 (by rfl) ⟨5842934, by rfl⟩ : syracuseStep 7790579 = 11685869) B11685869
theorem B5193719 : Blo 2307435 5193719 := bstep (se 1 (by rfl) ⟨3895289, by rfl⟩ : syracuseStep 5193719 = 7790579) B7790579
theorem B3462479 : Blo 2307435 3462479 := bstep (se 1 (by rfl) ⟨2596859, by rfl⟩ : syracuseStep 3462479 = 5193719) B5193719
theorem B2308319 : Blo 2307435 2308319 := bstep (se 1 (by rfl) ⟨1731239, by rfl⟩ : syracuseStep 2308319 = 3462479) B3462479
theorem B3462485 : Blo 2307435 3462485 := bbase (se 15 (by rfl) ⟨158, by rfl⟩ : syracuseStep 3462485 = 317) (by norm_num)
theorem B2308323 : Blo 2307435 2308323 := bstep (se 1 (by rfl) ⟨1731242, by rfl⟩ : syracuseStep 2308323 = 3462485) B3462485
theorem B2464997 : Blo 2307435 2464997 := bbase (se 4 (by rfl) ⟨231093, by rfl⟩ : syracuseStep 2464997 = 462187) (by norm_num)
theorem B6573325 : Blo 2307435 6573325 := bstep (se 3 (by rfl) ⟨1232498, by rfl⟩ : syracuseStep 6573325 = 2464997) B2464997
theorem B8764433 : Blo 2307435 8764433 := bstep (se 2 (by rfl) ⟨3286662, by rfl⟩ : syracuseStep 8764433 = 6573325) B6573325
theorem B5842955 : Blo 2307435 5842955 := bstep (se 1 (by rfl) ⟨4382216, by rfl⟩ : syracuseStep 5842955 = 8764433) B8764433
theorem B3895303 : Blo 2307435 3895303 := bstep (se 1 (by rfl) ⟨2921477, by rfl⟩ : syracuseStep 3895303 = 5842955) B5842955
theorem B5193737 : Blo 2307435 5193737 := bstep (se 2 (by rfl) ⟨1947651, by rfl⟩ : syracuseStep 5193737 = 3895303) B3895303
theorem B3462491 : Blo 2307435 3462491 := bstep (se 1 (by rfl) ⟨2596868, by rfl⟩ : syracuseStep 3462491 = 5193737) B5193737
theorem B2308327 : Blo 2307435 2308327 := bstep (se 1 (by rfl) ⟨1731245, by rfl⟩ : syracuseStep 2308327 = 3462491) B3462491
theorem B2596873 : Blo 2307435 2596873 := bbase (se 2 (by rfl) ⟨973827, by rfl⟩ : syracuseStep 2596873 = 1947655) (by norm_num)
theorem B3462497 : Blo 2307435 3462497 := bstep (se 2 (by rfl) ⟨1298436, by rfl⟩ : syracuseStep 3462497 = 2596873) B2596873
theorem B2308331 : Blo 2307435 2308331 := bstep (se 1 (by rfl) ⟨1731248, by rfl⟩ : syracuseStep 2308331 = 3462497) B3462497
theorem B9994549 : Blo 2307435 9994549 := bbase (se 5 (by rfl) ⟨468494, by rfl⟩ : syracuseStep 9994549 = 936989) (by norm_num)
theorem B13326065 : Blo 2307435 13326065 := bstep (se 2 (by rfl) ⟨4997274, by rfl⟩ : syracuseStep 13326065 = 9994549) B9994549
theorem B8884043 : Blo 2307435 8884043 := bstep (se 1 (by rfl) ⟨6663032, by rfl⟩ : syracuseStep 8884043 = 13326065) B13326065
theorem B5922695 : Blo 2307435 5922695 := bstep (se 1 (by rfl) ⟨4442021, by rfl⟩ : syracuseStep 5922695 = 8884043) B8884043
theorem B3948463 : Blo 2307435 3948463 := bstep (se 1 (by rfl) ⟨2961347, by rfl⟩ : syracuseStep 3948463 = 5922695) B5922695
theorem B5264617 : Blo 2307435 5264617 := bstep (se 2 (by rfl) ⟨1974231, by rfl⟩ : syracuseStep 5264617 = 3948463) B3948463
theorem B7019489 : Blo 2307435 7019489 := bstep (se 2 (by rfl) ⟨2632308, by rfl⟩ : syracuseStep 7019489 = 5264617) B5264617
theorem B4679659 : Blo 2307435 4679659 := bstep (se 1 (by rfl) ⟨3509744, by rfl⟩ : syracuseStep 4679659 = 7019489) B7019489
theorem B24958181 : Blo 2307435 24958181 := bstep (se 4 (by rfl) ⟨2339829, by rfl⟩ : syracuseStep 24958181 = 4679659) B4679659
theorem B16638787 : Blo 2307435 16638787 := bstep (se 1 (by rfl) ⟨12479090, by rfl⟩ : syracuseStep 16638787 = 24958181) B24958181
theorem B22185049 : Blo 2307435 22185049 := bstep (se 2 (by rfl) ⟨8319393, by rfl⟩ : syracuseStep 22185049 = 16638787) B16638787
theorem B29580065 : Blo 2307435 29580065 := bstep (se 2 (by rfl) ⟨11092524, by rfl⟩ : syracuseStep 29580065 = 22185049) B22185049
theorem B19720043 : Blo 2307435 19720043 := bstep (se 1 (by rfl) ⟨14790032, by rfl⟩ : syracuseStep 19720043 = 29580065) B29580065
theorem B13146695 : Blo 2307435 13146695 := bstep (se 1 (by rfl) ⟨9860021, by rfl⟩ : syracuseStep 13146695 = 19720043) B19720043
theorem B8764463 : Blo 2307435 8764463 := bstep (se 1 (by rfl) ⟨6573347, by rfl⟩ : syracuseStep 8764463 = 13146695) B13146695
theorem B5842975 : Blo 2307435 5842975 := bstep (se 1 (by rfl) ⟨4382231, by rfl⟩ : syracuseStep 5842975 = 8764463) B8764463
theorem B7790633 : Blo 2307435 7790633 := bstep (se 2 (by rfl) ⟨2921487, by rfl⟩ : syracuseStep 7790633 = 5842975) B5842975
theorem B5193755 : Blo 2307435 5193755 := bstep (se 1 (by rfl) ⟨3895316, by rfl⟩ : syracuseStep 5193755 = 7790633) B7790633
theorem B3462503 : Blo 2307435 3462503 := bstep (se 1 (by rfl) ⟨2596877, by rfl⟩ : syracuseStep 3462503 = 5193755) B5193755
theorem B2308335 : Blo 2307435 2308335 := bstep (se 1 (by rfl) ⟨1731251, by rfl⟩ : syracuseStep 2308335 = 3462503) B3462503
theorem B3462509 : Blo 2307435 3462509 := bbase (se 3 (by rfl) ⟨649220, by rfl⟩ : syracuseStep 3462509 = 1298441) (by norm_num)
theorem B2308339 : Blo 2307435 2308339 := bstep (se 1 (by rfl) ⟨1731254, by rfl⟩ : syracuseStep 2308339 = 3462509) B3462509
theorem B5193773 : Blo 2307435 5193773 := bbase (se 3 (by rfl) ⟨973832, by rfl⟩ : syracuseStep 5193773 = 1947665) (by norm_num)
theorem B3462515 : Blo 2307435 3462515 := bstep (se 1 (by rfl) ⟨2596886, by rfl⟩ : syracuseStep 3462515 = 5193773) B5193773
theorem B2308343 : Blo 2307435 2308343 := bstep (se 1 (by rfl) ⟨1731257, by rfl⟩ : syracuseStep 2308343 = 3462515) B3462515
theorem B4442045 : Blo 2307435 4442045 := bbase (se 3 (by rfl) ⟨832883, by rfl⟩ : syracuseStep 4442045 = 1665767) (by norm_num)
theorem B11845453 : Blo 2307435 11845453 := bstep (se 3 (by rfl) ⟨2221022, by rfl⟩ : syracuseStep 11845453 = 4442045) B4442045
theorem B15793937 : Blo 2307435 15793937 := bstep (se 2 (by rfl) ⟨5922726, by rfl⟩ : syracuseStep 15793937 = 11845453) B11845453
theorem B10529291 : Blo 2307435 10529291 := bstep (se 1 (by rfl) ⟨7896968, by rfl⟩ : syracuseStep 10529291 = 15793937) B15793937
theorem B28078109 : Blo 2307435 28078109 := bstep (se 3 (by rfl) ⟨5264645, by rfl⟩ : syracuseStep 28078109 = 10529291) B10529291
theorem B18718739 : Blo 2307435 18718739 := bstep (se 1 (by rfl) ⟨14039054, by rfl⟩ : syracuseStep 18718739 = 28078109) B28078109
theorem B12479159 : Blo 2307435 12479159 := bstep (se 1 (by rfl) ⟨9359369, by rfl⟩ : syracuseStep 12479159 = 18718739) B18718739
theorem B8319439 : Blo 2307435 8319439 := bstep (se 1 (by rfl) ⟨6239579, by rfl⟩ : syracuseStep 8319439 = 12479159) B12479159
theorem B11092585 : Blo 2307435 11092585 := bstep (se 2 (by rfl) ⟨4159719, by rfl⟩ : syracuseStep 11092585 = 8319439) B8319439
theorem B14790113 : Blo 2307435 14790113 := bstep (se 2 (by rfl) ⟨5546292, by rfl⟩ : syracuseStep 14790113 = 11092585) B11092585
theorem B9860075 : Blo 2307435 9860075 := bstep (se 1 (by rfl) ⟨7395056, by rfl⟩ : syracuseStep 9860075 = 14790113) B14790113
theorem B6573383 : Blo 2307435 6573383 := bstep (se 1 (by rfl) ⟨4930037, by rfl⟩ : syracuseStep 6573383 = 9860075) B9860075
theorem B4382255 : Blo 2307435 4382255 := bstep (se 1 (by rfl) ⟨3286691, by rfl⟩ : syracuseStep 4382255 = 6573383) B6573383
theorem B2921503 : Blo 2307435 2921503 := bstep (se 1 (by rfl) ⟨2191127, by rfl⟩ : syracuseStep 2921503 = 4382255) B4382255
theorem B3895337 : Blo 2307435 3895337 := bstep (se 2 (by rfl) ⟨1460751, by rfl⟩ : syracuseStep 3895337 = 2921503) B2921503
theorem B2596891 : Blo 2307435 2596891 := bstep (se 1 (by rfl) ⟨1947668, by rfl⟩ : syracuseStep 2596891 = 3895337) B3895337
theorem B3462521 : Blo 2307435 3462521 := bstep (se 2 (by rfl) ⟨1298445, by rfl⟩ : syracuseStep 3462521 = 2596891) B2596891
theorem B2308347 : Blo 2307435 2308347 := bstep (se 1 (by rfl) ⟨1731260, by rfl⟩ : syracuseStep 2308347 = 3462521) B3462521
theorem B21058613 : Blo 2307435 21058613 := bbase (se 5 (by rfl) ⟨987122, by rfl⟩ : syracuseStep 21058613 = 1974245) (by norm_num)
theorem B14039075 : Blo 2307435 14039075 := bstep (se 1 (by rfl) ⟨10529306, by rfl⟩ : syracuseStep 14039075 = 21058613) B21058613
theorem B9359383 : Blo 2307435 9359383 := bstep (se 1 (by rfl) ⟨7019537, by rfl⟩ : syracuseStep 9359383 = 14039075) B14039075
theorem B12479177 : Blo 2307435 12479177 := bstep (se 2 (by rfl) ⟨4679691, by rfl⟩ : syracuseStep 12479177 = 9359383) B9359383
theorem B8319451 : Blo 2307435 8319451 := bstep (se 1 (by rfl) ⟨6239588, by rfl⟩ : syracuseStep 8319451 = 12479177) B12479177
theorem B11092601 : Blo 2307435 11092601 := bstep (se 2 (by rfl) ⟨4159725, by rfl⟩ : syracuseStep 11092601 = 8319451) B8319451
theorem B7395067 : Blo 2307435 7395067 := bstep (se 1 (by rfl) ⟨5546300, by rfl⟩ : syracuseStep 7395067 = 11092601) B11092601
theorem B39440357 : Blo 2307435 39440357 := bstep (se 4 (by rfl) ⟨3697533, by rfl⟩ : syracuseStep 39440357 = 7395067) B7395067
theorem B26293571 : Blo 2307435 26293571 := bstep (se 1 (by rfl) ⟨19720178, by rfl⟩ : syracuseStep 26293571 = 39440357) B39440357
theorem B17529047 : Blo 2307435 17529047 := bstep (se 1 (by rfl) ⟨13146785, by rfl⟩ : syracuseStep 17529047 = 26293571) B26293571
theorem B11686031 : Blo 2307435 11686031 := bstep (se 1 (by rfl) ⟨8764523, by rfl⟩ : syracuseStep 11686031 = 17529047) B17529047
theorem B7790687 : Blo 2307435 7790687 := bstep (se 1 (by rfl) ⟨5843015, by rfl⟩ : syracuseStep 7790687 = 11686031) B11686031
theorem B5193791 : Blo 2307435 5193791 := bstep (se 1 (by rfl) ⟨3895343, by rfl⟩ : syracuseStep 5193791 = 7790687) B7790687
theorem B3462527 : Blo 2307435 3462527 := bstep (se 1 (by rfl) ⟨2596895, by rfl⟩ : syracuseStep 3462527 = 5193791) B5193791
theorem B2308351 : Blo 2307435 2308351 := bstep (se 1 (by rfl) ⟨1731263, by rfl⟩ : syracuseStep 2308351 = 3462527) B3462527
theorem B3462533 : Blo 2307435 3462533 := bbase (se 4 (by rfl) ⟨324612, by rfl⟩ : syracuseStep 3462533 = 649225) (by norm_num)
theorem B2308355 : Blo 2307435 2308355 := bstep (se 1 (by rfl) ⟨1731266, by rfl⟩ : syracuseStep 2308355 = 3462533) B3462533
theorem B3895357 : Blo 2307435 3895357 := bbase (se 3 (by rfl) ⟨730379, by rfl⟩ : syracuseStep 3895357 = 1460759) (by norm_num)
theorem B5193809 : Blo 2307435 5193809 := bstep (se 2 (by rfl) ⟨1947678, by rfl⟩ : syracuseStep 5193809 = 3895357) B3895357
theorem B3462539 : Blo 2307435 3462539 := bstep (se 1 (by rfl) ⟨2596904, by rfl⟩ : syracuseStep 3462539 = 5193809) B5193809
theorem B2308359 : Blo 2307435 2308359 := bstep (se 1 (by rfl) ⟨1731269, by rfl⟩ : syracuseStep 2308359 = 3462539) B3462539
theorem B2596909 : Blo 2307435 2596909 := bbase (se 3 (by rfl) ⟨486920, by rfl⟩ : syracuseStep 2596909 = 973841) (by norm_num)
theorem B3462545 : Blo 2307435 3462545 := bstep (se 2 (by rfl) ⟨1298454, by rfl⟩ : syracuseStep 3462545 = 2596909) B2596909
theorem B2308363 : Blo 2307435 2308363 := bstep (se 1 (by rfl) ⟨1731272, by rfl⟩ : syracuseStep 2308363 = 3462545) B3462545
theorem B7790741 : Blo 2307435 7790741 := bbase (se 6 (by rfl) ⟨182595, by rfl⟩ : syracuseStep 7790741 = 365191) (by norm_num)
theorem B5193827 : Blo 2307435 5193827 := bstep (se 1 (by rfl) ⟨3895370, by rfl⟩ : syracuseStep 5193827 = 7790741) B7790741
theorem B3462551 : Blo 2307435 3462551 := bstep (se 1 (by rfl) ⟨2596913, by rfl⟩ : syracuseStep 3462551 = 5193827) B5193827
theorem B2308367 : Blo 2307435 2308367 := bstep (se 1 (by rfl) ⟨1731275, by rfl⟩ : syracuseStep 2308367 = 3462551) B3462551
theorem B3462557 : Blo 2307435 3462557 := bbase (se 3 (by rfl) ⟨649229, by rfl⟩ : syracuseStep 3462557 = 1298459) (by norm_num)
theorem B2308371 : Blo 2307435 2308371 := bstep (se 1 (by rfl) ⟨1731278, by rfl⟩ : syracuseStep 2308371 = 3462557) B3462557
theorem B5193845 : Blo 2307435 5193845 := bbase (se 5 (by rfl) ⟨243461, by rfl⟩ : syracuseStep 5193845 = 486923) (by norm_num)
theorem B3462563 : Blo 2307435 3462563 := bstep (se 1 (by rfl) ⟨2596922, by rfl⟩ : syracuseStep 3462563 = 5193845) B5193845
theorem B2308375 : Blo 2307435 2308375 := bstep (se 1 (by rfl) ⟨1731281, by rfl⟩ : syracuseStep 2308375 = 3462563) B3462563
theorem B3509813 : Blo 2307435 3509813 := bbase (se 5 (by rfl) ⟨164522, by rfl⟩ : syracuseStep 3509813 = 329045) (by norm_num)
theorem B2339875 : Blo 2307435 2339875 := bstep (se 1 (by rfl) ⟨1754906, by rfl⟩ : syracuseStep 2339875 = 3509813) B3509813
theorem B3119833 : Blo 2307435 3119833 := bstep (se 2 (by rfl) ⟨1169937, by rfl⟩ : syracuseStep 3119833 = 2339875) B2339875
theorem B4159777 : Blo 2307435 4159777 := bstep (se 2 (by rfl) ⟨1559916, by rfl⟩ : syracuseStep 4159777 = 3119833) B3119833
theorem B5546369 : Blo 2307435 5546369 := bstep (se 2 (by rfl) ⟨2079888, by rfl⟩ : syracuseStep 5546369 = 4159777) B4159777
theorem B3697579 : Blo 2307435 3697579 := bstep (se 1 (by rfl) ⟨2773184, by rfl⟩ : syracuseStep 3697579 = 5546369) B5546369
theorem B19720421 : Blo 2307435 19720421 := bstep (se 4 (by rfl) ⟨1848789, by rfl⟩ : syracuseStep 19720421 = 3697579) B3697579
theorem B13146947 : Blo 2307435 13146947 := bstep (se 1 (by rfl) ⟨9860210, by rfl⟩ : syracuseStep 13146947 = 19720421) B19720421
theorem B8764631 : Blo 2307435 8764631 := bstep (se 1 (by rfl) ⟨6573473, by rfl⟩ : syracuseStep 8764631 = 13146947) B13146947
theorem B5843087 : Blo 2307435 5843087 := bstep (se 1 (by rfl) ⟨4382315, by rfl⟩ : syracuseStep 5843087 = 8764631) B8764631
theorem B3895391 : Blo 2307435 3895391 := bstep (se 1 (by rfl) ⟨2921543, by rfl⟩ : syracuseStep 3895391 = 5843087) B5843087
theorem B2596927 : Blo 2307435 2596927 := bstep (se 1 (by rfl) ⟨1947695, by rfl⟩ : syracuseStep 2596927 = 3895391) B3895391
theorem B3462569 : Blo 2307435 3462569 := bstep (se 2 (by rfl) ⟨1298463, by rfl⟩ : syracuseStep 3462569 = 2596927) B2596927
theorem B2308379 : Blo 2307435 2308379 := bstep (se 1 (by rfl) ⟨1731284, by rfl⟩ : syracuseStep 2308379 = 3462569) B3462569
theorem B8764645 : Blo 2307435 8764645 := bbase (se 4 (by rfl) ⟨821685, by rfl⟩ : syracuseStep 8764645 = 1643371) (by norm_num)
theorem B11686193 : Blo 2307435 11686193 := bstep (se 2 (by rfl) ⟨4382322, by rfl⟩ : syracuseStep 11686193 = 8764645) B8764645
theorem B7790795 : Blo 2307435 7790795 := bstep (se 1 (by rfl) ⟨5843096, by rfl⟩ : syracuseStep 7790795 = 11686193) B11686193
theorem B5193863 : Blo 2307435 5193863 := bstep (se 1 (by rfl) ⟨3895397, by rfl⟩ : syracuseStep 5193863 = 7790795) B7790795
theorem B3462575 : Blo 2307435 3462575 := bstep (se 1 (by rfl) ⟨2596931, by rfl⟩ : syracuseStep 3462575 = 5193863) B5193863
theorem B2308383 : Blo 2307435 2308383 := bstep (se 1 (by rfl) ⟨1731287, by rfl⟩ : syracuseStep 2308383 = 3462575) B3462575
theorem B3462581 : Blo 2307435 3462581 := bbase (se 5 (by rfl) ⟨162308, by rfl⟩ : syracuseStep 3462581 = 324617) (by norm_num)
theorem B2308387 : Blo 2307435 2308387 := bstep (se 1 (by rfl) ⟨1731290, by rfl⟩ : syracuseStep 2308387 = 3462581) B3462581
theorem B5843117 : Blo 2307435 5843117 := bbase (se 3 (by rfl) ⟨1095584, by rfl⟩ : syracuseStep 5843117 = 2191169) (by norm_num)
theorem B3895411 : Blo 2307435 3895411 := bstep (se 1 (by rfl) ⟨2921558, by rfl⟩ : syracuseStep 3895411 = 5843117) B5843117
theorem B5193881 : Blo 2307435 5193881 := bstep (se 2 (by rfl) ⟨1947705, by rfl⟩ : syracuseStep 5193881 = 3895411) B3895411
theorem B3462587 : Blo 2307435 3462587 := bstep (se 1 (by rfl) ⟨2596940, by rfl⟩ : syracuseStep 3462587 = 5193881) B5193881
theorem B2308391 : Blo 2307435 2308391 := bstep (se 1 (by rfl) ⟨1731293, by rfl⟩ : syracuseStep 2308391 = 3462587) B3462587
theorem B2596945 : Blo 2307435 2596945 := bbase (se 2 (by rfl) ⟨973854, by rfl⟩ : syracuseStep 2596945 = 1947709) (by norm_num)
theorem B3462593 : Blo 2307435 3462593 := bstep (se 2 (by rfl) ⟨1298472, by rfl⟩ : syracuseStep 3462593 = 2596945) B2596945
theorem B2308395 : Blo 2307435 2308395 := bstep (se 1 (by rfl) ⟨1731296, by rfl⟩ : syracuseStep 2308395 = 3462593) B3462593
theorem B3286765 : Blo 2307435 3286765 := bbase (se 3 (by rfl) ⟨616268, by rfl⟩ : syracuseStep 3286765 = 1232537) (by norm_num)
theorem B4382353 : Blo 2307435 4382353 := bstep (se 2 (by rfl) ⟨1643382, by rfl⟩ : syracuseStep 4382353 = 3286765) B3286765
theorem B5843137 : Blo 2307435 5843137 := bstep (se 2 (by rfl) ⟨2191176, by rfl⟩ : syracuseStep 5843137 = 4382353) B4382353
theorem B7790849 : Blo 2307435 7790849 := bstep (se 2 (by rfl) ⟨2921568, by rfl⟩ : syracuseStep 7790849 = 5843137) B5843137
theorem B5193899 : Blo 2307435 5193899 := bstep (se 1 (by rfl) ⟨3895424, by rfl⟩ : syracuseStep 5193899 = 7790849) B7790849
theorem B3462599 : Blo 2307435 3462599 := bstep (se 1 (by rfl) ⟨2596949, by rfl⟩ : syracuseStep 3462599 = 5193899) B5193899
theorem B2308399 : Blo 2307435 2308399 := bstep (se 1 (by rfl) ⟨1731299, by rfl⟩ : syracuseStep 2308399 = 3462599) B3462599
theorem B3462605 : Blo 2307435 3462605 := bbase (se 3 (by rfl) ⟨649238, by rfl⟩ : syracuseStep 3462605 = 1298477) (by norm_num)
theorem B2308403 : Blo 2307435 2308403 := bstep (se 1 (by rfl) ⟨1731302, by rfl⟩ : syracuseStep 2308403 = 3462605) B3462605
theorem B5193917 : Blo 2307435 5193917 := bbase (se 3 (by rfl) ⟨973859, by rfl⟩ : syracuseStep 5193917 = 1947719) (by norm_num)
theorem B3462611 : Blo 2307435 3462611 := bstep (se 1 (by rfl) ⟨2596958, by rfl⟩ : syracuseStep 3462611 = 5193917) B5193917
theorem B2308407 : Blo 2307435 2308407 := bstep (se 1 (by rfl) ⟨1731305, by rfl⟩ : syracuseStep 2308407 = 3462611) B3462611
theorem B3895445 : Blo 2307435 3895445 := bbase (se 6 (by rfl) ⟨91299, by rfl⟩ : syracuseStep 3895445 = 182599) (by norm_num)
theorem B2596963 : Blo 2307435 2596963 := bstep (se 1 (by rfl) ⟨1947722, by rfl⟩ : syracuseStep 2596963 = 3895445) B3895445
theorem B3462617 : Blo 2307435 3462617 := bstep (se 2 (by rfl) ⟨1298481, by rfl⟩ : syracuseStep 3462617 = 2596963) B2596963
theorem B2308411 : Blo 2307435 2308411 := bstep (se 1 (by rfl) ⟨1731308, by rfl⟩ : syracuseStep 2308411 = 3462617) B3462617
theorem B2498725 : Blo 2307435 2498725 := bbase (se 4 (by rfl) ⟨234255, by rfl⟩ : syracuseStep 2498725 = 468511) (by norm_num)
theorem B3331633 : Blo 2307435 3331633 := bstep (se 2 (by rfl) ⟨1249362, by rfl⟩ : syracuseStep 3331633 = 2498725) B2498725
theorem B4442177 : Blo 2307435 4442177 := bstep (se 2 (by rfl) ⟨1665816, by rfl⟩ : syracuseStep 4442177 = 3331633) B3331633
theorem B2961451 : Blo 2307435 2961451 := bstep (se 1 (by rfl) ⟨2221088, by rfl⟩ : syracuseStep 2961451 = 4442177) B4442177
theorem B3948601 : Blo 2307435 3948601 := bstep (se 2 (by rfl) ⟨1480725, by rfl⟩ : syracuseStep 3948601 = 2961451) B2961451
theorem B5264801 : Blo 2307435 5264801 := bstep (se 2 (by rfl) ⟨1974300, by rfl⟩ : syracuseStep 5264801 = 3948601) B3948601
theorem B3509867 : Blo 2307435 3509867 := bstep (se 1 (by rfl) ⟨2632400, by rfl⟩ : syracuseStep 3509867 = 5264801) B5264801
theorem B2339911 : Blo 2307435 2339911 := bstep (se 1 (by rfl) ⟨1754933, by rfl⟩ : syracuseStep 2339911 = 3509867) B3509867
theorem B3119881 : Blo 2307435 3119881 := bstep (se 2 (by rfl) ⟨1169955, by rfl⟩ : syracuseStep 3119881 = 2339911) B2339911
theorem B4159841 : Blo 2307435 4159841 := bstep (se 2 (by rfl) ⟨1559940, by rfl⟩ : syracuseStep 4159841 = 3119881) B3119881
theorem B11092909 : Blo 2307435 11092909 := bstep (se 3 (by rfl) ⟨2079920, by rfl⟩ : syracuseStep 11092909 = 4159841) B4159841
theorem B14790545 : Blo 2307435 14790545 := bstep (se 2 (by rfl) ⟨5546454, by rfl⟩ : syracuseStep 14790545 = 11092909) B11092909
theorem B9860363 : Blo 2307435 9860363 := bstep (se 1 (by rfl) ⟨7395272, by rfl⟩ : syracuseStep 9860363 = 14790545) B14790545
theorem B6573575 : Blo 2307435 6573575 := bstep (se 1 (by rfl) ⟨4930181, by rfl⟩ : syracuseStep 6573575 = 9860363) B9860363
theorem B17529533 : Blo 2307435 17529533 := bstep (se 3 (by rfl) ⟨3286787, by rfl⟩ : syracuseStep 17529533 = 6573575) B6573575
theorem B11686355 : Blo 2307435 11686355 := bstep (se 1 (by rfl) ⟨8764766, by rfl⟩ : syracuseStep 11686355 = 17529533) B17529533
theorem B7790903 : Blo 2307435 7790903 := bstep (se 1 (by rfl) ⟨5843177, by rfl⟩ : syracuseStep 7790903 = 11686355) B11686355
theorem B5193935 : Blo 2307435 5193935 := bstep (se 1 (by rfl) ⟨3895451, by rfl⟩ : syracuseStep 5193935 = 7790903) B7790903
theorem B3462623 : Blo 2307435 3462623 := bstep (se 1 (by rfl) ⟨2596967, by rfl⟩ : syracuseStep 3462623 = 5193935) B5193935
theorem B2308415 : Blo 2307435 2308415 := bstep (se 1 (by rfl) ⟨1731311, by rfl⟩ : syracuseStep 2308415 = 3462623) B3462623
theorem B3462629 : Blo 2307435 3462629 := bbase (se 4 (by rfl) ⟨324621, by rfl⟩ : syracuseStep 3462629 = 649243) (by norm_num)
theorem B2308419 : Blo 2307435 2308419 := bstep (se 1 (by rfl) ⟨1731314, by rfl⟩ : syracuseStep 2308419 = 3462629) B3462629
theorem B5622149 : Blo 2307435 5622149 := bbase (se 4 (by rfl) ⟨527076, by rfl⟩ : syracuseStep 5622149 = 1054153) (by norm_num)
theorem B3748099 : Blo 2307435 3748099 := bstep (se 1 (by rfl) ⟨2811074, by rfl⟩ : syracuseStep 3748099 = 5622149) B5622149
theorem B4997465 : Blo 2307435 4997465 := bstep (se 2 (by rfl) ⟨1874049, by rfl⟩ : syracuseStep 4997465 = 3748099) B3748099
theorem B3331643 : Blo 2307435 3331643 := bstep (se 1 (by rfl) ⟨2498732, by rfl⟩ : syracuseStep 3331643 = 4997465) B4997465
theorem B35537525 : Blo 2307435 35537525 := bstep (se 5 (by rfl) ⟨1665821, by rfl⟩ : syracuseStep 35537525 = 3331643) B3331643
theorem B23691683 : Blo 2307435 23691683 := bstep (se 1 (by rfl) ⟨17768762, by rfl⟩ : syracuseStep 23691683 = 35537525) B35537525
theorem B15794455 : Blo 2307435 15794455 := bstep (se 1 (by rfl) ⟨11845841, by rfl⟩ : syracuseStep 15794455 = 23691683) B23691683
theorem B21059273 : Blo 2307435 21059273 := bstep (se 2 (by rfl) ⟨7897227, by rfl⟩ : syracuseStep 21059273 = 15794455) B15794455
theorem B14039515 : Blo 2307435 14039515 := bstep (se 1 (by rfl) ⟨10529636, by rfl⟩ : syracuseStep 14039515 = 21059273) B21059273
theorem B18719353 : Blo 2307435 18719353 := bstep (se 2 (by rfl) ⟨7019757, by rfl⟩ : syracuseStep 18719353 = 14039515) B14039515
theorem B24959137 : Blo 2307435 24959137 := bstep (se 2 (by rfl) ⟨9359676, by rfl⟩ : syracuseStep 24959137 = 18719353) B18719353
theorem B33278849 : Blo 2307435 33278849 := bstep (se 2 (by rfl) ⟨12479568, by rfl⟩ : syracuseStep 33278849 = 24959137) B24959137
theorem B22185899 : Blo 2307435 22185899 := bstep (se 1 (by rfl) ⟨16639424, by rfl⟩ : syracuseStep 22185899 = 33278849) B33278849
theorem B14790599 : Blo 2307435 14790599 := bstep (se 1 (by rfl) ⟨11092949, by rfl⟩ : syracuseStep 14790599 = 22185899) B22185899
theorem B9860399 : Blo 2307435 9860399 := bstep (se 1 (by rfl) ⟨7395299, by rfl⟩ : syracuseStep 9860399 = 14790599) B14790599
theorem B6573599 : Blo 2307435 6573599 := bstep (se 1 (by rfl) ⟨4930199, by rfl⟩ : syracuseStep 6573599 = 9860399) B9860399
theorem B4382399 : Blo 2307435 4382399 := bstep (se 1 (by rfl) ⟨3286799, by rfl⟩ : syracuseStep 4382399 = 6573599) B6573599
theorem B2921599 : Blo 2307435 2921599 := bstep (se 1 (by rfl) ⟨2191199, by rfl⟩ : syracuseStep 2921599 = 4382399) B4382399
theorem B3895465 : Blo 2307435 3895465 := bstep (se 2 (by rfl) ⟨1460799, by rfl⟩ : syracuseStep 3895465 = 2921599) B2921599
theorem B5193953 : Blo 2307435 5193953 := bstep (se 2 (by rfl) ⟨1947732, by rfl⟩ : syracuseStep 5193953 = 3895465) B3895465
theorem B3462635 : Blo 2307435 3462635 := bstep (se 1 (by rfl) ⟨2596976, by rfl⟩ : syracuseStep 3462635 = 5193953) B5193953
theorem B2308423 : Blo 2307435 2308423 := bstep (se 1 (by rfl) ⟨1731317, by rfl⟩ : syracuseStep 2308423 = 3462635) B3462635
theorem B2596981 : Blo 2307435 2596981 := bbase (se 5 (by rfl) ⟨121733, by rfl⟩ : syracuseStep 2596981 = 243467) (by norm_num)
theorem B3462641 : Blo 2307435 3462641 := bstep (se 2 (by rfl) ⟨1298490, by rfl⟩ : syracuseStep 3462641 = 2596981) B2596981
theorem B2308427 : Blo 2307435 2308427 := bstep (se 1 (by rfl) ⟨1731320, by rfl⟩ : syracuseStep 2308427 = 3462641) B3462641
theorem B2921609 : Blo 2307435 2921609 := bbase (se 2 (by rfl) ⟨1095603, by rfl⟩ : syracuseStep 2921609 = 2191207) (by norm_num)
theorem B7790957 : Blo 2307435 7790957 := bstep (se 3 (by rfl) ⟨1460804, by rfl⟩ : syracuseStep 7790957 = 2921609) B2921609
theorem B5193971 : Blo 2307435 5193971 := bstep (se 1 (by rfl) ⟨3895478, by rfl⟩ : syracuseStep 5193971 = 7790957) B7790957
theorem B3462647 : Blo 2307435 3462647 := bstep (se 1 (by rfl) ⟨2596985, by rfl⟩ : syracuseStep 3462647 = 5193971) B5193971
theorem B2308431 : Blo 2307435 2308431 := bstep (se 1 (by rfl) ⟨1731323, by rfl⟩ : syracuseStep 2308431 = 3462647) B3462647
theorem B3462653 : Blo 2307435 3462653 := bbase (se 3 (by rfl) ⟨649247, by rfl⟩ : syracuseStep 3462653 = 1298495) (by norm_num)
theorem B2308435 : Blo 2307435 2308435 := bstep (se 1 (by rfl) ⟨1731326, by rfl⟩ : syracuseStep 2308435 = 3462653) B3462653
theorem B5193989 : Blo 2307435 5193989 := bbase (se 4 (by rfl) ⟨486936, by rfl⟩ : syracuseStep 5193989 = 973873) (by norm_num)
theorem B3462659 : Blo 2307435 3462659 := bstep (se 1 (by rfl) ⟨2596994, by rfl⟩ : syracuseStep 3462659 = 5193989) B5193989
theorem B2308439 : Blo 2307435 2308439 := bstep (se 1 (by rfl) ⟨1731329, by rfl⟩ : syracuseStep 2308439 = 3462659) B3462659
theorem B4382437 : Blo 2307435 4382437 := bbase (se 4 (by rfl) ⟨410853, by rfl⟩ : syracuseStep 4382437 = 821707) (by norm_num)
theorem B5843249 : Blo 2307435 5843249 := bstep (se 2 (by rfl) ⟨2191218, by rfl⟩ : syracuseStep 5843249 = 4382437) B4382437
theorem B3895499 : Blo 2307435 3895499 := bstep (se 1 (by rfl) ⟨2921624, by rfl⟩ : syracuseStep 3895499 = 5843249) B5843249
theorem B2596999 : Blo 2307435 2596999 := bstep (se 1 (by rfl) ⟨1947749, by rfl⟩ : syracuseStep 2596999 = 3895499) B3895499
theorem B3462665 : Blo 2307435 3462665 := bstep (se 2 (by rfl) ⟨1298499, by rfl⟩ : syracuseStep 3462665 = 2596999) B2596999
theorem B2308443 : Blo 2307435 2308443 := bstep (se 1 (by rfl) ⟨1731332, by rfl⟩ : syracuseStep 2308443 = 3462665) B3462665
theorem B11686517 : Blo 2307435 11686517 := bbase (se 5 (by rfl) ⟨547805, by rfl⟩ : syracuseStep 11686517 = 1095611) (by norm_num)
theorem B7791011 : Blo 2307435 7791011 := bstep (se 1 (by rfl) ⟨5843258, by rfl⟩ : syracuseStep 7791011 = 11686517) B11686517
theorem B5194007 : Blo 2307435 5194007 := bstep (se 1 (by rfl) ⟨3895505, by rfl⟩ : syracuseStep 5194007 = 7791011) B7791011
theorem B3462671 : Blo 2307435 3462671 := bstep (se 1 (by rfl) ⟨2597003, by rfl⟩ : syracuseStep 3462671 = 5194007) B5194007
theorem B2308447 : Blo 2307435 2308447 := bstep (se 1 (by rfl) ⟨1731335, by rfl⟩ : syracuseStep 2308447 = 3462671) B3462671
theorem B3462677 : Blo 2307435 3462677 := bbase (se 6 (by rfl) ⟨81156, by rfl⟩ : syracuseStep 3462677 = 162313) (by norm_num)
theorem B2308451 : Blo 2307435 2308451 := bstep (se 1 (by rfl) ⟨1731338, by rfl⟩ : syracuseStep 2308451 = 3462677) B3462677
theorem B5336725 : Blo 2307435 5336725 := bbase (se 6 (by rfl) ⟨125079, by rfl⟩ : syracuseStep 5336725 = 250159) (by norm_num)
theorem B7115633 : Blo 2307435 7115633 := bstep (se 2 (by rfl) ⟨2668362, by rfl⟩ : syracuseStep 7115633 = 5336725) B5336725
theorem B4743755 : Blo 2307435 4743755 := bstep (se 1 (by rfl) ⟨3557816, by rfl⟩ : syracuseStep 4743755 = 7115633) B7115633
theorem B3162503 : Blo 2307435 3162503 := bstep (se 1 (by rfl) ⟨2371877, by rfl⟩ : syracuseStep 3162503 = 4743755) B4743755
theorem B8433341 : Blo 2307435 8433341 := bstep (se 3 (by rfl) ⟨1581251, by rfl⟩ : syracuseStep 8433341 = 3162503) B3162503
theorem B5622227 : Blo 2307435 5622227 := bstep (se 1 (by rfl) ⟨4216670, by rfl⟩ : syracuseStep 5622227 = 8433341) B8433341
theorem B3748151 : Blo 2307435 3748151 := bstep (se 1 (by rfl) ⟨2811113, by rfl⟩ : syracuseStep 3748151 = 5622227) B5622227
theorem B9995069 : Blo 2307435 9995069 := bstep (se 3 (by rfl) ⟨1874075, by rfl⟩ : syracuseStep 9995069 = 3748151) B3748151
theorem B6663379 : Blo 2307435 6663379 := bstep (se 1 (by rfl) ⟨4997534, by rfl⟩ : syracuseStep 6663379 = 9995069) B9995069
theorem B8884505 : Blo 2307435 8884505 := bstep (se 2 (by rfl) ⟨3331689, by rfl⟩ : syracuseStep 8884505 = 6663379) B6663379
theorem B23692013 : Blo 2307435 23692013 := bstep (se 3 (by rfl) ⟨4442252, by rfl⟩ : syracuseStep 23692013 = 8884505) B8884505
theorem B15794675 : Blo 2307435 15794675 := bstep (se 1 (by rfl) ⟨11846006, by rfl⟩ : syracuseStep 15794675 = 23692013) B23692013
theorem B10529783 : Blo 2307435 10529783 := bstep (se 1 (by rfl) ⟨7897337, by rfl⟩ : syracuseStep 10529783 = 15794675) B15794675
theorem B7019855 : Blo 2307435 7019855 := bstep (se 1 (by rfl) ⟨5264891, by rfl⟩ : syracuseStep 7019855 = 10529783) B10529783
theorem B4679903 : Blo 2307435 4679903 := bstep (se 1 (by rfl) ⟨3509927, by rfl⟩ : syracuseStep 4679903 = 7019855) B7019855
theorem B12479741 : Blo 2307435 12479741 := bstep (se 3 (by rfl) ⟨2339951, by rfl⟩ : syracuseStep 12479741 = 4679903) B4679903
theorem B8319827 : Blo 2307435 8319827 := bstep (se 1 (by rfl) ⟨6239870, by rfl⟩ : syracuseStep 8319827 = 12479741) B12479741
theorem B5546551 : Blo 2307435 5546551 := bstep (se 1 (by rfl) ⟨4159913, by rfl⟩ : syracuseStep 5546551 = 8319827) B8319827
theorem B7395401 : Blo 2307435 7395401 := bstep (se 2 (by rfl) ⟨2773275, by rfl⟩ : syracuseStep 7395401 = 5546551) B5546551
theorem B19721069 : Blo 2307435 19721069 := bstep (se 3 (by rfl) ⟨3697700, by rfl⟩ : syracuseStep 19721069 = 7395401) B7395401
theorem B13147379 : Blo 2307435 13147379 := bstep (se 1 (by rfl) ⟨9860534, by rfl⟩ : syracuseStep 13147379 = 19721069) B19721069
theorem B8764919 : Blo 2307435 8764919 := bstep (se 1 (by rfl) ⟨6573689, by rfl⟩ : syracuseStep 8764919 = 13147379) B13147379
theorem B5843279 : Blo 2307435 5843279 := bstep (se 1 (by rfl) ⟨4382459, by rfl⟩ : syracuseStep 5843279 = 8764919) B8764919
theorem B3895519 : Blo 2307435 3895519 := bstep (se 1 (by rfl) ⟨2921639, by rfl⟩ : syracuseStep 3895519 = 5843279) B5843279
theorem B5194025 : Blo 2307435 5194025 := bstep (se 2 (by rfl) ⟨1947759, by rfl⟩ : syracuseStep 5194025 = 3895519) B3895519
theorem B3462683 : Blo 2307435 3462683 := bstep (se 1 (by rfl) ⟨2597012, by rfl⟩ : syracuseStep 3462683 = 5194025) B5194025
theorem B2308455 : Blo 2307435 2308455 := bstep (se 1 (by rfl) ⟨1731341, by rfl⟩ : syracuseStep 2308455 = 3462683) B3462683
theorem B2597017 : Blo 2307435 2597017 := bbase (se 2 (by rfl) ⟨973881, by rfl⟩ : syracuseStep 2597017 = 1947763) (by norm_num)
theorem B3462689 : Blo 2307435 3462689 := bstep (se 2 (by rfl) ⟨1298508, by rfl⟩ : syracuseStep 3462689 = 2597017) B2597017
theorem B2308459 : Blo 2307435 2308459 := bstep (se 1 (by rfl) ⟨1731344, by rfl⟩ : syracuseStep 2308459 = 3462689) B3462689
theorem B8764949 : Blo 2307435 8764949 := bbase (se 6 (by rfl) ⟨205428, by rfl⟩ : syracuseStep 8764949 = 410857) (by norm_num)
theorem B5843299 : Blo 2307435 5843299 := bstep (se 1 (by rfl) ⟨4382474, by rfl⟩ : syracuseStep 5843299 = 8764949) B8764949
theorem B7791065 : Blo 2307435 7791065 := bstep (se 2 (by rfl) ⟨2921649, by rfl⟩ : syracuseStep 7791065 = 5843299) B5843299
theorem B5194043 : Blo 2307435 5194043 := bstep (se 1 (by rfl) ⟨3895532, by rfl⟩ : syracuseStep 5194043 = 7791065) B7791065
theorem B3462695 : Blo 2307435 3462695 := bstep (se 1 (by rfl) ⟨2597021, by rfl⟩ : syracuseStep 3462695 = 5194043) B5194043
theorem B2308463 : Blo 2307435 2308463 := bstep (se 1 (by rfl) ⟨1731347, by rfl⟩ : syracuseStep 2308463 = 3462695) B3462695
theorem B3462701 : Blo 2307435 3462701 := bbase (se 3 (by rfl) ⟨649256, by rfl⟩ : syracuseStep 3462701 = 1298513) (by norm_num)
theorem B2308467 : Blo 2307435 2308467 := bstep (se 1 (by rfl) ⟨1731350, by rfl⟩ : syracuseStep 2308467 = 3462701) B3462701
theorem B5194061 : Blo 2307435 5194061 := bbase (se 3 (by rfl) ⟨973886, by rfl⟩ : syracuseStep 5194061 = 1947773) (by norm_num)
theorem B3462707 : Blo 2307435 3462707 := bstep (se 1 (by rfl) ⟨2597030, by rfl⟩ : syracuseStep 3462707 = 5194061) B5194061
theorem B2308471 : Blo 2307435 2308471 := bstep (se 1 (by rfl) ⟨1731353, by rfl⟩ : syracuseStep 2308471 = 3462707) B3462707
theorem B2921665 : Blo 2307435 2921665 := bbase (se 2 (by rfl) ⟨1095624, by rfl⟩ : syracuseStep 2921665 = 2191249) (by norm_num)
theorem B3895553 : Blo 2307435 3895553 := bstep (se 2 (by rfl) ⟨1460832, by rfl⟩ : syracuseStep 3895553 = 2921665) B2921665
theorem B2597035 : Blo 2307435 2597035 := bstep (se 1 (by rfl) ⟨1947776, by rfl⟩ : syracuseStep 2597035 = 3895553) B3895553
theorem B3462713 : Blo 2307435 3462713 := bstep (se 2 (by rfl) ⟨1298517, by rfl⟩ : syracuseStep 3462713 = 2597035) B2597035
theorem B2308475 : Blo 2307435 2308475 := bstep (se 1 (by rfl) ⟨1731356, by rfl⟩ : syracuseStep 2308475 = 3462713) B3462713
theorem B4159957 : Blo 2307435 4159957 := bbase (se 7 (by rfl) ⟨48749, by rfl⟩ : syracuseStep 4159957 = 97499) (by norm_num)
theorem B5546609 : Blo 2307435 5546609 := bstep (se 2 (by rfl) ⟨2079978, by rfl⟩ : syracuseStep 5546609 = 4159957) B4159957
theorem B3697739 : Blo 2307435 3697739 := bstep (se 1 (by rfl) ⟨2773304, by rfl⟩ : syracuseStep 3697739 = 5546609) B5546609
theorem B2465159 : Blo 2307435 2465159 := bstep (se 1 (by rfl) ⟨1848869, by rfl⟩ : syracuseStep 2465159 = 3697739) B3697739
theorem B26295029 : Blo 2307435 26295029 := bstep (se 5 (by rfl) ⟨1232579, by rfl⟩ : syracuseStep 26295029 = 2465159) B2465159
theorem B17530019 : Blo 2307435 17530019 := bstep (se 1 (by rfl) ⟨13147514, by rfl⟩ : syracuseStep 17530019 = 26295029) B26295029
theorem B11686679 : Blo 2307435 11686679 := bstep (se 1 (by rfl) ⟨8765009, by rfl⟩ : syracuseStep 11686679 = 17530019) B17530019
theorem B7791119 : Blo 2307435 7791119 := bstep (se 1 (by rfl) ⟨5843339, by rfl⟩ : syracuseStep 7791119 = 11686679) B11686679
theorem B5194079 : Blo 2307435 5194079 := bstep (se 1 (by rfl) ⟨3895559, by rfl⟩ : syracuseStep 5194079 = 7791119) B7791119
theorem B3462719 : Blo 2307435 3462719 := bstep (se 1 (by rfl) ⟨2597039, by rfl⟩ : syracuseStep 3462719 = 5194079) B5194079
theorem B2308479 : Blo 2307435 2308479 := bstep (se 1 (by rfl) ⟨1731359, by rfl⟩ : syracuseStep 2308479 = 3462719) B3462719
theorem B3462725 : Blo 2307435 3462725 := bbase (se 4 (by rfl) ⟨324630, by rfl⟩ : syracuseStep 3462725 = 649261) (by norm_num)
theorem B2308483 : Blo 2307435 2308483 := bstep (se 1 (by rfl) ⟨1731362, by rfl⟩ : syracuseStep 2308483 = 3462725) B3462725
theorem B3895573 : Blo 2307435 3895573 := bbase (se 6 (by rfl) ⟨91302, by rfl⟩ : syracuseStep 3895573 = 182605) (by norm_num)
theorem B5194097 : Blo 2307435 5194097 := bstep (se 2 (by rfl) ⟨1947786, by rfl⟩ : syracuseStep 5194097 = 3895573) B3895573
theorem B3462731 : Blo 2307435 3462731 := bstep (se 1 (by rfl) ⟨2597048, by rfl⟩ : syracuseStep 3462731 = 5194097) B5194097
theorem B2308487 : Blo 2307435 2308487 := bstep (se 1 (by rfl) ⟨1731365, by rfl⟩ : syracuseStep 2308487 = 3462731) B3462731
theorem B2597053 : Blo 2307435 2597053 := bbase (se 3 (by rfl) ⟨486947, by rfl⟩ : syracuseStep 2597053 = 973895) (by norm_num)
theorem B3462737 : Blo 2307435 3462737 := bstep (se 2 (by rfl) ⟨1298526, by rfl⟩ : syracuseStep 3462737 = 2597053) B2597053
theorem B2308491 : Blo 2307435 2308491 := bstep (se 1 (by rfl) ⟨1731368, by rfl⟩ : syracuseStep 2308491 = 3462737) B3462737
theorem B7791173 : Blo 2307435 7791173 := bbase (se 4 (by rfl) ⟨730422, by rfl⟩ : syracuseStep 7791173 = 1460845) (by norm_num)
theorem B5194115 : Blo 2307435 5194115 := bstep (se 1 (by rfl) ⟨3895586, by rfl⟩ : syracuseStep 5194115 = 7791173) B7791173
theorem B3462743 : Blo 2307435 3462743 := bstep (se 1 (by rfl) ⟨2597057, by rfl⟩ : syracuseStep 3462743 = 5194115) B5194115
theorem B2308495 : Blo 2307435 2308495 := bstep (se 1 (by rfl) ⟨1731371, by rfl⟩ : syracuseStep 2308495 = 3462743) B3462743
theorem B3462749 : Blo 2307435 3462749 := bbase (se 3 (by rfl) ⟨649265, by rfl⟩ : syracuseStep 3462749 = 1298531) (by norm_num)
theorem B2308499 : Blo 2307435 2308499 := bstep (se 1 (by rfl) ⟨1731374, by rfl⟩ : syracuseStep 2308499 = 3462749) B3462749
theorem B5194133 : Blo 2307435 5194133 := bbase (se 6 (by rfl) ⟨121737, by rfl⟩ : syracuseStep 5194133 = 243475) (by norm_num)
theorem B3462755 : Blo 2307435 3462755 := bstep (se 1 (by rfl) ⟨2597066, by rfl⟩ : syracuseStep 3462755 = 5194133) B5194133
theorem B2308503 : Blo 2307435 2308503 := bstep (se 1 (by rfl) ⟨1731377, by rfl⟩ : syracuseStep 2308503 = 3462755) B3462755
theorem B5546677 : Blo 2307435 5546677 := bbase (se 5 (by rfl) ⟨260000, by rfl⟩ : syracuseStep 5546677 = 520001) (by norm_num)
theorem B7395569 : Blo 2307435 7395569 := bstep (se 2 (by rfl) ⟨2773338, by rfl⟩ : syracuseStep 7395569 = 5546677) B5546677
theorem B4930379 : Blo 2307435 4930379 := bstep (se 1 (by rfl) ⟨3697784, by rfl⟩ : syracuseStep 4930379 = 7395569) B7395569
theorem B3286919 : Blo 2307435 3286919 := bstep (se 1 (by rfl) ⟨2465189, by rfl⟩ : syracuseStep 3286919 = 4930379) B4930379
theorem B8765117 : Blo 2307435 8765117 := bstep (se 3 (by rfl) ⟨1643459, by rfl⟩ : syracuseStep 8765117 = 3286919) B3286919
theorem B5843411 : Blo 2307435 5843411 := bstep (se 1 (by rfl) ⟨4382558, by rfl⟩ : syracuseStep 5843411 = 8765117) B8765117
theorem B3895607 : Blo 2307435 3895607 := bstep (se 1 (by rfl) ⟨2921705, by rfl⟩ : syracuseStep 3895607 = 5843411) B5843411
theorem B2597071 : Blo 2307435 2597071 := bstep (se 1 (by rfl) ⟨1947803, by rfl⟩ : syracuseStep 2597071 = 3895607) B3895607
theorem B3462761 : Blo 2307435 3462761 := bstep (se 2 (by rfl) ⟨1298535, by rfl⟩ : syracuseStep 3462761 = 2597071) B2597071
theorem B2308507 : Blo 2307435 2308507 := bstep (se 1 (by rfl) ⟨1731380, by rfl⟩ : syracuseStep 2308507 = 3462761) B3462761
theorem B9860773 : Blo 2307435 9860773 := bbase (se 4 (by rfl) ⟨924447, by rfl⟩ : syracuseStep 9860773 = 1848895) (by norm_num)
theorem B13147697 : Blo 2307435 13147697 := bstep (se 2 (by rfl) ⟨4930386, by rfl⟩ : syracuseStep 13147697 = 9860773) B9860773
theorem B8765131 : Blo 2307435 8765131 := bstep (se 1 (by rfl) ⟨6573848, by rfl⟩ : syracuseStep 8765131 = 13147697) B13147697
theorem B11686841 : Blo 2307435 11686841 := bstep (se 2 (by rfl) ⟨4382565, by rfl⟩ : syracuseStep 11686841 = 8765131) B8765131
theorem B7791227 : Blo 2307435 7791227 := bstep (se 1 (by rfl) ⟨5843420, by rfl⟩ : syracuseStep 7791227 = 11686841) B11686841
theorem B5194151 : Blo 2307435 5194151 := bstep (se 1 (by rfl) ⟨3895613, by rfl⟩ : syracuseStep 5194151 = 7791227) B7791227
theorem B3462767 : Blo 2307435 3462767 := bstep (se 1 (by rfl) ⟨2597075, by rfl⟩ : syracuseStep 3462767 = 5194151) B5194151
theorem B2308511 : Blo 2307435 2308511 := bstep (se 1 (by rfl) ⟨1731383, by rfl⟩ : syracuseStep 2308511 = 3462767) B3462767
theorem B3462773 : Blo 2307435 3462773 := bbase (se 5 (by rfl) ⟨162317, by rfl⟩ : syracuseStep 3462773 = 324635) (by norm_num)
theorem B2308515 : Blo 2307435 2308515 := bstep (se 1 (by rfl) ⟨1731386, by rfl⟩ : syracuseStep 2308515 = 3462773) B3462773
theorem B4382581 : Blo 2307435 4382581 := bbase (se 5 (by rfl) ⟨205433, by rfl⟩ : syracuseStep 4382581 = 410867) (by norm_num)
theorem B5843441 : Blo 2307435 5843441 := bstep (se 2 (by rfl) ⟨2191290, by rfl⟩ : syracuseStep 5843441 = 4382581) B4382581
theorem B3895627 : Blo 2307435 3895627 := bstep (se 1 (by rfl) ⟨2921720, by rfl⟩ : syracuseStep 3895627 = 5843441) B5843441
theorem B5194169 : Blo 2307435 5194169 := bstep (se 2 (by rfl) ⟨1947813, by rfl⟩ : syracuseStep 5194169 = 3895627) B3895627
theorem B3462779 : Blo 2307435 3462779 := bstep (se 1 (by rfl) ⟨2597084, by rfl⟩ : syracuseStep 3462779 = 5194169) B5194169
theorem B2308519 : Blo 2307435 2308519 := bstep (se 1 (by rfl) ⟨1731389, by rfl⟩ : syracuseStep 2308519 = 3462779) B3462779
theorem B2597089 : Blo 2307435 2597089 := bbase (se 2 (by rfl) ⟨973908, by rfl⟩ : syracuseStep 2597089 = 1947817) (by norm_num)
theorem B3462785 : Blo 2307435 3462785 := bstep (se 2 (by rfl) ⟨1298544, by rfl⟩ : syracuseStep 3462785 = 2597089) B2597089
theorem B2308523 : Blo 2307435 2308523 := bstep (se 1 (by rfl) ⟨1731392, by rfl⟩ : syracuseStep 2308523 = 3462785) B3462785
theorem B5843461 : Blo 2307435 5843461 := bbase (se 4 (by rfl) ⟨547824, by rfl⟩ : syracuseStep 5843461 = 1095649) (by norm_num)
theorem B7791281 : Blo 2307435 7791281 := bstep (se 2 (by rfl) ⟨2921730, by rfl⟩ : syracuseStep 7791281 = 5843461) B5843461
theorem B5194187 : Blo 2307435 5194187 := bstep (se 1 (by rfl) ⟨3895640, by rfl⟩ : syracuseStep 5194187 = 7791281) B7791281
theorem B3462791 : Blo 2307435 3462791 := bstep (se 1 (by rfl) ⟨2597093, by rfl⟩ : syracuseStep 3462791 = 5194187) B5194187
theorem B2308527 : Blo 2307435 2308527 := bstep (se 1 (by rfl) ⟨1731395, by rfl⟩ : syracuseStep 2308527 = 3462791) B3462791
theorem B3462797 : Blo 2307435 3462797 := bbase (se 3 (by rfl) ⟨649274, by rfl⟩ : syracuseStep 3462797 = 1298549) (by norm_num)
theorem B2308531 : Blo 2307435 2308531 := bstep (se 1 (by rfl) ⟨1731398, by rfl⟩ : syracuseStep 2308531 = 3462797) B3462797
theorem B5194205 : Blo 2307435 5194205 := bbase (se 3 (by rfl) ⟨973913, by rfl⟩ : syracuseStep 5194205 = 1947827) (by norm_num)
theorem B3462803 : Blo 2307435 3462803 := bstep (se 1 (by rfl) ⟨2597102, by rfl⟩ : syracuseStep 3462803 = 5194205) B5194205
theorem B2308535 : Blo 2307435 2308535 := bstep (se 1 (by rfl) ⟨1731401, by rfl⟩ : syracuseStep 2308535 = 3462803) B3462803
theorem B3895661 : Blo 2307435 3895661 := bbase (se 3 (by rfl) ⟨730436, by rfl⟩ : syracuseStep 3895661 = 1460873) (by norm_num)
theorem B2597107 : Blo 2307435 2597107 := bstep (se 1 (by rfl) ⟨1947830, by rfl⟩ : syracuseStep 2597107 = 3895661) B3895661
theorem B3462809 : Blo 2307435 3462809 := bstep (se 2 (by rfl) ⟨1298553, by rfl⟩ : syracuseStep 3462809 = 2597107) B2597107
theorem B2308539 : Blo 2307435 2308539 := bstep (se 1 (by rfl) ⟨1731404, by rfl⟩ : syracuseStep 2308539 = 3462809) B3462809
theorem B10530181 : Blo 2307435 10530181 := bbase (se 4 (by rfl) ⟨987204, by rfl⟩ : syracuseStep 10530181 = 1974409) (by norm_num)
theorem B56160965 : Blo 2307435 56160965 := bstep (se 4 (by rfl) ⟨5265090, by rfl⟩ : syracuseStep 56160965 = 10530181) B10530181
theorem B37440643 : Blo 2307435 37440643 := bstep (se 1 (by rfl) ⟨28080482, by rfl⟩ : syracuseStep 37440643 = 56160965) B56160965
theorem B49920857 : Blo 2307435 49920857 := bstep (se 2 (by rfl) ⟨18720321, by rfl⟩ : syracuseStep 49920857 = 37440643) B37440643
theorem B33280571 : Blo 2307435 33280571 := bstep (se 1 (by rfl) ⟨24960428, by rfl⟩ : syracuseStep 33280571 = 49920857) B49920857
theorem B22187047 : Blo 2307435 22187047 := bstep (se 1 (by rfl) ⟨16640285, by rfl⟩ : syracuseStep 22187047 = 33280571) B33280571
theorem B29582729 : Blo 2307435 29582729 := bstep (se 2 (by rfl) ⟨11093523, by rfl⟩ : syracuseStep 29582729 = 22187047) B22187047
theorem B19721819 : Blo 2307435 19721819 := bstep (se 1 (by rfl) ⟨14791364, by rfl⟩ : syracuseStep 19721819 = 29582729) B29582729
theorem B13147879 : Blo 2307435 13147879 := bstep (se 1 (by rfl) ⟨9860909, by rfl⟩ : syracuseStep 13147879 = 19721819) B19721819
theorem B17530505 : Blo 2307435 17530505 := bstep (se 2 (by rfl) ⟨6573939, by rfl⟩ : syracuseStep 17530505 = 13147879) B13147879
theorem B11687003 : Blo 2307435 11687003 := bstep (se 1 (by rfl) ⟨8765252, by rfl⟩ : syracuseStep 11687003 = 17530505) B17530505
theorem B7791335 : Blo 2307435 7791335 := bstep (se 1 (by rfl) ⟨5843501, by rfl⟩ : syracuseStep 7791335 = 11687003) B11687003
theorem B5194223 : Blo 2307435 5194223 := bstep (se 1 (by rfl) ⟨3895667, by rfl⟩ : syracuseStep 5194223 = 7791335) B7791335
theorem B3462815 : Blo 2307435 3462815 := bstep (se 1 (by rfl) ⟨2597111, by rfl⟩ : syracuseStep 3462815 = 5194223) B5194223
theorem B2308543 : Blo 2307435 2308543 := bstep (se 1 (by rfl) ⟨1731407, by rfl⟩ : syracuseStep 2308543 = 3462815) B3462815
theorem B3462821 : Blo 2307435 3462821 := bbase (se 4 (by rfl) ⟨324639, by rfl⟩ : syracuseStep 3462821 = 649279) (by norm_num)
theorem B2308547 : Blo 2307435 2308547 := bstep (se 1 (by rfl) ⟨1731410, by rfl⟩ : syracuseStep 2308547 = 3462821) B3462821
theorem B2921761 : Blo 2307435 2921761 := bbase (se 2 (by rfl) ⟨1095660, by rfl⟩ : syracuseStep 2921761 = 2191321) (by norm_num)
theorem B3895681 : Blo 2307435 3895681 := bstep (se 2 (by rfl) ⟨1460880, by rfl⟩ : syracuseStep 3895681 = 2921761) B2921761
theorem B5194241 : Blo 2307435 5194241 := bstep (se 2 (by rfl) ⟨1947840, by rfl⟩ : syracuseStep 5194241 = 3895681) B3895681
theorem B3462827 : Blo 2307435 3462827 := bstep (se 1 (by rfl) ⟨2597120, by rfl⟩ : syracuseStep 3462827 = 5194241) B5194241
theorem B2308551 : Blo 2307435 2308551 := bstep (se 1 (by rfl) ⟨1731413, by rfl⟩ : syracuseStep 2308551 = 3462827) B3462827
theorem B2597125 : Blo 2307435 2597125 := bbase (se 4 (by rfl) ⟨243480, by rfl⟩ : syracuseStep 2597125 = 486961) (by norm_num)
theorem B3462833 : Blo 2307435 3462833 := bstep (se 2 (by rfl) ⟨1298562, by rfl⟩ : syracuseStep 3462833 = 2597125) B2597125
theorem B2308555 : Blo 2307435 2308555 := bstep (se 1 (by rfl) ⟨1731416, by rfl⟩ : syracuseStep 2308555 = 3462833) B3462833
theorem B2465245 : Blo 2307435 2465245 := bbase (se 3 (by rfl) ⟨462233, by rfl⟩ : syracuseStep 2465245 = 924467) (by norm_num)
theorem B3286993 : Blo 2307435 3286993 := bstep (se 2 (by rfl) ⟨1232622, by rfl⟩ : syracuseStep 3286993 = 2465245) B2465245
theorem B4382657 : Blo 2307435 4382657 := bstep (se 2 (by rfl) ⟨1643496, by rfl⟩ : syracuseStep 4382657 = 3286993) B3286993
theorem B2921771 : Blo 2307435 2921771 := bstep (se 1 (by rfl) ⟨2191328, by rfl⟩ : syracuseStep 2921771 = 4382657) B4382657
theorem B7791389 : Blo 2307435 7791389 := bstep (se 3 (by rfl) ⟨1460885, by rfl⟩ : syracuseStep 7791389 = 2921771) B2921771
theorem B5194259 : Blo 2307435 5194259 := bstep (se 1 (by rfl) ⟨3895694, by rfl⟩ : syracuseStep 5194259 = 7791389) B7791389
theorem B3462839 : Blo 2307435 3462839 := bstep (se 1 (by rfl) ⟨2597129, by rfl⟩ : syracuseStep 3462839 = 5194259) B5194259
theorem B2308559 : Blo 2307435 2308559 := bstep (se 1 (by rfl) ⟨1731419, by rfl⟩ : syracuseStep 2308559 = 3462839) B3462839
theorem B3462845 : Blo 2307435 3462845 := bbase (se 3 (by rfl) ⟨649283, by rfl⟩ : syracuseStep 3462845 = 1298567) (by norm_num)
theorem B2308563 : Blo 2307435 2308563 := bstep (se 1 (by rfl) ⟨1731422, by rfl⟩ : syracuseStep 2308563 = 3462845) B3462845
theorem B5194277 : Blo 2307435 5194277 := bbase (se 4 (by rfl) ⟨486963, by rfl⟩ : syracuseStep 5194277 = 973927) (by norm_num)
theorem B3462851 : Blo 2307435 3462851 := bstep (se 1 (by rfl) ⟨2597138, by rfl⟩ : syracuseStep 3462851 = 5194277) B5194277
theorem B2308567 : Blo 2307435 2308567 := bstep (se 1 (by rfl) ⟨1731425, by rfl⟩ : syracuseStep 2308567 = 3462851) B3462851
theorem B5843573 : Blo 2307435 5843573 := bbase (se 5 (by rfl) ⟨273917, by rfl⟩ : syracuseStep 5843573 = 547835) (by norm_num)
theorem B3895715 : Blo 2307435 3895715 := bstep (se 1 (by rfl) ⟨2921786, by rfl⟩ : syracuseStep 3895715 = 5843573) B5843573
theorem B2597143 : Blo 2307435 2597143 := bstep (se 1 (by rfl) ⟨1947857, by rfl⟩ : syracuseStep 2597143 = 3895715) B3895715
theorem B3462857 : Blo 2307435 3462857 := bstep (se 2 (by rfl) ⟨1298571, by rfl⟩ : syracuseStep 3462857 = 2597143) B2597143
theorem B2308571 : Blo 2307435 2308571 := bstep (se 1 (by rfl) ⟨1731428, by rfl⟩ : syracuseStep 2308571 = 3462857) B3462857
theorem B2340073 : Blo 2307435 2340073 := bbase (se 2 (by rfl) ⟨877527, by rfl⟩ : syracuseStep 2340073 = 1755055) (by norm_num)
theorem B12480389 : Blo 2307435 12480389 := bstep (se 4 (by rfl) ⟨1170036, by rfl⟩ : syracuseStep 12480389 = 2340073) B2340073
theorem B8320259 : Blo 2307435 8320259 := bstep (se 1 (by rfl) ⟨6240194, by rfl⟩ : syracuseStep 8320259 = 12480389) B12480389
theorem B22187357 : Blo 2307435 22187357 := bstep (se 3 (by rfl) ⟨4160129, by rfl⟩ : syracuseStep 22187357 = 8320259) B8320259
theorem B14791571 : Blo 2307435 14791571 := bstep (se 1 (by rfl) ⟨11093678, by rfl⟩ : syracuseStep 14791571 = 22187357) B22187357
theorem B9861047 : Blo 2307435 9861047 := bstep (se 1 (by rfl) ⟨7395785, by rfl⟩ : syracuseStep 9861047 = 14791571) B14791571
theorem B6574031 : Blo 2307435 6574031 := bstep (se 1 (by rfl) ⟨4930523, by rfl⟩ : syracuseStep 6574031 = 9861047) B9861047
theorem B4382687 : Blo 2307435 4382687 := bstep (se 1 (by rfl) ⟨3287015, by rfl⟩ : syracuseStep 4382687 = 6574031) B6574031
theorem B11687165 : Blo 2307435 11687165 := bstep (se 3 (by rfl) ⟨2191343, by rfl⟩ : syracuseStep 11687165 = 4382687) B4382687
theorem B7791443 : Blo 2307435 7791443 := bstep (se 1 (by rfl) ⟨5843582, by rfl⟩ : syracuseStep 7791443 = 11687165) B11687165
theorem B5194295 : Blo 2307435 5194295 := bstep (se 1 (by rfl) ⟨3895721, by rfl⟩ : syracuseStep 5194295 = 7791443) B7791443
theorem B3462863 : Blo 2307435 3462863 := bstep (se 1 (by rfl) ⟨2597147, by rfl⟩ : syracuseStep 3462863 = 5194295) B5194295
theorem B2308575 : Blo 2307435 2308575 := bstep (se 1 (by rfl) ⟨1731431, by rfl⟩ : syracuseStep 2308575 = 3462863) B3462863
theorem B3462869 : Blo 2307435 3462869 := bbase (se 7 (by rfl) ⟨40580, by rfl⟩ : syracuseStep 3462869 = 81161) (by norm_num)
theorem B2308579 : Blo 2307435 2308579 := bstep (se 1 (by rfl) ⟨1731434, by rfl⟩ : syracuseStep 2308579 = 3462869) B3462869
theorem B4930541 : Blo 2307435 4930541 := bbase (se 3 (by rfl) ⟨924476, by rfl⟩ : syracuseStep 4930541 = 1848953) (by norm_num)
theorem B3287027 : Blo 2307435 3287027 := bstep (se 1 (by rfl) ⟨2465270, by rfl⟩ : syracuseStep 3287027 = 4930541) B4930541
theorem B8765405 : Blo 2307435 8765405 := bstep (se 3 (by rfl) ⟨1643513, by rfl⟩ : syracuseStep 8765405 = 3287027) B3287027
theorem B5843603 : Blo 2307435 5843603 := bstep (se 1 (by rfl) ⟨4382702, by rfl⟩ : syracuseStep 5843603 = 8765405) B8765405
theorem B3895735 : Blo 2307435 3895735 := bstep (se 1 (by rfl) ⟨2921801, by rfl⟩ : syracuseStep 3895735 = 5843603) B5843603
theorem B5194313 : Blo 2307435 5194313 := bstep (se 2 (by rfl) ⟨1947867, by rfl⟩ : syracuseStep 5194313 = 3895735) B3895735
theorem B3462875 : Blo 2307435 3462875 := bstep (se 1 (by rfl) ⟨2597156, by rfl⟩ : syracuseStep 3462875 = 5194313) B5194313
theorem B2308583 : Blo 2307435 2308583 := bstep (se 1 (by rfl) ⟨1731437, by rfl⟩ : syracuseStep 2308583 = 3462875) B3462875
theorem B2597161 : Blo 2307435 2597161 := bbase (se 2 (by rfl) ⟨973935, by rfl⟩ : syracuseStep 2597161 = 1947871) (by norm_num)
theorem B3462881 : Blo 2307435 3462881 := bstep (se 2 (by rfl) ⟨1298580, by rfl⟩ : syracuseStep 3462881 = 2597161) B2597161
theorem B2308587 : Blo 2307435 2308587 := bstep (se 1 (by rfl) ⟨1731440, by rfl⟩ : syracuseStep 2308587 = 3462881) B3462881
theorem B13327541 : Blo 2307435 13327541 := bbase (se 5 (by rfl) ⟨624728, by rfl⟩ : syracuseStep 13327541 = 1249457) (by norm_num)
theorem B8885027 : Blo 2307435 8885027 := bstep (se 1 (by rfl) ⟨6663770, by rfl⟩ : syracuseStep 8885027 = 13327541) B13327541
theorem B5923351 : Blo 2307435 5923351 := bstep (se 1 (by rfl) ⟨4442513, by rfl⟩ : syracuseStep 5923351 = 8885027) B8885027
theorem B31591205 : Blo 2307435 31591205 := bstep (se 4 (by rfl) ⟨2961675, by rfl⟩ : syracuseStep 31591205 = 5923351) B5923351
theorem B21060803 : Blo 2307435 21060803 := bstep (se 1 (by rfl) ⟨15795602, by rfl⟩ : syracuseStep 21060803 = 31591205) B31591205
theorem B14040535 : Blo 2307435 14040535 := bstep (se 1 (by rfl) ⟨10530401, by rfl⟩ : syracuseStep 14040535 = 21060803) B21060803
theorem B18720713 : Blo 2307435 18720713 := bstep (se 2 (by rfl) ⟨7020267, by rfl⟩ : syracuseStep 18720713 = 14040535) B14040535
theorem B12480475 : Blo 2307435 12480475 := bstep (se 1 (by rfl) ⟨9360356, by rfl⟩ : syracuseStep 12480475 = 18720713) B18720713
theorem B16640633 : Blo 2307435 16640633 := bstep (se 2 (by rfl) ⟨6240237, by rfl⟩ : syracuseStep 16640633 = 12480475) B12480475
theorem B11093755 : Blo 2307435 11093755 := bstep (se 1 (by rfl) ⟨8320316, by rfl⟩ : syracuseStep 11093755 = 16640633) B16640633
theorem B14791673 : Blo 2307435 14791673 := bstep (se 2 (by rfl) ⟨5546877, by rfl⟩ : syracuseStep 14791673 = 11093755) B11093755
theorem B9861115 : Blo 2307435 9861115 := bstep (se 1 (by rfl) ⟨7395836, by rfl⟩ : syracuseStep 9861115 = 14791673) B14791673
theorem B13148153 : Blo 2307435 13148153 := bstep (se 2 (by rfl) ⟨4930557, by rfl⟩ : syracuseStep 13148153 = 9861115) B9861115
theorem B8765435 : Blo 2307435 8765435 := bstep (se 1 (by rfl) ⟨6574076, by rfl⟩ : syracuseStep 8765435 = 13148153) B13148153
theorem B5843623 : Blo 2307435 5843623 := bstep (se 1 (by rfl) ⟨4382717, by rfl⟩ : syracuseStep 5843623 = 8765435) B8765435
theorem B7791497 : Blo 2307435 7791497 := bstep (se 2 (by rfl) ⟨2921811, by rfl⟩ : syracuseStep 7791497 = 5843623) B5843623
theorem B5194331 : Blo 2307435 5194331 := bstep (se 1 (by rfl) ⟨3895748, by rfl⟩ : syracuseStep 5194331 = 7791497) B7791497
theorem B3462887 : Blo 2307435 3462887 := bstep (se 1 (by rfl) ⟨2597165, by rfl⟩ : syracuseStep 3462887 = 5194331) B5194331
theorem B2308591 : Blo 2307435 2308591 := bstep (se 1 (by rfl) ⟨1731443, by rfl⟩ : syracuseStep 2308591 = 3462887) B3462887
theorem B3462893 : Blo 2307435 3462893 := bbase (se 3 (by rfl) ⟨649292, by rfl⟩ : syracuseStep 3462893 = 1298585) (by norm_num)
theorem B2308595 : Blo 2307435 2308595 := bstep (se 1 (by rfl) ⟨1731446, by rfl⟩ : syracuseStep 2308595 = 3462893) B3462893
theorem B5194349 : Blo 2307435 5194349 := bbase (se 3 (by rfl) ⟨973940, by rfl⟩ : syracuseStep 5194349 = 1947881) (by norm_num)
theorem B3462899 : Blo 2307435 3462899 := bstep (se 1 (by rfl) ⟨2597174, by rfl⟩ : syracuseStep 3462899 = 5194349) B5194349
theorem B2308599 : Blo 2307435 2308599 := bstep (se 1 (by rfl) ⟨1731449, by rfl⟩ : syracuseStep 2308599 = 3462899) B3462899
theorem B4382741 : Blo 2307435 4382741 := bbase (se 6 (by rfl) ⟨102720, by rfl⟩ : syracuseStep 4382741 = 205441) (by norm_num)
theorem B2921827 : Blo 2307435 2921827 := bstep (se 1 (by rfl) ⟨2191370, by rfl⟩ : syracuseStep 2921827 = 4382741) B4382741
theorem B3895769 : Blo 2307435 3895769 := bstep (se 2 (by rfl) ⟨1460913, by rfl⟩ : syracuseStep 3895769 = 2921827) B2921827
theorem B2597179 : Blo 2307435 2597179 := bstep (se 1 (by rfl) ⟨1947884, by rfl⟩ : syracuseStep 2597179 = 3895769) B3895769
theorem B3462905 : Blo 2307435 3462905 := bstep (se 2 (by rfl) ⟨1298589, by rfl⟩ : syracuseStep 3462905 = 2597179) B2597179
theorem B2308603 : Blo 2307435 2308603 := bstep (se 1 (by rfl) ⟨1731452, by rfl⟩ : syracuseStep 2308603 = 3462905) B3462905
theorem B4997861 : Blo 2307435 4997861 := bbase (se 4 (by rfl) ⟨468549, by rfl⟩ : syracuseStep 4997861 = 937099) (by norm_num)
theorem B53310517 : Blo 2307435 53310517 := bstep (se 5 (by rfl) ⟨2498930, by rfl⟩ : syracuseStep 53310517 = 4997861) B4997861
theorem B284322757 : Blo 2307435 284322757 := bstep (se 4 (by rfl) ⟨26655258, by rfl⟩ : syracuseStep 284322757 = 53310517) B53310517
theorem B379097009 : Blo 2307435 379097009 := bstep (se 2 (by rfl) ⟨142161378, by rfl⟩ : syracuseStep 379097009 = 284322757) B284322757
theorem B252731339 : Blo 2307435 252731339 := bstep (se 1 (by rfl) ⟨189548504, by rfl⟩ : syracuseStep 252731339 = 379097009) B379097009
theorem B168487559 : Blo 2307435 168487559 := bstep (se 1 (by rfl) ⟨126365669, by rfl⟩ : syracuseStep 168487559 = 252731339) B252731339
theorem B112325039 : Blo 2307435 112325039 := bstep (se 1 (by rfl) ⟨84243779, by rfl⟩ : syracuseStep 112325039 = 168487559) B168487559
theorem B74883359 : Blo 2307435 74883359 := bstep (se 1 (by rfl) ⟨56162519, by rfl⟩ : syracuseStep 74883359 = 112325039) B112325039
theorem B49922239 : Blo 2307435 49922239 := bstep (se 1 (by rfl) ⟨37441679, by rfl⟩ : syracuseStep 49922239 = 74883359) B74883359
theorem B66562985 : Blo 2307435 66562985 := bstep (se 2 (by rfl) ⟨24961119, by rfl⟩ : syracuseStep 66562985 = 49922239) B49922239
theorem B44375323 : Blo 2307435 44375323 := bstep (se 1 (by rfl) ⟨33281492, by rfl⟩ : syracuseStep 44375323 = 66562985) B66562985
theorem B59167097 : Blo 2307435 59167097 := bstep (se 2 (by rfl) ⟨22187661, by rfl⟩ : syracuseStep 59167097 = 44375323) B44375323
theorem B39444731 : Blo 2307435 39444731 := bstep (se 1 (by rfl) ⟨29583548, by rfl⟩ : syracuseStep 39444731 = 59167097) B59167097
theorem B26296487 : Blo 2307435 26296487 := bstep (se 1 (by rfl) ⟨19722365, by rfl⟩ : syracuseStep 26296487 = 39444731) B39444731
theorem B17530991 : Blo 2307435 17530991 := bstep (se 1 (by rfl) ⟨13148243, by rfl⟩ : syracuseStep 17530991 = 26296487) B26296487
theorem B11687327 : Blo 2307435 11687327 := bstep (se 1 (by rfl) ⟨8765495, by rfl⟩ : syracuseStep 11687327 = 17530991) B17530991
theorem B7791551 : Blo 2307435 7791551 := bstep (se 1 (by rfl) ⟨5843663, by rfl⟩ : syracuseStep 7791551 = 11687327) B11687327
theorem B5194367 : Blo 2307435 5194367 := bstep (se 1 (by rfl) ⟨3895775, by rfl⟩ : syracuseStep 5194367 = 7791551) B7791551
theorem B3462911 : Blo 2307435 3462911 := bstep (se 1 (by rfl) ⟨2597183, by rfl⟩ : syracuseStep 3462911 = 5194367) B5194367
theorem B2308607 : Blo 2307435 2308607 := bstep (se 1 (by rfl) ⟨1731455, by rfl⟩ : syracuseStep 2308607 = 3462911) B3462911
theorem B3462917 : Blo 2307435 3462917 := bbase (se 4 (by rfl) ⟨324648, by rfl⟩ : syracuseStep 3462917 = 649297) (by norm_num)
theorem B2308611 : Blo 2307435 2308611 := bstep (se 1 (by rfl) ⟨1731458, by rfl⟩ : syracuseStep 2308611 = 3462917) B3462917
theorem B3895789 : Blo 2307435 3895789 := bbase (se 3 (by rfl) ⟨730460, by rfl⟩ : syracuseStep 3895789 = 1460921) (by norm_num)
theorem B5194385 : Blo 2307435 5194385 := bstep (se 2 (by rfl) ⟨1947894, by rfl⟩ : syracuseStep 5194385 = 3895789) B3895789
theorem B3462923 : Blo 2307435 3462923 := bstep (se 1 (by rfl) ⟨2597192, by rfl⟩ : syracuseStep 3462923 = 5194385) B5194385
theorem B2308615 : Blo 2307435 2308615 := bstep (se 1 (by rfl) ⟨1731461, by rfl⟩ : syracuseStep 2308615 = 3462923) B3462923
theorem B2597197 : Blo 2307435 2597197 := bbase (se 3 (by rfl) ⟨486974, by rfl⟩ : syracuseStep 2597197 = 973949) (by norm_num)
theorem B3462929 : Blo 2307435 3462929 := bstep (se 2 (by rfl) ⟨1298598, by rfl⟩ : syracuseStep 3462929 = 2597197) B2597197
theorem B2308619 : Blo 2307435 2308619 := bstep (se 1 (by rfl) ⟨1731464, by rfl⟩ : syracuseStep 2308619 = 3462929) B3462929
theorem B7791605 : Blo 2307435 7791605 := bbase (se 5 (by rfl) ⟨365231, by rfl⟩ : syracuseStep 7791605 = 730463) (by norm_num)
theorem B5194403 : Blo 2307435 5194403 := bstep (se 1 (by rfl) ⟨3895802, by rfl⟩ : syracuseStep 5194403 = 7791605) B7791605
theorem B3462935 : Blo 2307435 3462935 := bstep (se 1 (by rfl) ⟨2597201, by rfl⟩ : syracuseStep 3462935 = 5194403) B5194403
theorem B2308623 : Blo 2307435 2308623 := bstep (se 1 (by rfl) ⟨1731467, by rfl⟩ : syracuseStep 2308623 = 3462935) B3462935
theorem B3462941 : Blo 2307435 3462941 := bbase (se 3 (by rfl) ⟨649301, by rfl⟩ : syracuseStep 3462941 = 1298603) (by norm_num)
theorem B2308627 : Blo 2307435 2308627 := bstep (se 1 (by rfl) ⟨1731470, by rfl⟩ : syracuseStep 2308627 = 3462941) B3462941
theorem B5194421 : Blo 2307435 5194421 := bbase (se 5 (by rfl) ⟨243488, by rfl⟩ : syracuseStep 5194421 = 486977) (by norm_num)
theorem B3462947 : Blo 2307435 3462947 := bstep (se 1 (by rfl) ⟨2597210, by rfl⟩ : syracuseStep 3462947 = 5194421) B5194421
theorem B2308631 : Blo 2307435 2308631 := bstep (se 1 (by rfl) ⟨1731473, by rfl⟩ : syracuseStep 2308631 = 3462947) B3462947
theorem B13148405 : Blo 2307435 13148405 := bbase (se 5 (by rfl) ⟨616331, by rfl⟩ : syracuseStep 13148405 = 1232663) (by norm_num)
theorem B8765603 : Blo 2307435 8765603 := bstep (se 1 (by rfl) ⟨6574202, by rfl⟩ : syracuseStep 8765603 = 13148405) B13148405
theorem B5843735 : Blo 2307435 5843735 := bstep (se 1 (by rfl) ⟨4382801, by rfl⟩ : syracuseStep 5843735 = 8765603) B8765603
theorem B3895823 : Blo 2307435 3895823 := bstep (se 1 (by rfl) ⟨2921867, by rfl⟩ : syracuseStep 3895823 = 5843735) B5843735
theorem B2597215 : Blo 2307435 2597215 := bstep (se 1 (by rfl) ⟨1947911, by rfl⟩ : syracuseStep 2597215 = 3895823) B3895823
theorem B3462953 : Blo 2307435 3462953 := bstep (se 2 (by rfl) ⟨1298607, by rfl⟩ : syracuseStep 3462953 = 2597215) B2597215
theorem B2308635 : Blo 2307435 2308635 := bstep (se 1 (by rfl) ⟨1731476, by rfl⟩ : syracuseStep 2308635 = 3462953) B3462953
theorem B6574213 : Blo 2307435 6574213 := bbase (se 4 (by rfl) ⟨616332, by rfl⟩ : syracuseStep 6574213 = 1232665) (by norm_num)
theorem B8765617 : Blo 2307435 8765617 := bstep (se 2 (by rfl) ⟨3287106, by rfl⟩ : syracuseStep 8765617 = 6574213) B6574213
theorem B11687489 : Blo 2307435 11687489 := bstep (se 2 (by rfl) ⟨4382808, by rfl⟩ : syracuseStep 11687489 = 8765617) B8765617
theorem B7791659 : Blo 2307435 7791659 := bstep (se 1 (by rfl) ⟨5843744, by rfl⟩ : syracuseStep 7791659 = 11687489) B11687489
theorem B5194439 : Blo 2307435 5194439 := bstep (se 1 (by rfl) ⟨3895829, by rfl⟩ : syracuseStep 5194439 = 7791659) B7791659
theorem B3462959 : Blo 2307435 3462959 := bstep (se 1 (by rfl) ⟨2597219, by rfl⟩ : syracuseStep 3462959 = 5194439) B5194439
theorem B2308639 : Blo 2307435 2308639 := bstep (se 1 (by rfl) ⟨1731479, by rfl⟩ : syracuseStep 2308639 = 3462959) B3462959
theorem B3462965 : Blo 2307435 3462965 := bbase (se 5 (by rfl) ⟨162326, by rfl⟩ : syracuseStep 3462965 = 324653) (by norm_num)
theorem B2308643 : Blo 2307435 2308643 := bstep (se 1 (by rfl) ⟨1731482, by rfl⟩ : syracuseStep 2308643 = 3462965) B3462965
theorem B5843765 : Blo 2307435 5843765 := bbase (se 5 (by rfl) ⟨273926, by rfl⟩ : syracuseStep 5843765 = 547853) (by norm_num)
theorem B3895843 : Blo 2307435 3895843 := bstep (se 1 (by rfl) ⟨2921882, by rfl⟩ : syracuseStep 3895843 = 5843765) B5843765
theorem B5194457 : Blo 2307435 5194457 := bstep (se 2 (by rfl) ⟨1947921, by rfl⟩ : syracuseStep 5194457 = 3895843) B3895843
theorem B3462971 : Blo 2307435 3462971 := bstep (se 1 (by rfl) ⟨2597228, by rfl⟩ : syracuseStep 3462971 = 5194457) B5194457
theorem B2308647 : Blo 2307435 2308647 := bstep (se 1 (by rfl) ⟨1731485, by rfl⟩ : syracuseStep 2308647 = 3462971) B3462971
theorem B2597233 : Blo 2307435 2597233 := bbase (se 2 (by rfl) ⟨973962, by rfl⟩ : syracuseStep 2597233 = 1947925) (by norm_num)
theorem B3462977 : Blo 2307435 3462977 := bstep (se 2 (by rfl) ⟨1298616, by rfl⟩ : syracuseStep 3462977 = 2597233) B2597233
theorem B2308651 : Blo 2307435 2308651 := bstep (se 1 (by rfl) ⟨1731488, by rfl⟩ : syracuseStep 2308651 = 3462977) B3462977
theorem B3698021 : Blo 2307435 3698021 := bbase (se 4 (by rfl) ⟨346689, by rfl⟩ : syracuseStep 3698021 = 693379) (by norm_num)
theorem B9861389 : Blo 2307435 9861389 := bstep (se 3 (by rfl) ⟨1849010, by rfl⟩ : syracuseStep 9861389 = 3698021) B3698021
theorem B6574259 : Blo 2307435 6574259 := bstep (se 1 (by rfl) ⟨4930694, by rfl⟩ : syracuseStep 6574259 = 9861389) B9861389
theorem B4382839 : Blo 2307435 4382839 := bstep (se 1 (by rfl) ⟨3287129, by rfl⟩ : syracuseStep 4382839 = 6574259) B6574259
theorem B5843785 : Blo 2307435 5843785 := bstep (se 2 (by rfl) ⟨2191419, by rfl⟩ : syracuseStep 5843785 = 4382839) B4382839
theorem B7791713 : Blo 2307435 7791713 := bstep (se 2 (by rfl) ⟨2921892, by rfl⟩ : syracuseStep 7791713 = 5843785) B5843785
theorem B5194475 : Blo 2307435 5194475 := bstep (se 1 (by rfl) ⟨3895856, by rfl⟩ : syracuseStep 5194475 = 7791713) B7791713
theorem B3462983 : Blo 2307435 3462983 := bstep (se 1 (by rfl) ⟨2597237, by rfl⟩ : syracuseStep 3462983 = 5194475) B5194475
theorem B2308655 : Blo 2307435 2308655 := bstep (se 1 (by rfl) ⟨1731491, by rfl⟩ : syracuseStep 2308655 = 3462983) B3462983
theorem B3462989 : Blo 2307435 3462989 := bbase (se 3 (by rfl) ⟨649310, by rfl⟩ : syracuseStep 3462989 = 1298621) (by norm_num)
theorem B2308659 : Blo 2307435 2308659 := bstep (se 1 (by rfl) ⟨1731494, by rfl⟩ : syracuseStep 2308659 = 3462989) B3462989
theorem B5194493 : Blo 2307435 5194493 := bbase (se 3 (by rfl) ⟨973967, by rfl⟩ : syracuseStep 5194493 = 1947935) (by norm_num)
theorem B3462995 : Blo 2307435 3462995 := bstep (se 1 (by rfl) ⟨2597246, by rfl⟩ : syracuseStep 3462995 = 5194493) B5194493
theorem B2308663 : Blo 2307435 2308663 := bstep (se 1 (by rfl) ⟨1731497, by rfl⟩ : syracuseStep 2308663 = 3462995) B3462995
theorem B3895877 : Blo 2307435 3895877 := bbase (se 4 (by rfl) ⟨365238, by rfl⟩ : syracuseStep 3895877 = 730477) (by norm_num)
theorem B2597251 : Blo 2307435 2597251 := bstep (se 1 (by rfl) ⟨1947938, by rfl⟩ : syracuseStep 2597251 = 3895877) B3895877
theorem B3463001 : Blo 2307435 3463001 := bstep (se 2 (by rfl) ⟨1298625, by rfl⟩ : syracuseStep 3463001 = 2597251) B2597251
theorem B2308667 : Blo 2307435 2308667 := bstep (se 1 (by rfl) ⟨1731500, by rfl⟩ : syracuseStep 2308667 = 3463001) B3463001
theorem B17531477 : Blo 2307435 17531477 := bbase (se 8 (by rfl) ⟨102723, by rfl⟩ : syracuseStep 17531477 = 205447) (by norm_num)
theorem B11687651 : Blo 2307435 11687651 := bstep (se 1 (by rfl) ⟨8765738, by rfl⟩ : syracuseStep 11687651 = 17531477) B17531477
theorem B7791767 : Blo 2307435 7791767 := bstep (se 1 (by rfl) ⟨5843825, by rfl⟩ : syracuseStep 7791767 = 11687651) B11687651
theorem B5194511 : Blo 2307435 5194511 := bstep (se 1 (by rfl) ⟨3895883, by rfl⟩ : syracuseStep 5194511 = 7791767) B7791767
theorem B3463007 : Blo 2307435 3463007 := bstep (se 1 (by rfl) ⟨2597255, by rfl⟩ : syracuseStep 3463007 = 5194511) B5194511
theorem B2308671 : Blo 2307435 2308671 := bstep (se 1 (by rfl) ⟨1731503, by rfl⟩ : syracuseStep 2308671 = 3463007) B3463007
theorem B3463013 : Blo 2307435 3463013 := bbase (se 4 (by rfl) ⟨324657, by rfl⟩ : syracuseStep 3463013 = 649315) (by norm_num)
theorem B2308675 : Blo 2307435 2308675 := bstep (se 1 (by rfl) ⟨1731506, by rfl⟩ : syracuseStep 2308675 = 3463013) B3463013
theorem B4382885 : Blo 2307435 4382885 := bbase (se 4 (by rfl) ⟨410895, by rfl⟩ : syracuseStep 4382885 = 821791) (by norm_num)
theorem B2921923 : Blo 2307435 2921923 := bstep (se 1 (by rfl) ⟨2191442, by rfl⟩ : syracuseStep 2921923 = 4382885) B4382885
theorem B3895897 : Blo 2307435 3895897 := bstep (se 2 (by rfl) ⟨1460961, by rfl⟩ : syracuseStep 3895897 = 2921923) B2921923
theorem B5194529 : Blo 2307435 5194529 := bstep (se 2 (by rfl) ⟨1947948, by rfl⟩ : syracuseStep 5194529 = 3895897) B3895897
theorem B3463019 : Blo 2307435 3463019 := bstep (se 1 (by rfl) ⟨2597264, by rfl⟩ : syracuseStep 3463019 = 5194529) B5194529
theorem B2308679 : Blo 2307435 2308679 := bstep (se 1 (by rfl) ⟨1731509, by rfl⟩ : syracuseStep 2308679 = 3463019) B3463019
theorem B2597269 : Blo 2307435 2597269 := bbase (se 6 (by rfl) ⟨60873, by rfl⟩ : syracuseStep 2597269 = 121747) (by norm_num)
theorem B3463025 : Blo 2307435 3463025 := bstep (se 2 (by rfl) ⟨1298634, by rfl⟩ : syracuseStep 3463025 = 2597269) B2597269
theorem B2308683 : Blo 2307435 2308683 := bstep (se 1 (by rfl) ⟨1731512, by rfl⟩ : syracuseStep 2308683 = 3463025) B3463025
theorem B2921933 : Blo 2307435 2921933 := bbase (se 3 (by rfl) ⟨547862, by rfl⟩ : syracuseStep 2921933 = 1095725) (by norm_num)
theorem B7791821 : Blo 2307435 7791821 := bstep (se 3 (by rfl) ⟨1460966, by rfl⟩ : syracuseStep 7791821 = 2921933) B2921933
theorem B5194547 : Blo 2307435 5194547 := bstep (se 1 (by rfl) ⟨3895910, by rfl⟩ : syracuseStep 5194547 = 7791821) B7791821
theorem B3463031 : Blo 2307435 3463031 := bstep (se 1 (by rfl) ⟨2597273, by rfl⟩ : syracuseStep 3463031 = 5194547) B5194547
theorem B2308687 : Blo 2307435 2308687 := bstep (se 1 (by rfl) ⟨1731515, by rfl⟩ : syracuseStep 2308687 = 3463031) B3463031
theorem B3463037 : Blo 2307435 3463037 := bbase (se 3 (by rfl) ⟨649319, by rfl⟩ : syracuseStep 3463037 = 1298639) (by norm_num)
theorem B2308691 : Blo 2307435 2308691 := bstep (se 1 (by rfl) ⟨1731518, by rfl⟩ : syracuseStep 2308691 = 3463037) B3463037
theorem B5194565 : Blo 2307435 5194565 := bbase (se 4 (by rfl) ⟨486990, by rfl⟩ : syracuseStep 5194565 = 973981) (by norm_num)
theorem B3463043 : Blo 2307435 3463043 := bstep (se 1 (by rfl) ⟨2597282, by rfl⟩ : syracuseStep 3463043 = 5194565) B5194565
theorem B2308695 : Blo 2307435 2308695 := bstep (se 1 (by rfl) ⟨1731521, by rfl⟩ : syracuseStep 2308695 = 3463043) B3463043
theorem B4930789 : Blo 2307435 4930789 := bbase (se 4 (by rfl) ⟨462261, by rfl⟩ : syracuseStep 4930789 = 924523) (by norm_num)
theorem B6574385 : Blo 2307435 6574385 := bstep (se 2 (by rfl) ⟨2465394, by rfl⟩ : syracuseStep 6574385 = 4930789) B4930789
theorem B4382923 : Blo 2307435 4382923 := bstep (se 1 (by rfl) ⟨3287192, by rfl⟩ : syracuseStep 4382923 = 6574385) B6574385
theorem B5843897 : Blo 2307435 5843897 := bstep (se 2 (by rfl) ⟨2191461, by rfl⟩ : syracuseStep 5843897 = 4382923) B4382923
theorem B3895931 : Blo 2307435 3895931 := bstep (se 1 (by rfl) ⟨2921948, by rfl⟩ : syracuseStep 3895931 = 5843897) B5843897
theorem B2597287 : Blo 2307435 2597287 := bstep (se 1 (by rfl) ⟨1947965, by rfl⟩ : syracuseStep 2597287 = 3895931) B3895931
theorem B3463049 : Blo 2307435 3463049 := bstep (se 2 (by rfl) ⟨1298643, by rfl⟩ : syracuseStep 3463049 = 2597287) B2597287
theorem B2308699 : Blo 2307435 2308699 := bstep (se 1 (by rfl) ⟨1731524, by rfl⟩ : syracuseStep 2308699 = 3463049) B3463049
theorem B11687813 : Blo 2307435 11687813 := bbase (se 4 (by rfl) ⟨1095732, by rfl⟩ : syracuseStep 11687813 = 2191465) (by norm_num)
theorem B7791875 : Blo 2307435 7791875 := bstep (se 1 (by rfl) ⟨5843906, by rfl⟩ : syracuseStep 7791875 = 11687813) B11687813
theorem B5194583 : Blo 2307435 5194583 := bstep (se 1 (by rfl) ⟨3895937, by rfl⟩ : syracuseStep 5194583 = 7791875) B7791875
theorem B3463055 : Blo 2307435 3463055 := bstep (se 1 (by rfl) ⟨2597291, by rfl⟩ : syracuseStep 3463055 = 5194583) B5194583
theorem B2308703 : Blo 2307435 2308703 := bstep (se 1 (by rfl) ⟨1731527, by rfl⟩ : syracuseStep 2308703 = 3463055) B3463055
theorem B3463061 : Blo 2307435 3463061 := bbase (se 6 (by rfl) ⟨81165, by rfl⟩ : syracuseStep 3463061 = 162331) (by norm_num)
theorem B2308707 : Blo 2307435 2308707 := bstep (se 1 (by rfl) ⟨1731530, by rfl⟩ : syracuseStep 2308707 = 3463061) B3463061
theorem B8434277 : Blo 2307435 8434277 := bbase (se 4 (by rfl) ⟨790713, by rfl⟩ : syracuseStep 8434277 = 1581427) (by norm_num)
theorem B5622851 : Blo 2307435 5622851 := bstep (se 1 (by rfl) ⟨4217138, by rfl⟩ : syracuseStep 5622851 = 8434277) B8434277
theorem B3748567 : Blo 2307435 3748567 := bstep (se 1 (by rfl) ⟨2811425, by rfl⟩ : syracuseStep 3748567 = 5622851) B5622851
theorem B4998089 : Blo 2307435 4998089 := bstep (se 2 (by rfl) ⟨1874283, by rfl⟩ : syracuseStep 4998089 = 3748567) B3748567
theorem B3332059 : Blo 2307435 3332059 := bstep (se 1 (by rfl) ⟨2499044, by rfl⟩ : syracuseStep 3332059 = 4998089) B4998089
theorem B71083925 : Blo 2307435 71083925 := bstep (se 6 (by rfl) ⟨1666029, by rfl⟩ : syracuseStep 71083925 = 3332059) B3332059
theorem B47389283 : Blo 2307435 47389283 := bstep (se 1 (by rfl) ⟨35541962, by rfl⟩ : syracuseStep 47389283 = 71083925) B71083925
theorem B31592855 : Blo 2307435 31592855 := bstep (se 1 (by rfl) ⟨23694641, by rfl⟩ : syracuseStep 31592855 = 47389283) B47389283
theorem B21061903 : Blo 2307435 21061903 := bstep (se 1 (by rfl) ⟨15796427, by rfl⟩ : syracuseStep 21061903 = 31592855) B31592855
theorem B28082537 : Blo 2307435 28082537 := bstep (se 2 (by rfl) ⟨10530951, by rfl⟩ : syracuseStep 28082537 = 21061903) B21061903
theorem B18721691 : Blo 2307435 18721691 := bstep (se 1 (by rfl) ⟨14041268, by rfl⟩ : syracuseStep 18721691 = 28082537) B28082537
theorem B12481127 : Blo 2307435 12481127 := bstep (se 1 (by rfl) ⟨9360845, by rfl⟩ : syracuseStep 12481127 = 18721691) B18721691
theorem B8320751 : Blo 2307435 8320751 := bstep (se 1 (by rfl) ⟨6240563, by rfl⟩ : syracuseStep 8320751 = 12481127) B12481127
theorem B5547167 : Blo 2307435 5547167 := bstep (se 1 (by rfl) ⟨4160375, by rfl⟩ : syracuseStep 5547167 = 8320751) B8320751
theorem B3698111 : Blo 2307435 3698111 := bstep (se 1 (by rfl) ⟨2773583, by rfl⟩ : syracuseStep 3698111 = 5547167) B5547167
theorem B2465407 : Blo 2307435 2465407 := bstep (se 1 (by rfl) ⟨1849055, by rfl⟩ : syracuseStep 2465407 = 3698111) B3698111
theorem B13148837 : Blo 2307435 13148837 := bstep (se 4 (by rfl) ⟨1232703, by rfl⟩ : syracuseStep 13148837 = 2465407) B2465407
theorem B8765891 : Blo 2307435 8765891 := bstep (se 1 (by rfl) ⟨6574418, by rfl⟩ : syracuseStep 8765891 = 13148837) B13148837
theorem B5843927 : Blo 2307435 5843927 := bstep (se 1 (by rfl) ⟨4382945, by rfl⟩ : syracuseStep 5843927 = 8765891) B8765891
theorem B3895951 : Blo 2307435 3895951 := bstep (se 1 (by rfl) ⟨2921963, by rfl⟩ : syracuseStep 3895951 = 5843927) B5843927
theorem B5194601 : Blo 2307435 5194601 := bstep (se 2 (by rfl) ⟨1947975, by rfl⟩ : syracuseStep 5194601 = 3895951) B3895951
theorem B3463067 : Blo 2307435 3463067 := bstep (se 1 (by rfl) ⟨2597300, by rfl⟩ : syracuseStep 3463067 = 5194601) B5194601
theorem B2308711 : Blo 2307435 2308711 := bstep (se 1 (by rfl) ⟨1731533, by rfl⟩ : syracuseStep 2308711 = 3463067) B3463067
theorem B2597305 : Blo 2307435 2597305 := bbase (se 2 (by rfl) ⟨973989, by rfl⟩ : syracuseStep 2597305 = 1947979) (by norm_num)
theorem B3463073 : Blo 2307435 3463073 := bstep (se 2 (by rfl) ⟨1298652, by rfl⟩ : syracuseStep 3463073 = 2597305) B2597305
theorem B2308715 : Blo 2307435 2308715 := bstep (se 1 (by rfl) ⟨1731536, by rfl⟩ : syracuseStep 2308715 = 3463073) B3463073
theorem B16641557 : Blo 2307435 16641557 := bbase (se 6 (by rfl) ⟨390036, by rfl⟩ : syracuseStep 16641557 = 780073) (by norm_num)
theorem B11094371 : Blo 2307435 11094371 := bstep (se 1 (by rfl) ⟨8320778, by rfl⟩ : syracuseStep 11094371 = 16641557) B16641557
theorem B7396247 : Blo 2307435 7396247 := bstep (se 1 (by rfl) ⟨5547185, by rfl⟩ : syracuseStep 7396247 = 11094371) B11094371
theorem B4930831 : Blo 2307435 4930831 := bstep (se 1 (by rfl) ⟨3698123, by rfl⟩ : syracuseStep 4930831 = 7396247) B7396247
theorem B6574441 : Blo 2307435 6574441 := bstep (se 2 (by rfl) ⟨2465415, by rfl⟩ : syracuseStep 6574441 = 4930831) B4930831
theorem B8765921 : Blo 2307435 8765921 := bstep (se 2 (by rfl) ⟨3287220, by rfl⟩ : syracuseStep 8765921 = 6574441) B6574441
theorem B5843947 : Blo 2307435 5843947 := bstep (se 1 (by rfl) ⟨4382960, by rfl⟩ : syracuseStep 5843947 = 8765921) B8765921
theorem B7791929 : Blo 2307435 7791929 := bstep (se 2 (by rfl) ⟨2921973, by rfl⟩ : syracuseStep 7791929 = 5843947) B5843947
theorem B5194619 : Blo 2307435 5194619 := bstep (se 1 (by rfl) ⟨3895964, by rfl⟩ : syracuseStep 5194619 = 7791929) B7791929
theorem B3463079 : Blo 2307435 3463079 := bstep (se 1 (by rfl) ⟨2597309, by rfl⟩ : syracuseStep 3463079 = 5194619) B5194619
theorem B2308719 : Blo 2307435 2308719 := bstep (se 1 (by rfl) ⟨1731539, by rfl⟩ : syracuseStep 2308719 = 3463079) B3463079
theorem B3463085 : Blo 2307435 3463085 := bbase (se 3 (by rfl) ⟨649328, by rfl⟩ : syracuseStep 3463085 = 1298657) (by norm_num)
theorem B2308723 : Blo 2307435 2308723 := bstep (se 1 (by rfl) ⟨1731542, by rfl⟩ : syracuseStep 2308723 = 3463085) B3463085
theorem B5194637 : Blo 2307435 5194637 := bbase (se 3 (by rfl) ⟨973994, by rfl⟩ : syracuseStep 5194637 = 1947989) (by norm_num)
theorem B3463091 : Blo 2307435 3463091 := bstep (se 1 (by rfl) ⟨2597318, by rfl⟩ : syracuseStep 3463091 = 5194637) B5194637
theorem B2308727 : Blo 2307435 2308727 := bstep (se 1 (by rfl) ⟨1731545, by rfl⟩ : syracuseStep 2308727 = 3463091) B3463091
theorem B2921989 : Blo 2307435 2921989 := bbase (se 4 (by rfl) ⟨273936, by rfl⟩ : syracuseStep 2921989 = 547873) (by norm_num)
theorem B3895985 : Blo 2307435 3895985 := bstep (se 2 (by rfl) ⟨1460994, by rfl⟩ : syracuseStep 3895985 = 2921989) B2921989
theorem B2597323 : Blo 2307435 2597323 := bstep (se 1 (by rfl) ⟨1947992, by rfl⟩ : syracuseStep 2597323 = 3895985) B3895985
theorem B3463097 : Blo 2307435 3463097 := bstep (se 2 (by rfl) ⟨1298661, by rfl⟩ : syracuseStep 3463097 = 2597323) B2597323
theorem B2308731 : Blo 2307435 2308731 := bstep (se 1 (by rfl) ⟨1731548, by rfl⟩ : syracuseStep 2308731 = 3463097) B3463097
theorem B2632765 : Blo 2307435 2632765 := bbase (se 3 (by rfl) ⟨493643, by rfl⟩ : syracuseStep 2632765 = 987287) (by norm_num)
theorem B3510353 : Blo 2307435 3510353 := bstep (se 2 (by rfl) ⟨1316382, by rfl⟩ : syracuseStep 3510353 = 2632765) B2632765
theorem B2340235 : Blo 2307435 2340235 := bstep (se 1 (by rfl) ⟨1755176, by rfl⟩ : syracuseStep 2340235 = 3510353) B3510353
theorem B12481253 : Blo 2307435 12481253 := bstep (se 4 (by rfl) ⟨1170117, by rfl⟩ : syracuseStep 12481253 = 2340235) B2340235
theorem B8320835 : Blo 2307435 8320835 := bstep (se 1 (by rfl) ⟨6240626, by rfl⟩ : syracuseStep 8320835 = 12481253) B12481253
theorem B5547223 : Blo 2307435 5547223 := bstep (se 1 (by rfl) ⟨4160417, by rfl⟩ : syracuseStep 5547223 = 8320835) B8320835
theorem B29585189 : Blo 2307435 29585189 := bstep (se 4 (by rfl) ⟨2773611, by rfl⟩ : syracuseStep 29585189 = 5547223) B5547223
theorem B19723459 : Blo 2307435 19723459 := bstep (se 1 (by rfl) ⟨14792594, by rfl⟩ : syracuseStep 19723459 = 29585189) B29585189
theorem B26297945 : Blo 2307435 26297945 := bstep (se 2 (by rfl) ⟨9861729, by rfl⟩ : syracuseStep 26297945 = 19723459) B19723459
theorem B17531963 : Blo 2307435 17531963 := bstep (se 1 (by rfl) ⟨13148972, by rfl⟩ : syracuseStep 17531963 = 26297945) B26297945
theorem B11687975 : Blo 2307435 11687975 := bstep (se 1 (by rfl) ⟨8765981, by rfl⟩ : syracuseStep 11687975 = 17531963) B17531963
theorem B7791983 : Blo 2307435 7791983 := bstep (se 1 (by rfl) ⟨5843987, by rfl⟩ : syracuseStep 7791983 = 11687975) B11687975
theorem B5194655 : Blo 2307435 5194655 := bstep (se 1 (by rfl) ⟨3895991, by rfl⟩ : syracuseStep 5194655 = 7791983) B7791983
theorem B3463103 : Blo 2307435 3463103 := bstep (se 1 (by rfl) ⟨2597327, by rfl⟩ : syracuseStep 3463103 = 5194655) B5194655
theorem B2308735 : Blo 2307435 2308735 := bstep (se 1 (by rfl) ⟨1731551, by rfl⟩ : syracuseStep 2308735 = 3463103) B3463103
theorem B3463109 : Blo 2307435 3463109 := bbase (se 4 (by rfl) ⟨324666, by rfl⟩ : syracuseStep 3463109 = 649333) (by norm_num)
theorem B2308739 : Blo 2307435 2308739 := bstep (se 1 (by rfl) ⟨1731554, by rfl⟩ : syracuseStep 2308739 = 3463109) B3463109
theorem B3896005 : Blo 2307435 3896005 := bbase (se 4 (by rfl) ⟨365250, by rfl⟩ : syracuseStep 3896005 = 730501) (by norm_num)
theorem B5194673 : Blo 2307435 5194673 := bstep (se 2 (by rfl) ⟨1948002, by rfl⟩ : syracuseStep 5194673 = 3896005) B3896005
theorem B3463115 : Blo 2307435 3463115 := bstep (se 1 (by rfl) ⟨2597336, by rfl⟩ : syracuseStep 3463115 = 5194673) B5194673
theorem B2308743 : Blo 2307435 2308743 := bstep (se 1 (by rfl) ⟨1731557, by rfl⟩ : syracuseStep 2308743 = 3463115) B3463115
theorem B2597341 : Blo 2307435 2597341 := bbase (se 3 (by rfl) ⟨487001, by rfl⟩ : syracuseStep 2597341 = 974003) (by norm_num)
theorem B3463121 : Blo 2307435 3463121 := bstep (se 2 (by rfl) ⟨1298670, by rfl⟩ : syracuseStep 3463121 = 2597341) B2597341
theorem B2308747 : Blo 2307435 2308747 := bstep (se 1 (by rfl) ⟨1731560, by rfl⟩ : syracuseStep 2308747 = 3463121) B3463121
theorem B7792037 : Blo 2307435 7792037 := bbase (se 4 (by rfl) ⟨730503, by rfl⟩ : syracuseStep 7792037 = 1461007) (by norm_num)
theorem B5194691 : Blo 2307435 5194691 := bstep (se 1 (by rfl) ⟨3896018, by rfl⟩ : syracuseStep 5194691 = 7792037) B7792037
theorem B3463127 : Blo 2307435 3463127 := bstep (se 1 (by rfl) ⟨2597345, by rfl⟩ : syracuseStep 3463127 = 5194691) B5194691
theorem B2308751 : Blo 2307435 2308751 := bstep (se 1 (by rfl) ⟨1731563, by rfl⟩ : syracuseStep 2308751 = 3463127) B3463127
theorem B3463133 : Blo 2307435 3463133 := bbase (se 3 (by rfl) ⟨649337, by rfl⟩ : syracuseStep 3463133 = 1298675) (by norm_num)
theorem B2308755 : Blo 2307435 2308755 := bstep (se 1 (by rfl) ⟨1731566, by rfl⟩ : syracuseStep 2308755 = 3463133) B3463133
theorem B5194709 : Blo 2307435 5194709 := bbase (se 7 (by rfl) ⟨60875, by rfl⟩ : syracuseStep 5194709 = 121751) (by norm_num)
theorem B3463139 : Blo 2307435 3463139 := bstep (se 1 (by rfl) ⟨2597354, by rfl⟩ : syracuseStep 3463139 = 5194709) B5194709
theorem B2308759 : Blo 2307435 2308759 := bstep (se 1 (by rfl) ⟨1731569, by rfl⟩ : syracuseStep 2308759 = 3463139) B3463139
theorem B96073813 : Blo 2307435 96073813 := bbase (se 8 (by rfl) ⟨562932, by rfl⟩ : syracuseStep 96073813 = 1125865) (by norm_num)
theorem B128098417 : Blo 2307435 128098417 := bstep (se 2 (by rfl) ⟨48036906, by rfl⟩ : syracuseStep 128098417 = 96073813) B96073813
theorem B170797889 : Blo 2307435 170797889 := bstep (se 2 (by rfl) ⟨64049208, by rfl⟩ : syracuseStep 170797889 = 128098417) B128098417
theorem B113865259 : Blo 2307435 113865259 := bstep (se 1 (by rfl) ⟨85398944, by rfl⟩ : syracuseStep 113865259 = 170797889) B170797889
theorem B151820345 : Blo 2307435 151820345 := bstep (se 2 (by rfl) ⟨56932629, by rfl⟩ : syracuseStep 151820345 = 113865259) B113865259
theorem B101213563 : Blo 2307435 101213563 := bstep (se 1 (by rfl) ⟨75910172, by rfl⟩ : syracuseStep 101213563 = 151820345) B151820345
theorem B134951417 : Blo 2307435 134951417 := bstep (se 2 (by rfl) ⟨50606781, by rfl⟩ : syracuseStep 134951417 = 101213563) B101213563
theorem B89967611 : Blo 2307435 89967611 := bstep (se 1 (by rfl) ⟨67475708, by rfl⟩ : syracuseStep 89967611 = 134951417) B134951417
theorem B59978407 : Blo 2307435 59978407 := bstep (se 1 (by rfl) ⟨44983805, by rfl⟩ : syracuseStep 59978407 = 89967611) B89967611
theorem B79971209 : Blo 2307435 79971209 := bstep (se 2 (by rfl) ⟨29989203, by rfl⟩ : syracuseStep 79971209 = 59978407) B59978407
theorem B53314139 : Blo 2307435 53314139 := bstep (se 1 (by rfl) ⟨39985604, by rfl⟩ : syracuseStep 53314139 = 79971209) B79971209
theorem B35542759 : Blo 2307435 35542759 := bstep (se 1 (by rfl) ⟨26657069, by rfl⟩ : syracuseStep 35542759 = 53314139) B53314139
theorem B47390345 : Blo 2307435 47390345 := bstep (se 2 (by rfl) ⟨17771379, by rfl⟩ : syracuseStep 47390345 = 35542759) B35542759
theorem B31593563 : Blo 2307435 31593563 := bstep (se 1 (by rfl) ⟨23695172, by rfl⟩ : syracuseStep 31593563 = 47390345) B47390345
theorem B21062375 : Blo 2307435 21062375 := bstep (se 1 (by rfl) ⟨15796781, by rfl⟩ : syracuseStep 21062375 = 31593563) B31593563
theorem B14041583 : Blo 2307435 14041583 := bstep (se 1 (by rfl) ⟨10531187, by rfl⟩ : syracuseStep 14041583 = 21062375) B21062375
theorem B9361055 : Blo 2307435 9361055 := bstep (se 1 (by rfl) ⟨7020791, by rfl⟩ : syracuseStep 9361055 = 14041583) B14041583
theorem B24962813 : Blo 2307435 24962813 := bstep (se 3 (by rfl) ⟨4680527, by rfl⟩ : syracuseStep 24962813 = 9361055) B9361055
theorem B16641875 : Blo 2307435 16641875 := bstep (se 1 (by rfl) ⟨12481406, by rfl⟩ : syracuseStep 16641875 = 24962813) B24962813
theorem B11094583 : Blo 2307435 11094583 := bstep (se 1 (by rfl) ⟨8320937, by rfl⟩ : syracuseStep 11094583 = 16641875) B16641875
theorem B14792777 : Blo 2307435 14792777 := bstep (se 2 (by rfl) ⟨5547291, by rfl⟩ : syracuseStep 14792777 = 11094583) B11094583
theorem B9861851 : Blo 2307435 9861851 := bstep (se 1 (by rfl) ⟨7396388, by rfl⟩ : syracuseStep 9861851 = 14792777) B14792777
theorem B6574567 : Blo 2307435 6574567 := bstep (se 1 (by rfl) ⟨4930925, by rfl⟩ : syracuseStep 6574567 = 9861851) B9861851
theorem B8766089 : Blo 2307435 8766089 := bstep (se 2 (by rfl) ⟨3287283, by rfl⟩ : syracuseStep 8766089 = 6574567) B6574567
theorem B5844059 : Blo 2307435 5844059 := bstep (se 1 (by rfl) ⟨4383044, by rfl⟩ : syracuseStep 5844059 = 8766089) B8766089
theorem B3896039 : Blo 2307435 3896039 := bstep (se 1 (by rfl) ⟨2922029, by rfl⟩ : syracuseStep 3896039 = 5844059) B5844059
theorem B2597359 : Blo 2307435 2597359 := bstep (se 1 (by rfl) ⟨1948019, by rfl⟩ : syracuseStep 2597359 = 3896039) B3896039
theorem B3463145 : Blo 2307435 3463145 := bstep (se 2 (by rfl) ⟨1298679, by rfl⟩ : syracuseStep 3463145 = 2597359) B2597359
theorem B2308763 : Blo 2307435 2308763 := bstep (se 1 (by rfl) ⟨1731572, by rfl⟩ : syracuseStep 2308763 = 3463145) B3463145
theorem B19723733 : Blo 2307435 19723733 := bbase (se 7 (by rfl) ⟨231137, by rfl⟩ : syracuseStep 19723733 = 462275) (by norm_num)
theorem B13149155 : Blo 2307435 13149155 := bstep (se 1 (by rfl) ⟨9861866, by rfl⟩ : syracuseStep 13149155 = 19723733) B19723733
theorem B8766103 : Blo 2307435 8766103 := bstep (se 1 (by rfl) ⟨6574577, by rfl⟩ : syracuseStep 8766103 = 13149155) B13149155
theorem B11688137 : Blo 2307435 11688137 := bstep (se 2 (by rfl) ⟨4383051, by rfl⟩ : syracuseStep 11688137 = 8766103) B8766103
theorem B7792091 : Blo 2307435 7792091 := bstep (se 1 (by rfl) ⟨5844068, by rfl⟩ : syracuseStep 7792091 = 11688137) B11688137
theorem B5194727 : Blo 2307435 5194727 := bstep (se 1 (by rfl) ⟨3896045, by rfl⟩ : syracuseStep 5194727 = 7792091) B7792091
theorem B3463151 : Blo 2307435 3463151 := bstep (se 1 (by rfl) ⟨2597363, by rfl⟩ : syracuseStep 3463151 = 5194727) B5194727
theorem B2308767 : Blo 2307435 2308767 := bstep (se 1 (by rfl) ⟨1731575, by rfl⟩ : syracuseStep 2308767 = 3463151) B3463151
theorem B3463157 : Blo 2307435 3463157 := bbase (se 5 (by rfl) ⟨162335, by rfl⟩ : syracuseStep 3463157 = 324671) (by norm_num)
theorem B2308771 : Blo 2307435 2308771 := bstep (se 1 (by rfl) ⟨1731578, by rfl⟩ : syracuseStep 2308771 = 3463157) B3463157
theorem B8320981 : Blo 2307435 8320981 := bbase (se 7 (by rfl) ⟨97511, by rfl⟩ : syracuseStep 8320981 = 195023) (by norm_num)
theorem B11094641 : Blo 2307435 11094641 := bstep (se 2 (by rfl) ⟨4160490, by rfl⟩ : syracuseStep 11094641 = 8320981) B8320981
theorem B7396427 : Blo 2307435 7396427 := bstep (se 1 (by rfl) ⟨5547320, by rfl⟩ : syracuseStep 7396427 = 11094641) B11094641
theorem B4930951 : Blo 2307435 4930951 := bstep (se 1 (by rfl) ⟨3698213, by rfl⟩ : syracuseStep 4930951 = 7396427) B7396427
theorem B6574601 : Blo 2307435 6574601 := bstep (se 2 (by rfl) ⟨2465475, by rfl⟩ : syracuseStep 6574601 = 4930951) B4930951
theorem B4383067 : Blo 2307435 4383067 := bstep (se 1 (by rfl) ⟨3287300, by rfl⟩ : syracuseStep 4383067 = 6574601) B6574601
theorem B5844089 : Blo 2307435 5844089 := bstep (se 2 (by rfl) ⟨2191533, by rfl⟩ : syracuseStep 5844089 = 4383067) B4383067
theorem B3896059 : Blo 2307435 3896059 := bstep (se 1 (by rfl) ⟨2922044, by rfl⟩ : syracuseStep 3896059 = 5844089) B5844089
theorem B5194745 : Blo 2307435 5194745 := bstep (se 2 (by rfl) ⟨1948029, by rfl⟩ : syracuseStep 5194745 = 3896059) B3896059
theorem B3463163 : Blo 2307435 3463163 := bstep (se 1 (by rfl) ⟨2597372, by rfl⟩ : syracuseStep 3463163 = 5194745) B5194745
theorem B2308775 : Blo 2307435 2308775 := bstep (se 1 (by rfl) ⟨1731581, by rfl⟩ : syracuseStep 2308775 = 3463163) B3463163
theorem B2597377 : Blo 2307435 2597377 := bbase (se 2 (by rfl) ⟨974016, by rfl⟩ : syracuseStep 2597377 = 1948033) (by norm_num)
theorem B3463169 : Blo 2307435 3463169 := bstep (se 2 (by rfl) ⟨1298688, by rfl⟩ : syracuseStep 3463169 = 2597377) B2597377
theorem B2308779 : Blo 2307435 2308779 := bstep (se 1 (by rfl) ⟨1731584, by rfl⟩ : syracuseStep 2308779 = 3463169) B3463169
theorem B5844109 : Blo 2307435 5844109 := bbase (se 3 (by rfl) ⟨1095770, by rfl⟩ : syracuseStep 5844109 = 2191541) (by norm_num)
theorem B7792145 : Blo 2307435 7792145 := bstep (se 2 (by rfl) ⟨2922054, by rfl⟩ : syracuseStep 7792145 = 5844109) B5844109
theorem B5194763 : Blo 2307435 5194763 := bstep (se 1 (by rfl) ⟨3896072, by rfl⟩ : syracuseStep 5194763 = 7792145) B7792145
theorem B3463175 : Blo 2307435 3463175 := bstep (se 1 (by rfl) ⟨2597381, by rfl⟩ : syracuseStep 3463175 = 5194763) B5194763
theorem B2308783 : Blo 2307435 2308783 := bstep (se 1 (by rfl) ⟨1731587, by rfl⟩ : syracuseStep 2308783 = 3463175) B3463175
theorem B3463181 : Blo 2307435 3463181 := bbase (se 3 (by rfl) ⟨649346, by rfl⟩ : syracuseStep 3463181 = 1298693) (by norm_num)
theorem B2308787 : Blo 2307435 2308787 := bstep (se 1 (by rfl) ⟨1731590, by rfl⟩ : syracuseStep 2308787 = 3463181) B3463181
theorem B5194781 : Blo 2307435 5194781 := bbase (se 3 (by rfl) ⟨974021, by rfl⟩ : syracuseStep 5194781 = 1948043) (by norm_num)
theorem B3463187 : Blo 2307435 3463187 := bstep (se 1 (by rfl) ⟨2597390, by rfl⟩ : syracuseStep 3463187 = 5194781) B5194781
theorem B2308791 : Blo 2307435 2308791 := bstep (se 1 (by rfl) ⟨1731593, by rfl⟩ : syracuseStep 2308791 = 3463187) B3463187
theorem B3896093 : Blo 2307435 3896093 := bbase (se 3 (by rfl) ⟨730517, by rfl⟩ : syracuseStep 3896093 = 1461035) (by norm_num)
theorem B2597395 : Blo 2307435 2597395 := bstep (se 1 (by rfl) ⟨1948046, by rfl⟩ : syracuseStep 2597395 = 3896093) B3896093
theorem B3463193 : Blo 2307435 3463193 := bstep (se 2 (by rfl) ⟨1298697, by rfl⟩ : syracuseStep 3463193 = 2597395) B2597395
theorem B2308795 : Blo 2307435 2308795 := bstep (se 1 (by rfl) ⟨1731596, by rfl⟩ : syracuseStep 2308795 = 3463193) B3463193
theorem B4160533 : Blo 2307435 4160533 := bbase (se 6 (by rfl) ⟨97512, by rfl⟩ : syracuseStep 4160533 = 195025) (by norm_num)
theorem B5547377 : Blo 2307435 5547377 := bstep (se 2 (by rfl) ⟨2080266, by rfl⟩ : syracuseStep 5547377 = 4160533) B4160533
theorem B14793005 : Blo 2307435 14793005 := bstep (se 3 (by rfl) ⟨2773688, by rfl⟩ : syracuseStep 14793005 = 5547377) B5547377
theorem B9862003 : Blo 2307435 9862003 := bstep (se 1 (by rfl) ⟨7396502, by rfl⟩ : syracuseStep 9862003 = 14793005) B14793005
theorem B13149337 : Blo 2307435 13149337 := bstep (se 2 (by rfl) ⟨4931001, by rfl⟩ : syracuseStep 13149337 = 9862003) B9862003
theorem B17532449 : Blo 2307435 17532449 := bstep (se 2 (by rfl) ⟨6574668, by rfl⟩ : syracuseStep 17532449 = 13149337) B13149337
theorem B11688299 : Blo 2307435 11688299 := bstep (se 1 (by rfl) ⟨8766224, by rfl⟩ : syracuseStep 11688299 = 17532449) B17532449
theorem B7792199 : Blo 2307435 7792199 := bstep (se 1 (by rfl) ⟨5844149, by rfl⟩ : syracuseStep 7792199 = 11688299) B11688299
theorem B5194799 : Blo 2307435 5194799 := bstep (se 1 (by rfl) ⟨3896099, by rfl⟩ : syracuseStep 5194799 = 7792199) B7792199
theorem B3463199 : Blo 2307435 3463199 := bstep (se 1 (by rfl) ⟨2597399, by rfl⟩ : syracuseStep 3463199 = 5194799) B5194799
theorem B2308799 : Blo 2307435 2308799 := bstep (se 1 (by rfl) ⟨1731599, by rfl⟩ : syracuseStep 2308799 = 3463199) B3463199
theorem B3463205 : Blo 2307435 3463205 := bbase (se 4 (by rfl) ⟨324675, by rfl⟩ : syracuseStep 3463205 = 649351) (by norm_num)
theorem B2308803 : Blo 2307435 2308803 := bstep (se 1 (by rfl) ⟨1731602, by rfl⟩ : syracuseStep 2308803 = 3463205) B3463205
theorem B2922085 : Blo 2307435 2922085 := bbase (se 4 (by rfl) ⟨273945, by rfl⟩ : syracuseStep 2922085 = 547891) (by norm_num)
theorem B3896113 : Blo 2307435 3896113 := bstep (se 2 (by rfl) ⟨1461042, by rfl⟩ : syracuseStep 3896113 = 2922085) B2922085
theorem B5194817 : Blo 2307435 5194817 := bstep (se 2 (by rfl) ⟨1948056, by rfl⟩ : syracuseStep 5194817 = 3896113) B3896113
theorem B3463211 : Blo 2307435 3463211 := bstep (se 1 (by rfl) ⟨2597408, by rfl⟩ : syracuseStep 3463211 = 5194817) B5194817
theorem B2308807 : Blo 2307435 2308807 := bstep (se 1 (by rfl) ⟨1731605, by rfl⟩ : syracuseStep 2308807 = 3463211) B3463211
theorem B2597413 : Blo 2307435 2597413 := bbase (se 4 (by rfl) ⟨243507, by rfl⟩ : syracuseStep 2597413 = 487015) (by norm_num)
theorem B3463217 : Blo 2307435 3463217 := bstep (se 2 (by rfl) ⟨1298706, by rfl⟩ : syracuseStep 3463217 = 2597413) B2597413
theorem B2308811 : Blo 2307435 2308811 := bstep (se 1 (by rfl) ⟨1731608, by rfl⟩ : syracuseStep 2308811 = 3463217) B3463217
theorem B8321125 : Blo 2307435 8321125 := bbase (se 4 (by rfl) ⟨780105, by rfl⟩ : syracuseStep 8321125 = 1560211) (by norm_num)
theorem B11094833 : Blo 2307435 11094833 := bstep (se 2 (by rfl) ⟨4160562, by rfl⟩ : syracuseStep 11094833 = 8321125) B8321125
theorem B7396555 : Blo 2307435 7396555 := bstep (se 1 (by rfl) ⟨5547416, by rfl⟩ : syracuseStep 7396555 = 11094833) B11094833
theorem B9862073 : Blo 2307435 9862073 := bstep (se 2 (by rfl) ⟨3698277, by rfl⟩ : syracuseStep 9862073 = 7396555) B7396555
theorem B6574715 : Blo 2307435 6574715 := bstep (se 1 (by rfl) ⟨4931036, by rfl⟩ : syracuseStep 6574715 = 9862073) B9862073
theorem B4383143 : Blo 2307435 4383143 := bstep (se 1 (by rfl) ⟨3287357, by rfl⟩ : syracuseStep 4383143 = 6574715) B6574715
theorem B2922095 : Blo 2307435 2922095 := bstep (se 1 (by rfl) ⟨2191571, by rfl⟩ : syracuseStep 2922095 = 4383143) B4383143
theorem B7792253 : Blo 2307435 7792253 := bstep (se 3 (by rfl) ⟨1461047, by rfl⟩ : syracuseStep 7792253 = 2922095) B2922095
theorem B5194835 : Blo 2307435 5194835 := bstep (se 1 (by rfl) ⟨3896126, by rfl⟩ : syracuseStep 5194835 = 7792253) B7792253
theorem B3463223 : Blo 2307435 3463223 := bstep (se 1 (by rfl) ⟨2597417, by rfl⟩ : syracuseStep 3463223 = 5194835) B5194835
theorem B2308815 : Blo 2307435 2308815 := bstep (se 1 (by rfl) ⟨1731611, by rfl⟩ : syracuseStep 2308815 = 3463223) B3463223
theorem B3463229 : Blo 2307435 3463229 := bbase (se 3 (by rfl) ⟨649355, by rfl⟩ : syracuseStep 3463229 = 1298711) (by norm_num)
theorem B2308819 : Blo 2307435 2308819 := bstep (se 1 (by rfl) ⟨1731614, by rfl⟩ : syracuseStep 2308819 = 3463229) B3463229
theorem B5194853 : Blo 2307435 5194853 := bbase (se 4 (by rfl) ⟨487017, by rfl⟩ : syracuseStep 5194853 = 974035) (by norm_num)
theorem B3463235 : Blo 2307435 3463235 := bstep (se 1 (by rfl) ⟨2597426, by rfl⟩ : syracuseStep 3463235 = 5194853) B5194853
theorem B2308823 : Blo 2307435 2308823 := bstep (se 1 (by rfl) ⟨1731617, by rfl⟩ : syracuseStep 2308823 = 3463235) B3463235
theorem B5844221 : Blo 2307435 5844221 := bbase (se 3 (by rfl) ⟨1095791, by rfl⟩ : syracuseStep 5844221 = 2191583) (by norm_num)
theorem B3896147 : Blo 2307435 3896147 := bstep (se 1 (by rfl) ⟨2922110, by rfl⟩ : syracuseStep 3896147 = 5844221) B5844221
theorem B2597431 : Blo 2307435 2597431 := bstep (se 1 (by rfl) ⟨1948073, by rfl⟩ : syracuseStep 2597431 = 3896147) B3896147
theorem B3463241 : Blo 2307435 3463241 := bstep (se 2 (by rfl) ⟨1298715, by rfl⟩ : syracuseStep 3463241 = 2597431) B2597431
theorem B2308827 : Blo 2307435 2308827 := bstep (se 1 (by rfl) ⟨1731620, by rfl⟩ : syracuseStep 2308827 = 3463241) B3463241
theorem B4383173 : Blo 2307435 4383173 := bbase (se 4 (by rfl) ⟨410922, by rfl⟩ : syracuseStep 4383173 = 821845) (by norm_num)
theorem B11688461 : Blo 2307435 11688461 := bstep (se 3 (by rfl) ⟨2191586, by rfl⟩ : syracuseStep 11688461 = 4383173) B4383173
theorem B7792307 : Blo 2307435 7792307 := bstep (se 1 (by rfl) ⟨5844230, by rfl⟩ : syracuseStep 7792307 = 11688461) B11688461
theorem B5194871 : Blo 2307435 5194871 := bstep (se 1 (by rfl) ⟨3896153, by rfl⟩ : syracuseStep 5194871 = 7792307) B7792307
theorem B3463247 : Blo 2307435 3463247 := bstep (se 1 (by rfl) ⟨2597435, by rfl⟩ : syracuseStep 3463247 = 5194871) B5194871
theorem B2308831 : Blo 2307435 2308831 := bstep (se 1 (by rfl) ⟨1731623, by rfl⟩ : syracuseStep 2308831 = 3463247) B3463247
theorem B3463253 : Blo 2307435 3463253 := bbase (se 8 (by rfl) ⟨20292, by rfl⟩ : syracuseStep 3463253 = 40585) (by norm_num)
theorem B2308835 : Blo 2307435 2308835 := bstep (se 1 (by rfl) ⟨1731626, by rfl⟩ : syracuseStep 2308835 = 3463253) B3463253
theorem B4998365 : Blo 2307435 4998365 := bbase (se 3 (by rfl) ⟨937193, by rfl⟩ : syracuseStep 4998365 = 1874387) (by norm_num)
theorem B3332243 : Blo 2307435 3332243 := bstep (se 1 (by rfl) ⟨2499182, by rfl⟩ : syracuseStep 3332243 = 4998365) B4998365
theorem B8885981 : Blo 2307435 8885981 := bstep (se 3 (by rfl) ⟨1666121, by rfl⟩ : syracuseStep 8885981 = 3332243) B3332243
theorem B23695949 : Blo 2307435 23695949 := bstep (se 3 (by rfl) ⟨4442990, by rfl⟩ : syracuseStep 23695949 = 8885981) B8885981
theorem B63189197 : Blo 2307435 63189197 := bstep (se 3 (by rfl) ⟨11847974, by rfl⟩ : syracuseStep 63189197 = 23695949) B23695949
theorem B42126131 : Blo 2307435 42126131 := bstep (se 1 (by rfl) ⟨31594598, by rfl⟩ : syracuseStep 42126131 = 63189197) B63189197
theorem B28084087 : Blo 2307435 28084087 := bstep (se 1 (by rfl) ⟨21063065, by rfl⟩ : syracuseStep 28084087 = 42126131) B42126131
theorem B37445449 : Blo 2307435 37445449 := bstep (se 2 (by rfl) ⟨14042043, by rfl⟩ : syracuseStep 37445449 = 28084087) B28084087
theorem B49927265 : Blo 2307435 49927265 := bstep (se 2 (by rfl) ⟨18722724, by rfl⟩ : syracuseStep 49927265 = 37445449) B37445449
theorem B33284843 : Blo 2307435 33284843 := bstep (se 1 (by rfl) ⟨24963632, by rfl⟩ : syracuseStep 33284843 = 49927265) B49927265
theorem B22189895 : Blo 2307435 22189895 := bstep (se 1 (by rfl) ⟨16642421, by rfl⟩ : syracuseStep 22189895 = 33284843) B33284843
theorem B14793263 : Blo 2307435 14793263 := bstep (se 1 (by rfl) ⟨11094947, by rfl⟩ : syracuseStep 14793263 = 22189895) B22189895
theorem B9862175 : Blo 2307435 9862175 := bstep (se 1 (by rfl) ⟨7396631, by rfl⟩ : syracuseStep 9862175 = 14793263) B14793263
theorem B6574783 : Blo 2307435 6574783 := bstep (se 1 (by rfl) ⟨4931087, by rfl⟩ : syracuseStep 6574783 = 9862175) B9862175
theorem B8766377 : Blo 2307435 8766377 := bstep (se 2 (by rfl) ⟨3287391, by rfl⟩ : syracuseStep 8766377 = 6574783) B6574783
theorem B5844251 : Blo 2307435 5844251 := bstep (se 1 (by rfl) ⟨4383188, by rfl⟩ : syracuseStep 5844251 = 8766377) B8766377
theorem B3896167 : Blo 2307435 3896167 := bstep (se 1 (by rfl) ⟨2922125, by rfl⟩ : syracuseStep 3896167 = 5844251) B5844251
theorem B5194889 : Blo 2307435 5194889 := bstep (se 2 (by rfl) ⟨1948083, by rfl⟩ : syracuseStep 5194889 = 3896167) B3896167
theorem B3463259 : Blo 2307435 3463259 := bstep (se 1 (by rfl) ⟨2597444, by rfl⟩ : syracuseStep 3463259 = 5194889) B5194889
theorem B2308839 : Blo 2307435 2308839 := bstep (se 1 (by rfl) ⟨1731629, by rfl⟩ : syracuseStep 2308839 = 3463259) B3463259
theorem B2597449 : Blo 2307435 2597449 := bbase (se 2 (by rfl) ⟨974043, by rfl⟩ : syracuseStep 2597449 = 1948087) (by norm_num)
theorem B3463265 : Blo 2307435 3463265 := bstep (se 2 (by rfl) ⟨1298724, by rfl⟩ : syracuseStep 3463265 = 2597449) B2597449
theorem B2308843 : Blo 2307435 2308843 := bstep (se 1 (by rfl) ⟨1731632, by rfl⟩ : syracuseStep 2308843 = 3463265) B3463265
theorem B5410453 : Blo 2307435 5410453 := bbase (se 6 (by rfl) ⟨126807, by rfl⟩ : syracuseStep 5410453 = 253615) (by norm_num)
theorem B7213937 : Blo 2307435 7213937 := bstep (se 2 (by rfl) ⟨2705226, by rfl⟩ : syracuseStep 7213937 = 5410453) B5410453
theorem B76948661 : Blo 2307435 76948661 := bstep (se 5 (by rfl) ⟨3606968, by rfl⟩ : syracuseStep 76948661 = 7213937) B7213937
theorem B205196429 : Blo 2307435 205196429 := bstep (se 3 (by rfl) ⟨38474330, by rfl⟩ : syracuseStep 205196429 = 76948661) B76948661
theorem B547190477 : Blo 2307435 547190477 := bstep (se 3 (by rfl) ⟨102598214, by rfl⟩ : syracuseStep 547190477 = 205196429) B205196429
theorem B364793651 : Blo 2307435 364793651 := bstep (se 1 (by rfl) ⟨273595238, by rfl⟩ : syracuseStep 364793651 = 547190477) B547190477
theorem B243195767 : Blo 2307435 243195767 := bstep (se 1 (by rfl) ⟨182396825, by rfl⟩ : syracuseStep 243195767 = 364793651) B364793651
theorem B162130511 : Blo 2307435 162130511 := bstep (se 1 (by rfl) ⟨121597883, by rfl⟩ : syracuseStep 162130511 = 243195767) B243195767
theorem B108087007 : Blo 2307435 108087007 := bstep (se 1 (by rfl) ⟨81065255, by rfl⟩ : syracuseStep 108087007 = 162130511) B162130511
theorem B144116009 : Blo 2307435 144116009 := bstep (se 2 (by rfl) ⟨54043503, by rfl⟩ : syracuseStep 144116009 = 108087007) B108087007
theorem B96077339 : Blo 2307435 96077339 := bstep (se 1 (by rfl) ⟨72058004, by rfl⟩ : syracuseStep 96077339 = 144116009) B144116009
theorem B64051559 : Blo 2307435 64051559 := bstep (se 1 (by rfl) ⟨48038669, by rfl⟩ : syracuseStep 64051559 = 96077339) B96077339
theorem B42701039 : Blo 2307435 42701039 := bstep (se 1 (by rfl) ⟨32025779, by rfl⟩ : syracuseStep 42701039 = 64051559) B64051559
theorem B28467359 : Blo 2307435 28467359 := bstep (se 1 (by rfl) ⟨21350519, by rfl⟩ : syracuseStep 28467359 = 42701039) B42701039
theorem B18978239 : Blo 2307435 18978239 := bstep (se 1 (by rfl) ⟨14233679, by rfl⟩ : syracuseStep 18978239 = 28467359) B28467359
theorem B50608637 : Blo 2307435 50608637 := bstep (se 3 (by rfl) ⟨9489119, by rfl⟩ : syracuseStep 50608637 = 18978239) B18978239
theorem B33739091 : Blo 2307435 33739091 := bstep (se 1 (by rfl) ⟨25304318, by rfl⟩ : syracuseStep 33739091 = 50608637) B50608637
theorem B22492727 : Blo 2307435 22492727 := bstep (se 1 (by rfl) ⟨16869545, by rfl⟩ : syracuseStep 22492727 = 33739091) B33739091
theorem B14995151 : Blo 2307435 14995151 := bstep (se 1 (by rfl) ⟨11246363, by rfl⟩ : syracuseStep 14995151 = 22492727) B22492727
theorem B9996767 : Blo 2307435 9996767 := bstep (se 1 (by rfl) ⟨7497575, by rfl⟩ : syracuseStep 9996767 = 14995151) B14995151
theorem B6664511 : Blo 2307435 6664511 := bstep (se 1 (by rfl) ⟨4998383, by rfl⟩ : syracuseStep 6664511 = 9996767) B9996767
theorem B4443007 : Blo 2307435 4443007 := bstep (se 1 (by rfl) ⟨3332255, by rfl⟩ : syracuseStep 4443007 = 6664511) B6664511
theorem B5924009 : Blo 2307435 5924009 := bstep (se 2 (by rfl) ⟨2221503, by rfl⟩ : syracuseStep 5924009 = 4443007) B4443007
theorem B3949339 : Blo 2307435 3949339 := bstep (se 1 (by rfl) ⟨2962004, by rfl⟩ : syracuseStep 3949339 = 5924009) B5924009
theorem B5265785 : Blo 2307435 5265785 := bstep (se 2 (by rfl) ⟨1974669, by rfl⟩ : syracuseStep 5265785 = 3949339) B3949339
theorem B3510523 : Blo 2307435 3510523 := bstep (se 1 (by rfl) ⟨2632892, by rfl⟩ : syracuseStep 3510523 = 5265785) B5265785
theorem B18722789 : Blo 2307435 18722789 := bstep (se 4 (by rfl) ⟨1755261, by rfl⟩ : syracuseStep 18722789 = 3510523) B3510523
theorem B12481859 : Blo 2307435 12481859 := bstep (se 1 (by rfl) ⟨9361394, by rfl⟩ : syracuseStep 12481859 = 18722789) B18722789
theorem B8321239 : Blo 2307435 8321239 := bstep (se 1 (by rfl) ⟨6240929, by rfl⟩ : syracuseStep 8321239 = 12481859) B12481859
theorem B11094985 : Blo 2307435 11094985 := bstep (se 2 (by rfl) ⟨4160619, by rfl⟩ : syracuseStep 11094985 = 8321239) B8321239
theorem B14793313 : Blo 2307435 14793313 := bstep (se 2 (by rfl) ⟨5547492, by rfl⟩ : syracuseStep 14793313 = 11094985) B11094985
theorem B19724417 : Blo 2307435 19724417 := bstep (se 2 (by rfl) ⟨7396656, by rfl⟩ : syracuseStep 19724417 = 14793313) B14793313
theorem B13149611 : Blo 2307435 13149611 := bstep (se 1 (by rfl) ⟨9862208, by rfl⟩ : syracuseStep 13149611 = 19724417) B19724417
theorem B8766407 : Blo 2307435 8766407 := bstep (se 1 (by rfl) ⟨6574805, by rfl⟩ : syracuseStep 8766407 = 13149611) B13149611
theorem B5844271 : Blo 2307435 5844271 := bstep (se 1 (by rfl) ⟨4383203, by rfl⟩ : syracuseStep 5844271 = 8766407) B8766407
theorem B7792361 : Blo 2307435 7792361 := bstep (se 2 (by rfl) ⟨2922135, by rfl⟩ : syracuseStep 7792361 = 5844271) B5844271
theorem B5194907 : Blo 2307435 5194907 := bstep (se 1 (by rfl) ⟨3896180, by rfl⟩ : syracuseStep 5194907 = 7792361) B7792361
theorem B3463271 : Blo 2307435 3463271 := bstep (se 1 (by rfl) ⟨2597453, by rfl⟩ : syracuseStep 3463271 = 5194907) B5194907
theorem B2308847 : Blo 2307435 2308847 := bstep (se 1 (by rfl) ⟨1731635, by rfl⟩ : syracuseStep 2308847 = 3463271) B3463271
theorem B3463277 : Blo 2307435 3463277 := bbase (se 3 (by rfl) ⟨649364, by rfl⟩ : syracuseStep 3463277 = 1298729) (by norm_num)
theorem B2308851 : Blo 2307435 2308851 := bstep (se 1 (by rfl) ⟨1731638, by rfl⟩ : syracuseStep 2308851 = 3463277) B3463277
theorem B5194925 : Blo 2307435 5194925 := bbase (se 3 (by rfl) ⟨974048, by rfl⟩ : syracuseStep 5194925 = 1948097) (by norm_num)
theorem B3463283 : Blo 2307435 3463283 := bstep (se 1 (by rfl) ⟨2597462, by rfl⟩ : syracuseStep 3463283 = 5194925) B5194925
theorem B2308855 : Blo 2307435 2308855 := bstep (se 1 (by rfl) ⟨1731641, by rfl⟩ : syracuseStep 2308855 = 3463283) B3463283
theorem B8321285 : Blo 2307435 8321285 := bbase (se 4 (by rfl) ⟨780120, by rfl⟩ : syracuseStep 8321285 = 1560241) (by norm_num)
theorem B5547523 : Blo 2307435 5547523 := bstep (se 1 (by rfl) ⟨4160642, by rfl⟩ : syracuseStep 5547523 = 8321285) B8321285
theorem B7396697 : Blo 2307435 7396697 := bstep (se 2 (by rfl) ⟨2773761, by rfl⟩ : syracuseStep 7396697 = 5547523) B5547523
theorem B4931131 : Blo 2307435 4931131 := bstep (se 1 (by rfl) ⟨3698348, by rfl⟩ : syracuseStep 4931131 = 7396697) B7396697
theorem B6574841 : Blo 2307435 6574841 := bstep (se 2 (by rfl) ⟨2465565, by rfl⟩ : syracuseStep 6574841 = 4931131) B4931131
theorem B4383227 : Blo 2307435 4383227 := bstep (se 1 (by rfl) ⟨3287420, by rfl⟩ : syracuseStep 4383227 = 6574841) B6574841
theorem B2922151 : Blo 2307435 2922151 := bstep (se 1 (by rfl) ⟨2191613, by rfl⟩ : syracuseStep 2922151 = 4383227) B4383227
theorem B3896201 : Blo 2307435 3896201 := bstep (se 2 (by rfl) ⟨1461075, by rfl⟩ : syracuseStep 3896201 = 2922151) B2922151
theorem B2597467 : Blo 2307435 2597467 := bstep (se 1 (by rfl) ⟨1948100, by rfl⟩ : syracuseStep 2597467 = 3896201) B3896201
theorem B3463289 : Blo 2307435 3463289 := bstep (se 2 (by rfl) ⟨1298733, by rfl⟩ : syracuseStep 3463289 = 2597467) B2597467
theorem B2308859 : Blo 2307435 2308859 := bstep (se 1 (by rfl) ⟨1731644, by rfl⟩ : syracuseStep 2308859 = 3463289) B3463289
theorem B11095061 : Blo 2307435 11095061 := bbase (se 6 (by rfl) ⟨260040, by rfl⟩ : syracuseStep 11095061 = 520081) (by norm_num)
theorem B29586829 : Blo 2307435 29586829 := bstep (se 3 (by rfl) ⟨5547530, by rfl⟩ : syracuseStep 29586829 = 11095061) B11095061
theorem B39449105 : Blo 2307435 39449105 := bstep (se 2 (by rfl) ⟨14793414, by rfl⟩ : syracuseStep 39449105 = 29586829) B29586829
theorem B26299403 : Blo 2307435 26299403 := bstep (se 1 (by rfl) ⟨19724552, by rfl⟩ : syracuseStep 26299403 = 39449105) B39449105
theorem B17532935 : Blo 2307435 17532935 := bstep (se 1 (by rfl) ⟨13149701, by rfl⟩ : syracuseStep 17532935 = 26299403) B26299403
theorem B11688623 : Blo 2307435 11688623 := bstep (se 1 (by rfl) ⟨8766467, by rfl⟩ : syracuseStep 11688623 = 17532935) B17532935
theorem B7792415 : Blo 2307435 7792415 := bstep (se 1 (by rfl) ⟨5844311, by rfl⟩ : syracuseStep 7792415 = 11688623) B11688623
theorem B5194943 : Blo 2307435 5194943 := bstep (se 1 (by rfl) ⟨3896207, by rfl⟩ : syracuseStep 5194943 = 7792415) B7792415
theorem B3463295 : Blo 2307435 3463295 := bstep (se 1 (by rfl) ⟨2597471, by rfl⟩ : syracuseStep 3463295 = 5194943) B5194943
theorem B2308863 : Blo 2307435 2308863 := bstep (se 1 (by rfl) ⟨1731647, by rfl⟩ : syracuseStep 2308863 = 3463295) B3463295
theorem B3463301 : Blo 2307435 3463301 := bbase (se 4 (by rfl) ⟨324684, by rfl⟩ : syracuseStep 3463301 = 649369) (by norm_num)
theorem B2308867 : Blo 2307435 2308867 := bstep (se 1 (by rfl) ⟨1731650, by rfl⟩ : syracuseStep 2308867 = 3463301) B3463301
theorem B3896221 : Blo 2307435 3896221 := bbase (se 3 (by rfl) ⟨730541, by rfl⟩ : syracuseStep 3896221 = 1461083) (by norm_num)
theorem B5194961 : Blo 2307435 5194961 := bstep (se 2 (by rfl) ⟨1948110, by rfl⟩ : syracuseStep 5194961 = 3896221) B3896221
theorem B3463307 : Blo 2307435 3463307 := bstep (se 1 (by rfl) ⟨2597480, by rfl⟩ : syracuseStep 3463307 = 5194961) B5194961
theorem B2308871 : Blo 2307435 2308871 := bstep (se 1 (by rfl) ⟨1731653, by rfl⟩ : syracuseStep 2308871 = 3463307) B3463307
theorem B2597485 : Blo 2307435 2597485 := bbase (se 3 (by rfl) ⟨487028, by rfl⟩ : syracuseStep 2597485 = 974057) (by norm_num)
theorem B3463313 : Blo 2307435 3463313 := bstep (se 2 (by rfl) ⟨1298742, by rfl⟩ : syracuseStep 3463313 = 2597485) B2597485
theorem B2308875 : Blo 2307435 2308875 := bstep (se 1 (by rfl) ⟨1731656, by rfl⟩ : syracuseStep 2308875 = 3463313) B3463313
theorem B7792469 : Blo 2307435 7792469 := bbase (se 9 (by rfl) ⟨22829, by rfl⟩ : syracuseStep 7792469 = 45659) (by norm_num)
theorem B5194979 : Blo 2307435 5194979 := bstep (se 1 (by rfl) ⟨3896234, by rfl⟩ : syracuseStep 5194979 = 7792469) B7792469
theorem B3463319 : Blo 2307435 3463319 := bstep (se 1 (by rfl) ⟨2597489, by rfl⟩ : syracuseStep 3463319 = 5194979) B5194979
theorem B2308879 : Blo 2307435 2308879 := bstep (se 1 (by rfl) ⟨1731659, by rfl⟩ : syracuseStep 2308879 = 3463319) B3463319
theorem B3463325 : Blo 2307435 3463325 := bbase (se 3 (by rfl) ⟨649373, by rfl⟩ : syracuseStep 3463325 = 1298747) (by norm_num)
theorem B2308883 : Blo 2307435 2308883 := bstep (se 1 (by rfl) ⟨1731662, by rfl⟩ : syracuseStep 2308883 = 3463325) B3463325
theorem B5194997 : Blo 2307435 5194997 := bbase (se 5 (by rfl) ⟨243515, by rfl⟩ : syracuseStep 5194997 = 487031) (by norm_num)
theorem B3463331 : Blo 2307435 3463331 := bstep (se 1 (by rfl) ⟨2597498, by rfl⟩ : syracuseStep 3463331 = 5194997) B5194997
theorem B2308887 : Blo 2307435 2308887 := bstep (se 1 (by rfl) ⟨1731665, by rfl⟩ : syracuseStep 2308887 = 3463331) B3463331
theorem B37446293 : Blo 2307435 37446293 := bbase (se 6 (by rfl) ⟨877647, by rfl⟩ : syracuseStep 37446293 = 1755295) (by norm_num)
theorem B24964195 : Blo 2307435 24964195 := bstep (se 1 (by rfl) ⟨18723146, by rfl⟩ : syracuseStep 24964195 = 37446293) B37446293
theorem B33285593 : Blo 2307435 33285593 := bstep (se 2 (by rfl) ⟨12482097, by rfl⟩ : syracuseStep 33285593 = 24964195) B24964195
theorem B22190395 : Blo 2307435 22190395 := bstep (se 1 (by rfl) ⟨16642796, by rfl⟩ : syracuseStep 22190395 = 33285593) B33285593
theorem B29587193 : Blo 2307435 29587193 := bstep (se 2 (by rfl) ⟨11095197, by rfl⟩ : syracuseStep 29587193 = 22190395) B22190395
theorem B19724795 : Blo 2307435 19724795 := bstep (se 1 (by rfl) ⟨14793596, by rfl⟩ : syracuseStep 19724795 = 29587193) B29587193
theorem B13149863 : Blo 2307435 13149863 := bstep (se 1 (by rfl) ⟨9862397, by rfl⟩ : syracuseStep 13149863 = 19724795) B19724795
theorem B8766575 : Blo 2307435 8766575 := bstep (se 1 (by rfl) ⟨6574931, by rfl⟩ : syracuseStep 8766575 = 13149863) B13149863
theorem B5844383 : Blo 2307435 5844383 := bstep (se 1 (by rfl) ⟨4383287, by rfl⟩ : syracuseStep 5844383 = 8766575) B8766575
theorem B3896255 : Blo 2307435 3896255 := bstep (se 1 (by rfl) ⟨2922191, by rfl⟩ : syracuseStep 3896255 = 5844383) B5844383
theorem B2597503 : Blo 2307435 2597503 := bstep (se 1 (by rfl) ⟨1948127, by rfl⟩ : syracuseStep 2597503 = 3896255) B3896255
theorem B3463337 : Blo 2307435 3463337 := bstep (se 2 (by rfl) ⟨1298751, by rfl⟩ : syracuseStep 3463337 = 2597503) B2597503
theorem B2308891 : Blo 2307435 2308891 := bstep (se 1 (by rfl) ⟨1731668, by rfl⟩ : syracuseStep 2308891 = 3463337) B3463337
theorem B8321413 : Blo 2307435 8321413 := bbase (se 4 (by rfl) ⟨780132, by rfl⟩ : syracuseStep 8321413 = 1560265) (by norm_num)
theorem B11095217 : Blo 2307435 11095217 := bstep (se 2 (by rfl) ⟨4160706, by rfl⟩ : syracuseStep 11095217 = 8321413) B8321413
theorem B7396811 : Blo 2307435 7396811 := bstep (se 1 (by rfl) ⟨5547608, by rfl⟩ : syracuseStep 7396811 = 11095217) B11095217
theorem B4931207 : Blo 2307435 4931207 := bstep (se 1 (by rfl) ⟨3698405, by rfl⟩ : syracuseStep 4931207 = 7396811) B7396811
theorem B3287471 : Blo 2307435 3287471 := bstep (se 1 (by rfl) ⟨2465603, by rfl⟩ : syracuseStep 3287471 = 4931207) B4931207
theorem B8766589 : Blo 2307435 8766589 := bstep (se 3 (by rfl) ⟨1643735, by rfl⟩ : syracuseStep 8766589 = 3287471) B3287471
theorem B11688785 : Blo 2307435 11688785 := bstep (se 2 (by rfl) ⟨4383294, by rfl⟩ : syracuseStep 11688785 = 8766589) B8766589
theorem B7792523 : Blo 2307435 7792523 := bstep (se 1 (by rfl) ⟨5844392, by rfl⟩ : syracuseStep 7792523 = 11688785) B11688785
theorem B5195015 : Blo 2307435 5195015 := bstep (se 1 (by rfl) ⟨3896261, by rfl⟩ : syracuseStep 5195015 = 7792523) B7792523
theorem B3463343 : Blo 2307435 3463343 := bstep (se 1 (by rfl) ⟨2597507, by rfl⟩ : syracuseStep 3463343 = 5195015) B5195015
theorem B2308895 : Blo 2307435 2308895 := bstep (se 1 (by rfl) ⟨1731671, by rfl⟩ : syracuseStep 2308895 = 3463343) B3463343
theorem B3463349 : Blo 2307435 3463349 := bbase (se 5 (by rfl) ⟨162344, by rfl⟩ : syracuseStep 3463349 = 324689) (by norm_num)
theorem B2308899 : Blo 2307435 2308899 := bstep (se 1 (by rfl) ⟨1731674, by rfl⟩ : syracuseStep 2308899 = 3463349) B3463349
theorem B5844413 : Blo 2307435 5844413 := bbase (se 3 (by rfl) ⟨1095827, by rfl⟩ : syracuseStep 5844413 = 2191655) (by norm_num)
theorem B3896275 : Blo 2307435 3896275 := bstep (se 1 (by rfl) ⟨2922206, by rfl⟩ : syracuseStep 3896275 = 5844413) B5844413
theorem B5195033 : Blo 2307435 5195033 := bstep (se 2 (by rfl) ⟨1948137, by rfl⟩ : syracuseStep 5195033 = 3896275) B3896275
theorem B3463355 : Blo 2307435 3463355 := bstep (se 1 (by rfl) ⟨2597516, by rfl⟩ : syracuseStep 3463355 = 5195033) B5195033
theorem B2308903 : Blo 2307435 2308903 := bstep (se 1 (by rfl) ⟨1731677, by rfl⟩ : syracuseStep 2308903 = 3463355) B3463355
theorem B2597521 : Blo 2307435 2597521 := bbase (se 2 (by rfl) ⟨974070, by rfl⟩ : syracuseStep 2597521 = 1948141) (by norm_num)
theorem B3463361 : Blo 2307435 3463361 := bstep (se 2 (by rfl) ⟨1298760, by rfl⟩ : syracuseStep 3463361 = 2597521) B2597521
theorem B2308907 : Blo 2307435 2308907 := bstep (se 1 (by rfl) ⟨1731680, by rfl⟩ : syracuseStep 2308907 = 3463361) B3463361
theorem B4383325 : Blo 2307435 4383325 := bbase (se 3 (by rfl) ⟨821873, by rfl⟩ : syracuseStep 4383325 = 1643747) (by norm_num)
theorem B5844433 : Blo 2307435 5844433 := bstep (se 2 (by rfl) ⟨2191662, by rfl⟩ : syracuseStep 5844433 = 4383325) B4383325
theorem B7792577 : Blo 2307435 7792577 := bstep (se 2 (by rfl) ⟨2922216, by rfl⟩ : syracuseStep 7792577 = 5844433) B5844433
theorem B5195051 : Blo 2307435 5195051 := bstep (se 1 (by rfl) ⟨3896288, by rfl⟩ : syracuseStep 5195051 = 7792577) B7792577
theorem B3463367 : Blo 2307435 3463367 := bstep (se 1 (by rfl) ⟨2597525, by rfl⟩ : syracuseStep 3463367 = 5195051) B5195051
theorem B2308911 : Blo 2307435 2308911 := bstep (se 1 (by rfl) ⟨1731683, by rfl⟩ : syracuseStep 2308911 = 3463367) B3463367
theorem B3463373 : Blo 2307435 3463373 := bbase (se 3 (by rfl) ⟨649382, by rfl⟩ : syracuseStep 3463373 = 1298765) (by norm_num)
theorem B2308915 : Blo 2307435 2308915 := bstep (se 1 (by rfl) ⟨1731686, by rfl⟩ : syracuseStep 2308915 = 3463373) B3463373
theorem B5195069 : Blo 2307435 5195069 := bbase (se 3 (by rfl) ⟨974075, by rfl⟩ : syracuseStep 5195069 = 1948151) (by norm_num)
theorem B3463379 : Blo 2307435 3463379 := bstep (se 1 (by rfl) ⟨2597534, by rfl⟩ : syracuseStep 3463379 = 5195069) B5195069
theorem B2308919 : Blo 2307435 2308919 := bstep (se 1 (by rfl) ⟨1731689, by rfl⟩ : syracuseStep 2308919 = 3463379) B3463379
theorem B3896309 : Blo 2307435 3896309 := bbase (se 5 (by rfl) ⟨182639, by rfl⟩ : syracuseStep 3896309 = 365279) (by norm_num)
theorem B2597539 : Blo 2307435 2597539 := bstep (se 1 (by rfl) ⟨1948154, by rfl⟩ : syracuseStep 2597539 = 3896309) B3896309
theorem B3463385 : Blo 2307435 3463385 := bstep (se 2 (by rfl) ⟨1298769, by rfl⟩ : syracuseStep 3463385 = 2597539) B2597539
theorem B2308923 : Blo 2307435 2308923 := bstep (se 1 (by rfl) ⟨1731692, by rfl⟩ : syracuseStep 2308923 = 3463385) B3463385
theorem B5547685 : Blo 2307435 5547685 := bbase (se 4 (by rfl) ⟨520095, by rfl⟩ : syracuseStep 5547685 = 1040191) (by norm_num)
theorem B7396913 : Blo 2307435 7396913 := bstep (se 2 (by rfl) ⟨2773842, by rfl⟩ : syracuseStep 7396913 = 5547685) B5547685
theorem B4931275 : Blo 2307435 4931275 := bstep (se 1 (by rfl) ⟨3698456, by rfl⟩ : syracuseStep 4931275 = 7396913) B7396913
theorem B6575033 : Blo 2307435 6575033 := bstep (se 2 (by rfl) ⟨2465637, by rfl⟩ : syracuseStep 6575033 = 4931275) B4931275
theorem B17533421 : Blo 2307435 17533421 := bstep (se 3 (by rfl) ⟨3287516, by rfl⟩ : syracuseStep 17533421 = 6575033) B6575033
theorem B11688947 : Blo 2307435 11688947 := bstep (se 1 (by rfl) ⟨8766710, by rfl⟩ : syracuseStep 11688947 = 17533421) B17533421
theorem B7792631 : Blo 2307435 7792631 := bstep (se 1 (by rfl) ⟨5844473, by rfl⟩ : syracuseStep 7792631 = 11688947) B11688947
theorem B5195087 : Blo 2307435 5195087 := bstep (se 1 (by rfl) ⟨3896315, by rfl⟩ : syracuseStep 5195087 = 7792631) B7792631
theorem B3463391 : Blo 2307435 3463391 := bstep (se 1 (by rfl) ⟨2597543, by rfl⟩ : syracuseStep 3463391 = 5195087) B5195087
theorem B2308927 : Blo 2307435 2308927 := bstep (se 1 (by rfl) ⟨1731695, by rfl⟩ : syracuseStep 2308927 = 3463391) B3463391
theorem B3463397 : Blo 2307435 3463397 := bbase (se 4 (by rfl) ⟨324693, by rfl⟩ : syracuseStep 3463397 = 649387) (by norm_num)
theorem B2308931 : Blo 2307435 2308931 := bstep (se 1 (by rfl) ⟨1731698, by rfl⟩ : syracuseStep 2308931 = 3463397) B3463397
theorem B4931293 : Blo 2307435 4931293 := bbase (se 3 (by rfl) ⟨924617, by rfl⟩ : syracuseStep 4931293 = 1849235) (by norm_num)
theorem B6575057 : Blo 2307435 6575057 := bstep (se 2 (by rfl) ⟨2465646, by rfl⟩ : syracuseStep 6575057 = 4931293) B4931293
theorem B4383371 : Blo 2307435 4383371 := bstep (se 1 (by rfl) ⟨3287528, by rfl⟩ : syracuseStep 4383371 = 6575057) B6575057
theorem B2922247 : Blo 2307435 2922247 := bstep (se 1 (by rfl) ⟨2191685, by rfl⟩ : syracuseStep 2922247 = 4383371) B4383371
theorem B3896329 : Blo 2307435 3896329 := bstep (se 2 (by rfl) ⟨1461123, by rfl⟩ : syracuseStep 3896329 = 2922247) B2922247
theorem B5195105 : Blo 2307435 5195105 := bstep (se 2 (by rfl) ⟨1948164, by rfl⟩ : syracuseStep 5195105 = 3896329) B3896329
theorem B3463403 : Blo 2307435 3463403 := bstep (se 1 (by rfl) ⟨2597552, by rfl⟩ : syracuseStep 3463403 = 5195105) B5195105
theorem B2308935 : Blo 2307435 2308935 := bstep (se 1 (by rfl) ⟨1731701, by rfl⟩ : syracuseStep 2308935 = 3463403) B3463403
theorem B2597557 : Blo 2307435 2597557 := bbase (se 5 (by rfl) ⟨121760, by rfl⟩ : syracuseStep 2597557 = 243521) (by norm_num)
theorem B3463409 : Blo 2307435 3463409 := bstep (se 2 (by rfl) ⟨1298778, by rfl⟩ : syracuseStep 3463409 = 2597557) B2597557
theorem B2308939 : Blo 2307435 2308939 := bstep (se 1 (by rfl) ⟨1731704, by rfl⟩ : syracuseStep 2308939 = 3463409) B3463409
theorem B2922257 : Blo 2307435 2922257 := bbase (se 2 (by rfl) ⟨1095846, by rfl⟩ : syracuseStep 2922257 = 2191693) (by norm_num)
theorem B7792685 : Blo 2307435 7792685 := bstep (se 3 (by rfl) ⟨1461128, by rfl⟩ : syracuseStep 7792685 = 2922257) B2922257
theorem B5195123 : Blo 2307435 5195123 := bstep (se 1 (by rfl) ⟨3896342, by rfl⟩ : syracuseStep 5195123 = 7792685) B7792685
theorem B3463415 : Blo 2307435 3463415 := bstep (se 1 (by rfl) ⟨2597561, by rfl⟩ : syracuseStep 3463415 = 5195123) B5195123
theorem B2308943 : Blo 2307435 2308943 := bstep (se 1 (by rfl) ⟨1731707, by rfl⟩ : syracuseStep 2308943 = 3463415) B3463415
theorem B3463421 : Blo 2307435 3463421 := bbase (se 3 (by rfl) ⟨649391, by rfl⟩ : syracuseStep 3463421 = 1298783) (by norm_num)
theorem B2308947 : Blo 2307435 2308947 := bstep (se 1 (by rfl) ⟨1731710, by rfl⟩ : syracuseStep 2308947 = 3463421) B3463421
theorem B5195141 : Blo 2307435 5195141 := bbase (se 4 (by rfl) ⟨487044, by rfl⟩ : syracuseStep 5195141 = 974089) (by norm_num)
theorem B3463427 : Blo 2307435 3463427 := bstep (se 1 (by rfl) ⟨2597570, by rfl⟩ : syracuseStep 3463427 = 5195141) B5195141
theorem B2308951 : Blo 2307435 2308951 := bstep (se 1 (by rfl) ⟨1731713, by rfl⟩ : syracuseStep 2308951 = 3463427) B3463427
theorem B3287557 : Blo 2307435 3287557 := bbase (se 4 (by rfl) ⟨308208, by rfl⟩ : syracuseStep 3287557 = 616417) (by norm_num)
theorem B4383409 : Blo 2307435 4383409 := bstep (se 2 (by rfl) ⟨1643778, by rfl⟩ : syracuseStep 4383409 = 3287557) B3287557
theorem B5844545 : Blo 2307435 5844545 := bstep (se 2 (by rfl) ⟨2191704, by rfl⟩ : syracuseStep 5844545 = 4383409) B4383409
theorem B3896363 : Blo 2307435 3896363 := bstep (se 1 (by rfl) ⟨2922272, by rfl⟩ : syracuseStep 3896363 = 5844545) B5844545
theorem B2597575 : Blo 2307435 2597575 := bstep (se 1 (by rfl) ⟨1948181, by rfl⟩ : syracuseStep 2597575 = 3896363) B3896363
theorem B3463433 : Blo 2307435 3463433 := bstep (se 2 (by rfl) ⟨1298787, by rfl⟩ : syracuseStep 3463433 = 2597575) B2597575
theorem B2308955 : Blo 2307435 2308955 := bstep (se 1 (by rfl) ⟨1731716, by rfl⟩ : syracuseStep 2308955 = 3463433) B3463433
theorem B11689109 : Blo 2307435 11689109 := bbase (se 6 (by rfl) ⟨273963, by rfl⟩ : syracuseStep 11689109 = 547927) (by norm_num)
theorem B7792739 : Blo 2307435 7792739 := bstep (se 1 (by rfl) ⟨5844554, by rfl⟩ : syracuseStep 7792739 = 11689109) B11689109
theorem B5195159 : Blo 2307435 5195159 := bstep (se 1 (by rfl) ⟨3896369, by rfl⟩ : syracuseStep 5195159 = 7792739) B7792739
theorem B3463439 : Blo 2307435 3463439 := bstep (se 1 (by rfl) ⟨2597579, by rfl⟩ : syracuseStep 3463439 = 5195159) B5195159
theorem B2308959 : Blo 2307435 2308959 := bstep (se 1 (by rfl) ⟨1731719, by rfl⟩ : syracuseStep 2308959 = 3463439) B3463439
theorem B3463445 : Blo 2307435 3463445 := bbase (se 6 (by rfl) ⟨81174, by rfl⟩ : syracuseStep 3463445 = 162349) (by norm_num)
theorem B2308963 : Blo 2307435 2308963 := bstep (se 1 (by rfl) ⟨1731722, by rfl⟩ : syracuseStep 2308963 = 3463445) B3463445
theorem B5547781 : Blo 2307435 5547781 := bbase (se 4 (by rfl) ⟨520104, by rfl⟩ : syracuseStep 5547781 = 1040209) (by norm_num)
theorem B29588165 : Blo 2307435 29588165 := bstep (se 4 (by rfl) ⟨2773890, by rfl⟩ : syracuseStep 29588165 = 5547781) B5547781
theorem B19725443 : Blo 2307435 19725443 := bstep (se 1 (by rfl) ⟨14794082, by rfl⟩ : syracuseStep 19725443 = 29588165) B29588165
theorem B13150295 : Blo 2307435 13150295 := bstep (se 1 (by rfl) ⟨9862721, by rfl⟩ : syracuseStep 13150295 = 19725443) B19725443
theorem B8766863 : Blo 2307435 8766863 := bstep (se 1 (by rfl) ⟨6575147, by rfl⟩ : syracuseStep 8766863 = 13150295) B13150295
theorem B5844575 : Blo 2307435 5844575 := bstep (se 1 (by rfl) ⟨4383431, by rfl⟩ : syracuseStep 5844575 = 8766863) B8766863
theorem B3896383 : Blo 2307435 3896383 := bstep (se 1 (by rfl) ⟨2922287, by rfl⟩ : syracuseStep 3896383 = 5844575) B5844575
theorem B5195177 : Blo 2307435 5195177 := bstep (se 2 (by rfl) ⟨1948191, by rfl⟩ : syracuseStep 5195177 = 3896383) B3896383
theorem B3463451 : Blo 2307435 3463451 := bstep (se 1 (by rfl) ⟨2597588, by rfl⟩ : syracuseStep 3463451 = 5195177) B5195177
theorem B2308967 : Blo 2307435 2308967 := bstep (se 1 (by rfl) ⟨1731725, by rfl⟩ : syracuseStep 2308967 = 3463451) B3463451
theorem B2597593 : Blo 2307435 2597593 := bbase (se 2 (by rfl) ⟨974097, by rfl⟩ : syracuseStep 2597593 = 1948195) (by norm_num)
theorem B3463457 : Blo 2307435 3463457 := bstep (se 2 (by rfl) ⟨1298796, by rfl⟩ : syracuseStep 3463457 = 2597593) B2597593
theorem B2308971 : Blo 2307435 2308971 := bstep (se 1 (by rfl) ⟨1731728, by rfl⟩ : syracuseStep 2308971 = 3463457) B3463457
theorem B2465689 : Blo 2307435 2465689 := bbase (se 2 (by rfl) ⟨924633, by rfl⟩ : syracuseStep 2465689 = 1849267) (by norm_num)
theorem B3287585 : Blo 2307435 3287585 := bstep (se 2 (by rfl) ⟨1232844, by rfl⟩ : syracuseStep 3287585 = 2465689) B2465689
theorem B8766893 : Blo 2307435 8766893 := bstep (se 3 (by rfl) ⟨1643792, by rfl⟩ : syracuseStep 8766893 = 3287585) B3287585
theorem B5844595 : Blo 2307435 5844595 := bstep (se 1 (by rfl) ⟨4383446, by rfl⟩ : syracuseStep 5844595 = 8766893) B8766893
theorem B7792793 : Blo 2307435 7792793 := bstep (se 2 (by rfl) ⟨2922297, by rfl⟩ : syracuseStep 7792793 = 5844595) B5844595
theorem B5195195 : Blo 2307435 5195195 := bstep (se 1 (by rfl) ⟨3896396, by rfl⟩ : syracuseStep 5195195 = 7792793) B7792793
theorem B3463463 : Blo 2307435 3463463 := bstep (se 1 (by rfl) ⟨2597597, by rfl⟩ : syracuseStep 3463463 = 5195195) B5195195
theorem B2308975 : Blo 2307435 2308975 := bstep (se 1 (by rfl) ⟨1731731, by rfl⟩ : syracuseStep 2308975 = 3463463) B3463463
theorem B3463469 : Blo 2307435 3463469 := bbase (se 3 (by rfl) ⟨649400, by rfl⟩ : syracuseStep 3463469 = 1298801) (by norm_num)
theorem B2308979 : Blo 2307435 2308979 := bstep (se 1 (by rfl) ⟨1731734, by rfl⟩ : syracuseStep 2308979 = 3463469) B3463469
theorem B5195213 : Blo 2307435 5195213 := bbase (se 3 (by rfl) ⟨974102, by rfl⟩ : syracuseStep 5195213 = 1948205) (by norm_num)
theorem B3463475 : Blo 2307435 3463475 := bstep (se 1 (by rfl) ⟨2597606, by rfl⟩ : syracuseStep 3463475 = 5195213) B5195213
theorem B2308983 : Blo 2307435 2308983 := bstep (se 1 (by rfl) ⟨1731737, by rfl⟩ : syracuseStep 2308983 = 3463475) B3463475
theorem B2922313 : Blo 2307435 2922313 := bbase (se 2 (by rfl) ⟨1095867, by rfl⟩ : syracuseStep 2922313 = 2191735) (by norm_num)
theorem B3896417 : Blo 2307435 3896417 := bstep (se 2 (by rfl) ⟨1461156, by rfl⟩ : syracuseStep 3896417 = 2922313) B2922313
theorem B2597611 : Blo 2307435 2597611 := bstep (se 1 (by rfl) ⟨1948208, by rfl⟩ : syracuseStep 2597611 = 3896417) B3896417
theorem B3463481 : Blo 2307435 3463481 := bstep (se 2 (by rfl) ⟨1298805, by rfl⟩ : syracuseStep 3463481 = 2597611) B2597611
theorem B2308987 : Blo 2307435 2308987 := bstep (se 1 (by rfl) ⟨1731740, by rfl⟩ : syracuseStep 2308987 = 3463481) B3463481
theorem B3749021 : Blo 2307435 3749021 := bbase (se 3 (by rfl) ⟨702941, by rfl⟩ : syracuseStep 3749021 = 1405883) (by norm_num)
theorem B2499347 : Blo 2307435 2499347 := bstep (se 1 (by rfl) ⟨1874510, by rfl⟩ : syracuseStep 2499347 = 3749021) B3749021
theorem B6664925 : Blo 2307435 6664925 := bstep (se 3 (by rfl) ⟨1249673, by rfl⟩ : syracuseStep 6664925 = 2499347) B2499347
theorem B4443283 : Blo 2307435 4443283 := bstep (se 1 (by rfl) ⟨3332462, by rfl⟩ : syracuseStep 4443283 = 6664925) B6664925
theorem B5924377 : Blo 2307435 5924377 := bstep (se 2 (by rfl) ⟨2221641, by rfl⟩ : syracuseStep 5924377 = 4443283) B4443283
theorem B7899169 : Blo 2307435 7899169 := bstep (se 2 (by rfl) ⟨2962188, by rfl⟩ : syracuseStep 7899169 = 5924377) B5924377
theorem B10532225 : Blo 2307435 10532225 := bstep (se 2 (by rfl) ⟨3949584, by rfl⟩ : syracuseStep 10532225 = 7899169) B7899169
theorem B28085933 : Blo 2307435 28085933 := bstep (se 3 (by rfl) ⟨5266112, by rfl⟩ : syracuseStep 28085933 = 10532225) B10532225
theorem B18723955 : Blo 2307435 18723955 := bstep (se 1 (by rfl) ⟨14042966, by rfl⟩ : syracuseStep 18723955 = 28085933) B28085933
theorem B24965273 : Blo 2307435 24965273 := bstep (se 2 (by rfl) ⟨9361977, by rfl⟩ : syracuseStep 24965273 = 18723955) B18723955
theorem B16643515 : Blo 2307435 16643515 := bstep (se 1 (by rfl) ⟨12482636, by rfl⟩ : syracuseStep 16643515 = 24965273) B24965273
theorem B22191353 : Blo 2307435 22191353 := bstep (se 2 (by rfl) ⟨8321757, by rfl⟩ : syracuseStep 22191353 = 16643515) B16643515
theorem B14794235 : Blo 2307435 14794235 := bstep (se 1 (by rfl) ⟨11095676, by rfl⟩ : syracuseStep 14794235 = 22191353) B22191353
theorem B9862823 : Blo 2307435 9862823 := bstep (se 1 (by rfl) ⟨7397117, by rfl⟩ : syracuseStep 9862823 = 14794235) B14794235
theorem B26300861 : Blo 2307435 26300861 := bstep (se 3 (by rfl) ⟨4931411, by rfl⟩ : syracuseStep 26300861 = 9862823) B9862823
theorem B17533907 : Blo 2307435 17533907 := bstep (se 1 (by rfl) ⟨13150430, by rfl⟩ : syracuseStep 17533907 = 26300861) B26300861
theorem B11689271 : Blo 2307435 11689271 := bstep (se 1 (by rfl) ⟨8766953, by rfl⟩ : syracuseStep 11689271 = 17533907) B17533907
theorem B7792847 : Blo 2307435 7792847 := bstep (se 1 (by rfl) ⟨5844635, by rfl⟩ : syracuseStep 7792847 = 11689271) B11689271
theorem B5195231 : Blo 2307435 5195231 := bstep (se 1 (by rfl) ⟨3896423, by rfl⟩ : syracuseStep 5195231 = 7792847) B7792847
theorem B3463487 : Blo 2307435 3463487 := bstep (se 1 (by rfl) ⟨2597615, by rfl⟩ : syracuseStep 3463487 = 5195231) B5195231
theorem B2308991 : Blo 2307435 2308991 := bstep (se 1 (by rfl) ⟨1731743, by rfl⟩ : syracuseStep 2308991 = 3463487) B3463487
theorem B3463493 : Blo 2307435 3463493 := bbase (se 4 (by rfl) ⟨324702, by rfl⟩ : syracuseStep 3463493 = 649405) (by norm_num)
theorem B2308995 : Blo 2307435 2308995 := bstep (se 1 (by rfl) ⟨1731746, by rfl⟩ : syracuseStep 2308995 = 3463493) B3463493
theorem B3896437 : Blo 2307435 3896437 := bbase (se 5 (by rfl) ⟨182645, by rfl⟩ : syracuseStep 3896437 = 365291) (by norm_num)
theorem B5195249 : Blo 2307435 5195249 := bstep (se 2 (by rfl) ⟨1948218, by rfl⟩ : syracuseStep 5195249 = 3896437) B3896437
theorem B3463499 : Blo 2307435 3463499 := bstep (se 1 (by rfl) ⟨2597624, by rfl⟩ : syracuseStep 3463499 = 5195249) B5195249
theorem B2308999 : Blo 2307435 2308999 := bstep (se 1 (by rfl) ⟨1731749, by rfl⟩ : syracuseStep 2308999 = 3463499) B3463499
theorem B2597629 : Blo 2307435 2597629 := bbase (se 3 (by rfl) ⟨487055, by rfl⟩ : syracuseStep 2597629 = 974111) (by norm_num)
theorem B3463505 : Blo 2307435 3463505 := bstep (se 2 (by rfl) ⟨1298814, by rfl⟩ : syracuseStep 3463505 = 2597629) B2597629
theorem B2309003 : Blo 2307435 2309003 := bstep (se 1 (by rfl) ⟨1731752, by rfl⟩ : syracuseStep 2309003 = 3463505) B3463505
theorem B7792901 : Blo 2307435 7792901 := bbase (se 4 (by rfl) ⟨730584, by rfl⟩ : syracuseStep 7792901 = 1461169) (by norm_num)
theorem B5195267 : Blo 2307435 5195267 := bstep (se 1 (by rfl) ⟨3896450, by rfl⟩ : syracuseStep 5195267 = 7792901) B7792901
theorem B3463511 : Blo 2307435 3463511 := bstep (se 1 (by rfl) ⟨2597633, by rfl⟩ : syracuseStep 3463511 = 5195267) B5195267
theorem B2309007 : Blo 2307435 2309007 := bstep (se 1 (by rfl) ⟨1731755, by rfl⟩ : syracuseStep 2309007 = 3463511) B3463511
theorem B3463517 : Blo 2307435 3463517 := bbase (se 3 (by rfl) ⟨649409, by rfl⟩ : syracuseStep 3463517 = 1298819) (by norm_num)
theorem B2309011 : Blo 2307435 2309011 := bstep (se 1 (by rfl) ⟨1731758, by rfl⟩ : syracuseStep 2309011 = 3463517) B3463517
theorem B5195285 : Blo 2307435 5195285 := bbase (se 6 (by rfl) ⟨121764, by rfl⟩ : syracuseStep 5195285 = 243529) (by norm_num)
theorem B3463523 : Blo 2307435 3463523 := bstep (se 1 (by rfl) ⟨2597642, by rfl⟩ : syracuseStep 3463523 = 5195285) B5195285
theorem B2309015 : Blo 2307435 2309015 := bstep (se 1 (by rfl) ⟨1731761, by rfl⟩ : syracuseStep 2309015 = 3463523) B3463523
theorem B8767061 : Blo 2307435 8767061 := bbase (se 8 (by rfl) ⟨51369, by rfl⟩ : syracuseStep 8767061 = 102739) (by norm_num)
theorem B5844707 : Blo 2307435 5844707 := bstep (se 1 (by rfl) ⟨4383530, by rfl⟩ : syracuseStep 5844707 = 8767061) B8767061
theorem B3896471 : Blo 2307435 3896471 := bstep (se 1 (by rfl) ⟨2922353, by rfl⟩ : syracuseStep 3896471 = 5844707) B5844707
theorem B2597647 : Blo 2307435 2597647 := bstep (se 1 (by rfl) ⟨1948235, by rfl⟩ : syracuseStep 2597647 = 3896471) B3896471
theorem B3463529 : Blo 2307435 3463529 := bstep (se 2 (by rfl) ⟨1298823, by rfl⟩ : syracuseStep 3463529 = 2597647) B2597647
theorem B2309019 : Blo 2307435 2309019 := bstep (se 1 (by rfl) ⟨1731764, by rfl⟩ : syracuseStep 2309019 = 3463529) B3463529
theorem B13150613 : Blo 2307435 13150613 := bbase (se 6 (by rfl) ⟨308217, by rfl⟩ : syracuseStep 13150613 = 616435) (by norm_num)
theorem B8767075 : Blo 2307435 8767075 := bstep (se 1 (by rfl) ⟨6575306, by rfl⟩ : syracuseStep 8767075 = 13150613) B13150613
theorem B11689433 : Blo 2307435 11689433 := bstep (se 2 (by rfl) ⟨4383537, by rfl⟩ : syracuseStep 11689433 = 8767075) B8767075
theorem B7792955 : Blo 2307435 7792955 := bstep (se 1 (by rfl) ⟨5844716, by rfl⟩ : syracuseStep 7792955 = 11689433) B11689433
theorem B5195303 : Blo 2307435 5195303 := bstep (se 1 (by rfl) ⟨3896477, by rfl⟩ : syracuseStep 5195303 = 7792955) B7792955
theorem B3463535 : Blo 2307435 3463535 := bstep (se 1 (by rfl) ⟨2597651, by rfl⟩ : syracuseStep 3463535 = 5195303) B5195303
theorem B2309023 : Blo 2307435 2309023 := bstep (se 1 (by rfl) ⟨1731767, by rfl⟩ : syracuseStep 2309023 = 3463535) B3463535
theorem B3463541 : Blo 2307435 3463541 := bbase (se 5 (by rfl) ⟨162353, by rfl⟩ : syracuseStep 3463541 = 324707) (by norm_num)
theorem B2309027 : Blo 2307435 2309027 := bstep (se 1 (by rfl) ⟨1731770, by rfl⟩ : syracuseStep 2309027 = 3463541) B3463541
theorem B2465749 : Blo 2307435 2465749 := bbase (se 7 (by rfl) ⟨28895, by rfl⟩ : syracuseStep 2465749 = 57791) (by norm_num)
theorem B3287665 : Blo 2307435 3287665 := bstep (se 2 (by rfl) ⟨1232874, by rfl⟩ : syracuseStep 3287665 = 2465749) B2465749
theorem B4383553 : Blo 2307435 4383553 := bstep (se 2 (by rfl) ⟨1643832, by rfl⟩ : syracuseStep 4383553 = 3287665) B3287665
theorem B5844737 : Blo 2307435 5844737 := bstep (se 2 (by rfl) ⟨2191776, by rfl⟩ : syracuseStep 5844737 = 4383553) B4383553
theorem B3896491 : Blo 2307435 3896491 := bstep (se 1 (by rfl) ⟨2922368, by rfl⟩ : syracuseStep 3896491 = 5844737) B5844737
theorem B5195321 : Blo 2307435 5195321 := bstep (se 2 (by rfl) ⟨1948245, by rfl⟩ : syracuseStep 5195321 = 3896491) B3896491
theorem B3463547 : Blo 2307435 3463547 := bstep (se 1 (by rfl) ⟨2597660, by rfl⟩ : syracuseStep 3463547 = 5195321) B5195321
theorem B2309031 : Blo 2307435 2309031 := bstep (se 1 (by rfl) ⟨1731773, by rfl⟩ : syracuseStep 2309031 = 3463547) B3463547
theorem B2597665 : Blo 2307435 2597665 := bbase (se 2 (by rfl) ⟨974124, by rfl⟩ : syracuseStep 2597665 = 1948249) (by norm_num)
theorem B3463553 : Blo 2307435 3463553 := bstep (se 2 (by rfl) ⟨1298832, by rfl⟩ : syracuseStep 3463553 = 2597665) B2597665
theorem B2309035 : Blo 2307435 2309035 := bstep (se 1 (by rfl) ⟨1731776, by rfl⟩ : syracuseStep 2309035 = 3463553) B3463553
theorem B5844757 : Blo 2307435 5844757 := bbase (se 6 (by rfl) ⟨136986, by rfl⟩ : syracuseStep 5844757 = 273973) (by norm_num)
theorem B7793009 : Blo 2307435 7793009 := bstep (se 2 (by rfl) ⟨2922378, by rfl⟩ : syracuseStep 7793009 = 5844757) B5844757
theorem B5195339 : Blo 2307435 5195339 := bstep (se 1 (by rfl) ⟨3896504, by rfl⟩ : syracuseStep 5195339 = 7793009) B7793009
theorem B3463559 : Blo 2307435 3463559 := bstep (se 1 (by rfl) ⟨2597669, by rfl⟩ : syracuseStep 3463559 = 5195339) B5195339
theorem B2309039 : Blo 2307435 2309039 := bstep (se 1 (by rfl) ⟨1731779, by rfl⟩ : syracuseStep 2309039 = 3463559) B3463559
theorem B3463565 : Blo 2307435 3463565 := bbase (se 3 (by rfl) ⟨649418, by rfl⟩ : syracuseStep 3463565 = 1298837) (by norm_num)
theorem B2309043 : Blo 2307435 2309043 := bstep (se 1 (by rfl) ⟨1731782, by rfl⟩ : syracuseStep 2309043 = 3463565) B3463565
theorem B5195357 : Blo 2307435 5195357 := bbase (se 3 (by rfl) ⟨974129, by rfl⟩ : syracuseStep 5195357 = 1948259) (by norm_num)
theorem B3463571 : Blo 2307435 3463571 := bstep (se 1 (by rfl) ⟨2597678, by rfl⟩ : syracuseStep 3463571 = 5195357) B5195357
theorem B2309047 : Blo 2307435 2309047 := bstep (se 1 (by rfl) ⟨1731785, by rfl⟩ : syracuseStep 2309047 = 3463571) B3463571
theorem B3896525 : Blo 2307435 3896525 := bbase (se 3 (by rfl) ⟨730598, by rfl⟩ : syracuseStep 3896525 = 1461197) (by norm_num)
theorem B2597683 : Blo 2307435 2597683 := bstep (se 1 (by rfl) ⟨1948262, by rfl⟩ : syracuseStep 2597683 = 3896525) B3896525
theorem B3463577 : Blo 2307435 3463577 := bstep (se 2 (by rfl) ⟨1298841, by rfl⟩ : syracuseStep 3463577 = 2597683) B2597683
theorem B2309051 : Blo 2307435 2309051 := bstep (se 1 (by rfl) ⟨1731788, by rfl⟩ : syracuseStep 2309051 = 3463577) B3463577
theorem B14794645 : Blo 2307435 14794645 := bbase (se 6 (by rfl) ⟨346749, by rfl⟩ : syracuseStep 14794645 = 693499) (by norm_num)
theorem B19726193 : Blo 2307435 19726193 := bstep (se 2 (by rfl) ⟨7397322, by rfl⟩ : syracuseStep 19726193 = 14794645) B14794645
theorem B13150795 : Blo 2307435 13150795 := bstep (se 1 (by rfl) ⟨9863096, by rfl⟩ : syracuseStep 13150795 = 19726193) B19726193
theorem B17534393 : Blo 2307435 17534393 := bstep (se 2 (by rfl) ⟨6575397, by rfl⟩ : syracuseStep 17534393 = 13150795) B13150795
theorem B11689595 : Blo 2307435 11689595 := bstep (se 1 (by rfl) ⟨8767196, by rfl⟩ : syracuseStep 11689595 = 17534393) B17534393
theorem B7793063 : Blo 2307435 7793063 := bstep (se 1 (by rfl) ⟨5844797, by rfl⟩ : syracuseStep 7793063 = 11689595) B11689595
theorem B5195375 : Blo 2307435 5195375 := bstep (se 1 (by rfl) ⟨3896531, by rfl⟩ : syracuseStep 5195375 = 7793063) B7793063
theorem B3463583 : Blo 2307435 3463583 := bstep (se 1 (by rfl) ⟨2597687, by rfl⟩ : syracuseStep 3463583 = 5195375) B5195375
theorem B2309055 : Blo 2307435 2309055 := bstep (se 1 (by rfl) ⟨1731791, by rfl⟩ : syracuseStep 2309055 = 3463583) B3463583
theorem B3463589 : Blo 2307435 3463589 := bbase (se 4 (by rfl) ⟨324711, by rfl⟩ : syracuseStep 3463589 = 649423) (by norm_num)
theorem B2309059 : Blo 2307435 2309059 := bstep (se 1 (by rfl) ⟨1731794, by rfl⟩ : syracuseStep 2309059 = 3463589) B3463589
theorem B2922409 : Blo 2307435 2922409 := bbase (se 2 (by rfl) ⟨1095903, by rfl⟩ : syracuseStep 2922409 = 2191807) (by norm_num)
theorem B3896545 : Blo 2307435 3896545 := bstep (se 2 (by rfl) ⟨1461204, by rfl⟩ : syracuseStep 3896545 = 2922409) B2922409
theorem B5195393 : Blo 2307435 5195393 := bstep (se 2 (by rfl) ⟨1948272, by rfl⟩ : syracuseStep 5195393 = 3896545) B3896545
theorem B3463595 : Blo 2307435 3463595 := bstep (se 1 (by rfl) ⟨2597696, by rfl⟩ : syracuseStep 3463595 = 5195393) B5195393
theorem B2309063 : Blo 2307435 2309063 := bstep (se 1 (by rfl) ⟨1731797, by rfl⟩ : syracuseStep 2309063 = 3463595) B3463595
theorem B2597701 : Blo 2307435 2597701 := bbase (se 4 (by rfl) ⟨243534, by rfl⟩ : syracuseStep 2597701 = 487069) (by norm_num)
theorem B3463601 : Blo 2307435 3463601 := bstep (se 2 (by rfl) ⟨1298850, by rfl⟩ : syracuseStep 3463601 = 2597701) B2597701
theorem B2309067 : Blo 2307435 2309067 := bstep (se 1 (by rfl) ⟨1731800, by rfl⟩ : syracuseStep 2309067 = 3463601) B3463601
theorem B4383629 : Blo 2307435 4383629 := bbase (se 3 (by rfl) ⟨821930, by rfl⟩ : syracuseStep 4383629 = 1643861) (by norm_num)
theorem B2922419 : Blo 2307435 2922419 := bstep (se 1 (by rfl) ⟨2191814, by rfl⟩ : syracuseStep 2922419 = 4383629) B4383629
theorem B7793117 : Blo 2307435 7793117 := bstep (se 3 (by rfl) ⟨1461209, by rfl⟩ : syracuseStep 7793117 = 2922419) B2922419
theorem B5195411 : Blo 2307435 5195411 := bstep (se 1 (by rfl) ⟨3896558, by rfl⟩ : syracuseStep 5195411 = 7793117) B7793117
theorem B3463607 : Blo 2307435 3463607 := bstep (se 1 (by rfl) ⟨2597705, by rfl⟩ : syracuseStep 3463607 = 5195411) B5195411
theorem B2309071 : Blo 2307435 2309071 := bstep (se 1 (by rfl) ⟨1731803, by rfl⟩ : syracuseStep 2309071 = 3463607) B3463607
theorem B3463613 : Blo 2307435 3463613 := bbase (se 3 (by rfl) ⟨649427, by rfl⟩ : syracuseStep 3463613 = 1298855) (by norm_num)
theorem B2309075 : Blo 2307435 2309075 := bstep (se 1 (by rfl) ⟨1731806, by rfl⟩ : syracuseStep 2309075 = 3463613) B3463613
theorem B5195429 : Blo 2307435 5195429 := bbase (se 4 (by rfl) ⟨487071, by rfl⟩ : syracuseStep 5195429 = 974143) (by norm_num)
theorem B3463619 : Blo 2307435 3463619 := bstep (se 1 (by rfl) ⟨2597714, by rfl⟩ : syracuseStep 3463619 = 5195429) B5195429
theorem B2309079 : Blo 2307435 2309079 := bstep (se 1 (by rfl) ⟨1731809, by rfl⟩ : syracuseStep 2309079 = 3463619) B3463619
theorem B5844869 : Blo 2307435 5844869 := bbase (se 4 (by rfl) ⟨547956, by rfl⟩ : syracuseStep 5844869 = 1095913) (by norm_num)
theorem B3896579 : Blo 2307435 3896579 := bstep (se 1 (by rfl) ⟨2922434, by rfl⟩ : syracuseStep 3896579 = 5844869) B5844869
theorem B2597719 : Blo 2307435 2597719 := bstep (se 1 (by rfl) ⟨1948289, by rfl⟩ : syracuseStep 2597719 = 3896579) B3896579
theorem B3463625 : Blo 2307435 3463625 := bstep (se 2 (by rfl) ⟨1298859, by rfl⟩ : syracuseStep 3463625 = 2597719) B2597719
theorem B2309083 : Blo 2307435 2309083 := bstep (se 1 (by rfl) ⟨1731812, by rfl⟩ : syracuseStep 2309083 = 3463625) B3463625
theorem B4161053 : Blo 2307435 4161053 := bbase (se 3 (by rfl) ⟨780197, by rfl⟩ : syracuseStep 4161053 = 1560395) (by norm_num)
theorem B2774035 : Blo 2307435 2774035 := bstep (se 1 (by rfl) ⟨2080526, by rfl⟩ : syracuseStep 2774035 = 4161053) B4161053
theorem B3698713 : Blo 2307435 3698713 := bstep (se 2 (by rfl) ⟨1387017, by rfl⟩ : syracuseStep 3698713 = 2774035) B2774035
theorem B4931617 : Blo 2307435 4931617 := bstep (se 2 (by rfl) ⟨1849356, by rfl⟩ : syracuseStep 4931617 = 3698713) B3698713
theorem B6575489 : Blo 2307435 6575489 := bstep (se 2 (by rfl) ⟨2465808, by rfl⟩ : syracuseStep 6575489 = 4931617) B4931617
theorem B4383659 : Blo 2307435 4383659 := bstep (se 1 (by rfl) ⟨3287744, by rfl⟩ : syracuseStep 4383659 = 6575489) B6575489
theorem B11689757 : Blo 2307435 11689757 := bstep (se 3 (by rfl) ⟨2191829, by rfl⟩ : syracuseStep 11689757 = 4383659) B4383659
theorem B7793171 : Blo 2307435 7793171 := bstep (se 1 (by rfl) ⟨5844878, by rfl⟩ : syracuseStep 7793171 = 11689757) B11689757
theorem B5195447 : Blo 2307435 5195447 := bstep (se 1 (by rfl) ⟨3896585, by rfl⟩ : syracuseStep 5195447 = 7793171) B7793171
theorem B3463631 : Blo 2307435 3463631 := bstep (se 1 (by rfl) ⟨2597723, by rfl⟩ : syracuseStep 3463631 = 5195447) B5195447
theorem B2309087 : Blo 2307435 2309087 := bstep (se 1 (by rfl) ⟨1731815, by rfl⟩ : syracuseStep 2309087 = 3463631) B3463631
theorem B3463637 : Blo 2307435 3463637 := bbase (se 7 (by rfl) ⟨40589, by rfl⟩ : syracuseStep 3463637 = 81179) (by norm_num)
theorem B2309091 : Blo 2307435 2309091 := bstep (se 1 (by rfl) ⟨1731818, by rfl⟩ : syracuseStep 2309091 = 3463637) B3463637
theorem B8767349 : Blo 2307435 8767349 := bbase (se 5 (by rfl) ⟨410969, by rfl⟩ : syracuseStep 8767349 = 821939) (by norm_num)
theorem B5844899 : Blo 2307435 5844899 := bstep (se 1 (by rfl) ⟨4383674, by rfl⟩ : syracuseStep 5844899 = 8767349) B8767349
theorem B3896599 : Blo 2307435 3896599 := bstep (se 1 (by rfl) ⟨2922449, by rfl⟩ : syracuseStep 3896599 = 5844899) B5844899
theorem B5195465 : Blo 2307435 5195465 := bstep (se 2 (by rfl) ⟨1948299, by rfl⟩ : syracuseStep 5195465 = 3896599) B3896599
theorem B3463643 : Blo 2307435 3463643 := bstep (se 1 (by rfl) ⟨2597732, by rfl⟩ : syracuseStep 3463643 = 5195465) B5195465
theorem B2309095 : Blo 2307435 2309095 := bstep (se 1 (by rfl) ⟨1731821, by rfl⟩ : syracuseStep 2309095 = 3463643) B3463643
theorem B2597737 : Blo 2307435 2597737 := bbase (se 2 (by rfl) ⟨974151, by rfl⟩ : syracuseStep 2597737 = 1948303) (by norm_num)
theorem B3463649 : Blo 2307435 3463649 := bstep (se 2 (by rfl) ⟨1298868, by rfl⟩ : syracuseStep 3463649 = 2597737) B2597737
theorem B2309099 : Blo 2307435 2309099 := bstep (se 1 (by rfl) ⟨1731824, by rfl⟩ : syracuseStep 2309099 = 3463649) B3463649
theorem B7397477 : Blo 2307435 7397477 := bbase (se 4 (by rfl) ⟨693513, by rfl⟩ : syracuseStep 7397477 = 1387027) (by norm_num)
theorem B4931651 : Blo 2307435 4931651 := bstep (se 1 (by rfl) ⟨3698738, by rfl⟩ : syracuseStep 4931651 = 7397477) B7397477
theorem B13151069 : Blo 2307435 13151069 := bstep (se 3 (by rfl) ⟨2465825, by rfl⟩ : syracuseStep 13151069 = 4931651) B4931651
theorem B8767379 : Blo 2307435 8767379 := bstep (se 1 (by rfl) ⟨6575534, by rfl⟩ : syracuseStep 8767379 = 13151069) B13151069
theorem B5844919 : Blo 2307435 5844919 := bstep (se 1 (by rfl) ⟨4383689, by rfl⟩ : syracuseStep 5844919 = 8767379) B8767379
theorem B7793225 : Blo 2307435 7793225 := bstep (se 2 (by rfl) ⟨2922459, by rfl⟩ : syracuseStep 7793225 = 5844919) B5844919
theorem B5195483 : Blo 2307435 5195483 := bstep (se 1 (by rfl) ⟨3896612, by rfl⟩ : syracuseStep 5195483 = 7793225) B7793225
theorem B3463655 : Blo 2307435 3463655 := bstep (se 1 (by rfl) ⟨2597741, by rfl⟩ : syracuseStep 3463655 = 5195483) B5195483
theorem B2309103 : Blo 2307435 2309103 := bstep (se 1 (by rfl) ⟨1731827, by rfl⟩ : syracuseStep 2309103 = 3463655) B3463655
theorem B3463661 : Blo 2307435 3463661 := bbase (se 3 (by rfl) ⟨649436, by rfl⟩ : syracuseStep 3463661 = 1298873) (by norm_num)
theorem B2309107 : Blo 2307435 2309107 := bstep (se 1 (by rfl) ⟨1731830, by rfl⟩ : syracuseStep 2309107 = 3463661) B3463661
theorem B5195501 : Blo 2307435 5195501 := bbase (se 3 (by rfl) ⟨974156, by rfl⟩ : syracuseStep 5195501 = 1948313) (by norm_num)
theorem B3463667 : Blo 2307435 3463667 := bstep (se 1 (by rfl) ⟨2597750, by rfl⟩ : syracuseStep 3463667 = 5195501) B5195501
theorem B2309111 : Blo 2307435 2309111 := bstep (se 1 (by rfl) ⟨1731833, by rfl⟩ : syracuseStep 2309111 = 3463667) B3463667
theorem B7117669 : Blo 2307435 7117669 := bbase (se 4 (by rfl) ⟨667281, by rfl⟩ : syracuseStep 7117669 = 1334563) (by norm_num)
theorem B9490225 : Blo 2307435 9490225 := bstep (se 2 (by rfl) ⟨3558834, by rfl⟩ : syracuseStep 9490225 = 7117669) B7117669
theorem B12653633 : Blo 2307435 12653633 := bstep (se 2 (by rfl) ⟨4745112, by rfl⟩ : syracuseStep 12653633 = 9490225) B9490225
theorem B8435755 : Blo 2307435 8435755 := bstep (se 1 (by rfl) ⟨6326816, by rfl⟩ : syracuseStep 8435755 = 12653633) B12653633
theorem B11247673 : Blo 2307435 11247673 := bstep (se 2 (by rfl) ⟨4217877, by rfl⟩ : syracuseStep 11247673 = 8435755) B8435755
theorem B14996897 : Blo 2307435 14996897 := bstep (se 2 (by rfl) ⟨5623836, by rfl⟩ : syracuseStep 14996897 = 11247673) B11247673
theorem B9997931 : Blo 2307435 9997931 := bstep (se 1 (by rfl) ⟨7498448, by rfl⟩ : syracuseStep 9997931 = 14996897) B14996897
theorem B26661149 : Blo 2307435 26661149 := bstep (se 3 (by rfl) ⟨4998965, by rfl⟩ : syracuseStep 26661149 = 9997931) B9997931
theorem B17774099 : Blo 2307435 17774099 := bstep (se 1 (by rfl) ⟨13330574, by rfl⟩ : syracuseStep 17774099 = 26661149) B26661149
theorem B11849399 : Blo 2307435 11849399 := bstep (se 1 (by rfl) ⟨8887049, by rfl⟩ : syracuseStep 11849399 = 17774099) B17774099
theorem B7899599 : Blo 2307435 7899599 := bstep (se 1 (by rfl) ⟨5924699, by rfl⟩ : syracuseStep 7899599 = 11849399) B11849399
theorem B5266399 : Blo 2307435 5266399 := bstep (se 1 (by rfl) ⟨3949799, by rfl⟩ : syracuseStep 5266399 = 7899599) B7899599
theorem B7021865 : Blo 2307435 7021865 := bstep (se 2 (by rfl) ⟨2633199, by rfl⟩ : syracuseStep 7021865 = 5266399) B5266399
theorem B4681243 : Blo 2307435 4681243 := bstep (se 1 (by rfl) ⟨3510932, by rfl⟩ : syracuseStep 4681243 = 7021865) B7021865
theorem B6241657 : Blo 2307435 6241657 := bstep (se 2 (by rfl) ⟨2340621, by rfl⟩ : syracuseStep 6241657 = 4681243) B4681243
theorem B8322209 : Blo 2307435 8322209 := bstep (se 2 (by rfl) ⟨3120828, by rfl⟩ : syracuseStep 8322209 = 6241657) B6241657
theorem B5548139 : Blo 2307435 5548139 := bstep (se 1 (by rfl) ⟨4161104, by rfl⟩ : syracuseStep 5548139 = 8322209) B8322209
theorem B3698759 : Blo 2307435 3698759 := bstep (se 1 (by rfl) ⟨2774069, by rfl⟩ : syracuseStep 3698759 = 5548139) B5548139
theorem B2465839 : Blo 2307435 2465839 := bstep (se 1 (by rfl) ⟨1849379, by rfl⟩ : syracuseStep 2465839 = 3698759) B3698759
theorem B3287785 : Blo 2307435 3287785 := bstep (se 2 (by rfl) ⟨1232919, by rfl⟩ : syracuseStep 3287785 = 2465839) B2465839
theorem B4383713 : Blo 2307435 4383713 := bstep (se 2 (by rfl) ⟨1643892, by rfl⟩ : syracuseStep 4383713 = 3287785) B3287785
theorem B2922475 : Blo 2307435 2922475 := bstep (se 1 (by rfl) ⟨2191856, by rfl⟩ : syracuseStep 2922475 = 4383713) B4383713
theorem B3896633 : Blo 2307435 3896633 := bstep (se 2 (by rfl) ⟨1461237, by rfl⟩ : syracuseStep 3896633 = 2922475) B2922475
theorem B2597755 : Blo 2307435 2597755 := bstep (se 1 (by rfl) ⟨1948316, by rfl⟩ : syracuseStep 2597755 = 3896633) B3896633
theorem B3463673 : Blo 2307435 3463673 := bstep (se 2 (by rfl) ⟨1298877, by rfl⟩ : syracuseStep 3463673 = 2597755) B2597755
theorem B2309115 : Blo 2307435 2309115 := bstep (se 1 (by rfl) ⟨1731836, by rfl⟩ : syracuseStep 2309115 = 3463673) B3463673
theorem B6326821 : Blo 2307435 6326821 := bbase (se 4 (by rfl) ⟨593139, by rfl⟩ : syracuseStep 6326821 = 1186279) (by norm_num)
theorem B8435761 : Blo 2307435 8435761 := bstep (se 2 (by rfl) ⟨3163410, by rfl⟩ : syracuseStep 8435761 = 6326821) B6326821
theorem B44990725 : Blo 2307435 44990725 := bstep (se 4 (by rfl) ⟨4217880, by rfl⟩ : syracuseStep 44990725 = 8435761) B8435761
theorem B59987633 : Blo 2307435 59987633 := bstep (se 2 (by rfl) ⟨22495362, by rfl⟩ : syracuseStep 59987633 = 44990725) B44990725
theorem B639868085 : Blo 2307435 639868085 := bstep (se 5 (by rfl) ⟨29993816, by rfl⟩ : syracuseStep 639868085 = 59987633) B59987633
theorem B426578723 : Blo 2307435 426578723 := bstep (se 1 (by rfl) ⟨319934042, by rfl⟩ : syracuseStep 426578723 = 639868085) B639868085
theorem B284385815 : Blo 2307435 284385815 := bstep (se 1 (by rfl) ⟨213289361, by rfl⟩ : syracuseStep 284385815 = 426578723) B426578723
theorem B189590543 : Blo 2307435 189590543 := bstep (se 1 (by rfl) ⟨142192907, by rfl⟩ : syracuseStep 189590543 = 284385815) B284385815
theorem B126393695 : Blo 2307435 126393695 := bstep (se 1 (by rfl) ⟨94795271, by rfl⟩ : syracuseStep 126393695 = 189590543) B189590543
theorem B84262463 : Blo 2307435 84262463 := bstep (se 1 (by rfl) ⟨63196847, by rfl⟩ : syracuseStep 84262463 = 126393695) B126393695
theorem B56174975 : Blo 2307435 56174975 := bstep (se 1 (by rfl) ⟨42131231, by rfl⟩ : syracuseStep 56174975 = 84262463) B84262463
theorem B37449983 : Blo 2307435 37449983 := bstep (se 1 (by rfl) ⟨28087487, by rfl⟩ : syracuseStep 37449983 = 56174975) B56174975
theorem B99866621 : Blo 2307435 99866621 := bstep (se 3 (by rfl) ⟨18724991, by rfl⟩ : syracuseStep 99866621 = 37449983) B37449983
theorem B66577747 : Blo 2307435 66577747 := bstep (se 1 (by rfl) ⟨49933310, by rfl⟩ : syracuseStep 66577747 = 99866621) B99866621
theorem B88770329 : Blo 2307435 88770329 := bstep (se 2 (by rfl) ⟨33288873, by rfl⟩ : syracuseStep 88770329 = 66577747) B66577747
theorem B59180219 : Blo 2307435 59180219 := bstep (se 1 (by rfl) ⟨44385164, by rfl⟩ : syracuseStep 59180219 = 88770329) B88770329
theorem B39453479 : Blo 2307435 39453479 := bstep (se 1 (by rfl) ⟨29590109, by rfl⟩ : syracuseStep 39453479 = 59180219) B59180219
theorem B26302319 : Blo 2307435 26302319 := bstep (se 1 (by rfl) ⟨19726739, by rfl⟩ : syracuseStep 26302319 = 39453479) B39453479
theorem B17534879 : Blo 2307435 17534879 := bstep (se 1 (by rfl) ⟨13151159, by rfl⟩ : syracuseStep 17534879 = 26302319) B26302319
theorem B11689919 : Blo 2307435 11689919 := bstep (se 1 (by rfl) ⟨8767439, by rfl⟩ : syracuseStep 11689919 = 17534879) B17534879
theorem B7793279 : Blo 2307435 7793279 := bstep (se 1 (by rfl) ⟨5844959, by rfl⟩ : syracuseStep 7793279 = 11689919) B11689919
theorem B5195519 : Blo 2307435 5195519 := bstep (se 1 (by rfl) ⟨3896639, by rfl⟩ : syracuseStep 5195519 = 7793279) B7793279
theorem B3463679 : Blo 2307435 3463679 := bstep (se 1 (by rfl) ⟨2597759, by rfl⟩ : syracuseStep 3463679 = 5195519) B5195519
theorem B2309119 : Blo 2307435 2309119 := bstep (se 1 (by rfl) ⟨1731839, by rfl⟩ : syracuseStep 2309119 = 3463679) B3463679
theorem B3463685 : Blo 2307435 3463685 := bbase (se 4 (by rfl) ⟨324720, by rfl⟩ : syracuseStep 3463685 = 649441) (by norm_num)
theorem B2309123 : Blo 2307435 2309123 := bstep (se 1 (by rfl) ⟨1731842, by rfl⟩ : syracuseStep 2309123 = 3463685) B3463685
theorem B3896653 : Blo 2307435 3896653 := bbase (se 3 (by rfl) ⟨730622, by rfl⟩ : syracuseStep 3896653 = 1461245) (by norm_num)
theorem B5195537 : Blo 2307435 5195537 := bstep (se 2 (by rfl) ⟨1948326, by rfl⟩ : syracuseStep 5195537 = 3896653) B3896653
theorem B3463691 : Blo 2307435 3463691 := bstep (se 1 (by rfl) ⟨2597768, by rfl⟩ : syracuseStep 3463691 = 5195537) B5195537
theorem B2309127 : Blo 2307435 2309127 := bstep (se 1 (by rfl) ⟨1731845, by rfl⟩ : syracuseStep 2309127 = 3463691) B3463691
theorem B2597773 : Blo 2307435 2597773 := bbase (se 3 (by rfl) ⟨487082, by rfl⟩ : syracuseStep 2597773 = 974165) (by norm_num)
theorem B3463697 : Blo 2307435 3463697 := bstep (se 2 (by rfl) ⟨1298886, by rfl⟩ : syracuseStep 3463697 = 2597773) B2597773
theorem B2309131 : Blo 2307435 2309131 := bstep (se 1 (by rfl) ⟨1731848, by rfl⟩ : syracuseStep 2309131 = 3463697) B3463697
theorem B7793333 : Blo 2307435 7793333 := bbase (se 5 (by rfl) ⟨365312, by rfl⟩ : syracuseStep 7793333 = 730625) (by norm_num)
theorem B5195555 : Blo 2307435 5195555 := bstep (se 1 (by rfl) ⟨3896666, by rfl⟩ : syracuseStep 5195555 = 7793333) B7793333
theorem B3463703 : Blo 2307435 3463703 := bstep (se 1 (by rfl) ⟨2597777, by rfl⟩ : syracuseStep 3463703 = 5195555) B5195555
theorem B2309135 : Blo 2307435 2309135 := bstep (se 1 (by rfl) ⟨1731851, by rfl⟩ : syracuseStep 2309135 = 3463703) B3463703
theorem B3463709 : Blo 2307435 3463709 := bbase (se 3 (by rfl) ⟨649445, by rfl⟩ : syracuseStep 3463709 = 1298891) (by norm_num)
theorem B2309139 : Blo 2307435 2309139 := bstep (se 1 (by rfl) ⟨1731854, by rfl⟩ : syracuseStep 2309139 = 3463709) B3463709
theorem B5195573 : Blo 2307435 5195573 := bbase (se 5 (by rfl) ⟨243542, by rfl⟩ : syracuseStep 5195573 = 487085) (by norm_num)
theorem B3463715 : Blo 2307435 3463715 := bstep (se 1 (by rfl) ⟨2597786, by rfl⟩ : syracuseStep 3463715 = 5195573) B5195573
theorem B2309143 : Blo 2307435 2309143 := bstep (se 1 (by rfl) ⟨1731857, by rfl⟩ : syracuseStep 2309143 = 3463715) B3463715
theorem B2499517 : Blo 2307435 2499517 := bbase (se 3 (by rfl) ⟨468659, by rfl⟩ : syracuseStep 2499517 = 937319) (by norm_num)
theorem B13330757 : Blo 2307435 13330757 := bstep (se 4 (by rfl) ⟨1249758, by rfl⟩ : syracuseStep 13330757 = 2499517) B2499517
theorem B8887171 : Blo 2307435 8887171 := bstep (se 1 (by rfl) ⟨6665378, by rfl⟩ : syracuseStep 8887171 = 13330757) B13330757
theorem B11849561 : Blo 2307435 11849561 := bstep (se 2 (by rfl) ⟨4443585, by rfl⟩ : syracuseStep 11849561 = 8887171) B8887171
theorem B7899707 : Blo 2307435 7899707 := bstep (se 1 (by rfl) ⟨5924780, by rfl⟩ : syracuseStep 7899707 = 11849561) B11849561
theorem B5266471 : Blo 2307435 5266471 := bstep (se 1 (by rfl) ⟨3949853, by rfl⟩ : syracuseStep 5266471 = 7899707) B7899707
theorem B7021961 : Blo 2307435 7021961 := bstep (se 2 (by rfl) ⟨2633235, by rfl⟩ : syracuseStep 7021961 = 5266471) B5266471
theorem B4681307 : Blo 2307435 4681307 := bstep (se 1 (by rfl) ⟨3510980, by rfl⟩ : syracuseStep 4681307 = 7021961) B7021961
theorem B3120871 : Blo 2307435 3120871 := bstep (se 1 (by rfl) ⟨2340653, by rfl⟩ : syracuseStep 3120871 = 4681307) B4681307
theorem B4161161 : Blo 2307435 4161161 := bstep (se 2 (by rfl) ⟨1560435, by rfl⟩ : syracuseStep 4161161 = 3120871) B3120871
theorem B2774107 : Blo 2307435 2774107 := bstep (se 1 (by rfl) ⟨2080580, by rfl⟩ : syracuseStep 2774107 = 4161161) B4161161
theorem B14795237 : Blo 2307435 14795237 := bstep (se 4 (by rfl) ⟨1387053, by rfl⟩ : syracuseStep 14795237 = 2774107) B2774107
theorem B9863491 : Blo 2307435 9863491 := bstep (se 1 (by rfl) ⟨7397618, by rfl⟩ : syracuseStep 9863491 = 14795237) B14795237
theorem B13151321 : Blo 2307435 13151321 := bstep (se 2 (by rfl) ⟨4931745, by rfl⟩ : syracuseStep 13151321 = 9863491) B9863491
theorem B8767547 : Blo 2307435 8767547 := bstep (se 1 (by rfl) ⟨6575660, by rfl⟩ : syracuseStep 8767547 = 13151321) B13151321
theorem B5845031 : Blo 2307435 5845031 := bstep (se 1 (by rfl) ⟨4383773, by rfl⟩ : syracuseStep 5845031 = 8767547) B8767547
theorem B3896687 : Blo 2307435 3896687 := bstep (se 1 (by rfl) ⟨2922515, by rfl⟩ : syracuseStep 3896687 = 5845031) B5845031
theorem B2597791 : Blo 2307435 2597791 := bstep (se 1 (by rfl) ⟨1948343, by rfl⟩ : syracuseStep 2597791 = 3896687) B3896687
theorem B3463721 : Blo 2307435 3463721 := bstep (se 2 (by rfl) ⟨1298895, by rfl⟩ : syracuseStep 3463721 = 2597791) B2597791
theorem B2309147 : Blo 2307435 2309147 := bstep (se 1 (by rfl) ⟨1731860, by rfl⟩ : syracuseStep 2309147 = 3463721) B3463721
theorem B31598869 : Blo 2307435 31598869 := bbase (se 6 (by rfl) ⟨740598, by rfl⟩ : syracuseStep 31598869 = 1481197) (by norm_num)
theorem B42131825 : Blo 2307435 42131825 := bstep (se 2 (by rfl) ⟨15799434, by rfl⟩ : syracuseStep 42131825 = 31598869) B31598869
theorem B28087883 : Blo 2307435 28087883 := bstep (se 1 (by rfl) ⟨21065912, by rfl⟩ : syracuseStep 28087883 = 42131825) B42131825
theorem B18725255 : Blo 2307435 18725255 := bstep (se 1 (by rfl) ⟨14043941, by rfl⟩ : syracuseStep 18725255 = 28087883) B28087883
theorem B12483503 : Blo 2307435 12483503 := bstep (se 1 (by rfl) ⟨9362627, by rfl⟩ : syracuseStep 12483503 = 18725255) B18725255
theorem B8322335 : Blo 2307435 8322335 := bstep (se 1 (by rfl) ⟨6241751, by rfl⟩ : syracuseStep 8322335 = 12483503) B12483503
theorem B5548223 : Blo 2307435 5548223 := bstep (se 1 (by rfl) ⟨4161167, by rfl⟩ : syracuseStep 5548223 = 8322335) B8322335
theorem B14795261 : Blo 2307435 14795261 := bstep (se 3 (by rfl) ⟨2774111, by rfl⟩ : syracuseStep 14795261 = 5548223) B5548223
theorem B9863507 : Blo 2307435 9863507 := bstep (se 1 (by rfl) ⟨7397630, by rfl⟩ : syracuseStep 9863507 = 14795261) B14795261
theorem B6575671 : Blo 2307435 6575671 := bstep (se 1 (by rfl) ⟨4931753, by rfl⟩ : syracuseStep 6575671 = 9863507) B9863507
theorem B8767561 : Blo 2307435 8767561 := bstep (se 2 (by rfl) ⟨3287835, by rfl⟩ : syracuseStep 8767561 = 6575671) B6575671
theorem B11690081 : Blo 2307435 11690081 := bstep (se 2 (by rfl) ⟨4383780, by rfl⟩ : syracuseStep 11690081 = 8767561) B8767561
theorem B7793387 : Blo 2307435 7793387 := bstep (se 1 (by rfl) ⟨5845040, by rfl⟩ : syracuseStep 7793387 = 11690081) B11690081
theorem B5195591 : Blo 2307435 5195591 := bstep (se 1 (by rfl) ⟨3896693, by rfl⟩ : syracuseStep 5195591 = 7793387) B7793387
theorem B3463727 : Blo 2307435 3463727 := bstep (se 1 (by rfl) ⟨2597795, by rfl⟩ : syracuseStep 3463727 = 5195591) B5195591
theorem B2309151 : Blo 2307435 2309151 := bstep (se 1 (by rfl) ⟨1731863, by rfl⟩ : syracuseStep 2309151 = 3463727) B3463727
theorem B3463733 : Blo 2307435 3463733 := bbase (se 5 (by rfl) ⟨162362, by rfl⟩ : syracuseStep 3463733 = 324725) (by norm_num)
theorem B2309155 : Blo 2307435 2309155 := bstep (se 1 (by rfl) ⟨1731866, by rfl⟩ : syracuseStep 2309155 = 3463733) B3463733
theorem B5845061 : Blo 2307435 5845061 := bbase (se 4 (by rfl) ⟨547974, by rfl⟩ : syracuseStep 5845061 = 1095949) (by norm_num)
theorem B3896707 : Blo 2307435 3896707 := bstep (se 1 (by rfl) ⟨2922530, by rfl⟩ : syracuseStep 3896707 = 5845061) B5845061
theorem B5195609 : Blo 2307435 5195609 := bstep (se 2 (by rfl) ⟨1948353, by rfl⟩ : syracuseStep 5195609 = 3896707) B3896707
theorem B3463739 : Blo 2307435 3463739 := bstep (se 1 (by rfl) ⟨2597804, by rfl⟩ : syracuseStep 3463739 = 5195609) B5195609
theorem B2309159 : Blo 2307435 2309159 := bstep (se 1 (by rfl) ⟨1731869, by rfl⟩ : syracuseStep 2309159 = 3463739) B3463739
theorem B2597809 : Blo 2307435 2597809 := bbase (se 2 (by rfl) ⟨974178, by rfl⟩ : syracuseStep 2597809 = 1948357) (by norm_num)
theorem B3463745 : Blo 2307435 3463745 := bstep (se 2 (by rfl) ⟨1298904, by rfl⟩ : syracuseStep 3463745 = 2597809) B2597809
theorem B2309163 : Blo 2307435 2309163 := bstep (se 1 (by rfl) ⟨1731872, by rfl⟩ : syracuseStep 2309163 = 3463745) B3463745
theorem B6575717 : Blo 2307435 6575717 := bbase (se 4 (by rfl) ⟨616473, by rfl⟩ : syracuseStep 6575717 = 1232947) (by norm_num)
theorem B4383811 : Blo 2307435 4383811 := bstep (se 1 (by rfl) ⟨3287858, by rfl⟩ : syracuseStep 4383811 = 6575717) B6575717
theorem B5845081 : Blo 2307435 5845081 := bstep (se 2 (by rfl) ⟨2191905, by rfl⟩ : syracuseStep 5845081 = 4383811) B4383811
theorem B7793441 : Blo 2307435 7793441 := bstep (se 2 (by rfl) ⟨2922540, by rfl⟩ : syracuseStep 7793441 = 5845081) B5845081
theorem B5195627 : Blo 2307435 5195627 := bstep (se 1 (by rfl) ⟨3896720, by rfl⟩ : syracuseStep 5195627 = 7793441) B7793441
theorem B3463751 : Blo 2307435 3463751 := bstep (se 1 (by rfl) ⟨2597813, by rfl⟩ : syracuseStep 3463751 = 5195627) B5195627
theorem B2309167 : Blo 2307435 2309167 := bstep (se 1 (by rfl) ⟨1731875, by rfl⟩ : syracuseStep 2309167 = 3463751) B3463751
theorem B3463757 : Blo 2307435 3463757 := bbase (se 3 (by rfl) ⟨649454, by rfl⟩ : syracuseStep 3463757 = 1298909) (by norm_num)
theorem B2309171 : Blo 2307435 2309171 := bstep (se 1 (by rfl) ⟨1731878, by rfl⟩ : syracuseStep 2309171 = 3463757) B3463757
theorem B5195645 : Blo 2307435 5195645 := bbase (se 3 (by rfl) ⟨974183, by rfl⟩ : syracuseStep 5195645 = 1948367) (by norm_num)
theorem B3463763 : Blo 2307435 3463763 := bstep (se 1 (by rfl) ⟨2597822, by rfl⟩ : syracuseStep 3463763 = 5195645) B5195645
theorem B2309175 : Blo 2307435 2309175 := bstep (se 1 (by rfl) ⟨1731881, by rfl⟩ : syracuseStep 2309175 = 3463763) B3463763
theorem B3896741 : Blo 2307435 3896741 := bbase (se 4 (by rfl) ⟨365319, by rfl⟩ : syracuseStep 3896741 = 730639) (by norm_num)
theorem B2597827 : Blo 2307435 2597827 := bstep (se 1 (by rfl) ⟨1948370, by rfl⟩ : syracuseStep 2597827 = 3896741) B3896741
theorem B3463769 : Blo 2307435 3463769 := bstep (se 2 (by rfl) ⟨1298913, by rfl⟩ : syracuseStep 3463769 = 2597827) B2597827
theorem B2309179 : Blo 2307435 2309179 := bstep (se 1 (by rfl) ⟨1731884, by rfl⟩ : syracuseStep 2309179 = 3463769) B3463769
theorem B5548301 : Blo 2307435 5548301 := bbase (se 3 (by rfl) ⟨1040306, by rfl⟩ : syracuseStep 5548301 = 2080613) (by norm_num)
theorem B3698867 : Blo 2307435 3698867 := bstep (se 1 (by rfl) ⟨2774150, by rfl⟩ : syracuseStep 3698867 = 5548301) B5548301
theorem B2465911 : Blo 2307435 2465911 := bstep (se 1 (by rfl) ⟨1849433, by rfl⟩ : syracuseStep 2465911 = 3698867) B3698867
theorem B3287881 : Blo 2307435 3287881 := bstep (se 2 (by rfl) ⟨1232955, by rfl⟩ : syracuseStep 3287881 = 2465911) B2465911
theorem B17535365 : Blo 2307435 17535365 := bstep (se 4 (by rfl) ⟨1643940, by rfl⟩ : syracuseStep 17535365 = 3287881) B3287881
theorem B11690243 : Blo 2307435 11690243 := bstep (se 1 (by rfl) ⟨8767682, by rfl⟩ : syracuseStep 11690243 = 17535365) B17535365
theorem B7793495 : Blo 2307435 7793495 := bstep (se 1 (by rfl) ⟨5845121, by rfl⟩ : syracuseStep 7793495 = 11690243) B11690243
theorem B5195663 : Blo 2307435 5195663 := bstep (se 1 (by rfl) ⟨3896747, by rfl⟩ : syracuseStep 5195663 = 7793495) B7793495
theorem B3463775 : Blo 2307435 3463775 := bstep (se 1 (by rfl) ⟨2597831, by rfl⟩ : syracuseStep 3463775 = 5195663) B5195663
theorem B2309183 : Blo 2307435 2309183 := bstep (se 1 (by rfl) ⟨1731887, by rfl⟩ : syracuseStep 2309183 = 3463775) B3463775
theorem B3463781 : Blo 2307435 3463781 := bbase (se 4 (by rfl) ⟨324729, by rfl⟩ : syracuseStep 3463781 = 649459) (by norm_num)
theorem B2309187 : Blo 2307435 2309187 := bstep (se 1 (by rfl) ⟨1731890, by rfl⟩ : syracuseStep 2309187 = 3463781) B3463781
theorem B3287893 : Blo 2307435 3287893 := bbase (se 9 (by rfl) ⟨9632, by rfl⟩ : syracuseStep 3287893 = 19265) (by norm_num)
theorem B4383857 : Blo 2307435 4383857 := bstep (se 2 (by rfl) ⟨1643946, by rfl⟩ : syracuseStep 4383857 = 3287893) B3287893
theorem B2922571 : Blo 2307435 2922571 := bstep (se 1 (by rfl) ⟨2191928, by rfl⟩ : syracuseStep 2922571 = 4383857) B4383857
theorem B3896761 : Blo 2307435 3896761 := bstep (se 2 (by rfl) ⟨1461285, by rfl⟩ : syracuseStep 3896761 = 2922571) B2922571
theorem B5195681 : Blo 2307435 5195681 := bstep (se 2 (by rfl) ⟨1948380, by rfl⟩ : syracuseStep 5195681 = 3896761) B3896761
theorem B3463787 : Blo 2307435 3463787 := bstep (se 1 (by rfl) ⟨2597840, by rfl⟩ : syracuseStep 3463787 = 5195681) B5195681
theorem B2309191 : Blo 2307435 2309191 := bstep (se 1 (by rfl) ⟨1731893, by rfl⟩ : syracuseStep 2309191 = 3463787) B3463787
theorem B2597845 : Blo 2307435 2597845 := bbase (se 7 (by rfl) ⟨30443, by rfl⟩ : syracuseStep 2597845 = 60887) (by norm_num)
theorem B3463793 : Blo 2307435 3463793 := bstep (se 2 (by rfl) ⟨1298922, by rfl⟩ : syracuseStep 3463793 = 2597845) B2597845
theorem B2309195 : Blo 2307435 2309195 := bstep (se 1 (by rfl) ⟨1731896, by rfl⟩ : syracuseStep 2309195 = 3463793) B3463793
theorem B2922581 : Blo 2307435 2922581 := bbase (se 8 (by rfl) ⟨17124, by rfl⟩ : syracuseStep 2922581 = 34249) (by norm_num)
theorem B7793549 : Blo 2307435 7793549 := bstep (se 3 (by rfl) ⟨1461290, by rfl⟩ : syracuseStep 7793549 = 2922581) B2922581
theorem B5195699 : Blo 2307435 5195699 := bstep (se 1 (by rfl) ⟨3896774, by rfl⟩ : syracuseStep 5195699 = 7793549) B7793549
theorem B3463799 : Blo 2307435 3463799 := bstep (se 1 (by rfl) ⟨2597849, by rfl⟩ : syracuseStep 3463799 = 5195699) B5195699
theorem B2309199 : Blo 2307435 2309199 := bstep (se 1 (by rfl) ⟨1731899, by rfl⟩ : syracuseStep 2309199 = 3463799) B3463799
theorem B3463805 : Blo 2307435 3463805 := bbase (se 3 (by rfl) ⟨649463, by rfl⟩ : syracuseStep 3463805 = 1298927) (by norm_num)
theorem B2309203 : Blo 2307435 2309203 := bstep (se 1 (by rfl) ⟨1731902, by rfl⟩ : syracuseStep 2309203 = 3463805) B3463805
theorem B5195717 : Blo 2307435 5195717 := bbase (se 4 (by rfl) ⟨487098, by rfl⟩ : syracuseStep 5195717 = 974197) (by norm_num)
theorem B3463811 : Blo 2307435 3463811 := bstep (se 1 (by rfl) ⟨2597858, by rfl⟩ : syracuseStep 3463811 = 5195717) B5195717
theorem B2309207 : Blo 2307435 2309207 := bstep (se 1 (by rfl) ⟨1731905, by rfl⟩ : syracuseStep 2309207 = 3463811) B3463811
theorem B9863765 : Blo 2307435 9863765 := bbase (se 8 (by rfl) ⟨57795, by rfl⟩ : syracuseStep 9863765 = 115591) (by norm_num)
theorem B6575843 : Blo 2307435 6575843 := bstep (se 1 (by rfl) ⟨4931882, by rfl⟩ : syracuseStep 6575843 = 9863765) B9863765
theorem B4383895 : Blo 2307435 4383895 := bstep (se 1 (by rfl) ⟨3287921, by rfl⟩ : syracuseStep 4383895 = 6575843) B6575843
theorem B5845193 : Blo 2307435 5845193 := bstep (se 2 (by rfl) ⟨2191947, by rfl⟩ : syracuseStep 5845193 = 4383895) B4383895
theorem B3896795 : Blo 2307435 3896795 := bstep (se 1 (by rfl) ⟨2922596, by rfl⟩ : syracuseStep 3896795 = 5845193) B5845193
theorem B2597863 : Blo 2307435 2597863 := bstep (se 1 (by rfl) ⟨1948397, by rfl⟩ : syracuseStep 2597863 = 3896795) B3896795
theorem B3463817 : Blo 2307435 3463817 := bstep (se 2 (by rfl) ⟨1298931, by rfl⟩ : syracuseStep 3463817 = 2597863) B2597863
theorem B2309211 : Blo 2307435 2309211 := bstep (se 1 (by rfl) ⟨1731908, by rfl⟩ : syracuseStep 2309211 = 3463817) B3463817
theorem B11690405 : Blo 2307435 11690405 := bbase (se 4 (by rfl) ⟨1095975, by rfl⟩ : syracuseStep 11690405 = 2191951) (by norm_num)
theorem B7793603 : Blo 2307435 7793603 := bstep (se 1 (by rfl) ⟨5845202, by rfl⟩ : syracuseStep 7793603 = 11690405) B11690405
theorem B5195735 : Blo 2307435 5195735 := bstep (se 1 (by rfl) ⟨3896801, by rfl⟩ : syracuseStep 5195735 = 7793603) B7793603
theorem B3463823 : Blo 2307435 3463823 := bstep (se 1 (by rfl) ⟨2597867, by rfl⟩ : syracuseStep 3463823 = 5195735) B5195735
theorem B2309215 : Blo 2307435 2309215 := bstep (se 1 (by rfl) ⟨1731911, by rfl⟩ : syracuseStep 2309215 = 3463823) B3463823
theorem B3463829 : Blo 2307435 3463829 := bbase (se 6 (by rfl) ⟨81183, by rfl⟩ : syracuseStep 3463829 = 162367) (by norm_num)
theorem B2309219 : Blo 2307435 2309219 := bstep (se 1 (by rfl) ⟨1731914, by rfl⟩ : syracuseStep 2309219 = 3463829) B3463829
theorem B3120973 : Blo 2307435 3120973 := bbase (se 3 (by rfl) ⟨585182, by rfl⟩ : syracuseStep 3120973 = 1170365) (by norm_num)
theorem B16645189 : Blo 2307435 16645189 := bstep (se 4 (by rfl) ⟨1560486, by rfl⟩ : syracuseStep 16645189 = 3120973) B3120973
theorem B22193585 : Blo 2307435 22193585 := bstep (se 2 (by rfl) ⟨8322594, by rfl⟩ : syracuseStep 22193585 = 16645189) B16645189
theorem B14795723 : Blo 2307435 14795723 := bstep (se 1 (by rfl) ⟨11096792, by rfl⟩ : syracuseStep 14795723 = 22193585) B22193585
theorem B9863815 : Blo 2307435 9863815 := bstep (se 1 (by rfl) ⟨7397861, by rfl⟩ : syracuseStep 9863815 = 14795723) B14795723
theorem B13151753 : Blo 2307435 13151753 := bstep (se 2 (by rfl) ⟨4931907, by rfl⟩ : syracuseStep 13151753 = 9863815) B9863815
theorem B8767835 : Blo 2307435 8767835 := bstep (se 1 (by rfl) ⟨6575876, by rfl⟩ : syracuseStep 8767835 = 13151753) B13151753
theorem B5845223 : Blo 2307435 5845223 := bstep (se 1 (by rfl) ⟨4383917, by rfl⟩ : syracuseStep 5845223 = 8767835) B8767835
theorem B3896815 : Blo 2307435 3896815 := bstep (se 1 (by rfl) ⟨2922611, by rfl⟩ : syracuseStep 3896815 = 5845223) B5845223
theorem B5195753 : Blo 2307435 5195753 := bstep (se 2 (by rfl) ⟨1948407, by rfl⟩ : syracuseStep 5195753 = 3896815) B3896815
theorem B3463835 : Blo 2307435 3463835 := bstep (se 1 (by rfl) ⟨2597876, by rfl⟩ : syracuseStep 3463835 = 5195753) B5195753
theorem B2309223 : Blo 2307435 2309223 := bstep (se 1 (by rfl) ⟨1731917, by rfl⟩ : syracuseStep 2309223 = 3463835) B3463835
theorem B2597881 : Blo 2307435 2597881 := bbase (se 2 (by rfl) ⟨974205, by rfl⟩ : syracuseStep 2597881 = 1948411) (by norm_num)
theorem B3463841 : Blo 2307435 3463841 := bstep (se 2 (by rfl) ⟨1298940, by rfl⟩ : syracuseStep 3463841 = 2597881) B2597881
theorem B2309227 : Blo 2307435 2309227 := bstep (se 1 (by rfl) ⟨1731920, by rfl⟩ : syracuseStep 2309227 = 3463841) B3463841
theorem B11557253 : Blo 2307435 11557253 := bbase (se 4 (by rfl) ⟨1083492, by rfl⟩ : syracuseStep 11557253 = 2166985) (by norm_num)
theorem B30819341 : Blo 2307435 30819341 := bstep (se 3 (by rfl) ⟨5778626, by rfl⟩ : syracuseStep 30819341 = 11557253) B11557253
theorem B20546227 : Blo 2307435 20546227 := bstep (se 1 (by rfl) ⟨15409670, by rfl⟩ : syracuseStep 20546227 = 30819341) B30819341
theorem B109579877 : Blo 2307435 109579877 := bstep (se 4 (by rfl) ⟨10273113, by rfl⟩ : syracuseStep 109579877 = 20546227) B20546227
theorem B73053251 : Blo 2307435 73053251 := bstep (se 1 (by rfl) ⟨54789938, by rfl⟩ : syracuseStep 73053251 = 109579877) B109579877
theorem B48702167 : Blo 2307435 48702167 := bstep (se 1 (by rfl) ⟨36526625, by rfl⟩ : syracuseStep 48702167 = 73053251) B73053251
theorem B32468111 : Blo 2307435 32468111 := bstep (se 1 (by rfl) ⟨24351083, by rfl⟩ : syracuseStep 32468111 = 48702167) B48702167
theorem B21645407 : Blo 2307435 21645407 := bstep (se 1 (by rfl) ⟨16234055, by rfl⟩ : syracuseStep 21645407 = 32468111) B32468111
theorem B14430271 : Blo 2307435 14430271 := bstep (se 1 (by rfl) ⟨10822703, by rfl⟩ : syracuseStep 14430271 = 21645407) B21645407
theorem B19240361 : Blo 2307435 19240361 := bstep (se 2 (by rfl) ⟨7215135, by rfl⟩ : syracuseStep 19240361 = 14430271) B14430271
theorem B12826907 : Blo 2307435 12826907 := bstep (se 1 (by rfl) ⟨9620180, by rfl⟩ : syracuseStep 12826907 = 19240361) B19240361
theorem B8551271 : Blo 2307435 8551271 := bstep (se 1 (by rfl) ⟨6413453, by rfl⟩ : syracuseStep 8551271 = 12826907) B12826907
theorem B5700847 : Blo 2307435 5700847 := bstep (se 1 (by rfl) ⟨4275635, by rfl⟩ : syracuseStep 5700847 = 8551271) B8551271
theorem B7601129 : Blo 2307435 7601129 := bstep (se 2 (by rfl) ⟨2850423, by rfl⟩ : syracuseStep 7601129 = 5700847) B5700847
theorem B5067419 : Blo 2307435 5067419 := bstep (se 1 (by rfl) ⟨3800564, by rfl⟩ : syracuseStep 5067419 = 7601129) B7601129
theorem B13513117 : Blo 2307435 13513117 := bstep (se 3 (by rfl) ⟨2533709, by rfl⟩ : syracuseStep 13513117 = 5067419) B5067419
theorem B18017489 : Blo 2307435 18017489 := bstep (se 2 (by rfl) ⟨6756558, by rfl⟩ : syracuseStep 18017489 = 13513117) B13513117
theorem B12011659 : Blo 2307435 12011659 := bstep (se 1 (by rfl) ⟨9008744, by rfl⟩ : syracuseStep 12011659 = 18017489) B18017489
theorem B64062181 : Blo 2307435 64062181 := bstep (se 4 (by rfl) ⟨6005829, by rfl⟩ : syracuseStep 64062181 = 12011659) B12011659
theorem B341664965 : Blo 2307435 341664965 := bstep (se 4 (by rfl) ⟨32031090, by rfl⟩ : syracuseStep 341664965 = 64062181) B64062181
theorem B227776643 : Blo 2307435 227776643 := bstep (se 1 (by rfl) ⟨170832482, by rfl⟩ : syracuseStep 227776643 = 341664965) B341664965
theorem B151851095 : Blo 2307435 151851095 := bstep (se 1 (by rfl) ⟨113888321, by rfl⟩ : syracuseStep 151851095 = 227776643) B227776643
theorem B101234063 : Blo 2307435 101234063 := bstep (se 1 (by rfl) ⟨75925547, by rfl⟩ : syracuseStep 101234063 = 151851095) B151851095
theorem B67489375 : Blo 2307435 67489375 := bstep (se 1 (by rfl) ⟨50617031, by rfl⟩ : syracuseStep 67489375 = 101234063) B101234063
theorem B89985833 : Blo 2307435 89985833 := bstep (se 2 (by rfl) ⟨33744687, by rfl⟩ : syracuseStep 89985833 = 67489375) B67489375
theorem B59990555 : Blo 2307435 59990555 := bstep (se 1 (by rfl) ⟨44992916, by rfl⟩ : syracuseStep 59990555 = 89985833) B89985833
theorem B159974813 : Blo 2307435 159974813 := bstep (se 3 (by rfl) ⟨29995277, by rfl⟩ : syracuseStep 159974813 = 59990555) B59990555
theorem B106649875 : Blo 2307435 106649875 := bstep (se 1 (by rfl) ⟨79987406, by rfl⟩ : syracuseStep 106649875 = 159974813) B159974813
theorem B142199833 : Blo 2307435 142199833 := bstep (se 2 (by rfl) ⟨53324937, by rfl⟩ : syracuseStep 142199833 = 106649875) B106649875
theorem B189599777 : Blo 2307435 189599777 := bstep (se 2 (by rfl) ⟨71099916, by rfl⟩ : syracuseStep 189599777 = 142199833) B142199833
theorem B126399851 : Blo 2307435 126399851 := bstep (se 1 (by rfl) ⟨94799888, by rfl⟩ : syracuseStep 126399851 = 189599777) B189599777
theorem B84266567 : Blo 2307435 84266567 := bstep (se 1 (by rfl) ⟨63199925, by rfl⟩ : syracuseStep 84266567 = 126399851) B126399851
theorem B56177711 : Blo 2307435 56177711 := bstep (se 1 (by rfl) ⟨42133283, by rfl⟩ : syracuseStep 56177711 = 84266567) B84266567
theorem B37451807 : Blo 2307435 37451807 := bstep (se 1 (by rfl) ⟨28088855, by rfl⟩ : syracuseStep 37451807 = 56177711) B56177711
theorem B24967871 : Blo 2307435 24967871 := bstep (se 1 (by rfl) ⟨18725903, by rfl⟩ : syracuseStep 24967871 = 37451807) B37451807
theorem B16645247 : Blo 2307435 16645247 := bstep (se 1 (by rfl) ⟨12483935, by rfl⟩ : syracuseStep 16645247 = 24967871) B24967871
theorem B11096831 : Blo 2307435 11096831 := bstep (se 1 (by rfl) ⟨8322623, by rfl⟩ : syracuseStep 11096831 = 16645247) B16645247
theorem B7397887 : Blo 2307435 7397887 := bstep (se 1 (by rfl) ⟨5548415, by rfl⟩ : syracuseStep 7397887 = 11096831) B11096831
theorem B9863849 : Blo 2307435 9863849 := bstep (se 2 (by rfl) ⟨3698943, by rfl⟩ : syracuseStep 9863849 = 7397887) B7397887
theorem B6575899 : Blo 2307435 6575899 := bstep (se 1 (by rfl) ⟨4931924, by rfl⟩ : syracuseStep 6575899 = 9863849) B9863849
theorem B8767865 : Blo 2307435 8767865 := bstep (se 2 (by rfl) ⟨3287949, by rfl⟩ : syracuseStep 8767865 = 6575899) B6575899
theorem B5845243 : Blo 2307435 5845243 := bstep (se 1 (by rfl) ⟨4383932, by rfl⟩ : syracuseStep 5845243 = 8767865) B8767865
theorem B7793657 : Blo 2307435 7793657 := bstep (se 2 (by rfl) ⟨2922621, by rfl⟩ : syracuseStep 7793657 = 5845243) B5845243
theorem B5195771 : Blo 2307435 5195771 := bstep (se 1 (by rfl) ⟨3896828, by rfl⟩ : syracuseStep 5195771 = 7793657) B7793657
theorem B3463847 : Blo 2307435 3463847 := bstep (se 1 (by rfl) ⟨2597885, by rfl⟩ : syracuseStep 3463847 = 5195771) B5195771
theorem B2309231 : Blo 2307435 2309231 := bstep (se 1 (by rfl) ⟨1731923, by rfl⟩ : syracuseStep 2309231 = 3463847) B3463847
theorem B3463853 : Blo 2307435 3463853 := bbase (se 3 (by rfl) ⟨649472, by rfl⟩ : syracuseStep 3463853 = 1298945) (by norm_num)
theorem B2309235 : Blo 2307435 2309235 := bstep (se 1 (by rfl) ⟨1731926, by rfl⟩ : syracuseStep 2309235 = 3463853) B3463853
theorem B5195789 : Blo 2307435 5195789 := bbase (se 3 (by rfl) ⟨974210, by rfl⟩ : syracuseStep 5195789 = 1948421) (by norm_num)
theorem B3463859 : Blo 2307435 3463859 := bstep (se 1 (by rfl) ⟨2597894, by rfl⟩ : syracuseStep 3463859 = 5195789) B5195789
theorem B2309239 : Blo 2307435 2309239 := bstep (se 1 (by rfl) ⟨1731929, by rfl⟩ : syracuseStep 2309239 = 3463859) B3463859
theorem B2922637 : Blo 2307435 2922637 := bbase (se 3 (by rfl) ⟨547994, by rfl⟩ : syracuseStep 2922637 = 1095989) (by norm_num)
theorem B3896849 : Blo 2307435 3896849 := bstep (se 2 (by rfl) ⟨1461318, by rfl⟩ : syracuseStep 3896849 = 2922637) B2922637
theorem B2597899 : Blo 2307435 2597899 := bstep (se 1 (by rfl) ⟨1948424, by rfl⟩ : syracuseStep 2597899 = 3896849) B3896849
theorem B3463865 : Blo 2307435 3463865 := bstep (se 2 (by rfl) ⟨1298949, by rfl⟩ : syracuseStep 3463865 = 2597899) B2597899
theorem B2309243 : Blo 2307435 2309243 := bstep (se 1 (by rfl) ⟨1731932, by rfl⟩ : syracuseStep 2309243 = 3463865) B3463865
theorem B22193813 : Blo 2307435 22193813 := bbase (se 6 (by rfl) ⟨520167, by rfl⟩ : syracuseStep 22193813 = 1040335) (by norm_num)
theorem B14795875 : Blo 2307435 14795875 := bstep (se 1 (by rfl) ⟨11096906, by rfl⟩ : syracuseStep 14795875 = 22193813) B22193813
theorem B19727833 : Blo 2307435 19727833 := bstep (se 2 (by rfl) ⟨7397937, by rfl⟩ : syracuseStep 19727833 = 14795875) B14795875
theorem B26303777 : Blo 2307435 26303777 := bstep (se 2 (by rfl) ⟨9863916, by rfl⟩ : syracuseStep 26303777 = 19727833) B19727833
theorem B17535851 : Blo 2307435 17535851 := bstep (se 1 (by rfl) ⟨13151888, by rfl⟩ : syracuseStep 17535851 = 26303777) B26303777
theorem B11690567 : Blo 2307435 11690567 := bstep (se 1 (by rfl) ⟨8767925, by rfl⟩ : syracuseStep 11690567 = 17535851) B17535851
theorem B7793711 : Blo 2307435 7793711 := bstep (se 1 (by rfl) ⟨5845283, by rfl⟩ : syracuseStep 7793711 = 11690567) B11690567
theorem B5195807 : Blo 2307435 5195807 := bstep (se 1 (by rfl) ⟨3896855, by rfl⟩ : syracuseStep 5195807 = 7793711) B7793711
theorem B3463871 : Blo 2307435 3463871 := bstep (se 1 (by rfl) ⟨2597903, by rfl⟩ : syracuseStep 3463871 = 5195807) B5195807
theorem B2309247 : Blo 2307435 2309247 := bstep (se 1 (by rfl) ⟨1731935, by rfl⟩ : syracuseStep 2309247 = 3463871) B3463871
theorem B3463877 : Blo 2307435 3463877 := bbase (se 4 (by rfl) ⟨324738, by rfl⟩ : syracuseStep 3463877 = 649477) (by norm_num)
theorem B2309251 : Blo 2307435 2309251 := bstep (se 1 (by rfl) ⟨1731938, by rfl⟩ : syracuseStep 2309251 = 3463877) B3463877
theorem B3896869 : Blo 2307435 3896869 := bbase (se 4 (by rfl) ⟨365331, by rfl⟩ : syracuseStep 3896869 = 730663) (by norm_num)
theorem B5195825 : Blo 2307435 5195825 := bstep (se 2 (by rfl) ⟨1948434, by rfl⟩ : syracuseStep 5195825 = 3896869) B3896869
theorem B3463883 : Blo 2307435 3463883 := bstep (se 1 (by rfl) ⟨2597912, by rfl⟩ : syracuseStep 3463883 = 5195825) B5195825
theorem B2309255 : Blo 2307435 2309255 := bstep (se 1 (by rfl) ⟨1731941, by rfl⟩ : syracuseStep 2309255 = 3463883) B3463883
theorem B2597917 : Blo 2307435 2597917 := bbase (se 3 (by rfl) ⟨487109, by rfl⟩ : syracuseStep 2597917 = 974219) (by norm_num)
theorem B3463889 : Blo 2307435 3463889 := bstep (se 2 (by rfl) ⟨1298958, by rfl⟩ : syracuseStep 3463889 = 2597917) B2597917
theorem B2309259 : Blo 2307435 2309259 := bstep (se 1 (by rfl) ⟨1731944, by rfl⟩ : syracuseStep 2309259 = 3463889) B3463889
theorem B7793765 : Blo 2307435 7793765 := bbase (se 4 (by rfl) ⟨730665, by rfl⟩ : syracuseStep 7793765 = 1461331) (by norm_num)
theorem B5195843 : Blo 2307435 5195843 := bstep (se 1 (by rfl) ⟨3896882, by rfl⟩ : syracuseStep 5195843 = 7793765) B7793765
theorem B3463895 : Blo 2307435 3463895 := bstep (se 1 (by rfl) ⟨2597921, by rfl⟩ : syracuseStep 3463895 = 5195843) B5195843
theorem B2309263 : Blo 2307435 2309263 := bstep (se 1 (by rfl) ⟨1731947, by rfl⟩ : syracuseStep 2309263 = 3463895) B3463895
theorem B3463901 : Blo 2307435 3463901 := bbase (se 3 (by rfl) ⟨649481, by rfl⟩ : syracuseStep 3463901 = 1298963) (by norm_num)
theorem B2309267 : Blo 2307435 2309267 := bstep (se 1 (by rfl) ⟨1731950, by rfl⟩ : syracuseStep 2309267 = 3463901) B3463901
theorem B5195861 : Blo 2307435 5195861 := bbase (se 8 (by rfl) ⟨30444, by rfl⟩ : syracuseStep 5195861 = 60889) (by norm_num)
theorem B3463907 : Blo 2307435 3463907 := bstep (se 1 (by rfl) ⟨2597930, by rfl⟩ : syracuseStep 3463907 = 5195861) B5195861
theorem B2309271 : Blo 2307435 2309271 := bstep (se 1 (by rfl) ⟨1731953, by rfl⟩ : syracuseStep 2309271 = 3463907) B3463907
theorem B2774261 : Blo 2307435 2774261 := bbase (se 5 (by rfl) ⟨130043, by rfl⟩ : syracuseStep 2774261 = 260087) (by norm_num)
theorem B7398029 : Blo 2307435 7398029 := bstep (se 3 (by rfl) ⟨1387130, by rfl⟩ : syracuseStep 7398029 = 2774261) B2774261
theorem B4932019 : Blo 2307435 4932019 := bstep (se 1 (by rfl) ⟨3699014, by rfl⟩ : syracuseStep 4932019 = 7398029) B7398029
theorem B6576025 : Blo 2307435 6576025 := bstep (se 2 (by rfl) ⟨2466009, by rfl⟩ : syracuseStep 6576025 = 4932019) B4932019
theorem B8768033 : Blo 2307435 8768033 := bstep (se 2 (by rfl) ⟨3288012, by rfl⟩ : syracuseStep 8768033 = 6576025) B6576025
theorem B5845355 : Blo 2307435 5845355 := bstep (se 1 (by rfl) ⟨4384016, by rfl⟩ : syracuseStep 5845355 = 8768033) B8768033
theorem B3896903 : Blo 2307435 3896903 := bstep (se 1 (by rfl) ⟨2922677, by rfl⟩ : syracuseStep 3896903 = 5845355) B5845355
theorem B2597935 : Blo 2307435 2597935 := bstep (se 1 (by rfl) ⟨1948451, by rfl⟩ : syracuseStep 2597935 = 3896903) B3896903
theorem B3463913 : Blo 2307435 3463913 := bstep (se 2 (by rfl) ⟨1298967, by rfl⟩ : syracuseStep 3463913 = 2597935) B2597935
theorem B2309275 : Blo 2307435 2309275 := bstep (se 1 (by rfl) ⟨1731956, by rfl⟩ : syracuseStep 2309275 = 3463913) B3463913
theorem B15800309 : Blo 2307435 15800309 := bbase (se 5 (by rfl) ⟨740639, by rfl⟩ : syracuseStep 15800309 = 1481279) (by norm_num)
theorem B10533539 : Blo 2307435 10533539 := bstep (se 1 (by rfl) ⟨7900154, by rfl⟩ : syracuseStep 10533539 = 15800309) B15800309
theorem B7022359 : Blo 2307435 7022359 := bstep (se 1 (by rfl) ⟨5266769, by rfl⟩ : syracuseStep 7022359 = 10533539) B10533539
theorem B37452581 : Blo 2307435 37452581 := bstep (se 4 (by rfl) ⟨3511179, by rfl⟩ : syracuseStep 37452581 = 7022359) B7022359
theorem B24968387 : Blo 2307435 24968387 := bstep (se 1 (by rfl) ⟨18726290, by rfl⟩ : syracuseStep 24968387 = 37452581) B37452581
theorem B16645591 : Blo 2307435 16645591 := bstep (se 1 (by rfl) ⟨12484193, by rfl⟩ : syracuseStep 16645591 = 24968387) B24968387
theorem B22194121 : Blo 2307435 22194121 := bstep (se 2 (by rfl) ⟨8322795, by rfl⟩ : syracuseStep 22194121 = 16645591) B16645591
theorem B29592161 : Blo 2307435 29592161 := bstep (se 2 (by rfl) ⟨11097060, by rfl⟩ : syracuseStep 29592161 = 22194121) B22194121
theorem B19728107 : Blo 2307435 19728107 := bstep (se 1 (by rfl) ⟨14796080, by rfl⟩ : syracuseStep 19728107 = 29592161) B29592161
theorem B13152071 : Blo 2307435 13152071 := bstep (se 1 (by rfl) ⟨9864053, by rfl⟩ : syracuseStep 13152071 = 19728107) B19728107
theorem B8768047 : Blo 2307435 8768047 := bstep (se 1 (by rfl) ⟨6576035, by rfl⟩ : syracuseStep 8768047 = 13152071) B13152071
theorem B11690729 : Blo 2307435 11690729 := bstep (se 2 (by rfl) ⟨4384023, by rfl⟩ : syracuseStep 11690729 = 8768047) B8768047
theorem B7793819 : Blo 2307435 7793819 := bstep (se 1 (by rfl) ⟨5845364, by rfl⟩ : syracuseStep 7793819 = 11690729) B11690729
theorem B5195879 : Blo 2307435 5195879 := bstep (se 1 (by rfl) ⟨3896909, by rfl⟩ : syracuseStep 5195879 = 7793819) B7793819
theorem B3463919 : Blo 2307435 3463919 := bstep (se 1 (by rfl) ⟨2597939, by rfl⟩ : syracuseStep 3463919 = 5195879) B5195879
theorem B2309279 : Blo 2307435 2309279 := bstep (se 1 (by rfl) ⟨1731959, by rfl⟩ : syracuseStep 2309279 = 3463919) B3463919
theorem B3463925 : Blo 2307435 3463925 := bbase (se 5 (by rfl) ⟨162371, by rfl⟩ : syracuseStep 3463925 = 324743) (by norm_num)
theorem B2309283 : Blo 2307435 2309283 := bstep (se 1 (by rfl) ⟨1731962, by rfl⟩ : syracuseStep 2309283 = 3463925) B3463925
theorem B4161413 : Blo 2307435 4161413 := bbase (se 4 (by rfl) ⟨390132, by rfl⟩ : syracuseStep 4161413 = 780265) (by norm_num)
theorem B11097101 : Blo 2307435 11097101 := bstep (se 3 (by rfl) ⟨2080706, by rfl⟩ : syracuseStep 11097101 = 4161413) B4161413
theorem B7398067 : Blo 2307435 7398067 := bstep (se 1 (by rfl) ⟨5548550, by rfl⟩ : syracuseStep 7398067 = 11097101) B11097101
theorem B9864089 : Blo 2307435 9864089 := bstep (se 2 (by rfl) ⟨3699033, by rfl⟩ : syracuseStep 9864089 = 7398067) B7398067
theorem B6576059 : Blo 2307435 6576059 := bstep (se 1 (by rfl) ⟨4932044, by rfl⟩ : syracuseStep 6576059 = 9864089) B9864089
theorem B4384039 : Blo 2307435 4384039 := bstep (se 1 (by rfl) ⟨3288029, by rfl⟩ : syracuseStep 4384039 = 6576059) B6576059
theorem B5845385 : Blo 2307435 5845385 := bstep (se 2 (by rfl) ⟨2192019, by rfl⟩ : syracuseStep 5845385 = 4384039) B4384039
theorem B3896923 : Blo 2307435 3896923 := bstep (se 1 (by rfl) ⟨2922692, by rfl⟩ : syracuseStep 3896923 = 5845385) B5845385
theorem B5195897 : Blo 2307435 5195897 := bstep (se 2 (by rfl) ⟨1948461, by rfl⟩ : syracuseStep 5195897 = 3896923) B3896923
theorem B3463931 : Blo 2307435 3463931 := bstep (se 1 (by rfl) ⟨2597948, by rfl⟩ : syracuseStep 3463931 = 5195897) B5195897
theorem B2309287 : Blo 2307435 2309287 := bstep (se 1 (by rfl) ⟨1731965, by rfl⟩ : syracuseStep 2309287 = 3463931) B3463931
theorem B2597953 : Blo 2307435 2597953 := bbase (se 2 (by rfl) ⟨974232, by rfl⟩ : syracuseStep 2597953 = 1948465) (by norm_num)
theorem B3463937 : Blo 2307435 3463937 := bstep (se 2 (by rfl) ⟨1298976, by rfl⟩ : syracuseStep 3463937 = 2597953) B2597953
theorem B2309291 : Blo 2307435 2309291 := bstep (se 1 (by rfl) ⟨1731968, by rfl⟩ : syracuseStep 2309291 = 3463937) B3463937
theorem B5845405 : Blo 2307435 5845405 := bbase (se 3 (by rfl) ⟨1096013, by rfl⟩ : syracuseStep 5845405 = 2192027) (by norm_num)
theorem B7793873 : Blo 2307435 7793873 := bstep (se 2 (by rfl) ⟨2922702, by rfl⟩ : syracuseStep 7793873 = 5845405) B5845405
theorem B5195915 : Blo 2307435 5195915 := bstep (se 1 (by rfl) ⟨3896936, by rfl⟩ : syracuseStep 5195915 = 7793873) B7793873
theorem B3463943 : Blo 2307435 3463943 := bstep (se 1 (by rfl) ⟨2597957, by rfl⟩ : syracuseStep 3463943 = 5195915) B5195915
theorem B2309295 : Blo 2307435 2309295 := bstep (se 1 (by rfl) ⟨1731971, by rfl⟩ : syracuseStep 2309295 = 3463943) B3463943
theorem B3463949 : Blo 2307435 3463949 := bbase (se 3 (by rfl) ⟨649490, by rfl⟩ : syracuseStep 3463949 = 1298981) (by norm_num)
theorem B2309299 : Blo 2307435 2309299 := bstep (se 1 (by rfl) ⟨1731974, by rfl⟩ : syracuseStep 2309299 = 3463949) B3463949
theorem B5195933 : Blo 2307435 5195933 := bbase (se 3 (by rfl) ⟨974237, by rfl⟩ : syracuseStep 5195933 = 1948475) (by norm_num)
theorem B3463955 : Blo 2307435 3463955 := bstep (se 1 (by rfl) ⟨2597966, by rfl⟩ : syracuseStep 3463955 = 5195933) B5195933
theorem B2309303 : Blo 2307435 2309303 := bstep (se 1 (by rfl) ⟨1731977, by rfl⟩ : syracuseStep 2309303 = 3463955) B3463955
theorem B3896957 : Blo 2307435 3896957 := bbase (se 3 (by rfl) ⟨730679, by rfl⟩ : syracuseStep 3896957 = 1461359) (by norm_num)
theorem B2597971 : Blo 2307435 2597971 := bstep (se 1 (by rfl) ⟨1948478, by rfl⟩ : syracuseStep 2597971 = 3896957) B3896957
theorem B3463961 : Blo 2307435 3463961 := bstep (se 2 (by rfl) ⟨1298985, by rfl⟩ : syracuseStep 3463961 = 2597971) B2597971
theorem B2309307 : Blo 2307435 2309307 := bstep (se 1 (by rfl) ⟨1731980, by rfl⟩ : syracuseStep 2309307 = 3463961) B3463961
theorem B4393253 : Blo 2307435 4393253 := bbase (se 4 (by rfl) ⟨411867, by rfl⟩ : syracuseStep 4393253 = 823735) (by norm_num)
theorem B2928835 : Blo 2307435 2928835 := bstep (se 1 (by rfl) ⟨2196626, by rfl⟩ : syracuseStep 2928835 = 4393253) B4393253
theorem B3905113 : Blo 2307435 3905113 := bstep (se 2 (by rfl) ⟨1464417, by rfl⟩ : syracuseStep 3905113 = 2928835) B2928835
theorem B5206817 : Blo 2307435 5206817 := bstep (se 2 (by rfl) ⟨1952556, by rfl⟩ : syracuseStep 5206817 = 3905113) B3905113
theorem B3471211 : Blo 2307435 3471211 := bstep (se 1 (by rfl) ⟨2603408, by rfl⟩ : syracuseStep 3471211 = 5206817) B5206817
theorem B4628281 : Blo 2307435 4628281 := bstep (se 2 (by rfl) ⟨1735605, by rfl⟩ : syracuseStep 4628281 = 3471211) B3471211
theorem B6171041 : Blo 2307435 6171041 := bstep (se 2 (by rfl) ⟨2314140, by rfl⟩ : syracuseStep 6171041 = 4628281) B4628281
theorem B4114027 : Blo 2307435 4114027 := bstep (se 1 (by rfl) ⟨3085520, by rfl⟩ : syracuseStep 4114027 = 6171041) B6171041
theorem B5485369 : Blo 2307435 5485369 := bstep (se 2 (by rfl) ⟨2057013, by rfl⟩ : syracuseStep 5485369 = 4114027) B4114027
theorem B7313825 : Blo 2307435 7313825 := bstep (se 2 (by rfl) ⟨2742684, by rfl⟩ : syracuseStep 7313825 = 5485369) B5485369
theorem B4875883 : Blo 2307435 4875883 := bstep (se 1 (by rfl) ⟨3656912, by rfl⟩ : syracuseStep 4875883 = 7313825) B7313825
theorem B26004709 : Blo 2307435 26004709 := bstep (se 4 (by rfl) ⟨2437941, by rfl⟩ : syracuseStep 26004709 = 4875883) B4875883
theorem B34672945 : Blo 2307435 34672945 := bstep (se 2 (by rfl) ⟨13002354, by rfl⟩ : syracuseStep 34672945 = 26004709) B26004709
theorem B46230593 : Blo 2307435 46230593 := bstep (se 2 (by rfl) ⟨17336472, by rfl⟩ : syracuseStep 46230593 = 34672945) B34672945
theorem B493126325 : Blo 2307435 493126325 := bstep (se 5 (by rfl) ⟨23115296, by rfl⟩ : syracuseStep 493126325 = 46230593) B46230593
theorem B328750883 : Blo 2307435 328750883 := bstep (se 1 (by rfl) ⟨246563162, by rfl⟩ : syracuseStep 328750883 = 493126325) B493126325
theorem B219167255 : Blo 2307435 219167255 := bstep (se 1 (by rfl) ⟨164375441, by rfl⟩ : syracuseStep 219167255 = 328750883) B328750883
theorem B146111503 : Blo 2307435 146111503 := bstep (se 1 (by rfl) ⟨109583627, by rfl⟩ : syracuseStep 146111503 = 219167255) B219167255
theorem B3117045397 : Blo 2307435 3117045397 := bstep (se 6 (by rfl) ⟨73055751, by rfl⟩ : syracuseStep 3117045397 = 146111503) B146111503
theorem B4156060529 : Blo 2307435 4156060529 := bstep (se 2 (by rfl) ⟨1558522698, by rfl⟩ : syracuseStep 4156060529 = 3117045397) B3117045397
theorem B2770707019 : Blo 2307435 2770707019 := bstep (se 1 (by rfl) ⟨2078030264, by rfl⟩ : syracuseStep 2770707019 = 4156060529) B4156060529
theorem B3694276025 : Blo 2307435 3694276025 := bstep (se 2 (by rfl) ⟨1385353509, by rfl⟩ : syracuseStep 3694276025 = 2770707019) B2770707019
theorem B2462850683 : Blo 2307435 2462850683 := bstep (se 1 (by rfl) ⟨1847138012, by rfl⟩ : syracuseStep 2462850683 = 3694276025) B3694276025
theorem B1641900455 : Blo 2307435 1641900455 := bstep (se 1 (by rfl) ⟨1231425341, by rfl⟩ : syracuseStep 1641900455 = 2462850683) B2462850683
theorem B1094600303 : Blo 2307435 1094600303 := bstep (se 1 (by rfl) ⟨820950227, by rfl⟩ : syracuseStep 1094600303 = 1641900455) B1641900455
theorem B729733535 : Blo 2307435 729733535 := bstep (se 1 (by rfl) ⟨547300151, by rfl⟩ : syracuseStep 729733535 = 1094600303) B1094600303
theorem B486489023 : Blo 2307435 486489023 := bstep (se 1 (by rfl) ⟨364866767, by rfl⟩ : syracuseStep 486489023 = 729733535) B729733535
theorem B324326015 : Blo 2307435 324326015 := bstep (se 1 (by rfl) ⟨243244511, by rfl⟩ : syracuseStep 324326015 = 486489023) B486489023
theorem B216217343 : Blo 2307435 216217343 := bstep (se 1 (by rfl) ⟨162163007, by rfl⟩ : syracuseStep 216217343 = 324326015) B324326015
theorem B144144895 : Blo 2307435 144144895 := bstep (se 1 (by rfl) ⟨108108671, by rfl⟩ : syracuseStep 144144895 = 216217343) B216217343
theorem B192193193 : Blo 2307435 192193193 := bstep (se 2 (by rfl) ⟨72072447, by rfl⟩ : syracuseStep 192193193 = 144144895) B144144895
theorem B512515181 : Blo 2307435 512515181 := bstep (se 3 (by rfl) ⟨96096596, by rfl⟩ : syracuseStep 512515181 = 192193193) B192193193
theorem B341676787 : Blo 2307435 341676787 := bstep (se 1 (by rfl) ⟨256257590, by rfl⟩ : syracuseStep 341676787 = 512515181) B512515181
theorem B455569049 : Blo 2307435 455569049 := bstep (se 2 (by rfl) ⟨170838393, by rfl⟩ : syracuseStep 455569049 = 341676787) B341676787
theorem B303712699 : Blo 2307435 303712699 := bstep (se 1 (by rfl) ⟨227784524, by rfl⟩ : syracuseStep 303712699 = 455569049) B455569049
theorem B404950265 : Blo 2307435 404950265 := bstep (se 2 (by rfl) ⟨151856349, by rfl⟩ : syracuseStep 404950265 = 303712699) B303712699
theorem B269966843 : Blo 2307435 269966843 := bstep (se 1 (by rfl) ⟨202475132, by rfl⟩ : syracuseStep 269966843 = 404950265) B404950265
theorem B179977895 : Blo 2307435 179977895 := bstep (se 1 (by rfl) ⟨134983421, by rfl⟩ : syracuseStep 179977895 = 269966843) B269966843
theorem B119985263 : Blo 2307435 119985263 := bstep (se 1 (by rfl) ⟨89988947, by rfl⟩ : syracuseStep 119985263 = 179977895) B179977895
theorem B79990175 : Blo 2307435 79990175 := bstep (se 1 (by rfl) ⟨59992631, by rfl⟩ : syracuseStep 79990175 = 119985263) B119985263
theorem B53326783 : Blo 2307435 53326783 := bstep (se 1 (by rfl) ⟨39995087, by rfl⟩ : syracuseStep 53326783 = 79990175) B79990175
theorem B71102377 : Blo 2307435 71102377 := bstep (se 2 (by rfl) ⟨26663391, by rfl⟩ : syracuseStep 71102377 = 53326783) B53326783
theorem B94803169 : Blo 2307435 94803169 := bstep (se 2 (by rfl) ⟨35551188, by rfl⟩ : syracuseStep 94803169 = 71102377) B71102377
theorem B126404225 : Blo 2307435 126404225 := bstep (se 2 (by rfl) ⟨47401584, by rfl⟩ : syracuseStep 126404225 = 94803169) B94803169
theorem B84269483 : Blo 2307435 84269483 := bstep (se 1 (by rfl) ⟨63202112, by rfl⟩ : syracuseStep 84269483 = 126404225) B126404225
theorem B56179655 : Blo 2307435 56179655 := bstep (se 1 (by rfl) ⟨42134741, by rfl⟩ : syracuseStep 56179655 = 84269483) B84269483
theorem B37453103 : Blo 2307435 37453103 := bstep (se 1 (by rfl) ⟨28089827, by rfl⟩ : syracuseStep 37453103 = 56179655) B56179655
theorem B24968735 : Blo 2307435 24968735 := bstep (se 1 (by rfl) ⟨18726551, by rfl⟩ : syracuseStep 24968735 = 37453103) B37453103
theorem B16645823 : Blo 2307435 16645823 := bstep (se 1 (by rfl) ⟨12484367, by rfl⟩ : syracuseStep 16645823 = 24968735) B24968735
theorem B11097215 : Blo 2307435 11097215 := bstep (se 1 (by rfl) ⟨8322911, by rfl⟩ : syracuseStep 11097215 = 16645823) B16645823
theorem B7398143 : Blo 2307435 7398143 := bstep (se 1 (by rfl) ⟨5548607, by rfl⟩ : syracuseStep 7398143 = 11097215) B11097215
theorem B4932095 : Blo 2307435 4932095 := bstep (se 1 (by rfl) ⟨3699071, by rfl⟩ : syracuseStep 4932095 = 7398143) B7398143
theorem B13152253 : Blo 2307435 13152253 := bstep (se 3 (by rfl) ⟨2466047, by rfl⟩ : syracuseStep 13152253 = 4932095) B4932095
theorem B17536337 : Blo 2307435 17536337 := bstep (se 2 (by rfl) ⟨6576126, by rfl⟩ : syracuseStep 17536337 = 13152253) B13152253
theorem B11690891 : Blo 2307435 11690891 := bstep (se 1 (by rfl) ⟨8768168, by rfl⟩ : syracuseStep 11690891 = 17536337) B17536337
theorem B7793927 : Blo 2307435 7793927 := bstep (se 1 (by rfl) ⟨5845445, by rfl⟩ : syracuseStep 7793927 = 11690891) B11690891
theorem B5195951 : Blo 2307435 5195951 := bstep (se 1 (by rfl) ⟨3896963, by rfl⟩ : syracuseStep 5195951 = 7793927) B7793927
theorem B3463967 : Blo 2307435 3463967 := bstep (se 1 (by rfl) ⟨2597975, by rfl⟩ : syracuseStep 3463967 = 5195951) B5195951
theorem B2309311 : Blo 2307435 2309311 := bstep (se 1 (by rfl) ⟨1731983, by rfl⟩ : syracuseStep 2309311 = 3463967) B3463967
theorem B3463973 : Blo 2307435 3463973 := bbase (se 4 (by rfl) ⟨324747, by rfl⟩ : syracuseStep 3463973 = 649495) (by norm_num)
theorem B2309315 : Blo 2307435 2309315 := bstep (se 1 (by rfl) ⟨1731986, by rfl⟩ : syracuseStep 2309315 = 3463973) B3463973
theorem B2922733 : Blo 2307435 2922733 := bbase (se 3 (by rfl) ⟨548012, by rfl⟩ : syracuseStep 2922733 = 1096025) (by norm_num)
theorem B3896977 : Blo 2307435 3896977 := bstep (se 2 (by rfl) ⟨1461366, by rfl⟩ : syracuseStep 3896977 = 2922733) B2922733
theorem B5195969 : Blo 2307435 5195969 := bstep (se 2 (by rfl) ⟨1948488, by rfl⟩ : syracuseStep 5195969 = 3896977) B3896977
theorem B3463979 : Blo 2307435 3463979 := bstep (se 1 (by rfl) ⟨2597984, by rfl⟩ : syracuseStep 3463979 = 5195969) B5195969
theorem B2309319 : Blo 2307435 2309319 := bstep (se 1 (by rfl) ⟨1731989, by rfl⟩ : syracuseStep 2309319 = 3463979) B3463979
theorem B2597989 : Blo 2307435 2597989 := bbase (se 4 (by rfl) ⟨243561, by rfl⟩ : syracuseStep 2597989 = 487123) (by norm_num)
theorem B3463985 : Blo 2307435 3463985 := bstep (se 2 (by rfl) ⟨1298994, by rfl⟩ : syracuseStep 3463985 = 2597989) B2597989
theorem B2309323 : Blo 2307435 2309323 := bstep (se 1 (by rfl) ⟨1731992, by rfl⟩ : syracuseStep 2309323 = 3463985) B3463985
theorem B2466065 : Blo 2307435 2466065 := bbase (se 2 (by rfl) ⟨924774, by rfl⟩ : syracuseStep 2466065 = 1849549) (by norm_num)
theorem B6576173 : Blo 2307435 6576173 := bstep (se 3 (by rfl) ⟨1233032, by rfl⟩ : syracuseStep 6576173 = 2466065) B2466065
theorem B4384115 : Blo 2307435 4384115 := bstep (se 1 (by rfl) ⟨3288086, by rfl⟩ : syracuseStep 4384115 = 6576173) B6576173
theorem B2922743 : Blo 2307435 2922743 := bstep (se 1 (by rfl) ⟨2192057, by rfl⟩ : syracuseStep 2922743 = 4384115) B4384115
theorem B7793981 : Blo 2307435 7793981 := bstep (se 3 (by rfl) ⟨1461371, by rfl⟩ : syracuseStep 7793981 = 2922743) B2922743
theorem B5195987 : Blo 2307435 5195987 := bstep (se 1 (by rfl) ⟨3896990, by rfl⟩ : syracuseStep 5195987 = 7793981) B7793981
theorem B3463991 : Blo 2307435 3463991 := bstep (se 1 (by rfl) ⟨2597993, by rfl⟩ : syracuseStep 3463991 = 5195987) B5195987
theorem B2309327 : Blo 2307435 2309327 := bstep (se 1 (by rfl) ⟨1731995, by rfl⟩ : syracuseStep 2309327 = 3463991) B3463991
theorem B3463997 : Blo 2307435 3463997 := bbase (se 3 (by rfl) ⟨649499, by rfl⟩ : syracuseStep 3463997 = 1298999) (by norm_num)
theorem B2309331 : Blo 2307435 2309331 := bstep (se 1 (by rfl) ⟨1731998, by rfl⟩ : syracuseStep 2309331 = 3463997) B3463997
theorem B5196005 : Blo 2307435 5196005 := bbase (se 4 (by rfl) ⟨487125, by rfl⟩ : syracuseStep 5196005 = 974251) (by norm_num)
theorem B3464003 : Blo 2307435 3464003 := bstep (se 1 (by rfl) ⟨2598002, by rfl⟩ : syracuseStep 3464003 = 5196005) B5196005
theorem B2309335 : Blo 2307435 2309335 := bstep (se 1 (by rfl) ⟨1732001, by rfl⟩ : syracuseStep 2309335 = 3464003) B3464003
theorem B5845517 : Blo 2307435 5845517 := bbase (se 3 (by rfl) ⟨1096034, by rfl⟩ : syracuseStep 5845517 = 2192069) (by norm_num)
theorem B3897011 : Blo 2307435 3897011 := bstep (se 1 (by rfl) ⟨2922758, by rfl⟩ : syracuseStep 3897011 = 5845517) B5845517
theorem B2598007 : Blo 2307435 2598007 := bstep (se 1 (by rfl) ⟨1948505, by rfl⟩ : syracuseStep 2598007 = 3897011) B3897011
theorem B3464009 : Blo 2307435 3464009 := bstep (se 2 (by rfl) ⟨1299003, by rfl⟩ : syracuseStep 3464009 = 2598007) B2598007
theorem B2309339 : Blo 2307435 2309339 := bstep (se 1 (by rfl) ⟨1732004, by rfl⟩ : syracuseStep 2309339 = 3464009) B3464009
theorem B3288109 : Blo 2307435 3288109 := bbase (se 3 (by rfl) ⟨616520, by rfl⟩ : syracuseStep 3288109 = 1233041) (by norm_num)
theorem B4384145 : Blo 2307435 4384145 := bstep (se 2 (by rfl) ⟨1644054, by rfl⟩ : syracuseStep 4384145 = 3288109) B3288109
theorem B11691053 : Blo 2307435 11691053 := bstep (se 3 (by rfl) ⟨2192072, by rfl⟩ : syracuseStep 11691053 = 4384145) B4384145
theorem B7794035 : Blo 2307435 7794035 := bstep (se 1 (by rfl) ⟨5845526, by rfl⟩ : syracuseStep 7794035 = 11691053) B11691053
theorem B5196023 : Blo 2307435 5196023 := bstep (se 1 (by rfl) ⟨3897017, by rfl⟩ : syracuseStep 5196023 = 7794035) B7794035
theorem B3464015 : Blo 2307435 3464015 := bstep (se 1 (by rfl) ⟨2598011, by rfl⟩ : syracuseStep 3464015 = 5196023) B5196023
theorem B2309343 : Blo 2307435 2309343 := bstep (se 1 (by rfl) ⟨1732007, by rfl⟩ : syracuseStep 2309343 = 3464015) B3464015
theorem B3464021 : Blo 2307435 3464021 := bbase (se 9 (by rfl) ⟨10148, by rfl⟩ : syracuseStep 3464021 = 20297) (by norm_num)
theorem B2309347 : Blo 2307435 2309347 := bstep (se 1 (by rfl) ⟨1732010, by rfl⟩ : syracuseStep 2309347 = 3464021) B3464021
theorem B4932181 : Blo 2307435 4932181 := bbase (se 8 (by rfl) ⟨28899, by rfl⟩ : syracuseStep 4932181 = 57799) (by norm_num)
theorem B6576241 : Blo 2307435 6576241 := bstep (se 2 (by rfl) ⟨2466090, by rfl⟩ : syracuseStep 6576241 = 4932181) B4932181
theorem B8768321 : Blo 2307435 8768321 := bstep (se 2 (by rfl) ⟨3288120, by rfl⟩ : syracuseStep 8768321 = 6576241) B6576241
theorem B5845547 : Blo 2307435 5845547 := bstep (se 1 (by rfl) ⟨4384160, by rfl⟩ : syracuseStep 5845547 = 8768321) B8768321
theorem B3897031 : Blo 2307435 3897031 := bstep (se 1 (by rfl) ⟨2922773, by rfl⟩ : syracuseStep 3897031 = 5845547) B5845547
theorem B5196041 : Blo 2307435 5196041 := bstep (se 2 (by rfl) ⟨1948515, by rfl⟩ : syracuseStep 5196041 = 3897031) B3897031
theorem B3464027 : Blo 2307435 3464027 := bstep (se 1 (by rfl) ⟨2598020, by rfl⟩ : syracuseStep 3464027 = 5196041) B5196041
theorem B2309351 : Blo 2307435 2309351 := bstep (se 1 (by rfl) ⟨1732013, by rfl⟩ : syracuseStep 2309351 = 3464027) B3464027
theorem B2598025 : Blo 2307435 2598025 := bbase (se 2 (by rfl) ⟨974259, by rfl⟩ : syracuseStep 2598025 = 1948519) (by norm_num)
theorem B3464033 : Blo 2307435 3464033 := bstep (se 2 (by rfl) ⟨1299012, by rfl⟩ : syracuseStep 3464033 = 2598025) B2598025
theorem B2309355 : Blo 2307435 2309355 := bstep (se 1 (by rfl) ⟨1732016, by rfl⟩ : syracuseStep 2309355 = 3464033) B3464033
theorem B44389781 : Blo 2307435 44389781 := bbase (se 6 (by rfl) ⟨1040385, by rfl⟩ : syracuseStep 44389781 = 2080771) (by norm_num)
theorem B29593187 : Blo 2307435 29593187 := bstep (se 1 (by rfl) ⟨22194890, by rfl⟩ : syracuseStep 29593187 = 44389781) B44389781
theorem B19728791 : Blo 2307435 19728791 := bstep (se 1 (by rfl) ⟨14796593, by rfl⟩ : syracuseStep 19728791 = 29593187) B29593187
theorem B13152527 : Blo 2307435 13152527 := bstep (se 1 (by rfl) ⟨9864395, by rfl⟩ : syracuseStep 13152527 = 19728791) B19728791
theorem B8768351 : Blo 2307435 8768351 := bstep (se 1 (by rfl) ⟨6576263, by rfl⟩ : syracuseStep 8768351 = 13152527) B13152527
theorem B5845567 : Blo 2307435 5845567 := bstep (se 1 (by rfl) ⟨4384175, by rfl⟩ : syracuseStep 5845567 = 8768351) B8768351
theorem B7794089 : Blo 2307435 7794089 := bstep (se 2 (by rfl) ⟨2922783, by rfl⟩ : syracuseStep 7794089 = 5845567) B5845567
theorem B5196059 : Blo 2307435 5196059 := bstep (se 1 (by rfl) ⟨3897044, by rfl⟩ : syracuseStep 5196059 = 7794089) B7794089
theorem B3464039 : Blo 2307435 3464039 := bstep (se 1 (by rfl) ⟨2598029, by rfl⟩ : syracuseStep 3464039 = 5196059) B5196059
theorem B2309359 : Blo 2307435 2309359 := bstep (se 1 (by rfl) ⟨1732019, by rfl⟩ : syracuseStep 2309359 = 3464039) B3464039
theorem B3464045 : Blo 2307435 3464045 := bbase (se 3 (by rfl) ⟨649508, by rfl⟩ : syracuseStep 3464045 = 1299017) (by norm_num)
theorem B2309363 : Blo 2307435 2309363 := bstep (se 1 (by rfl) ⟨1732022, by rfl⟩ : syracuseStep 2309363 = 3464045) B3464045
theorem B5196077 : Blo 2307435 5196077 := bbase (se 3 (by rfl) ⟨974264, by rfl⟩ : syracuseStep 5196077 = 1948529) (by norm_num)
theorem B3464051 : Blo 2307435 3464051 := bstep (se 1 (by rfl) ⟨2598038, by rfl⟩ : syracuseStep 3464051 = 5196077) B5196077
theorem B2309367 : Blo 2307435 2309367 := bstep (se 1 (by rfl) ⟨1732025, by rfl⟩ : syracuseStep 2309367 = 3464051) B3464051
theorem B4161565 : Blo 2307435 4161565 := bbase (se 3 (by rfl) ⟨780293, by rfl⟩ : syracuseStep 4161565 = 1560587) (by norm_num)
theorem B5548753 : Blo 2307435 5548753 := bstep (se 2 (by rfl) ⟨2080782, by rfl⟩ : syracuseStep 5548753 = 4161565) B4161565
theorem B7398337 : Blo 2307435 7398337 := bstep (se 2 (by rfl) ⟨2774376, by rfl⟩ : syracuseStep 7398337 = 5548753) B5548753
theorem B9864449 : Blo 2307435 9864449 := bstep (se 2 (by rfl) ⟨3699168, by rfl⟩ : syracuseStep 9864449 = 7398337) B7398337
theorem B6576299 : Blo 2307435 6576299 := bstep (se 1 (by rfl) ⟨4932224, by rfl⟩ : syracuseStep 6576299 = 9864449) B9864449
theorem B4384199 : Blo 2307435 4384199 := bstep (se 1 (by rfl) ⟨3288149, by rfl⟩ : syracuseStep 4384199 = 6576299) B6576299
theorem B2922799 : Blo 2307435 2922799 := bstep (se 1 (by rfl) ⟨2192099, by rfl⟩ : syracuseStep 2922799 = 4384199) B4384199
theorem B3897065 : Blo 2307435 3897065 := bstep (se 2 (by rfl) ⟨1461399, by rfl⟩ : syracuseStep 3897065 = 2922799) B2922799
theorem B2598043 : Blo 2307435 2598043 := bstep (se 1 (by rfl) ⟨1948532, by rfl⟩ : syracuseStep 2598043 = 3897065) B3897065
theorem B3464057 : Blo 2307435 3464057 := bstep (se 2 (by rfl) ⟨1299021, by rfl⟩ : syracuseStep 3464057 = 2598043) B2598043
theorem B2309371 : Blo 2307435 2309371 := bstep (se 1 (by rfl) ⟨1732028, by rfl⟩ : syracuseStep 2309371 = 3464057) B3464057
theorem B33292565 : Blo 2307435 33292565 := bbase (se 6 (by rfl) ⟨780294, by rfl⟩ : syracuseStep 33292565 = 1560589) (by norm_num)
theorem B22195043 : Blo 2307435 22195043 := bstep (se 1 (by rfl) ⟨16646282, by rfl⟩ : syracuseStep 22195043 = 33292565) B33292565
theorem B14796695 : Blo 2307435 14796695 := bstep (se 1 (by rfl) ⟨11097521, by rfl⟩ : syracuseStep 14796695 = 22195043) B22195043
theorem B39457853 : Blo 2307435 39457853 := bstep (se 3 (by rfl) ⟨7398347, by rfl⟩ : syracuseStep 39457853 = 14796695) B14796695
theorem B26305235 : Blo 2307435 26305235 := bstep (se 1 (by rfl) ⟨19728926, by rfl⟩ : syracuseStep 26305235 = 39457853) B39457853
theorem B17536823 : Blo 2307435 17536823 := bstep (se 1 (by rfl) ⟨13152617, by rfl⟩ : syracuseStep 17536823 = 26305235) B26305235
theorem B11691215 : Blo 2307435 11691215 := bstep (se 1 (by rfl) ⟨8768411, by rfl⟩ : syracuseStep 11691215 = 17536823) B17536823
theorem B7794143 : Blo 2307435 7794143 := bstep (se 1 (by rfl) ⟨5845607, by rfl⟩ : syracuseStep 7794143 = 11691215) B11691215
theorem B5196095 : Blo 2307435 5196095 := bstep (se 1 (by rfl) ⟨3897071, by rfl⟩ : syracuseStep 5196095 = 7794143) B7794143
theorem B3464063 : Blo 2307435 3464063 := bstep (se 1 (by rfl) ⟨2598047, by rfl⟩ : syracuseStep 3464063 = 5196095) B5196095
theorem B2309375 : Blo 2307435 2309375 := bstep (se 1 (by rfl) ⟨1732031, by rfl⟩ : syracuseStep 2309375 = 3464063) B3464063
theorem B3464069 : Blo 2307435 3464069 := bbase (se 4 (by rfl) ⟨324756, by rfl⟩ : syracuseStep 3464069 = 649513) (by norm_num)
theorem B2309379 : Blo 2307435 2309379 := bstep (se 1 (by rfl) ⟨1732034, by rfl⟩ : syracuseStep 2309379 = 3464069) B3464069
theorem B3897085 : Blo 2307435 3897085 := bbase (se 3 (by rfl) ⟨730703, by rfl⟩ : syracuseStep 3897085 = 1461407) (by norm_num)
theorem B5196113 : Blo 2307435 5196113 := bstep (se 2 (by rfl) ⟨1948542, by rfl⟩ : syracuseStep 5196113 = 3897085) B3897085
theorem B3464075 : Blo 2307435 3464075 := bstep (se 1 (by rfl) ⟨2598056, by rfl⟩ : syracuseStep 3464075 = 5196113) B5196113
theorem B2309383 : Blo 2307435 2309383 := bstep (se 1 (by rfl) ⟨1732037, by rfl⟩ : syracuseStep 2309383 = 3464075) B3464075
theorem B2598061 : Blo 2307435 2598061 := bbase (se 3 (by rfl) ⟨487136, by rfl⟩ : syracuseStep 2598061 = 974273) (by norm_num)
theorem B3464081 : Blo 2307435 3464081 := bstep (se 2 (by rfl) ⟨1299030, by rfl⟩ : syracuseStep 3464081 = 2598061) B2598061
theorem B2309387 : Blo 2307435 2309387 := bstep (se 1 (by rfl) ⟨1732040, by rfl⟩ : syracuseStep 2309387 = 3464081) B3464081
theorem B7794197 : Blo 2307435 7794197 := bbase (se 6 (by rfl) ⟨182676, by rfl⟩ : syracuseStep 7794197 = 365353) (by norm_num)
theorem B5196131 : Blo 2307435 5196131 := bstep (se 1 (by rfl) ⟨3897098, by rfl⟩ : syracuseStep 5196131 = 7794197) B7794197
theorem B3464087 : Blo 2307435 3464087 := bstep (se 1 (by rfl) ⟨2598065, by rfl⟩ : syracuseStep 3464087 = 5196131) B5196131
theorem B2309391 : Blo 2307435 2309391 := bstep (se 1 (by rfl) ⟨1732043, by rfl⟩ : syracuseStep 2309391 = 3464087) B3464087
theorem B3464093 : Blo 2307435 3464093 := bbase (se 3 (by rfl) ⟨649517, by rfl⟩ : syracuseStep 3464093 = 1299035) (by norm_num)
theorem B2309395 : Blo 2307435 2309395 := bstep (se 1 (by rfl) ⟨1732046, by rfl⟩ : syracuseStep 2309395 = 3464093) B3464093
theorem B5196149 : Blo 2307435 5196149 := bbase (se 5 (by rfl) ⟨243569, by rfl⟩ : syracuseStep 5196149 = 487139) (by norm_num)
theorem B3464099 : Blo 2307435 3464099 := bstep (se 1 (by rfl) ⟨2598074, by rfl⟩ : syracuseStep 3464099 = 5196149) B5196149
theorem B2309399 : Blo 2307435 2309399 := bstep (se 1 (by rfl) ⟨1732049, by rfl⟩ : syracuseStep 2309399 = 3464099) B3464099
theorem B5548829 : Blo 2307435 5548829 := bbase (se 3 (by rfl) ⟨1040405, by rfl⟩ : syracuseStep 5548829 = 2080811) (by norm_num)
theorem B14796877 : Blo 2307435 14796877 := bstep (se 3 (by rfl) ⟨2774414, by rfl⟩ : syracuseStep 14796877 = 5548829) B5548829
theorem B19729169 : Blo 2307435 19729169 := bstep (se 2 (by rfl) ⟨7398438, by rfl⟩ : syracuseStep 19729169 = 14796877) B14796877
theorem B13152779 : Blo 2307435 13152779 := bstep (se 1 (by rfl) ⟨9864584, by rfl⟩ : syracuseStep 13152779 = 19729169) B19729169
theorem B8768519 : Blo 2307435 8768519 := bstep (se 1 (by rfl) ⟨6576389, by rfl⟩ : syracuseStep 8768519 = 13152779) B13152779
theorem B5845679 : Blo 2307435 5845679 := bstep (se 1 (by rfl) ⟨4384259, by rfl⟩ : syracuseStep 5845679 = 8768519) B8768519
theorem B3897119 : Blo 2307435 3897119 := bstep (se 1 (by rfl) ⟨2922839, by rfl⟩ : syracuseStep 3897119 = 5845679) B5845679
theorem B2598079 : Blo 2307435 2598079 := bstep (se 1 (by rfl) ⟨1948559, by rfl⟩ : syracuseStep 2598079 = 3897119) B3897119
theorem B3464105 : Blo 2307435 3464105 := bstep (se 2 (by rfl) ⟨1299039, by rfl⟩ : syracuseStep 3464105 = 2598079) B2598079
theorem B2309403 : Blo 2307435 2309403 := bstep (se 1 (by rfl) ⟨1732052, by rfl⟩ : syracuseStep 2309403 = 3464105) B3464105
theorem B8768533 : Blo 2307435 8768533 := bbase (se 6 (by rfl) ⟨205512, by rfl⟩ : syracuseStep 8768533 = 411025) (by norm_num)
theorem B11691377 : Blo 2307435 11691377 := bstep (se 2 (by rfl) ⟨4384266, by rfl⟩ : syracuseStep 11691377 = 8768533) B8768533
theorem B7794251 : Blo 2307435 7794251 := bstep (se 1 (by rfl) ⟨5845688, by rfl⟩ : syracuseStep 7794251 = 11691377) B11691377
theorem B5196167 : Blo 2307435 5196167 := bstep (se 1 (by rfl) ⟨3897125, by rfl⟩ : syracuseStep 5196167 = 7794251) B7794251
theorem B3464111 : Blo 2307435 3464111 := bstep (se 1 (by rfl) ⟨2598083, by rfl⟩ : syracuseStep 3464111 = 5196167) B5196167
theorem B2309407 : Blo 2307435 2309407 := bstep (se 1 (by rfl) ⟨1732055, by rfl⟩ : syracuseStep 2309407 = 3464111) B3464111
theorem B3464117 : Blo 2307435 3464117 := bbase (se 5 (by rfl) ⟨162380, by rfl⟩ : syracuseStep 3464117 = 324761) (by norm_num)
theorem B2309411 : Blo 2307435 2309411 := bstep (se 1 (by rfl) ⟨1732058, by rfl⟩ : syracuseStep 2309411 = 3464117) B3464117
theorem B5845709 : Blo 2307435 5845709 := bbase (se 3 (by rfl) ⟨1096070, by rfl⟩ : syracuseStep 5845709 = 2192141) (by norm_num)
theorem B3897139 : Blo 2307435 3897139 := bstep (se 1 (by rfl) ⟨2922854, by rfl⟩ : syracuseStep 3897139 = 5845709) B5845709
theorem B5196185 : Blo 2307435 5196185 := bstep (se 2 (by rfl) ⟨1948569, by rfl⟩ : syracuseStep 5196185 = 3897139) B3897139
theorem B3464123 : Blo 2307435 3464123 := bstep (se 1 (by rfl) ⟨2598092, by rfl⟩ : syracuseStep 3464123 = 5196185) B5196185
theorem B2309415 : Blo 2307435 2309415 := bstep (se 1 (by rfl) ⟨1732061, by rfl⟩ : syracuseStep 2309415 = 3464123) B3464123
theorem B2598097 : Blo 2307435 2598097 := bbase (se 2 (by rfl) ⟨974286, by rfl⟩ : syracuseStep 2598097 = 1948573) (by norm_num)
theorem B3464129 : Blo 2307435 3464129 := bstep (se 2 (by rfl) ⟨1299048, by rfl⟩ : syracuseStep 3464129 = 2598097) B2598097
theorem B2309419 : Blo 2307435 2309419 := bstep (se 1 (by rfl) ⟨1732064, by rfl⟩ : syracuseStep 2309419 = 3464129) B3464129
theorem B10020181 : Blo 2307435 10020181 := bbase (se 12 (by rfl) ⟨3669, by rfl⟩ : syracuseStep 10020181 = 7339) (by norm_num)
theorem B13360241 : Blo 2307435 13360241 := bstep (se 2 (by rfl) ⟨5010090, by rfl⟩ : syracuseStep 13360241 = 10020181) B10020181
theorem B35627309 : Blo 2307435 35627309 := bstep (se 3 (by rfl) ⟨6680120, by rfl⟩ : syracuseStep 35627309 = 13360241) B13360241
theorem B23751539 : Blo 2307435 23751539 := bstep (se 1 (by rfl) ⟨17813654, by rfl⟩ : syracuseStep 23751539 = 35627309) B35627309
theorem B15834359 : Blo 2307435 15834359 := bstep (se 1 (by rfl) ⟨11875769, by rfl⟩ : syracuseStep 15834359 = 23751539) B23751539
theorem B10556239 : Blo 2307435 10556239 := bstep (se 1 (by rfl) ⟨7917179, by rfl⟩ : syracuseStep 10556239 = 15834359) B15834359
theorem B14074985 : Blo 2307435 14074985 := bstep (se 2 (by rfl) ⟨5278119, by rfl⟩ : syracuseStep 14074985 = 10556239) B10556239
theorem B37533293 : Blo 2307435 37533293 := bstep (se 3 (by rfl) ⟨7037492, by rfl⟩ : syracuseStep 37533293 = 14074985) B14074985
theorem B25022195 : Blo 2307435 25022195 := bstep (se 1 (by rfl) ⟨18766646, by rfl⟩ : syracuseStep 25022195 = 37533293) B37533293
theorem B16681463 : Blo 2307435 16681463 := bstep (se 1 (by rfl) ⟨12511097, by rfl⟩ : syracuseStep 16681463 = 25022195) B25022195
theorem B11120975 : Blo 2307435 11120975 := bstep (se 1 (by rfl) ⟨8340731, by rfl⟩ : syracuseStep 11120975 = 16681463) B16681463
theorem B7413983 : Blo 2307435 7413983 := bstep (se 1 (by rfl) ⟨5560487, by rfl⟩ : syracuseStep 7413983 = 11120975) B11120975
theorem B4942655 : Blo 2307435 4942655 := bstep (se 1 (by rfl) ⟨3706991, by rfl⟩ : syracuseStep 4942655 = 7413983) B7413983
theorem B3295103 : Blo 2307435 3295103 := bstep (se 1 (by rfl) ⟨2471327, by rfl⟩ : syracuseStep 3295103 = 4942655) B4942655
theorem B35147765 : Blo 2307435 35147765 := bstep (se 5 (by rfl) ⟨1647551, by rfl⟩ : syracuseStep 35147765 = 3295103) B3295103
theorem B23431843 : Blo 2307435 23431843 := bstep (se 1 (by rfl) ⟨17573882, by rfl⟩ : syracuseStep 23431843 = 35147765) B35147765
theorem B31242457 : Blo 2307435 31242457 := bstep (se 2 (by rfl) ⟨11715921, by rfl⟩ : syracuseStep 31242457 = 23431843) B23431843
theorem B41656609 : Blo 2307435 41656609 := bstep (se 2 (by rfl) ⟨15621228, by rfl⟩ : syracuseStep 41656609 = 31242457) B31242457
theorem B55542145 : Blo 2307435 55542145 := bstep (se 2 (by rfl) ⟨20828304, by rfl⟩ : syracuseStep 55542145 = 41656609) B41656609
theorem B74056193 : Blo 2307435 74056193 := bstep (se 2 (by rfl) ⟨27771072, by rfl⟩ : syracuseStep 74056193 = 55542145) B55542145
theorem B49370795 : Blo 2307435 49370795 := bstep (se 1 (by rfl) ⟨37028096, by rfl⟩ : syracuseStep 49370795 = 74056193) B74056193
theorem B32913863 : Blo 2307435 32913863 := bstep (se 1 (by rfl) ⟨24685397, by rfl⟩ : syracuseStep 32913863 = 49370795) B49370795
theorem B21942575 : Blo 2307435 21942575 := bstep (se 1 (by rfl) ⟨16456931, by rfl⟩ : syracuseStep 21942575 = 32913863) B32913863
theorem B14628383 : Blo 2307435 14628383 := bstep (se 1 (by rfl) ⟨10971287, by rfl⟩ : syracuseStep 14628383 = 21942575) B21942575
theorem B9752255 : Blo 2307435 9752255 := bstep (se 1 (by rfl) ⟨7314191, by rfl⟩ : syracuseStep 9752255 = 14628383) B14628383
theorem B6501503 : Blo 2307435 6501503 := bstep (se 1 (by rfl) ⟨4876127, by rfl⟩ : syracuseStep 6501503 = 9752255) B9752255
theorem B4334335 : Blo 2307435 4334335 := bstep (se 1 (by rfl) ⟨3250751, by rfl⟩ : syracuseStep 4334335 = 6501503) B6501503
theorem B92465813 : Blo 2307435 92465813 := bstep (se 6 (by rfl) ⟨2167167, by rfl⟩ : syracuseStep 92465813 = 4334335) B4334335
theorem B61643875 : Blo 2307435 61643875 := bstep (se 1 (by rfl) ⟨46232906, by rfl⟩ : syracuseStep 61643875 = 92465813) B92465813
theorem B82191833 : Blo 2307435 82191833 := bstep (se 2 (by rfl) ⟨30821937, by rfl⟩ : syracuseStep 82191833 = 61643875) B61643875
theorem B54794555 : Blo 2307435 54794555 := bstep (se 1 (by rfl) ⟨41095916, by rfl⟩ : syracuseStep 54794555 = 82191833) B82191833
theorem B36529703 : Blo 2307435 36529703 := bstep (se 1 (by rfl) ⟨27397277, by rfl⟩ : syracuseStep 36529703 = 54794555) B54794555
theorem B24353135 : Blo 2307435 24353135 := bstep (se 1 (by rfl) ⟨18264851, by rfl⟩ : syracuseStep 24353135 = 36529703) B36529703
theorem B16235423 : Blo 2307435 16235423 := bstep (se 1 (by rfl) ⟨12176567, by rfl⟩ : syracuseStep 16235423 = 24353135) B24353135
theorem B10823615 : Blo 2307435 10823615 := bstep (se 1 (by rfl) ⟨8117711, by rfl⟩ : syracuseStep 10823615 = 16235423) B16235423
theorem B7215743 : Blo 2307435 7215743 := bstep (se 1 (by rfl) ⟨5411807, by rfl⟩ : syracuseStep 7215743 = 10823615) B10823615
theorem B4810495 : Blo 2307435 4810495 := bstep (se 1 (by rfl) ⟨3607871, by rfl⟩ : syracuseStep 4810495 = 7215743) B7215743
theorem B6413993 : Blo 2307435 6413993 := bstep (se 2 (by rfl) ⟨2405247, by rfl⟩ : syracuseStep 6413993 = 4810495) B4810495
theorem B4275995 : Blo 2307435 4275995 := bstep (se 1 (by rfl) ⟨3206996, by rfl⟩ : syracuseStep 4275995 = 6413993) B6413993
theorem B11402653 : Blo 2307435 11402653 := bstep (se 3 (by rfl) ⟨2137997, by rfl⟩ : syracuseStep 11402653 = 4275995) B4275995
theorem B15203537 : Blo 2307435 15203537 := bstep (se 2 (by rfl) ⟨5701326, by rfl⟩ : syracuseStep 15203537 = 11402653) B11402653
theorem B10135691 : Blo 2307435 10135691 := bstep (se 1 (by rfl) ⟨7601768, by rfl⟩ : syracuseStep 10135691 = 15203537) B15203537
theorem B6757127 : Blo 2307435 6757127 := bstep (se 1 (by rfl) ⟨5067845, by rfl⟩ : syracuseStep 6757127 = 10135691) B10135691
theorem B4504751 : Blo 2307435 4504751 := bstep (se 1 (by rfl) ⟨3378563, by rfl⟩ : syracuseStep 4504751 = 6757127) B6757127
theorem B3003167 : Blo 2307435 3003167 := bstep (se 1 (by rfl) ⟨2252375, by rfl⟩ : syracuseStep 3003167 = 4504751) B4504751
theorem B8008445 : Blo 2307435 8008445 := bstep (se 3 (by rfl) ⟨1501583, by rfl⟩ : syracuseStep 8008445 = 3003167) B3003167
theorem B5338963 : Blo 2307435 5338963 := bstep (se 1 (by rfl) ⟨4004222, by rfl⟩ : syracuseStep 5338963 = 8008445) B8008445
theorem B7118617 : Blo 2307435 7118617 := bstep (se 2 (by rfl) ⟨2669481, by rfl⟩ : syracuseStep 7118617 = 5338963) B5338963
theorem B9491489 : Blo 2307435 9491489 := bstep (se 2 (by rfl) ⟨3559308, by rfl⟩ : syracuseStep 9491489 = 7118617) B7118617
theorem B6327659 : Blo 2307435 6327659 := bstep (se 1 (by rfl) ⟨4745744, by rfl⟩ : syracuseStep 6327659 = 9491489) B9491489
theorem B4218439 : Blo 2307435 4218439 := bstep (se 1 (by rfl) ⟨3163829, by rfl⟩ : syracuseStep 4218439 = 6327659) B6327659
theorem B5624585 : Blo 2307435 5624585 := bstep (se 2 (by rfl) ⟨2109219, by rfl⟩ : syracuseStep 5624585 = 4218439) B4218439
theorem B3749723 : Blo 2307435 3749723 := bstep (se 1 (by rfl) ⟨2812292, by rfl⟩ : syracuseStep 3749723 = 5624585) B5624585
theorem B2499815 : Blo 2307435 2499815 := bstep (se 1 (by rfl) ⟨1874861, by rfl⟩ : syracuseStep 2499815 = 3749723) B3749723
theorem B6666173 : Blo 2307435 6666173 := bstep (se 3 (by rfl) ⟨1249907, by rfl⟩ : syracuseStep 6666173 = 2499815) B2499815
theorem B4444115 : Blo 2307435 4444115 := bstep (se 1 (by rfl) ⟨3333086, by rfl⟩ : syracuseStep 4444115 = 6666173) B6666173
theorem B47403893 : Blo 2307435 47403893 := bstep (se 5 (by rfl) ⟨2222057, by rfl⟩ : syracuseStep 47403893 = 4444115) B4444115
theorem B31602595 : Blo 2307435 31602595 := bstep (se 1 (by rfl) ⟨23701946, by rfl⟩ : syracuseStep 31602595 = 47403893) B47403893
theorem B42136793 : Blo 2307435 42136793 := bstep (se 2 (by rfl) ⟨15801297, by rfl⟩ : syracuseStep 42136793 = 31602595) B31602595
theorem B28091195 : Blo 2307435 28091195 := bstep (se 1 (by rfl) ⟨21068396, by rfl⟩ : syracuseStep 28091195 = 42136793) B42136793
theorem B18727463 : Blo 2307435 18727463 := bstep (se 1 (by rfl) ⟨14045597, by rfl⟩ : syracuseStep 18727463 = 28091195) B28091195
theorem B12484975 : Blo 2307435 12484975 := bstep (se 1 (by rfl) ⟨9363731, by rfl⟩ : syracuseStep 12484975 = 18727463) B18727463
theorem B16646633 : Blo 2307435 16646633 := bstep (se 2 (by rfl) ⟨6242487, by rfl⟩ : syracuseStep 16646633 = 12484975) B12484975
theorem B11097755 : Blo 2307435 11097755 := bstep (se 1 (by rfl) ⟨8323316, by rfl⟩ : syracuseStep 11097755 = 16646633) B16646633
theorem B7398503 : Blo 2307435 7398503 := bstep (se 1 (by rfl) ⟨5548877, by rfl⟩ : syracuseStep 7398503 = 11097755) B11097755
theorem B4932335 : Blo 2307435 4932335 := bstep (se 1 (by rfl) ⟨3699251, by rfl⟩ : syracuseStep 4932335 = 7398503) B7398503
theorem B3288223 : Blo 2307435 3288223 := bstep (se 1 (by rfl) ⟨2466167, by rfl⟩ : syracuseStep 3288223 = 4932335) B4932335
theorem B4384297 : Blo 2307435 4384297 := bstep (se 2 (by rfl) ⟨1644111, by rfl⟩ : syracuseStep 4384297 = 3288223) B3288223
theorem B5845729 : Blo 2307435 5845729 := bstep (se 2 (by rfl) ⟨2192148, by rfl⟩ : syracuseStep 5845729 = 4384297) B4384297
theorem B7794305 : Blo 2307435 7794305 := bstep (se 2 (by rfl) ⟨2922864, by rfl⟩ : syracuseStep 7794305 = 5845729) B5845729
theorem B5196203 : Blo 2307435 5196203 := bstep (se 1 (by rfl) ⟨3897152, by rfl⟩ : syracuseStep 5196203 = 7794305) B7794305
theorem B3464135 : Blo 2307435 3464135 := bstep (se 1 (by rfl) ⟨2598101, by rfl⟩ : syracuseStep 3464135 = 5196203) B5196203
theorem B2309423 : Blo 2307435 2309423 := bstep (se 1 (by rfl) ⟨1732067, by rfl⟩ : syracuseStep 2309423 = 3464135) B3464135
theorem B3464141 : Blo 2307435 3464141 := bbase (se 3 (by rfl) ⟨649526, by rfl⟩ : syracuseStep 3464141 = 1299053) (by norm_num)
theorem B2309427 : Blo 2307435 2309427 := bstep (se 1 (by rfl) ⟨1732070, by rfl⟩ : syracuseStep 2309427 = 3464141) B3464141
theorem B5196221 : Blo 2307435 5196221 := bbase (se 3 (by rfl) ⟨974291, by rfl⟩ : syracuseStep 5196221 = 1948583) (by norm_num)
theorem B3464147 : Blo 2307435 3464147 := bstep (se 1 (by rfl) ⟨2598110, by rfl⟩ : syracuseStep 3464147 = 5196221) B5196221
theorem B2309431 : Blo 2307435 2309431 := bstep (se 1 (by rfl) ⟨1732073, by rfl⟩ : syracuseStep 2309431 = 3464147) B3464147
theorem B3897173 : Blo 2307435 3897173 := bbase (se 9 (by rfl) ⟨11417, by rfl⟩ : syracuseStep 3897173 = 22835) (by norm_num)
theorem B2598115 : Blo 2307435 2598115 := bstep (se 1 (by rfl) ⟨1948586, by rfl⟩ : syracuseStep 2598115 = 3897173) B3897173
theorem B3464153 : Blo 2307435 3464153 := bstep (se 2 (by rfl) ⟨1299057, by rfl⟩ : syracuseStep 3464153 = 2598115) B2598115
theorem B2309435 : Blo 2307435 2309435 := bstep (se 1 (by rfl) ⟨1732076, by rfl⟩ : syracuseStep 2309435 = 3464153) B3464153
theorem C0 (j : ℕ) (h1 : 576858 ≤ j) (h2 : j ≤ 577358) : Blo 2307435 (4 * j + 3) := by
  interval_cases j
  · exact B2307435
  · exact B2307439
  · exact B2307443
  · exact B2307447
  · exact B2307451
  · exact B2307455
  · exact B2307459
  · exact B2307463
  · exact B2307467
  · exact B2307471
  · exact B2307475
  · exact B2307479
  · exact B2307483
  · exact B2307487
  · exact B2307491
  · exact B2307495
  · exact B2307499
  · exact B2307503
  · exact B2307507
  · exact B2307511
  · exact B2307515
  · exact B2307519
  · exact B2307523
  · exact B2307527
  · exact B2307531
  · exact B2307535
  · exact B2307539
  · exact B2307543
  · exact B2307547
  · exact B2307551
  · exact B2307555
  · exact B2307559
  · exact B2307563
  · exact B2307567
  · exact B2307571
  · exact B2307575
  · exact B2307579
  · exact B2307583
  · exact B2307587
  · exact B2307591
  · exact B2307595
  · exact B2307599
  · exact B2307603
  · exact B2307607
  · exact B2307611
  · exact B2307615
  · exact B2307619
  · exact B2307623
  · exact B2307627
  · exact B2307631
  · exact B2307635
  · exact B2307639
  · exact B2307643
  · exact B2307647
  · exact B2307651
  · exact B2307655
  · exact B2307659
  · exact B2307663
  · exact B2307667
  · exact B2307671
  · exact B2307675
  · exact B2307679
  · exact B2307683
  · exact B2307687
  · exact B2307691
  · exact B2307695
  · exact B2307699
  · exact B2307703
  · exact B2307707
  · exact B2307711
  · exact B2307715
  · exact B2307719
  · exact B2307723
  · exact B2307727
  · exact B2307731
  · exact B2307735
  · exact B2307739
  · exact B2307743
  · exact B2307747
  · exact B2307751
  · exact B2307755
  · exact B2307759
  · exact B2307763
  · exact B2307767
  · exact B2307771
  · exact B2307775
  · exact B2307779
  · exact B2307783
  · exact B2307787
  · exact B2307791
  · exact B2307795
  · exact B2307799
  · exact B2307803
  · exact B2307807
  · exact B2307811
  · exact B2307815
  · exact B2307819
  · exact B2307823
  · exact B2307827
  · exact B2307831
  · exact B2307835
  · exact B2307839
  · exact B2307843
  · exact B2307847
  · exact B2307851
  · exact B2307855
  · exact B2307859
  · exact B2307863
  · exact B2307867
  · exact B2307871
  · exact B2307875
  · exact B2307879
  · exact B2307883
  · exact B2307887
  · exact B2307891
  · exact B2307895
  · exact B2307899
  · exact B2307903
  · exact B2307907
  · exact B2307911
  · exact B2307915
  · exact B2307919
  · exact B2307923
  · exact B2307927
  · exact B2307931
  · exact B2307935
  · exact B2307939
  · exact B2307943
  · exact B2307947
  · exact B2307951
  · exact B2307955
  · exact B2307959
  · exact B2307963
  · exact B2307967
  · exact B2307971
  · exact B2307975
  · exact B2307979
  · exact B2307983
  · exact B2307987
  · exact B2307991
  · exact B2307995
  · exact B2307999
  · exact B2308003
  · exact B2308007
  · exact B2308011
  · exact B2308015
  · exact B2308019
  · exact B2308023
  · exact B2308027
  · exact B2308031
  · exact B2308035
  · exact B2308039
  · exact B2308043
  · exact B2308047
  · exact B2308051
  · exact B2308055
  · exact B2308059
  · exact B2308063
  · exact B2308067
  · exact B2308071
  · exact B2308075
  · exact B2308079
  · exact B2308083
  · exact B2308087
  · exact B2308091
  · exact B2308095
  · exact B2308099
  · exact B2308103
  · exact B2308107
  · exact B2308111
  · exact B2308115
  · exact B2308119
  · exact B2308123
  · exact B2308127
  · exact B2308131
  · exact B2308135
  · exact B2308139
  · exact B2308143
  · exact B2308147
  · exact B2308151
  · exact B2308155
  · exact B2308159
  · exact B2308163
  · exact B2308167
  · exact B2308171
  · exact B2308175
  · exact B2308179
  · exact B2308183
  · exact B2308187
  · exact B2308191
  · exact B2308195
  · exact B2308199
  · exact B2308203
  · exact B2308207
  · exact B2308211
  · exact B2308215
  · exact B2308219
  · exact B2308223
  · exact B2308227
  · exact B2308231
  · exact B2308235
  · exact B2308239
  · exact B2308243
  · exact B2308247
  · exact B2308251
  · exact B2308255
  · exact B2308259
  · exact B2308263
  · exact B2308267
  · exact B2308271
  · exact B2308275
  · exact B2308279
  · exact B2308283
  · exact B2308287
  · exact B2308291
  · exact B2308295
  · exact B2308299
  · exact B2308303
  · exact B2308307
  · exact B2308311
  · exact B2308315
  · exact B2308319
  · exact B2308323
  · exact B2308327
  · exact B2308331
  · exact B2308335
  · exact B2308339
  · exact B2308343
  · exact B2308347
  · exact B2308351
  · exact B2308355
  · exact B2308359
  · exact B2308363
  · exact B2308367
  · exact B2308371
  · exact B2308375
  · exact B2308379
  · exact B2308383
  · exact B2308387
  · exact B2308391
  · exact B2308395
  · exact B2308399
  · exact B2308403
  · exact B2308407
  · exact B2308411
  · exact B2308415
  · exact B2308419
  · exact B2308423
  · exact B2308427
  · exact B2308431
  · exact B2308435
  · exact B2308439
  · exact B2308443
  · exact B2308447
  · exact B2308451
  · exact B2308455
  · exact B2308459
  · exact B2308463
  · exact B2308467
  · exact B2308471
  · exact B2308475
  · exact B2308479
  · exact B2308483
  · exact B2308487
  · exact B2308491
  · exact B2308495
  · exact B2308499
  · exact B2308503
  · exact B2308507
  · exact B2308511
  · exact B2308515
  · exact B2308519
  · exact B2308523
  · exact B2308527
  · exact B2308531
  · exact B2308535
  · exact B2308539
  · exact B2308543
  · exact B2308547
  · exact B2308551
  · exact B2308555
  · exact B2308559
  · exact B2308563
  · exact B2308567
  · exact B2308571
  · exact B2308575
  · exact B2308579
  · exact B2308583
  · exact B2308587
  · exact B2308591
  · exact B2308595
  · exact B2308599
  · exact B2308603
  · exact B2308607
  · exact B2308611
  · exact B2308615
  · exact B2308619
  · exact B2308623
  · exact B2308627
  · exact B2308631
  · exact B2308635
  · exact B2308639
  · exact B2308643
  · exact B2308647
  · exact B2308651
  · exact B2308655
  · exact B2308659
  · exact B2308663
  · exact B2308667
  · exact B2308671
  · exact B2308675
  · exact B2308679
  · exact B2308683
  · exact B2308687
  · exact B2308691
  · exact B2308695
  · exact B2308699
  · exact B2308703
  · exact B2308707
  · exact B2308711
  · exact B2308715
  · exact B2308719
  · exact B2308723
  · exact B2308727
  · exact B2308731
  · exact B2308735
  · exact B2308739
  · exact B2308743
  · exact B2308747
  · exact B2308751
  · exact B2308755
  · exact B2308759
  · exact B2308763
  · exact B2308767
  · exact B2308771
  · exact B2308775
  · exact B2308779
  · exact B2308783
  · exact B2308787
  · exact B2308791
  · exact B2308795
  · exact B2308799
  · exact B2308803
  · exact B2308807
  · exact B2308811
  · exact B2308815
  · exact B2308819
  · exact B2308823
  · exact B2308827
  · exact B2308831
  · exact B2308835
  · exact B2308839
  · exact B2308843
  · exact B2308847
  · exact B2308851
  · exact B2308855
  · exact B2308859
  · exact B2308863
  · exact B2308867
  · exact B2308871
  · exact B2308875
  · exact B2308879
  · exact B2308883
  · exact B2308887
  · exact B2308891
  · exact B2308895
  · exact B2308899
  · exact B2308903
  · exact B2308907
  · exact B2308911
  · exact B2308915
  · exact B2308919
  · exact B2308923
  · exact B2308927
  · exact B2308931
  · exact B2308935
  · exact B2308939
  · exact B2308943
  · exact B2308947
  · exact B2308951
  · exact B2308955
  · exact B2308959
  · exact B2308963
  · exact B2308967
  · exact B2308971
  · exact B2308975
  · exact B2308979
  · exact B2308983
  · exact B2308987
  · exact B2308991
  · exact B2308995
  · exact B2308999
  · exact B2309003
  · exact B2309007
  · exact B2309011
  · exact B2309015
  · exact B2309019
  · exact B2309023
  · exact B2309027
  · exact B2309031
  · exact B2309035
  · exact B2309039
  · exact B2309043
  · exact B2309047
  · exact B2309051
  · exact B2309055
  · exact B2309059
  · exact B2309063
  · exact B2309067
  · exact B2309071
  · exact B2309075
  · exact B2309079
  · exact B2309083
  · exact B2309087
  · exact B2309091
  · exact B2309095
  · exact B2309099
  · exact B2309103
  · exact B2309107
  · exact B2309111
  · exact B2309115
  · exact B2309119
  · exact B2309123
  · exact B2309127
  · exact B2309131
  · exact B2309135
  · exact B2309139
  · exact B2309143
  · exact B2309147
  · exact B2309151
  · exact B2309155
  · exact B2309159
  · exact B2309163
  · exact B2309167
  · exact B2309171
  · exact B2309175
  · exact B2309179
  · exact B2309183
  · exact B2309187
  · exact B2309191
  · exact B2309195
  · exact B2309199
  · exact B2309203
  · exact B2309207
  · exact B2309211
  · exact B2309215
  · exact B2309219
  · exact B2309223
  · exact B2309227
  · exact B2309231
  · exact B2309235
  · exact B2309239
  · exact B2309243
  · exact B2309247
  · exact B2309251
  · exact B2309255
  · exact B2309259
  · exact B2309263
  · exact B2309267
  · exact B2309271
  · exact B2309275
  · exact B2309279
  · exact B2309283
  · exact B2309287
  · exact B2309291
  · exact B2309295
  · exact B2309299
  · exact B2309303
  · exact B2309307
  · exact B2309311
  · exact B2309315
  · exact B2309319
  · exact B2309323
  · exact B2309327
  · exact B2309331
  · exact B2309335
  · exact B2309339
  · exact B2309343
  · exact B2309347
  · exact B2309351
  · exact B2309355
  · exact B2309359
  · exact B2309363
  · exact B2309367
  · exact B2309371
  · exact B2309375
  · exact B2309379
  · exact B2309383
  · exact B2309387
  · exact B2309391
  · exact B2309395
  · exact B2309399
  · exact B2309403
  · exact B2309407
  · exact B2309411
  · exact B2309415
  · exact B2309419
  · exact B2309423
  · exact B2309427
  · exact B2309431
  · exact B2309435
theorem solution (m : ℕ) (hlo : 2307435 ≤ m) (hhi : m ≤ 2309435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 576858 ≤ j := by omega
    have hj2 : j ≤ 577358 := by omega
    have hb : Blo 2307435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
