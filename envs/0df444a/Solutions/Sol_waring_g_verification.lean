-- Prove2me | solution 1 for waring_g_verification
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T07:26:27.173961+00:00
-- url     : https://prove2.me/submissions/0c59e057-b2c3-48e1-82eb-f33e226ace27

-- Ported from ryanshin accepted submission 0ebe04d2-3b53-4ca8-b1e9-c5e62b5553ef.
import Mathlib

/-!
Every natural number is a sum of 19 cubes (nonnegative).

Strategy.
* `eight_cubes`: for `m ≤ z^2`, `8 z^3 + 6 z m` is a sum of 8 cubes
  (four squares theorem and `(z+x)^3 + (z-x)^3 = 2 z^3 + 6 z x^2`).
* `frob`: every `M` with `z^2 + z ≤ M ≤ 2z^3 + 2z^2 + 4z + 1` is `z m₁ + (z+1) m₂`
  with `m₁ ≤ z^2`, `m₂ ≤ (z+1)^2`.
* `cover`: for `L z ≤ n ≤ U z` the number `n + u^3` is a sum of 19 cubes, where
  `L z = 16 z^3 + 30 z^2 + 30 z + 133` and `U z = 28 z^3 + 36 z^2 + 48 z + 14`.
* `small`: every `n < 2000` is a sum of 18 cubes (fixed-denomination decomposition).
* the intervals `[L z, U z]` overlap for `z ≥ 6`; the remaining range `[2000, 4849)` is
  covered by `z = 4, 5` together with the shifts `u = 8` and `u = 6`.
-/

lemma eight_cubes (z m : ℕ) (hm : m ≤ z ^ 2) :
    ∃ x1 x2 x3 x4 x5 x6 x7 x8 : ℕ,
      8 * z ^ 3 + 6 * z * m
        = x1 ^ 3 + x2 ^ 3 + x3 ^ 3 + x4 ^ 3 + x5 ^ 3 + x6 ^ 3 + x7 ^ 3 + x8 ^ 3 := by
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares m
  have ha : a ≤ z := by nlinarith
  have hb : b ≤ z := by nlinarith
  have hc : c ≤ z := by nlinarith
  have hd : d ≤ z := by nlinarith
  refine ⟨z + a, z - a, z + b, z - b, z + c, z - c, z + d, z - d, ?_⟩
  subst habcd
  zify [ha, hb, hc, hd]
  ring

lemma frob1 (z M : ℕ) (hz : 1 ≤ z) (h1 : z ^ 2 + z ≤ M) (h2 : M ≤ (z + 1) ^ 3 + z) :
    ∃ m1 m2 : ℕ, m1 ≤ z ∧ m2 ≤ (z + 1) ^ 2 ∧ M = z * m1 + (z + 1) * m2 := by
  obtain ⟨q, r, hM, hr⟩ : ∃ q r, M = (z + 1) * q + r ∧ r < z + 1 :=
    ⟨M / (z + 1), M % (z + 1), (Nat.div_add_mod M (z + 1)).symm, Nat.mod_lt _ (by omega)⟩
  have hqz : z ≤ q := by
    by_contra hcon
    push_neg at hcon
    have : (z + 1) * (q + 1) ≤ (z + 1) * z := Nat.mul_le_mul_left _ hcon
    nlinarith
  have hq2 : q ≤ (z + 1) ^ 2 := by
    by_contra hcon
    push_neg at hcon
    have : (z + 1) * ((z + 1) ^ 2 + 1) ≤ (z + 1) * q := Nat.mul_le_mul_left _ hcon
    nlinarith
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · exact ⟨0, q, by omega, hq2, by rw [hM, h0]; ring⟩
  · refine ⟨z + 1 - r, q + r - z, by omega, by omega, ?_⟩
    obtain ⟨s, rfl⟩ : ∃ s, z = r + s := ⟨z - r, by omega⟩
    obtain ⟨q', rfl⟩ : ∃ q', q = r + s + q' := ⟨q - (r + s), by omega⟩
    have e1 : r + s + 1 - r = s + 1 := by omega
    have e2 : r + s + q' + r - (r + s) = q' + r := by omega
    rw [e1, e2, hM]
    ring

lemma frob (z M : ℕ) (hz : 1 ≤ z) (h1 : z ^ 2 + z ≤ M)
    (h2 : M ≤ 2 * z ^ 3 + 2 * z ^ 2 + 4 * z + 1) :
    ∃ m1 m2 : ℕ, m1 ≤ z ^ 2 ∧ m2 ≤ (z + 1) ^ 2 ∧ M = z * m1 + (z + 1) * m2 := by
  by_cases hc : M ≤ (z + 1) ^ 3 + z
  · obtain ⟨m1, m2, hm1, hm2, hM⟩ := frob1 z M hz h1 hc
    exact ⟨m1, m2, by nlinarith, hm2, hM⟩
  · push_neg at hc
    have hzz : z ≤ z ^ 2 := by nlinarith
    obtain ⟨w, hw⟩ : ∃ w, z ^ 2 = z + w := ⟨z ^ 2 - z, by omega⟩
    have hw3 : z ^ 3 = z ^ 2 + z * w := by
      calc z ^ 3 = z * z ^ 2 := by ring
        _ = z * (z + w) := by rw [hw]
        _ = z ^ 2 + z * w := by ring
    have hcube : (z + 1) ^ 3 = z ^ 3 + 3 * z ^ 2 + 3 * z + 1 := by ring
    have hzw : z * w ≤ M := by omega
    obtain ⟨m1, m2, hm1, hm2, hM⟩ := frob1 z (M - z * w) hz (by omega) (by omega)
    refine ⟨m1 + w, m2, by omega, hm2, ?_⟩
    have : M = (M - z * w) + z * w := by omega
    rw [this, hM]
    ring

lemma overlap (z : ℕ) (hz : 6 ≤ z) :
    16 * (z + 1) ^ 3 + 30 * (z + 1) ^ 2 + 30 * (z + 1) + 133
      ≤ 28 * z ^ 3 + 36 * z ^ 2 + 48 * z + 14 + 1 := by
  have h1 : 6 * z ^ 2 ≤ z ^ 3 := by nlinarith
  have h2 : 6 * z ≤ z ^ 2 := by nlinarith
  nlinarith

lemma cover (z u n : ℕ) (hz : 1 ≤ z)
    (hL : 16 * z ^ 3 + 30 * z ^ 2 + 30 * z + 133 ≤ n)
    (hU : n ≤ 28 * z ^ 3 + 36 * z ^ 2 + 48 * z + 14) :
    ∃ a : Fin 19 → ℕ, n + u ^ 3 = ∑ i, (a i) ^ 3 := by
  have hB : 8 * (z + 1) ^ 3 = 8 * z ^ 3 + 24 * z ^ 2 + 24 * z + 8 := by ring
  obtain ⟨R, hR⟩ : ∃ R, n = 8 * z ^ 3 + 8 * (z + 1) ^ 3 + R :=
    ⟨n - (8 * z ^ 3 + 8 * (z + 1) ^ 3), by omega⟩
  obtain ⟨t, ht⟩ : ∃ t, t = R % 6 := ⟨_, rfl⟩
  have ht6 : t < 6 := by omega
  have ht3 : t ^ 3 % 6 = t := by interval_cases t <;> rfl
  have ht125 : t ^ 3 ≤ 125 := by interval_cases t <;> norm_num
  obtain ⟨M, hM⟩ : ∃ M, R = 6 * M + t ^ 3 := ⟨(R - t ^ 3) / 6, by omega⟩
  have hM1 : z ^ 2 + z ≤ M := by omega
  have hM2 : M ≤ 2 * z ^ 3 + 2 * z ^ 2 + 4 * z + 1 := by omega
  obtain ⟨m1, m2, hm1, hm2, hMm⟩ := frob z M hz hM1 hM2
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, hx⟩ := eight_cubes z m1 hm1
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, hy⟩ := eight_cubes (z + 1) m2 hm2
  refine ⟨![x1, x2, x3, x4, x5, x6, x7, x8, y1, y2, y3, y4, y5, y6, y7, y8, t, u, 0], ?_⟩
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  have k0 : (0 : ℕ) ^ 3 = 0 := by norm_num
  rw [hR, hM, hMm]
  nlinarith [hx, hy, k0]

lemma small (n : ℕ) (hn : n < 2000) : ∃ a : Fin 19 → ℕ, n = ∑ i, (a i) ^ 3 := by
  obtain ⟨a, b, c, d, e, f, g, h, j, ha, hb, hc, hd, he, hf, hg, hh, hj, hsum⟩ :
      ∃ a b c d e f g h j : ℕ, a ≤ 1 ∧ b ≤ 1 ∧ c ≤ 1 ∧ d ≤ 1 ∧ e ≤ 1 ∧ f ≤ 1 ∧ g ≤ 2 ∧ h ≤ 3 ∧
        j ≤ 7 ∧ n = 1000 * a + 512 * b + 343 * c + 216 * d + 125 * e + 64 * f + 27 * g + 8 * h + j := by
    refine ⟨n / 1000, n % 1000 / 512, n % 1000 % 512 / 343, n % 1000 % 512 % 343 / 216,
      n % 1000 % 512 % 343 % 216 / 125, n % 1000 % 512 % 343 % 216 % 125 / 64,
      n % 1000 % 512 % 343 % 216 % 125 % 64 / 27, n % 1000 % 512 % 343 % 216 % 125 % 64 % 27 / 8,
      n % 1000 % 512 % 343 % 216 % 125 % 64 % 27 % 8, ?_⟩
    omega
  have ka : (10 * a) ^ 3 = 1000 * a := by interval_cases a <;> rfl
  have kb : (8 * b) ^ 3 = 512 * b := by interval_cases b <;> rfl
  have kc : (7 * c) ^ 3 = 343 * c := by interval_cases c <;> rfl
  have kd : (6 * d) ^ 3 = 216 * d := by interval_cases d <;> rfl
  have ke : (5 * e) ^ 3 = 125 * e := by interval_cases e <;> rfl
  have kf : (4 * f) ^ 3 = 64 * f := by interval_cases f <;> rfl
  have kg : (3 * min g 1) ^ 3 + (3 * (g - 1)) ^ 3 = 27 * g := by
    interval_cases g <;> decide
  have kh : (2 * min h 1) ^ 3 + (2 * min (h - 1) 1) ^ 3 + (2 * (h - 2)) ^ 3 = 8 * h := by
    interval_cases h <;> decide
  have kj : (min j 1) ^ 3 + (min (j - 1) 1) ^ 3 + (min (j - 2) 1) ^ 3 + (min (j - 3) 1) ^ 3
      + (min (j - 4) 1) ^ 3 + (min (j - 5) 1) ^ 3 + (j - 6) ^ 3 = j := by
    interval_cases j <;> decide
  have k0 : (0 : ℕ) ^ 3 = 0 := by norm_num
  refine ⟨![10 * a, 8 * b, 7 * c, 6 * d, 5 * e, 4 * f, 3 * min g 1, 3 * (g - 1),
    2 * min h 1, 2 * min (h - 1) 1, 2 * (h - 2), min j 1, min (j - 1) 1, min (j - 2) 1,
    min (j - 3) 1, min (j - 4) 1, min (j - 5) 1, j - 6, 0], ?_⟩
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  linarith

theorem solution :
    ∀ n : ℕ, ∃ (a : Fin 19 → ℕ), n = ∑ i, (a i) ^ 3 := by
  intro n
  by_cases h0 : n < 2000
  · exact small n h0
  push_neg at h0
  by_cases h1 : n ≤ 2574
  · obtain ⟨a, ha⟩ := cover 4 0 n (by norm_num) (by norm_num; omega) (by norm_num; omega)
    exact ⟨a, by simpa using ha⟩
  push_neg at h1
  by_cases h2 : n ≤ 3032
  · obtain ⟨a, ha⟩ := cover 4 8 (n - 512) (by norm_num) (by norm_num; omega) (by norm_num; omega)
    exact ⟨a, by norm_num at ha; omega⟩
  push_neg at h2
  by_cases h3 : n ≤ 4654
  · obtain ⟨a, ha⟩ := cover 5 0 n (by norm_num) (by norm_num; omega) (by norm_num; omega)
    exact ⟨a, by simpa using ha⟩
  push_neg at h3
  by_cases h4 : n ≤ 4848
  · obtain ⟨a, ha⟩ := cover 5 6 (n - 216) (by norm_num) (by norm_num; omega) (by norm_num; omega)
    exact ⟨a, by norm_num at ha; omega⟩
  push_neg at h4
  -- general case: n ≥ 4849 = L 6
  have hex : ∃ z, n < 16 * (z + 1) ^ 3 + 30 * (z + 1) ^ 2 + 30 * (z + 1) + 133 :=
    ⟨n, by nlinarith⟩
  obtain ⟨z, hzdef⟩ : ∃ z, z = Nat.find hex := ⟨_, rfl⟩
  have hz1 : n < 16 * (z + 1) ^ 3 + 30 * (z + 1) ^ 2 + 30 * (z + 1) + 133 := by
    rw [hzdef]; exact Nat.find_spec hex
  have hz6 : 6 ≤ z := by
    by_contra hcon
    push_neg at hcon
    interval_cases z <;> omega
  have hz2 : 16 * z ^ 3 + 30 * z ^ 2 + 30 * z + 133 ≤ n := by
    have hlt : z - 1 < Nat.find hex := by omega
    have := Nat.find_min hex hlt
    have e : z - 1 + 1 = z := by omega
    rw [e] at this
    omega
  have hU := overlap z hz6
  obtain ⟨a, ha⟩ := cover z 0 n (by omega) hz2 (by omega)
  exact ⟨a, by simpa using ha⟩
