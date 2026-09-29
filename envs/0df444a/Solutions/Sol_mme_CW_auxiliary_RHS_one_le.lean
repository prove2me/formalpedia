-- Prove2me | solution 1 for mme_CW_auxiliary_RHS_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T04:31:15.896452+00:00
-- url     : https://prove2.me/submissions/eee07f91-3ef6-4219-8104-e17a697dd1f6

import Definitions.Def_mme_CW_auxiliary_RHS

/-!
# Positivity normalization for the CW Section 8 expression

The five denominator bases are the marginals in equation (13).  Under the
normalization constraint they are positive and sum to one, hence every
`x^x` denominator factor is at most one.  The numerator factors are all at
least one when `q ≥ 3` and `3*tau ≥ 2`.
-/

open MME Real

theorem solution
    (q : ℕ) (hq : 3 ≤ q)
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hnorm : 3 * a + 6 * b + 3 * c + 3 * d = 1) :
    1 ≤ auxiliaryRHS q tau a b c d := by
  let s₁ : ℝ := 2 * a + 2 * b + c
  let s₂ : ℝ := 2 * b + 2 * d
  let s₃ : ℝ := 2 * c + d
  let s₄ : ℝ := 2 * b
  let s₅ : ℝ := a
  have hs₁ : 0 < s₁ := by dsimp [s₁]; linarith
  have hs₂ : 0 < s₂ := by dsimp [s₂]; linarith
  have hs₃ : 0 < s₃ := by dsimp [s₃]; linarith
  have hs₄ : 0 < s₄ := by dsimp [s₄]; linarith
  have hs₅ : 0 < s₅ := by dsimp [s₅]; exact ha
  have hsum : s₁ + s₂ + s₃ + s₄ + s₅ = 1 := by
    dsimp [s₁, s₂, s₃, s₄, s₅]
    linarith
  have hs₁le : s₁ ≤ 1 := by linarith
  have hs₂le : s₂ ≤ 1 := by linarith
  have hs₃le : s₃ ≤ 1 := by linarith
  have hs₄le : s₄ ≤ 1 := by linarith
  have hs₅le : s₅ ≤ 1 := by linarith
  have hp₁ : s₁ ^ s₁ ≤ 1 := Real.rpow_le_one hs₁.le hs₁le hs₁.le
  have hp₂ : s₂ ^ s₂ ≤ 1 := Real.rpow_le_one hs₂.le hs₂le hs₂.le
  have hp₃ : s₃ ^ s₃ ≤ 1 := Real.rpow_le_one hs₃.le hs₃le hs₃.le
  have hp₄ : s₄ ^ s₄ ≤ 1 := Real.rpow_le_one hs₄.le hs₄le hs₄.le
  have hp₅ : s₅ ^ s₅ ≤ 1 := Real.rpow_le_one hs₅.le hs₅le hs₅.le
  have hp₁nonneg : 0 ≤ s₁ ^ s₁ := Real.rpow_nonneg hs₁.le _
  have hp₂nonneg : 0 ≤ s₂ ^ s₂ := Real.rpow_nonneg hs₂.le _
  have hp₃nonneg : 0 ≤ s₃ ^ s₃ := Real.rpow_nonneg hs₃.le _
  have hp₄nonneg : 0 ≤ s₄ ^ s₄ := Real.rpow_nonneg hs₄.le _
  have hp₅nonneg : 0 ≤ s₅ ^ s₅ := Real.rpow_nonneg hs₅.le _
  have hden_le :
      s₁ ^ s₁ * s₂ ^ s₂ * s₃ ^ s₃ * s₄ ^ s₄ * s₅ ^ s₅ ≤ 1 := by
    exact mul_le_one₀
      (mul_le_one₀
        (mul_le_one₀
          (mul_le_one₀ hp₁ hp₂nonneg hp₂)
          hp₃nonneg hp₃)
        hp₄nonneg hp₄)
      hp₅nonneg hp₅
  have hden_pos :
      0 < s₁ ^ s₁ * s₂ ^ s₂ * s₃ ^ s₃ * s₄ ^ s₄ * s₅ ^ s₅ := by
    positivity
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (le_trans (by decide : 1 ≤ 3) hq)
  have htau0 : 0 ≤ tau := by linarith
  have hqtau : 1 ≤ (q : ℝ) ^ (3 * tau) :=
    Real.one_le_rpow hq1 (by linarith)
  have hn₁ : 1 ≤ ((2 : ℝ) * q) ^ (6 * tau * b) := by
    apply Real.one_le_rpow
    · nlinarith
    · positivity
  have hn₂ : 1 ≤ (((q : ℝ) ^ (2 : ℕ)) + 2) ^ (3 * tau * c) := by
    apply Real.one_le_rpow
    · nlinarith [sq_nonneg (q : ℝ)]
    · positivity
  have hcentral :
      1 ≤ 4 * (q : ℝ) ^ (3 * tau) * ((q : ℝ) ^ (3 * tau) + 2) := by
    nlinarith
  have hn₃ :
      1 ≤
        (4 * (q : ℝ) ^ (3 * tau) * ((q : ℝ) ^ (3 * tau) + 2)) ^ d :=
    Real.one_le_rpow hcentral hd.le
  have hnum :
      1 ≤
        ((2 : ℝ) * q) ^ (6 * tau * b) *
          (((q : ℝ) ^ (2 : ℕ)) + 2) ^ (3 * tau * c) *
          (4 * (q : ℝ) ^ (3 * tau) * ((q : ℝ) ^ (3 * tau) + 2)) ^ d := by
    nlinarith [mul_pos (lt_of_lt_of_le zero_lt_one hn₁) (lt_of_lt_of_le zero_lt_one hn₂)]
  unfold auxiliaryRHS
  change 1 ≤
    (((2 : ℝ) * q) ^ (6 * tau * b) *
        (((q : ℝ) ^ (2 : ℕ)) + 2) ^ (3 * tau * c) *
        (4 * (q : ℝ) ^ (3 * tau) * ((q : ℝ) ^ (3 * tau) + 2)) ^ d) /
      (s₁ ^ s₁ * s₂ ^ s₂ * s₃ ^ s₃ * s₄ ^ s₄ * s₅ ^ s₅)
  rw [le_div_iff₀ hden_pos]
  simpa only [one_mul] using hden_le.trans hnum
