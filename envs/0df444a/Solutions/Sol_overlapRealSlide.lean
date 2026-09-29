-- Prove2me | solution 1 for overlapRealSlide
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T00:32:32.383745+00:00
-- url     : https://prove2.me/submissions/55de65d0-5272-4a84-8123-90c1d20e2c1e

import Mathlib

theorem solution (n : ℕ) :
    ∀ (x0 : ℝ), (n : ℝ) + 1 - 3 / 4 < x0 →
      (x0 < (n : ℝ) + 1 ∨ 0 < (1 : ℝ) ∨ dist (⟨x0, 1⟩ : ℂ) ((n + 2 : ℕ) : ℂ) < 1 / 2) →
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        (n : ℝ) + 1 - 3 / 4 < (⟨(1 - s) * x0 + s * ((n : ℝ) + 1 - 3 / 4 + 1 / 2), 1 - s⟩ : ℂ).re ∧
        ((⟨(1 - s) * x0 + s * ((n : ℝ) + 1 - 3 / 4 + 1 / 2), 1 - s⟩ : ℂ).re < (n : ℝ) + 1 ∨
          0 < (⟨(1 - s) * x0 + s * ((n : ℝ) + 1 - 3 / 4 + 1 / 2), 1 - s⟩ : ℂ).im ∨
          dist (⟨(1 - s) * x0 + s * ((n : ℝ) + 1 - 3 / 4 + 1 / 2), 1 - s⟩ : ℂ) ((n + 2 : ℕ) : ℂ) < 1 / 2) := by
  intro x0 hx0 hmem s hs0 hs1
  have hn : (0 : ℝ) ≤ n := by positivity
  -- The real part of the image is a convex combination of `x0` and
  -- `px = (n+1) - 3/4 + 1/2`, which is the midpoint of `(n+1-3/4, n+1)`.  Both endpoints
  -- exceed the lower bound, so the bound survives; no `dist` arithmetic is needed.
  have hpx2 : (n : ℝ) + 1 - 3 / 4 + 1 / 2 < (n : ℝ) + 1 := by linarith
  have hrw : (⟨(1 - s) * x0 + s * ((n : ℝ) + 1 - 3 / 4 + 1 / 2), 1 - s⟩ : ℂ).re
      = (1 - s) * x0 + s * ((n : ℝ) + 1 - 3 / 4 + 1 / 2) := rfl
  have hiw : (⟨(1 - s) * x0 + s * ((n : ℝ) + 1 - 3 / 4 + 1 / 2), 1 - s⟩ : ℂ).im = 1 - s := rfl
  -- The lower bound: both endpoints of the convex combination exceed it, with
  -- non-negative weights summing to one.
  have h1m : (0 : ℝ) ≤ 1 - s := by linarith
  have hs0' : (0 : ℝ) ≤ s := hs0
  have hcomb : (n : ℝ) + 1 - 3 / 4
      < (1 - s) * x0 + s * ((n : ℝ) + 1 - 3 / 4 + 1 / 2) := by
    have hx0'' : (0 : ℝ) ≤ x0 := by linarith
    have hx0' : (0 : ℝ) ≤ (1 - s) * x0 := mul_nonneg h1m hx0''
    have hpx' : (0 : ℝ) ≤ s * ((n : ℝ) + 1 - 3 / 4 + 1 / 2) := by
      have : (0 : ℝ) < (n : ℝ) + 1 - 3 / 4 + 1 / 2 := by linarith
      exact mul_nonneg hs0' (le_of_lt this)
    nlinarith
  refine ⟨hrw ▸ hcomb, ?_⟩
  -- The disjunct, decided by the imaginary part.  If `1 - s > 0` the second disjunct
  -- holds directly.  Otherwise `1 - s ≤ 0` forces `s = 1`, and then the image is
  -- exactly the anchor, whose real part is still strictly below `n + 1`, so the FIRST
  -- disjunct holds.  Splitting on the imaginary part first is essential: the real part
  -- is not assumed below `n + 1` here, so committing to the first disjunct
  -- prematurely would be unjustified.
  by_cases hspos : 0 < 1 - s
  · exact Or.inr (Or.inl (hiw ▸ hspos))
  · have hseq : s = 1 := by linarith
    subst hseq
    have hre : (⟨(1 - 1) * x0 + 1 * ((n : ℝ) + 1 - 3 / 4 + 1 / 2), 1 - 1⟩ : ℂ).re
        = (n : ℝ) + 1 - 3 / 4 + 1 / 2 := by
      show (1 - 1) * x0 + 1 * ((n : ℝ) + 1 - 3 / 4 + 1 / 2) = _
      ring
    rw [hre]
    left
    linarith
