-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_initial_atom_discounted_grid_uniform_negative_residual_budget
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_initial_atom_discounted_grid_uniform_negative_residual_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:45:56.56389+00:00
-- url     : https://prove2.me/theorems/6d5b0bac-024b-43e9-a32f-136507fef8ee
-- title:
--   Original BV full initial atom and finite discounted grid with uniform candidate-negative residual cap
-- statement:
--   For the genuine original bounded-variation spectrally negative Levy process and its controlled right/continuous payment grid, if the candidate negative part is bounded above by M on the localisation band, then the cumulative discounted signed residual is bounded by M times the total discount loss from time zero to the grid endpoint. This gives a finite-horizon original-process uniform residual bound, preserving the exact initial Stieltjes atom and all original right-limit payment increments.
-- source:
--   Proved original negative-value residual finite grid and telescoping of the monotone nonnegative discount weights; no new source stochastic axioms.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_initial_atom_discounted_grid_negative_value_residual_budget
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_initial_atom_discounted_grid_uniform_negative_residual_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (a b L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hbC : ENNReal.ofReal b ≤ C) (hL1 : 1 ≤ L)
    (hLip : ∀ y ∈ Icc a b, ∀ z ∈ Icc a b,
      |w y - w z| ≤ L * |y - z|)
    (q : ℝ) (hq : 0 ≤ q)
    (M : ℝ) (hM : ∀ y ∈ Icc a b, max 0 (-w y) ≤ M) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u →
      u 0 = 0 →
      (∀ n, x + X.X (u n) ω - rightLimit D (u n) ω ∈ Icc a b) →
      ∀ n,
        rightLimit D 0 ω +
        (∑ i ∈ Finset.range n,
          Real.exp (-(q * (u (i + 1) : ℝ))) *
            (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) +
        Real.exp (-(q * (u n : ℝ))) *
          w (x + X.X (u n) ω - rightLimit D (u n) ω) ≤
        w x +
        (∑ i ∈ Finset.range n,
          Real.exp (-(q * (u (i + 1) : ℝ))) *
            (L * (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift))) +
        M * (Real.exp (-(q * (u 0 : ℝ))) -
          Real.exp (-(q * (u n : ℝ)))) := by sorry
