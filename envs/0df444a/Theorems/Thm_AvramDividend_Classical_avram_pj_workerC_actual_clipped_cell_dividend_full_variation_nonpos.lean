-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_clipped_cell_dividend_full_variation_nonpos
-- name    : AvramDividend.Classical.avram_pj_workerC_actual_clipped_cell_dividend_full_variation_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:44:06.361394+00:00
-- url     : https://prove2.me/theorems/b26a0c39-9c24-4e69-b1de-3da166d5065e
-- title:
--   Actual ruin-clipped physical-grid within-cell dividend cash minus discounted w loss is nonpositive
-- statement:
--   On the original physical grid, at fixed endpoint X.X(u_{i+1}), continuous and jump dividends paid inside each cell change rightLimit D between u_i and u_{i+1}. For nonnegative postreserve and pre-reserve within cap, the derivative condition implies discounted cash minus potential lost is nonpositive in aggregate. Explicit source conditions hDmono and hpost/hcap must be established from the original strategy/path before use.
-- source:
--   Exact genuine pathwise finite-variation correction for purejump source c2a65023, without the false claim that all dividend payments occur at sampled physical-grid points. Uses Proved e79bfcb7 and original risk process definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_discounted_physical_dividend_cell_gradient_losses_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_actual_clipped_cell_dividend_full_variation_nonpos
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ)
    (n m : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω)
    (u : ℕ → ℝ≥0)
    (hu : ∀ i, u i = min
      ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))) (ρ ω))
    (hDmono : ∀ i ∈ Finset.range (m + 1),
      rightLimit D (u i) ω ≤ rightLimit D (u (i + 1)) ω)
    (hpost : ∀ i ∈ Finset.range (m + 1),
      0 ≤ x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω)
    (hcap : ∀ i ∈ Finset.range (m + 1),
      ENNReal.ofReal (x + X.X (u (i + 1)) ω -
        rightLimit D (u i) ω) ≤ C) :
    (∑ i ∈ Finset.range (m + 1),
      Real.exp (-(q * (u (i + 1) : ℝ))) *
        ((rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) -
          (w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
           w (x + X.X (u (i + 1)) ω -
              rightLimit D (u (i + 1)) ω)))) ≤ 0 := by sorry
