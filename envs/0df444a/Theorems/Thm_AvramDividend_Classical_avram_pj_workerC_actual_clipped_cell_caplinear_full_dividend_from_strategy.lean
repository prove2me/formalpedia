-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_clipped_cell_caplinear_full_dividend_from_strategy
-- name    : AvramDividend.Classical.avram_pj_workerC_actual_clipped_cell_caplinear_full_dividend_from_strategy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:56:48.544082+00:00
-- url     : https://prove2.me/theorems/865e22fd-a75f-4148-afb6-ef85e95e9720
-- title:
--   Automatic right-dividend monotonicity gives original caplinear true-grid full-cell nonpositive cash correction
-- statement:
--   Under an original dividend strategy, rightLimit D is nondecreasing automatically on the genuine clipped grid. With positive postreserve, full within-cell paid dividend minus lost global caplinear potential has nonpositive discounted sum; no prepayment cap or finite jump-intensity assumption.
-- source:
--   Uses Proved f7eef805 monotonic rightLimit of genuine dividend strategy and the sound corrected original caplinear true-grid lemma fdc74c36; removes explicit hDmono requirement, leaving only true postreserve survival.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_caplinear_allcell_discounted_cash_loss_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_actual_clipped_cell_caplinear_full_dividend_from_strategy
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n m : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω)
    (u : ℕ → ℝ≥0)
    (hu : ∀ i, u i = min
      ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))) (ρ ω))
    (hpost : ∀ i ∈ Finset.range (m + 1),
      0 ≤ x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) :
    (∑ i ∈ Finset.range (m + 1),
      Real.exp (-(q * (u (i + 1) : ℝ))) *
        ((rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) -
          (V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
           V (x + X.X (u (i + 1)) ω -
              rightLimit D (u (i + 1)) ω)))) ≤ 0 := by sorry
