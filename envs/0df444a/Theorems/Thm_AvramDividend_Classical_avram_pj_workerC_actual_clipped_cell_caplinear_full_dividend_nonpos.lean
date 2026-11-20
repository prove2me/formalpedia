-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_clipped_cell_caplinear_full_dividend_nonpos
-- name    : AvramDividend.Classical.avram_pj_workerC_actual_clipped_cell_caplinear_full_dividend_nonpos
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T20:50:36.88519+00:00
-- url     : https://prove2.me/theorems/2875724f-f7d5-41dd-a5f2-455373167d5c
-- title:
--   Original true clipped grid full dividend loss nonpositive for caplinear value without pre-reserve cap
-- statement:
--   At original ruin-clipped physical grid endpoints, full within-cell rightLimit D dividend variation is nonpositive relative to lost globally caplinear value V, even when prepayment reserve exceeds finite cap. The postreserve nonnegative and monotone strategy assumptions are explicitly required; the genuine compensated-jump source remains separate.
-- source:
--   Proved global caplinear finite-cell signed source 5acde692, which itself uses proved a4675c8a; replaces the overly restrictive pre-reserve cap assumption of proved b26a0c39.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_caplinear_allcell_discounted_cash_loss_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_actual_clipped_cell_caplinear_full_dividend_nonpos
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
    (D : ℝ≥0 → Ω → ℝ)
    (n m : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω)
    (u : ℕ → ℝ≥0)
    (hu : ∀ i, u i = min
      ((i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))) (ρ ω))
    (hDmono : ∀ i ∈ Finset.range (m + 1),
      rightLimit D (u i) ω ≤ rightLimit D (u (i + 1)) ω)
    (hpost : ∀ i ∈ Finset.range (m + 1),
      0 ≤ x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) :
    (∑ i ∈ Finset.range (m + 1),
      Real.exp (-(q * (u (i + 1) : ℝ))) *
        ((rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) -
          (V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
           w (x + X.X (u (i + 1)) ω -
              rightLimit D (u (i + 1)) ω)))) ≤ 0 := by sorry
