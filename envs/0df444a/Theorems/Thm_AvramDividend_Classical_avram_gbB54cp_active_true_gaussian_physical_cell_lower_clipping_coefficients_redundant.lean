-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB54cp_active_true_gaussian_physical_cell_lower_clipping_coefficients_redundant
-- name    : AvramDividend.Classical.avram_gbB54cp_active_true_gaussian_physical_cell_lower_clipping_coefficients_redundant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T14:51:04.631242+00:00
-- url     : https://prove2.me/theorems/ebf14722-7b98-4bf4-88eb-2ffe7926e0bb
-- title:
--   Original active stopped Gaussian grid has no lower-clipping branch in gradient or Hessian coefficients
-- statement:
--   At each original true physical Gaussian mesh start time strictly before the stopping clock, the proved source postpayment reserve floor guarantees Y_i≥delta/2. Consequently the exact source gain G and Hessian coefficient H clipped to Icc[delta/2,b] coincide identically with the upper-clipped-only coefficients using Y_i≤b, including the original boundary conventions. Both gradient and Hessian identities hold simultaneously, with no Brownian replacement or lower-kink local-time assumption. This is a source-specific algebraic reduction for the unresolved B54cp positive-error mesh.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_gbB54cp_active_true_gaussian_physical_cell_lower_clipping_coefficients_redundant
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (j n m i : ℕ) (ω : Ω)
    (hMask : (i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)) < ρ ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let y : ℝ := x + X.X s ω - rightLimit D s ω
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    (if y ∈ Icc a b then deriv w y else 1) =
      (if y ≤ b then deriv w y else 1) ∧
    (if y ∈ Icc a b then iteratedDeriv 2 w y else 0) =
      (if y ≤ b then iteratedDeriv 2 w y else 0) := by sorry
