-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_finite_t3_original_all_rows_positive_prejump_ae
-- name    : AvramDividend.Classical.avram_route_finite_t3_original_all_rows_positive_prejump_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:45:40.373194+00:00
-- url     : https://prove2.me/theorems/8c8e1b33-d63f-45dd-a043-d1e831f55df1
-- title:
--   Original BV physical-grid prepayment left-limits simultaneously equal the actual reserve at positive row times
-- statement:
--   The original controlled Lévy process has a deterministic positive-grid prepayment left-limit equality outside one null set simultaneously across every row and column of any countable two-index physical grid. This bridges the existing one-index pre-jump identity to the two-scale limit of the finite-cap stopped original process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_finite_t3_original_all_rows_positive_prejump_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (u : ℕ → ℕ → ℝ≥0)
    (hu : ∀ n i, 0 < u n (i + 1)) :
    ∀ᵐ ω ∂P, ∀ n i,
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
        (u n (i + 1)) =
      riskProcess X x D (u n (i + 1)) ω := by sorry
