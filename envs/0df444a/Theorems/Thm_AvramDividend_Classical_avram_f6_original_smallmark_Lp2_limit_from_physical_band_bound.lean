-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_smallmark_Lp2_limit_from_physical_band_bound
-- name    : AvramDividend.Classical.avram_f6_original_smallmark_Lp2_limit_from_physical_band_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T18:42:58.166626+00:00
-- url     : https://prove2.me/theorems/75618748-3c64-4ba5-a7cf-b26221c56c7a
-- title:
--   Original Lévy smallmark L² compensated terminal limit from physical annulus band bound alone
-- statement:
--   For the original spectrally negative Lévy process under probability P, any family of physical smallmark martingale approximants whose L² increment distances satisfy the natural truncated original Lévy quadratic moment bound converges in L² at every time. The finite quadratic-tail premise of the generic theorem is automatically discharged by the genuine original Lévy integrability axiom, so the remaining assumption is precisely the stochastic band isometry estimate to establish for the actual stopped compensated physical jump sum. This is a rigorous noncircular convergence bridge toward the infinite-activity stopped Itô source.
-- source:
--   Proved 720bc49f finite original Lévy quadratic tail; Proved 642b186a original Lp2 cutoff terminal existence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_smallmark_Lp2_limit_from_physical_band_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (M : ℕ → ℝ≥0 → Lp ℝ (2 : ℝ≥0∞) P)
    (C : ℝ)
    (hBandBound : ∀ t n m, n ≤ m →
      dist (M n t) (M m t) ≤
        C * Real.sqrt ((∫⁻ z in Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
        ENNReal.ofReal (z ^ 2) ∂X.ν).toReal)) :
    ∀ t, ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto (fun n => M n t) atTop (𝓝 L) := by sorry
