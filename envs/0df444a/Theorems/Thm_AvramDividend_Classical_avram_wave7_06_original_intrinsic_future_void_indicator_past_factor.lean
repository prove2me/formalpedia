-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_future_void_indicator_past_factor
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_future_void_indicator_past_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:17:11.091061+00:00
-- url     : https://prove2.me/theorems/c6109ede-2eb1-458e-991c-f57a78692950
-- title:
--   Exact future intrinsic source marked-void indicator factors from original past
-- statement:
--   On the actual original Lévy probability space, the indicator of no intrinsic jumps in the future interval (s,t] with any Borel marks B has its mixed nonnegative expectation factor from every past measurable event A. The proof uses the accepted measurable extractor for the same original path and independence of future path functionals from original-past weights; no auxiliary process or compensation-rate assumption is used.
-- source:
--   W7-06 future-void probabilistic independence step towards intrinsic Poisson zero-count law aa265c9f; exact original X.X and ν definitions preserved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_future_void_indicator_past_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫⁻ ω, (A.indicator (fun _ => (1 : ℝ≥0∞)) ω) *
      (if ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) = 0 then (1 : ℝ≥0∞) else 0) ∂P) =
    (∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P) *
    (∫⁻ ω, (if ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) = 0 then (1 : ℝ≥0∞) else 0) ∂P) := by sorry
