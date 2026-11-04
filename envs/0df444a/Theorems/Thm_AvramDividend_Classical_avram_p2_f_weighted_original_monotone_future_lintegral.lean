-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_monotone_future_lintegral
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_monotone_future_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:18:23.545087+00:00
-- url     : https://prove2.me/theorems/2eb734c7-195d-41b2-8a36-9995a9682127
-- title:
--   Monotonicity of the genuine original intrinsic marked future-count weighted lintegral
-- statement:
--   For the original Lévy intrinsic marked future count, any nonnegative pathwise weight bound H≤K transports monotonically to their integrated expected marked-count contributions without finiteness, ν-rate or filtration assumptions. It is the order step needed for simple-weight approximation.
-- source:
--   ENNReal multiplication monotonicity and Mathlib MeasureTheory.lintegral_mono on the actual original intrinsic marked count.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_monotone_future_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ)
    (H K : Ω → ℝ≥0∞) (hHK : ∀ ω, H ω ≤ K ω) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) ∂P) ≤
    (∫⁻ ω, K ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) ∂P) := by sorry
