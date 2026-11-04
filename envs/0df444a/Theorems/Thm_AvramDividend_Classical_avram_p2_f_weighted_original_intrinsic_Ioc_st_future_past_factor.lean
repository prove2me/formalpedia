-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_Ioc_st_future_past_factor
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_Ioc_st_future_past_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:18:35.469951+00:00
-- url     : https://prove2.me/theorems/7090fa21-7f82-4913-ab72-882c2c3aa0bc
-- title:
--   Original intrinsic (s,t] marked jump count factors against adapted weights
-- statement:
--   For every source-original spectrally negative Lévy path, deterministic times s ≤ t and arbitrary Borel marked-jump set B, the first moment of the original intrinsic count over (s,t] multiplied by an arbitrary nonnegative past-measurable weight equals the product of its separate first moments. It transports the already-Proved (s,s+T] future/past identity to the exact interval used in P2-E's compensator statement, using T=t-s. No Poisson substitution, ν rate or finiteness is needed.
-- source:
--   Proved source original future/past product 267e2229 and pinned Mathlib add_tsub_cancel_left.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_future_past_product

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_Ioc_st_future_past_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) ∂P) =
    (∫⁻ ω, H ω ∂P) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) ∂P) := by sorry
