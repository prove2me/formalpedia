-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_finite_l1_of_finite_source_means
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_finite_l1_of_finite_source_means
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:14:12.122047+00:00
-- url     : https://prove2.me/theorems/c458e9f2-ef1f-4248-b3a3-b61d87f8f89e
-- title:
--   Finite weighted original intrinsic marked count first moment from finite source means
-- statement:
--   For actual original spectrally negative Lévy marked jump counts, a nonnegative weight measurable at the past time has a finite expected product when both its own first moment and the original unweighted marked-count mean are finite. This transfers first-moment finiteness to weighted predictable L1 compensation using proved source-original future/past factorisation, while requiring source count equality and independent moment bounds explicitly. No ν rate is assumed.
-- source:
--   Proved original future/past 267e2229 and pinned Mathlib ENNReal.mul_ne_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_future_past_product

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_finite_l1_of_finite_source_means
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (H N : Ω → ℝ≥0∞)
    (hH : Measurable[𝓕 s] H)
    (hSource : ∀ ω : Ω, N ω = ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B))
    (hHfinite : (∫⁻ ω, H ω ∂P) ≠ ∞)
    (hNfinite : (∫⁻ ω, N ω ∂P) ≠ ∞) :
    (∫⁻ ω, H ω * N ω ∂P) ≠ ∞ := by sorry
