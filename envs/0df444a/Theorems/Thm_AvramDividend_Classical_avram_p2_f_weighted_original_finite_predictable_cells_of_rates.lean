-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_finite_predictable_cells_of_rates
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_finite_predictable_cells_of_rates
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:06:13.865203+00:00
-- url     : https://prove2.me/theorems/e80034fc-3088-49c6-aa47-cc81bd9e2df2
-- title:
--   Finite source-original predictable marked jump cells compensate from separately proved unweighted rates
-- statement:
--   For a finite family of genuine original spectrally negative Lévy marked-jump rectangles, possibly at distinct deterministic past times, any nonnegative weights measurable in the corresponding source-past filtrations have exact finite-sum expected compensation given individually proved unweighted count means. The count equality to the original intrinsic jump measure and each unweighted rate are explicit hypotheses; no auxiliary Poisson copy or assumed ν-rate is hidden. Reuses the accepted original future/past product theorem and finite ENNReal lintegral additivity, preserving 0*infinity.
-- source:
--   Proved d9c55240, 267e2229, a30d1d38; directly aids P2-E predictable rectangle integrands while P2-A source ν rate remains Open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_future_past_product
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_ambient_finite_lintegral_sum_from_individual_rates

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_finite_predictable_cells_of_rates
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ι) (s T : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (H N : ι → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ S, Measurable[𝓕 (s i)] (H i))
    (hSource : ∀ i ∈ S, ∀ ω : Ω, N i ω = ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (s i + T i) ×ˢ B i))
    (r : ι → ℝ≥0∞)
    (hRate : ∀ i ∈ S, (∫⁻ ω, N i ω ∂P) = r i) :
    (∫⁻ ω, S.sum (fun i => H i ω * N i ω) ∂P) =
    S.sum (fun i => (∫⁻ ω, H i ω ∂P) * r i) := by sorry
