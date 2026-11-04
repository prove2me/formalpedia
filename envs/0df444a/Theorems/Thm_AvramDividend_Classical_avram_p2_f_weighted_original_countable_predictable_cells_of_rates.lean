-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_predictable_cells_of_rates
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_countable_predictable_cells_of_rates
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:13:18.787955+00:00
-- url     : https://prove2.me/theorems/2d249f3f-c06c-4ef2-8814-2247ba824d6e
-- title:
--   Countable source-original predictable marked jump rectangle compensation from separately proved rates
-- statement:
--   Countably many genuine original spectrally negative Lévy intrinsic jump counts on deterministic future marked rectangles, each with its own adapted nonnegative past weight, have exact total first-moment compensation provided their separate unweighted first moments are already established. The pathwise source identities and each rate are explicit hypotheses. Monotone/Tonelli lintegral-tsum handles infinite total mass and zero-times-infinity correctly. This supplies the source-faithful countable transfer needed for P2-E; it does not prove the outstanding zero-origin Lévy ν rate.
-- source:
--   Original source factor theorem 267e2229 and measurability d9c55240, plus pinned Mathlib MeasureTheory.lintegral_tsum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_future_past_product

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_countable_predictable_cells_of_rates
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (H N : ι → Ω → ℝ≥0∞)
    (hH : ∀ i, Measurable[𝓕 (s i)] (H i))
    (hSource : ∀ i, ∀ ω : Ω, N i ω = ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (s i + T i) ×ˢ B i))
    (r : ι → ℝ≥0∞)
    (hRate : ∀ i, (∫⁻ ω, N i ω ∂P) = r i) :
    (∫⁻ ω, ∑' i, H i ω * N i ω ∂P) =
    ∑' i, (∫⁻ ω, H i ω ∂P) * r i := by sorry
