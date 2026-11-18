-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_predictable_negative_Borel_simple_marked_compensation_no_rate_hypothesis_20261117
-- name    : AvramDividend.Classical.avram_a27_original_predictable_negative_Borel_simple_marked_compensation_no_rate_hypothesis_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:08:02.832038+00:00
-- url     : https://prove2.me/theorems/72f270d5-1eb7-4f22-83d3-f9805ea7a0f9
-- title:
--   Original predictable finite-simple negative Borel marked compensation without auxiliary rate hypotheses
-- statement:
--   For arbitrary finite families of original predictable left-endpoint weights, time intervals and negative Borel mark bands, the expectation of the actual physical marked-jump weighted count equals the sum of expected past weights multiplied by exact original Lévy mark intensities. The source rectangular rate follows automatically from the already-Proved original physical Campbell mean law.
-- source:
--   Original finite predictable simple weighted rate compensation 08ea13f2 and physical negative Borel interval Campbell mean 811bf7d8; no BV assumption and no new probability space.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_a27_original_predictable_negative_Borel_simple_marked_compensation_no_rate_hypothesis_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (hst : ∀ i ∈ S, s i ≤ t i)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (W : ι → Ω → ℝ≥0∞)
    (hW : ∀ i ∈ S, Measurable[𝓕 (s i)] (W i))
    (hNeg : ∀ i ∈ S, B i ⊆ Iio (0 : ℝ)) :
    (∫⁻ ω, ∑ i ∈ S,
      W i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) =
    ∑ i ∈ S, (∫⁻ ω, W i ω ∂P) *
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by sorry
