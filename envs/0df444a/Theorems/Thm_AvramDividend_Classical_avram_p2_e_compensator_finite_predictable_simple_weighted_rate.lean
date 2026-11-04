-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_predictable_simple_weighted_rate
-- name    : AvramDividend.Classical.avram_p2_e_compensator_finite_predictable_simple_weighted_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:06:42.307198+00:00
-- url     : https://prove2.me/theorems/08ea13f2-08d4-48bf-8521-bc255de73322
-- title:
--   Finite predictable simple marked jump compensation on the original Lévy process
-- statement:
--   For a finite family of original-process predictable rectangles with individually chosen half-open time intervals (s_i,t_i], measurable jump-mark sets B_i and nonnegative F_{s_i}-measurable weights W_i, the ENNReal expected sum of W_i times the actual intrinsic source jump count equals the sum of E[W_i](t_i-s_i)ν(B_i), assuming only the separately sourced unconditional ν rate for each rectangle. No Poisson replacement, integrability finiteness, or compensated martingale is assumed.
-- source:
--   P2-E Proved source measurability 8146a449 and weighted conditional-rate e13617a2; Mathlib pinned lintegral_finset_sum. Canonical 393b03a8 remains Open awaiting P2-D rate 859bf7be.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_weighted_rate_from_unconditional

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_e_compensator_finite_predictable_simple_weighted_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (hst : ∀ i ∈ S, s i ≤ t i)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (W : ι → Ω → ℝ≥0∞)
    (hW : ∀ i ∈ S, Measurable[𝓕 (s i)] (W i))
    (hRate : ∀ i ∈ S,
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) =
        ((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) :
    (∫⁻ ω, ∑ i ∈ S,
      W i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) =
    ∑ i ∈ S, (∫⁻ ω, W i ω ∂P) *
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by sorry
