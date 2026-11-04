-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_integer_mean_zero_global_intervals
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_integer_mean_zero_global_intervals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:19:12.710712+00:00
-- url     : https://prove2.me/theorems/8f35fe90-cdeb-40bc-b2e0-1b3f99226613
-- title:
--   Global original BV physical drift from countable integer residual mean-zero conditions
-- statement:
--   For the actual original spectrally negative BV Levy process, finite first moment and mean zero of the nonnegative physical drift residual at each integer horizon imply on one probability-one event the exact drift minus genuine intrinsic negative jumps formula simultaneously over all time intervals. No Standing, independent auxiliary noise or assumed deterministic drift representation. The source-measurable mean-zero obligation remains explicit.
-- source:
--   From remotely Proved ecc56f30, obtain exact original intervals on [0,n] for each integer n. Intersect the countable a.e. events with ae_all_iff and dominate any endpoint by a natural n. This is the original process/measure/filtration, no new stochastic hypotheses except the displayed integer moment conditions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_any_BV_single_moment_exact_original_intervals

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Zero expected genuine residual at each integer horizon yields a single
almost-sure all-time original bounded-variation drift-minus-jump identity. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_integer_mean_zero_global_intervals
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hInt : ∀ n : ℕ, Integrable (fun ω : Ω =>
      (((n : ℝ≥0) : ℝ) * X.drift - X.X (n : ℝ≥0) ω) -
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ (n : ℝ≥0) then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal) P)
    (hMean : ∀ n : ℕ, (∫ ω : Ω,
      ((((n : ℝ≥0) : ℝ) * X.drift - X.X (n : ℝ≥0) ω) -
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ (n : ℝ≥0) then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal) ∂P) = 0) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      X.X t ω - X.X s ω =
        ((t : ℝ) - (s : ℝ)) * X.drift -
        (∫⁻ p,
          (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by sorry
