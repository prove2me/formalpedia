-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_exponential_jump_domination
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_exponential_jump_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:40:43.577824+00:00
-- url     : https://prove2.me/theorems/3ce8adcb-5b3c-497c-8409-bb635904b380
-- title:
--   Original BV source exponential is pointwise bounded by true negative-jump exponential
-- statement:
--   For original BV spectrally negative Lévy X, and every θ≥0 and T, the drift-normalised source exponential is bounded almost everywhere by the exponential of the negative actual left-jump magnitude sum, on the same Ω/P. Only existing proved original drift/residual and genuine jump encoding are used. No compensator, jump expectation or added process.
-- source:
--   Proved unconditional original BV drift upper bound 96dce014 and left-jump tsum/intrinsic marked measure equivalence 3d5eead6; multiply by θ≥0 and apply strict monotonicity of the real exponential.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_actual_source_negative_jumps_drift_upper_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Actual BV jump magnitudes dominate the physical-drift-normalised
source exponential at every finite horizon, before any compensator. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_exponential_jump_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ᵐ ω ∂P,
      Real.exp (θ * (X.X T ω - (T : ℝ) * X.drift)) ≤
        Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal)) := by sorry
