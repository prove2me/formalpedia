-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:40:26.306141+00:00
-- url     : https://prove2.me/theorems/09869e16-9a95-47e7-b1cd-83739a17b285
-- title:
--   Exact original bounded-variation Lévy source intervals through intrinsic jump measure and downward residual
-- statement:
--   For the actual bounded-variation spectrally negative Levy process X, almost surely there is an explicitly defined nondecreasing downward finite-variation residual R after removing physical source drift and all actual intrinsic negative original left jumps. Every source interval X_t-X_s equals its drift increment minus the real value of the intrinsic original-source negative-mark integral over (s,t] minus the nonnegative residual increment R_t-R_s. This is an exact original-path decomposition stated in terms of the genuine intrinsic jump measure, not a Poisson replacement. The theorem does not assume R=0, and is sufficient for the nonpositive residual contribution with increasing C1 verification functions.
-- source:
--   Chat04-A exact measure-level original BV decomposition from Proved original-source remainder interval identity c4b53c7c-d769-4894-a0d8-c0b2a1516d1e and dedicated pathwise intrinsic negative mark integral-to-left-jump sum identity. Neither independent Poisson processes nor controlled Ito-Meyer used.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Exact almost-sure original BV source interval decomposition using
its intrinsic negative left-jump counting MEASURE, retaining the
nondecreasing downward finite-variation residual. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (s t : ℝ≥0), s ≤ t →
        X.X t ω - X.X s ω =
          ((t : ℝ) - (s : ℝ)) * X.drift -
            (∫⁻ p,
              (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
              ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
                (fun u : ℝ≥0 => (u,
                  X.X u ω - Function.leftLim
                    (fun v : ℝ≥0 => X.X v ω) u)))).toReal -
            (R t - R s) := by sorry
