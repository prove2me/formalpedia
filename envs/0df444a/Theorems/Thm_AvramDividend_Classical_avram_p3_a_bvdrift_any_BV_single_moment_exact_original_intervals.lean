-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_any_BV_single_moment_exact_original_intervals
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_any_BV_single_moment_exact_original_intervals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:36:13.808489+00:00
-- url     : https://prove2.me/theorems/ecc56f30-3613-4ab5-a796-bac54e9afa36
-- title:
--   Original BV exact drift-minus-jumps intervals under single mean-zero residual, no Standing
-- statement:
--   For any original bounded-variation spectrally negative Lévy process, without Standing, positive drift, a chosen generator test function or a replacement process, if the explicit original residual at one finite horizon is integrable and has mean zero, then on one full-measure event every original-source increment within that horizon is exactly elapsed-time physical drift minus the actual marked negative-jump integral.
-- source:
--   The newly Proved unconditional original BV physical drift bound 96dce014 and true jump-series/marked-measure identity 3d5eead6 imply original residual nonnegativity. The genuine integral_eq_zero_iff_of_nonneg_ae kills its fixed-horizon value. The already Proved exact source interval residual decomposition and residual monotonicity propagate zero backwards to every earlier pair.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_actual_source_negative_jumps_drift_upper_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Any original BV source has exact drift-minus-jumps increments on [0,T]
once the original nonnegative residual has integrable mean zero at T. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_any_BV_single_moment_exact_original_intervals
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0)
    (hIntegrable : Integrable (fun ω : Ω =>
      ((T : ℝ) * X.drift - X.X T ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) P)
    (hMeanZero : (∫ ω : Ω,
      (((T : ℝ) * X.drift - X.X T ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) ∂P) = 0) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
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
