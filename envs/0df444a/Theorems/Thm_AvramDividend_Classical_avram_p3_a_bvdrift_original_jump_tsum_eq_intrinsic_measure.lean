-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:25:23.081517+00:00
-- url     : https://prove2.me/theorems/3d5eead6-0d60-47c7-8d3e-2db4c473b715
-- title:
--   Original BV full-event left-jump magnitude tsum equals intrinsic marked-count integral
-- statement:
--   For a bounded-variation spectrally negative Lévy source, without Standing, additional moments or an auxiliary representation, the total actual left-jump magnitudes over (0,t] equal the marked-count integral of actual jumps on the same probability-one event simultaneously for every nonnegative time t.
-- source:
--   Derived from Proved original source BV interval residual decomposition 09869e16 and its simultaneous time-zero residual normalisation; compare the same residual written using two original-source jump encodings.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Original BV left-jump sum agrees with the actual marked-count integral. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ t then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal =
      (∫⁻ p,
        (if 0 < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
        ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
          X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by sorry
