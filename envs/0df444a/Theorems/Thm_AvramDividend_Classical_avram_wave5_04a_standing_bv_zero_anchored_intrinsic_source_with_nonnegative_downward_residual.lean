-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual
-- name    : AvramDividend.Classical.avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:11:50.053107+00:00
-- url     : https://prove2.me/theorems/93ee4a8c-bc51-4b92-ad77-e9fcff70bbd6
-- title:
--   Original Standing BV Lévy source: zero-anchored exact intrinsic negative-mark formula with nonnegative downward remainder and positive drift
-- statement:
--   For the actual spectrally negative Levy process under Standing and bounded variation, the physical drift is positive. Almost surely the explicitly defined original-source residual R starts at exactly zero and is nondecreasing, hence nonnegative. Every original source sample path X_t starts at zero and equals t times its own drift minus the complete intrinsic source negative-mark counting-measure mass on (0,t] minus the nonnegative residual R_t. No independent Poisson process, complete Ito-Meyer identity, or residual-vanishing assumption is used.
-- source:
--   Chat04-A original source-side normalisation by X.X_zero applied to canonically Proved 09869e16-9a95-47e7-b1cd-83739a17b285; positive physical drift from already Proved 0432f641-b22a-4ba0-b92e-6972ea7a1908. This is the exact anchored actual-path datum needed by the stopped C1 source bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original BV source starts at zero.  The actual intrinsic negative
mark integral and an explicitly normalised, nonnegative downward residual
then give the complete anchored source path, with positive physical drift
under Standing.  This does not assert that the residual vanishes. -/

theorem AvramDividend.Classical.avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation) :
    0 < X.drift ∧
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      R 0 = 0 ∧ Monotone R ∧
      ∀ t : ℝ≥0,
        0 ≤ R t ∧
        X.X t ω =
          (t : ℝ) * X.drift -
            (∫⁻ p,
              (if 0 < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
              ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
                (fun u : ℝ≥0 => (u,
                  X.X u ω - Function.leftLim
                    (fun v : ℝ≥0 => X.X v ω) u)))).toReal - R t := by sorry
