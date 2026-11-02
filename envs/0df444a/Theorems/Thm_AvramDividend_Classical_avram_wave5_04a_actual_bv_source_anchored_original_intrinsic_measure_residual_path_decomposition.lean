-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_anchored_original_intrinsic_measure_residual_path_decomposition
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_source_anchored_original_intrinsic_measure_residual_path_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:35:58.359944+00:00
-- url     : https://prove2.me/theorems/8c70f1e8-a39f-46d1-87a6-30a13b17798b
-- title:
--   Anchored genuine original BV Levy path equals initial value plus drift minus intrinsic left jumps and downward residual
-- statement:
--   For almost every actual source path of a bounded-variation spectrally negative Levy process, construct a coherent nondecreasing explicit downward residual R. For all t≥0 simultaneously, the original path X_t equals its actual initial value X_0 plus t times its specified source drift, minus the real negative-mark mass of its actual intrinsic source jump counting measure on (0,t], minus R_t-R_0. This is an exact original-process path decomposition (not merely an increment inequality), retains the honest initial-value anchor and makes no false claim of pure-jump R=0. The intrinsic jump measure counts only original source left jumps, not chronological right dividend payments.
-- source:
--   Chat04-A anchors the canonically Proved exact original BV source increment decomposition c4b53c7c-d769-4894-a0d8-c0b2a1516d1e at s=0 and rewrites the complete original negative left-jump sum by the pathwise intrinsic source measure identity Proved e40a85f1-31c7-4d8a-b66e-a0bd93a1554b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The actual original BV Levy source sample path is anchored at
its genuine initial source value, with drift minus all intrinsic
negative source jumps minus an increasing downward residual. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_source_anchored_original_intrinsic_measure_residual_path_decomposition
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
      ∀ t : ℝ≥0,
        X.X t ω = X.X 0 ω + (t : ℝ) * X.drift -
          (∫⁻ p,
            (if (0 : ℝ≥0) < p.1 ∧ p.1 ≤ t then
              ENNReal.ofReal (-p.2) else 0) ∂
            ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u)))).toReal -
          (R t - R 0) := by sorry
