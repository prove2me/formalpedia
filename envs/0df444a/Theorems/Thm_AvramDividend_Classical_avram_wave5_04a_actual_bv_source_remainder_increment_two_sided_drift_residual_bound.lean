-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_remainder_increment_two_sided_drift_residual_bound
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_increment_two_sided_drift_residual_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:41:11.719658+00:00
-- url     : https://prove2.me/theorems/e425d9f0-6f03-4fd4-9326-f6cf11453bc0
-- title:
--   Actual BV source residual increment lies between zero and the complete source drift-minus-path residual
-- statement:
--   For the actual spectrally negative Lévy source of bounded variation, almost surely the explicitly defined original-path downward residual R, after subtracting all intrinsic negative source left jumps, is monotone; on every ordered source interval its increment is at least zero and at most the actual drift-minus-source-path increment. This is a two-sided real bound potentially suitable for source finite-variation integrability estimates, without asserting pure-jump equality or a controlled Itô–Meyer integration identity.
-- source:
--   Chat04-A original BV source envelope, deduced from canonically Proved exact source intrinsic-jump interval decomposition c4b53c7c-d769-4894-a0d8-c0b2a1516d1e and nonnegativity of the full negative-jump ENNReal.toReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original source BV downward residual is squeezed between zero
and the actual drift-minus-source-path increment, on one a.s. event;
the bound may be used as an integrability envelope without Ito-Meyer. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_increment_two_sided_drift_residual_bound
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
      ∀ (s t : ℝ≥0) (hst : s ≤ t),
        0 ≤ R t - R s ∧
          R t - R s ≤
            ((t : ℝ) - (s : ℝ)) * X.drift -
              (X.X t ω - X.X s ω) := by sorry
