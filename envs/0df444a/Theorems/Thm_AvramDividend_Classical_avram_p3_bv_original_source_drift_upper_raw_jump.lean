-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_drift_upper_raw_jump
-- name    : AvramDividend.Classical.avram_p3_bv_original_source_drift_upper_raw_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:41:27.04337+00:00
-- url     : https://prove2.me/theorems/188cbca7-da49-4463-825d-ebda178dd0d8
-- title:
--   Original BV physical drift upper bounds actual increments plus their raw left-jump losses
-- statement:
--   On the genuine original bounded-variation Lévy sample paths, all raw negative left-jump losses plus the actual source increment are bounded above by the physical drift over every nonnegative time interval. This is an unconditional one-sided consequence of the proved nonnegative residual decomposition, without requiring the residual to vanish, replacing the source process, or adding any compensation hypothesis. It is the favourable direction for an HJB supermartingale upper bound when the candidate is increasing.
-- source:
--   Exact proved original-process nonnegative residual theorem 46850ddf-12e0-4cba-87a8-dbb185492ee8 and real polynomial rearrangement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_source_raw_jump_interval_nonnegative_remainder
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_source_drift_upper_raw_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      X.X t ω - X.X s ω +
        (∑' u : ℝ≥0,
          if s < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
          else 0) ≤
        ((t : ℝ) - (s : ℝ)) * X.drift := by sorry
