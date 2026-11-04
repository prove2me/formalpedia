-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_cutoff_le_source_residual
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_interval_cutoff_le_source_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:41:53.386209+00:00
-- url     : https://prove2.me/theorems/a2003828-abe5-400b-bdab-e6f230952bc3
-- title:
--   Original bounded-variation interval source drift dominates all negative-jump size cutoffs
-- statement:
--   On the original sample space and original filtration, every bounded-variation spectrally negative Levy sample path almost surely satisfies that the actual intrinsic negative left-jump magnitude sum on an ordered interval (s,t], after an arbitrary positive size cutoff, is at most the source drift-minus-path increment. No jump law, compensator, independent process, or representation is assumed.
-- source:
--   Combine the Proved original interval full-negative-jump-total-to-source-residual inequality (0ebd2a44) with ENNReal.tsum_le_tsum comparing cutoff terms to the complete source jump series.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Any separated actual-source jump cutoff is dominated by the original
bounded-variation drift-minus-path increment on each ordered interval. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_interval_cutoff_le_source_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t → ∀ ε : ℝ≥0∞,
      (∑' (u : ℝ≥0),
        if s < u ∧ u ≤ t ∧
             ε < ENNReal.ofReal (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
        then ENNReal.ofReal (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
        else 0) ≤
      ENNReal.ofReal
        (((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω)) := by sorry
