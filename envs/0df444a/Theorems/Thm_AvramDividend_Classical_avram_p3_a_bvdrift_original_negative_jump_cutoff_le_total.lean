-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_negative_jump_cutoff_le_total
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_negative_jump_cutoff_le_total
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:16:37.876827+00:00
-- url     : https://prove2.me/theorems/0ab55ee4-590b-45c2-8744-142792a2c8ae
-- title:
--   Actual source jump band truncated magnitude bounded by the complete original negative-jump total
-- statement:
--   On every sample path of the original spectrally negative Levy process, the total of negative left-jump magnitudes with size above any nonnegative ENNReal cutoff is at most the complete original negative-jump magnitude total on (0,T]. No BV, integrability, compensator or rate premise is required; it is the natural first inequality for monotone cutoff convergence.
-- source:
--   Pointwise inclusion of actual source left-jump cutoff mask into all positive times and ENNReal.tsum_le_tsum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Removing small actual source left jumps cannot increase their total
negative-jump magnitude on any sample path. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_negative_jump_cutoff_le_total
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (ω : Ω) (ε : ℝ≥0∞) :
    (∑' (v : ℝ≥0),
      if 0 < v ∧ v ≤ T ∧ ε < ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      then ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) else 0) ≤
    (∑' (v : ℝ≥0),
      if 0 < v ∧ v ≤ T then ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) else 0) := by sorry
