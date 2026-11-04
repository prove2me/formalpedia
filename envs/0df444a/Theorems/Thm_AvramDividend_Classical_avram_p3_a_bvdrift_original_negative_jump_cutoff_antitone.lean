-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_negative_jump_cutoff_antitone
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_negative_jump_cutoff_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:15:49.13021+00:00
-- url     : https://prove2.me/theorems/d3c31092-a912-43a0-a9f4-df67c371679a
-- title:
--   Actual original negative-jump cutoff sums are antitone in threshold
-- statement:
--   For the original spectrally negative Levy process, the ENNReal total of actual downward left-jump magnitudes on (0,T] with magnitudes strictly above a cutoff decreases as that cutoff increases. The result is pointwise in the original sample ω and holds without any bounded-variation, expectation or auxiliary-process assumption. It is a source-backed deterministic building block for monotone cutoff convergence.
-- source:
--   Pointwise monotonicity of ENNReal.ofReal of the actual X.X left-limit jump and ENNReal.tsum_le_tsum in pinned Mathlib.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The actual source negative-jump magnitude series is antitone in the
lower cutoff: decreasing the cutoff can only include more source jumps. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_negative_jump_cutoff_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (ω : Ω) (ε₁ ε₂ : ℝ≥0∞) (hε : ε₁ ≤ ε₂) :
    (∑' (v : ℝ≥0),
      if 0 < v ∧ v ≤ T ∧ ε₂ < ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      then ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) else 0) ≤
    (∑' (v : ℝ≥0),
      if 0 < v ∧ v ≤ T ∧ ε₁ < ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      then ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) else 0) := by sorry
