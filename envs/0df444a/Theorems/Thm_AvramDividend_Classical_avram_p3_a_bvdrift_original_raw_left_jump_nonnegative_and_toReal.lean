-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:11:52.883206+00:00
-- url     : https://prove2.me/theorems/561ccef5-08ed-4169-b930-9bd8544810a6
-- title:
--   Original source left-jump magnitude is nonnegative and converts exactly from ENNReal to real
-- statement:
--   On the actual original spectrally negative Levy sample space, every positive-time raw negative left-jump magnitude leftLim X - X_t is nonnegative and equals the real conversion of its ENNReal.ofReal representation. This connects intrinsic ENNReal jump sums with the genuine signed real source path and needs no bounded-variation or compensator assumptions.
-- source:
--   Use the source cadlag left-limit axiom X.leftLim, pathwise X.noPosJumps and pinned Mathlib leftLim_eq_of_tendsto / ENNReal.toReal_ofReal, with the nontrivial nhdsLT.neBot side condition for positive time.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Every positive-time original negative left-jump magnitude is nonnegative,
and its ENNReal representation converts back to the raw real source jump. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    0 ≤ Function.leftLim (fun u : ℝ≥0 => X.X u ω) t - X.X t ω ∧
      (ENNReal.ofReal (Function.leftLim (fun u : ℝ≥0 => X.X u ω) t - X.X t ω)).toReal = Function.leftLim (fun u : ℝ≥0 => X.X u ω) t - X.X t ω := by sorry
