-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_jump_magnitude_sfinite
-- name    : AvramDividend.Classical.bv_jump_magnitude_sfinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T22:54:30.051888+00:00
-- url     : https://prove2.me/theorems/8f6d4571-1174-41ff-a0e6-d1bdd1e1bf78
-- title:
--   S-finiteness of the BV Lévy jump-magnitude pushforward under Standing
-- statement:
--   For a spectrally negative Levy process satisfying the classical Standing condition and bounded variation, the jump measure on negative jumps is absolutely continuous with respect to Lebesgue measure by Condition33. Consequently it is s-finite; the pushforward measure of jump magnitudes z=max(-y,0) on nonnegative reals is also s-finite. This supplies a required hypothesis to the already Proved positiveLaplace_tilted_kernel_measure theorem in constructing a positive renewal representation of the q scale function.
-- source:
--   Condition33 in Avram, Palmowski and Pistorius, arXiv:math/0702893v1; pinned Mathlib MeasureTheory.sFinite_of_absolutelyContinuous, Measure.isFiniteMeasure_map and Measure.map_sum; local campaign BV_SHIFTED_POSITIVE_RENEWAL_20261006.md.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_jump_magnitude_sfinite
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) :
    SFinite (X.ν.map (fun y : ℝ => Real.toNNReal (-y))) := by sorry
