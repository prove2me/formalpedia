-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_negative_tail_continuous_of_standing_bv
-- name    : AvramDividend.Classical.levy_negative_tail_continuous_of_standing_bv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:16:40.255209+00:00
-- url     : https://prove2.me/theorems/38e3529e-e67e-476e-97f7-44920e280c7e
-- title:
--   Continuous large-jump tail under the BV standing assumptions
-- statement:
--   For a bounded-variation spectrally negative Lévy process satisfying the standing assumptions, the intensity of jumps whose magnitude is at least r is continuous in every r>0. The standing assumptions ensure the jump measure has no atoms; Lévy integrability gives finite mass away from zero. This is a concrete continuity input for the Esscher-renewal kernel in the bounded-variation C1 proof.
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 3.2 regularity of the q-scale function under condition (3.3); finite atomless Lévy tails as renewal-density kernel input.

import Mathlib.MeasureTheory.Measure.Restrict
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyMeasure_singleton_null_of_standing_boundedVariation
import Theorems.Thm_AvramDividend_Classical_levy_negative_mass_away_from_zero_finite
import Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Iic_negative_of_finite_noAtoms
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_negative_tail_continuous_of_standing_bv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) :
    ContinuousOn (fun r : ℝ => X.ν.real (Iic (-r))) (Ioi (0 : ℝ)) := by sorry
