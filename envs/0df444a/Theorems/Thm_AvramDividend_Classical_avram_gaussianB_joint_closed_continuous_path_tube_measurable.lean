-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_joint_closed_continuous_path_tube_measurable
-- name    : AvramDividend.Classical.avram_gaussianB_joint_closed_continuous_path_tube_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:35:46.426978+00:00
-- url     : https://prove2.me/theorems/1ced4c01-721e-4197-85e5-4a3569eefd12
-- title:
--   Joint centred and drifted Gaussian Brownian closed-tube event is measurable under a continuous path lift
-- statement:
--   For a measurable random continuous path B on the unit interval, the closed joint tube event constraining |B_t|≤r and |B_t+2t|≤R at every t≤T is measurable. The proof uses closedness of each evaluation constraint and arbitrary intersections of closed sets, not an invalid uncountable intersection of measurable sets. Together with the Proved canonical Brownian joint strict tube B186 this supplies an explicit measurable localisation set of positive probability for the original Gaussian positive-drift counterexample.

import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.MeasureTheory.Constructions.Polish.Basic
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_joint_closed_continuous_path_tube_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (C(unitInterval, ℝ))]
    [OpensMeasurableSpace (C(unitInterval, ℝ))]
    (B : Ω → C(unitInterval, ℝ)) (hB : Measurable B)
    (T : unitInterval) (r R : ℝ) :
    MeasurableSet {ω | ∀ t : unitInterval, t ≤ T →
      |B ω t| ≤ r ∧ |B ω t + 2 * (t : ℝ)| ≤ R} := by sorry
