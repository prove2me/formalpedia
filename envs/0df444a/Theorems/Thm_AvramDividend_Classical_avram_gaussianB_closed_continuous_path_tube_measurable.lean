-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_closed_continuous_path_tube_measurable
-- name    : AvramDividend.Classical.avram_gaussianB_closed_continuous_path_tube_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:35:45.794268+00:00
-- url     : https://prove2.me/theorems/64c7e007-b162-4592-b8ba-2d21c82091d5
-- title:
--   Closed uniform tube of a measurable continuous Brownian path lift is measurable
-- statement:
--   For a measurable continuous-path-valued random variable B on the unit interval, and fixed horizon T and radius r, the event that |B_t|≤r at every time t≤T is measurable. This uses an arbitrary intersection of closed point-evaluation bounds in continuous path space, avoiding false countability assumptions on uncountable time indices. It is a missing source-faithful prerequisite for turning the Proved canonical positive Brownian small-ball event into a measurable Gaussian localisation event.

import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.MeasureTheory.Constructions.Polish.Basic
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_closed_continuous_path_tube_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (C(unitInterval, ℝ))]
    [OpensMeasurableSpace (C(unitInterval, ℝ))]
    (B : Ω → C(unitInterval, ℝ)) (hB : Measurable B)
    (T : unitInterval) (r : ℝ) :
    MeasurableSet {ω | ∀ t : unitInterval, t ≤ T → |B ω t| ≤ r} := by sorry
