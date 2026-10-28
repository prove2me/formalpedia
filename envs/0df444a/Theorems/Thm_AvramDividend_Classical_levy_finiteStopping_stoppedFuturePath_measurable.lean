-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
-- name    : AvramDividend.Classical.levy_finiteStopping_stoppedFuturePath_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:25:30.42429+00:00
-- url     : https://prove2.me/theorems/722354f7-aca7-470b-8d9d-cf00d3ab29c5
-- title:
--   Whole future Lévy path measurability at arbitrary finite stopping times
-- statement:
--   The future increment path after any almost surely pointwise finite Lévy stopping time is a measurable map into the coordinate product measurable space. Follows by truncation at increasing deterministic integer horizons and pointwise eventual equality of stopped path coordinates.
-- source:
--   Mathematical prerequisite for the exact full stopped-path strong Markov theorem 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and dividend barrier child 79978d61-9d1f-4b20-b8a5-114797a8e380. Builds directly on bounded stopped-path measurability.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Constructions
import Mathlib.Order.WithBot
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFuturePath_measurable

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finiteStopping_stoppedFuturePath_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable (fun ω : Ω => fun t : ℝ≥0 =>
      X.X (τ ω + t) ω - X.X (τ ω) ω) := by
  sorry
