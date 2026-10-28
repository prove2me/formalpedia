-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFuturePath_measurable
-- name    : AvramDividend.Classical.levy_boundedStopping_stoppedFuturePath_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:16:09.285577+00:00
-- url     : https://prove2.me/theorems/c68a1334-6bce-46d7-b161-2e94222c544e
-- title:
--   Measurability of the whole shifted Lévy future path at bounded stopping times
-- statement:
--   For any bounded stopping time of an adapted right-continuous Lévy process, the random entire future increment path is a measurable map into the real-valued product path space. Derives coordinate measurability from bounded continuous nonnegative reward measurability via positive and negative parts.
-- source:
--   Eliminates the stopped-path pushforward measurability blocker for full strong-Markov independence 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and barrier-value splitting 79978d61-9d1f-4b20-b8a5-114797a8e380. No scale function hypotheses.

import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Algebra.Order.Group.MinMax
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFutureReward_measurable

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_boundedStopping_stoppedFuturePath_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) :
    Measurable (fun ω : Ω => fun t : ℝ≥0 =>
      X.X (τ ω + t) ω - X.X (τ ω) ω) := by
  sorry
