-- Prove2me | Theorems.Thm_Csg_idsRoundHealthy_measure_true
-- name    : Csg.idsRoundHealthy_measure_true
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:26:16.263526+00:00
-- url     : https://prove2.me/theorems/4f596cb0-156b-4016-8fa9-07364c6d9d65
-- title:
--   Csg: ids Round Healthy measure true
-- statement:
--   The `.toOuterMeasure` fact above, transported to `idsPlayMeasure`'s own coordinate-`n` marginal
--       via `infinitePi_map_eval` (the marginal of an infinite product measure at any one coordinate is
--       exactly that coordinate's own factor measure) and the standard `PMF.toMeasure`/`toOuterMeasure`
--       coincidence on measurable sets.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionRecurrence.lean#L219-L233
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionRecurrence.lean#L219-L233

import Definitions.Def_Csg_IntrusionDetection
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Definitions.Def_Csg_IntrusionDetectionRecurrence
set_option autoImplicit true
open Csg
open MeasureTheory Measure ProbabilityTheory
variable (q : ℕ → PMF AttackAction)

theorem Csg.idsRoundHealthy_measure_true (n : ℕ) :
    (idsPlayMeasure q) {ω : ℕ → PolicyAction × AttackAction | idsRoundHealthy (ω n) = true}
      = 1 / 2 := by sorry
