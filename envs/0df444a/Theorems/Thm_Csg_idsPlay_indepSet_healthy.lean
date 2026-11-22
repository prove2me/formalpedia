-- Prove2me | Theorems.Thm_Csg_idsPlay_indepSet_healthy
-- name    : Csg.idsPlay_indepSet_healthy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:26:04.60614+00:00
-- url     : https://prove2.me/theorems/315f0f7f-4568-4418-a809-2a6965fd443b
-- title:
--   Csg: ids Play indep Set healthy
-- statement:
--   Restating `idsPlay_indepFun_healthy` as independence of the *events* `{healthy at round n}`, the
--       shape `measure_limsup_eq_one` expects. **The one genuine gap flagged before this file's first
--       build attempt** (see the module docstring): no single ready-made Mathlib lemma performs exactly
--       this `iIndepFun → iIndepSet` conversion (confirmed again by reading
--       `Probability/Independence/Basic.lean` directly). Rather than the original comap/`generateFrom`
--       attempt, this instead restates both sides as the *same* measure-of-intersection identity --
--       `iIndepFun_iff_measure_inter_preimage_eq_mul` for the hypothesis, `iIndepSets_singleton_iff`
--       (via `iIndepSet_iff_iIndepSets_singleton`) for the goal -- and instantiates the former's
--       per-index target set at the constant `{true}`, landing exactly on the latter.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionRecurrence.lean#L244-L254
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionRecurrence.lean#L244-L254

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

theorem Csg.idsPlay_indepSet_healthy :
    iIndepSet (fun n => {ω : ℕ → PolicyAction × AttackAction | idsRoundHealthy (ω n) = true})
      (idsPlayMeasure q) := by sorry
