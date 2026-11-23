-- Prove2me | Theorems.Thm_Csg_idsPlay_indepFun_healthy
-- name    : Csg.idsPlay_indepFun_healthy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:26:03.607499+00:00
-- url     : https://prove2.me/theorems/c2dc4215-3ffe-4d7b-bf98-c7a849070eae
-- title:
--   Csg: ids Play indep Fun healthy
-- statement:
--   **Independence.** `iIndepFun_infinitePi`, instantiated at the constant per-round map
--       `idsRoundHealthy`, gives independence of the family `fun n ω => idsRoundHealthy (ω n)`
--       directly -- `X` is passed explicitly (named), matching how the lemma is used in its own
--       source file rather than leaving it to be inferred.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionRecurrence.lean#L167-L170
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionRecurrence.lean#L167-L170

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

theorem Csg.idsPlay_indepFun_healthy :
    iIndepFun (fun n (ω : ℕ → PolicyAction × AttackAction) => idsRoundHealthy (ω n))
      (idsPlayMeasure q) := by sorry
