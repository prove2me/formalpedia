-- Prove2me | Theorems.Thm_Csg_idsRoundPMF_healthy
-- name    : Csg.idsRoundPMF_healthy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:26:14.834927+00:00
-- url     : https://prove2.me/theorems/81a7964b-0c10-4b9e-8af7-035d6fd6b9e3
-- title:
--   Csg: ids Round PMF healthy
-- statement:
--   **The key fact.** `P(round n = healthy) = 1/2`, for *any* oblivious attacker sequence `q` -- the
--       hand computation from the module docstring, now as a genuine `PMF`/outer-measure identity. The
--       `Finset.univ = {.defend1, .defend2}` rewrites are a self-contained way to unfold a two-element
--       `Fintype` sum without depending on whether `IntrusionDetection.lean`'s own `policyAction_sum`/
--       `attackAction_sum` helpers are stated generically enough for `ℝ≥0∞` (they were written for `ℝ`
--       payoffs; safer not to assume here).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionRecurrence.lean#L178-L213
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionRecurrence.lean#L178-L213

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

theorem Csg.idsRoundPMF_healthy (n : ℕ) :
    (idsRoundPMF q n).toOuterMeasure {p : PolicyAction × AttackAction | idsNext p.1 p.2 = .healthy}
      = 1 / 2 := by sorry
