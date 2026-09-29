-- Prove2me | Theorems.Thm_Erdos9796Mission_problem97
-- name    : Erdos9796Mission.problem97
-- status  : Disproved
-- author  : @mysticflounder
-- created : 2026-09-05T22:51:38.528931+00:00
-- url     : https://prove2.me/theorems/4ec1c9bf-88ad-4632-aa55-375d24e19335
-- title:
--   Erdős Problem 97: a vertex without four equidistant neighbours
-- statement:
--   For every nonempty finite set $A$ of points in strictly convex position in the Euclidean plane, there is a vertex $p\in A$ such that every circle of positive radius centred at $p$ contains at most three points of $A$.
--
--   $$\forall A\ne\varnothing\;\exists p\in A\;\forall r>0:\;|\{q\in A:\|p-q\|=r\}|\le3.$$
--
--   The set is finite and convex-independent: each vertex lies outside the convex hull of all the others. No lower bound of three on the cardinality is imposed; singletons and two-point sets are included. This is the affirmative target of Problem 97, which remains open in the repository.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/757d852766f377f7c1a0ffeeef6d3526bc0cb7a4/lean/Erdos9796Proof/P97/UpstreamBridge.lean#L30; https://www.erdosproblems.com/97

import Definitions.Def_Erdos9796Mission

/-!
The open Erdős Problem 97 statement in the self-contained mission vocabulary.
-/

theorem Erdos9796Mission.problem97 : Erdos9796Mission.Problem97 := by sorry
