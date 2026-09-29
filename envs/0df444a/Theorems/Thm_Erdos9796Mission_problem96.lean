-- Prove2me | Theorems.Thm_Erdos9796Mission_problem96
-- name    : Erdos9796Mission.problem96
-- status  : Disproved
-- author  : @mysticflounder
-- created : 2026-09-05T22:52:28.349821+00:00
-- url     : https://prove2.me/theorems/8ade9b04-8ed3-4b0a-a948-9a5df9f1c637
-- title:
--   Erdős Problem 96: linearly many unit distances in convex position
-- statement:
--   For each natural number $n$, let $U_c(n)$ be the supremum of the numbers of unordered unit-distance pairs determined by convex-independent sets of $n$ points in the Euclidean plane. Then
--
--   $$U_c(n)=O(n)\qquad(n\to\infty).$$
--
--   Thus there are a constant $C$ and a threshold after which $U_c(n)\le Cn$. Pairs are unordered and counted once. The set of counts is bounded by the number of two-element subsets. The formal target uses the natural-number supremum, real casts, and Big-O at the filter of natural numbers tending to infinity. It does not require the stronger explicit constant three. The mission's Problem 97 route would supply that constant; the unconditional Problem 96 target is still open in the repository.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/757d852766f377f7c1a0ffeeef6d3526bc0cb7a4/lean/Erdos9796Proof/P96/UpstreamBridge.lean#L96; https://www.erdosproblems.com/96

import Definitions.Def_Erdos9796Mission

/-!
The open Erdős Problem 96 statement in the self-contained mission vocabulary.
-/

theorem Erdos9796Mission.problem96 : Erdos9796Mission.Problem96 := by sorry
