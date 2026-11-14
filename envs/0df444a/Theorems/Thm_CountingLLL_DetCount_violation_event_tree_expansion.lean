-- Prove2me | Theorems.Thm_CountingLLL_DetCount_violation_event_tree_expansion
-- name    : CountingLLL.DetCount.violation_event_tree_expansion
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:27:21.422514+00:00
-- url     : https://prove2.me/theorems/9bab2904-7c38-4ea2-9054-ba944aa51a56
-- title:
--   Pointwise tree expansion intersected with an arbitrary event
-- statement:
--   For every event A and every root constraint r in E, the product-measure probability of A together with violation of r and satisfaction of E without r is the signed sum over rooted 2-trees T of the probability of A together with violation of every constraint in T and satisfaction of every free constraint. This is the eventwise form of equation (36), before division by any satisfaction probability; no feasibility or LLL assumption is needed.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, equation (36) in proof of Lemma 6.1, PDF p.22, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Expansion
open CountingLLL.DetCount

theorem CountingLLL.DetCount.violation_event_tree_expansion (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hr : r ∈ E) (A : Φ.Config → Prop) :
    Φ.prob (fun σ => A σ ∧ (¬ Φ.Sat r σ ∧ Φ.SatAll (E.erase r) σ)) =
      ∑ T ∈ Φ.twoTrees E r, (-1 : ℝ) ^ (T.card - 1) *
        Φ.prob (fun σ => A σ ∧ (Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free E r T) σ)) := by sorry
