-- Prove2me | Theorems.Thm_CountingLLL_DetCount_tree_event_far_independence
-- name    : CountingLLL.DetCount.tree_event_far_independence
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:28:02.294887+00:00
-- url     : https://prove2.me/theorems/b371fba7-981d-47fd-adf7-6f879e4b05ca
-- title:
--   Tree event and distant-free satisfaction are independent
-- statement:
--   For every rooted 2-tree, the event that all distant free constraints are satisfied is independent, under the product measure, of the joint event that every tree constraint is violated and every nearby free constraint is satisfied. This disjoint-scope factorization needs no positivity or local-lemma condition and is used in the signed-measure expansion of Lemma 6.1.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, proof of Lemma 6.1, Section 6.1, PDF p.22, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Expansion
open CountingLLL.DetCount

theorem CountingLLL.DetCount.tree_event_far_independence (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hT : T ∈ Φ.twoTrees E r) :
    Φ.prob (fun σ => Φ.SatAll (Φ.free E r T \ Φ.free1 E r T) σ ∧
      (Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free1 E r T) σ)) =
      Φ.prob (Φ.SatAll (Φ.free E r T \ Φ.free1 E r T)) *
      Φ.prob (fun σ => Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free1 E r T) σ) := by sorry
