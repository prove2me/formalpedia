-- Prove2me | Theorems.Thm_CountingLLL_DetCount_free_near_far_independence
-- name    : CountingLLL.DetCount.free_near_far_independence
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:16:22.191196+00:00
-- url     : https://prove2.me/theorems/2c9c592f-e616-44ca-aa24-2a80ae392dce
-- title:
--   Near and distant free-constraint independence
-- statement:
--   For any rooted 2-tree T, the satisfaction event of all free constraints factors into the satisfaction events of the nearby free constraints free^1(T) and the remaining distant free constraints. The underlying variable scopes are disjoint, so this identity holds under the product measure without any local-lemma or positivity assumption. It is the factorization used in Lemma 5.1.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, proof of Lemma 5.1, Section 5.1, PDF p.16, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Expansion
open CountingLLL.DetCount

theorem CountingLLL.DetCount.free_near_far_independence (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hT : T ∈ Φ.twoTrees E r) :
    Φ.prob (Φ.SatAll (Φ.free E r T)) =
      Φ.prob (Φ.SatAll (Φ.free1 E r T)) *
      Φ.prob (Φ.SatAll (Φ.free E r T \ Φ.free1 E r T)) := by sorry
