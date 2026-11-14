-- Prove2me | Theorems.Thm_CountingLLL_DetCount_tested_card_bound
-- name    : CountingLLL.DetCount.tested_card_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:11:44.549906+00:00
-- url     : https://prove2.me/theorems/13b9d51b-e40b-4895-90c4-0f795d3c57ea
-- title:
--   Number of non-root exploration tests
-- statement:
--   For a rooted 2-tree T of the constraint dependency graph, the set of constraints tested after the root in its canonical transcript consists of the accepted non-root constraints and the rejected constraints. Its cardinality is at most D^2 |T|, where D is the maximum dependency degree of the full CSP. This proves the deterministic test-count ingredient used in the expected exploration-size bound (32); the probabilistic conditional test law remains separate.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, proof of Lemma 5.7, Section 5.2.3, equation (32), PDF p.20, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Expansion
open CountingLLL.DetCount

theorem CountingLLL.DetCount.tested_card_bound (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hT : T ∈ Φ.twoTrees E r) :
    (Φ.rest E r T).card ≤ Φ.Dmax^2 * T.card := by sorry
