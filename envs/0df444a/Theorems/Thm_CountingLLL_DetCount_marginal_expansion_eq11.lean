-- Prove2me | Theorems.Thm_CountingLLL_DetCount_marginal_expansion_eq11
-- name    : CountingLLL.DetCount.marginal_expansion_eq11
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:22:56.179064+00:00
-- url     : https://prove2.me/theorems/6a1dd12f-d5b8-4c69-b167-a696652606b4
-- title:
--   Canonical-tree marginal expansion before telescoping
-- statement:
--   For a CSP satisfying Condition 1.1, the root violation marginal equals the sum over rooted canonical 2-trees of the signed conditional tree coefficient multiplied by the ratio between free-set satisfaction probability and root-deleted-family satisfaction probability. This is equation (11), obtained by regrouping inclusion–exclusion before applying the probability telescope.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, equation (11), Section 3.3, PDF p.10, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Expansion
open CountingLLL.DetCount

theorem CountingLLL.DetCount.marginal_expansion_eq11 (Φ : CSP) (hΦ : Φ.Condition11)
    (E : Finset (Fin Φ.m)) (r : Fin Φ.m) (hr : r ∈ E) :
    Φ.r E r = ∑ T ∈ Φ.twoTrees E r,
      (-1 : ℝ) ^ (T.card - 1) * Φ.treeCoeff E r T *
        (Φ.prob (Φ.SatAll (Φ.free E r T)) / Φ.prob (Φ.SatAll (E.erase r))) := by sorry
