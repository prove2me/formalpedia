-- Prove2me | Theorems.Thm_CountingLLL_DetCount_lemma_5_1
-- name    : CountingLLL.DetCount.lemma_5_1
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:19:37.197303+00:00
-- url     : https://prove2.me/theorems/b8a3172e-2764-4894-9c99-12b48d1a5525
-- title:
--   Two-tree recursion for randomized marginal estimation (Lemma 5.1)
-- statement:
--   For a CSP satisfying Condition 1.1, a constraint family E and root r in E, sum over rooted 2-trees T. Let the distant-free base B_T be free(T) minus free^1(T), and enumerate every constraint in E minus ({r} union B_T) injectively. Starting from B_T, let each successive subfamily add the next enumerated constraint. Then the exact root marginal is the sum over T of (-1)^(|T|-1) times the unconditional probability that T is violated and free^1(T) is satisfied, multiplied by the reciprocal marginal factors for the successive subfamilies. This is the paper’s randomized-estimation recursion, equations (23)–(24).
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, Lemma 5.1, equations (23)-(24), Section 5.1, PDF pp.15-16, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Expansion
open CountingLLL.DetCount
open CountingLLL.DetCount.CSP

theorem CountingLLL.DetCount.lemma_5_1 (Φ : CSP) (hΦ : Φ.Condition11) (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hr : r ∈ E)
    (e : (T : Finset (Fin Φ.m)) →
      Fin ((E.erase r) \ (Φ.free E r T \ Φ.free1 E r T)).card → Fin Φ.m)
    (he : ∀ T ∈ Φ.twoTrees E r, Function.Injective (e T) ∧
      ∀ j, e T j ∈ (E.erase r) \ (Φ.free E r T \ Φ.free1 E r T)) :
    Φ.r E r = ∑ T ∈ Φ.twoTrees E r, (-1 : ℝ) ^ (T.card - 1) *
      Φ.prob (fun σ => Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free1 E r T) σ) *
      ∏ j : Fin ((E.erase r) \ (Φ.free E r T \ Φ.free1 E r T)).card,
        1 / (1 - Φ.r (Φ.prefixFam (Φ.free E r T \ Φ.free1 E r T) (e T) j) (e T j)) := by sorry
