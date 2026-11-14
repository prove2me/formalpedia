-- Prove2me | Theorems.Thm_CountingLLL_DetCount_lemma_6_1
-- name    : CountingLLL.DetCount.lemma_6_1
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:25:54.204042+00:00
-- url     : https://prove2.me/theorems/df56ac33-c461-4055-8763-ee37299d4b8e
-- title:
--   Two-tree expansion of the root-violation measure (Lemma 6.1)
-- statement:
--   Assume r is a constraint in E and E has at least one satisfying assignment. For every event A, the probability of A and violation of r under the uniform law conditioned on E without r is the signed sum over rooted two-trees in equation (35): unconditional probability of the tree-violation and near-free satisfaction event, times the source reciprocal-marginal product, times the probability of A under the distant-free law conditioned on that tree event. The enumeration is an arbitrary bijective enumeration of E without the root and distant-free family, and terms with zero tree-event probability evaluate to zero. This is the finite-event form of the signed-measure equality in Lemma 6.1; it does not assume Condition 1.1.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC submission #442, Lemma 6.1, equation (35), Section 6.1, PDF pp.21-22, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Expansion
open CountingLLL.DetCount
open CountingLLL.DetCount.CSP

theorem CountingLLL.DetCount.lemma_6_1 (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hr : r ∈ E) (hpos : 0 < Φ.Z E)
    (e : (T : Finset (Fin Φ.m)) →
      Fin ((E.erase r) \ (Φ.free E r T \ Φ.free1 E r T)).card → Fin Φ.m)
    (he : ∀ T ∈ Φ.twoTrees E r, Function.Injective (e T) ∧
      ∀ j, e T j ∈ (E.erase r) \ (Φ.free E r T \ Φ.free1 E r T))
    (A : Φ.Config → Prop) :
    Φ.prob (fun σ => A σ ∧ ¬ Φ.Sat r σ ∧ Φ.SatAll (E.erase r) σ) /
        Φ.prob (Φ.SatAll (E.erase r)) =
      ∑ T ∈ Φ.twoTrees E r,
        (-1 : ℝ) ^ (T.card - 1) *
        Φ.prob (fun σ => Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free1 E r T) σ) *
        (∏ j : Fin ((E.erase r) \ (Φ.free E r T \ Φ.free1 E r T)).card,
          1 / (1 - Φ.r (Φ.prefixFam (Φ.free E r T \ Φ.free1 E r T) (e T) j) (e T j))) *
        (Φ.prob (fun σ => A σ ∧ Φ.SatAll (Φ.free E r T \ Φ.free1 E r T) σ ∧
          (Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free1 E r T) σ)) /
         Φ.prob (fun σ => Φ.SatAll (Φ.free E r T \ Φ.free1 E r T) σ ∧
          (Φ.ViolAll T σ ∧ Φ.SatAll (Φ.free1 E r T) σ))) := by sorry
