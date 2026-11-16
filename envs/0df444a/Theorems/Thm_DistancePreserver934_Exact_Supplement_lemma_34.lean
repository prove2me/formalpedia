-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_Supplement_lemma_34
-- name    : DistancePreserver934.Exact.Supplement.lemma_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:27:00.983049+00:00
-- url     : https://prove2.me/theorems/44827cad-8d1b-44f8-9239-95f34ee115b0
-- title:
--   Lemma 34 — Both sampling reductions, with exact sample-size and half-demand guarantees
-- statement:
--   Let $p=|P|>0$, $d\ge1$ be real and $\beta\ge0$ an integer. Both constructions provide $J_0\subseteq G$ and $R\subseteq V$ with the same explicit bounds
--
--   $$|E(J_0)|\le15nd,\qquad |R|\le p/d^2.$$
--
--   1. If $P\subseteq S\times V$, then adjoining any additive $+\beta$ spanner for the reachable pairs in $S\times R$ satisfies at least half of the original $P$ with additive error $\beta+2$.
--   2. For arbitrary $P$, adjoining any additive $+\beta$ spanner for the reachable pairs in $R\times R$ satisfies at least half of $P$ with error $\beta+4$.
--
--   Each construction chooses its own $J_0,R$ before quantification over the auxiliary spanner. The sets may differ between clauses and $R$ may be empty. This deterministic reduction serves both Theorems 36 and 37. The numerical coefficient 15 is supplied by the proof on printed p. 31.
--
--   Differences from the source:
--   - encoding: finite graphs on n vertices, with the section demand convention → an arbitrary finite vertex type, unordered technical demands in §4 and §7.1–7.2 and ordered demands in Definition 26 and §8; reason: the published graph and extended-distance definitions retain exactly these instances; undirected edges are counted once
--   - encoding: O(nd) edges for each sampling construction → at most 15nd edges for each construction; reason: the proof gives |E(J0)|<3n ceil(4d)≤15nd, with exactly the same instances
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026); canonical source.pdf SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b; Lemma 34, printed p. 30–31 (PDF p. 31–32)

import Definitions.Def_DistancePreserver934_Exact_Supplement_EdgePaths
import Definitions.Def_DistancePreserver934_Exact_Supplement_Hitting
import Definitions.Def_DistancePreserver934_Exact_Supplement_Sourcewise
import Definitions.Def_DistancePreserver934_Exact_Supplement_Budgets

set_option autoImplicit false

namespace DistancePreserver934.Exact.Supplement

open Classical

theorem lemma_34 :

  ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (P : Finset (V × V))
    (S : Finset V) (d : ℝ) (β : ℕ),
    0 < P.card → 1 ≤ d →
    ((SourceDemands S P → ∃ (J0 : SimpleGraph V) (R : Finset V),
      J0 ≤ G ∧ (numEdges J0 : ℝ) ≤ 15 * (Fintype.card V : ℝ) * d ∧
      (R.card : ℝ) ≤ (P.card : ℝ) / d ^ 2 ∧
      ∀ Jaux : SimpleGraph V, IsAdditive G Jaux (reachablePairs G S R) β →
        HalfSatisfied G (J0 ⊔ Jaux) P (β + 2)) ∧
    (∃ (J0 : SimpleGraph V) (R : Finset V),
      J0 ≤ G ∧ (numEdges J0 : ℝ) ≤ 15 * (Fintype.card V : ℝ) * d ∧
      (R.card : ℝ) ≤ (P.card : ℝ) / d ^ 2 ∧
      ∀ Jaux : SimpleGraph V, IsAdditive G Jaux (reachablePairs G R R) β →
        HalfSatisfied G (J0 ⊔ Jaux) P (β + 4)))
 := by sorry

end DistancePreserver934.Exact.Supplement
