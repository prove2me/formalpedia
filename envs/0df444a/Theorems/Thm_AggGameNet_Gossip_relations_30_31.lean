-- Prove2me | Theorems.Thm_AggGameNet_Gossip_relations_30_31
-- name    : AggGameNet.Gossip.relations_30_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:35:37.727111+00:00
-- url     : https://prove2.me/theorems/d10cae6a-0a7c-463f-8690-d9fc813695ae
-- title:
--   Relations (30)–(31), p. 18 — mean-square gossip contraction
-- statement:
--   For a connected gossip graph with strictly positive edge-contact probabilities, let $W$ average the pair $(a,b)$ and set $D=W-N^{-1}\mathbf1\mathbf1^T$. There is a constant $0<\lambda<1$ such that, for every $z\in\mathbb R^N$,
--
--   $$
--   \mathbb E\|Dz\|_2^2\le\lambda\|z\|_2^2,
--   \qquad
--   \mathbb E\|Dz\|_2\le\sqrt\lambda\|z\|_2.
--   $$
--
--   This is the spectral contraction governing how quickly gossip reduces disagreement.
--
--   **Formalization Note** Both expectations are the finite sums over ordered pairs $(a,b)$ weighted by $p_{ab}/N$, the exact one-tick law. The Euclidean norm is written as the square root of the coordinate sum of squares, avoiding Lean's sup norm on functions $\mathrm{Fin}\,N\to\mathbb R$.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, relations (30)–(31), p. 18

import Mathlib
import Definitions.Def_AggGameNet_Gossip_Setting

open MeasureTheory Filter Finset
open scoped BigOperators

namespace AggGameNet.Gossip

theorem relations_30_31 {N : ℕ} (hN : 0 < N)
    (G : SimpleGraph (Fin N)) (h7 : G.Connected)
    (p : Fin N → Fin N → ℝ) (hp : GossipProbs G p) :
    ∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧
      ∀ z : Fin N → ℝ,
        (∑ a, ∑ b, (p a b / (N : ℝ)) * euclidNorm (Dz a b z) ^ 2) ≤
            lam * euclidNorm z ^ 2 ∧
        (∑ a, ∑ b, (p a b / (N : ℝ)) * euclidNorm (Dz a b z)) ≤
            Real.sqrt lam * euclidNorm z := by sorry

end AggGameNet.Gossip
