-- Prove2me | Theorems.Thm_ExAnteExPost_RPS_one_item_per_stage
-- name    : ExAnteExPost.RPS.one_item_per_stage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:36.361988+00:00
-- url     : https://prove2.me/theorems/b789e182-b566-480f-8c78-431eff307d47
-- title:
--   §3.1, p. 9 — by (3a) of Theorem 1, each agent receives exactly one item in each allocation of a stage's decomposition
-- statement:
--   Fix an instance, a favorite-good choice rule and a set of goods $M'$, and let $X = \mathrm{Eating}(M', 1)$. Let $X = \sum_{k} w^k A^k$ be any decomposition of $X$ satisfying the conclusions of Theorem 1. Then
--
--   1. every bundle uses only goods of $M'$: $A^k_i \subseteq M'$ for every $k$ and every agent $i$;
--   2. if $|M'| \ge n$, each agent receives exactly one item in each integral allocation:
--   $$|A^k_i| = 1 \quad \text{for every } k \text{ and every agent } i .$$
--
--   This is what makes each stage of Algorithm 1 assign one good to every agent and only goods still available.
--
--   **Formalization Note.** The statement covers every term of the decomposition, including terms of weight zero; part 1 follows from the column bound (3b), not from the weights.
-- source:
--   Freeman, Shah, Vaish, Best of Both Worlds: Ex-Ante and Ex-Post Fairness in Resource Allocation, arXiv:2005.14122v1, p. 9, §3.1

import Mathlib
import Definitions.Def_ExAnteExPost_RPS_Model

namespace ExAnteExPost.RPS
open Finset

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] [DecidableEq G]

/-- §3.1, p. 9: every integral allocation of a Theorem 1 decomposition of one eating stage on
`M'` uses only goods of `M'`, and gives every agent exactly one good when `n ≤ |M'|`. -/
theorem one_item_per_stage [Nonempty N] (I : Instance N G) (pick : PickRule N G)
    (hpick : IsFavoritePick I pick) (M' : Finset G) (d : Decomp N G)
    (hd : IsBvNDecomp (eating pick M') d) :
    (∀ k i, d.A k i ⊆ M') ∧ (Fintype.card N ≤ M'.card → ∀ k i, (d.A k i).card = 1) := by sorry
end ExAnteExPost.RPS
