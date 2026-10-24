-- Prove2me | Theorems.Thm_DecisionForest_Universal_depth_le_and_finite
-- name    : DecisionForest.Universal.depth_le_and_finite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:31.515264+00:00
-- url     : https://prove2.me/theorems/bb81231d-45c0-499b-8c93-356dedadffa8
-- title:
--   §3.2, p. 8 — Requirement 3 bounds the depth of a purchase decision tree by N + 1, so only finitely many trees satisfy Requirements 1–3
-- statement:
--   Let $N\ge 0$ be the number of products. Recall that a purchase decision tree splits on products (Requirement 1), that Requirement 3 asks the splits along every root-to-leaf path to carry pairwise distinct products, and that the depth of a tree is the number of nodes on a longest root-to-leaf path (a single leaf has depth $1$).
--
--   1. Every purchase decision tree $t$ satisfying Requirement 3 has
--   $$\mathrm{Depth}(t)\le N+1 .$$
--   2. The set of purchase decision trees satisfying Requirements 1–3 is finite.
--
--   The first part says that a path can test each of the $N$ products at most once; the second part is what makes "a distribution over $F_{N+1}$" in Theorem 1 a distribution over a finite set.
--
--   **Formalization Note** Trees are the inductive type `PTree N`, whose split nodes carry products of `Fin N`, so Requirement 1 holds for every tree of the type; `IsPurchaseTree` is Requirement 2 together with Requirement 3. Finiteness is `Set.Finite`.
--
--   Differences from the source:
--   - encoding: products $\{1,\dots,N\}$ → `Fin N` (product $k$ is `k - 1`); reason: Lean convention, same instances.
--   - encoding: Requirement 1 as a condition on trees → built into the type `PTree N`; reason: every split carries a product by construction, same trees.
-- source:
--   Chen and Mišić, Decision Forest: A Nonparametric Approach to Modeling Irrational Choice, arXiv:1904.11532v3, p. 8, §3.2 (remark after the definition of depth)

import Mathlib
import Definitions.Def_DecisionForest_Universal_Setting

namespace DecisionForest.Universal

theorem depth_le_and_finite (N : ℕ) :
    (∀ t : PTree N, Req3 t → depth t ≤ N + 1) ∧ {t : PTree N | IsPurchaseTree t}.Finite := by sorry

end DecisionForest.Universal
