-- Prove2me | Theorems.Thm_BudgetClock_Subadditive_subadditive_cover
-- name    : BudgetClock.Subadditive.subadditive_cover
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:28.68513+00:00
-- url     : https://prove2.me/theorems/c2145437-4eb6-4ae2-95a2-09a21a4ec7f2
-- title:
--   Proof of Theorem 8, p. 16 — Σ_{i=1}^{r+1} v(Z_i) ≥ v(O) when O = Z_1 ∪ … ∪ Z_{r+1}
-- statement:
--   Let $v : 2^N \to \mathbb{R}$ be subadditive, let $r \in \mathbb{N}$, and let $Z_1, \dots, Z_{r+1} \subseteq N$ be sets whose union is $O$. Then
--
--   $$v(O) \le \sum_{i=1}^{r+1} v(Z_i).$$
--
--   In the proof of Theorem 8 the sets $Z_i$ partition the optimal set $O$; this inequality turns the assumption that every block has small value into an upper bound on $v(O)$, which drives the second case of the proof.
--
--   **Formalization Note** The blocks are indexed by `Fin (r + 1)`, so there is at least one block, as in the paper. With no block the claim would read $v(\emptyset) \le 0$, which subadditivity alone does not give. Disjointness of the blocks is not needed and not assumed, which makes the statement slightly more general than the paper's use.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 16, proof of Theorem 8, second case

import Mathlib
import Definitions.Def_BudgetClock_Subadditive_Setting

namespace BudgetClock.Subadditive

theorem subadditive_cover {n : ℕ} (v : Finset (Fin n) → ℝ) (hsub : IsSubadditive v)
    (r : ℕ) (Z : Fin (r + 1) → Finset (Fin n)) (O : Finset (Fin n))
    (hO : O = Finset.univ.biUnion Z) :
    v O ≤ ∑ i : Fin (r + 1), v (Z i) := by sorry

end BudgetClock.Subadditive
