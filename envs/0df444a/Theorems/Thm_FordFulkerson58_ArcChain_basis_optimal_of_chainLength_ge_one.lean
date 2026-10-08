-- Prove2me | Theorems.Thm_FordFulkerson58_ArcChain_basis_optimal_of_chainLength_ge_one
-- name    : FordFulkerson58.ArcChain.basis_optimal_of_chainLength_ge_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:38:10.521797+00:00
-- url     : https://prove2.me/theorems/f0292a24-1034-4c91-9988-f46b75cbd27b
-- title:
--   §3, p. 1779 — with all α_r ≥ 0 and every commodity chain of length Σ α_r a_rs ≥ 1, the arc-chain basis is optimal
-- statement:
--   Consider the arc-chain program (2)–(3) of a multi-commodity network. Let $B$ be a basis (columns $s_1,\dots,s_m$ of $[A\mid I]$ with invertible submatrix), $z$ its basic feasible solution, and $\alpha_1,\dots,\alpha_m$ its simplex multipliers (4). Interpret $\alpha_r$ as the length of arc $A_r$. Suppose that
--
--   1. $\alpha_r \ge 0$ for every arc $r$, and
--   2. every commodity chain $C_s$ has length at least one: $\sum_{r=1}^{m} \alpha_r a_{rs} \ge 1$ for all $s$.
--
--   Then the basis is optimal: for every feasible solution $(x, x_{n+1},\dots,x_{n+m})$ of (3),
--   $$\sum_{s=1}^{n} x_s \;\le\; \sum_{s=1}^{n} z_s .$$
--
--   This is the optimality half of the pricing test of §3: once no chain is shorter than its objective coefficient $1$, no column can enter and the simplex computation stops.
--
--   **Formalization Note** Optimality is stated against every feasible $(x, y)$, with no supremum. The LP fact behind it is the simplex optimality criterion / weak duality, available as the referenced items `MatousekLP.Simplex.optimality_criterion` and `MatousekLP.Duality.weak_duality`.
-- source:
--   Ford and Fulkerson, A suggested computation for maximal multi-commodity network flows, Management Sci. 50(12S) (2004), p. 1779, §3 ("If each of the chains thus selected has length at least one, the basis is optimal")

import Mathlib
import Definitions.Def_FordFulkerson58_ArcChain_Network
import Definitions.Def_FordFulkerson58_ArcChain_LP
import Definitions.Def_FordFulkerson58_ArcChain_Labeling

namespace FordFulkerson58.ArcChain

/-- §3, p. 1779: if the simplex multipliers of a feasible basis are non-negative and every commodity
chain has length `∑_r α_r a_rs ≥ 1` (the arc lengths being the multipliers), the basis is optimal: no
feasible flow has a larger total than the basic solution. -/
theorem basis_optimal_of_chainLength_ge_one {V E ι : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype ι] [DecidableEq ι] (N : Network V E ι)
    (β : E → Col N ⊕ E) (hβ : IsUnit (basisMatrix N β).det)
    (z : Col N ⊕ E → ℝ) (hz : IsBasicFeasibleSolution N β z)
    (α : E → ℝ) (h4 : IsSimplexMultiplier N β α)
    (hα : ∀ r, 0 ≤ α r) (hlen : ∀ s : Col N, (1 : ℝ) ≤ chainLength α s.1.2) :
    ∀ (x : Col N → ℝ) (y : E → ℝ), Feasible N x y → ∑ s, x s ≤ ∑ s, z (Sum.inl s) := by sorry

end FordFulkerson58.ArcChain
