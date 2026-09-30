-- Prove2me | Theorems.Thm_ComplementFreeCA_XOSRounding_alg_ge_sum_max_clause
-- name    : ComplementFreeCA.XOSRounding.alg_ge_sum_max_clause
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:23:20.671926+00:00
-- url     : https://prove2.me/theorems/448d2c93-052b-42aa-ad58-08f2454ad657
-- title:
--   $ALG \ge \sum_j Q_j$ for every preallocation
-- statement:
--   Let every bidder $i$ have an XOS valuation $v_i$ with admissible clause set $W_i$, let $\mathrm{cl}_i$ be an XOS oracle for $v_i$, and let $\mathrm{win}$ be a highest-clause assignment rule. Fix any preallocation $\sigma=(S_1,\dots,S_n)$, write $p^i=\mathrm{cl}_i(S_i)$ and $Q_j=\max_{i}p^i_j$, and let $\mathrm{ALG}(\sigma)$ be the welfare of the allocation that gives each item $j$ to bidder $\mathrm{win}(\sigma,j)$. Then
--   $$\sum_{j\in M} Q_j\ \le\ \mathrm{ALG}(\sigma).$$
--
--   The inequality holds pointwise, for every outcome of the rounding step; it reduces the analysis of the algorithm to a lower bound on the expectation of each $Q_j$ separately.
--
--   **Formalization Note** The paper justifies the step by the clause bound $\sum_{j\in T}p^{(i,S)}_j\le v_i(T)$ "for every $T\subseteq S$". The bundle a bidder receives need not lie inside its preallocated bundle, so the argument uses the bound for every $T$, which holds because $p^{(i,S)}$ is a clause of $v_i$'s expression. At least one bidder ($n\ge1$) is assumed.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 7, §3.2, proof of Theorem 3.2, paragraph after the first display (ALG ≥ Σ_j Q_j)

import Mathlib
import Definitions.Def_ComplementFreeCA_XOSRounding_Model
import Definitions.Def_ComplementFreeCA_XOSRounding_Algorithm

namespace ComplementFreeCA.XOSRounding

theorem alg_ge_sum_max_clause {n m : ℕ} (hn : 0 < n)
    (W : Fin n → Finset (Fin m → ℝ)) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsXOSWith (v i) (W i))
    (cl : Fin n → Finset (Fin m) → Fin m → ℝ) (hcl : ∀ i, IsXOSOracle (v i) (W i) (cl i))
    (win : (Fin n → Finset (Fin m)) → Fin m → Fin n) (hwin : IsHighestClauseRule cl win)
    (σ : Fin n → Finset (Fin m)) :
    ∑ j, maxClauseEntry hn cl σ j ≤ algWelfare v win σ := by sorry

end ComplementFreeCA.XOSRounding
