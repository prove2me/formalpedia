-- Prove2me | Theorems.Thm_ComplementFreeCA_XOSRounding_expected_max_clause_lower_bound
-- name    : ComplementFreeCA.XOSRounding.expected_max_clause_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:27:01.319451+00:00
-- url     : https://prove2.me/theorems/7bfdf39d-afff-463b-8d76-c445baef7e62
-- title:
--   Lemma 3.3 — $E[Q_j]\ge(1-(1-1/n)^n)\sum_{i,S\ni j}x_{i,S}p^{(i,S)}_j$
-- statement:
--   Let $n\ge1$, let every bidder $i$ have an XOS valuation $v_i$ with admissible clause set $W_i$, and let $\mathrm{cl}_i$ be an XOS oracle for $v_i$; write $p^{(i,S)}=\mathrm{cl}_i(S)$ for the maximizing clause of $S$ in $v_i$. Let $x$ be a feasible solution of the LP relaxation and let $(S_1,\dots,S_n)$ be drawn by randomized rounding from $x$. For an item $j$ let $Q_j=\max_{i\in N}p^{(i,S_i)}_j$. Then for every item $j$,
--   $$\mathbb E[Q_j]\ \ge\ \Big(1-\Big(1-\frac1n\Big)^n\Big)\sum_{i\in N}\ \sum_{S\ni j}x_{i,S}\,p^{(i,S)}_j .$$
--
--   Summed over the items, the right-hand side is $(1-(1-1/n)^n)\,\mathrm{OPT}^*$, which yields the approximation ratio of Theorem 3.2.
--
--   **Formalization Note** The paper's display of Lemma 3.3 prints the sum over all pairs $(i,S)$. As printed it is false: a maximizing clause assigns values to items outside $S$ (two bidders, items $a,b$, both with the single clause $(1,1)$, $x_{1,\{a\}}=x_{2,\{b\}}=1$ give $Q_a=1<\tfrac34\cdot2$). The last line of the paper's proof restricts to $S\ni j$, which is what is stated here. Only feasibility of $x$ is assumed, not optimality.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 7, §3.2, Lemma 3.3 (statement), with the index set of the last display of its proof, p. 8

import Mathlib
import Definitions.Def_ComplementFreeCA_XOSRounding_Model
import Definitions.Def_ComplementFreeCA_XOSRounding_Rounding
import Definitions.Def_ComplementFreeCA_XOSRounding_Algorithm

namespace ComplementFreeCA.XOSRounding

open Finset

theorem expected_max_clause_lower_bound {n m : ℕ} (hn : 0 < n)
    (W : Fin n → Finset (Fin m → ℝ)) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsXOSWith (v i) (W i))
    (cl : Fin n → Finset (Fin m) → Fin m → ℝ) (hcl : ∀ i, IsXOSOracle (v i) (W i) (cl i))
    (x : Fin n → Finset (Fin m) → ℝ) (hx : IsLPFeasible x) (j : Fin m) :
    (1 - (1 - 1 / (n : ℝ)) ^ n) *
        ∑ i, ∑ S ∈ univ.filter (fun S : Finset (Fin m) => j ∈ S), x i S * cl i S j ≤
      roundingExpectation x (fun σ => maxClauseEntry hn cl σ j) := by sorry

end ComplementFreeCA.XOSRounding
