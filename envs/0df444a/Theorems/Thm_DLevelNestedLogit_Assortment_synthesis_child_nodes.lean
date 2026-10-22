-- Prove2me | Theorems.Thm_DLevelNestedLogit_Assortment_synthesis_child_nodes
-- name    : DLevelNestedLogit.Assortment.synthesis_child_nodes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T05:02:36.87221+00:00
-- url     : https://prove2.me/theorems/43382b26-d981-4b7c-9d71-9d3fb45e02ca
-- title:
--   Theorem 4.2 (Synthesis from child nodes): the union of optimal local solutions at the children solves the local problem at the parent
-- statement:
--   Consider a $d$-level nested logit model with $\eta_{\mathrm{root}}=0$, $\eta_j\in(0,1]$ at the other nonleaf nodes, and $v_0,\dots,v_n>0$. Let $S^*$ be an optimal solution of the assortment problem (3) and $t^*$ the scalars computed from it. Let $j$ be a nonleaf node, and suppose that for every child $k\in\mathrm{Children}(j)$ the set $\hat S_k\subseteq N_k$ is an optimal solution of the local problem at node $k$, $\max_{S_k\subseteq N_k}V_k(S_k)(R_k(S_k)-t^*_{\mathrm{Parent}(k)})$. Then
--   $$\bigcup_{k\in\mathrm{Children}(j)}\hat S_k\ \text{ is an optimal solution of }\ \max_{S_j\subseteq N_j}V_j(S_j)\big(R_j(S_j)-t^*_{\mathrm{Parent}(j)}\big).$$
--   The union is disjoint, since the sets $N_k$ of distinct children are disjoint.
--
--   The theorem lets the local problems be solved bottom-up, and is the inductive step of the corollary that characterizes an optimal assortment by revenue thresholds.
--
--   **Formalization Note.** $\hat S$ is any function from nodes to finsets of `Fin (n + 1)`; only its values at the children of $j$ matter, and "optimal for the local problem at $k$" includes $\hat S_k\subseteq N_k$ and $0\notin\hat S_k$. The thresholds $t^*_{\mathrm{Parent}(k)}=t^*_j$ are computed from the optimal $S^*$. Positivity of $v$ is presupposed by the model, not stated on the page.
-- source:
--   Li, Rusmevichientong, Topaloglu, The d-Level Nested Logit Model: Assortment and Price Optimization Problems, Oper. Res. 63(2), 2015, p. 329, Theorem 4.2

import Mathlib
import Definitions.Def_DLevelNestedLogit_Assortment_Tree
import Definitions.Def_DLevelNestedLogit_Assortment_Choice

namespace DLevelNestedLogit.Assortment

open ProductTree

theorem synthesis_child_nodes (n : ℕ) (T : ProductTree n) (η : T.Node → ℝ)
    (v r : Fin (n + 1) → ℝ) (hη : T.StandingEta η) (hv : ∀ i, 0 < v i)
    (Sstar : Finset (Fin (n + 1))) (hopt : T.IsOptimalAssortment η v r Sstar)
    (j : T.Node) (hj : ¬ T.IsLeaf j) (Shat : T.Node → Finset (Fin (n + 1)))
    (hShat : ∀ k ∈ T.children j, T.IsLocalOptimal η v r k (T.tparent η v r Sstar k) (Shat k)) :
    T.IsLocalOptimal η v r j (T.tparent η v r Sstar j) ((T.children j).biUnion Shat) := by sorry

end DLevelNestedLogit.Assortment
