-- Prove2me | Theorems.Thm_DLevelNestedLogit_Assortment_recovering_optimal
-- name    : DLevelNestedLogit.Assortment.recovering_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T05:02:11.750016+00:00
-- url     : https://prove2.me/theorems/281bdad7-f07c-4bc3-8eab-fc6082c4087f
-- title:
--   Proposition 4.1 (Recovering optimal assortment): for an optimal S*, each S*_j solves the local problem at node j
-- statement:
--   Consider a $d$-level nested logit model with $\eta_{\mathrm{root}}=0$, $\eta_j\in(0,1]$ at the other nonleaf nodes, and attractiveness parameters $v_0,\dots,v_n>0$. Let $S^*\subseteq\{1,\dots,n\}$ be an optimal solution of the assortment problem (3), and let $t^*$ be the scalars computed from $S^*$. Then for every node $j$ of the tree, $S^*_j=S^*\cap N_j$ is an optimal solution of the local problem at node $j$:
--   $$S^*_j\in\operatorname*{arg\,max}_{S_j\subseteq N_j}\ V_j(S_j)\big(R_j(S_j)-t^*_{\mathrm{Parent}(j)}\big).$$
--
--   The scalar $t^*_{\mathrm{Parent}(j)}$ is thereby the minimum expected revenue a customer at node $j$ must bring for it to be worthwhile to offer any product below $j$.
--
--   **Formalization Note.** Positivity of $v_0,\dots,v_n$ is not stated on the page; the model presupposes it (it makes the denominators in (2) positive, including for the empty assortment). The value $R_j(\emptyset)=0$ at a nonleaf node, Lean's `x / 0 = 0`, enters $t^*$ when $S^*_j=\emptyset$.
-- source:
--   Li, Rusmevichientong, Topaloglu, The d-Level Nested Logit Model: Assortment and Price Optimization Problems, Oper. Res. 63(2), 2015, p. 329, Proposition 4.1

import Mathlib
import Definitions.Def_DLevelNestedLogit_Assortment_Tree
import Definitions.Def_DLevelNestedLogit_Assortment_Choice

namespace DLevelNestedLogit.Assortment

open ProductTree

theorem recovering_optimal (n : ℕ) (T : ProductTree n) (η : T.Node → ℝ) (v r : Fin (n + 1) → ℝ)
    (hη : T.StandingEta η) (hv : ∀ i, 0 < v i)
    (Sstar : Finset (Fin (n + 1))) (hopt : T.IsOptimalAssortment η v r Sstar) (j : T.Node) :
    T.IsLocalOptimal η v r j (T.tparent η v r Sstar j) (Sstar ∩ T.N j) := by sorry

end DLevelNestedLogit.Assortment
