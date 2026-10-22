-- Prove2me | Theorems.Thm_DLevelNestedLogit_Assortment_revenue_comparison
-- name    : DLevelNestedLogit.Assortment.revenue_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T05:02:47.183212+00:00
-- url     : https://prove2.me/theorems/ef2c1598-32a0-49af-a3d1-162e3788bc94
-- title:
--   Corollary 4.3 (Revenue comparison): Ŝ = {l : r_l ≥ t*_Parent(l)} is an optimal assortment
-- statement:
--   Consider a $d$-level nested logit model: a $d$-level product tree whose leaves are the products $1,\dots,n$ and the no-purchase option $0$, nest parameters with $\eta_{\mathrm{root}}=0$ and $\eta_j\in(0,1]$ at the other nonleaf nodes, attractiveness parameters $v_0,\dots,v_n>0$, and revenues $r_1,\dots,r_n$ of any sign. Let $S^*\subseteq\{1,\dots,n\}$ be any optimal solution of the assortment problem
--   $$Z^*=\max_{S\subseteq\{1,\dots,n\}}R_{\mathrm{root}}(S_{\mathrm{root}}),$$
--   and let $t^*_j=\max\{t^*_{\mathrm{Parent}(j)},\ \eta_jt^*_{\mathrm{Parent}(j)}+(1-\eta_j)R_j(S^*_j)\}$ with $t^*_{\mathrm{Parent}(\mathrm{root})}=0$. Then
--   $$\hat S=\{\,l\in\{1,\dots,n\}:\ r_l\ge t^*_{\mathrm{Parent}(l)}\,\}$$
--   is an optimal solution of the assortment problem: $R_{\mathrm{root}}(S_{\mathrm{root}})\le R_{\mathrm{root}}(\hat S_{\mathrm{root}})$ for every $S\subseteq\{1,\dots,n\}$.
--
--   An optimal assortment is thus found by comparing each product's revenue with a threshold attached to its parent node: if a product is offered, so is every product with a larger revenue under the same parent. For one level this recovers the optimality of revenue-ordered assortments under the multinomial logit model, and for two levels the characterization of Davis, Gallego and Topaloglu (2014).
--
--   **Formalization Note.** The thresholds are computed from the given optimal $S^*$ (a function of it, not free parameters), and the conclusion is optimality ($\forall S$) rather than equality with a supremum. Positivity of $v_0,\dots,v_n$ is presupposed by the model, not stated on the page. $R_j(\emptyset)=0$ at a nonleaf node by Lean's `x / 0 = 0`. The comparison is `≤` (ties are included in $\hat S$).
-- source:
--   Li, Rusmevichientong, Topaloglu, The d-Level Nested Logit Model: Assortment and Price Optimization Problems, Oper. Res. 63(2), 2015, p. 330, Corollary 4.3

import Mathlib
import Definitions.Def_DLevelNestedLogit_Assortment_Tree
import Definitions.Def_DLevelNestedLogit_Assortment_Choice

namespace DLevelNestedLogit.Assortment

open ProductTree

theorem revenue_comparison (n : ℕ) (T : ProductTree n) (η : T.Node → ℝ) (v r : Fin (n + 1) → ℝ)
    (hη : T.StandingEta η) (hv : ∀ i, 0 < v i)
    (Sstar : Finset (Fin (n + 1))) (hopt : T.IsOptimalAssortment η v r Sstar) :
    T.IsOptimalAssortment η v r
      (Finset.univ.filter (fun l : Fin (n + 1) => l ≠ 0 ∧ T.tparent η v r Sstar (T.leaf l) ≤ r l)) := by sorry

end DLevelNestedLogit.Assortment
