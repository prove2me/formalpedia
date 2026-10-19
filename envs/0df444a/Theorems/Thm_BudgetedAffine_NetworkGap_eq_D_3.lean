-- Prove2me | Theorems.Thm_BudgetedAffine_NetworkGap_eq_D_3
-- name    : BudgetedAffine.NetworkGap.eq_D_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:33.312444+00:00
-- url     : https://prove2.me/theorems/0526e89f-e8c7-4208-b140-76a4f6579a74
-- title:
--   (D.3), p. 36 — a feasible affine policy on arc (i, j) is the constant P_{(i,j),i} + q_{ij} = 0 off its own node
-- statement:
--   Consider the family of lot-sizing instances (7.2) with $m=2k$ nodes and $k\ge 2$. Let $(x,\,y(h)=Ph+q)$ be any feasible affine solution, where $P$ has one row per arc $(i,j)\in J_1\times J_2$ and one column per node, so that
--   $$y_{ij}(h)=\sum_{\ell=1}^m P_{(i,j),\ell}\,h_\ell+q_{ij}.$$
--   Then $x_i=1$ for every $i\in J_1$, and for every $i\in J_1$ and $j\in J_2$
--   $$P_{(i,j),i}+q_{ij}=0\qquad\text{and}\qquad P_{(i,j),\ell}=0\quad\text{for every node }\ell\ne i. \tag{D.3}$$
--
--   In words: no inventory can be shipped out of a $J_1$ node whose own demand is $1$, and an affine policy can only respect this on all such scenarios if the flow on arc $(i,j)$ depends on $h_i$ alone and vanishes at $h_i=1$. This rigidity is what forces affine policies to pay on $J_2$.
--
--   **Formalization Note** The hypothesis $k\ge 2$ ($m\ge 4$) is added and necessary. For $k=1$ the only scenario with $h_i=1$ is $e_i$, and (D.3) fails: $x=(1,\tfrac12)$, $y(h)=1-h_{J_1}-\tfrac12h_{J_2}$ is a feasible affine solution with $P_{(1,1),J_2}=-\tfrac12\ne0$. The paper's "$x_i=1$ for all $i\in J_1$" is derived from (D.2) at $h=e_i$ and the capacity $x_i\le1$. Lean indices are 0-based; $P$ has rows indexed by the arcs $J_1\times J_2$, the only arcs of finite distance.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, App. D, eq. (D.3) and the paragraph before it, p. 36

import Mathlib
import Definitions.Def_BudgetedAffine_NetworkGap_LotSizing
import Definitions.Def_BudgetedAffine_NetworkGap_Instance

namespace BudgetedAffine.NetworkGap

/-- App. D, p. 36, (D.3): for `k ≥ 2` (`m ≥ 4`), every feasible affine solution
`(x, y(h) = P h + q)` of the family (7.2) has `x_i = 1` on `J₁`, and for every arc `(i, j)`
`P_{(i,j),i} + q_{ij} = 0` and `P_{(i,j),ℓ} = 0` for every node `ℓ ≠ i`. -/
theorem eq_D_3 (k : ℕ) (hk : 2 ≤ k) (x : Node k → ℝ) (P : Matrix (Arc k) (Node k) ℝ)
    (q : Arc k → ℝ) (hfeas : (lotSizingFamily k).Feasible x (LotSizing.affinePolicy P q)) :
    (∀ i, x (Sum.inl i) = 1) ∧
      ∀ i j, P (i, j) (Sum.inl i) + q (i, j) = 0 ∧
        ∀ v, v ≠ Sum.inl i → P (i, j) v = 0 := by sorry

end BudgetedAffine.NetworkGap
