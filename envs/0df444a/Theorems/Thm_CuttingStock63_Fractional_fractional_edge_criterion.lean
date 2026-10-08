-- Prove2me | Theorems.Thm_CuttingStock63_Fractional_fractional_edge_criterion
-- name    : CuttingStock63.Fractional.fractional_edge_criterion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:11:20.875028+00:00
-- url     : https://prove2.me/theorems/04abf014-be41-472a-9b3c-fed91d0970e2
-- title:
--   Customer Tolerances, p. 882 — for ζ = z₁/z₂, a basic feasible solution with no improving edge is a global minimum
-- statement:
--   Let $A$ be a real $m\times n$ matrix, $b\in\mathbb R^m$, and $c,d\in\mathbb R^n$. Consider the linear-fractional program
--   $$\text{minimize}\quad \zeta(x)=\frac{z_1(x)}{z_2(x)}=\frac{\sum_i c_ix_i}{\sum_i d_ix_i}\qquad\text{subject to}\quad Ax=b,\ x\ge0,$$
--   and assume the denominator is positive on the whole feasible set: $\sum_i d_ix_i>0$ whenever $Ax=b$, $x\ge0$.
--
--   Let $\bar x$ be a basic feasible solution with basis $B$ (that is, $|B|=m$, the columns $A_B$ are linearly independent, and $\bar x_k=0$ for $k\notin B$). Suppose that no edge leading from $\bar x$ improves the objective: for every nonbasic index $j\notin B$ and every edge direction $v$ of $x_j$ (so $Av=0$, $v_j=1$, $v_k=0$ for the other nonbasic $k$),
--   $$\frac{d}{d\tau}\,\zeta(\bar x+\tau v)\Big|_{\tau=0}\ \ge\ 0 .$$
--   Then $\bar x$ is a global minimum:
--   $$\zeta(\bar x)\le\zeta(x)\qquad\text{for every } x \text{ with } Ax=b,\ x\ge0 .$$
--
--   This is the justification of the paper's claim that "the ordinary simplex method can be used" for a ratio objective: the method moves from vertex to vertex, testing only the edges at the current vertex, and stops when no edge improves. In the cutting stock problem with customer tolerances, $c$ is the vector of pattern wastes $w_j$, $d$ is $1$ on the pattern columns and $0$ on the slack columns, so $\zeta$ is the fraction of waste.
--
--   **Formalization Note** The paper's sentence speaks of maximization; the statement is for minimization, the paper's actual problem ("minimize $\zeta$", p. 881); the maximization version is the same statement applied to $-c$. "In a domain where the denominator does not vanish" is taken as positivity on the feasible set (the paper's footnote: $\sum_jx_j>0$); on the convex feasible set a nonvanishing denominator has constant sign, and the negative case is the statement for $(-c,-d)$. The upper bounds $s_i\le N_i''-N_i'$ on the slacks are dropped, as the paper drops them on p. 882. The test quantifies over every nonbasic variable and every edge direction, feasible or not, as the simplex test does at a degenerate vertex; the derivative is Mathlib's `deriv`, the actual rate of change of $\zeta$.
-- source:
--   Gilmore & Gomory, A linear programming approach to the cutting stock problem—Part II, Opns. Res. 11 (1963), p. 882, Customer Tolerances, paragraph "It follows that the ordinary simplex method can be used to maximize a rational function … If no line yields any improvement, the calculation is finished" and its footnote; model of p. 881

import Mathlib
import Definitions.Def_DermanSeqDecisions_LinProg_LinearFractional
import Definitions.Def_MatousekLP_BFS_EquationalForm
import Definitions.Def_CuttingStock63_Fractional_Edge

namespace CuttingStock63.Fractional
open DermanSeqDecisions.LinProg
theorem fractional_edge_criterion {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c d : Fin n → ℝ) (B : Finset (Fin n)) (xbar : Fin n → ℝ)
    (hden : ∀ x, IsFeasible11 A b x → 0 < ∑ i, d i * x i)
    (hxbar : IsBasicFeasibleFor A b B xbar)
    (hedge : ∀ j, j ∉ B → ∀ v, IsEdgeDirection A B j v →
      0 ≤ deriv (fun τ : ℝ => fracObj c d (xbar + τ • v)) 0) :
    ∀ x, IsFeasible11 A b x → fracObj c d xbar ≤ fracObj c d x := by sorry
end CuttingStock63.Fractional
