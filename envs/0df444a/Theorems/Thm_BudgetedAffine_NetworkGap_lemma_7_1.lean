-- Prove2me | Theorems.Thm_BudgetedAffine_NetworkGap_lemma_7_1
-- name    : BudgetedAffine.NetworkGap.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:54.971497+00:00
-- url     : https://prove2.me/theorems/a6972fc4-403c-4253-9ab1-a5240a0ec0d1
-- title:
--   Lemma 7.1 — on the lot-sizing family (7.2), z_AR(U) = 0 and z_Aff(U) = m/2 − 1
-- statement:
--   Consider the two-stage robust lot-sizing problem (7.1) on the family of instances (7.2): $m=2k$ nodes with $k\ge1$ split into $J_1$ and $J_2$, $|J_1|=|J_2|=m/2$; inventory costs $c_i=0$ on $J_1$ and $c_i=1$ on $J_2$; capacities $K_i=1$; distances $d_{ij}=0$ from $J_1$ to $J_2$ and $\infty$ otherwise; and demand uncertainty
--   $$\mathcal U=\Big\{h\in[0,1]^m\ \Big|\ \sum_{i=1}^m h_i\le m/2\Big\}.$$
--   Then the optimal adjustable value and the optimal affine value are
--   $$z_{AR}(\mathcal U)=0\qquad\text{and}\qquad z_{Aff}(\mathcal U)=\frac m2-1,$$
--   both attained. In particular the gap between affine and adjustable policies is unbounded as $m\to\infty$.
--
--   The recourse matrix of (7.1) is a network matrix with entries in $\{-1,0,1\}$. The lemma shows that the non-negativity of the recourse matrix, under which the paper proves its $O(\log n/\log\log n)$ approximation bounds for affine policies, cannot be dropped.
--
--   **Formalization Note** Each optimal value is stated as `IsLeast` of the set of objective values $t$ for which some feasible solution (adjustable, resp. affine $y(h)=Ph+q$) has cost at most $t$ in every scenario; this asserts that the value is attained and is the minimum, and cannot hold vacuously. The distances $d_{ij}=\infty$ are encoded by keeping only the arcs $J_1\times J_2$ (a solution of finite cost never uses another arc); $P$ has one row per kept arc, as in App. D. The paper's "$m$ even" is $m=2k$, and $k\ge1$ makes $J_1,J_2$ nonempty. The unboundedness of the gap is the immediate consequence $z_{Aff}-z_{AR}=k-1\to\infty$ and is not stated separately.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Lemma 7.1, p. 28 (family (7.2), p. 28; proof App. D, pp. 35–37)

import Mathlib
import Definitions.Def_BudgetedAffine_NetworkGap_LotSizing
import Definitions.Def_BudgetedAffine_NetworkGap_Instance

namespace BudgetedAffine.NetworkGap

/-- Lemma 7.1, p. 28: for the family of instances (7.2) with `m = 2k` nodes (`k ≥ 1`), the
optimal adjustable value is `z_AR(U) = 0` and the optimal affine value is
`z_Aff(U) = m/2 − 1 = k − 1`, both attained. -/
theorem lemma_7_1 (k : ℕ) (hk : 1 ≤ k) :
    IsLeast (lotSizingFamily k).adjustableValues 0 ∧
      IsLeast (lotSizingFamily k).affineValues ((k : ℝ) - 1) := by sorry

end BudgetedAffine.NetworkGap
