-- Prove2me | Theorems.Thm_BudgetedAffine_NetworkGap_affine_solution
-- name    : BudgetedAffine.NetworkGap.affine_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:37.244286+00:00
-- url     : https://prove2.me/theorems/efec5cb2-53e8-4a27-9191-855b6dc041ff
-- title:
--   App. D, p. 37 — the affine solution y_{im}(h) = 1 − h_i is feasible and costs m/2 − 1
-- statement:
--   Consider the family of lot-sizing instances (7.2) with $m=2k$ nodes, $k=n+1\ge1$, and let $m$ also denote the last node of $J_2$. The affine solution
--   $$x_i=1\ \ (i=1,\dots,m-1),\qquad x_m=0,\qquad y_{ij}(h)=0\ \ (j\in J_2\setminus\{m\}),\qquad y_{im}(h)=1-h_i\qquad(i\in J_1)$$
--   is feasible for (7.1) on $\mathcal U=\{h\in[0,1]^m:\sum_ih_i\le m/2\}$, and its cost in every scenario $h\in\mathcal U$ is
--   $$\sum_{i=1}^mc_ix_i+\sum_{i\in J_1}\sum_{j\in J_2}d_{ij}\,y_{ij}(h)=\frac m2-1=n .$$
--
--   It shows $z_{Aff}(\mathcal U)\le m/2-1$, the upper half of the affine value in Lemma 7.1.
--
--   **Formalization Note** The solution is written $y(h)=Ph+q$ with the explicit $P$ (row of arc $(i,m)$ equal to $-e_i$, all else $0$) and $q$ ($q_{im}=1$, all else $0$) of the instance definition, for $k=n+1$; the paper's node $m$ is the last $J_2$ node `Sum.inr (Fin.last n)`. Lean indices are 0-based.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, App. D, from "Now we consider the following affine solution" to "zAff(U) = m/2 − 1.", p. 37

import Mathlib
import Definitions.Def_BudgetedAffine_NetworkGap_LotSizing
import Definitions.Def_BudgetedAffine_NetworkGap_Instance

namespace BudgetedAffine.NetworkGap

/-- App. D, p. 37: for `k = n + 1`, the affine solution `x_i = 1` (`i ≠ m`), `x_m = 0`,
`y_{im}(h) = 1 − h_i`, `y_{ij}(h) = 0` (`j ≠ m`) is feasible for the family (7.2) and costs
`m/2 − 1 = n` in every scenario. -/
theorem affine_solution (n : ℕ) :
    (lotSizingFamily (n + 1)).Feasible (ubX n) (LotSizing.affinePolicy (ubP n) (ubQ n)) ∧
      ∀ h ∈ (lotSizingFamily (n + 1)).U,
        (lotSizingFamily (n + 1)).cost (ubX n) (LotSizing.affinePolicy (ubP n) (ubQ n) h)
          = (n : ℝ) := by sorry

end BudgetedAffine.NetworkGap
