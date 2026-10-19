-- Prove2me | Theorems.Thm_ConsHalving_Additive_affine_comb_solves
-- name    : ConsHalving.Additive.affine_comb_solves
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:43.681036+00:00
-- url     : https://prove2.me/theorems/bc80e783-2915-4507-8dbd-c3e85fb7737c
-- title:
--   Proof of Theorem 2.2, p. 5 — the combination (1 − γ)x + γy of two solutions of (1) solves (1)
-- statement:
--   Let $n$ agents have additive utilities $u_i(j)$ over $m$ items. If $x$ and $y$ both solve the system $S$,
--   $$\sum_j \big(x_j-\tfrac12\big)u_i(j)=0,\qquad \sum_j \big(y_j-\tfrac12\big)u_i(j)=0\qquad(\text{every agent } i),$$
--   then for every real $\gamma$ so does the point $s=(1-\gamma)\,x+\gamma\,y$ of Step 3(c).
--
--   The system $S$ is the system (1) of the paper written in the unknowns $y$. This is the first half of the loop invariant of the algorithm: the updated point still satisfies (1).
--
--   **Formalization Note** The paper calls $s$ a *convex* combination, but in Step 3(c) the coefficient $\gamma=\gamma_{j^*}$ can exceed $1$ (for $x_j=\tfrac12$, $y_j=0.6$ one gets $\gamma_j=5$), so the statement is posed for every real $\gamma$ (an affine combination); since (1) is affine, this is what the proof uses.
-- source:
--   Goldberg et al., Consensus Halving for Sets of Items, arXiv:2007.06754v1, p. 5, proof of Theorem 2.2, 'Observe that, since both …'

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting

namespace ConsHalving.Additive

theorem affine_comb_solves {n m : ℕ} (u : Fin n → Fin m → ℝ) (x y : Fin m → ℝ) (γ : ℝ)
    (hx : SolvesS u x) (hy : SolvesS u y) : SolvesS u (stepPoint x y γ) := by sorry

end ConsHalving.Additive
