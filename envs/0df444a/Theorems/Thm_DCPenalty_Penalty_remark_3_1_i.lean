-- Prove2me | Theorems.Thm_DCPenalty_Penalty_remark_3_1_i
-- name    : DCPenalty.Penalty.remark_3_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:34.098319+00:00
-- url     : https://prove2.me/theorems/9319814b-5b0e-4cdf-b692-2f889ca1d4e4
-- title:
--   Remark 3.1(i), p. 8 — the ε-active index sets contain the active ones near x̄
-- statement:
--   Let the standing assumptions of problem (1.1) hold, let $\epsilon>0$ and let $\bar x\in X$. Then for all $x\in X$ sufficiently close to $\bar x$,
--
--   $$
--   \mathcal J_0(\bar x)\subseteq\mathcal J_{0,\epsilon}(x)\qquad\text{and}\qquad \mathcal J(\bar x)\subseteq\mathcal J_\epsilon(x).
--   $$
--
--   This is the first step of the proof of Theorem 3.1: it lets the inequality (3.7), which the method enforces only for $\epsilon$-active pieces at $x^k$, be used for the pieces active at the limit point.
--
--   **Formalization Note** "For all $x\in X$ sufficiently close to $\bar x$" is the filter `𝓝[X] x̄`.
-- source:
--   Lu, Sun & Zhou, Penalty and augmented Lagrangian methods for constrained DC programming, arXiv:2111.09263v1, p. 8, Remark 3.1(i)

import Mathlib
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_DCPenalty_Penalty_Problem
import Definitions.Def_DCPenalty_Penalty_Stationarity
import Definitions.Def_DCPenalty_Penalty_Algorithm

namespace DCPenalty.Penalty

open Filter Topology

/-- Remark 3.1(i), p. 8: for any `x̄ ∈ X`, `𝓙_0(x̄) ⊆ 𝓙_{0,ε}(x)` and `𝓙(x̄) ⊆ 𝓙_ε(x)` for all
`x ∈ X` sufficiently close to `x̄`. -/
theorem remark_3_1_i {n m : ℕ} (P : DCProblem n m) (hP : P.Standing) {ε : ℝ} (hε : 0 < ε)
    {xbar : EuclideanSpace ℝ (Fin n)} (hxbar : xbar ∈ P.X) :
    ∀ᶠ x in 𝓝[P.X] xbar, P.Jact 0 xbar ⊆ P.J0eps ε x ∧ P.Jtup xbar ⊆ P.Jeps ε x := by sorry

end DCPenalty.Penalty
