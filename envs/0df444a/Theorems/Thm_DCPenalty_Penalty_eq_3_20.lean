-- Prove2me | Theorems.Thm_DCPenalty_Penalty_eq_3_20
-- name    : DCPenalty.Penalty.eq_3_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:33.798543+00:00
-- url     : https://prove2.me/theorems/0a66b012-f311-4423-93c2-d3e67e4039bf
-- title:
--   (3.20)–(3.21), p. 12 — moving towards x̂ and shrinking towards x̄ makes every φ̂-model constraint strict
-- statement:
--   Let the standing assumptions of problem (1.1) hold. Let $\bar x\in\Omega$ with $\mathcal I_=(\bar x)\neq\emptyset$, let $\mathbb J=(j_1,\dots,j_I)\in\mathcal J(\bar x)$, and let $\hat x\in Y_{\mathbb J}(\bar x)$ satisfy (3.18): $\phi_i(\hat x)+\zeta_i(\hat x)-\ell_{\psi_{i,j_i}}(\hat x;\bar x)<0$ for all $i\in\mathcal I_=(\bar x)$. For $t,\tau\in[0,1]$ and $x\in Y_{\mathbb J}(\bar x)$ put
--
--   $$
--   x(t,\tau)=\bar x+t\big(x(\tau)-\bar x\big),\qquad x(\tau)=(1-\tau)x+\tau\hat x. \tag{3.21}
--   $$
--
--   Then for every $\tau\in(0,1]$ and every $x\in Y_{\mathbb J}(\bar x)$ there is some $\hat t\in(0,1)$ such that $x(\hat t,\tau)\in Y_{\mathbb J}(\bar x)$ and
--
--   $$
--   \hat\phi_i\big(x(\hat t,\tau);\bar x\big)+\zeta_i\big(x(\hat t,\tau)\big)-\ell_{\psi_{i,j_i}}\big(x(\hat t,\tau);\bar x\big)<0\qquad\forall i\in\mathcal I. \tag{3.20}
--   $$
--
--   In the proof of Theorem 3.1(iii) (at $\bar x=x^\infty$) these strictly feasible points of the quadratic model constraints stay feasible for the models built at nearby iterates $x^k$, which is what allows passing to the limit in (3.10).
--
--   **Formalization Note** $\hat x$ and its property (3.18) are hypotheses here, exactly as in the proof, where $\hat x$ is the point produced by (3.18) for the same $\mathbb J$.
-- source:
--   Lu, Sun & Zhou, Penalty and augmented Lagrangian methods for constrained DC programming, arXiv:2111.09263v1, p. 12, proof of Theorem 3.1(iii), (3.20), (3.21)

import Mathlib
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_DCPenalty_Penalty_Problem
import Definitions.Def_DCPenalty_Penalty_Stationarity
import Definitions.Def_DCPenalty_Penalty_Algorithm

namespace DCPenalty.Penalty

/-- (3.20)–(3.21), p. 12: let `x̄ ∈ Ω` with `𝓘_=(x̄) ≠ ∅`, `𝕁 ∈ 𝓙(x̄)`, and `x̂ ∈ Y_𝕁(x̄)` satisfy (3.18).
For every `τ ∈ (0, 1]` and `x ∈ Y_𝕁(x̄)` there is `t̂ ∈ (0, 1)` such that
`x(t̂, τ) = x̄ + t̂ (x(τ) − x̄)`, `x(τ) = (1 − τ) x + τ x̂`, lies in `Y_𝕁(x̄)` and
`φ̂_i(x(t̂, τ); x̄) + ζ_i(x(t̂, τ)) − ℓ_{ψ_{i,j_i}}(x(t̂, τ); x̄) < 0` for all `i ∈ 𝓘`. -/
theorem eq_3_20 {n m : ℕ} (P : DCProblem n m) (hP : P.Standing)
    {xbar : EuclideanSpace ℝ (Fin n)} (hfeas : xbar ∈ P.Ω) (hact : (P.Ieq xbar).Nonempty)
    {jj : (i : Fin m) → Fin (P.J i.succ)} (hjj : jj ∈ P.Jtup xbar)
    {xhat : EuclideanSpace ℝ (Fin n)} (hxhat : xhat ∈ P.Y jj xbar)
    (h318 : ∀ i ∈ P.Ieq xbar,
      P.φ i.succ xhat + P.ζ i.succ xhat - lin (P.ψ i.succ (jj i)) xbar xhat < 0) :
    ∀ τ ∈ Set.Ioc (0 : ℝ) 1, ∀ x ∈ P.Y jj xbar, ∃ that ∈ Set.Ioo (0 : ℝ) 1,
      xbar + that • (((1 - τ) • x + τ • xhat) - xbar) ∈ P.Y jj xbar ∧
      ∀ i : Fin m,
        P.phiHat i.succ xbar (xbar + that • (((1 - τ) • x + τ • xhat) - xbar)) +
          P.ζ i.succ (xbar + that • (((1 - τ) • x + τ • xhat) - xbar)) -
          lin (P.ψ i.succ (jj i)) xbar (xbar + that • (((1 - τ) • x + τ • xhat) - xbar)) < 0 := by sorry

end DCPenalty.Penalty
