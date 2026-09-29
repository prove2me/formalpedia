-- Prove2me | Theorems.Thm_FatkhullinPolyak_Discrete_lyapunov_eigen_lower_bounds
-- name    : FatkhullinPolyak.Discrete.lyapunov_eigen_lower_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:36:33.861993+00:00
-- url     : https://prove2.me/theorems/fbba02e3-a6a6-4fdd-ac02-2da54ed6a275
-- title:
--   Lemma A.5 — eigenvalue lower bounds for the Lyapunov equation $A^\top X+XA+Q=0$ (sign misprint corrected)
-- statement:
--   Let $A\in\mathbb R^{n\times n}$ be Hurwitz, $Q\succ0$, and let $X\succ0$ solve the Lyapunov equation
--   $$A^\top X + XA + Q = 0 .$$
--   Write $\sigma(A):=-\max_i\Re\lambda_i(A)>0$ for the stability degree of $A$ and $\|A\|$ for its spectral norm. Then
--   $$\lambda_n(X)\ge\frac{\lambda_1(Q)}{2\sigma(A)},\qquad \lambda_1(X)\ge\frac{\lambda_1(Q)}{2\|A\|}.$$
--
--   These well-known bounds are what make the cost blow up at the boundary of the stabilizing set (Lemma 3.8) and give the positive lower bound on $\lambda_1(Y)$ used in Lemma C.1.
--
--   **Formalization Note** The paper prints the equation as $A^\top X+XA-Q=0$. With $A$ Hurwitz and $Q\succ0$ that equation has no positive definite solution (its solution is negative definite), and the paper applies the lemma to (2.7) and (3.4), which carry $+Q$ and $+\Sigma$. The statement is therefore given with $+Q$.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 15, Lemma A.5 (sign of Q corrected; applied on pp. 15 and 18)

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_Matrix

namespace FatkhullinPolyak.Discrete

/-- Lemma A.5 (p. 15), with the sign misprint corrected: if `X ≻ 0` solves
`AᵀX + XA + Q = 0` (the paper prints `− Q`) with `A` Hurwitz and `Q ≻ 0`, then
`λₙ(X) ≥ λ₁(Q) / (2σ(A))` and `λ₁(X) ≥ λ₁(Q) / (2‖A‖)`, `σ(A) = −maxᵢ ℜλᵢ(A)`. -/
theorem lyapunov_eigen_lower_bounds {n : ℕ} (A X Q : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsHurwitz A) (hQ : Q.PosDef) (hX : X.PosDef)
    (hLyap : A.transpose * X + X * A + Q = 0) :
    lamMin Q / (2 * stabDegree A) ≤ lamMax X ∧
      lamMin Q / (2 * specNorm A) ≤ lamMin X := by sorry

end FatkhullinPolyak.Discrete
