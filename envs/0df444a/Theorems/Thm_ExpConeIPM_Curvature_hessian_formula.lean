-- Prove2me | Theorems.Thm_ExpConeIPM_Curvature_hessian_formula
-- name    : ExpConeIPM.Curvature.hessian_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:26.946972+00:00
-- url     : https://prove2.me/theorems/cb829f6b-3b55-4e85-97f7-7d9ba410ed86
-- title:
--   A.2 — the Hessian $F''(x) = -\frac{1}{\psi}(\psi'' - \psi'\psi'^T/\psi) + h''$ of the exponential-cone barrier
-- statement:
--   Let $F$, $\psi$, $h$ be as in Appendix A.1 and $\psi'(x) = (x_2/x_1,\ \log(x_1/x_2) - 1,\ -1)$. For every $x \in \operatorname{int}(K_{\exp})$,
--
--   $$
--   F''(x) = -\frac{1}{\psi(x)}\Bigl(\psi''(x) - \frac{\psi'(x)\psi'(x)^T}{\psi(x)}\Bigr) + h''(x)
--   $$
--
--   with $h''(x) = \operatorname{diag}(1/x_1^2,\ 1/x_2^2,\ 0)$ and
--
--   $$
--   \psi''(x) = \begin{bmatrix} -x_2/x_1^2 & 1/x_1 & 0 \\ 1/x_1 & -1/x_2 & 0 \\ 0 & 0 & 0 \end{bmatrix}.
--   $$
--
--   The statement asserts the three identities: the formula for $F''(x)$, and the displayed expressions for $\psi''(x)$ and $h''(x)$.
--
--   This closed form of the barrier Hessian is what the method uses to build scaling matrices and Newton systems.
--
--   **Formalization Note** Hessians are `SelfScaledIPM.ShortStep.hess` (derivative of the gradient), linear maps of `EuclideanSpace ℝ (Fin 3)`; a $3\times3$ matrix $M$ is identified with the map $v \mapsto Mv$ through the standard basis (`Matrix.toEuclideanCLM`). Indices are 0-based. Only the first display of A.2 is stated; the block factorization $F''(x) = R(x)R(x)^T$ that follows it on pp. 367–368 is not.
-- source:
--   Dahl, Andersen, A primal-dual interior-point algorithm for nonsymmetric exponential-cone optimization, Math. Program. 194 (2022), p. 367, Appendix A.2 (first display)

import Mathlib
import Definitions.Def_ExpConeIPM_Curvature_ExpCone
import Definitions.Def_ExpConeIPM_Curvature_NegativeCurvature

open scoped InnerProductSpace

namespace ExpConeIPM.Curvature

open Matrix

/-- **A.2, p. 367 — second-order derivatives.** For `x ∈ int(Kexp)`,
`F''(x) = −(1/ψ(x)) (ψ''(x) − ψ'(x)ψ'(x)ᵀ/ψ(x)) + h''(x)` with `h''(x) = diag(1/x₁², 1/x₂², 0)` and
`ψ''(x) = [−x₂/x₁², 1/x₁, 0; 1/x₁, −1/x₂, 0; 0, 0, 0]`, where `ψ'(x) = (x₂/x₁, log(x₁/x₂) − 1, −1)`
(A.1). Matrices act on `ℝ³` through the standard basis (`Matrix.toEuclideanCLM`). -/
theorem hessian_formula (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ interior Kexp) :
    let ψ' : Fin 3 → ℝ := ![x 1 / x 0, Real.log (x 0 / x 1) - 1, -1]
    let ψ'' : Matrix (Fin 3) (Fin 3) ℝ :=
      !![-x 1 / x 0 ^ 2, 1 / x 0, 0; 1 / x 0, -1 / x 1, 0; 0, 0, 0]
    let h'' : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1 / x 0 ^ 2, 1 / x 1 ^ 2, 0]
    SelfScaledIPM.ShortStep.hess psi x = Matrix.toEuclideanCLM (𝕜 := ℝ) ψ'' ∧
      SelfScaledIPM.ShortStep.hess h x = Matrix.toEuclideanCLM (𝕜 := ℝ) h'' ∧
      SelfScaledIPM.ShortStep.hess barrier x =
        Matrix.toEuclideanCLM (𝕜 := ℝ)
          (-(1 / psi x) • (ψ'' - (1 / psi x) • Matrix.vecMulVec ψ' ψ') + h'') := by sorry

end ExpConeIPM.Curvature
