-- Prove2me | Theorems.Thm_ExpConeIPM_Curvature_third_derivative_formula
-- name    : ExpConeIPM.Curvature.third_derivative_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:08:16.748376+00:00
-- url     : https://prove2.me/theorems/0a401dff-e5a0-4d20-980f-4a62fd23a8b7
-- title:
--   A.3, (33) — the third directional derivative $F'''(x)[u]$ of the exponential-cone barrier
-- statement:
--   Let $F$, $\psi$, $g$, $h$ be as in Appendix A.1, with $\psi'(x)$ and $\psi''(x)$ as in A.1–A.2 and $g''(x) = F''(x) - h''(x) = -\frac{1}{\psi(x)}\bigl(\psi''(x) - \psi'(x)\psi'(x)^T/\psi(x)\bigr)$. For every $x \in \operatorname{int}(K_{\exp})$ and every $u \in \mathbb{R}^3$, the third directional derivative $F'''(x)[u] = \frac{d}{dt}F''(x+tu)\big|_{t=0}$ equals
--
--   $$
--   F'''(x)[u] = -2\frac{\langle\psi'(x), u\rangle}{\psi(x)}\, g''(x) - \frac{\langle\psi'(x), u\rangle}{\psi(x)^2}\,\psi''(x) - \frac{1}{\psi(x)}\,\psi'''(x)[u] + \frac{1}{\psi(x)^2}\Bigl(\psi'(x)u^T\psi''(x) + \psi''(x)u\psi'(x)^T\Bigr) + h'''(x)[u],
--   $$
--
--   where $h'''(x)[u]$ and $\psi'''(x)[u]$ vanish outside their leading $2\times2$ blocks, which are, by (33),
--
--   $$
--   \hat h'''(x)[u] = -2\begin{bmatrix} u_1/x_1^3 & 0 \\ 0 & u_2/x_2^3 \end{bmatrix}, \qquad
--   \hat\psi'''(x)[u] = \begin{bmatrix} 2x_2u_1/x_1^3 - u_2/x_1^2 & -u_1/x_1^2 \\ -u_1/x_1^2 & u_2/x_2^2 \end{bmatrix}.
--   $$
--
--   This formula is what the algorithm uses to evaluate the higher-order corrector term $-\tfrac12 F'''(x)[u, v]$, and it is the expression the paper uses to compute $F'''(\hat x)[\hat u]$ in §5.
--
--   **Formalization Note** $F'''(x)[u]$ is `fderiv ℝ (hess barrier) x u`; matrices act on `EuclideanSpace ℝ (Fin 3)` through the standard basis (`Matrix.toEuclideanCLM`), $\langle\psi'(x), u\rangle$ is a dot product, and indices are 0-based. The paper gives only the leading $2\times2$ parts of $h'''$ and $\psi'''$ ("leading parts", p. 367); the statement pads them with a zero third row and column, which is their true value, since $h''$ and $\psi''$ vanish outside their leading blocks and do not depend on $x_3$. $g''(x)$ is written out by the A.2 formula.
-- source:
--   Dahl, Andersen, A primal-dual interior-point algorithm for nonsymmetric exponential-cone optimization, Math. Program. 194 (2022), p. 368, Appendix A.3, (33)

import Mathlib
import Definitions.Def_ExpConeIPM_Curvature_ExpCone
import Definitions.Def_ExpConeIPM_Curvature_NegativeCurvature

open scoped InnerProductSpace

namespace ExpConeIPM.Curvature

open Matrix

/-- **A.3, p. 368 — third-order directional derivatives.** For `x ∈ int(Kexp)` and `u ∈ ℝ³`,
```
F'''(x)[u] = −2 (⟨ψ'(x), u⟩/ψ(x)) g''(x) − (⟨ψ'(x), u⟩/ψ(x)²) ψ''(x) − (1/ψ(x)) ψ'''(x)[u]
             + (1/ψ(x)²) (ψ'(x)uᵀψ''(x) + ψ''(x)uψ'(x)ᵀ) + h'''(x)[u],
```
where `g''(x) = F''(x) − h''(x) = −(1/ψ(x))(ψ''(x) − ψ'(x)ψ'(x)ᵀ/ψ(x))` (A.2), and `h'''(x)[u]`,
`ψ'''(x)[u]` are the 3×3 matrices whose leading 2×2 parts are given by (33),
`ĥ'''(x)[u] = −2 [u₁/x₁³, 0; 0, u₂/x₂³]`,
`ψ̂'''(x)[u] = [2x₂u₁/x₁³ − u₂/x₁², −u₁/x₁²; −u₁/x₁², u₂/x₂²]`,
and whose third row and column are zero. -/
theorem third_derivative_formula (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ interior Kexp)
    (u : EuclideanSpace ℝ (Fin 3)) :
    let ψ' : Fin 3 → ℝ := ![x 1 / x 0, Real.log (x 0 / x 1) - 1, -1]
    let ψ'' : Matrix (Fin 3) (Fin 3) ℝ :=
      !![-x 1 / x 0 ^ 2, 1 / x 0, 0; 1 / x 0, -1 / x 1, 0; 0, 0, 0]
    let g'' : Matrix (Fin 3) (Fin 3) ℝ := -(1 / psi x) • (ψ'' - (1 / psi x) • Matrix.vecMulVec ψ' ψ')
    let ψ''' : Matrix (Fin 3) (Fin 3) ℝ :=
      !![2 * x 1 * u 0 / x 0 ^ 3 - u 1 / x 0 ^ 2, -u 0 / x 0 ^ 2, 0;
         -u 0 / x 0 ^ 2, u 1 / x 1 ^ 2, 0;
         0, 0, 0]
    let h''' : Matrix (Fin 3) (Fin 3) ℝ :=
      (-2 : ℝ) • !![u 0 / x 0 ^ 3, 0, 0; 0, u 1 / x 1 ^ 3, 0; 0, 0, 0]
    let ip : ℝ := ψ' ⬝ᵥ WithLp.ofLp u
    thirdDeriv barrier x u =
      Matrix.toEuclideanCLM (𝕜 := ℝ)
        (-(2 * ip / psi x) • g'' - (ip / psi x ^ 2) • ψ'' - (1 / psi x) • ψ'''
          + (1 / psi x ^ 2) •
              (Matrix.vecMulVec ψ' (WithLp.ofLp u) * ψ'' + ψ'' * Matrix.vecMulVec (WithLp.ofLp u) ψ')
          + h''') := by sorry

end ExpConeIPM.Curvature
