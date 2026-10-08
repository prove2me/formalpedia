-- Prove2me | Theorems.Thm_BilinearGramian_Integrability_field_hasFDerivAt
-- name    : BilinearGramian.Integrability.field_hasFDerivAt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:01.468993+00:00
-- url     : https://prove2.me/theorems/7c9b03b3-7b3f-4747-86b6-7eac25263234
-- title:
--   Example 3.3, p. 697 — the derivative F′(x)h = P̃(x)⁻¹h − P̃(x)⁻¹P̃′ₓ(h)P̃(x)⁻¹x of F(x) = P̃(x)⁻¹x
-- statement:
--   Let $A, N_1, \dots, N_m \in \mathbb R^{n\times n}$ and $B \in \mathbb R^{n\times m}$ with columns $b_j$, and assume the Lyapunov operator $X \mapsto AX + XA^T$ is injective, so that (3.9) determines its solution. Let $\tilde P(x)$ solve (3.9),
--   $$A \tilde P(x) + \tilde P(x) A^T = -\sum_{j=1}^m (N_j x + b_j)(N_j x + b_j)^T,$$
--   for every $x \in \mathbb R^n$, and consider the vector field $F(x) := \tilde P(x)^{-1}x$. At every point $x$ where $\tilde P(x)$ is invertible, $F$ is (Fréchet) differentiable, and its derivative is
--   $$h \mapsto F'(x)h = \tilde P(x)^{-1}h - \tilde P(x)^{-1}\tilde P'_x(h)\tilde P(x)^{-1}x,$$
--   where $\tilde P'_x(h)$ is the solution of
--   $$A \tilde P'_x(h) + \tilde P'_x(h) A^T = -\sum_{j=1}^m \big(N_j h (N_j x + b_j)^T + (N_j x + b_j) h^T N_j^T\big).$$
--
--   This is the formula the paper uses to test the integrability of $F$: $F$ can be a gradient field only if the matrix $F'(x)$ is symmetric.
--
--   **Formalization Note** The statement asserts the existence of a continuous linear map $L$ that is the derivative of $F$ at $x$ and satisfies the displayed formula for every $h$ and every solution $X$ of the equation for $\tilde P'_x(h)$. The printed equation for $\tilde P'_x(h)$ on p. 697 has no parentheses after the minus sign; differentiating (3.9) puts the minus sign on both terms, and that is what is stated. Invertibility of $\tilde P(x)$ is `IsUnit (Pt x).det`; injectivity of the Lyapunov operator is the paper's implicit "$\tilde P(x)$ defined by (3.9)". The paper's indices $j = 1,\dots,m$ are `Fin m`.
-- source:
--   Benner, Damm, Lyapunov Equations, Energy Functionals, and Model Order Reduction of Bilinear and Stochastic Systems, SIAM J. Control Optim. 49(2) (2011), p. 697, Example 3.3 (display after "Its derivative is")

import Mathlib
import Definitions.Def_BilinearGramian_Integrability_LinGramian
import Definitions.Def_BilinearGramian_Integrability_Example33

open Matrix

namespace BilinearGramian.Integrability

/-- Example 3.3, p. 697 (Benner–Damm 2011): the derivative of the field `F(x) = P̃(x)⁻¹ x`.
Let `P̃(x)` be defined by (3.9) for every `x`, the Lyapunov operator `X ↦ A X + X Aᵀ` being
injective (so that (3.9) determines `P̃(x)`). At a point `x` where `P̃(x)` is invertible,
`F` is differentiable and its derivative is
`F′(x) h = P̃(x)⁻¹ h - P̃(x)⁻¹ P̃′ₓ(h) P̃(x)⁻¹ x`, where `P̃′ₓ(h)` solves
`A X + X Aᵀ = -∑_j (N_j h (N_j x + b_j)ᵀ + (N_j x + b_j) hᵀ N_jᵀ)`. -/
theorem field_hasFDerivAt {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (hA : ∀ X : Matrix (Fin n) (Fin n) ℝ, A * X + X * Aᵀ = 0 → X = 0)
    (Pt : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (hPt : ∀ x, IsLinGramian A N B x (Pt x))
    (x : Fin n → ℝ) (hx : IsUnit (Pt x).det) :
    ∃ L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ),
      HasFDerivAt (fun y => (Pt y)⁻¹ *ᵥ y) L x ∧
      ∀ (h : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℝ),
        A * X + X * Aᵀ = -∑ j, (vecMulVec (N j *ᵥ h) (N j *ᵥ x + fun i => B i j) +
            vecMulVec (N j *ᵥ x + fun i => B i j) (N j *ᵥ h)) →
        L h = (Pt x)⁻¹ *ᵥ h - ((Pt x)⁻¹ * X * (Pt x)⁻¹) *ᵥ x := by sorry

end BilinearGramian.Integrability
