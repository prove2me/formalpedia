-- Prove2me | Theorems.Thm_AugLagLLC_Penalty_lemma_5_2
-- name    : AugLagLLC.Penalty.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:38:14.164533+00:00
-- url     : https://prove2.me/theorems/1f0ba451-6741-4444-b3c0-0f049a897c94
-- title:
--   Lemma 5.2, p. 11 — under Assumptions 3 and 5 the KKT matrix with −πI block is nonsingular for all π ∈ [0, 1/ρ̄]
-- statement:
--   Consider problem (5.1) with Lagrangian $L_0(x,\lambda,v)=f(x)+\langle h_1(x),\lambda\rangle+\langle h_2(x),v\rangle$, a point $x_*$ at which $f,h_1,h_2$ are twice continuously differentiable, and multipliers $\lambda_*,v_*$. Suppose:
--
--   1. (Assumption 3) the gradients $\nabla[h_1(x_*)]_i$, $i\le m_1$, and $\nabla[h_2(x_*)]_i$, $i\le m_2$, are linearly independent;
--   2. (Assumption 5) $\nabla_xL_0(x_*,\lambda_*,v_*)=0$ and $\langle z,\nabla^2_{xx}L_0(x_*,\lambda_*,v_*)z\rangle>0$ for all $z\ne0$ with $\nabla h_1(x_*)^Tz=0$, $\nabla h_2(x_*)^Tz=0$.
--
--   Then there exists $\bar\rho>0$ such that for all $\pi\in[0,1/\bar\rho]$ the matrix
--   $$\begin{pmatrix}\nabla^2_{xx}L_0(x_*,\lambda_*,v_*) & \nabla h_1(x_*) & \nabla h_2(x_*)\\ \nabla h_1(x_*)^T & -\pi I & 0\\ \nabla h_2(x_*)^T & 0 & 0\end{pmatrix}$$
--   is nonsingular.
--
--   This is the Jacobian of the system solved implicitly in Lemma 5.3, with $\pi=1/\rho_k$; its uniform nonsingularity gives the error bounds (5.4) and (5.5).
--
--   **Formalization Note** The matrix is the linear map $(d,a,b)\mapsto(\nabla^2_{xx}L_0\,d+\sum_ia_i\nabla[h_1(x_*)]_i+\sum_ib_i\nabla[h_2(x_*)]_i,\ (\langle\nabla[h_1(x_*)]_i,d\rangle-\pi a_i)_i,\ (\langle\nabla[h_2(x_*)]_i,d\rangle)_i)$ of the finite-dimensional space $\mathbb R^n\times\mathbb R^{m_1}\times\mathbb R^{m_2}$ into itself, and nonsingular is stated as injective (equivalent for a linear endomorphism of a finite-dimensional space). Assumption 5 is pinned to Fletcher's equality-constrained second-order condition; the Hessian is the derivative of the gradient, so twice continuous differentiability at $x_*$ (Assumption 4 of the page) is carried as part of the meaning of Assumption 5. Feasibility of $x_*$ and the standing $C^1$ hypothesis are not needed and not assumed.
-- source:
--   Andreani, Birgin, Martínez & Schuverdt, On augmented Lagrangian methods with general lower-level constraints, HAL hal-01295437v1, p. 11, Lemma 5.2 (with Assumptions 3 and 5)

import Mathlib
import Definitions.Def_AugLagLLC_Penalty_SecondOrder

open Filter
open scoped Topology

namespace AugLagLLC.Penalty

/-- Lemma 5.2, p. 11: under Assumptions 3 and 5 (with `C²` at `x_*`, Assumption 4, which gives
the Hessian its meaning), there is `ρ̄ > 0` such that for every `π ∈ [0, 1/ρ̄]` the block matrix
`[[∇²ₓₓL₀(x_*, λ_*, v_*), ∇h₁(x_*), ∇h₂(x_*)], [∇h₁(x_*)ᵀ, −πI, 0], [∇h₂(x_*)ᵀ, 0, 0]]`
is nonsingular (as a linear map of the finite-dimensional space `ℝⁿ × ℝ^{m₁} × ℝ^{m₂}` into
itself, injective). -/
theorem lemma_5_2
    {n m1 m2 : ℕ} (P : Problem n m1 0 m2 0) {xs : EuclideanSpace ℝ (Fin n)}
    -- Assumption 3
    (hLI : LinearIndependent ℝ
      (Sum.elim (fun i => gradient (P.h1 i) xs) (fun i => gradient (P.h2 i) xs)))
    -- Assumption 4
    (hC2 : P.IsC2At xs)
    -- Assumption 5
    (lamS : Fin m1 → ℝ) (vS : Fin m2 → ℝ) (hSOSC : P.SOSC0 lamS vS xs)
    :
    ∃ ρbar : ℝ, 0 < ρbar ∧
      ∀ π ∈ Set.Icc (0 : ℝ) (1 / ρbar), Function.Injective (P.kktMap lamS vS xs π) := by sorry

end AugLagLLC.Penalty
