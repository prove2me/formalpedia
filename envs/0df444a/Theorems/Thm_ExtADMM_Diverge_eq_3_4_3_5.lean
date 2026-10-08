-- Prove2me | Theorems.Thm_ExtADMM_Diverge_eq_3_4_3_5
-- name    : ExtADMM.Diverge.eq_3_4_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:59.983959+00:00
-- url     : https://prove2.me/theorems/a5ca5b8c-ea94-4d4d-8d51-f25130e91c84
-- title:
--   (3.4)–(3.5), p. 11 — on (3.1), x₁^{k+1} is given by (3.4) and L(x₂, x₃, μ)^{k+1} = R(x₂, x₃, μ)^k with μ = λ/β
-- statement:
--   Let $a_1,a_2,a_3\in\mathbb R^3$ be column vectors such that the $3\times3$ matrix $[A_1,A_2,A_3]=[a_1,a_2,a_3]$ is nonsingular, and consider the linear system (3.1), $A_1x_1+A_2x_2+A_3x_3=0$ with $x_i\in\mathbb R$, as an instance of problem (1.1). Let $\beta>0$ and let $(x_1^k,x_2^k,x_3^k,\lambda^k)_{k\ge0}$ be any run of the direct extension of ADMM (1.5) on it. Put $\mu^k=\lambda^k/\beta$. Then for every $k\ge0$,
--
--   $$x_1^{k+1}=\frac{1}{A_1^TA_1}\bigl(-A_1^TA_2x_2^k-A_1^TA_3x_3^k+A_1^T\mu^k\bigr)\qquad(3.4)$$
--
--   and
--
--   $$L\begin{pmatrix}x_2^{k+1}\\x_3^{k+1}\\\mu^{k+1}\end{pmatrix}=R\begin{pmatrix}x_2^{k}\\x_3^{k}\\\mu^{k}\end{pmatrix}\qquad(3.5)$$
--
--   with the $5\times5$ matrices $L$ of (3.6) and $R$ of (3.7).
--
--   The point is that neither $L$ nor $R$ involves $\beta$: in the scaled variables $\mu=\lambda/\beta$ the iteration is the same linear map for every penalty parameter. This is what makes the divergence of the example hold for every $\beta>0$ at once.
--
--   **Formalization Note.** The run is any sequence satisfying the minimiser conditions of (1.5); no particular minimiser is chosen. $x_1^0$ is never read. $\mu^k$ has components $\lambda^k_i/\beta$, indexed $0,1,2$ in Lean.
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), p. 11, (3.3)–(3.5)

import Mathlib
import Definitions.Def_ExtADMM_Diverge_Setting

open Matrix Filter Topology

namespace ExtADMM.Diverge

/-- (3.4)–(3.5), p. 11. For the linear system (3.1) with columns `a₁, a₂, a₃ ∈ ℝ³` such that
`[A₁, A₂, A₃]` is nonsingular, and any `β > 0`, every run of the direct extension of ADMM (1.5)
satisfies, for every `k`, the closed form (3.4) of `x₁^{k+1}` and the recursion (3.5)
`L (x₂^{k+1}, x₃^{k+1}, μ^{k+1}) = R (x₂ᵏ, x₃ᵏ, μᵏ)` in the variables `μ = λ/β`. -/
theorem eq_3_4_3_5 (a1 a2 a3 : Fin 3 → ℝ) (hA : (colMat a1 a2 a3).det ≠ 0)
    (β : ℝ) (hβ : 0 < β)
    (x1 x2 x3 : ℕ → Fin 1 → ℝ) (lam : ℕ → Fin 3 → ℝ)
    (hrun : (instance31 a1 a2 a3).IsRun15 β x1 x2 x3 lam) (k : ℕ) :
    x1 (k+1) 0 = (1 / (a1 ⬝ᵥ a1)) *
        (-(a1 ⬝ᵥ a2) * x2 k 0 - (a1 ⬝ᵥ a3) * x3 k 0 + a1 ⬝ᵥ (β⁻¹ • lam k)) ∧
      Lmat a2 a3 *ᵥ stateVec β (x2 (k+1)) (x3 (k+1)) (lam (k+1)) =
        Rmat a1 a2 a3 *ᵥ stateVec β (x2 k) (x3 k) (lam k) := by sorry

end ExtADMM.Diverge
