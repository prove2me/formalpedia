-- Prove2me | Theorems.Thm_ALADIN_DualDecomp_stationarity
-- name    : ALADIN.DualDecomp.stationarity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:37.258585+00:00
-- url     : https://prove2.me/theorems/da3933a3-ec34-46ab-a1a3-b8001b605d71
-- title:
--   App. A, proof of Lemma 5 — with ρ = 0 the step-1 output satisfies 0 = ∇fᵢ(yᵢ) + Aᵢᵀλ + (C*ᵢ)ᵀκᵢ = gᵢ + Aᵢᵀλ + Cᵢᵀκᵢ
-- statement:
--   Let $(f,h,A,b)$ be an instance of problem (1.1) and fix a block $i$. Suppose $f_i$ and $h_i$ are twice continuously differentiable, and $(y_i,\kappa_i)$ is a step-1 output of Algorithm 2 for block $i$ with penalty parameter $\rho = 0$ (any scaling matrix $\Sigma_i$, any $x_i$, dual iterate $\lambda$), so that $y_i$ solves (A.2) with multiplier $\kappa_i$. Then for every matrix $C_i\in\mathbb R^{n_h\times n}$,
--   $$0 = \nabla f_i(y_i) + A_i^\top\lambda + (C^*_i)^\top\kappa_i = g_i + A_i^\top\lambda + C_i^\top\kappa_i,$$
--   where $C^*_i$ is the active-constraint Jacobian at $y_i$ and $g_i = \nabla f_i(y_i) + (C^*_i - C_i)^\top\kappa_i$ is the modified gradient of step 3.
--
--   This is the stationarity condition of (A.2) rewritten with the modified gradient; in the proof of Lemma 5 it eliminates $g_i$ from the dual of the QP (3.3).
-- source:
--   Houska, Frasch, Diehl, An augmented Lagrangian based algorithm for distributed nonconvex optimization, SIAM J. Optim. 26 (2016), pp. 1123–1124, App. A, proof of Lemma 5, stationarity display

import Mathlib
import Definitions.Def_ALADIN_DualDecomp_Problem
import Definitions.Def_ALADIN_DualDecomp_Step

namespace ALADIN.DualDecomp

open Matrix

/-- App. A, proof of Lemma 5, p. 1123: if `(yᵢ, κᵢ)` is the output of Algorithm 2, step 1 with `ρ = 0`
(so (3.2) is (A.2)), and `fᵢ`, `hᵢ` are twice continuously differentiable, then for every
choice of `Cᵢ`,
`0 = ∇fᵢ(yᵢ) + Aᵢᵀ λ + (C*ᵢ)ᵀ κᵢ = gᵢ + Aᵢᵀ λ + Cᵢᵀ κᵢ`. -/
theorem stationarity {N n m nh : ℕ} (P : Problem N n m nh) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (lam : Fin m → ℝ) (i : Fin N) (yi : Fin n → ℝ) (κi : Fin nh → ℝ)
    (Ci : Matrix (Fin nh) (Fin n) ℝ)
    (hf : ContDiff ℝ 2 (P.f i)) (hh : ContDiff ℝ 2 (P.h i))
    (hstep1 : Step1Solution P 0 Sig x lam i yi κi) :
    grad (P.f i) yi + (P.A i)ᵀ *ᵥ lam + (Cstar P i yi)ᵀ *ᵥ κi = 0 ∧
    modGrad P i yi κi Ci + (P.A i)ᵀ *ᵥ lam + Ciᵀ *ᵥ κi = 0 := by sorry

end ALADIN.DualDecomp
