-- Prove2me | Theorems.Thm_ExtADMM_Diverge_eq_3_8
-- name    : ExtADMM.Diverge.eq_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:06:05.267241+00:00
-- url     : https://prove2.me/theorems/c156f91e-fc93-465e-9b7c-12264ad45fc4
-- title:
--   (3.8)–(3.9), p. 11 — on (3.1), (x₂ᵏ, x₃ᵏ, μᵏ) = Mᵏ(x₂⁰, x₃⁰, μ⁰) with M = L⁻¹R
-- statement:
--   Let $a_1,a_2,a_3\in\mathbb R^3$ be such that $[A_1,A_2,A_3]$ is nonsingular, let $\beta>0$, and let $(x_1^k,x_2^k,x_3^k,\lambda^k)_{k\ge0}$ be any run of the direct extension of ADMM (1.5) on the linear system (3.1). With $\mu^k=\lambda^k/\beta$ and $M=L^{-1}R$ (3.9), for every $k\ge0$
--
--   $$\begin{pmatrix}x_2^{k}\\x_3^{k}\\\mu^{k}\end{pmatrix}=M^{k}\begin{pmatrix}x_2^{0}\\x_3^{0}\\\mu^{0}\end{pmatrix}.\qquad(3.8)$$
--
--   So the extended ADMM on (3.1) is a fixed linear iteration on $\mathbb R^5$, independent of $\beta$, and its behaviour is governed by the powers of $M$.
--
--   **Formalization Note.** $L$ is lower triangular with $\det L=(A_2^TA_2)(A_3^TA_3)$, which is nonzero under the nonsingularity hypothesis, so $L^{-1}$ is the genuine inverse. The page writes the identity as $M^{k+1}$ applied to the starting point; the Lean states it for every $k\ge0$ as $M^k$, which is the same family of identities together with the trivial case $k=0$.
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), p. 11, (3.8)–(3.9)

import Mathlib
import Definitions.Def_ExtADMM_Diverge_Setting

open Matrix Filter Topology

namespace ExtADMM.Diverge

/-- (3.8)–(3.9), p. 11. For the linear system (3.1) with `[A₁, A₂, A₃]` nonsingular and any
`β > 0`, every run of (1.5) satisfies
`(x₂ᵏ, x₃ᵏ, μᵏ) = Mᵏ (x₂⁰, x₃⁰, μ⁰)` with `M = L⁻¹R` and `μ = λ/β`. -/
theorem eq_3_8 (a1 a2 a3 : Fin 3 → ℝ) (hA : (colMat a1 a2 a3).det ≠ 0)
    (β : ℝ) (hβ : 0 < β)
    (x1 x2 x3 : ℕ → Fin 1 → ℝ) (lam : ℕ → Fin 3 → ℝ)
    (hrun : (instance31 a1 a2 a3).IsRun15 β x1 x2 x3 lam) (k : ℕ) :
    stateVec β (x2 k) (x3 k) (lam k) =
      (Mmat a1 a2 a3 ^ k) *ᵥ stateVec β (x2 0) (x3 0) (lam 0) := by sorry

end ExtADMM.Diverge
