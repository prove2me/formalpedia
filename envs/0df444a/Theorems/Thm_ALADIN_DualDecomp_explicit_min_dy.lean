-- Prove2me | Theorems.Thm_ALADIN_DualDecomp_explicit_min_dy
-- name    : ALADIN.DualDecomp.explicit_min_dy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:04.348996+00:00
-- url     : https://prove2.me/theorems/833e9fec-a2d8-43b1-9132-94464184cd68
-- title:
--   App. A, proof of Lemma 5 — explicit minimization of ½ΔᵀHΔ + wᵀΔ over {CΔ = 0}
-- statement:
--   Let $H\in\mathbb R^{n\times n}$ be symmetric positive definite, $C\in\mathbb R^{n_h\times n}$ of full row rank $n_h$, and $w\in\mathbb R^n$. Put
--   $$P = H^{-1} - H^{-1}C^\top\big(CH^{-1}C^\top\big)^{-1}CH^{-1}.$$
--   Then
--   1. $CH^{-1}C^\top$ is invertible;
--   2. $\Delta^\star = -Pw$ satisfies $C\Delta^\star = 0$;
--   3. $\Delta^\star$ minimizes $\Delta\mapsto\tfrac12\Delta^\top H\Delta + w^\top\Delta$ over $\{\Delta : C\Delta = 0\}$;
--   4. the minimum value is $-\tfrac12\,w^\top P w$;
--   5. $w^\top P w\ge 0$.
--
--   In the proof of Lemma 5 this is applied blockwise with $H = H_i$, $C = C_i$, $w = A_i^\top(\lambda_{\mathrm{QP}}-\lambda)$: summing the minimum values gives $\tfrac12(\lambda_{\mathrm{QP}}-\lambda)^\top M(\lambda_{\mathrm{QP}}-\lambda)$ with $M$ from (the corrected) (A.6), and item 5 shows that $M$ is negative semidefinite.
-- source:
--   Houska, Frasch, Diehl, An augmented Lagrangian based algorithm for distributed nonconvex optimization, SIAM J. Optim. 26 (2016), p. 1124, App. A, proof of Lemma 5, explicit minimization over Δy

import Mathlib

namespace ALADIN.DualDecomp

open Matrix

/-- App. A, proof of Lemma 5, p. 1124 ("we solve the remaining minimization problem over Δy
explicitly"): for `H ∈ ℝ^{n×n}` positive definite, `C ∈ ℝ^{nh×n}` of full row rank and `w ∈ ℝⁿ`, put
`P = H⁻¹ − H⁻¹ Cᵀ (C H⁻¹ Cᵀ)⁻¹ C H⁻¹`. Then `C H⁻¹ Cᵀ` is invertible, `Δ⋆ = −P w` satisfies `C Δ⋆ = 0`
and minimizes `½ Δᵀ H Δ + wᵀ Δ` over `{Δ | C Δ = 0}`, the minimum value is `−½ wᵀ P w`, and `wᵀ P w ≥ 0`. -/
theorem explicit_min_dy {n nh : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin nh) (Fin n) ℝ)
    (hH : H.PosDef) (hC : C.rank = nh) (w : Fin n → ℝ) :
    let P := H⁻¹ - H⁻¹ * Cᵀ * (C * H⁻¹ * Cᵀ)⁻¹ * C * H⁻¹
    IsUnit (C * H⁻¹ * Cᵀ).det ∧
    C *ᵥ (-(P *ᵥ w)) = 0 ∧
    IsMinOn (fun Δ : Fin n → ℝ => 1 / 2 * (Δ ⬝ᵥ (H *ᵥ Δ)) + w ⬝ᵥ Δ) {Δ | C *ᵥ Δ = 0}
      (-(P *ᵥ w)) ∧
    1 / 2 * ((-(P *ᵥ w)) ⬝ᵥ (H *ᵥ (-(P *ᵥ w)))) + w ⬝ᵥ (-(P *ᵥ w)) = -(1 / 2) * (w ⬝ᵥ (P *ᵥ w)) ∧
    0 ≤ w ⬝ᵥ (P *ᵥ w) := by sorry

end ALADIN.DualDecomp
