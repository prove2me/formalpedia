-- Prove2me | Theorems.Thm_DDMomentDRO_Type3_lmi_rewrite_C20d
-- name    : DDMomentDRO.Type3.lmi_rewrite_C20d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:45:23.668617+00:00
-- url     : https://prove2.me/theorems/eb0e1cd1-7fac-4515-a5cf-785b9418e4d8
-- title:
--   Proof of Theorem 3, p. 38 — (C-20d) rewritten as a positive semidefinite block matrix
-- statement:
--   Let $\Sigma(x) \in \mathbb R^{J\times J}$ be positive definite, $\mu(x),\tau \in \mathbb R^J$ and $\gamma \in \mathbb R$. Then the ellipsoidal mean constraint (C-20d) holds exactly when the bordered matrix is positive semidefinite:
--   $$(\tau-\mu(x))^\top \Sigma(x)^{-1} (\tau-\mu(x)) \le \gamma \iff \begin{pmatrix}\Sigma(x) & \tau-\mu(x)\\ (\tau-\mu(x))^\top & \gamma\end{pmatrix} \succeq 0.$$
--
--   This is the step that turns the inverse-matrix constraint of the Type 3 ambiguity set into a linear matrix inequality in $\tau$, so that the inner problem of the Bellman equation becomes a conic program to which semidefinite duality applies.
--
--   **Formalization Note** The block matrix is indexed by `Fin J ⊕ Unit`; $\succeq 0$ is Mathlib's `PosSemidef`, which includes symmetry. The hypothesis $\Sigma(x) \succ 0$ is implicit on the page (it writes $\Sigma(x)^{-1}$) and is required: Mathlib's inverse of a singular matrix is zero.
-- source:
--   Yu & Shen, Multistage distributionally robust mixed-integer programming with decision-dependent moment-based ambiguity sets, arXiv:2002.12518v3, p. 38, proof of Theorem 3, display after (C-20f)

import Mathlib
import Definitions.Def_DDMomentDRO_Type3_Setting

namespace DDMomentDRO.Type3

open Matrix

theorem lmi_rewrite_C20d {I J : ℕ} (μ : (Fin I → ℝ) → Fin J → ℝ)
    (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ) (γ : ℝ) (x : Fin I → ℝ)
    (τ : Fin J → ℝ) (hSig : (Sig x).PosDef) :
    (τ - μ x) ⬝ᵥ ((Sig x)⁻¹ *ᵥ (τ - μ x)) ≤ γ ↔
      (block2 (Sig x) (τ - μ x) γ).PosSemidef := by sorry

end DDMomentDRO.Type3
