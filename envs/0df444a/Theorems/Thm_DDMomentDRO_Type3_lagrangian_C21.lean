-- Prove2me | Theorems.Thm_DDMomentDRO_Type3_lagrangian_C21
-- name    : DDMomentDRO.Type3.lagrangian_C21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:45:23.520987+00:00
-- url     : https://prove2.me/theorems/dd9cf0ae-438b-46c8-a16e-d1d129aca16b
-- title:
--   (C-21), p. 38 — the Lagrangian of (C-20), regrouped by p and τ
-- statement:
--   For every state $x$, weights $p \in \mathbb R^K$, $\tau \in \mathbb R^J$, and dual variables $s \in \mathbb R$, $u \in \mathbb R^J$, $z_1, Y \in \mathbb R^{J\times J}$, $z_2 \in \mathbb R^J$, $z_3 \in \mathbb R$, the Lagrangian $L(p,\tau,s,u,Z,Y)$ of (C-20) (first line of (C-21)) satisfies
--   $$L = \sum_{k=1}^K p_k\Big(Q^k(x) - s - u^\top\xi^k - M_k(x)\bullet Y\Big) + \tau^\top(u+2z_2) + s + \Sigma(x)\bullet z_1 - \mu(x)^\top(2z_2) + \gamma z_3 + \eta\,\Sigma(x)\bullet Y,$$
--   where $M_k(x) = (\xi^k-\mu(x))(\xi^k-\mu(x))^\top$ and $A\bullet B = \operatorname{tr}(A^\top B)$.
--
--   The regrouping isolates the coefficient of each $p_k$ and of $\tau$, which is what determines the dual function in (C-22).
--
--   **Formalization Note** This is an algebraic identity with no hypotheses; it holds for arbitrary (not necessarily symmetric) $z_1$, $Y$ and $\Sigma(x)$.
-- source:
--   Yu & Shen, Multistage distributionally robust mixed-integer programming with decision-dependent moment-based ambiguity sets, arXiv:2002.12518v3, p. 38, proof of Theorem 3, (C-21)

import Mathlib
import Definitions.Def_DDMomentDRO_Type3_Setting

namespace DDMomentDRO.Type3

open Matrix

theorem lagrangian_C21 {I J K : ℕ} (Qn : (Fin I → ℝ) → Fin K → ℝ) (ξ : Fin K → Fin J → ℝ)
    (μ : (Fin I → ℝ) → Fin J → ℝ) (Sig : (Fin I → ℝ) → Matrix (Fin J) (Fin J) ℝ)
    (γ η : ℝ) (x : Fin I → ℝ) (p : Fin K → ℝ) (τ : Fin J → ℝ) (s : ℝ) (u : Fin J → ℝ)
    (z1 : Matrix (Fin J) (Fin J) ℝ) (z2 : Fin J → ℝ) (z3 : ℝ)
    (Y : Matrix (Fin J) (Fin J) ℝ) :
    lagr Qn ξ μ Sig γ η x p τ s u z1 z2 z3 Y =
      ∑ k, p k * (Qn x k - s - u ⬝ᵥ ξ k - frob (outerDev ξ μ x k) Y)
        + τ ⬝ᵥ (u + 2 • z2) + s + frob (Sig x) z1 - μ x ⬝ᵥ (2 • z2) + γ * z3
        + η * frob (Sig x) Y := by sorry

end DDMomentDRO.Type3
