-- Prove2me | Theorems.Thm_ConvexOptAlg_CoordDescent_thm_6_7_expected_decrease
-- name    : ConvexOptAlg.CoordDescent.thm_6_7_expected_decrease
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T19:08:38.290194+00:00
-- url     : https://prove2.me/theorems/c7278975-96fa-4504-8d93-3a9c74795d44
-- title:
--   §6.4.1, proof of Theorem 6.7, p. 340 — one RCD(γ) step decreases f in expectation by (‖∇f(x)‖*_[1−γ])²/(2Σβ_i^γ)
-- statement:
--   Let $n\ge1$, $\gamma\ge0$, $\beta_1,\dots,\beta_n>0$, and let $f:\mathbb R^n\to\mathbb R$ be differentiable and directionally smooth with constants $\beta_i$. Let $x\in\mathbb R^n$ (the current iterate $x_s$) and draw the coordinate $i$ from $p_\gamma(i)=\beta_i^\gamma/\sum_j\beta_j^\gamma$. Then
--
--   $$\sum_{i=1}^n p_\gamma(i)\,f\Big(x-\frac{1}{\beta_i}\nabla_i f(x)e_i\Big)-f(x)\le-\frac{1}{2\sum_{i=1}^n\beta_i^\gamma}\Big(\|\nabla f(x)\|^*_{[1-\gamma]}\Big)^2,$$
--
--   where $\|v\|^*_{[1-\gamma]}=\sqrt{\sum_i v_i^2/\beta_i^{1-\gamma}}$. The left side is $\mathbb E_{i_s}f(x_{s+1})-f(x_s)$ for one step of RCD(γ).
--
--   This is the expected one-step decrease that drives both Theorem 6.7 and Theorem 6.8.
--
--   **Formalization Note** $n\ge1$ and $\beta_i>0$ are added: $p_\gamma$ and the step $1/\beta_i$ require them. The expectation over one draw is written as the finite sum. Convexity is not assumed (it is not used).
-- source:
--   Bubeck, arXiv:1405.4980v2, §6.4.1, proof of Theorem 6.7, second display, p. 340

import Mathlib
import Definitions.Def_ConvexOptAlg_CoordDescent_Defs

namespace ConvexOptAlg.CoordDescent

/-- Proof of Theorem 6.7, second display (Bubeck, arXiv:1405.4980v2, §6.4.1, p. 340): for a
coordinate-wise smooth `f` with constants `βᵢ > 0`, `γ ≥ 0` and any point `x` (the current iterate
`x_s`), the expected value of `f` after one RCD(γ) step, with the coordinate `i` drawn from `p_γ`,
satisfies
`Σᵢ p_γ(i) f(x − (1/βᵢ)∇ᵢ f(x) eᵢ) − f(x) ≤ −(1/(2 Σᵢ βᵢ^γ)) (‖∇f(x)‖*_[1−γ])²`. -/
theorem thm_6_7_expected_decrease {n : ℕ} (hn : 0 < n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : Fin n → ℝ) (γ : ℝ)
    (hγ : 0 ≤ γ) (hβ : ∀ i, 0 < β i) (hsm : IsCoordSmooth f g β) (x : EuclideanSpace ℝ (Fin n)) :
    (∑ i, pGamma β γ i * f (rcdStep β g x i)) - f x ≤
      -(1 / (2 * ∑ i, β i ^ γ)) * wnormDual β (1 - γ) (g x) ^ 2 := by sorry

end ConvexOptAlg.CoordDescent
