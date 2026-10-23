-- Prove2me | Theorems.Thm_ExplodingOffer_Mrl_theorem_3
-- name    : ExplodingOffer.Mrl.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:43.764147+00:00
-- url     : https://prove2.me/theorems/299b739e-5887-42f9-bbf2-66cb05c70ec8
-- title:
--   Theorem 3, p. 18 — if X1 ≤mrl X2, a non-exploding optimum stays non-exploding (smaller, longer) and an exploding one stays exploding (smaller)
-- statement:
--   Let $X_1, X_2$ be nonnegative continuous random variables with supports $[a_i, b_i]$ and finite means $\bar x_i$, with $X_1 \le_{\mathrm{mrl}} X_2$, and let $\lambda > 0$, $T > 0$, $u > 0$. For $i = 1, 2$ let $\mathcal T_i$, $\hat s_i$ be the objects (3), (10) of $X_i$, and let $(s_i^*, t_{D,i}^*)$ be an optimal offer package (an optimal solution of problem (7)) when the alternative offer size is $X_i$. Then:
--
--   1. (if $u \ne \bar x_2$ or $a_2 = 0$) if $(s_1^*, t_{D,1}^*) = (\hat s_1, T - \mathcal T_1(\hat s_1)/\lambda)$ with $\hat s_1 < \mathcal T_1^{-1}(\lambda T)$, then $(s_2^*, t_{D,2}^*) = (\hat s_2, T - \mathcal T_2(\hat s_2)/\lambda)$ with $\hat s_2 < \mathcal T_2^{-1}(\lambda T)$, and
--   $$s_1^* \ge s_2^*, \qquad 0 < t_{D,1}^* \le t_{D,2}^*;$$
--   2. (if $u \ne \bar x_1$ or $a_1 = 0$) if $(s_2^*, t_{D,2}^*) = (\mathcal T_2^{-1}(\lambda T), 0)$, then $(s_1^*, t_{D,1}^*) = (\mathcal T_1^{-1}(\lambda T), 0)$, and $s_1^* \le s_2^*$, $t_{D,1}^* = t_{D,2}^* = 0$.
--
--   When the responder's alternatives get better in the mean residual life order, a proposer who was making a non-exploding offer keeps doing so with a smaller offer and a longer deadline, and a proposer who makes an exploding offer against the better alternatives also makes one, of smaller size, against the worse ones.
--
--   **Formalization Note** The packages are arbitrary optimal solutions of problem (7), not the closed form of Theorem 2. The paper speaks of "the" optimal package; it is unique except in the boundary case $u = \bar x_i$, $a_i > 0$ (see Theorem 2), where the statement fails as printed: for $X_1 = X_2$ uniform on $[1, 2]$, $u = 3/2$ and $\lambda T$ large enough that $\mathcal T^{-1}(\lambda T) > 1$, both $s = 1 = \hat s$ and $s = 1/2$ (each with its deadline $t_D^*(s)$) are optimal. Each part therefore carries the condition that excludes that case for the distribution whose package it concludes about. The mrl order is the platform's `MrlOrder` with the identity random variables.
-- source:
--   Hu & Tang, Size Matters, So Does Duration: The Interplay between Offer Size and Offer Deadline, SSRN preprint 3143414 (version of 2020-05-16), p. 18, Theorem 3

import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_MrlOrder
import Definitions.Def_ExplodingOffer_Mrl_Model

namespace ExplodingOffer.Mrl

open MeasureTheory

theorem theorem_3 {μ₁ μ₂ : Measure ℝ} {a₁ a₂ : ℝ} {b₁ b₂ : EReal}
    (h₁ : OfferDist μ₁ a₁ b₁) (h₂ : OfferDist μ₂ a₂ b₂)
    {lam T u : ℝ} (hlam : 0 < lam) (hT : 0 < T) (hu : 0 < u)
    (hmrl : StochasticOrders.MeanResidualLife.MrlOrder μ₁ μ₂ id id)
    {sh₁ sh₂ : ℝ} (hsh₁ : IsSHat μ₁ a₁ b₁ u sh₁) (hsh₂ : IsSHat μ₂ a₂ b₂ u sh₂)
    {s₁ t₁ s₂ t₂ : ℝ}
    (ho₁ : IsOptimalPackage μ₁ b₁ lam T u s₁ t₁)
    (ho₂ : IsOptimalPackage μ₂ b₂ lam T u s₂ t₂) :
    ((u ≠ mean μ₂ ∨ a₂ = 0) →
      (s₁ = sh₁ ∧ t₁ = T - Tval μ₁ sh₁ / lam ∧ sh₁ < Tinv μ₁ b₁ (lam * T)) →
        (s₂ = sh₂ ∧ t₂ = T - Tval μ₂ sh₂ / lam ∧ sh₂ < Tinv μ₂ b₂ (lam * T)) ∧
        s₂ ≤ s₁ ∧ 0 < t₁ ∧ t₁ ≤ t₂) ∧
    ((u ≠ mean μ₁ ∨ a₁ = 0) →
      (s₂ = Tinv μ₂ b₂ (lam * T) ∧ t₂ = 0) →
        (s₁ = Tinv μ₁ b₁ (lam * T) ∧ t₁ = 0) ∧ s₁ ≤ s₂ ∧ t₁ = 0 ∧ t₂ = 0) := by sorry

end ExplodingOffer.Mrl
