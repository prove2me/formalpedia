-- Prove2me | Theorems.Thm_ExplodingOffer_Mrl_theorem_3_order_steps
-- name    : ExplodingOffer.Mrl.theorem_3_order_steps
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:46.370141+00:00
-- url     : https://prove2.me/theorems/78fb4daa-936e-458c-a9c7-d452fe886cea
-- title:
--   Proof of Theorem 3, p. 37 — X1 ≤mrl X2 gives 𝒯1 ≥ 𝒯2, 𝒯1⁻¹(λT) ≤ 𝒯2⁻¹(λT), and ŝ1 ≥ ŝ2 for 0 < u < b1
-- statement:
--   Let $X_1, X_2$ be nonnegative continuous random variables with supports $[a_i, b_i]$ and finite means, with $X_1 \le_{\mathrm{mrl}} X_2$, and let $\lambda > 0$, $T > 0$. Write $\mathcal T_i$, $\mathcal T_i^{-1}$ and $\hat s_i$ for the objects (3) and (10) of $X_i$. Then
--
--   1. $\mathcal T_1(V) \ge \mathcal T_2(V)$ for every $0 \le V < b_1$;
--   2. $\mathcal T_1^{-1}(\lambda T) \le \mathcal T_2^{-1}(\lambda T)$;
--   3. for every $0 < u < b_1$, if $\hat s_1$ and $\hat s_2$ satisfy (10) for $X_1$ and $X_2$, then
--   $$\hat s_1 \ge \hat s_2.$$
--
--   These are the two comparisons that the proof of Theorem 3 combines with Theorem 2.
--
--   **Formalization Note** The page says "for any $V \ge 0$"; for $V \ge b_1$ the page's $\mathcal T_1(V)$ is $+\infty$, and the statement is restricted to $V < b_1$, where $\mathcal T_1$ is finite.
-- source:
--   Hu & Tang, Size Matters, So Does Duration: The Interplay between Offer Size and Offer Deadline, SSRN preprint 3143414 (version of 2020-05-16), p. 37, proof of Theorem 3

import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_MrlOrder
import Definitions.Def_ExplodingOffer_Mrl_Model

namespace ExplodingOffer.Mrl

open MeasureTheory

theorem theorem_3_order_steps {μ₁ μ₂ : Measure ℝ} {a₁ a₂ : ℝ} {b₁ b₂ : EReal}
    (h₁ : OfferDist μ₁ a₁ b₁) (h₂ : OfferDist μ₂ a₂ b₂)
    (hmrl : StochasticOrders.MeanResidualLife.MrlOrder μ₁ μ₂ id id)
    {lam T : ℝ} (hlam : 0 < lam) (hT : 0 < T) :
    (∀ V : ℝ, 0 ≤ V → (V : EReal) < b₁ → Tval μ₂ V ≤ Tval μ₁ V) ∧
    Tinv μ₁ b₁ (lam * T) ≤ Tinv μ₂ b₂ (lam * T) ∧
    (∀ u sh₁ sh₂ : ℝ, 0 < u → (u : EReal) < b₁ →
      IsSHat μ₁ a₁ b₁ u sh₁ → IsSHat μ₂ a₂ b₂ u sh₂ → sh₂ ≤ sh₁) := by sorry

end ExplodingOffer.Mrl
