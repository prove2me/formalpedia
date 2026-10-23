-- Prove2me | Theorems.Thm_ExplodingOffer_Mrl_lemma_4
-- name    : ExplodingOffer.Mrl.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:55.625707+00:00
-- url     : https://prove2.me/theorems/43b398f6-d0ac-48c1-8de6-1e280fe703a9
-- title:
--   Lemma 4 (i)–(ii), p. 18 — X1 ≤mrl X2 gives x̄1 ≤ x̄2, b1 ≤ b2 and E[(X1 − s)⁺] ≤ E[(X2 − s)⁺] for all s
-- statement:
--   Let $X_1, X_2$ be nonnegative continuous random variables with supports $[a_1, b_1]$, $[a_2, b_2]$ and finite means $\bar x_1, \bar x_2$. Suppose $X_1 \le_{\mathrm{mrl}} X_2$, i.e. their mean residual life functions satisfy $m_1(t) \le m_2(t)$ for every real $t$, where $m_i(t) = \mathbb E[X_i - t \mid X_i > t]$ when $\mathbb P(X_i > t) > 0$ and $m_i(t) = 0$ otherwise. Then
--
--   1. $\bar x_1 \le \bar x_2$ and $b_1 \le b_2$;
--   2. for every $s \in \mathbb R$,
--   $$\mathbb E[(X_1 - s)^+] \le \mathbb E[(X_2 - s)^+].$$
--
--   Part 2 says that the stop-loss transform $\mathcal L_1$ is dominated by $\mathcal L_2$; it is the comparison that drives the comparative statics of Theorem 3. The paper cites Shaked and Shanthikumar (2007), where the mrl order is shown to imply the increasing convex order.
--
--   **Formalization Note** The mrl order is the platform's `MrlOrder` with the identity random variables on $(\mathbb R, \mu_i)$. For continuous nonnegative laws it agrees with the paper's order on $s \ge 0$ (the platform uses $X > t$, the paper $X \ge s$; at $s = b$ both give $0$, and for $t < 0$ the platform's comparison is the one at $t = 0$). Part (iii) of the paper's Lemma 4 (standard deviations) is not formalized.
-- source:
--   Hu & Tang, Size Matters, So Does Duration: The Interplay between Offer Size and Offer Deadline, SSRN preprint 3143414 (version of 2020-05-16), p. 18, Lemma 4 (i)–(ii)

import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_MrlOrder
import Definitions.Def_ExplodingOffer_Mrl_Model

namespace ExplodingOffer.Mrl

open MeasureTheory

theorem lemma_4 {μ₁ μ₂ : Measure ℝ} {a₁ a₂ : ℝ} {b₁ b₂ : EReal}
    (h₁ : OfferDist μ₁ a₁ b₁) (h₂ : OfferDist μ₂ a₂ b₂)
    (hmrl : StochasticOrders.MeanResidualLife.MrlOrder μ₁ μ₂ id id) :
    mean μ₁ ≤ mean μ₂ ∧ b₁ ≤ b₂ ∧ ∀ s : ℝ, Lfun μ₁ s ≤ Lfun μ₂ s := by sorry

end ExplodingOffer.Mrl
