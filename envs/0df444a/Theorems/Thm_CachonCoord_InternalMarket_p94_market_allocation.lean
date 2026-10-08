-- Prove2me | Theorems.Thm_CachonCoord_InternalMarket_p94_market_allocation
-- name    : CachonCoord.InternalMarket.p94_market_allocation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:56:53.820991+00:00
-- url     : https://prove2.me/theorems/5be8eb03-146f-4c25-b9ea-77268350b3a8
-- title:
--   §6.9.1, pp. 93–94 — at the price w(α, Q) the retailers order γ°(α)Q and (1 − γ°(α))Q, in total Q, and this allocation maximizes revenue
-- statement:
--   Let $\eta>1$, $\alpha_1,\alpha_2>0$ and $Q>0$, and let the supplier charge both retailers the per-unit price
--   $$
--   w(\alpha,Q)=\Big(\frac{\eta-1}{\eta}\Big)(\alpha_1^\eta+\alpha_2^\eta)^{1/\eta}Q^{-1/\eta}.
--   $$
--   Write $\gamma^o(\alpha)=\alpha_1^\eta/(\alpha_1^\eta+\alpha_2^\eta)$ and $r=(\eta-1)/\eta$. Then:
--
--   1. retailer one's unique optimal quantity over $[0,\infty)$ is $q_1^*=\gamma^o(\alpha)Q$, and retailer two's is $q_2^*=(1-\gamma^o(\alpha))Q$;
--   2. so the retailers order exactly $q_1^*+q_2^*=Q$ units in total;
--   3. this allocation maximizes the retailers' total revenue: for all $q_1,q_2\ge0$ with $q_1+q_2\le Q$,
--   $$
--   \alpha_1q_1^{r}+\alpha_2q_2^{r}\le\alpha_1(q_1^*)^{r}+\alpha_2(q_2^*)^{r}.
--   $$
--
--   The price $w(\alpha,Q)$ therefore clears the market and allocates the output as the integrated supply chain would.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.9.1, p. 93 ("It follows that q*_i = γ°(α)Q when w = w(α, Q)") and p. 94 ("Hence, when the supplier charges w(α, Q) …")

import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue

namespace CachonCoord.InternalMarket

/-- §6.9.1, pp. 93–94 (Cachon 2003, 3rd draft): when the supplier charges
`w(α, Q) = ((η − 1)/η)(α₁^η + α₂^η)^{1/η} Q^{−1/η}` (`α₁, α₂ > 0`, `η > 1`, `Q > 0`),
1. retailer one's unique optimal quantity over `[0, ∞)` is `γ°(α) Q` and retailer two's is
   `(1 − γ°(α)) Q`, so the retailers order exactly `Q` units in total;
2. this allocation maximizes the retailers' total revenue `α₁ q₁^{(η−1)/η} + α₂ q₂^{(η−1)/η}` over all
   allocations `q₁, q₂ ≥ 0` with `q₁ + q₂ ≤ Q`. -/
theorem p94_market_allocation (η α₁ α₂ Q : ℝ) (hη : 1 < η) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hQ : 0 < Q) :
    (∀ q : ℝ, 0 ≤ q →
      (IsMaxOn (retailerProfit η α₁ (price η α₁ α₂ Q)) (Set.Ici 0) q ↔
        q = optShare η α₁ α₂ * Q)) ∧
    (∀ q : ℝ, 0 ≤ q →
      (IsMaxOn (retailerProfit η α₂ (price η α₁ α₂ Q)) (Set.Ici 0) q ↔
        q = (1 - optShare η α₁ α₂) * Q)) ∧
    optShare η α₁ α₂ * Q + (1 - optShare η α₁ α₂) * Q = Q ∧
    ∀ q₁ q₂ : ℝ, 0 ≤ q₁ → 0 ≤ q₂ → q₁ + q₂ ≤ Q →
      α₁ * q₁ ^ ((η - 1) / η) + α₂ * q₂ ^ ((η - 1) / η) ≤
        α₁ * (optShare η α₁ α₂ * Q) ^ ((η - 1) / η) +
          α₂ * ((1 - optShare η α₁ α₂) * Q) ^ ((η - 1) / η) := by sorry

end CachonCoord.InternalMarket
