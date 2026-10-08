-- Prove2me | Theorems.Thm_CachonCoord_InternalMarket_sec_6_9_1_internal_market
-- name    : CachonCoord.InternalMarket.sec_6_9_1_internal_market
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:10:04.842028+00:00
-- url     : https://prove2.me/theorems/dd7a3be7-1a4b-47d0-b36b-951ddda8f30b
-- title:
--   §6.9.1, pp. 93–94 — the market at w(α, Q) allocates output optimally, ∂π/∂Q = w, and paying (46) per unit induces e° at zero expected profit
-- statement:
--   Consider the internal-market model of §6.9.1: elasticity $\eta>1$, demand shocks $A_1,A_2>0$, output shock $Y\in[0,1]$, output $Q=Ye$ from effort $e$ at the strictly convex increasing cost $c(e)$, retailer profits $\pi_i(q_i,w)=\alpha_iq_i^{(\eta-1)/\eta}-wq_i$, and the contingent price
--   $$
--   w(\alpha,Q)=\Big(\frac{\eta-1}{\eta}\Big)(\alpha_1^\eta+\alpha_2^\eta)^{1/\eta}Q^{-1/\eta}.
--   $$
--
--   1. **The market allocates output optimally.** For every realization $\alpha_1,\alpha_2>0$ and output $Q>0$: at the price $w(\alpha,Q)$ retailer one's unique optimal quantity is $\gamma^o(\alpha)Q$ and retailer two's is $(1-\gamma^o(\alpha))Q$, where $\gamma^o(\alpha)=\alpha_1^\eta/(\alpha_1^\eta+\alpha_2^\eta)$, so they order exactly $Q$ in total; this allocation maximizes the retailers' total revenue over all $q_1,q_2\ge0$ with $q_1+q_2\le Q$; and $w(\alpha,Q)$ is the marginal value of output,
--   $$
--   \frac{\partial\pi(\alpha,Q)}{\partial Q}=w(\alpha,Q).
--   $$
--   2. **The payment (46) induces the optimal effort.** Assume $K=E\big[(A_1^\eta+A_2^\eta)^{1/\eta}Y^{(\eta-1)/\eta}\big]$ has an integrable integrand, $E[Y]>0$, and $e^o>0$ satisfies (45). If the supplier pays the manager
--   $$
--   \Big(\frac{\eta-1}{\eta}\Big)(e^o)^{-1/\eta}K/E[Y]
--   $$
--   per unit of realized output, then $e^o$ uniquely maximizes the manager's expected utility over $e\ge0$, the payment equals $E[Q\,w(A,Q)\mid e^o]/E[Q\mid e^o]$, and the supplier's expected profit from the internal market at $e^o$ is zero.
--
--   Together these say that an internal market for output, plus a linear payment for realized output, coordinates the production and allocation decisions without the supplier observing the demand shocks or the manager's effort.
--
--   **Formalization Note** $E[Y]>0$ and the integrability of the integrand of $K$ are added (the page divides by $E[Y]$ and takes the expectation). The existence of an effort satisfying (45) is a hypothesis, as on the page. The supplier's per-unit price must be positive for the retailers' problems to have solutions; $w(\alpha,Q)>0$ automatically.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.9.1, pp. 93–94 (retailers' orders at w(α, Q), ∂π(α, Q)/∂Q = w(α, Q), Eq. (46), u(e), zero expected profit)

import Mathlib
import Definitions.Def_CachonCoord_InternalMarket_Revenue
import Definitions.Def_CachonCoord_InternalMarket_Model

namespace CachonCoord.InternalMarket

open MeasureTheory

/-- §6.9.1, pp. 93–94 (Cachon 2003, 3rd draft), the internal market coordinates the chain.
1. **The market.** For every realization `α₁, α₂ > 0` and output `Q > 0`, at the price `w(α, Q)`
   retailer one's unique optimal quantity is `γ°(α) Q` and retailer two's is `(1 − γ°(α)) Q` (so they
   order exactly `Q` in total), this allocation maximizes total retailer revenue over all
   `q₁, q₂ ≥ 0` with `q₁ + q₂ ≤ Q`, and `∂π(α, Q)/∂Q = w(α, Q)`.
2. **The manager.** If `K = E[(A₁^η + A₂^η)^{1/η} Y^{(η−1)/η}]` is integrable, `E[Y] > 0` and `e° > 0`
   satisfies (45), then under the per-unit payment (46) the manager's expected utility
   `u(e) = payRate(e°) E[Ye] − c(e)` is uniquely maximized over `[0, ∞)` at `e°`, the payment rate
   equals `E[Q w(A, Q) | e°] / E[Q | e°]`, and the supplier's expected profit from the market,
   `E[Q w(A, Q) | e°] − payRate(e°) E[Q | e°]`, is zero. -/
theorem sec_6_9_1_internal_market {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) :
    (∀ α₁ α₂ Q : ℝ, 0 < α₁ → 0 < α₂ → 0 < Q →
      (∀ q : ℝ, 0 ≤ q →
        (IsMaxOn (retailerProfit M.η α₁ (price M.η α₁ α₂ Q)) (Set.Ici 0) q ↔
          q = optShare M.η α₁ α₂ * Q)) ∧
      (∀ q : ℝ, 0 ≤ q →
        (IsMaxOn (retailerProfit M.η α₂ (price M.η α₁ α₂ Q)) (Set.Ici 0) q ↔
          q = (1 - optShare M.η α₁ α₂) * Q)) ∧
      (∀ q₁ q₂ : ℝ, 0 ≤ q₁ → 0 ≤ q₂ → q₁ + q₂ ≤ Q →
        α₁ * q₁ ^ ((M.η - 1) / M.η) + α₂ * q₂ ^ ((M.η - 1) / M.η) ≤
          α₁ * (optShare M.η α₁ α₂ * Q) ^ ((M.η - 1) / M.η) +
            α₂ * ((1 - optShare M.η α₁ α₂) * Q) ^ ((M.η - 1) / M.η)) ∧
      HasDerivAt (fun Q' => optRevenue M.η α₁ α₂ Q') (price M.η α₁ α₂ Q) Q) ∧
    (Integrable (fun ω => (M.A₁ ω ^ M.η + M.A₂ ω ^ M.η) ^ (1 / M.η) *
        M.Y ω ^ ((M.η - 1) / M.η)) M.P →
      0 < ∫ ω, M.Y ω ∂M.P →
      ∀ eo : ℝ, 0 < eo →
        (M.η - 1) / M.η * eo ^ (-1 / M.η) * M.K - M.c' eo = 0 →
        IsMaxOn (M.managerUtility eo) (Set.Ici 0) eo ∧
        (∀ e : ℝ, 0 ≤ e → IsMaxOn (M.managerUtility eo) (Set.Ici 0) e → e = eo) ∧
        M.payRate eo = M.expMarketRevenue eo / M.expOutput eo ∧
        M.expMarketRevenue eo - M.payRate eo * M.expOutput eo = 0) := by sorry

end CachonCoord.InternalMarket
