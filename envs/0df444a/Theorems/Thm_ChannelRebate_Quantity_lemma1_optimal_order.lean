-- Prove2me | Theorems.Thm_ChannelRebate_Quantity_lemma1_optimal_order
-- name    : ChannelRebate.Quantity.lemma1_optimal_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:13:32.160163+00:00
-- url     : https://prove2.me/theorems/e9e9bd90-e778-4ef5-b59c-16b9fbd25445
-- title:
--   Lemma 1, p. 995 — τ₀ ∈ (Q₀, Q₁) exists uniquely; the retailer orders Q₁ if T < τ₀, Q₀ if T > τ₀, either if T = τ₀
-- statement:
--   In the setting of the mission, let $0<c<w<p$, $s<c$, $u>0$, and let $Q_0, Q_1 > 0$ satisfy
--   $$
--   \Phi(Q_0) = \frac{p-w}{p-s}, \qquad \Phi(Q_1) = \frac{p+u-w}{p+u-s}.
--   $$
--   For a target $T$ put $f_0(T) = r(Q_0\mid T) - r(Q_1\mid T)$. Then:
--   1. **(a)** there is exactly one $\tau_0 \in [Q_0,Q_1]$ with $f_0(\tau_0) = 0$, and it lies in the open interval $(Q_0,Q_1)$;
--   2. **(b)** for every target $T \ge 0$, the set of the retailer's optimal orders under the target rebate $(w,u,T)$ is
--   $$
--   \arg\max_{Q\ge 0} r(Q\mid T) = \begin{cases} \{Q_1\} & T < \tau_0,\\ \{Q_0\} & T > \tau_0,\\ \{Q_0, Q_1\} & T = \tau_0. \end{cases}
--   $$
--
--   The lemma says the retailer either ignores the rebate and orders the wholesale newsvendor quantity, or "goes for" it and orders the newsvendor quantity at the effective price $p+u$, switching at the threshold $\tau_0$.
--
--   **Formalization Note** $\tau_0$ is not a function of the data: part (b) holds for every $\tau_0 \in [Q_0,Q_1]$ solving $f_0(\tau_0)=0$, which part (a) shows to be unique. The optimal-order claims are equalities of sets of maximizers over $Q \ge 0$.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 995, Lemma 1 (with the definitions of Q₁, f₀, τ₀ preceding it); proof p. 1005

import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts
import Definitions.Def_ChannelRebate_Quantity_Setting
open MeasureTheory

namespace ChannelRebate.Quantity

/-- Taylor (2002), Lemma 1, p. 995. With `Q₀ = Φ⁻¹((p − w)/(p − s))`,
`Q₁ = Φ⁻¹((p + u − w)/(p + u − s))` and `f₀(T) = r(Q₀|T) − r(Q₁|T)` on `T ∈ [Q₀, Q₁]`:
(a) the root `τ₀` of `f₀` on `[Q₀, Q₁]` exists, is unique and lies in `(Q₀, Q₁)`;
(b) the retailer's optimal order set is `{Q₁}` if `T < τ₀`, `{Q₀}` if `T > τ₀`, and
`{Q₀, Q₁}` if `T = τ₀`. -/
theorem lemma1_optimal_order (p c s w u : ℝ) (hc : 0 < c) (hcw : c < w) (hwp : w < p)
    (hsc : s < c) (hu : 0 < u) (D : Demand)
    (Q0 : ℝ) (hQ0 : 0 < Q0) (hΦ0 : Phi D Q0 = (p - w) / (p - s))
    (Q1 : ℝ) (hQ1 : 0 < Q1) (hΦ1 : Phi D Q1 = (p + u - w) / (p + u - s)) :
    -- (a)
    (∃! τ0 : ℝ, τ0 ∈ Set.Icc Q0 Q1 ∧
        retailerProfit p s w u τ0 D Q0 - retailerProfit p s w u τ0 D Q1 = 0) ∧
    (∀ τ0 : ℝ, τ0 ∈ Set.Icc Q0 Q1 →
        retailerProfit p s w u τ0 D Q0 - retailerProfit p s w u τ0 D Q1 = 0 →
        τ0 ∈ Set.Ioo Q0 Q1) ∧
    -- (b)
    (∀ τ0 : ℝ, τ0 ∈ Set.Icc Q0 Q1 →
      retailerProfit p s w u τ0 D Q0 - retailerProfit p s w u τ0 D Q1 = 0 →
      ∀ T : ℝ, 0 ≤ T →
        (T < τ0 → optimalOrders (retailerProfit p s w u T D) = {Q1}) ∧
        (τ0 < T → optimalOrders (retailerProfit p s w u T D) = {Q0}) ∧
        (T = τ0 → optimalOrders (retailerProfit p s w u T D) = {Q0, Q1})) := by sorry

end ChannelRebate.Quantity
