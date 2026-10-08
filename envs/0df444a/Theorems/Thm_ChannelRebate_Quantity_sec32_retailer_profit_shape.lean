-- Prove2me | Theorems.Thm_ChannelRebate_Quantity_sec32_retailer_profit_shape
-- name    : ChannelRebate.Quantity.sec32_retailer_profit_shape
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:58.854985+00:00
-- url     : https://prove2.me/theorems/7156e79c-f50a-4f8a-bdfe-f535f48c8ae5
-- title:
--   §3.2, p. 995 — r(·|T) is piecewise, with derivative p−w−(p−s)Φ(Q) below T and p+u−w−(p+u−s)Φ(Q) above; strictly concave on [0,T) and (T,∞); kink up at T
-- statement:
--   In the setting of the mission (demand density $\varphi$ positive on $[0,\infty)$ and zero on $(-\infty,0)$, $0<c<w<p$, $s<c$), let $u > 0$ and $T \ge 0$, and let $r(Q\mid T)$ be the retailer's profit under the target rebate $(w,u,T)$. Then:
--   1. for $0 \le Q \le T$,
--   $$
--   r(Q\mid T) = (p-w)Q - (p-s)\int_0^Q (Q-\xi)\,d\Phi(\xi);
--   $$
--   2. for $Q > T$,
--   $$
--   r(Q\mid T) = (p-w)Q - (p-s)\int_0^Q (Q-\xi)\,d\Phi(\xi) + u\Big(\int_T^Q (\xi-T)\,d\Phi(\xi) + (Q-T)[1-\Phi(Q)]\Big);
--   $$
--   3. $r(\cdot\mid T)$ is differentiable at every $Q \in (0,T)$ with derivative $p-w-(p-s)\Phi(Q)$, and at every $Q > T$ with derivative $p+u-w-(p+u-s)\Phi(Q)$;
--   4. $r(\cdot\mid T)$ is strictly concave on $[0,T)$ and on $(T,\infty)$;
--   5. $r(\cdot\mid T)$ is continuous;
--   6. the derivative tends to $p-w-(p-s)\Phi(T)$ as $Q \to T^-$ and to $p+u-w-(p+u-s)\Phi(T)$ as $Q \to T^+$, and the left limit is strictly smaller than the right limit.
--
--   The upward kink at the target is what makes the retailer's problem non-concave and produces the two candidate orders of Lemma 1.
--
--   **Formalization Note** No continuity of $\varphi$ is assumed; the derivatives exist because $\Phi$ is continuous. The derivative used in item 6 is Lean's `deriv`, which agrees with the formulas of item 3 near $T$.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 995, §3.2 (display of r(Q|T), its derivative, and the following paragraph)

import Mathlib
import Definitions.Def_CachonCoord_Newsvendor_Contracts
import Definitions.Def_ChannelRebate_Quantity_Setting
open MeasureTheory

open Filter Topology

namespace ChannelRebate.Quantity

/-- Taylor (2002), §3.2, p. 995. The piecewise form of `r(Q|T)`, its derivative on each
piece, strict concavity on `[0, T)` and on `(T, ∞)`, continuity, and the upward kink of the
derivative at the target `T`. -/
theorem sec32_retailer_profit_shape (p c s w u T : ℝ) (hc : 0 < c) (hcw : c < w) (hwp : w < p)
    (hsc : s < c) (hu : 0 < u) (hT : 0 ≤ T) (D : Demand) :
    -- the two closed forms
    (∀ Q : ℝ, 0 ≤ Q → Q ≤ T →
      retailerProfit p s w u T D Q =
        (p - w) * Q - (p - s) * ∫ x in (0 : ℝ)..Q, (Q - x) * D.φ x) ∧
    (∀ Q : ℝ, T < Q →
      retailerProfit p s w u T D Q =
        (p - w) * Q - (p - s) * (∫ x in (0 : ℝ)..Q, (Q - x) * D.φ x)
          + u * ((∫ x in T..Q, (x - T) * D.φ x) + (Q - T) * (1 - Phi D Q))) ∧
    -- the derivative on each piece
    (∀ Q : ℝ, 0 < Q → Q < T →
      HasDerivAt (retailerProfit p s w u T D) (p - w - (p - s) * Phi D Q) Q) ∧
    (∀ Q : ℝ, T < Q →
      HasDerivAt (retailerProfit p s w u T D) (p + u - w - (p + u - s) * Phi D Q) Q) ∧
    -- strict concavity on each piece
    StrictConcaveOn ℝ (Set.Ico 0 T) (retailerProfit p s w u T D) ∧
    StrictConcaveOn ℝ (Set.Ioi T) (retailerProfit p s w u T D) ∧
    -- continuity
    Continuous (retailerProfit p s w u T D) ∧
    -- the kink: the left limit of the derivative at T is below the right limit
    Tendsto (deriv (retailerProfit p s w u T D)) (𝓝[<] T)
      (𝓝 (p - w - (p - s) * Phi D T)) ∧
    Tendsto (deriv (retailerProfit p s w u T D)) (𝓝[>] T)
      (𝓝 (p + u - w - (p + u - s) * Phi D T)) ∧
    p - w - (p - s) * Phi D T < p + u - w - (p + u - s) * Phi D T := by sorry

end ChannelRebate.Quantity
