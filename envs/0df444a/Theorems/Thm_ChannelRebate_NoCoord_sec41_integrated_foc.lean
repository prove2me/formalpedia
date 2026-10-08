-- Prove2me | Theorems.Thm_ChannelRebate_NoCoord_sec41_integrated_foc
-- name    : ChannelRebate.NoCoord.sec41_integrated_foc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:21:10.636958+00:00
-- url     : https://prove2.me/theorems/854ab1d9-bd8c-4d2a-aa30-bf9096089d40
-- title:
--   §4.1, p. 999 — the integrated optimum satisfies V′(ē) = (p − s)Γ(Q̄₀), Q̄ = ēQ̄₀, and earns Π = ēV′(ē) − V(ē)
-- statement:
--   Let demand be $e\xi$, where $\xi$ has a density $\varphi$ that vanishes on $(-\infty, 0)$ and is strictly positive on $[0, \infty)$ with finite mean, and let the effort cost $V$ satisfy $V(0) = 0$, be strictly increasing and strictly convex on $[0, \infty)$ and differentiable on $(0, \infty)$ with derivative $V'$. Let $0 < c$, $s < c < p$, and let $\bar Q_0 > 0$ be the critical fractile of the integrated channel,
--   $$\Phi(\bar Q_0) = \frac{p - c}{p - s}.$$
--   If $(\bar Q, \bar e)$ maximizes the integrated channel's profit $\Pi(Q, e) = -cQ + pE\min(Q, e\xi) + sE(Q - e\xi)^+ - V(e)$ over $Q \ge 0$, $e \ge 0$, and $\bar e > 0$, then
--   $$\bar Q = \bar e\,\bar Q_0, \qquad V'(\bar e) = (p - s)\,\Gamma(\bar Q_0), \qquad \Pi(\bar Q, \bar e) = \Lambda(\bar e) = \bar e\,V'(\bar e) - V(\bar e),$$
--   where $\Gamma(Q) = \int_0^Q \xi\,d\Phi(\xi)$.
--
--   These are the integrated channel's first-order conditions and its optimal profit. They fix the benchmark $(\bar Q, \bar e)$ that a coordinating contract must induce the retailer to choose.
--
--   **Formalization Note** The paper assumes in words that an optimal solution exists; the statement takes an optimal pair as a hypothesis. Its positivity $\bar e > 0$ is a disclosed hypothesis: the first-order condition in $e$ is an interior condition, and the paper's optimum is interior. The derivative $V'$ comes with the effort-cost structure (differentiability is used but not stated in the paper). The fractile $\Phi^{-1}((p-c)/(p-s))$ is given by its defining equation.
-- source:
--   Taylor, Supply Chain Coordination Under Channel Rebates with Sales Effort Effects, Management Science 48(8) (2002), p. 999, §4.1 (first-order conditions and Π = Λ(ē)); p. 995, §3.1 (Q̄₀, Γ)

import Mathlib
import Definitions.Def_ChannelRebate_NoCoord_Setting

open MeasureTheory ProbabilityTheory

namespace ChannelRebate.NoCoord

theorem sec41_integrated_foc (p c s : ℝ) (hc : 0 < c) (hcp : c < p) (hsc : s < c)
    (D : Demand) (V : EffortCost)
    (Qbar0 : ℝ) (hQbar0_pos : 0 < Qbar0) (hQbar0 : Phi D Qbar0 = (p - c) / (p - s))
    (Qbar ebar : ℝ) (hopt : ChannelRebate.Effort.IsOptimalPair (chainProfit p c s D V) Qbar ebar) (hebar : 0 < ebar) :
    Qbar = ebar * Qbar0 ∧
    V.dV ebar = (p - s) * Gam D Qbar0 ∧
    chainProfit p c s D V Qbar ebar = ebar * V.dV ebar - V.V ebar := by sorry

end ChannelRebate.NoCoord
