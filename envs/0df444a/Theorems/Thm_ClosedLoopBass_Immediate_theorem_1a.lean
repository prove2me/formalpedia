-- Prove2me | Theorems.Thm_ClosedLoopBass_Immediate_theorem_1a
-- name    : ClosedLoopBass.Immediate.theorem_1a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:10.566987+00:00
-- url     : https://prove2.me/theorems/ac10b7d2-43a3-42a5-9ef1-6d0bea8d028f
-- title:
--   Theorem 1(a), first clause, p. 8 — if ẽₜ ≤ γ₂d̃ₜ in every period, the immediate-fulfillment plan is feasible and maximizes total profit
-- statement:
--   Consider the closed-loop sales-planning model of Nadar, Kaya and Güler under its standing assumptions:
--
--   - $m>0$, $p,q>0$ with $p+q\le1$;
--   - $\alpha,\gamma_2\in[0,1]$;
--   - $\beta_i\ge0$ with $\sum_i\beta_i\le1$;
--   - $p_n>c_n$, $p_r>c_r$ and $p_r-c_r>p_n-c_n$.
--
--   Let $\widetilde d_t$ be the demand of the original Bass process. Let $\widetilde e_t$ be the accumulated return volume and $(\widetilde n,\widetilde r)$ the sales of the **immediate-fulfillment plan**, which meets all demand in each period and meets remanufactured-item demand from the available returns to the fullest extent possible: $\widetilde r_t=\min\{\widetilde e_t,\gamma_2\widetilde d_t\}$ and $\widetilde n_t=\widetilde d_t-\widetilde r_t$.
--
--   Suppose that, under this plan, remanufactured-item demand is no less than the accumulated return volume in each period:
--
--   $$
--   \widetilde e_t\le\gamma_2\,\widetilde d_t\qquad(t=1,\dots,T).
--   $$
--
--   Then the immediate-fulfillment plan is optimal. It is feasible, and for every feasible sales plan $(n,r)$ (constraints (2)–(6) with diffusion (1))
--
--   $$
--   \sum_{t=1}^{T}\bigl[(p_n-c_n)n_t+(p_r-c_r)r_t\bigr]\ \le\ \sum_{t=1}^{T}\bigl[(p_n-c_n)\widetilde n_t+(p_r-c_r)\widetilde r_t\bigr].
--   $$
--
--   This is the first sentence of Theorem 1(a). When returns are always scarce relative to remanufactured-item demand, delaying customers cannot let the producer serve more of them with higher-margin remanufactured units. Rejecting demand then only slows diffusion. The paper's second sentence of (a), and parts (b)–(c), rely on thresholds given in an online appendix and are not part of this statement.
--
--   **Formalization Note**
--
--   1. "Remanufactured-item demand" under the immediate plan is $\gamma_2\widetilde d_t+\widetilde b_{2t}=\gamma_2\widetilde d_t$, since every backlog vanishes under that plan. "Accumulated return volume" is $\widetilde e_t$ of (6), as in the paper's Figure 2.
--   2. The feasible set is exactly (2), (3) and (5) with $d,b,e$ given by (1), (4) and (6). $n_t\ge0$ is not imposed, as on the page.
--   3. The sign conditions listed above are implicit in the page and stated explicitly.
-- source:
--   Nadar, Kaya and Güler, New-Product Diffusion in Closed-Loop Supply Chains, MSOM (Articles in Advance, 2020), doi:10.1287/msom.2019.0864, p. 8, Theorem 1(a), first sentence

import Mathlib
import Definitions.Def_ClosedLoopBass_Immediate_Model

namespace ClosedLoopBass.Immediate

/-- Theorem 1(a), first clause, p. 8: if, under the immediate-fulfillment plan, the
remanufactured-item demand `γ2 d̃_t` is no less than the accumulated return volume `ẽ_t` in each
period `t = 1, …, T`, then the immediate-fulfillment plan `(ñ, r̃)` is feasible and its total
profit is at least that of every feasible sales plan. -/
theorem theorem_1a (P : Params) (hP : Standing P)
    (hcond : ∀ t ∈ Finset.Icc 1 P.T, eIF P t ≤ P.gamma2 * dB P t) :
    Feasible P (nIF P) (rIF P) ∧
    ∀ n r : ℕ → ℝ, Feasible P n r → profit P n r ≤ profit P (nIF P) (rIF P) := by sorry

end ClosedLoopBass.Immediate
