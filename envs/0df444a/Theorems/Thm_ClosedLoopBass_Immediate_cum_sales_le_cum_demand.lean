-- Prove2me | Theorems.Thm_ClosedLoopBass_Immediate_cum_sales_le_cum_demand
-- name    : ClosedLoopBass.Immediate.cum_sales_le_cum_demand
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:24:24.016859+00:00
-- url     : https://prove2.me/theorems/a72503be-058b-408c-9147-969507059218
-- title:
--   §4.1, p. 7 — for a feasible partial-fulfillment plan, cumulative sales never exceed cumulative diffusion demand: Ŝₜ ≤ D̂ₜ
-- statement:
--   Consider the closed-loop sales-planning model under its standing assumptions, and let $(n,r)$ be a feasible class-(b) plan. Some demand is first rejected in period $t_p<T$: sales before $t_p$ equal the immediate-fulfillment Bass demand, and sales in period $t_p$ fall below that demand. Let $S_t$ be its cumulative sales and $D_t$ its cumulative diffusion demand. Then
--
--   $$
--   S_t\le D_t\qquad\text{for every period }1\le t\le T+1.
--   $$
--
--   In words: a producer can never have sold more units in total than the diffusion process has generated in total. Unmet demand is partly lost and partly backlogged at rate $\alpha\le1$, and only backlogged demand can be served later.
--
--   This inequality compares the word-of-mouth term $qS_t/m$ of a partial-fulfillment plan with its own cumulative demand.
--
--   **Formalization Note** The class-(b) condition uses the page's description of the first rejection period $t_p$. The range $t\le T+1$ covers every period whose cumulative quantities depend only on the plan's sales in periods $1,\dots,T$.
-- source:
--   Nadar, Kaya and Güler, New-Product Diffusion in Closed-Loop Supply Chains, MSOM (Articles in Advance, 2020), doi:10.1287/msom.2019.0864, p. 7, §4.1 ("Note that Ŝt ≤ D̂t, ∀t.")

import Mathlib
import Definitions.Def_ClosedLoopBass_Immediate_Model

namespace ClosedLoopBass.Immediate

/-- §4.1, p. 7 ("Note that Ŝ_t ≤ D̂_t, ∀t"): for a feasible class-(b) sales plan,
whose first rejected demand is in period `tp < T`, cumulative sales never exceed
cumulative diffusion demand in every period `1 ≤ t ≤ T + 1`. -/
theorem cum_sales_le_cum_demand (P : Params) (hP : Standing P) (n r : ℕ → ℝ)
    (hfeas : Feasible P n r)
    (hclassb : ∃ tp : ℕ, 1 ≤ tp ∧ tp < P.T ∧
      (∀ t ∈ Finset.Ico 1 tp, sales n r t = dB P t) ∧
      sales n r tp < dB P tp) :
    ∀ t : ℕ, 1 ≤ t → t ≤ P.T + 1 → S n r t ≤ D P n r t := by sorry

end ClosedLoopBass.Immediate
