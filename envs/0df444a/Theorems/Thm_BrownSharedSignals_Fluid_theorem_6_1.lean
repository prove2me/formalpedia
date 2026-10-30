-- Prove2me | Theorems.Thm_BrownSharedSignals_Fluid_theorem_6_1
-- name    : BrownSharedSignals.Fluid.theorem_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:53:56.101015+00:00
-- url     : https://prove2.me/theorems/d0529c3e-e329-4cc8-8f6f-4f023a8a6c20
-- title:
--   Theorem 6.1 — Performance guarantee with the printed constant dependence
-- statement:
--   For each fixed positive horizon $T$, there exist constants $\gamma_t,\delta_t$ depending only on $t,T$ such that, for every finite shared-resource model with the Section 6 bounds and every feasible dynamic fluid policy,
--   $$V_1^*-V_1^{\pi^F}\le L_1^{\lambda^*}-V_1^{\pi^F}\le(r_{\rm upper}-r_{\rm lower})\sum_{t=1}^T\left(\gamma_t\,\mathbb E[\sqrt{B_t(z_t)}]+\delta_t\right).$$
--   All three values use the specified initial state. The relaxation is optimized over full-history multipliers. The expectation remains outside the square root. The constants are quantified before all model data, reward and resource scales, schedules and rankings, retaining the printed dependence restriction even though the source finding challenges it.
--
--   Differences from the source:
--   - encoding: periods 1 through T and finite nonempty state and signal sets → periods 0 through T-1 with terminal T, and finite carriers numbered by Fin (size+1); reason: index renaming represents every finite nonempty carrier and changes no model
--   - encoding: finite-horizon expectations and maxima or minima → finite probability sums and real extrema of the operationally defined feasible value sets; reason: feasible action sets are finite and contain zero, and the finite-horizon LP and fluid feasible objectives have finite attained extrema on their stated domains
--   - encoding: current-signal notation abbreviating the fixed fluid or multiplier history → complete signal history is explicit, and fluid memory is computed from the fixed optimizer schedule; reason: the paper’s policies depend on this memory even when their displayed arguments suppress it
--   - encoding: normalized local action masses, undefined when the local mass is zero → arbitrary probability-distribution completions at zero local mass, with the printed ratio required at positive mass; reason: the source allows zero occupancies and repaired trajectories can reach them; no full-support or optimal-action-completion condition is added
--   - reading: positive nonzero-action consumptions and the bounded resource ratio invoked in Section 6 → uniform scales satisfy 0 < b_lower <= b_upper; reason: this is the standing positive-scale interpretation required by the printed divisions and bounded ratio; no unit-consumption normalization is imposed
--   - encoding: constants depending only on t and T → both existential constant sequences precede every model, bound and policy quantifier; reason: this preserves the printed uniformity despite the separate counterexample finding
--   - reading: the main-text display leaves delta_t outside the displayed summation → each summand includes gamma_t E[sqrt(B_t)] plus delta_t; reason: the final display on EC-18 explicitly supplies this grouping and avoids a free time index
-- source:
--   Brown and Zhang (2021), Dynamic Programs with Shared Resources and Signals: Dynamic Fluid Policies and Asymptotic Optimality, DOI https://doi.org/10.1287/opre.2021.2181, supplied July 28, 2021 artifact (published citation basis), Theorem 6.1, printed 25 / PDF 26

import Definitions.Def_BrownSharedSignals_Fluid_GreedyPolicy

open scoped BigOperators
open BrownSharedSignals.Fluid

namespace BrownSharedSignals.Fluid

theorem theorem_6_1 (T : ℕ) (hT : 0 < T) :
    ∃ gamma delta : ℕ → ℝ,
      ∀ N (M : Model N T) (rlo rhi blo bhi : ℝ), Bounded M rlo rhi blo bhi →
      ∀ (u : Schedule M) (p : LocalPolicy M), DynamicFluidPolicy M u p →
      ∀ v : Priority M,
        optimalValue M 0 (initialHistory M) M.initialState -
            policyValue M (repairedPolicy M p v) 0 (initialHistory M) M.initialState ≤
          optimalRelaxation M - policyValue M (repairedPolicy M p v) 0 (initialHistory M) M.initialState ∧
        optimalRelaxation M - policyValue M (repairedPolicy M p v) 0 (initialHistory M) M.initialState ≤
          (rhi-rlo) * ∑ t : Fin T,
            (gamma t.val * (∑ h : History M t.val,
              historyProb M t.val h * Real.sqrt (M.budget t.val (current M h))) + delta t.val) := by sorry

end BrownSharedSignals.Fluid
