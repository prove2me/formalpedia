-- Prove2me | Theorems.Thm_BrownSharedSignals_Fluid_lemma_ec4_3
-- name    : BrownSharedSignals.Fluid.lemma_ec4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:53:34.221389+00:00
-- url     : https://prove2.me/theorems/c6726c85-738c-42d0-842c-b873ae8e50a1
-- title:
--   Lemma EC4.3 — Value sensitivity with the printed constant dependence
-- statement:
--   For each fixed positive horizon $T$, there are nonnegative constants $k_t$ depending only on $t,T$ such that, for every shared-resource model, every choice of Section 6 bounds, every feasible dynamic fluid policy and every pair of project states differing in at most $m$ coordinates,
--   $$|V_t^{\pi^F}(s,h)-V_t^{\pi^F}(\widetilde s,h)|\le k_t(r_{\rm upper}-r_{\rm lower})m.$$
--   The two values share the same fixed signal-history and fluid memory. Constants are quantified before project counts, model data, reward and consumption scales, schedules and priority indices. The printed dependence restriction is preserved; no resource-dependent correction is substituted.
--
--   Differences from the source:
--   - encoding: periods 1 through T and finite nonempty state and signal sets → periods 0 through T-1 with terminal T, and finite carriers numbered by Fin (size+1); reason: index renaming represents every finite nonempty carrier and changes no model
--   - encoding: finite-horizon expectations and maxima or minima → finite probability sums and real extrema of the operationally defined feasible value sets; reason: feasible action sets are finite and contain zero, and the finite-horizon LP and fluid feasible objectives have finite attained extrema on their stated domains
--   - encoding: current-signal notation abbreviating the fixed fluid or multiplier history → complete signal history is explicit, and fluid memory is computed from the fixed optimizer schedule; reason: the paper’s policies depend on this memory even when their displayed arguments suppress it
--   - encoding: normalized local action masses, undefined when the local mass is zero → arbitrary probability-distribution completions at zero local mass, with the printed ratio required at positive mass; reason: the source allows zero occupancies and repaired trajectories can reach them; no full-support or optimal-action-completion condition is added
--   - reading: positive nonzero-action consumptions and the bounded resource ratio invoked in Section 6 → uniform scales satisfy 0 < b_lower <= b_upper; reason: this is the standing positive-scale interpretation required by the printed divisions and bounded ratio; no unit-consumption normalization is imposed
--   - encoding: constants depending only on t and T → the existential sequence of constants precedes every model, bound and policy quantifier; reason: this makes the printed uniformity explicit rather than silently allowing instance-dependent constants
-- source:
--   Brown and Zhang (2021), Dynamic Programs with Shared Resources and Signals: Dynamic Fluid Policies and Asymptotic Optimality, DOI https://doi.org/10.1287/opre.2021.2181, supplied July 28, 2021 artifact (published citation basis), Lemma EC4.3, printed EC-15 / PDF 53

import Definitions.Def_BrownSharedSignals_Fluid_GreedyPolicy

open scoped BigOperators
open BrownSharedSignals.Fluid

namespace BrownSharedSignals.Fluid

theorem lemma_ec4_3 (T : ℕ) (hT : 0 < T) :
    ∃ k : ℕ → ℝ, (∀ t ≤ T, 0 ≤ k t) ∧
      ∀ N (M : Model N T) (rlo rhi blo bhi : ℝ), Bounded M rlo rhi blo bhi →
      ∀ (u : Schedule M) (p : LocalPolicy M), DynamicFluidPolicy M u p →
      ∀ (v : Priority M) (t : ℕ), t < T →
      ∀ (h : History M t), h 0 = M.initialSignal →
      ∀ (s s' : State M) (m : ℕ), stateMismatch M s s' ≤ m →
        |policyValue M (repairedPolicy M p v) t h s -
          policyValue M (repairedPolicy M p v) t h s'| ≤ k t * (rhi-rlo) * (m : ℝ) := by sorry

end BrownSharedSignals.Fluid
