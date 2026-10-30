-- Prove2me | Theorems.Thm_BrownSharedSignals_Fluid_corollary_6_2
-- name    : BrownSharedSignals.Fluid.corollary_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:54:08.356363+00:00
-- url     : https://prove2.me/theorems/09f6c196-1f4c-4cb6-9758-424a3b6f10cc
-- title:
--   Corollary 6.2 — Asymptotic optimality of feasible dynamic fluid policies
-- statement:
--   Consider any sequence of the paper’s finite shared-resource problems indexed by the positive number of projects $N$, with a fixed positive horizon $T$. Reward bounds and positive nonzero-action consumption bounds are uniform in $N$; all finite state and action sets, signal kernels, initial states and budgets may vary with $N$. For any sequence of optimal dynamic fluid schedules, any distribution-valued zero-occupancy completions, and any sequence of local priority index rankings, if
--   $$\frac{V^*_{1,N}(s_{1,N},z_{1,N})}{\sqrt N}\longrightarrow+\infty,$$
--   then the corresponding feasible greedy dynamic fluid policies satisfy
--   $$\frac{L^{\lambda_N^*}_{1,N}(s_{1,N},z_{1,N})-V^{\pi_N^F}_{1,N}(s_{1,N},z_{1,N})}{V^*_{1,N}(s_{1,N},z_{1,N})}\longrightarrow0.$$
--   The numerator retains the optimal relaxation-minus-policy gap. No identical-project, fixed-menu, budget-scaling or everywhere-positive-value assumption is made. The growth hypothesis implies positivity eventually, which suffices for the ratio limit.
--
--   Differences from the source:
--   - encoding: periods 1 through T and finite nonempty state and signal sets → periods 0 through T-1 with terminal T, and finite carriers numbered by Fin (size+1); reason: index renaming represents every finite nonempty carrier and changes no model
--   - encoding: finite-horizon expectations and maxima or minima → finite probability sums and real extrema of the operationally defined feasible value sets; reason: feasible action sets are finite and contain zero, and the finite-horizon LP and fluid feasible objectives have finite attained extrema on their stated domains
--   - encoding: current-signal notation abbreviating the fixed fluid or multiplier history → complete signal history is explicit, and fluid memory is computed from the fixed optimizer schedule; reason: the paper’s policies depend on this memory even when their displayed arguments suppress it
--   - encoding: normalized local action masses, undefined when the local mass is zero → arbitrary probability-distribution completions at zero local mass, with the printed ratio required at positive mass; reason: the source allows zero occupancies and repaired trajectories can reach them; no full-support or optimal-action-completion condition is added
--   - reading: positive nonzero-action consumptions and the bounded resource ratio invoked in Section 6 → uniform scales satisfy 0 < b_lower <= b_upper; reason: this is the standing positive-scale interpretation required by the printed divisions and bounded ratio; no unit-consumption normalization is imposed
--   - encoding: positive project counts N tending to infinity → the family at natural index n has N=n+1 projects, with sqrt(n+1) in the growth hypothesis; reason: this is a bijective reindexing of positive project counts and introduces no restriction on small-N values
-- source:
--   Brown and Zhang (2021), Dynamic Programs with Shared Resources and Signals: Dynamic Fluid Policies and Asymptotic Optimality, DOI https://doi.org/10.1287/opre.2021.2181, supplied July 28, 2021 artifact (published citation basis), Corollary 6.2, printed 27 / PDF 28

import Definitions.Def_BrownSharedSignals_Fluid_GreedyPolicy

open scoped BigOperators
open BrownSharedSignals.Fluid

namespace BrownSharedSignals.Fluid

theorem corollary_6_2 (T : ℕ) (hT : 0 < T)
    (M : (n : ℕ) → Model (n+1) T)
    (rlo rhi blo bhi : ℝ) (hb : ∀ n, Bounded (M n) rlo rhi blo bhi)
    (u : (n : ℕ) → Schedule (M n)) (p : (n : ℕ) → LocalPolicy (M n))
    (hp : ∀ n, DynamicFluidPolicy (M n) (u n) (p n)) (v : (n : ℕ) → Priority (M n))
    (hgrowth : Filter.Tendsto
      (fun n => optimalValue (M n) 0 (initialHistory (M n)) (M n).initialState /
        Real.sqrt (n+1 : ℕ)) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n =>
      (optimalRelaxation (M n) -
        policyValue (M n) (repairedPolicy (M n) (p n) (v n)) 0 (initialHistory (M n)) (M n).initialState) /
      optimalValue (M n) 0 (initialHistory (M n)) (M n).initialState)
      Filter.atTop (nhds 0) := by sorry

end BrownSharedSignals.Fluid
