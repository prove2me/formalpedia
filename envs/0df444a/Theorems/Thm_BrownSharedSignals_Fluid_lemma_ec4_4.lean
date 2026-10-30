-- Prove2me | Theorems.Thm_BrownSharedSignals_Fluid_lemma_ec4_4
-- name    : BrownSharedSignals.Fluid.lemma_ec4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:53:23.625989+00:00
-- url     : https://prove2.me/theorems/1f43f9ae-eeaf-437c-90d0-5f46a223bb66
-- title:
--   Lemma EC4.4 — Conditional independence of project states
-- statement:
--   For every dynamic fluid policy generated from an optimal schedule, every period and every rooted signal history, the local project states are conditionally independent. Explicitly, the conditional probability of any joint state equals the product of its local marginal probabilities:
--   $$\Pr(S_t=s\mid h_t)=\prod_i\Pr(S_{t,i}=s_i\mid h_t).$$
--   Conditioning uses the fixed-history forward kernel. The policy uses independent local action draws and retains its original fluid schedule.
--
--   Differences from the source:
--   - encoding: periods 1 through T and finite nonempty state and signal sets → periods 0 through T-1 with terminal T, and finite carriers numbered by Fin (size+1); reason: index renaming represents every finite nonempty carrier and changes no model
--   - encoding: finite-horizon expectations and maxima or minima → finite probability sums and real extrema of the operationally defined feasible value sets; reason: feasible action sets are finite and contain zero, and the finite-horizon LP and fluid feasible objectives have finite attained extrema on their stated domains
--   - encoding: current-signal notation abbreviating the fixed fluid or multiplier history → complete signal history is explicit, and fluid memory is computed from the fixed optimizer schedule; reason: the paper’s policies depend on this memory even when their displayed arguments suppress it
--   - encoding: normalized local action masses, undefined when the local mass is zero → arbitrary probability-distribution completions at zero local mass, with the printed ratio required at positive mass; reason: the source allows zero occupancies and repaired trajectories can reach them; no full-support or optimal-action-completion condition is added
--   - encoding: conditioning on every rooted signal history → the forward project kernel along the fixed signal path, also on probability-zero histories; reason: this explicitly chooses a conditional-kernel version without adding a positive-history-probability assumption or removing null histories
-- source:
--   Brown and Zhang (2021), Dynamic Programs with Shared Resources and Signals: Dynamic Fluid Policies and Asymptotic Optimality, DOI https://doi.org/10.1287/opre.2021.2181, supplied July 28, 2021 artifact (published citation basis), Lemma EC4.4, printed EC-15 / PDF 53

import Definitions.Def_BrownSharedSignals_Fluid_GreedyPolicy

open scoped BigOperators
open BrownSharedSignals.Fluid

namespace BrownSharedSignals.Fluid

theorem lemma_ec4_4 {N T : ℕ} (M : Model N T)
    (u : Schedule M) (p : LocalPolicy M) (hp : DynamicFluidPolicy M u p)
    (t : ℕ) (ht : t < T) (h : History M t) (hroot : h 0 = M.initialSignal) :
    ∀ s : State M, conditionalState M (independentPolicy M p) t h s =
      ∏ i, ∑ x : State M,
        if x i = s i then conditionalState M (independentPolicy M p) t h x else 0 := by sorry

end BrownSharedSignals.Fluid
