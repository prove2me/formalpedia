-- Prove2me | Theorems.Thm_BrownSharedSignals_Fluid_lemma_ec4_5
-- name    : BrownSharedSignals.Fluid.lemma_ec4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T01:53:04.291384+00:00
-- url     : https://prove2.me/theorems/ddf65102-ff99-4d4d-b665-2e2a895b91bb
-- title:
--   Lemma EC4.5 — Expected proposal-repair mismatch
-- statement:
--   For every dynamic fluid policy and every local priority index repair, under the uniform signed reward and positive consumption bounds of Section 6, at each period and rooted history,
--   $$\mathbb E\!\left[\sum_i\mathbf 1\{a_{t,i}^{\pi^F}\ne a_{t,i}^{\rho^*}\}\mid h_t\right]\le 1+\frac{\sqrt{b_{\rm upper}B_t(z_t)}}{b_{\rm lower}}.$$
--   Both actions are evaluated at the same state drawn from the dynamic fluid policy and use the same proposal draw. The conditional law is the fixed-history forward kernel, including null histories.
--
--   Differences from the source:
--   - encoding: periods 1 through T and finite nonempty state and signal sets → periods 0 through T-1 with terminal T, and finite carriers numbered by Fin (size+1); reason: index renaming represents every finite nonempty carrier and changes no model
--   - encoding: finite-horizon expectations and maxima or minima → finite probability sums and real extrema of the operationally defined feasible value sets; reason: feasible action sets are finite and contain zero, and the finite-horizon LP and fluid feasible objectives have finite attained extrema on their stated domains
--   - encoding: current-signal notation abbreviating the fixed fluid or multiplier history → complete signal history is explicit, and fluid memory is computed from the fixed optimizer schedule; reason: the paper’s policies depend on this memory even when their displayed arguments suppress it
--   - encoding: normalized local action masses, undefined when the local mass is zero → arbitrary probability-distribution completions at zero local mass, with the printed ratio required at positive mass; reason: the source allows zero occupancies and repaired trajectories can reach them; no full-support or optimal-action-completion condition is added
--   - encoding: conditioning on every rooted signal history → the forward project kernel along the fixed signal path, also on probability-zero histories; reason: this explicitly chooses a conditional-kernel version without adding a positive-history-probability assumption or removing null histories
--   - reading: positive nonzero-action consumptions and the bounded resource ratio invoked in Section 6 → uniform scales satisfy 0 < b_lower <= b_upper; reason: this is the standing positive-scale interpretation required by the printed divisions and bounded ratio; no unit-consumption normalization is imposed
-- source:
--   Brown and Zhang (2021), Dynamic Programs with Shared Resources and Signals: Dynamic Fluid Policies and Asymptotic Optimality, DOI https://doi.org/10.1287/opre.2021.2181, supplied July 28, 2021 artifact (published citation basis), Lemma EC4.5, printed EC-16 / PDF 54

import Definitions.Def_BrownSharedSignals_Fluid_GreedyPolicy

open scoped BigOperators
open BrownSharedSignals.Fluid

namespace BrownSharedSignals.Fluid

theorem lemma_ec4_5 {N T : ℕ} (M : Model N T)
    (rlo rhi blo bhi : ℝ) (hb : Bounded M rlo rhi blo bhi)
    (u : Schedule M) (p : LocalPolicy M) (hp : DynamicFluidPolicy M u p) (v : Priority M)
    (t : ℕ) (ht : t < T) (h : History M t) (hroot : h 0 = M.initialSignal) :
    conditionalActionExpectation M (independentPolicy M p) t h
      (fun s a => mismatch
        (repair M v t s (current M h) (actionVector M a)) (actionVector M a)) ≤
      1 + Real.sqrt (bhi * M.budget t (current M h)) / blo := by sorry

end BrownSharedSignals.Fluid
