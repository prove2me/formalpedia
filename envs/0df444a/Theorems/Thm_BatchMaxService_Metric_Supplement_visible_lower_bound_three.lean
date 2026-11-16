-- Prove2me | Theorems.Thm_BatchMaxService_Metric_Supplement_visible_lower_bound_three
-- name    : BatchMaxService.Metric.Supplement.visible_lower_bound_three
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:10:58.845702+00:00
-- url     : https://prove2.me/theorems/e87c1017-0c64-40d7-a497-aa3b07de04ea
-- title:
--   Theorem 7.6 — Visible deterministic ratio is at least 3, even with additive constants
-- statement:
--   Fix any $D>0$, the two-site line $X=\{0,D\}$ and start $0$, and either service rule $r$. For every feasible deterministic causal visible policy $A$, every real $\rho<3$ and every fixed $B\ge0$, there is a finite input $I$, fixed once $A$ is chosen, for which
--
--   $$\operatorname{ALG}_A(I)>\rho\operatorname{OPT}_r(I)+B.$$
--
--   In particular $B=0$ gives the strict ratio violation from the printed statement. The input starts at $0$ and its offline value is finite. Policies may wait, revisit, reposition purely and use several separately billed same-time events; they need not be lazy or efficient. The quantifier on $D$ precedes the policy and input, so no metric rescaling is used to defeat $B$.
--
--   Differences from the source:
--   - encoding: fixed line {0,D} and every deterministic visible online algorithm → arbitrary metric instance on Fin 2 with off-diagonal distance D, and arbitrary-state causal feedback policies feasible on every finite input from index zero; reason: the interaction represents unrestricted finite schedules, timers and pure moves; no phase, laziness or efficiency hypothesis is used
--   - encoding: ratio lower bound surviving any fixed additive constant → every real rho below three and every nonnegative B have a strict finite-input witness with finite offline value; reason: this expresses the printed additive-constant clause explicitly; converting the nonnegative extended offline value to a real is guarded by finiteness in the conclusion
-- source:
--   Lu, Ren, Liu, Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), canonical source.pdf sha256 652f1a7bbf08e31c9fd0855a098b7b7439589f55b2df3115db7c34adc0eaec34, Theorem 7.6, printed p. 28 / PDF p. 29

import Mathlib
import Definitions.Def_BatchMaxService_Metric_Supplement_LowerBounds

namespace BatchMaxService.Metric.Supplement

theorem visible_lower_bound_three (D : ℝ) (hD : 0 < D)
    [MetricSpace (Fin 2)]
    (hm : ∀ u v : Fin 2, dist u v = if u = v then 0 else D) :
    ∀ (r : Rule) (S : Type) (p : Policy 2 S),
      ValidPolicy .visible r 0 p →
      ∀ ρ : ℝ, ρ < 3 → ∀ B : ℝ, 0 ≤ B →
        ∃ I : RequestInput 2, I.start = 0 ∧ ruleOPT r I ≠ ⊤ ∧
          ρ * (ruleOPT r I).toReal + B < cost I (execution .visible r p I).log := by sorry

end BatchMaxService.Metric.Supplement
