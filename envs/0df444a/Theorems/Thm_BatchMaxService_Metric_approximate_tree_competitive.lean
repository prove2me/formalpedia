-- Prove2me | Theorems.Thm_BatchMaxService_Metric_approximate_tree_competitive
-- name    : BatchMaxService.Metric.approximate_tree_competitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:39:10.186733+00:00
-- url     : https://prove2.me/theorems/9f6aec10-ebef-4630-9239-8758945850a5
-- title:
--   Proposition 5.6 — approximate connecting trees, ratio and conditional runtime
-- statement:
--   Fix any real $\rho\ge1$. On a known finite metric, let a deterministic tree procedure return a tree $F(A)$ containing every nonempty terminal set $A$, possibly using extra metric sites, with weight $\Gamma(A)\le\rho\operatorname{ST}_X(A)$. Use the phase controller of Section 5.3: free anchor arrivals, oldest-request clock, retained prefix maximum $E$, threshold $E/\rho$, canonical actual-request endpoint and an open traversal of the current tree. It is deterministic and causal, terminates feasibly on every finite visible elective input, and satisfies
--
--   $$\operatorname{ALG}_{\rho,F}(I)\le4(2\rho+1)\operatorname{OPT}(I).$$
--
--   If $\rho$ is rational and the tree procedure has a uniform polynomial work bound, the phase algorithm also has a uniform polynomial work bound. The rationality condition is confined to this runtime implication and does not narrow the competitive guarantee.
--
--   This is the general reduction instantiated by Algorithm 4 after establishing the factor-two terminal-MST bound.
--
--   Differences from the source:
--   - encoding: a known nonempty finite metric and finitely many distinct request labels → sites Fin n with an arbitrary MetricSpace, an initial site, and a finite subset of natural labels; reason: every such metric and finite identity set can be enumerated, preserving all real distances, arrivals and repeated location/time pairs
--   - encoding: finite nonnegative tree minima and the elective optimum → finite tree minima and the unrestricted schedule infimum in ENNReal, with real event costs embedded by ofReal; reason: finite tree families have attained minima and finite feasible schedules have nonnegative finite cost; +infinity is the empty-infimum sentinel, never a real default zero
--   - reading: polynomial time with no machine model stated in Theorem 5.8 or Proposition 5.6 → unit-cost exact real arithmetic, comparisons, finite data scans, tree computation and traversal construction, measured by loop-derived work counters and one uniform polynomial; reason: this event-driven arithmetic/comparison reading keeps all real inputs and does not count elapsed waiting as CPU time; no binary bit-cost theorem is claimed
--   - encoding: event-driven phase execution and deterministic procedures → an explicit costed controller, complete-epoch environment driver, visible finite evaluation budget and prefix-consistency conclusion; reason: one step consumes an epoch or clears a nonempty phase; successful termination and all cost bounds are conclusions, while the tree approximation remains only the source hypothesis of this proposition
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), Proposition 5.6 with its Section 5.3 preamble, (5.13)–(5.16), printed pp. 17–18 / PDF pp. 18–19

import Mathlib
import Definitions.Def_BatchMaxService_Metric_PhaseAlgorithm

namespace BatchMaxService.Metric

/-- Proposition 5.6 with its entire Section 5.3 preamble, printed pp. 17–18 / PDF 18–19.
    The ratio is for every real rho >= 1; only the conditional runtime clause asks for rational rho. -/
theorem approximate_tree_competitive (ρ : ℝ) (hρ : 1 ≤ ρ) :
    (∀ n (m : MetricSpace (Fin n)) (f : TreeProcedure n),
      letI : MetricSpace (Fin n) := m
      TreeApproximation ρ f →
      DeterministicOnline (phaseRun ρ f) ∧
      (∀ I : RequestInput n,
        let r := phaseRun ρ f I
        r.finished = true ∧ Feasible I r.state.log ∧
        ENNReal.ofReal (cost I r.state.log) ≤ ENNReal.ofReal (4 * (2 * ρ + 1)) * OPT I)) ∧
    ((∃ r : ℚ, (r : ℝ) = ρ) →
      ∀ f : ∀ n, MetricSpace (Fin n) → TreeProcedure n,
        (∀ n (m : MetricSpace (Fin n)),
          letI : MetricSpace (Fin n) := m
          TreeApproximation ρ (f n m)) →
        PolynomialTreeWork f → PolynomialPhaseWork ρ f) := by sorry

end BatchMaxService.Metric
