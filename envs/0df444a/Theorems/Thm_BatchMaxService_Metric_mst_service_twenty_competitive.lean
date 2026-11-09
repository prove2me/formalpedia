-- Prove2me | Theorems.Thm_BatchMaxService_Metric_mst_service_twenty_competitive
-- name    : BatchMaxService.Metric.mst_service_twenty_competitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:36:53.493399+00:00
-- url     : https://prove2.me/theorems/da6d854b-6024-4ec4-832e-325c03d7439e
-- title:
--   Theorem 5.8 — Algorithm 4 is deterministic, polynomial-time and 20-competitive
-- statement:
--   On every known finite metric with an initial site, real nonnegative arrival times, visible request locations and elective service, Algorithm 4 is a deterministic causal online algorithm. Its concrete Prim-based retained-maximum execution terminates with all requests served exactly once, and
--
--   $$\operatorname{ALG}_4(I)\le20\operatorname{OPT}_{\mathrm{elective}}(I).$$
--
--   There is no additive constant. Uniform natural constants $C>0$ and $d$ exist, independent of the site count $N$, metric weights, request labels, arrival values and waiting gaps, such that its charged computational work satisfies
--
--   $$W_4(I)\le C(|Q|+1)^d(N+1)^d.$$
--
--   The empty input and one-site metrics are included. Empty input has algorithm cost and optimum zero. A separate unrestricted one-batch offline candidate is feasible and witnesses finiteness of OPT. The guarantee concerns the actual schedule produced by the defined algorithm; no tree, normalization, certificate or competitive bound is assumed.
--
--   **Formalization Note** Prefix consistency explicitly expresses nonanticipation, including full-epoch-before-service ordering at timer ties. The finite driver budget must be proved sufficient. The runtime bound concerns arithmetic/comparison work, not elapsed time or a separate binary bit-complexity claim.
--
--   Differences from the source:
--   - encoding: a known nonempty finite metric and finitely many distinct request labels → sites Fin n with an arbitrary MetricSpace, an initial site, and a finite subset of natural labels; reason: every such metric and finite identity set can be enumerated, preserving all real distances, arrivals and repeated location/time pairs
--   - encoding: finite nonnegative tree minima and the elective optimum → finite tree minima and the unrestricted schedule infimum in ENNReal, with real event costs embedded by ofReal; reason: finite tree families have attained minima and finite feasible schedules have nonnegative finite cost; +infinity is the empty-infimum sentinel, never a real default zero
--   - reading: polynomial time with no machine model stated in Theorem 5.8 or Proposition 5.6 → unit-cost exact real arithmetic, comparisons, finite data scans, tree computation and traversal construction, measured by loop-derived work counters and one uniform polynomial; reason: this event-driven arithmetic/comparison reading keeps all real inputs and does not count elapsed waiting as CPU time; no binary bit-cost theorem is claimed
--   - encoding: a canonical terminal MST and a canonical actual-request endpoint → explicit lexicographic Prim scans and the least phase identity, with a rooted current-tree open depth-first traversal; reason: these fix the source-authorized tie orders without using future information or any minimizer oracle
--   - encoding: finite feasible service on every input, including empty and one-site cases → explicit successful completion, empty pending and undelivered sets, a feasible unrestricted offline witness, finite OPT and zero cost on empty input; reason: these spell out well-posedness and the boundary cases already implied by the source model, without additional hypotheses
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), Theorem 5.8, printed p. 18 / PDF p. 19; Algorithm 4, printed p. 19 / PDF p. 20

import Mathlib
import Definitions.Def_BatchMaxService_Metric_PhaseAlgorithm

namespace BatchMaxService.Metric

/-- Theorem 5.8, printed p. 18 / PDF 19; Algorithm 4, printed p. 19 / PDF 20.
    No certificate, MST optimality, phase bound or normalization is a premise.
    The work coefficient and degree are uniform over sites, real metrics and arrivals. -/
theorem mst_service_twenty_competitive :
    (∀ n (m : MetricSpace (Fin n)),
      letI : MetricSpace (Fin n) := m
      DeterministicOnline (algorithm4 (n := n))) ∧
    (∃ C d : ℕ, 0 < C ∧ ∀ n (m : MetricSpace (Fin n)) (I : RequestInput n),
      letI : MetricSpace (Fin n) := m
      (algorithm4 I).state.work ≤ C * (I.ids.card + 1)^d * (n + 1)^d) ∧
    (∀ n (m : MetricSpace (Fin n)) (I : RequestInput n),
      letI : MetricSpace (Fin n) := m
      let r := algorithm4 I
      r.finished = true ∧ r.undelivered = [] ∧ r.state.pending = ∅ ∧
      Feasible I r.state.log ∧ Feasible I (oneBatchSchedule I) ∧ OPT I < ⊤ ∧
      ENNReal.ofReal (cost I r.state.log) ≤ 20 * OPT I ∧
      (I.ids = ∅ → cost I r.state.log = 0 ∧ OPT I = 0)) := by sorry

end BatchMaxService.Metric
