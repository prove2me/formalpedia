-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_Supplement_theorem_5_1
-- name    : BipartiteVRM.Competitive.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:34:11.0572+00:00
-- url     : https://prove2.me/theorems/091b7416-e743-491a-9f88-6cafa3e31f40
-- title:
--   Theorem 5.1 — non-bipartite VRM is $\frac{2\gamma}{\gamma-1}[1+2(\gamma+1)(1+\ln m)]$-competitive for MPMD
-- statement:
--   For every fixed real $\gamma>1$ and every fixed tie rule, non-bipartite VRM is a deterministic online algorithm for the minimum-cost perfect matching with delays problem (MPMD) in any metric space. On every input with $|R|=2m$ requests it halts with a feasible perfect matching of $R$, decisions are irrevocable, the offline optimum $\mathrm{OPT}$ of the actual timed objective is attained, and for $m\ge1$
--
--   $$\mathrm{ALG}\le\frac{2\gamma}{\gamma-1}\bigl[1+2(\gamma+1)(1+\ln m)\bigr]\mathrm{OPT}.$$
--
--   In particular
--
--   $$\gamma=2\quad\Longrightarrow\quad\mathrm{ALG}\le(28+24\ln m)\,\mathrm{OPT}.$$
--
--   For the empty input the output is empty and $\mathrm{ALG}=\mathrm{OPT}=0$. Across different metric spaces and different final input sizes, inputs with identical observations through $t$ give identical output through $t$: the algorithm needs neither the metric space nor $m$ in advance.
--
--   This is the paper's extension of its main result to general (non-bipartite) matching with delays, a companion theorem of the mission's goal (Theorem 1.1), not a step of its proof. Arbitrary real times, simultaneous arrivals, coincident locations, $m=1$ and $\mathrm{OPT}=0$ are all included.
--
--   Differences from the source:
--   - encoding: a finite request set R with |R| = 2m in any metric space, locations and arrival times a_v ≥ 0 that may coincide → the published MatchingDelays.Linear.Instance n X (labels 0..n−1 in nondecreasing arrival order, any MetricSpace X) with Even n, m = n/2; reason: every finite input can be relabeled in arrival order (simultaneous arrivals in any order); labels give the algorithm no future data, and repeated locations and arrival times are allowed
--   - encoding: an arbitrary but fixed rule for ties among simultaneous events and among the choices of N_uv and v in Steps 1 and 2 → every TieRule, a View-and-history selector over the nonempty finite option sets; reason: the rule sees only received data and its own history; every statement quantifies over all such rules
--   - encoding: OPT, the minimum of the actual distance-plus-both-delays objective over timed perfect matchings → offlineOpt of the published instance (the real infimum of feasible schedule costs), with OfflineAttained as a conclusion; reason: the conclusion that the infimum is attained by a feasible schedule rules out the empty or unbounded sInf default
--   - encoding: a deterministic online algorithm that does not need to know the metric space or m in advance → ExecutionCorrect and Causal, comparing inputs in different metric spaces and of different final sizes; reason: these express halting, feasible irrevocable perfect output and dependence only on observed data
--   - generalization: the displayed bound on every input, where ln m is defined (m ≥ 1) → the identical bound for n = 2m > 0, plus a separate empty-input branch with empty output and ALG = OPT = 0; reason: this adds only the boundary case where ln m is undefined and keeps every nonempty input and the exact coefficient
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 13, Theorem 5.1; algorithm §§5.1–5.2, pp. 14–15; proof §§5.3–5.5, pp. 16–19

import Definitions.Def_BipartiteVRM_Competitive_Supplement_Specifications

set_option autoImplicit false

universe uNBgoal

namespace BipartiteVRM.Competitive.Supplement

open MatchingDelays.Linear (Instance offlineOpt)

/-- Full Theorem 5.1, p. 13. Causality compares different metric spaces and different
input sizes; completion, feasibility and attainment of OPT are conclusions. The bound is
stated for m = n/2 ≥ 1, with the empty input handled separately. -/
theorem theorem_5_1 (γ : ℝ) (hγ : 1 < γ) (tie : TieRule) :
    Causal.{uNBgoal, uNBgoal} γ tie ∧
    ∀ {n : ℕ} {X : Type uNBgoal} [MetricSpace X] (I : Instance n X), Even n →
      ExecutionCorrect I γ tie ∧ OfflineAttained I ∧
      (n = 0 → output I γ tie = [] ∧ ALG I γ tie = 0 ∧ offlineOpt I = 0) ∧
      (0 < n → ALG I γ tie ≤
        2 * γ / (γ - 1) *
          (1 + 2 * (γ + 1) * (1 + Real.log ((n : ℝ) / 2))) * offlineOpt I) ∧
      (γ = 2 → 0 < n → ALG I γ tie ≤
        (28 + 24 * Real.log ((n : ℝ) / 2)) * offlineOpt I) := by sorry

end BipartiteVRM.Competitive.Supplement
