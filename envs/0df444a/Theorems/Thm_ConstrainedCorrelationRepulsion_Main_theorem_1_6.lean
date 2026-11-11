-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_theorem_1_6
-- name    : ConstrainedCorrelationRepulsion.Main.theorem_1_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:31:56.724786+00:00
-- url     : https://prove2.me/theorems/af393e3b-8ad3-4405-964e-cf105b6d6bf5
-- title:
--   Theorem 1.6 — randomized and deterministic radius-2/3 Repulsion
-- statement:
--   Let $L(x)$ denote the constrained metric-LP objective. For every feasible pseudometric solution $x$ of that LP, uniform proper-center radius-$2/3$ Repulsion returns a feasible partition in polynomial time. Its deterministic minimum-excess version does so as well. Their guarantees are
--
--   $$
--   \mathbb E[\mathrm{cost}(P_{\rm rand})]\le3L(x),\qquad \mathrm{cost}(P_{\rm det})\le3L(x).
--   $$
--
--   The programs realize the two explicitly defined recursion laws, preserving must-links even when distinct vertices have distance zero. Both sides of every proper split are processed.
--
--   Differences from the source:
--   - encoding: finite vertex set and partitions → Fin n with vertex-label partitions and unordered-pair cost; reason: every finite partition admits these labels, including n = 0; each pair is counted once
--   - reading: polynomial-time algorithm without a named machine → one finite charged register program, with fair random bits in rational bit-cost executions and exact-real arithmetic/Bernoulli(p) access for real inputs; reason: this makes the implicit computational model explicit without admitting optimization instructions or semantic callbacks
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Theorem 1.6, printed p.41 (PDF p.42), proof printed pp.41–42 (PDF pp.42–43)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Encoding

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

theorem theorem_1_6 :
  ∃ randomCode deterministicCode : Program, Deterministic deterministicCode ∧
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧ ∀ n (I : Instance n) (x : Fin n → Fin n → ℝ),
      MetricFeasible I x →
      let B := polynomialBound C d n
      let oracle := metricOracle I x
      let randomLaw := outputLaw randomCode oracle (initialState n) B false
      let deterministicLaw := outputLaw deterministicCode oracle (initialState n) B false
      BoundedRun false randomCode oracle (initialState n) B ∧
      BoundedRun false deterministicCode oracle (initialState n) B ∧
      randomLaw = (randomRepulsionBlocks I x n Finset.univ).map partitionOfBlocks ∧
      deterministicLaw = PMF.pure (partitionOfBlocks
        (repulsionBlocks I x (2/3) (potentialTwoThirds I x) n Finset.univ)) ∧
      (∀ P ∈ randomLaw.support, Feasible I P) ∧
      expectedCost I randomLaw ≤ 3 * lpObjective (signedCosts I) x ∧
      (∀ P ∈ deterministicLaw.support,
        Feasible I P ∧ (cost I P : ℝ) ≤ 3 * lpObjective (signedCosts I) x) := by sorry

end ConstrainedCorrelationRepulsion.Main
