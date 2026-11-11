-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_lemma_6_4
-- name    : ConstrainedCorrelationRepulsion.Main.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:31:52.756698+00:00
-- url     : https://prove2.me/theorems/abe2899a-dfe3-4a92-b449-115b5770a219
-- title:
--   Lemma 6.4 — rational truncation and feasible unitwise completion
-- statement:
--   For every rational $0<\tau<n^2$, run independent fixed-law rounds for exactly
--
--   $$
--   T=n\left\lceil\log_2\left(n^2/\tau\right)\right\rceil.
--   $$
--
--   Put each unprocessed unit into its own cluster. Every supported output is feasible, and its expected residual cost is at most the final bound in (41) plus $\tau$. Explicitly, the cost bound is $2L-L_-+2Y/r+3\sqrt{2YP_+/r}+\tau$, where $L=L_++L_-$ is the residual LP objective split by sign, $Y$ is cross-unit co-clustering mass, $P_+$ is the positive cross-unit pair count, and $r$ is the even LP level. The factor $n$ is outside the ceiling. The law and LP solution are held fixed across all rounds.
--
--   Differences from the source:
--   - encoding: finite vertex set and partitions → Fin n with vertex-label partitions and unordered-pair cost; reason: every finite partition admits these labels, including n = 0; each pair is counted once
--   - generalization: units obtained by the preclustering procedure → any unit partition satisfying the stated residual structural conditions; reason: these conclusions use normalized labels, hard cross-products and local LP constraints; atom optimality and the free-degree budget are not used
--   - encoding: real expectations of conditional inclusion values → extended nonnegative sums of conditional inclusion values; reason: reachable inclusion values lie in [0,1] and the sampler has finite support, so these equalities are equivalent to the ordinary real expectations
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Lemma 6.4, equation (42), printed p.33 (PDF p.34)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Rounds

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

theorem lemma_6_4 {n : ℕ} (I : Instance n) (U : Units n) (r : ℕ)
    (y : LocalTable n) (hn : 0 < n) (hr : 6 ≤ r) (heven : Even r)
    (hres : ResidualUnits I U) (hy : BoundedOptimal I U r y) (hq : RationalTable y)
    (tau : ℚ) (ht : 0 < tau) (htn : (tau : ℝ) < (n : ℝ)^2) :
  (∀ stream, (∀ t, stream t ∈ (candidateLaw I U y r).support) →
    Feasible I (finitePartition I U (tableDistance U y) stream (roundCount n tau))) ∧
  0 ≤ roundsBound I U y r + (tau : ℝ) ∧
  finiteExpectedCost I U y r (roundCount n tau) ≤ ENNReal.ofReal (roundsBound I U y r + (tau : ℝ)) := by sorry

end ConstrainedCorrelationRepulsion.Main
