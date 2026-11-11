-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_theorem_2_2
-- name    : ConstrainedCorrelationRepulsion.Main.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:27:11.927017+00:00
-- url     : https://prove2.me/theorems/f7713a5f-8842-45b6-ba03-362ae74ca1e8
-- title:
--   Theorem 2.2 — removing must-links without constant-factor loss
-- statement:
--   For constants $\alpha\ge1$ and $\delta>0$, a polynomial-time expected $\alpha$-approximation that always satisfies cannot-links yields a randomized polynomial-time algorithm for general feasible constrained instances with
--
--   $$
--   \mathbb E[\mathrm{cost}(P)]\le(\alpha+\delta)\mathrm{OPT}(I).
--   $$
--
--   Every supported output satisfies both kinds of hard constraint. A polynomial-time algorithm is a single finite program with uniform polynomial bounds over vertex count and input instance.
--
--   Differences from the source:
--   - encoding: finite vertex set and partitions → Fin n with vertex-label partitions and unordered-pair cost; reason: every finite partition admits these labels, including n = 0; each pair is counted once
--   - reading: polynomial-time algorithm without a named machine → one finite charged register program, with fair random bits in rational bit-cost executions and exact-real arithmetic/Bernoulli(p) access for real inputs; reason: this makes the implicit computational model explicit without admitting optimization instructions or semantic callbacks
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Theorem 2.2, printed p.16 (PDF p.17)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Algorithm

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

theorem theorem_2_2 (alpha delta : ℝ) (ha : 1 ≤ alpha) (hd : 0 < delta) :
  PolynomialApproximation alpha true → PolynomialApproximation (alpha + delta) false := by sorry

end ConstrainedCorrelationRepulsion.Main
