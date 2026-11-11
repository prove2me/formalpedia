-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_lemma_6_3
-- name    : ConstrainedCorrelationRepulsion.Main.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:31:22.766126+00:00
-- url     : https://prove2.me/theorems/cc9bcf72-69cb-41bb-bd0e-073e399f6440
-- title:
--   Lemma 6.3 — both inequalities in the infinite-round objective bound
-- statement:
--   Let $r$ be the even LP level, $L=L_++L_-$ the residual LP objective split by sign, $Y$ the cross-unit LP co-clustering mass, $P_+$ the positive cross-unit pair count, $D_s$ the signed discrepancy over non-hard cross-unit pairs, and $D_+$ the absolute discrepancy on positive cross-unit pairs. For the fixed candidate law, the complete chained estimate is
--
--   $$
--   \mathbb E\mathrm{cost}_{I'}(\mathrm{ALG}_\infty)\le2L-L_-+D_s+3D_+\le2L-L_-+\frac{2Y}{r}+3\sqrt{\frac{2YP_+}{r}}.
--   $$
--
--   Both inequalities are retained. The signed error remains signed; the LP objective and the expected cost refer to the residual labels.
--
--   Differences from the source:
--   - encoding: finite vertex set and partitions → Fin n with vertex-label partitions and unordered-pair cost; reason: every finite partition admits these labels, including n = 0; each pair is counted once
--   - generalization: units obtained by the preclustering procedure → any unit partition satisfying the stated residual structural conditions; reason: these conclusions use normalized labels, hard cross-products and local LP constraints; atom optimality and the free-degree budget are not used
--   - encoding: real expectations of conditional inclusion values → extended nonnegative sums of conditional inclusion values; reason: reachable inclusion values lie in [0,1] and the sampler has finite support, so these equalities are equivalent to the ordinary real expectations
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Lemma 6.3, equation (41), printed p.33 (PDF p.34)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Rounds

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

theorem lemma_6_3 {n : ℕ} (I : Instance n) (U : Units n) (r : ℕ)
    (y : LocalTable n) (hn : 0 < n) (hr : 6 ≤ r) (heven : Even r)
    (hres : ResidualUnits I U) (hy : BoundedOptimal I U r y) (hq : RationalTable y) :
  let A := 2 * L I U y - Lminus I U y + signedError I U y r + 3 * positiveError I U y r
  0 ≤ A ∧ infiniteExpectedCost I U y r ≤ ENNReal.ofReal A ∧ A ≤ roundsBound I U y r := by sorry

end ConstrainedCorrelationRepulsion.Main
