-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_lemma_5_4
-- name    : ConstrainedCorrelationRepulsion.Main.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:30:36.863384+00:00
-- url     : https://prove2.me/theorems/82b8911a-f612-42ab-a7de-658c3b9410a8
-- title:
--   Lemma 5.4 — squared discrepancy and both signed bounds
-- statement:
--   At even LP level $r\ge6$, let $D_s$ be the sum of discrepancies over non-hard cross-unit pairs. For the actual Figure 5 candidate distribution, define $d_{uv}=Z(q_{uv}-q^0_{uv})$ on cross-unit pairs and $Y=\sum_{u<v,B(u)\ne B(v)}(1-x_{uv})$. Then
--
--   $$
--   \sum_{\rm cross}d_{uv}^2\le2Y/r,\qquad 0\le\sum_{\rm cross}d_{uv}\le2Y/r,\qquad D_s\le2Y/r.
--   $$
--
--   The first two sums include cannot-link pairs. Only $D_s$ excludes hard pairs, and no nonnegativity conclusion is asserted for $D_s$. The law is defined by actual conditioning and sampling, rather than by these bounds.
--
--   Differences from the source:
--   - encoding: finite vertex set and partitions → Fin n with vertex-label partitions and unordered-pair cost; reason: every finite partition admits these labels, including n = 0; each pair is counted once
--   - generalization: units obtained by the preclustering procedure → any unit partition satisfying the stated residual structural conditions; reason: these conclusions use normalized labels, hard cross-products and local LP constraints; atom optimality and the free-degree budget are not used
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Lemma 5.4, equations (22)–(23), printed p.27 (PDF p.28)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Sampler

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

theorem lemma_5_4 {n : ℕ} (I : Instance n) (U : Units n) (r : ℕ)
    (y : LocalTable n) (hn : 0 < n) (hr : 6 ≤ r) (heven : Even r)
    (hres : ResidualUnits I U) (hy : BoundedOptimal I U r y) (hq : RationalTable y) :
  (pairSum (fun u v => if unitOf U u ≠ unitOf U v then (discrepancy I U y r u v)^2 else 0)) ≤ 2 * Y U y / r ∧
  0 ≤ pairSum (fun u v => if unitOf U u ≠ unitOf U v then discrepancy I U y r u v else 0) ∧
  (pairSum (fun u v => if unitOf U u ≠ unitOf U v then discrepancy I U y r u v else 0)) ≤ 2 * Y U y / r ∧
  signedError I U y r ≤ 2 * Y U y / r := by sorry

end ConstrainedCorrelationRepulsion.Main
