-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_lemma_5_5
-- name    : ConstrainedCorrelationRepulsion.Main.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:30:24.991925+00:00
-- url     : https://prove2.me/theorems/728f580b-f56b-4119-a017-dde7d25e15b5
-- title:
--   Lemma 5.5 — positive-pair error and all degree/objective bounds
-- statement:
--   Let $I'$ and its units arise from the Figure 4 trace on $I$, and use a rational optimal table at even level $r\ge6$. Write $Y$ for cross-unit LP co-clustering mass and $L_+,L_-$ for the positive and negative parts of the residual LP objective. Let $S_F$ be the free positive-degree sum evaluated with the residual labels, and let $P_+,D_+$ count cross-unit positive pairs and their absolute normalized discrepancy. All clauses are
--
--   $$
--   D_+\le\sqrt{2YP_+/r},\quad Y\le S_F+L_-,\quad P_+\le S_F+L_+,\quad Y,P_+\le60007\,\mathrm{OPT}(I).
--   $$
--
--   The last optimum is that of the instance entering preclustering, not the smaller residual optimum. The trace is constructed from metric rounding and expansion certificates and does not assume these error bounds.
--
--   Differences from the source:
--   - encoding: finite vertex set and partitions → Fin n with vertex-label partitions and unordered-pair cost; reason: every finite partition admits these labels, including n = 0; each pair is counted once
--   - encoding: an absolute constant Cpre → the common value Cpre = 60006; reason: the proof supplies 6 times 10001 on printed p.20 (PDF p.21)
--   - generalization: the preclustering input normalized as stipulated in Section 4 → a Figure 4 trace from any feasible unweighted cannot-link input; reason: the full preclustering guarantees hold without the initial normalization; the residual labels and unit conditions needed in Section 5 are unchanged
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Lemma 5.5, equation (30), printed p.29 (PDF p.30)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Sampler
import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Preclustering

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

theorem lemma_5_5 {n : ℕ} (I J : Instance n) (U : Units n) (r : ℕ)
    (y : LocalTable n) (hn : 0 < n) (hr : 6 ≤ r) (heven : Even r)
    (hI : FeasibleInput I) (hM : I.mustLink = ⊥) (htrace : PreclusterTrace I J U)
    (hy : BoundedOptimal J U r y) (hq : RationalTable y) :
  positiveError J U y r ≤ Real.sqrt (2 * Y U y * positivePairs J U / r) ∧
  Y U y ≤ (freeDegree J U : ℝ) + Lminus J U y ∧
  positivePairs J U ≤ (freeDegree J U : ℝ) + Lplus J U y ∧
  Y U y ≤ ((Cpre + 1 : ℕ) : ℝ) * (OPT I : ℝ) ∧
  positivePairs J U ≤ ((Cpre + 1 : ℕ) : ℝ) * (OPT I : ℝ) := by sorry

end ConstrainedCorrelationRepulsion.Main
