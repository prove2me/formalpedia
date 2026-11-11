-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_theorem_3_3
-- name    : ConstrainedCorrelationRepulsion.Main.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:30:02.884987+00:00
-- url     : https://prove2.me/theorems/f0a93791-e892-4c19-9803-a032d109fa4a
-- title:
--   Theorem 3.3 — probability-weighted expansion transfer
-- statement:
--   Fix real constants $\alpha\ge1$ and $\delta>0$. Suppose a polynomial-time randomized algorithm on complete unweighted instances with only cannot-links always returns a feasible partition and has expected approximation factor $\alpha$. Then arbitrary probability-weighted cannot-link instances admit a randomized polynomial-time algorithm that always returns a feasible partition and satisfies
--
--   $$
--   \mathbb E[\mathrm{cost}(P)]\le(\alpha+\delta)\mathrm{OPT}.
--   $$
--
--   This transfer retains every real separation probability $p\in[0,1]$, including arbitrarily small nonintegral optima. The expansion and representative laws are defined separately, with full hard cross-products and the majority-clique direct branch.
--
--   **Formalization Note.** Appendix B supplies $T=\lceil256n^4\gamma^{-4}L_b^2\rceil$, with the constants defined in the reduction item. All exponent constants are fixed before the input; the probability-weighted computational model is exact-real arithmetic and Bernoulli access.
--
--   Differences from the source:
--   - encoding: finite vertex set and partitions → Fin n with vertex-label partitions and unordered-pair cost; reason: every finite partition admits these labels, including n = 0; each pair is counted once
--   - reading: polynomial-time algorithm without a named machine → one finite charged register program, with fair random bits in rational bit-cost executions and exact-real arithmetic/Bernoulli(p) access for real inputs; reason: this makes the implicit computational model explicit without admitting optimization instructions or semantic callbacks
--   - encoding: pair costs defined only for distinct vertices → total functions on Sym2 with unused diagonal padding; probability padding lies in [0,1]; reason: every source assignment extends to such a function, every objective ignores the diagonal, and no source instance is excluded
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Theorem 3.3, printed p.15 (PDF p.16), proof printed pp.43–45 (PDF pp.44–46)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Reductions

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

theorem theorem_3_3 (alpha delta : ℝ) (ha : 1 ≤ alpha) (hd : 0 < delta) :
  PolynomialApproximation alpha true → WeightedPolynomialApproximation (alpha + delta) := by sorry

end ConstrainedCorrelationRepulsion.Main
