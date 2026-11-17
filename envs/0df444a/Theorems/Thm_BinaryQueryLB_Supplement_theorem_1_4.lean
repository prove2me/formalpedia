-- Prove2me | Theorems.Thm_BinaryQueryLB_Supplement_theorem_1_4
-- name    : BinaryQueryLB.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:53:33.628421+00:00
-- url     : https://prove2.me/theorems/68ccfcbe-0f51-456e-ab40-ff21d6d20490
-- title:
--   Theorem 1.4 — with exact values plus one linear measurement, accuracy $c_0MR/\sqrt d$ under every chart needs more than $d^2/(3600\log(d+1))$ queries
-- statement:
--   Let $d\ge4$, $R,M>0$ and $c_0=5\cdot10^{-8}$. Let $A$ be a deterministic algorithm with the strong oracle $O^*$, which answers a query $(y,v)$, $y\in X=[-R,R]^d$, $v\in\mathbb R^d$, by the exact pair $\big(f(y),\langle v,g_f(y)\rangle\big)$. Suppose that, for every $f\in F(d,R,M)$ and every first-order chart $G$, the run of $A$ on $(f,G)$ outputs a point $\hat y$ with
--   $$
--   f(\hat y)-\min_X f\le\frac{c_0MR}{\sqrt d}.
--   $$
--   Then there are a first-order chart $G$ and a function $f\in F(d,R,M)$ on which $A$ makes more than
--   $$
--   \frac{d^2}{3600\,\log(d+1)}
--   $$
--   queries.
--
--   The hard chart may depend on the algorithm. The result extends Kerger's exact-value lower bound to the box with the maximum-norm normalization while allowing, in addition to the value, one exact linear measurement of the subgradient per query. Logarithms are natural.
--
--   Differences from the source:
--   - encoding: a deterministic algorithm with O∗ choosing each query (y, v), y ∈ X, and its output as functions of the previous real answers → a map from answer histories (List (ℝ × ℝ)) to a query or an output, with the hypothesis that every query point lies in X; reason: this is the model of p.12; there is no bound on the number of queries and the answers are exact reals
--   - encoding: f(ŷ) − min_X f ≤ ε with ŷ ∈ X → ŷ ∈ X and f(ŷ) ≤ f(y) + ε for all y ∈ X; reason: the minimum over X is attained for f ∈ F(d,R,M) (continuous on the compact box), so the two forms agree
--   - encoding: makes more than N queries on some f and chart → there are a chart G and f ∈ F(d,R,M) whose run stops after T queries with N < T; reason: the hypothesis makes every run stop, so its query count is this T
--   - encoding: ℝ^d with ⟨·,·⟩ and ∥·∥∞, c0 = 5·10⁻⁸ → EuclideanSpace ℝ (Fin d) with its inner product and the maximum norm supNorm, 5 / 10 ^ 8; reason: the same space, inner product, norm and constant
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Theorem 1.4, p.5 (proof §5, pp.21–25, Appendix B pp.26–27)

import Mathlib
import Definitions.Def_BinaryQueryLB_IsChart
import Definitions.Def_BinaryQueryLB_ProblemClass
import Definitions.Def_BinaryQueryLB_Supplement_StrongQueriesInBox
import Definitions.Def_BinaryQueryLB_Supplement_StrongSolvesEveryChart

namespace BinaryQueryLB.Supplement

/-- **Theorem 1.4 (Exact value plus one measurement).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Theorem 1.4, p.5 (proof §5, pp.21–25, with Appendix B): "Let `d ≥ 4` and `R, M > 0`. Every
deterministic algorithm with `O∗` that outputs a `(c0MR/√d)`-optimal point for every
`f ∈ F(d, R, M)` and every first-order chart makes more than `d²/(3600 log(d + 1))` queries on some
`f` and chart."

**Formalization Note.** `c0 = 5·10^{−8}` (Theorem 1.1, p.4) is written `5 / 10 ^ 8`; the accuracy is
the single value `c0·M·R/√d`. The algorithm is a map on histories of exact real answer pairs
(`StrongAlgorithm`), with no bound on its number of queries; `StrongQueriesInBox` says its query
points lie in `X`. The quantifier order is the paper's: the algorithm is fixed first and the bad
chart may depend on it (p.5). "Makes more than `N` queries on `f` and chart `G`" is: its run on
`(f, G)` stops after `T` queries with `N < T`. Natural logarithm. -/
theorem theorem_1_4 (d : ℕ) (hd : 4 ≤ d) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (A : StrongAlgorithm d) (hbox : StrongQueriesInBox d R A)
    (hsolve : StrongSolvesEveryChart d R M (5 / 10 ^ 8 * M * R / Real.sqrt d) A) :
    ∃ G : BinaryQueryLB.Chart d, BinaryQueryLB.IsChart d R M G ∧
      ∃ f ∈ BinaryQueryLB.ProblemClass d R M, ∃ (T : ℕ) (yh : EuclideanSpace ℝ (Fin d)),
        StrongStopsWith A G f T yh ∧
        (d : ℝ) ^ 2 / (3600 * Real.log (d + 1)) < T := by sorry

end BinaryQueryLB.Supplement
