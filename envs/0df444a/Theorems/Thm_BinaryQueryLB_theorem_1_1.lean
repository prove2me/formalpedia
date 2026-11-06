-- Prove2me | Theorems.Thm_BinaryQueryLB_theorem_1_1
-- name    : BinaryQueryLB.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:49:04.332301+00:00
-- url     : https://prove2.me/theorems/d375959e-f981-4f8a-99f9-5befb9b87a8a
-- title:
--   Theorem 1.1 — under one fixed chart, $\varepsilon$-optimization over $F(d,R,M)$ needs $d^2\log(MR/\varepsilon)/(1000\log^2(d+1))$ local binary queries
-- statement:
--   Let $d\ge2$, $R,M>0$ and $c_0=5\cdot10^{-8}$. There is a first-order chart $G_{\mathrm{can}}$ with the following property. For every $\varepsilon\in(0,\,c_0MR/\sqrt d\,]$, every deterministic algorithm with local binary queries that, under $G_{\mathrm{can}}$, outputs an $\varepsilon$-optimal point for every $f\in F(d,R,M)$ makes, on some $f\in F(d,R,M)$, at least
--   $$
--   \frac{d^2\log(MR/\varepsilon)}{1000\,\log^2(d+1)}
--   $$
--   queries, and at least
--   $$
--   \frac{d^2\log(MR/\varepsilon)}{216\,\log(d+1)}
--   $$
--   queries if $\log(MR/\varepsilon)\ge27\log(d+1)$.
--
--   The chart is fixed before the accuracy and the algorithm. Each local binary query reads one bit of first-order information $(f(y),G(f,y))$ through an arbitrary (possibly non-measurable) function, so the bound covers the bit, shifted-bit and inner-product threshold oracles. Logarithms are natural and $\log^2(d+1)=(\log(d+1))^2$.
--
--   Differences from the source:
--   - encoding: a deterministic algorithm choosing queries and stopping as functions of the earlier answers, with query points in X → a map from answer histories (List Bool) to a query or an output, with the hypothesis that every query point lies in X; reason: this is the definition of p.11; there is no bound on the number of queries and no condition on the binary functions
--   - encoding: f(ŷ) − min_X f ≤ ε with ŷ ∈ X → ŷ ∈ X and f(ŷ) ≤ f(y) + ε for all y ∈ X; reason: the minimum over X is attained for the functions considered, so the two forms agree
--   - reading: makes, on some f, at least N₁ queries, and at least N₂ queries if log(MR/ε) ≥ 27 log(d+1) → one f whose run stops after T queries with N₁ ≤ T and (log(MR/ε) ≥ 27 log(d+1) → N₂ ≤ T); reason: equivalent to one f per bound: the function with the larger query count satisfies both
--   - encoding: ℝ^d with ∥·∥∞ and {0,1} → EuclideanSpace ℝ (Fin d) with the maximum norm supNorm written out, and Bool; reason: the same space, norm and bits
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Theorem 1.1, p.4

import Mathlib
import Definitions.Def_BinaryQueryLB_IsChart
import Definitions.Def_BinaryQueryLB_QueriesInBox
import Definitions.Def_BinaryQueryLB_Solves
import Definitions.Def_BinaryQueryLB_ProblemClass

namespace BinaryQueryLB

/-- **Theorem 1.1 (Main theorem).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Theorem 1.1, p.4: "Let `d ≥ 2`, `R, M > 0` and
`c0 = 5·10^{−8}`. There is a first-order chart `Gcan` with the following property. For every
`ε ∈ (0, c0MR/√d]`, every deterministic algorithm with local binary queries that, under `Gcan`,
outputs an ε-optimal point for every `f ∈ F(d, R, M)` makes, on some `f ∈ F(d, R, M)`, at least
`d² log(MR/ε)/(1000 log²(d + 1))` queries, and at least `d² log(MR/ε)/(216 log(d + 1))` queries if
`log(MR/ε) ≥ 27 log(d + 1)`."

**Formalization Note.** The chart is chosen before `ε` and the algorithm. An algorithm is a map on
answer histories (`Algorithm`), with arbitrary binary functions and no bound on its number of
queries; `QueriesInBox` says its query points lie in `X`. "Makes at least `N` queries on `f`" is:
its run on `(f, G)` stops after `T ≥ N` queries; one function `f` carries both bounds (equivalent
to one function per bound, since the larger of the two query counts satisfies both). Natural
logarithms; `log²(d+1) = (log(d+1))²`; `c0 = 5/10⁸`. -/
theorem theorem_1_1 (d : ℕ) (hd : 2 ≤ d) (R M : ℝ) (hR : 0 < R) (hM : 0 < M) :
    ∃ G : Chart d, IsChart d R M G ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 5 / 10 ^ 8 * M * R / Real.sqrt d →
      ∀ A : Algorithm d, QueriesInBox d R A → Solves d R G (ProblemClass d R M) ε A →
        ∃ f ∈ ProblemClass d R M, ∃ (T : ℕ) (yh : EuclideanSpace ℝ (Fin d)),
          StopsWith A G f T yh ∧
          (d : ℝ) ^ 2 * Real.log (M * R / ε) / (1000 * Real.log (d + 1) ^ 2) ≤ T ∧
          (27 * Real.log (d + 1) ≤ Real.log (M * R / ε) →
            (d : ℝ) ^ 2 * Real.log (M * R / ε) / (216 * Real.log (d + 1)) ≤ T) := by sorry

end BinaryQueryLB
