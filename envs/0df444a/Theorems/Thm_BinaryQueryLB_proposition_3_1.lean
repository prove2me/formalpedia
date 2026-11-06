-- Prove2me | Theorems.Thm_BinaryQueryLB_proposition_3_1
-- name    : BinaryQueryLB.proposition_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:50:49.947194+00:00
-- url     : https://prove2.me/theorems/b114a9ac-684b-45b3-a7a5-0c15a646db29
-- title:
--   Proposition 3.1 — $\frac{m^2}{4\log(8m)}\log\frac{MR}{C_K\sqrt m\,\varepsilon}$ queries on some $F_W\in\mathcal H$
-- statement:
--   Let $d\ge2$, $R,M>0$ and $m=\lfloor d/2\rfloor$, and let $\varepsilon>0$ satisfy $C_K\sqrt m\,\varepsilon<MR$. Let $A$ be a deterministic algorithm with local binary queries that, under $G_{\mathrm{can}}$, outputs an $\varepsilon$-optimal point for every $F_W\in\mathcal H$. Then on some $F_W\in\mathcal H$ the algorithm makes at least
--   $$
--   \frac{m^2}{4\log(8m)}\,\log\frac{MR}{C_K\sqrt m\,\varepsilon}
--   $$
--   queries (natural logarithms).
--
--   This is the core bound; Theorem 1.1 follows from it by arithmetic on the constants.
--
--   Differences from the source:
--   - generalization: under the chart Gcan of Definition 2.7 (some fixed subgradient off ℋ) → under every chart G that is a first-order chart and equals g_W on ℋ (IsCanonicalChart); reason: the paper's Gcan is one such chart, and the argument uses only its values on ℋ
--   - encoding: a deterministic algorithm choosing queries and stopping as functions of the earlier answers, with query points in X → a map from answer histories (List Bool) to a query or an output, with the hypothesis that every query point lies in X; reason: this is the definition of p.11; there is no bound on the number of queries and no condition on the binary functions
--   - encoding: f(ŷ) − min_X f ≤ ε with ŷ ∈ X → ŷ ∈ X and f(ŷ) ≤ f(y) + ε for all y ∈ X; reason: the minimum over X is attained for the functions considered, so the two forms agree
--   - encoding: m = ⌊d/2⌋ → m = d / 2 (natural-number division); reason: the same number
--   - encoding: makes at least N queries on F_W → its run on (F_W, G) stops after T queries with N ≤ T; reason: success on ℋ includes stopping
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Proposition 3.1, p.15

import Mathlib
import Definitions.Def_BinaryQueryLB_IsCanonicalChart
import Definitions.Def_BinaryQueryLB_QueriesInBox
import Definitions.Def_BinaryQueryLB_Solves
import Definitions.Def_BinaryQueryLB_hardFamily
import Definitions.Def_BinaryQueryLB_CK

namespace BinaryQueryLB

/-- **Proposition 3.1.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Proposition 3.1, p.15: "Let `d ≥ 2`, `R, M > 0` and `m = ⌊d/2⌋`, and let
`ε > 0` satisfy `C_K√m ε < MR`. Let `A` be a deterministic algorithm with local binary queries that,
under `Gcan`, outputs an ε-optimal point for every `F_W ∈ ℋ`. Then on some `F_W ∈ ℋ` the algorithm
`A` makes at least `(m²/(4 log(8m))) log(MR/(C_K√m ε))` queries."

**Formalization Note.** `Gcan` is any chart satisfying Definition 2.7 (`IsCanonicalChart`);
success is assumed on `ℋ` only. "Makes at least `N` queries on `F_W`" is: the run on `(F_W, Gcan)`
stops after `T ≥ N` queries. Natural logarithms; `m = d / 2`. -/
theorem proposition_3_1 (d : ℕ) (hd : 2 ≤ d) (R M : ℝ) (hR : 0 < R) (hM : 0 < M) (ε : ℝ) (hε : 0 < ε)
    (hεK : CK * Real.sqrt ((d / 2 : ℕ) : ℝ) * ε < M * R)
    (G : Chart d) (hG : IsCanonicalChart d R M G) (A : Algorithm d) (hA : QueriesInBox d R A)
    (hsol : Solves d R G (hardFamily d R M) ε A) :
    ∃ W ∈ Wset (d / 2), ∃ (T : ℕ) (yh : EuclideanSpace ℝ (Fin d)),
      StopsWith A G (FW d R M W) T yh ∧
        ((d / 2 : ℕ) : ℝ) ^ 2 / (4 * Real.log (8 * ((d / 2 : ℕ) : ℝ))) *
          Real.log (M * R / (CK * Real.sqrt ((d / 2 : ℕ) : ℝ) * ε)) ≤ T := by sorry

end BinaryQueryLB
