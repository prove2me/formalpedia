-- Prove2me | Theorems.Thm_BinaryQueryLB_corollary_3_3
-- name    : BinaryQueryLB.corollary_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:50:10.306919+00:00
-- url     : https://prove2.me/theorems/d68dada6-d063-494f-8e18-bd39c145f937
-- title:
--   Corollary 3.3 — $\Pi_T\ge(\omega_m\tau^m)^m(8m)^{-T}$, and surviving instances reproduce the run
-- statement:
--   In the setting of Lemma 3.2, after $T$ queries against the adversary,
--   $$
--   \Pi_T\ge(\omega_m\tau^m)^m\,(8m)^{-T},
--   $$
--   and for every $W$ in the product $\mathcal P$ at that time, the first $T$ queries and answers of $A$ on $(F_W,G_{\mathrm{can}})$ coincide with those of $A$ against the adversary. In particular, if $A$ stops against the adversary after $T$ queries, then it also stops on $(F_W,G_{\mathrm{can}})$ after $T$ queries and outputs the same point.
--
--   Here $\omega_m$ is the volume of the unit ball of $\mathbb R^m$ and $\tau=a/(\Gamma\sqrt m)$.
--
--   Differences from the source:
--   - generalization: under the chart Gcan of Definition 2.7 (some fixed subgradient off ℋ) → under every chart G that is a first-order chart and equals g_W on ℋ (IsCanonicalChart); reason: the paper's Gcan is one such chart, and the argument uses only its values on ℋ
--   - generalization: the adversary of §3.1 (some admissible levels r_k and some admissible bit β at each step) → every run obeying the §3.1 rules, with any admissible levels and bits (IsAdvRun); reason: the paper's adversary is one such run; the statement covers all of them
--   - generalization: A as in Proposition 3.1 (it outputs an ε-optimal point for every F_W ∈ ℋ under Gcan, for an ε with C_K√m ε < MR) → every algorithm whose query points lie in X (QueriesInBox), with no success hypothesis; reason: the argument uses only the queries of A, so the paper's A is a special case
--   - encoding: a deterministic algorithm choosing queries and stopping as functions of the earlier answers, with query points in X → a map from answer histories (List Bool) to a query or an output, with the hypothesis that every query point lies in X; reason: this is the definition of p.11; there is no bound on the number of queries and no condition on the binary functions
--   - encoding: m = ⌊d/2⌋ → m = d / 2 (natural-number division); reason: the same number
--   - encoding: Lebesgue outer measure µ* → MeasureTheory.volume evaluated on arbitrary sets, values in ℝ≥0∞; reason: volume on an arbitrary set is its outer measure
--   - encoding: the first T queries and answers coincide → for every t ≤ T the answer history on (F_W, G) after t steps is the adversary's first t answers; reason: queries are functions of the answer history
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Corollary 3.3, p.17

import Mathlib
import Definitions.Def_BinaryQueryLB_IsAdvRun
import Definitions.Def_BinaryQueryLB_IsCanonicalChart
import Definitions.Def_BinaryQueryLB_QueriesInBox
import Definitions.Def_BinaryQueryLB_StopsWith
import Definitions.Def_BinaryQueryLB_FW__386b32
import Definitions.Def_BinaryQueryLB_omegaVol
import Definitions.Def_BinaryQueryLB_tau
open scoped ENNReal

namespace BinaryQueryLB

/-- **Corollary 3.3.** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Corollary 3.3, p.17: "After `T` queries, `Π_T ≥ (ω_m τ^m)^m (8m)^{−T}`,
and for every `W` in the product `𝒫` at that time, the first `T` queries and answers of `A` on
`(F_W, Gcan)` coincide with those of `A` against the adversary. In particular, if `A` stops against
the adversary after `T` queries, then it also stops on `(F_W, Gcan)` after `T` queries and outputs
the same point."

**Formalization Note.** Stated for every run obeying the §3.1 rules (`IsAdvRun`) of length `T`.
"The first `T` queries and answers coincide" is: for every `t ≤ T` the answer history of `A` on
`(F_W, Gcan)` after `t` steps is `β 0, …, β (t−1)` (the queries are functions of these histories).
`Π_T` is in `ℝ≥0∞`; `m = d / 2`; `ω_m` is `omegaVol m`. -/
theorem corollary_3_3 (d : ℕ) (hd : 2 ≤ d) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (G : Chart d) (hG : IsCanonicalChart d R M G) (A : Algorithm d) (hA : QueriesInBox d R A)
    (T : ℕ) (s : ℕ → AdvState d) (β : ℕ → Bool) (hrun : IsAdvRun d R M A T s β) :
    ENNReal.ofReal ((omegaVol (d / 2) * tau (d / 2) ^ (d / 2)) ^ (d / 2)) /
        (8 * ((d / 2 : ℕ) : ℝ≥0∞)) ^ T ≤ ∏ i, MeasureTheory.volume ((s T).1 i) ∧
      ∀ W : Fin (d / 2) → EuclideanSpace ℝ (Fin (d / 2)), (∀ i, W i ∈ (s T).1 i) →
        (∀ t ≤ T, history A G (FW d R M W) t = (List.range t).map β) ∧
        ∀ yh : EuclideanSpace ℝ (Fin d), A ((List.range T).map β) = Sum.inr yh →
          StopsWith A G (FW d R M W) T yh := by sorry

end BinaryQueryLB
