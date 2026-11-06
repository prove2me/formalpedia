-- Prove2me | Theorems.Thm_BinaryQueryLB_lemma_3_2
-- name    : BinaryQueryLB.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:50:16.705142+00:00
-- url     : https://prove2.me/theorems/40ac2111-b71a-42ac-8d76-df0fcac441c0
-- title:
--   Lemma 3.2 — adversary invariants (a)–(d)
-- statement:
--   Let $d\ge2$, $R,M>0$, $m=\lfloor d/2\rfloor$, let $G_{\mathrm{can}}$ be the canonical chart, and let $A$ be a deterministic algorithm with local binary queries, run against the adversary of §3.1 for $T$ queries. Write $P_1,\dots,P_m$ for the adversary's row sets, $\mathcal P=P_1\times\dots\times P_m$ for the surviving matrices, $j(y)$ for the committed indices, and $\Pi=\prod_{i=1}^m\mu^*(P_i)$. After each query the following hold.
--
--   1. Every $P_i$ is a subset of $\tau\mathbb B_m$ with $\mu^*(P_i)>0$.
--   2. For every surviving $W\in\mathcal P$ and every point $y$ queried so far, $i_W(y)=j(y)$.
--   3. For every surviving $W\in\mathcal P$, every answer given so far equals the answer of the same query on $F_W$ under $G_{\mathrm{can}}$.
--   4. The potential satisfies $\Pi_{\mathrm{new}}\ge\Pi_{\mathrm{old}}/(8m)$.
--
--   Each answer of the adversary therefore costs at most a factor $8m$ of potential, while staying consistent with every surviving hard function.
--
--   Differences from the source:
--   - generalization: under the chart Gcan of Definition 2.7 (some fixed subgradient off ℋ) → under every chart G that is a first-order chart and equals g_W on ℋ (IsCanonicalChart); reason: the paper's Gcan is one such chart, and the argument uses only its values on ℋ
--   - generalization: the adversary of §3.1 (some admissible levels r_k and some admissible bit β at each step) → every run obeying the §3.1 rules, with any admissible levels and bits (IsAdvRun); reason: the paper's adversary is one such run; the statement covers all of them
--   - generalization: A as in Proposition 3.1 (it outputs an ε-optimal point for every F_W ∈ ℋ under Gcan, for an ε with C_K√m ε < MR) → every algorithm whose query points lie in X (QueriesInBox), with no success hypothesis; reason: the argument uses only the queries of A, so the paper's A is a special case
--   - encoding: a deterministic algorithm choosing queries and stopping as functions of the earlier answers, with query points in X → a map from answer histories (List Bool) to a query or an output, with the hypothesis that every query point lies in X; reason: this is the definition of p.11; there is no bound on the number of queries and no condition on the binary functions
--   - encoding: m = ⌊d/2⌋ → m = d / 2 (natural-number division); reason: the same number
--   - encoding: Lebesgue outer measure µ* → MeasureTheory.volume evaluated on arbitrary sets, values in ℝ≥0∞; reason: volume on an arbitrary set is its outer measure
--   - encoding: after each query → after t queries, for every t ≤ T (clause 4 for t < T); reason: the run has T queries
-- source:
--   Shen–Zhong, Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries (manuscript, sha256 9502d824…), Lemma 3.2, pp.16–17

import Mathlib
import Definitions.Def_BinaryQueryLB_IsAdvRun
import Definitions.Def_BinaryQueryLB_IsCanonicalChart
import Definitions.Def_BinaryQueryLB_QueriesInBox
import Definitions.Def_BinaryQueryLB_answer
import Definitions.Def_BinaryQueryLB_iW
import Definitions.Def_BinaryQueryLB_FW__386b32
import Definitions.Def_BinaryQueryLB_tau
open scoped ENNReal

namespace BinaryQueryLB

/-- **Lemma 3.2 (Adversary invariants).** Shen–Zhong, *Near-Quadratic Lower Bounds for Convex Optimization with Binary First-Order Queries* (manuscript, sha256 9502d824…), Lemma 3.2, pp.16–17: "After each query the following
hold. (a) Every `P_i` is a subset of `τB_m` with `µ*(P_i) > 0`. (b) For every surviving `W ∈ 𝒫` and
every point `y` queried so far, `i_W(y) = j(y)`. (c) For every surviving `W ∈ 𝒫`, every answer given
so far equals the answer of the same query on `F_W` under `Gcan`. (d) The potential satisfies
`Π_new ≥ Π_old/(8m)`."

The context is §3.1: `A` is a deterministic algorithm with local binary queries, run against the
adversary for `T` queries (`IsAdvRun`); `𝒫 = P_1 × ⋯ × P_m` is the set of surviving matrices and
`Π = ∏_i µ*(P_i)`.

**Formalization Note.** Stated for every run obeying the §3.1 rules, at every time `t ≤ T`
((d) for `t < T`). `(s t).1` are the row sets and `(s t).2` the committed indices after `t`
queries; the `u`-th query is `A` applied to the answers `β 0, …, β (u−1)`. `Gcan` is any chart
satisfying Definition 2.7 (`IsCanonicalChart`). `µ*` is `volume` on arbitrary sets; `Π` is in
`ℝ≥0∞`; `m = d / 2`. -/
theorem lemma_3_2 (d : ℕ) (hd : 2 ≤ d) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (G : Chart d) (hG : IsCanonicalChart d R M G) (A : Algorithm d) (hA : QueriesInBox d R A)
    (T : ℕ) (s : ℕ → AdvState d) (β : ℕ → Bool) (hrun : IsAdvRun d R M A T s β) :
    ∀ t ≤ T,
      (∀ i, (s t).1 i ⊆ Metric.closedBall 0 (tau (d / 2)) ∧ 0 < MeasureTheory.volume ((s t).1 i)) ∧
      (∀ W : Fin (d / 2) → EuclideanSpace ℝ (Fin (d / 2)), (∀ i, W i ∈ (s t).1 i) →
        ∀ u < t, ∀ qr : LocalQuery d, A ((List.range u).map β) = Sum.inl qr →
          ∃ j, (s t).2 qr.1 = some j ∧ iW W (R⁻¹ • ybar d qr.1) = some j) ∧
      (∀ W : Fin (d / 2) → EuclideanSpace ℝ (Fin (d / 2)), (∀ i, W i ∈ (s t).1 i) →
        ∀ u < t, ∀ qr : LocalQuery d, A ((List.range u).map β) = Sum.inl qr →
          answer G (FW d R M W) qr = β u) ∧
      (t < T → (∏ i, MeasureTheory.volume ((s t).1 i)) / (8 * ((d / 2 : ℕ) : ℝ≥0∞)) ≤
        ∏ i, MeasureTheory.volume ((s (t + 1)).1 i)) := by sorry

end BinaryQueryLB
