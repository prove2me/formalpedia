-- Prove2me | Theorems.Thm_DoublingMST_Supplement_theorem_6_7
-- name    : DoublingMST.Supplement.theorem_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:20:36.011217+00:00
-- url     : https://prove2.me/theorems/34d16138-2219-46bf-bcc6-87da333fe3d6
-- title:
--   Theorem 6.7 — exact-distance query lower bound $\Omega\big(\min\{n^2,\frac n\epsilon\log\frac1\epsilon\}\big)$ in doubling dimension $7$
-- statement:
--   There are absolute constants $c>0$ and $N$ such that the following holds for every $n\ge N$ and every $\epsilon\in(0,\tfrac12]$. Let $(A_\omega)_{\omega\in\Omega}$ be a randomized exact-distance query algorithm on $n$ points over a probability space $(\Omega,\mu)$ (Definition 6.2: each query of an unordered pair $\{x,y\}$ returns $d(x,y)$ exactly and costs one unit; computation on returned values is free). Suppose that on every metric $d$ on the $n$ points with doubling dimension $\mathrm{ddim}(d)\le7$ it outputs a spanning tree $T$ with $w_d(T)\le(1+\epsilon)\,\mathrm{MST}(d)$ with probability at least $2/3$. Then some such metric $d$ has expected number of queries
--
--   $$\mathbb E[q]\ \ge\ c\,\min\Big\{n^2,\ \frac n\epsilon\log_2\frac1\epsilon\Big\}.$$
--
--   This shows that the $\epsilon^{-1}\log(1/\epsilon)$ dependence of the doubling-metric algorithm (Theorem 1.1) cannot be improved with oracle access, even with unlimited free computation.
--
--   **Formalization Note** The model is `DoublingMST.Supplement.QueryAlg`; for every metric with $\mathrm{ddim}\le 7$, the query count and the success event are assumed measurable in $\omega$. Doubling dimension is the published `DoublingMST.ddim`.
--
--   Differences from the source:
--   - encoding: for every sufficiently large n and 0 < ϵ ≤ 1/2, Ω(·) → ∃ c > 0, ∃ N, ∀ n ≥ N, ∀ ϵ ∈ (0, 1/2]; reason: c and N are absolute, independent of ϵ; the proof uses n ≥ 2^18 and two ranges of ϵ
--   - encoding: any randomized algorithm (Definition 6.2: exact-distance queries, unrestricted computation) → a family A : Ω → QryStrategy n over a probability space (Ω, μ), with the query count and the success event measurable in ω for every metric with ddim ≤ 7; reason: the probabilities and expectations of the source are those of measurable quantities; without measurability μ and ∫⁻ would be outer measure and lower integral
--   - encoding: worst-case expected distance-query complexity over n-point metrics of doubling dimension at most 7 → ∃ d with IsMetric d, ddim d ≤ 7 and ∫⁻ qryCount ≥ ofReal(c · min{n², (n/ϵ) log₂(1/ϵ)}); a strategy that never outputs has count ⊤; reason: the worst case is attained by some input
--   - encoding: log(1/ϵ) → Real.logb 2; reason: a change of base changes only the constant c
-- source:
--   Höckendorff–Hommelsheim–Sohler–Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Theorem 6.7, p.34 (PDF p.36); proof §6.3.4, pp.41–42 (PDF pp.43–44)

import Mathlib
import Definitions.Def_DoublingMST_Supplement_QueryAlg
import Definitions.Def_DoublingMST_Supplement_IsApproxTree
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_ddim
open scoped Classical ENNReal

namespace DoublingMST.Supplement

open MeasureTheory

/-- **Theorem 6.7 (exact-distance query lower bound).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning
Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Theorem 6.7,
p.34 (PDF p.36), proof pp.41–42: "For every sufficiently large integer n and 0 < ϵ ≤ 1/2, any
randomized algorithm that returns a (1 + ϵ)-approximate spanning tree with probability at least
2/3 on every n-point metric of doubling dimension at most 7 has worst-case expected distance-query
complexity Ω(min{n², (n/ϵ) log(1/ϵ)})."

There are `c > 0` and `N` such that for every `n ≥ N`, every `ϵ ∈ (0, 1/2]` and every randomized
exact-distance query algorithm `A` over a probability space `(Ω, μ)`: if on every metric `d` on
the `n` points with `ddim d ≤ 7` it outputs a `(1 + ϵ)`-approximate spanning tree with probability
at least `2/3`, then some such metric has expected query count at least
`c · min{n², (n/ϵ) log₂(1/ϵ)}`.

**Formalization Note.** The model is Definition 6.2
(`Definitions.Def_DoublingMST_Supplement_QueryAlg`): computation between queries is free. For every
such metric the query count and the success event are assumed measurable in the randomness. Logs
are base 2. -/
theorem theorem_6_7 : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → ∀ ϵ : ℝ, 0 < ϵ → ϵ ≤ 1 / 2 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (A : Ω → QryStrategy n),
      (∀ d : Fin n → Fin n → ℝ, DoublingMST.IsMetric d → DoublingMST.ddim d ≤ 7 →
        Measurable (fun ω => qryCount (A ω) d) ∧
        MeasurableSet {ω | ∃ T, QryOutputs (A ω) d T ∧ IsApproxTree d (1 + ϵ) T}) →
      (∀ d : Fin n → Fin n → ℝ, DoublingMST.IsMetric d → DoublingMST.ddim d ≤ 7 →
        (2 / 3 : ℝ≥0∞) ≤ μ {ω | ∃ T, QryOutputs (A ω) d T ∧ IsApproxTree d (1 + ϵ) T}) →
      ∃ d : Fin n → Fin n → ℝ, DoublingMST.IsMetric d ∧ DoublingMST.ddim d ≤ 7 ∧
        ENNReal.ofReal (c * min ((n : ℝ) ^ 2) ((n : ℝ) / ϵ * Real.logb 2 (1 / ϵ))) ≤
          ∫⁻ ω, ((qryCount (A ω) d : ℕ∞) : ℝ≥0∞) ∂μ := by sorry

end DoublingMST.Supplement
