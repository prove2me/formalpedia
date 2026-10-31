-- Prove2me | Theorems.Thm_CompetitionComplexity_lemma_3
-- name    : CompetitionComplexity.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:09.554309+00:00
-- url     : https://prove2.me/theorems/37eacd68-c503-47a2-be52-d56dd99b874f
-- title:
--   Lemma 3 (corrected: adds the hypothesis $\partial B_n\to0$) — every $(B_n)$ with $B_0=0$, (a)–(c) and $\partial B_n\to0$ equals $(A_n(G))$ for a distribution $G$ with equality in Lemma 2
-- statement:
--   Let $(B_n)_{n\in\mathbb N}$ be a real sequence with $B_0=0$ that is strictly increasing, has non-increasing increments $\partial B_n=B_{n+1}-B_n$, and has non-decreasing ratios $\partial B_{n+1}/\partial B_n$, and suppose that $\partial B_n\to0$. Then there is a distribution $G$ on $[0,\infty)$ with finite mean such that
--
--   1. $A_n(G)=B_n$ for every $n\in\mathbb N$, and
--   2. for every $n$,
--   $$
--   M_n(G)=\sum_{j=0}^{\infty}\Bigl(1-\Bigl(\frac{\partial B_{j+1}}{\partial B_j}\Bigr)^n\Bigr)\partial B_j .
--   $$
--
--   So the bound of Lemma 2 is attained, and every such sequence is realized by some distribution. The hypothesis $\partial B_n\to0$ is also necessary: it holds for $(A_n(F))$ whenever $F$ has finite mean.
--
--   **Formalization Note** One distribution $G$ serves every $n$. The series is summed in $[0,\infty]$; its terms are non-negative by (a)–(b).
--
--   Differences from the source:
--   - correction: every (Bₙ) with B₀ = 0 satisfying (a)-(c) → adds the hypothesis ∂Bₙ → 0; reason: the printed statement is false: Bₙ = n has B₀ = 0 and (a)-(c), but no distribution has Aₙ = n, because ∂Aₙ = ∫_{Aₙ}^∞ (1 − F) → 0 for every F with finite mean; the printed proof never shows A₁(G) = B₁ (its G has mean B₁ − lim ∂Bₙ)
--   - encoding: a series of real numbers → a series in [0, ∞] of ENNReal.ofReal of the terms; reason: the terms are non-negative under (a)–(b), so the sum is the same and Lean's junk tsum is avoided
--   - encoding: Mₙ a real number → Mₙ in [0, ∞] (Mval, valued in ENNReal); reason: Mₙ is finite for every distribution, so the comparison with the series in [0, ∞] is unchanged
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, Lemma 3, p.10

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting
import Definitions.Def_CompetitionComplexity_Distribution
import Definitions.Def_CompetitionComplexity_SequenceProperties

open MeasureTheory Filter Topology
open CorreaThreshold.Adaptive (dpW)

namespace CompetitionComplexity

/-- **Lemma 3** (corrected: adds the hypothesis `∂Bₙ → 0`).
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), Lemma 3, p.10:
"For every (Bn)n∈N with B0 = 0, and satisfying (a)-(c), there exists a distribution G such that
An(G) = Bn for every non-negative integer n. Furthermore, we have
Mn(G) = Σ_{j=0}^∞ (1 − (∂Bj+1/∂Bj)^n) ∂Bj."

**Correction.** The printed statement is false without `∂Bₙ → 0`. Take `Bₙ = n`: it has `B₀ = 0`
and (a)–(c), but no distribution has `Aₙ = n`, since `∂Aₙ = ∫_{Aₙ}^∞ (1 − F) → 0` for every
distribution of finite mean. The printed proof starts its induction at `A₀ = B₀` and never shows
`A₁(G) = B₁`; its `G` has `E G = B₁ − lim ∂Bₙ`. The hypothesis is therefore also necessary, and
with it the printed construction proves the lemma.

**Formalization Note.** `G` is in the standing class (`IsDist`: probability measure on `[0, ∞)` with
finite mean). The same `G` serves every `n` ("Furthermore" refers to it). The series is summed in
`[0, ∞]`; under (a)–(b) its terms are nonnegative, so `ENNReal.ofReal` does not change them. -/
theorem lemma_3 (B : ℕ → ℝ) (hB0 : B 0 = 0) (ha : PropA B) (hb : PropB B) (hc : PropC B)
    (hlim : Tendsto (dS B) atTop (𝓝 0)) :
    ∃ G : Measure ℝ, IsDist G ∧ (∀ n : ℕ, dpW G n = B n) ∧
      ∀ n : ℕ, Mval G n = ∑' j : ℕ,
        ENNReal.ofReal ((1 - (dS B (j + 1) / dS B j) ^ n) * dS B j) := by sorry

end CompetitionComplexity
