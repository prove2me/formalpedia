-- Prove2me | Theorems.Thm_ActiveCtxSearch_lemma_2
-- name    : ActiveCtxSearch.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:41:37.515284+00:00
-- url     : https://prove2.me/theorems/a90a6491-dcc1-4a71-a2c0-163dc0fbaac0
-- title:
--   Lemma 2 (corrected: clamped bracket) — the trisection search brackets $b^*$ with $O(\varepsilon_s^{-2}\log(1/(\delta_s\varepsilon_s)))$ queries
-- statement:
--   There are constants $C,\bar\varepsilon>0$, depending only on $\theta$, with the following property. For every $d\ge2$, every instance satisfying (A1)–(A3), every $\varepsilon_s\in(0,\bar\varepsilon]$ and every $\delta_s\in(0,1)$, with probability at least $1-\delta_s$ Algorithm 2, run on the item stream from its first item, halts and returns $(\hat b_1,\hat b_2)$ with
--   $$\hat b_1\le\max\big(-B,\min(b^*,B)\big)\le\hat b_2,$$
--   after at most $C\,\varepsilon_s^{-2}\ln\!\big(1/(\delta_s\varepsilon_s)\big)$ queries.
--
--   Moreover there are $C'>0$ and $d_0$ such that for $d\ge d_0$, $\varepsilon_s=0.1/\sqrt{d-1}$, $\delta_s=\delta/3$ and $\delta\in(0,1)$, the same holds with probability at least $1-\delta/3$ and at most $C'd\ln(d/\delta)$ queries.
--
--   This is the first stage of Algorithm 1: it locates the label-balancing action to accuracy $\varepsilon_s$ with few queries.
--
--   Differences from the source:
--   - correction: b̂₁ ≤ b* ≤ b̂₂ → b̂₁ ≤ max(−B, min(b*, B)) ≤ b̂₂; reason: the search never leaves [−B, B], and b* can lie outside it: d = 2, B = 1, w* = (1, 0), μ* = −1, ξ ∼ Unif[−2, 2], f_x = 1.5f_u on {x₁ ≥ 0} and 0.5f_u on {x₁ < 0} satisfy (A1)–(A3) and give b* > 1; the clamped point is b* whenever |b*| ≤ B
--   - reading: BisectionSearch(ε_s, δ_s) → Algorithm 2 (TrisectionSearch); reason: a misnaming; only Algorithm 2 is defined
--   - reading: O(ε_s⁻² log(1/δ_sε_s)) = O(d log(d/δ)) → ∃ C, ε̄ depending on θ (first form) and ∃ C′, d₀ (second form, at ε_s = 0.1/√(d−1), δ_s = δ/3); reason: the O-convention of p.7; the second form is the instantiation made in Algorithm 1
--   - reading: ℘(b) = Pr_x[v(x) ≥ b] and b* with Pr_x[v(x) ≥ b*] = 1/2 (pp.10–12, 17–18) → ℘(b) = Pr_{x,ξ}[v(x) + ξ ≥ b] and b* its 1/2-point; reason: Figure 2 (p.11), the proofs of Lemmas 1 and 4 and the quantity Algorithm 2 estimates all use the label probability
--   - reading: with probability 1 − δ_s → outer measure of the failure set under the stream law ≤ δ_s; reason: the success event of an algorithm run need not be measurable; the outer measure is the stronger form
--   - encoding: the algorithm's output and its query/sample counts → an event requiring that the run halts, with its output and counters bounded; reason: a run that does not halt has no output; halting is part of the success event, so a count cannot hold vacuously
-- source:
--   Chen, Liu & Wang, Active Learning for Contextual Search with Binary Feedback, arXiv:2110.01072v2, §3.1, Lemma 2, p.12 (proof §4.1.2, pp.17–19)

import Mathlib
import Definitions.Def_ActiveCtxSearch_Errors
import Definitions.Def_ActiveCtxSearch_Trisection

open MeasureTheory

namespace ActiveCtxSearch

/-- **Lemma 2** (corrected: bracket around `b*` clamped to `[−B, B]`), Chen, Liu & Wang,
arXiv:2110.01072v2, p.12. There are `C, ε̄ > 0`, depending only on `θ`, such that for every `d ≥ 2`,
every instance satisfying (A1)–(A3), `ε_s ∈ (0, ε̄]` and `δ_s ∈ (0, 1)`, with probability at least
`1 − δ_s` Algorithm 2 (`TrisectionSearch(ε_s, δ_s)`, started at the first item) halts and returns
`(b̂₁, b̂₂)` with `b̂₁ ≤ max(−B, min(b*, B)) ≤ b̂₂`, after at most `C ε_s⁻² ln(1/(δ_s ε_s))` queries.
Moreover there are `C′ > 0` and `d₀` such that for `d ≥ d₀`, `ε_s = 0.1/√(d − 1)` and `δ_s = δ/3`,
`δ ∈ (0, 1)`, the same holds with probability at least `1 − δ/3` with at most `C′ d ln(d/δ)` queries.

**Formalization Note** "BisectionSearch" in the source is Algorithm 2. The printed bracket
`b̂₁ ≤ b* ≤ b̂₂` fails when `b* ∉ [−B, B]` (the search never leaves `[−B, B]`): `d = 2`, `B = 1`,
`w* = (1, 0)`, `μ* = −1`, `ξ ∼ Unif[−2, 2]`, `f_x = 1.5 f_u` on `{x₁ ≥ 0}` and `0.5 f_u` on `{x₁ < 0}` give
`b* > 1`. The clamped point equals `b*` when `|b*| ≤ B`. The probability is the outer measure of the
failure set under the stream law. -/
theorem lemma_2 (θ : Params) :
    ∃ C εbar : ℝ, 0 < C ∧ 0 < εbar ∧
      (∀ d : ℕ, 2 ≤ d → ∀ I : Problem d, Assumptions θ I → ∀ εs δs : ℝ, 0 < εs → εs ≤ εbar →
        0 < δs → δs < 1 →
        I.streamLaw {ω | ¬ ∃ T : TriResult, I.trisection θ.B εs δs ω 0 = some T ∧
            T.b1 ≤ max (-θ.B) (min I.bStar θ.B) ∧ max (-θ.B) (min I.bStar θ.B) ≤ T.b2 ∧
            (T.queries : ℝ) ≤ C * εs⁻¹ ^ 2 * Real.log (1 / (δs * εs))} ≤
          ENNReal.ofReal δs) ∧
      ∃ C' : ℝ, ∃ d₀ : ℕ, 0 < C' ∧
        ∀ d : ℕ, d₀ ≤ d → ∀ I : Problem d, Assumptions θ I → ∀ δ : ℝ, 0 < δ → δ < 1 →
          I.streamLaw {ω | ¬ ∃ T : TriResult,
              I.trisection θ.B (0.1 / Real.sqrt ((d : ℝ) - 1)) (δ / 3) ω 0 = some T ∧
              T.b1 ≤ max (-θ.B) (min I.bStar θ.B) ∧ max (-θ.B) (min I.bStar θ.B) ≤ T.b2 ∧
              (T.queries : ℝ) ≤ C' * d * Real.log (d / δ)} ≤
            ENNReal.ofReal (δ / 3) := by sorry

end ActiveCtxSearch
