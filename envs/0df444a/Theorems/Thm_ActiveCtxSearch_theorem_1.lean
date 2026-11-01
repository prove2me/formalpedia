-- Prove2me | Theorems.Thm_ActiveCtxSearch_theorem_1
-- name    : ActiveCtxSearch.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:44:22.163432+00:00
-- url     : https://prove2.me/theorems/35c29630-865e-4537-ae93-6541191f6feb
-- title:
--   Theorem 1 — Algorithm 1 estimates $v$ to accuracy $\varepsilon$ with $\tilde O(d^3/\varepsilon^2)$ queries among $\tilde O(d^3/\varepsilon^3)$ contexts
-- statement:
--   Fix the constants $\theta=(B,c_x,C_x,c_\xi,C_\xi)$. There are thresholds $c_m,c_\beta>0$, and for every $A_m$ a threshold $c_n>0$, such that for all $0<a\le A$ there are $C$, $d_0$ and $\varepsilon_0>0$ with the following property. Let $d\ge d_0$, $\varepsilon\in(0,\varepsilon_0]$, $\delta\in(0,1)$, put $L=d+\ln\ln(1/\varepsilon)+\ln(1/\delta)$, and run Algorithm 1 with parameters
--   $$\kappa_m\in[c_m,A_m],\qquad\kappa_n\in[c_nL,\,AL],\qquad\kappa_\varepsilon\in[a/d,\,A/d],\qquad\beta_0\in[c_\beta/\sqrt d,\,A/\sqrt d]$$
--   (that is, $\kappa_m\asymp1$, $\kappa_n\asymp d+\log\log(1/\varepsilon)+\log(1/\delta)$, $\kappa_\varepsilon\asymp1/d$, $\beta_0\asymp1/\sqrt d$), on any instance satisfying (A1)–(A3) and with any tie-breaking rule for the arg min of Algorithm 3. Then with probability at least $1-\delta$ the algorithm halts, its estimate satisfies
--   $$|\hat v(x)-v(x)|\le\varepsilon\quad\text{for all }x\in B_2(d),$$
--   and it makes $n(\delta,\varepsilon)$ queries among $m(\delta,\varepsilon)$ contexts read, with
--   $$n(\delta,\varepsilon)\le C\,\frac{d^3\ln\!\big(d\ln(d\varepsilon^{-1})/\delta\big)\ln^2(1/\varepsilon)}{\varepsilon^2},\qquad
--   m(\delta,\varepsilon)\le C\,\frac{d^3\ln\!\big(d\ln(d\varepsilon^{-1})/\delta\big)\ln^3(1/\varepsilon)}{\varepsilon^3}.$$
--
--   This is the paper's main result: by skipping uninformative contexts, the learner reaches uniform accuracy $\varepsilon$ with order $\varepsilon^{-2}$ queries, using order $\varepsilon^{-3}$ contexts in total.
--
--   Differences from the source:
--   - reading: κ_m ≍ 1, κ_n ≍ d + log log(1/ε) + log(1/δ), κ_ε ≍ 1/d, β₀ ≍ 1/√d → every parameter in a range whose lower end is a threshold depending only on θ (for κ_n also on the upper end A_m of κ_m) and whose upper end is arbitrary; κ_ε's lower end a/d arbitrary; reason: ≍ is not defined in the source; a single parameter choice would be weaker, and arbitrarily small lower ends are false (a tiny β₀ excludes the Bayes intercept, a tiny κ_n starves Lemma 9); the proof needs κ_n ≳ κ_m²·L (Lemma 3, (21))
--   - reading: O(·), 'sufficiently small ε, sufficiently large d' → ∃ C, d₀, ε₀ depending on θ and the range constants; reason: the O-convention of p.7
--   - reading: with probability 1 − δ, for the arg min of Algorithm 3 → outer measure of the failure set under the stream law ≤ δ, for every tie-breaking rule; reason: the source does not say which minimizer is returned and an arbitrary rule need not make the event measurable; the outer measure is the stronger form
--   - encoding: the algorithm's output and its query/sample counts → an event requiring that the run halts, with its output and counters bounded; reason: a run that does not halt has no output; halting is part of the success event, so a count cannot hold vacuously
--   - encoding: log → natural logarithm; reason: inside O(·) the base only changes C
-- source:
--   Chen, Liu & Wang, Active Learning for Contextual Search with Binary Feedback, arXiv:2110.01072v2, §3.3, Theorem 1, pp.14–15 (proof §4.3, pp.23–24)

import Mathlib
import Definitions.Def_ActiveCtxSearch_MetaAlgorithm

open MeasureTheory
open scoped RealInnerProductSpace

namespace ActiveCtxSearch

/-- **Theorem 1**, Chen, Liu & Wang, arXiv:2110.01072v2, pp.14–15. Fix `θ = (B, c_x, C_x, c_ξ, C_ξ)`.
There are thresholds `c_m, c_β > 0`, and for every `A_m` a threshold `c_n > 0`, such that for all
`0 < a ≤ A` there are `C`, `d₀` and `ε₀ > 0` with the following property. Let `d ≥ d₀`, `ε ∈ (0, ε₀]`,
`δ ∈ (0, 1)`, `L = d + ln ln(1/ε) + ln(1/δ)`, and let Algorithm 1 be executed with

* `κ_m ∈ [c_m, A_m]` (`κ_m ≍ 1`), `κ_n ∈ [c_n L, A L]` (`κ_n ≍ d + log log(1/ε) + log(1/δ)`),
* `κ_ε ∈ [a/d, A/d]` (`κ_ε ≍ 1/d`), `β₀ ∈ [c_β/√d, A/√d]` (`β₀ ≍ 1/√d`),

on any instance satisfying (A1)–(A3) and with any tie-breaking rule for the arg min of Algorithm 3.
With probability at least `1 − δ`, Algorithm 1 halts, its estimate satisfies
`|v̂(x) − v(x)| ≤ ε` for all `x ∈ B₂(d)`, and it makes `n(δ, ε)` queries among `m(δ, ε)` items read, with

`n(δ, ε) ≤ C d³ ln(d ln(d ε⁻¹)/δ) ln²(1/ε)/ε²`,  `m(δ, ε) ≤ C d³ ln(d ln(d ε⁻¹)/δ) ln³(1/ε)/ε³`.

**Formalization Note** `≍` (undefined in the source) is read as: the lower end of each range is a
threshold depending only on `θ` (for `κ_n`, also on the upper end of `κ_m`, as the proof of Lemma 3
needs), and the upper end is arbitrary; the constants `C, d₀, ε₀` depend on `θ` and the range constants
(the `O`-convention of p.7). "With probability `1 − δ`" is the outer measure of the failure set under
the stream law, for every tie-breaking rule. Logarithms are natural. -/
theorem theorem_1 (θ : Params) :
    ∃ cm cβ : ℝ, 0 < cm ∧ 0 < cβ ∧ ∀ Am : ℝ, ∃ cn : ℝ, 0 < cn ∧ ∀ a A : ℝ, 0 < a → a ≤ A →
      ∃ C : ℝ, ∃ d₀ : ℕ, ∃ ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
        ∀ d : ℕ, d₀ ≤ d → ∀ ε δ : ℝ, 0 < ε → ε ≤ ε₀ → 0 < δ → δ < 1 →
        ∀ κm κn κε β₀ : ℝ, cm ≤ κm → κm ≤ Am →
          cn * ((d : ℝ) + Real.log (Real.log (1 / ε)) + Real.log (1 / δ)) ≤ κn →
          κn ≤ A * ((d : ℝ) + Real.log (Real.log (1 / ε)) + Real.log (1 / δ)) →
          a / d ≤ κε → κε ≤ A / d → cβ / Real.sqrt d ≤ β₀ → β₀ ≤ A / Real.sqrt d →
        ∀ I : Problem d, Assumptions θ I →
        ∀ sel : List (E d × ℤ) → E d × ℝ, IsERMSelection β₀ sel →
          I.streamLaw {ω | ¬ ∃ R : MetaResult d,
              I.metaAlgorithm θ.B ε δ κm κn κε sel ω = some R ∧
              (∀ x ∈ unitBall d, |(⟪x, R.what⟫ - R.μhat) - I.v x| ≤ ε) ∧
              (R.queries : ℝ) ≤ C * (d : ℝ) ^ 3 * Real.log (d * Real.log (d / ε) / δ) *
                Real.log (1 / ε) ^ 2 / ε ^ 2 ∧
              (R.items : ℝ) ≤ C * (d : ℝ) ^ 3 * Real.log (d * Real.log (d / ε) / δ) *
                Real.log (1 / ε) ^ 3 / ε ^ 3} ≤
            ENNReal.ofReal δ := by sorry

end ActiveCtxSearch
