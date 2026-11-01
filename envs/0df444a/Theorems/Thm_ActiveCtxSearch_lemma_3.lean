-- Prove2me | Theorems.Thm_ActiveCtxSearch_lemma_3
-- name    : ActiveCtxSearch.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:42:50.615983+00:00
-- url     : https://prove2.me/theorems/47521a68-49bb-46e4-aa20-2b2894c5a90c
-- title:
--   Lemma 3 (corrected: hypothesis $|\mu^*+b|$) — margin-based active learning reaches excess error $\varepsilon_a$
-- statement:
--   Fix $\theta$ and $c_\beta>0$. There is $c_m>0$ such that for every $A_m$ there are $c_n>0$, $C$, $c$, $d_0$ and $\bar\varepsilon>0$ (depending only on $\theta$, $c_\beta$ and $A_m$) with the following property. Let $d\ge d_0$, $\varepsilon_a\in(0,\bar\varepsilon]$, $\delta_a\in(0,1)$, let an instance satisfy (A1)–(A3), and let the action $b$ and the parameters satisfy
--   $$\frac{|\mu^*+b|}{\|w^*\|_2}\le\beta_0\le\frac{c_\beta}{\sqrt d},\qquad c_m\le\kappa_m\le A_m,\qquad \kappa_n\ge c_n\big(d+\ln\ln(1/\varepsilon_a)+\ln(1/\delta_a)\big),\qquad \epsilon_0=\sqrt{\varepsilon_a}.$$
--   For every tie-breaking rule, with probability at least $1-\delta_a$, Algorithm 3 run on the item stream from its first item halts and returns $\hat v=(\hat w,\hat\beta)$ with
--
--   1. $\Delta\mathrm{err}_b(\hat v)\le\varepsilon_a$;
--   2. at most $C\kappa_nd/\varepsilon_a$ queries and at most $C(\ln(1/\varepsilon_a))^{c}\,\kappa_n\sqrt d\,e^{d\varepsilon_a}/\varepsilon_a^{3/2}$ items read.
--
--   This is the active-learning guarantee: the number of queries scales as $1/\varepsilon_a$, while the number of contexts read scales as $\varepsilon_a^{-3/2}$.
--
--   Differences from the source:
--   - correction: |μ* − b|/‖w*‖₂ ≤ β₀ → |μ* + b|/‖w*‖₂ ≤ β₀; reason: the Bayes classifier at b has intercept β = b + μ* (pp.12, 19); with w* = e₁, μ* = b = 1, P_X = P_U, ξ ∼ Unif[−2, 2] the printed hypothesis holds, η ≤ 1/4 on the ball, v*_b ≡ −1, and every (ŵ, β̂) with |β̂| ≤ β₀ < 1 has excess error bounded below
--   - reading: κ_m = Ω(1), κ_n = Ω(d + log log(1/ε_a) + log(1/δ_a)), β₀ = O(1/√d), O(·) and Õ(·) → c_m ≤ κ_m ≤ A_m with ∀ A_m; κ_n ≥ c_n(…) with c_n depending on θ and A_m; β₀ ≤ c_β/√d; constants C, d₀, ε̄ depending on θ, c_β, A_m; Õ hides (ln(1/ε_a))^c; reason: the p.7 conventions; the proof's use of Lemma 9 at (21) needs n_k ≳ κ_m²d(d + ln(k₀/δ_a))/ϵ_k, so the threshold of κ_n depends on the size of κ_m, and with κ_m unbounded the epochs degrade to passive learning
--   - reading: with probability 1 − δ, for the arg min of Algorithm 3 → outer measure of the failure set under the stream law ≤ δ, for every tie-breaking rule; reason: the source does not say which minimizer is returned and an arbitrary rule need not make the event measurable; the outer measure is the stronger form
--   - encoding: the algorithm's output and its query/sample counts → an event requiring that the run halts, with its output and counters bounded; reason: a run that does not halt has no output; halting is part of the success event, so a count cannot hold vacuously
-- source:
--   Chen, Liu & Wang, Active Learning for Contextual Search with Binary Feedback, arXiv:2110.01072v2, §3.2, Lemma 3, pp.13–14 (proof §4.2, pp.21–23)

import Mathlib
import Definitions.Def_ActiveCtxSearch_MarginAL

open MeasureTheory

namespace ActiveCtxSearch

/-- **Lemma 3** (corrected: hypothesis `|μ* + b|`), Chen, Liu & Wang, arXiv:2110.01072v2, pp.13–14.
For every `c_β > 0` there is `c_m > 0`, and for every `A_m` there are `c_n > 0`, `C`, `c`, `d₀` and `ε̄ > 0`
(depending only on `θ`, `c_β`, `A_m`), such that the following holds. Let `d ≥ d₀`, `ε_a ∈ (0, ε̄]`,
`δ_a ∈ (0, 1)`, an instance satisfying (A1)–(A3), a query point `b` and parameters with
`|μ* + b|/‖w*‖₂ ≤ β₀ ≤ c_β/√d`, `c_m ≤ κ_m ≤ A_m`, `κ_n ≥ c_n (d + ln ln(1/ε_a) + ln(1/δ_a))`, `ϵ₀ = √ε_a`,
and any tie-breaking rule for the arg min. With probability at least `1 − δ_a`, Algorithm 3 started at
the first item halts and returns `v̂ = (ŵ, β̂)` with

1. `Δerr_b(v̂) ≤ ε_a`;
2. at most `C κ_n d/ε_a` queries, and at most `C (ln(1/ε_a))^c κ_n √d e^{dε_a}/ε_a^{3/2}` items read.

**Formalization Note** The printed hypothesis `|μ* − b|/‖w*‖₂ ≤ β₀` does not bound the Bayes intercept
`β̃ = (μ* + b)/‖w*‖₂` (p.12, p.19): with `w* = e₁`, `μ* = b = 1`, `P_X = P_U`, `ξ ∼ Unif[−2, 2]` it holds,
`v*_b ≡ −1`, and every feasible `(ŵ, β̂)` has excess error bounded below. `O`, `Ω` and `Õ` follow p.7: the
constants depend on `θ` and the constants of the parameter ranges, and `Õ` hides a factor `(ln(1/ε_a))^c`.
The threshold of `κ_n` may depend on the upper end `A_m` of `κ_m` (the proof's use of Lemma 9 at (21)
needs `n_k ≳ κ_m² d (d + ln(k₀/δ_a))/ϵ_k`). The probability is the outer measure of the failure set. -/
theorem lemma_3 (θ : Params) (cβ : ℝ) (hcβ : 0 < cβ) :
    ∃ cm : ℝ, 0 < cm ∧ ∀ Am : ℝ, ∃ cn C c : ℝ, ∃ d₀ : ℕ, ∃ εbar : ℝ,
      0 < cn ∧ 0 < C ∧ 0 < εbar ∧
      ∀ d : ℕ, d₀ ≤ d → ∀ εa δa : ℝ, 0 < εa → εa ≤ εbar → 0 < δa → δa < 1 →
      ∀ I : Problem d, Assumptions θ I → ∀ b β₀ κm κn : ℝ,
        |I.μ + b| / ‖I.w‖ ≤ β₀ → β₀ ≤ cβ / Real.sqrt d → cm ≤ κm → κm ≤ Am →
        cn * ((d : ℝ) + Real.log (Real.log (1 / εa)) + Real.log (1 / δa)) ≤ κn →
        ∀ sel : List (E d × ℤ) → E d × ℝ, IsERMSelection β₀ sel →
          I.streamLaw {ω | ¬ ∃ R : MBResult d,
              I.marginAL b εa κm κn (Real.sqrt εa) sel ω 0 = some R ∧
              I.excessErr b R.c ≤ εa ∧
              (R.queries : ℝ) ≤ C * κn * d / εa ∧
              (R.endPos : ℝ) ≤ C * Real.log (1 / εa) ^ c * κn * Real.sqrt d *
                Real.exp (d * εa) / εa ^ (3 / 2 : ℝ)} ≤
            ENNReal.ofReal δa := by sorry

end ActiveCtxSearch
