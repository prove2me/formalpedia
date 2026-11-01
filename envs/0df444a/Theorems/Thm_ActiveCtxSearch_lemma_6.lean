-- Prove2me | Theorems.Thm_ActiveCtxSearch_lemma_6
-- name    : ActiveCtxSearch.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:41:41.865079+00:00
-- url     : https://prove2.me/theorems/874a310b-3fa2-4f76-9227-e1b536618068
-- title:
--   Lemma 6 — small excess error forces a close intercept
-- statement:
--   For every $c>0$ there are $d_0$ and $\varepsilon_1>0$, depending only on $\theta$ and $c$, such that the following holds for every $d\ge d_0$. Let an instance satisfy (A1)–(A3), let the query point $b$ and $\beta_0$ satisfy $|\mu^*+b|/\|w^*\|_2\le\beta_0\le c/\sqrt d$, and let $\hat v(\cdot)=\langle\cdot,\hat w\rangle-\hat\beta$ with $\|\hat w\|_2=1$ and $|\hat\beta|\le\beta_0$ have excess error $\Delta\mathrm{err}_b(\hat v)\le\epsilon\le\varepsilon_1$. Then, with $\tilde\beta=(\mu^*+b)/\|w^*\|_2$,
--   $$|\hat\beta-\tilde\beta|\le 3601\sqrt\pi\,\frac{C_xC_\xi}{c_xc_\xi}\,\max\{e^{(d-1)\beta_0^2},1\}\sqrt{\epsilon}.$$
--
--   Together with Lemma 5 this shows that a classifier with small excess error is close to the normalized Bayes classifier in both direction and intercept.
--
--   Differences from the source:
--   - encoding: Δerr(v̂) = ϵ → Δerr_b(v̂) ≤ ϵ; reason: equivalent: the bound increases with ϵ and the statement is for every ϵ ≤ ε₁, so applying the equality form at ϵ′ = Δerr_b(v̂) gives the inequality form
--   - reading: §4.2 standing assumptions: 'd sufficiently large, ε_a sufficiently small', β̃ = (b + μ*)/‖w*‖₂ with |β̃| ≤ β₀ = O(1/√d) → ∀ c > 0, ∃ d₀, ε₁ depending only on θ and c, for d ≥ d₀, ϵ ≤ ε₁ and |μ* + b|/‖w*‖₂ ≤ β₀ ≤ c/√d; reason: the p.7 O-convention; the standing assumption of p.19 is Lemma 3's hypothesis with its sign corrected (β = b + μ*, p.19)
-- source:
--   Chen, Liu & Wang, Active Learning for Contextual Search with Binary Feedback, arXiv:2110.01072v2, §4.2, Lemma 6, p.20 (standing assumptions p.19)

import Mathlib
import Definitions.Def_ActiveCtxSearch_Errors

open MeasureTheory

namespace ActiveCtxSearch

/-- **Lemma 6**, Chen, Liu & Wang, arXiv:2110.01072v2, p.20, under the standing assumptions of §4.2,
p.19. For every `c > 0` there are `d₀` and `ε₁ > 0`, depending only on `θ` and `c`, such that the
following holds for `d ≥ d₀`. Let an instance satisfy (A1)–(A3), let the query point `b` and `β₀` satisfy
`|μ* + b|/‖w*‖₂ ≤ β₀ ≤ c/√d`, and let `v̂(·) = ⟨·, ŵ⟩ − β̂` with `‖ŵ‖₂ = 1` and `|β̂| ≤ β₀` have excess error
`Δerr_b(v̂) ≤ ϵ ≤ ε₁`. Then, with `β̃ = (μ* + b)/‖w*‖₂`,
`|β̂ − β̃| ≤ 3601 √π C_x C_ξ c_x⁻¹ c_ξ⁻¹ max{e^{(d−1)β₀²}, 1} √ϵ`.

**Formalization Note** The source assumes `Δerr(v̂) = ϵ`. Because the bound increases with `ϵ` and the
statement is for every `ϵ ≤ ε₁`, the `≤ ϵ` form used here is equivalent to it. -/
theorem lemma_6 (θ : Params) (c : ℝ) (hc : 0 < c) :
    ∃ d₀ : ℕ, ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ d : ℕ, d₀ ≤ d → ∀ I : Problem d, Assumptions θ I →
      ∀ b β₀ : ℝ, |I.μ + b| / ‖I.w‖ ≤ β₀ → β₀ ≤ c / Real.sqrt d →
      ∀ (w : E d) (β ϵ : ℝ), ‖w‖ = 1 → |β| ≤ β₀ → ϵ ≤ ε₁ → I.excessErr b (w, β) ≤ ϵ →
        |β - (I.μ + b) / ‖I.w‖| ≤
          3601 * Real.sqrt Real.pi * θ.Cx * θ.Cξ / (θ.cx * θ.cξ) *
            max (Real.exp (((d : ℝ) - 1) * β₀ ^ 2)) 1 * Real.sqrt ϵ := by sorry

end ActiveCtxSearch
