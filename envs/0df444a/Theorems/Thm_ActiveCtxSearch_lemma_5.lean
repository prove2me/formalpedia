-- Prove2me | Theorems.Thm_ActiveCtxSearch_lemma_5
-- name    : ActiveCtxSearch.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:41:50.776958+00:00
-- url     : https://prove2.me/theorems/393671ed-2448-4a6a-a6f8-027bf5653e3b
-- title:
--   Lemma 5 (corrected: constant $49(c_xc_\xi)^{-1/2}d^{1/4}e^{(d-2)\beta_0^2}$) — small excess error forces a small angle
-- statement:
--   For every $c>0$ there are $d_0$ and $\varepsilon_1>0$, depending only on $\theta$ and $c$, such that the following holds for every $d\ge d_0$. Let an instance satisfy (A1)–(A3), let the query point $b$ and the constraint level $\beta_0$ satisfy
--   $$\frac{|\mu^*+b|}{\|w^*\|_2}\le\beta_0\le\frac{c}{\sqrt d},$$
--   and let $\hat v(\cdot)=\langle\cdot,\hat w\rangle-\hat\beta$ with $\|\hat w\|_2=1$ have excess error $\Delta\mathrm{err}_b(\hat v)\le\epsilon\le\varepsilon_1$. Then the angle $\theta(\hat w,\tilde w^*)$ between $\hat w$ and $\tilde w^*=w^*/\|w^*\|_2$ is acute and
--   $$\tan\theta(\hat w,\tilde w^*)\le\frac{49}{\sqrt{c_xc_\xi}}\,d^{1/4}\,e^{(d-2)\beta_0^2}\sqrt{\epsilon}.$$
--
--   Lemma 5 converts excess error into a bound on the direction of the learned hyperplane; with Lemma 6 it fixes the width of the margin around which Algorithm 3 queries.
--
--   Differences from the source:
--   - correction: tan θ(ŵ, w̃*) ≤ 23e^{(d−2)β₀²/2}√ϵ → tan θ(ŵ, w̃*) ≤ 49(c_xc_ξ)^{−1/2}d^{1/4}e^{(d−2)β₀²}√ϵ; reason: the printed bound fails for all large d: P_X = P_U, w* = e₁, μ* = b = 0, ξ ∼ Unif[−2, 2], ŵ = (cos t, sin t, 0, …), β̂ = 0 give tan t/√Δerr → ≈ 3.2d^{1/4} (31.7 at d = 10⁴, 100.1 at d = 10⁶), while 23e^{(d−2)β₀²/2} stays bounded for β₀ = c/√d; the proof's (14) drops the width r/2 of the region Ω and the factor c_xc_ξ, and restoring them with the corrected Lemma 8 gives Δerr ≥ c_xc_ξe^{−3/8}e^{−2(d−2)β₀²}tan²θ/(512π√d)
--   - encoding: tan θ(ŵ, w̃*) ≤ … → ⟨ŵ, w̃*⟩ > 0 and tan θ(ŵ, w̃*) ≤ …; reason: the source's θ is acute (its proof takes tan θ ≤ 1); Lean's tan is ≤ 0 on [π/2, π], so acuteness is stated to keep the bound meaningful
--   - reading: §4.2 standing assumptions: 'd sufficiently large, ε_a sufficiently small', β̃ = (b + μ*)/‖w*‖₂ with |β̃| ≤ β₀ = O(1/√d) → ∀ c > 0, ∃ d₀, ε₁ depending only on θ and c, for d ≥ d₀, ϵ ≤ ε₁ and |μ* + b|/‖w*‖₂ ≤ β₀ ≤ c/√d; reason: the p.7 O-convention; the standing assumption of p.19 is Lemma 3's hypothesis with its sign corrected (β = b + μ*, p.19)
-- source:
--   Chen, Liu & Wang, Active Learning for Contextual Search with Binary Feedback, arXiv:2110.01072v2, §4.2, Lemma 5, p.19 (standing assumptions p.19)

import Mathlib
import Definitions.Def_ActiveCtxSearch_Errors

open MeasureTheory
open scoped RealInnerProductSpace

namespace ActiveCtxSearch

/-- **Lemma 5** (corrected: constant `49 (c_x c_ξ)^{−1/2} d^{1/4} e^{(d−2)β₀²}`), Chen, Liu & Wang,
arXiv:2110.01072v2, p.19, under the standing assumptions of §4.2, p.19. For every `c > 0` there are
`d₀` and `ε₁ > 0`, depending only on `θ` and `c`, such that the following holds for `d ≥ d₀`. Let an
instance satisfy (A1)–(A3), let the query point `b` and `β₀` satisfy `|μ* + b|/‖w*‖₂ ≤ β₀ ≤ c/√d`, and let
`v̂(·) = ⟨·, ŵ⟩ − β̂` with `‖ŵ‖₂ = 1` have excess error `Δerr_b(v̂) ≤ ϵ ≤ ε₁`. Then the angle `θ(ŵ, w̃*)`
between `ŵ` and `w̃* = w*/‖w*‖₂` is acute and
`tan θ(ŵ, w̃*) ≤ 49 (c_x c_ξ)^{−1/2} d^{1/4} e^{(d−2)β₀²} √ϵ`.

**Formalization Note** The printed bound `23 e^{(d−2)β₀²/2} √ϵ` fails for all large `d`: with
`P_X = P_U`, `w* = e₁`, `μ* = b = 0`, `ξ ∼ Unif[−2, 2]`, `ŵ = (cos θ, sin θ, 0, …)`, `β̂ = 0`, the ratio
`tan θ/√Δerr` tends to `≈ 3.2 d^{1/4}` as `θ → 0` (31.7 at `d = 10⁴`). The proof's (14) drops the width
`r/2` of the region `Ω` and the factor `c_x c_ξ`; restoring them, with the corrected Lemma 8, gives the
constant used. "`d` sufficiently large, `ε_a` sufficiently small, `|β̃| ≤ β₀ = O(1/√d)`" are the §4.2
standing assumptions, with `β̃ = (b + μ*)/‖w*‖₂`. The acuteness clause states what `tan θ ≤ …` means in the
source; Lean's `tan` is `≤ 0` for angles in `[π/2, π]`. -/
theorem lemma_5 (θ : Params) (c : ℝ) (hc : 0 < c) :
    ∃ d₀ : ℕ, ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ d : ℕ, d₀ ≤ d → ∀ I : Problem d, Assumptions θ I →
      ∀ b β₀ : ℝ, |I.μ + b| / ‖I.w‖ ≤ β₀ → β₀ ≤ c / Real.sqrt d →
      ∀ (w : E d) (β ϵ : ℝ), ‖w‖ = 1 → ϵ ≤ ε₁ → I.excessErr b (w, β) ≤ ϵ →
        0 < ⟪w, ‖I.w‖⁻¹ • I.w⟫ ∧
          Real.tan (InnerProductGeometry.angle w (‖I.w‖⁻¹ • I.w)) ≤
            49 / Real.sqrt (θ.cx * θ.cξ) * (d : ℝ) ^ (1 / 4 : ℝ) *
              Real.exp (((d : ℝ) - 2) * β₀ ^ 2) * Real.sqrt ϵ := by sorry

end ActiveCtxSearch
