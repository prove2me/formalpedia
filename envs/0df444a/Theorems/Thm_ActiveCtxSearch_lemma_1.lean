-- Prove2me | Theorems.Thm_ActiveCtxSearch_lemma_1
-- name    : ActiveCtxSearch.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:41:37.561504+00:00
-- url     : https://prove2.me/theorems/b6a1c32b-9eee-421d-8342-1f46e8828cb8
-- title:
--   Lemma 1 (corrected: $d$ large depending on $\theta$) — the balancing intercept is $O(1/\sqrt d)$
-- statement:
--   There is a dimension threshold $d_0$, depending only on $\theta=(B,c_x,C_x,c_\xi,C_\xi)$, such that for every $d\ge\max(2,d_0)$ and every instance satisfying (A1)–(A3) with these constants, $\beta^*=b^*+\mu^*$ satisfies
--   $$\frac{|\beta^*|}{\|w^*\|_2}\le\sqrt{\frac{2\ln\!\big(100\,C_xC_\xi/(c_xc_\xi)\big)}{d-1}}.$$
--
--   Here $b^*$ is the label-balancing action. The lemma says that the action which balances the labels is close to the intercept, at the scale $1/\sqrt d$ of a typical projection of a context; Theorem 1 uses it to show that the margin-based learner is run at an action whose Bayes intercept is within its constraint $|\beta|\le\beta_0$.
--
--   Differences from the source:
--   - correction: d ≥ 2 → d ≥ max(2, d₀) with d₀ depending only on θ; reason: the printed lemma fails when ‖w*‖₂ is large compared with d: d = 60, w* = 10⁶e₁, μ* = 0, P_X = P_U, c_ξ = 0.01, C_ξ = 1/4, f_ξ = 1/(4‖w*‖₂) on [−2‖w*‖₂, 0] and c_ξ/‖w*‖₂ on [0, 2] (rest of the mass far right) satisfy (A1)–(A3) with B = 10⁶ and give |β*|/‖w*‖₂ ≈ 0.530 > 0.515; the proof's step (7) needs ‖w*‖₂-scaled noise bounds on a window of width ≈ 1/√(d−1); d₀(θ) is the source's 'd sufficiently large' convention (p.7)
--   - reading: ℘(b) = Pr_x[v(x) ≥ b] and b* with Pr_x[v(x) ≥ b*] = 1/2 (pp.10–12, 17–18) → ℘(b) = Pr_{x,ξ}[v(x) + ξ ≥ b] and b* its 1/2-point; reason: Figure 2 (p.11), the proofs of Lemmas 1 and 4 and the quantity Algorithm 2 estimates all use the label probability
--   - encoding: |β*|/‖w*‖₂ ≤ … = O(1/√d) → the explicit bound only; reason: O(1/√d) is a consequence of the explicit bound for fixed θ
-- source:
--   Chen, Liu & Wang, Active Learning for Contextual Search with Binary Feedback, arXiv:2110.01072v2, §3.1, Lemma 1, p.12 (proof §4.1.1, pp.16–17)

import Mathlib
import Definitions.Def_ActiveCtxSearch_Errors

open MeasureTheory

namespace ActiveCtxSearch

/-- **Lemma 1** (corrected: for `d` large depending on `θ`), Chen, Liu & Wang, arXiv:2110.01072v2,
p.12. There is `d₀`, depending only on `θ = (B, c_x, C_x, c_ξ, C_ξ)`, such that for every `d ≥ max(2, d₀)`
and every instance satisfying (A1)–(A3), `β* = b* + μ*` satisfies
`|β*|/‖w*‖₂ ≤ √(2 ln(100 C_x C_ξ/(c_x c_ξ))/(d − 1))`.

**Formalization Note** `b*` is the label-balancing action (`Problem.bStar`). The printed lemma assumes
only `d ≥ 2`; it fails when `‖w*‖₂` is large compared with `d` (`d = 60`, `w* = 10⁶ e₁`, `μ* = 0`,
`P_X = P_U`, `c_ξ = 0.01`, `C_ξ = 1/4`, `f_ξ = 1/(4‖w*‖)` on `[−2‖w*‖, 0]`, `c_ξ/‖w*‖` on `[0, 2]`, the rest
of the mass far to the right: `|β*|/‖w*‖ ≈ 0.530 > 0.515`). The threshold `d₀(θ)` is the source's
"`d` sufficiently large" convention (p.7). -/
theorem lemma_1 (θ : Params) :
    ∃ d₀ : ℕ, ∀ d : ℕ, 2 ≤ d → d₀ ≤ d → ∀ I : Problem d, Assumptions θ I →
      |I.bStar + I.μ| / ‖I.w‖ ≤
        Real.sqrt (2 * Real.log (100 * θ.Cx * θ.Cξ / (θ.cx * θ.cξ)) / ((d : ℝ) - 1)) := by sorry

end ActiveCtxSearch
