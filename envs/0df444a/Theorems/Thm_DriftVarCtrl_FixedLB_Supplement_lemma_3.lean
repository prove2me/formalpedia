-- Prove2me | Theorems.Thm_DriftVarCtrl_FixedLB_Supplement_lemma_3
-- name    : DriftVarCtrl.FixedLB.Supplement.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:41:15.488071+00:00
-- url     : https://prove2.me/theorems/39eaa22d-a0e4-4aa4-9870-fde1cdbbe033
-- title:
--   Lemma 3, p. 22 — the upper curve (28) starts at 0 with slope μ₂/μ₁, tends to slope σ₂²/σ₁², and is strictly concave
-- statement:
--   Let $\hat h_2(h_1)=\frac{\mu_2}{\mu_1}h_1\Bigl[1+\frac{v_2-v_1}{v_2}LW\bigl(-e^{-1-\frac{(-M)\mu_1v_1}{h_1}}\bigr)\Bigr]$ be the upper curve (28), a function of $h_1>0$. Then
--   $$\lim_{h_1\to0^+}\hat h_2(h_1)=0,\qquad \lim_{h_1\to0^+}\frac{d\hat h_2}{dh_1}=\frac{\mu_2}{\mu_1},\qquad \lim_{h_1\to\infty}\frac{d\hat h_2}{dh_1}=\frac{\sigma_2^2}{\sigma_1^2},$$
--   and $\dfrac{d^2\hat h_2}{dh_1^2}(h_1)<0$ for every $h_1\in(0,\infty)$.
--
--   So the curve separating "always use 1" from "use 1 then 2" is increasing and concave, between the slopes $\mu_2/\mu_1$ and $\sigma_2^2/\sigma_1^2$; the proof of Theorem 3 (c) uses that it is upward sloping.
--
--   **Formalization Note** Derivatives are Lean's `deriv`; the stated limits and the strict sign cannot hold through its junk value $0$ at a point of non-differentiability, since $\mu_2/\mu_1\ne0$. The standing $v_1<v_2$ of p. 12 is a hypothesis.
--
--   Differences from the source:
--
--   - encoding: LW is the Lambert W function on [−1/e, ∞) → LiquidWelfareFPA.lambertW, the principal branch (the unique y ≥ −1 with ye^y = x), with the value 0 below −1/e; reason: the argument −e^{−1−(−M)μ₁v₁/h₁} lies in (−1/e, 0) for h₁ > 0, so the junk value is never evaluated
--   - encoding: dĥ₂/dh₁ and d²ĥ₂/dh₁² → deriv (upperCurve p) and deriv (deriv (upperCurve p)); reason: ĥ₂ is smooth on (0, ∞); deriv agrees with the classical derivative there
-- source:
--   Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. 22, Lemma 3, (30)–(32) (proof p. EC-30, (190)–(191))

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_Thresholds

namespace DriftVarCtrl.FixedLB.Supplement

open DriftVarCtrl.FixedLB Filter
open scoped Topology

/-- Lemma 3 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. 22, (30)–(32); proof p. EC-30). The upper curve (28),
`ĥ₂(h₁) = (μ₂/μ₁) h₁ [1 + ((v₂ − v₁)/v₂) LW(−e^{−1−(−M)μ₁v₁/h₁})]`, satisfies
`ĥ₂(h₁) → 0` and `ĥ₂′(h₁) → μ₂/μ₁` as `h₁ → 0+`, `ĥ₂′(h₁) → σ₂²/σ₁²` as `h₁ → ∞`, and
`ĥ₂″(h₁) < 0` for every `h₁ ∈ (0, ∞)`.

Formalization Note: `ĥ₂` is `upperCurve p`, a function of `h₁` alone (it does not involve the
running costs of `p` or `U`); derivatives are `deriv`. The standing `v₁ < v₂` is `hv`. -/
theorem lemma_3 (p : Params) (hv : v p .one < v p .two) :
    Tendsto (upperCurve p) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (deriv (upperCurve p)) (𝓝[>] 0) (𝓝 (p.μ₂ / p.μ₁)) ∧
    Tendsto (deriv (upperCurve p)) atTop (𝓝 (p.σ₂ ^ 2 / p.σ₁ ^ 2)) ∧
    ∀ h₁ : ℝ, 0 < h₁ → deriv (deriv (upperCurve p)) h₁ < 0 := by sorry

end DriftVarCtrl.FixedLB.Supplement
