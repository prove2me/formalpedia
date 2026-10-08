-- Prove2me | Theorems.Thm_BSUMM_Rand_eq_2_28
-- name    : BSUMM.Rand.eq_2_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:44.067483+00:00
-- url     : https://prove2.me/theorems/0eece42f-6947-4d09-9837-3263f5b2b015
-- title:
--   (2.28) — the constraint violation ‖q − Ex^t‖² bounded through ‖q − Ex̄^{t+1}‖ and ‖x̂^{t+1} − x^t‖
-- statement:
--   Assume Assumptions A and B. Let $\tau>0$ be a constant for which the error bound (2.4) holds, let $\hat\sigma_1,\hat\sigma_2>0$ be constants for which (2.13) holds, and set $\tilde\sigma_i^2=2\tau^2\hat\sigma_i^2$ ($i=1,2$). Let $x\in X$ be a state with dual variable $y$, $a=\alpha^t>0$ a stepsize with
--
--   $$1-2\tilde\sigma_2^2\,a^2\,\|E\|^2>0,$$
--
--   $\hat x$ the block steps (2.5) and $\hat y=y+a(q-Ex)$. If $\bar x\in X(\hat y)$ is a point of $X(\hat y)$ nearest to $x$, then
--
--   $$\|q-Ex\|^2\ \le\ \frac{2\|q-E\bar x\|^2+2\|E\|^2\tilde\sigma_1^2\,\|\hat x-x\|^2}{1-2\tilde\sigma_2^2\,a^2\,\|E\|^2}. \tag{2.28}$$
--
--   Here $\|E\|$ is the operator norm of $x\mapsto Ex$. The bound transfers the vanishing of $\|E\bar x^{t+1}-q\|$ and of the block steps to the vanishing of the constraint violation of the iterates.
--
--   **Formalization Note** In the proof of Theorem 2.1 (§2.3, p. 16), $x=x^t$, $y=y^t$, $\bar x=\bar x^{t+1}$, $\hat x=\hat x^{t+1}$. The constants $\tau,\hat\sigma_1,\hat\sigma_2$ are hypotheses ((2.4) globally on $X$ with constant $\tau$, and (2.13) at every state with constants $\hat\sigma_1,\hat\sigma_2$), and $\tilde\sigma_i^2$ is written out as $2\tau^2\hat\sigma_i^2$. The nearest point is expressed by $\|x-\bar x\|=\operatorname{dist}(x,X(\hat y))$.
-- source:
--   Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, p. 16, §2.3, proof of Theorem 2.1, (2.27)–(2.28)

import Mathlib
import Definitions.Def_BSUMM_Rand_Setting
import Definitions.Def_BSUMM_Rand_RBSUMM

open scoped RealInnerProductSpace

namespace BSUMM.Rand

/-- (2.28) (arXiv:1401.7079v1, §2.3, proof of Theorem 2.1, p. 16): with `τ` an error-bound
constant (2.4)/(2.23), `σ̂₁, σ̂₂` constants of (2.13) and `σ̃_i² = 2τ²σ̂_i²`, at every state
`x ∈ X`, `y`, stepsize `a > 0` with `1 - 2σ̃₂² a² ‖E‖² > 0`, and `x̄ ∈ X(ŷ)` nearest to `x`,
`‖q - Ex‖² ≤ (2‖q - E x̄‖² + 2‖E‖² σ̃₁² ‖x̂ - x‖²) / (1 - 2σ̃₂² a² ‖E‖²)`. -/
theorem eq_2_28 (S : Setting) (hA : S.AssumptionA) (u : S.UFun) (hB : S.AssumptionB u)
    (τ σ1 σ2 : ℝ) (hτ : 0 < τ) (hσ1 : 0 < σ1) (hσ2 : 0 < σ2)
    (hEB : S.ErrorBoundWith τ) (hPG : S.ProxGradBound u σ1 σ2)
    (x : S.Xsp) (hx : x ∈ S.Xset) (y : S.Ysp) (a : ℝ) (ha : 0 < a)
    (hsmall : 0 < 1 - 2 * (2 * τ ^ 2 * σ2 ^ 2) * a ^ 2 * ‖S.Emap‖ ^ 2)
    (xhat : S.Xsp) (hxhat : S.IsHatStep u x y xhat)
    (xbar : S.Xsp) (hxbar : xbar ∈ S.Xopt (S.dualStep x y a))
    (hnear : ‖x - xbar‖ = Metric.infDist x (S.Xopt (S.dualStep x y a))) :
    ‖S.q - S.Emap x‖ ^ 2 ≤
      (2 * ‖S.q - S.Emap xbar‖ ^ 2 + 2 * ‖S.Emap‖ ^ 2 * (2 * τ ^ 2 * σ1 ^ 2) * ‖xhat - x‖ ^ 2) /
        (1 - 2 * (2 * τ ^ 2 * σ2 ^ 2) * a ^ 2 * ‖S.Emap‖ ^ 2) := by sorry

end BSUMM.Rand
