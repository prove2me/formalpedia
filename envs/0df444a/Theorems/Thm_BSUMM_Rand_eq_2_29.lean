-- Prove2me | Theorems.Thm_BSUMM_Rand_eq_2_29
-- name    : BSUMM.Rand.eq_2_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:09.431383+00:00
-- url     : https://prove2.me/theorems/301b45a7-2a27-4b3a-abca-380f5aec6c60
-- title:
--   (2.29) — the descent estimate of Δ_p + Δ_d with explicit coefficients
-- statement:
--   Assume Assumptions A and B, let $(p_0,\dots,p_K)$ be a probability vector with all $p_k>0$, let $\tau,\hat\sigma_1,\hat\sigma_2>0$ be constants of (2.4) and (2.13), $\tilde\sigma_i^2=2\tau^2\hat\sigma_i^2$, and let $\hat\gamma>0$ be a constant for which (2.25) holds at every state. Let $x\in X$, $y$, $a=\alpha^t>0$ with $D:=1-2\tilde\sigma_2^2a^2\|E\|^2>0$, let $\hat x$ be the block steps (2.5), $\hat y=y+a(q-Ex)$, and $\bar x\in X(\hat y)$ nearest to $x$. Then
--
--   $$\mathbb E\big[(\Delta_p^{t+1}+\Delta_d^{t+1})-(\Delta_p^t+\Delta_d^t)\,\big|\,z^t\big]\ \le\ \Big(a p_0\|E\|^2\tilde\sigma_1^2+\frac{2\|E\|^4\tilde\sigma_1^2a^3p_0\tilde\sigma_2^2}{D}-\hat\gamma\Big)\|\hat x-x\|^2+\Big(\frac{2a^3p_0\|E\|^2\tilde\sigma_2^2}{D}-a p_0\Big)\|E\bar x-q\|^2. \tag{2.29}$$
--
--   For small stepsizes both coefficients are negative, which makes $\Delta_p+\Delta_d$ a nonnegative almost supermartingale along RBSUM-M.
--
--   **Formalization Note** Only the final inequality of the display (2.29) is stated (the intermediate bound with $\|q-Ex^t\|^2$ is a step of its proof). The conditional expectation is the one-step average over the random index at the state $z^t=(x,y)$; $\hat\gamma$ is a hypothesis-carrying constant ("any $\hat\gamma>0$ for which (2.25) holds"). Source: §2.3, proof of Theorem 2.1.
-- source:
--   Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, p. 16, §2.3, proof of Theorem 2.1, (2.29)

import Mathlib
import Definitions.Def_BSUMM_Rand_Setting
import Definitions.Def_BSUMM_Rand_RBSUMM

open scoped RealInnerProductSpace

namespace BSUMM.Rand

/-- (2.29) (arXiv:1401.7079v1, §2.3, proof of Theorem 2.1, p. 16), the second inequality: with
`τ`, `σ̂₁, σ̂₂` as in (2.28), `σ̃_i² = 2τ²σ̂_i²`, and `γ̂ > 0` any constant for which (2.25)
holds, at every state `x ∈ X`, `y`, stepsize `a > 0` with `D := 1 - 2σ̃₂² a² ‖E‖² > 0` and
`x̄ ∈ X(ŷ)` nearest to `x`, the one-step average of the change of `Δ_p + Δ_d` is at most
`(a p₀‖E‖²σ̃₁² + 2‖E‖⁴σ̃₁² a³ p₀ σ̃₂² / D - γ̂)‖x̂ - x‖² + (2a³p₀‖E‖²σ̃₂² / D - a p₀)‖E x̄ - q‖²`. -/
theorem eq_2_29 (S : Setting) (hA : S.AssumptionA) (u : S.UFun) (hB : S.AssumptionB u)
    (p : Fin (S.K + 1) → ℝ) (hp : S.IsProbVec p)
    (τ σ1 σ2 : ℝ) (hτ : 0 < τ) (hσ1 : 0 < σ1) (hσ2 : 0 < σ2)
    (hEB : S.ErrorBoundWith τ) (hPG : S.ProxGradBound u σ1 σ2)
    (γhat : ℝ) (hγhat : 0 < γhat)
    (h225 : ∀ x ∈ S.Xset, ∀ (y : S.Ysp) (a : ℝ) (xhat : S.Xsp), 0 < a → S.IsHatStep u x y xhat →
      ∀ xbar ∈ S.Xopt (S.dualStep x y a),
        S.condAvg p (fun x' y' => (S.DeltaP x' y' + S.DeltaD y') - (S.DeltaP x y + S.DeltaD y))
            x y a xhat ≤
          a * p 0 * ‖S.Emap x - S.Emap xbar‖ ^ 2 - a * p 0 * ‖S.Emap xbar - S.q‖ ^ 2 -
            γhat * ‖xhat - x‖ ^ 2)
    (x : S.Xsp) (hx : x ∈ S.Xset) (y : S.Ysp) (a : ℝ) (ha : 0 < a)
    (hsmall : 0 < 1 - 2 * (2 * τ ^ 2 * σ2 ^ 2) * a ^ 2 * ‖S.Emap‖ ^ 2)
    (xhat : S.Xsp) (hxhat : S.IsHatStep u x y xhat)
    (xbar : S.Xsp) (hxbar : xbar ∈ S.Xopt (S.dualStep x y a))
    (hnear : ‖x - xbar‖ = Metric.infDist x (S.Xopt (S.dualStep x y a))) :
    S.condAvg p (fun x' y' => (S.DeltaP x' y' + S.DeltaD y') - (S.DeltaP x y + S.DeltaD y))
        x y a xhat ≤
      (a * p 0 * ‖S.Emap‖ ^ 2 * (2 * τ ^ 2 * σ1 ^ 2) +
          2 * ‖S.Emap‖ ^ 4 * (2 * τ ^ 2 * σ1 ^ 2) * a ^ 3 * p 0 * (2 * τ ^ 2 * σ2 ^ 2) /
            (1 - 2 * (2 * τ ^ 2 * σ2 ^ 2) * a ^ 2 * ‖S.Emap‖ ^ 2) - γhat) * ‖xhat - x‖ ^ 2 +
        (2 * a ^ 3 * p 0 * ‖S.Emap‖ ^ 2 * (2 * τ ^ 2 * σ2 ^ 2) /
            (1 - 2 * (2 * τ ^ 2 * σ2 ^ 2) * a ^ 2 * ‖S.Emap‖ ^ 2) - a * p 0) *
          ‖S.Emap xbar - S.q‖ ^ 2 := by sorry

end BSUMM.Rand
