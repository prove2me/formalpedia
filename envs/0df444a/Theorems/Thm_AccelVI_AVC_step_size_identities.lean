-- Prove2me | Theorems.Thm_AccelVI_AVC_step_size_identities
-- name    : AccelVI.AVC.step_size_identities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:03.535093+00:00
-- url     : https://prove2.me/theorems/d403558c-54b3-4fe4-ae39-30c65f7ba207
-- title:
--   Proof of Lemma 5.2, p. 8 — the step sizes (4.1) give 1 + 1/κ − 2α = 0, (1−α)(1+γ) = αλ(1+γ) = 1 − √(1/κ), αγλ = (1−α)γ = α − √(1/κ) = ½(1 − √(1/κ))²
-- statement:
--   Let $\lambda\in(0,1)$, and take the step sizes (4.1) of Accelerated Value Computation,
--   $$\alpha=\frac1{1+\lambda},\qquad \gamma=\frac{1-\sqrt{1-\lambda^2}}{\lambda},$$
--   together with $\kappa=(1+\lambda)/(1-\lambda)$. Then
--
--   1. $1+1/\kappa-2\alpha=0$;
--   2. $(1-\alpha)(1+\gamma)=\alpha\lambda(1+\gamma)=1-\sqrt{1/\kappa}$;
--   3. $\alpha\gamma\lambda=(1-\alpha)\gamma=\alpha-\sqrt{1/\kappa}=\tfrac12\big(1-\sqrt{1/\kappa}\big)^2$.
--
--   These identities collapse the two-step recursion of A-VC into the block matrix $B_\pi$ of (5.1): the coefficient of $v_s$ becomes $(1-\sqrt{1/\kappa})(I+L_\pi)$ and that of $v_{s-1}$ becomes $-\tfrac12(1-\sqrt{1/\kappa})^2(I+L_\pi)$.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 8, proof of Lemma 5.2, displays after 'Recall that α = 1/(1 + λ)'

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_AVC_Setting

namespace AccelVI.AVC

/-- Proof of Lemma 5.2, p. 8: for λ ∈ (0, 1), with α = 1/(1 + λ), γ = (1 − √(1 − λ²))/λ and
κ = (1 + λ)/(1 − λ): `1 + 1/κ − 2α = 0`, `(1 − α)(1 + γ) = αλ(1 + γ) = 1 − √(1/κ)` and
`αγλ = (1 − α)γ = α − √(1/κ) = ½(1 − √(1/κ))²`. -/
theorem step_size_identities (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    1 + 1 / kappa lam - 2 * alphaAVC lam = 0 ∧
    (1 - alphaAVC lam) * (1 + gammaAVC lam) = alphaAVC lam * lam * (1 + gammaAVC lam) ∧
    alphaAVC lam * lam * (1 + gammaAVC lam) = 1 - Real.sqrt (1 / kappa lam) ∧
    alphaAVC lam * gammaAVC lam * lam = (1 - alphaAVC lam) * gammaAVC lam ∧
    (1 - alphaAVC lam) * gammaAVC lam = alphaAVC lam - Real.sqrt (1 / kappa lam) ∧
    alphaAVC lam - Real.sqrt (1 / kappa lam) = 1 / 2 * (1 - Real.sqrt (1 / kappa lam)) ^ 2 := by sorry

end AccelVI.AVC
