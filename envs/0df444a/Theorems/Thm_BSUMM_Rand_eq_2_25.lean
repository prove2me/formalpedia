-- Prove2me | Theorems.Thm_BSUMM_Rand_eq_2_25
-- name    : BSUMM.Rand.eq_2_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:32:59.958252+00:00
-- url     : https://prove2.me/theorems/f89bca8f-6243-43b6-9030-187a1bae8e3b
-- title:
--   (2.24)–(2.25) — expected change of the potential Δ_p + Δ_d along RBSUM-M
-- statement:
--   Assume Assumptions A and B, and let $(p_0,\dots,p_K)$ be a probability vector with all $p_k>0$. There is $\hat\gamma>0$, independent of the iterates, such that for RBSUM-M
--
--   $$\mathbb E\big[\Delta_p^{t+1}+\Delta_d^{t+1}\,\big|\,z^t\big]-\big(\Delta_p^t+\Delta_d^t\big)\ \le\ \alpha^tp_0\,\|Ex^t-E\bar x^{t+1}\|^2-\alpha^tp_0\,\|E\bar x^{t+1}-q\|^2-\hat\gamma\,\|\hat x^{t+1}-x^t\|^2 \tag{2.25}$$
--
--   for every $\bar x^{t+1}\in X(\hat y^{t+1})$, $\hat y^{t+1}=y^t+\alpha^t(q-Ex^t)$.
--
--   This is the supermartingale-type estimate for the potential $\Delta_p+\Delta_d$ from which the almost-sure convergence of RBSUM-M is derived, once the first term is controlled by the error bound.
--
--   **Formalization Note** Stated at an arbitrary state $x\in X$, $y$, stepsize $a=\alpha^t>0$, with the conditional expectation written as the one-step average over the random index of the change $(\Delta_p+\Delta_d)(z^{t+1})-(\Delta_p+\Delta_d)(z^t)$; since $\sum_kp_k=1$ this equals the left side of (2.24). Source: §2.3, proof of Theorem 2.1.
-- source:
--   Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, p. 15, §2.3, proof of Theorem 2.1, (2.24)–(2.25)

import Mathlib
import Definitions.Def_BSUMM_Rand_Setting
import Definitions.Def_BSUMM_Rand_RBSUMM

open scoped RealInnerProductSpace

namespace BSUMM.Rand

/-- (2.24)–(2.25) (arXiv:1401.7079v1, §2.3, proof of Theorem 2.1, p. 15), in operator form: for the
potential `Δ_p + Δ_d`, the one-step average of `(Δ_p^{t+1} + Δ_d^{t+1}) - (Δ_p^t + Δ_d^t)` is at most
`α^t p_0 ‖Ex^t - E x̄^{t+1}‖² - α^t p_0 ‖E x̄^{t+1} - q‖² - γ̂ ‖x̂^{t+1} - x^t‖²` for every
`x̄^{t+1} ∈ X(ŷ^{t+1})`, with `γ̂ > 0` independent of the state. -/
theorem eq_2_25 (S : Setting) (hA : S.AssumptionA) (u : S.UFun) (hB : S.AssumptionB u)
    (p : Fin (S.K + 1) → ℝ) (hp : S.IsProbVec p) :
    ∃ γhat : ℝ, 0 < γhat ∧
      ∀ x ∈ S.Xset, ∀ (y : S.Ysp) (a : ℝ) (xhat : S.Xsp), 0 < a → S.IsHatStep u x y xhat →
        ∀ xbar ∈ S.Xopt (S.dualStep x y a),
          S.condAvg p (fun x' y' => (S.DeltaP x' y' + S.DeltaD y') - (S.DeltaP x y + S.DeltaD y))
              x y a xhat ≤
            a * p 0 * ‖S.Emap x - S.Emap xbar‖ ^ 2 - a * p 0 * ‖S.Emap xbar - S.q‖ ^ 2 -
              γhat * ‖xhat - x‖ ^ 2 := by sorry

end BSUMM.Rand
