-- Prove2me | Theorems.Thm_BSUMM_Rand_lemma_2_3_part_2
-- name    : BSUMM.Rand.lemma_2_3_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:00.996122+00:00
-- url     : https://prove2.me/theorems/23586e52-0799-403c-844a-c406683f7006
-- title:
--   Lemma 2.3(2) — E[L(z^t) − L(z^{t+1}) | z^t] ≥ γ̂‖x^t − x̂^{t+1}‖² − α^t p₀‖q − Ex^t‖² for RBSUM-M
-- statement:
--   Assume Assumptions A and B, and let $(p_0,\dots,p_K)$ be a probability vector with all $p_k>0$. For RBSUM-M (1.13) there is a constant $\hat\gamma>0$, independent of $t$ and of $y^t$, such that
--
--   $$\mathbb E\big[L(z^t)-L(z^{t+1})\,\big|\,z^t\big]\ \ge\ \hat\gamma\,\|x^t-\hat x^{t+1}\|^2-\alpha^t p_0\,\|q-Ex^t\|^2, \tag{2.8}$$
--
--   where $z^t=(x^t,y^t)$, $\hat x^{t+1}$ collects the block steps (2.5) from $z^t$, and the expectation is over the random choice of the update index at iteration $t$.
--
--   A primal block update decreases the augmented Lagrangian by a strong-convexity margin, while a dual update increases it by $\alpha^t\|q-Ex^t\|^2$; averaged over the index, this is the descent estimate behind the convergence of RBSUM-M.
--
--   **Formalization Note** The conditional expectation is written as the finite average $p_0\,[L(x;y)-L(x;\hat y)]+\sum_k p_k\,[L(x;y)-L((\hat x_k,x_{-k});y)]$ at an arbitrary state $x\in X$, $y$, stepsize $a=\alpha^t>0$, with $\hat y=y+a(q-Ex)$; this is $\mathbb E[\cdot\mid z^t]$ under (1.13) because the index at iteration $t$ is independent of $z^t$ with law $p$. The constant $\hat\gamma$ is stated existentially, before the state, as on the page.
-- source:
--   Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, p. 10, Lemma 2.3 (2.8)

import Mathlib
import Definitions.Def_BSUMM_Rand_Setting
import Definitions.Def_BSUMM_Rand_RBSUMM

open scoped RealInnerProductSpace

namespace BSUMM.Rand

/-- Lemma 2.3(2) (arXiv:1401.7079v1, p. 10, (2.8)), in operator form: the one-step average over
the random index of RBSUM-M of `L(z^t) - L(z^{t+1})` is at least
`γ̂ ‖x^t - x̂^{t+1}‖² - α^t p_0 ‖q - Ex^t‖²`, with `γ̂ > 0` independent of the state, of `t`
and of `y^t`. -/
theorem lemma_2_3_part_2 (S : Setting) (hA : S.AssumptionA) (u : S.UFun) (hB : S.AssumptionB u)
    (p : Fin (S.K + 1) → ℝ) (hp : S.IsProbVec p) :
    ∃ γhat : ℝ, 0 < γhat ∧
      ∀ x ∈ S.Xset, ∀ (y : S.Ysp) (a : ℝ) (xhat : S.Xsp), 0 < a → S.IsHatStep u x y xhat →
        γhat * ‖x - xhat‖ ^ 2 - a * p 0 * ‖S.q - S.Emap x‖ ^ 2 ≤
          S.condAvg p (fun x' y' => S.Lag x y - S.Lag x' y') x y a xhat := by sorry

end BSUMM.Rand
