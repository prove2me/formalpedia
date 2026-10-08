-- Prove2me | Theorems.Thm_BSUMM_Rand_eq_2_40
-- name    : BSUMM.Rand.eq_2_40
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:35:12.245333+00:00
-- url     : https://prove2.me/theorems/15943b66-f70c-46e5-bd39-920f8d8ab120
-- title:
--   (2.40) — ‖Ex̄^{t+1} − q‖ − ‖Ex̄^t − q‖ ≤ (α^t/ρ)‖q − Ex^t‖ + (α^{t−1}/ρ)‖q − Ex^{t−1}‖ along RBSUM-M
-- statement:
--   Assume Assumption A, and let $(x^t,y^t)$ be any RBSUM-M path (1.13), for any sequence of update indices, with stepsizes $\alpha^t>0$. Write $\hat y^{s+1}=y^s+\alpha^s(q-Ex^s)$. Then for every $t\ge2$, every $\bar x^{t+1}\in X(\hat y^{t+1})$ and every $\bar x^t\in X(\hat y^t)$,
--
--   $$\|E\bar x^{t+1}-q\|-\|E\bar x^t-q\|\ \le\ \frac{\alpha^t}{\rho}\|q-Ex^t\|+\frac{\alpha^{t-1}}{\rho}\|q-Ex^{t-1}\|. \tag{2.40}$$
--
--   This controls how fast the dual gradient $\nabla d(\hat y^t)=q-E\bar x^t$ can move, which rules out oscillation of $\|E\bar x^t-q\|$ under diminishing stepsizes.
--
--   **Formalization Note** The inequality is pathwise, so it is stated for every path rather than almost surely. The page derives it from the $1/\rho$-Lipschitz bound of Lemma 2.1, which is stated on a level set $\{d\ge\eta\}$ that $\hat y^t,\hat y^{t+1}$ need not lie in; the inequality is nevertheless stated without a level-set hypothesis, as on the page. The index $t\ge2$ keeps $t-1\ge1$ inside the range where (1.13) is applied. Source: §2.3, proof of Theorem 2.1.
-- source:
--   Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, p. 18, §2.3, proof of Theorem 2.1, (2.40)

import Mathlib
import Definitions.Def_BSUMM_Rand_Setting
import Definitions.Def_BSUMM_Rand_RBSUMM

open scoped RealInnerProductSpace

namespace BSUMM.Rand

/-- (2.40) (arXiv:1401.7079v1, §2.3, proof of Theorem 2.1, p. 18), pathwise: along any RBSUM-M
path with positive stepsizes, for every `t ≥ 2`, `x̄^{t+1} ∈ X(ŷ^{t+1})` and `x̄^t ∈ X(ŷ^t)`,
where `ŷ^{s+1} = y^s + α^s(q - Ex^s)`,
`‖E x̄^{t+1} - q‖ - ‖E x̄^t - q‖ ≤ (α^t/ρ)‖q - Ex^t‖ + (α^{t-1}/ρ)‖q - Ex^{t-1}‖`. -/
theorem eq_2_40 (S : Setting) (hA : S.AssumptionA) (u : S.UFun) (α : ℕ → ℝ)
    (hα : ∀ t, 0 < α t) (κ : ℕ → Fin (S.K + 1)) (x : ℕ → S.Xsp) (y : ℕ → S.Ysp)
    (hpath : S.IsRBSUMMPath u α κ x y) (t : ℕ) (ht : 2 ≤ t)
    (xb1 : S.Xsp) (hxb1 : xb1 ∈ S.Xopt (S.dualStep (x t) (y t) (α t)))
    (xb0 : S.Xsp) (hxb0 : xb0 ∈ S.Xopt (S.dualStep (x (t - 1)) (y (t - 1)) (α (t - 1)))) :
    ‖S.Emap xb1 - S.q‖ - ‖S.Emap xb0 - S.q‖ ≤
      α t / S.ρ * ‖S.q - S.Emap (x t)‖ + α (t - 1) / S.ρ * ‖S.q - S.Emap (x (t - 1))‖ := by sorry

end BSUMM.Rand
