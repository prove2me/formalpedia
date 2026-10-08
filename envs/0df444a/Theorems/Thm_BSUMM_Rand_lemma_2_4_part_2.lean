-- Prove2me | Theorems.Thm_BSUMM_Rand_lemma_2_4_part_2
-- name    : BSUMM.Rand.lemma_2_4_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:12.890633+00:00
-- url     : https://prove2.me/theorems/7c174cda-bd21-4f69-a024-a2572ab15500
-- title:
--   Lemma 2.4(2) — ‖∇̃L(x^t; ŷ^{t+1})‖ ≤ σ̂₁‖x̂^{t+1} − x^t‖ + σ̂₂‖ŷ^{t+1} − y^t‖ for RBSUM-M
-- statement:
--   Assume Assumptions A and B. There exist constants $\hat\sigma_1>0$ and $\hat\sigma_2>0$, independent of the iterates, such that for the RBSUM-M iterates and all $t\ge1$
--
--   $$\|\tilde\nabla L(x^t;\hat y^{t+1})\|\ \le\ \hat\sigma_1\,\|\hat x^{t+1}-x^t\|+\hat\sigma_2\,\|\hat y^{t+1}-y^t\|, \tag{2.13}$$
--
--   where $\hat x^{t+1}$ are the block steps (2.5) and $\hat y^{t+1}=y^t+\alpha^t(q-Ex^t)$ is the dual step (2.6), and $\tilde\nabla L$ is the proximal gradient (2.3) of the augmented Lagrangian in $x$.
--
--   Combined with the error bound (2.4), this bounds the distance of $x^t$ to $X(\hat y^{t+1})$ by the size of the block steps and of the dual step.
--
--   **Formalization Note** The bound is stated for every state $x\in X$, $y$ and stepsize $a>0$ (every iterate is such a state), with $\tilde\nabla L(x;\hat y)=x-p$ for $p$ the proximal point of $x-\nabla_x(L(x;\hat y)-h(x))$ with respect to $h+\iota_X$. The page's (2.3) prints the prox of $h$ alone; its proof at (2.14) uses the prox that includes $X_k$, which is the reading adopted throughout the mission.
-- source:
--   Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, p. 11, Lemma 2.4 (2.13)

import Mathlib
import Definitions.Def_BSUMM_Rand_Setting
import Definitions.Def_BSUMM_Rand_RBSUMM

open scoped RealInnerProductSpace

namespace BSUMM.Rand

/-- Lemma 2.4(2) (arXiv:1401.7079v1, p. 11, (2.13)): there are constants `σ̂₁, σ̂₂ > 0`,
independent of the state, such that at every state `x ∈ X`, `y`, every stepsize `a > 0`,
`‖∇̃L(x; ŷ)‖ ≤ σ̂₁ ‖x̂ - x‖ + σ̂₂ ‖ŷ - y‖`, where `x̂` are the block steps (2.5), `ŷ = y + a(q - Ex)`
and the proximal gradient is taken with the prox of `h + ι_X` (see `Setting.ProxGradBound`). -/
theorem lemma_2_4_part_2 (S : Setting) (hA : S.AssumptionA) (u : S.UFun)
    (hB : S.AssumptionB u) :
    ∃ σ1 : ℝ, 0 < σ1 ∧ ∃ σ2 : ℝ, 0 < σ2 ∧ S.ProxGradBound u σ1 σ2 := by sorry

end BSUMM.Rand
