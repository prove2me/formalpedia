-- Prove2me | Theorems.Thm_CondatPD_FB_lemma_4_3
-- name    : CondatPD.FB.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:56:40.097242+00:00
-- url     : https://prove2.me/theorems/1be9f97b-6fa1-40cf-b9e3-64d12f5a68ab
-- title:
--   Lemma 4.3 — composition of averaged operators
-- statement:
--   Let $T_1\in\mathcal A(\mathcal H,\alpha_1)$ and $T_2\in\mathcal A(\mathcal H,\alpha_2)$, where $0<\alpha_1<1$ and $0<\alpha_2\le1$. Their composition is averaged with the exact parameter
--   $$T_1\circ T_2\in\mathcal A(\mathcal H,\alpha'),\qquad \alpha'=\frac{\alpha_1+\alpha_2-2\alpha_1\alpha_2}{1-\alpha_1\alpha_2}. $$
--
--   The parameter calculation supplies the relaxation range in Lemma 4.4, including the endpoint $\alpha_2=1$.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 9, Lemma 4.3, (16)

import Mathlib
import Definitions.Def_CondatPD_FB_Setting

namespace CondatPD.FB

/-- Lemma 4.3, p. 9: composition of averaged maps. -/
theorem lemma_4_3 {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (α₁ α₂ : ℝ) (T₁ T₂ : K → K)
    (hα₁ : 0 < α₁ ∧ α₁ < 1) (hα₂ : 0 < α₂ ∧ α₂ ≤ 1)
    (hT₁ : IsAvg α₁ T₁) (hT₂ : IsAvg α₂ T₂) :
    IsAvg ((α₁ + α₂ - 2 * α₁ * α₂) / (1 - α₁ * α₂)) (T₁ ∘ T₂) := by sorry

end CondatPD.FB
