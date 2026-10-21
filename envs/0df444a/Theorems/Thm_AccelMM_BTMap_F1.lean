-- Prove2me | Theorems.Thm_AccelMM_BTMap_F1
-- name    : AccelMM.BTMap.F1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:34:05.707836+00:00
-- url     : https://prove2.me/theorems/f6916c7e-36dc-4ad3-a402-eed5027566b0
-- title:
--   §4.2, p. 12 — condition (F1): −ρ is (d(M)/2 + e^{ω}β)-smooth on W_ω
-- statement:
--   Let $\alpha\ge1$, $\beta>0$, $\omega\ge0$. The negative log-a posteriori function $f=-\rho$ is $\mu$-smooth on $W_\omega$ with
--   $$\mu=\frac{d(M)}{2}+e^{\omega}\beta,$$
--   that is, $\|\nabla f(x)-\nabla f(y)\|\le\mu\|x-y\|$ for all $x,y\in W_\omega$.
--
--   This is condition (F1) of the general framework for the Bradley–Terry MAP problem; it combines Lemma 3.4 with the bound $\lambda_n(L_M)\le2d(M)$.
-- source:
--   Vojnović, Yun & Zhou, Accelerated MM Algorithms for Ranking Scores Inference from Comparison Data, arXiv:1901.00150v3 (26 Dec 2020), p. 12, §4.2, condition (F1)

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework
import Definitions.Def_AccelMM_BTMap_Model

namespace AccelMM.BTMap

theorem F1 {n : ℕ} (d : Fin n → Fin n → ℕ) (α β ω : ℝ)
    (hα : 1 ≤ α) (hβ : 0 < β) (hω : 0 ≤ ω) :
    SmoothOn (fun w => -rho α β d w) (box ω) (degM d / 2 + Real.exp ω * β) := by sorry

end AccelMM.BTMap
