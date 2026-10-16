-- Prove2me | Theorems.Thm_AccelVI_MVC_rate_identity
-- name    : AccelVI.MVC.rate_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:00:32.03798+00:00
-- url     : https://prove2.me/theorems/988aecf2-9af7-417b-8c51-3b2d2fb40268
-- title:
--   Proof of Lemma B.2, p. 22 — λ/(1 + √(1 − λ²)) = (√(1+λ) − √(1−λ))/(√(1+λ) + √(1−λ)) = (1 − √(1/κ))/(1 + √(1/κ))
-- statement:
--   Let $\lambda \in (0,1)$ and $\kappa = (1+\lambda)/(1-\lambda)$. Then
--   $$\frac{\lambda}{1 + \sqrt{1-\lambda^2}} = \frac{\sqrt{1+\lambda} - \sqrt{1-\lambda}}{\sqrt{1+\lambda} + \sqrt{1-\lambda}} = \frac{1 - \sqrt{1/\kappa}}{1 + \sqrt{1/\kappa}} .$$
--
--   This identifies the common modulus of the eigenvalues of $B_\pi$ with the rate of Theorem 5.5.
--
--   **Formalization Note.** The page's display prints $\lambda/(1+\sqrt{1-\lambda})^2$ in the first term, $\sqrt{1\lambda}$ for $\sqrt{1-\lambda}$ in the second, and ends with $(1-\sqrt{\kappa})/(1+\sqrt{\kappa})$, which is negative because $\kappa > 1$. The statement uses the values the proof needs: the constant of (B.2)–(B.3) and the rate of Theorem 5.5.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 22, proof of Lemma B.2, second display (corrected)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_MVC_Setting

namespace AccelVI.MVC

/-- Proof of Lemma B.2, p. 22, second display (with the corrected constants):
λ/(1 + √(1 − λ²)) = (√(1 + λ) − √(1 − λ))/(√(1 + λ) + √(1 − λ)) = (1 − √(1/κ))/(1 + √(1/κ)). -/
theorem rate_identity (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    lam / (1 + Real.sqrt (1 - lam ^ 2))
        = (Real.sqrt (1 + lam) - Real.sqrt (1 - lam)) / (Real.sqrt (1 + lam) + Real.sqrt (1 - lam)) ∧
      (Real.sqrt (1 + lam) - Real.sqrt (1 - lam)) / (Real.sqrt (1 + lam) + Real.sqrt (1 - lam))
        = rateMVC lam := by sorry

end AccelVI.MVC
