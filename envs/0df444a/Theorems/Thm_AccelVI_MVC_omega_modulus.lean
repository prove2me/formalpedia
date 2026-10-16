-- Prove2me | Theorems.Thm_AccelVI_MVC_omega_modulus
-- name    : AccelVI.MVC.omega_modulus
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:45.894978+00:00
-- url     : https://prove2.me/theorems/3b49a532-0571-4de6-bcab-9a1a5f53c68d
-- title:
--   Proof of Lemma B.2, p. 22 — |ω±(µ)| = λ/(1 + √(1 − λ²)) for µ ∈ [−1, 1] (printed √(1 − λ)²)
-- statement:
--   Let $\lambda \in (0,1)$ and $\mu \in [-1, 1]$, and let
--   $$\omega^{\pm}(\mu) = \frac{\lambda}{1 + \sqrt{1-\lambda^2}}\Big(\mu \pm i\sqrt{1-\mu^2}\Big)$$
--   be the two roots (B.2)–(B.3) of (B.1). Then
--   $$|\omega^+(\mu)| = |\omega^-(\mu)| = \frac{\lambda}{1 + \sqrt{1-\lambda^2}} .$$
--
--   Since the eigenvalues of $L_\pi$ lie in $[-1,1]$ for a reversible chain, every eigenvalue of $B_\pi$ has this same modulus.
--
--   **Formalization Note.** The page prints the constant as $\lambda/(1 + \sqrt{1-\lambda})^2$, a typesetting slip: (B.2)–(B.3) on p. 21 carry $\lambda/(1+\sqrt{1-\lambda^2})$, and only that value equals the rate of Theorem 5.5. The modulus is the complex absolute value.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 22, proof of Lemma B.2, first line (with (B.2)–(B.3), p. 21)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_MVC_Setting

namespace AccelVI.MVC

/-- Proof of Lemma B.2, p. 22, first display (with λ/(1 + √(1 − λ²)) for the printed λ/(1 + √(1 − λ)²)):
for μ ∈ [−1, 1], the roots ω^±(μ) = λ/(1 + √(1 − λ²)) · (μ ± i√(1 − μ²)) of (B.1), given in (B.2)–(B.3),
both have modulus λ/(1 + √(1 − λ²)). -/
theorem omega_modulus (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) (μ : ℝ) (hμ1 : -1 ≤ μ) (hμ2 : μ ≤ 1) :
    ‖((lam / (1 + Real.sqrt (1 - lam ^ 2)) : ℝ) : ℂ) * ((μ : ℂ) + Complex.I * (Real.sqrt (1 - μ ^ 2) : ℂ))‖
        = lam / (1 + Real.sqrt (1 - lam ^ 2)) ∧
      ‖((lam / (1 + Real.sqrt (1 - lam ^ 2)) : ℝ) : ℂ) * ((μ : ℂ) - Complex.I * (Real.sqrt (1 - μ ^ 2) : ℂ))‖
        = lam / (1 + Real.sqrt (1 - lam ^ 2)) := by sorry

end AccelVI.MVC
