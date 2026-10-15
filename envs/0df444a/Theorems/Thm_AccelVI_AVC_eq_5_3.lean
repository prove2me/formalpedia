-- Prove2me | Theorems.Thm_AccelVI_AVC_eq_5_3
-- name    : AccelVI.AVC.eq_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:06.814169+00:00
-- url     : https://prove2.me/theorems/d97788f0-8a51-448a-958d-00c13f565213
-- title:
--   (5.3), p. 8 — every eigenvalue ω of B_π solves ω² − (μ+1)(1 − √(1/κ))ω + ½(μ+1)(1 − √(1/κ))² = 0 for some μ ∈ Sp(L_π)
-- statement:
--   Let $(\mathbb S,\mathbb A,P,r,\lambda)$ be a finite MDP with $\lambda\in(0,1)$, $\pi$ a policy with transition matrix $L_\pi$, $\kappa=(1+\lambda)/(1-\lambda)$, and $B_\pi$ the matrix (5.1). For every complex eigenvalue $\omega$ of $B_\pi$ there is a complex eigenvalue $\mu$ of $L_\pi$ such that
--   $$\omega^2-(\mu+1)\big(1-\sqrt{1/\kappa}\big)\,\omega+\tfrac12(\mu+1)\big(1-\sqrt{1/\kappa}\big)^2=0.$$
--
--   The equation ties the spectrum of $B_\pi$ to that of $L_\pi$; its two roots $\omega^\pm(\mu)$ are the candidates for the leading eigenvalue of $B_\pi$. No reversibility is needed.
--
--   **Formalization Note.** Both spectra are taken over $\mathbb C$ (the matrices are real, their eigenvalues need not be).
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 8, proof of Lemma 5.3, display (5.3)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_AVC_Setting

namespace AccelVI.AVC

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- (5.3), p. 8 (proof of Lemma 5.3): every complex eigenvalue `ω` of `B_π` satisfies
`ω² − (μ + 1)(1 − √(1/κ))ω + ½(μ + 1)(1 − √(1/κ))² = 0` for some eigenvalue `μ` of `L_π`. -/
theorem eq_5_3 (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hpol : FoundationsML.ReinforcementLearning.IsPolicy pol) :
    ∀ ω ∈ spectrum ℂ ((Bpol M pol).map (algebraMap ℝ ℂ)),
      ∃ μ ∈ spectrum ℂ ((LPol M pol).map (algebraMap ℝ ℂ)),
        ω ^ 2 - (μ + 1) * (theta M.lam : ℂ) * ω + 1 / 2 * (μ + 1) * (theta M.lam : ℂ) ^ 2 = 0 := by sorry

end AccelVI.AVC
