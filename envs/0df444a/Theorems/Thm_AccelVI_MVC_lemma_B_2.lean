-- Prove2me | Theorems.Thm_AccelVI_MVC_lemma_B_2
-- name    : AccelVI.MVC.lemma_B_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:00:53.672142+00:00
-- url     : https://prove2.me/theorems/d1fe570d-db5e-455a-8b8f-47838f380ecf
-- title:
--   Lemma B.2, p. 21 — for a reversible policy chain, ρ(B_π) = (1 − √(1/κ))/(1 + √(1/κ)) (printed (1 − √κ)/(1 + √κ))
-- statement:
--   Let $(S, A, P, r, \lambda)$ be a valid finite MDP and $\pi$ a policy whose transition matrix $L_\pi$ defines an irreducible, reversible Markov chain, and let $B_\pi$ be the matrix of App. B built with the constant step sizes (4.2). With $\kappa = (1+\lambda)/(1-\lambda)$, the spectral radius of $B_\pi$ is
--   $$\rho(B_\pi) = \frac{1 - \sqrt{1/\kappa}}{1 + \sqrt{1/\kappa}} .$$
--
--   Together with Lemma B.1 this gives the linear convergence rate of Momentum Value Computation in Theorem 5.5.
--
--   **Formalization Note.** The lemma prints $\rho(B_\pi) = (1-\sqrt{\kappa})/(1+\sqrt{\kappa})$, which is negative since $\kappa > 1$ and so cannot be a spectral radius; the proof's final display computes $\lambda/(1+\sqrt{1-\lambda^2}) = (1-\sqrt{1/\kappa})/(1+\sqrt{1/\kappa})$, the rate of Theorem 5.5, which is the value stated. The spectral radius is that of the complexified matrix over $\mathbb{C}$, an extended nonnegative real compared with the (positive) rate.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 21, Lemma B.2 (constant corrected per its proof, p. 22)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_MVC_Setting

namespace AccelVI.MVC

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- Lemma B.2, p. 21 (with the rate (1 − √(1/κ))/(1 + √(1/κ)) of its proof for the printed
(1 − √κ)/(1 + √κ)): if π defines an irreducible, reversible Markov chain, then for step sizes (4.2)
ρ(B_π) = (1 − √(1/κ))/(1 + √(1/κ)). -/
theorem lemma_B_2 (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hpol : IsPolicy pol)
    (hrev : AccelVI.AVC.IsReversible (LPol M pol)) :
    spectralRadius ℂ ((Bpol M pol).map (algebraMap ℝ ℂ)) = ENNReal.ofReal (rateMVC M.lam) := by sorry

end AccelVI.MVC
