-- Prove2me | Theorems.Thm_AccelVI_MVC_eq_B_1
-- name    : AccelVI.MVC.eq_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:05.607523+00:00
-- url     : https://prove2.me/theorems/1c8a7bc9-9b8f-462f-8887-07badc85f2f1
-- title:
--   (B.1), p. 21 — every eigenvalue ω of B_π solves ω² − 2λµω/(1 + √(1 − λ²)) + (1 − √(1 − λ²))/(1 + √(1 − λ²)) = 0 for an eigenvalue µ of L_π
-- statement:
--   Let $(S, A, P, r, \lambda)$ be a valid finite MDP and $\pi$ a policy, and let $B_\pi$ be the matrix of App. B built with the step sizes (4.2). For every (complex) eigenvalue $\omega$ of $B_\pi$ there is an eigenvalue $\mu$ of $L_\pi$ such that
--   $$\omega^2 - \frac{2\lambda\mu}{1 + \sqrt{1-\lambda^2}}\,\omega + \frac{1 - \sqrt{1-\lambda^2}}{1 + \sqrt{1-\lambda^2}} = 0. \tag{B.1}$$
--
--   So the spectrum of $B_\pi$ is determined by that of $L_\pi$, each $\mu$ contributing at most two eigenvalues of $B_\pi$.
--
--   **Formalization Note.** The paper states that to every eigenvalue $\mu$ of $L_\pi$ correspond at most two eigenvalues of $B_\pi$ satisfying (B.1); the formal statement records the direction the proof of Lemma B.2 uses: every eigenvalue of $B_\pi$ arises in this way. Spectra are of the complexified matrices.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 21, proof of Lemma B.2, display (B.1)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_MVC_Setting

namespace AccelVI.MVC

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- (B.1), p. 21: every eigenvalue ω of B_π (step sizes (4.2)) is a root of
ω² − 2λμ/(1 + √(1 − λ²)) ω + (1 − √(1 − λ²))/(1 + √(1 − λ²)) = 0 for some eigenvalue μ of L_π. -/
theorem eq_B_1 (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hpol : IsPolicy pol) :
    ∀ ω ∈ spectrum ℂ ((Bpol M pol).map (algebraMap ℝ ℂ)),
      ∃ μ ∈ spectrum ℂ ((LPol M pol).map (algebraMap ℝ ℂ)),
        ω ^ 2 - (2 * (M.lam : ℂ) * μ / (1 + (Real.sqrt (1 - M.lam ^ 2) : ℂ))) * ω
          + ((1 - Real.sqrt (1 - M.lam ^ 2)) / (1 + Real.sqrt (1 - M.lam ^ 2)) : ℝ) = 0 := by sorry

end AccelVI.MVC
