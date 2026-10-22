-- Prove2me | Theorems.Thm_AccelVI_AVC_real_spectrum
-- name    : AccelVI.AVC.real_spectrum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:12.583649+00:00
-- url     : https://prove2.me/theorems/9d6bc1c6-8f09-4dae-a2b3-2ccb67dfdcf8
-- title:
--   §2, p. 4 — the eigenvalues of the transition matrix of a reversible Markov chain are all real
-- statement:
--   Let $L$ be the transition matrix of a Markov chain on a finite state space $\mathbb S$ (nonnegative entries, rows summing to one), and suppose the chain is reversible in the sense of Definition 2.1: $L$ is irreducible and has a stationary distribution $\nu$ with $\nu_iL_{ij}=\nu_jL_{ji}$ for all $i,j$. Then every eigenvalue of $L$ is real:
--   $$\mu\in\operatorname{Sp}(L)\subset\mathbb C\ \Longrightarrow\ \operatorname{Im}\mu=0.$$
--
--   The paper cites this from Brémaud (2013, Ch. 6, §2.1) and uses it to locate the spectrum of $L_\pi$ in the analysis of A-VC.
--
--   **Formalization Note.** The spectrum is that of $L$ viewed as a complex matrix, so non-real eigenvalues are not excluded by the choice of field. The stationary distribution is a probability vector by the definition of stationarity in `mm_basic`.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 4, paragraph after Definition 2.1

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_AVC_Setting

namespace AccelVI.AVC

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- §2, p. 4 (after Definition 2.1): the eigenvalues of the transition matrix `L` of a
reversible Markov chain are all real. -/
theorem real_spectrum (L : Matrix S S ℝ) (hL : MarkovMixing.IsStochastic L)
    (hrev : IsReversible L) :
    ∀ μ ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ)), μ.im = 0 := by sorry

end AccelVI.AVC
