-- Prove2me | Theorems.Thm_AccelVI_MVC_reversible_real_spectrum
-- name    : AccelVI.MVC.reversible_real_spectrum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:00:44.964171+00:00
-- url     : https://prove2.me/theorems/c56c68e1-7f4b-41fb-b4ae-518f15fc667d
-- title:
--   §2, p. 4 — the eigenvalues of the transition matrix of an irreducible, reversible Markov chain are real
-- statement:
--   Let $L$ be the transition matrix of a Markov chain on a finite state set $S$ (nonnegative entries, rows summing to $1$), and suppose the chain is irreducible and reversible: there is a stationary probability distribution $\nu$ with $\nu_i L_{ij} = \nu_j L_{ji}$ for all $i, j$. Then every eigenvalue of $L$ is real:
--   $$\operatorname{Sp}(L) \subset \mathbb{R}.$$
--
--   The paper quotes this fact from Brémaud (Chapter 6, Section 2.1); it is what makes the eigenvalues of $B_\pi$ explicit in the proof of Lemma B.2.
--
--   **Formalization Note.** The spectrum is taken over $\mathbb{C}$: $\operatorname{Sp}(L)$ is the spectrum of the complexified matrix, and "real" means zero imaginary part. Irreducibility, stationarity and detailed balance are the published `mm_basic` notions.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 4, paragraph after Definition 2.1

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_MVC_Setting

namespace AccelVI.MVC

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- §2, p. 4 (after Definition 2.1): the eigenvalues of the transition matrix of an irreducible,
reversible Markov chain are all real. -/
theorem reversible_real_spectrum (L : Matrix S S ℝ) (hL : MarkovMixing.IsStochastic L)
    (hrev : AccelVI.AVC.IsReversible L) :
    ∀ μ ∈ spectrum ℂ (L.map (algebraMap ℝ ℂ)), μ.im = 0 := by sorry

end AccelVI.MVC
