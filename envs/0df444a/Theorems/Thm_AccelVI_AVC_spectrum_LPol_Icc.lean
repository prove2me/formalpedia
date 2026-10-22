-- Prove2me | Theorems.Thm_AccelVI_AVC_spectrum_LPol_Icc
-- name    : AccelVI.AVC.spectrum_LPol_Icc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:11.518403+00:00
-- url     : https://prove2.me/theorems/a615eaf9-1465-4552-815b-6ba2142b8562
-- title:
--   Proof of Lemma 5.3, p. 9 — for a reversible policy chain, Sp(L_π) ⊂ [−1, 1]
-- statement:
--   Let $(\mathbb S,\mathbb A,P,r,\lambda)$ be a finite MDP and $\pi$ a policy whose transition matrix $L_\pi$ (with $L_{\pi,ij}=\sum_a\pi_{ia}P_{iaj}$) defines an irreducible, reversible Markov chain (Definition 2.1). Then every complex eigenvalue of $L_\pi$ is a real number of absolute value at most one:
--   $$\operatorname{Sp}(L_\pi)\subset[-1,1].$$
--
--   This is the location of the spectrum on which the computation of $\rho(B_\pi)$ in Lemma 5.3 rests: $|\mu|\le1$ because $L_\pi$ is stochastic, and $\mu\in\mathbb R$ because the chain is reversible.
--
--   **Formalization Note.** The spectrum is that of $L_\pi$ as a complex matrix; the conclusion says each of its elements equals a real number $t\in[-1,1]$.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 9, proof of Lemma 5.3, paragraph 'First, since L_π is a stochastic matrix'

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_AVC_Setting

namespace AccelVI.AVC

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- Proof of Lemma 5.3, p. 9: if the chain of `π` is irreducible and reversible, then
`Sp(L_π) ⊂ [−1, 1]`: every complex eigenvalue of `L_π` is a real number in `[−1, 1]`. -/
theorem spectrum_LPol_Icc (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hpol : FoundationsML.ReinforcementLearning.IsPolicy pol)
    (hrev : IsReversible (LPol M pol)) :
    ∀ μ ∈ spectrum ℂ ((LPol M pol).map (algebraMap ℝ ℂ)),
      ∃ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 ∧ μ = (t : ℂ) := by sorry

end AccelVI.AVC
