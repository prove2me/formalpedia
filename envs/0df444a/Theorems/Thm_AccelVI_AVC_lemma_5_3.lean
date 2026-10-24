-- Prove2me | Theorems.Thm_AccelVI_AVC_lemma_5_3
-- name    : AccelVI.AVC.lemma_5_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:07.576771+00:00
-- url     : https://prove2.me/theorems/86932aa8-8e15-4226-aea7-c16d60634f0b
-- title:
--   Lemma 5.3, p. 8 — for a reversible policy chain, ρ(B_π) = 1 − √(1/κ)
-- statement:
--   Let $(\mathbb S,\mathbb A,P,r,\lambda)$ be a finite MDP with $\lambda\in(0,1)$, $\kappa=(1+\lambda)/(1-\lambda)$, and let $\pi$ be a policy whose transition matrix $L_\pi$ defines an irreducible, reversible Markov chain (Definition 2.1). Let $B_\pi$ be the matrix (5.1). Then the spectral radius of $B_\pi$ is
--   $$\rho(B_\pi)=1-\sqrt{1/\kappa}.$$
--
--   Since $1-\sqrt{1/\kappa}<1$, this is the geometric rate at which the powers of $B_\pi$, and hence (by Lemma 5.2) the A-VC errors, decay; it is the constant of Theorem 5.1.
--
--   **Formalization Note.** $\rho(B_\pi)$ is the spectral radius of $B_\pi$ regarded as a complex matrix (the largest modulus of a complex eigenvalue), valued in $[0,\infty]$; $B_\pi$ has non-real eigenvalues, so the real spectrum would give a different quantity.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 8, Lemma 5.3; proof pp. 8–9

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_AVC_Setting

namespace AccelVI.AVC

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- Lemma 5.3, p. 8: if the chain of `π` is irreducible and reversible, the spectral radius of
`B_π` (over `ℂ`) is `ρ(B_π) = 1 − √(1/κ)`. -/
theorem lemma_5_3 (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hpol : FoundationsML.ReinforcementLearning.IsPolicy pol)
    (hrev : IsReversible (LPol M pol)) :
    spectralRadius ℂ ((Bpol M pol).map (algebraMap ℝ ℂ)) = ENNReal.ofReal (theta M.lam) := by sorry

end AccelVI.AVC
