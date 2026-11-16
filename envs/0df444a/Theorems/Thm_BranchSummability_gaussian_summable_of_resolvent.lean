-- Prove2me | Theorems.Thm_BranchSummability_gaussian_summable_of_resolvent
-- name    : BranchSummability.gaussian_summable_of_resolvent
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T05:57:45.935795+00:00
-- url     : https://prove2.me/theorems/c09c89c3-8040-4d0a-b857-2dc202b93d27
-- title:
--   gaussian summable of resolvent
-- statement:
--   Let gamma be a real sequence. If $$\sum_j(1+\gamma_j^2)^{-1}<\infty,$$ then for every t>0 the Gaussian series $$\sum_j e^{-t\gamma_j^2}$$ converges. This is a summability implication for arbitrary real sequences; it does not assert the premise for the zeta zeros.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Analytic completion of conditional Branch certificate, 16 Nov 2026. No novelty claim.

import Mathlib
open Real

theorem BranchSummability.gaussian_summable_of_resolvent (gamma : ℕ → ℝ)
    (h : Summable (fun j => (1+(gamma j)^2)⁻¹))
    (t : ℝ) (ht : 0 < t) :
    Summable (fun j => Real.exp (-(gamma j)^2*t)) := by sorry
