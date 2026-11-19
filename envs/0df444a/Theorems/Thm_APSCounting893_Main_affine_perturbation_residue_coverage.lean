-- Prove2me | Theorems.Thm_APSCounting893_Main_affine_perturbation_residue_coverage
-- name    : APSCounting893.Main.affine_perturbation_residue_coverage
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T10:08:20.858369+00:00
-- url     : https://prove2.me/theorems/e2727136-5042-4c4e-af99-6caa3e2c3f4f
-- title:
--   Affine perturbation limits cover the actual zero fiber
-- statement:
--   Let $F:\mathbb C^n\to\mathbb C^{n+1}$ be a reduced map and let the normalization, good open set, and affine line be the prescribed admissible data. Homogenize the associated square system and perturb its equations by $\epsilon z_i^{d_i}$. Let $Z_0^*$ be the actual projective limits of bounded-ramification $\epsilon$-Puiseux solutions.
--
--   Every affine point of $Z_0^*$ has output coordinates of nonnegative $t$-valuation, and their residues cover exactly the actual zero fiber:
--
--   $$\{\operatorname{res}_t(y(z)):z\in Z_0^*,\ z_0\ne0\}=Y\cap\pi^{-1}(0).$$
--
--   Both directions refer to actual series solutions of the perturbed equations. This is the geometric identification of roots needed for the trailing-coefficient product in Theorem 5.3.
-- source:
--   Agarwal, Hari, Pandey and Shukla, Approximate Polynomial Satisfiability and Integral Closure Membership in the Counting Hierarchy, STOC 2027 submission #893, Section 5.1, Remark 5.1 and proof of Theorem 5.3, pp. 21–22, using Proposition 4.5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_Resultant
set_option autoImplicit false
open APSCounting893.Main

theorem APSCounting893.Main.affine_perturbation_residue_coverage
    (F : ReducedMap) (D : LineData F)
    (degrees : Fin (F.n + (F.n+1)) → ℕ) (hdegrees : HomogenizingDegrees F D.c D.alpha degrees) :
    (∀ z ∈ epsilonLimitSet F D.c D.alpha degrees, z 0 ≠ 0 →
      (∀ j : Fin (F.n+1), PuiseuxIntegral (z (j.natAdd F.n).succ / z 0)) ∧
        outputResidue F (fun j => z j.succ / z 0) ∈ zeroFiber F D.c) ∧
    (∀ y ∈ zeroFiber F D.c, ∃ z ∈ epsilonLimitSet F D.c D.alpha degrees,
      z 0 ≠ 0 ∧ outputResidue F (fun j => z j.succ / z 0) = y) := by sorry
