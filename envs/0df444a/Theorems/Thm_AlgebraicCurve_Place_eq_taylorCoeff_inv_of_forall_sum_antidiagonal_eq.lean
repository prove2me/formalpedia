-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_eq_taylorCoeff_inv_of_forall_sum_antidiagonal_eq
-- name    : AlgebraicCurve.Place.eq_taylorCoeff_inv_of_forall_sum_antidiagonal_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/fb67f2f5-c98e-552d-a88b-3fd484b14bd9
-- title:
--   Truncated Cauchy inverse system determines Taylor coefficients of s⁻¹
-- statement:
--   Let $K \subseteq F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F/K$ in the sense of the project: a valuation subring $\mathcal O_v \subseteq F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring. Assume $v$ is rational, i.e. the composite $K \to \mathcal O_v \to \mathcal O_v/\mathfrak m_v$ is surjective, so that each residue has a chosen preimage in $K$ and $f \mapsto v.\mathrm{evalAt}\, f$ is defined on $\mathcal O_v$ (and set to $0$ off $\mathcal O_v$). Let $t \in F$ satisfy $\mathrm{ord}_v(t) = 1$, where $\mathrm{ord}_v$ is minus the logarithm of the associated height-one-spectrum valuation, so $t$ is a uniformiser. Let $s \in \mathcal O_v$ with $v.\mathrm{evalAt}\, s \neq 0$. Write $a_b(g) = \mathrm{taylorCoeff}\ v\ t\ b\ g$ for the $b$-th coefficient produced by the recursion $g_0 = g$, $g_{r+1} = (g_r - \mathrm{evalAt}(g_r))t^{-1}$, $a_r(g) = \mathrm{evalAt}(g_r)$. Let $m \in \mathbb N$ and $\sigma : \mathbb N \to K$ satisfy, for every $r < m$, the convolution identity $\sum_{a+b=r} \sigma_a\, a_b(s) = \delta_{r,0}$, the sum being over the antidiagonal of $r$. The conclusion is that $\sigma_r = a_r(s^{-1})$ for every $r < m$.
--
--   This identifies the solutions of the truncated Cauchy inverse system for the Taylor expansion of $s$ along a uniformiser with the Taylor coefficients of $s^{-1}$, the point being that the system is lower triangular with invertible diagonal entry $a_0(s) = v.\mathrm{evalAt}\, s$. It is used in the analysis of prolongation tuples for models of the $m$-division locus on modular curves, where the unknowns of an incidence system are recognised as the jet of an inverse.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_eq_taylorCoeff_inv_of_forall_sum_antidiagonal_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.Place

theorem AlgebraicCurve.Place.eq_taylorCoeff_inv_of_forall_sum_antidiagonal_eq
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
    {s : F} (hs : s ∈ v.toValuationSubring) (hs0 : v.evalAt s ≠ 0)
    (m : ℕ) (σ : ℕ → K)
    (hσ : ∀ r, r < m →
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal r, σ x.1 * taylorCoeff v t x.2 s = if r = 0 then 1 else 0) :
    ∀ r, r < m → σ r = taylorCoeff v t r s⁻¹ := by sorry
