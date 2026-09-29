-- Prove2me | Theorems.Thm_AlgebraicCurve_RROpens_exists_mem_riemannRochSpace_sub_hasValue_mul_zpow_neg_forall_hasValue
-- name    : AlgebraicCurve.RROpens.exists_mem_riemannRochSpace_sub_hasValue_mul_zpow_neg_forall_hasValue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/ba359402-e51d-514b-9e1b-748b1395413c
-- title:
--   Interpolation in L(D-mP₀) with prescribed leading coefficient
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field that is a $K$-algebra satisfying `IsCurveOver K F`: every nonzero element of $F$ has a principal divisor (a finitely supported integer-valued function on places whose value at each place $v$ is $v.\mathrm{ord}$ of the element, of degree $0$), each residue field of a place is finite over $K$, and $\Omega[F/K]$ is free of rank one over $F$; here a place is a valuation subring of $F$ containing $\mathrm{algebraMap}\,K\,F$, distinct from $F$ and a principal ideal ring, a divisor is a finitely supported function from places to $\mathbb{Z}$, and $\mathrm{degree}$ sums the coefficients weighted by the degrees of the places. Fix a divisor $K_C$ and $g \in \mathbb{N}$ such that for every divisor $D$ one has $\ell(D) - \ell(K_C - D) = \deg D + 1 - g$, where $\ell(D)$ is the $K$-dimension of $\mathrm{riemannRochSpace}\,D = \{f \in F : v(f) \le \exp(D\,v)\ \text{for all places}\ v\}$. Let $D$ be a divisor, $Z$ a finite set of places with $D\,z = 0$ for all $z \in Z$, $c$ an assignment of an element of $K$ to every place, $P_0 \notin Z$ a place with $D\,P_0 = 0$, $x \in F$ with $P_0.\mathrm{ord}\,x = 1$, $m \in \mathbb{N}$ and $c_0 \in K$. If $2g + m + \#Z \le \deg D$, then there is $f \in F$ lying in $\mathrm{riemannRochSpace}(D - m\,P_0)$ such that $f\,x^{-m}$ lies in the valuation subring of $P_0$ with residue the image of $c_0$, and for each $z \in Z$ the element $f$ lies in the valuation subring of $z$ with residue the image of $c\,z$.
--
--   This is the classical interpolation statement in a Riemann–Roch space: for a divisor of large enough degree one may prescribe values at finitely many places where the divisor has coefficient zero together with the leading coefficient, relative to a uniformiser $x$, of a zero of order $m$ at one further place. It is used for a dimension bound on functions with prescribed values and leading term, and in the construction of functions with controlled vanishing orders on a model of a modular curve at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RROpens_exists_mem_riemannRochSpace_sub_hasValue_mul_zpow_neg_forall_hasValue.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.RROpens.exists_mem_riemannRochSpace_sub_hasValue_mul_zpow_neg_forall_hasValue
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (D : Divisor K F)
    (Z : Finset (Place K F)) (hZ : ∀ z ∈ Z, D z = 0) (c : Place K F → K)
    (P₀ : Place K F) (hP₀Z : P₀ ∉ Z) (hP₀D : D P₀ = 0)
    (x : F) (hx : P₀.ord x = 1) (m : ℕ) (c₀ : K)
    (hdeg : 2 * (g : ℤ) + m + Z.card ≤ Divisor.degree D) :
    ∃ f : F, f ∈ riemannRochSpace (D - Finsupp.single P₀ (m : ℤ)) ∧
      P₀.HasValue (f * x ^ (-(m : ℤ))) c₀ ∧ ∀ z ∈ Z, z.HasValue f (c z) := by sorry
