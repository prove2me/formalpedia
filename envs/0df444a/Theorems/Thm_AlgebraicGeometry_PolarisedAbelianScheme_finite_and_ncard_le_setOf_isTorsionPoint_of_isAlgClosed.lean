-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_finite_and_ncard_le_setOf_isTorsionPoint_of_isAlgClosed
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.finite_and_ncard_le_setOf_isTorsionPoint_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/a7687d18-3300-5ca6-857f-9b5b63b6bf30
-- title:
--   Finiteness and bound ≤ ℓ^{2g} for ℓ-torsion over ̄ k
-- statement:
--   Let $g$, $d$, $n$ be natural numbers and $k$ an algebraically closed field, and let $u$ be a polarised abelian scheme of the project's shape over $k$: it consists of a scheme $A$ with a structure morphism $f : A \to \operatorname{Spec} k$; a relative group law $L$ on $f$, that is, a multiplication, unit and inverse on the sets $\mathrm{SchemeHomOver}\,t\,f$ of morphisms $T \to A$ over a given $t : T \to \operatorname{Spec} k$, satisfying the group axioms and natural in $T$; commutativity of $L$; the property bundle asserting that $f$ is smooth and proper with connected fibres and admits a relative group law; the requirement that every fibre of $f$ has topological Krull dimension $g$; a family $P_0,\dots,P_{2g-1}$ of sections over the identity of $\operatorname{Spec} k$ that are killed by $n$ and that, after base change along any ring map from $k$ to an algebraically closed field, are independent and span the $n$-torsion with coefficients in $\mathrm{Fin}\,n$; and a module $\mathrm{pol}$ on $A$ which is invertible, defines a closed immersion into projective space by its sections, and has geometric fibre $H^0$-rank $d$. Let $\ell$ be a natural number whose image in $k$ is a unit and with $\ell \neq 0$. Then the set of sections $x$ of $f$ over the identity of $\operatorname{Spec} k$ with $\ell$-fold sum $L.\mathrm{nsmul}\,\ell\,x$ equal to the unit section is finite, and its cardinality (as `Set.ncard`) is at most $\ell^{2g}$. Classically this set has exactly $\ell^{2g}$ elements; only finiteness and the upper bound are asserted here.
--
--   This is the standard count of the $\ell$-torsion of a $g$-dimensional abelian variety over an algebraically closed field, in the weaker form of an upper bound. It supplies the uniform bound on torsion used in the construction of a morphism compatible with the polarisation in [`AlgebraicGeometry.PolarisedAbelianScheme.exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_pol_iso_of_small`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_pol_iso_of_small).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_finite_and_ncard_le_setOf_isTorsionPoint_of_isAlgClosed.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

theorem AlgebraicGeometry.PolarisedAbelianScheme.finite_and_ncard_le_setOf_isTorsionPoint_of_isAlgClosed
    {g d n : ℕ} {k : Type} [Field k] [IsAlgClosed k] (u : PolarisedAbelianScheme g d n k)
    (ℓ : ℕ) (hℓ : IsUnit ((ℓ : ℕ) : k)) (hℓ0 : ℓ ≠ 0) :
    {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) u.f | u.L.IsTorsionPoint (𝟙 _) ℓ x}.Finite ∧
      {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) u.f | u.L.IsTorsionPoint (𝟙 _) ℓ x}.ncard ≤ ℓ ^ (2 * g) := by sorry
