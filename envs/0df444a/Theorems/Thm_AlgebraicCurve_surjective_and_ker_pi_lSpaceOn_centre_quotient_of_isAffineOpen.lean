-- Prove2me | Theorems.Thm_AlgebraicCurve_surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen
-- name    : AlgebraicCurve.surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/27fc0011-b9be-51b4-ab2d-cca9aaab0dcd
-- title:
--   Global-to-local δ map on an affine chart: surjectivity and kernel
-- statement:
--   Let $k$ be an algebraically closed field, $C$ an integral scheme with a proper morphism $c : C \to \operatorname{Spec} k$, and give the function field $K =$ `C.functionField` the $k$-algebra structure coming from the germ at the generic point of the structure map; assume $K/k$ satisfies `IsCurveOver`, i.e. every nonzero $f \in K$ has a divisor of degree $0$ recording its orders at all places, every place has residue field finite over $k$, and $\Omega_{K/k}$ is free of rank one. Let $F$ be a field over $k$ with a `CurveModel` $M$ (a proper smooth integral $k$-scheme of relative dimension $1$ whose function field is identified with $F$, together with a bijection between its closed points and the places of $F/k$ matching stalks with valuation rings, and with every finite set of points contained in an affine open), let $\nu : M.C \to C$ satisfy $\nu$ followed by $c$ equals $M.\mathrm{toBase}$, and assume the stalk map of $\nu$ at the generic point of $M.C$ is an isomorphism. Let $U$ be an affine open of $C$ containing the generic point. For a place $v$ of $K/k$ (a valuation subring of $K$ containing $k$, proper and with principal ideals) say $v$ is centred at $z \in C$ when every $s$ in the stalk $\mathcal{O}_{C,z}$ has $v$-adic valuation $\le 1$ in $K$ and every $s$ in the maximal ideal has valuation $< 1$. Write $\tilde A_z$ for `lSpaceOn` of the set of places centred at $z$ at the zero divisor, i.e. $\{f \in K : v(f) \le 1$ for all such $v\}$, and $\tilde A_U$ for the same construction with the set of places centred at some point of $U$; put $Q_z = \tilde A_z / O_z$, where $O_z$ is the preimage in $\tilde A_z$ of the $k$-span of the image of $\mathcal{O}_{C,z} \to K$. Since the condition set for $z \in U$ is contained in the one for $U$, antitonicity of `lSpaceOn` gives $\tilde A_U \subseteq \tilde A_z$, and $\varphi$ denotes the $k$-linear map from $\tilde A_U$ to $\prod_{z} Q_z$, indexed by the points $z \in U$ with $\{z\}$ closed, whose $z$-component is this inclusion followed by the quotient map. The assertion is that $\varphi$ is surjective, that its kernel is the preimage in $\tilde A_U$ of the $k$-span of the image of the germ map $\Gamma(C,U) \to K$ at the generic point, that the set of indices $z$ with $Q_z$ nontrivial is finite, and that each $Q_z$ is finite-dimensional over $k$.
--
--   This is the global-to-local comparison on an affine chart of a proper integral curve: the ring of functions regular at all places centred in $U$ modulo the sections over $U$ decomposes as the finite direct sum of the local $\delta$-spaces $Q_z$, whose dimensions are the singularity invariants $\delta_z$. It is used to bound the Euler characteristic of a section space of a divisor and to show that only finitely many stalks of $C$ fail to be regular local rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry
open AlgebraicCurve

theorem AlgebraicCurve.surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c]
    (hK : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra; IsCurveOver k C.functionField)
    {F : Type v} [Field F] [Algebra k F] (M : AlgebraicCurve.CurveModel k F)
    (ν : M.C ⟶ C) (hν : ν ≫ c = M.toBase) (hbir : IsIso (ν.stalkMap (genericPoint M.C)))
    (U : C.Opens) (hUaff : IsAffineOpen U) (hU : genericPoint C ∈ U) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra

    let Q : C → Type u := fun z =>
      ↥(lSpaceOn {v : Place k C.functionField | (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 : Divisor k C.functionField)) ⧸
        (Submodule.span k (Set.range (algebraMap (C.presheaf.stalk z) C.functionField))).comap
          (lSpaceOn {v : Place k C.functionField | (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 : Divisor k C.functionField)).subtype

    let φ : ↥(lSpaceOn {v : Place k C.functionField | ∃ z : C, z ∈ U ∧ (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 : Divisor k C.functionField)) →ₗ[k]
        ((z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)}) → Q z.1) :=
      LinearMap.pi fun z => (Submodule.mkQ _).comp
        (Submodule.inclusion (lSpaceOn_anti (S₀ := {v : Place k C.functionField | (∀ s : C.presheaf.stalk z.1,
          v.adicValuation (algebraMap (C.presheaf.stalk z.1) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z.1) →
            v.adicValuation (algebraMap (C.presheaf.stalk z.1) C.functionField s) < 1))})
          (S₁ := {v : Place k C.functionField | ∃ z : C, z ∈ U ∧ (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))})
          (fun v hv => ⟨z.1, z.2.1, hv⟩) 0))
    Function.Surjective φ ∧
      LinearMap.ker φ = (Submodule.span k (Set.range (C.presheaf.germ U (genericPoint C) hU).hom)).comap
        (lSpaceOn {v : Place k C.functionField | ∃ z : C, z ∈ U ∧ (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 : Divisor k C.functionField)).subtype ∧
      {z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)} | Nontrivial (Q z.1)}.Finite ∧
      ∀ z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)}, FiniteDimensional k (Q z.1) := by sorry
