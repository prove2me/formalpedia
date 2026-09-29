-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_isFinite_and_flat_and_locallyOfFinitePresentation_and_surjective_of_pointEquivPlace_comp_eq_restrictAlong
-- name    : AlgebraicCurve.CurveModel.isFinite_and_flat_and_locallyOfFinitePresentation_and_surjective_of_pointEquivPlace_comp_eq_restrictAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/a71edb6d-fec8-5a60-9d1f-cc8c7d57b5aa
-- title:
--   Finiteness and flatness of a curve morphism inducing φ
-- statement:
--   Let $k$ be an algebraically closed field and let $F$, $F'$ be fields equipped with $k$-algebra structures, each satisfying `HasPrincipalDivisors`: for every nonzero $f$ there is a finitely supported integer-valued function $D$ on places with $D(v) = v.\mathrm{ord}(f)$ for all places $v$ and $\deg D = 0$. Let $M$ and $M'$ be curve models of $F$ and of $F'$ over $k$, that is, integral schemes $M.C$, $M'.C$ together with proper, smooth of relative dimension $1$ structure morphisms to $\operatorname{Spec} k$, ring isomorphisms of $F$ resp. $F'$ with the function field compatible with $k$, and bijections from closed points to places matching stalks with valuation subrings, every finite set of points lying in an affine open. Let $\varphi : F \to F'$ be a $k$-algebra homomorphism whose underlying ring homomorphism is integral, and let $g : M'.C \to M.C$ be a morphism over $\operatorname{Spec} k$, i.e. $g$ followed by $M.\mathrm{toBase}$ equals $M'.\mathrm{toBase}$. Assume that $g$ induces restriction of places along $\varphi$: for every $k$-point $x'$ of $M'.C$ (a section of $M'.\mathrm{toBase}$), the place of $F$ attached by `M.pointEquivPlace` to $x'$ followed by $g$ is the place whose valuation subring is the preimage under $\varphi$ of that of the place attached to $x'$ by `M'.pointEquivPlace`. Then $g$ is finite, flat, locally of finite presentation and surjective.
--
--   This is the classical statement that a morphism of smooth proper curves over an algebraically closed field which is non-constant, here expressed through the requirement that it read a given integral extension of function fields on places, is finite, flat, of finite presentation and surjective. It underlies the description of the fibres of $g$ over a closed point in terms of ramification indices along $\varphi$, which is the form in which it is used later.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_isFinite_and_flat_and_locallyOfFinitePresentation_and_surjective_of_pointEquivPlace_comp_eq_restrictAlong.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicCurve
open AlgebraicGeometry

theorem AlgebraicCurve.CurveModel.isFinite_and_flat_and_locallyOfFinitePresentation_and_surjective_of_pointEquivPlace_comp_eq_restrictAlong
    {k : Type u} [Field k] [IsAlgClosed k]
    {F : Type v} [Field F] [Algebra k F] [HasPrincipalDivisors k F] {F' : Type v} [Field F'] [Algebra k F'] [HasPrincipalDivisors k F']
    (M : CurveModel k F) (M' : CurveModel k F')
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral)
    (g : M'.C ⟶ M.C) (hg : g ≫ M.toBase = M'.toBase)
    (hgφ : ∀ x' : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _},
      M.pointEquivPlace ⟨x'.1 ≫ g, by rw [Category.assoc, hg]; exact x'.2⟩ = (M'.pointEquivPlace x').restrictAlong φ hφ) :
    IsFinite g ∧ Flat g ∧ LocallyOfFinitePresentation g ∧ Surjective g := by sorry
