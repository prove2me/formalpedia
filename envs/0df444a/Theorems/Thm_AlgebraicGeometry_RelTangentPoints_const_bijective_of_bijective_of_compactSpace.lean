-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelTangentPoints_const_bijective_of_bijective_of_compactSpace
-- name    : AlgebraicGeometry.RelTangentPoints.const_bijective_of_bijective_of_compactSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/402e3341-0e98-5e6d-a147-238cba0377d4
-- title:
--   Constant parametrised tangent vectors when Γ(Z₀,𝒪)=k
-- statement:
--   Let $k$ be a field and let $X$ be a scheme equipped with a morphism $x \colon X \to \operatorname{Spec} k$ and a morphism $pt \colon \operatorname{Spec} k \to X$ that is a section of $x$, i.e. $x \circ pt = \mathrm{id}$. Let $V$ be a $k$-vector space, finite over $k$, carrying left and right $k$-module structures that agree, and write $\operatorname{Spec}(k \oplus V)$ for the spectrum of the trivial square-zero extension $\mathrm{TrivSqZeroExt}\,k\,V$, with $\mathrm{toBase}$ the morphism to $\operatorname{Spec} k$ induced by the structure map $k \to k \oplus V$. Let $Z_0$ be a scheme whose underlying space is compact and quasi-separated, with a morphism $f_0 \colon Z_0 \to \operatorname{Spec} k$ such that the associated ring homomorphism $k \to \Gamma(Z_0, \mathcal O_{Z_0})$ (the inverse of the isomorphism $\Gamma \circ \operatorname{Spec} \cong \mathrm{id}$ followed by the map on global sections induced by $f_0$) is bijective. Let $q_1 \colon Z \to Z_0$ and $q_2 \colon Z \to \operatorname{Spec}(k \oplus V)$ form a cartesian square with $f_0$ and $\mathrm{toBase}$. Then the assignment sending a morphism $v \colon \operatorname{Spec}(k \oplus V) \to X$ with $x \circ v = \mathrm{toBase}$ and $v$ restricting to $pt$ at the base point to the composite $v \circ q_2$ is a bijection onto the set of morphisms $w \colon Z \to X$ with $x \circ w = \mathrm{toBase} \circ q_2$ whose restriction along the zero section $Z_0 \to Z$ (the morphism induced by $\mathrm{id}_{Z_0}$ and $\mathrm{basePoint} \circ f_0$) equals $pt \circ f_0$.
--
--   This is an infinitesimal rigidity statement: a $V$-valued tangent vector of $X$ at the rational point $pt$, parametrised by $Z_0$ and constant to zeroth order, is constant, so that such parametrised vectors are exactly the constant ones when $\Gamma(Z_0,\mathcal O_{Z_0}) = k$. It is used in the study of morphisms out of square-zero thickenings, in particular by [`AlgebraicGeometry.RelTangentPoints.eq_comp_zeroSection_of_thickenedPoint_comp_eq`](thm.html#AlgebraicGeometry.RelTangentPoints.eq_comp_zeroSection_of_thickenedPoint_comp_eq); the proof invokes the fact that a pullback along the spectrum of a surjection with nilpotent kernel is a surjective closed immersion inducing a homeomorphism, so that $Z$ and $Z_0$ have the same underlying space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelTangentPoints_const_bijective_of_bijective_of_compactSpace.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.RelTangentPoints.const_bijective_of_bijective_of_compactSpace
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (pt : Spec (CommRingCat.of k) ⟶ X) (hpt : pt ≫ x = 𝟙 (Spec (CommRingCat.of k)))
    (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V] [Module.Finite k V]
    {Z₀ Z : Scheme.{u}} [CompactSpace Z₀] [QuasiSeparatedSpace Z₀] (f₀ : Z₀ ⟶ Spec (CommRingCat.of k))
    (h₀ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f₀.appTop).hom)
    (q₁ : Z ⟶ Z₀) (q₂ : Z ⟶ SquareZero.spec k V) (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase k V)) :
    Function.Bijective (RelTangentPoints.const x pt V f₀ q₁ q₂ hZ) := by sorry
