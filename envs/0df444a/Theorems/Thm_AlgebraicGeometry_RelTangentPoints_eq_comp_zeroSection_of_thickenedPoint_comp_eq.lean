-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelTangentPoints_eq_comp_zeroSection_of_thickenedPoint_comp_eq
-- name    : AlgebraicGeometry.RelTangentPoints.eq_comp_zeroSection_of_thickenedPoint_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/fe7680a7-960c-5f52-8a3e-4e8753b4435b
-- title:
--   Infinitesimal rigidity: a tangent field constant at one thickened point
-- statement:
--   Let $k$ be a field, $X$ a scheme and $x : X \to \operatorname{Spec} k$ a structure morphism equipped with a relative group law $L$, i.e. a group structure on each set $\{\varphi : T \to X \mid \varphi \circ x = t\}$ of $X$-valued points over $t : T \to \operatorname{Spec} k$, with multiplication, unit and inverse compatible with base change along morphisms $T' \to T$ over $\operatorname{Spec} k$. Let $V$ be a finite-dimensional $k$-vector space (with the two-sided, centrally acting module structure used to form the trivial square-zero extension), and write $D_V = \operatorname{Spec}(k \oplus V)$ for $\operatorname{Spec}$ of $\mathrm{TrivSqZeroExt}\ k\ V$, with structure morphism $\mathrm{toBase}$ coming from $k \to k \oplus V$. Let $f_0 : Z_0 \to \operatorname{Spec} k$ be a scheme whose underlying space is compact and quasi-separated and for which the induced map $k \to \Gamma(Z_0, \mathcal{O})$ is bijective, and let $q_1 : Z \to Z_0$, $q_2 : Z \to D_V$ exhibit $Z$ as a pullback of $f_0$ along $\mathrm{toBase}$; $\mathrm{zeroSection}$ denotes the section $Z_0 \to Z$ determined by $\mathrm{id}_{Z_0}$ and $f_0$ followed by the base point $\operatorname{Spec} k \to D_V$. Let $w_0 : Z \to X$ satisfy $w_0 \circ x = q_2 \circ \mathrm{toBase}$ (a morphism over the base), let $y : \operatorname{Spec} k \to Z_0$, and let $y_Z : D_V \to Z$ satisfy $y_Z \circ q_1 = \mathrm{toBase} \circ y$ and $y_Z \circ q_2 = \mathrm{id}$. If $w_0$ is constant along $y_Z$, in the sense that $y_Z$ followed by $w_0$ equals $\mathrm{toBase}$ followed by $y$, the zero section and $w_0$, then $w_0 = q_1$ followed by the zero section followed by $w_0$, i.e. $w_0$ is the pullback along $q_1$ of its restriction to the zero section.
--
--   This is the infinitesimal rigidity statement for group laws: a $V$-valued tangent field along a morphism $Z_0 \to X$ which is constant at a single thickened point is constant everywhere, the hypothesis $\Gamma(Z_0,\mathcal{O}) = k$ playing the role of properness and connectedness in the classical rigidity lemma. It is used in the comparison of relative group laws with their Néron-model incarnations, being cited by the two forms of [`GoodReductionJacobian.RelativeGroupLaw.eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot`](thm.html#GoodReductionJacobian.RelativeGroupLaw.eq_of_comp_eq_of_section_comp_eq_of_ker_mul_maximalIdeal_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelTangentPoints_eq_comp_zeroSection_of_thickenedPoint_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem AlgebraicGeometry.RelTangentPoints.eq_comp_zeroSection_of_thickenedPoint_comp_eq
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k x)
    (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V] [Module.Finite k V]
    {Z₀ Z : Scheme.{u}} [CompactSpace Z₀] [QuasiSeparatedSpace Z₀] (f₀ : Z₀ ⟶ Spec (CommRingCat.of k))
    (h₀ : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f₀.appTop).hom)
    (q₁ : Z ⟶ Z₀) (q₂ : Z ⟶ SquareZero.spec k V) (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase k V))
    (w₀ : Z ⟶ X) (hw₀ : w₀ ≫ x = q₂ ≫ SquareZero.toBase k V)
    (y : Spec (CommRingCat.of k) ⟶ Z₀)
    (yZ : SquareZero.spec k V ⟶ Z) (hyZ₁ : yZ ≫ q₁ = SquareZero.toBase k V ≫ y) (hyZ₂ : yZ ≫ q₂ = 𝟙 _)
    (hconst : yZ ≫ w₀ = SquareZero.toBase k V ≫ y ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w₀) :
    w₀ = q₁ ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w₀ := by sorry
