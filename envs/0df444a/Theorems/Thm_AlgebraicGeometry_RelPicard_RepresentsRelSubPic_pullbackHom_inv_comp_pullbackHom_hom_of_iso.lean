-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_pullbackHom_inv_comp_pullbackHom_hom_of_iso
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.pullbackHom_inv_comp_pullbackHom_hom_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/6f83d27a-0ce3-5013-a756-7c765a956b88
-- title:
--   Pull-back along e and e⁻¹ are mutually inverse
-- statement:
--   Let $R$ be a commutative ring and let $c : C \to \operatorname{Spec} R$ and $c' : C' \to \operatorname{Spec} R$ be schemes over $\operatorname{Spec} R$, each equipped with a section: $\varepsilon$ is a morphism $\operatorname{Spec} R \to C$ with $\varepsilon$ followed by $c$ the identity, and likewise $\varepsilon'$ for $c'$. Let $e : C \cong C'$ be an isomorphism of schemes with $e.\mathrm{hom}$ followed by $c'$ equal to $c$, $e.\mathrm{inv}$ followed by $c$ equal to $c'$, and compatible with the sections in both directions: $\varepsilon$ followed by $e.\mathrm{hom}$ is $\varepsilon'$, and $\varepsilon'$ followed by $e.\mathrm{inv}$ is $\varepsilon$. Let $D$ and $D'$ be designations for $c$ and for $c'$, each consisting of a scheme $P$, a structure morphism to $\operatorname{Spec} R$ and a section of it, and assume $h$ and $h'$ exhibit $D$ and $D'$ as representing the subfunctor of rigidified line bundles cut out by `algEquivZeroCut`, i.e. by fibrewise algebraic equivalence to zero over algebraically closed points: each carries a Poincaré rigidified bundle lying in the condition, classifies uniquely up to isomorphism of underlying bundles every rigidified bundle in the condition, and restricts along its zero section to the unit bundle. Then the underlying scheme morphisms of `pullbackHom` for $e.\mathrm{inv}$ (from $D.P$ to $D'.P$) and for $e.\mathrm{hom}$ (from $D'.P$ to $D.P$) compose to $\mathbf{1}_{D.P}$ in one order and to $\mathbf{1}_{D'.P}$ in the other.
--
--   This is the functoriality statement that isomorphic pointed curves have isomorphic representing schemes for the algebraic-equivalence-to-zero part of the rigidified relative Picard functor: pull-back along an isomorphism of pointed $R$-schemes is an isomorphism of the representing objects. It is used in the construction of the Néron-type objects attached to the modular curves $X_H$ and in the comparison of their torsion and toric point groups under Galois and inertia actions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_pullbackHom_inv_comp_pullbackHom_hom_of_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard

universe u

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.pullbackHom_inv_comp_pullbackHom_hom_of_iso
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    (e : C ≅ C') (he : e.hom ≫ c' = c) (he' : e.inv ≫ c = c')
    (hε : ε.1 ≫ e.hom = ε'.1) (hε' : ε'.1 ≫ e.inv = ε.1)
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D') :
    (pullbackHom e.inv he' hε' h h').1 ≫ (pullbackHom e.hom he hε h' h).1 = 𝟙 D.P ∧
    (pullbackHom e.hom he hε h' h).1 ≫ (pullbackHom e.inv he' hε' h h').1 = 𝟙 D'.P := by sorry
