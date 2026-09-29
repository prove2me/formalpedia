-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut
-- name    : AlgebraicGeometry.RelPicard.geometricallyConnected_of_representsRelSubPic_algEquivZeroCut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/c517c41d-1ea2-52fb-8e32-5396ee675b34
-- title:
--   Geometric connectedness of a scheme representing the Pic⁰ cut
-- statement:
--   Let $R$ be a commutative ring, let $C$ be a scheme, let $c\colon C\to\operatorname{Spec}R$ be a morphism, and let $\varepsilon$ be a section of $c$, that is, a morphism $\operatorname{Spec}R\to C$ composing with $c$ to the identity. Let $D$ consist of a scheme $P$, a structure morphism $D.\mathrm{toBase}\colon P\to\operatorname{Spec}R$ and a section $D.\mathrm{zeroSection}$ of it. Assume $D$ represents the rigidified relative Picard presheaf of $(c,\varepsilon)$ cut out by the condition `algEquivZeroCut`, in the following sense: there is a rigidified line bundle `poincare` on $C\times_{\operatorname{Spec}R}P$ — an invertible module whose restriction along the rigidifying section is trivial — whose pullback to the fibre of $c$ over every point $\operatorname{Spec}k\to P$ with $k$ algebraically closed satisfies `IsAlgEquivZero`; such that for every scheme $T$ over $\operatorname{Spec}R$ and every rigidified line bundle $M$ on $C\times_{\operatorname{Spec}R}T$ with the same fibrewise property there is a unique morphism $g\colon T\to P$ over $\operatorname{Spec}R$ with $g^*\,$`poincare` isomorphic to $M$; and such that the pullback of `poincare` along $D.\mathrm{zeroSection}$ is isomorphic to the unit module. If $D.\mathrm{toBase}$ is locally of finite type, then $D.\mathrm{toBase}$ is geometrically connected.
--
--   This is the standard connectedness property of $\mathrm{Pic}^0$: cutting the rigidified relative Picard functor by algebraic equivalence to zero on geometric fibres forces any representing scheme, once locally of finite type over the base, to have geometrically connected fibres; no properness, flatness or smoothness of $c$ is assumed. It is used by the results constructing representing objects for this cut, and thereby in the identification of $\mathrm{Pic}^0$ of a curve with the Jacobian entering the Néron model discussion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_geometricallyConnected_of_representsRelSubPic_algEquivZeroCut.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.geometricallyConnected_of_representsRelSubPic_algEquivZeroCut
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [LocallyOfFiniteType D.toBase] :
    GeometricallyConnected D.toBase := by sorry
