-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_smooth_of_representsRelSubPic_algEquivZeroCut_of_twoAffineOpenCover
-- name    : AlgebraicGeometry.RelPicard.smooth_of_representsRelSubPic_algEquivZeroCut_of_twoAffineOpenCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/cdc92f1e-4184-5924-bee5-1369ae7c68d5
-- title:
--   Smoothness of a representing scheme for the Pic⁰ cut
-- statement:
--   Let $R$ be a Noetherian commutative ring, $C$ a scheme and $c\colon C\to\operatorname{Spec}R$ a morphism, and let $\mathcal V$ be a two-affine open cover of $C$, that is, two affine open subschemes $U_0,U_1\subseteq C$ with affine intersection and $U_0\cup U_1=C$. Let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec}R\to C$ composing with $c$ to the identity. Let $D$ consist of a scheme $P$, a structure morphism $D.toBase\colon P\to\operatorname{Spec}R$ and a zero section $\operatorname{Spec}R\to P$ of it. Assume $D$ represents the subfunctor `algEquivZeroCut` of the rigidified relative Picard functor of $(c,\varepsilon)$ cut out by fibrewise algebraic equivalence to zero: there is a rigidified invertible module $\mathcal P$ on $C\times_{\operatorname{Spec}R}P$ satisfying that condition, every rigidified invertible module on $C\times_{\operatorname{Spec}R}T$ with the condition is, up to isomorphism, the pullback of $\mathcal P$ along a unique $\operatorname{Spec}R$-morphism $T\to P$, and the pullback of $\mathcal P$ along the zero section is isomorphic to the unit module. Assume further that $D.toBase$ is locally of finite type. Then $D.toBase$ is smooth.
--
--   This is the smoothness of the relative $\mathrm{Pic}^0$ over a Noetherian base, obtained from the infinitesimal lifting of rigidified line bundles across a square-zero thickening; the two-affine open cover of $C$ is the only geometric input on the curve side, no properness, flatness or integrality of $c$ being assumed. It is used in the construction of a smooth model of the Jacobian, feeding the existence statement [`AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_openCharts_of_bijective_sections`](thm.html#AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_openCharts_of_bijective_sections).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_smooth_of_representsRelSubPic_algEquivZeroCut_of_twoAffineOpenCover.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.smooth_of_representsRelSubPic_algEquivZeroCut_of_twoAffineOpenCover
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (𝒱 : C.TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [LocallyOfFiniteType D.toBase] :
    Smooth D.toBase := by sorry
