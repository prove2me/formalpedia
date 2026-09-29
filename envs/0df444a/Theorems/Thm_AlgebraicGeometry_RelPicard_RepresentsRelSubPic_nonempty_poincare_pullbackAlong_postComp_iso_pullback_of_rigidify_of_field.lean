-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_postComp_iso_pullback_of_rigidify_of_field
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_postComp_iso_pullback_of_rigidify_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/12e9dc51-e390-5a2d-bccb-88f1f33e9056
-- title:
--   Poincaré bundle at a field-valued point over a B-point
-- statement:
--   Let $R$ be a commutative ring, $c_X\colon X\to\operatorname{Spec}R$ a morphism of schemes, and $\varepsilon$ a section of $c_X$, i.e. a morphism $\operatorname{Spec}R\to X$ with $\varepsilon\mathbin{;}c_X=\mathrm{id}$. Let $D$ consist of a scheme $P$ with a structure morphism $D.\mathrm{toBase}\colon P\to\operatorname{Spec}R$ and a section of it, and let `hrep` be a witness that $D$ represents the rigidified Picard condition `algEquivZeroCut`, whose underlying data include the Poincaré object `hrep.poincare`: an invertible module on $X\times_R P$ rigidified along `rigSection`. Let $\rho\colon R\to B$ be a ring homomorphism, $k'$ a field, $t\colon\operatorname{Spec}k'\to\operatorname{Spec}R$, and $\psi$ a morphism $\operatorname{Spec}k'\to\operatorname{Spec}B$ with $\psi\mathbin{;}\operatorname{Spec}\rho=t$. Let $a\colon\operatorname{Spec}B\to P$ satisfy $a\mathbin{;}D.\mathrm{toBase}=\operatorname{Spec}\rho$, let $N$ be an invertible module on $X\times_R B$, and assume an isomorphism `isoA` between the pullback of the Poincaré bundle along the base change $1_X\times a$ and the rigidification $N\otimes q^{*}\bigl((\sigma^{*}N)^{\vee}\bigr)$, where $\sigma=$ `rigSection` and $q=$ `pullback.snd`. The conclusion asserts that the type of isomorphisms between the module underlying the pullback of the Poincaré bundle along $\psi\mathbin{;}a$ and $(1_X\times\psi)^{*}N$ on $X\times_R k'$ is nonempty.
--
--   This is the compatibility statement saying that an identification of the Poincaré bundle at a $B$-valued point of the relative $\mathrm{Pic}^0$ scheme with a rigidified invertible module $N$ on $X\times_R B$ specialises, at a field-valued point of $\operatorname{Spec}B$ over $R$, to an identification with the plain pullback of $N$, the rigidifying twist becoming trivial over a field. It is used in the computation of divisor classes on the generic fibre of a model of a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_postComp_iso_pullback_of_rigidify_of_field.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_postComp_iso_pullback_of_rigidify_of_field
    {R : Type u} [CommRing R] {X : Scheme.{u}} (cX : X ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) cX)
    (D : RelativePic0Designation R cX) (hrep : RepresentsRelSubPic cX ε (algEquivZeroCut cX ε) D)
    {B : Type u} [CommRing B] (ρ : R →+* B) {k' : Type u} [Field k']
    (t : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of R)) (ψ : SchemeHomOver t (Spec.map (CommRingCat.ofHom ρ)))
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase)
    (N : (pullback cX (Spec.map (CommRingCat.ofHom ρ))).Modules) (hN : Scheme.Modules.IsInvertible N)
    (isoA : (hrep.poincare.pullbackAlong a).L ≅
      Scheme.Modules.rigidify (rigSection cX (Spec.map (CommRingCat.ofHom ρ)) ε) (pullback.snd cX (Spec.map (CommRingCat.ofHom ρ))) N) :
    Nonempty ((hrep.poincare.pullbackAlong (postComp a ψ)).L ≅ (Scheme.Modules.pullback (baseChangeSnd cX ψ)).obj N) := by sorry
