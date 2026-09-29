-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_baseChangeSnd_comp_restrictHom_eq_of_baseChangeSnd_comp
-- name    : AlgebraicGeometry.RelPicard.baseChangeSnd_comp_restrictHom_eq_of_baseChangeSnd_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/73ef96a5-7aca-5538-bc80-9cac92c357da
-- title:
--   Base-changed Picard restriction maps commute with 1×τ
-- statement:
--   Let $R$ be a commutative ring and $\kappa$ a commutative $R$-algebra, with $\mathrm{specMap}\colon\operatorname{Spec}\kappa\to\operatorname{Spec}R$ the induced morphism. Let $x\colon\mathfrak X\to\operatorname{Spec}R$ and $x_0\colon\mathfrak X_0\to\operatorname{Spec}R$ be schemes over $\operatorname{Spec}R$ equipped with sections $\varepsilon_R,\varepsilon_0$ (morphisms $\operatorname{Spec}R\to\mathfrak X$, resp. $\to\mathfrak X_0$, splitting the structure morphism), and let $D_R$, $D_0$ be relative $\mathrm{Pic}^0$ designations for $x$, $x_0$: schemes over $\operatorname{Spec}R$ with a zero section. Assume $D_R$ and $D_0$ represent the functors of rigidified invertible modules on the pullbacks of $x$, resp. $x_0$, satisfying the cut `algEquivZeroCut` (fibrewise algebraic equivalence to zero over algebraically closed fields), with Poincaré objects $\mathcal P_R$, $\mathcal P_0$; assume further that the base changes $D_R\times_R\kappa$ and $D_0\times_R\kappa$ (pullbacks along $\mathrm{specMap}$, with second projection as structure morphism) represent the corresponding functors for $\mathfrak X\times_R\kappa$, $\mathfrak X_0\times_R\kappa$ with their base-changed sections, and that their Poincaré objects are isomorphic, as modules, to the transports along `BaseChange.ofR` of the pullbacks of $\mathcal P_R$, $\mathcal P_0$ along the first projections $D_R\times_R\kappa\to D_R$, $D_0\times_R\kappa\to D_0$. Let $f\colon\mathfrak X_0\times_R\kappa\to\mathfrak X\times_R\kappa$ be a morphism over $\operatorname{Spec}\kappa$, let $\tau$ be an endomorphism of $\operatorname{Spec}\kappa$ over $\operatorname{Spec}R$, and assume $f$ commutes with the endomorphisms $1\times\tau$ of the two base changes. Two conclusions are asserted. First, if $f$ carries the base-changed section of $\mathfrak X_0$ to that of $\mathfrak X$, then the morphism `RepresentsRelSubPic.pullbackHom` $D_R\times_R\kappa\to D_0\times_R\kappa$, obtained by classifying the pullback of the Poincaré object along `curveChange` $f$, commutes with the endomorphisms $1\times\tau$ of $D_R\times_R\kappa$ and $D_0\times_R\kappa$. Second, the same commutation holds for every morphism $\nu\colon D_R\times_R\kappa\to D_0\times_R\kappa$ over $\operatorname{Spec}\kappa$ with the property that for every scheme $T$, every $t\colon T\to\operatorname{Spec}\kappa$ and every $T$-point $a$ of $D_R\times_R\kappa$ over $t$, the module underlying the pullback of the Poincaré object of $D_0\times_R\kappa$ along $a$ followed by $\nu$ is isomorphic to the rigidification, in the sense of `Scheme.Modules.rigidify` along the rigidifying section at $t$ and the projection, of the pullback along `curveChange` $f$ $t$ of the module underlying the pullback of the Poincaré object of $D_R\times_R\kappa$ along $a$.
--
--   This is the equivariance, or descent, statement for restriction morphisms between base-changed relative Picard schemes: a morphism of pointed curves that commutes with the semilinear twist $1\times\tau$ of the base induces a morphism on relative $\mathrm{Pic}^0$ that does too, both for the canonically constructed restriction morphism and for any morphism characterised pointwise by the same rigidified pullback recipe. It is used, with $\tau$ the Frobenius of a residue field, to verify the twist compatibility of the maps to abelian quotients of the Néron object of $J_0$ at $p$, and in the description of points on the special fibre of the model of the relevant modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_baseChangeSnd_comp_restrictHom_eq_of_baseChangeSnd_comp.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.baseChangeSnd_comp_restrictHom_eq_of_baseChangeSnd_comp
    {R : Type u} [CommRing R] (κ : Type u) [CommRing κ] [Algebra R κ]
    {𝔛 𝔛₀ : Scheme.{u}} {x : 𝔛 ⟶ Spec (CommRingCat.of R)} {x₀ : 𝔛₀ ⟶ Spec (CommRingCat.of R)}
    {εR : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) x} {ε₀R : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) x₀}
    {D_R : RelativePic0Designation R x} {D₀ : RelativePic0Designation R x₀}
    (hD_R : RepresentsRelSubPic x εR (algEquivZeroCut x εR) D_R)
    (hD₀ : RepresentsRelSubPic x₀ ε₀R (algEquivZeroCut x₀ ε₀R) D₀)
    (hD : RepresentsRelSubPic (baseChange R x κ) (sectionBaseChange κ εR)
      (algEquivZeroCut (baseChange R x κ) (sectionBaseChange κ εR)) (D_R.baseChange κ))
    (hPD : Nonempty (hD.poincare.L ≅ (BaseChange.ofR x εR κ
      (hD_R.poincare.pullbackAlong ⟨pullback.fst D_R.toBase (specMap R κ), pullback.condition⟩)).L))
    (hD' : RepresentsRelSubPic (baseChange R x₀ κ) (sectionBaseChange κ ε₀R)
      (algEquivZeroCut (baseChange R x₀ κ) (sectionBaseChange κ ε₀R)) (D₀.baseChange κ))
    (hPD' : Nonempty (hD'.poincare.L ≅ (BaseChange.ofR x₀ ε₀R κ
      (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap R κ), pullback.condition⟩)).L))
    (f : pullback x₀ (specMap R κ) ⟶ pullback x (specMap R κ)) (hf : f ≫ baseChange R x κ = baseChange R x₀ κ)
    (τ : SchemeHomOver (specMap R κ) (specMap R κ))
    (hcomm : baseChangeSnd x₀ τ ≫ f = f ≫ baseChangeSnd x τ) :
    (∀ hε : (sectionBaseChange κ ε₀R).1 ≫ f = (sectionBaseChange κ εR).1,
      baseChangeSnd D_R.toBase τ ≫ (RepresentsRelSubPic.pullbackHom f hf hε hD hD').1 =
        (RepresentsRelSubPic.pullbackHom f hf hε hD hD').1 ≫ baseChangeSnd D₀.toBase τ) ∧
    (∀ ν : SchemeHomOver (D_R.baseChange κ).toBase (D₀.baseChange κ).toBase,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t (D_R.baseChange κ).toBase),
        Nonempty ((hD'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν)).L ≅
          Scheme.Modules.rigidify (rigSection (baseChange R x₀ κ) t (sectionBaseChange κ ε₀R))
            (pullback.snd (baseChange R x₀ κ) t)
            ((Scheme.Modules.pullback (curveChange f hf t)).obj (hD.poincare.pullbackAlong a).L))) →
      baseChangeSnd D_R.toBase τ ≫ ν.1 = ν.1 ≫ baseChangeSnd D₀.toBase τ) := by sorry
