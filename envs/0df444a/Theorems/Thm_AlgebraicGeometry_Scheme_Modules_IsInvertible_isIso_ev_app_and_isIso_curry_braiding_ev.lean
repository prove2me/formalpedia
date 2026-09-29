-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ev_app_and_isIso_curry_braiding_ev
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_ev_app_and_isIso_curry_braiding_ev
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/0c8c6709-686e-588f-9ed6-6510d39133e4
-- title:
--   Invertible module sheaves are reflexive: evaluation and bidual
-- statement:
--   Let $X$ be a scheme and let $L$ be an object of $X$`.Modules`, the symmetric monoidal closed category of sheaves of modules over the structure sheaf of $X$, whose unit $\mathbb{1}$ is the structure sheaf itself. Assume `Scheme.Modules.IsInvertible L`, that is: for every point $x$ of $X$ there is an open subscheme $U \subseteq X$ containing $x$ such that the pullback of $L$ along the inclusion $U.\iota$ is isomorphic to the unit sheaf of modules on $U$. The conclusion is a conjunction. First, for every $F$ in $X$`.Modules` the component at $F$ of the evaluation counit of the internal hom, $\mathrm{ev}_F \colon L \otimes (\mathrm{ihom}\,L).\mathrm{obj}\,F \to F$, is an isomorphism. Second, writing $L^\vee$ for `Scheme.Modules.dual L`, defined as $(\mathrm{ihom}\,L).\mathrm{obj}\,\mathbb{1}$, the transpose under the closed-monoidal adjunction (`MonoidalClosed.curry`) of the composite of the braiding $\beta_{L^\vee, L} \colon L^\vee \otimes L \to L \otimes L^\vee$ followed by $\mathrm{ev}_{\mathbb{1}} \colon L \otimes L^\vee \to \mathbb{1}$ is an isomorphism; this transpose is the canonical map $L \to L^{\vee\vee}$.
--
--   This is the reflexivity of an invertible sheaf of modules on a scheme, together with the statement that evaluation identifies $L \otimes \mathcal{H}om(L, F)$ with $F$ for every $F$, so that $L^\vee$ is inverse to $L$ for the tensor product. It is used in the treatment of invertible ideal sheaves and of line bundles on the curves occurring in the relative Picard functor, in particular by [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_iso_invModule_zeroSchemeIdeal`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_iso_invModule_zeroSchemeIdeal) and [`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.zeroSchemeIdeal_invModuleSection`](thm.html#AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.zeroSchemeIdeal_invModuleSection).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ev_app_and_isIso_curry_braiding_ev.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_ev_app_and_isIso_curry_braiding_ev
    {X : Scheme.{u}} {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) :
    (∀ F : X.Modules, IsIso ((ihom.ev L).app F)) ∧
      IsIso (MonoidalClosed.curry
        ((β_ (Scheme.Modules.dual L) L).hom ≫ (ihom.ev L).app (𝟙_ X.Modules))) := by sorry
