-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ihom_ev_app_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_ihom_ev_app_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/3c13f8f8-50e8-5283-a417-f4be61a97754
-- title:
--   Evaluation and double dual for an invertible 𝒪_X-module
-- statement:
--   Let $X$ be a scheme and let $L$ be an object of the category $X$`.Modules` of sheaves of modules on $X$, with its monoidal closed structure (tensor product $\otimes$, unit $\mathbb{1}$, internal hom `ihom` and evaluation counit `ihom.ev`). Assume $L$ satisfies `Scheme.Modules.IsInvertible`, that is: for every point $x \in X$ there is an open subscheme $U \subseteq X$ with $x \in U$ such that the pullback of $L$ along the inclusion $U \to X$ is isomorphic to the unit sheaf of modules on $U$. Then two assertions hold simultaneously. First, for every $F$ in $X$`.Modules` the component at $F$ of the evaluation map, $L \otimes (\mathrm{ihom}\,L)(F) \to F$, is an isomorphism. Second, writing $L^{\vee} = (\mathrm{ihom}\,L)(\mathbb{1})$ for `Scheme.Modules.dual L`, the currying of the composite of the braiding $L^{\vee} \otimes L \cong L \otimes L^{\vee}$ with the evaluation at the unit $L \otimes L^{\vee} \to \mathbb{1}$ is an isomorphism; this curried morphism is the canonical map $L \to (\mathrm{ihom}\,L^{\vee})(\mathbb{1}) = L^{\vee\vee}$ to the double dual.
--
--   This is the standard duality statement for invertible sheaves: evaluation against an invertible module is an isomorphism, and an invertible module is reflexive. It is the version typed over the monoidal structure on sheaves of modules used downstream, where it feeds the computation of global sections of fibres of line bundles on fake elliptic curves in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ihom_ev_app_monoidalV2.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_ihom_ev_app_monoidalV2
    {X : Scheme.{u}} {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) :
    (∀ F : X.Modules, IsIso ((ihom.ev L).app F)) ∧
      IsIso (MonoidalClosed.curry
        ((β_ (Scheme.Modules.dual L) L).hom ≫ (ihom.ev L).app (𝟙_ X.Modules))) := by sorry
