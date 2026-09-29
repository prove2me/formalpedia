-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_mono_whiskerLeft_moduleIota
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.mono_whiskerLeft_moduleIota
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/225a0e13-6e51-5749-9daf-0546e72b24ce
-- title:
--   Tensoring an ideal sheaf inclusion with a locally free module preserves monomorphy
-- statement:
--   Let $X$ be a scheme and let $I$ be a quasi-coherent ideal sheaf datum on $X$, i.e. a term of `X.IdealSheafData`; write `I.module` for the associated sheaf of modules, defined as the kernel of the canonical morphism `I.subschemeι.unitToPushforwardUnit` from the unit module $\mathcal O_X$ of `X.ringCatSheaf` to the pushforward along the closed immersion `I.subschemeι` of the unit module of the associated closed subscheme, and `I.moduleι` for its morphism to the unit object of the monoidal category `X.Modules`. Let $n$ be a natural number and let $F$ be a sheaf of modules on $X$ which is locally free of rank $n$ in the sense of `Scheme.Modules.IsLocallyFreeOfRank n F`: for every point $x$ of $X$ there is an open $U \subseteq X$ containing $x$ such that the pullback of $F$ along the inclusion $U \to X$ is isomorphic to the free module on `ULift (Fin n)`. The conclusion is that the left whiskering $F \mathbin{◁} I.moduleι$, i.e. the morphism $F \otimes_{\mathcal O_X} I.module \to F \otimes_{\mathcal O_X} \mathcal O_X$ obtained by tensoring `I.moduleι` with $F$, is a monomorphism in `X.Modules`.
--
--   This is the standard flatness statement for locally free modules in the form needed for ideal sheaves: tensoring the inclusion $\mathcal I \hookrightarrow \mathcal O_X$ with a rank $n$ vector bundle remains injective, so that $F \otimes \mathcal I$ realises the product ideal sheaf inside $F$. It is used in the treatment of invertible ideal sheaves, for instance to produce the short exact sequences attached to thickenings of a closed subscheme twisted by a vector bundle; monomorphy is tested on sections over all opens via [`AlgebraicGeometry.Scheme.Modules.Hom.mono_iff_injective`](thm.html#AlgebraicGeometry.Scheme.Modules.Hom.mono_iff_injective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_mono_whiskerLeft_moduleIota.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.mono_whiskerLeft_moduleIota
    {X : Scheme.{u}} (I : X.IdealSheafData) {n : ℕ} (F : X.Modules)
    (hF : Scheme.Modules.IsLocallyFreeOfRank n F) :
    Mono (F ◁ I.moduleι) := by sorry
