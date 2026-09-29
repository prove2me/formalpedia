-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionIdeal_pow_module_iso
-- name    : AlgebraicGeometry.RelPicard.nonempty_pullback_sectionIdeal_pow_module_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/b88c3a1d-f970-5194-9c04-59c211dabb0b
-- title:
--   Section ideal powers commute with base change
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme, and $c\colon C\to\operatorname{Spec}R$ a separated morphism that is smooth of relative dimension $1$. Let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec}R\to C$ whose composite with $c$ is the identity. Let $T,T'$ be schemes with structure morphisms $t\colon T\to\operatorname{Spec}R$ and $t'\colon T'\to\operatorname{Spec}R$, and let $\psi$ be a morphism $T'\to T$ with $\psi$ followed by $t$ equal to $t'$. For each $r\in\mathbb N$, write `sectionIdeal c ε t` for the kernel ideal sheaf datum on $C\times_{\operatorname{Spec}R}T$ of the section `rigSection c t ε` $=$ `pullback.lift (t ≫ ε.1) (𝟙 T)`, and let $I\mapsto I$`.module` be the associated sheaf of modules, namely the kernel of the map from the unit module of the structure sheaf to the pushforward of the unit along the closed immersion of the associated closed subscheme. The assertion is that the set of isomorphisms of modules on $C\times_{\operatorname{Spec}R}T'$ between the pullback of `((sectionIdeal c ε t) ^ r).module` along `baseChangeSnd c ψ` $=\mathrm{id}_C\times\psi$ and `((sectionIdeal c ε t') ^ r).module` is non-empty; no particular isomorphism is named.
--
--   This is the statement that the ideal sheaf $\mathcal O(-r\varepsilon_T)$ of $r$ times the unit section of a smooth separated relative curve is compatible with base change in the parameter scheme. It is used in the construction of the theta bundle on the relative Picard functor, where it feeds into the compatibility of the bundle with base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionIdeal_pow_module_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.nonempty_pullback_sectionIdeal_pow_module_iso
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (r : ℕ) :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (((sectionIdeal c ε t) ^ r).module) ≅
      ((sectionIdeal c ε t') ^ r).module) := by sorry
