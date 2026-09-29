-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionIdeal_pow_module_iso_of_smoothLocus
-- name    : AlgebraicGeometry.RelPicard.nonempty_pullback_sectionIdeal_pow_module_iso_of_smoothLocus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/cc8879f7-f11c-5d82-958f-1a39f4e1f531
-- title:
--   Base change of I(ε_T)^r along 1×ψ
-- statement:
--   Let $R$ be a commutative ring, let $c\colon C\to\operatorname{Spec}R$ be a separated morphism of schemes, and let $U$ be an open subscheme of $C$ such that the composite of the open immersion $U\hookrightarrow C$ with $c$ is smooth of relative dimension $1$. Let $\varepsilon$ be a section of $c$ over $\operatorname{Spec}R$, that is, a morphism $\varepsilon_1\colon\operatorname{Spec}R\to C$ together with the identity $\varepsilon_1\circ c=\mathrm{id}$, and assume the set-theoretic image of $\varepsilon_1$ is contained in $U$. Let $t\colon T\to\operatorname{Spec}R$ and $t'\colon T'\to\operatorname{Spec}R$ be $R$-schemes and let $\psi$ be a morphism $T'\to T$ over $\operatorname{Spec}R$, and let $r$ be a natural number. For an $R$-scheme $t$, write $\mathcal I(\varepsilon_t)$ for `sectionIdeal`, the ideal sheaf data on $C\times_R T$ given by the kernel of the rigidifying section $T\to C\times_R T$ with components $\varepsilon_1\circ t$ and $\mathrm{id}_T$, and for ideal sheaf data $I$ write $I$`.module` for the associated sheaf of modules, namely the kernel of the unit map from the structure sheaf to the pushforward of the structure sheaf of the closed subscheme cut out by $I$. The assertion is that there exists an isomorphism of sheaves of modules on $C\times_R T'$ between the pullback of $\mathcal I(\varepsilon_t)^r$`.module` along $\mathrm{id}_C\times\psi\colon C\times_R T'\to C\times_R T$ and $\mathcal I(\varepsilon_{t'})^r$`.module`; only the nonemptiness of the set of such isomorphisms is claimed, no canonical choice being specified.
--
--   This is the base-change compatibility of the divisorial ideal sheaves $\mathcal O(-r\,\varepsilon_T)$ attached to a section lying in the smooth locus, in the form needed for the relative Picard functor and the theta-bundle construction; it is the smooth-locus variant of the corresponding statement for a globally smooth $c$. It is used in [`AlgebraicGeometry.RelPicard.isInvertible_and_nonempty_pullback_iso_foldr_sectionTwist_tensor_of_range_subset`](thm.html#AlgebraicGeometry.RelPicard.isInvertible_and_nonempty_pullback_iso_foldr_sectionTwist_tensor_of_range_subset), where invertibility of the section ideal and compatibility of its powers with base change are combined.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionIdeal_pow_module_iso_of_smoothLocus.lean

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

theorem AlgebraicGeometry.RelPicard.nonempty_pullback_sectionIdeal_pow_module_iso_of_smoothLocus
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hεU : Set.range ε.1 ⊆ (U : Set C))
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (r : ℕ) :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (((sectionIdeal c ε t) ^ r).module) ≅
      ((sectionIdeal c ε t') ^ r).module) := by sorry
