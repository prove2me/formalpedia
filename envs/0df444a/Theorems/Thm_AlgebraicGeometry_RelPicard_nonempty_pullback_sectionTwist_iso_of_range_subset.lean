-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso_of_range_subset
-- name    : AlgebraicGeometry.RelPicard.nonempty_pullback_sectionTwist_iso_of_range_subset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/d3be018c-560b-53c9-a074-4c5e9ec5f6e5
-- title:
--   Section twists commute with base change along ψ
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c\colon C\to\operatorname{Spec}R$ a separated morphism. Let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec}R\to C$ whose composite with $c$ is the identity, and let $U\subseteq C$ be an open subscheme such that the composite of the inclusion $U\hookrightarrow C$ with $c$ is smooth of relative dimension $1$, with the set-theoretic image of $\varepsilon$ contained in $U$. Let $T,T'$ be schemes with morphisms $t\colon T\to\operatorname{Spec}R$, $t'\colon T'\to\operatorname{Spec}R$, and let $\psi\colon T'\to T$ satisfy $\psi$ followed by $t$ equals $t'$; let $r\in\mathbb{N}$. For a base $V\to\operatorname{Spec}R$, write $\mathcal I_V$ for the ideal sheaf `sectionIdeal c ε`, the kernel of the section `rigSection` of $C\times_{\operatorname{Spec}R}V$ determined by $\varepsilon$, and `sectionTwist c ε` for the dual of the module attached to $\mathcal I_V^{\,r}$. The assertion is that the type of isomorphisms between the pullback of the $r$-th section twist over $T$ along $\mathrm{id}_C\times\psi\colon C\times_{\operatorname{Spec}R}T'\to C\times_{\operatorname{Spec}R}T$ and the $r$-th section twist over $T'$ is nonempty; no canonical isomorphism is named.
--
--   This is the base-change compatibility of the line bundles $\mathcal O(r\cdot\varepsilon)$ on a relative curve, in the form needed when only an open subscheme $U$ containing the section is smooth of relative dimension one over the base, the total morphism being merely separated (the situation of a semistable model of a modular curve and its smooth locus). It feeds the computations of Euler characteristics of fibres of section twists and the local charts used for the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso_of_range_subset.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.nonempty_pullback_sectionTwist_iso_of_range_subset
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1 ⊆ (U : Set C))
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (r : ℕ) :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (sectionTwist c ε t r) ≅ sectionTwist c ε t' r) := by sorry
