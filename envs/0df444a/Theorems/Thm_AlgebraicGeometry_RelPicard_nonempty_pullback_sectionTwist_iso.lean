-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso
-- name    : AlgebraicGeometry.RelPicard.nonempty_pullback_sectionTwist_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/cdad5030-5bcb-5cfb-8bf4-7d7733f8a86b
-- title:
--   Base change of the twisting module 𝒪(rε_T) along T'→ T
-- statement:
--   Let $R$ be a commutative ring and let $c\colon C\to\operatorname{Spec}R$ be a separated morphism of schemes that is smooth of relative dimension $1$. Let $\varepsilon$ be a section of $c$ over the identity of $\operatorname{Spec}R$, i.e. a morphism $\varepsilon\colon\operatorname{Spec}R\to C$ with $\varepsilon$ followed by $c$ equal to the identity. Let $T,T'$ be schemes with morphisms $t\colon T\to\operatorname{Spec}R$ and $t'\colon T'\to\operatorname{Spec}R$, and let $\psi$ be a morphism $T'\to T$ over $\operatorname{Spec}R$, i.e. one whose composite with $t$ is $t'$; write $1_C\times\psi$ for the induced morphism `baseChangeSnd c ψ` from the fibre product of $c$ and $t'$ to that of $c$ and $t$, built from $1_C$, $\psi$ and $1_{\operatorname{Spec}R}$. For a natural number $r$, let `sectionTwist c ε t r` be the dual of the module attached to the $r$-th power of the ideal sheaf of data given by the kernel of the section `rigSection c t ε` of the second projection $C\times_R T\to T$ determined by $t$ followed by $\varepsilon$, and likewise for $t'$. The assertion is that the type of isomorphisms, in the category of modules on $C\times_R T'$, between the pullback of `sectionTwist c ε t r` along $1_C\times\psi$ and `sectionTwist c ε t' r` is nonempty; no particular isomorphism is named.
--
--   This is the base-change compatibility of the line bundle $\mathcal{O}(r\varepsilon_T)$ on a pointed smooth separated relative curve: pulling back along $1_C\times\psi$ turns $\mathcal{O}(r\varepsilon_T)$ into $\mathcal{O}(r\varepsilon_{T'})$. It is used in the construction of the relative Picard and theta bundles, for instance in the Euler-characteristic computations for `sectionTwist` twisted by ideal and fibre modules, and in the production of charts on which the first cohomology of a fibre vanishes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.nonempty_pullback_sectionTwist_iso
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (r : ℕ) :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (sectionTwist c ε t r) ≅ sectionTwist c ε t' r) := by sorry
