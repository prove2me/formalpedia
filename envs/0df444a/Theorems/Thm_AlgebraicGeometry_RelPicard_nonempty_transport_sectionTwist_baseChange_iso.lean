-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_transport_sectionTwist_baseChange_iso
-- name    : AlgebraicGeometry.RelPicard.nonempty_transport_sectionTwist_baseChange_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/b5f43c58-c90b-5f13-8fd9-3515fb967b1e
-- title:
--   Base change compatibility of the section twist 𝒪(rε)
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c\colon C\to\operatorname{Spec}R$ a separated morphism that is smooth of relative dimension $1$, and let $\varepsilon$ be a section of $c$ over the identity of $\operatorname{Spec}R$, i.e. a morphism $\varepsilon\colon\operatorname{Spec}R\to C$ with $\varepsilon\circ c$ (diagrammatically $\varepsilon\ {\gg}\ c$) equal to $\mathbf 1$. Let $R'$ be an $R$-algebra, $T$ a scheme and $t'\colon T\to\operatorname{Spec}R'$. Write $\mathrm{baseChange}$ for the projection $C\times_{\operatorname{Spec}R}\operatorname{Spec}R'\to\operatorname{Spec}R'$ and $\mathrm{sectionBaseChange}$ for the induced section of it obtained from $\varepsilon$ by the universal property of the fibre product. For a natural number $r$, the section twist $\mathrm{sectionTwist}$ of a pointed curve at a base scheme is the dual of the module of the $r$-th power of the ideal sheaf $\mathrm{sectionIdeal}$, the kernel of the rigidified section `rigSection` in the relevant fibre product. The assertion is that the set of isomorphisms, in the category of modules on $C\times_{\operatorname{Spec}R}T$, between the pullback along the inverse of the canonical isomorphism `κ c R' t'` of the section twist of $(\mathrm{baseChange},\mathrm{sectionBaseChange})$ at $t'$ of order $r$ and the section twist of $(c,\varepsilon)$ at $t'$ followed by $\operatorname{Spec}R'\to\operatorname{Spec}R$, again of order $r$, is nonempty.
--
--   This is the compatibility of the twisting module $\mathcal O(r\varepsilon)$ with the identification $(C_{R'})\times_{\operatorname{Spec}R'}T\cong C\times_{\operatorname{Spec}R}T$: transporting the twist formed for the base-changed pointed curve along that identification gives the twist formed for $(C,\varepsilon)$ directly. It is used to compare the theta bundle of $C_{R'}/R'$ with the theta bundle of $C/R$, in [`AlgebraicGeometry.RelPicard.nonempty_thetaBundle_baseChange_iso_thetaBundle_toR`](thm.html#AlgebraicGeometry.RelPicard.nonempty_thetaBundle_baseChange_iso_thetaBundle_toR).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nonempty_transport_sectionTwist_baseChange_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.RelPicard.BaseChange

theorem AlgebraicGeometry.RelPicard.nonempty_transport_sectionTwist_baseChange_iso
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (R' : Type u) [CommRing R'] [Algebra R R'] {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (r : ℕ) :
    Nonempty ((Scheme.Modules.pullback (κ c R' t').inv).obj
        (sectionTwist (baseChange R c R') (sectionBaseChange R' ε) t' r) ≅
      sectionTwist c ε (t' ≫ specMap R R') r) := by sorry
