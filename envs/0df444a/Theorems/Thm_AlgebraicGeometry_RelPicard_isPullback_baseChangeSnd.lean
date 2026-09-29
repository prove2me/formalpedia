-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isPullback_baseChangeSnd
-- name    : AlgebraicGeometry.RelPicard.isPullback_baseChangeSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/46306c29-e7cb-5534-a0bd-960f89218205
-- title:
--   Transitivity of base change: C×_R T'=(C×_R T)×_T T'
-- statement:
--   Let $R$ be a commutative ring and let $C$, $T$, $T'$ be schemes (all in one universe). Fix a morphism $c : C \to \operatorname{Spec} R$, and structure morphisms $t : T \to \operatorname{Spec} R$, $t' : T' \to \operatorname{Spec} R$. Let $\psi$ be an element of `SchemeHomOver t' t`, that is, a pair consisting of a scheme morphism $\psi_1 : T' \to T$ together with a proof that $\psi_1$ followed by $t$ equals $t'$; so $\psi$ is a morphism of $R$-schemes. The morphism `baseChangeSnd c ψ` is the induced map $\operatorname{pullback} c\, t' \to \operatorname{pullback} c\, t$ obtained from the identity of $C$, the morphism $\psi_1$ and the identity of $\operatorname{Spec} R$, i.e. $1_C \times \psi_1$. The assertion is that the square with top edge `baseChangeSnd c ψ`, left edge the second projection $\operatorname{pullback} c\, t' \to T'$, right edge the second projection $\operatorname{pullback} c\, t \to T$, and bottom edge $\psi_1$ is a pullback square in the category of schemes: equivalently, $C \times_R T'$ realises $(C \times_R T) \times_T T'$.
--
--   This is the transitivity (pasting) property of fibre products, $C_{T'} \cong C_T \times_T T'$, for the relative base-change morphism $1 \times \psi$. It supplies the cartesian-square witness used by base-change constructions over the relative Picard functor, and is invoked in the treatment of polarisations and of symmetry and kernel conditions for line bundles pulled back along $1 \times \psi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isPullback_baseChangeSnd.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.isPullback_baseChangeSnd
    {R : Type u} [CommRing R] {C T T' : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    IsPullback (baseChangeSnd c ψ) (pullback.snd c t') (pullback.snd c t) ψ.1 := by sorry
