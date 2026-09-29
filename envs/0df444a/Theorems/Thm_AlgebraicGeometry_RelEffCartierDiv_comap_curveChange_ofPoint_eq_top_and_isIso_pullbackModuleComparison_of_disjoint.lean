-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_comap_curveChange_ofPoint_eq_top_and_isIso_pullbackModuleComparison_of_disjoint
-- name    : AlgebraicGeometry.RelEffCartierDiv.comap_curveChange_ofPoint_eq_top_and_isIso_pullbackModuleComparison_of_disjoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/bf46afbc-c399-5f78-a006-c73da984cfee
-- title:
--   Ideal sheaf of a point restricts trivially to a disjoint closed subscheme
-- statement:
--   Let $R$ be a commutative ring, let $c : C \to \operatorname{Spec} R$ be a separated morphism of schemes, let $c'' : C'' \to \operatorname{Spec} R$ be a morphism, and let $i'' : C'' \to C$ be a closed immersion with $i'' \gg c = c''$. Let $t : T \to \operatorname{Spec} R$ be a morphism and $Q : T \to C$ a morphism with $Q \gg c = t$, and assume the ranges of the underlying continuous maps of $Q$ and of $i''$ are disjoint subsets of $C$. Let $V \subseteq C$ be an open subscheme whose range contains the range of the underlying map of $Q$, and assume the composite of the inclusion $V \hookrightarrow C$ with $c$ is smooth of relative dimension $1$. Consider the relative effective Cartier divisor `RelEffCartierDiv.ofPoint c Q hQ` of degree $1$ on $\operatorname{pullback} c\, t$, whose ideal sheaf datum $I$ is the kernel ideal of the graph morphism $\operatorname{graphOver} c\, Q = (Q, \mathrm{id}_T) : T \to \operatorname{pullback} c\, t$, and the morphism $\operatorname{pullback} c''\, t \to \operatorname{pullback} c\, t$ given by `RelPicard.curveChange i'' hi'' t`, i.e. the base change of $i''$ along $t$ built from $i''$ and $\mathrm{id}_T$. Then the comap of $I$ along that morphism is the unit ideal sheaf $\top$, and the comparison morphism `pullbackModuleComparison` from the pullback of the module $I.\mathrm{module}$ (the kernel of the unit-to-pushforward map of the closed immersion cut out by $I$) to the module of the comap of $I$ is an isomorphism.
--
--   This says that the ideal sheaf $\mathcal O(-\Gamma_Q)$ of the graph of a $T$-valued point $Q$ restricts to the trivial bundle on a closed subscheme whose image avoids $Q$. It supplies one of the two component restrictions used for curves glued from two smooth pieces in the description of the relative Picard functor of such a curve, and is cited in the construction of admissible glued twists and in the analysis of modules attached to points on models of $X_1(p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_comap_curveChange_ofPoint_eq_top_and_isIso_pullbackModuleComparison_of_disjoint.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.comap_curveChange_ofPoint_eq_top_and_isIso_pullbackModuleComparison_of_disjoint
    {R : Type u} [CommRing R] {C C'' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) (c'' : C'' ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (i'' : C'' ⟶ C) (hi'' : i'' ≫ c = c'') [IsClosedImmersion i'']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (Q : T ⟶ C) (hQ : Q ≫ c = t)
    (hdisj : Disjoint (Set.range Q.base) (Set.range i''.base))

    (V : C.Opens) (hQV : Set.range Q.base ⊆ (V : Set C)) [SmoothOfRelativeDimension 1 (V.ι ≫ c)] :
    (RelEffCartierDiv.ofPoint c Q hQ).I.comap (RelPicard.curveChange i'' hi'' t) = ⊤ ∧
      IsIso ((RelEffCartierDiv.ofPoint c Q hQ).I.pullbackModuleComparison (RelPicard.curveChange i'' hi'' t)) := by sorry
