-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_comap_curveChange_ofPoint_comp_eq_and_isIso_pullbackModuleComparison_of_isIso_morphismRestrict
-- name    : AlgebraicGeometry.RelEffCartierDiv.comap_curveChange_ofPoint_comp_eq_and_isIso_pullbackModuleComparison_of_isIso_morphismRestrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/d7530184-4642-55b2-ab6e-bbc5b9395e1b
-- title:
--   Restriction of 𝒪(-P) along a closed immersion through P
-- statement:
--   Let $R$ be a commutative ring, let $c : C \to \operatorname{Spec} R$ and $c' : C' \to \operatorname{Spec} R$ be separated morphisms of schemes, and let $i : C' \to C$ be a closed immersion with $i$ followed by $c$ equal to $c'$. Let $t : T \to \operatorname{Spec} R$ be a further scheme over $R$ and $P : T \to C'$ a morphism with $P$ followed by $c'$ equal to $t$. Assume given an open subscheme $U \subseteq C$ whose underlying set contains the set-theoretic image of the composite $P$ followed by $i$, such that the restricted morphism $i \mid_U : i^{-1}U \to U$ is an isomorphism and such that the inclusion $U \hookrightarrow C$ followed by $c$ is smooth of relative dimension $1$. For a point $a : T \to \mathcal{C}$ over $S$, `RelEffCartierDiv.ofPoint` attaches the relative effective Cartier divisor of degree one whose ideal sheaf datum is the kernel ideal sheaf of the graph morphism $T \to \mathcal{C} \times_S T$ obtained from $a$ and $\mathrm{id}_T$; and `RelPicard.curveChange` is the morphism $i \times \mathrm{id}_T : C' \times_R T \to C \times_R T$. The conclusion is twofold: first, the comap along $i \times \mathrm{id}_T$ of the graph ideal sheaf of the point $P$ followed by $i$ on $C \times_R T$ equals the graph ideal sheaf of $P$ on $C' \times_R T$; second, the canonical comparison morphism from the pullback along $i \times \mathrm{id}_T$ of the sheaf of modules attached to the former ideal (the kernel of the unit into the pushforward along the closed subscheme inclusion) to the sheaf of modules attached to its comap is an isomorphism.
--
--   This is the restriction calculus for the line bundle $\mathcal{O}(-P)$ attached to a section: on a closed subscheme $C' \subseteq C$ which is locally isomorphic to $C$ near the image of $P$, inside a locus smooth of relative dimension one, the divisor $P$ on $C$ restricts to the divisor $P$ on $C'$ and the bundles match canonically. It is used in the analysis of relative Picard functors of curves glued from two smooth components, in particular by [`AlgebraicGeometry.RelPicard.exists_gluedTwist_admissible_of_twoGluedSmoothCurves`](thm.html#AlgebraicGeometry.RelPicard.exists_gluedTwist_admissible_of_twoGluedSmoothCurves) and by [`AlgebraicGeometry.RelPicard.isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue`](thm.html#AlgebraicGeometry.RelPicard.isNodeUnitModule_foldr_ofPoint_of_forall_eq_ord_of_hasValue).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_comap_curveChange_ofPoint_comp_eq_and_isIso_pullbackModuleComparison_of_isIso_morphismRestrict.lean

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

theorem AlgebraicGeometry.RelEffCartierDiv.comap_curveChange_ofPoint_comp_eq_and_isIso_pullbackModuleComparison_of_isIso_morphismRestrict
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) (c' : C' ⟶ Spec (CommRingCat.of R)) [IsSeparated c] [IsSeparated c']
    (i : C' ⟶ C) (hi : i ≫ c = c') [IsClosedImmersion i]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : T ⟶ C') (hP : P ≫ c' = t)

    (U : C.Opens) (hPU : Set.range (P ≫ i).base ⊆ (U : Set C)) [IsIso (i ∣_ U)]
    [SmoothOfRelativeDimension 1 (U.ι ≫ c)] :
    (RelEffCartierDiv.ofPoint c (P ≫ i) (by rw [Category.assoc, hi, hP])).I.comap (RelPicard.curveChange i hi t) =
        (RelEffCartierDiv.ofPoint c' P hP).I ∧
      IsIso ((RelEffCartierDiv.ofPoint c (P ≫ i) (by rw [Category.assoc, hi, hP])).I.pullbackModuleComparison
        (RelPicard.curveChange i hi t)) := by sorry
