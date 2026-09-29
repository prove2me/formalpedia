-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_small_fppfCohomology_zero_of_small_sections
-- name    : AlgebraicGeometry.Scheme.small_fppfCohomology_zero_of_small_sections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/85f4ddf3-1aa5-5ba8-b9ab-de515bc965ae
-- title:
--   Degree-zero fppf cohomology inherits smallness from global sections
-- statement:
--   Let $S$ be a scheme with structure in universe $u$, and let $F$ be a sheaf of abelian groups, valued in $\mathrm{Ab}$ of universe $u+1$, on the small fppf site of $S$: the site whose underlying category `S.Fppf` consists of the $S$-schemes $X \to S$ whose structure morphism is flat and locally of finite presentation (the objects of `MorphismProperty.Over fppfProperty ⊤ S`, where `fppfProperty` is the infimum of `Flat` and `LocallyOfFinitePresentation`), equipped with the small Grothendieck topology `smallFppfTopology S` attached to that morphism property. Write `fppfTerminal S` for the terminal object of this category, namely $S$ itself with structure morphism the identity $\mathbb{1}_S$. Assume that the abelian group of sections of the underlying presheaf `F.1` at that object, that is $F(\mathbb{1}_S)$, is $v$-small, i.e. in bijection with a type of universe $v$. The conclusion is that `fppfCohomology S F 0`, the degree-$0$ cohomology group `F.H 0` of $F$ on this site (the group $\mathrm{Ext}^0$ from the constant sheaf), is likewise $v$-small. Only smallness, not any explicit identification, is asserted.
--
--   This is the smallness counterpart of the classical identification $H^0_{\mathrm{fppf}}(S,F) = F(S)$ of degree-zero cohomology with global sections. It serves to discharge smallness hypotheses on $H^0$ of the fppf sheaf attached to a group scheme over $\operatorname{Spec}\mathbb{Z}$, and is used in the construction of torsion points on the Néron model of the Jacobian of $X_0$, in [`ModularCurve.JZeroNeronIdentityComponent.exists_jZeroNeronPrimaryTorsionCore_forall_exists_points_embedding`](thm.html#ModularCurve.JZeroNeronIdentityComponent.exists_jZeroNeronPrimaryTorsionCore_forall_exists_points_embedding) and [`ModularCurve.nonempty_jZeroNeronPrimaryTorsionCore_of_dvd`](thm.html#ModularCurve.nonempty_jZeroNeronPrimaryTorsionCore_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_small_fppfCohomology_zero_of_small_sections.lean

import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

theorem AlgebraicGeometry.Scheme.small_fppfCohomology_zero_of_small_sections
    {S : Scheme.{u}} (F : Sheaf (smallFppfTopology S) Ab.{u + 1})
    [Small.{v} (F.1.obj (op (fppfTerminal S)))] :
    Small.{v} (fppfCohomology S F 0) := by sorry
