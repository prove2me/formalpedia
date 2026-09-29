-- Prove2me | Theorems.Thm_AlgebraicGeometry_fppf_exists_section_of_map_eq_unit
-- name    : AlgebraicGeometry.fppf_exists_section_of_map_eq_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/b5b8976a-6fa2-5780-b6cd-a28e9b299d81
-- title:
--   Splitting a map of fppf sheaves onto constant ℤ
-- statement:
--   Work on the fppf site of schemes, with the Grothendieck topology `Scheme.fppfTopology` in universe $0$, and consider sheaves of additive commutative groups (objects of `AddCommGrpCat.{1}`) on it. Let $E$ be such a sheaf, let $\underline{\mathbb{Z}}$ denote the value at the group $\mathrm{ULift}\,\mathbb{Z}$ of the constant-sheaf functor `constantSheaf` for this topology, and let $g \colon E \to \underline{\mathbb{Z}}$ be a morphism of sheaves. Let $e$ be an element of the underlying type of the abelian group $E$ evaluated at the object $\mathrm{Spec}\,\mathbb{Z}$, i.e. a section of $E$ over $\mathrm{Spec}\,\mathbb{Z}$. Assume that the component of $g$ at $\mathrm{Spec}\,\mathbb{Z}$ carries $e$ to the element obtained by applying, at the group $\mathrm{ULift}\,\mathbb{Z}$, the unit of the adjunction `constantSheafAdj` associated with the terminality of $\mathrm{Spec}\,\mathbb{Z}$ in the category of schemes (`specZIsTerminal`) to the lifted integer $1$. The conclusion is that there exists a morphism of sheaves $s \colon \underline{\mathbb{Z}} \to E$ such that $s$ followed by $g$ is the identity morphism of $\underline{\mathbb{Z}}$; that is, $g$ admits a section.
--
--   This is the splitting criterion for a morphism of abelian fppf sheaves onto the constant sheaf $\underline{\mathbb{Z}}$: a global section over the terminal scheme $\mathrm{Spec}\,\mathbb{Z}$ mapping to the constant section $1$ produces a retraction. It is used in the fppf descent material, notably by [`AlgebraicGeometry.exists_section_of_fppfAmitsurTrivial`](thm.html#AlgebraicGeometry.exists_section_of_fppfAmitsurTrivial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_fppf_exists_section_of_map_eq_unit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory Abelian Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.fppf_exists_section_of_map_eq_unit
    {E : CategoryTheory.Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}}
    (g : E ⟶ (CategoryTheory.constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj (.of (ULift.{1} ℤ)))
    (e : ToType (E.obj.obj (op (Spec (.of ℤ)))))
    (he : g.hom.app (op (Spec (.of ℤ))) e =
      (CategoryTheory.constantSheafAdj Scheme.fppfTopology.{0} AddCommGrpCat.{1}
          AlgebraicGeometry.specZIsTerminal).unit.app (.of (ULift.{1} ℤ)) (ULift.up 1)) :
    ∃ s : (CategoryTheory.constantSheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1}).obj (.of (ULift.{1} ℤ)) ⟶ E,
      s ≫ g = 𝟙 _ := by sorry
