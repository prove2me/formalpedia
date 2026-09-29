-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap
-- name    : AlgebraicCurve.CurveModel.surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/f9c61054-adae-5ca8-a0ef-cc68f07201c3
-- title:
--   Surjectivity and generic-or-closed points under a birational proper map
-- statement:
--   Let $k$ be a field and let $c : C \to \operatorname{Spec} k$ be a morphism of schemes with $C$ integral and $c$ proper. Let $F$ be a field equipped with a $k$-algebra structure, and let $M$ be a curve model of $F$ over $k$, i.e. the data of an integral scheme $M.C$ with a proper, smooth of relative dimension one structure morphism $M.\mathrm{toBase} : M.C \to \operatorname{Spec} k$, a ring isomorphism $\mathrm{ffEquiv} : F \cong \mathcal{O}_{M.C,\eta}$ onto the function field of $M.C$ carrying $\mathrm{algebraMap}\,k\,F$ to the map $k \to \mathcal{O}_{M.C,\eta}$ induced by $M.\mathrm{toBase}$, together with a bijection from the closed points of $M.C$ to the places of $F$ over $k$ (valuation subrings of $F$ containing the image of $k$, distinct from the whole of $F$, and principal ideal rings) under which the image of the stalk at a closed point inside the function field, transported to $F$, is exactly the corresponding valuation subring, and the requirement that every finite set of points of $M.C$ lie in a single affine open. Let $\nu : M.C \to C$ satisfy $c \circ \nu = M.\mathrm{toBase}$ and assume the stalk map of $\nu$ at the generic point of $M.C$ is an isomorphism. Then the underlying map of topological spaces of $\nu$ is surjective, and every point $z$ of $C$ is either the generic point of $C$ or such that $\{z\}$ is closed.
--
--   This is the standard statement that an integral scheme proper over $k$ which receives a birational proper map from a smooth proper curve model is swept out by that curve: the map is onto and $C$ is a curve in the point-set sense (one generic point, all others closed). It is the geometric input for the finiteness of $\nu$ and for the comparison of local rings on $C$ with those on $M.C$, and is used in the analysis of sections of sheaves on affine opens of $C$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap
    (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsIntegral C] [IsProper c]
    {F : Type v} [Field F] [Algebra k F] (M : AlgebraicCurve.CurveModel k F)
    (ν : M.C ⟶ C) (hν : ν ≫ c = M.toBase)
    (hbir : IsIso (ν.stalkMap (genericPoint M.C))) :
    Function.Surjective ν.base ∧ ∀ z : C, z = genericPoint C ∨ IsClosed ({z} : Set C) := by sorry
