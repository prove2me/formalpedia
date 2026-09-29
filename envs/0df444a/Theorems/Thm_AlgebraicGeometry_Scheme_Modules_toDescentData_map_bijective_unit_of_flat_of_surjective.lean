-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_toDescentData_map_bijective_unit_of_flat_of_surjective
-- name    : AlgebraicGeometry.Scheme.Modules.toDescentData_map_bijective_unit_of_flat_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/ae74421a-6e78-5884-8e37-80a3aeec4e9c
-- title:
--   fpqc descent of functions: mathcal O_Y → mathcal O_{Y'} descent data
-- statement:
--   Let $Y$ and $Y'$ be schemes and let $q \colon Y' \to Y$ be a morphism that is quasi-compact, flat and surjective. Consider the pseudofunctor `Scheme.Modules.pseudofunctor`, which assigns to a scheme its category of sheaves of modules over its structure sheaf and to a morphism the associated pullback–pushforward adjunction, composed with `Bicategory.Adj.forget₁`, which retains only the pullback direction; write `toDescentData` for the induced functor from modules on the base to descent data relative to a family of morphisms, and take for that family the one-element family indexed by `Unit` with single member $q$. The assertion is that the action of this functor on morphisms, taken between the unit object `SheafOfModules.unit Y.ringCatSheaf` and itself, is a bijection
--   $$\operatorname{Hom}(\mathcal O_Y, \mathcal O_Y) \longrightarrow \operatorname{Hom}\big(q^{*}\mathcal O_Y, q^{*}\mathcal O_Y\big)_{\mathrm{DD}(q)},$$
--   where the left-hand side is the endomorphism set of the structure sheaf of $Y$ regarded as a sheaf of modules over itself, and the right-hand side is the set of morphisms of descent data for $q$ between the pullbacks of that unit object, i.e. those morphisms $q^{*}\mathcal O_Y \to q^{*}\mathcal O_Y$ compatible with the canonical cocycle identifications over the iterated fibre products of $q$.
--
--   This is fpqc descent of morphisms in the case of the trivial module, equivalently the statement that the structure sheaf, viewed as the functor $X \mapsto \Gamma(X, \mathcal O_X)$, is a sheaf for the single quasi-compact faithfully flat covering $\{q\}$; no affineness of $q$ is required. It serves as the base case for descent of morphisms between invertible sheaves of modules, and is cited by [`AlgebraicGeometry.Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_toDescentData_map_bijective_unit_of_flat_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.toDescentData_map_bijective_unit_of_flat_of_surjective
    {Y Y' : Scheme.{u}} (q : Y' ⟶ Y) [QuasiCompact q] [Flat q] [Surjective q] :
    Function.Bijective
      ((((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
        (fun _ : Unit => q)).map :
          (SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf) → _) := by sorry
