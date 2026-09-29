-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/0d8777b4-2221-5e34-abc4-53fad4f4f251
-- title:
--   Descent of morphisms of invertible modules along affine faithfully flat maps
-- statement:
--   Let $q \colon Y' \to Y$ be a morphism of schemes (in a fixed universe) which is an affine morphism, flat and surjective, and let $L_1, L_2$ be sheaves of modules on $Y$, each assumed invertible in the sense of the project predicate `Scheme.Modules.IsInvertible`: for every point $x$ of $Y$ there is an open subscheme $U \subseteq Y$ with $x \in U$ such that the pullback of the module along the inclusion $U.\iota$ is isomorphic to the unit module $\mathcal O_U$ viewed as a module over itself. Form the pseudofunctor $X \mapsto \mathbf{Mod}(\mathcal O_X)$, $f \mapsto f^{*}$ given by `Scheme.Modules.pseudofunctor` followed by `Bicategory.Adj.forget₁`, and apply Mathlib's descent-data construction `toDescentData` to the one-element family of morphisms indexed by `Unit` whose single member is $q$. The assertion is that the resulting map on morphisms, from $\operatorname{Hom}_{\mathcal O_Y}(L_1, L_2)$ to the set of morphisms of descent data between the images of $L_1$ and $L_2$, is bijective: every morphism $q^{*}L_1 \to q^{*}L_2$ compatible with the descent data comes from a unique morphism $L_1 \to L_2$.
--
--   This is the fpqc (here: affine faithfully flat) descent statement for morphisms of invertible modules, the "full faithfulness" half of flat descent in the form needed for line bundles. It is obtained by combining the Zariski-local statement [`AlgebraicGeometry.Scheme.Modules.toDescentData_map_bijective_of_openCover`](thm.html#AlgebraicGeometry.Scheme.Modules.toDescentData_map_bijective_of_openCover) for open covers with the case of the unit module [`AlgebraicGeometry.Scheme.Modules.toDescentData_map_bijective_unit_of_flat_of_surjective`](thm.html#AlgebraicGeometry.Scheme.Modules.toDescentData_map_bijective_unit_of_flat_of_surjective), and it feeds the comparison of rigidified line bundles under flat base change used in the relative Picard functor, for instance [`AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_of_pullback_of_isAffineHom_of_flat_of_surjective_of_bijective_sections`](thm.html#AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_of_pullback_of_isAffineHom_of_flat_of_surjective_of_bijective_sections).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.toDescentData_map_bijective_of_isAffineHom_of_flat_of_surjective
    {Y Y' : Scheme.{u}} (q : Y' ⟶ Y) [IsAffineHom q] [Flat q] [Surjective q]
    (L₁ L₂ : Y.Modules) (h₁ : Scheme.Modules.IsInvertible L₁) (h₂ : Scheme.Modules.IsInvertible L₂) :
    Function.Bijective
      ((((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).toDescentData
        (fun _ : Unit => q)).map : (L₁ ⟶ L₂) → _) := by sorry
