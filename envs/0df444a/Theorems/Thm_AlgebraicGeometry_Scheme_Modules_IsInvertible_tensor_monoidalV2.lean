-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/779ff889-ca26-501a-bc20-2961e50c0de1
-- title:
--   Tensor product of locally trivial 𝒪_X-modules is locally trivial
-- statement:
--   Let $X$ be a scheme (in a fixed universe $u$) and let $L$, $M$ be sheaves of modules on $X$, i.e. objects of `X.Modules`. Assume `IsInvertible L` and `IsInvertible M`, which by definition means: for each point $x$ of $X$ there is an open subset $U$ of $X$ with $x \in U$ such that the pullback of the module along the open immersion $U.\iota : U \to X$, formed by `Scheme.Modules.pullback U.ι`, admits an isomorphism to the unit sheaf of modules `SheafOfModules.unit` on the sheaf of rings of $U$ (the statement records the nonemptiness of the type of such isomorphisms, not a chosen one). Then the tensor product $L \otimes M$, taken with respect to the monoidal structure on `X.Modules`, again satisfies `IsInvertible`: every point of $X$ has an open neighbourhood on which the pullback of $L \otimes M$ is isomorphic to the unit module. Thus local triviality of sheaves of $\mathcal{O}_X$-modules in the above sense is stable under tensor product.
--
--   This is the closure of the class of invertible sheaves (line bundles) under tensor product, the property that makes isomorphism classes of such sheaves into a monoid and, with duals, into the Picard group; here it is what lets the rigidified relative Picard functor take values in groups. It is invoked throughout the project wherever line bundles are twisted or multiplied, for instance in the Euler-characteristic and Čech-rank computations for tensor products and twists by the pullback of the unit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor_monoidalV2 {X : AlgebraicGeometry.Scheme.{u}}
    {L M : X.Modules} (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L)
    (hM : AlgebraicGeometry.Scheme.Modules.IsInvertible M) :
    AlgebraicGeometry.Scheme.Modules.IsInvertible (L ⊗ M) := by sorry
