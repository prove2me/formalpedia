-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/4438d1ef-0b68-58ed-aad8-cc29ee3112f0
-- title:
--   Tensor product of invertible sheaves of modules is invertible
-- statement:
--   Let $X$ be a scheme and let $L$, $M$ be objects of the category `X.Modules` of sheaves of modules over the sheaf of rings `X.ringCatSheaf`. Invertibility of an object $N$ is taken in the sense of the predicate [`AlgebraicGeometry.Scheme.Modules.IsInvertible`](def/AlgebraicGeometry_RelativePicardFunctor.html#L16): for every point $x$ of $X$ there is an open subset $U$ of $X$ with $x \in U$ such that the pullback of $N$ along the open immersion $U.\iota \colon U \to X$ is isomorphic, in the category of sheaves of modules on $U$, to the unit object `SheafOfModules.unit` of the ring sheaf of the scheme $U$ — the existence of such an isomorphism being asserted as a `Nonempty` statement, so the trivialisations are not part of the data. Assuming $L$ and $M$ both satisfy this local triviality condition, the theorem asserts that the tensor product $L \otimes M$, formed with the monoidal structure on `X.Modules`, again satisfies it: every point of $X$ has an open neighbourhood on which $L \otimes M$ pulls back to the unit sheaf of modules.
--
--   This is the closure of the class of invertible sheaves (line bundles) on a scheme under tensor product, the property making isomorphism classes of invertible sheaves a monoid and, with duals, the Picard group. It is used throughout the construction of the rigidified relative Picard functor and of line bundles on curve models, for instance in establishing additivity of degree and in the many divisor-class computations that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor {X : AlgebraicGeometry.Scheme.{u}}
    {L M : X.Modules} (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L)
    (hM : AlgebraicGeometry.Scheme.Modules.IsInvertible M) :
    AlgebraicGeometry.Scheme.Modules.IsInvertible (L ⊗ M) := by sorry
