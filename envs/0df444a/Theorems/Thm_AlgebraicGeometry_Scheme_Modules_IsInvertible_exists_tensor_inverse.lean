-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensor_inverse
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/3e663aff-17d2-5c48-98ca-3bf04a81d749
-- title:
--   Invertible sheaves of modules admit tensor inverses
-- statement:
--   Let $X$ be a scheme and let $L$ be a sheaf of modules over the structure sheaf of $X$ (an object of `X.Modules`). Assume $L$ is invertible in the sense of the project predicate [`AlgebraicGeometry.Scheme.Modules.IsInvertible`](def/AlgebraicGeometry_RelativePicardFunctor.html#L16): for every point $x$ of $X$ there is an open subset $U$ of $X$ with $x \in U$ such that the pullback of $L$ along the inclusion $U \hookrightarrow X$ is isomorphic, as a sheaf of modules on $U$, to the unit sheaf of modules $\mathcal{O}_U$ over the sheaf of rings of $U$. The conclusion asserts the existence of a sheaf of modules $M$ on $X$ which is again invertible in this local sense, together with the existence (as a nonempty type of isomorphisms, no particular one being selected) of an isomorphism $L \otimes M \cong \mathbf{1}$ in the monoidal category `X.Modules`, where $\otimes$ is the tensor product of sheaves of modules and $\mathbf{1}$ is its unit object, namely the structure sheaf $\mathcal{O}_X$ regarded as a module over itself.
--
--   This is the statement that invertible sheaves are invertible objects for the tensor product of $\mathcal{O}_X$-modules, so that the isomorphism classes of such sheaves form a group, the Picard group of $X$; classically the inverse is the dual $\mathcal{H}\!om(L,\mathcal{O}_X)$. It is used in the construction and analysis of the relative Picard functor, in particular in producing inverse pairs of line bundles from data on sections, and in Euler-characteristic computations for tensor products of sheaves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse.lean

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

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensor_inverse
    {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules}
    (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L) :
    ∃ M : X.Modules, AlgebraicGeometry.Scheme.Modules.IsInvertible M ∧
      Nonempty (L ⊗ M ≅ 𝟙_ X.Modules) := by sorry
