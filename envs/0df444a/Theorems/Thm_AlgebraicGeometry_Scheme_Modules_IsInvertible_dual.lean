-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.dual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/1e15fe31-03fb-59b2-a967-a139d425c7e4
-- title:
--   The dual of an invertible sheaf of modules is an inverse
-- statement:
--   Let $X$ be a scheme and let $L$ be an object of $X$`.Modules`, the category of sheaves of modules over the structure sheaf of $X$, which carries a monoidal closed structure with tensor product $\otimes$, unit $\mathbb{1}_{X.\mathrm{Modules}}$ (the structure sheaf viewed as a module over itself) and internal hom `ihom`. Assume `IsInvertible L`, that is: for every point $x$ of $X$ there is an open subscheme $U$ of $X$ with $x \in U$ such that the pullback of $L$ along the inclusion $U.\iota \colon U \to X$ admits an isomorphism to the unit sheaf of modules on $U$ (the type of such isomorphisms is asserted to be nonempty). Write $L^{\vee} :=$ `Scheme.Modules.dual L`, defined as the internal hom $\mathcal{H}om(L, \mathbb{1}_{X.\mathrm{Modules}})$, i.e. the value of `ihom L` at the monoidal unit. The conclusion is a conjunction: first, $L^{\vee}$ is invertible in exactly the same local sense; second, the type of isomorphisms $L \otimes L^{\vee} \cong \mathbb{1}_{X.\mathrm{Modules}}$ in $X$`.Modules` is nonempty. Thus an isomorphism is asserted to exist rather than a particular evaluation map being exhibited as one.
--
--   This is the standard statement that an invertible sheaf of modules on a scheme has an inverse in the Picard monoid, realised by its dual $\mathcal{H}om(L,\mathcal{O}_X)$. It serves as the basic formal input for working with line bundles on schemes in this development: invertibility of the sheaf attached to an effective Cartier divisor, additivity $\mathcal{O}(D_1+D_2)\cong\mathcal{O}(D_1)\otimes\mathcal{O}(D_2)$, and the existence of inverses in the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual.lean

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

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.dual
    {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules}
    (hL : AlgebraicGeometry.Scheme.Modules.IsInvertible L) :
    AlgebraicGeometry.Scheme.Modules.IsInvertible (AlgebraicGeometry.Scheme.Modules.dual L) ∧
      Nonempty (L ⊗ AlgebraicGeometry.Scheme.Modules.dual L ≅ 𝟙_ X.Modules) := by sorry
