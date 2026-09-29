-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_exteriorPower_free_iso_unit
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_exteriorPower_free_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/15e7e986-01d3-51eb-abc5-2aeddba97ea1
-- title:
--   bigwedgeⁿ(mathcal O_X^{⊕ n})≅mathcal O_X for the free sheaf of rank n
-- statement:
--   Let $X$ be a scheme and let $n$ be a natural number. Consider the category of sheaves of modules over the sheaf of rings $X$.`ringCatSheaf` underlying $X$, and the functor `Scheme.Modules.exteriorPower X n` on it: it sends a sheaf of modules first to its underlying presheaf of modules, then applies the presheaf-level $n$-th exterior power, whose value on an open $U$ is the exterior power $\bigwedge^n_{\mathcal O_X(U)} M(U)$ with transition maps induced functorially by the restriction maps of $M$ and of the ring presheaf, and finally sheafifies the result along the identity of the sheaf of rings of $X$. The theorem asserts that the type of isomorphisms, in the category of sheaves of modules on $X$, between the value of this functor at the free sheaf of modules `SheafOfModules.free (ULift (Fin n))` (the coproduct of copies of the unit object indexed by a lift of $\mathrm{Fin}\,n$, i.e. $\mathcal O_X^{\oplus n}$) and the unit object `SheafOfModules.unit X.ringCatSheaf` (the structure sheaf regarded as a module over itself) is nonempty. Thus an isomorphism $\bigwedge^n(\mathcal O_X^{\oplus n}) \cong \mathcal O_X$ exists; no particular isomorphism is selected.
--
--   This is the classical statement that the determinant of a trivial bundle of rank $n$ is trivial, in the form $\bigwedge^n(\mathcal O_X^{\oplus n})\cong\mathcal O_X$. It is the local input for showing that the $n$-th exterior power of a sheaf of modules that is locally free of rank $n$ is invertible, and is used in that form in the treatment of relative Picard groups and of short exact sequences arising from pushforward along thickenings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_exteriorPower_free_iso_unit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesDet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.nonempty_exteriorPower_free_iso_unit (X : Scheme.{u}) (n : ℕ) :
    Nonempty ((Scheme.Modules.exteriorPower X n).obj (SheafOfModules.free.{u} (ULift.{u} (Fin n))) ≅
      SheafOfModules.unit X.ringCatSheaf) := by sorry
