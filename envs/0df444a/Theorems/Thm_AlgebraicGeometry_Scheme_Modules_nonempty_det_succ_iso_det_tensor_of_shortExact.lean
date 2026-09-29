-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_det_succ_iso_det_tensor_of_shortExact
-- name    : AlgebraicGeometry.Scheme.Modules.nonempty_det_succ_iso_det_tensor_of_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/dd694276-016c-539e-86d3-7892fc75d7c0
-- title:
--   Determinant of an extension of an invertible sheaf
-- statement:
--   Let $X$ be a scheme and $n$ a natural number, and let $S$ be a short complex $S.X_1 \xrightarrow{S.f} S.X_2 \xrightarrow{S.g} S.X_3$ of sheaves of modules on $X$ which is short exact (so $S.f$ is a monomorphism, $S.g$ an epimorphism, and the complex is exact). Assume: $S.X_1$ is locally free of rank $n$, in the sense that every point of $X$ has an open neighbourhood $U$ such that the pullback of $S.X_1$ along the inclusion $U \hookrightarrow X$ is isomorphic to the free sheaf of modules on $\mathrm{Fin}\,n$ (suitably lifted in universe); $S.X_2$ is locally free of rank $n+1$ in the same sense; and $S.X_3$ is invertible, in the sense that every point has an open neighbourhood $U$ on which the pullback of $S.X_3$ is isomorphic to the unit sheaf of modules of $U$. Then the type of isomorphisms $\det^{n+1} S.X_2 \cong \det^{n} S.X_1 \otimes S.X_3$ in the category of sheaves of modules on $X$ is nonempty, where $\det^{m} M$ denotes the sheafification of the presheaf $m$-th exterior power of $M$ and $\otimes$ is the monoidal tensor product of sheaves of modules.
--
--   This is the multiplicativity of the determinant line bundle along a short exact sequence of vector bundles in the case of an invertible quotient, $\det \mathcal{E} \cong \det \mathcal{E}' \otimes \mathcal{L}$. It is used in the construction of the relative Picard functor, in particular for the determinant of pushforwards along thickenings and for the twist by the ideal sheaf of a section.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_nonempty_det_succ_iso_det_tensor_of_shortExact.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesWedge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.nonempty_det_succ_iso_det_tensor_of_shortExact
    {X : Scheme.{u}} {n : ℕ} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₁ : Scheme.Modules.IsLocallyFreeOfRank n S.X₁) (h₂ : Scheme.Modules.IsLocallyFreeOfRank (n + 1) S.X₂)
    (h₃ : Scheme.Modules.IsInvertible S.X₃) :
    Nonempty (Scheme.Modules.det (n + 1) S.X₂ ≅ Scheme.Modules.det n S.X₁ ⊗ S.X₃) := by sorry
