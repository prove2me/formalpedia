-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isZero_exteriorPower_of_isLocallyFreeOfRank
-- name    : AlgebraicGeometry.Scheme.Modules.isZero_exteriorPower_of_isLocallyFreeOfRank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/9b449e68-7880-5e0f-9afb-0f7c18bbf087
-- title:
--   Exterior powers above the rank of a locally free sheaf vanish
-- statement:
--   Let $X$ be a scheme, let $n, m$ be natural numbers and let $M$ be an object of the category `X.Modules` of sheaves of $\mathcal{O}_X$-modules on $X$. Assume `IsLocallyFreeOfRank n M`, that is: for every point $x$ of $X$ there is an open subset $U \subseteq X$ with $x \in U$ such that the restriction of $M$ along the inclusion $U \hookrightarrow X$, given by the pullback functor `Modules.pullback U.ι`, is isomorphic to the free sheaf of $\mathcal{O}_U$-modules on the index type `ULift (Fin n)`; assume also $n < m$. Then the object $(\bigwedge^m M)$ obtained by applying the functor `Scheme.Modules.exteriorPower X m` to $M$ — the sheafification of the presheaf of modules $V \mapsto \bigwedge^m_{\mathcal{O}_X(V)} M(V)$ — is a zero object of `X.Modules`, in the sense of `Limits.IsZero` (it is both initial and terminal).
--
--   This is the standard vanishing $\bigwedge^m \mathcal{E} = 0$ for $\mathcal{E}$ locally free of rank $n < m$, reflecting the fact that the exterior power of a free module of rank $n$ in degree $m > n$ has empty basis. It is used in establishing the multiplicativity of the determinant sheaf on short exact sequences of locally free sheaves, via `nonempty_det_succ_iso_det_tensor_of_shortExact`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isZero_exteriorPower_of_isLocallyFreeOfRank.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isZero_exteriorPower_of_isLocallyFreeOfRank
    {X : Scheme.{u}} {n m : ℕ} {M : X.Modules}
    (hM : Scheme.Modules.IsLocallyFreeOfRank n M) (h : n < m) :
    Limits.IsZero ((Scheme.Modules.exteriorPower X m).obj M) := by sorry
