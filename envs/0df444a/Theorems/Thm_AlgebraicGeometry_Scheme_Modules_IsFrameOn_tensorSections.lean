-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections
-- name    : AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/b4faf4fb-e0bf-59d4-b135-1d8bbae242f6
-- title:
--   The tensor product of two frames is a frame
-- statement:
--   Let $X$ be a scheme, let $L$ and $M$ be objects of `X.Modules` (sheaves of modules over the structure sheaf of $X$), let $U$ and $V$ be open subsets of $X$, and let $s \in \Gamma(L,U)$ and $t \in \Gamma(M,U)$. Here a section $u \in \Gamma(N,U)$ is said to satisfy `IsFrameOn u V` when for every open $W$ with $W \le U$ and $W \le V$ the $\Gamma(X,W)$-scaling map $\Gamma(X,W) \to \Gamma(N,W)$, $g \mapsto g \cdot (u|_W)$, is bijective, $u|_W$ denoting the restriction of $u$ along the inclusion $W \le U$. Assume that $s$ is a frame on $V$ and that $t$ is a frame on $V$ in this sense. Then the section $\mathrm{tensorSections}\, s\, t \in \Gamma(L \otimes M, U)$ — the image of the elementary tensor $s \otimes_{\Gamma(X,U)} t$ of the underlying presheaf sections under the component at $U$ of `tensorSectionsHom`, i.e. of the unit of the sheafification adjunction for presheaves of modules followed by the comparison isomorphism between the sheafified presheaf tensor product and the monoidal product $L \otimes M$ in `X.Modules` — is again a frame on $V$: for every open $W \le U$ with $W \le V$, the map $g \mapsto g \cdot (\mathrm{tensorSections}\, s\, t)|_W$ from $\Gamma(X,W)$ to $\Gamma(L \otimes M, W)$ is bijective.
--
--   This is the statement that local trivialisations multiply: if $s$ and $t$ trivialise $L$ and $M$ over $V$, then $s \otimes t$ trivialises $L \otimes M$ over $V$, which is the local step behind the multiplicativity of invertibility under tensor product and behind the group law on the relative Picard group. It is used in the development of invertible sheaves of modules on schemes, for instance in the construction of deformation-class maps on relative Picard groups and in producing frames for tensor products with ideal sheaves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections.lean

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections
    {X : AlgebraicGeometry.Scheme.{u}} {L M : X.Modules} {U V : X.Opens}
    {s : Γ(L, U)} {t : Γ(M, U)}
    (hs : AlgebraicGeometry.Scheme.Modules.IsFrameOn s V)
    (ht : AlgebraicGeometry.Scheme.Modules.IsFrameOn t V) :
    AlgebraicGeometry.Scheme.Modules.IsFrameOn
      (AlgebraicGeometry.Scheme.Modules.tensorSections s t) V := by sorry
