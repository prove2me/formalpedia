-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
-- name    : AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/65433a78-70b2-58b8-b926-c30cde776715
-- title:
--   Tensor product of two frames is a frame
-- statement:
--   Let $X$ be a scheme and let $L$ and $M$ be objects of `X.Modules`, that is, sheaves of modules over the structure sheaf of $X$; let $U$ and $V$ be open subsets of $X$, and let $s \in \Gamma(L,U)$ and $t \in \Gamma(M,U)$ be sections over $U$. Say that a section is a frame on $V$ when, for every open $W$ with $W \le U$ and $W \le V$, the map $\Gamma(X,W) \to \Gamma(L,W)$ sending $g$ to $g$ times the restriction of the section along the inclusion $W \le U$ is bijective; this is the predicate `IsFrameOn`. Assume $s$ is a frame on $V$ for $L$ and $t$ is a frame on $V$ for $M$. The conclusion is that the section `tensorSections s t` $\in \Gamma(L \otimes M, U)$ — the image of the elementary tensor $s \otimes_{\Gamma(X,U)} t$ of the underlying presheaf sections under the map `tensorSectionsHom`, built from the unit of the sheafification adjunction for sheaves of modules followed by the comparison isomorphism `tensorIsoSheafify` identifying the sheafified presheaf tensor product with the monoidal product $L \otimes M$ — is again a frame on $V$: for every open $W \le U$ with $W \le V$, the map $\Gamma(X,W) \to \Gamma(L \otimes M, W)$, $g \mapsto g \cdot (s \otimes t)|_W$, is bijective.
--
--   This is the multiplicativity of local trivialisations: the tensor product of two invertible sheaves is again invertible, with frame the tensor product of the given frames. It is used in the project's treatment of graded $\mathcal{O}$-algebras and their Proj presentations, where sections trivialising line bundles on distinguished opens are multiplied.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.lean

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections_monoidalV2
    {X : AlgebraicGeometry.Scheme.{u}} {L M : X.Modules} {U V : X.Opens}
    {s : Γ(L, U)} {t : Γ(M, U)}
    (hs : AlgebraicGeometry.Scheme.Modules.IsFrameOn s V)
    (ht : AlgebraicGeometry.Scheme.Modules.IsFrameOn t V) :
    AlgebraicGeometry.Scheme.Modules.IsFrameOn
      (AlgebraicGeometry.Scheme.Modules.tensorSections s t) V := by sorry
