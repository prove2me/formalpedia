-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
-- name    : AlgebraicGeometry.Scheme.Modules.IsFrameOn.pullbackLocalSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/73127650-b00d-52dc-b355-2da99edb5210
-- title:
--   Frames pull back to frames along a morphism of schemes
-- statement:
--   Let $\varphi\colon X\to Y$ be a morphism of schemes, $L$ an $\mathcal O_Y$-module (an object of `Y.Modules`), $U,V\subseteq Y$ open subsets and $s\in\Gamma(L,U)$. Assume `Scheme.Modules.IsFrameOn s V`, i.e. for every open $W\subseteq Y$ with $W\le U$ and $W\le V$ the map $\Gamma(Y,W)\to\Gamma(L,W)$, $g\mapsto g\cdot (s|_W)$, with $s|_W$ the image of $s$ under the restriction map of the presheaf of $L$ along $W\le U$, is bijective. The conclusion is `Scheme.Modules.IsFrameOn (pullbackLocalSection φ s) (φ ⁻¹ᵁ V)`: the section $\varphi^{*}s\in\Gamma((\mathtt{Modules.pullback }\varphi).obj\,L,\ \varphi^{-1}U)$ obtained as the value at $s$ of the component at $U$ of the unit of the adjunction between pullback and pushforward of modules along $\varphi$, evaluated at $L$, is a frame on the open preimage $\varphi^{-1}V$; that is, for every open $W\subseteq X$ with $W\le\varphi^{-1}U$ and $W\le\varphi^{-1}V$, the map $\Gamma(X,W)\to\Gamma(\varphi^{*}L,W)$ sending $g$ to $g$ times the restriction of $\varphi^{*}s$ to $W$ is bijective.
--
--   This is the local form of the statement that trivialisations pull back to trivialisations: a section trivialising a module over an open set remains, after pullback along an arbitrary morphism of schemes, a trivialising section over the preimage open set. It feeds the criterion `isIso_of_isFrameOn_of_iSup_eq_top`, by which a morphism of modules matching frames over a covering family is an isomorphism, and is used throughout the treatment of line bundles on relative Picard schemes and on abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsFrameOn.pullbackLocalSection
    {X Y : Scheme.{u}} (φ : X ⟶ Y) {L : Y.Modules} {U V : Y.Opens} {s : Γ(L, U)}
    (hs : Scheme.Modules.IsFrameOn s V) :
    Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection φ s) (φ ⁻¹ᵁ V) := by sorry
