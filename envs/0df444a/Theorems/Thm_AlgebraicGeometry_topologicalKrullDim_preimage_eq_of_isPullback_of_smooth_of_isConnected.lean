-- Prove2me | Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isPullback_of_smooth_of_isConnected
-- name    : AlgebraicGeometry.topologicalKrullDim_preimage_eq_of_isPullback_of_smooth_of_isConnected
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/9aedd41f-2ac8-59a2-8fc3-b42e94250b4c
-- title:
--   Base-change invariance of connected smooth fibre dimension
-- statement:
--   Let $X$, $S$, $X'$, $S'$ be schemes (in the bottom universe), let $f : X \to S$ be a smooth morphism, let $b : S' \to S$, $f' : X' \to S'$ and $g : X' \to X$ be morphisms such that the square with sides $g$, $f'$ on one pair and $f$, $b$ on the other is cartesian, i.e. $g$ followed by $f$ equals $f'$ followed by $b$ and $X'$ together with $g, f'$ is a pullback of $f$ and $b$. Let $s'$ be a point of the underlying space of $S'$, put $s = b(s')$ for its image under the map of underlying spaces, and assume the set-theoretic fibre $f^{-1}(\{s\})$ is connected, that is, nonempty and preconnected. Then the topological Krull dimensions of the two fibres, taken as subspaces of the underlying spaces of $X'$ and $X$ and valued in $\mathrm{WithBot}\,\mathbb{N}_\infty$, agree: $$\dim f'^{-1}(\{s'\}) = \dim f^{-1}(\{s\}).$$
--
--   This is the smooth, connected-fibre case of the invariance of fibre dimension under base change (EGA IV, 4.1.4, combined with the constancy of the relative dimension of a smooth morphism on connected sources). It serves as a geometric input for the results on connectedness and fibre dimension of base-changed smooth morphisms, and thence for the work on polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isPullback_of_smooth_of_isConnected.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.topologicalKrullDim_preimage_eq_of_isPullback_of_smooth_of_isConnected
    {X S X' S' : Scheme.{0}} (f : X ⟶ S) (hs : Smooth f) (b : S' ⟶ S) (f' : X' ⟶ S') (g : X' ⟶ X)
    (hg : IsPullback g f' f b) (s' : ↥S') (hconn : _root_.IsConnected (f.base ⁻¹' {b.base s'})) :
    topologicalKrullDim ↥(f'.base ⁻¹' {s'}) = topologicalKrullDim ↥(f.base ⁻¹' {b.base s'}) := by sorry
