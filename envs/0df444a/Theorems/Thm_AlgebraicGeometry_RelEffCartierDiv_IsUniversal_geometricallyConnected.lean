-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_geometricallyConnected
-- name    : AlgebraicGeometry.RelEffCartierDiv.IsUniversal.geometricallyConnected
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/713d9d9a-0f9b-53ff-a95b-c4094e1259cc
-- title:
--   Geometric connectedness of a universal relative divisor scheme
-- statement:
--   Let $f \colon \mathcal{C} \to S$ be a morphism of schemes which is separated, smooth of relative dimension $1$ and geometrically connected, let $r$ be a natural number, and let $y \colon Y \to S$ be a morphism of schemes. Let $D_{\mathrm{univ}}$ be a relative effective Cartier divisor of degree $r$ for $f$ over $y$, that is, an ideal sheaf datum $I$ on the pullback $\mathcal{C} \times_S Y$ such that the closed immersion of the associated closed subscheme followed by the projection to $Y$ is finite, flat and locally of finite presentation and has fibre rank exactly $r$ at every point of $Y$. Assume $D_{\mathrm{univ}}$ is universal: for every scheme $T$, every $g \colon T \to S$ and every relative effective Cartier divisor $D$ of degree $r$ for $f$ over $g$, there is exactly one pair consisting of a morphism $\varphi \colon T \to Y$ with $\varphi$ followed by $y$ equal to $g$ and for which the pullback of the ideal sheaf datum $I$ along the induced morphism $\mathcal{C} \times_S T \to \mathcal{C} \times_S Y$ is the ideal sheaf datum of $D$. Then $y \colon Y \to S$ is geometrically connected.
--
--   This is the connectedness half of the standard statement that, for a smooth separated curve with geometrically connected fibres, the degree-$r$ relative divisor scheme $\mathrm{Div}^r_{\mathcal{C}/S}$ is geometrically connected over $S$; it is used in establishing that the relevant relative Picard functor is represented by a proper, geometrically connected $S$-scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_geometricallyConnected.lean

import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.IsUniversal.geometricallyConnected
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [GeometricallyConnected f] {r : ℕ} {Y : Scheme.{u}} {y : Y ⟶ S}
    {Duniv : RelEffCartierDiv f r y} (hU : Duniv.IsUniversal) : GeometricallyConnected y := by sorry
