-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_isProper
-- name    : AlgebraicGeometry.RelEffCartierDiv.IsUniversal.isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/89be4342-0c79-5987-81aa-212318e5ae9c
-- title:
--   Properness of a universal relative effective divisor base
-- statement:
--   Let $\mathcal C$ and $S$ be schemes and $f \colon \mathcal C \to S$ a morphism which is proper and smooth of relative dimension $1$, with $S$ locally Noetherian, and let $r$ be a natural number. Let $y \colon Y \to S$ be a scheme over $S$ equipped with a datum $D_{\mathrm{univ}}$ of type `RelEffCartierDiv f r y`, that is: an ideal sheaf datum $I$ on the pullback $\mathcal C \times_S Y$ such that the inclusion of the associated closed subscheme followed by the second projection to $Y$ is finite, flat and locally of finite presentation and has fibre rank exactly $r$ at every point of $Y$. Assume $D_{\mathrm{univ}}$ is universal in the sense of `IsUniversal`: for every scheme $T$, every $g \colon T \to S$ and every datum $D$ of type `RelEffCartierDiv f r g`, there is exactly one pair consisting of a morphism $\varphi \colon T \to Y$ with $\varphi$ followed by $y$ equal to $g$ and whose induced comparison morphism of products over $S$ pulls the ideal $I$ back to $D.I$. The conclusion is that $y \colon Y \to S$ is proper.
--
--   This is the properness over a locally Noetherian base of the scheme $\mathrm{Div}^r_{\mathcal C/S}$ of relative effective divisors of degree $r$ on a proper smooth relative curve, stated for an arbitrary universal pair and hence independent of any particular construction of $Y$. It feeds the analysis of the relative Picard functor, being used in the construction of open charts for the relative sub-Picard presheaf and in the properness and geometric connectedness statement for its representing object.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_isProper.lean

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.IsUniversal.isProper
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f] [SmoothOfRelativeDimension 1 f]
    [IsLocallyNoetherian S] {r : ℕ} {Y : Scheme.{u}} {y : Y ⟶ S}
    {Duniv : RelEffCartierDiv f r y} (hU : Duniv.IsUniversal) : IsProper y := by sorry
