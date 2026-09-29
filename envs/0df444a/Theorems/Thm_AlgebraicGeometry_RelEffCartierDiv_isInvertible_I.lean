-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
-- name    : AlgebraicGeometry.RelEffCartierDiv.isInvertible_I
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/ab490839-55fa-5eef-92db-3de0b69e3ca7
-- title:
--   Relative effective divisors on smooth relative curves are Cartier
-- statement:
--   Let $f \colon \mathcal{C} \to S$ be a morphism of schemes which is separated and smooth of relative dimension $1$, let $r$ be a natural number, and let $g \colon T \to S$ be an arbitrary morphism of schemes. Let $D$ be a relative effective divisor of degree $r$ for $f$ over $g$, that is: an ideal sheaf datum $D.I$ on the fibre product $\mathcal{C} \times_S T$ such that the composite of the closed immersion $D.I.\mathrm{subscheme\iota}$ of the associated closed subscheme with the second projection $\mathcal{C} \times_S T \to T$ is finite, flat and locally of finite presentation, and has fibre rank exactly $r$ at every point $t$ of $T$. The assertion is that $D.I$ is invertible in the sense of the predicate `IsInvertible`: for every point $x$ of $\mathcal{C} \times_S T$ there are an affine open $U$ and a section $u \in \Gamma(\mathcal{C} \times_S T, U)$ with $x$ in the basic open set $D(u)$, together with an element $h$ of $\Gamma$ of the affine basic open $D(u)$ which is a non-zerodivisor there and generates the ideal cut out by $D.I$ on that open: $D.I(D(u)) = (h)$.
--
--   This is the statement that a closed subscheme of a smooth relative curve which is finite, flat and locally of finite presentation of degree $r$ over the base is a relative effective Cartier divisor, in the relative dimension one case. It is the basic local structure result underlying the divisor and Picard-group formalism for curves in this development, and is invoked throughout the constructions with relative divisors, line bundles and Picard functors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicCurve_RelCartier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.isInvertible_I
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f] {r : ℕ}
    {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) : D.I.IsInvertible := by sorry
