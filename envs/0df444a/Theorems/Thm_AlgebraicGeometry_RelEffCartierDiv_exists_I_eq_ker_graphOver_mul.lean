-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_graphOver_mul
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_ker_graphOver_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/f3858048-5f58-59ea-9769-720b3de528e5
-- title:
--   Splitting off a graph from a relative effective divisor
-- statement:
--   Let $f \colon \mathcal{C} \to S$ be a separated morphism of schemes which is smooth of relative dimension $1$, let $r$ be a natural number, and let $g \colon T \to S$ be an $S$-scheme. Let $D$ be a relative effective Cartier divisor of degree $r+1$ for $f$ over $g$, that is, a quasi-coherent ideal sheaf datum $D.I$ on the fibre product $\mathcal{C} \times_S T$ whose associated closed immersion, followed by the second projection to $T$, is finite, flat and locally of finite presentation, and has fibre rank exactly $r+1$ at every point $t$ of $T$. Let $a \colon T \to \mathcal{C}$ be a morphism with $a$ followed by $f$ equal to $g$, and let $\Gamma_a =$ `graphOver f a ha` be the induced section $T \to \mathcal{C} \times_S T$ with components $a$ and $\mathrm{id}_T$. Assume $D.I \le \Gamma_a.\mathrm{ker}$, the ideal sheaf datum cut out by $\Gamma_a$, i.e. the graph is contained in $D$. Then there exists a relative effective Cartier divisor $E$ of degree $r$ for $f$ over $g$ with $D.I = \Gamma_a.\mathrm{ker} \cdot E.I$.
--
--   This is the residual step in the construction of relative divisor schemes of a smooth relative curve: a degree $r+1$ relative effective divisor passing through a section splits off that section, leaving a degree $r$ relative effective divisor. It is used by [`AlgebraicGeometry.RelEffCartierDiv.exists_split`](thm.html#AlgebraicGeometry.RelEffCartierDiv.exists_split) and by [`AlgebraicGeometry.RelEffCartierDiv.isInvertible_I`](thm.html#AlgebraicGeometry.RelEffCartierDiv.isInvertible_I), and rests on the invertibility of the ideal of a section of a separated smooth relative curve ([`AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id`](thm.html#AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_graphOver_mul.lean

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_ker_graphOver_mul
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f] {r : ℕ}
    {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f (r + 1) g)
    (a : T ⟶ 𝒞) (ha : a ≫ f = g) (hle : D.I ≤ (graphOver f a ha).ker) :
    ∃ E : RelEffCartierDiv f r g, D.I = (graphOver f a ha).ker * E.I := by sorry
