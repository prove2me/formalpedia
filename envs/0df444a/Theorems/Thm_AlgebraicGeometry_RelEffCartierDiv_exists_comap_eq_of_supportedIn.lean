-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_comap_eq_of_supportedIn
-- name    : AlgebraicGeometry.RelEffCartierDiv.exists_comap_eq_of_supportedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/966f7bc9-28e8-5f87-98fb-48798f43b0ac
-- title:
--   Restricting a relative effective divisor supported in an open
-- statement:
--   Let $c\colon\mathcal X\to S$ be a morphism of schemes, let $U$ be an open subscheme of $\mathcal X$ with open immersion $U.\iota\colon U\to\mathcal X$, let $r$ be a natural number and let $g\colon T\to S$ be a morphism. Let $D$ be a relative effective Cartier divisor of degree $r$ for $c$ along $g$, that is: a quasi-coherent ideal sheaf datum $D.I$ on the fibre product $\mathcal X\times_S T$ whose associated closed subscheme, followed by the second projection to $T$, is finite, flat and locally of finite presentation, and has fibre rank exactly $r$ at every point $t$ of $T$. Assume $D$ is supported in $U$, meaning that the support of $D.I$, as a subset of $\mathcal X\times_S T$, is contained in the preimage of $U$ under the first projection. Then there exists a relative effective Cartier divisor $D'$ of degree $r$ for the restricted family $U\to\mathcal X\to S$ along the same $g$ whose ideal sheaf datum $D'.I$ is the pullback of $D.I$ along the open immersion $U\times_S T\to\mathcal X\times_S T$ obtained as the map of pullbacks induced by $U.\iota$ and the identities of $T$ and of $S$.
--
--   This is the restriction step for relative effective divisors: a divisor whose support avoids the complement of an open $U$ of the source is already a divisor of the same relative degree for the smaller family $U\to S$, with ideal sheaf obtained by comap. It is used in [`AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn`](thm.html#AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_exists_comap_eq_of_supportedIn.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.exists_comap_eq_of_supportedIn
    {𝒳 S : Scheme.{u}} {c : 𝒳 ⟶ S} (U : 𝒳.Opens) {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv c r g) (hD : D.SupportedIn U) :
    ∃ D' : RelEffCartierDiv (U.ι ≫ c) r g,
      D'.I = D.I.comap (pullback.map (U.ι ≫ c) g c g U.ι (𝟙 T) (𝟙 S) (by simp) (by simp)) := by sorry
