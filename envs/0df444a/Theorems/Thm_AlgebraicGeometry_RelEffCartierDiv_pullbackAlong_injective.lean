-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_injective
-- name    : AlgebraicGeometry.RelEffCartierDiv.pullbackAlong_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/dafcfc47-e22c-518f-b02b-94821689d142
-- title:
--   Injectivity of divisor pullback along a flat surjective base change
-- statement:
--   Let $f \colon \mathcal{C} \to S$ be a morphism of schemes, $r$ a natural number, and let $g \colon T \to S$ and $g' \colon T' \to S$ be two $S$-schemes. Let $\varphi \colon T \to T'$ be a morphism with $\varphi$ followed by $g'$ equal to $g$, and assume $\varphi$ is flat and surjective. Here a term of `RelEffCartierDiv f r g'` consists of a quasi-coherent ideal sheaf datum $I$ on the fibre product $\mathcal{C} \times_S T'$ such that the closed immersion of the corresponding closed subscheme followed by the projection $\mathcal{C} \times_S T' \to T'$ is finite, flat and locally of finite presentation, and has fibre rank (`finrank`) equal to $r$ at every point of $T'$; the operation `pullbackAlong` sends such a datum to the one on $\mathcal{C} \times_S T$ obtained by taking the inverse image of $I$ along $\mathrm{id}_{\mathcal{C}} \times \varphi \colon \mathcal{C} \times_S T \to \mathcal{C} \times_S T'$ (the morphism `mapOnProdOver f φ hφ` induced by $\mathrm{id}_{\mathcal{C}}$, $\varphi$ and $\mathrm{id}_S$). The assertion is that the map $D \mapsto D.\mathrm{pullbackAlong}\ \varphi$ from `RelEffCartierDiv f r g'` to `RelEffCartierDiv f r g` is injective. No hypothesis is imposed on $f$.
--
--   This is the elementary descent statement that a relative effective Cartier divisor of degree $r$ on $\mathcal{C}/S$ over a base $T'$ is determined by its pullback to any flatly surjective cover $T \to T'$; it is used in the construction of a universal divisor over an affine base, in [`AlgebraicGeometry.RelEffCartierDiv.exists_isUniversal_of_isAffine`](thm.html#AlgebraicGeometry.RelEffCartierDiv.exists_isUniversal_of_isAffine).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_injective.lean

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.pullbackAlong_injective
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {T T' : Scheme.{u}} {g : T ⟶ S} {g' : T' ⟶ S}
    (φ : T ⟶ T') (hφ : φ ≫ g' = g) [Flat φ] [Surjective φ] :
    Function.Injective fun D : RelEffCartierDiv f r g' => D.pullbackAlong φ hφ := by sorry
