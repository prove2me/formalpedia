-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint
-- name    : AlgebraicGeometry.RelEffCartierDiv.pullbackAlong_ofPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/71cb31a7-c159-5fde-99c3-f6211c5265c5
-- title:
--   Base change of the degree-one divisor of a point
-- statement:
--   Let $f \colon \mathcal{C} \to S$ be a separated morphism of schemes, let $g \colon T \to S$ and $g' \colon T' \to S$ be two $S$-schemes, let $a \colon T' \to \mathcal{C}$ satisfy $a \circ f = g'$ in diagrammatic order (i.e. $f \circ a = g'$), and let $\varphi \colon T \to T'$ satisfy $g' \circ \varphi = g$. Here a relative effective Cartier divisor of degree $r$ on $\mathcal{C}$ over a base $g \colon T \to S$ is a quasi-coherent ideal sheaf datum $I$ on $\mathcal{C} \times_S T$ whose closed subscheme, composed with the second projection to $T$, is finite, flat and locally of finite presentation and has fibre rank $r$ at every point of $T$; `RelEffCartierDiv.ofPoint` attaches to $a$ the divisor of degree $1$ whose ideal is the kernel ideal of the graph $\langle a, \mathrm{id}_{T'}\rangle \colon T' \to \mathcal{C} \times_S T'$, and `pullbackAlong` pulls a divisor back along $\varphi$ by taking the inverse image of its ideal under $\mathrm{id}_{\mathcal{C}} \times \varphi \colon \mathcal{C} \times_S T \to \mathcal{C} \times_S T'$. The assertion is the equality, as divisors of degree $1$ over $g$, of the pullback along $\varphi$ of the divisor of $a$ and the divisor of the point $a \circ \varphi \colon T \to \mathcal{C}$.
--
--   This is the naturality in the base of the assignment sending an $S$-point of $\mathcal{C}$ to its associated degree-one relative divisor; together with the bijectivity of that assignment it identifies the functor $T \mapsto \operatorname{Div}^1_{\mathcal{C}/S}(T)$ with the functor of points of $\mathcal{C}$ over $S$. It is used throughout the construction of the universal divisor and of divisors on relative curves, being cited by the splitting and line-bundle comparison results for relative effective Cartier divisors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint.lean

import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.pullbackAlong_ofPoint
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {T T' : Scheme.{u}} {g : T ⟶ S}
    {g' : T' ⟶ S} (a : T' ⟶ 𝒞) (ha : a ≫ f = g') (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    (RelEffCartierDiv.ofPoint f a ha).pullbackAlong φ hφ =
      RelEffCartierDiv.ofPoint f (φ ≫ a) (by rw [Category.assoc, ha, hφ]) := by sorry
