-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isSheaf_functor
-- name    : AlgebraicGeometry.RelEffCartierDiv.isSheaf_functor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/f585929f-a949-5686-b254-56dada3fdf27
-- title:
--   Relative degree-r Cartier divisors form a Zariski sheaf
-- statement:
--   Let $f \colon \mathcal{C} \to S$ be a morphism of schemes (in a fixed universe) and let $r$ be a natural number. Consider the presheaf `RelEffCartierDiv.functor f r` on the opposite of the category of schemes: it assigns to a scheme $T$ the type of pairs consisting of a morphism $g \colon T \to S$ together with a datum $D$ of type `RelEffCartierDiv f r g`, that is, an ideal sheaf datum $I$ on the fibre product $\mathcal{C} \times_S T$ (pullback of $f$ along $g$) such that the composite of the inclusion of the closed subscheme cut out by $I$ with the second projection $\mathcal{C} \times_S T \to T$ is finite, flat and locally of finite presentation, and has fibre rank exactly $r$ at every point $t$ of $T$; on morphisms it sends $\varphi \colon T \to T'$ (an arrow of $\mathrm{Scheme}^{\mathrm{op}}$ in the opposite direction) to $(g, D) \mapsto (\varphi \circ g,\ D$ pulled back along $\varphi$ via `RelEffCartierDiv.pullbackAlong`, whose ideal sheaf is the comap of $I$ along the induced map of fibre products$)$. The assertion is that this presheaf of types satisfies `Presieve.IsSheaf` for `Scheme.zariskiTopology`: over every scheme, each family of such pairs indexed by a Zariski covering sieve and compatible under restriction has a unique amalgamation.
--
--   This is the Zariski-local nature of relative effective Cartier divisors of constant relative degree $r$: morphisms to $S$ glue, quasi-coherent ideal sheaves on $\mathcal{C}\times_S T$ glue along the cover of $T$, and finiteness, flatness, local finite presentation and the relative rank are local on the base. It is the descent input to [`AlgebraicGeometry.RelEffCartierDiv.exists_isUniversal`](thm.html#AlgebraicGeometry.RelEffCartierDiv.exists_isUniversal), the representability of this divisor functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_isSheaf_functor.lean

import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.isSheaf_functor
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) :
    Presieve.IsSheaf Scheme.zariskiTopology (RelEffCartierDiv.functor f r) := by sorry
