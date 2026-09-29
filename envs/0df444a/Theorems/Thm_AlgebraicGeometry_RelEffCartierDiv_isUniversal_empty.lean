-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isUniversal_empty
-- name    : AlgebraicGeometry.RelEffCartierDiv.isUniversal_empty
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/361f4227-9b15-5998-aeab-9445f5573837
-- title:
--   The empty divisor represents degree-zero relative divisors
-- statement:
--   Let $f \colon \mathcal{C} \to S$ be an arbitrary morphism of schemes. For an $S$-scheme $g \colon T \to S$ and $r \in \mathbb{N}$, a term of `RelEffCartierDiv f r g` consists of an ideal sheaf datum $I$ on the fibre product $\mathcal{C} \times_S T$ together with the requirements that the closed immersion of the subscheme cut out by $I$, followed by the projection $\mathcal{C} \times_S T \to T$, be finite, flat and locally of finite presentation, and that its fibre rank at every point $t$ of $T$ equal $r$. The object `RelEffCartierDiv.empty f (𝟙 S)` is the degree-zero such datum over the identity $\mathrm{id}_S \colon S \to S$ given by the unit ideal sheaf $I = \top$, whose subscheme is empty. The assertion is that this datum is universal: for every scheme $T$, every $g \colon T \to S$ and every degree-zero datum $D$ on $\mathcal{C} \times_S T$ as above, there is exactly one pair consisting of a morphism $\varphi \colon T \to S$ together with a proof that $\varphi$ followed by $\mathrm{id}_S$ equals $g$, such that the pullback of $\top$ along the induced map $\mathcal{C} \times_S T \to \mathcal{C} \times_S S$ equals $D.I$.
--
--   This is the degree-zero case of the representability of the relative divisor functor $\mathrm{Div}^r_{\mathcal{C}/S}$: the functor $\mathrm{Div}^0$ is represented by $S$ itself, with universal object the empty divisor. It is used in the construction of the representing object for divisors supported in a prescribed finite set of sections and in the inductive treatment of the affine-openness statement for universal objects.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_isUniversal_empty.lean

import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.isUniversal_empty {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) :
    (RelEffCartierDiv.empty f (𝟙 S)).IsUniversal := by sorry
