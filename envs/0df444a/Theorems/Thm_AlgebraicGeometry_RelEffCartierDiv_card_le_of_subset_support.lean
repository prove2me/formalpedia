-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_card_le_of_subset_support
-- name    : AlgebraicGeometry.RelEffCartierDiv.card_le_of_subset_support
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/fcf02fb9-c673-57ae-a14c-16f1cda7d28f
-- title:
--   A degree r relative divisor over a field has at most r support points
-- statement:
--   Let $\mathcal{C}$ and $S$ be schemes, $f \colon \mathcal{C} \to S$ a morphism, $r$ a natural number, $k$ a field and $x \colon \operatorname{Spec} k \to S$ a $k$-point of $S$. Let $D$ be a term of `RelEffCartierDiv f r x`, that is: an ideal sheaf datum $D.I$ on the fibre product $\mathcal{C} \times_S \operatorname{Spec} k$ such that the closed immersion $\zeta$ of the closed subscheme cut out by $D.I$, followed by the projection $\mathrm{pullback.snd}\ f\ x$ to $\operatorname{Spec} k$, is finite, flat and locally of finite presentation, and has $\mathrm{finrank}$ equal to $r$ at every point $t$ of $\operatorname{Spec} k$. Let $F$ be a finite set of points of the underlying space of $\mathcal{C} \times_S \operatorname{Spec} k$ such that every $z \in F$ lies in the support of $D.I$. Then the cardinality of $F$ is at most $r$. No further hypothesis is imposed on $f$, on $k$ or on the ambient schemes.
--
--   The statement is the scheme-theoretic count that a divisor which is finite flat of degree $r$ over a field has at most $r$ points in its support, the geometric input bounding the number of zeros of a section. It is used in the construction of relative effective Cartier divisors on the two glued projective lines, in [`AlgebraicGeometry.TwoGluedProjectiveLines.exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_and_supportedIn_of_ne_zero_of_pos`](thm.html#AlgebraicGeometry.TwoGluedProjectiveLines.exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_and_supportedIn_of_ne_zero_of_pos).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_card_le_of_subset_support.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.card_le_of_subset_support
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {k : Type u} [Field k] {x : Spec (CommRingCat.of k) ⟶ S}
    (D : RelEffCartierDiv f r x) (F : Finset ↥(pullback f x)) (hF : ∀ z ∈ F, z ∈ D.I.support) :
    F.card ≤ r := by sorry
