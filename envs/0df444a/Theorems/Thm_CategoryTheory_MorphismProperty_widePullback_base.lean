-- Prove2me | Theorems.Thm_CategoryTheory_MorphismProperty_widePullback_base
-- name    : CategoryTheory.MorphismProperty.widePullback_base
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/55759f84-dfa2-5fa9-9644-5f6be68bfd76
-- title:
--   Base morphism of a finite wide pullback lies in P
-- statement:
--   Let $C$ be a category with pullbacks and with finite wide pullbacks, and let $P$ be a class of morphisms of $C$ which is multiplicative (contains all identities and is closed under composition) and stable under base change. Fix an object $S$, a natural number $r$, a family of objects $X \colon \mathrm{Fin}\,r \to C$ and morphisms $f_i \colon X_i \to S$ for each $i \in \mathrm{Fin}\,r$, and suppose $P(f_i)$ holds for every $i$. Then the base morphism $\mathrm{WidePullback.base}\ f$ of the wide pullback of the family $f$, that is the structure morphism $X_0 \times_S \cdots \times_S X_{r-1} \to S$ of the $r$-fold fibre product of the $X_i$ over $S$, also lies in $P$. The case $r = 0$ is included, where the wide pullback is a terminal cone over the empty family and its base morphism is an isomorphism.
--
--   This is the standard stability statement that an $r$-fold fibre product over $S$ of morphisms belonging to a multiplicative, base-change-stable class again belongs to that class; applied to schemes it yields, for instance, that the $r$-fold fibre power of a proper (or flat, smooth, separated) morphism is again such. In this development it underlies the construction and properties of universal relative effective Cartier divisors, being cited by [`AlgebraicGeometry.RelEffCartierDiv.IsUniversal.isProper`](thm.html#AlgebraicGeometry.RelEffCartierDiv.IsUniversal.isProper), [`AlgebraicGeometry.RelEffCartierDiv.IsUniversal.geometricallyConnected`](thm.html#AlgebraicGeometry.RelEffCartierDiv.IsUniversal.geometricallyConnected) and `AlgebraicGeometry.RelEffCartierDiv.exists_isAffine`-type existence results.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CategoryTheory_MorphismProperty_widePullback_base.lean

import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits

theorem CategoryTheory.MorphismProperty.widePullback_base
    {C : Type u} [Category.{v} C] [HasPullbacks C] [HasFiniteWidePullbacks C]
    {P : MorphismProperty C} [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {S : C} {r : ℕ} (X : Fin r → C) (f : ∀ i, X i ⟶ S) (hf : ∀ i, P (f i)) :
    P (WidePullback.base f) := by sorry
