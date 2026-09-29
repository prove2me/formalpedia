-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_of_forall_pullback_iso_of_isOpenImmersion
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.of_forall_pullback_iso_of_isOpenImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/fcb9121e-8841-55ea-9bf2-9630bd75070f
-- title:
--   Invertibility is local on a jointly surjective open cover
-- statement:
--   Let $Y$ be a scheme, let $I$ be an index type, let $X : I \to \mathrm{Scheme}$ be a family of schemes and let $\iota_i : X_i \to Y$ be morphisms, each an open immersion. Assume the family is jointly surjective on points: for every $y \in Y$ there are an index $i$ and a point $x \in X_i$ with $(\iota_i)(x) = y$. Let $M_i$ be a sheaf of $\mathcal O_{X_i}$-modules for each $i$, and assume each $M_i$ is invertible in the sense of the project's predicate `Scheme.Modules.IsInvertible`, namely that every point of $X_i$ has an open neighbourhood $U$ for which the pullback of $M_i$ along the inclusion $U \hookrightarrow X_i$ admits an isomorphism to the unit sheaf of modules over the ring sheaf of $U$. Let $Mg$ be a sheaf of $\mathcal O_Y$-modules, and suppose that for every $i$ there is an isomorphism between the pullback of $Mg$ along $\iota_i$ and $M_i$. Then $Mg$ is invertible in the same sense: every point of $Y$ has an open neighbourhood on which the restriction of $Mg$ is isomorphic to the unit sheaf of modules.
--
--   This is the statement that being an invertible sheaf (here: locally isomorphic to the structure sheaf) can be checked on a family of open immersions covering the base, the local data being given only up to isomorphism after pullback. It is used in the construction of invertible sheaves by gluing and Čech trivialisation data, for instance in the descent of line bundles along a family of charts and in the relative Picard functor machinery.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_of_forall_pullback_iso_of_isOpenImmersion.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.of_forall_pullback_iso_of_isOpenImmersion
    {Y : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}} (ι : ∀ i, X i ⟶ Y) [∀ i, IsOpenImmersion (ι i)]
    (hι : ∀ y : ↥Y, ∃ (i : I) (x : ↥(X i)), (ι i).base x = y)
    (M : ∀ i, (X i).Modules) (hM : ∀ i, Scheme.Modules.IsInvertible (M i))
    (Mg : Y.Modules) (ψ : ∀ i, (Scheme.Modules.pullback (ι i)).obj Mg ≅ M i) :
    Scheme.Modules.IsInvertible Mg := by sorry
