-- Prove2me | Theorems.Thm_AlgebraicGeometry_surjective_and_generalizingMap_pullback_fst_of_flat
-- name    : AlgebraicGeometry.surjective_and_generalizingMap_pullback_fst_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/7c4a805c-8f7d-5026-9818-302db84de3d6
-- title:
--   Flat surjective base change: surjective, generalising, preserves generic points
-- statement:
--   Let $X$, $S$, $S'$ be schemes (in a fixed universe), and let $f \colon X \to S$ and $g \colon S' \to S$ be morphisms of schemes with $g$ flat and surjective. Write $p =$ `pullback.fst f g` for the first projection $X \times_S S' \to X$ of the pullback. The assertion is threefold. First, $p$ is surjective. Secondly, the underlying continuous map of $p$ is generalising: for every point $\eta$ of $X \times_S S'$ and every point $y$ of $X$ with $y \rightsquigarrow p(\eta)$ (that is, $y$ specialises to $p(\eta)$, so $y$ is a generalisation of $p(\eta)$), there is a point $\eta'$ of $X \times_S S'$ with $\eta' \rightsquigarrow \eta$ and $p(\eta') = y$. Thirdly, maximality under generalisation is transported along $p$: if $\eta$ is a point of $X \times_S S'$ such that every $\eta'$ with $\eta' \rightsquigarrow \eta$ satisfies $\eta' = \eta$, then every $y$ in $X$ with $y \rightsquigarrow p(\eta)$ satisfies $y = p(\eta)$; that is, generic points of irreducible components of $X \times_S S'$ are carried to points of $X$ admitting no proper generalisation.
--
--   This is the standard stability of surjectivity and of flatness (hence of the going-down property) under base change, together with the resulting transport of the property 'generic point of an irreducible component' along the projection. It is used, for a field extension $\kappa \subseteq k$ and $g = \operatorname{Spec} k \to \operatorname{Spec} \kappa$, to pass between generic points of components of a geometric special fibre and of the special fibre itself, in the analysis of the stalks at generic points of components of the model of $X_1(Mp)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_surjective_and_generalizingMap_pullback_fst_of_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.surjective_and_generalizingMap_pullback_fst_of_flat
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [Flat g] [Surjective g] :
    Surjective (pullback.fst f g) ∧ GeneralizingMap (pullback.fst f g).base ∧
      ∀ η : ↥(pullback f g), (∀ η' : ↥(pullback f g), η' ⤳ η → η' = η) →
        ∀ y : ↥X, y ⤳ (pullback.fst f g).base η → y = (pullback.fst f g).base η := by sorry
