-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_pullbackMap_of_comp_eq
-- name    : AlgebraicGeometry.Scheme.Hom.finrank_pullbackMap_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/1c0edee4-71c0-5bfc-8f1c-783ccb624f1d
-- title:
--   Rank of a finite flat morphism is stable under base change
-- statement:
--   Let $X$, $X'$, $S$, $T$ be schemes and let $f : X \to S$, $f' : X' \to S$, $t : T \to S$ be morphisms, together with a morphism $\pi : X' \to X$ which is a morphism over $S$ in the sense that $\pi$ followed by $f$ equals $f'$; assume $\pi$ is flat and finite (Mathlib's `AlgebraicGeometry.Flat` and `AlgebraicGeometry.IsFinite`). Let $y$ be a point of the underlying topological space of the fibre product $X \times_S T$ (the Mathlib pullback of $f$ along $t$). Consider the morphism $X' \times_S T \to X \times_S T$ obtained from the triple $(\pi, \mathrm{id}_T, \mathrm{id}_S)$ by the universal property of the pullback, i.e. the base change $\pi \times_S T$ of $\pi$ along $t$, written `pullback.map f' t f t π (𝟙 T) (𝟙 S) _ _`; the two compatibility conditions it requires reduce to the hypothesis on $\pi$, $f$, $f'$ and to functoriality of identities. The assertion is that the value of Mathlib's `Scheme.Hom.finrank` for this base-changed morphism at the point $y$ equals the value of `Scheme.Hom.finrank` for $\pi$ at the image of $y$ under the first projection `pullback.fst f t` : $X \times_S T \to X$.
--
--   This is the invariance of the rank of a finite flat (equivalently, finite locally free) morphism under base change, in the relative form in which the morphism $\pi$ is given over a base $S$ and the base change is along an arbitrary $T \to S$. It is used throughout the relative Picard-group material of the development, where finite flat morphisms of constant rank (norm and trace constructions, curve changes) have to be transported along base change without re-exhibiting the cartesian square each time.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_finrank_pullbackMap_of_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe v w u

open CategoryTheory CategoryTheory.Limits

theorem AlgebraicGeometry.Scheme.Hom.finrank_pullbackMap_of_comp_eq {X X' S T : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S) (t : T ⟶ S) (π : X' ⟶ X) (hπ : π ≫ f = f')
    [AlgebraicGeometry.Flat π] [AlgebraicGeometry.IsFinite π] (y : ↑(pullback f t)) :
    (pullback.map f' t f t π (𝟙 T) (𝟙 S) (by rw [Category.comp_id, hπ])
        (by rw [Category.comp_id, Category.id_comp])).finrank y =
      π.finrank (pullback.fst f t y) := by sorry
