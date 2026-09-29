-- Prove2me | Theorems.Thm_AlgebraicGeometry_eq_of_comp_eq_of_forall_specializes_of_lift_mem_range_diagonal
-- name    : AlgebraicGeometry.eq_of_comp_eq_of_forall_specializes_of_lift_mem_range_diagonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/40d99b12-8883-536a-aec4-44cafe5cb5e1
-- title:
--   Sections of an unramified morphism agreeing at one point coincide
-- statement:
--   Let $X$, $Y$, $T$ be schemes (in a fixed universe) and let $f \colon X \to Y$ be a morphism which is formally unramified and locally of finite type. Let $s, s' \colon T \to X$ be two morphisms with $s$ followed by $f$ equal to $s'$ followed by $f$, so that the pair $(s,s')$ induces a morphism $T \to X \times_Y X$ into the fibre product, namely `pullback.lift s s' h`. Let $t_0$ be a point of the underlying topological space of $T$ such that every point $t$ of $T$ specialises to $t_0$, i.e. $t_0$ lies in the closure of $\{t\}$ for each $t$ (as holds when $T$ is the spectrum of a local ring and $t_0$ its closed point). Assume finally that the image of $t_0$ under the map of topological spaces underlying $(s,s')$ belongs to the set-theoretic range of the map underlying the diagonal $\Delta_f \colon X \to X \times_Y X$. Then $s = s'$ as morphisms of schemes.
--
--   This is the uniqueness half of the lifting criterion along unramified (in particular étale) morphisms: two sections over a base all of whose points specialise to a single point, agreeing at that point after composing to the diagonal, agree everywhere. It is used in the construction of sections of the relevant modular curve model, in [`ModularCurve.XHDRModelAtP.section_eq_of_comp_chart_eq_of_base_closedPoint_eq_of_chart`](thm.html#ModularCurve.XHDRModelAtP.section_eq_of_comp_chart_eq_of_base_closedPoint_eq_of_chart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_eq_of_comp_eq_of_forall_specializes_of_lift_mem_range_diagonal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.eq_of_comp_eq_of_forall_specializes_of_lift_mem_range_diagonal
    {X Y T : Scheme.{u}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    (s s' : T ⟶ X) (h : s ≫ f = s' ≫ f) (t₀ : ↥T) (ht₀ : ∀ t : ↥T, t ⤳ t₀)
    (hΔ : (pullback.lift s s' h).base t₀ ∈ Set.range (pullback.diagonal f).base) :
    s = s' := by sorry
