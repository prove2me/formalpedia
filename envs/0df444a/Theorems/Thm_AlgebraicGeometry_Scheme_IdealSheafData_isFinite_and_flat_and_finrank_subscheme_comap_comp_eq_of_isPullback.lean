-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isFinite_and_flat_and_finrank_subscheme_comap_comp_eq_of_isPullback
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.isFinite_and_flat_and_finrank_subscheme_comap_comp_eq_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/d1bf90a1-57de-50f4-ac37-e00c719f80ea
-- title:
--   Base change and constant rank of finite flat closed subschemes
-- statement:
--   Let $X$, $Y$, $S$, $T$ be schemes and let $f : X \to S$, $g : T \to S$, $y : Y \to T$ and $bc : Y \to X$ be morphisms forming a cartesian square, in the sense that `IsPullback bc y f g` holds: $bc$ followed by $f$ equals $y$ followed by $g$, and $Y$ together with these two projections is a limit of the diagram given by $f$ and $g$. Assume $S$ is locally Noetherian and its underlying topological space is preconnected. Let $I$ be an ideal sheaf datum on $X$, with associated closed immersion `I.subschemeι` from the closed subscheme cut out by $I$, and assume that `I.subschemeι` followed by $f$ is a finite morphism and a flat morphism. Then the closed immersion `(I.comap bc).subschemeι` attached to the pullback ideal sheaf $bc^{*}I$ on $Y$, followed by $y$, is again finite and flat, and for every point $t$ of $T$ and every point $s$ of $S$ the rank `finrank` of this morphism at $t$ equals the rank of `I.subschemeι` followed by $f$ at $s$. In particular the rank over $S$ is constant, and the constant is unchanged by the base change along $g$.
--
--   This is the standard statement that a finite flat closed subscheme stays finite and flat after base change and that its rank, being locally constant, is a single number over a connected locally Noetherian base, readable on any fibre of either family. It is used in the construction of sections of line bundles on models of the modular curve $X_1(p)$, where it identifies the degree of the special fibre of a divisor with its generic degree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_isFinite_and_flat_and_finrank_subscheme_comap_comp_eq_of_isPullback.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.isFinite_and_flat_and_finrank_subscheme_comap_comp_eq_of_isPullback
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (y : Y ⟶ T) (bc : Y ⟶ X)
    (H : IsPullback bc y f g) [IsLocallyNoetherian S] [PreconnectedSpace S]
    (I : X.IdealSheafData) [IsFinite (I.subschemeι ≫ f)] [Flat (I.subschemeι ≫ f)] :
    IsFinite ((I.comap bc).subschemeι ≫ y) ∧ Flat ((I.comap bc).subschemeι ≫ y) ∧
      ∀ (t : T) (s : S), ((I.comap bc).subschemeι ≫ y).finrank t = (I.subschemeι ≫ f).finrank s := by sorry
