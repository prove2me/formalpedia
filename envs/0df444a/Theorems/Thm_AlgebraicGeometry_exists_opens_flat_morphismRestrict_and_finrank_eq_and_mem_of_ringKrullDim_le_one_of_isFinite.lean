-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_opens_flat_morphismRestrict_and_finrank_eq_and_mem_of_ringKrullDim_le_one_of_isFinite
-- name    : AlgebraicGeometry.exists_opens_flat_morphismRestrict_and_finrank_eq_and_mem_of_ringKrullDim_le_one_of_isFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/eb903d25-9b52-5020-bb6d-3ab6976354a5
-- title:
--   Finite surjections onto normal schemes are locally free in codimension ≤ 1
-- statement:
--   Let $\pi\colon X\to Y$ be a morphism of schemes (in a fixed universe) which is finite and surjective, with $X$ and $Y$ integral schemes, $Y$ locally Noetherian, and assume that for every point $y$ of $Y$ the local ring $\mathcal{O}_{Y,y}$ (the stalk of the structure presheaf of $Y$ at $y$) is integrally closed in its fraction field. The assertion is the existence of an open subscheme $V$ of $Y$ and a natural number $d$ such that the restriction $\pi \mid_V$ of $\pi$ over $V$ (the base change of $\pi$ along the open immersion $V\hookrightarrow Y$) is flat and locally of finite presentation, such that the rank of $\pi \mid_V$ at every point $y$ of $V$ equals the single number $d$, and such that $V$ contains every point $y$ of $Y$ whose local ring $\mathcal{O}_{Y,y}$ has Krull dimension at most $1$. Note that $V$ is produced as one open set carrying all three properties simultaneously, with a rank $d$ independent of the point, and that the bound on $V$ from below is only that it contains the points of codimension $\le 1$; no statement is made about points of larger codimension.
--
--   This is the standard fact that a finite surjection onto a normal locally Noetherian integral scheme is finite locally free of constant rank over an open set containing all points of codimension at most one, the local rings there being fields or discrete valuation rings. It is used to obtain flatness and constancy of degree for finite surjective morphisms of integral schemes, in particular for degeneracy maps between Deligne–Rapoport models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_opens_flat_morphismRestrict_and_finrank_eq_and_mem_of_ringKrullDim_le_one_of_isFinite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_opens_flat_morphismRestrict_and_finrank_eq_and_mem_of_ringKrullDim_le_one_of_isFinite
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    ∃ (V : Y.Opens) (d : ℕ), Flat (π ∣_ V) ∧ LocallyOfFinitePresentation (π ∣_ V) ∧
      (∀ y : V, (π ∣_ V).finrank y = d) ∧
      ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 1 → y ∈ V := by sorry
