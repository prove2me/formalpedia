-- Prove2me | Theorems.Thm_AlgebraicGeometry_flat_of_locallyOfFinitePresentation_of_forall_flat_pullback_snd_fibre
-- name    : AlgebraicGeometry.flat_of_locallyOfFinitePresentation_of_forall_flat_pullback_snd_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/3cab27a1-d995-59b8-a933-6571e35ee1e8
-- title:
--   Fibrewise criterion of flatness over a general base
-- statement:
--   Let $S$, $X$, $Y$ be schemes (in a fixed universe) and let $p_X \colon X \to S$, $p_Y \colon Y \to S$ and $g \colon X \to Y$ be morphisms of schemes such that $g$ followed by $p_Y$ equals $p_X$. Assume $p_X$ is flat, and that both $p_X$ and $p_Y$ are locally of finite presentation. Assume further that for every point $s$ of $S$ the second projection $X \times_Y Y_s \to Y_s$ of the pullback of $g$ along the inclusion $Y_s \hookrightarrow Y$ of the scheme-theoretic fibre $Y_s$ of $p_Y$ over $s$ is flat; that is, the base change $g_s$ of $g$ over the residue field of $s$ is flat. The conclusion is that $g$ itself is flat. No Noetherian or quasi-compactness hypothesis is imposed on $S$, $X$ or $Y$, and the fibre condition is required at all points of $S$, not merely at images of points of $X$.
--
--   This is the fibrewise criterion of flatness (critère de platitude par fibres) in its two-morphism form over an arbitrary base, deduced from the corresponding statement for finitely presented algebras and residue fields at prime ideals, [`Module.Flat.of_finitePresentation_of_forall_flat_residueField_tensorProduct`](thm.html#Module.Flat.of_finitePresentation_of_forall_flat_residueField_tensorProduct). It is used in the Čerednik–Drinfel'd part of the development to establish that certain morphisms between fake elliptic curves are finite, flat and surjective.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_flat_of_locallyOfFinitePresentation_of_forall_flat_pullback_snd_fibre.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.flat_of_locallyOfFinitePresentation_of_forall_flat_pullback_snd_fibre
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (g : X ⟶ Y) (hg : g ≫ pY = pX)
    [Flat pX] [LocallyOfFinitePresentation pX] [LocallyOfFinitePresentation pY]
    (hfib : ∀ s : S, Flat (pullback.snd g (pY.fiberι s))) :
    Flat g := by sorry
