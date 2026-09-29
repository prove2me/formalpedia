-- Prove2me | Theorems.Thm_AlgebraicGeometry_bijective_app_of_bijective_appTop_morphismRestrict
-- name    : AlgebraicGeometry.bijective_app_of_bijective_appTop_morphismRestrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/2ef493a4-5145-5ade-9ee8-392753b20755
-- title:
--   Bijectivity on sections over U from the restricted morphism
-- statement:
--   Let $X$ and $B$ be schemes, let $p \colon X \to B$ be a morphism of schemes, and let $U$ be an open subscheme of $B$ (an element of `B.Opens`). Write $p \mid_ U$ for the restriction of $p$ over $U$, a morphism from the open subscheme of $X$ cut out by $p^{-1}(U)$ to the open subscheme $U$ of $B$, and write `appTop` for the component at the top open of the map of structure sheaves induced by a morphism, i.e. the induced map on global sections. The hypothesis is that $(p \mid_ U)$`.appTop`, the map $\Gamma(U, \mathcal{O}_U) \to \Gamma(p^{-1}(U), \mathcal{O}_{p^{-1}(U)})$ on global sections of the restricted morphism, is a bijective function. The conclusion is that `p.app U`, the component at $U$ of the comparison map of $p$, namely $\Gamma(U, \mathcal{O}_B) \to \Gamma(p^{-1}(U), \mathcal{O}_X)$, is likewise bijective. Both maps are morphisms of commutative rings, and bijectivity is asserted of the underlying functions.
--
--   This is the bookkeeping step identifying the sections of $\mathcal{O}_B$ over an open $U$, and of $\mathcal{O}_X$ over $p^{-1}(U)$, with the global sections of the open subschemes $U$ and $p^{-1}(U)$, so that a statement about the restricted morphism $p \mid_ U$ transfers to a statement about $p$ over $U$. It is used in the proofs that a proper flat morphism whose fibrewise maps on global sections are bijective has bijective maps on sections over opens.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_bijective_app_of_bijective_appTop_morphismRestrict.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem AlgebraicGeometry.bijective_app_of_bijective_appTop_morphismRestrict {X B : Scheme.{u}} (p : X ⟶ B) (U : B.Opens)
    (h : Function.Bijective (p ∣_ U).appTop) : Function.Bijective (p.app U) := by sorry
