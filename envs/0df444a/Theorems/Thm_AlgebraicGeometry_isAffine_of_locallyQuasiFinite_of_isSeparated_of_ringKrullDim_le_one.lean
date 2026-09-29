-- Prove2me | Theorems.Thm_AlgebraicGeometry_isAffine_of_locallyQuasiFinite_of_isSeparated_of_ringKrullDim_le_one
-- name    : AlgebraicGeometry.isAffine_of_locallyQuasiFinite_of_isSeparated_of_ringKrullDim_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/d915ac11-497c-5c50-b2f4-37d0d2f40133
-- title:
--   Quasi-finite separated schemes over a one-dimensional base are affine
-- statement:
--   Let $R$ be a commutative ring, assumed Noetherian, whose Krull dimension satisfies $\operatorname{ringKrullDim} R \le 1$ (the inequality being taken in the extended integers, so that the zero ring, with dimension $-\infty$, is allowed). Let $X$ be a scheme and let $f \colon X \to \operatorname{Spec} R$ be a morphism of schemes which is locally quasi-finite, separated, locally of finite type and quasi-compact, these four properties being imposed as typeclass hypotheses on $f$. The conclusion is that $X$ is affine, i.e. the canonical morphism $X \to \operatorname{Spec} \Gamma(X, \mathcal{O}_X)$ is an isomorphism. Note that no flatness, properness or finiteness hypothesis on $f$ is required, and the base is not assumed reduced, integral or of dimension exactly one; in particular Artinian rings, Dedekind domains, discrete valuation rings and $\mathbb{Z}$ all qualify as bases.
--
--   This is the affineness statement underlying the scheme-theoretic form of Zariski's Main Theorem over a one-dimensional Noetherian base: a quasi-finite separated scheme of finite type over such a base is affine. It is applied in the construction of relative group laws for Jacobians of good reduction, to show that the kernel scheme of a morphism of group schemes is affine and to deduce flatness and finite type properties from local quasi-finiteness; its own proof relies on the affineness of dense open subsets of the spectrum of a one-dimensional Noetherian ring, as recorded in [`AlgebraicGeometry.isAffineOpen_of_dense_of_ringKrullDim_le_one`](thm.html#AlgebraicGeometry.isAffineOpen_of_dense_of_ringKrullDim_le_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isAffine_of_locallyQuasiFinite_of_isSeparated_of_ringKrullDim_le_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isAffine_of_locallyQuasiFinite_of_isSeparated_of_ringKrullDim_le_one
    {R : Type u} [CommRing R] [IsNoetherianRing R] (hR : ringKrullDim R ≤ 1)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyQuasiFinite f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    IsAffine X := by sorry
