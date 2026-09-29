-- Prove2me | Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
-- name    : AlgebraicGeometry.not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/10178eea-b905-5457-bf3b-f9457afdbb19
-- title:
--   A smooth proper curve over a field is not affine
-- statement:
--   Let $k$ be a field and let $X$ be a scheme (in a fixed universe) equipped with a morphism $f \colon X \to \operatorname{Spec} k$, where $\operatorname{Spec} k$ is the spectrum of $k$ regarded as a commutative ring. Assume that $X$ is integral, that $f$ is proper, and that $f$ is smooth of relative dimension $1$. The conclusion is that $X$ is not affine, i.e. the canonical morphism from $X$ to the spectrum of its ring of global sections is not an isomorphism. Note that no hypothesis forces $X$ to be nonempty beyond integrality, which already includes irreducibility and hence nonemptiness; the statement is the negation of affineness, so it is the assertion that an integral scheme which is proper and smooth of relative dimension one over a field can never be affine.
--
--   This is the classical fact that a smooth complete curve over a field is not affine (equivalently, an affine scheme proper over a field is finite, so of dimension zero). It is used in the treatment of smooth proper curves, for instance in the finiteness statements for the cohomology of the structure sheaf and in the identification of the genus via Kähler differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.not_isAffine_of_isProper_of_smoothOfRelativeDimension_one {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsProper f] [SmoothOfRelativeDimension 1 f] : ¬ IsAffine X := by sorry
