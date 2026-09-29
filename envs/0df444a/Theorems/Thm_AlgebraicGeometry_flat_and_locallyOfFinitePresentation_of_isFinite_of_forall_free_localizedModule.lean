-- Prove2me | Theorems.Thm_AlgebraicGeometry_flat_and_locallyOfFinitePresentation_of_isFinite_of_forall_free_localizedModule
-- name    : AlgebraicGeometry.flat_and_locallyOfFinitePresentation_of_isFinite_of_forall_free_localizedModule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/269731c7-28cb-544f-a0b1-24ee5140d11f
-- title:
--   Finite morphisms with pointwise free direct image are flat
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe) and let $\pi : X \to Y$ be a morphism that is finite, with $Y$ locally Noetherian. Assume the following pointwise freeness hypothesis: for every point $y$ of $Y$ there exist an open subset $U \subseteq Y$, a proof that $U$ is affine, and a proof that $y \in U$, such that, when $\Gamma(X, \pi^{-1}U)$ is made into an algebra over $\Gamma(Y, U)$ by the ring homomorphism $\pi^\sharp$ on sections over $U$, the localisation of the $\Gamma(Y,U)$-module $\Gamma(X, \pi^{-1}U)$ at the complement of the prime ideal $\mathfrak p$ of $\Gamma(Y,U)$ corresponding to $y$ under the affine open $U$ (that is, $\mathrm{LocalizedModule}$ along $\mathfrak p^{\mathrm c}$) is a free module over the local ring $\Gamma(Y,U)_{\mathfrak p}$. The conclusion is the conjunction of two properties of morphisms of schemes: $\pi$ is flat, and $\pi$ is locally of finite presentation.
--
--   This is the standard local criterion that a finite morphism to a locally Noetherian base whose direct image is free at each point of the base is flat (and then automatically finite locally free); compare EGA IV 11.3.10. It is used in the construction of models of modular curves, where flatness of the structural map of an Igusa-type scheme, and of the projection attached to a Deligne–Rapoport model package, is deduced from freeness of the module of sections at each point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_flat_and_locallyOfFinitePresentation_of_isFinite_of_forall_free_localizedModule.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.flat_and_locallyOfFinitePresentation_of_isFinite_of_forall_free_localizedModule
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [IsLocallyNoetherian Y]
    (h : ∀ y : Y, ∃ (U : Y.Opens) (hU : IsAffineOpen U) (hy : y ∈ U),
      letI := (π.app U).hom.toAlgebra
      Module.Free (Localization.AtPrime (hU.primeIdealOf ⟨y, hy⟩).asIdeal)
        (LocalizedModule (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl Γ(X, π ⁻¹ᵁ U))) :
    Flat π ∧ LocallyOfFinitePresentation π := by sorry
