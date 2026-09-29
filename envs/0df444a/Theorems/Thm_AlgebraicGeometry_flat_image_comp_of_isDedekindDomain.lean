-- Prove2me | Theorems.Thm_AlgebraicGeometry_flat_image_comp_of_isDedekindDomain
-- name    : AlgebraicGeometry.flat_image_comp_of_isDedekindDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/0093abf9-2f6b-5aae-b6d3-66bbae6ed1a3
-- title:
--   Flatness of the scheme-theoretic image over a Dedekind base
-- statement:
--   Let $R$ be a commutative ring which is a domain and a Dedekind domain, and let $X$ and $J$ be schemes (in a fixed universe). Let $\sigma \colon X \to J$ be a quasi-compact morphism of schemes, and let $f \colon J \to \operatorname{Spec} R$ be a morphism to the spectrum of $R$, viewed as a commutative ring object. Assume that the composite $\sigma$ followed by $f$, i.e. the structure morphism $X \to \operatorname{Spec} R$, is flat in the sense of Mathlib's morphism property `Flat`. The conclusion is that the composite of `σ.imageι`, the canonical closed immersion of the scheme-theoretic image $\sigma.\mathrm{image} \hookrightarrow J$ of $\sigma$, with $f$ is again flat; that is, the scheme-theoretic image of $X$ in $J$ is flat over $\operatorname{Spec} R$. Flatness of $X$ over $R$ and quasi-compactness of $\sigma$ are hypotheses carried as instances, as is the Dedekind hypothesis on $R$.
--
--   This is the standard fact that over a Dedekind base flatness is preserved by passing to the scheme-theoretic image of a quasi-compact morphism, the typical case being $R$ a discrete valuation ring and $X$ a scheme over the fraction field, so that the image is the flat closure of $X$ inside $J$. It is used in the construction of a relative group law on the closure of a generic fibre, in the treatment of good reduction of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_flat_image_comp_of_isDedekindDomain.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.flat_image_comp_of_isDedekindDomain
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {X J : Scheme.{u}} (σ : X ⟶ J) [QuasiCompact σ] (f : J ⟶ Spec (CommRingCat.of R)) [Flat (σ ≫ f)] :
    Flat (σ.imageι ≫ f) := by sorry
