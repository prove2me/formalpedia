-- Prove2me | Theorems.Thm_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField
-- name    : AlgebraicGeometry.bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/de358833-02b2-5a66-a753-742694f8e734
-- title:
--   Global sections of a fibre and of a field-valued base change
-- statement:
--   Let $q \colon X \to Y$ be a morphism of schemes which is quasi-compact and quasi-separated, let $K$ be a field and let $k \colon \operatorname{Spec} K \to Y$ be a morphism of schemes; write $y = k(\mathfrak{m}_K)$ for the image under the underlying continuous map of $k$ of the closed point of $\operatorname{Spec} K$. Consider the fibre morphism `q.fiberToSpecResidueField y`, that is the projection $X_y = X \times_Y \operatorname{Spec} \kappa(y) \to \operatorname{Spec} \kappa(y)$ obtained by base change of $q$ along the canonical morphism $\operatorname{Spec} \kappa(y) \to Y$. The hypothesis is that the ring homomorphism induced by this fibre morphism on sections over the whole space, $\Gamma(\operatorname{Spec} \kappa(y), \mathcal{O}) \to \Gamma(X_y, \mathcal{O}_{X_y})$, is bijective. The conclusion is that the corresponding homomorphism for the second projection $X \times_Y \operatorname{Spec} K \to \operatorname{Spec} K$, namely $\Gamma(\operatorname{Spec} K, \mathcal{O}) \to \Gamma(X \times_Y \operatorname{Spec} K, \mathcal{O})$, is bijective as well.
--
--   This is the degree-zero case of cohomology and base change in the form needed to propagate a fibrewise normalisation $\kappa(y) \xrightarrow{\sim} \Gamma(X_y, \mathcal{O}_{X_y})$ from the residue field of a point to an arbitrary field-valued point above it. It is used in the proofs that, for a proper flat morphism all of whose fibres have only constant global functions, the map on sections is bijective.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem AlgebraicGeometry.bijective_appTop_pullback_snd_of_bijective_appTop_fiberToSpecResidueField
    {X Y : Scheme.{u}} (q : X ⟶ Y) [QuasiCompact q] [QuasiSeparated q]
    {K : Type u} [Field K] (k : Spec (CommRingCat.of K) ⟶ Y)
    (h : Function.Bijective (q.fiberToSpecResidueField (k.base (IsLocalRing.closedPoint K))).appTop) :
    Function.Bijective (pullback.snd q k).appTop := by sorry
