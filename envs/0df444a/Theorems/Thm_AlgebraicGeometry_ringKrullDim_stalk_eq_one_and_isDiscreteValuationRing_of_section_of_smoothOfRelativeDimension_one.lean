-- Prove2me | Theorems.Thm_AlgebraicGeometry_ringKrullDim_stalk_eq_one_and_isDiscreteValuationRing_of_section_of_smoothOfRelativeDimension_one
-- name    : AlgebraicGeometry.ringKrullDim_stalk_eq_one_and_isDiscreteValuationRing_of_section_of_smoothOfRelativeDimension_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/0fb30009-c4b4-5350-bd82-9f16a4928398
-- title:
--   Local ring at a rational point of a smooth relative curve is a DVR
-- statement:
--   Let $k$ be a field and let $c\colon X \to \operatorname{Spec} k$ be a morphism of schemes which is smooth of relative dimension $1$, in the sense of the Mathlib class `SmoothOfRelativeDimension 1 c`. Suppose $\sigma\colon \operatorname{Spec} k \to X$ is a section of $c$, that is, a morphism with $\sigma$ followed by $c$ equal to the identity of $\operatorname{Spec} k$; write $x = \sigma(\mathfrak{pt})$ for the image under the underlying continuous map of the closed point of $\operatorname{Spec} k$. The assertion is twofold: the Krull dimension of the local ring $\mathcal{O}_{X,x}$, taken as an element of $\mathbb{N} \cup \{\pm\infty\}$ in the `ringKrullDim` sense, equals $1$; and $\mathcal{O}_{X,x}$ is a discrete valuation ring, the conclusion being packaged as the existence of an `IsDomain` instance on $\mathcal{O}_{X,x}$ together with, relative to it, the property `IsDiscreteValuationRing`.
--
--   This is the standard local description of a smooth relative curve at a rational point: such a point is a regular point of dimension one, so its local ring is a discrete valuation ring. It is used in the analysis of the local rings of the integral model of the modular curve treated in [`ModularCurve.XHDRModelAtP.isIntegrallyClosed_stalk_and_ringKrullDim_eq_two_of_isIso_residueFieldMap_of_not_mem_range_comp`](thm.html#ModularCurve.XHDRModelAtP.isIntegrallyClosed_stalk_and_ringKrullDim_eq_two_of_isIso_residueFieldMap_of_not_mem_range_comp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ringKrullDim_stalk_eq_one_and_isDiscreteValuationRing_of_section_of_smoothOfRelativeDimension_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory
open AlgebraicGeometry
open IsLocalRing

universe u

theorem AlgebraicGeometry.ringKrullDim_stalk_eq_one_and_isDiscreteValuationRing_of_section_of_smoothOfRelativeDimension_one
    {k : Type u} [Field k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 c]
    (σ : Spec (CommRingCat.of k) ⟶ X) (hσ : σ ≫ c = 𝟙 _) :
    ringKrullDim (X.presheaf.stalk (σ.base (closedPoint k))) = 1 ∧
      ∃ _ : IsDomain (X.presheaf.stalk (σ.base (closedPoint k))), IsDiscreteValuationRing (X.presheaf.stalk (σ.base (closedPoint k))) := by sorry
