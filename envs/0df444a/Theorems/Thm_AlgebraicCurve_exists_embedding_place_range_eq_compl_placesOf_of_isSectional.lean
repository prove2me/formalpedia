-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_embedding_place_range_eq_compl_placesOf_of_isSectional
-- name    : AlgebraicCurve.exists_embedding_place_range_eq_compl_placesOf_of_isSectional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/9448a132-5826-53c0-b631-fb4328799927
-- title:
--   Places off the chart U₁ are the section points
-- statement:
--   Let $k$ be a field and $X$ a scheme over $k$ via a morphism $c \colon X \to \operatorname{Spec} k$, with $X$ integral and $c$ proper and smooth of relative dimension one. Let $\mathcal V$ be a two-affine open cover of $X$, that is, a pair of affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine, and let $\sigma \colon \iota \to (\operatorname{Spec} k \to X)$ be a family of morphisms which is sectional for $\mathcal V$ and $c$: each $\sigma_i$ followed by $c$ is the identity, the image of each $\sigma_i$ on points lies in $U_0$, the complement of $U_1$ in the space of $X$ is the union of the images of the $\sigma_i$, and these images are pairwise disjoint. Regard $k$ as a subfield of the function field $k(X) =$ `X.functionField` through [`AlgebraicCurve.baseToFunctionField c`](def/AlgebraicCurve_CurveModel.html#L18) (germ at the generic point of the global sections pulled back along $c$). Then there is an injection $p$ from $\iota$ into the places of $k(X)$ over $k$ — a place being a valuation subring of $k(X)$ containing the image of $k$, distinct from $k(X)$ itself, and a principal ideal ring — such that, first, the range of $p$ is exactly the complement of [`AlgebraicCurve.placesOf c 𝒱.U1`](def/AlgebraicCurve_PlacesOf.html#L17), the set of places whose valuation subring is the image in $k(X)$ of the local ring $\mathcal O_{X,x}$ at some closed point $x$ lying in $U_1$; and second, for every $i$ the image in $k(X)$ of the stalk of $X$ at the point $\sigma_i(\text{closed point of } \operatorname{Spec} k)$ is, as a subring, the valuation subring of $p_i$.
--
--   This identifies the places of the function field of a smooth proper curve that are not centred in the affine chart $U_1$ with the boundary sections of a sectional two-affine cover, the valuation ring of the place attached to a section being the local ring of $X$ at the section point read inside $k(X)$. It supplies the indexing of the 'bad' places used in the comparison of the integral and the function-field Serre pairings for a two-chart Čech description of the curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_embedding_place_range_eq_compl_placesOf_of_isSectional.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicCurve

theorem exists_embedding_place_range_eq_compl_placesOf_of_isSectional
    {k : Type u} [Field k] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsProper c] [SmoothOfRelativeDimension 1 c]
    {ι : Type w} (σ : ι → (Spec (CommRingCat.of k) ⟶ X)) (hσ : 𝒱.IsSectional c σ) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∃ p : ι ↪ AlgebraicCurve.Place k X.functionField,
      Set.range p = (AlgebraicCurve.placesOf c 𝒱.U1)ᶜ ∧
      ∀ i, (algebraMap (X.presheaf.stalk ((σ i).base (IsLocalRing.closedPoint k))) X.functionField).range =
        (p i).toValuationSubring.toSubring := by sorry
