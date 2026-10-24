-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_finite_and_surjective_of_distinct_images_of_finite_cover
-- name    : AlgebraicGeometry.SmoothProperCurve.finite_and_surjective_of_distinct_images_of_finite_cover
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-23T12:47:53.218054+00:00
-- url     : https://prove2.me/theorems/3ca580bf-b65e-4dc6-870e-a0c86e3b3c63
-- title:
--   Nonconstant maps to integral finite covers of proper curves are finite and surjective
-- statement:
--   Let $K$ be a field, let $C$ be a smooth proper integral $K$-curve, and let $g:W\to C$ be finite and surjective with $W$ integral. Let $D$ be a smooth proper integral $K$-curve and $f:D\to W$ a morphism over $K$. If two $K$-rational points $a,b$ of $D$ have distinct images as $K$-rational points of $W$, then
--
--   $$f:D\longrightarrow W\quad\text{is finite and surjective.}$$
--
--   The target $W$ may be singular. Neither algebraic closedness of $K$ nor separability of any map is required. This is a derived version of the proper-curve finiteness criterion for the displayed integral finite cover of a smooth curve. It upgrades a selected smooth curve with nonconstant image to an actual finite cover.
-- source:
--   Derived consequence of Stacks Project, Lemma 53.2.4, https://stacks.math.columbia.edu/tag/0CCL (finiteness of nonconstant maps from proper curves), and Lemma 29.45.9, https://stacks.math.columbia.edu/tag/0ECG (dimension under integral surjective morphisms). The target W is an integral proper curve. Distinct K-rational images ensure geometric nonconstancy; the proper image is a closed irreducible subset with more than one point, hence all of W. This is a derived consequence, not a literal transcription of a single source statement.

import Mathlib
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.SmoothProperCurve.finite_and_surjective_of_distinct_images_of_finite_cover
    (K : Type u) [Field K] {C W D : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsIntegral C] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (g : W ⟶ C)
    [IsIntegral W] [IsFinite g] [Surjective g]
    (d : D ⟶ Spec (.of K)) [IsIntegral D] [IsProper d]
    [SmoothOfRelativeDimension 1 d] (f : D ⟶ W) (hf : f ≫ (g ≫ c) = d)
    (a b : Spec (.of K) ⟶ D) (ha : a ≫ d = 𝟙 _) (hb : b ≫ d = 𝟙 _)
    (hne : a ≫ f ≠ b ≫ f) : IsFinite f ∧ Surjective f := by sorry
