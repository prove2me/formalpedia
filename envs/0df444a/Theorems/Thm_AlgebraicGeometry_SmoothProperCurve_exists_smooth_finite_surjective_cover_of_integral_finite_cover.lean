-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_smooth_finite_surjective_cover_of_integral_finite_cover
-- name    : AlgebraicGeometry.SmoothProperCurve.exists_smooth_finite_surjective_cover_of_integral_finite_cover
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-22T17:49:54.654008+00:00
-- url     : https://prove2.me/theorems/a533e230-5d90-49c3-8567-b612221098da
-- title:
--   Smoothing an integral finite cover of a smooth proper curve
-- statement:
--   Let $K$ be an algebraically closed field, let $C$ be a smooth proper integral curve over $K$, and let $g:W\to C$ be a finite surjective morphism with $W$ integral. There exist an integral scheme $D$ and a finite surjective morphism $\nu:D\to W$ such that
--
--   $$D\xrightarrow{\nu}W\xrightarrow{g}C\longrightarrow\operatorname{Spec}K\quad\text{is smooth of relative dimension }1.$$
--
--   The scheme $D$ is thus a smooth proper integral curve. Neither $W$ nor $g$ is assumed smooth, and the finite maps may be inseparable. This is the finite normalization consequence of the cited results for curves over a perfect field, specialized to an algebraically closed field. The statement asserts existence of the finite cover and does not require a chosen normalization construction.
-- source:
--   Derived consequence of Stacks Project, Lemma 33.27.1, https://stacks.math.columbia.edu/tag/0BXR (normalization of a variety is finite and birational), Theorem 53.2.6, https://stacks.math.columbia.edu/tag/0BY1 (normal proper curve models), and Lemma 53.2.8, https://stacks.math.columbia.edu/tag/0BY3 (smoothness over a perfect field). A finite integral surjective cover of a proper integral curve is an integral proper curve; normalize it. This is an explicit consequence rather than a verbatim source statement.

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.SmoothProperCurve.exists_smooth_finite_surjective_cover_of_integral_finite_cover
    (K : Type u) [Field K] [IsAlgClosed K] {C W : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsIntegral C] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (g : W ⟶ C)
    [IsIntegral W] [IsFinite g] [Surjective g] :
    ∃ (D : Scheme.{u}) (ν : D ⟶ W),
      IsIntegral D ∧ IsFinite ν ∧ Surjective ν ∧
        SmoothOfRelativeDimension 1 ((ν ≫ g) ≫ c) := by sorry
