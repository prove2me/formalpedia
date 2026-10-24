-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_integral_finite_multisection_of_proper_surjective
-- name    : AlgebraicGeometry.SmoothProperCurve.exists_integral_finite_multisection_of_proper_surjective
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-22T17:49:53.302724+00:00
-- url     : https://prove2.me/theorems/e2912d9a-34cb-4b57-b271-fa79382d5004
-- title:
--   An integral finite multisection inside a proper surjection onto a smooth curve
-- statement:
--   Let $K$ be a field, let $C$ be a smooth proper integral curve over $K$, and let $p:Z\to C$ be a proper surjective morphism. There exist an integral scheme $W$ and a closed immersion $i:W\hookrightarrow Z$ such that
--
--   $$p\circ i:W\longrightarrow C\quad\text{is finite and surjective.}$$
--
--   The scheme $W$ is therefore an integral proper curve over $K$. No reducedness, smoothness, or integrality is required of $Z$, and no separability is required of the finite map. The field need not be algebraically closed. This is a derived finite-multisection consequence of the cited dimension and proper-curve finiteness results; it supplies the integral curve before normalization.
-- source:
--   Derived consequence: Stacks Project, Section 29.52, Lemma 29.52.7, https://stacks.math.columbia.edu/tag/02NV (generic finiteness and finite function-field extension); Section 10.116, Lemma 10.116.1, https://stacks.math.columbia.edu/tag/07NB (dimension and transcendence degree); Lemma 53.2.4, https://stacks.math.columbia.edu/tag/0CCL (finiteness of a nonconstant map from a proper curve). Choose a closed point in the nonempty finite-type generic fibre and take its reduced closure in Z. This finite-multisection formulation is a derived consequence, not a literal transcription of a single lemma.

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.SmoothProperCurve.exists_integral_finite_multisection_of_proper_surjective
    (K : Type u) [Field K] {C Z : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsIntegral C] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (p : Z ⟶ C) [IsProper p] [Surjective p] :
    ∃ (W : Scheme.{u}) (i : W ⟶ Z),
      IsIntegral W ∧ IsClosedImmersion i ∧ IsFinite (i ≫ p) ∧ Surjective (i ≫ p) := by sorry
