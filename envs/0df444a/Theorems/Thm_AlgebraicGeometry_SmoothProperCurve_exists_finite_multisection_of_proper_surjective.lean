-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_finite_multisection_of_proper_surjective
-- name    : AlgebraicGeometry.SmoothProperCurve.exists_finite_multisection_of_proper_surjective
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-13T16:39:55.26+00:00
-- url     : https://prove2.me/theorems/7c5841f9-f8c6-47ba-9796-3e74cb415014
-- title:
--   A finite multisection of a proper surjection onto a smooth curve
-- statement:
--   Let $K$ be an algebraically closed field, let $C$ be a smooth proper integral curve over $K$, and let $p:Z\to C$ be a proper surjective morphism. There exist a smooth proper integral curve $D$ over $K$ and a morphism $b:D\to Z$ such that
--
--   $$g=p\circ b:D\longrightarrow C$$
--
--   is finite and surjective. The structure morphism of $D$ is the composite of $g$ with the structure morphism of $C$.
--
--   No smoothness, reducedness, or integrality is assumed for $Z$. The map $p$ may have positive-dimensional fibres, and $g$ need not be separable. This form of the normalized multisection theorem provides finite covers of curve tests through arbitrary proper surjections.
-- source:
--   Derived normalized-multisection consequence of the Stacks Project: normalization of varieties, Lemma 33.27.1 (https://stacks.math.columbia.edu/tag/0BXR); normal proper models of curve function fields, Theorem 53.2.6 (https://stacks.math.columbia.edu/tag/0BY1); smoothness over a perfect field, Lemma 53.2.8 (https://stacks.math.columbia.edu/tag/0BY3); and finiteness of nonconstant maps of proper curves, Lemma 53.2.4 (https://stacks.math.columbia.edu/tag/0CCL). Choose a closed point of the nonempty generic fibre of p, take its reduced closure, and normalize. Its residue field is finite over K(C), so the closure has dimension one. Properness and dominance give a surjective curve map. Algebraically closed K is perfect. This states the resulting multisection consequence, not a verbatim transcription of any one lemma.

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.SmoothProperCurve.exists_finite_multisection_of_proper_surjective
    (K : Type u) [Field K] [IsAlgClosed K] {C Z : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsIntegral C] [IsProper c]
    [SmoothOfRelativeDimension 1 c] (p : Z ⟶ C) [IsProper p] [Surjective p] :
    ∃ (D : Scheme.{u}) (b : D ⟶ Z),
      IsIntegral D ∧ IsProper ((b ≫ p) ≫ c) ∧
        SmoothOfRelativeDimension 1 ((b ≫ p) ≫ c) ∧
          IsFinite (b ≫ p) ∧ Surjective (b ≫ p) := by
  sorry
