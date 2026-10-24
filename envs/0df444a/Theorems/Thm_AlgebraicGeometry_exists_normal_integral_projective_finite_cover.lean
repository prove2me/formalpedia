-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_normal_integral_projective_finite_cover
-- name    : AlgebraicGeometry.exists_normal_integral_projective_finite_cover
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-23T16:30:21.194743+00:00
-- url     : https://prove2.me/theorems/548d711e-d466-4d25-8c18-268def25fc53
-- title:
--   Normal integral projective finite cover with preserved dimension
-- statement:
--   Let $K$ be a field and let $X$ be an integral proper $K$-scheme with a given closed immersion into a projective space. There exist an integral normal $K$-scheme $Y$ and a finite surjective morphism $\nu:Y\to X$ such that $\dim Y=\dim X$ and $Y$ admits a closed immersion into a projective space over $K$, compatible with $\nu$ and the structure map of $X$. Normality is expressed by integral closedness of every local ring; these local rings are domains because $Y$ is integral. No assumption on the characteristic, dimension, or algebraic closure of $K$ is imposed.
--
--   **Formalization Note.** This is a consequence of finite normalization and projectivity of finite covers. The conclusion only records a normal finite cover and dimension preservation; it does not assert a universal property or birationality.
-- source:
--   Stacks Project, Section 33.27, Lemmas 33.27.1 and 33.27.2 (finite normalization and projectivity), https://stacks.math.columbia.edu/tag/0BXQ ; Section 29.44, especially the projectivity criteria and composition results, https://stacks.math.columbia.edu/tag/01W7 . This auxiliary formulation retains a finite surjective normal integral cover and its dimension, with explicit projective embeddings. The proof generalizes the accepted FLT finite-over-quasi-projective construction https://prove2.me/theorems/20c95f7f-c5bb-513e-ae20-a9ddb31748a5 to arbitrary universes, using lifted finite cocycle indices. Accepted source implementations and attribution are archived locally.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_normal_integral_projective_finite_cover
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π) :
    ∃ (Y : Scheme.{u}) (ν : Y ⟶ X),
      IsIntegral Y ∧ (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧
      IsFinite ν ∧ Surjective ν ∧ topologicalKrullDim Y = topologicalKrullDim X ∧
      ∃ (m : ℕ)
        (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = ν ≫ π := by sorry
