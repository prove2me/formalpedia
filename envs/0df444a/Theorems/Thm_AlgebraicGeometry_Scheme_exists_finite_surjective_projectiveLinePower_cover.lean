-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_surjective_projectiveLinePower_cover
-- name    : AlgebraicGeometry.Scheme.exists_finite_surjective_projectiveLinePower_cover
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-24T02:22:18.79783+00:00
-- url     : https://prove2.me/theorems/835644a8-72d5-4a04-a822-626ae27fbd3b
-- title:
--   Products of projective lines finitely cover projective space
-- statement:
--   Over any commutative ring $R$, the product over $R$ of $n+1$ projective lines admits a finite surjection to $\mathbf P_R^{n+1}$ over $\operatorname{Spec}R$. The expected map sends a tuple of linear binary forms to the coefficients of their product.
-- source:
--   Stacks Project, Lemma 59.91.10, https://stacks.math.columbia.edu/tag/0A4F.

import Definitions.Def_AlgebraicGeometry_ProjectiveLineTower
import Mathlib.AlgebraicGeometry.Morphisms.Finite

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleProjectiveLineTower (linePower)
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.exists_finite_surjective_projectiveLinePower_cover
    (R : Type u) [CommRing R] (n : ℕ) :
    ∃ k : (linePower (𝟙 (Spec (.of R))) n).left ⟶
        Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1 + 1)) R),
      IsFinite k ∧ Surjective k ∧ k ≫ ProjSpace.π R (n + 1) = (linePower (𝟙 (Spec (.of R))) n).hom := by sorry
