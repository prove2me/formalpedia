-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_integral_proper_compactification_of_isSeparated
-- name    : AlgebraicGeometry.exists_integral_proper_compactification_of_isSeparated
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-08T05:05:00.258202+00:00
-- url     : https://prove2.me/theorems/acd0a494-7c12-406e-88c1-0d0e0da39fc7
-- title:
--   Integral proper compactification over a field
-- statement:
--   Let $K$ be an arbitrary field and let $X$ be an integral separated scheme of finite type over $K$. There is an integral proper $K$-scheme $C$ and a dense open immersion
--   $$j:X\hookrightarrow C$$
--   which commutes with the given structure morphisms to $\operatorname{Spec}K$.
--
--   This is the integral form of Nagata compactification over a field. It supplies a proper ambient variety without any smoothness, normality, projectivity or perfectness assumption.
-- source:
--   The Stacks Project, Theorem 38.33.8 (Nagata compactification), Tag 0F41: https://stacks.math.columbia.edu/tag/0F41 . Specialize the base to Spec K. For integral X, replace the compactification by the scheme-theoretic closure of X; the given open subscheme is retained, and its closure is integral and proper. This is a corollary of Nagata compactification, not an assertion that an arbitrary variety is quasi-projective.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_integral_proper_compactification_of_isSeparated
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    [LocallyOfFiniteType π] [QuasiCompact π] [IsSeparated π] :
    ∃ (C : Scheme.{u}) (πC : C ⟶ Spec (.of K)),
      IsIntegral C ∧ IsProper πC ∧
      ∃ j : X ⟶ C, IsOpenImmersion j ∧ IsDominant j ∧ j ≫ πC = π := by sorry
