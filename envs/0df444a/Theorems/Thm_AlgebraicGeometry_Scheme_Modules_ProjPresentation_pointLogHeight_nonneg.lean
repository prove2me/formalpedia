-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_pointLogHeight_nonneg
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.pointLogHeight_nonneg
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:13:35.098884+00:00
-- url     : https://prove2.me/theorems/0ae3ca8a-baa1-4767-8746-3eac3edc6b0b
-- title:
--   The logarithmic height of a projective presentation is nonnegative
-- statement:
--   Let $K$ be a number field, let $P$ be a projective presentation, and let $x$ be a $K$-rational point. Then $$0≤h_P(x).$$ This normalization allows the later height inequalities to be used without lower-order sign issues.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.pointLogHeight_nonneg {K : Type} [Field K] [NumberField K] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of K)} {M : X.Modules} {N : ℕ}
    (P : M.ProjPresentation f N) (x : Scheme.KPoint f) : 0 ≤ P.pointLogHeight x := by sorry
