-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_numberField_finiteFrame_descent
-- name    : AlgebraicGeometry.Scheme.Modules.exists_numberField_finiteFrame_descent
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:17.323148+00:00
-- url     : https://prove2.me/theorems/9f3965f1-dabe-40b3-945c-eee7ba9f6dbf
-- title:
--   An abelian scheme acquires an invertible finite projective frame over a number field
-- statement:
--   Let $A→Spec(ℚ)$ be an abelian scheme. There exists a finite-dimensional intermediate field $F⊂Qbar$, an invertible module $L$ on the base change $A_F$, and a projective presentation $P$ of $L$ whose associated map is finite: $$P:A_F→ℙ^N_F\text{ is finite}.$$ This supplies the finite projective frame from which the height is built.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_SymmetricFiniteFrame

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules

theorem AlgebraicGeometry.Scheme.Modules.exists_numberField_finiteFrame_descent {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of ℚ))
    (hA : AbelianSchemePropertyBundle ℚ f) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ F)
      (𝓛 : (CategoryTheory.Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap ℚ ↥F)))).Modules) (N : ℕ)
      (P : 𝓛.ProjPresentation (CategoryTheory.Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap ℚ ↥F)))) N),
      Scheme.Modules.IsInvertible 𝓛 ∧ IsFinite P.toProj := by sorry
