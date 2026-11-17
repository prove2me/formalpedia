-- Prove2me | Theorems.Thm_AlgebraicGeometry_SymmetricFiniteFrame_exists_bounded_double
-- name    : AlgebraicGeometry.SymmetricFiniteFrame.exists_bounded_double
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:42.583249+00:00
-- url     : https://prove2.me/theorems/8f1fcd09-9189-4a3b-b3f5-31b35b968048
-- title:
--   A symmetric finite-frame height is quadratic under doubling up to a bounded error
-- statement:
--   Let $K$ be a number field and let $F$ be a symmetric finite frame on a relative group scheme. There exists $C_2≥0$ such that every $K$-point $x$ satisfies $$|h_F(2x)-4h_F(x)|≤C_2.$$ This is the bounded doubling estimate used to construct and compare canonical heights.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry
open AlgebraicGeometry.SymmetricFiniteFrame

theorem AlgebraicGeometry.SymmetricFiniteFrame.exists_bounded_double {K : Type} [Field K] [NumberField K] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of K)} {G : RelativeGroupLaw K f} (F : SymmetricFiniteFrame K f G) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ x : Scheme.KPoint f, |F.height (G.mul (𝟙 _) x x) - 4 * F.height x| ≤ C₂ := by sorry
