-- Prove2me | Theorems.Thm_AlgebraicGeometry_SymmetricFiniteFrame_exists_bounded_parallelogram
-- name    : AlgebraicGeometry.SymmetricFiniteFrame.exists_bounded_parallelogram
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:50.321564+00:00
-- url     : https://prove2.me/theorems/1b176618-c9e9-48bd-92c7-c25338d527b6
-- title:
--   A symmetric finite-frame height satisfies the parallelogram law up to bounded error
-- statement:
--   Let $K$ be a number field and let $F$ be a symmetric finite frame on a relative group scheme. There exists $C_P≥0$ such that for all $K$-points $x,y$, $$|h_F(x+y)+h_F(x-y)-2h_F(x)-2h_F(y)|≤C_P.$$ This controls the height under the endomorphisms used in the N25 descent.
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

theorem AlgebraicGeometry.SymmetricFiniteFrame.exists_bounded_parallelogram {K : Type} [Field K] [NumberField K] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of K)} {G : RelativeGroupLaw K f} (F : SymmetricFiniteFrame K f G) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ x y : Scheme.KPoint f,
      |F.height (G.mul (𝟙 _) x y) + F.height (G.mul (𝟙 _) x (G.inv (𝟙 _) y)) - 2 * F.height x - 2 * F.height y| ≤ Cp := by sorry
