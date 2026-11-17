-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_tensor_pointLogHeight_eq_add
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_tensor_pointLogHeight_eq_add
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:13:32.185011+00:00
-- url     : https://prove2.me/theorems/cf0379fb-867a-4d42-823d-288dfbb5ee4a
-- title:
--   A tensor-product presentation has point height equal to the sum of the two heights
-- statement:
--   Let $P$ and $Q$ be projective presentations of modules $L$ and $M$ over a number field. There are a pairing of coordinate indices and a presentation $R$ of $L⊗M$ whose sections are the corresponding tensor products and such that $$h_R(x)=h_P(x)+h_Q(x)$$ for every rational point $x$. This is the exact additivity of heights under tensor product.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_tensor_pointLogHeight_eq_add
    {K : Type} [Field K] [NumberField K]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {L M : X.Modules} {N N' : ℕ}
    (P : L.ProjPresentation f N) (Q : M.ProjPresentation f N') :
    ∃ (idx : Fin (N * N' + N + N' + 1) ≃ Fin (N + 1) × Fin (N' + 1))
      (R : (L ⊗ M).ProjPresentation f (N * N' + N + N')),
      (∀ k, R.σ k = Scheme.Modules.tensorSections (P.σ (idx k).1) (Q.σ (idx k).2)) ∧
      ∀ x, R.pointLogHeight x = P.pointLogHeight x + Q.pointLogHeight x := by sorry
