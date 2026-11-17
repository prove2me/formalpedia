-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_tensor_pointLogHeight_eq_add_and_isFinite
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_tensor_pointLogHeight_eq_add_and_isFinite
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:13:34.001651+00:00
-- url     : https://prove2.me/theorems/f21b4224-915c-4c3b-a9b3-67e507981275
-- title:
--   A tensor-product presentation can be chosen finite while preserving additive height
-- statement:
--   Let $P$ and $Q$ be projective presentations over a number field and assume the map defined by $P$ is finite. Then there is a finite presentation $R$ of the tensor product, with tensor-product sections, satisfying $$h_R(x)=h_P(x)+h_Q(x)$$ for every rational point $x$. This combines the tensor construction with the finiteness needed for Northcott's theorem.
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

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_tensor_pointLogHeight_eq_add_and_isFinite
    {K : Type} [Field K] [NumberField K]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {L M : X.Modules} {N N' : ℕ}
    (P : L.ProjPresentation f N) (Q : M.ProjPresentation f N')
    (hP : IsFinite P.toProj) :
    ∃ (idx : Fin (N * N' + N + N' + 1) ≃ Fin (N + 1) × Fin (N' + 1))
      (R : (L ⊗ M).ProjPresentation f (N * N' + N + N')), IsFinite R.toProj ∧
      (∀ k, R.σ k = Scheme.Modules.tensorSections (P.σ (idx k).1) (Q.σ (idx k).2)) ∧
      ∀ x, R.pointLogHeight x = P.pointLogHeight x + Q.pointLogHeight x := by sorry
