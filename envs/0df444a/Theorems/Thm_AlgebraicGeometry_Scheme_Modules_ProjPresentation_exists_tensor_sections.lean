-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_tensor_sections
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_tensor_sections
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:05:29.203283+00:00
-- url     : https://prove2.me/theorems/39348bd3-7ce0-452a-af9a-5c2ef8014bfb
-- title:
--   Tensor products of section systems form a projective presentation
-- statement:
--   Let $P$ and $Q$ be projective presentations of modules $L$ and $M$. There exist a bijection between the new coordinate indices and pairs of old indices, and a presentation $R$ of $L⊗M$, such that each section of $R$ is the tensor product of the corresponding sections of $P$ and $Q$, and $$U^P_i∩U^Q_j⊆U^R_{(i,j)}.$$ This is the Segre-style construction of a tensor presentation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_tensor_sections
    {K : Type} [Field K] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {L M : X.Modules} {N N' : ℕ}
    (P : L.ProjPresentation f N) (Q : M.ProjPresentation f N') :
    ∃ (idx : Fin (N * N' + N + N' + 1) ≃ Fin (N + 1) × Fin (N' + 1))
      (R : (L ⊗ M).ProjPresentation f (N * N' + N + N')),
      (∀ k, R.σ k = Scheme.Modules.tensorSections (P.σ (idx k).1) (Q.σ (idx k).2)) ∧
      ∀ k, (P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).1)) ⊓
        (Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).2)) ≤
        R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k) := by sorry
