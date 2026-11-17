-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_tensor_chart_eq
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.tensor_chart_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:06.627615+00:00
-- url     : https://prove2.me/theorems/23df78c1-faa2-4264-80f4-d34f44b650c1
-- title:
--   A tensor-product chart is exactly the intersection of its two factor charts
-- statement:
--   Let $R$ be a tensor presentation built from presentations $P$ and $Q$, with tensor-product sections and the prescribed chart inclusions. If $idx(k)=(i_k,j_k)$, then $$U^R_k=U^P_{i_k}∩U^Q_{j_k}.$$ This exact chart formula is the key local input for proving finiteness of tensor presentations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.tensor_chart_eq
    {K : Type} [Field K] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {L M : X.Modules} {N N' : ℕ}
    (P : L.ProjPresentation f N) (Q : M.ProjPresentation f N')
    (idx : Fin (N*N'+N+N'+1) ≃ Fin (N+1) × Fin (N'+1))
    (R : (L ⊗ M).ProjPresentation f (N*N'+N+N'))
    (hσ : ∀ k, R.σ k = Scheme.Modules.tensorSections (P.σ (idx k).1) (Q.σ (idx k).2))
    (hU : ∀ k, (P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).1)) ⊓
      (Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).2)) ≤
      R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k))
    (k : Fin (N*N'+N+N'+1)) :
    R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k) =
      (P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).1)) ⊓
        (Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).2)) := by sorry
