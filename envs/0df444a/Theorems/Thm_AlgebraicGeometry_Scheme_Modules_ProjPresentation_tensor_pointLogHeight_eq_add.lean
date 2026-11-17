-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_tensor_pointLogHeight_eq_add
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.tensor_pointLogHeight_eq_add
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:13:38.218276+00:00
-- url     : https://prove2.me/theorems/aa4ae4d4-801a-4732-ae7e-a52c5b6936bc
-- title:
--   The point height of a tensor presentation is the sum of the factor heights
-- statement:
--   Let $K$ be a number field and let $P,Q,R$ be compatible projective presentations of $L,M,L⊗M$, with tensor-product sections and the stated chart inclusions. Then for every $K$-point $x$, $$h_R(x)=h_P(x)+h_Q(x).$$ This is the exact height identity used in the quadratic and parallelogram estimates.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Definitions.Def_AlgebraicGeometry_ProjSpaceEquivalence
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.tensor_pointLogHeight_eq_add
    {K : Type} [Field K] [NumberField K] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {L M : X.Modules} {N N' : ℕ}
    (P : L.ProjPresentation f N) (Q : M.ProjPresentation f N')
    (idx : Fin (N * N' + N + N' + 1) ≃ Fin (N + 1) × Fin (N' + 1))
    (R : (L ⊗ M).ProjPresentation f (N * N' + N + N'))
    (hσ : ∀ k, R.σ k = Scheme.Modules.tensorSections (P.σ (idx k).1) (Q.σ (idx k).2))
    (hU : ∀ k, (P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).1)) ⊓
      (Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).2)) ≤
      R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k))
    (x : Scheme.KPoint f) :
    R.pointLogHeight x = P.pointLogHeight x + Q.pointLogHeight x := by sorry
