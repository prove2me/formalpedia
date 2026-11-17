-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isFinite_tensor_of_charts
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.isFinite_tensor_of_charts
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:36.072814+00:00
-- url     : https://prove2.me/theorems/ec89bf8c-8a2f-432a-be4a-a2a9d15a0956
-- title:
--   Exact tensor-chart equalities preserve finiteness of a projective presentation
-- statement:
--   Let $P$ and $Q$ be projective presentations on the same scheme, let $R$ present their tensor product, and suppose each chart of $R$ is exactly the intersection of the corresponding charts of $P$ and $Q$. If $P_{proj}$ is finite, then $$R_{proj}\text{ is finite}.$$ This propagates the finite-map property to tensor powers and symmetric combinations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.isFinite_tensor_of_charts
    {K : Type} [Field K] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {L M : X.Modules} {N N' : ℕ}
    (P : L.ProjPresentation f N) (Q : M.ProjPresentation f N')
    (idx : Fin (N*N'+N+N'+1) ≃ Fin (N+1) × Fin (N'+1))
    (R : (L ⊗ M).ProjPresentation f (N*N'+N+N'))
    (hchart : ∀ k, R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k) =
      (P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).1)) ⊓
        (Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).2)))
    (hP : IsFinite P.toProj) : IsFinite R.toProj := by sorry
