-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_pointProjectivization_tensor
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.pointProjectivization_tensor
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:13:56.903394+00:00
-- url     : https://prove2.me/theorems/31a50ae6-eaf5-4274-903d-027300b2bb4a
-- title:
--   The tensor presentation sends a point to the Segre product of its coordinate vectors
-- statement:
--   Let $P,Q,R$ be compatible projective presentations of $L,M,L⊗M$, with tensor-product sections and the stated chart inclusions. If nonzero vectors $a$ and $b$ represent $P(x)$ and $Q(x)$, then the vector $c$ with $c_k=a_{i_k}b_{j_k}$ is nonzero and $$R(x)=[c].$$ This is the pointwise Segre formula for tensor coordinates.
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

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.pointProjectivization_tensor
    {K : Type} [Field K] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {L M : X.Modules} {N N' : ℕ}
    (P : L.ProjPresentation f N) (Q : M.ProjPresentation f N')
    (idx : Fin (N * N' + N + N' + 1) ≃ Fin (N + 1) × Fin (N' + 1))
    (R : (L ⊗ M).ProjPresentation f (N * N' + N + N'))
    (hσ : ∀ k, R.σ k = Scheme.Modules.tensorSections (P.σ (idx k).1) (Q.σ (idx k).2))
    (hU : ∀ k, (P.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).1)) ⊓
      (Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (idx k).2)) ≤
      R.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X k))
    (x : Scheme.KPoint f)
    (a : Fin (N+1) → K) (ha : a ≠ 0)
    (b : Fin (N'+1) → K) (hb : b ≠ 0)
    (hap : (ProjSpace.kPointOfVec K N a ha).1 = x.1 ≫ P.toProj)
    (hbp : (ProjSpace.kPointOfVec K N' b hb).1 = x.1 ≫ Q.toProj) :
    ∃ hc : (fun k => a (idx k).1 * b (idx k).2) ≠ 0,
      R.pointProjectivization x = Projectivization.mk K (fun k => a (idx k).1 * b (idx k).2) hc := by sorry
