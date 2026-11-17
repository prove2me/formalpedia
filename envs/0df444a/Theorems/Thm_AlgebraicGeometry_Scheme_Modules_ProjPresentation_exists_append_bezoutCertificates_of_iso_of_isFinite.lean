-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_append_bezoutCertificates_of_iso_of_isFinite
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_append_bezoutCertificates_of_iso_of_isFinite
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:32.986194+00:00
-- url     : https://prove2.me/theorems/b5b9f5ee-322f-4945-b1aa-3b0297fb1129
-- title:
--   Isomorphic finite presentations admit joint homogeneous Bézout certificates
-- statement:
--   Let $K$ be a number field, let $P_1,P_2$ present isomorphic modules, and assume $P_1$ is finite. Then there are degrees $D_1,D_2$ and homogeneous polynomials $q_1,q_2$ in the combined coordinate set such that every $K$-point has a joint vector $z$ representing both projectivizations and, for every combined coordinate $k$, $$z_k^{D_1+1}=\sum_i q_1(k,i)(z)z_{inl(i)},\qquad z_k^{D_2+1}=\sum_j q_2(k,j)(z)z_{inr(j)}.$$ These identities transfer height bounds between the two coordinate blocks.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_append_bezoutCertificates_of_iso_of_isFinite {K : Type} [Field K] [NumberField K]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)} {M₁ M₂ : X.Modules} {N₁ N₂ : ℕ}
    (P₁ : M₁.ProjPresentation f N₁) (P₂ : M₂.ProjPresentation f N₂) (e : M₁ ≅ M₂)
    (hfin : IsFinite P₁.toProj) :
    ∃ (D₁ D₂ : ℕ)
      (q₁ : (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) × Fin (N₁ + 1) → MvPolynomial (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) K)
      (q₂ : (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) × Fin (N₂ + 1) → MvPolynomial (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) K),
      (∀ a, (q₁ a).IsHomogeneous D₁) ∧ (∀ a, (q₂ a).IsHomogeneous D₂) ∧
      ∀ x : Scheme.KPoint f, ∃ (z : Fin (N₁ + 1) ⊕ Fin (N₂ + 1) → K)
          (h₁ : z ∘ Sum.inl ≠ 0) (h₂ : z ∘ Sum.inr ≠ 0),
        P₁.pointProjectivization x = Projectivization.mk K (z ∘ Sum.inl) h₁ ∧
        P₂.pointProjectivization x = Projectivization.mk K (z ∘ Sum.inr) h₂ ∧
        (∀ k, ∑ i, (q₁ (k, i)).eval z * z (Sum.inl i) = z k ^ (D₁ + 1)) ∧
        (∀ k, ∑ j, (q₂ (k, j)).eval z * z (Sum.inr j) = z k ^ (D₂ + 1)) := by sorry
