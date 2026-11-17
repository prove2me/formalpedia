-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_append
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_append
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:00.583202+00:00
-- url     : https://prove2.me/theorems/2e607d6c-6e31-4195-8b58-9f4176c08915
-- title:
--   Two presentations of isomorphic modules can be combined into one appended presentation
-- statement:
--   Let $P_1$ and $P_2$ be projective presentations of isomorphic modules, and choose an indexing bijection for the disjoint union of their coordinates. There exists a presentation $Q$ whose sections are the sections of $P_1$ together with the inverse-transported sections of $P_2$, and each basic chart of either original presentation is contained in the corresponding chart of $Q$. This creates a common coordinate system for comparing the two presentations.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_append {K : Type} [Field K]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {M₁ M₂ : X.Modules} {N₁ N₂ : ℕ}
    (P₁ : M₁.ProjPresentation f N₁) (P₂ : M₂.ProjPresentation f N₂)
    (e : M₁ ≅ M₂)
    (ι : Fin (N₁ + N₂ + 1 + 1) ≃ (Fin (N₁ + 1) ⊕ Fin (N₂ + 1))) :
    ∃ Q : M₁.ProjPresentation f (N₁ + N₂ + 1),
      (∀ k, Q.σ k = Sum.elim P₁.σ (fun j => e.inv.app ⊤ (P₂.σ j)) (ι k)) ∧
      (∀ i, P₁.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i) ≤
        Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (ι.symm (Sum.inl i)))) ∧
      (∀ j, P₂.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j) ≤
        Q.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X (ι.symm (Sum.inr j)))) := by sorry
