-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_append_homogeneousIdeal
-- name    : AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_append_homogeneousIdeal
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:21:33.655197+00:00
-- url     : https://prove2.me/theorems/d4cbac3b-0a64-4837-95da-060f247610a1
-- title:
--   Two isomorphic finite presentations admit a common homogeneous image ideal
-- statement:
--   Let $K$ be a number field, let $P_1,P_2$ present isomorphic modules, and assume $P_1$ is finite. There is a homogeneous ideal $I$ in the combined coordinates such that adjoining either entire coordinate block to $I$ has only the origin as an affine zero over $Kbar$, and every $K$-point admits a joint vector $z$ representing both presentations with $$p(z)=0\quad\text{for every }p∈I.$$ This is the common projective model from which the Bézout certificates are derived.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjPresentationHeight

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.ProjPresentation

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_append_homogeneousIdeal {K : Type} [Field K] [NumberField K]
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)} {M₁ M₂ : X.Modules} {N₁ N₂ : ℕ}
    (P₁ : M₁.ProjPresentation f N₁) (P₂ : M₂.ProjPresentation f N₂) (e : M₁ ≅ M₂)
    (hfin : IsFinite P₁.toProj) :
    ∃ I : HomogeneousIdeal
        (MvPolynomial.homogeneousSubmodule (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) K),
      (∀ z : (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) → AlgebraicClosure K,
        z ∈ MvPolynomial.zeroLocus (AlgebraicClosure K)
          (I.toIdeal ⊔ Ideal.span (Set.range
            (fun i : Fin (N₁ + 1) =>
              (MvPolynomial.X (Sum.inl i) :
                MvPolynomial (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) K)))) → z = 0) ∧
      (∀ z : (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) → AlgebraicClosure K,
        z ∈ MvPolynomial.zeroLocus (AlgebraicClosure K)
          (I.toIdeal ⊔ Ideal.span (Set.range
            (fun j : Fin (N₂ + 1) =>
              (MvPolynomial.X (Sum.inr j) :
                MvPolynomial (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) K)))) → z = 0) ∧
      ∀ x : Scheme.KPoint f,
        ∃ (z : (Fin (N₁ + 1) ⊕ Fin (N₂ + 1)) → K)
            (h₁ : z ∘ Sum.inl ≠ 0) (h₂ : z ∘ Sum.inr ≠ 0),
          P₁.pointProjectivization x = Projectivization.mk K (z ∘ Sum.inl) h₁ ∧
          P₂.pointProjectivization x = Projectivization.mk K (z ∘ Sum.inr) h₂ ∧
          ∀ p ∈ I.toIdeal, MvPolynomial.eval z p = 0 := by sorry
