-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_cover_of_normal_projective_generic_curve_fibration
-- name    : AlgebraicGeometry.exists_smooth_projective_cover_of_normal_projective_generic_curve_fibration
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-23T21:42:51.396666+00:00
-- url     : https://prove2.me/theorems/24700494-6f7d-4195-ba71-67cca0ce2ace
-- title:
--   Smooth projective cover of a normal projective generic-curve fibration
-- statement:
--   Let $K$ be algebraically closed. Let $G$ be a normal integral proper $K$-scheme with a specified projective embedding, and let
--   $$q:G\longrightarrow\mathbb P^r_K$$
--   be a proper surjective $K$-morphism, where $r>0$ and $\dim G=r+1$. Suppose that $G$ contains a nonempty dense affine open $W$ on which $q$ is smooth. Let $\eta$ be the generic point of the displayed projective space. Assume that the actual fibre
--   $$C=G\times_{\mathbb P^r_K}\operatorname{Spec}\kappa(\eta)$$
--   is an integral normal proper curve of dimension one, and that its inclusion into $G$ induces an isomorphism on every local ring.
--
--   Then there exist an integral smooth projective $K$-scheme $Y$ and a proper surjective $K$-morphism
--   $$f:Y\longrightarrow G.$$
--   Projectivity of $Y$ is witnessed by a closed immersion into projective space compatible with the displayed structure morphism.
--
--   This is the alteration step after a normal projective variety has been placed in a generic-curve fibration. **Formalization Note.** Smoothness of the entire generic curve, geometric normality over $\kappa(\eta)$, flatness of $q$, equidimensionality of all fibres and semistability are not hypotheses. Establishing suitable modifications and base changes is part of the remaining proof. Generic finiteness and normal-crossing boundary conclusions are omitted.
-- source:
--   Derived special case of A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathematiques de l IHES 83 (1996), Theorem 4.1 and Remark 4.2, p.66, https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . The fibration approach is described in the introduction, p.53, and developed in Sections 4.11-4.24. The displayed hypotheses give only a generic-curve model, not the stronger fibrewise conditions of Lemma 4.11; reaching semistable pointed curves and resolving their total spaces remains part of this specialized alteration problem. The conclusion follows from the full theorem, and is stated separately to isolate the remaining geometric step after the proved projection construction.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_smooth_projective_cover_of_normal_projective_generic_curve_fibration
    (K : Type u) [Field K] [IsAlgClosed K] {G : Scheme.{u}} [IsIntegral G]
    (π : G ⟶ Spec (.of K)) [IsProper π] (d : ℕ)
    (k : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) K))
    [IsClosedImmersion k] (hk : k ≫ ProjSpace.π K d = π)
    (r : ℕ) (q : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
    [IsProper q] [Surjective q] (hr : 0 < r)
    (hbase : q ≫ ProjSpace.π K r = π)
    (hnormal : ∀ g : G, IsIntegrallyClosed (G.presheaf.stalk g))
    (hdim : topologicalKrullDim G = ((r + 1 : ℕ) : WithBot ℕ∞))
    (W : G.Opens) (hW : IsAffineOpen W) (hWne : Nonempty W)
    (hWdense : Dense (W : Set G)) (hsmooth : Smooth (W.ι ≫ q))
    (η : Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K))
    (hη : IsGenericPoint η Set.univ) (hC : IsIntegral (q.fiber η))
    (hCnormal : ∀ z : q.fiber η, IsIntegrallyClosed ((q.fiber η).presheaf.stalk z))
    (hCproper : IsProper (q.fiberToSpecResidueField η))
    (hCdim : topologicalKrullDim (q.fiber η) = 1)
    (hCstalk : ∀ z : q.fiber η, IsIso ((q.fiberι η).stalkMap z)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ G),
      IsIntegral Y ∧ IsProper f ∧ Surjective f ∧ Smooth (f ≫ π) ∧
      ∃ (m : ℕ)
        (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = f ≫ π := by sorry
