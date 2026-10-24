-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_normal_projective_projection_with_dense_smooth_open
-- name    : AlgebraicGeometry.exists_normal_projective_projection_with_dense_smooth_open
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-23T19:43:48.743726+00:00
-- url     : https://prove2.me/theorems/156ec284-7d67-4beb-a287-5c07cb2316dc
-- title:
--   Normal projective projection with a dense affine smooth open
-- statement:
--   Let $K$ be a perfect field and let $X$ be an integral normal proper $K$-scheme equipped with a projective embedding. Suppose that $\dim X>1$. There are an integer $r>0$, an integral normal projective $K$-scheme $G$, and proper surjective morphisms
--   $$p:G\longrightarrow X,\qquad q:G\longrightarrow\mathbb P^r_K$$
--   such that
--   $$\dim G=\dim X=r+1,\qquad \pi_X\circ p=\pi_{\mathbb P^r}\circ q.$$
--   There is a nonempty dense affine open $W\subset G$ on which the restricted projection $q|_W:W\to\mathbb P^r_K$ is smooth. At every point $w\in W$, the homomorphism of local rings induced by $p$ is an isomorphism. Projectivity of $G$ is witnessed by a closed immersion into an actual projective space, compatible with its structure morphism.
--
--   This refines a normal curve-projection model by a smooth affine open in its source. It uses the original separating parameters and their actual coordinate germs to identify a suitable principal localization of the parameter chart. **Formalization Note.** Smoothness is asserted for the displayed restriction to $W$. Equidimensionality and smoothness of every geometric fibre, smoothness of the entire generic fibre, semistability and regular alteration are not part of this statement.
-- source:
--   Auxiliary consequence of the proved normal curve-projection model https://prove2.me/theorems/443127a4-5bf9-4291-bb4e-9de03aa84d66 and spreading smoothness from separating function-field parameters. Stacks Project, Section 29.35, Definition 29.35.1 and Lemmas 29.35.2, 29.35.4, 29.35.6, https://stacks.math.columbia.edu/tag/01V4 ; Definition 10.137.10 (smoothness on a principal open), https://stacks.math.columbia.edu/tag/00TB . The field-theoretic input is the separating-basis criterion for formal smoothness, formalized by Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable in Mathlib/RingTheory/Smooth/Field.lean at https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Smooth/Field.lean . Preparatory projection step for A. J. de Jong, Smoothness, semi-stability and alterations (1996), Sections 4.11-4.12, https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf ; this is weaker than the fibrewise assertions of Lemma 4.11.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_normal_projective_projection_with_dense_smooth_open
    (K : Type u) [Field K] [PerfectField K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π)
    (hnormalX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : 1 < topologicalKrullDim X) :
    ∃ (r : ℕ) (G : Scheme.{u}) (p : G ⟶ X)
      (q : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)),
      0 < r ∧ IsIntegral G ∧ (∀ g : G, IsIntegrallyClosed (G.presheaf.stalk g)) ∧
      topologicalKrullDim G = topologicalKrullDim X ∧
      topologicalKrullDim X = ((r + 1 : ℕ) : WithBot ℕ∞) ∧
      IsProper p ∧ Surjective p ∧ IsProper q ∧ Surjective q ∧
      p ≫ π = q ≫ ProjSpace.π K r ∧
      (∃ W : G.Opens, IsAffineOpen W ∧ Nonempty W ∧ Dense (W : Set G) ∧
        Smooth (W.ι ≫ q) ∧ (∀ w : W, IsIso (p.stalkMap w.val))) ∧
      ∃ (d : ℕ)
        (k : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) K)),
        IsClosedImmersion k ∧ k ≫ ProjSpace.π K d = p ≫ π := by sorry
