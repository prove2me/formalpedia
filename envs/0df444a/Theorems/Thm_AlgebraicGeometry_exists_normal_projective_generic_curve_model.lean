-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_normal_projective_generic_curve_model
-- name    : AlgebraicGeometry.exists_normal_projective_generic_curve_model
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-23T21:14:49.174532+00:00
-- url     : https://prove2.me/theorems/029fbd2d-f7ba-4b34-a526-ce4f8ab55108
-- title:
--   A normal projective model with a normal proper integral generic curve
-- statement:
--   Let $K$ be a perfect field and let $X$ be a normal integral proper $K$-scheme, with a specified projective embedding and dimension greater than one. There are an integer $r>0$, a normal integral projective $K$-scheme $G$, and proper surjective morphisms
--   $$p:G\longrightarrow X,\qquad q:G\longrightarrow\mathbb P^r_K$$
--   over $K$, with
--   $$\dim G=\dim X=r+1.$$
--   The source has a nonempty dense affine open $W$ on which the restriction of $q$ is smooth and the stalk maps induced by $p$ are isomorphisms.
--
--   If $\eta$ is the generic point of the displayed projective space, the actual scheme-theoretic fibre
--   $$C=G\times_{\mathbb P^r_K}\operatorname{Spec}\kappa(\eta)$$
--   is an integral proper curve of dimension one over $\kappa(\eta)$, and all its local rings are integrally closed. Moreover the inclusion $C\to G$ induces an isomorphism at every local ring. The projective embedding of $G$ and its compatibility with the structure morphism are retained.
--
--   **Formalization Note.** This adds a statement about the entire generic-fibre scheme to the separating projection model. It does not assert that this curve is geometrically normal or smooth over the generally imperfect field $\kappa(\eta)$, or that all other fibres have dimension one. Semistability and the eventual smooth alteration remain separate steps.
-- source:
--   Derived auxiliary consequence of the proved projection model https://prove2.me/theorems/156ec284-7d67-4beb-a287-5c07cb2316dc and generic-fibre integrality https://prove2.me/theorems/fd773659-17a0-42e8-8f33-baf6f63e161d . The dimension calculation uses dimension as transcendence degree over a field and the transcendence-degree tower formula; compare Stacks Project, Lemma 29.53.4 and its generic-fibre argument, https://stacks.math.columbia.edu/tag/02JT , and Section 29.29, https://stacks.math.columbia.edu/tag/02FW . Local rings of the generic fibre agree with those of the integral source, as also used in the proof of Lemma 29.53.4. This is preparatory infrastructure for A. J. de Jong, Smoothness, semi-stability and alterations (1996), Sections 4.11-4.12, https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf ; it is weaker than the fibrewise assertions of Lemma 4.11.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_normal_projective_generic_curve_model
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
      (∃ (d : ℕ)
        (k : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) K)),
        IsClosedImmersion k ∧ k ≫ ProjSpace.π K d = p ≫ π) ∧
      ∃ η : Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K),
        IsGenericPoint η Set.univ ∧ IsIntegral (q.fiber η) ∧
        (∀ z : q.fiber η, IsIntegrallyClosed ((q.fiber η).presheaf.stalk z)) ∧
        IsProper (q.fiberToSpecResidueField η) ∧
        topologicalKrullDim (q.fiber η) = 1 ∧
        ∀ z : q.fiber η, IsIso ((q.fiberι η).stalkMap z) := by sorry
