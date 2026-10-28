-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_finite_extension_with_distinct_sections_of_positive_dimension
-- name    : AlgebraicGeometry.exists_finite_extension_with_distinct_sections_of_positive_dimension
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-26T18:22:40.345978+00:00
-- url     : https://prove2.me/theorems/95de04f8-bcbf-423d-8fa5-4887dfe80630
-- title:
--   Distinct rational markings after a finite field extension
-- statement:
--   Let $K$ be any field and let $X$ be a scheme locally of finite type over $K$, of positive topological Krull dimension. For every integer $n\geq0$, there is a finite field extension $L/K$ such that the actual base change
--   $$X_L=X\times_{\operatorname{Spec}K}\operatorname{Spec}L$$
--   has $n$ rational sections
--   $$\sigma_i:\operatorname{Spec}L\longrightarrow X_L\qquad (0\leq i<n).$$
--   Each section is a closed immersion, its composite with $X_L\to\operatorname{Spec}L$ is the identity, and the images of different sections are disjoint as subsets of the actual scheme $X_L$.
--
--   The scheme need not be proper, smooth, integral, separated or quasi-compact. Neither algebraic closedness nor perfectness of $K$ is assumed, and the finite extension is not required to be separable. In the alteration argument this supplies arbitrarily many distinct markings on the smooth integral generic curve after a finite extension. Extension over a whole base and stable-curve moduli are further steps.
-- source:
--   Auxiliary finite-generic-point marking step for A. J. de Jong, Smoothness, semi-stability and alterations, Publications Mathématiques de l’IHÉS 83 (1996), Section 4.16-4.17, pp. 71-72, https://www.numdam.org/item/PMIHES_1996__83__51_0.pdf . This is a derived and generalized field-valued marking statement, not the full family or componentwise marking theorem of Section 5.2. Closed-point residue fields are finite by the Hilbert Nullstellensatz, as in Stacks Project Lemma 29.21.3, tag 01TF, https://stacks.math.columbia.edu/tag/01TF . The proof takes a finite compositum of their embeddings in an algebraic closure and uses actual cartesian lifts. It does not assert separability or stable reduction.

import Mathlib
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

theorem AlgebraicGeometry.exists_finite_extension_with_distinct_sections_of_positive_dimension
    {K : Type u} [Field K] {X : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (hdim : 0 < topologicalKrullDim X) (n : ℕ) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (σ : Fin n → (Spec (.of L) ⟶
        pullback π (Spec.map (CommRingCat.ofHom (algebraMap K L))))),
      (∀ i, σ i ≫ pullback.snd π (Spec.map (CommRingCat.ofHom (algebraMap K L))) =
        𝟙 (Spec (.of L))) ∧
      (∀ i, IsClosedImmersion (σ i)) ∧
      Pairwise (fun i j => Disjoint (Set.range (σ i)) (Set.range (σ j))) := by sorry
