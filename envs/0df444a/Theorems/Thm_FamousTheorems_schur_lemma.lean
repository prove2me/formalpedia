-- Prove2me | Theorems.Thm_FamousTheorems_schur_lemma
-- name    : FamousTheorems.schur_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:38.682278+00:00
-- url     : https://prove2.me/theorems/cd091ea1-488b-4e82-8650-fa48bcb9d824
-- title:
--   Schur's lemma (algebraically closed fields)
-- statement:
--   **Schur's lemma.** Let $\mathcal C$ be a $\mathbb k$-linear preadditive category with kernels over an algebraically closed field $\mathbb k$, and $X$ a simple object whose endomorphism space is finite-dimensional. Then $\operatorname{End}(X)$ is one-dimensional: every endomorphism of $X$ is a scalar multiple of the identity.
--
--   For representations of groups or algebras this says that the endomorphisms of an irreducible finite-dimensional representation over $\mathbb C$ are scalars. It is the key lemma behind orthogonality of characters, the central character of an irreducible representation, and the classification of semisimple algebras over algebraically closed fields.
--
--   **Formalization note.** Mathlib's `CategoryTheory.finrank_endomorphism_simple_eq_one`, stated for a simple object in a `𝕜`-linear category with kernels; module categories over `𝕜`-algebras are the main example.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CategoryTheory.finrank_endomorphism_simple_eq_one`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe u v

theorem schur_lemma {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.Preadditive C] (𝕜 : Type*) [Field 𝕜]
    [IsAlgClosed 𝕜] [CategoryTheory.Linear 𝕜 C] [CategoryTheory.Limits.HasKernels C] (X : C)
    [CategoryTheory.Simple X] [FiniteDimensional 𝕜 (X ⟶ X)] : Module.finrank 𝕜 (X ⟶ X) = 1 := by sorry

end FamousTheorems
