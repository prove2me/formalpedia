-- Prove2me | Theorems.Thm_FamousTheorems_noether_normalization_lemma
-- name    : FamousTheorems.noether_normalization_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:56:10.090417+00:00
-- url     : https://prove2.me/theorems/c524bd57-49f8-49de-8dad-9841f7b1c4ef
-- title:
--   The Noether normalization lemma
-- statement:
--   **The Noether normalization lemma.** Let $k$ be a field and $R\neq0$ a finitely generated $k$-algebra. Then there are $s\in\mathbb N$ and an injective $k$-algebra homomorphism
--   $$k[X_1,\dots,X_s]\hookrightarrow R$$
--   over which $R$ is integral (hence finite as a module).
--
--   So every affine algebra is a finite extension of a polynomial ring. Geometrically, every affine variety admits a finite surjective map onto affine space. The number $s$ is the Krull dimension of $R$, and the lemma is a standard route to Hilbert's Nullstellensatz and to dimension theory.
--
--   **Formalization note.** Mathlib's `exists_integral_inj_algHom_of_fg`. `Algebra.FiniteType k R` means finitely generated as a $k$-algebra, and `g.IsIntegral` means $R$ is integral over the image of `g`. The statement does not record that $s=\dim R$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `exists_integral_inj_algHom_of_fg`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem noether_normalization_lemma (k R : Type*) [Field k] [CommRing R] [Nontrivial R] [Algebra k R] [Algebra.FiniteType k R] :
    ∃ (s : ℕ) (g : MvPolynomial (Fin s) k →ₐ[k] R), Function.Injective g ∧ g.IsIntegral := by sorry

end FamousTheorems
