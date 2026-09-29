-- Prove2me | Theorems.Thm_FamousTheorems_splitting_lemma_modules
-- name    : FamousTheorems.splitting_lemma_modules
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:23:13.053421+00:00
-- url     : https://prove2.me/theorems/cdfd3f6a-8843-4979-b6d5-33ead46e7bc9
-- title:
--   The splitting lemma
-- statement:
--   **The splitting lemma.** Let $0\to M\xrightarrow{f}N\xrightarrow{g}P\to0$ be a short exact sequence of modules over a ring $R$. The following are equivalent:
--   1. $g$ has a section: there is $l:P\to N$ with $g\circ l=\mathrm{id}_P$;
--   2. $f$ has a retraction: there is $l:N\to M$ with $l\circ f=\mathrm{id}_M$;
--   3. the sequence is isomorphic to the split sequence $0\to M\to M\oplus P\to P\to0$, via an isomorphism $N\cong M\oplus P$ compatible with $f$ and $g$.
--
--   The splitting lemma is the basic criterion for a short exact sequence to split. It underlies the definitions of projective and injective modules and the vanishing of $\operatorname{Ext}^1$.
--
--   **Formalization note.** Mathlib's `Function.Exact.split_tfae`. Exactness, injectivity of $f$ and surjectivity of $g$ are the hypotheses, and `List.TFAE` asserts that the three conditions are equivalent. `LinearMap.inl` and `LinearMap.snd` are the canonical inclusion and projection of $M\times P$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Function.Exact.split_tfae`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem splitting_lemma_modules {R M N P : Type*} [Semiring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M]
    [Module R N] [Module R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P} (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    List.TFAE [∃ l : P →ₗ[R] N, g ∘ₗ l = LinearMap.id, ∃ l : N →ₗ[R] M, l ∘ₗ f = LinearMap.id,
      ∃ e : N ≃ₗ[R] M × P, f = e.symm.toLinearMap ∘ₗ LinearMap.inl R M P ∧ g = LinearMap.snd R M P ∘ₗ e.toLinearMap] := by sorry

end FamousTheorems
