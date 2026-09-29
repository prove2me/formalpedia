-- Prove2me | Theorems.Thm_FamousTheorems_hahn_embedding_theorem
-- name    : FamousTheorems.hahn_embedding_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:15:24.39218+00:00
-- url     : https://prove2.me/theorems/ba71b2a2-ba8c-4707-8815-32c39f36e50c
-- title:
--   The Hahn embedding theorem
-- statement:
--   **The Hahn embedding theorem.** Every linearly ordered abelian group $M$ embeds, as an ordered group, into the lexicographically ordered group of Hahn series $\mathbb R((\Gamma))$ with real coefficients, where $\Gamma$ is the ordered set of nontrivial Archimedean classes of $M$. The embedding sends each element to a series whose leading exponent is its Archimedean class.
--
--   It generalises Hölder's theorem (Archimedean ordered groups embed in $\mathbb R$) and gives a complete picture of ordered abelian groups up to their Archimedean skeleton. It is basic to valuation theory and the model theory of ordered fields.
--
--   **Formalization note.** Mathlib's `hahnEmbedding_isOrderedAddMonoid`. The target is `Lex (HahnSeries (FiniteArchimedeanClass M) ℝ)`, and the second conjunct says the Archimedean class of `a` equals the order (leading exponent) of its image, via `FiniteArchimedeanClass.withTopOrderIso`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `hahnEmbedding_isOrderedAddMonoid`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hahn_embedding_theorem (M : Type*) [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] :
    ∃ f : M →+o Lex (HahnSeries (FiniteArchimedeanClass M) ℝ), Function.Injective f ∧
      ∀ a : M, ArchimedeanClass.mk a = FiniteArchimedeanClass.withTopOrderIso M (ofLex (f a)).orderTop := by sorry

end FamousTheorems
