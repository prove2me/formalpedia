-- Prove2me | Theorems.Thm_FamousTheorems_algebraic_closure_unique_7b
-- name    : FamousTheorems.algebraic_closure_unique_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:32:48.721986+00:00
-- url     : https://prove2.me/theorems/05afe1ea-5884-422c-98cb-8bc1e8556bba
-- title:
--   Uniqueness of the algebraic closure up to isomorphism
-- statement:
--   **Uniqueness of the algebraic closure.** Let $K$ be a field and let $L$ and $M$ be algebraic closures of $K$, meaning algebraically closed fields that are algebraic over $K$. Then there is an isomorphism of fields $L\cong M$ that is the identity on $K$.
--
--   Together with the existence of an algebraic closure, this lets one speak of *the* algebraic closure $\overline K$. The isomorphism is not unique, and the group of its choices is the absolute Galois group of $K$. The proof extends the identity of $K$ to an embedding $L\to M$ by Zorn's lemma; the image is algebraically closed and $M$ is algebraic over it, so the embedding is onto.
--
--   **Formalization note.** Mathlib's `IsAlgClosure.equiv`. `IsAlgClosure K L` says that $L$ is algebraically closed and algebraic over $K$. `L ≃ₐ[K] M` is the type of $K$-algebra isomorphisms, and the statement asserts that it is nonempty.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsAlgClosure.equiv`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem algebraic_closure_unique_7b (K L M : Type*) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    [IsAlgClosure K L] [IsAlgClosure K M] : Nonempty (L ≃ₐ[K] M) := by sorry

end FamousTheorems
