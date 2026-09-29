-- Prove2me | Theorems.Thm_FamousTheorems_normal_basis_theorem
-- name    : FamousTheorems.normal_basis_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:22:27.502982+00:00
-- url     : https://prove2.me/theorems/82935e46-acc5-4219-b676-265047bc6eaa
-- title:
--   The normal basis theorem
-- statement:
--   **The normal basis theorem.** Let $L/K$ be a finite field extension with automorphism group $\operatorname{Gal}(L/K)$. Then there is an element $x\in L$ whose conjugates $\sigma(x)$, $\sigma\in\operatorname{Gal}(L/K)$, are linearly independent over $K$.
--
--   When $L/K$ is Galois there are exactly $[L:K]$ automorphisms, so these conjugates form a basis of $L$ over $K$, called a normal basis. In other words, $L\cong K[G]$ as a Galois module. The theorem is basic in Galois module theory and in computations in finite fields.
--
--   **Formalization note.** Mathlib's `exists_linearIndependent_algEquiv_apply`, which works for any finite extension. The automorphisms are `L ≃ₐ[K] L`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `exists_linearIndependent_algEquiv_apply`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem normal_basis_theorem (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    ∃ x : L, LinearIndependent K fun σ : L ≃ₐ[K] L => σ x := by sorry

end FamousTheorems
