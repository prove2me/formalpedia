-- Prove2me | Theorems.Thm_FamousTheorems_wedderburn_artin
-- name    : FamousTheorems.wedderburn_artin
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:13:56.968101+00:00
-- url     : https://prove2.me/theorems/56a32441-2361-4a6e-abd1-074ad4039ad6
-- title:
--   The Wedderburn–Artin theorem
-- statement:
--   **The Wedderburn–Artin theorem.** Every semisimple ring $R$ is isomorphic to a finite product of matrix rings over division rings:
--   $$R\cong\prod_{i=1}^n M_{d_i}(D_i),\qquad d_i\ge1 .$$
--   If $R$ is an algebra over a commutative ring $R_0$, the isomorphism is one of $R_0$-algebras and the $D_i$ are $R_0$-algebras.
--
--   It classifies semisimple rings completely. With Maschke's theorem it describes group algebras $\mathbb C[G]$ as products of matrix algebras, one per irreducible representation. For a simple Artinian ring it gives $R\cong M_d(D)$, the starting point of the theory of central simple algebras and the Brauer group.
--
--   **Formalization note.** Mathlib's `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing`. The division rings are quantified together with their `DivisionRing` and `Algebra R₀` structures and live in the universe of `R`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe u v

theorem wedderburn_artin (R₀ : Type v) (R : Type u) [CommSemiring R₀] [Ring R] [Algebra R₀ R] [IsSemisimpleRing R] :
    ∃ (n : ℕ) (D : Fin n → Type u) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (D i)) (_ : ∀ i, Algebra R₀ (D i)),
      (∀ i, NeZero (d i)) ∧ Nonempty (R ≃ₐ[R₀] ((i : Fin n) → Matrix (Fin (d i)) (Fin (d i)) (D i))) := by sorry

end FamousTheorems
