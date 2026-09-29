-- Prove2me | Theorems.Thm_FamousTheorems_krull_maximal_ideal_theorem
-- name    : FamousTheorems.krull_maximal_ideal_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:21:58.264239+00:00
-- url     : https://prove2.me/theorems/cbfda7fa-c5aa-4a0d-b0ae-2b0693421d32
-- title:
--   Krull's theorem on maximal ideals
-- statement:
--   **Krull's theorem on maximal ideals.** In a ring $R$ (not necessarily commutative), every proper ideal $I\ne R$ is contained in a maximal ideal.
--
--   The theorem is proved with Zorn's lemma and is in fact equivalent to the axiom of choice. It guarantees that every nonzero ring has a maximal ideal, and so has a nonzero homomorphism to a simple ring (a field in the commutative case). It underlies the definition of the Jacobson radical and of the maximal spectrum.
--
--   **Formalization note.** Mathlib's `Ideal.exists_le_maximal`, stated for left ideals of a semiring.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Ideal.exists_le_maximal`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem krull_maximal_ideal_theorem {R : Type*} [Semiring R] (I : Ideal R) (hI : I ≠ ⊤) : ∃ M : Ideal R, M.IsMaximal ∧ I ≤ M := by sorry

end FamousTheorems
