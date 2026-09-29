-- Prove2me | Theorems.Thm_FamousTheorems_gelfand_mazur
-- name    : FamousTheorems.gelfand_mazur
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:43.651674+00:00
-- url     : https://prove2.me/theorems/9e7c06bc-e5f2-48bf-85bf-e3259bf2b58d
-- title:
--   The Gelfand–Mazur theorem
-- statement:
--   **The Gelfand–Mazur theorem.** Let $A$ be a complex Banach algebra in which every nonzero element is invertible. Then $A$ is isomorphic to $\mathbb C$ as a $\mathbb C$-algebra.
--
--   The proof rests on the nonemptiness of the spectrum, via Liouville's theorem. The theorem is a cornerstone of Gelfand theory: quotients of a commutative Banach algebra by maximal ideals are $\mathbb C$, so maximal ideals correspond to characters. This is the entry point to the Gelfand transform and the commutative Gelfand–Naimark theorem.
--
--   **Formalization note.** Mathlib's `NormedRing.algEquivComplexOfComplete`, which constructs the algebra isomorphism `ℂ ≃ₐ[ℂ] A`. The division hypothesis is `∀ a, IsUnit a ↔ a ≠ 0`. The real version (a real normed division field is $\mathbb R$ or $\mathbb C$) is `NormedAlgebra.Real.nonempty_algEquiv_or`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `NormedRing.algEquivComplexOfComplete`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem gelfand_mazur {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (hA : ∀ {a : A}, IsUnit a ↔ a ≠ 0) :
    Nonempty (ℂ ≃ₐ[ℂ] A) := by sorry

end FamousTheorems
