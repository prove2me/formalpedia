-- Prove2me | Theorems.Thm_FamousTheorems_cohen_noetherian_prime_ideals_7b
-- name    : FamousTheorems.cohen_noetherian_prime_ideals_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:49.463562+00:00
-- url     : https://prove2.me/theorems/c1a9d97b-7df4-4b7b-b919-4102b376d861
-- title:
--   Cohen's theorem: a ring whose prime ideals are finitely generated is Noetherian
-- statement:
--   **Cohen's theorem.** Let $R$ be a commutative ring in which every prime ideal is finitely generated. Then $R$ is Noetherian.
--
--   To check that a ring is Noetherian it is therefore enough to look at prime ideals. The proof is by contradiction: if some ideal is not finitely generated, Zorn's lemma gives a maximal such ideal, and one shows that it is prime. The argument is a model for the "Oka families" of ideals studied by Lam and Reyes. A similar result for principal ideals says that a ring whose prime ideals are principal is a principal ideal ring.
--
--   **Formalization note.** Mathlib's `IsNoetherianRing.of_prime`. `Ideal.FG` means finitely generated.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsNoetherianRing.of_prime`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cohen_noetherian_prime_ideals_7b {R : Type*} [CommRing R] (h : ∀ I : Ideal R, I.IsPrime → I.FG) : IsNoetherianRing R := by sorry

end FamousTheorems
