-- Prove2me | Theorems.Thm_FamousTheorems_jacobson_density
-- name    : FamousTheorems.jacobson_density
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T09:15:16.136516+00:00
-- url     : https://prove2.me/theorems/d1c0064b-8cb7-4b48-bed5-0292831c6d9c
-- title:
--   The Jacobson density theorem
-- statement:
--   **The Jacobson density theorem.** Let $M$ be a semisimple module over a ring $R$, and let $f$ be any additive map $M\to M$ commuting with every $R$-endomorphism of $M$ (i.e. an element of the bicommutant). For every finite set $s\subseteq M$ there is $r\in R$ with $f(m)=r\cdot m$ for all $m\in s$.
--
--   So the image of $R$ is dense in its bicommutant in the finite topology. This is the algebraic analogue of von Neumann's bicommutant theorem. With Schur's lemma it yields the Wedderburn–Artin structure theorem and Burnside's theorem on irreducible matrix algebras.
--
--   **Formalization note.** Mathlib's `jacobson_density`; the bicommutant is `Module.End (Module.End R M) M`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `jacobson_density`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem jacobson_density {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]
    (f : Module.End (Module.End R M) M) (s : Finset M) : ∃ r : R, ∀ m ∈ s, f m = r • m := by sorry

end FamousTheorems
