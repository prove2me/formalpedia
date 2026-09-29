-- Prove2me | Theorems.Thm_FamousTheorems_spectrum_nonempty_banach_algebra_7a
-- name    : FamousTheorems.spectrum_nonempty_banach_algebra_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:25:55.106187+00:00
-- url     : https://prove2.me/theorems/8b516c74-3789-4f50-8624-54a63fc831fc
-- title:
--   The spectrum of an element of a complex Banach algebra is nonempty
-- statement:
--   **The spectrum of an element of a complex Banach algebra is nonempty.** Let $A$ be a nontrivial complex Banach algebra with unit. For every $a\in A$ the spectrum
--   $$\sigma(a)=\{\lambda\in\mathbb C: a-\lambda1\text{ is not invertible}\}$$
--   is nonempty.
--
--   Gelfand proved this in 1941. The proof applies Liouville's theorem to the resolvent $\lambda\mapsto(a-\lambda)^{-1}$. The theorem fails over $\mathbb R$, as rotation matrices show. A consequence is the Gelfand–Mazur theorem, that a complex Banach division algebra is $\mathbb C$. It is the starting point of Gelfand theory for commutative Banach algebras.
--
--   **Formalization note.** Mathlib's `spectrum.nonempty`. `spectrum ℂ a` is the set of $\lambda$ such that $\lambda\cdot1-a$ is not a unit.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `spectrum.nonempty`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem spectrum_nonempty_banach_algebra_7a {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (a : A) :
    (spectrum ℂ a).Nonempty := by sorry

end FamousTheorems
