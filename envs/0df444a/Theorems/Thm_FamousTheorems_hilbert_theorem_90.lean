-- Prove2me | Theorems.Thm_FamousTheorems_hilbert_theorem_90
-- name    : FamousTheorems.hilbert_theorem_90
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:39.169364+00:00
-- url     : https://prove2.me/theorems/705a8989-5d61-4f02-be03-41bf337d9ecf
-- title:
--   Hilbert's Theorem 90
-- statement:
--   **Hilbert's Theorem 90 (multiplicative form).** Let $L/K$ be a finite Galois extension with group $G$, or more generally any finite extension with $G=\operatorname{Aut}_K(L)$. Let $f:G\to L^\times$ be a 1-cocycle, meaning $f(\sigma\tau)=f(\sigma)\,\sigma(f(\tau))$. Then $f$ is a coboundary: there is $\beta\in L^\times$ with $f(\sigma)=\sigma(\beta)/\beta$ for all $\sigma$. Equivalently, $H^1(G,L^\times)=0$.
--
--   For a cyclic extension this gives the classical statement: an element of norm $1$ has the form $\sigma(\beta)/\beta$. Hilbert's Theorem 90 is a cornerstone of Galois cohomology. It underlies Kummer theory, the classification of Pythagorean triples via $\mathbb Q(i)/\mathbb Q$, and descent for vector spaces.
--
--   **Formalization note.** Mathlib's `groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`. The group is `L ≃ₐ[K] L`, the $K$-algebra automorphisms of $L$. `IsMulCocycle₁` and `IsMulCoboundary₁` are Mathlib's multiplicative 1-cocycle and 1-coboundary conditions for the natural action on the units `Lˣ`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hilbert_theorem_90 {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (f : (L ≃ₐ[K] L) → Lˣ)
    (hf : groupCohomology.IsMulCocycle₁ f) : groupCohomology.IsMulCoboundary₁ f := by sorry

end FamousTheorems
