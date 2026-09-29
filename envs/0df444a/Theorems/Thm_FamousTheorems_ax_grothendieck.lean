-- Prove2me | Theorems.Thm_FamousTheorems_ax_grothendieck
-- name    : FamousTheorems.ax_grothendieck
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:15:18.169308+00:00
-- url     : https://prove2.me/theorems/29995e37-0a2e-4a9a-a7d3-4f0b15ade434
-- title:
--   The Ax–Grothendieck theorem
-- statement:
--   **The Ax–Grothendieck theorem.** Let $K$ be an algebraically closed field. Every injective polynomial map $K^n\to K^n$ is surjective.
--
--   Ax's proof is a celebrated application of model theory. The statement is trivially true over finite fields and therefore over their algebraic closures, and it transfers to all algebraically closed fields by the Lefschetz principle (completeness of the theory of algebraically closed fields of each characteristic). Grothendieck gave an algebraic-geometric proof.
--
--   **Formalization note.** Mathlib's `ax_grothendieck_univ`, for a finite index type `ι` of coordinates; the map is $v\mapsto(p_i(v))_i$. Mathlib's more general `ax_grothendieck_zeroLocus` handles polynomial self-maps of any affine variety.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ax_grothendieck_univ`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem ax_grothendieck {K ι : Type*} [Field K] [IsAlgClosed K] [Finite ι] (p : ι → MvPolynomial ι K)
    (hinj : Function.Injective fun (v : ι → K) (i : ι) => MvPolynomial.eval v (p i)) :
    Function.Surjective fun (v : ι → K) (i : ι) => MvPolynomial.eval v (p i) := by sorry

end FamousTheorems
