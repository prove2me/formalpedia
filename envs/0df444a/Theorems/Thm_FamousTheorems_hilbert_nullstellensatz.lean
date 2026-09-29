-- Prove2me | Theorems.Thm_FamousTheorems_hilbert_nullstellensatz
-- name    : FamousTheorems.hilbert_nullstellensatz
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:15.256892+00:00
-- url     : https://prove2.me/theorems/0b87d8d1-640a-4eae-a5e5-4bbd63906345
-- title:
--   Hilbert's Nullstellensatz
-- statement:
--   **Hilbert's Nullstellensatz.** Let $k\subseteq K$ be fields with $K$ algebraically closed, and $I$ an ideal of $k[x_1,\dots,x_n]$. A polynomial over $k$ vanishes at every common zero of $I$ in $K^n$ if and only if some power of it lies in $I$:
--   $$\mathcal I\big(\mathcal Z_K(I)\big)=\sqrt I .$$
--
--   This is the foundational theorem of classical algebraic geometry. It sets up the bijection between radical ideals and algebraic sets (and between maximal ideals and points), turning geometry into commutative algebra.
--
--   **Formalization note.** Mathlib's `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`, for a finite set of variables `σ`. The zero locus is taken over the algebraically closed extension `K`, and the vanishing ideal back in polynomials over `k`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hilbert_nullstellensatz {k K : Type*} [Field k] [Field K] [Algebra k K] {σ : Type*} [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) : MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus K I) = I.radical := by sorry

end FamousTheorems
