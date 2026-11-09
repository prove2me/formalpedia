-- Prove2me | Theorems.Thm_ConstGapCircuits_main_spectral_gaps
-- name    : ConstGapCircuits.main_spectral_gaps
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:56:46.852427+00:00
-- url     : https://prove2.me/theorems/a54f53b8-cee7-4aa7-836c-3298e5d80179
-- title:
--   Theorem 1.3 — all four constant spectral-gap bounds
-- statement:
--   Consider the four probability laws of Definition 1.2, using the special unitary group and the special Clifford normalizer with all central phases retained. Their spectral gaps satisfy all four bounds:
--   $$\begin{aligned}
--   \Delta(\nu_{\mathrm{RPR}},\mathrm{SU}(2^n))&>2^{-4} &&(n\ge1),\\
--   \Delta(\nu_{\mathrm{RPCR}},\mathrm{Cl}(n))&>2^{-3} &&(n\ge1),\\
--   \Delta(\nu_{\mathrm{BRUC}},\mathrm{SU}(2^n))&>2^{-53} &&(n\ge2),\\
--   \Delta(\nu_{\mathrm{BRCC}},\mathrm{Cl}(n))&>2^{-7} &&(n\ge2).
--   \end{aligned}$$
--
--   Every bound is on the real infimum over all continuous finite-dimensional unitary representations. The constants are independent of both the number of qubits and the representation dimension. The brickwork circuits use the open chain and independent Haar-random local gates, with no periodic wraparound.
--
--   **Formalization Note** These are four universally quantified assertions in a single conjunction. The two-qubit brickwork Clifford law is Haar on the full Clifford group, so its gap is one.
--
--   Differences from the source:
--   - reading: finite-dimensional unitary representations in the compact-group setting → continuous homomorphisms into U(d), for every natural dimension d; reason: continuity is the standing compact-group representation convention and ensures the moment integrals are genuine expectations
--   - encoding: matrices on n qubits, local subgroup averages, and operator norms → computational basis Fin n → Fin 2, zero-based qubit indices, closed subgroup Haar measures and Euclidean operator norms; reason: reindexing and bundling preserve every matrix, central phase, measure and norm
--   - encoding: uniform angles and independent local gates → Haar measures on the same closed rotation subgroups and ordered convolution of local Haar measures as in (1.20),(1.22); reason: a uniform angle maps to Haar on its image; the finite-angle law also averages the full centre; the even zero-based layer precedes the odd layer in product order
--   - reading: Theorem 1.3 gives no range for n → Pauli clauses for n≥1 and brickwork clauses for n≥2; reason: §3 assumes n≥1; at n=1 both brickwork laws are the identity step and have zero gap; 4.18 starts at n=2; at n=2 the Clifford law is Haar, extending the n≥3 estimate of 2.14 without losing any defined nontrivial case
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 3, Theorem 1.3, clauses (1)–(4)

import Definitions.Def_ConstGapCircuits_walks

namespace ConstGapCircuits

theorem main_spectral_gaps :
    (∀ n : ℕ, 1 ≤ n → (1 / (2 : ℝ)^4) < spectralGap (rpr n)) ∧
    (∀ n : ℕ, 1 ≤ n → (1 / (2 : ℝ)^3) < spectralGap (rpcr n)) ∧
    (∀ n : ℕ, 2 ≤ n → (1 / (2 : ℝ)^53) < spectralGap (bruc n)) ∧
    (∀ n : ℕ, 2 ≤ n → (1 / (2 : ℝ)^7) < spectralGap (brcc n)) := by sorry

end ConstGapCircuits
