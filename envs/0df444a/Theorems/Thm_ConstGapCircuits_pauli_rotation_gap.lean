-- Prove2me | Theorems.Thm_ConstGapCircuits_pauli_rotation_gap
-- name    : ConstGapCircuits.pauli_rotation_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:53:22.37962+00:00
-- url     : https://prove2.me/theorems/165613f9-3155-405c-9135-7327babc5a26
-- title:
--   Theorem 3.18 — the explicit random Pauli rotation bound
-- statement:
--   For every $n\ge1$, random Pauli rotations on the full special unitary group satisfy
--   $$\Delta(\nu_{\mathrm{RPR}},\mathrm{SU}(2^n))\ge\frac{4^n+16}{16(4^n-1)}>\frac1{16}.$$
--
--   Both comparisons are retained. The estimate concerns the actual infimum over every continuous finite-dimensional unitary representation, giving the strict first clause of Theorem 1.3.
--
--   Differences from the source:
--   - reading: finite-dimensional unitary representations in the compact-group setting → continuous homomorphisms into U(d), for every natural dimension d; reason: continuity is the standing compact-group representation convention and ensures the moment integrals are genuine expectations
--   - encoding: matrices on n qubits, local subgroup averages, and operator norms → computational basis Fin n → Fin 2, zero-based qubit indices, closed subgroup Haar measures and Euclidean operator norms; reason: reindexing and bundling preserve every matrix, central phase, measure and norm
--   - encoding: uniform angles and independent local gates → Haar measures on the same closed rotation subgroups and ordered convolution of local Haar measures as in (1.20),(1.22); reason: a uniform angle maps to Haar on its image; the finite-angle law also averages the full centre; the even zero-based layer precedes the odd layer in product order
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 20, Theorem 3.18

import Definitions.Def_ConstGapCircuits_walks

namespace ConstGapCircuits

theorem pauli_rotation_gap (n : ℕ) (hn : 1 ≤ n) :
    ((4 : ℝ)^n + 16) / (16 * ((4 : ℝ)^n - 1)) ≤ spectralGap (rpr n) ∧
    (1 / 16 : ℝ) < ((4 : ℝ)^n + 16) / (16 * ((4 : ℝ)^n - 1)) := by sorry

end ConstGapCircuits
