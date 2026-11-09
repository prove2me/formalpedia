-- Prove2me | Theorems.Thm_ConstGapCircuits_pauli_clifford_gap
-- name    : ConstGapCircuits.pauli_clifford_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:53:13.904869+00:00
-- url     : https://prove2.me/theorems/a678e4a7-ee84-4269-8d33-4686f92ccf56
-- title:
--   Theorem 3.12 — the explicit random Pauli Clifford bound
-- statement:
--   For every $n\ge1$, random Pauli Clifford rotations on the special Clifford group satisfy
--   $$\Delta(\nu_{\mathrm{RPCR}},\mathrm{Cl}(n))\ge\frac{4^n+8}{8(4^n-1)}>\frac18.$$
--
--   The strict inequality is stated for the explicit rational lower bound itself, so it supplies a uniform margin for the real infimum over all representations. Central phases are sampled independently as in Definition 1.2.
--
--   Differences from the source:
--   - reading: finite-dimensional unitary representations in the compact-group setting → continuous homomorphisms into U(d), for every natural dimension d; reason: continuity is the standing compact-group representation convention and ensures the moment integrals are genuine expectations
--   - encoding: matrices on n qubits, local subgroup averages, and operator norms → computational basis Fin n → Fin 2, zero-based qubit indices, closed subgroup Haar measures and Euclidean operator norms; reason: reindexing and bundling preserve every matrix, central phase, measure and norm
--   - encoding: uniform angles and independent local gates → Haar measures on the same closed rotation subgroups and ordered convolution of local Haar measures as in (1.20),(1.22); reason: a uniform angle maps to Haar on its image; the finite-angle law also averages the full centre; the even zero-based layer precedes the odd layer in product order
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 20, Theorem 3.12

import Definitions.Def_ConstGapCircuits_walks

namespace ConstGapCircuits

theorem pauli_clifford_gap (n : ℕ) (hn : 1 ≤ n) :
    ((4 : ℝ)^n + 8) / (8 * ((4 : ℝ)^n - 1)) ≤ spectralGap (rpcr n) ∧
    (1 / 8 : ℝ) < ((4 : ℝ)^n + 8) / (8 * ((4 : ℝ)^n - 1)) := by sorry

end ConstGapCircuits
