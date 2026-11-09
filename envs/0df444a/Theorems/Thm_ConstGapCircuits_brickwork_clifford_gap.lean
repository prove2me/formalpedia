-- Prove2me | Theorems.Thm_ConstGapCircuits_brickwork_clifford_gap
-- name    : ConstGapCircuits.brickwork_clifford_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:53:52.638921+00:00
-- url     : https://prove2.me/theorems/33b1594a-b5b4-45a8-b413-61ac292d6e80
-- title:
--   Theorem 2.14 — brickwork Clifford gap at least 1/80
-- statement:
--   For every $n\ge3$, the depth-two open-chain brickwork random Clifford circuit on $\mathrm{Cl}(n)$ satisfies
--   $$\Delta(\nu_{\mathrm{BRCC}},\mathrm{Cl}(n))\ge\frac1{80}.$$
--
--   The gap is the infimum over all continuous finite-dimensional unitary representations. This uniform estimate implies the Clifford brickwork clause of Theorem 1.3.
--
--   Differences from the source:
--   - reading: finite-dimensional unitary representations in the compact-group setting → continuous homomorphisms into U(d), for every natural dimension d; reason: continuity is the standing compact-group representation convention and ensures the moment integrals are genuine expectations
--   - encoding: matrices on n qubits, local subgroup averages, and operator norms → computational basis Fin n → Fin 2, zero-based qubit indices, closed subgroup Haar measures and Euclidean operator norms; reason: reindexing and bundling preserve every matrix, central phase, measure and norm
--   - encoding: uniform angles and independent local gates → Haar measures on the same closed rotation subgroups and ordered convolution of local Haar measures as in (1.20),(1.22); reason: a uniform angle maps to Haar on its image; the finite-angle law also averages the full centre; the even zero-based layer precedes the odd layer in product order
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 11, Theorem 2.14, (2.15)

import Definitions.Def_ConstGapCircuits_walks

namespace ConstGapCircuits

theorem brickwork_clifford_gap (n : ℕ) (hn : 3 ≤ n) :
    (1 / 80 : ℝ) ≤ spectralGap (brcc n) := by sorry

end ConstGapCircuits
