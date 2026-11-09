-- Prove2me | Theorems.Thm_ConstGapCircuits_brickwork_unitary_gap
-- name    : ConstGapCircuits.brickwork_unitary_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:53:48.786886+00:00
-- url     : https://prove2.me/theorems/54d16ece-3d48-4c9c-9ee7-1ca1238720eb
-- title:
--   Theorem 4.18 — brickwork unitary gap greater than 2^{-53}
-- statement:
--   For every $n\ge2$, the depth-two brickwork random unitary circuit on the open one-dimensional chain satisfies
--   $$\Delta(\nu_{\mathrm{BRUC}},\mathrm{SU}(2^n))>2^{-53}.$$
--
--   This is the strict bound on the real infimum over every continuous finite-dimensional unitary representation, with the printed constant retained.
--
--   Differences from the source:
--   - reading: finite-dimensional unitary representations in the compact-group setting → continuous homomorphisms into U(d), for every natural dimension d; reason: continuity is the standing compact-group representation convention and ensures the moment integrals are genuine expectations
--   - encoding: matrices on n qubits, local subgroup averages, and operator norms → computational basis Fin n → Fin 2, zero-based qubit indices, closed subgroup Haar measures and Euclidean operator norms; reason: reindexing and bundling preserve every matrix, central phase, measure and norm
--   - encoding: uniform angles and independent local gates → Haar measures on the same closed rotation subgroups and ordered convolution of local Haar measures as in (1.20),(1.22); reason: a uniform angle maps to Haar on its image; the finite-angle law also averages the full centre; the even zero-based layer precedes the odd layer in product order
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 28, Theorem 4.18

import Definitions.Def_ConstGapCircuits_walks

namespace ConstGapCircuits

theorem brickwork_unitary_gap (n : ℕ) (hn : 2 ≤ n) :
    (1 / (2 : ℝ)^53) < spectralGap (bruc n) := by sorry

end ConstGapCircuits
