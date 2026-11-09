-- Prove2me | Theorems.Thm_ConstGapCircuits_circle_angle_gap
-- name    : ConstGapCircuits.circle_angle_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:56:47.069622+00:00
-- url     : https://prove2.me/theorems/2056cc6b-d30f-4908-833f-e6309c220311
-- title:
--   Lemma 3.13 — the full-circle local gap 5/4
-- statement:
--   For every $n\ge1$, take the full angle group $\Theta=\mathbb R/2\pi\mathbb Z$. The one-qubit triangle Hamiltonian, embedded on the first qubit, has universal local gap
--   $$\Delta_\Theta=\frac54.$$
--
--   The definition tests every continuous finite-dimensional unitary representation of the generated one-qubit group. This is the local spectral input for the random Pauli rotation theorem.
--
--   Differences from the source:
--   - reading: finite-dimensional unitary representations in the compact-group setting → continuous homomorphisms into U(d), for every natural dimension d; reason: continuity is the standing compact-group representation convention and ensures the moment integrals are genuine expectations
--   - encoding: matrices on n qubits, local subgroup averages, and operator norms → computational basis Fin n → Fin 2, zero-based qubit indices, closed subgroup Haar measures and Euclidean operator norms; reason: reindexing and bundling preserve every matrix, central phase, measure and norm
--   - reading: L_Θ≤LU(2) alongside an explicit inclusion in SU(2) → the three Pauli axes on one qubit inside SU(2^n); reason: the same sentence and the proof of 3.10 identify the one-qubit group
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 20, Lemma 3.13

import Definitions.Def_ConstGapCircuits_triangleGap

namespace ConstGapCircuits

theorem circle_angle_gap (n : ℕ) (hn : 1 ≤ n) :
    thetaGap n circleAngles = (5 / 4 : ℝ) := by sorry

end ConstGapCircuits
