-- Prove2me | Theorems.Thm_ConstGapCircuits_clifford_angle_gap
-- name    : ConstGapCircuits.clifford_angle_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:56:49.064873+00:00
-- url     : https://prove2.me/theorems/8c7f4fb0-7654-44c7-8724-8a60fb0c2cd0
-- title:
--   Lemma 3.10 — Clifford membership and the local gap 3/2
-- statement:
--   Let $n\ge1$ and $\Theta_8=\{m\pi/4+2\pi\mathbb Z:m\in\mathbb Z\}$. Every nonidentity Hermitian Pauli string $P$ and every angle $\theta\in\Theta_8$ satisfy
--   $$e^{i\theta P}\in\mathrm{Cl}(n),\qquad \Delta_{\Theta_8}=\frac32.$$
--
--   The first clause concerns actual determinant-one matrices, with no phase quotient. The second gives the single-qubit input for the random Pauli Clifford bound. The discrete local projectors include the full centre as specified in the proof.
--
--   Differences from the source:
--   - reading: finite-dimensional unitary representations in the compact-group setting → continuous homomorphisms into U(d), for every natural dimension d; reason: continuity is the standing compact-group representation convention and ensures the moment integrals are genuine expectations
--   - encoding: matrices on n qubits, local subgroup averages, and operator norms → computational basis Fin n → Fin 2, zero-based qubit indices, closed subgroup Haar measures and Euclidean operator norms; reason: reindexing and bundling preserve every matrix, central phase, measure and norm
--   - encoding: membership of the unitary rotation in Cl(n) → existence of a Clifford-group element with exactly that matrix; reason: Cl(n) is a subtype of SU(2^n), so this states both matrix membership and determinant one
--   - reading: the discrete local group includes the centre in the proof → the triangle projectors include that same centre; reason: this makes (3.3) consistent with its use in 3.12
--   - reading: L_Θ≤LU(2) alongside an explicit inclusion in SU(2) → the three Pauli axes on one qubit inside SU(2^n); reason: the same sentence and the proof of 3.10 identify the one-qubit group
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 19, Lemma 3.10

import Definitions.Def_ConstGapCircuits_triangleGap

namespace ConstGapCircuits

theorem clifford_angle_gap (n : ℕ) (hn : 1 ≤ n) :
    (∀ p : PauliIndex n, ∀ θ : ℝ, (θ : AngleGroup) ∈ cliffordAngles →
      ∃ U : Cl n, ((U.val : SU n) : Mat n) = rotation p.val θ) ∧
    thetaGap n cliffordAngles = (3 / 2 : ℝ) := by sorry

end ConstGapCircuits
