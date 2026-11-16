-- Prove2me | Theorems.Thm_ConstGapCircuits_Supplement_brickwork_orthogonal_clifford_gap
-- name    : ConstGapCircuits.Supplement.brickwork_orthogonal_clifford_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:31:08.179525+00:00
-- url     : https://prove2.me/theorems/9e586e34-435d-42cb-aebf-71c162c801df
-- title:
--   Theorem 2.50 — brickwork orthogonal Clifford gap at least 1/144
-- statement:
--   For every $n\ge3$, let $\nu_{\mathrm{BROCC}}$ be the depth-two brickwork law on the open chain of $n$ qubits, with independent Haar-random local orthogonal Clifford gates. Its spectral gap on the orthogonal Clifford group satisfies
--   $$
--   \Delta(\nu_{\mathrm{BROCC}},\mathrm{Cl}(n;\mathbb R))\ge\frac1{144}.
--   $$
--   This is a companion theorem to the unitary and Clifford bounds in Theorem 1.3. The constant is uniform in the number of qubits and over every representation of the orthogonal Clifford group.
--
--   Differences from the source:
--   - encoding: real determinant-one matrices on n qubits and their local groups → the real-entry closed subgroup of the published SU n, with computational basis Fin n → Fin 2 and zero-based qubit labels; reason: the inclusion preserves every matrix and its subspace topology; the full-space determinant test retains both local determinant components when permitted
--   - encoding: the spectral gap of Definition 1.1 and Haar subgroup projectors → the published spectralGap and subgroupProjector on the designated compact group, over all continuous finite-dimensional complex unitary representations and with Euclidean operator norm; reason: this is the standing representation convention of §1.4; normalized Haar averages are probability expectations on compact groups
--   - encoding: independent Haar local gates in the depth-two open-chain brickwork order → the published brickwork convolution on n−1 bonds, even zero-based bonds followed by odd zero-based bonds; reason: zero-based bond j is the source bond j+1, preserving the two layers and their product order
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 18, Theorem 2.50; PDF sha256 e8cf47b0382db220adaab4a2a08a778925d68118885ede05fe433e280cb5da26

import Definitions.Def_ConstGapCircuits_Supplement_orthogonalWalks

namespace ConstGapCircuits.Supplement

/-- Theorem 2.50, (2.51), p.18. -/
theorem brickwork_orthogonal_clifford_gap (n : ℕ) (hn : 3 ≤ n) :
    (1 / 144 : ℝ) ≤ spectralGap (brocc n) := by sorry

end ConstGapCircuits.Supplement
