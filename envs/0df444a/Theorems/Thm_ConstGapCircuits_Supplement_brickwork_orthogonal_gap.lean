-- Prove2me | Theorems.Thm_ConstGapCircuits_Supplement_brickwork_orthogonal_gap
-- name    : ConstGapCircuits.Supplement.brickwork_orthogonal_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:32:24.297867+00:00
-- url     : https://prove2.me/theorems/73168afe-4f46-4276-8d4f-e1ed68bdf504
-- title:
--   Theorem 4.19 — brickwork orthogonal gap greater than 2^{-56}
-- statement:
--   For every $n\ge2$, let $\nu_{\mathrm{BROC}}$ be the depth-two brickwork law on an open chain of $n$ qubits, with independent Haar-random gates from the full supported orthogonal local groups. Then
--   $$
--   \Delta(\nu_{\mathrm{BROC}},\mathrm{SO}(2^n))>2^{-56}.
--   $$
--   The full-space determinant-one convention allows local $\mathrm O(4)$ blocks of either determinant when $n\ge3$; for $n=2$ the single local group is $\mathrm{SO}(4)$. This companion theorem gives a constant lower bound uniform over the qubit count and all representations of the designated orthogonal group.
--
--   Differences from the source:
--   - encoding: real determinant-one matrices on n qubits and their local groups → the real-entry closed subgroup of the published SU n, with computational basis Fin n → Fin 2 and zero-based qubit labels; reason: the inclusion preserves every matrix and its subspace topology; the full-space determinant test retains both local determinant components when permitted
--   - encoding: the spectral gap of Definition 1.1 and Haar subgroup projectors → the published spectralGap and subgroupProjector on the designated compact group, over all continuous finite-dimensional complex unitary representations and with Euclidean operator norm; reason: this is the standing representation convention of §1.4; normalized Haar averages are probability expectations on compact groups
--   - encoding: independent Haar local gates in the depth-two open-chain brickwork order → the published brickwork convolution on n−1 bonds, even zero-based bonds followed by odd zero-based bonds; reason: zero-based bond j is the source bond j+1, preserving the two layers and their product order
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 28, Theorem 4.19; PDF sha256 e8cf47b0382db220adaab4a2a08a778925d68118885ede05fe433e280cb5da26

import Definitions.Def_ConstGapCircuits_Supplement_orthogonalWalks

namespace ConstGapCircuits.Supplement

/-- Theorem 4.19, p.28, with the full supported orthogonal local groups. -/
theorem brickwork_orthogonal_gap (n : ℕ) (hn : 2 ≤ n) :
    (1 / (2 : ℝ) ^ 56) < spectralGap (broc n) := by sorry

end ConstGapCircuits.Supplement
