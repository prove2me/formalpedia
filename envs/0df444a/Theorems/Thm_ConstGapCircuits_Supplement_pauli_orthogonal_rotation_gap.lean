-- Prove2me | Theorems.Thm_ConstGapCircuits_Supplement_pauli_orthogonal_rotation_gap
-- name    : ConstGapCircuits.Supplement.pauli_orthogonal_rotation_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:31:46.138743+00:00
-- url     : https://prove2.me/theorems/33851701-cc81-46b8-9f7b-71ffa6d99e65
-- title:
--   Theorem 3.54 (corrected: false comparison with 1/16 removed) — orthogonal Pauli rotation gap
-- statement:
--   For every $n\ge1$, let $\nu_{\mathrm{RPOR}}$ choose a Hermitian Pauli string with an odd number of $Y$ factors uniformly, choose an independent uniform circle angle $\theta$, and apply $e^{i\theta P}$. On the special orthogonal group,
--   $$
--   \Delta(\nu_{\mathrm{RPOR}},\mathrm{SO}(2^n))\ge
--   \frac{4^{n-1}-2^{n-1}+8}{4^{n+1}-2^{n+2}}.
--   $$
--   This companion theorem supplies the explicit orthogonal rotation estimate. The printed additional comparison of this fraction with $1/16$ is false: at $n=5$ it equals $248/3968=1/16$, and at $n=6$ it equals $125/2016<1/16$. The explicit lower bound is retained on the entire domain, including the one-qubit circle case.
--
--   Differences from the source:
--   - correction: the displayed lower bound is followed by the strict comparison >1/16 → the exact displayed lower bound alone for every n≥1; reason: n=5 satisfies the domain and makes the fraction 248/3968=1/16; n=6 makes it 125/2016<1/16, so the numerical comparison is false; equation (3.55) yields the retained fraction
--   - encoding: real determinant-one matrices on n qubits and their local groups → the real-entry closed subgroup of the published SU n, with computational basis Fin n → Fin 2 and zero-based qubit labels; reason: the inclusion preserves every matrix and its subspace topology; the full-space determinant test retains both local determinant components when permitted
--   - encoding: the spectral gap of Definition 1.1 and Haar subgroup projectors → the published spectralGap and subgroupProjector on the designated compact group, over all continuous finite-dimensional complex unitary representations and with Euclidean operator norm; reason: this is the standing representation convention of §1.4; normalized Haar averages are probability expectations on compact groups
--   - encoding: P uniform on Y_n and θ uniform on the full circle, for n≥1 in §3 → the uniform finite mixture of Haar measures on the closed rotation circles inside SO n, with 1≤n; reason: odd Y parity makes every rotation real and determinant one; a uniform angle pushes to Haar on its image, and n≥1 ensures the Pauli index set is nonempty
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 25, Theorem 3.54; PDF sha256 e8cf47b0382db220adaab4a2a08a778925d68118885ede05fe433e280cb5da26

import Definitions.Def_ConstGapCircuits_Supplement_orthogonalWalks

namespace ConstGapCircuits.Supplement

/-- Theorem 3.54, p.25 (corrected: remove the false comparison of the fraction with 1/16).
At n=5 the displayed fraction is 248/3968=1/16; at n=6 it is 1000/16128=125/2016<1/16.
The exact lower bound itself is retained for every n≥1, including SO(2). -/
theorem pauli_orthogonal_rotation_gap (n : ℕ) (hn : 1 ≤ n) :
    ((4 : ℝ) ^ (n - 1) - (2 : ℝ) ^ (n - 1) + 8) /
      ((4 : ℝ) ^ (n + 1) - (2 : ℝ) ^ (n + 2)) ≤ spectralGap (rpor n) := by sorry

end ConstGapCircuits.Supplement
