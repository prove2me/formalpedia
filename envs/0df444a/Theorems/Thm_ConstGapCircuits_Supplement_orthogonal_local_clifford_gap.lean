-- Prove2me | Theorems.Thm_ConstGapCircuits_Supplement_orthogonal_local_clifford_gap
-- name    : ConstGapCircuits.Supplement.orthogonal_local_clifford_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:30:28.709516+00:00
-- url     : https://prove2.me/theorems/aea68751-98e0-4b62-992a-653d27067d96
-- title:
--   Corollary 2.46 — three-qubit orthogonal Clifford gap
-- statement:
--   Let $n\ge3$ and let $a,b,c$ be three distinct qubits. Write $L_S=\mathrm{LCl}(S,n;\mathbb R)$. For every continuous finite-dimensional complex unitary representation $\rho$ of $L_{\{a,b,c\}}$, let $\Pi(\rho|L_T)$ be its Haar invariant projector on the subgroup $L_T$. Then
--   $$
--   \left\|\frac{\Pi(\rho|L_{\{a,b\}})+\Pi(\rho|L_{\{b,c\}})}2-\Pi(\rho|L_{\{a,b,c\}})\right\|_{\mathrm{op}}\le1-\frac5{18}.
--   $$
--   This uniform local estimate is the quantitative input for the orthogonal Clifford brickwork gap.
--
--   Differences from the source:
--   - encoding: real determinant-one matrices on n qubits and their local groups → the real-entry closed subgroup of the published SU n, with computational basis Fin n → Fin 2 and zero-based qubit labels; reason: the inclusion preserves every matrix and its subspace topology; the full-space determinant test retains both local determinant components when permitted
--   - encoding: the spectral gap of Definition 1.1 and Haar subgroup projectors → the published spectralGap and subgroupProjector on the designated compact group, over all continuous finite-dimensional complex unitary representations and with Euclidean operator norm; reason: this is the standing representation convention of §1.4; normalized Haar averages are probability expectations on compact groups
--   - encoding: three qubits a,b,c and pair subgroups inside LCl^R_{abc} → three pairwise distinct Fin n labels; withinLocal subgroups for ab and bc and the invariantProjector of the abc parent; reason: the labels are three distinct physical qubits; intersection with the abc group leaves the pair groups unchanged, and its full Haar projector equals the displayed abc projector
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 17, Corollary 2.46; PDF sha256 e8cf47b0382db220adaab4a2a08a778925d68118885ede05fe433e280cb5da26

import Definitions.Def_ConstGapCircuits_Supplement_orthogonalGroups
import Definitions.Def_ConstGapCircuits_spectralGap

namespace ConstGapCircuits.Supplement

/-- Corollary 2.46, (2.47), p.17, for all representations of the three-qubit local group. -/
theorem orthogonal_local_clifford_gap (n : ℕ) (hn : 3 ≤ n)
    (a b c : Fin n) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (ρ : UnitaryRep (localOrthogonalClifford {a,b,c})) :
    opNorm ((1 / 2 : ℂ) •
      (subgroupProjector (withinLocal {a,b,c} {a,b}) ρ +
       subgroupProjector (withinLocal {a,b,c} {b,c}) ρ) - invariantProjector ρ) ≤
      1 - (5 / 18 : ℝ) := by sorry

end ConstGapCircuits.Supplement
