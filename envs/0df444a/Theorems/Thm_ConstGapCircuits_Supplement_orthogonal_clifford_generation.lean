-- Prove2me | Theorems.Thm_ConstGapCircuits_Supplement_orthogonal_clifford_generation
-- name    : ConstGapCircuits.Supplement.orthogonal_clifford_generation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:30:04.296114+00:00
-- url     : https://prove2.me/theorems/1e605b71-d5e3-45d6-b38f-ea3a201a1d26
-- title:
--   Proposition 2.44 — generation by two-qubit orthogonal Cliffords
-- statement:
--   For $n\ge3$, consider every two-element qubit set $S$ and its local orthogonal Clifford group $\mathrm{LCl}(S,n;\mathbb R)$. Then
--   $$
--   \left\langle\bigcup_{|S|=2}\mathrm{LCl}(S,n;\mathbb R)\right\rangle=\mathrm{Cl}(n;\mathbb R).
--   $$
--   Generation here means finite products and inverses, and includes every pair, without a nearest-neighbor restriction. The result identifies the common invariant space needed by the orthogonal Clifford chain argument.
--
--   Differences from the source:
--   - encoding: real determinant-one matrices on n qubits and their local groups → the real-entry closed subgroup of the published SU n, with computational basis Fin n → Fin 2 and zero-based qubit labels; reason: the inclusion preserves every matrix and its subspace topology; the full-space determinant test retains both local determinant components when permitted
--   - encoding: the two-qubit local groups generate Cl(n; R) → Subgroup.closure of the union indexed by two-element finite qubit sets equals the full group; reason: Subgroup.closure is algebraic generation, with no topological closure or density substitution
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 17, Proposition 2.44; PDF sha256 e8cf47b0382db220adaab4a2a08a778925d68118885ede05fe433e280cb5da26

import Definitions.Def_ConstGapCircuits_Supplement_orthogonalGroups

namespace ConstGapCircuits.Supplement

/-- Proposition 2.44, p.17. Generation is algebraic and ranges over every qubit pair. -/
theorem orthogonal_clifford_generation (n : ℕ) (hn : 3 ≤ n) :
    Subgroup.closure {U : OCl n | ∃ S : Finset (Fin n),
      S.card = 2 ∧ U ∈ localOrthogonalClifford S} = ⊤ := by sorry

end ConstGapCircuits.Supplement
