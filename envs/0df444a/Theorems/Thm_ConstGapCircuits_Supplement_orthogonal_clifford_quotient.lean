-- Prove2me | Theorems.Thm_ConstGapCircuits_Supplement_orthogonal_clifford_quotient
-- name    : ConstGapCircuits.Supplement.orthogonal_clifford_quotient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:29:34.900928+00:00
-- url     : https://prove2.me/theorems/b06125fe-06de-4841-acff-63fe1d46a4f9
-- title:
--   Proposition 2.36 — orthogonal Clifford quotient
-- statement:
--   Let $n\ge3$. Let $\mathcal P(n;\mathbb R)$ be the orthogonal Pauli group and let $\mathrm{Cl}(n;\mathbb R)$ be its normalizer in $\mathrm{SO}(2^n)$. For $\phi(a,b)=a\cdot b$ on $\mathbb F_2^n\times\mathbb F_2^n$, one has
--   $$
--   \mathrm{Cl}(n;\mathbb R)/\mathcal P(n;\mathbb R)\cong\mathrm O^+(2n;\mathbb F_2).
--   $$
--   The central signs already lie in $\mathcal P(n;\mathbb R)$. This identifies the finite quadratic symmetry group used by the orthogonal Clifford local-gap calculation.
--
--   Differences from the source:
--   - encoding: real determinant-one matrices on n qubits and their local groups → the real-entry closed subgroup of the published SU n, with computational basis Fin n → Fin 2 and zero-based qubit labels; reason: the inclusion preserves every matrix and its subspace topology; the full-space determinant test retains both local determinant components when permitted
--   - encoding: the quotient by the orthogonal Pauli group and the center is isomorphic to O^+(2n; F_2) → there exists a surjective group homomorphism to the linear automorphism group of φ(a,b)=a·b whose kernel is exactly the orthogonal Pauli set; reason: the first isomorphism theorem gives precisely the quotient claim; the center {±1} is already contained in that kernel
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 15, Proposition 2.36; PDF sha256 e8cf47b0382db220adaab4a2a08a778925d68118885ede05fe433e280cb5da26

import Definitions.Def_ConstGapCircuits_Supplement_orthogonalGroups
import Definitions.Def_ConstGapCircuits_Supplement_splitOrthogonal

namespace ConstGapCircuits.Supplement

/-- Proposition 2.36, pp.15--17: the quotient is O^+(2n; F_2).
The equivalent surjection-with-exact-kernel formulation avoids a separate normality interface.
The central signs already belong to the orthogonal Pauli group. -/
theorem orthogonal_clifford_quotient (n : ℕ) (hn : 3 ≤ n) :
    ∃ ψ : OCl n →* SplitOrthogonal n,
      Function.Surjective ψ ∧
      ∀ U : OCl n, ψ U = 1 ↔
        orthogonalCliffordInclusion n U ∈ orthogonalPauliSet n := by sorry

end ConstGapCircuits.Supplement
