-- Prove2me | Theorems.Thm_ConstGapCircuits_unitary_chain_gap
-- name    : ConstGapCircuits.unitary_chain_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:54:13.341486+00:00
-- url     : https://prove2.me/theorems/fdb3ca66-80b5-4752-8ffe-61781fbf1787
-- title:
--   Theorem 4.1 — chain and all-pairs unitary averages
-- statement:
--   Let $n\ge2$ and let $\rho$ be a continuous finite-dimensional unitary representation of $\mathrm{SU}(2^n)$. Set $\Pi_{ij}=\Pi(\rho|\mathrm{LU}(\{i,j\},n))$ and $\Pi_G=\Pi(\rho|\mathrm{SU}(2^n))$. Then
--   $$\left\|\frac1{n-1}\sum_{j=0}^{n-2}\Pi_{j,j+1}-\Pi_G\right\|_{\mathrm{op}}\le1-\frac1{9\cdot2^{45}(n-1)},$$
--   $$\left\|\frac2{n(n-1)}\sum_{0\le i<j<n}\Pi_{ij}-\Pi_G\right\|_{\mathrm{op}}\le1-\frac1{9\cdot2^{45}(n-1)}.$$
--
--   On a nontrivial irreducible representation $\Pi_G=0$, so these give exactly the two printed inequalities. The formulation also allows arbitrary invariant summands.
--
--   Differences from the source:
--   - reading: finite-dimensional unitary representations in the compact-group setting → continuous homomorphisms into U(d), for every natural dimension d; reason: continuity is the standing compact-group representation convention and ensures the moment integrals are genuine expectations
--   - encoding: matrices on n qubits, local subgroup averages, and operator norms → computational basis Fin n → Fin 2, zero-based qubit indices, closed subgroup Haar measures and Euclidean operator norms; reason: reindexing and bundling preserve every matrix, central phase, measure and norm
--   - generalization: nontrivial irreducible representations, without a Haar-projector subtraction → all continuous finite-dimensional unitary representations, subtracting Π(ρ|G); reason: finite-dimensional unitary representations split orthogonally; the subtraction kills the trivial summands, and Π(ρ|G)=0 on each source nontrivial irrep
--   - encoding: averages with denominators n−1 and n(n−1) → n≥2; reason: this is the full defined range of both source formulas
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 26, Theorem 4.1, (4.2)–(4.3)

import Definitions.Def_ConstGapCircuits_walks

namespace ConstGapCircuits

theorem unitary_chain_gap (n : ℕ) (hn : 2 ≤ n) (ρ : UnitaryRep (SU n)) :
    opNorm (chainProjector n localUnitary ρ - invariantProjector ρ) ≤
      1 - 1 / (9 * (2 : ℝ)^45 * ((n - 1 : ℕ) : ℝ)) ∧
    opNorm (allPairsProjector n localUnitary ρ - invariantProjector ρ) ≤
      1 - 1 / (9 * (2 : ℝ)^45 * ((n - 1 : ℕ) : ℝ)) := by sorry

end ConstGapCircuits
