-- Prove2me | Theorems.Thm_ConstGapCircuits_clifford_chain_gap
-- name    : ConstGapCircuits.clifford_chain_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:53:03.742491+00:00
-- url     : https://prove2.me/theorems/58f7c375-9945-4fbb-9ed6-008daa671742
-- title:
--   Theorem 2.7 — chain and all-pairs Clifford averages
-- statement:
--   Let $n\ge2$ and let $\rho$ be any continuous finite-dimensional unitary representation of $\mathrm{Cl}(n)$. Write $\Pi_{ij}=\Pi(\rho|\mathrm{LCl}(\{i,j\},n))$ and $\Pi_{\mathrm{Cl}}=\Pi(\rho|\mathrm{Cl}(n))$. Then both bounds hold:
--   $$\left\|\frac1{n-1}\sum_{j=0}^{n-2}\Pi_{j,j+1}-\Pi_{\mathrm{Cl}}\right\|_{\mathrm{op}}\le1-\frac1{5(n-1)},$$
--   $$\left\|\frac2{n(n-1)}\sum_{0\le i<j<n}\Pi_{ij}-\Pi_{\mathrm{Cl}}\right\|_{\mathrm{op}}\le1-\frac1{5(n-1)}.$$
--
--   This supplies the quantitative Clifford-chain input and its all-pairs counterpart.
--
--   Differences from the source:
--   - reading: finite-dimensional unitary representations in the compact-group setting → continuous homomorphisms into U(d), for every natural dimension d; reason: continuity is the standing compact-group representation convention and ensures the moment integrals are genuine expectations
--   - encoding: matrices on n qubits, local subgroup averages, and operator norms → computational basis Fin n → Fin 2, zero-based qubit indices, closed subgroup Haar measures and Euclidean operator norms; reason: reindexing and bundling preserve every matrix, central phase, measure and norm
--   - encoding: the n-qubit chain with denominators n−1 → n≥2; reason: this is the full range on which the printed averages are defined
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 10, Theorem 2.7, (2.8)–(2.9)

import Definitions.Def_ConstGapCircuits_walks

namespace ConstGapCircuits

theorem clifford_chain_gap (n : ℕ) (hn : 2 ≤ n) (ρ : UnitaryRep (Cl n)) :
    opNorm (chainProjector n localClifford ρ - invariantProjector ρ) ≤
      1 - 1 / (5 * ((n - 1 : ℕ) : ℝ)) ∧
    opNorm (allPairsProjector n localClifford ρ - invariantProjector ρ) ≤
      1 - 1 / (5 * ((n - 1 : ℕ) : ℝ)) := by sorry

end ConstGapCircuits
