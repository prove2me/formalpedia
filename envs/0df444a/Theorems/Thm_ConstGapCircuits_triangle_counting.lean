-- Prove2me | Theorems.Thm_ConstGapCircuits_triangle_counting
-- name    : ConstGapCircuits.triangle_counting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:57:00.595056+00:00
-- url     : https://prove2.me/theorems/def76489-8cd1-43df-a157-e898bfa37b44
-- title:
--   Lemma 3.4 — Pauli triangle-counting estimate
-- statement:
--   Let $n\ge1$, let $\Theta\le\mathbb R/2\pi\mathbb Z$ be any closed additive subgroup, and let $\rho$ be any continuous finite-dimensional unitary representation of $G_\Theta$. Using the triangle gap $\Delta_\Theta$ from (3.2)–(3.3),
--   $$\left\|\frac1{4^n-1}\sum_{P\in\mathcal P_n}\Pi(\rho|\Theta,P)-\Pi(\rho|G_\Theta)\right\|_{\mathrm{op}}
--   \le1-\frac{1+4^{n-1}(\Delta_\Theta-1)}{4^n-1}.$$
--
--   This is the general closed-angle statement, including both finite angle groups and the circle. In the discrete case, the projectors and the local triangle Hamiltonian average the centre, consistently with the proof of Theorem 3.12.
--
--   Differences from the source:
--   - reading: finite-dimensional unitary representations in the compact-group setting → continuous homomorphisms into U(d), for every natural dimension d; reason: continuity is the standing compact-group representation convention and ensures the moment integrals are genuine expectations
--   - encoding: matrices on n qubits, local subgroup averages, and operator norms → computational basis Fin n → Fin 2, zero-based qubit indices, closed subgroup Haar measures and Euclidean operator norms; reason: reindexing and bundling preserve every matrix, central phase, measure and norm
--   - reading: (3.1),(3.3),(3.5) omit a central average but the proof of 3.12 explicitly includes it → discrete-angle projectors average the full centre in both the triangle gap and the Pauli average; reason: this is the paper’s stated convention at its use in 3.12; without it centre-sensitive characters for n≥4 invalidate (3.5)
--   - reading: L_Θ≤LU(2) alongside an explicit inclusion in SU(2) → the three Pauli axes on one qubit inside SU(2^n); reason: the same sentence and the proof of 3.10 identify the one-qubit group
--   - encoding: the section starts with n≥1 → an explicit n≥1 binder; reason: excludes the empty nonidentity Pauli index set and the zero denominator
-- source:
--   Baer, Haah, Random unitary circuits with constant spectral gap, STOC 2027 submission #15 (preprint), p. 18, Lemma 3.4, (3.5)

import Definitions.Def_ConstGapCircuits_triangleGap

namespace ConstGapCircuits

theorem triangle_counting (n : ℕ) (hn : 1 ≤ n) (Θ : Angles)
    (ρ : UnitaryRep (ThetaGlobal n Θ)) :
    opNorm (thetaPauliAverage n Θ ρ - invariantProjector ρ) ≤
      1 - (1 + (4 : ℝ)^(n - 1) * (thetaGap n Θ - 1)) / ((4 : ℝ)^n - 1) := by sorry

end ConstGapCircuits
