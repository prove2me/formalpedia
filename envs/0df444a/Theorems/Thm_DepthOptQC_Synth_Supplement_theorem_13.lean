-- Prove2me | Theorems.Thm_DepthOptQC_Synth_Supplement_theorem_13
-- name    : DepthOptQC.Synth.Supplement.theorem_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:51:20.023795+00:00
-- url     : https://prove2.me/theorems/3126fa6c-39c4-4e68-86ed-6c9e382e8bdd
-- title:
--   Theorem 13 — constant-depth QRAC approximation of encoded generalized Toffoli
-- statement:
--   There are uniform constants $K>0$ and $k\in\mathbb N$ such that, for every $r\ge1$ and $\eta\in(0,1/2)$, a QRAC circuit $\widetilde O$ of depth at most $K$ acts on the $2r$ Pauli-label qubits and $A$ fresh clean ancillas, with size and $A$ at most $K(r+1/\eta)^k$, and satisfies
--   $$
--   \sup_{\|\phi\|_2=1}
--   \|\widetilde O(|\phi\rangle|0^A\rangle)-(O_{\mathrm{Toffoli}_r}|\phi\rangle)|0^A\rangle\|_2
--   \le\eta.
--   $$
--   Here $\mathrm{Toffoli}_r$ acts on $r$ physical qubits with $r-1$ controls, and $\mathrm{Toffoli}_1=X$.
--
--   The theorem approximates the real Pauli-transfer action, not the physical Toffoli matrix.
--
--   Differences from the source:
--   - reading: constant depth and $\operatorname{poly}(r,1/\eta)$ → uniform witnesses $K,k$ chosen before $r,\eta$; reason: explicit asymptotic quantifiers
--   - encoding: adjacent label pairs $(a_j,b_j)$ → all $a$ labels followed by all $b$ labels; reason: a fixed permutation of the same $2r$ qubits
--   - encoding: a supremum over the unit sphere → a bound for every unit vector; reason: these are equivalent, and the universal form avoids introducing a totalized real supremum
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Theorem 13, p.63 (PDF p.65), Eq. (306)

import Definitions.Def_DepthOptQC_Synth_Supplement_pauliTransfer

set_option autoImplicit false

namespace DepthOptQC.Synth.Supplement

open QAlgorithms DepthOptQC.Synth

/-- **Theorem 13 (Encoded Generalized Toffoli)** — Vasconcelos, arXiv:2609.34659, p.63,
Eq. (306). The Pauli-transfer action of the `r`-qubit generalized Toffoli has a constant-depth,
polynomial-size clean QRAC approximation, including `r=1`, where the physical gate is `X`.

**Formalization Note.** The input has `2r` Pauli-label qubits; this is not an approximation of the
physical `r`-qubit Toffoli matrix. No global phase is allowed in the displayed clean-input bound. -/
theorem theorem_13 :
    ∃ K : ℝ, 0 < K ∧ ∃ k : ℕ,
      ∀ r : ℕ, (hr : 0 < r) → ∀ η : ℝ, 0 < η → η < 1 / 2 →
        ∃ A : ℕ, ∃ Otilde : LayeredCircuit qracGateSet ((r + r) + A),
          (Otilde.depth : ℝ) ≤ K ∧
          (Otilde.size : ℝ) ≤ K * ((r : ℝ) + 1 / η) ^ k ∧
          (A : ℝ) ≤ K * ((r : ℝ) + 1 / η) ^ k ∧
          ∀ φ : EuclideanSpace ℂ (Qubits (r + r)), ‖φ‖ = 1 →
            ‖act Otilde.unitary (zeroAncillaVec φ A) -
              zeroAncillaVec (act (generalizedToffoliTransfer r hr) φ) A‖ ≤ η := by sorry

end DepthOptQC.Synth.Supplement
