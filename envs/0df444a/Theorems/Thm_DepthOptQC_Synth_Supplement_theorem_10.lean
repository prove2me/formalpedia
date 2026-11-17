-- Prove2me | Theorems.Thm_DepthOptQC_Synth_Supplement_theorem_10
-- name    : DepthOptQC.Synth.Supplement.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:48:36.875899+00:00
-- url     : https://prove2.me/theorems/e8509ffc-2fe4-41eb-b0be-fdfc6101aae9
-- title:
--   Theorem 10 — clean fixed-gate simulation of QAC circuits
-- statement:
--   There are uniform constants $K>0$ and $k\in\mathbb N$ such that every size-$s\ge1$, depth-$d$ QAC circuit $C$ on $w$ qubits and every $\varepsilon\in(0,1)$ admit a circuit $\widetilde C$ over $H$, $T$ and generalized Toffoli gates, with $A$ fresh clean ancillas, for which one phase $\varphi$ satisfies
--   $$
--   \|\widetilde C(|\psi\rangle|0^A\rangle)-e^{i\varphi}(C|\psi\rangle)|0^A\rangle\|_2
--   \le\varepsilon\|\psi\|_2
--   $$
--   for every $w$-qubit vector $|\psi\rangle$. Moreover, its depth is at most $Kd$, while its size and $A$ are at most $K(s+1/\varepsilon)^k$.
--
--   This is a full-unitary clean compiler, stronger than merely preserving a decision probability.
--
--   Differences from the source:
--   - reading: $O(d)$ and $\operatorname{poly}(s,1/\varepsilon)$ → uniform witnesses $K>0$ and $k\in\mathbb N$ chosen before the circuit and precision; reason: makes the printed asymptotics explicit without choosing a special exponent
--   - encoding: the paper writes $|0^A\rangle|\psi\rangle$ → Lean stores the data wires before the appended zero ancillas; reason: a fixed wire relabelling changes neither depth, size nor Euclidean error
--   - encoding: the paper quantifies normalized inputs → Lean quantifies every vector with error $\varepsilon\|\psi\|_2$; reason: homogeneity of the two linear maps makes this exactly equivalent, including the zero vector
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Theorem 10, p.43 (PDF p.45), Eq. (203)

import Definitions.Def_DepthOptQC_Synth_Supplement_CircuitModel

set_option autoImplicit false

namespace DepthOptQC.Synth.Supplement

open QAlgorithms DepthOptQC.Synth

/-- **Theorem 10 (Fixed-Gate Simulation of QAC Circuits)** — Vasconcelos,
arXiv:2609.34659, p.43, Eq. (203). Every size-`s`, depth-`d` QAC circuit has a clean simulation
over `H`, `T` and generalized Toffoli gates, with constant-factor depth and polynomial gate and
clean-workspace costs.

**Formalization Note.** The witnesses `K,k` make both `O(d)` and `poly(s,1/ε)` uniform. The clean
error is on the complete output for every quantum input, with one phase selected before the input. -/
theorem theorem_10 :
    ∃ K : ℝ, 0 < K ∧ ∃ k : ℕ,
      ∀ (w s d : ℕ) (C : LayeredCircuit qacGateSet w),
        1 ≤ s → C.size = s → C.depth = d →
        ∀ ε : ℝ, 0 < ε → ε < 1 →
          ∃ A : ℕ, ∃ Ctilde : LayeredCircuit quacGateSet (w + A),
            CleanlyApproximatesCircuit Ctilde.unitary C.unitary ε ∧
            (Ctilde.depth : ℝ) ≤ K * d ∧
            (Ctilde.size : ℝ) ≤ K * ((s : ℝ) + 1 / ε) ^ k ∧
            (A : ℝ) ≤ K * ((s : ℝ) + 1 / ε) ^ k := by sorry

end DepthOptQC.Synth.Supplement
