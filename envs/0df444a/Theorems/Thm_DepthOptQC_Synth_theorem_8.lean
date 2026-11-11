-- Prove2me | Theorems.Thm_DepthOptQC_Synth_theorem_8
-- name    : DepthOptQC.Synth.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:18:18.407531+00:00
-- url     : https://prove2.me/theorems/20aa25f5-13b0-4d43-890c-42cefbe91214
-- title:
--   Theorem 8 — $R_z(\theta)$ synthesis over $G_{\mathrm{QNC}}$ with phase $\pi$: depth $O(\log\log(1/\varepsilon))$, size and ancillas $O(\log(1/\varepsilon))$
-- statement:
--   There is a constant $C$ such that for every $\theta\in\mathbb R$ and $\varepsilon\in(0,1)$ there exist $a\in\mathbb N$ and a fully unitary layered circuit $C_{\theta,\varepsilon}$ over
--   $$
--   G_{\mathrm{QNC}}=\{H,X,Z,S,S^\dagger,\mathrm{CNOT},CZ,\mathrm{Toffoli}\}
--   $$
--   on one system qubit and $a$ ancillas initialized to $|0^a\rangle$ such that the single input-independent phase $\varphi=\pi$ satisfies
--   $$
--   \big\|C_{\theta,\varepsilon}(|0^a\rangle\otimes I)+|0^a\rangle\otimes R_z(\theta)\big\|_{\mathrm{op}}\le\varepsilon ,
--   $$
--   and
--   $$
--   \operatorname{depth}(C_{\theta,\varepsilon})\le C\,(1+\log_2 L(\varepsilon)),\qquad \operatorname{size}(C_{\theta,\varepsilon})\le C\,L(\varepsilon),\qquad a\le C\,L(\varepsilon),
--   $$
--   where $L(\varepsilon)=\log_2(2/\varepsilon)$.
--
--   This is the paper's Theorem 8: depth $O(\log\log(1/\varepsilon))$, gate count $O(\log(1/\varepsilon))$ and space $O(\log(1/\varepsilon))$, with the constants independent of $\theta$.
--
--   **Formalization Note** The system qubit is wire $0$ and the ancillas follow it. The approximation is stated per input vector, $\|C(\psi\otimes0^a)+R_z(\theta)\psi\otimes0^a\|\le\varepsilon\|\psi\|$, which is the operator-norm bound.
--
--   Differences from the source:
--   - reading: depth O(log log(1/ε)), gate count O(log(1/ε)), space O(log(1/ε)) → one constant C chosen before θ and ε with depth ≤ C(1 + log₂ L(ε)), size ≤ C·L(ε), ancillas ≤ C·L(ε), L(ε) = log₂(2/ε); reason: reading R1: the literal bound C·log(1/ε) on all of ε ∈ (0,1) is false, since log(1/ε) → 0 as ε → 1 while a circuit approximating, e.g., X to error 0.99 needs at least one gate; L(ε) = log₂(2/ε) = 1 + log₂(1/ε) is the same asymptotics as ε → 0, so the statement is not weaker
--   - encoding: circuit depth → number of layers of a LayeredCircuit, a layer being gates with pairwise disjoint wire sets; reason: reading R3: the paper's depth (layers of gates on disjoint qubits)
--   - encoding: ancillas first, |0^a⟩ ⊗ I → system qubit on wire 0, ancillas on wires 1, …, a; reason: reading R4: a fixed relabelling of wires changes no depth, size or norm
--   - encoding: ‖C(|0^a⟩ ⊗ I) + |0^a⟩ ⊗ R_z(θ)‖_op ≤ ε → ∀ ψ, ‖C(ψ ⊗ 0^a) − (−1)(R_z(θ)ψ ⊗ 0^a)‖ ≤ ε‖ψ‖ (CleanlyApproxWith with phase factor −1); reason: reading R6: the operator norm bound and the per-vector bound are equivalent by homogeneity; the whole output, ancillas included, is compared
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Theorem 8, p.23

import Definitions.Def_DepthOptQC_Synth_LayeredCircuit
import Definitions.Def_DepthOptQC_Synth_gqncGateSet
import Definitions.Def_DepthOptQC_Synth_CleanlyApprox
import Definitions.Def_DepthOptQC_Synth_rzQ
import Definitions.Def_DepthOptQC_Synth_precLog

namespace DepthOptQC.Synth

open QAlgorithms

/-- **Theorem 8 (Approximate `R_z(θ)` Synthesis with Bounded-Width Gates)** (Vasconcelos,
*Depth-Optimal Quantum Compilation*, arXiv:2609.34659, Theorem 8, p.23). Fix `θ ∈ ℝ` and
`ε ∈ (0, 1)`. There is an angle-dependent, fully unitary circuit `C_{θ,ε}` over
`G_QNC = {H, X, Z, S, S†, CNOT, CZ, Toffoli}` (79), using `a = O(log(1/ε))` ancillas initialized to
`|0^a⟩`, such that the single input-independent phase `φ = π` satisfies
`‖C_{θ,ε}(|0^a⟩ ⊗ I) + |0^a⟩ ⊗ R_z(θ)‖_op ≤ ε` (80); it has depth `O(log log(1/ε))`, gate count
`O(log(1/ε))` and space `O(log(1/ε))`.

**Formalization Note.** `O(·)` is one constant `C` chosen before `θ` and `ε`, with
`log(1/ε) ↦ L(ε) = log₂(2/ε)` and `log log(1/ε) ↦ 1 + log₂ L(ε)` (reading R1, `precLog`). The phase
is fixed: `e^{iπ} = −1`. The system qubit is wire `0`, ancillas follow (R4); the error is measured on
the whole output (R6); depth counts disjoint layers (R3). -/
theorem theorem_8 :
    ∃ C : ℝ, ∀ θ ε : ℝ, 0 < ε → ε < 1 →
      ∃ a : ℕ, ∃ c : LayeredCircuit gqncGateSet (1 + a),
        CleanlyApproxWith c.unitary (rzQ θ) (-1) ε ∧
        (c.depth : ℝ) ≤ C * (1 + Real.logb 2 (precLog ε)) ∧
        (c.size : ℝ) ≤ C * precLog ε ∧ (a : ℝ) ≤ C * precLog ε := by sorry

end DepthOptQC.Synth
