-- Prove2me | Theorems.Thm_DepthOptQC_Synth_lemma_6
-- name    : DepthOptQC.Synth.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:16:49.799959+00:00
-- url     : https://prove2.me/theorems/0fc38b8e-2f36-4116-9b3a-2ef8a9bb1d6c
-- title:
--   Lemma 6 — reduction from single-qubit synthesis to $R_z$ synthesis: depth $3d(\varepsilon/3)+2$, size $3s(\varepsilon/3)+2$, $a(\varepsilon/3)$ ancillas
-- statement:
--   Let $\mathcal G$ be a gate set of unitary gates containing $H$. Let $a,d,s$ assign natural numbers to precisions, and suppose that for every $\theta\in\mathbb R$ and $\eta\in(0,1)$ there is a layered circuit $C^z_{\theta,\eta}$ over $\mathcal G$ on one system qubit and $a(\eta)$ clean ancillas, of depth at most $d(\eta)$ and gate count at most $s(\eta)$, and a phase $\varphi_{\theta,\eta}\in\mathbb R$ with
--   $$
--   \big\|C^z_{\theta,\eta}|0^{a(\eta)}\rangle|\psi\rangle-e^{i\varphi_{\theta,\eta}}|0^{a(\eta)}\rangle R_z(\theta)|\psi\rangle\big\|\le\eta
--   $$
--   for every state $|\psi\rangle$. Then for every single-qubit unitary $U$ and $\varepsilon\in(0,1)$ there is a layered circuit $C_{U,\varepsilon}$ over $\mathcal G$ using $a(\varepsilon/3)$ clean ancillas and a phase $\varphi\in\mathbb R$ such that for every state $|\psi\rangle$
--   $$
--   \big\|C_{U,\varepsilon}|0^{a(\varepsilon/3)}\rangle|\psi\rangle-e^{i\varphi}|0^{a(\varepsilon/3)}\rangle U|\psi\rangle\big\|\le\varepsilon ,
--   $$
--   and
--   $$
--   \operatorname{depth}(C_{U,\varepsilon})\le3d(\varepsilon/3)+2,\qquad\operatorname{size}(C_{U,\varepsilon})\le3s(\varepsilon/3)+2,\qquad\operatorname{space}(C_{U,\varepsilon})=a(\varepsilon/3)+1 .
--   $$
--
--   The three rotations of an Euler decomposition $U=e^{i\alpha}R_z(\beta)HR_z(\gamma)HR_z(\delta)$ share one workspace, and their errors add even though the workspace is only approximately restored after each. This turns the $R_z$ synthesizers of Theorem 8 and Corollary 1 into synthesizers for all of $U(2)$.
--
--   **Formalization Note** The circuit lives on $1+a(\varepsilon/3)$ wires, which is the space bound. The per-state bounds are stated as $\|\cdot\|\le\eta\|\psi\|$ for all vectors $\psi$, the same condition by homogeneity.
--
--   Differences from the source:
--   - generalization: a circuit with depth d(η) and gate count s(η) → a circuit with depth ≤ d(η) and size ≤ s(η); reason: reading R7: a weaker hypothesis, so a stronger lemma; circuits of exactly that depth and size are an instance
--   - encoding: a fully unitary circuit over G → the hypothesis that every gate of G is unitary (Gate.IsUnitary), circuits being measurement-free by the model; reason: reading R7: a fully unitary circuit is one without measurement whose gates are unitary
--   - encoding: for every state |ψ⟩ (unit vector), ‖…‖ ≤ η (106) and ‖…‖ ≤ ε (107) → for every vector ψ, ‖…‖ ≤ η‖ψ‖ and ‖…‖ ≤ ε‖ψ‖ (CleanlyApprox); reason: equivalent by homogeneity; the phase is chosen before ψ as in (106)–(107)
--   - encoding: space(C_{U,ε}) = a(ε/3) + 1 (110) → the circuit type LayeredCircuit G (1 + a(ε/3)); reason: the space counts the system qubit and the a(ε/3) ancillas, which is the wire count
--   - encoding: a(η), d(η), s(η) defined for η ∈ (0,1) → functions ℝ → ℕ; reason: only their values on (0,1) enter the hypothesis and the conclusion
--   - encoding: circuit depth → number of layers of a LayeredCircuit, a layer being gates with pairwise disjoint wire sets; reason: reading R3: the paper's depth (layers of gates on disjoint qubits)
--   - encoding: ancillas first, |0^a⟩ ⊗ I → system qubit on wire 0, ancillas on wires 1, …, a; reason: reading R4: a fixed relabelling of wires changes no depth, size or norm
--   - encoding: R_z(θ)(θ) in (106) → R_z(θ); reason: the repeated argument is a typesetting slip; the operator is R_z(θ)
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Lemma 6, pp.26–27

import Definitions.Def_DepthOptQC_Synth_LayeredCircuit
import Definitions.Def_DepthOptQC_Synth_CleanlyApprox
import Definitions.Def_DepthOptQC_Synth_rzQ

namespace DepthOptQC.Synth

open QAlgorithms

/-- **Lemma 6 (Reduction from Single-Qubit Synthesis to `R_z(θ)` Synthesis)** (Vasconcelos,
*Depth-Optimal Quantum Compilation*, arXiv:2609.34659, Lemma 6, pp.26–27). Let `G` be a gate set
containing `H`. Suppose that for every `θ ∈ ℝ` and `η ∈ (0, 1)` there is a fully unitary circuit
`C^z_{θ,η}` over `G` using `a(η)` clean ancillas, with depth `d(η)` and gate count `s(η)`, and a phase
`φ_{θ,η}` with `‖C^z_{θ,η}|0^{a(η)}⟩|ψ⟩ − e^{iφ_{θ,η}}|0^{a(η)}⟩R_z(θ)|ψ⟩‖ ≤ η` (106) for every state.
Then for every single-qubit unitary `U` and `ε ∈ (0, 1)` there is a fully unitary circuit `C_{U,ε}`
over `G` using `a(ε/3)` clean ancillas and a phase `φ` with (107), and
`depth ≤ 3d(ε/3) + 2` (108), `size ≤ 3s(ε/3) + 2` (109), `space = a(ε/3) + 1` (110).

**Formalization Note.** "Fully unitary" is the hypothesis that every gate of `G` is unitary.
"With depth `d(η)` and gate count `s(η)`" is read as "at most" (reading R7). The ancilla count is
exactly `a(η)`, a function of `η` alone; the space `a(ε/3) + 1` of (110) is the wire count `1 + a(ε/3)`
of the circuit type. `a, d, s` are functions on `ℝ`, used only on `(0, 1)`. -/
theorem lemma_6 (G : Set Gate) (hH : Gate.ofMatrix1 hadamard ∈ G) (hG : ∀ g ∈ G, g.IsUnitary)
    (a d s : ℝ → ℕ)
    (hsyn : ∀ θ η : ℝ, 0 < η → η < 1 →
      ∃ c : LayeredCircuit G (1 + a η),
        c.depth ≤ d η ∧ c.size ≤ s η ∧ CleanlyApprox c.unitary (rzQ θ) η) :
    ∀ U ∈ Matrix.unitaryGroup (Qubits 1) ℂ, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ c : LayeredCircuit G (1 + a (ε / 3)),
        CleanlyApprox c.unitary U ε ∧
        c.depth ≤ 3 * d (ε / 3) + 2 ∧ c.size ≤ 3 * s (ε / 3) + 2 := by sorry

end DepthOptQC.Synth
