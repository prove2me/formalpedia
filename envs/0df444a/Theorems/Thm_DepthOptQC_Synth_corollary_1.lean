-- Prove2me | Theorems.Thm_DepthOptQC_Synth_corollary_1
-- name    : DepthOptQC.Synth.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:18:20.859193+00:00
-- url     : https://prove2.me/theorems/09cd3323-34cb-4cb2-ae34-81529e0b9215
-- title:
--   Corollary 1 — constant-depth $R_z(\theta)$ synthesis over $G_{\mathrm{QACf}}$ with phase $\pi$
-- statement:
--   There is a constant $C_0$ such that for every $\gamma\in(0,1)$ there is a constant $C_\gamma$ with the following property. For every $\theta\in\mathbb R$ and $\varepsilon\in(0,1)$, with $L(\varepsilon)=\log_2(2/\varepsilon)$, there exist $a,w_F,w_T\in\mathbb N$ with
--   $$
--   w_T\le C_0\,L(\varepsilon),\qquad w_F\le C_\gamma\,L(\varepsilon)^{1/2+\gamma},
--   $$
--   and a fully unitary layered circuit $C^{(\gamma)}_{\theta,\varepsilon}$ over the wide gate set $G_{\mathrm{QACf}}=\{H,X,Z,S,S^\dagger,\mathrm{CNOT},CZ,\text{Fan-Out},\text{GToffoli}\}$ (Fan-Out with at most $w_F$ targets, generalized Toffoli with at most $w_T$ controls) on one system qubit and $a$ ancillas initialized to $|0^a\rangle$, such that the fixed phase $\varphi=\pi$ works for all inputs,
--   $$
--   \big\|C^{(\gamma)}_{\theta,\varepsilon}(|0^a\rangle\otimes I)+|0^a\rangle\otimes R_z(\theta)\big\|_{\mathrm{op}}\le\varepsilon ,
--   $$
--   and
--   $$
--   \operatorname{depth}\le C_\gamma,\qquad\operatorname{size}\le C_\gamma\,L(\varepsilon),\qquad a\le C_\gamma\,L(\varepsilon)^{1+\gamma}.
--   $$
--
--   This is the paper's Corollary 1: depth $O_\gamma(1)$, gate count $O_\gamma(\log(1/\varepsilon))$ and space $O_\gamma(\log^{1+\gamma}(1/\varepsilon))$, with Fan-Out width $O_\gamma(\log^{1/2+\gamma}(1/\varepsilon))$ and Toffoli width $O(\log(1/\varepsilon))$.
--
--   **Formalization Note** $C_0$ is chosen before $\gamma$ and $C_\gamma$ depends on $\gamma$ only. Widths and their bounds are chosen with the circuit. Conventions on wires, depth and the approximation are as in Theorem 8.
--
--   Differences from the source:
--   - reading: Toffoli width O(log(1/ε)); Fan-Out width O_γ(log^{1/2+γ}(1/ε)); depth O_γ(1); gate count O_γ(log(1/ε)); space O_γ(log^{1+γ}(1/ε)) → ∃ C₀ ∀ γ ∈ (0,1) ∃ C_γ ∀ θ ε: wT ≤ C₀·L(ε), wF ≤ C_γ·L(ε)^{1/2+γ}, depth ≤ C_γ, size ≤ C_γ·L(ε), ancillas ≤ C_γ·L(ε)^{1+γ}; reason: reading R1: the literal bound C·log(1/ε) on all of ε ∈ (0,1) is false, since log(1/ε) → 0 as ε → 1 while a circuit approximating, e.g., X to error 0.99 needs at least one gate; L(ε) = log₂(2/ε) = 1 + log₂(1/ε) is the same asymptotics as ε → 0, so the statement is not weaker
--   - encoding: Fan-Out of size w, GToffoli of size w → Fan-Out with at most wF targets, generalized Toffoli with at most wT controls; reason: reading R5: width counts targets (resp. controls), as in Lemma 4's wording; a ±1 shift is absorbed by the constants
--   - encoding: circuit depth → number of layers of a LayeredCircuit, a layer being gates with pairwise disjoint wire sets; reason: reading R3: the paper's depth (layers of gates on disjoint qubits)
--   - encoding: ancillas first, |0^a⟩ ⊗ I → system qubit on wire 0, ancillas on wires 1, …, a; reason: reading R4: a fixed relabelling of wires changes no depth, size or norm
--   - encoding: ‖C(|0^a⟩ ⊗ I) + |0^a⟩ ⊗ R_z(θ)‖_op ≤ ε → ∀ ψ, ‖C(ψ ⊗ 0^a) − (−1)(R_z(θ)ψ ⊗ 0^a)‖ ≤ ε‖ψ‖ (CleanlyApproxWith with phase factor −1); reason: reading R6: the operator norm bound and the per-vector bound are equivalent by homogeneity; the whole output, ancillas included, is compared
--   - encoding: R_z(θ)(θ) in (102) → R_z(θ); reason: the repeated argument is a typesetting slip; the operator is R_z(θ)
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Corollary 1, p.26

import Definitions.Def_DepthOptQC_Synth_LayeredCircuit
import Definitions.Def_DepthOptQC_Synth_gqacfGateSet
import Definitions.Def_DepthOptQC_Synth_CleanlyApprox
import Definitions.Def_DepthOptQC_Synth_rzQ
import Definitions.Def_DepthOptQC_Synth_precLog

namespace DepthOptQC.Synth

open QAlgorithms

/-- **Corollary 1 (Constant-Depth Approximate `R_z(θ)` Synthesis with Wide Gates)** (Vasconcelos,
*Depth-Optimal Quantum Compilation*, arXiv:2609.34659, Corollary 1, p.26). Fix `γ ∈ (0, 1)`,
`θ ∈ ℝ`, `ε ∈ (0, 1)`. Over `G_QACf = {H, X, Z, S, S†, CNOT, CZ, Fan-Out, GToffoli}` (101), with
Fan-Out of up to `O_γ(log^{1/2+γ}(1/ε))` targets and GToffoli of up to `O(log(1/ε))` controls,
there is an angle-dependent, fully unitary circuit using `a = O_γ(log^{1+γ}(1/ε))` ancillas
initialized to `|0^a⟩` such that the fixed phase `φ = π` works for all inputs (102), with depth
`O_γ(1)`, gate count `O_γ(log(1/ε))` and space `O_γ(log^{1+γ}(1/ε))`.

**Formalization Note.** The universal constant `C₀` (Toffoli width) comes before `γ`; `C_γ` comes after
`γ` only (readings R1, R2); `log(1/ε) ↦ L(ε) = log₂(2/ε)`. Widths are Fan-Out targets and Toffoli
controls (R5); the widths `wF`, `wT` are chosen with the circuit and bounded. Phase `e^{iπ} = −1`;
system wire `0` (R4); whole-output error (R6); depth counts disjoint layers (R3). -/
theorem corollary_1 :
    ∃ C₀ : ℝ, ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ Cγ : ℝ, ∀ θ ε : ℝ, 0 < ε → ε < 1 →
      ∃ a wF wT : ℕ, ∃ c : LayeredCircuit (gqacfGateSet wF wT) (1 + a),
        (wT : ℝ) ≤ C₀ * precLog ε ∧ (wF : ℝ) ≤ Cγ * precLog ε ^ (1 / 2 + γ) ∧
        CleanlyApproxWith c.unitary (rzQ θ) (-1) ε ∧
        (c.depth : ℝ) ≤ Cγ ∧ (c.size : ℝ) ≤ Cγ * precLog ε ∧
        (a : ℝ) ≤ Cγ * precLog ε ^ (1 + γ) := by sorry

end DepthOptQC.Synth
