-- Prove2me | Theorems.Thm_DepthOptQC_Synth_single_qubit_synthesis
-- name    : DepthOptQC.Synth.single_qubit_synthesis
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:18:41.496616+00:00
-- url     : https://prove2.me/theorems/f3d9d5ea-7f84-4fe4-8423-8bc95e369488
-- title:
--   Theorem 1 — every single-qubit unitary: depth $O(\log\log(1/\varepsilon))$ over $\{H,T,\mathrm{CNOT}\}$, and constant depth over $H,S$ with Fan-Out and generalized Toffoli
-- statement:
--   Let $L(\varepsilon)=\log_2(2/\varepsilon)$.
--
--   1. **Bounded width.** There is a constant $C$ such that for every single-qubit unitary $U$ and every $\varepsilon\in(0,1)$ there are $a\in\mathbb N$ and a layered circuit over $\{H,T,\mathrm{CNOT}\}$ on one system qubit and $a$ ancillas that cleanly $\varepsilon$-approximates $U$, with
--   $$
--   \operatorname{depth}\le C\,(1+\log_2L(\varepsilon)),\qquad\operatorname{size}\le C\,L(\varepsilon),\qquad a\le C\,L(\varepsilon).
--   $$
--   2. **Wide gates, constant depth.** There is a constant $C_0$ such that for every $\gamma\in(0,1)$ there is a constant $C_\gamma$ such that for every single-qubit unitary $U$ and every $\varepsilon\in(0,1)$ there are $a,w_F,w_T\in\mathbb N$ with $w_T\le C_0\,L(\varepsilon)$ and $w_F\le C_\gamma\,L(\varepsilon)^{1/2+\gamma}$, and a layered circuit over $H$ and $S$ together with generalized Toffoli gates of at most $w_T$ controls and Fan-Out gates of at most $w_F$ targets, on one system qubit and $a$ ancillas, that cleanly $\varepsilon$-approximates $U$, with
--   $$
--   \operatorname{depth}\le C_\gamma,\qquad\operatorname{size}\le C_0\,L(\varepsilon),\qquad a\le C_\gamma\,L(\varepsilon)^{1+\gamma}.
--   $$
--
--   Here a circuit **cleanly $\varepsilon$-approximates** $U$ if its ancillas start in $|0^a\rangle$ and there is one phase $\varphi$, independent of the input, with $\|C(|\psi\rangle\otimes|0^a\rangle)-e^{i\varphi}U|\psi\rangle\otimes|0^a\rangle\|\le\varepsilon\|\psi\|$ for every $|\psi\rangle$; the whole output, ancillas included, is compared.
--
--   This is the paper's Theorem 1, with the formal resource shapes of Theorem 8, Corollary 1 and Lemma 6: depth $O(\log\log(1/\varepsilon))$ with $O(\log(1/\varepsilon))$ gates and ancillas over $\{H,T,\mathrm{CNOT}\}$, and constant depth with width-$O(\log(1/\varepsilon))$ Toffoli and width-$O_\gamma(\log^{1/2+\gamma}(1/\varepsilon))$ Fan-Out gates, using $O(\log(1/\varepsilon))$ gates and $O_\gamma(\log^{1+\gamma}(1/\varepsilon))$ ancillas. As on p.6, the gate count and the Toffoli width of the second clause have a constant independent of $\gamma$; Corollary 1 states only an $O_\gamma(\log(1/\varepsilon))$ gate count for its $R_z$ synthesizer, so this clause is stronger than what Corollary 1 and Lemma 6 give as printed. Together with the $\Omega(\log\log(1/\varepsilon))$ lower bound (Theorem 9) the first clause is depth-optimal.
--
--   **Formalization Note** Depth counts layers of gates on disjoint wires. The system qubit is wire $0$. Widths count Fan-Out targets and Toffoli controls.
--
--   Differences from the source:
--   - reading: O(log log(1/ε)) depth, O(log(1/ε)) gates and ancillas, width-O(log(1/ε)) Toffoli, width-O_γ(log^{1/2+γ}(1/ε)) Fan-Out, O_γ(log^{1+γ}(1/ε)) ancillas, constant depth → ∃ C ∀ U ε (clause a) and ∃ C₀ ∀ γ ∃ C_γ ∀ U ε (clause b, with the unsubscripted O's, Toffoli width and gate count, bounded by C₀ and the O_γ's by C_γ) with L(ε) = log₂(2/ε) in place of log(1/ε), 1 + log₂ L(ε) in place of log log(1/ε), depth ≤ C_γ for constant depth; reason: reading R1: the literal bound C·log(1/ε) on all of ε ∈ (0,1) is false, since log(1/ε) → 0 as ε → 1 while a circuit approximating, e.g., X to error 0.99 needs at least one gate; L(ε) = log₂(2/ε) = 1 + log₂(1/ε) is the same asymptotics as ε → 0, so the statement is not weaker
--   - encoding: circuit depth → number of layers of a LayeredCircuit, a layer being gates with pairwise disjoint wire sets; reason: reading R3: the paper's depth (layers of gates on disjoint qubits)
--   - encoding: ancillas first, |0^a⟩ ⊗ I → system qubit on wire 0, ancillas on wires 1, …, a; reason: reading R4: a fixed relabelling of wires changes no depth, size or norm
--   - encoding: Fan-Out of size w, GToffoli of size w → Fan-Out with at most wF targets, generalized Toffoli with at most wT controls; reason: reading R5: width counts targets (resp. controls), as in Lemma 4's wording; a ±1 shift is absorbed by the constants
--   - encoding: cleanly ε-approximates U (one input-independent phase, |0⟩ ancillas approximately restored) → CleanlyApprox: ∃ φ, ∀ ψ, ‖C(ψ ⊗ 0^a) − e^{iφ}(Uψ ⊗ 0^a)‖ ≤ ε‖ψ‖; reason: reading R6: the phase is chosen before ψ and the whole output is compared; equivalent to the operator-norm form of (80) and the per-state form of (107)
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Theorem 1, p.6, with Theorem 8, p.23, Corollary 1, p.26 and Lemma 6, pp.26–27 (p.5: "The formal upper bounds appear in Theorem 8 and Corollary 1, together with Lemma 6")

import Definitions.Def_DepthOptQC_Synth_LayeredCircuit
import Definitions.Def_DepthOptQC_Synth_wideGateSet
import Definitions.Def_DepthOptQC_Synth_CleanlyApprox
import Definitions.Def_DepthOptQC_Synth_precLog
import Definitions.Def_QAlgorithms_Defs_GradientMethods

namespace DepthOptQC.Synth

open QAlgorithms

/-- **Theorem 1 (Single-qubit synthesis)** (Vasconcelos, *Depth-Optimal Quantum Compilation*,
arXiv:2609.34659, Theorem 1, p.6, at the strength of Theorem 8, p.23, Corollary 1, p.26 and Lemma 6,
pp.26–27). For every single-qubit unitary `U` and precision `ε ∈ (0, 1)`, there is a
depth-`O(log log(1/ε))` circuit over `{H, T, CNOT}` that cleanly `ε`-approximates `U` using
`O(log(1/ε))` gates and clean ancillas. Moreover, for every fixed `γ ∈ (0, 1)`, there is a
constant-depth circuit over `H` and `S`, together with width-`O(log(1/ε))` generalized Toffoli gates
and width-`O_γ(log^{1/2+γ}(1/ε))` Fan-Out gates, that cleanly `ε`-approximates `U` using
`O(log(1/ε))` gates and `O_γ(log^{1+γ}(1/ε))` clean ancillas.

**Formalization Note.** `O(·)` is a constant chosen before `U` and `ε` (and `C₀` before `γ`; `C_γ`
after `γ` only), with `log(1/ε) ↦ L(ε) = log₂(2/ε)` and `log log(1/ε) ↦ 1 + log₂ L(ε)` (R1). The gate
count and the Toffoli width of the second clause carry no `γ` subscript on p.6, so their constant
is the universal `C₀` (Corollary 1 states the weaker `O_γ` gate count; the goal is Theorem 1's). Depth counts layers of gates on disjoint
wires (R3); system wire `0`, ancillas after it, all starting in `|0⟩` (R4); widths are Fan-Out
targets and Toffoli controls (R5); one global phase chosen before the input, error on the whole
output (R6). `htcxGateSet = {H, T, CNOT}` is the shared `QAlgorithms` gate set. -/
theorem single_qubit_synthesis :
    (∃ C : ℝ, ∀ U ∈ Matrix.unitaryGroup (Qubits 1) ℂ, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ a : ℕ, ∃ c : LayeredCircuit htcxGateSet (1 + a),
        CleanlyApprox c.unitary U ε ∧
        (c.depth : ℝ) ≤ C * (1 + Real.logb 2 (precLog ε)) ∧
        (c.size : ℝ) ≤ C * precLog ε ∧ (a : ℝ) ≤ C * precLog ε) ∧
    (∃ C₀ : ℝ, ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ Cγ : ℝ,
      ∀ U ∈ Matrix.unitaryGroup (Qubits 1) ℂ, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ a wF wT : ℕ, ∃ c : LayeredCircuit (wideGateSet wF wT) (1 + a),
        (wT : ℝ) ≤ C₀ * precLog ε ∧ (wF : ℝ) ≤ Cγ * precLog ε ^ (1 / 2 + γ) ∧
        CleanlyApprox c.unitary U ε ∧
        (c.depth : ℝ) ≤ Cγ ∧ (c.size : ℝ) ≤ C₀ * precLog ε ∧
        (a : ℝ) ≤ Cγ * precLog ε ^ (1 + γ)) := by sorry

end DepthOptQC.Synth
