-- Prove2me | Theorems.Thm_DepthOptQC_Synth_lemma_3
-- name    : DepthOptQC.Synth.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:18:29.136502+00:00
-- url     : https://prove2.me/theorems/a8208d13-77e0-48dc-aa93-797069a9f24a
-- title:
--   Lemma 3 — $\{X,\mathrm{CNOT},\mathrm{Toffoli}\}$ value thresholding in depth $O(\log m)$, size and space $O(m)$
-- statement:
--   There is a constant $C$ such that for every $m\ge1$ and every hardwired $M\in\{0,1,\dots,2^m\}$, the value thresholding function $f^m_M(\vec x)=\mathbf 1[\mathrm{int}(\vec x)<M]$ is computed exactly and cleanly,
--   $$
--   |\vec x\rangle|b\rangle|0^a\rangle\longmapsto|\vec x\rangle|b\oplus f^m_M(\vec x)\rangle|0^a\rangle ,
--   $$
--   by a reversible layered circuit over $\{X,\mathrm{CNOT},\mathrm{Toffoli}\}$ with $a$ ancillas, of depth at most $C(1+\log_2 m)$, size at most $Cm$, and $a\le Cm$.
--
--   This is the paper's Lemma 3 ("$O(\log m)$ depth, $O(m)$ size, and $O(m)$ space"). Three such comparisons label the interval of an address in the bounded-width synthesizer, and they account for its $O(\log\log(1/\varepsilon))$ depth.
--
--   **Formalization Note** Depth counts layers of gates on disjoint wires; space is the number of ancillas besides the $m$ input wires and the output wire. Bit $x_j$ is on wire $j$, the output bit on wire $m$.
--
--   Differences from the source:
--   - reading: O(log m) depth, O(m) size, O(m) space → one constant C chosen before m and M with depth ≤ C(1 + log₂ m), size ≤ C·m, ancillas ≤ C·m; reason: reading R1: the proof gives O(log(m + 1)) (p.18); the literal C·log₂ m is 0 at m = 1, where the nonconstant f¹₁(x) = ¬x needs at least one gate
--   - encoding: circuit depth → number of layers of a LayeredCircuit, a layer being gates with pairwise disjoint wire sets; reason: reading R3: the paper's depth (layers of gates on disjoint qubits)
--   - encoding: |x⟩|b⟩|0^a⟩ with x_{m−1} the most significant bit → x_j on wire j, b on wire m, ancillas on the last a wires; reason: readings R9 and Eq. (33): a fixed assignment of bits to wires; the statement quantifies over all M and is existential in the circuit
--   - encoding: Toffoli → gToffoli 2 (generalized Toffoli with two controls); reason: the ordinary three-qubit Toffoli gate
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Lemma 3, p.16

import Definitions.Def_DepthOptQC_Synth_CleanlyComputes
import Definitions.Def_DepthOptQC_Synth_thresh
import Definitions.Def_QuantumLTF_Membership_gatesRev

namespace DepthOptQC.Synth

open QAlgorithms

/-- **Lemma 3 ({X, CNOT, Toffoli} Value Thresholding)** (Vasconcelos, *Depth-Optimal Quantum
Compilation*, arXiv:2609.34659, Lemma 3, p.16). For every `m ≥ 1` and every hardwired
`M ∈ {0, 1, …, 2^m}`, the value thresholding function `f^m_M` can be computed exactly and cleanly by a
reversible circuit containing only the gates `{X, CNOT, Toffoli}` with `O(log m)` depth, `O(m)` size
and `O(m)` space.

**Formalization Note.** `O(·)` is one constant `C`, chosen before `m` and `M` (reading R1); `O(log m)`
is `C · (1 + log₂ m)`, which is what the proof gives (`O(log(m + 1))`, p.18) and is positive at
`m = 1`. The gate set `{X, CNOT, Toffoli}` is the published `QuantumLTF.Membership.gatesRev`
(Toffoli: controls on gate wires `0, 1`, target on wire `2`). Depth counts layers of gates on disjoint wires (R3); size is the gate count; space is the
number `a` of ancillas besides the `m` input wires and the output wire. The circuit acts on
`|x⟩|b⟩|0^a⟩` with `x` on wires `0, …, m−1` (bit `x_j` on wire `j`, R9), `b` on wire `m`. -/
theorem lemma_3 :
    ∃ C : ℝ, ∀ m : ℕ, 1 ≤ m → ∀ M : ℕ, M ≤ 2 ^ m →
      ∃ a : ℕ, ∃ c : LayeredCircuit QuantumLTF.Membership.gatesRev (m + 1 + a),
        CleanlyComputes c (thresh m M) ∧
        (c.depth : ℝ) ≤ C * (1 + Real.logb 2 m) ∧ (c.size : ℝ) ≤ C * m ∧ (a : ℝ) ≤ C * m := by sorry

end DepthOptQC.Synth
