-- Prove2me | Theorems.Thm_DepthOptQC_Synth_lemma_4
-- name    : DepthOptQC.Synth.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:18:47.714135+00:00
-- url     : https://prove2.me/theorems/7918805f-aac8-49e1-b971-f107e334d217
-- title:
--   Lemma 4 — value thresholding with wide gates: depth $O(k)$, Fan-Out and Toffoli width $b_{\max}$
-- statement:
--   There is a universal constant $C$ such that for every integer $k\ge1$ there is a constant $C_k$ with the following property. For every integer $m\ge1$ let
--   $$
--   b_{\max} := \Big\lceil m^{\,2^{k-1}/(2^k-1)}\Big\rceil .
--   $$
--   For every $M\in\{0,1,\dots,2^m\}$, the value thresholding function $f^m_M$ is computed exactly and cleanly by a reversible layered circuit containing only $X$ gates, Fan-Out gates with at most $b_{\max}$ targets and generalized Toffoli gates with at most $b_{\max}$ controls, of depth at most $Ck$, size at most $C_k m$, and with at most
--   $$
--   C_k\, m^{\,1+1/(2^k-1)}
--   $$
--   ancillas.
--
--   This is the paper's Lemma 4 ("$O(k)$ depth, $O_k(m)$ size, and $O_k(m^{1+1/(2^k-1)})$ space"). With $k$ fixed it gives constant-depth comparisons, which make the wide-gate synthesizer of Corollary 1 constant depth.
--
--   **Formalization Note** The wire layout and the notion of clean computation are as in Lemma 3. A CNOT is the Fan-Out gate with one target.
--
--   Differences from the source:
--   - reading: O(k) depth, O_k(m) size, O_k(m^{1+1/(2^k−1)}) space → ∃ C ∀ k ≥ 1 ∃ C_k ∀ m ≥ 1 ∀ M: depth ≤ C·k, size ≤ C_k·m, ancillas ≤ C_k·m^{1+1/(2^k−1)}; reason: readings R1, R8: O(k) has a universal constant, O_k a constant depending on k only; b_max is exact
--   - encoding: circuit depth → number of layers of a LayeredCircuit, a layer being gates with pairwise disjoint wire sets; reason: reading R3: the paper's depth (layers of gates on disjoint qubits)
--   - encoding: |x⟩|b⟩|0^a⟩ with x_{m−1} the most significant bit → x_j on wire j, b on wire m, ancillas on the last a wires; reason: readings R9 and Eq. (33): a fixed assignment of bits to wires
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Lemma 4, p.18

import Definitions.Def_DepthOptQC_Synth_CleanlyComputes
import Definitions.Def_DepthOptQC_Synth_thresh
import Definitions.Def_DepthOptQC_Synth_wideThresholdGateSet
import Definitions.Def_DepthOptQC_Synth_bmax

namespace DepthOptQC.Synth

open QAlgorithms

/-- **Lemma 4 (Value Thresholding with Wide Gates)** (Vasconcelos, *Depth-Optimal Quantum
Compilation*, arXiv:2609.34659, Lemma 4, p.18). For every integer `m ≥ 1` and constant integer
`k ≥ 1`, let `b_max := ⌈m^{2^{k−1}/(2^k−1)}⌉` (44). For every `M ∈ {0, 1, …, 2^m}`, `f^m_M` can be
computed exactly and cleanly by a reversible circuit containing only X gates, Fan-Out gates with at
most `b_max` targets and Toffoli gates with at most `b_max` controls, using `O(k)` depth, `O_k(m)`
size and `O_k(m^{1+1/(2^k−1)})` space.

**Formalization Note.** `O(k)` is `C · k` with `C` universal, chosen before `k`; `O_k` is a constant
`C_k` chosen after `k` and before `m`, `M` (readings R1, R8). `b_max` is exact. Depth counts disjoint
layers (R3); space is the number `a` of ancillas besides input and output wires; the wire layout is
that of `CleanlyComputes` (R9). -/
theorem lemma_4 :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → ∃ Ck : ℝ, ∀ m : ℕ, 1 ≤ m → ∀ M : ℕ, M ≤ 2 ^ m →
      ∃ a : ℕ, ∃ c : LayeredCircuit (wideThresholdGateSet (bmax m k)) (m + 1 + a),
        CleanlyComputes c (thresh m M) ∧
        (c.depth : ℝ) ≤ C * k ∧ (c.size : ℝ) ≤ Ck * m ∧
        (a : ℝ) ≤ Ck * (m : ℝ) ^ (1 + 1 / ((2 : ℝ) ^ k - 1)) := by sorry

end DepthOptQC.Synth
