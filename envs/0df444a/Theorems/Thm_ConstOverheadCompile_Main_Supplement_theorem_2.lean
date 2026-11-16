-- Prove2me | Theorems.Thm_ConstOverheadCompile_Main_Supplement_theorem_2
-- name    : ConstOverheadCompile.Main.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:33:31.510404+00:00
-- url     : https://prove2.me/theorems/3d3fb9db-3561-45f8-8e45-4adb00e94740
-- title:
--   Theorem 2 (corrected: $\log(1/\min(\epsilon,1))$) — circuits over the dyadic gate set compile to adaptive $\{H,T,\mathrm{CNOT}\}$ circuits with $O(G+\log(1/\epsilon))$ gates
-- statement:
--   Let $\mathcal D=\{H,T,\mathrm{CNOT}\}\cup\{R(\pi/2^j):j\ge1\}$ be the dyadic gate set of Eq. (4), $R(\theta)=\mathrm{diag}(1,e^{i\theta})$, and $\mathcal G=\{H,T,\mathrm{CNOT}\}$.
--
--   There is an absolute constant $C$ such that the following holds for every $\epsilon>0$, every number of qubits $n$ and every $G$. Let $A$ be an adaptive circuit on $n$ qubits (computational-basis measurements with classical feed-forward) whose every execution branch applies at most $G$ gates from $\mathcal D$. Then there are $a\ge0$ and an adaptive circuit $A'$ over $\mathcal G$ on $n+a$ qubits whose every branch applies at most
--
--   $$C\Big(G+\log\frac{1}{\min(\epsilon,1)}\Big)$$
--
--   gates, and whose channel on the $n$ data qubits (ancillas initialized to $|0\rangle$ and traced out at the end) is within diamond distance $\epsilon$ of the channel of $A$. For $\epsilon\le1$ the bound is the printed $O(G+\log(1/\epsilon))$.
--
--   Since even one dyadic gate needs $\Omega(\log(1/\epsilon))$ gates over $\mathcal G$ and $G$ gates need at least about $G$, this is the best possible scaling; it improves the $O(G\log(G/\epsilon))$ of gate-by-gate synthesis.
--
--   **Formalization Note** Gate counts are worst-case over branches; measurements are not counted. The diamond distance is the full-trace-norm one, required for every reference system.
--
--   Differences from the source:
--   - correction: O(G + log(1/ε)) gates for every ε > 0 → C·(G + log(1/min(ε, 1))); reason: for ε > 1 the printed bound can be negative: with C > 0, G = 0, ε = 2 and A the empty circuit it is C·log(1/2) < 0 and no circuit meets it; with C ≤ 0, G = 1, ε = 1/2 and A a single R(π/2) on input |+⟩, a gate-free circuit is at full-trace-norm distance ≥ 1 from |+i⟩⟨+i|; the two bounds agree for ε ≤ 1
--   - generalization: a circuit of G one- and two-qubit gates from 𝒟 → an adaptive circuit over 𝒟 with at most G gates on every branch; reason: p.3: 'the original circuit can also be adaptive in the same sense as in Theorem 1'; a measurement-free circuit is the special case with channel ρ ↦ UρU†
--   - encoding: O(·) → one real constant C quantified before ε, n, G and the circuit; natural logarithm; reason: meaning of the bound; the log base only changes C
--   - encoding: diamond distance → full-trace-norm diamond distance in universal form (DiamondClose), on the data register with the |0⟩ ancillas traced out; reason: it dominates the half-normalized diamond distance, so the bound implies the source's under either convention; the same convention as the published Theorems 1 and 9
--   - encoding: uses O(·) gates in the worst case → maximum over branches of the number of gates (maxGates); measurements not counted; reason: the source counts gates
-- source:
--   Chenyi Zhang, Xinyu Tan, Robin Kothari, David Gosset, Craig Gidney, Quantum circuit compilation with constant overhead, STOC 2027 submission #397 (October 2026), source.pdf SHA-256 b848604016de1821f5f693c59f328e0b2a9e535bca0b37bb664e6f40dbe3681f, p.2, Theorem 2, Eq. (5); 𝒟: p.2 Eq. (4); adaptive input: p.3 (first paragraph); proof: §2, pp.5–8

import Mathlib
import Definitions.Def_ConstOverheadCompile_Main_GateSets
import Definitions.Def_ConstOverheadCompile_Main_AdaptiveCircuit
import Definitions.Def_ConstOverheadCompile_Main_Supplement_PhaseGradient

namespace ConstOverheadCompile.Main.Supplement

open QAlgorithms ConstOverheadCompile.Main

/-- Theorem 2, p.2 (with the adaptive input of p.3; corrected: `log(1/min(ε, 1))`): there is an
absolute constant `C` such that for every `ε > 0` and every adaptive circuit on `n` wires over the
dyadic gate set `𝒟` with at most `G` gates on every branch, some adaptive circuit over
`𝒢 = {H, T, CNOT}` on `n + a` wires (ancillas in `|0⟩`, traced out) uses at most
`C (G + log(1/min(ε, 1)))` gates on every branch and is within diamond distance `ε` of it. -/
theorem theorem_2 :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ (n G : ℕ) (A : AdaptiveCircuit dyadicGates n),
      A.maxGates ≤ G →
        ∃ (a : ℕ) (A' : AdaptiveCircuit CliffordT (n + a)),
          (A'.maxGates : ℝ) ≤ C * ((G : ℝ) + Real.log (1 / min ε 1)) ∧
          DiamondClose A'.dataChannelRef A.channelRef ε := by sorry

end ConstOverheadCompile.Main.Supplement
