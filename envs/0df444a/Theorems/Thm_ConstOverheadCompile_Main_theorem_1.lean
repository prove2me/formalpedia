-- Prove2me | Theorems.Thm_ConstOverheadCompile_Main_theorem_1
-- name    : ConstOverheadCompile.Main.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:13.625516+00:00
-- url     : https://prove2.me/theorems/94621996-4c34-4d52-873a-955d017a8c30
-- title:
--   Theorem 1: a circuit of $G$ one- and two-qubit gates has an adaptive $\{H,T,\mathrm{CNOT}\}$ implementation with $O(G)$ gates to any $1/\mathrm{poly}(G)$ diamond-distance error
-- statement:
--   For all real $K>0$ and $c>0$ there is a constant $C$ with the following property. Let $n\ge0$ and $G\ge1$ be integers, and let $A$ be an adaptive circuit on $n$ qubits whose gates are arbitrary one- and two-qubit unitaries, with computational-basis measurements and classical feed-forward, using at most $G$ gates on every execution branch. Then for some number $a$ of ancillas there is an adaptive circuit $A'$ on $n+a$ qubits whose only gates are $H$, $T$ and CNOT, such that
--
--   1. every branch of $A'$ uses at most $C\,G$ gates, and
--   2. the data channel of $A'$ (ancillas initialized to $|0\rangle$, traced out at the end) is within diamond distance
--   $$\frac{1}{K\,G^{c}}$$
--   of the channel of $A$.
--
--   The constant $C$ depends only on $K$ and $c$, not on $n$, $G$ or $A$. The standard gate-by-gate compilation costs $O(G\log(G/\varepsilon))$ gates; the theorem removes the logarithmic overhead for every inverse-polynomial target error.
--
--   Differences from the source:
--   - generalization: a circuit of $G$ one- and two-qubit gates → an adaptive circuit with at most $G$ one- and two-qubit unitary gates on every branch; reason: the paragraph after Theorem 1 on p.2 and Remark 5; a measurement-free circuit is the special case, whose channel is $\rho\mapsto U\rho U^\dagger$.
--   - encoding: "any given $1/\mathrm{poly}(G)$ error" and "$O(G)$" → for all $K,c>0$ there is $C$, quantified before $n$, $G$, $A$, with error $1/(KG^c)$ and gate bound $CG$; reason: every polynomial $p$ satisfies $p(G)\le KG^c$ for $G\ge1$, so the family $1/(KG^c)$ contains every inverse-polynomial error, and the constant may depend only on the polynomial.
--   - encoding: $G$ arbitrary → $G\ge1$; reason: the chosen error expression $1/(KG^c)$ has a zero denominator at $G=0$; circuits with no unitary gates, possibly containing measurements and feed-forward, compile exactly by retaining their measurement tree, so the omitted case needs no approximation.
--   - encoding: "diamond distance" → the full-trace-norm diamond distance in universal form over all reference dimensions, on the data register with $|0\rangle$ ancillas traced out; reason: it dominates the half-normalized one, so the bound implies the source's under either convention.
--   - encoding: "uses $O(G)$ gates in the worst case" → the maximum over branches of the number of gates; measurements are not counted; reason: the source counts gates.
-- source:
--   Chenyi Zhang, Xinyu Tan, Robin Kothari, David Gosset, Craig Gidney, Quantum circuit compilation with constant overhead, STOC 2027 submission #397 (October 2026), source.pdf SHA-256 b848604016de1821f5f693c59f328e0b2a9e535bca0b37bb664e6f40dbe3681f, p.2, §1, Theorem 1, Eq. (3), and the following paragraph; p.8 Remark 5; proof: §4, pp.10–11

import Mathlib
import Definitions.Def_ConstOverheadCompile_Main_GateSets
import Definitions.Def_ConstOverheadCompile_Main_AdaptiveCircuit

namespace ConstOverheadCompile.Main

open QAlgorithms

/-- Theorem 1, p.2 (with the adaptive input of p.2 and Remark 5): for every polynomial error
bound `1/(K G^c)` there is a constant `C` such that every adaptive circuit on `n` wires over
arbitrary one- and two-qubit unitary gates, with at most `G ≥ 1` gates on every branch, is
implemented within diamond distance `1/(K G^c)` by an adaptive circuit over `{H, T, CNOT}` on
`n + a` wires (ancillas in `|0⟩`, traced out) with at most `C G` gates on every branch. -/
theorem theorem_1 :
    ∀ K c : ℝ, 0 < K → 0 < c → ∃ C : ℝ, ∀ (n G : ℕ), 1 ≤ G →
      ∀ A : AdaptiveCircuit ArbGates n, A.maxGates ≤ G →
        ∃ (a : ℕ) (A' : AdaptiveCircuit CliffordT (n + a)),
          (A'.maxGates : ℝ) ≤ C * G ∧
          DiamondClose A'.dataChannelRef A.channelRef (1 / (K * (G : ℝ) ^ c)) := by sorry

end ConstOverheadCompile.Main
