-- Prove2me | Theorems.Thm_ConstOverheadCompile_Main_theorem_9
-- name    : ConstOverheadCompile.Main.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:14.859128+00:00
-- url     : https://prove2.me/theorems/0b206022-ada3-460a-a072-2d23a9937091
-- title:
--   Theorem 9 (corrected: ε ≤ 1): circuits over $\mathcal G\cup\mathcal S_D$, $D=B^r$, compile with $O(rG+rB\log B\log(\epsilon^{-1}Br\log B))$ gates
-- statement:
--   There is an absolute constant $C_0$ with the following property. Let $r\ge2$ and $b\ge0$ be integers, $B=2^b$, $D=B^r$, and $0<\varepsilon\le1$. Let $A$ be an adaptive circuit on $n$ wires over $\mathcal G\cup\mathcal S_D$ (with $\mathcal G=\{H,T,\mathrm{CNOT}\}$ and $\mathcal S_D=\{R(2\pi j/D):0\le j<D\}$) that uses at most $G$ gates on every branch. Then for some number $a$ of ancillas there is an adaptive circuit $A'$ over $\mathcal G$ on $n+a$ wires such that
--
--   1. every branch of $A'$ uses at most
--   $$C_0\Big(rG+rB\log(B)\,\log\big(\varepsilon^{-1}Br\log(B)\big)\Big)$$
--   gates, and
--   2. the data channel of $A'$ (ancillas initialized to $|0\rangle$ and traced out) is within diamond distance $\varepsilon$ of the channel of $A$.
--
--   This is the core compilation result: Theorem 1 follows by decomposing into CNOT, $H$ and rotations, rounding every angle to the grid $\mathcal S_D$ with $D=\Theta(G/\varepsilon)$, and choosing $r$ and $B$ so that the bound is $O(G)$.
--
--   Differences from the source:
--   - correction: all $\epsilon>0$ → $0<\varepsilon\le1$; reason: the printed bound is false for large $\epsilon$: with $B=2$, $r=2$, $G=0$, $\epsilon=100$ the quantity in (30) is $2\cdot2\ln2\cdot\ln(4\ln2/100)<0$, so no circuit meets it for any positive big-O constant; for $\varepsilon\le1$ the bound is nonnegative, and the paper uses $\epsilon<1$ throughout.
--   - generalization: a circuit of $G$ gates from $\mathcal G\cup\mathcal S_D$ → an adaptive circuit (computational-basis measurements, classical feed-forward) with at most $G$ gates on every branch; reason: Remark 5 (p.8) and the paragraph after Theorem 1; a measurement-free circuit is the special case, whose channel is $\rho\mapsto U\rho U^\dagger$.
--   - reading: "$D,B$ powers of two" with (30) undefined at $B=1$ → $B=2^b$ for every $b\ge0$; at $B=1$ the second term is $0$ (Lean's $\log 0=0$); reason: $1=2^0$ is a power of two and $\mathcal S_1=\{I\}$; the case is not excluded by the source.
--   - encoding: $O(\cdot)$ → one real constant $C_0$ quantified before $r,b,\varepsilon,n,G,A$; natural logarithms; reason: the meaning of the bound; the base of the logarithm only changes $C_0$.
--   - encoding: "diamond distance" → the full-trace-norm diamond distance in universal form over all reference dimensions; reason: it is at least the half-normalized one, so the bound implies the source's under either convention.
-- source:
--   Chenyi Zhang, Xinyu Tan, Robin Kothari, David Gosset, Craig Gidney, Quantum circuit compilation with constant overhead, STOC 2027 submission #397 (October 2026), source.pdf SHA-256 b848604016de1821f5f693c59f328e0b2a9e535bca0b37bb664e6f40dbe3681f, p.10, §4, Theorem 9, Eq. (30); 𝒮_D: p.8 Eq. (18); adaptive input: p.8 Remark 5

import Mathlib
import Definitions.Def_ConstOverheadCompile_Main_GateSets
import Definitions.Def_ConstOverheadCompile_Main_AdaptiveCircuit

namespace ConstOverheadCompile.Main

open QAlgorithms

/-- Theorem 9, p.10, with `ε ≤ 1` (the printed bound (30) is negative for large `ε`): there is
an absolute constant `C₀` such that for all `r ≥ 2`, `B = 2^b`, `D = B^r`, `ε ∈ (0, 1]` and every
adaptive circuit on `n` wires over `𝒢 ∪ 𝒮_D` with at most `G` gates on every branch, some
adaptive circuit over `𝒢` on `n + a` wires (ancillas in `|0⟩`, traced out) uses at most
`C₀ (rG + rB log B · log(ε⁻¹ B r log B))` gates on every branch and is within diamond distance
`ε` of it. -/
theorem theorem_9 :
    ∃ C₀ : ℝ, ∀ r b : ℕ, 2 ≤ r → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ (n G : ℕ) (A : AdaptiveCircuit (CliffordT ∪ gridGates ((2 ^ b) ^ r)) n),
        A.maxGates ≤ G →
        ∃ (a : ℕ) (A' : AdaptiveCircuit CliffordT (n + a)),
          (A'.maxGates : ℝ) ≤ C₀ * ((r : ℝ) * G + (r : ℝ) * (2 : ℝ) ^ b * Real.log ((2 : ℝ) ^ b) *
              Real.log (ε⁻¹ * (2 : ℝ) ^ b * (r : ℝ) * Real.log ((2 : ℝ) ^ b))) ∧
          DiamondClose A'.dataChannelRef A.channelRef ε := by sorry

end ConstOverheadCompile.Main
