-- Prove2me | Theorems.Thm_F3SubsetSum_theorem_1_3
-- name    : F3SubsetSum.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:06.465302+00:00
-- url     : https://prove2.me/theorems/cfc8a384-25d3-438f-9c7b-66ea55770650
-- title:
--   Theorem 1.3 — quantum time $(m/n)^{O(\lceil n^2/m\rceil)}$ for average-case $\mathbb F_3^n$-Subset-Sum at every $m\ge\kappa n$, $\kappa>\log_2 3$
-- statement:
--   Let $\kappa>\log_2 3$. There are a quantum algorithm and constants $C,c>0$ (depending on $\kappa$) such that for all $n\ge1$ and $m\ge\kappa n$: given $h_1,\dots,h_m$ independent and uniform in $\mathbb F_3^n$, the algorithm outputs a nonempty $S\subseteq[m]$ with
--
--   $$\sum_{i\in S}h_i=0$$
--
--   with probability at least $1-2^{-cm}$, and it runs in time
--
--   $$\Bigl(\frac mn\Bigr)^{C\lceil n^2/m\rceil}.$$
--
--   Concretely, one classical generator, on input $1^n0\,1^m$, writes within that many steps a qutrit circuit over the gate set $G_3$ with at least $nm+m$ and at most that many wires and at most that many gates; the circuit is run on $|h\rangle\otimes|0\cdots0\rangle$, all wires are measured, and $S$ is read from the $m$ wires after the input. For $m=\epsilon n^2$ with $\epsilon>0$ fixed this is polynomial time, while the best known classical algorithms need $m\approx0.1022\,n^2$.
--
--   Differences from the source:
--   - reading: a quantum algorithm … runs in time (m/n)^{O_κ(⌈n²/m⌉)} → a Turing-machine generator (Turing.TM2ComputableAux Bool Bool) writes, within ⌊(m/n)^{C⌈n²/m⌉}⌋ steps, the code of a qutrit circuit over the fixed finite gate set G₃ with at most that many gates and wires, run on the input layout and measured on all wires; reason: the paper names no model of quantum computation; any fixed finite universal gate set gives the same theorem at this precision
--   - reading: for every m ≥ κ·n there is a quantum algorithm …, O_κ, Ω_κ → one generator and constants C, c > 0 chosen before n and m, for every n ≥ 1 and m ≥ κn; no constant factor outside the power; reason: the strongest reading; the proof's algorithm is uniform, and since m/n ≥ κ > 1 a constant factor is absorbed into C
--   - encoding: n arbitrary → n ≥ 1; reason: m/n is undefined at n = 0
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Theorem 1.3, p.4 (restated p.22; proof pp.22–23)

import Mathlib
import Definitions.Def_F3SubsetSum_SubsetSum
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_F3SubsetSum_MachineCodes
import Definitions.Def_F3SubsetSum_QutritCircuit

namespace F3SubsetSum

/-- **Theorem 1.3** (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1, Theorem 1.3,
p.4; restated p.22; proof pp.22–23): "Let κ > log(3) be any constant. For every m ≥ κ · n, there
is a quantum algorithm that solves Problem 1.1 with probability at least 1 − 2^{−Ω_κ(m)} and runs
in time (m/n)^{O_κ(⌈n²/m⌉)}."

For every `κ > log₂ 3` there are one circuit generator `M` and constants `C, c > 0` such that for
all `n ≥ 1` and `m ≥ κn`, on input `1ⁿ 0 1ᵐ` the generator writes, within
`T = (m/n)^{C⌈n²/m⌉}` steps, a qutrit circuit over `G₃` with at least `nm + m` and at most `T`
wires and at most `T` gates; run on `|h⟩ ⊗ |0…0⟩` and measured, it outputs a nonempty `S ⊆ [m]`
with `Σ_{i∈S} h_i = 0` with probability at least `1 − 2^{−cm}`, over uniform `h₁, …, h_m ∈ F₃ⁿ`
and the measurement.

**Formalization Note** The paper names no model of quantum computation. A quantum algorithm is
read as a deterministic multi-stack Turing machine with Boolean alphabets
(`Turing.TM2ComputableAux Bool Bool`, run as in the published `HMBinPacking.OutputsWithin`) that
writes the (injective) code of a circuit over the
fixed finite qutrit gate set `G₃`; the circuit acts on the input layout `inputBasis` and its
output is read from the `m` wires after the input (`successProb`). "Time" is the generator's
step count, which also bounds the number of gates and wires (stated explicitly). `log` is base 2.
`O_κ`, `Ω_κ` are constants depending on `κ` only, chosen with the generator before `n` and `m`.
`⌈·⌉` is the real ceiling and the power is a real power; there is no constant factor outside
the power because `m/n ≥ κ > 1`. `n ≥ 1` because `m/n` is undefined at `n = 0`. -/
theorem theorem_1_3 (κ : ℝ) (hκ : Real.logb 2 3 < κ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (circ : ℕ → ℕ → Circuit) (C c : ℝ), 0 < C ∧ 0 < c ∧
      ∀ n m : ℕ, 1 ≤ n → κ * n ≤ m →
        HMBinPacking.OutputsWithin M (unaryD n ++ unary m) (encodeCircuit (circ n m))
            ⌊((m : ℝ) / n) ^ (C * (⌈(n : ℝ) ^ 2 / m⌉ : ℝ))⌋₊ ∧
          n * m + m ≤ (circ n m).wires ∧
          ((circ n m).gates.length : ℝ) ≤ ((m : ℝ) / n) ^ (C * (⌈(n : ℝ) ^ 2 / m⌉ : ℝ)) ∧
          ((circ n m).wires : ℝ) ≤ ((m : ℝ) / n) ^ (C * (⌈(n : ℝ) ^ 2 / m⌉ : ℝ)) ∧
          1 - (2 : ℝ) ^ (-(c * m)) ≤ successProb n m (circ n m) := by sorry

end F3SubsetSum
