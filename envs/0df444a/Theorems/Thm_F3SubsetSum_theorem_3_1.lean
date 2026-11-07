-- Prove2me | Theorems.Thm_F3SubsetSum_theorem_3_1
-- name    : F3SubsetSum.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:15.781461+00:00
-- url     : https://prove2.me/theorems/e2c8f7d2-d88b-4609-9dac-4689277af5a6
-- title:
--   Theorem 3.1 — quantum reduction from $\mathbb F_3^n$-Subset-Sum to average-case Binary-Error LWE
-- statement:
--   Let $\mathrm{Dec}$ be a deterministic decoder for Binary-Error LWE over $\mathbb F_3$, computed by a machine that runs in time $T$ on every $(n,m)$-input, and let
--
--   $$\eta=\Pr_{A\sim\mathbb F_3^{n\times m},\,s\sim\mathbb F_3^n,\,e\sim\{0,1\}^m}\bigl[\mathrm{Dec}(A,A^\top s+e)\neq s\bigr]$$
--
--   be its average-case error. Then there is a quantum algorithm (depending only on the decoder's machine) that, for every $n,m,T$, runs in time $\mathrm{poly}(n,m,T)$ and solves Problem 1.1 with probability at least
--
--   $$1-2\eta-3^n\cdot(2/3)^m .$$
--
--   Concretely, a classical generator writes, on input $1^n0\,1^m0\,1^T$ and within $C(n+m+T+1)^C$ steps, a qutrit circuit over $G_3$ with at most that many gates and wires; the circuit is run on $|h\rangle\otimes|0\cdots0\rangle$ and measured. This is the reduction of Chen, Liu and Zhandry through Regev's method, which turns any good decoder into a Subset-Sum solver.
--
--   Differences from the source:
--   - reading: a quantum algorithm … runs in time poly(m, n, T) → a Turing-machine generator (Turing.TM2ComputableAux Bool Bool), given 1ⁿ 0 1ᵐ 0 1ᵀ, writes the code of a G₃ qutrit circuit within ⌊C(n+m+T+1)^C⌋ steps, with at most C(n+m+T+1)^C gates and wires, run on the input layout and measured on all wires; reason: the paper names no model of quantum computation; the + 1 keeps the bound positive at n = m = T = 0
--   - reading: a decoder Dec that runs in time T → a Turing machine M (Turing.TM2ComputableAux Bool Bool) computing Dec on every (n, m)-input within T steps; the generator depends on M; reason: the paper names no machine model
--   - encoding: error at most η → η replaced by the exact average-case error avgError Dec n m; reason: the bound for the exact error implies it for every η ≥ the error; same theorem
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Theorem 3.1, p.13 (proof pp.13–16)

import Mathlib
import Definitions.Def_F3SubsetSum_BinaryErrorLWE
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_F3SubsetSum_MachineCodes
import Definitions.Def_F3SubsetSum_QutritCircuit

namespace F3SubsetSum

/-- **Theorem 3.1** (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1, Theorem 3.1,
p.13; proof pp.13–16): "Suppose we have a deterministic decoder Dec : F_3^{n×m} × F_3^m → F_3^n
that runs in time T and solves average-case Binary-Error LWE over F_3 with error η, i.e.,
Pr_{A∼F_3^{n×m}, s∼F_3^n, e∼{0,1}^m}[Dec(A, A⊤s + e) ≠ s] ≤ η. Then there is a quantum algorithm
that solves average-case F_3^n-Subset-Sum (Problem 1.1) with probability at least
1 − 2η − 3^n · (2/3)^m and runs in time poly(m, n, T)."

For every machine `M` computing a decoder `Dec`, there are a circuit generator `G` and a
constant `C > 0` such that for all `n`, `m`, `T`: if `M` halts within `T` steps on every
`(n, m)`-input, then on input `1ⁿ 0 1ᵐ 0 1ᵀ` the generator writes, within `C(n + m + T + 1)^C`
steps, a qutrit circuit over `G₃` with at most that many gates and wires, which solves
Problem 1.1 with probability at least `1 − 2η − 3ⁿ(2/3)^m`, where `η = avgError Dec n m` is the
decoder's exact average-case error.

**Formalization Note** The quantum algorithm is a classical multi-stack Turing machine with Boolean
alphabets (`Turing.TM2ComputableAux Bool Bool`) that writes the code of a
qutrit circuit over the fixed gate set `G₃`, which is then run on `|h⟩ ⊗ |0…0⟩` and measured in
the computational basis (`successProb`). The generator depends on the decoder machine, which it
compiles. `poly(m, n, T)` is read as `C(n + m + T + 1)^C`; the `+ 1` keeps the bound positive at
`n = m = T = 0`. `η` is taken to be the error itself (the hypothesis `error ≤ η` then gives the
printed bound for every `η`). -/
theorem theorem_3_1 (M : Turing.TM2ComputableAux Bool Bool) (Dec : DecoderFn 3) :
    ∃ (G : Turing.TM2ComputableAux Bool Bool) (circ : ℕ → ℕ → ℕ → Circuit) (C : ℝ), 0 < C ∧
      ∀ n m T : ℕ, ComputesWithin M Dec n m T →
        HMBinPacking.OutputsWithin G (unaryD n ++ unaryD m ++ unary T) (encodeCircuit (circ n m T))
            ⌊C * ((n + m + T + 1 : ℕ) : ℝ) ^ C⌋₊ ∧
          n * m + m ≤ (circ n m T).wires ∧
          ((circ n m T).gates.length : ℝ) ≤ C * ((n + m + T + 1 : ℕ) : ℝ) ^ C ∧
          ((circ n m T).wires : ℝ) ≤ C * ((n + m + T + 1 : ℕ) : ℝ) ^ C ∧
          1 - 2 * avgError Dec n m - (3 : ℝ) ^ n * (2 / 3 : ℝ) ^ m ≤
            successProb n m (circ n m T) := by sorry

end F3SubsetSum
