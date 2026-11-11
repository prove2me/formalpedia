-- Prove2me | Theorems.Thm_ArbLindbladLearn_corollary_4_7
-- name    : ArbLindbladLearn.corollary_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:30:05.793173+00:00
-- url     : https://prove2.me/theorems/473d2804-e1c0-43dd-869b-182311b8a21e
-- title:
--   Corollary 4.7 — all coefficients of an arbitrary $n$-qubit Lindbladian to error $\varepsilon$ w.p. $1-\delta$: $\tilde O(\Lambda^2\varepsilon^{-2}\log\frac1\delta)$ experiments, polynomial time
-- statement:
--   There are absolute constants $C,K$ and one algorithm such that for every $n$, every $\Lambda$, every $\varepsilon,\delta\in(0,1)$ and every $n$-qubit Lindbladian $\mathcal L$ with Hamiltonian coefficients $h_a$, dissipative coefficients $\gamma_{ab}$ and $\|\mathcal L^\dagger\|_{\infty\to\infty}\le\Lambda$, the algorithm, given $n,\Lambda,\varepsilon,\delta$ and black-box access to $\{e^{t\mathcal L}\}_{t\ge0}$, outputs estimates $\hat h_a,\hat\gamma_{ab}$ with the following properties.
--   1. With probability at least $1-\delta$:
--   $$\max_{a\ne0}|\hat h_a-h_a|\le\varepsilon,\qquad\max_{a\ne0,\,b\ne0}|\hat\gamma_{ab}-\gamma_{ab}|\le\varepsilon;$$
--   on the same event at most $9\Lambda^2/\varepsilon^2$ estimates are nonzero, and every coefficient of magnitude at least $\varepsilon$ has a nonzero estimate.
--   2. With $g_1=(\Lambda/\varepsilon)^2\log(2/\delta)$, every run makes at most $C\,g_1\log^K(2+g_1)$ experiments, i.e. $\tilde O(\Lambda^2\varepsilon^{-2}\log\frac1\delta)$.
--   3. Every run has total evolution time at most $C\,(\Lambda/\varepsilon^2)\log(2/\delta)\log^K(2+g_1)$, i.e. $\tilde O(\Lambda\varepsilon^{-2}\log\frac1\delta)$.
--   4. With $g_3=n^3(\Lambda/\varepsilon)^{10}\log^5(2/\delta)$, every run halts within $C(1+g_3)\log^K(2+g_3)$ steps of classical work, i.e. $\tilde O(n^3\Lambda^{10}\varepsilon^{-10}\log^5\frac1\delta)$.
--
--   The experiment count and total evolution time do not depend on $n$, and no locality, sparsity or support information is assumed.
--
--   **Formalization Note** The algorithm is an admissible program of the learner's machine (classical real RAM with a fair coin and a Clifford-experiment instruction); it reads $n,\Lambda,\varepsilon,\delta$ and accesses $\mathcal L$ only through experiments. The output is a sparse record list; the probability is the run's probability of having halted with a good output after the step budget.
--
--   Differences from the source:
--   - encoding: Pauli labels a = (z, x) ∈ 𝔽₂²ⁿ with P_a = ⊗ᵢ(−i)^{zᵢxᵢ}Z^{zᵢ}X^{xᵢ} → labels Fin n → Fin 4 (letters I, X, Y, Z) with the public pauliMatrix; reason: (−i)ZX = Y, so both label sets index the same Hermitian Pauli operators, with 0 the identity
--   - encoding: a Lindbladian ℒ of the form (8) with h_a ∈ ℝ and γ Hermitian PSD → coefficients c = (h, γ) with IsLindbladCoeffs c and the generator gen c; reason: ℒ is determined by its coefficients (Lemma 3.1) and every such coefficient vector gives a Lindbladian; same instances
--   - encoding: ‖ℒ†‖_{∞→∞} ≤ Λ (induced spectral norm, Hilbert–Schmidt adjoint) → StrengthLE c Λ: ‖(gen c)ᴴ(A)‖_op ≤ Λ‖A‖_op for every operator A; reason: the induced-norm bound is equivalent to the pointwise bound for every A; same instances
--   - reading: for any ε, δ there exists an algorithm → ∃ C K and one admissible program P before n, Λ, ε, δ and ℒ, reading (n, Λ, ε, δ); reason: the stronger uniform reading; Algorithms 1–2 take these as inputs; a program depending on ℒ would make the statement trivial
--   - reading: an algorithm with experiments, evolution time and classical running time (no machine fixed) → the learner's machine: real RAM core with pointer arithmetic, integer memory, fair coin, halt, and one experiment instruction (Clifford preparation C₁|0ⁿ⟩, e^{tℒ}, Clifford C₂, computational-basis measurement), unit cost except 1 + n + |C₁| + |C₂| per experiment, and an admissible program (rational real literals only, output by halt, no core accept/reject; no cos, log or square root); reason: the paper's access model (§1.1, p.2); every experiment of Algorithms 1–2 has this form; fair coins and rational literals are stronger than the paper's sampling primitives and exact real arithmetic (nodes, logarithms and sampling weights must be approximated, with the slack in the proof)
--   - reading: Õ(g) (suppressing polylogarithmic factors) → C·g·log(2 + g)^K with absolute C, K chosen before every parameter; reason: the paper's notation (p.11); the experiment and evolution-time bounds carry no n, as the proof's counts do not
--   - reading: log(1/δ) → log(2/δ); reason: the printed form fails as δ → 1: for ε < Λ/4 the 2(4ⁿ − 1) Hamiltonians ±(Λ/2)P_a have pairwise disjoint success events, a bound below 1 forces zero experiments, and then some instance succeeds with probability ≤ 1/(2(4ⁿ − 1)) < 1 − δ; log(2/δ) ≤ 2 log(1/δ) for δ ≤ 1/2
--   - reading: classical running time Õ(n³Λ¹⁰ε⁻¹⁰ log⁵(1/δ)) → work at most ⌈C(1 + g₃) log(2 + g₃)^K⌉ and halting within that many steps; reason: a halting program takes at least one step, while the printed bound is 0 at Λ = 0
--   - reading: the numbers of experiments, total evolution time and running time → worst-case bounds on every run (every reachable configuration); reason: the stronger reading; the paper's bounds are deterministic
--   - encoding: the output: the list of nonzero estimates with their labels; at most 9Λ²/ε² estimates nonzero → a sparse record list read by decode; the count is the number of nonzero ĥ_a (a ≠ 0) plus the number of nonzero γ̂_ab (a, b ≠ 0, ordered pairs); reason: the paper counts dissipative coordinates as ordered pairs (p.2); unnamed labels get 0
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Corollary 4.7, p.34 (formal version of Theorem 1.1, p.3)

import Mathlib
import Definitions.Def_ArbLindbladLearn_Admissible
import Definitions.Def_ArbLindbladLearn_Reach
import Definitions.Def_ArbLindbladLearn_mass
import Definitions.Def_ArbLindbladLearn_Halted
import Definitions.Def_ArbLindbladLearn_initState
import Definitions.Def_ArbLindbladLearn_decode
import Definitions.Def_ArbLindbladLearn_StrengthLE
import Definitions.Def_ArbLindbladLearn_IsLindbladCoeffs

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker

namespace ArbLindbladLearn

open LindbladTolerant.Testing

open Classical in
/-- Corollary 4.7 (Learning arbitrary Lindbladians in polynomial time; Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…),
p.34). Let `ℒ` be an arbitrary `n`-qubit Lindbladian with `‖ℒ†‖_{∞→∞} ≤ Λ`. For any
`ε, δ ∈ (0, 1)`, there exists an algorithm that outputs coefficient estimates satisfying
`max_{a≠0} |ĥ_a − h_a| ≤ ε` and `max_{a≠0, b≠0} |γ̂_ab − γ_ab| ≤ ε` with probability at least `1 − δ`.
On the same event, at most `9Λ²/ε²` estimates are nonzero, and every coefficient of magnitude at
least `ε` has a nonzero estimate. The total number of experiments is `Õ(Λ²/ε² log 1/δ)`, the total
evolution time is `Õ(Λ/ε² log 1/δ)`, and the classical running time is
`Õ(n³Λ¹⁰ε⁻¹⁰ log⁵(1/δ))`.

**Formalization Note**
1. The algorithm is one admissible program of the learner's machine (`Instr`, `branches`), chosen
   before `n, Λ, ε, δ` and `ℒ`; it reads `n, Λ, ε, δ` (`initState`) and accesses `ℒ` only through
   the `experiment` instruction (prepare `C₁|0ⁿ⟩` with a Clifford circuit, apply `e^{tℒ}`, apply a
   Clifford circuit `C₂`, measure in the computational basis), with `evo t = e^{tℒ}`. Its output is
   the sparse record list read by `decode`.
2. `ℒ` is given by coefficients `c = (h, γ)` with `γ` Hermitian PSD (`IsLindbladCoeffs`) and
   `‖ℒ†(A)‖_∞ ≤ Λ‖A‖_∞` for every operator `A` (`StrengthLE`, spectral norm), which forces `Λ ≥ 0`.
3. `Õ(g)` is read as `C·g·log(2 + g)^K` with absolute constants `C, K` (chosen before every
   parameter), and `log(1/δ)` as `log(2/δ)` (equal up to a factor 2 for `δ ≤ 1/2`; the printed form
   cannot hold as `δ → 1`). With `g₁ = (Λ/ε)² log(2/δ)` and `g₃ = n³(Λ/ε)¹⁰ log⁵(2/δ)`: every run
   halts, with work at most `N = ⌈C(1 + g₃) log(2 + g₃)^K⌉`, within `N` steps; every reachable
   configuration has made at most `C·g₁·log(2 + g₁)^K` experiments with total duration at most
   `C(Λ/ε²) log(2/δ) log(2 + g₁)^K`. These cost bounds are worst case (on every run).
4. With probability (`mass` after `N` steps) at least `1 − δ` the machine has halted with output
   `(ĥ, γ̂) = decode n s` such that all four clauses hold on that one event: `|ĥ_a − h_a| ≤ ε`
   for every `a ≠ 0`; `|γ̂_ab − γ_ab| ≤ ε` for every `a, b ≠ 0`; the number of nonzero `ĥ_a` (`a ≠ 0`)
   plus the number of nonzero `γ̂_ab` (`a, b ≠ 0`, ordered pairs) is at most `9Λ²/ε²`; and every
   `h_a`, `γ_ab` of magnitude at least `ε` has a nonzero estimate. -/
theorem corollary_4_7 :
    ∃ C K : ℕ, ∃ P : Program, Admissible P ∧
      ∀ n : ℕ, ∀ Λ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∀ c : Coeffs n, IsLindbladCoeffs c → StrengthLE c Λ →
        let evo : ℝ → Super (Qubits n) (Qubits n) := fun t => evolution (gen c) t
        let s₀ : MState := initState n Λ ε δ
        let g₁ : ℝ := (Λ / ε) ^ 2 * Real.log (2 / δ)
        let g₃ : ℝ := (n : ℝ) ^ 3 * (Λ / ε) ^ 10 * Real.log (2 / δ) ^ 5
        let N : ℕ := ⌈(C : ℝ) * (1 + g₃) * Real.log (2 + g₃) ^ K⌉₊
        (∀ s : MState, Reach P n evo N s₀ s → Halted s ∧ s.work ≤ N) ∧
        ENNReal.ofReal (1 - δ) ≤ mass P n evo N s₀ (fun s => Halted s ∧
          (∀ a : Pauli n, a ≠ 0 → |(decode n s).h a - c.h a| ≤ ε) ∧
          (∀ a b : Pauli n, a ≠ 0 → b ≠ 0 → ‖(decode n s).γ a b - c.γ a b‖ ≤ ε) ∧
          (((Finset.univ.filter (fun a : Pauli n => a ≠ 0 ∧ (decode n s).h a ≠ 0)).card +
              (Finset.univ.filter (fun p : Pauli n × Pauli n =>
                p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ (decode n s).γ p.1 p.2 ≠ 0)).card : ℕ) : ℝ) ≤
            9 * Λ ^ 2 / ε ^ 2 ∧
          (∀ a : Pauli n, a ≠ 0 → ε ≤ |c.h a| → (decode n s).h a ≠ 0) ∧
          (∀ a b : Pauli n, a ≠ 0 → b ≠ 0 → ε ≤ ‖c.γ a b‖ → (decode n s).γ a b ≠ 0)) ∧
        ∀ (M : ℕ) (s : MState), Reach P n evo M s₀ s →
          (s.durations.length : ℝ) ≤ C * g₁ * Real.log (2 + g₁) ^ K ∧
          s.durations.sum ≤ C * (Λ / ε ^ 2) * Real.log (2 / δ) * Real.log (2 + g₁) ^ K := by sorry

end ArbLindbladLearn
