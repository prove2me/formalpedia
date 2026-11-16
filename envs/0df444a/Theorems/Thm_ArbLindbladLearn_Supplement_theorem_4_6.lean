-- Prove2me | Theorems.Thm_ArbLindbladLearn_Supplement_theorem_4_6
-- name    : ArbLindbladLearn.Supplement.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:23:58.921207+00:00
-- url     : https://prove2.me/theorems/d357f892-9e64-40ff-b515-b03590e0b42b
-- title:
--   Theorem 4.6 — coefficient learning by Clifford probing on given candidate supports with $\tilde O(\Lambda^2\varepsilon^{-2}\log(M/\delta))$ experiments (corrected: running time)
-- statement:
--   There are absolute constants $C,K$ and one algorithm such that the following holds for every $n$, every $\Lambda$, every $\varepsilon,\delta\in(0,1)$, all candidate supports $\hat{\mathcal S}_H$ (a set of nonidentity Pauli labels) and $\hat{\mathcal S}_D$ (a set of ordered pairs of nonidentity labels) of total size $M=|\hat{\mathcal S}_H|+|\hat{\mathcal S}_D|$, and every $n$-qubit Lindbladian $\mathcal L$ with Hamiltonian coefficients $h_a$, dissipative coefficients $\gamma_{ab}$ and $\|\mathcal L^\dagger\|_{\infty\to\infty}\le\Lambda$. Given $n,\Lambda,\varepsilon,\delta,\hat{\mathcal S}_H,\hat{\mathcal S}_D$ and black-box access to $\{e^{t\mathcal L}\}_{t\ge0}$, the algorithm outputs estimates $\hat h_a$, $\hat\gamma_{ab}$ such that:
--   1. with probability at least $1-\delta$,
--   $$\max_{a\in\hat{\mathcal S}_H}|\hat h_a-h_a|\le\varepsilon\qquad\text{and}\qquad\max_{(a,b)\in\hat{\mathcal S}_D}|\hat\gamma_{ab}-\gamma_{ab}|\le\varepsilon;$$
--   2. with $g=(\Lambda/\varepsilon)^2\log(M/\delta)$, every run makes at most $N_b=C\,g\log^K(2+g)$ experiments, i.e. $N=\tilde O(\Lambda^2\varepsilon^{-2}\log\frac M\delta)$, with total evolution time at most $C(\Lambda/\varepsilon^2)\log(M/\delta)\log^K(2+g)$, i.e. $\tilde O(\Lambda\varepsilon^{-2}\log\frac M\delta)$;
--   3. every run halts within $\lceil C(1+N_b+\log(2+\Lambda/\varepsilon))(1+M)(1+n)^3\rceil$ steps of classical work, the form $O(NMn^3)$ takes once $N,M,n\ge1$ and $N\gtrsim\log(\Lambda/\varepsilon)$.
--
--   The experiment count depends on the candidate supports only through $\log M$, so even the full family of all $4^n-1+(4^n-1)^2$ coordinates needs only $\tilde O(\Lambda^2\varepsilon^{-2}(n+\log\frac1\delta))$ experiments. Composed with the support-learning stage (Theorem 3.8) it gives Corollary 4.7.
--
--   **Formalization Note** The algorithm is one admissible program of the base mission's learner machine, chosen before all parameters; it reads $(n,\Lambda,\varepsilon,\delta)$ and the candidate lists from its input and accesses $\mathcal L$ only through Clifford experiments. The estimates are read by the published `decode`.
--
--   Differences from the source:
--   - encoding: Pauli labels a = (z, x) ∈ 𝔽₂²ⁿ → labels Fin n → Fin 4 (letters I, X, Y, Z) with the public pauliMatrix; reason: (−i)ZX = Y, so both label sets index the same Hermitian Pauli operators, with 0 the identity
--   - encoding: an n-qubit Lindbladian ℒ of the form (8), γ Hermitian PSD → coefficients c = (h, γ) with IsLindbladCoeffs c and the published generator gen c; reason: ℒ is determined by its coefficients and every such coefficient vector gives a Lindbladian; same instances
--   - encoding: ‖ℒ†‖_{∞→∞} ≤ Λ → StrengthLE c Λ: ‖(gen c)ᴴ(A)‖_op ≤ Λ‖A‖_op for every operator A; reason: the induced-norm bound is equivalent to the pointwise bound for every A; same instances
--   - reading: Algorithm 2 outputs estimates with these guarantees → ∃ C K and one admissible program P, chosen before n, Λ, ε, δ, the candidate supports and ℒ, with these guarantees; reason: Algorithm 2 cannot run verbatim on the machine (Chebyshev nodes need cos, exact uniform stabilizer and Clifford sampling with fair coins); its content is an algorithm with these guarantees, uniform in the parameters
--   - reading: an algorithm with experiments, evolution time and classical running time (no machine fixed) → the published learner's machine (real RAM with pointer arithmetic, integer memory, fair coin, halt and one Clifford experiment instruction; unit cost except 1 + n + |C₁| + |C₂| per experiment) and an admissible program; reason: the paper's access model (§1.1, p.2) and the base mission's machine; every experiment of Algorithms 1–2 has this form
--   - encoding: candidate supports Ŝ_H and Ŝ_D of total size M = |Ŝ_H| + |Ŝ_D|, given → duplicate-free lists SH of nonidentity labels and SD of ordered pairs of nonidentity labels, written into the machine's input (initStateCand); M = |SH| + |SD|; reason: the candidates are sets of coordinates of Definition 2.6 (labels a ≠ 0); a duplicate-free list is a finite set
--   - reading: Õ(g) → C·g·log(2 + g)^K with absolute C, K chosen before every parameter; reason: the paper's notation (p.11), as in the base mission's goal
--   - correction: classical running time O(NMn³) → work at most ⌈C(1 + N_b + log(2 + Λ/ε))(1 + M)(1 + n)³⌉ and halting within that many steps; reason: the printed bound fails when N_b → 0: n = 1, SH = [X], SD = [], ε = 1/2, Λ large and δ so close to 1 that N_b < 1; then no experiment is made and the output law does not depend on h_X, which may be any value in [−Λ/2, Λ/2] (strength ≤ 2|h_X|); a run with w steps flips at most w coins, so outputs at most 2^w values, and once 2^w < Λ/2 some h_X is missed by all of them, with success probability 0 < 1 − δ; so w ≥ log₂(Λ/2) is needed while C(1 + N)(1 + M)(1 + n)³ stays bounded; the 1 + terms also cover N = 0, M = 0, n = 0, where a halting run still takes a step; for M ≥ 2 or δ ≤ 1/2, N_b ≥ c(Λ/ε)² dominates the added log term
--   - reading: the number of experiments, total evolution time and running time → worst-case bounds on every run (every reachable configuration); reason: the stronger reading; the paper's bounds are deterministic
--   - encoding: the estimates {ĥ_a}_{a∈Ŝ_H} and {γ̂_ab}_{(a,b)∈Ŝ_D} → a sparse record list read by the published decode; the accuracy clause is checked at the labels of SH and the pairs of SD; reason: the base mission's output format
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Theorem 4.6, p.32 (pdf p.34); Algorithm 2, p.31

import Mathlib
import Definitions.Def_ArbLindbladLearn_Admissible
import Definitions.Def_ArbLindbladLearn_Reach
import Definitions.Def_ArbLindbladLearn_mass
import Definitions.Def_ArbLindbladLearn_Halted
import Definitions.Def_ArbLindbladLearn_decode
import Definitions.Def_ArbLindbladLearn_StrengthLE
import Definitions.Def_ArbLindbladLearn_IsLindbladCoeffs
import Definitions.Def_ArbLindbladLearn_Supplement_initStateCand

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker

namespace ArbLindbladLearn.Supplement

open LindbladTolerant.Testing
open ArbLindbladLearn

/-- Theorem 4.6 (Coefficient learning by Clifford probing; Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.32). Let `ℒ` be an arbitrary
`n`-qubit Lindbladian with `‖ℒ†‖_{∞→∞} ≤ Λ`. Suppose candidate supports `Ŝ_H` and `Ŝ_D`, of total
size `M ≔ |Ŝ_H| + |Ŝ_D|`, are given. For any `ε, δ ∈ (0, 1)`, Algorithm 2 outputs, with probability
at least `1 − δ`, estimates satisfying `max_{a∈Ŝ_H} |ĥ_a − h_a| ≤ ε` and
`max_{(a,b)∈Ŝ_D} |γ̂_ab − γ_ab| ≤ ε`. The total number of experiments is `N = Õ(Λ²/ε² log M/δ)`.
The total evolution time is `T_tot = Õ(Λε⁻² log(M/δ))`, and the classical running time is
`O(NMn³)`.

**Formalization Note**
1. The algorithm is one admissible program of the published learner's machine, chosen with
   `C, K` before `n, Λ, ε, δ`, the candidate supports and `ℒ`; it reads `n, Λ, ε, δ` and the
   candidate supports from `initStateCand` and accesses `ℒ` only through the Clifford `experiment`
   instruction (every experiment of Algorithm 2 is a random stabilizer preparation, `e^{tℒ}`, a
   random Clifford and a computational-basis measurement), with `evo t = e^{tℒ}`. Its estimates are
   read by the published `decode`.
2. The candidate supports are duplicate-free lists `SH` of nonidentity labels and `SD` of ordered
   pairs of nonidentity labels (the coordinates of Definition 2.6), so `M = |SH| + |SD|`.
3. `Õ(g)` is read as `C·g·log(2 + g)^K` with absolute `C, K`; the printed `log(M/δ)` is kept. With
   `g = (Λ/ε)² log(M/δ)` and `N_b = C·g·log(2 + g)^K`: every reachable configuration has made at most
   `N_b` experiments, with total duration at most `C(Λ/ε²) log(M/δ) log(2 + g)^K`.
4. Running time `O(NMn³)` becomes: every run halts, with work at most
   `W = ⌈C(1 + N_b + log(2 + Λ/ε))(1 + M)(1 + n)³⌉`, within `W` steps. The `1 +` terms keep the
   bound positive when `N_b`, `M` or `n` vanish, and `log(2 + Λ/ε)` covers the case `M = 1`,
   `δ → 1`, where `N_b → 0` (see the item's list of differences).
5. With probability (`mass` after `W` steps) at least `1 − δ` the machine has halted with
   `|ĥ_a − h_a| ≤ ε` for every `a ∈ SH` and `|γ̂_ab − γ_ab| ≤ ε` for every `(a, b) ∈ SD`. -/
theorem theorem_4_6 :
    ∃ C K : ℕ, ∃ P : Program, Admissible P ∧
      ∀ n : ℕ, ∀ Λ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∀ (SH : List (Pauli n)) (SD : List (Pauli n × Pauli n)), SH.Nodup → SD.Nodup →
      (∀ a ∈ SH, a ≠ 0) → (∀ p ∈ SD, p.1 ≠ 0 ∧ p.2 ≠ 0) →
      ∀ c : Coeffs n, IsLindbladCoeffs c → StrengthLE c Λ →
        let evo : ℝ → Super (Qubits n) (Qubits n) := fun t => evolution (gen c) t
        let s₀ : MState := initStateCand n Λ ε δ SH SD
        let M : ℕ := SH.length + SD.length
        let g : ℝ := (Λ / ε) ^ 2 * Real.log ((M : ℝ) / δ)
        let Nb : ℝ := C * g * Real.log (2 + g) ^ K
        let W : ℕ := ⌈(C : ℝ) * (1 + Nb + Real.log (2 + Λ / ε)) * (1 + (M : ℝ)) *
          (1 + (n : ℝ)) ^ 3⌉₊
        (∀ s : MState, Reach P n evo W s₀ s → Halted s ∧ s.work ≤ W) ∧
        ENNReal.ofReal (1 - δ) ≤ mass P n evo W s₀ (fun s => Halted s ∧
          (∀ a ∈ SH, |(decode n s).h a - c.h a| ≤ ε) ∧
          (∀ p ∈ SD, ‖(decode n s).γ p.1 p.2 - c.γ p.1 p.2‖ ≤ ε)) ∧
        ∀ (M' : ℕ) (s : MState), Reach P n evo M' s₀ s →
          (s.durations.length : ℝ) ≤ Nb ∧
          s.durations.sum ≤
            C * (Λ / ε ^ 2) * Real.log ((M : ℝ) / δ) * Real.log (2 + g) ^ K := by sorry

end ArbLindbladLearn.Supplement
