-- Prove2me | Theorems.Thm_ArbLindbladLearn_Supplement_theorem_3_8
-- name    : ArbLindbladLearn.Supplement.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:22:45.663423+00:00
-- url     : https://prove2.me/theorems/34152d03-0323-4f49-8d36-0b0a6bd846c9
-- title:
--   Theorem 3.8 — threshold support learning: $\eta$-heavy supports covered w.p. $1-\delta$ with $\tilde O(\Lambda^2\eta^{-2}\log\frac1\delta)$ experiments (corrected: $\log(2/\delta)$)
-- statement:
--   There are absolute constants $C,K$ and one algorithm such that the following holds for every $n$, every $\Lambda$, every $\eta\in(0,\Lambda]$, every $\delta\in(0,1)$ and every $n$-qubit Lindbladian $\mathcal L$ with $\|\mathcal L^\dagger\|_{\infty\to\infty}\le\Lambda$. Given $n,\Lambda,\eta,\delta$ and black-box access to $\{e^{t\mathcal L}\}_{t\ge0}$, the algorithm outputs candidate supports $\hat{\mathcal S}_H$ (nonidentity labels) and $\hat{\mathcal S}_D$ (ordered pairs of nonidentity labels) such that:
--   1. with probability at least $1-\delta$,
--   $$\mathcal S_H^{\ge\eta}\subseteq\hat{\mathcal S}_H,\qquad\mathcal S_D^{\ge\eta}\subseteq\hat{\mathcal S}_D,$$
--   where $\mathcal S_H^{\ge\eta}=\{a\ne0:|h_a|\ge\eta\}$ and $\mathcal S_D^{\ge\eta}=\{(a,b):a,b\ne0,\ |\gamma_{ab}|\ge\eta\}$ are the $\eta$-heavy supports;
--   2. on every run the output size satisfies $|\hat{\mathcal S}_H|+|\hat{\mathcal S}_D|\le C\,g_{\mathrm{out}}\log^K(2+g_{\mathrm{out}})$ with $g_{\mathrm{out}}=(\Lambda/\eta)^8\log^4(2/\delta)$, i.e. $\tilde O(\Lambda^8\eta^{-8}\log^4\frac1\delta)$;
--   3. with $g_1=(\Lambda/\eta)^2\log(2/\delta)$, every run makes at most $C\,g_1\log^K(2+g_1)$ experiments, i.e. $\tilde O(\Lambda^2\eta^{-2}\log\frac1\delta)$, with total evolution time at most $C(\Lambda/\eta^2)\log(2/\delta)\log^K(2+g_1)$, i.e. $\tilde O(\Lambda\eta^{-2}\log\frac1\delta)$;
--   4. with $g_{\mathrm{run}}=n(\Lambda/\eta)^8\log^4(2/\delta)$, every run halts within $\lceil C(1+g_{\mathrm{run}})\log^K(2+g_{\mathrm{run}})\rceil$ steps of classical work, i.e. $\tilde O(n\Lambda^8\eta^{-8}\log^4\frac1\delta)$.
--
--   This is the support-learning stage of the arbitrary-Lindbladian learner: composed with Theorem 4.6 on the output supports, it gives Corollary 4.7.
--
--   **Formalization Note** The algorithm is one admissible program of the base mission's learner machine, chosen before all parameters; it reads $(n,\Lambda,\eta,\delta)$ and accesses $\mathcal L$ only through Clifford experiments. The output is read from the halted configuration by `decodeSupports`; the probability is that of having halted with a good output after the step budget.
--
--   Differences from the source:
--   - encoding: Pauli labels a = (z, x) ∈ 𝔽₂²ⁿ → labels Fin n → Fin 4 (letters I, X, Y, Z) with the public pauliMatrix; reason: (−i)ZX = Y, so both label sets index the same Hermitian Pauli operators, with 0 the identity
--   - encoding: an n-qubit Lindbladian ℒ of the form (8), γ Hermitian PSD → coefficients c = (h, γ) with IsLindbladCoeffs c and the published generator gen c; reason: ℒ is determined by its coefficients and every such coefficient vector gives a Lindbladian; same instances
--   - encoding: ‖ℒ†‖_{∞→∞} ≤ Λ → StrengthLE c Λ: ‖(gen c)ᴴ(A)‖_op ≤ Λ‖A‖_op for every operator A; reason: the induced-norm bound is equivalent to the pointwise bound for every A; same instances
--   - reading: Algorithm 1 outputs Ŝ_H and Ŝ_D with these guarantees → ∃ C K and one admissible program P, chosen before n, Λ, η, δ and ℒ, with these guarantees; reason: Algorithm 1 cannot run verbatim on the machine (its Chebyshev nodes need cos and p_j must be sampled with fair coins); its content is an algorithm with these guarantees, uniform in the parameters, and a program depending on ℒ would make the statement trivial
--   - reading: an algorithm with experiments, evolution time and classical running time (no machine fixed) → the published learner's machine (real RAM with pointer arithmetic, integer memory, fair coin, halt and one Clifford experiment instruction; unit cost except 1 + n + |C₁| + |C₂| per experiment) and an admissible program; reason: the paper's access model (§1.1, p.2) and the base mission's machine; every experiment of Algorithms 1–2 has this form
--   - reading: Õ(g) → C·g·log(2 + g)^K with absolute C, K chosen before every parameter; reason: the paper's notation (p.11), as in the base mission's goal
--   - correction: log(1/δ) in the four bounds → log(2/δ); reason: the printed form fails as δ → 1: n = 1, Λ = 1, η = 1/2, ℒ = −i(1/2)[X, ·] (strength ≤ 1, h_X = 1/2 ≥ η); once the output-size bound C·g·log(2+g)^K with g = 2⁸log⁴(1/δ) is below 1 the output is empty, but 𝒮_H^{≥η} = {X}, so success has probability 0 < 1 − δ; log(2/δ) ≤ 2 log(1/δ) for δ ≤ 1/2
--   - correction: classical running time Õ(nΛ⁸η⁻⁸log⁴(1/δ)) → work at most ⌈C(1 + g_run) log(2 + g_run)^K⌉ and halting within that many steps; reason: at n = 0 the printed bound is 0, but every halting run takes at least one step
--   - reading: the number of experiments, total evolution time and running time → worst-case bounds on every run (every reachable configuration); reason: the stronger reading; the paper's bounds are deterministic
--   - encoding: output size |Ŝ_H| + |Ŝ_D| = Õ(…) deterministically → on every reachable halted configuration, the sum of the cardinalities of the two sets read by decodeSupports is at most C·g_out·log(2 + g_out)^K; reason: the output is a record list on the machine; sets count repeated records once
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Theorem 3.8, p.24 (pdf p.26); Algorithm 1, p.23; Definition 2.7, p.14

import Mathlib
import Definitions.Def_ArbLindbladLearn_Admissible
import Definitions.Def_ArbLindbladLearn_Reach
import Definitions.Def_ArbLindbladLearn_mass
import Definitions.Def_ArbLindbladLearn_Halted
import Definitions.Def_ArbLindbladLearn_initState
import Definitions.Def_ArbLindbladLearn_StrengthLE
import Definitions.Def_ArbLindbladLearn_IsLindbladCoeffs
import Definitions.Def_ArbLindbladLearn_Supplement_heavySupportH
import Definitions.Def_ArbLindbladLearn_Supplement_heavySupportD
import Definitions.Def_ArbLindbladLearn_Supplement_decodeSupports

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker

namespace ArbLindbladLearn.Supplement

open LindbladTolerant.Testing
open ArbLindbladLearn

/-- Theorem 3.8 (Threshold support learning; Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.24). Let `ℒ` be an arbitrary `n`-qubit
Lindbladian satisfying `‖ℒ†‖_{∞→∞} ≤ Λ`, and let `𝒮_H^{≥η}` and `𝒮_D^{≥η}` be the `η`-heavy supports
defined in Definition 2.7. For every `η ∈ (0, Λ]` and `δ ∈ (0, 1)`, Algorithm 1 outputs `Ŝ_H` and
`Ŝ_D` such that, with probability at least `1 − δ`, `𝒮_H^{≥η} ⊆ Ŝ_H` and `𝒮_D^{≥η} ⊆ Ŝ_D`. Moreover,
the output size deterministically satisfies `|Ŝ_H| + |Ŝ_D| = Õ(Λ⁸η⁻⁸ log⁴(1/δ))`. The number of
experiments is `Õ(Λ²/η² log 1/δ)`. The total evolution time is `T_tot = Õ(Λη⁻² log(1/δ))`. The
classical running time is `Õ(nΛ⁸η⁻⁸ log⁴(1/δ))`.

**Formalization Note**
1. The algorithm is one admissible program of the published learner's machine (`Instr`,
   `branches`), chosen with the constants `C, K` before `n, Λ, η, δ` and `ℒ`; it reads
   `n, Λ, η, δ` (published `initState`, with `η` in the accuracy cell) and accesses `ℒ` only through
   the Clifford `experiment` instruction (every experiment of Algorithm 1 is a product Pauli
   eigenstate preparation, `e^{tℒ}`, and a single-qubit Pauli measurement), with
   `evo t = e^{tℒ}`. Its output `(Ŝ_H, Ŝ_D)` is read by `decodeSupports`. Algorithm 1 itself cannot
   be run verbatim on the machine (its nodes need `cos`, and `p_j` must be sampled with fair coins),
   so the statement asserts the existence of a program with Algorithm 1's guarantees.
2. `ℒ = gen c` with `IsLindbladCoeffs c` and `StrengthLE c Λ` (published).
3. `Õ(g)` is read as `C·g·log(2 + g)^K` with absolute `C, K`, and `log(1/δ)` as `log(2/δ)` (the printed
   form fails as `δ → 1`). With `g₁ = (Λ/η)² log(2/δ)`, `g_out = (Λ/η)⁸ log⁴(2/δ)` and
   `g_run = n(Λ/η)⁸ log⁴(2/δ)`: every run halts, with work at most
   `N = ⌈C(1 + g_run) log(2 + g_run)^K⌉`, within `N` steps; every reachable configuration has made at
   most `C·g₁·log(2 + g₁)^K` experiments with total duration at most
   `C(Λ/η²) log(2/δ) log(2 + g₁)^K`; every reachable halted configuration has
   `|Ŝ_H| + |Ŝ_D| ≤ C·g_out·log(2 + g_out)^K`. These bounds hold on every run.
4. With probability (`mass` after `N` steps) at least `1 − δ` the machine has halted with
   `𝒮_H^{≥η} ⊆ Ŝ_H` and `𝒮_D^{≥η} ⊆ Ŝ_D`. -/
theorem theorem_3_8 :
    ∃ C K : ℕ, ∃ P : Program, Admissible P ∧
      ∀ n : ℕ, ∀ Λ η δ : ℝ, 0 < η → η ≤ Λ → 0 < δ → δ < 1 →
      ∀ c : Coeffs n, IsLindbladCoeffs c → StrengthLE c Λ →
        let evo : ℝ → Super (Qubits n) (Qubits n) := fun t => evolution (gen c) t
        let s₀ : MState := initState n Λ η δ
        let g₁ : ℝ := (Λ / η) ^ 2 * Real.log (2 / δ)
        let gOut : ℝ := (Λ / η) ^ 8 * Real.log (2 / δ) ^ 4
        let gRun : ℝ := (n : ℝ) * (Λ / η) ^ 8 * Real.log (2 / δ) ^ 4
        let N : ℕ := ⌈(C : ℝ) * (1 + gRun) * Real.log (2 + gRun) ^ K⌉₊
        (∀ s : MState, Reach P n evo N s₀ s → Halted s ∧ s.work ≤ N) ∧
        ENNReal.ofReal (1 - δ) ≤ mass P n evo N s₀ (fun s => Halted s ∧
          heavySupportH c η ⊆ (decodeSupports n s).1 ∧
          heavySupportD c η ⊆ (decodeSupports n s).2) ∧
        (∀ (M : ℕ) (s : MState), Reach P n evo M s₀ s → Halted s →
          (((decodeSupports n s).1.card + (decodeSupports n s).2.card : ℕ) : ℝ) ≤
            C * gOut * Real.log (2 + gOut) ^ K) ∧
        ∀ (M : ℕ) (s : MState), Reach P n evo M s₀ s →
          (s.durations.length : ℝ) ≤ C * g₁ * Real.log (2 + g₁) ^ K ∧
          s.durations.sum ≤ C * (Λ / η ^ 2) * Real.log (2 / δ) * Real.log (2 + g₁) ^ K := by sorry

end ArbLindbladLearn.Supplement
