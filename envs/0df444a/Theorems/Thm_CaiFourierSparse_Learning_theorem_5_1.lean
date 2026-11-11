-- Prove2me | Theorems.Thm_CaiFourierSparse_Learning_theorem_5_1
-- name    : CaiFourierSparse.Learning.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:17:33.669919+00:00
-- url     : https://prove2.me/theorems/493255f0-cb29-49b4-aefa-dc363c72a599
-- title:
--   Theorem 5.1 — improper learning: $\tilde O(k/\varepsilon^2)$ samples and time, $\|\tilde x-x\|^2\le O(\varepsilon)\|x\|^2+O(1)\|\eta\|^2$ with probability 0.9
-- statement:
--   There is a randomized point-query program (Algorithm 1, ImproperLearning) such that for every bandlimit $F\ge0$, sparsity $k\ge1$, error $\varepsilon>0$, $k$-Fourier-sparse $x$ with frequencies in $[-F,F]$ and noise $\eta$, run on $(F,k,\varepsilon)$ with point queries to $y=x+\eta$ on $[-1,1]$, it uses $\tilde O(k/\varepsilon^2)$ samples and $\tilde O(k/\varepsilon^2)$ time and reconstructs $\tilde x=\sum_H\tilde a_H\varphi_H$ in the Haar–Fourier basis $\mathcal B$ with $\tilde O(k/\varepsilon)$ terms, such that with probability $0.9$
--   $$\|\tilde x-x\|^2_{[-1,1]}\le C_1\varepsilon\|x\|^2_{[-1,1]}+C_2\|\eta\|^2_{[-1,1]} .$$
--   All constants and the program are fixed before $F,k,\varepsilon,x,\eta$ and the randomness.
--
--   Differences from the source:
--   - reading: Algorithm 1 reconstructs x̃ … in Õ(k/ε²) samples and time → there exists a program of the randomized point-query machine with these guarantees; reason: Algorithm 1 calls a sparse-FFT subroutine that the page does not specify (Lemma 5.5, obtained by 'adjusting parameters' of [HIKP12]), so the page does not determine one program; the cost model is explicit and the program sees only (F, k, ε) and its query answers
--   - reading: an algorithm with Õ(·) samples and Õ(·) time → a fixed program of the randomized point-query machine (Machine) halting on every random tape within the step bound, with at most that many queries; reason: unit-cost exact complex arithmetic is the reading of the paper's operation counts; worst case over the randomness is the stronger reading
--   - reading: Õ(g), which hides (log(kF/ε))^{O(1)} factors (footnote 1) → A · g · log^e(2 + kF/ε) with A > 0 and e ∈ ℕ fixed before all inputs; reason: the printed polylog factor is zero or negative for kF/ε ≤ 1 (F = 0 is admissible), where no cost or size bound can hold; 2 + kF/ε is the standard boundary convention and agrees asymptotically
--   - encoding: x̃ := Σ_H ã_H φ_H in B of sparsity Õ(k/ε) → output encHF b a terms with ValidHF (N = 2^b ≥ 2F, K = 2^a ≥ k, K | 2N, each H once) and at most Õ(k/ε) terms on every tape; reason: Lean representation of the output
--   - encoding: = O(ε)·‖x‖² + O(1)·‖η‖² → ≤ C₁ε‖x‖² + C₂‖η‖² (energies in ℝ≥0∞); reason: an O-bound is an upper bound with universal constants
--   - encoding: noise η with bounded window L² norm → IsNoise η: a.e.-measurable on the window with finite window energy; y = x + η is queried pointwise; reason: point queries need a function, not an L² class; this is every noise the source allows
--   - encoding: with probability p → ProbAtLeast: a measurable event of tape-probability ≥ p inside the success event; reason: inner probability; the success event of a real-RAM run need not be measurable a priori
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), Theorem 5.1, printed p. 24 (PDF p. 26)

import Mathlib
import Definitions.Def_CaiFourierSparse_Learning_Signal
import Definitions.Def_CaiFourierSparse_Learning_HaarFourier
import Definitions.Def_CaiFourierSparse_Learning_Machine
import Definitions.Def_CaiFourierSparse_Learning_Cover

namespace CaiFourierSparse.Learning

/-- Theorem 5.1 (printed p. 24, PDF p. 26). There is a randomized point-query program
(`ImproperLearning`, Algorithm 1) such that, for every bandlimit `F ≥ 0`, sparsity `k ≥ 1`, error
`ε > 0`, `k`-Fourier-sparse `x` with frequencies in `[-F, F]` and noise `η` of finite window
energy, run on the inputs `(F, k, ε)` with point queries to `y = x + η` on `[-1, 1]`:
on every random tape it halts within `Õ(k/ε²)` steps and queries and outputs a Haar–Fourier
expansion `x̃ = ∑_H β_H φ_H` in the basis `B` with `Õ(k/ε)` terms; and with probability at least
`0.9`, `‖x̃ - x‖²_{[-1,1]} ≤ C₁ ε ‖x‖²_{[-1,1]} + C₂ ‖η‖²_{[-1,1]}`. Here `Õ(g)` is
`A · g · log^e(2 + kF/ε)`; `e, A, C₁, C₂` and the program are fixed before all inputs. -/
theorem theorem_5_1 :
    ∃ (e : ℕ) (A C₁ C₂ : ℝ) (P : Program), 0 < A ∧ 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (F ε : ℝ) (k : ℕ) (α : Fin k → ℂ) (f : Fin k → ℝ) (η : ℝ → ℂ),
        0 ≤ F → 0 < ε → 1 ≤ k → Bandlimited F f → IsNoise η →
        let x := sparseSignal α f
        let y : ℝ → ℂ := fun t => x t + η t
        let pl := Real.log (2 + k * F / ε) ^ e
        let input : List ℂ := [(F : ℂ), (k : ℂ), (ε : ℂ)]
        (∀ ω : Tape, HaltsWith P window y ω input (A * (k / ε ^ 2) * pl) (A * (k / ε ^ 2) * pl)
          (fun out => ∃ (b a : ℕ) (terms : List (HaarIdx × ℂ)), out = encHF b a terms ∧
            ValidHF k F b a terms ∧ (terms.length : ℝ) ≤ A * (k / ε) * pl)) ∧
        ProbAtLeast tapeLaw
          {ω | OutputSatisfies P window y ω input
            (fun out => ∃ (b a : ℕ) (terms : List (HaarIdx × ℂ)), out = encHF b a terms ∧
              wsq (fun t => hfSum b a terms t - x t) ≤
                ENNReal.ofReal (C₁ * ε) * wsq x + ENNReal.ofReal C₂ * wsq η)}
          0.9 := by sorry

end CaiFourierSparse.Learning
