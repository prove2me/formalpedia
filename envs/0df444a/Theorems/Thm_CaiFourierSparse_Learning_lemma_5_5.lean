-- Prove2me | Theorems.Thm_CaiFourierSparse_Learning_lemma_5_5
-- name    : CaiFourierSparse.Learning.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:15:44.181789+00:00
-- url     : https://prove2.me/theorems/3895d62f-35cc-4b41-b420-40f03a24a552
-- title:
--   Lemma 5.5 — a sparse FFT in $k\log^{O(1)}(m/\delta)$ time with $\|\hat v-\hat v_o\|_2\le2\|\mathrm{bottom}_k(\hat v)\|_2+\delta\|\hat v\|_2$
-- statement:
--   There is a sparse-FFT program such that for every dimension $m\ge1$, sparsity $k\ge1$, error $\delta>0$ and input $v\in\mathbb C^m$ (accessed by index queries), it runs in time $C\,k\log^e(2+m/\delta)$ on every random tape and outputs a sparse $\hat v_o$ that, with probability at least $1-\frac{0.01}{\log k}$, satisfies
--   $$\|\hat v-\hat v_o\|_2\le2\,\|\mathrm{bottom}_k(\hat v)\|_2+\delta\,\|\hat v\|_2 .$$
--   The constants $C$, $e$ and the program are fixed before $m,k,\delta,v$.
--
--   Differences from the source:
--   - reading: an algorithm with Õ(·) samples and Õ(·) time → a fixed program of the randomized point-query machine (Machine) halting on every random tape within the step bound, with at most that many queries; reason: unit-cost exact complex arithmetic is the reading of the paper's operation counts; worst case over the randomness is the stronger reading
--   - reading: k log^{O(1)}(m/δ) time → C·k·log^e(2 + m/δ) steps; reason: log(m/δ) ≤ 0 when m/δ ≤ 1, where no running-time bound can hold; 2 + m/δ is the standard boundary convention
--   - encoding: with probability 1 − 0.01/log k → stated for k ≥ 2 only; reason: at k = 1 the printed bound 1 − 0.01/0 is undefined (−∞, vacuous); Lean's 0.01/0 = 0 would turn it into probability 1
--   - reading: log k in the failure probability → log₂ k; reason: the base is not printed; 0.01/log₂ k ≤ 0.01/ln k, so base 2 is the stronger claim
--   - encoding: outputs a sparse v̂_o → the output is a list of (index, value) pairs describing v̂_o; its length is at most the step bound; reason: 'sparse' is not quantified on the page; each output entry costs a step
--   - encoding: any error δ → δ > 0; reason: a nonpositive error is meaningless
--   - encoding: with probability p → ProbAtLeast: a measurable event of tape-probability ≥ p inside the success event; reason: inner probability; the success event of a real-RAM run need not be measurable a priori
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), Lemma 5.5, printed p. 27 (PDF p. 29)

import Mathlib
import Definitions.Def_CaiFourierSparse_Learning_Signal
import Definitions.Def_CaiFourierSparse_Learning_HaarFourier
import Definitions.Def_CaiFourierSparse_Learning_Machine
import Definitions.Def_CaiFourierSparse_Learning_SparseFFT

namespace CaiFourierSparse.Learning

/-- Lemma 5.5 (printed p. 27, PDF p. 29). There is a sparse-FFT program: run on the inputs
`(m, k, δ)` with query access to the entries of any `v ∈ ℂ^m`, on every random tape it halts
within `C · k · log^e(2 + m/δ)` steps (so with at most that many queries and output entries),
and with probability at least `1 - 0.01/log k` its output, a sparse `v̂_o ∈ ℂ^m` given by
(index, value) pairs, satisfies `‖v̂ - v̂_o‖₂ ≤ 2 ‖bottom_k(v̂)‖₂ + δ ‖v̂‖₂`. The exponent `e` and
the constant `C` are universal. -/
theorem lemma_5_5 :
    ∃ (e : ℕ) (C : ℝ) (P : Program), 0 < C ∧
      ∀ (m k : ℕ) (δ : ℝ), 1 ≤ m → 1 ≤ k → 0 < δ → ∀ v : Fin m → ℂ,
        let T := C * k * Real.log (2 + m / δ) ^ e
        (∀ ω : Tape, HaltsWith P (vecDomain m) (vecOracle v) ω [(m : ℂ), (k : ℂ), (δ : ℂ)] T T
          (fun _ => True)) ∧
        (2 ≤ k → ProbAtLeast tapeLaw
          {ω | OutputSatisfies P (vecDomain m) (vecOracle v) ω [(m : ℂ), (k : ℂ), (δ : ℂ)]
            (fun out => ∃ L : List (Fin m × ℂ), out = encSparse L ∧
              l2norm (fun j => dft v j - sparseVec L j) ≤
                2 * Real.sqrt (bottomSq (dft v) Finset.univ k) + δ * l2norm (dft v))}
          (1 - 0.01 / Real.logb 2 k)) := by sorry

end CaiFourierSparse.Learning
