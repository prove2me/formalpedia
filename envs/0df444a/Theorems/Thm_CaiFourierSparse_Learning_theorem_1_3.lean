-- Prove2me | Theorems.Thm_CaiFourierSparse_Learning_theorem_1_3
-- name    : CaiFourierSparse.Learning.theorem_1_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:17:36.694788+00:00
-- url     : https://prove2.me/theorems/5167c231-9188-4148-a1f9-832878bfad53
-- title:
--   Theorem 1.3 — nearly-linear frequency recovery and reconstruction of Fourier-sparse signals (at the strength of Theorems 5.1 and 8.1)
-- statement:
--   There is one randomized point-query algorithm such that, for every bandlimit $F\ge0$, sparsity $k\ge1$, error $0<\varepsilon\le1/2$ and every noisy observation $y=x+\eta$ of $x(t)=\sum_{j=1}^k\alpha_je^{2\pi if_jt}$ ($|f_j|\le F$) with noise $\eta$, it uses $\tilde O(k/\varepsilon^2)$ samples and time and outputs
--   1. a list $L$ of $\tilde O(k/\varepsilon^2)$ frequencies with error $O(k)$ for most of the frequencies of $x$: with high probability, for $x$'s clusters (Algorithm 2), the clusters all of whose frequencies lie within $B\cdot k$ of $L$ carry all but $O(\varepsilon)\|x\|^2+O(1)\|\eta\|^2$ of the energy,
--   $$\Big\|x-\sum_{C_j\text{ covered by }L}x_{C_j}\Big\|^2_{[-1,1]}\le C_1\varepsilon\|x\|^2_{[-1,1]}+C_2\|\eta\|^2_{[-1,1]};$$
--   2. a reconstruction $\tilde x$, a Haar–Fourier expansion with $\tilde O(k/\varepsilon)$ terms, such that with probability $0.9$
--   $$\|\tilde x-x\|^2_{[-1,1]}\le C_3\varepsilon\|x\|^2_{[-1,1]}+C_4\|\eta\|^2_{[-1,1]} .$$
--   For constant $\varepsilon$ the counts are $\tilde O(k)$, as in the printed statement.
--
--   Differences from the source:
--   - generalization: a small constant ε, with Õ(k) samples, time and list size → every ε ∈ (0, 1/2] with explicit dependence: Õ(k/ε²) samples and time, |L| = Õ(k/ε²), and one program uniform in ε; reason: for any fixed ε these are Õ(k), so the Lean statement specializes to the printed one (Theorems 5.1 and 8.1 give these ε-dependences)
--   - generalization: a reconstruction x̃ → x̃ is output as a Haar–Fourier expansion in B with Õ(k/ε) terms (the form of Theorem 5.1); reason: an added conclusion; forgetting it gives the printed clause
--   - reading: for most of the frequencies f_j of x, ∃ f̃ ∈ L with |f_j − f̃| ≤ O(k) → the clusters of Algorithm 2 all of whose frequencies are within B·k of L carry all but C₁ε‖x‖² + C₂‖η‖² of the window energy, for every merge order and every even filter constant C ≥ 64; reason: the paper's own reading (§1.1 remark, (9), Theorem 8.1): cancelling frequencies cannot all be recovered, so 'most' is an energy statement about whole clusters, not a count of tones
--   - reading: no success probability printed → clause (2) with probability ≥ 0.9 (Theorem 5.1) and clause (1) with high probability (Theorem 8.1, whpBound), on the same run of the same program; reason: the formal counterparts' probabilities
--   - reading: an algorithm with Õ(·) samples and Õ(·) time → a fixed program of the randomized point-query machine (Machine) halting on every random tape within the step bound, with at most that many queries; reason: unit-cost exact complex arithmetic is the reading of the paper's operation counts; worst case over the randomness is the stronger reading
--   - reading: Õ(g), which hides (log(kF/ε))^{O(1)} factors (footnote 1) → A · g · log^e(2 + kF/ε) with A > 0 and e ∈ ℕ fixed before all inputs; reason: the printed polylog factor is zero or negative for kF/ε ≤ 1 (F = 0 is admissible), where no cost or size bound can hold; 2 + kF/ε is the standard boundary convention and agrees asymptotically
--   - encoding: any F, sparsity k → F ≥ 0, k ≥ 1, and ε ≤ 1/2; reason: the clusters (via M_{k,ε}, Δ_{k,ε}) are defined for 0 < ε ≤ 1/2; 'small constant ε'
--   - encoding: noise η with bounded window L² norm → IsNoise η: a.e.-measurable on the window with finite window energy; y = x + η is queried pointwise; reason: point queries need a function, not an L² class; this is every noise the source allows
--   - encoding: with probability p → ProbAtLeast: a measurable event of tape-probability ≥ p inside the success event; reason: inner probability; the success event of a real-RAM run need not be measurable a priori
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), Theorem 1.3, printed p. 2 (PDF p. 4)

import Mathlib
import Definitions.Def_CaiFourierSparse_Learning_Signal
import Definitions.Def_CaiFourierSparse_Learning_HaarFourier
import Definitions.Def_CaiFourierSparse_Learning_Machine
import Definitions.Def_CaiFourierSparse_Learning_Filter
import Definitions.Def_CaiFourierSparse_Learning_Clusters
import Definitions.Def_CaiFourierSparse_Learning_Cover

namespace CaiFourierSparse.Learning

open Classical in
/-- Theorem 1.3 (printed p. 2, PDF p. 4), at the strength of Theorems 5.1 and 8.1. There is one
randomized point-query program such that, for every bandlimit `F ≥ 0`, sparsity `k ≥ 1`, error
`0 < ε ≤ 1/2`, hidden `k`-Fourier-sparse `x = ∑_j α_j e^{2π i f_j t}` with `|f_j| ≤ F` and noise
`η` of finite window energy, run on `(F, k, ε)` with point queries to `y = x + η` on `[-1,1]`:
on every random tape it halts within `Õ(k/ε²)` steps and queries and outputs a reconstruction
`x̃`, a Haar–Fourier expansion with `Õ(k/ε)` terms, and a list `L` of `Õ(k/ε²)` frequencies;
(2) with probability at least `0.9`,
`‖x̃ - x‖²_{[-1,1]} ≤ O(ε) ‖x‖²_{[-1,1]} + O(1) ‖η‖²_{[-1,1]}`;
(1) for every filter constant `C ≥ 64` (even) defining the clusters, with high probability,
for every output of Algorithm 2 (x's clusters), the clusters all of whose frequencies lie within `B · k` of `L`
carry all but `O(ε) ‖x‖² + O(1) ‖η‖²` of the window energy:
`‖x - ∑_{C_j covered} x_{C_j}‖²_{[-1,1]} ≤ O(ε) ‖x‖²_{[-1,1]} + O(1) ‖η‖²_{[-1,1]}`.
`Õ(g)` is `A · g · log^e(2 + kF/ε)`; "with high probability" is `whpBound` with exponent
`a₀ > 0`, threshold `n₀` and floor `p₀ > 0`. All constants are fixed before the inputs. -/
theorem theorem_1_3 :
    ∃ (e : ℕ) (A : ℝ) (P : Program), 0 < A ∧
      ∀ C : ℕ, Even C → 64 ≤ C →
        ∃ (B C₁ C₂ C₃ C₄ a₀ n₀ p₀ : ℝ), 0 < B ∧ 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ 0 < C₄ ∧
          0 < a₀ ∧ 0 < p₀ ∧
          ∀ (F ε : ℝ) (k : ℕ) (α : Fin k → ℂ) (f : Fin k → ℝ) (η : ℝ → ℂ),
            0 ≤ F → 0 < ε → ε ≤ 1 / 2 → 1 ≤ k → Bandlimited F f → IsNoise η →
            let x := sparseSignal α f
            let y : ℝ → ℂ := fun t => x t + η t
            let pl := Real.log (2 + k * F / ε) ^ e
            let input : List ℂ := [(F : ℂ), (k : ℂ), (ε : ℂ)]
            (∀ ω : Tape, HaltsWith P window y ω input (A * (k / ε ^ 2) * pl) (A * (k / ε ^ 2) * pl)
              (fun out => ∃ (b a : ℕ) (terms : List (HaarIdx × ℂ)) (L : List ℝ),
                out = encHF b a terms ++ encFreqs L ∧ ValidHF k F b a terms ∧
                (terms.length : ℝ) ≤ A * (k / ε) * pl ∧ (L.length : ℝ) ≤ A * (k / ε ^ 2) * pl)) ∧
            ProbAtLeast tapeLaw
              {ω | OutputSatisfies P window y ω input
                (fun out => ∃ (b a : ℕ) (terms : List (HaarIdx × ℂ)) (L : List ℝ),
                  out = encHF b a terms ++ encFreqs L ∧
                  wsq (fun t => hfSum b a terms t - x t) ≤
                    ENNReal.ofReal (C₃ * ε) * wsq x + ENNReal.ofReal C₄ * wsq η)}
              0.9 ∧
            ProbAtLeast tapeLaw
              {ω | OutputSatisfies P window y ω input
                (fun out => ∃ (b a : ℕ) (terms : List (HaarIdx × ℂ)) (L : List ℝ),
                  out = encHF b a terms ++ encFreqs L ∧
                  ∀ Pc : Finset (Finset (Fin k)), IsAlg2Output C ε f Pc →
                    wsq (fun t => x t - ∑ D ∈ Pc.filter
                        (fun D => ∀ j ∈ D, ∃ g ∈ L, |f j - g| ≤ B * k), subSignal α f D t) ≤
                      ENNReal.ofReal (C₁ * ε) * wsq x + ENNReal.ofReal C₂ * wsq η)}
              (whpBound a₀ n₀ p₀ (k * F / ε)) := by sorry

end CaiFourierSparse.Learning
