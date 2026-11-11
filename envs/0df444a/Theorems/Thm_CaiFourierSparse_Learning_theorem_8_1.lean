-- Prove2me | Theorems.Thm_CaiFourierSparse_Learning_theorem_8_1
-- name    : CaiFourierSparse.Learning.theorem_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:17:42.429399+00:00
-- url     : https://prove2.me/theorems/c303b6cb-7482-4746-ad41-988f1795c5ba
-- title:
--   Theorem 8.1 — Algorithm 3 covers the principal frequency clusters: short cover $I'$, and the uncovered clusters carry $O(\varepsilon)\|x\|^2+O(1)\|\eta\|^2$
-- statement:
--   For every sufficiently small constant $c>0$ of Algorithm 3 there is a randomized point-query program (FrequenciesCover) such that for every $F\ge0$, $k\ge1$, $0<\varepsilon\le1/2$, $k$-Fourier-sparse $x$ with frequencies in $[-F,F]$ and noise $\eta$, run on $(F,k,\varepsilon)$ with point queries to $y=x+\eta$: it uses $\tilde O(k/\varepsilon^2)$ samples and time and outputs the expansion $\tilde x$ of ImproperLearning and the multiband $I'=\bigcup_{r=1}^{n'}I'_r$ computed from it by Algorithm 3 with $n'=\tilde O(k/\varepsilon)$, such that w.h.p., for $x$'s clusters $C_1,\dots,C_n$,
--   $$|I'|\le O\Big(\frac{k^2\log^{5/2}(k/\varepsilon)\log^2F}{\varepsilon^2}\Big)\quad\text{and}\quad\Big\|x-\sum_{C_j:\operatorname{range}(C_j)\subset I'}x_{C_j}\Big\|^2_{[-1,1]}\le O(\varepsilon)\|x\|^2_{[-1,1]}+O(1)\|\eta\|^2_{[-1,1]}\qquad\text{(eq. (80))},$$
--   and in particular $\|\sum_{C_j:\operatorname{range}(C_j)\not\subset I'}x_{C_j}\|^2_{[-1,1]}\le O(\varepsilon)\|x\|^2_{[-1,1]}+O(1)\|\eta\|^2_{[-1,1]}$. The bound $\log^2F$ and "w.h.p." are stated as printed (INSIGHTS I3, I4).
--
--   Differences from the source:
--   - reading: Algorithm 3 (which runs ImproperLearning, Algorithm 1) → there exists a program of the randomized point-query machine whose output is a Haar–Fourier expansion x̃ in B together with I′ = alg3Cover c ε k b a x̃, the printed post-processing of Algorithm 3 applied to that x̃; reason: ImproperLearning's sparse-FFT subroutine is not specified by the page (as in Theorem 5.1); Algorithm 3's own steps (regions, merging, τ, scans) are pinned exactly
--   - reading: for a sufficiently small constant c > 0 (in τ) → there is c₀ > 0 such that the statement holds for every c ∈ (0, c₀]; reason: 'sufficiently small' read as every small enough c, the stronger reading
--   - reading: w.h.p. (undefined in the paper) → probability ≥ 1 − (2 + kF/ε)^{−a₀} when kF/ε ≥ n₀ and ≥ p₀ > 0 otherwise (whpBound), with a₀, n₀, p₀ fixed before the inputs; reason: the planning reading of the brief; it is not downgraded to 0.9 (INSIGHTS I3)
--   - reading: an algorithm with Õ(·) samples and Õ(·) time → a fixed program of the randomized point-query machine (Machine) halting on every random tape within the step bound, with at most that many queries; reason: unit-cost exact complex arithmetic is the reading of the paper's operation counts; worst case over the randomness is the stronger reading
--   - reading: Õ(g), which hides (log(kF/ε))^{O(1)} factors (footnote 1) → A · g · log^e(2 + kF/ε) with A > 0 and e ∈ ℕ fixed before all inputs; reason: the printed polylog factor is zero or negative for kF/ε ≤ 1 (F = 0 is admissible), where no cost or size bound can hold; 2 + kF/ε is the standard boundary convention and agrees asymptotically
--   - encoding: error ε (any) → 0 < ε ≤ 1/2; reason: the filter M_{k,ε} and Δ_{k,ε}, hence the clusters, are built under the section's standing assumption 0 < δ ≤ 1/2 (Claim 6.5, Lemma 6.1); it excludes only parameters for which these objects are not defined by the paper
--   - encoding: |I′| ≤ O(k² log^{5/2}(k/ε) log² F/ε²) for every F → the same bound for F > 0; no |I′| clause at F = 0; reason: log² F is undefined at F = 0 (in real analysis it diverges, so the printed bound is vacuous there); Lean's log 0 = 0 would make it a false bound 0. At F = 1 the bound is stated as printed (INSIGHTS I4)
--   - reading: x's clusters C₁, …, Cₙ → every output of Algorithm 2 under every merge order, for every even filter constant C ≥ 64 (constants after C); reason: the page fixes neither the merge order nor C beyond C ≥ 64 even
--   - encoding: range(C_j) ⊂ I′ → [min_{C_j} f, max_{C_j} f] ⊆ ⋃_i [L_i, R_i]; reason: inclusion of the closed range in the union
--   - encoding: O(·) bounds → constants C₀, C₁, C₂ > 0 fixed before the inputs; reason: universal O-constants
--   - encoding: noise η with bounded window L² norm → IsNoise η: a.e.-measurable on the window with finite window energy; y = x + η is queried pointwise; reason: point queries need a function, not an L² class; this is every noise the source allows
--   - encoding: with probability p → ProbAtLeast: a measurable event of tape-probability ≥ p inside the success event; reason: inner probability; the success event of a real-RAM run need not be measurable a priori
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), Theorem 8.1, printed p. 40 (PDF p. 42)

import Mathlib
import Definitions.Def_CaiFourierSparse_Learning_Signal
import Definitions.Def_CaiFourierSparse_Learning_HaarFourier
import Definitions.Def_CaiFourierSparse_Learning_Machine
import Definitions.Def_CaiFourierSparse_Learning_Filter
import Definitions.Def_CaiFourierSparse_Learning_Clusters
import Definitions.Def_CaiFourierSparse_Learning_Cover

namespace CaiFourierSparse.Learning

open MeasureTheory

open Classical in
/-- Theorem 8.1 (printed p. 40, PDF p. 42), with (80) as printed (`log² F`). For every
sufficiently small constant `c > 0` of Algorithm 3 there is a randomized point-query program
(`FrequenciesCover`) such that, for every `F ≥ 0`, `k ≥ 1`, `0 < ε ≤ 1/2`, `k`-Fourier-sparse `x`
with frequencies in `[-F, F]` and noise `η`, run on `(F, k, ε)` with point queries to
`y = x + η` on `[-1, 1]`: on every random tape it halts within `Õ(k/ε²)` steps and queries and
outputs a Haar–Fourier expansion `x̃` (from `ImproperLearning`) and the multiband
`I' = ⋃_{r ≤ n'} I'_r` obtained from it by Algorithm 3 (regions, merging, `τ` with constant
`c`, forward and backward scans), with `n' = Õ(k/ε)`; and, for every filter constant `C ≥ 64`
(even) defining the clusters, with high probability `|I'| ≤ O(k² log^{5/2}(k/ε) log² F / ε²)`
(for `F > 0`; at `F = 0` the printed `log² F` is undefined) and, for every output
`C_1, …, C_n` of Algorithm 2 (x's clusters),
`‖x - ∑_{range(C_j) ⊆ I'} x_{C_j}‖²_{[-1,1]} ≤ O(ε) ‖x‖²_{[-1,1]} + O(1) ‖η‖²_{[-1,1]}`, and
`‖∑_{range(C_j) ⊄ I'} x_{C_j}‖²_{[-1,1]} ≤ O(ε) ‖x‖²_{[-1,1]} + O(1) ‖η‖²_{[-1,1]}`.
"With high probability" is read as: probability at least `1 - (2 + kF/ε)^{-a}` when
`kF/ε ≥ n₀`, and at least `p₀ > 0` otherwise (`whpBound`). `Õ(g)` is `A · g · log^e(2 + kF/ε)`. -/
theorem theorem_8_1 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∃ (e : ℕ) (A : ℝ) (P : Program), 0 < A ∧
        ∀ C : ℕ, Even C → 64 ≤ C →
          ∃ (C₀ C₁ C₂ a₀ n₀ p₀ : ℝ), 0 < C₀ ∧ 0 < C₁ ∧ 0 < C₂ ∧ 0 < a₀ ∧ 0 < p₀ ∧
            ∀ (F ε : ℝ) (k : ℕ) (α : Fin k → ℂ) (f : Fin k → ℝ) (η : ℝ → ℂ),
              0 ≤ F → 0 < ε → ε ≤ 1 / 2 → 1 ≤ k → Bandlimited F f → IsNoise η →
              let x := sparseSignal α f
              let y : ℝ → ℂ := fun t => x t + η t
              let pl := Real.log (2 + k * F / ε) ^ e
              let input : List ℂ := [(F : ℂ), (k : ℂ), (ε : ℂ)]
              (∀ ω : Tape, HaltsWith P window y ω input (A * (k / ε ^ 2) * pl)
                (A * (k / ε ^ 2) * pl)
                (fun out => ∃ (b a : ℕ) (terms : List (HaarIdx × ℂ)) (I : List (ℝ × ℝ)),
                  out = encHF b a terms ++ encIv I ∧ ValidHF k F b a terms ∧
                  alg3Cover c ε k b a terms = some I ∧ (I.length : ℝ) ≤ A * (k / ε) * pl)) ∧
              ProbAtLeast tapeLaw
                {ω | OutputSatisfies P window y ω input
                  (fun out => ∃ (b a : ℕ) (terms : List (HaarIdx × ℂ)) (I : List (ℝ × ℝ)),
                    out = encHF b a terms ++ encIv I ∧
                    (0 < F → volume (ivUnion I) ≤ ENNReal.ofReal (C₀ * (k : ℝ) ^ 2 *
                      Real.log ((k : ℝ) / ε) ^ (5 / 2 : ℝ) * Real.log F ^ 2 / ε ^ 2)) ∧
                    ∀ Pc : Finset (Finset (Fin k)), IsAlg2Output C ε f Pc →
                      wsq (fun t => x t - ∑ B ∈ Pc.filter
                          (fun B => Set.Icc (cLo f B) (cHi f B) ⊆ ivUnion I), subSignal α f B t) ≤
                        ENNReal.ofReal (C₁ * ε) * wsq x + ENNReal.ofReal C₂ * wsq η ∧
                      wsq (fun t => ∑ B ∈ Pc.filter
                          (fun B => ¬ Set.Icc (cLo f B) (cHi f B) ⊆ ivUnion I), subSignal α f B t) ≤
                        ENNReal.ofReal (C₁ * ε) * wsq x + ENNReal.ofReal C₂ * wsq η)}
                (whpBound a₀ n₀ p₀ (k * F / ε)) := by sorry

end CaiFourierSparse.Learning
