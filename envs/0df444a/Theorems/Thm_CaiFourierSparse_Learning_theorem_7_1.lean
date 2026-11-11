-- Prove2me | Theorems.Thm_CaiFourierSparse_Learning_theorem_7_1
-- name    : CaiFourierSparse.Learning.theorem_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:16:40.750202+00:00
-- url     : https://prove2.me/theorems/33876d3b-e1a3-4322-8fe2-f99b41b3496b
-- title:
--   Theorem 7.1 — every $k$-Fourier-sparse signal has a multiband approximation with at most $k$ bands of total length $\tilde O(k^2/\varepsilon)$
-- statement:
--   For every $k$-Fourier-sparse $x(t)=\sum_{j=1}^k\alpha_je^{2\pi if_jt}$ and every $\varepsilon>0$ there is a multiband signal $x'$ such that
--   1. $\|x'\|^2_{[-1,1]}\ge(1-\varepsilon)\|x'\|_2^2$;
--   2. $\|x-x'\|^2_{[-1,1]}\le\varepsilon\|x\|^2_{[-1,1]}$;
--   3. $\operatorname{supp}(\widehat{x'})\subseteq I_1\cup\dots\cup I_n$ with $n\le k$ and $|I_1|+\dots+|I_n|=\tilde O(k^2/\varepsilon)$.
--
--   Differences from the source:
--   - reading: Õ(g) (footnote 1) → A · g · log^e(2 + k/ε) with A > 0 and e ∈ ℕ fixed before all inputs; reason: the statement involves no bandlimit, so the polylog factor is taken in k/ε only (the stronger choice); 2 + k/ε keeps the factor positive at the smallest parameters
--   - encoding: multiband signal x′ with supp(x̂′) ⊆ I₁ ∪ ⋯ ∪ Iₙ → x′ ∈ L²(ℝ) whose L² Fourier transform vanishes a.e. outside the union of the closed bands (IsMultiband); bands as endpoint pairs (L ≤ R), |I| = R − L; reason: Lean representation; the paper's multiband signals are L² with spectrum in finitely many intervals (§1)
--   - encoding: squared L² norms → ℝ≥0∞-valued lower integrals wsq/lsq/osq, real coefficients through ENNReal.ofReal; reason: non-square-integrable functions get energy ∞, so no bound holds through a junk value
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), Theorem 7.1, printed p. 34 (PDF p. 36)

import Mathlib
import Definitions.Def_CaiFourierSparse_Learning_Signal
import Definitions.Def_CaiFourierSparse_Learning_Clusters

namespace CaiFourierSparse.Learning

/-- Theorem 7.1 (printed p. 34, PDF p. 36). For every `k`-Fourier-sparse `x` and every `ε > 0`
there is a multiband signal `x'` (in `L²(ℝ)`, Fourier transform supported in bands
`I_1 ∪ ⋯ ∪ I_n`) such that
(1) `‖x'‖²_{[-1,1]} ≥ (1 - ε) ‖x'‖²₂`;
(2) `‖x - x'‖²_{[-1,1]} ≤ ε ‖x‖²_{[-1,1]}`;
(3) `n ≤ k` and `|I_1| + ⋯ + |I_n| = Õ(k²/ε)`, where `Õ(g)` is `A · g · log^e(2 + k/ε)`. -/
theorem theorem_7_1 :
    ∃ (A : ℝ) (e : ℕ), 0 < A ∧
      ∀ (k : ℕ) (ε : ℝ), 1 ≤ k → 0 < ε → ∀ (α : Fin k → ℂ) (f : Fin k → ℝ),
        ∃ (x' : ℝ → ℂ) (bands : List (ℝ × ℝ)),
          IsMultiband x' bands ∧
          ENNReal.ofReal (1 - ε) * lsq x' ≤ wsq x' ∧
          wsq (fun t => sparseSignal α f t - x' t) ≤ ENNReal.ofReal ε * wsq (sparseSignal α f) ∧
          bands.length ≤ k ∧ (∀ I ∈ bands, I.1 ≤ I.2) ∧
          (bands.map fun I => I.2 - I.1).sum ≤ A * ((k : ℝ) ^ 2 / ε) * Real.log (2 + k / ε) ^ e := by sorry

end CaiFourierSparse.Learning
