-- Prove2me | Theorems.Thm_ArbLindbladLearn_fact_2_7
-- name    : ArbLindbladLearn.fact_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:22:28.522518+00:00
-- url     : https://prove2.me/theorems/d8149816-6301-4b79-a653-a26123c28634
-- title:
--   Fact 2.7 — median-of-means bound
-- statement:
--   Let $X_1,\dots,X_N$ be i.i.d. real random variables with mean $\mu$ and $\mathbb E[X_1^2]\le\sigma^2$, let $\eta>0$ and $\delta\in(0,1)$. Partition $[N]$ into $K=\lceil8\log(1/\delta)\rceil$ batches of equal size $m$ and let $\hat\mu$ be the median of the $K$ batch means. If $N\ge K\lceil4\sigma^2/\eta^2\rceil$, then
--   $$\Pr\big[|\hat\mu-\mu|>\eta\big]\le\delta .$$
--   In particular, $N=O(\sigma^2\eta^{-2}\log(1/\delta))$ samples suffice: $K\lceil4\sigma^2/\eta^2\rceil\le(8\log(1/\delta)+1)(4\sigma^2/\eta^2+1)$.
--
--   Algorithm 2 applies it with $\sigma^2=160$ to every node of every witness.
--
--   Differences from the source:
--   - encoding: N samples partitioned into K batches of equal size with N ≥ K⌈4σ²/η²⌉ → N = K·m with m ≥ ⌈4σ²/η²⌉, batch k = indices km, …, km + m − 1; reason: equal batch sizes force N = Km; same condition
--   - reading: the median of the K batch means → the lower median; reason: K may be even; any value between the two middle ones satisfies the bound
--   - encoding: E[X₁²] ≤ σ² → X₁ ∈ L² and ∫ X₁² ≤ σ²; reason: the hypothesis presupposes a finite second moment; it excludes only undefined cases
--   - reading: N = O(σ²η⁻² log(1/δ)) samples suffice → K⌈4σ²/η²⌉ ≤ (8 log(1/δ) + 1)(4σ²/η² + 1); reason: explicit form of the O-clause; the +1 terms are needed when σ²/η² or log(1/δ) is small
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Fact 2.7, p.17 [JVV86]

import Mathlib
import Definitions.Def_ArbLindbladLearn_lowerMedian

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker

namespace ArbLindbladLearn



/-- Fact 2.7 (Median-of-means bound; see, e.g., [JVV86]; Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.17). Let
`X₁, …, X_N` be i.i.d. real random variables with mean `μ` and `E[X₁²] ≤ σ²`. Partition `[N]` into
`K = ⌈8 log(1/δ)⌉` batches of equal size, and let `μ̂` be the median of the `K` batch means. If
`N ≥ K⌈4σ²/η²⌉`, then `Pr[|μ̂ − μ| > η] ≤ δ`. In particular, `N = O(σ²η⁻² log(1/δ))` samples
suffice to achieve accuracy `η` with failure probability `δ`.

**Formalization Note** The samples are `X 0, …, X (N−1)` on a probability space; only these are
assumed independent and identically distributed. Batches of equal size `m` give `N = Km`, so
`N ≥ K⌈4σ²/η²⌉` is `m ≥ ⌈4σ²/η²⌉`; batch `k` holds the indices `km, …, km + m − 1` and the median is
the lower median (`batchMedian`). `E[X₁²]` is finite (`MemLp _ 2`), as the hypothesis
`E[X₁²] ≤ σ²` requires. `η > 0` and `δ ∈ (0, 1)`. The "In particular" clause is the explicit count
`K⌈4σ²/η²⌉ ≤ (8 log(1/δ) + 1)(4σ²/η² + 1)`. -/
theorem fact_2_7 {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (μ σ η δ : ℝ) (m : ℕ)
    (hind : ProbabilityTheory.iIndepFun
      (fun i : Fin (⌈8 * Real.log (1 / δ)⌉₊ * m) => X i) P)
    (hid : ∀ i < ⌈8 * Real.log (1 / δ)⌉₊ * m, ProbabilityTheory.IdentDistrib (X i) (X 0) P P)
    (hL2 : MeasureTheory.MemLp (X 0) 2 P) (hμ : ∫ ω, X 0 ω ∂P = μ)
    (hσ : ∫ ω, X 0 ω ^ 2 ∂P ≤ σ ^ 2) (hη : 0 < η) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hm : ⌈4 * σ ^ 2 / η ^ 2⌉₊ ≤ m) :
    P {ω | η < |batchMedian X ⌈8 * Real.log (1 / δ)⌉₊ m ω - μ|} ≤ ENNReal.ofReal δ ∧
      ((⌈8 * Real.log (1 / δ)⌉₊ * ⌈4 * σ ^ 2 / η ^ 2⌉₊ : ℕ) : ℝ) ≤
        (8 * Real.log (1 / δ) + 1) * (4 * σ ^ 2 / η ^ 2 + 1) := by sorry

end ArbLindbladLearn
