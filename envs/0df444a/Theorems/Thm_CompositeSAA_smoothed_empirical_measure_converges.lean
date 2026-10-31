-- Prove2me | Theorems.Thm_CompositeSAA_smoothed_empirical_measure_converges
-- name    : CompositeSAA.smoothed_empirical_measure_converges
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:32:48.758972+00:00
-- url     : https://prove2.me/theorems/40046ab3-2402-4146-a2ef-3b0812b77eff
-- title:
--   Proof of Theorem 7, p.11 — the smoothed empirical measures converge weakly with their first moments, almost surely (corrected: about $P_N*\mu_N$)
-- statement:
--   Let $X_1,X_2,\dots$ be independent random vectors in $\mathbb R^m$ with law $P$ and $\mathbb E\|X\|<\infty$, and let the smoothing measures $\mu_N$ satisfy Assumption 6. Then, almost surely,
--
--   $$
--   P_N*\mu_N\to P\ \text{weakly}\qquad\text{and}\qquad\int\|x\|\,(P_N*\mu_N)(dx)\to\int\|x\|\,P(dx),
--   $$
--
--   where $P_N$ is the empirical measure of $X_1,\dots,X_N$.
--
--   This verifies, path by path, the hypotheses of Theorem 4(b) for $Q^j_N=P_N*\mu_N$, the measures integrated against on the smoothed levels of the estimator $\varrho^{(N,J)}_\mu$.
--
--   Differences from the source:
--   - correction: "We only need verify that $\int_{\mathcal X}\|x\|\,\mu_N(dx)\to\int_{\mathcal X}\|x\|\,P(dx)$" → the claim for $P_N*\mu_N$, together with its weak convergence; reason: the printed claim is false, since $\mu_N\to\delta(0)$ forces its left side to $0$ (take $\mu_N=\delta(0)$, $P=\delta(1)$); the convergence Theorem 4(b) needs is that of $P_N*\mu_N$.
--   - generalization: finite $p$-th moment of $X$, $p\ge1$ (p.1) → $\mathbb E\|X\|<\infty$; reason: the case $p=1$ covers every $p\ge1$.
--   - reading: "$\{\mu_N\}$ independent of $P_N$" → a deterministic sequence; the inner $\lim_{N\to\infty}$ of Assumption 6 → $\limsup$; reason: the only randomness of the paper is the sample, and the printed limit presupposes existence; the limsup reading is the weaker hypothesis.
--   - encoding: $P_N*\mu_N$ as $\frac1N\sum_i$ of the image of $\mu_N$ under $z\mapsto X_i+z$, weak convergence through bounded continuous test functions, 0-based sample; reason: Lean convention, same instances.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, proof of Theorem 7, p.11 (with Assumption 6, p.9)

import Mathlib
import Definitions.Def_CompositeSAA_SmoothingAssumption
import Definitions.Def_CompositeSAA_smoothedEmpiricalMeasure

open MeasureTheory Filter Topology ProbabilityTheory
open scoped BoundedContinuousFunction

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, proof of Theorem 7, p.11 (corrected): the smoothed
empirical measures satisfy the hypotheses of Theorem 4(b). Let `X_1, X_2, …` be i.i.d. with law
`P` and `E‖X‖ < ∞`, and let `(µ_N)` satisfy Assumption 6. Then, almost surely,
`P_N ∗ µ_N → P` weakly and `∫ ‖x‖ d(P_N ∗ µ_N)(x) → ∫ ‖x‖ dP(x)`.

**Formalization Note**
1. Correction: the page claims `∫ ‖x‖ µ_N(dx) → ∫ ‖x‖ P(dx)`, which is false (`µ_N → δ(0)` forces
   the left side to `0`; take `µ_N = δ(0)`, `P = δ(1)`). What Theorem 4(b) needs, and what is
   stated, is the claim for `Q_N = P_N ∗ µ_N`.
2. `P_N ∗ µ_N` is `smoothedEmpiricalMeasure (µ N) N (X · ω)`; the sample `X_1, …, X_N` is
   `X 0, …, X (N − 1)`. Weak convergence is written with bounded continuous test functions. -/
theorem smoothed_empirical_measure_converges {m : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin m))) (hPmom : Integrable (fun x => ‖x‖) P)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin m)) (hindep : iIndepFun X Pr)
    (hlaw : ∀ i, HasLaw (X i) P Pr)
    (μ : ℕ → Measure (EuclideanSpace ℝ (Fin m))) (hμ : SmoothingAssumption μ) :
    ∀ᵐ ω ∂Pr,
      (∀ g : EuclideanSpace ℝ (Fin m) →ᵇ ℝ,
        Tendsto (fun N => ∫ x, g x ∂(smoothedEmpiricalMeasure (μ N) N (fun i => X i ω))) atTop
          (𝓝 (∫ x, g x ∂P))) ∧
      Tendsto (fun N => ∫ x, ‖x‖ ∂(smoothedEmpiricalMeasure (μ N) N (fun i => X i ω))) atTop
        (𝓝 (∫ x, ‖x‖ ∂P)) := by sorry

end CompositeSAA
