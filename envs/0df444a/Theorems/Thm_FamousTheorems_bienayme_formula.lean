-- Prove2me | Theorems.Thm_FamousTheorems_bienayme_formula
-- name    : FamousTheorems.bienayme_formula
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:51.118355+00:00
-- url     : https://prove2.me/theorems/0590a18d-48fb-4988-bcc2-83bc62b6a7d2
-- title:
--   Bienaymé's formula
-- statement:
--   **Bienaymé's formula.** Let $X_1,\dots,X_n$ be pairwise independent real random variables with finite second moments. Then
--   $$\operatorname{Var}\Big(\sum_iX_i\Big)=\sum_i\operatorname{Var}(X_i).$$
--
--   The variance of a sum of uncorrelated variables is the sum of the variances. With Chebyshev's inequality this gives the weak law of large numbers, and it is the reason the standard deviation of an average of $n$ independent samples scales like $1/\sqrt n$.
--
--   **Formalization note.** Mathlib's `ProbabilityTheory.IndepFun.variance_sum`. The variables are indexed by a finset `s`, finite second moment is `MemLp (X i) 2 μ`, and only pairwise independence is assumed. `ProbabilityTheory.variance` is the variance with respect to `μ`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ProbabilityTheory.IndepFun.variance_sum`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem bienayme_formula {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {X : ι → Ω → ℝ} {s : Finset ι}
    (hs : ∀ i ∈ s, MeasureTheory.MemLp (X i) 2 μ)
    (h : (s : Set ι).Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ) :
    ProbabilityTheory.variance (∑ i ∈ s, X i) μ = ∑ i ∈ s, ProbabilityTheory.variance (X i) μ := by sorry

end FamousTheorems
