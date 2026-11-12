-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb39_orthogonal_sum_second_moment_bound
-- name    : AvramDividend.Classical.avram_gb39_orthogonal_sum_second_moment_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:09:52.912114+00:00
-- url     : https://prove2.me/theorems/22842af0-d40d-4ed2-8cb8-380fe85c1a16
-- title:
--   Pairwise orthogonal finite real random sums have diagonal second-moment bounds
-- statement:
--   Let a finite family of real random variables have integrable squares with their second moments bounded above by K. Suppose every cross-product for distinct indices is integrable and has expectation zero. The square of the sum is integrable, and its expectation is at most the cardinality of the index set times K. This isolates the exact algebraic step connecting original Gaussian grid cell fourth moments and orthogonality to the finite-cap quadratic L2 rate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped BigOperators

theorem AvramDividend.Classical.avram_gb39_orthogonal_sum_second_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (s : Finset ℕ) (U : ℕ → Ω → ℝ) (K : ℝ)
    (hdiag : ∀ i ∈ s, Integrable (fun ω => (U i ω) ^ 2) P ∧
      (∫ ω, (U i ω) ^ 2 ∂P) ≤ K)
    (hoff : ∀ i ∈ s, ∀ r ∈ s, i ≠ r →
      Integrable (fun ω => U i ω * U r ω) P ∧
      (∫ ω, U i ω * U r ω ∂P) = 0) :
    Integrable (fun ω => ((∑ i ∈ s, U i ω) ^ 2)) P ∧
      (∫ ω, (∑ i ∈ s, U i ω) ^ 2 ∂P) ≤ (s.card : ℝ) * K := by
  sorry
