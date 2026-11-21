-- Prove2me | Theorems.Thm_BFWFluidLimit_integral_sum_sq_average_add_le
-- name    : BFWFluidLimit.integral_sum_sq_average_add_le
-- status  : Proved
-- author  : @wfe2017
-- created : 2026-11-20T11:13:09.859189+00:00
-- url     : https://prove2.me/theorems/eff9a4e2-3dea-49c7-ae29-3fe081cb88b5
-- title:
--   Corrected exploration initialization: finite-coordinate mean-square estimate
-- statement:
--   For finitely many coordinates, average K≥1 observations of two square-integrable arrays a and z. Assume each array is separately orthogonal across observation indices in each coordinate, with coordinate second-moment bounds A_j and Z_j. Then the expected squared Euclidean norm of the empirical average of a+z is at most 2 Σ_j(A_j+Z_j)/K. Cross-array orthogonality and independence between coordinates are not assumed. This is an analytic ingredient for the corrected martingale initialization argument; identifying a=Φ(P)−μ_X and z=(0,ε,0,P⊙ε) is a separate step.
-- source:
--   J. Baek, V. F. Farias, F. Wu, Misspecified Estimate-then-Optimize Leads to Supra-Competitive Prices, arXiv:2605.16064v2, https://arxiv.org/pdf/2605.16064; Lemma E.3 p. 40 and Appendix F.3 pp. 46–48; corrected O(1/K) initialization estimate.

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

namespace BFWFluidLimit
theorem integral_sum_sq_average_add_le {d : Type*} [Fintype d]
    (K : ℕ) (hK : 0 < K) (a z : d → ℕ → Ω → ℝ)
    (ha : ∀ j i, i < K → MemLp (a j i) 2 μ)
    (hz : ∀ j i, i < K → MemLp (z j i) 2 μ)
    (haorth : ∀ j i, i < K → ∀ l, l < K → i ≠ l →
      ∫ ω, a j i ω * a j l ω ∂μ = 0)
    (hzorth : ∀ j i, i < K → ∀ l, l < K → i ≠ l →
      ∫ ω, z j i ω * z j l ω ∂μ = 0)
    (A Z : d → ℝ)
    (habound : ∀ j i, i < K → ∫ ω, (a j i ω) ^ 2 ∂μ ≤ A j)
    (hzbound : ∀ j i, i < K → ∫ ω, (z j i ω) ^ 2 ∂μ ≤ Z j) :
    ∫ ω, (∑ j, ((∑ i ∈ Finset.range K, (a j i ω + z j i ω)) / K) ^ 2) ∂μ
      ≤ 2 * (∑ j, (A j + Z j)) / K := by sorry
end BFWFluidLimit
