-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_binomial_cell_limit_identifies_poisson_singletons_20261115
-- name    : AvramDividend.Classical.avram_a25_binomial_cell_limit_identifies_poisson_singletons_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:24:28.576094+00:00
-- url     : https://prove2.me/theorems/a0b3ad1a-6dd3-4378-8299-e9c5dbd81171
-- title:
--   A count law approximable pointwise by rare-event binomials is exactly Poisson
-- statement:
--   Let μ be a measure on natural counts, r≥0, and p_n an event probability in [0,1] with n p_n→r. If for each k the mass Bin(n,p_n){k} converges to μ{k}, then μ{k}=Poisson(r){k}. The pinned Mathlib Poisson limit theorem already establishes Bin(n,p_n){k}→Poisson(r){k}; uniqueness of limits yields the result. This isolates the final analytic identification of the original physical negative-Borel count law from the stochastic Bernoulli time-grid approximation. It applies also when r=0 without invalid factorial-moment assumptions.
-- source:
--   Mathlib.Probability.Distributions.Poisson.PoissonLimitThm binomial_tendsto_poissonPMFReal_atTop and tendsto_nhds_unique.

import Mathlib
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a25_binomial_cell_limit_identifies_poisson_singletons_20261115
    (μ : Measure ℕ) (r : ℝ≥0) (p : ℕ → unitInterval)
    (hRate : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ))
      atTop (𝓝 (r : ℝ)))
    (hApprox : ∀ k : ℕ,
      Tendsto (fun n : ℕ => Bin(n, p n) {k})
        atTop (𝓝 (μ {k}))) :
    ∀ k : ℕ, μ {k} = poissonMeasure r {k} := by sorry
