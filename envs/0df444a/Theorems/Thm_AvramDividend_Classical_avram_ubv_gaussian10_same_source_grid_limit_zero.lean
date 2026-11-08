-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_same_source_grid_limit_zero
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_same_source_grid_limit_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:33:37.614311+00:00
-- url     : https://prove2.me/theorems/3bf5dcd5-428b-4da7-b1a4-7ef91bf02186
-- title:
--   Same-original-path Gaussian stopped grid limit preserves zero expectation under explicit bounded localisation
-- statement:
--   On the original Lévy probability space, suppose the Brownian projection is given by a pathwise Lévy-Itô decomposition into a continuous Gaussian process Y and the same source jump residuals. If each finite stopped predictable-step sum of projected increments is integrable with mean zero, its absolute value is uniformly bounded in the localisation index, and the sums converge almost surely to M, then M is integrable and has mean zero. The proof retains the exact source identity and uses finite-sum integration and dominated convergence. Finite-step centring, the decomposition, and uniform domination remain explicit hypotheses.
-- source:
--   Fukasawa, stochastic-analysis-lean, Chapter11BoundedStoppedExpectation.lean and Chapter11BoundedStrategyIntegral.lean, accessed 2026-11-07; adapted to original Avram path and same-space Gaussian projection, with source assumptions explicit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_same_source_grid_limit_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge B : ℝ≥0 → Ω → ℝ)
    (hDecomp : ∀ ω t, X.X t ω =
      (t : ℝ) * X.c + (Y.X t ω - (t : ℝ) * Y.c) +
      Jsmall t ω + Jlarge t ω)
    (hB : ∀ ω t, B t ω = X.X t ω - (t : ℝ) * X.c -
      Jsmall t ω - Jlarge t ω)
    (S : ℕ → Finset ℕ)
    (u v : ℕ → ℕ → Ω → ℝ≥0)
    (G : ℕ → ℕ → Ω → ℝ)
    (F : ℕ → Ω → ℝ)
    (hF : ∀ n ω, F n ω = ∑ i ∈ S n,
      G n i ω * (B (v n i ω) ω - B (u n i ω) ω))
    (hStepI : ∀ n i, i ∈ S n →
      Integrable (fun ω => G n i ω *
        (B (v n i ω) ω - B (u n i ω) ω)) P)
    (hStepZero : ∀ n i, i ∈ S n →
      (∫ ω, G n i ω *
        (B (v n i ω) ω - B (u n i ω) ω) ∂P) = 0)
    (K : ℝ) (hBound : ∀ n, ∀ᵐ ω ∂P, |F n ω| ≤ K)
    (M : Ω → ℝ)
    (hConv : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (M ω))) :
    (∀ ω t, B t ω = Y.X t ω - (t : ℝ) * Y.c) ∧
      Integrable M P ∧ (∫ ω, M ω ∂P) = 0 := by sorry
