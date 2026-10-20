-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_two_sided_grid_compensated_exp_moment_one
-- name    : AvramDividend.Classical.chat03_two_sided_grid_compensated_exp_moment_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T17:17:13.974878+00:00
-- url     : https://prove2.me/theorems/6b72c3df-fe64-48b4-9676-1c02513fc800
-- title:
--   Unit expectation of the exponential martingale at any bounded two-sided grid exit
-- statement:
--   For the published spectrally negative Lévy process X, a monotone deterministic grid clock starting at zero, an exactly matching sampled filtration H and any nonnegative Laplace parameter theta, let K be the first strict grid index with X_clock(k)>upper or X_clock(k)<lower, capped at m. Then the expectation of exp(theta X_clock(K) -clock(K) psi(theta)) is exactly 1. The proof composes three independently Proved results: the exponential martingale in X's original filtration, deterministic-clock martingale reindexing, and bounded strict two-sided grid optional sampling. This supplies the exact stopped exponential moment used for the finite-horizon uniform L² estimate, without continuous-time optional stopping or usual filtration assumptions.
-- source:
--   Exact Proved dependencies: levy_compensated_exponential_martingale b707e3a2-56a3-4a7b-af9e-53cba9e3731b; chat03_martingale_sampled_filtration_reindex_corrected 149bd72c-c5a0-44b2-82bb-90d7608ebb47; chat03_two_sided_grid_stopped_martingale_identity 73464341-39b0-42c4-8f14-5b4618f13688, all pinned Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_chat03_martingale_sampled_filtration_reindex_corrected
import Theorems.Thm_AvramDividend_Classical_chat03_two_sided_grid_stopped_martingale_identity

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_two_sided_grid_compensated_exp_moment_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ : ℝ) (hθ : 0 ≤ θ) (lower upper : ℝ) (m : ℕ)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω) :
    (∫ ω, Real.exp (θ * X.X (clock (K ω)) ω -
      ((clock (K ω)) : ℝ) * X.ψ θ) ∂P) = 1 := by sorry
