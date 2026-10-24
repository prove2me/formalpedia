-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_capped_upper_grid_exp_moment_one
-- name    : AvramDividend.Classical.levy_capped_upper_grid_exp_moment_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:08:04.640992+00:00
-- url     : https://prove2.me/theorems/c023eacf-a8d8-4e0e-9a42-48fc016b929b
-- title:
--   Unit expectation of the compensated Lévy exponential at a capped strictly upper grid passage
-- statement:
--   For a spectrally negative Lévy process, any nonnegative Laplace exponent parameter theta, a monotone deterministic nonnegative-time grid clock starting at zero and matching sampled filtration, the compensated exponential martingale exp(theta X(clock k)-clock k psi(theta)) has expectation exactly one when stopped at the first sampled strict upper passage above a level z, capped at integer horizon m. The stopping index is hittingBtwn of the observed reserve X(clock k) with upper set Ioi z. Apply the Proved sampled-filtration exponential martingale and generic bounded-first-crossing optional sampling results. Unlike the existing two-sided stopped-moment theorem, this is the exact one-sided observable needed to prove the remaining upper-grid q-discount bound.

import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.HittingTime
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_chat03_martingale_sampled_filtration_reindex_corrected
import Theorems.Thm_AvramDividend_Classical_chat03_bounded_first_crossing_martingale_identity
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_capped_upper_grid_exp_moment_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ : ℝ) (hθ : 0 ≤ θ) (z : ℝ) (m : ℕ) :
    (∫ ω,
      let K := hittingBtwn (fun k ω => X.X (clock k) ω)
        (Ioi z) 0 m ω
      Real.exp (θ * X.X (clock K) ω - (clock K : ℝ) * X.ψ θ) ∂P) = 1 := by sorry
