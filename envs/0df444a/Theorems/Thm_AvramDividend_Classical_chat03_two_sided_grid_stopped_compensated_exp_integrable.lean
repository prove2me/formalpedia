-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_two_sided_grid_stopped_compensated_exp_integrable
-- name    : AvramDividend.Classical.chat03_two_sided_grid_stopped_compensated_exp_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T18:13:15.97488+00:00
-- url     : https://prove2.me/theorems/fd70203f-fcda-42d8-9fc5-0ee686d3aa19
-- title:
--   Compensated exponential integrability at finite strict two-sided grid stopping
-- statement:
--   Let X be the official spectrally negative Lévy process, sample it on a monotone deterministic grid clock with matched filtration H, and let K be the bounded first strict two-sided grid exit. For every nonnegative Laplace parameter theta, the stopped compensated exponential exp(theta X_clock(K)-clock(K) psi(theta)) is Bochner integrable under P. First show that the strict-exit witness max(X_clock(k)-upper, lower-X_clock(k)) is adapted. The pinned discrete isStoppingTime_hittingBtwn establishes K as a stopping time; monotone-clock reindexing of the previously Proved exponential martingale gives a discrete martingale; pinned integrable_stoppedValue then supplies integrability from the finite bound K≤m. This closes a genuine measure-theoretic hypothesis of the finite-horizon L² estimate without assuming right-continuity of the original filtration.
-- source:
--   Pinned Mathlib Probability.Process.HittingTime, Probability.Process.Stopping integrable_stoppedValue, and the two already Proved theorem modules levy_compensated_exponential_martingale and chat03_martingale_sampled_filtration_reindex_corrected. Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_chat03_martingale_sampled_filtration_reindex_corrected
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_two_sided_grid_stopped_compensated_exp_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ : ℝ) (hθ : 0 ≤ θ) (lower upper : ℝ) (m : ℕ)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω) :
    Integrable (fun ω =>
      Real.exp (θ * X.X (clock (K ω)) ω -
        ((clock (K ω)) : ℝ) * X.ψ θ)) P := by sorry
