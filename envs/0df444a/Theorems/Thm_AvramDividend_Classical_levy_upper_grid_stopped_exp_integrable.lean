-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_upper_grid_stopped_exp_integrable
-- name    : AvramDividend.Classical.levy_upper_grid_stopped_exp_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:23:59.820596+00:00
-- url     : https://prove2.me/theorems/0ebde21a-82c5-41f7-94f6-89944f9047d9
-- title:
--   Bochner integrability of the compensated Lévy exponential at a capped upper-only grid passage
-- statement:
--   For any NNReal monotone deterministic clock and exact sampled filtration, let K be hittingBtwn X(clock k) (Ioi z) 0 m. The compensated exponential exp(theta X(clock K)-clock K psi(theta)) is integrable for theta≥0. Use the proved continuous-time Lévy exponential martingale, its deterministic-clock reindexing and the pinned integrable_stoppedValue theorem. This is the one-sided counterpart of the existing two-sided stopped compensated exponential integrability theorem, with exactly the cap K≤m.

import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_chat03_martingale_sampled_filtration_reindex_corrected
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_upper_grid_stopped_exp_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ : ℝ) (hθ : 0 ≤ θ) (z : ℝ) (m : ℕ)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => X.X (clock k) ω) (Ioi z) 0 m ω) :
    Integrable (fun ω => Real.exp
      (θ * X.X (clock (K ω)) ω - ((clock (K ω)) : ℝ) * X.ψ θ)) P := by sorry
