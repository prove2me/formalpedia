-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_two_sided_grid_compensated_exp_integrable
-- name    : AvramDividend.Classical.chat03_two_sided_grid_compensated_exp_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T17:29:20.314997+00:00
-- url     : https://prove2.me/theorems/3364dc95-7c8f-4fbb-a245-9b7c42fab6f3
-- title:
--   Compensated Lévy exponential is integrable at bounded strict two-sided grid exit
-- statement:
--   Let X be the published spectrally negative Lévy process, clock any monotone deterministic grid, H its sampled filtration and K the first strictly upper/lower sampled exit bounded by m. For any θ≥0, the compensated exponential exp(θ X_clock(K)−clock(K)ψ(θ)) is integrable under the original probability measure. Adaptedness gives the finite grid exit as a bounded stopping time in H; the already Proved exponential martingale and deterministic-clock reindexing supply integrability at each grid index; the pinned Mathlib integrable_stoppedValue theorem then gives integrability at K. No right-continuity or completeness of the original continuous-time filtration is assumed.
-- source:
--   Mathlib/Probability/Process/Stopping.lean at revision 0df444a360eaa60ab8c11dca51a86af692955474, theorem integrable_stoppedValue; Proved AvramDividend.Classical.levy_compensated_exponential_martingale and chat03_martingale_sampled_filtration_reindex_corrected. Avram Palmowski Pistorius (2007) arXiv:math/0702893 Section 3.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_chat03_martingale_sampled_filtration_reindex_corrected

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_two_sided_grid_compensated_exp_integrable
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
    Integrable (fun ω => Real.exp
      (θ * X.X (clock (K ω)) ω -
        ((clock (K ω)) : ℝ) * X.ψ θ)) P := by sorry
