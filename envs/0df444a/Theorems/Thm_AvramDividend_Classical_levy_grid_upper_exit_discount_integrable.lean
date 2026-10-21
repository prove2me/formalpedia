-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_grid_upper_exit_discount_integrable
-- name    : AvramDividend.Classical.levy_grid_upper_exit_discount_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:35:11.411166+00:00
-- url     : https://prove2.me/theorems/c4aad9bf-7e5a-482c-9bd7-3fcbc047d58a
-- title:
--   Integrability of the discounted strict upper-exit indicator at a bounded Lévy grid stop
-- statement:
--   The actual compensated Lévy process sampled at a bounded two-sided grid stopping time has measurable stopped reserve and stopped time. If q≥0, the discounted indicator of strict upper exit is measurable and bounded by one. The underlying probability measure makes it integrable. This supplies the outstanding payoff-integrability premise for the exponential finite-grid first-passage bound.
-- source:
--   Proved chat03_grid_stopped_reserve_time_measurable and pinned Mathlib Integrable.of_bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_grid_upper_exit_discount_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → NNReal) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Ioi (0 : ℝ)) 0 m ω)
    (q : ℝ) (hq : 0 ≤ q) :
    Integrable
      ({ω : Ω | upper < X.X (clock (K ω)) ω}.indicator
        (fun ω => Real.exp (-((clock (K ω)) : ℝ) * q))) P := by sorry
