-- Prove2me | Theorems.Thm_AvramDividend_Classical_postPaymentReserve_grid_exit_stopped_measurable
-- name    : AvramDividend.Classical.postPaymentReserve_grid_exit_stopped_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:35:31.376919+00:00
-- url     : https://prove2.me/theorems/50825628-1572-44e6-a919-c0fecdf24524
-- title:
--   Measurable stopped post-payment reserve and time at a finite grid exit
-- statement:
--   For a bounded discrete time grid whose filtration at index k is the right-continuous original filtration at clock(k), detect the first grid index where the post-payment controlled reserve exits the open interval (lower,upper), using the Mathlib hittingBtwn max-distance construction. Show that both the controlled reserve evaluated at the first exit index and the real-valued grid stopping time are measurable. The post-payment reserve is adapted on the right-continuous filtration by an accepted theorem. The remaining argument uses the accepted Mathlib discrete hitting-time and progressive stopped-value lemmas, in the same pattern already accepted for the unregulated Lévy path. This is discrete localisation infrastructure; it does not claim the continuous-time HJB martingale estimate.
-- source:
--   Source-complete bounded-grid controlled reserve localisation; no Open theorem imports; based on accepted chat03_grid_stop_meas and accepted postPaymentReserve_cadlag_adapted.

import Mathlib
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.postPaymentReserve_grid_exit_stopped_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕.rightCont (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (x + X.X (clock k) ω - rightLimit D (clock k) ω - upper)
        (lower - (x + X.X (clock k) ω - rightLimit D (clock k) ω))) (Set.Ioi (0 : ℝ)) 0 m ω) :
    Measurable (fun ω =>
      x + X.X (clock (K ω)) ω - rightLimit D (clock (K ω)) ω) ∧
    Measurable (fun ω => (clock (K ω) : ℝ)) := by sorry
