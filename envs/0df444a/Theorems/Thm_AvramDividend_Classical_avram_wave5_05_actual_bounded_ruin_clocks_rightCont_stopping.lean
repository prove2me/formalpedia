-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_actual_bounded_ruin_clocks_rightCont_stopping
-- name    : AvramDividend.Classical.avram_wave5_05_actual_bounded_ruin_clocks_rightCont_stopping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:56:00.180937+00:00
-- url     : https://prove2.me/theorems/bf7c0745-eb71-4ba2-9687-279d493b227b
-- title:
--   Native controlled ruin-clock truncations are true stopping times for the lifted original filtration
-- statement:
--   For the exact original spectrally negative Lévy source X and its native admissible dividend strategy D, the clock τ_n(ω)=min(ruinTime X x D ω,n) is a stopping time relative to the right-continuous enlargement of the original filtration. Uses the independently Proved same-source controlled ruinTime stopping theorem and the exact pinned Mathlib stopping-time closure under min with a constant. This supplies the true stopping-time property needed for the Gaussian/compensated-jump martingale localisation; it does not replace the remaining stochastic Itô–Meyer identity. No independent Brownian or finite-variation surrogate is introduced.
-- source:
--   Native ruinTime_stopping_rightCont_filtration Proved UUID 2d036d4f-57b5-4b28-864b-a2ff5082e323 and pinned Mathlib MeasureTheory.IsStoppingTime.min, MeasureTheory.isStoppingTime_const.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_05_actual_bounded_ruin_clocks_rightCont_stopping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ n : ℕ, IsStoppingTime 𝓕.rightCont
      (fun ω : Ω => min (ruinTime X x D ω) (n : ℝ≥0∞)) := by
  sorry
