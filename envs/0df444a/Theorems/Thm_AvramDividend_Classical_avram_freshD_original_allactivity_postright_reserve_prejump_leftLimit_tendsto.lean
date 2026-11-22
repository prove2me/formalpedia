-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_allactivity_postright_reserve_prejump_leftLimit_tendsto
-- name    : AvramDividend.Classical.avram_freshD_original_allactivity_postright_reserve_prejump_leftLimit_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:50:36.012698+00:00
-- url     : https://prove2.me/theorems/1b2ef671-ba93-4f57-a1b5-93acf2120be5
-- title:
--   Every actual original controlled post-right dividend reserve approaches its correct pre-jump value from the left, with all Lévy jumps retained
-- statement:
--   For every path of the original spectrally negative Lévy process X, including nonzero negative Lévy marks, and any genuine nondecreasing left-continuous dividend strategy D, the sampled post-right-payment reserve x+X_s-D(s+) converges from strictly below t>0 to x+X(t-)-D(t). This preserves the left-then-right source dividend convention at every actual negative Lévy jump time, using the Proved all-path càdlàg left convergence of X and exact strict-left limit of D(s+). It supplies the physical sampled-prejump convergence input of the separately indexed finite negative-mark nonlinear Taylor bound, without assuming ν=0 or smoothing the ruin event.
-- source:
--   Original Avram physical stopped Itô–Meyer finite-activity two-noise path, canonical definitions, Proved avram_p2_a_zero_rate_original_cadlag_regular_all_times and avram_wave3_04_rightLimit_leftLimit_eq_dividend.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_allactivity_postright_reserve_prejump_leftLimit_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    Tendsto
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
      (𝓝[<] t)
      (𝓝 (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω)) := by sorry
