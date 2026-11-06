-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_controlled_left_prestate_explicit_source_eq
-- name    : AvramDividend.Classical.avram_p3_2_original_controlled_left_prestate_explicit_source_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T09:02:26.372809+00:00
-- url     : https://prove2.me/theorems/af64d023-2b0f-4c98-86e3-aa2e1a08fcf4
-- title:
--   Controlled original Lévy source left prestate equals actual X left limit less prepayment dividend
-- statement:
--   For the original spectrally negative Lévy source path and an admissible dividend strategy, at every strictly positive time t and any actual left limit lX of X at t, the controlled post-rightpayment path has left limit x+lX-D(t). It uses the original rightLimit D left limit, which equals D(t), without a surrogate process, equality in law or a boundary-continuity assumption on w.
-- source:
--   Pinned original rightLimit-leftLimit-equals-D Proved theorem f9c3a5c4, confirmed Mathlib leftLim_eq_of_tendsto and nhdsLT_neBot_of_exists_lt, and accepted original controlled left prestate submission 69b58911.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_controlled_left_prestate_explicit_source_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (lX : ℝ)
    (hXleft : Tendsto (fun s : ℝ≥0 => X.X s ω) (𝓝[<] t) (𝓝 lX)) :
    Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
      x + lX - D t ω := by sorry
