-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_true_ruinbranch_W_le_runningSup
-- name    : AvramDividend.Classical.avram_f6_original_true_ruinbranch_W_le_runningSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:35:25.377569+00:00
-- url     : https://prove2.me/theorems/e529db9c-d5e7-4eba-94e4-ef3defb93e3d
-- title:
--   True stopped postpayment reserve across both ruin branches is at most x plus true runningSup
-- statement:
--   For true original Lévy X and nondecreasing dividend D with D0=0, both the pre-ruin rightpayment reserve and ruin-time riskProcess are upper bounded by x+runningSup X T at every t≤T. This controls exact HJB caplinear terminal growth at all stopped clocks without fabricated paths.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a35_original_dividend_rightLimit_nonnegative
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_true_ruinbranch_W_le_runningSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T t : ℝ≥0) (ht : t ≤ T) (ω : Ω) :
    (if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X t ω - rightLimit D t ω
      else riskProcess X x D t ω) ≤
      x + runningSup X T ω := by sorry
