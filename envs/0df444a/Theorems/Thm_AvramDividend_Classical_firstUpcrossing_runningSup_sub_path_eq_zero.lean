-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
-- name    : AvramDividend.Classical.firstUpcrossing_runningSup_sub_path_eq_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T10:14:11.142786+00:00
-- url     : https://prove2.me/theorems/9243feef-85e4-45be-9f62-5e56edb2abbf
-- title:
--   Drawdown is exactly zero at a finite first upcrossing without upward jumps
-- statement:
--   Let u be a finite first strict upward passage over nonnegative level b for a spectrally negative Lévy process. Since there are no positive jumps, the path reaches its running supremum at u, and the reflected drawdown runningSup X u − X_u equals zero. This is a boundary-contact fact needed to handle the strict excursion-ruin endpoint when regenerating discounted dividend value at new record levels. It is deterministic and does not claim the law or Markov restart.
-- source:
--   Avram Palmowski Pistorius (2007), first-passage at a new reflected record; follows from Prove2Me accepted firstUpcrossing_attains_peak (473109a5-7650-47ba-b397-29e7480e709e) and runningSup_eq_rawSup_nonneg (992246e6-0bba-4d6f-bd75-5b29c32037f9).

import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg

open MeasureTheory Set
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstUpcrossing_runningSup_sub_path_eq_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞))) :
    runningSup X u ω - X.X u ω = 0 := by sorry
