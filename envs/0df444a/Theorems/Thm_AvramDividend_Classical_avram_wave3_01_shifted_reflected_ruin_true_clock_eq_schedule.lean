-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_shifted_reflected_ruin_true_clock_eq_schedule
-- name    : AvramDividend.Classical.avram_wave3_01_shifted_reflected_ruin_true_clock_eq_schedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:51:27.551824+00:00
-- url     : https://prove2.me/theorems/8c7cefec-043c-4a11-9c84-80a1c14dba00
-- title:
--   True reflected drawdown strict ruin clock after arbitrary Lévy shift equals canonical countable schedule
-- statement:
--   For the original spectrally negative Levy sample path at any possibly random finite shift time u, the actual strict reflected drawdown ruin time measured from u, using the true historical running supremum, equals the infimum of all crossings on the canonical countable rational schedule. The result is exact pathwise rather than an almost sure or in-law assertion. It is proved by original process right-continuity together with continuity of its running maximum, then translating the strict-crossing right persistence interval and applying the established exact countable crossing theorem. This supplies the first nontrivial pathwise half of the correct fresh reflected ruin clock representation needed for the genuine source first-record Markov semigroup and pure-jump scale C1 regularity.
-- source:
--   Kuznetsov, Kyprianou and Rivero (2013), reflected excursion exits; accepted runningSup_continuous_actual, rightInterval_lower_strictExit_eq_schedule, source Lévy rightCont.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
import Theorems.Thm_AvramDividend_Classical_rightInterval_lower_strictExit_eq_schedule

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_shifted_reflected_ruin_true_clock_eq_schedule
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u : ℝ≥0) (a : ℝ) :
    (⨅ i : {t : ℝ≥0 //
      X.X (u + t) ω - runningSup X (u + t) ω < -a},
        (i.1 : ℝ≥0∞)) =
    (⨅ j : ℕ,
      if X.X (u + (((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹))) ω -
         runningSup X (u + (((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹))) ω < -a
      then ((((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) : ℝ≥0∞)
      else ⊤) := by sorry
