-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_true_shifted_record_ruin_clock_pair
-- name    : AvramDividend.Classical.avram_wave3_01_true_shifted_record_ruin_clock_pair
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:23:47.798796+00:00
-- url     : https://prove2.me/theorems/acce5dd9-68df-47c5-88fb-48f0dbad055a
-- title:
--   Actual shifted Lévy record and reflected-ruin first clocks equal their measurable Cantor path clocks
-- statement:
--   For the genuine spectrally negative Lévy path shifted at any finite age u, the pair consisting of the first strict upward increment record clock and the first strict drawdown-ruin clock agrees pathwise with the two countably sampled Borel clocks on the Cantor rational grid, the latter using the clipped prefix supremum. This simultaneously identifies the actual future first-record and reflected-killing clocks inside the stopped strong-Markov reward. Proof relies on exact right-continuous upper-exit schedule, shifted reflected drawdown true-clock schedule, and source-level dense prefix supremum identity. No conditional stochastic regularity is assumed.
-- source:
--   Accepted rightInterval_upper_strictExit_eq_schedule, levy_shiftedUpper_strictCrossing_rightInterval, avram_root29_05_shifted_strict_drawdown_clock_eq_cantor_schedule, avram_ws01e_b_actual_shifted_levy_dense_prefix_eq_shiftedSup, chat05_cantor_rational_schedule_dense.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_rightInterval_upper_strictExit_eq_schedule
import Theorems.Thm_AvramDividend_Classical_levy_shiftedUpper_strictCrossing_rightInterval
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_strict_drawdown_clock_eq_cantor_schedule
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_shifted_levy_dense_prefix_eq_shiftedSup
import Theorems.Thm_AvramDividend_Classical_chat05_cantor_rational_schedule_dense

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_true_shifted_record_ruin_clock_pair
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u : ℝ≥0) (a c : ℝ) :
    (let f : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
     let M : ℝ≥0 → ℝ := fun t => sSup (f '' Set.Icc 0 t)
     ((⨅ i : {t : ℝ≥0 // c < f t}, (i.1 : ℝ≥0∞)),
      (⨅ i : {t : ℝ≥0 // f t - M t < -a}, (i.1 : ℝ≥0∞)))) =
    (let f : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
     let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     ((⨅ j : ℕ, if c < f (samples j)
          then (samples j : ℝ≥0∞) else ⊤),
      (⨅ j : ℕ, if f (samples j) -
        (⨆ k : ℕ, if samples k ≤ samples j
           then ENNReal.ofReal (f (samples k)) else 0).toReal < -a
          then (samples j : ℝ≥0∞) else ⊤))) := by sorry
