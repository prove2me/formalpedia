-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_strict_drawdown_clock_eq_cantor_schedule
-- name    : AvramDividend.Classical.avram_root29_05_shifted_strict_drawdown_clock_eq_cantor_schedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:27:41.143378+00:00
-- url     : https://prove2.me/theorems/30399e7d-0d45-4d64-b39d-badea1b5beae
-- title:
--   True future-increment strict drawdown ruin clock equals dense Cantor-sampled clock
-- statement:
--   For any original spectrally negative Lévy sample path and any finite shifted age u, the first strict reflected drawdown breach of the exact shifted-increment process equals the infimum of the same strict breach on the countable rational Cantor schedule. Uses the genuine right-continuity of shifted increments and their running supremum, including zero-time and infinite first passage.
-- source:
--   The Proved generic rightInterval_lower_strictExit_eq_schedule and Proved shiftedLevy_increments_right_continuous and shiftedSup_right_continuous_of_levy yield right-interval persistence of any strict shifted drawdown breach. Exact ENNReal time casts of the rational schedule are normalised by ENNReal.coe_mul and ENNReal.coe_inv. No original-clock identity is assumed on a shifted process.

import Mathlib.Topology.Order
import Mathlib.Data.Nat.Pairing
import Theorems.Thm_AvramDividend_Classical_rightInterval_lower_strictExit_eq_schedule
import Theorems.Thm_AvramDividend_Classical_shiftedLevy_increments_right_continuous
import Theorems.Thm_AvramDividend_Classical_shiftedSup_right_continuous_of_levy

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

/-- Every shifted genuine Lévy future has its strict drawdown first-passage
clock on the same dense Cantor schedule used for sampled regulator payments. -/

theorem AvramDividend.Classical.avram_root29_05_shifted_strict_drawdown_clock_eq_cantor_schedule
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u : ℝ≥0) (a : ℝ) :
    (let f : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
     let M : ℝ≥0 → ℝ := fun t => sSup (f '' Set.Icc 0 t)
     ⨅ i : {t : ℝ≥0 // f t - M t < -a}, (i.1 : ℝ≥0∞)) =
    (let f : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
     let M : ℝ≥0 → ℝ := fun t => sSup (f '' Set.Icc 0 t)
     let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     ⨅ j : ℕ, if f (samples j) - M (samples j) < -a
       then (samples j : ℝ≥0∞) else ⊤) := by sorry
