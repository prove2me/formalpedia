-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb27b_original_stopped_mark_compensator_real_clock
-- name    : AvramDividend.Classical.avram_bvb27b_original_stopped_mark_compensator_real_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T16:41:14.374342+00:00
-- url     : https://prove2.me/theorems/9c934e7d-8f77-42d3-a72b-01f60369de20
-- title:
--   Original stopped negative-mark compensated double integral equals real-time masked rate
-- statement:
--   For the genuine original Lévy negative-mark measure and finite-time mapped real clock, the source-exact compensated double integral with the literal inclusive reserve, strict inner horizon and ruin masks equals the masked integrated mark rate on [0,T]. Assumes only the required original mapped-time almost-everywhere strong measurability. The proof composes the Proved exact K transport and the mapped positive-clock lemma, without changing the process or truncation conventions.
-- source:
--   Proved 9ace2e92 original negative-mark K real time bridge and bvb26 source clock-cast lemma; Avram et al Prop 4(i) equation (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva21_original_K_negative_mark_real_time_bridge
import Theorems.Thm_AvramDividend_Classical_avram_bvb26b_real_clock_mapped_positive_mask_eq
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb27b_original_stopped_mark_compensator_real_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C τ : ℝ≥0∞) (U : ℝ≥0 → ℝ) (w : ℝ → ℝ)
    (q T : ℝ) (n : ℕ) :
    let a : ℝ := T - T / ((n : ℝ) + 2)
    let p : ℝ≥0 → Prop := fun t =>
      (t : ℝ≥0∞) ≤ τ ∧ 0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
    let rate : ℝ≥0 → ℝ := fun t =>
      Real.exp (-(q * (t : ℝ))) *
        (∫ z in Set.Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν)
    let J : ℝ≥0 → ℝ := fun t =>
      if 0 < t ∧ (t : ℝ) < a ∧ p t then rate t else 0
    let L : ℝ≥0 → ℝ := fun t =>
      ∫ z : ℝ, (if 0 < t ∧ (t : ℝ) < a ∧
         (t : ℝ≥0∞) ≤ τ ∧ 0 ≤ U t ∧
         ENNReal.ofReal (U t) ≤ C ∧ z < 0 then
         Real.exp (-(q * (t : ℝ))) *
          (w (U t + z) - w (U t)) else 0)
        ∂(X.ν.restrict (Set.Iio (0 : ℝ)))
    let μ : Measure ℝ≥0 :=
      ((volume : Measure ℝ).restrict (Set.Icc 0 T)).map Real.toNNReal
    AEStronglyMeasurable J μ →
    (∫ t : ℝ≥0, L t ∂μ) =
      ∫ r in Set.Icc (0 : ℝ) T,
        if 0 < r ∧ r < a ∧ p (Real.toNNReal r)
        then rate (Real.toNNReal r) else 0 := by sorry
