-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid14_cofinal_band_bad_event_measure_tendsto_zero
-- name    : AvramDividend.Classical.avram_p3_grid14_cofinal_band_bad_event_measure_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:23:27.310705+00:00
-- url     : https://prove2.me/theorems/a27bbe5c-b3ab-490b-b604-9e0718346731
-- title:
--   Cofinal original-grid interior masks exhaust finite-measure samples in probability
-- statement:
--   For a fixed finite row of measurably observed original pre-jump reserves and exhaustive compact interior bands, the event that at least one genuinely positive, under-cap cell remains outside the band has probability tending to zero. Pointwise finite-row cofinality (Proved ed03fa23) yields eventual membership for every sample. Countable measurable tail-bad events decrease to the empty set; continuity from above under finite P and a measure squeeze give the result. This is a nontrivial probability-level interface needed before expected positive errors in e49a5fce can be controlled. It does not assert uniform integrability.
-- source:
--   Mathlib finite-measure continuity from above and original finite-row interior-mask eventuality ed03fa23; no path model modifications.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn13_original_finite_row_interior_mask_eventually
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid14_cofinal_band_bad_event_measure_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (n : ℕ) (z : Ω → ℕ → ℝ)
    (hz : ∀ i, Measurable (fun ω => z ω i)) :
    Tendsto (fun k : ℕ =>
      P ({ω : Ω | ∀ i < n + 1,
        (0 < z ω i ∧ ENNReal.ofReal (z ω i) < C) →
          z ω i ∈ Icc (a k) (b k)}ᶜ))
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
