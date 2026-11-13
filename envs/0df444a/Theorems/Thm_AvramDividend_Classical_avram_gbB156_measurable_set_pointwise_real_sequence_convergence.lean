-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB156_measurable_set_pointwise_real_sequence_convergence
-- name    : AvramDividend.Classical.avram_gbB156_measurable_set_pointwise_real_sequence_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:37:19.166459+00:00
-- url     : https://prove2.me/theorems/f2750414-809e-461e-8aa4-6f11bc663a98
-- title:
--   Measurable pointwise convergence event for a real sequence
-- statement:
--   The event of pointwise convergence of a measurable sequence to a measurable limit is measurable. Subtract the variable limit to obtain convergence to zero and apply Mathlib measurableSet_tendsto.
-- source:
--   Pinned Mathlib measurableSet_tendsto

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB156_measurable_set_pointwise_real_sequence_convergence
    {α : Type*} [MeasurableSpace α]
    (f : ℕ → α → ℝ) (g : α → ℝ)
    (hf : ∀ m, Measurable (f m)) (hg : Measurable g) :
    MeasurableSet {z : α | Filter.Tendsto (fun m : ℕ => f m z) Filter.atTop (𝓝 (g z))} := by sorry
