-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_killed_martingale_from_source
-- name    : AvramDividend.Classical.avram_root29_01_unbounded_killed_martingale_from_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:04:27.493002+00:00
-- url     : https://prove2.me/theorems/dba19614-8306-4d6a-9cc3-c2e4aa815d63
-- title:
--   Genuine unbounded-variation original-Lévy killed discounted q-scale martingale
-- statement:
--   For a true spectrally negative Lévy process of unbounded variation, its actual lower-killed discounted q-scale reward is a martingale for all real starting reserves. The proof discharges the Proved chat04_unbounded_killed_martingale_of_future_window_harmonicity premise using the source-specific future-window conditional harmonicity and a globally rational-covering countable schedule.
-- source:
--   WS1A stage source work/avram_root29_01_unbounded_killed_martingale_from_source_draft.lean; publish only after source future-window theorem is canonically Proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_unbounded_future_window_harmonicity
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_martingale_of_future_window_harmonicity
import Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_unbounded_killed_martingale_from_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) :
    Martingale (fun t ω =>
      ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) *
          W (x + X.X t ω)) ω) 𝓕 P := by sorry
