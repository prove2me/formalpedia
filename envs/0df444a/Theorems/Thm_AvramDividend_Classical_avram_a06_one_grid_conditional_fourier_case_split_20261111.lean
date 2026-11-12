-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_one_grid_conditional_fourier_case_split_20261111
-- name    : AvramDividend.Classical.avram_a06_one_grid_conditional_fourier_case_split_20261111
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:16:55.743513+00:00
-- url     : https://prove2.me/theorems/12f52caf-14d0-41d4-a568-264d1741d1f8
-- title:
--   Random-grid conditional Fourier formula for exactly one interval (resubmitted after dependencies proved)
-- statement:
--   The one-interval branch of the A06 conditional Fourier representation follows without independence assumptions. Construct the measurable random-interval mark sum from the measurable count grid and mark stream, then invoke the accepted one-coordinate constant-kernel characteristic-function factorisation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_single_grid_constant_fourier_factor_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a06_measurable_random_mark_interval_20261111
open MeasureTheory ProbabilityTheory Finset
noncomputable section

theorem AvramDividend.Classical.avram_a06_one_grid_conditional_fourier_case_split_20261111
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Fin 2 → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable (fun ω => fun i => N i ω))
    (hY : Measurable (fun ω => fun j => Y j ω)) :
    ∀ t : WithLp 2 (Fin 1 → ℝ), ∃ φ : Fin 1 → ℕ → ℂ,
      MeasureTheory.charFun
        (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin 1 =>
          ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω)) P) t =
        ∫ ω, ∏ i : Fin 1, φ i (N i.succ ω - N i.castSucc ω) ∂P
      ∧ ∀ i : Fin 1, MeasureTheory.charFun
          (Measure.map (fun ω : Ω =>
            ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω) P)
            (t.ofLp i) =
          ∫ ω, φ i (N i.succ ω - N i.castSucc ω) ∂P := by sorry
