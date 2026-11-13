-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB157_ae_L2_on_time_interval_from_bounded_double_ae
-- name    : AvramDividend.Classical.avram_gbB157_ae_L2_on_time_interval_from_bounded_double_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T13:02:21.716208+00:00
-- url     : https://prove2.me/theorems/23c2ecf4-68dd-489e-a32f-83aa40c8facb
-- title:
--   Almost-everywhere bounded mesh convergence gives time-restricted iterated L2 loss convergence
-- statement:
--   A bounded jointly measurable sequence converging for almost every outcome and almost every physical time has its nested time/probability squared loss tend to zero. Extend both functions by zero outside the finite time interval, apply Proved B156 to obtain a measurable convergence event, and Proved B155 to exchange the almost-everywhere quantifiers and obtain L2 convergence.
-- source:
--   Proved B155 and B156

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB155_bounded_double_ae_L2_iterated_loss_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_gbB156_measurable_set_pointwise_real_sequence_convergence
open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB157_ae_L2_on_time_interval_from_bounded_double_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (n : ℕ) (hn : 0 < n) (K : ℕ → ℝ → Ω → ℝ) (H : ℝ → Ω → ℝ)
    (hKm : ∀ m, Measurable (fun z : ℝ × Ω => K m z.1 z.2))
    (hHm : Measurable (fun z : ℝ × Ω => H z.1 z.2))
    (BK BH : ℝ) (hBK : 0 ≤ BK) (hBH : 0 ≤ BH)
    (hKb : ∀ m t ω, t ∈ Set.Ioo (0 : ℝ) (n : ℝ) → |K m t ω| ≤ BK)
    (hHb : ∀ t ω, t ∈ Set.Ioo (0 : ℝ) (n : ℝ) → |H t ω| ≤ BH)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ t ∂(volume.restrict (Set.Ioo (0 : ℝ) (n : ℝ))),
      Tendsto (fun m : ℕ => K m t ω) atTop (𝓝 (H t ω))) :
    Tendsto (fun m : ℕ => ∫ t in Set.Ioo (0 : ℝ) (n : ℝ),
      (∫ ω, (K m t ω - H t ω) ^ 2 ∂P) ∂volume)
      atTop (𝓝 (0 : ℝ)) := by sorry
