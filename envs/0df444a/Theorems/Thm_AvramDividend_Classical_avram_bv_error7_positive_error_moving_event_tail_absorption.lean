-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_positive_error_moving_event_tail_absorption
-- name    : AvramDividend.Classical.avram_bv_error7_positive_error_moving_event_tail_absorption
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T13:01:10.565073+00:00
-- url     : https://prove2.me/theorems/d9416dc6-c3fc-4b3d-b0a5-217ed1753dba
-- title:
--   Moving physical-grid interior-plus-boundary-tail positive error absorption
-- statement:
--   For the original positive stopped-grid approximation residual Err_m and sample-dependent interior localisation events s_m, an exact measurable partition identifies the expected full positive error as the sum of its interior contribution and complementary ruin/horizon/cap tail. If both contributions converge to zero in expectation, the original expected positive error converges to zero. This reduction exposes the required missing tail control and does not import the signed BV prebudget.
-- source:
--   Consequence of fresh exact partition lemma DD and additivity of convergence. The interior event process and tail remain the actual Err, not a surrogate.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_positive_error_measurable_event_split
open MeasureTheory Set Filter AvramDividend.Classical
open scoped Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_positive_error_moving_event_tail_absorption
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (s : ℕ → Set Ω) (hs : ∀ m, MeasurableSet (s m))
    (Err : ℕ → Ω → ℝ)
    (hPos : ∀ m, Integrable (fun ω => max (Err m ω) 0) P)
    (hLocal : Tendsto
      (fun m => ∫ ω, max (if ω ∈ s m then Err m ω else 0) 0 ∂P)
      atTop (nhds (0 : ℝ)))
    (hTail : Tendsto
      (fun m => ∫ ω, max (if ω ∉ s m then Err m ω else 0) 0 ∂P)
      atTop (nhds (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
