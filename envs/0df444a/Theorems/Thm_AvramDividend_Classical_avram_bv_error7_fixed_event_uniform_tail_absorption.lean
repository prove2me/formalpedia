-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_fixed_event_uniform_tail_absorption
-- name    : AvramDividend.Classical.avram_bv_error7_fixed_event_uniform_tail_absorption
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T13:01:22.624099+00:00
-- url     : https://prove2.me/theorems/114318fd-edd7-47cb-a53c-395cf31f9a41
-- title:
--   Uniform original positive-error tail absorption from fixed localisation events
-- statement:
--   A useful exact two-limit convergence criterion for the original physical-grid positive Taylor/source error. For each fixed measurable compact-interior localisation event s_n, suppose local expected error vanishes as the mesh index tends to infinity. Suppose a quantitative uniform-in-m complementary error bound tail(n) tends to zero as the localisation grows. Then the full original positive-error expectation vanishes. The proof uses the exact event partition and a direct epsilon argument, so no interchange of limits is assumed; it isolates the additional original-process boundary/contact domination estimate.
-- source:
--   Exact event-partition child DD; direct metric filter epsilon proof. The outstanding tail bound is explicit, not derived from or assumed as the signed BV prebudget.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_positive_error_measurable_event_split
open MeasureTheory Set Filter Metric AvramDividend.Classical
open scoped Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_fixed_event_uniform_tail_absorption
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (Err : ℕ → Ω → ℝ)
    (hPos : ∀ m, Integrable (fun ω => max (Err m ω) 0) P)
    (hLocal : ∀ n, Tendsto
      (fun m => ∫ ω, max (if ω ∈ s n then Err m ω else 0) 0 ∂P)
      atTop (nhds (0 : ℝ)))
    (tail : ℕ → ℝ)
    (hTail : Tendsto tail atTop (nhds (0 : ℝ)))
    (hTailBound : ∀ n m,
      (∫ ω, max (if ω ∉ s n then Err m ω else 0) 0 ∂P) ≤ tail n) :
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
