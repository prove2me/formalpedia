-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_nonnegative_set_integral_L1_squeeze
-- name    : AvramDividend.Classical.avram_ga_nonnegative_set_integral_L1_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T07:30:18.04468+00:00
-- url     : https://prove2.me/theorems/331905a6-6e6b-475f-bffe-7ec093fffad6
-- title:
--   Nonnegative integrable residual with vanishing expectation also vanishes on every measurable event
-- statement:
--   For a sequence of pointwise nonnegative integrable random variables with expectations tending to zero, the integrals restricted to any event tend to zero by monotonicity and squeeze.

import Mathlib
open MeasureTheory Set Filter
noncomputable section

theorem AvramDividend.Classical.avram_ga_nonnegative_set_integral_L1_squeeze
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (f : ℕ → Ω → ℝ)
    (hInt : ∀ m, Integrable (f m) P)
    (hNonneg : ∀ m ω, 0 ≤ f m ω)
    (hVan : Tendsto (fun m => ∫ ω, f m ω ∂P) atTop (nhds (0 : ℝ)))
    (A : Set Ω) :
    Tendsto (fun m => ∫ ω in A, f m ω ∂P) atTop (nhds (0 : ℝ)) := by sorry
