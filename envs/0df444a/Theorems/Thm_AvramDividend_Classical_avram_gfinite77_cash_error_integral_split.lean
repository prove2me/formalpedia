-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite77_cash_error_integral_split
-- name    : AvramDividend.Classical.avram_gfinite77_cash_error_integral_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:59:24.544635+00:00
-- url     : https://prove2.me/theorems/404abd3b-1756-468f-a75b-4bdf7af483ee
-- title:
--   Expected positive cash mesh error is subadditive under splitting
-- statement:
--   For integrable positive parts of a source cash error, an approximation error, and their sum, the expected positive part of the combined error is at most the sum of the separate expected positive parts, over any measurable event. This enables separate source and mesh analysis of the Gaussian dividend cash ledger.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.avram_gfinite77_cash_error_integral_split
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (f g : Ω → ℝ)
    (hf : IntegrableOn (fun ω => max (f ω) 0) A P)
    (hg : IntegrableOn (fun ω => max (g ω) 0) A P)
    (hs : IntegrableOn (fun ω => max (f ω + g ω) 0) A P) :
    (∫ ω in A, max (f ω + g ω) 0 ∂P) ≤
      (∫ ω in A, max (f ω) 0 ∂P) +
        (∫ ω in A, max (g ω) 0 ∂P) := by
  sorry
