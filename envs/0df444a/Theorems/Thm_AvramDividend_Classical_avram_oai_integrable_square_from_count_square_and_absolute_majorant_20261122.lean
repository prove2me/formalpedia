-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_integrable_square_from_count_square_and_absolute_majorant_20261122
-- name    : AvramDividend.Classical.avram_oai_integrable_square_from_count_square_and_absolute_majorant_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:41:12.767919+00:00
-- url     : https://prove2.me/theorems/a1bed408-1f6b-46b5-a39d-67039461242f
-- title:
--   L2 integrability of a signed residual from a square-integrable count and constant absolute envelope
-- statement:
--   For a probability measure P, any integrable signed J satisfying |J| ≤ N + |c| almost surely, for a nonnegative N with N² integrable, has J² integrable. Used for the actual (non synthetic) finite-annulus negative jump mark integral when the original physical count has an integrable square.

import Mathlib
open MeasureTheory
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_integrable_square_from_count_square_and_absolute_majorant_20261122
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (J N : Ω → ℝ) (c : ℝ)
    (hJ : Integrable J P)
    (hN2 : Integrable (fun ω => (N ω) ^ 2) P)
    (hNonneg : ∀ᵐ ω ∂P, 0 ≤ N ω)
    (hBound : ∀ᵐ ω ∂P, |J ω| ≤ N ω + |c|) :
    Integrable (fun ω => (J ω) ^ 2) P := by sorry
