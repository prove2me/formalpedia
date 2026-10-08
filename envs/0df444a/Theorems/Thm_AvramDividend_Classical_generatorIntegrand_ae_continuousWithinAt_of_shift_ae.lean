-- Prove2me | Theorems.Thm_AvramDividend_Classical_generatorIntegrand_ae_continuousWithinAt_of_shift_ae
-- name    : AvramDividend.Classical.generatorIntegrand_ae_continuousWithinAt_of_shift_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:19:23.652986+00:00
-- url     : https://prove2.me/theorems/d5b8acb0-0131-448d-a880-ee433bff7b8e
-- title:
--   Almost-everywhere state continuity of compensated jumps away from origin discontinuities
-- statement:
--   At a fixed state x, if W and W' are continuous at x and W is continuous at the shifted state x+y for almost every jump y under a measure μ, then the compensated generator increment is continuous within any chosen state set at x for almost every y. This reduces the exceptional-jump issue to showing x+y does not hit a discontinuity of W with positive Lévy mass.
-- source:
--   Continuity of compensated increments and an almost-everywhere filter, in the Avram Dividend generator argument.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generatorIntegrand_ae_continuousWithinAt_of_shift_ae
    (W : ℝ → ℝ) (μ : Measure ℝ) (s : Set ℝ) (x : ℝ)
    (hWx : ContinuousAt W x)
    (hderiv : ContinuousAt (deriv W) x)
    (hshift : ∀ᵐ y ∂μ, ContinuousAt W (x + y)) :
    ∀ᵐ y ∂μ,
      ContinuousWithinAt
        (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand W z y)
        s x := by sorry

end AvramDividend.Classical
