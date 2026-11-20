-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_positive_ruin_openclosed_cash_support_is_strict_open
-- name    : AvramDividend.Classical.avram_jump6_B_original_positive_ruin_openclosed_cash_support_is_strict_open
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:30:07.267533+00:00
-- url     : https://prove2.me/theorems/092d862e-ef12-4237-ad58-87564a70195a
-- title:
--   True original ruin-contact cash open-closed endpoint equals strict open payment support
-- statement:
--   Since original paymentTimes excludes the positive ruin instant, its intersection with the open-closed crossing interval (a,rho] is identical to its intersection with the fully open interval (a,rho). This justifies exact use of crossing-cell signed cash without erroneously paying an atom at ruin.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_positive_ruin_closed_cash_support_equals_strict
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_positive_ruin_openclosed_cash_support_is_strict_open
    (σ : ℝ≥0∞) (t : ℝ≥0) (ht : 0 < t)
    (hruin : (t : ℝ≥0∞) = σ) (a : ℝ) :
    paymentTimes σ ∩ Ioc a (t : ℝ) =
      paymentTimes σ ∩ Ioo a (t : ℝ) := by sorry
