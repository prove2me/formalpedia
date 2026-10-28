-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_discounted_call_nonneg
-- name    : FinancialDerivatives.FD06.discounted_call_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:30:32.56525+00:00
-- url     : https://prove2.me/theorems/2c79daa3-ee64-4576-819d-94f11337c6d0
-- title:
--   Nonnegative call expectation
-- statement:
--   Nonnegative call expectation
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_discountedCallGaussian

namespace FinancialDerivatives.FD06

theorem discounted_call_nonneg (S K R Q V : ℝ) : 0 ≤ discountedCallGaussian S K R Q V := by sorry

end FinancialDerivatives.FD06
