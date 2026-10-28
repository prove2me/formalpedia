-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_discounted_put_nonneg
-- name    : FinancialDerivatives.FD06.discounted_put_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:31:12.229408+00:00
-- url     : https://prove2.me/theorems/2b2824a1-fe7b-474f-8762-f35abcf7fdda
-- title:
--   Nonnegative put expectation
-- statement:
--   Nonnegative put expectation
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_discountedPutGaussian

namespace FinancialDerivatives.FD06

theorem discounted_put_nonneg (S K R Q V : ℝ) : 0 ≤ discountedPutGaussian S K R Q V := by sorry

end FinancialDerivatives.FD06
