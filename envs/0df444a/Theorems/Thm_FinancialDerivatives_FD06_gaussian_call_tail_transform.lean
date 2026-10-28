-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_gaussian_call_tail_transform
-- name    : FinancialDerivatives.FD06.gaussian_call_tail_transform
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:28:13.671574+00:00
-- url     : https://prove2.me/theorems/1d494c98-e7de-4574-9a50-897e5503e0a1
-- title:
--   Gaussian call expectation equals closed formula
-- statement:
--   Gaussian call expectation equals closed formula
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_discountedCallGaussian
import Definitions.Def_fd06_generalisedCall

namespace FinancialDerivatives.FD06

theorem gaussian_call_tail_transform (S K R Q V : ℝ) (hS : 0 < S) (hK : 0 < K) (hV : 0 < V) : discountedCallGaussian S K R Q V = generalisedCall S K R Q V := by sorry

end FinancialDerivatives.FD06
