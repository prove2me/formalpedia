-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_gaussian_put_tail_transform
-- name    : FinancialDerivatives.FD06.gaussian_put_tail_transform
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:28:45.664978+00:00
-- url     : https://prove2.me/theorems/1569518c-bb6c-42a1-92ca-85e8c49a706d
-- title:
--   Gaussian put expectation equals closed formula
-- statement:
--   Gaussian put expectation equals closed formula
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_discountedPutGaussian
import Definitions.Def_fd06_generalisedPut

namespace FinancialDerivatives.FD06

theorem gaussian_put_tail_transform (S K R Q V : ℝ) (hS : 0 < S) (hK : 0 < K) (hV : 0 < V) : discountedPutGaussian S K R Q V = generalisedPut S K R Q V := by sorry

end FinancialDerivatives.FD06
