-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_discounted_gaussian_parity
-- name    : FinancialDerivatives.FD06.discounted_gaussian_parity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:29:58.794263+00:00
-- url     : https://prove2.me/theorems/e19fe75b-1cc3-449a-8970-8ce5e20d5e9e
-- title:
--   Gaussian payoff parity via expected stock
-- statement:
--   Gaussian payoff parity via expected stock
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_discountedCallGaussian
import Definitions.Def_fd06_discountedPutGaussian

namespace FinancialDerivatives.FD06

theorem discounted_gaussian_parity (S K R Q V : ℝ) (hS : 0 < S) (hK : 0 < K) (hV : 0 < V) : discountedCallGaussian S K R Q V - discountedPutGaussian S K R Q V = S * Real.exp (-Q) - K * Real.exp (-R) := by sorry

end FinancialDerivatives.FD06
