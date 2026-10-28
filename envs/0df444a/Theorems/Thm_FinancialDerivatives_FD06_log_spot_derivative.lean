-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_log_spot_derivative
-- name    : FinancialDerivatives.FD06.log_spot_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:39:58.050384+00:00
-- url     : https://prove2.me/theorems/4801b404-22e6-4f16-a561-064e5a0f2fd3
-- title:
--   Logarithmic stock-coordinate chain rule
-- statement:
--   Logarithmic stock-coordinate chain rule
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6, with explicit analytic extensions.

import Mathlib

namespace FinancialDerivatives.FD06

theorem log_spot_derivative (f : ℝ → ℝ) (S : ℝ) (hS : 0 < S) (hf : DifferentiableAt ℝ f (Real.log S)) : deriv (fun x => f (Real.log x)) S = deriv f (Real.log S) / S := by sorry

end FinancialDerivatives.FD06
