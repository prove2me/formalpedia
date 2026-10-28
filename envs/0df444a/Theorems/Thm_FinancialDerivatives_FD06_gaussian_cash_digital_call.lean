-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_gaussian_cash_digital_call
-- name    : FinancialDerivatives.FD06.gaussian_cash_digital_call
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:41:14.506104+00:00
-- url     : https://prove2.me/theorems/f18fa65d-3379-4324-a943-720f31101802
-- title:
--   Cash-or-nothing call digital expectation
-- statement:
--   Cash-or-nothing call digital expectation
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6, with explicit analytic extensions.

import Mathlib
import Definitions.Def_fd06_generalisedD2
import Definitions.Def_fd06_lognormalTerminal
import Definitions.Def_fd06_standardNormalCDF
open MeasureTheory intervalIntegral

namespace FinancialDerivatives.FD06

theorem gaussian_cash_digital_call (S K R Q V : ℝ) (hS : 0 < S) (hK : 0 < K) (hV : 0 < V) : Real.exp (-R) * (∫ z : ℝ, (if K ≤ lognormalTerminal S R Q V z then (1 : ℝ) else 0) ∂ProbabilityTheory.gaussianReal 0 1) = Real.exp (-R) * standardNormalCDF (generalisedD2 S K R Q V) := by sorry

end FinancialDerivatives.FD06
