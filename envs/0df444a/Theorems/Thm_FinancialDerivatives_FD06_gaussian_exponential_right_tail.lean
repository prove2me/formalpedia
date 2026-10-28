-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_gaussian_exponential_right_tail
-- name    : FinancialDerivatives.FD06.gaussian_exponential_right_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:40:53.519667+00:00
-- url     : https://prove2.me/theorems/9f2706b1-6692-4696-bd33-83dc4ec1f530
-- title:
--   Truncated exponential Gaussian tail identity
-- statement:
--   Truncated exponential Gaussian tail identity
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6, with explicit analytic extensions.

import Mathlib
import Definitions.Def_fd06_standardNormalCDF
open MeasureTheory intervalIntegral

namespace FinancialDerivatives.FD06

theorem gaussian_exponential_right_tail (b c : ℝ) : (∫ z : ℝ, (if c ≤ z then Real.exp (b * z) else 0) ∂ProbabilityTheory.gaussianReal 0 1) = Real.exp (b ^ 2 / 2) * standardNormalCDF (b - c) := by sorry

end FinancialDerivatives.FD06
