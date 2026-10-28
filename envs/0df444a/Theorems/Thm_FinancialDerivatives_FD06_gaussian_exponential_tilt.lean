-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_gaussian_exponential_tilt
-- name    : FinancialDerivatives.FD06.gaussian_exponential_tilt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:26:30.589516+00:00
-- url     : https://prove2.me/theorems/abe6757e-8f9c-4dbd-94aa-ed06060316f3
-- title:
--   Gaussian exponential moment identity
-- statement:
--   Gaussian exponential moment identity
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
open MeasureTheory intervalIntegral

namespace FinancialDerivatives.FD06

theorem gaussian_exponential_tilt (a b : ℝ) : (∫ z : ℝ, Real.exp (a + b * z) ∂ProbabilityTheory.gaussianReal 0 1) = Real.exp (a + b ^ 2 / 2) := by sorry

end FinancialDerivatives.FD06
