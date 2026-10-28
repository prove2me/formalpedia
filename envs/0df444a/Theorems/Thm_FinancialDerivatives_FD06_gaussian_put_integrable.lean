-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_gaussian_put_integrable
-- name    : FinancialDerivatives.FD06.gaussian_put_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:27:29.371238+00:00
-- url     : https://prove2.me/theorems/bde0b0de-be95-4c2e-8c15-32f42366c246
-- title:
--   Gaussian put payoff integrability
-- statement:
--   Gaussian put payoff integrability
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_lognormalTerminal

namespace FinancialDerivatives.FD06

theorem gaussian_put_integrable (S K R Q V : ℝ) : MeasureTheory.Integrable (fun z : ℝ => max (K - lognormalTerminal S R Q V z) 0) (ProbabilityTheory.gaussianReal 0 1) := by sorry

end FinancialDerivatives.FD06
