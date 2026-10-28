-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_gaussian_call_integrable
-- name    : FinancialDerivatives.FD06.gaussian_call_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:26:58.566714+00:00
-- url     : https://prove2.me/theorems/bce5347c-8e39-4e2c-afce-aeb6d8b226e0
-- title:
--   Gaussian call payoff integrability
-- statement:
--   Gaussian call payoff integrability
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_lognormalTerminal

namespace FinancialDerivatives.FD06

theorem gaussian_call_integrable (S K R Q V : ℝ) : MeasureTheory.Integrable (fun z : ℝ => max (lognormalTerminal S R Q V z - K) 0) (ProbabilityTheory.gaussianReal 0 1) := by sorry

end FinancialDerivatives.FD06
