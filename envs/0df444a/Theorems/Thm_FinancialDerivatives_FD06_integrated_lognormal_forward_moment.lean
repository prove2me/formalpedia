-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_integrated_lognormal_forward_moment
-- name    : FinancialDerivatives.FD06.integrated_lognormal_forward_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:42:25.3185+00:00
-- url     : https://prove2.me/theorems/723b86c5-73a4-44a8-8508-0999b6e89213
-- title:
--   Expected terminal lognormal stock equals deterministic forward
-- statement:
--   Expected terminal lognormal stock equals deterministic forward
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6, with explicit analytic extensions.

import Mathlib
import Definitions.Def_fd06_deterministicForward
import Definitions.Def_fd06_lognormalTerminal
open MeasureTheory intervalIntegral

namespace FinancialDerivatives.FD06

theorem integrated_lognormal_forward_moment (S R Q V : ℝ) (hV : 0 ≤ V) : (∫ z : ℝ, lognormalTerminal S R Q V z ∂ProbabilityTheory.gaussianReal 0 1) = deterministicForward S R Q := by sorry

end FinancialDerivatives.FD06
