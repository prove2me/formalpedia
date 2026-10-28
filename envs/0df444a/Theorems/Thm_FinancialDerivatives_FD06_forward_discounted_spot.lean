-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_forward_discounted_spot
-- name    : FinancialDerivatives.FD06.forward_discounted_spot
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:37:29.357947+00:00
-- url     : https://prove2.me/theorems/1e17ebbd-0589-40ec-a743-2e87375d7bb6
-- title:
--   Prepaid forward identity
-- statement:
--   Prepaid forward identity
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_deterministicForward

namespace FinancialDerivatives.FD06

theorem forward_discounted_spot (S R Q : ℝ) : Real.exp (-R) * deterministicForward S R Q = S * Real.exp (-Q) := by sorry

end FinancialDerivatives.FD06
