-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_forward_carry_ratio
-- name    : FinancialDerivatives.FD06.forward_carry_ratio
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:37:02.052664+00:00
-- url     : https://prove2.me/theorems/e01561c0-1969-4a45-8ece-ccbee921b09d
-- title:
--   Forward price from deterministic carry
-- statement:
--   Forward price from deterministic carry
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_deterministicForward

namespace FinancialDerivatives.FD06

theorem forward_carry_ratio (S R Q : ℝ) (hS : 0 < S) : deterministicForward S R Q = S * Real.exp R / Real.exp Q := by sorry

end FinancialDerivatives.FD06
