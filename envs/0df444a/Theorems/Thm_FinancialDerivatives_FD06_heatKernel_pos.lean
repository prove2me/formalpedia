-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_heatKernel_pos
-- name    : FinancialDerivatives.FD06.heatKernel_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:23:18.400668+00:00
-- url     : https://prove2.me/theorems/db2e53cb-baea-47f4-9ed4-4074acd0feeb
-- title:
--   Strict positivity of the Gaussian heat kernel
-- statement:
--   Strict positivity of the Gaussian heat kernel
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_heatKernel

namespace FinancialDerivatives.FD06

theorem heatKernel_pos (τ x : ℝ) (hτ : 0 < τ) : 0 < heatKernel τ x := by sorry

end FinancialDerivatives.FD06
