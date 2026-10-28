-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_heatFlow_constant
-- name    : FinancialDerivatives.FD06.heatFlow_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:24:36.811269+00:00
-- url     : https://prove2.me/theorems/08a77182-778f-4019-b5d4-0e3850a60e95
-- title:
--   Heat flow preserves constants
-- statement:
--   Heat flow preserves constants
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_gaussianHeatFlow

namespace FinancialDerivatives.FD06

theorem heatFlow_constant (c τ x : ℝ) : gaussianHeatFlow (fun _ => c) τ x = c := by sorry

end FinancialDerivatives.FD06
