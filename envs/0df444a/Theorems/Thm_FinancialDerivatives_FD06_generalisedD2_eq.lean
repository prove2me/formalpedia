-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_generalisedD2_eq
-- name    : FinancialDerivatives.FD06.generalisedD2_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:26:17.819756+00:00
-- url     : https://prove2.me/theorems/27b0f696-9779-4d8e-80a1-6772966d899a
-- title:
--   Exact d2 relation
-- statement:
--   Exact d2 relation
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_generalisedD1
import Definitions.Def_fd06_generalisedD2

namespace FinancialDerivatives.FD06

theorem generalisedD2_eq (S K R Q V : ℝ) : generalisedD2 S K R Q V = generalisedD1 S K R Q V - Real.sqrt V := by sorry

end FinancialDerivatives.FD06
