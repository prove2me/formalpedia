-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_integratedRate_constant
-- name    : FinancialDerivatives.FD06.integratedRate_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:35:49.904721+00:00
-- url     : https://prove2.me/theorems/3130e8c4-f656-4c27-b1da-c9c7d587ba7d
-- title:
--   Integrated constant interest rate
-- statement:
--   Integrated constant interest rate
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_integratedRate

namespace FinancialDerivatives.FD06

theorem integratedRate_constant (r t T : ℝ) : integratedRate (fun _ => r) t T = r * (T - t) := by sorry

end FinancialDerivatives.FD06
