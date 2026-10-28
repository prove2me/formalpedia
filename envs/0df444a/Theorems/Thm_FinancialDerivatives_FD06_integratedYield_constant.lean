-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_integratedYield_constant
-- name    : FinancialDerivatives.FD06.integratedYield_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:36:14.377387+00:00
-- url     : https://prove2.me/theorems/e38d7e55-7858-4f0a-a7ee-5fbb35d2d67a
-- title:
--   Integrated constant dividend yield
-- statement:
--   Integrated constant dividend yield
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_integratedYield

namespace FinancialDerivatives.FD06

theorem integratedYield_constant (q t T : ℝ) : integratedYield (fun _ => q) t T = q * (T - t) := by sorry

end FinancialDerivatives.FD06
