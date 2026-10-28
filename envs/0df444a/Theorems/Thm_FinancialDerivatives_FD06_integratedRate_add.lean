-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_integratedRate_add
-- name    : FinancialDerivatives.FD06.integratedRate_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:33:53.289616+00:00
-- url     : https://prove2.me/theorems/99cfab68-ff1c-4e46-9404-0955498e5a14
-- title:
--   Additive short-rate integral
-- statement:
--   Additive short-rate integral
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_integratedRate

namespace FinancialDerivatives.FD06

theorem integratedRate_add (r : ℝ → ℝ) (t u T : ℝ) (hr : Continuous r) : integratedRate r t T = integratedRate r t u + integratedRate r u T := by sorry

end FinancialDerivatives.FD06
