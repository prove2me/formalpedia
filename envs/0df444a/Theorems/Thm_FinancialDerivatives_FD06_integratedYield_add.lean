-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_integratedYield_add
-- name    : FinancialDerivatives.FD06.integratedYield_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:34:21.507884+00:00
-- url     : https://prove2.me/theorems/d27ea583-da15-47c8-beb2-ce90caf7239f
-- title:
--   Additive dividend-yield integral
-- statement:
--   Additive dividend-yield integral
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_integratedYield

namespace FinancialDerivatives.FD06

theorem integratedYield_add (q : ℝ → ℝ) (t u T : ℝ) (hq : Continuous q) : integratedYield q t T = integratedYield q t u + integratedYield q u T := by sorry

end FinancialDerivatives.FD06
