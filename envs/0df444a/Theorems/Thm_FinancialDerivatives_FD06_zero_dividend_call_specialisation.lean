-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_zero_dividend_call_specialisation
-- name    : FinancialDerivatives.FD06.zero_dividend_call_specialisation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:38:39.873563+00:00
-- url     : https://prove2.me/theorems/54facd13-28a7-4f8e-9572-da66eb5fa010
-- title:
--   Zero-dividend specialisation
-- statement:
--   Zero-dividend specialisation
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_generalisedCall
import Definitions.Def_fd06_generalisedD1
import Definitions.Def_fd06_generalisedD2
import Definitions.Def_fd06_standardNormalCDF

namespace FinancialDerivatives.FD06

theorem zero_dividend_call_specialisation (S K R V : ℝ) : generalisedCall S K R 0 V = S * standardNormalCDF (generalisedD1 S K R 0 V) - K * Real.exp (-R) * standardNormalCDF (generalisedD2 S K R 0 V) := by sorry

end FinancialDerivatives.FD06
