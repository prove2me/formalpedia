-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_normalCDF_symmetry
-- name    : FinancialDerivatives.FD06.normalCDF_symmetry
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:20:54.718848+00:00
-- url     : https://prove2.me/theorems/443dc006-923d-4ec3-9768-6e5151b5ed69
-- title:
--   Standard normal CDF reflection symmetry
-- statement:
--   Standard normal CDF reflection symmetry
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_standardNormalCDF

namespace FinancialDerivatives.FD06

theorem normalCDF_symmetry (x : ℝ) : standardNormalCDF (-x) = 1 - standardNormalCDF x := by sorry

end FinancialDerivatives.FD06
