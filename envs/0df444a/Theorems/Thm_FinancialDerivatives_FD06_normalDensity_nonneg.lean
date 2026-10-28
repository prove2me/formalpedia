-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_normalDensity_nonneg
-- name    : FinancialDerivatives.FD06.normalDensity_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:22:56.060461+00:00
-- url     : https://prove2.me/theorems/2d20c214-1741-4554-92e9-8b552aa50195
-- title:
--   Nonnegativity of Gaussian density
-- statement:
--   Nonnegativity of Gaussian density
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_standardNormalDensity

namespace FinancialDerivatives.FD06

theorem normalDensity_nonneg (x : ℝ) : 0 ≤ standardNormalDensity x := by sorry

end FinancialDerivatives.FD06
