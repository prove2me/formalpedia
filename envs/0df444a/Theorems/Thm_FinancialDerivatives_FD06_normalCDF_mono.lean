-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_normalCDF_mono
-- name    : FinancialDerivatives.FD06.normalCDF_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:21:23.45341+00:00
-- url     : https://prove2.me/theorems/8ae39d09-5464-4f2d-a841-ea725a94d6ec
-- title:
--   Normal CDF is monotone
-- statement:
--   Normal CDF is monotone
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_standardNormalCDF

namespace FinancialDerivatives.FD06

theorem normalCDF_mono : Monotone standardNormalCDF := by sorry

end FinancialDerivatives.FD06
