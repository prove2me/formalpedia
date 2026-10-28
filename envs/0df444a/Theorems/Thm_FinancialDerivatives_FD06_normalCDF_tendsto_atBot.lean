-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_normalCDF_tendsto_atBot
-- name    : FinancialDerivatives.FD06.normalCDF_tendsto_atBot
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:22:26.04168+00:00
-- url     : https://prove2.me/theorems/05809226-e045-426c-972a-56e2b64eb489
-- title:
--   CDF tends to zero at negative infinity
-- statement:
--   CDF tends to zero at negative infinity
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_standardNormalCDF

namespace FinancialDerivatives.FD06

theorem normalCDF_tendsto_atBot : Filter.Tendsto standardNormalCDF Filter.atBot (nhds 0) := by sorry

end FinancialDerivatives.FD06
