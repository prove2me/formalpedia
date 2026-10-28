-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_generalised_call_delta
-- name    : FinancialDerivatives.FD06.generalised_call_delta
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:31:52.631873+00:00
-- url     : https://prove2.me/theorems/3e84b65b-b381-4d4f-b1cf-d4a8d4d1313f
-- title:
--   Generalised call delta
-- statement:
--   Generalised call delta
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_generalisedCall
import Definitions.Def_fd06_generalisedD1
import Definitions.Def_fd06_standardNormalCDF

namespace FinancialDerivatives.FD06

theorem generalised_call_delta (S K R Q V : ℝ) (hS : 0 < S) (hK : 0 < K) (hV : 0 < V) : deriv (fun x => generalisedCall x K R Q V) S = Real.exp (-Q) * standardNormalCDF (generalisedD1 S K R Q V) := by sorry

end FinancialDerivatives.FD06
