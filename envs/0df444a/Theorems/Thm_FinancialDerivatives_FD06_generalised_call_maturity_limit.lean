-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_generalised_call_maturity_limit
-- name    : FinancialDerivatives.FD06.generalised_call_maturity_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:39:11.65097+00:00
-- url     : https://prove2.me/theorems/17881d3d-d2e1-4ab7-a2d4-d6ccee73f8ce
-- title:
--   Maturity value in zero-variance limit
-- statement:
--   Maturity value in zero-variance limit
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_generalisedCall

namespace FinancialDerivatives.FD06

theorem generalised_call_maturity_limit (S K : ℝ) (hS : 0 < S) (hK : 0 < K) : Filter.Tendsto (fun V : ℝ => generalisedCall S K 0 0 V) (nhdsWithin 0 (Set.Ioi 0)) (nhds (max (S - K) 0)) := by sorry

end FinancialDerivatives.FD06
