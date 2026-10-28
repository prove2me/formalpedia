-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_generalised_call_gamma
-- name    : FinancialDerivatives.FD06.generalised_call_gamma
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:32:38.500974+00:00
-- url     : https://prove2.me/theorems/f6f828f1-4c22-478d-94bc-0efe025d0a0c
-- title:
--   Generalised call gamma
-- statement:
--   Generalised call gamma
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_generalisedCall
import Definitions.Def_fd06_generalisedD1
import Definitions.Def_fd06_standardNormalDensity

namespace FinancialDerivatives.FD06

theorem generalised_call_gamma (S K R Q V : ℝ) (hS : 0 < S) (hK : 0 < K) (hV : 0 < V) : deriv (deriv (fun x => generalisedCall x K R Q V)) S = Real.exp (-Q) * standardNormalDensity (generalisedD1 S K R Q V) / (S * Real.sqrt V) := by sorry

end FinancialDerivatives.FD06
