-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_generalised_call_vega_variance
-- name    : FinancialDerivatives.FD06.generalised_call_vega_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:41:55.053117+00:00
-- url     : https://prove2.me/theorems/c7b25c4e-74c3-4023-a12d-2b3dac80f4ab
-- title:
--   Call sensitivity to total integrated variance
-- statement:
--   Call sensitivity to total integrated variance
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6, with explicit analytic extensions.

import Mathlib
import Definitions.Def_fd06_generalisedCall
import Definitions.Def_fd06_generalisedD1
import Definitions.Def_fd06_standardNormalDensity

namespace FinancialDerivatives.FD06

theorem generalised_call_vega_variance (S K R Q V : ℝ) (hS : 0 < S) (hK : 0 < K) (hV : 0 < V) : deriv (fun v => generalisedCall S K R Q v) V = S * Real.exp (-Q) * standardNormalDensity (generalisedD1 S K R Q V) / (2 * Real.sqrt V) := by sorry

end FinancialDerivatives.FD06
