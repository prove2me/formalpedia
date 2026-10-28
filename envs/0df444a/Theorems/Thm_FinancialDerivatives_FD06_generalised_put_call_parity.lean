-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_generalised_put_call_parity
-- name    : FinancialDerivatives.FD06.generalised_put_call_parity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:29:29.881831+00:00
-- url     : https://prove2.me/theorems/4f907eed-b9ce-4147-a8bd-606796df0727
-- title:
--   Dividend-adjusted Black-Scholes put-call parity
-- statement:
--   Dividend-adjusted Black-Scholes put-call parity
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_generalisedCall
import Definitions.Def_fd06_generalisedPut

namespace FinancialDerivatives.FD06

theorem generalised_put_call_parity (S K R Q V : ℝ) (hS : 0 < S) (hK : 0 < K) (hV : 0 < V) : generalisedCall S K R Q V - generalisedPut S K R Q V = S * Real.exp (-Q) - K * Real.exp (-R) := by sorry

end FinancialDerivatives.FD06
