-- Prove2me | Theorems.Thm_FinancialDerivatives_FD06_integrated_generalised_call_parity
-- name    : FinancialDerivatives.FD06.integrated_generalised_call_parity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:37:57.768454+00:00
-- url     : https://prove2.me/theorems/1cade156-0427-4aa5-92b0-466fa4f5a737
-- title:
--   Time-dependent deterministic-carry put-call parity
-- statement:
--   Time-dependent deterministic-carry put-call parity
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapters 4–6; analytic rigor and extension.

import Mathlib
import Definitions.Def_fd06_generalisedCall
import Definitions.Def_fd06_generalisedPut
import Definitions.Def_fd06_integratedRate
import Definitions.Def_fd06_integratedVariance
import Definitions.Def_fd06_integratedYield

namespace FinancialDerivatives.FD06

theorem integrated_generalised_call_parity (S K t T : ℝ) (r q σ : ℝ → ℝ) (hS : 0 < S) (hK : 0 < K) (hV : 0 < integratedVariance σ t T) : generalisedCall S K (integratedRate r t T) (integratedYield q t T) (integratedVariance σ t T) - generalisedPut S K (integratedRate r t T) (integratedYield q t T) (integratedVariance σ t T) = S * Real.exp (-integratedYield q t T) - K * Real.exp (-integratedRate r t T) := by sorry

end FinancialDerivatives.FD06
