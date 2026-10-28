-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_call_price_tower
-- name    : FinancialDerivatives.FD04.call_price_tower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:49:56.859334+00:00
-- url     : https://prove2.me/theorems/0b4ffc98-b005-4c5e-8a31-b32199dd3b4f
-- title:
--   Two-stage call-price valuation
-- statement:
--   Pricing the future choice-date call value back to inception equals pricing the call directly over the sum of choice and post-choice steps.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_payoffTreeMap
import Definitions.Def_fd03_terminalStockTree
import Definitions.Def_fd04_callAtChoice
import Definitions.Def_fd04_callInitialValue

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

theorem call_price_tower (m : BinomialMarket) (K : ℝ)
    (choiceSteps postChoiceSteps : ℕ) :
    europeanValue m choiceSteps
      (payoffTreeMap (callAtChoice m K postChoiceSteps)
        choiceSteps (terminalStockTree m choiceSteps m.initialSpot)) =
    callInitialValue m K (choiceSteps + postChoiceSteps) := by sorry

end FinancialDerivatives.FD04
