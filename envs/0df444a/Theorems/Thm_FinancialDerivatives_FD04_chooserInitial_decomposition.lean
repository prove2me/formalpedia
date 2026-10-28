-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_chooserInitial_decomposition
-- name    : FinancialDerivatives.FD04.chooserInitial_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:50:10.281185+00:00
-- url     : https://prove2.me/theorems/2db55bff-bbe6-418a-abfd-ad4c1ae7ab56
-- title:
--   Chooser price separated at the decision date
-- statement:
--   The initial chooser premium equals the value of receiving the later call at choice time plus an earlier-expiring put at the discounted strike.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue
import Definitions.Def_fd03_payoffTreeMap
import Definitions.Def_fd03_terminalStockTree
import Definitions.Def_fd04_chooserInitialValue
import Definitions.Def_fd04_callAtChoice
import Definitions.Def_fd04_putInitialValue
import Definitions.Def_fd04_discountedStrike

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

theorem chooserInitial_decomposition (m : BinomialMarket)
    (K : ℝ) (choiceSteps postChoiceSteps : ℕ) :
    chooserInitialValue m K choiceSteps postChoiceSteps =
      europeanValue m choiceSteps
        (payoffTreeMap (callAtChoice m K postChoiceSteps) choiceSteps
          (terminalStockTree m choiceSteps m.initialSpot)) +
      putInitialValue m (discountedStrike m K postChoiceSteps)
        choiceSteps := by sorry

end FinancialDerivatives.FD04
