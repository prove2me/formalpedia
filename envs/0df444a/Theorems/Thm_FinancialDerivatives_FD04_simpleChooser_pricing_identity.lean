-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_simpleChooser_pricing_identity
-- name    : FinancialDerivatives.FD04.simpleChooser_pricing_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:53:35.41224+00:00
-- url     : https://prove2.me/theorems/1d63245c-fd57-49e6-8f22-0df76fcadf79
-- title:
--   MAIN GOAL: finite-binomial simple chooser pricing formula
-- statement:
--   For a simple chooser at choice date n and common final expiry after another k steps, inception chooser price equals the vanilla call expiring at n+k plus a put expiring at n with strike K/R^k.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_chooserInitialValue
import Definitions.Def_fd04_callInitialValue
import Definitions.Def_fd04_putInitialValue
import Definitions.Def_fd04_discountedStrike

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

theorem simpleChooser_pricing_identity (m : BinomialMarket)
    (K : ℝ) (choiceSteps postChoiceSteps : ℕ) :
    chooserInitialValue m K choiceSteps postChoiceSteps =
      callInitialValue m K (choiceSteps + postChoiceSteps) +
      putInitialValue m (discountedStrike m K postChoiceSteps)
        choiceSteps := by sorry

end FinancialDerivatives.FD04
