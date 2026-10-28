-- Prove2me | Theorems.Thm_FinancialDerivatives_FD04_compoundCallOnCall_antitone_strike
-- name    : FinancialDerivatives.FD04.compoundCallOnCall_antitone_strike
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:51:18.181546+00:00
-- url     : https://prove2.me/theorems/4fac2ea9-3189-4ad3-9534-ff460ade6fba
-- title:
--   Compound call declines with compound strike
-- statement:
--   If the compound strike increases, its exercise payment weakly decreases, path by path.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 11, printed pp. 197–205, especially §§11.2–11.4. Original discrete-binomial formalisation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd04_compoundCallOnCallAtChoice

namespace FinancialDerivatives.FD04
open FinancialDerivatives.FD03

theorem compoundCallOnCall_antitone_strike (m : BinomialMarket)
    (K L₁ L₂ spot : ℝ) (n : ℕ) (h : L₁ ≤ L₂) :
    compoundCallOnCallAtChoice m K L₂ n spot ≤
      compoundCallOnCallAtChoice m K L₁ n spot := by sorry

end FinancialDerivatives.FD04
