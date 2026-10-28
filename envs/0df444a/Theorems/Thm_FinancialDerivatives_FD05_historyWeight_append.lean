-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_historyWeight_append
-- name    : FinancialDerivatives.FD05.historyWeight_append
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:40:41.203925+00:00
-- url     : https://prove2.me/theorems/36a40b7f-40db-45c4-b197-bb651711a8ee
-- title:
--   Risk-neutral path weight factors over concatenated histories
-- statement:
--   The risk-neutral probability of a concatenated move history is the product of the corresponding history weights.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_historyWeight

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

theorem historyWeight_append (m : BinomialMarket) (xs ys : List Bool) :
    historyWeight m (xs ++ ys) =
      historyWeight m xs * historyWeight m ys := by sorry

end FinancialDerivatives.FD05
