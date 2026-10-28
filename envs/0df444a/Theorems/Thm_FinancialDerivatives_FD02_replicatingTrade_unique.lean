-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_replicatingTrade_unique
-- name    : FinancialDerivatives.FD02.replicatingTrade_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:12:37.100801+00:00
-- url     : https://prove2.me/theorems/07e01c73-10b3-4076-bfdf-3347cad2021f
-- title:
--   Nondegenerate stock and bank holdings make a hedge unique
-- statement:
--   If two stock-and-bank portfolios deliver the same terminal claim, their share holdings agree because the stock factors differ, and their cash holdings then agree because bank growth is positive.
--
--   A proof must use the exact published definitions and be accepted by the authoritative Prove2Me compiler.
-- source:
--   Original derived theorem based on Wilmott, Howison and Dewynne (1995), §§2.4,3.2, pp. 30–34; https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_terminalPayoff
import Definitions.Def_fd02_Replicates

namespace FinancialDerivatives.FD02

/-- Nondegenerate stock and bank holdings make a hedge unique. -/
theorem replicatingTrade_unique (m : TwoStateMarket) (H : Bool → ℝ) (a b : Trade) (ha : Replicates m a H) (hb : Replicates m b H) :
  a = b := by sorry

end FinancialDerivatives.FD02
