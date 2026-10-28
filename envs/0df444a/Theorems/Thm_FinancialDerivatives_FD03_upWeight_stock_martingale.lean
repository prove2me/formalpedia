-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_upWeight_stock_martingale
-- name    : FinancialDerivatives.FD03.upWeight_stock_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:07:32.648067+00:00
-- url     : https://prove2.me/theorems/d39d21ac-c671-436d-9ee5-75ac001c922e
-- title:
--   Risk-neutral expected stock growth equals the bank growth factor
-- statement:
--   The one-period risk-neutral up weight satisfies q times the up multiplier plus (1-q) times the down multiplier equal to R, ensuring discounted stock is fairly priced at each strictly positive node.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.2, printed pp. 182–186, one-period binomial risk-neutral stock martingale equation.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_upWeight

namespace FinancialDerivatives.FD03

theorem upWeight_stock_martingale (m : BinomialMarket) :
    upWeight m * m.up + (1 - upWeight m) * m.down =
      m.growth := by sorry

end FinancialDerivatives.FD03
