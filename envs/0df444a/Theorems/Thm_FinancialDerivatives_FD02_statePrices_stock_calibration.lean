-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_statePrices_stock_calibration
-- name    : FinancialDerivatives.FD02.statePrices_stock_calibration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:08:48.757324+00:00
-- url     : https://prove2.me/theorems/927d0949-f820-4fe2-95f0-cae030dfe07f
-- title:
--   Constructed state prices correctly value the share
-- statement:
--   Under the unique martingale weights, the FD-01 price of the stock's up/down terminal payoffs equals its initial share price S0.
--
--   This is an original derived proof obligation in the private FD-02 authoring graph.
-- source:
--   Wilmott, Howison and Dewynne (1995), §10.2, equation (10.4), pp. 183–184; original finite-market formalisation. https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp
import Definitions.Def_fd02_riskNeutralValue
import Definitions.Def_fd02_toFD01PriceSystem

namespace FinancialDerivatives.FD02

/-- Constructed state prices correctly value the share. -/
theorem statePrices_stock_calibration (m : TwoStateMarket) (hq0 : 0 < riskNeutralUp m) (hq1 : riskNeutralUp m < 1) :
  (toFD01PriceSystem m hq0 hq1).price (fun ω : Bool => if ω then m.spot * m.up else m.spot * m.down) = m.spot := by sorry

end FinancialDerivatives.FD02
