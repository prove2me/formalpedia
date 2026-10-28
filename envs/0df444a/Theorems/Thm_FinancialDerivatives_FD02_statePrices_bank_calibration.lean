-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_statePrices_bank_calibration
-- name    : FinancialDerivatives.FD02.statePrices_bank_calibration
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:08:23.897179+00:00
-- url     : https://prove2.me/theorems/2b3c6ec8-a41a-48a5-82dc-3f19d168d1d2
-- title:
--   Constructed state prices correctly value one bank deposit
-- statement:
--   The positive Arrow–Debreu prices value the bank-account claim paying R in either state at exactly its initial unit cost.
--
--   This is an original derived proof obligation in the private FD-02 authoring graph.
-- source:
--   Wilmott, Howison and Dewynne (1995), §§3.2,10.1, pp. 33–34 and 182; original finite-market formalisation. https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp
import Definitions.Def_fd02_riskNeutralValue
import Definitions.Def_fd02_toFD01PriceSystem

namespace FinancialDerivatives.FD02

/-- Constructed state prices correctly value one bank deposit. -/
theorem statePrices_bank_calibration (m : TwoStateMarket) (hq0 : 0 < riskNeutralUp m) (hq1 : riskNeutralUp m < 1) :
  (toFD01PriceSystem m hq0 hq1).price (fun _ : Bool => m.growth) = 1 := by sorry

end FinancialDerivatives.FD02
