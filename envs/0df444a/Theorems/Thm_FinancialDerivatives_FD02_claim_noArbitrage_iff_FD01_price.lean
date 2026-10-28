-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_claim_noArbitrage_iff_FD01_price
-- name    : FinancialDerivatives.FD02.claim_noArbitrage_iff_FD01_price
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:15:27.293267+00:00
-- url     : https://prove2.me/theorems/557feedf-35af-4f38-b261-b88ce9cffa20
-- title:
--   No-arbitrage quotation is FD-01 state-price valuation
-- statement:
--   Strong no-arbitrage constructs the actual FD-01 state-price system with prescribed positive Arrow prices. A derivative extension is arbitrage-free exactly when its quotation equals the system's valuation.
--
--   This is an original derived proof obligation in the private FD-02 authoring graph.
-- source:
--   Wilmott, Howison and Dewynne (1995), §§3.2,10.1–10.3, pp. 33–34 and 180–187; original finite-market formalisation. https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp
import Definitions.Def_fd02_riskNeutralValue
import Definitions.Def_fd02_toFD01PriceSystem
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_NoArbitrage
import Definitions.Def_fd02_ClaimNoArbitrage

namespace FinancialDerivatives.FD02

/-- No-arbitrage quotation is FD-01 state-price valuation. -/
theorem claim_noArbitrage_iff_FD01_price (m : TwoStateMarket) (hNA : NoArbitrage m) (H : Bool → ℝ) :
  ∃ sys : FinancialDerivatives.FD01.FinitePriceSystem Bool, sys.statePrice true = riskNeutralUp m / m.growth ∧ sys.statePrice false = (1 - riskNeutralUp m) / m.growth ∧ (∀ p : ℝ, ClaimNoArbitrage m H p ↔ p = sys.price H) := by sorry

end FinancialDerivatives.FD02
