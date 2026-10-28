-- Prove2me | Theorems.Thm_FinancialDerivatives_FD02_unique_replication_noArbitrage_pricing
-- name    : FinancialDerivatives.FD02.unique_replication_noArbitrage_pricing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:15:56.383378+00:00
-- url     : https://prove2.me/theorems/926e3eb2-f985-43cc-b044-88eea94f4018
-- title:
--   One-period replication, unique quote and FD-01 risk-neutral pricing
-- statement:
--   For an arbitrary signed terminal claim, prove a unique stock/cash replicator, a unique arbitrage-free derivative quote, and a constructed FD-01 state-price operator that agrees with discounted risk-neutral valuation and characterises all permitted quotes.
--
--   This is an original derived proof obligation in the private FD-02 authoring graph.
-- source:
--   Wilmott, Howison and Dewynne (1995), §§2.4,3.2,10.1–10.3, pp. 30–34 and 180–187; original finite-market formalisation. https://doi.org/10.1017/CBO9780511812545.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price
import Definitions.Def_fd02_TwoStateMarket
import Definitions.Def_fd02_riskNeutralUp
import Definitions.Def_fd02_riskNeutralValue
import Definitions.Def_fd02_toFD01PriceSystem
import Definitions.Def_fd02_Trade
import Definitions.Def_fd02_Replicates
import Definitions.Def_fd02_NoArbitrage
import Definitions.Def_fd02_ClaimNoArbitrage

namespace FinancialDerivatives.FD02

/-- One-period replication, unique quote and FD-01 risk-neutral pricing. -/
theorem unique_replication_noArbitrage_pricing (m : TwoStateMarket) (hNA : NoArbitrage m) (H : Bool → ℝ) :
  (∃! t : Trade, Replicates m t H) ∧ (∃! p : ℝ, ClaimNoArbitrage m H p) ∧ (∃ sys : FinancialDerivatives.FD01.FinitePriceSystem Bool, sys.statePrice true = riskNeutralUp m / m.growth ∧ sys.statePrice false = (1 - riskNeutralUp m) / m.growth ∧ sys.price H = riskNeutralValue m H ∧ (∀ p : ℝ, ClaimNoArbitrage m H p ↔ p = sys.price H)) := by sorry

end FinancialDerivatives.FD02
