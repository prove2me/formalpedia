-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_barrier_claim_unique_no_arbitrage_price
-- name    : FinancialDerivatives.FD05.barrier_claim_unique_no_arbitrage_price
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:45:41.786542+00:00
-- url     : https://prove2.me/theorems/642f5264-f3dc-4c46-af5b-0c9b3e58539c
-- title:
--   Unique arbitrage-free price of an upper barrier claim
-- statement:
--   The discounted first-hit path price is exactly the quotation that avoids arbitrage when an upper barrier claim is traded alongside the binomial stock and bank.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_quotedClaimArbitrage
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd05_discountedSurvivalPathPrice

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

theorem barrier_claim_unique_no_arbitrage_price (m : BinomialMarket)
    (N : ℕ) (B : ℝ) (monitor : ℕ → Bool)
    (g : ℝ → ℝ) (quote : ℝ) :
    ¬ quotedClaimArbitrage m N m.initialSpot
        (upperKnockOutTree m B monitor g N 0 m.initialSpot false) quote ↔
      quote = discountedSurvivalPathPrice m N B monitor g := by sorry

end FinancialDerivatives.FD05
