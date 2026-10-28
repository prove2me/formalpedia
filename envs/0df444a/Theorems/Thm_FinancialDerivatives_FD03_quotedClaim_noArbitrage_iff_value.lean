-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_quotedClaim_noArbitrage_iff_value
-- name    : FinancialDerivatives.FD03.quotedClaim_noArbitrage_iff_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:08:59.836641+00:00
-- url     : https://prove2.me/theorems/2ea37701-8911-464b-a018-688e33c02811
-- title:
--   The European backward price is the unique arbitrage-free initial quotation
-- statement:
--   For every finite horizon, positive initial stock price, and signed European payoff tree, the expanded market consisting of the stock, bank and a claim trading at quoted price Q has no zero-cost arbitrage if and only if Q equals the full-tree discounted risk-neutral value. Arbitrage means a self-financing portfolio in the stock and bank plus a fixed long or short derivative position, with zero net initial cost, nonnegative terminal cash in every state and strictly positive cash in some state.
-- source:
--   Original finite-market no-arbitrage quotation equivalence formalising the repeated two-state replication argument of Wilmott, Howison and Dewynne (1995), Chapter 10 §§10.2–10.4, printed pp. 182–189.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_quotedClaimArbitrage
import Definitions.Def_fd03_europeanValue

namespace FinancialDerivatives.FD03

theorem quotedClaim_noArbitrage_iff_value (m : BinomialMarket)
    (n : ℕ) (spot : ℝ) (hspot : 0 < spot)
    (claim : PayoffTree n) (quote : ℝ) :
    ¬ quotedClaimArbitrage m n spot claim quote ↔
      quote = europeanValue m n claim := by sorry

end FinancialDerivatives.FD03
