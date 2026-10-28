-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_call_payoff_bounds
-- name    : FinancialDerivatives.FD01.call_payoff_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:31:27.962156+00:00
-- url     : https://prove2.me/theorems/e4ef8909-d885-406b-97f7-627600076d3d
-- title:
--   European call payoff cannot exceed the asset
-- statement:
--   European call payoff cannot exceed the asset. A nonnegative asset payoff and strike bound a purchased European call's maturity payment. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   0\leq (s-K)^+\leq s
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 36, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. A nonnegative asset payoff and strike bound a purchased European call's maturity payment.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FinancialDerivatives.FD01

theorem call_payoff_bounds (s K : ℝ) (hs : 0 ≤ s) (hK : 0 ≤ K) :
  0 ≤ max (s - K) 0 ∧ max (s - K) 0 ≤ s := by sorry

end FinancialDerivatives.FD01
