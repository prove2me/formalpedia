-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_put_payoff_bounds
-- name    : FinancialDerivatives.FD01.put_payoff_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:31:35.582512+00:00
-- url     : https://prove2.me/theorems/db0de050-17a9-4f17-a3e7-bb043801ca56
-- title:
--   European put payoff cannot exceed its strike
-- statement:
--   European put payoff cannot exceed its strike. A nonnegative asset and strike bound the European put's maturity payment. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   0\leq(K-s)^+\leq K
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 38, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. A nonnegative asset and strike bound the European put's maturity payment.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FinancialDerivatives.FD01

theorem put_payoff_bounds (s K : ℝ) (hs : 0 ≤ s) (hK : 0 ≤ K) :
  0 ≤ max (K - s) 0 ∧ max (K - s) 0 ≤ K := by sorry

end FinancialDerivatives.FD01
