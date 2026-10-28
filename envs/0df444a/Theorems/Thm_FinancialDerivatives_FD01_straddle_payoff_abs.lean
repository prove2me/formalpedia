-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_straddle_payoff_abs
-- name    : FinancialDerivatives.FD01.straddle_payoff_abs
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:14:55.785777+00:00
-- url     : https://prove2.me/theorems/a1935eb1-01cb-4ec3-980b-9d19d98893ec
-- title:
--   A call and put at one strike form an absolute-value straddle
-- statement:
--   A call and put at one strike form an absolute-value straddle. Both options share a strike and expiry, so their total maturity payment equals the absolute distance from the strike. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   c_K(s)+p_K(s)=\lvert s-K\rvert
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 39, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. Both options share a strike and expiry, so their total maturity payment equals the absolute distance from the strike.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FinancialDerivatives.FD01

theorem straddle_payoff_abs (s K : ℝ) :
  max (s - K) 0 + max (K - s) 0 = |s - K| := by sorry

end FinancialDerivatives.FD01
