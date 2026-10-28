-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_put_payoff_convex_strike
-- name    : FinancialDerivatives.FD01.put_payoff_convex_strike
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:14:46.465445+00:00
-- url     : https://prove2.me/theorems/497342ba-2c5b-4ccb-8fac-1f5ae71cc322
-- title:
--   Put payoff is convex in strike
-- statement:
--   Put payoff is convex in strike. The nonnegative convex weights sum to one, and the terminal underlying is fixed across the strikes. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   p_{\lambda K_1+(1-\lambda)K_2}(s)\leq\lambda p_{K_1}(s)+(1-\lambda)p_{K_2}(s)
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 38, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. The nonnegative convex weights sum to one, and the terminal underlying is fixed across the strikes.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FinancialDerivatives.FD01

theorem put_payoff_convex_strike (s K₁ K₂ w : ℝ) (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1) :
  max ((w * K₁ + (1 - w) * K₂) - s) 0 ≤ w * max (K₁ - s) 0 + (1 - w) * max (K₂ - s) 0 := by sorry

end FinancialDerivatives.FD01
