-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_put_vertical_spread_payoff_bounds
-- name    : FinancialDerivatives.FD01.put_vertical_spread_payoff_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:15:15.166009+00:00
-- url     : https://prove2.me/theorems/f928d2ab-ad62-4247-9a00-19ad1adbd4d2
-- title:
--   Bear put vertical-spread payoff has bounded range
-- statement:
--   Bear put vertical-spread payoff has bounded range. A long higher-strike put and short lower-strike put share expiry and have a nonnegative capped payoff. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   0\leq p_{K_2}(s)-p_{K_1}(s)\leq K_2-K_1
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 39, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. A long higher-strike put and short lower-strike put share expiry and have a nonnegative capped payoff.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FinancialDerivatives.FD01

theorem put_vertical_spread_payoff_bounds (s K₁ K₂ : ℝ) (hK : K₁ ≤ K₂) :
  0 ≤ max (K₂ - s) 0 - max (K₁ - s) 0 ∧ max (K₂ - s) 0 - max (K₁ - s) 0 ≤ K₂ - K₁ := by sorry

end FinancialDerivatives.FD01
