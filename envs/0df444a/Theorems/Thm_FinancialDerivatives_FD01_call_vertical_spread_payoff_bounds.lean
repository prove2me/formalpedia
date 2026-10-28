-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_call_vertical_spread_payoff_bounds
-- name    : FinancialDerivatives.FD01.call_vertical_spread_payoff_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:15:06.41381+00:00
-- url     : https://prove2.me/theorems/6b5332b2-0751-4e47-a8a8-666309ed1f1b
-- title:
--   Bull call vertical-spread payoff has bounded range
-- statement:
--   Bull call vertical-spread payoff has bounded range. A long lower-strike call and short higher-strike call share expiry and the same terminal asset, as in Figure 3.5. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   0\leq c_{K_1}(s)-c_{K_2}(s)\leq K_2-K_1
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 39, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. A long lower-strike call and short higher-strike call share expiry and the same terminal asset, as in Figure 3.5.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FinancialDerivatives.FD01

theorem call_vertical_spread_payoff_bounds (s K₁ K₂ : ℝ) (hK : K₁ ≤ K₂) :
  0 ≤ max (s - K₁) 0 - max (s - K₂) 0 ∧ max (s - K₁) 0 - max (s - K₂) 0 ≤ K₂ - K₁ := by sorry

end FinancialDerivatives.FD01
