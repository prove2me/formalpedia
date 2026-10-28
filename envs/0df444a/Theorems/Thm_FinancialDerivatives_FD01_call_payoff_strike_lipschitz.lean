-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_call_payoff_strike_lipschitz
-- name    : FinancialDerivatives.FD01.call_payoff_strike_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:32:15.616417+00:00
-- url     : https://prove2.me/theorems/6f87b70a-6bca-44e1-8aee-61d639e9e0e6
-- title:
--   Call payoff is one-Lipschitz in strike
-- statement:
--   Call payoff is one-Lipschitz in strike. The absolute terminal call-payoff change is bounded by the absolute difference between exercise prices. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   \lvert c_{K_1}(s)-c_{K_2}(s)\rvert\leq\lvert K_1-K_2\rvert
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 36, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. The absolute terminal call-payoff change is bounded by the absolute difference between exercise prices.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FinancialDerivatives.FD01

theorem call_payoff_strike_lipschitz (s K₁ K₂ : ℝ) :
  |max (s - K₁) 0 - max (s - K₂) 0| ≤ |K₁ - K₂| := by sorry

end FinancialDerivatives.FD01
