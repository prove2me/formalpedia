-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_call_butterfly_payoff_nonneg
-- name    : FinancialDerivatives.FD01.call_butterfly_payoff_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:15:24.010487+00:00
-- url     : https://prove2.me/theorems/67e93787-2a5f-4aaf-8f00-a8a5d3c951ee
-- title:
--   Equal-spacing call butterfly has nonnegative payoff
-- statement:
--   Equal-spacing call butterfly has nonnegative payoff. The wings and middle call have the same expiry; the middle strike is the arithmetic midpoint of the two wings. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   0\leq c_{K_1}(s)-2c_{K_2}(s)+c_{K_3}(s)
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 40, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. The wings and middle call have the same expiry; the middle strike is the arithmetic midpoint of the two wings.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FinancialDerivatives.FD01

theorem call_butterfly_payoff_nonneg (s K₁ K₂ K₃ : ℝ) (hK₁ : K₁ ≤ K₂) (hK₂ : K₂ ≤ K₃) (hmid : 2 * K₂ = K₁ + K₃) :
  0 ≤ max (s - K₁) 0 - 2 * max (s - K₂) 0 + max (s - K₃) 0 := by sorry

end FinancialDerivatives.FD01
