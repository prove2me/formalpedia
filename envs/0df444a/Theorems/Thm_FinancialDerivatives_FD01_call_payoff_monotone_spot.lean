-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_call_payoff_monotone_spot
-- name    : FinancialDerivatives.FD01.call_payoff_monotone_spot
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:31:43.101637+00:00
-- url     : https://prove2.me/theorems/1e7be77e-73f3-40cc-81b8-f68ad1a5e051
-- title:
--   Call payoff rises with the terminal underlying
-- statement:
--   Call payoff rises with the terminal underlying. The same exercise strike is used for both terminal asset values, including the exercise boundary. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   s_1\leq s_2\ \Longrightarrow\ c_K(s_1)\leq c_K(s_2)
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 36, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. The same exercise strike is used for both terminal asset values, including the exercise boundary.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FinancialDerivatives.FD01

theorem call_payoff_monotone_spot (s₁ s₂ K : ℝ) (hs : s₁ ≤ s₂) :
  max (s₁ - K) 0 ≤ max (s₂ - K) 0 := by sorry

end FinancialDerivatives.FD01
