-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_put_payoff_antitone_spot
-- name    : FinancialDerivatives.FD01.put_payoff_antitone_spot
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:31:52.004691+00:00
-- url     : https://prove2.me/theorems/1431a1ba-de93-4e4d-8eae-d2b7b9891a13
-- title:
--   Put payoff falls with the terminal underlying
-- statement:
--   Put payoff falls with the terminal underlying. A put exercised at the same strike becomes no more valuable at maturity when the underlying increases. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   s_1\leq s_2\ \Longrightarrow\ p_K(s_2)\leq p_K(s_1)
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 38, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. A put exercised at the same strike becomes no more valuable at maturity when the underlying increases.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FinancialDerivatives.FD01

theorem put_payoff_antitone_spot (s₁ s₂ K : ℝ) (hs : s₁ ≤ s₂) :
  max (K - s₂) 0 ≤ max (K - s₁) 0 := by sorry

end FinancialDerivatives.FD01
