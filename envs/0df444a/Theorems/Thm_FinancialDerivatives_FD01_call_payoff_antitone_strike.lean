-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_call_payoff_antitone_strike
-- name    : FinancialDerivatives.FD01.call_payoff_antitone_strike
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:32:01.884202+00:00
-- url     : https://prove2.me/theorems/d5e5ad45-f19d-423d-8590-a0e1dff29e0d
-- title:
--   Call payoff falls when its exercise price rises
-- statement:
--   Call payoff falls when its exercise price rises. The same terminal asset is considered at two ordered exercise prices. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   K_1\leq K_2\ \Longrightarrow\ c_{K_2}(s)\leq c_{K_1}(s)
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 36, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. The same terminal asset is considered at two ordered exercise prices.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace FinancialDerivatives.FD01

theorem call_payoff_antitone_strike (s K₁ K₂ : ℝ) (hK : K₁ ≤ K₂) :
  max (s - K₂) 0 ≤ max (s - K₁) 0 := by sorry

end FinancialDerivatives.FD01
