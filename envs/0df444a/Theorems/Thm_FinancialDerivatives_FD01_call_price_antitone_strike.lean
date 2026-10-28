-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_call_price_antitone_strike
-- name    : FinancialDerivatives.FD01.call_price_antitone_strike
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:16:46.330973+00:00
-- url     : https://prove2.me/theorems/b62a8216-ebcf-4e01-a9a3-8a636d1bae52
-- title:
--   Call premium falls as the strike increases
-- statement:
--   Call premium falls as the strike increases. Pointwise exercise-payoff dominance transfers to today's prices through positivity of the common pricing operator. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   K_1\leq K_2\ \Longrightarrow\ C(K_2)\leq C(K_1)
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 40, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. Pointwise exercise-payoff dominance transfers to today's prices through positivity of the common pricing operator.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_callValue

namespace FinancialDerivatives.FD01

theorem call_price_antitone_strike {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K₁ K₂ : ℝ) (hK : K₁ ≤ K₂) :
  m.callValue s K₂ ≤ m.callValue s K₁ := by sorry

end FinancialDerivatives.FD01
