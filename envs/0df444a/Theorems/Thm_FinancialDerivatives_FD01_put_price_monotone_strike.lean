-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_put_price_monotone_strike
-- name    : FinancialDerivatives.FD01.put_price_monotone_strike
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:16:56.031699+00:00
-- url     : https://prove2.me/theorems/26f208ad-056a-40f0-ac4f-e04700feb9f3
-- title:
--   Put premium rises as the strike increases
-- statement:
--   Put premium rises as the strike increases. Pointwise exercise-payoff dominance transfers to today's prices through positivity of the common pricing operator. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   K_1\leq K_2\ \Longrightarrow\ P(K_1)\leq P(K_2)
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 40, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. Pointwise exercise-payoff dominance transfers to today's prices through positivity of the common pricing operator.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_putValue

namespace FinancialDerivatives.FD01

theorem put_price_monotone_strike {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K₁ K₂ : ℝ) (hK : K₁ ≤ K₂) :
  m.putValue s K₁ ≤ m.putValue s K₂ := by sorry

end FinancialDerivatives.FD01
