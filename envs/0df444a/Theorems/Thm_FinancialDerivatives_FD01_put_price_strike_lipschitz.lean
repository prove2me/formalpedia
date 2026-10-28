-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_put_price_strike_lipschitz
-- name    : FinancialDerivatives.FD01.put_price_strike_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:17:25.078785+00:00
-- url     : https://prove2.me/theorems/b3ea7d1b-08dc-4957-9206-e3bcd48e052a
-- title:
--   Put premium is discount-Lipschitz in strike
-- statement:
--   Put premium is discount-Lipschitz in strike. Any two strikes at the same maturity have put prices whose difference is bounded by the discounted strike difference. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   \lvert P(K_1)-P(K_2)\rvert\leq D\lvert K_1-K_2\rvert
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 40, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. Any two strikes at the same maturity have put prices whose difference is bounded by the discounted strike difference.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_putValue

namespace FinancialDerivatives.FD01

theorem put_price_strike_lipschitz {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K₁ K₂ : ℝ) :
  |m.putValue s K₁ - m.putValue s K₂| ≤ m.discount * |K₁ - K₂| := by sorry

end FinancialDerivatives.FD01
