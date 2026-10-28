-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_price_uniform_error_bound
-- name    : FinancialDerivatives.FD01.price_uniform_error_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:30:45.178979+00:00
-- url     : https://prove2.me/theorems/72466b87-1f94-4ed0-bf9b-3c470797ae26
-- title:
--   Uniform payoff errors have bounded price effects
-- statement:
--   Uniform payoff errors have bounded price effects. A nonnegative uniform error limit over all terminal states transfers to the same discount-scaled error at valuation. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   \lvert\mathcal V(f)-\mathcal V(g)\rvert\leq DB
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 41, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. A nonnegative uniform error limit over all terminal states transfers to the same discount-scaled error at valuation.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price

namespace FinancialDerivatives.FD01

theorem price_uniform_error_bound {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (f g : Ω → ℝ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ ω, |f ω - g ω| ≤ B) :
  |m.price f - m.price g| ≤ m.discount * B := by sorry

end FinancialDerivatives.FD01
