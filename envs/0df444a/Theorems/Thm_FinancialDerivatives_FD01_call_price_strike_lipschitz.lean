-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_call_price_strike_lipschitz
-- name    : FinancialDerivatives.FD01.call_price_strike_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:17:12.190651+00:00
-- url     : https://prove2.me/theorems/bf1873ff-e12b-45a1-bdbf-5b6fe607a4ae
-- title:
--   Call premium is discount-Lipschitz in strike
-- statement:
--   Call premium is discount-Lipschitz in strike. Any two strikes at the same maturity have call prices whose difference is bounded by the discounted strike difference. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   \lvert C(K_1)-C(K_2)\rvert\leq D\lvert K_1-K_2\rvert
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 40, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. Any two strikes at the same maturity have call prices whose difference is bounded by the discounted strike difference.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_callValue

namespace FinancialDerivatives.FD01

theorem call_price_strike_lipschitz {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K₁ K₂ : ℝ) :
  |m.callValue s K₁ - m.callValue s K₂| ≤ m.discount * |K₁ - K₂| := by sorry

end FinancialDerivatives.FD01
