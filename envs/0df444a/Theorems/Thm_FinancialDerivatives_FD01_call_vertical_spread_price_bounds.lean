-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_call_vertical_spread_price_bounds
-- name    : FinancialDerivatives.FD01.call_vertical_spread_price_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:18:09.269108+00:00
-- url     : https://prove2.me/theorems/165ea635-eaf1-4635-89d4-a0d1e590553e
-- title:
--   Bull call spread is priced between zero and discounted width
-- statement:
--   Bull call spread is priced between zero and discounted width. The lower-strike long call and higher-strike short call are on the same asset and settle at the same time. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   0\leq C(K_1)-C(K_2)\leq D(K_2-K_1)
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 40, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. The lower-strike long call and higher-strike short call are on the same asset and settle at the same time.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_callValue

namespace FinancialDerivatives.FD01

theorem call_vertical_spread_price_bounds {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K₁ K₂ : ℝ) (hK : K₁ ≤ K₂) :
  0 ≤ m.callValue s K₁ - m.callValue s K₂ ∧ m.callValue s K₁ - m.callValue s K₂ ≤ m.discount * (K₂ - K₁) := by sorry

end FinancialDerivatives.FD01
