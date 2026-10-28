-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_call_price_convex_strike
-- name    : FinancialDerivatives.FD01.call_price_convex_strike
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:17:39.98466+00:00
-- url     : https://prove2.me/theorems/287ebd25-d79a-4299-a31d-430a32a41f89
-- title:
--   European call-price surface is convex in exercise price
-- statement:
--   European call-price surface is convex in exercise price. The valuation operator uses one nonnegative state-price vector for all three strikes, preserving terminal convexity. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   C(\lambda K_1+(1-\lambda)K_2)\leq\lambda C(K_1)+(1-\lambda)C(K_2)
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 40, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. The valuation operator uses one nonnegative state-price vector for all three strikes, preserving terminal convexity.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_callValue

namespace FinancialDerivatives.FD01

theorem call_price_convex_strike {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K₁ K₂ w : ℝ) (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1) :
  m.callValue s (w * K₁ + (1 - w) * K₂) ≤ w * m.callValue s K₁ + (1 - w) * m.callValue s K₂ := by sorry

end FinancialDerivatives.FD01
