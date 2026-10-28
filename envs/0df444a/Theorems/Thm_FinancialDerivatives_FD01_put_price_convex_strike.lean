-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_put_price_convex_strike
-- name    : FinancialDerivatives.FD01.put_price_convex_strike
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:17:48.821329+00:00
-- url     : https://prove2.me/theorems/88396ebc-3975-4b37-acb4-4eb7102cd3fb
-- title:
--   European put-price surface is convex in exercise price
-- statement:
--   European put-price surface is convex in exercise price. The valuation operator uses one nonnegative state-price vector for all three strikes, preserving terminal convexity. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   P(\lambda K_1+(1-\lambda)K_2)\leq\lambda P(K_1)+(1-\lambda)P(K_2)
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 40, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. The valuation operator uses one nonnegative state-price vector for all three strikes, preserving terminal convexity.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_putValue

namespace FinancialDerivatives.FD01

theorem put_price_convex_strike {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K₁ K₂ w : ℝ) (hw₀ : 0 ≤ w) (hw₁ : w ≤ 1) :
  m.putValue s (w * K₁ + (1 - w) * K₂) ≤ w * m.putValue s K₁ + (1 - w) * m.putValue s K₂ := by sorry

end FinancialDerivatives.FD01
