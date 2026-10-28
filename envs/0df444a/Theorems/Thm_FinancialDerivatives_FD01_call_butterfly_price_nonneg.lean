-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_call_butterfly_price_nonneg
-- name    : FinancialDerivatives.FD01.call_butterfly_price_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:18:20.900782+00:00
-- url     : https://prove2.me/theorems/f2d00d19-da9e-46f9-a4cb-dceeecc1026f
-- title:
--   Equal-spacing call butterfly cannot have a negative price
-- statement:
--   Equal-spacing call butterfly cannot have a negative price. The butterfly is long one option at each wing and short two at the midpoint, all with one expiry. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   0\leq C(K_1)-2C(K_2)+C(K_3)
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 40, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. The butterfly is long one option at each wing and short two at the midpoint, all with one expiry.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_callValue

namespace FinancialDerivatives.FD01

theorem call_butterfly_price_nonneg {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K₁ K₂ K₃ : ℝ) (hK₁ : K₁ ≤ K₂) (hK₂ : K₂ ≤ K₃) (hmid : 2 * K₂ = K₁ + K₃) :
  0 ≤ m.callValue s K₁ - 2 * m.callValue s K₂ + m.callValue s K₃ := by sorry

end FinancialDerivatives.FD01
