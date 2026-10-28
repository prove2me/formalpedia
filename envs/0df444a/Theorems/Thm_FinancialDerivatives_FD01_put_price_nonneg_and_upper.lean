-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_put_price_nonneg_and_upper
-- name    : FinancialDerivatives.FD01.put_price_nonneg_and_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:15:47.864601+00:00
-- url     : https://prove2.me/theorems/e44e4199-142e-4481-9af8-f6a8a5f6852e
-- title:
--   Nonnegative European put price bounded by discounted strike
-- statement:
--   Nonnegative European put price bounded by discounted strike. The asset and strike are nonnegative and the terminal strike amount is discounted using this market's state prices. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   0\leq P(K)\leq DK
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 41, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. The asset and strike are nonnegative and the terminal strike amount is discounted using this market's state prices.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_putValue

namespace FinancialDerivatives.FD01

theorem put_price_nonneg_and_upper {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (hs : ∀ ω, 0 ≤ s ω) (K : ℝ) (hK : 0 ≤ K) :
  0 ≤ m.putValue s K ∧ m.putValue s K ≤ m.discount * K := by sorry

end FinancialDerivatives.FD01
