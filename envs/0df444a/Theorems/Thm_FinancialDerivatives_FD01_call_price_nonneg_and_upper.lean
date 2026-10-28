-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_call_price_nonneg_and_upper
-- name    : FinancialDerivatives.FD01.call_price_nonneg_and_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:15:35.547542+00:00
-- url     : https://prove2.me/theorems/b84d114d-3dbd-47aa-97a3-68f30ca26cd1
-- title:
--   Nonnegative European call price bounded by spot
-- statement:
--   Nonnegative European call price bounded by spot. The asset and exercise price are nonnegative, and the option is valued with the same state prices as the asset. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   0\leq C(K)\leq S_0
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 41, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. The asset and exercise price are nonnegative, and the option is valued with the same state prices as the asset.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_spotValue
import Definitions.Def_fd01_callValue

namespace FinancialDerivatives.FD01

theorem call_price_nonneg_and_upper {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (hs : ∀ ω, 0 ≤ s ω) (K : ℝ) (hK : 0 ≤ K) :
  0 ≤ m.callValue s K ∧ m.callValue s K ≤ m.spotValue s := by sorry

end FinancialDerivatives.FD01
