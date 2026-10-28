-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_put_price_intrinsic_lower
-- name    : FinancialDerivatives.FD01.put_price_intrinsic_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:16:31.164114+00:00
-- url     : https://prove2.me/theorems/58e26ff8-e5e4-4d17-bfa5-d989f29285fb
-- title:
--   European put price dominates its discounted intrinsic lower bound
-- statement:
--   European put price dominates its discounted intrinsic lower bound. Parity and nonnegative call prices imply a model-independent lower bound on today's put premium. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   P(K)\geq\max(0,DK-S_0)
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 41, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. Parity and nonnegative call prices imply a model-independent lower bound on today's put premium.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_spotValue
import Definitions.Def_fd01_putValue

namespace FinancialDerivatives.FD01

theorem put_price_intrinsic_lower {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (hs : ∀ ω, 0 ≤ s ω) (K : ℝ) (hK : 0 ≤ K) :
  max (m.discount * K - m.spotValue s) 0 ≤ m.putValue s K := by sorry

end FinancialDerivatives.FD01
