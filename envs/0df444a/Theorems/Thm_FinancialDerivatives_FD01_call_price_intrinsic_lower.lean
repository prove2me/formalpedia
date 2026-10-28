-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_call_price_intrinsic_lower
-- name    : FinancialDerivatives.FD01.call_price_intrinsic_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:16:20.25818+00:00
-- url     : https://prove2.me/theorems/5b7597be-a52d-4c2e-81e6-b8c540710504
-- title:
--   European call price dominates its discounted intrinsic lower bound
-- statement:
--   European call price dominates its discounted intrinsic lower bound. Parity and nonnegative put prices imply a model-independent lower bound on today's call premium. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   C(K)\geq\max(0,S_0-DK)
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 41, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. Parity and nonnegative put prices imply a model-independent lower bound on today's call premium.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_spotValue
import Definitions.Def_fd01_callValue

namespace FinancialDerivatives.FD01

theorem call_price_intrinsic_lower {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (hs : ∀ ω, 0 ≤ s ω) (K : ℝ) (hK : 0 ≤ K) :
  max (m.spotValue s - m.discount * K) 0 ≤ m.callValue s K := by sorry

end FinancialDerivatives.FD01
