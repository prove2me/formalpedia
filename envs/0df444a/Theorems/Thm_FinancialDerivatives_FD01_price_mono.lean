-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_price_mono
-- name    : FinancialDerivatives.FD01.price_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:30:18.837006+00:00
-- url     : https://prove2.me/theorems/499d48eb-bc45-4aad-9089-8c75d7fc2623
-- title:
--   Positive pricing preserves pointwise order
-- statement:
--   Positive pricing preserves pointwise order. A pointwise claim comparison transfers to a present-value comparison because every state-price weight is nonnegative. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   f\leq g\ \Longrightarrow\ \mathcal V(f)\leq\mathcal V(g)
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 41, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. A pointwise claim comparison transfers to a present-value comparison because every state-price weight is nonnegative.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price

namespace FinancialDerivatives.FD01

theorem price_mono {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (f g : Ω → ℝ) (h : ∀ ω, f ω ≤ g ω) :
  m.price f ≤ m.price g := by sorry

end FinancialDerivatives.FD01
