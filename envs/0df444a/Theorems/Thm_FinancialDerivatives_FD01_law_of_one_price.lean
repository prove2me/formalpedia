-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_law_of_one_price
-- name    : FinancialDerivatives.FD01.law_of_one_price
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:31:20.406046+00:00
-- url     : https://prove2.me/theorems/6417f8af-19dc-4258-8726-40602a7e506e
-- title:
--   Identical contingent claims have identical values
-- statement:
--   Identical contingent claims have identical values. The terminal payoffs agree state by state and therefore must carry identical prices under one linear valuation operator. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   f=g\ \Longrightarrow\ \mathcal V(f)=\mathcal V(g)
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 41, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. The terminal payoffs agree state by state and therefore must carry identical prices under one linear valuation operator.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price

namespace FinancialDerivatives.FD01

theorem law_of_one_price {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (f g : Ω → ℝ) (h : ∀ ω, f ω = g ω) :
  m.price f = m.price g := by sorry

end FinancialDerivatives.FD01
