-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_price_linear
-- name    : FinancialDerivatives.FD01.price_linear
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:29:46.630056+00:00
-- url     : https://prove2.me/theorems/7854697c-cdf4-4a60-97e6-1bd38105e7d8
-- title:
--   Linear pricing of a two-claim portfolio
-- statement:
--   Linear pricing of a two-claim portfolio. Both claims are evaluated with the same finite nonnegative state-price vector; the scalar coefficients can be any real numbers. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   \mathcal V(af+bg)=a\mathcal V(f)+b\mathcal V(g)
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 41, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. Both claims are evaluated with the same finite nonnegative state-price vector; the scalar coefficients can be any real numbers.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price

namespace FinancialDerivatives.FD01

theorem price_linear {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (f g : Ω → ℝ) (a b : ℝ) :
  m.price (fun ω => a * f ω + b * g ω) = a * m.price f + b * m.price g := by sorry

end FinancialDerivatives.FD01
