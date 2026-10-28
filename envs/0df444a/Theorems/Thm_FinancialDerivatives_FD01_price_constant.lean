-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_price_constant
-- name    : FinancialDerivatives.FD01.price_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:29:59.875323+00:00
-- url     : https://prove2.me/theorems/bc00db21-cd33-45f8-85b2-6e9e4bd01d2e
-- title:
--   Price of a state-independent payment
-- statement:
--   Price of a state-independent payment. The discount factor equals the sum of every terminal state price, so a fixed payment is priced consistently across all states. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   \mathcal V(a\mathbf 1)=Da
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 41, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. The discount factor equals the sum of every terminal state price, so a fixed payment is priced consistently across all states.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price

namespace FinancialDerivatives.FD01

theorem price_constant {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (a : ℝ) :
  m.price (fun _ => a) = m.discount * a := by sorry

end FinancialDerivatives.FD01
