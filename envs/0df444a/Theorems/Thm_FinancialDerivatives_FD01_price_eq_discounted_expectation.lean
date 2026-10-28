-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_price_eq_discounted_expectation
-- name    : FinancialDerivatives.FD01.price_eq_discounted_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:31:11.345636+00:00
-- url     : https://prove2.me/theorems/59f56ec7-a313-4576-8d84-97125e52f834
-- title:
--   State-price valuation equals discounted finite expectation
-- statement:
--   State-price valuation equals discounted finite expectation. The weights are those obtained from the same state prices; the formula holds for every real-valued terminal claim. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   \mathcal V(f)=D\sum_\omega q_\omega f_\omega
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 41, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. The weights are those obtained from the same state prices; the formula holds for every real-valued terminal claim.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price
import Definitions.Def_fd01_riskNeutralWeight

namespace FinancialDerivatives.FD01

theorem price_eq_discounted_expectation {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (f : Ω → ℝ) :
  m.price f = m.discount * (∑ ω, m.riskNeutralWeight ω * f ω) := by sorry

end FinancialDerivatives.FD01
