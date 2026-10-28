-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_riskNeutralWeight_isProbability
-- name    : FinancialDerivatives.FD01.riskNeutralWeight_isProbability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:30:56.506657+00:00
-- url     : https://prove2.me/theorems/471866eb-3bbe-4d8a-a98c-7e49b76d38d4
-- title:
--   Normalised state-price weights form a probability vector
-- statement:
--   Normalised state-price weights form a probability vector. Normalisation follows from a strictly positive discount factor and summability; probability axioms are conclusions, not assumptions. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   q_\omega=\pi_\omega/D\geq0,\quad\sum_\omega q_\omega=1
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 41, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. Normalisation follows from a strictly positive discount factor and summability; probability axioms are conclusions, not assumptions.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_riskNeutralWeight

namespace FinancialDerivatives.FD01

theorem riskNeutralWeight_isProbability {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) :
  (∀ ω, 0 ≤ m.riskNeutralWeight ω) ∧ (∑ ω, m.riskNeutralWeight ω) = 1 := by sorry

end FinancialDerivatives.FD01
