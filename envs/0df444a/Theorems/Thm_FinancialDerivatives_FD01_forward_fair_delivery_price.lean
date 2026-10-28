-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_forward_fair_delivery_price
-- name    : FinancialDerivatives.FD01.forward_fair_delivery_price
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:18:33.144861+00:00
-- url     : https://prove2.me/theorems/8b4f4385-04c9-4c2a-9718-c8c6c206b021
-- title:
--   Forward value and unique fair delivery price
-- statement:
--   Forward value and unique fair delivery price. The forward value is a present amount, while the fair delivery price is the strike making that amount zero; positive discounting makes it unique. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   \mathcal V(s-K)=S_0-DK,\quad\mathcal V(s-K)=0\iff K=S_0/D
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 41, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. The forward value is a present amount, while the fair delivery price is the strike making that amount zero; positive discounting makes it unique.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price
import Definitions.Def_fd01_spotValue
import Definitions.Def_fd01_forwardPayoff

namespace FinancialDerivatives.FD01

theorem forward_fair_delivery_price {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K : ℝ) :
  m.price (fun ω => forwardPayoff (s ω) K) = m.spotValue s - m.discount * K ∧ (m.price (fun ω => forwardPayoff (s ω) K) = 0 ↔ K = m.spotValue s / m.discount) := by sorry

end FinancialDerivatives.FD01
