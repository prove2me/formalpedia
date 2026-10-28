-- Prove2me | Theorems.Thm_FinancialDerivatives_FD01_put_call_price_parity
-- name    : FinancialDerivatives.FD01.put_call_price_parity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T15:16:10.548989+00:00
-- url     : https://prove2.me/theorems/1e8aa059-63e1-4230-b4ba-62645a18785a
-- title:
--   Finite-state put-call parity for a common expiry
-- statement:
--   Finite-state put-call parity for a common expiry. All contracts have one expiry; the same state prices value the asset, the cash strike and both options. The statement retains all specified state, sign, strike and common-expiry assumptions; the indicated inequality or identity is required for every input satisfying those hypotheses.
--
--   $$
--   C(K)-P(K)=S_0-DK
--   $$
--
--   This is an open formal proof target in the present finite-state development.
-- source:
--   Original derived result inspired by Wilmott, Howison and Dewynne (1995), printed page 41, https://doi.org/10.1017/CBO9780511812545. Parent context: European option payoffs, same-expiry static portfolios and put-call parity (Equation 3.2 on page 41). The stated mathematical definition or theorem is an original derived formalisation, not a verbatim numbered theorem of the textbook. All contracts have one expiry; the same state prices value the asset, the cash strike and both options.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_spotValue
import Definitions.Def_fd01_callValue
import Definitions.Def_fd01_putValue

namespace FinancialDerivatives.FD01

theorem put_call_price_parity {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (s : Ω → ℝ) (K : ℝ) :
  m.callValue s K - m.putValue s K = m.spotValue s - m.discount * K := by sorry

end FinancialDerivatives.FD01
