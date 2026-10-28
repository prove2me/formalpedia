-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_european_step
-- name    : FinancialDerivatives.FD03.european_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:57:11.754993+00:00
-- url     : https://prove2.me/theorems/272783f8-1a0a-4a5c-ac2c-77e4f1712cf8
-- title:
--   European binomial backward-induction step
-- statement:
--   For up/down subtrees of depth n, the value of their common parent equals the discounted risk-neutral combination of the two subtree values.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.4, printed p. 188, equation (10.16). Formal statement of the European backward step.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_europeanValue

namespace FinancialDerivatives.FD03

theorem european_step (m : BinomialMarket) (n : ℕ)
    (u d : PayoffTree n) :
    europeanValue m (n + 1) (.branch u d) =
      oneStepValue m (europeanValue m n u) (europeanValue m n d) := by sorry

end FinancialDerivatives.FD03
