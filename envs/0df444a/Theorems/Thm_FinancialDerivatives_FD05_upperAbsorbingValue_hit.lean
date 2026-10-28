-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_upperAbsorbingValue_hit
-- name    : FinancialDerivatives.FD05.upperAbsorbingValue_hit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:41:10.753065+00:00
-- url     : https://prove2.me/theorems/317ef0b8-36d2-45fc-a9e4-a984ec768b83
-- title:
--   An activated knock-out state has zero continuation value
-- statement:
--   Once the knock-out flag records a prior barrier touch, the independently defined recursion has zero value at every remaining maturity.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperAbsorbingValue

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

theorem upperAbsorbingValue_hit (m : BinomialMarket) (B : ℝ)
    (monitor : ℕ → Bool) (g : ℝ → ℝ)
    (n t : ℕ) (S : ℝ) :
    upperAbsorbingValue m B monitor g n t S true = 0 := by sorry

end FinancialDerivatives.FD05
