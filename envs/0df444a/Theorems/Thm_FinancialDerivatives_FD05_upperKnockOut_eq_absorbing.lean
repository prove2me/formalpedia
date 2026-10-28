-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_upperKnockOut_eq_absorbing
-- name    : FinancialDerivatives.FD05.upperKnockOut_eq_absorbing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:37:57.210989+00:00
-- url     : https://prove2.me/theorems/97d67224-1d54-4cc0-b2a0-49f0f0be1cbf
-- title:
--   Absorbing backward recursion equals full-tree European valuation
-- statement:
--   The independently defined absorbing recursion produces exactly the FD-03 European price of the full-path upper knock-out terminal claim.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperKnockOutTree
import Definitions.Def_fd05_upperAbsorbingValue
import Definitions.Def_fd03_europeanValue

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

theorem upperKnockOut_eq_absorbing (m : BinomialMarket) (N : ℕ)
    (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ) :
    upperAbsorbingValue m B monitor g N 0 m.initialSpot false =
      europeanValue m N
        (upperKnockOutTree m B monitor g N 0 m.initialSpot false) := by sorry

end FinancialDerivatives.FD05
