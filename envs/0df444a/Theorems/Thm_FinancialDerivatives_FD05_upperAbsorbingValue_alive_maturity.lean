-- Prove2me | Theorems.Thm_FinancialDerivatives_FD05_upperAbsorbingValue_alive_maturity
-- name    : FinancialDerivatives.FD05.upperAbsorbingValue_alive_maturity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T19:41:32.273391+00:00
-- url     : https://prove2.me/theorems/fd5082a9-6919-495b-9367-0a704134adab
-- title:
--   Alive contract settles its terminal reward
-- statement:
--   At alive maturity, an untriggered upper-barrier contract pays precisely the specified terminal reward.
-- source:
--   Wilmott, Howison and Dewynne (1995), The Mathematics of Financial Derivatives, Chapter 12, pp. 206–212. Rigorous finite-binomial first-hit analogue.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd05_upperAbsorbingValue
import Definitions.Def_fd05_upperTouch

namespace FinancialDerivatives.FD05
open FinancialDerivatives.FD03

theorem upperAbsorbingValue_alive_maturity (m : BinomialMarket)
    (B : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ)
    (t : ℕ) (S : ℝ) (h : upperTouch B S monitor t = false) :
    upperAbsorbingValue m B monitor g 0 t S false = g S := by sorry

end FinancialDerivatives.FD05
