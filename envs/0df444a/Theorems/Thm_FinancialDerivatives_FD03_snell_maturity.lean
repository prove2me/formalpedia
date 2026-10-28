-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_snell_maturity
-- name    : FinancialDerivatives.FD03.snell_maturity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:57:29.592357+00:00
-- url     : https://prove2.me/theorems/819d2935-2a9a-4dda-9520-eab92487f87f
-- title:
--   The Snell value at maturity is the exercise payment
-- statement:
--   With no trading periods left, the American/Bermudan value equals the contracted maturity reward.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.5, printed p. 191, equation (10.17). Maturity condition.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_snellValue

namespace FinancialDerivatives.FD03

theorem snell_maturity (m : BinomialMarket) (c : ℝ) :
    snellValue m 0 (.maturity c) = c := by sorry

end FinancialDerivatives.FD03
