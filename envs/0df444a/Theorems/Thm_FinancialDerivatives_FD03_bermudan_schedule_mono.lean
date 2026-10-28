-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_bermudan_schedule_mono
-- name    : FinancialDerivatives.FD03.bermudan_schedule_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:04:12.092973+00:00
-- url     : https://prove2.me/theorems/905e670d-5de4-4335-beda-f081f588d33d
-- title:
--   More permitted exercise dates cannot lower Bermudan value
-- statement:
--   For two stock-based exercise schedules A and B with every exercise date of A also allowed by B, the time-zero optimal stopping price under schedule B is at least the price under schedule A, for any signed reward and finite maturity.
-- source:
--   Original finite optimal stopping monotonicity result inspired by Wilmott, Howison and Dewynne (1995), Chapter 10 §10.5, equation (10.17), printed p. 191.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_snellValue
import Definitions.Def_fd03_exerciseStockTree

namespace FinancialDerivatives.FD03

theorem bermudan_schedule_mono (m : BinomialMarket)
    (n : ℕ) (spot : ℝ) (reward : ℝ → ℝ)
    (A B : ℕ → Bool) (hAB : ∀ k, A k = true → B k = true) :
    snellValue m n (exerciseStockTree m reward A n spot) ≤
      snellValue m n (exerciseStockTree m reward B n spot) := by sorry

end FinancialDerivatives.FD03
