-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_snell_allowed_step
-- name    : FinancialDerivatives.FD03.snell_allowed_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:57:57.941522+00:00
-- url     : https://prove2.me/theorems/885f81ce-b495-46ca-9253-587807c8dd43
-- title:
--   Snell maximum at an allowed exercise date
-- statement:
--   At a node where immediate exercise is permitted, value is the maximum of immediate exercise reward and the discounted up/down continuation value.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.5, printed p. 191, equation (10.17), Figure 10.7. American immediate exercise comparison.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_snellValue

namespace FinancialDerivatives.FD03

theorem snell_allowed_step (m : BinomialMarket) (n : ℕ)
    (reward : ℝ) (u d : ExerciseTree n) :
    snellValue m (n + 1) (.node true reward u d) =
      max reward (oneStepValue m (snellValue m n u) (snellValue m n d)) := by sorry

end FinancialDerivatives.FD03
