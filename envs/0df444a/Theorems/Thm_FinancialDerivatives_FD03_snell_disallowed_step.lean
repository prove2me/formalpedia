-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_snell_disallowed_step
-- name    : FinancialDerivatives.FD03.snell_disallowed_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:57:42.392576+00:00
-- url     : https://prove2.me/theorems/5087b126-cd26-4b57-841a-1d28f6a815df
-- title:
--   Snell continuation at a forbidden exercise date
-- statement:
--   At a non-maturity node where exercise is forbidden, the contract value equals its one-step discounted continuation price.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.5, printed pp. 189–191, equation (10.17). Bermudan disallowed-date case.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_snellValue

namespace FinancialDerivatives.FD03

theorem snell_disallowed_step (m : BinomialMarket) (n : ℕ)
    (reward : ℝ) (u d : ExerciseTree n) :
    snellValue m (n + 1) (.node false reward u d) =
      oneStepValue m (snellValue m n u) (snellValue m n d) := by sorry

end FinancialDerivatives.FD03
