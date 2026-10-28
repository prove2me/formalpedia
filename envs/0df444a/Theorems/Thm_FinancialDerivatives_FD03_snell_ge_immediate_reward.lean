-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_snell_ge_immediate_reward
-- name    : FinancialDerivatives.FD03.snell_ge_immediate_reward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:58:17.011507+00:00
-- url     : https://prove2.me/theorems/0418cfdf-1adc-46d2-bdc3-2dd9bd2bb5c8
-- title:
--   Permitted immediate exercise is bounded by Snell value
-- statement:
--   Where exercise is permitted, the Snell value is at least the contractual immediate reward, including equality at an indifference node.
-- source:
--   Wilmott, Howison and Dewynne (1995), Chapter 10 §10.5, printed p. 191, equation (10.17). Derived inequality for holder's permissible early exercise.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_snellValue

namespace FinancialDerivatives.FD03

theorem snell_ge_immediate_reward (m : BinomialMarket) (n : ℕ)
    (reward : ℝ) (u d : ExerciseTree n) :
    reward ≤ snellValue m (n + 1) (.node true reward u d) := by sorry

end FinancialDerivatives.FD03
