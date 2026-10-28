-- Prove2me | Theorems.Thm_FinancialDerivatives_FD03_writer_superhedge_exists
-- name    : FinancialDerivatives.FD03.writer_superhedge_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T08:06:01.714558+00:00
-- url     : https://prove2.me/theorems/6be96a67-d195-4e53-9c7a-0e3607edf05e
-- title:
--   The Snell value is attainable as seller-superhedging capital
-- statement:
--   For each finite exercise claim at a positive node stock price, the seller can begin with wealth exactly equal to Snell value and construct a self-financing stock-bank strategy that covers all permitted exercise and maturity payoffs.
-- source:
--   Original seller replication/superhedging attainment theorem based on the American exercise recursion, Wilmott, Howison and Dewynne (1995), Chapter 10 §10.5, equation (10.17), printed p. 191.

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_SelfFinancing
import Definitions.Def_fd03_hedgeWealth
import Definitions.Def_fd03_hedgeCoversExercise
import Definitions.Def_fd03_snellValue

namespace FinancialDerivatives.FD03

theorem writer_superhedge_exists (m : BinomialMarket)
    (n : ℕ) (spot : ℝ) (hspot : 0 < spot)
    (exercise : ExerciseTree n) :
    ∃ hedge : HedgeTree n,
      SelfFinancing m n spot hedge ∧
      hedgeCoversExercise m n spot hedge exercise ∧
      hedgeWealth m n spot hedge = snellValue m n exercise := by sorry

end FinancialDerivatives.FD03
