-- Prove2me | Theorems.Thm_DeletionCode_RedundancyBounds_paper_redundancy_bound
-- name    : DeletionCode.RedundancyBounds.paper_redundancy_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:50:26.138962+00:00
-- url     : https://prove2.me/theorems/e93abbd6-71b8-4c5e-b349-41e49f2c9b9d
-- title:
--   Redundancy Bounds: paper redundancy bound
-- statement:
--   Explicit redundancy bound for the actual parameter choice. Its only code
--   hypothesis is the established finite cardinality inequality.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RedundancyBounds.lean#L77-L92
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RedundancyBounds.lean#L77-L92

import Definitions.Def_DeletionCode_PaperParameters
import Definitions.Def_DeletionCode_WitnessCost
import Definitions.Def_DeletionCode_RedundancyBounds
set_option autoImplicit true
open DeletionCode DeletionCode.RedundancyBounds
open HeaderRecovery

theorem DeletionCode.RedundancyBounds.paper_redundancy_bound (t n : ℕ) (C : Finset (Bits n)) (hn : 4 ≤ n)
    (hcard : 2 ^ n ≤ 8 * labelCount t n * C.card) :
    redundancy n C ≤
      ((2 * t - 1 : ℕ) : ℝ) * Real.logb 2 (n : ℝ) +
        ((6 * WitnessCost.exponent t + 6 : ℕ) : ℝ) *
          Real.logb 2 (Real.logb 2 (n : ℝ)) := by sorry
