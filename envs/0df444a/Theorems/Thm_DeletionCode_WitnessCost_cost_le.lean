-- Prove2me | Theorems.Thm_DeletionCode_WitnessCost_cost_le
-- name    : DeletionCode.WitnessCost.cost_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:48:36.882074+00:00
-- url     : https://prove2.me/theorems/8b0dd8a0-47a0-4b85-b92d-938b4af59d9c
-- title:
--   Witness Cost: cost le
-- statement:
--   All non-position factors in the paper's bounded-witness count fit into
--   L^(b_t R), with b_t explicit. This also holds for R = 0 and R = 1.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCost.lean#L51-L71
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCost.lean#L51-L71

import Definitions.Def_DeletionCode_CountExponent
import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_WitnessCost
set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCost
open HeaderRecovery UniqueWordParameters

theorem DeletionCode.WitnessCost.cost_le (t L R : ℕ) (hL : 4 * t + 2 ≤ L)
    (hR : R ≤ 1 + 4 * t * L ^ 2) :
    2 ^ R * (2 * t * R + 1) * (L * R) ^ (CountExponent.exponent t * R) ≤
      L ^ (exponent t * R) := by sorry
