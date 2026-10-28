-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_001_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.right_prefix_001_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:41:15.976504+00:00
-- url     : https://prove2.me/theorems/7183642e-bca2-48d3-a916-ddc14d8cb19a
-- title:
--   Selected-floor prefix certificate for prepared pair 39, right list
-- statement:
--   For prepared pair 39, right list, the selected-floor certificate succeeds for at most `138` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`.
-- source:
--   D1Bound5/SmallPairLightRight39Prefix001.lean, lines 13-48, SHA-256 16b2c88453efda4b98aed2ca8b64055e28e3987fb51014244b514a72c6905bc0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared39.right_prefix_001_direct_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 138
      (PairLightPrepared39.rightCached.drop 98) (PairLightPrepared39.rightRows.drop 98) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared39
end
