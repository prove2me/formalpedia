-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared5_left_prefix_001_direct_checked
-- name    : D1Bound5.PairLightAdaptivePrepared5.left_prefix_001_direct_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:45:57.215137+00:00
-- url     : https://prove2.me/theorems/59f278b4-2a0a-44a8-8dc1-d20e1adc03cc
-- title:
--   Selected-floor prefix certificate for prepared pair 5, left list
-- statement:
--   For prepared pair 5, left list, the selected-floor certificate succeeds for at most `164` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared5.sieve`.
-- source:
--   D1Bound5/SmallPairLightLeft5Prefix001.lean, lines 14-55, SHA-256 b31a97157dc46696e325aff0ac6341c55221df6e38640860f9b8828cae6e39ca. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.PairLightAdaptivePrepared5.left_prefix_001_direct_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 164
      (PairLightPrepared5.leftCached.drop 105) (PairLightPrepared5.leftRows.drop 105) = true := by sorry
end D1Bound5.PairLightAdaptivePrepared5
end
