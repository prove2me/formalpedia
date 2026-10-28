-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_left_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared40.left_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:59.79035+00:00
-- url     : https://prove2.me/theorems/5f6d9335-5ee6-4b58-a68c-2f79299525a5
-- title:
--   Selected-floor prefix certificate for prepared pair 40, left list, part 3
-- statement:
--   For prepared pair 40, left list, part 3, the selected-floor certificate succeeds for at most `40` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared40.sieve`. Original heads 94 through 133; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft40_000Part03.lean, lines 7-11, SHA-256 ca4395797fc40c53152bd12946c9e2c448df69e0a9a280733a456db598226357. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared40.left_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 40
      (leftCached000.drop 94) (leftRows000.drop 94) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared40
end
