-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_right_prefix_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.right_prefix_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:23.42722+00:00
-- url     : https://prove2.me/theorems/ced10bef-9d08-4c11-952c-80c3a8d94f20
-- title:
--   Selected-floor prefix certificate for prepared pair 39, right list, part 3
-- statement:
--   For prepared pair 39, right list, part 3, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 170 through 193, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight39_001Part03.lean, lines 11-16, SHA-256 ed33ba0eafa2cf077e5df39bec27403abf4413d497ac223b35c3bfe8103068ad. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.right_prefix_001_part03_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 24
      (PairLightPrepared39.rightCached.drop 170)
      (PairLightPrepared39.rightRows.drop 170) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
