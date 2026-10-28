-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_right_prefix_002_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.right_prefix_002_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:40.354978+00:00
-- url     : https://prove2.me/theorems/fde826d4-8b19-41b4-ada5-39fee48e49d1
-- title:
--   Selected-floor prefix certificate for prepared pair 24, right list, part 0
-- statement:
--   For prepared pair 24, right list, part 0, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 248 through 271, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight24_002Part00.lean, lines 11-16, SHA-256 4431cf509043ce39f386d69cc16cea6bd215fd6466946379721670a4d3f290fd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.right_prefix_002_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 24
      (PairLightPrepared24.rightCached.drop 248)
      (PairLightPrepared24.rightRows.drop 248) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
