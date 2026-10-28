-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_left_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.left_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:34.769441+00:00
-- url     : https://prove2.me/theorems/466dc2d1-0ae4-4051-9f4c-9bb6358d6941
-- title:
--   Selected-floor prefix certificate for prepared pair 17, left list, part 0
-- statement:
--   For prepared pair 17, left list, part 0, the selected-floor certificate succeeds for at most `50` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared17.sieve`. Original heads 137 through 186; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft17_001Part00.lean, lines 7-11, SHA-256 f55dd66fbb38c401cdc36038a26e989e1fe838186aef6c506874b2dca6fa618b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared17.left_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 50
      (leftCached001.drop 0) (leftRows001.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared17
end
