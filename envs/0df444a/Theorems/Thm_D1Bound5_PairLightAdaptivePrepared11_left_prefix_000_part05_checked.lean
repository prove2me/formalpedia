-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_left_prefix_000_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared11.left_prefix_000_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:31.297958+00:00
-- url     : https://prove2.me/theorems/7ffb2c16-cc11-4376-81a3-28def3c379de
-- title:
--   Selected-floor prefix certificate for prepared pair 11, left list, part 5
-- statement:
--   For prepared pair 11, left list, part 5, the selected-floor certificate succeeds for at most `30` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared11.sieve`. Original heads 108 through 137, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft11_000Part05.lean, lines 7-11, SHA-256 5fb5accb9251489b2949b13d842fd7b1ae4f0fc3cbf4df04a0ae6af5ec5072db. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared11.left_prefix_000_part05_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 30
      (leftCached000.drop 108) (leftRows000.drop 108) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared11
end
