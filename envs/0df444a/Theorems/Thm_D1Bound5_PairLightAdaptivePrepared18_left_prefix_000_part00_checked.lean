-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared18_left_prefix_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared18.left_prefix_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:23:54.656712+00:00
-- url     : https://prove2.me/theorems/6f39e5e0-6444-45e8-8349-c43cc11aee23
-- title:
--   Selected-floor prefix certificate for prepared pair 18, left list, part 0
-- statement:
--   For prepared pair 18, left list, part 0, the selected-floor certificate succeeds for at most `35` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared18.sieve`. Original heads 0 through 34; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft18_000Part00.lean, lines 7-11, SHA-256 3a74df4b449c4267d01a0a5e7e125feb54e21cb3c9637ee8b684736228ae9fb4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData18_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared18.left_prefix_000_part00_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 35
      (leftCached000.drop 0) (leftRows000.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared18
end
