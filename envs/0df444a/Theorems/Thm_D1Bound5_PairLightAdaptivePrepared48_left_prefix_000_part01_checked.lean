-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_left_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared48.left_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:31.82099+00:00
-- url     : https://prove2.me/theorems/35994321-f6a7-48f6-8eb8-af375575683f
-- title:
--   Selected-floor prefix certificate for prepared pair 48, left list, part 1
-- statement:
--   For prepared pair 48, left list, part 1, the selected-floor certificate succeeds for at most `31` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 8, and the sieve is `PairLightPrepared48.sieve`. Original heads 28 through 58; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft48_000Part01.lean, lines 7-11, SHA-256 374f392580ff4ff5b38b2c1eb3422ad338c732469b282129a02022d430e0c815. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared48.left_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 31
      (leftCached000.drop 28) (leftRows000.drop 28) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared48
end
