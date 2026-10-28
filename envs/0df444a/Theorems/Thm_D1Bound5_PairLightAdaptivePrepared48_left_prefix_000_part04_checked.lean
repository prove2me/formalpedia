-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_left_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared48.left_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:02.65059+00:00
-- url     : https://prove2.me/theorems/c53b8efe-8bbd-4b5f-a7d5-25ff50c4cfae
-- title:
--   Selected-floor prefix certificate for prepared pair 48, left list, part 4
-- statement:
--   For prepared pair 48, left list, part 4, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 8, and the sieve is `PairLightPrepared48.sieve`. Original heads 134 through 136; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft48_000Part04.lean, lines 7-11, SHA-256 4bb39bbe8ce3daa1eeebe32e5c280610c3f655e6df6af6377cb232d8898e3e1a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared48.left_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 3
      (leftCached000.drop 134) (leftRows000.drop 134) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared48
end
