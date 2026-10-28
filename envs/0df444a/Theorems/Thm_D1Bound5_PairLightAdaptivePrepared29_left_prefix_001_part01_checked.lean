-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared29_left_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared29.left_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:58.609225+00:00
-- url     : https://prove2.me/theorems/70cf3e6c-a488-465e-9438-7d00c34ae0a1
-- title:
--   Selected-floor prefix certificate for prepared pair 29, left list, part 1
-- statement:
--   For prepared pair 29, left list, part 1, the selected-floor certificate succeeds for at most `46` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared29.sieve`. Original heads 164 through 209, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft29_001Part01.lean, lines 7-11, SHA-256 22a82d94ac6382c8227edcb8a401f1999a850ea504ce9f60d6552040a5db5380. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared29.left_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 46
      (leftCached001.drop 38) (leftRows001.drop 38) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared29
end
