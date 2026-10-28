-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_004_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_004_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:03:28.239922+00:00
-- url     : https://prove2.me/theorems/9b2235cc-a88f-4b0f-b0ac-640ff8afdd7e
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 7
-- statement:
--   For prepared pair 26, right list, part 7, the selected-floor certificate succeeds for at most `1` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 335 through 335; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_004Part07.lean, lines 7-11, SHA-256 86d3bfe221bf17aea39e7321a19982c63c8b39e0a705c8f35638abbf736cfe40. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_004_part07_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 1
      (rightCached004.drop 84) (rightRows004.drop 84) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
