-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_right_prefix_004_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.right_prefix_004_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:51.057047+00:00
-- url     : https://prove2.me/theorems/d3ccb2fb-5c70-47e2-965b-bc41b8266601
-- title:
--   Selected-floor prefix certificate for prepared pair 6, right list, part 2
-- statement:
--   For prepared pair 6, right list, part 2, the selected-floor certificate succeeds for at most `23` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 363 through 385, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight6_004Part02.lean, lines 11-16, SHA-256 5544bcd9246a28cab9c991a52387097dd3ccc5d49e636a101b78677acaaff8f7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.right_prefix_004_part02_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 23
      (PairLightPrepared6.rightCached.drop 363)
      (PairLightPrepared6.rightRows.drop 363) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
