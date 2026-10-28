-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_right_prefix_004_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.right_prefix_004_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:08.321992+00:00
-- url     : https://prove2.me/theorems/f1a6d195-b922-4002-86bd-3912bccb9453
-- title:
--   Selected-floor prefix certificate for prepared pair 26, right list, part 4
-- statement:
--   For prepared pair 26, right list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 299 through 310; every full later-vertex tail retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight26_004Part04.lean, lines 7-11, SHA-256 eb2e876d856e099e2cd0b2155ce19614bf8ac9646210cdc7ff40eb4ecc14aacd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.right_prefix_004_part04_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (rightCached004.drop 48) (rightRows004.drop 48) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
