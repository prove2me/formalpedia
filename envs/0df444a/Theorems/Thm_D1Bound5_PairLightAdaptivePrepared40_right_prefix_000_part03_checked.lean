-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_right_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared40.right_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:03.80999+00:00
-- url     : https://prove2.me/theorems/3d8e8389-cae7-421c-87b8-ec0a174aaf2d
-- title:
--   Selected-floor prefix certificate for prepared pair 40, right list, part 3
-- statement:
--   For prepared pair 40, right list, part 3, the selected-floor certificate succeeds for at most `41` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared40.sieve`. Original heads 96 through 136; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight40_000Part03.lean, lines 7-11, SHA-256 3d69568fb1119f92ea51432db6748a8838a57d62d99ebf93a2e592bf72ee568e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared40.right_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 41
      (rightCached000.drop 96) (rightRows000.drop 96) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared40
end
