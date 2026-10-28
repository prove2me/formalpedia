-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_left_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared35.left_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:57.533908+00:00
-- url     : https://prove2.me/theorems/13202c93-76c9-489b-9cf4-57c08941f6c7
-- title:
--   Selected-floor prefix certificate for prepared pair 35, left list, part 3
-- statement:
--   For prepared pair 35, left list, part 3, the selected-floor certificate succeeds for at most `38` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared35.sieve`. Original heads 92 through 129; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft35_000Part03.lean, lines 7-11, SHA-256 6379a7722245094340da3e61627976f361ab6373bb6ba2c260da7c4c2970519e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared35.left_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 38
      (leftCached000.drop 92) (leftRows000.drop 92) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared35
end
