-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared12_left_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared12.left_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:08.880569+00:00
-- url     : https://prove2.me/theorems/d040d6ec-8a1a-4f31-bc5b-96d94cbf09fb
-- title:
--   Selected-floor prefix certificate for prepared pair 12, left list, part 3
-- statement:
--   For prepared pair 12, left list, part 3, the selected-floor certificate succeeds for at most `41` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared12.sieve`. Original heads 95 through 135; every head retains its complete original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft12_000Part03.lean, lines 7-11, SHA-256 774efc7fab224054c12194fbd0287bc726150cf1c64ce671bd14392b67b7db61. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared12.left_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 41
      (leftCached000.drop 95) (leftRows000.drop 95) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared12
end
