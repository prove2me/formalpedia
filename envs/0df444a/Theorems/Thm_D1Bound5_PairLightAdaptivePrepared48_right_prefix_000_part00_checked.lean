-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_right_prefix_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared48.right_prefix_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:02.218926+00:00
-- url     : https://prove2.me/theorems/a50a1664-53da-49d4-b4db-499e55c9b9b5
-- title:
--   Selected-floor prefix certificate for prepared pair 48, right list, part 0
-- statement:
--   For prepared pair 48, right list, part 0, the selected-floor certificate succeeds for at most `29` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 8, and the sieve is `PairLightPrepared48.sieve`. Original heads 0 through 28; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight48_000Part00.lean, lines 7-11, SHA-256 4e10e472df5a1ce3accd98aeecc601924d2bb7aaea0d3c0f226c49c9fe90b590. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared48.right_prefix_000_part00_checked :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 29
      (rightCached000.drop 0) (rightRows000.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared48
end
