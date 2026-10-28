-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_right_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared48.right_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:17.446268+00:00
-- url     : https://prove2.me/theorems/6686e6f4-8c7e-409c-bebf-852ac1f3a7f0
-- title:
--   Selected-floor prefix certificate for prepared pair 48, right list, part 1
-- statement:
--   For prepared pair 48, right list, part 1, the selected-floor certificate succeeds for at most `32` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 8, and the sieve is `PairLightPrepared48.sieve`. Original heads 29 through 60; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight48_000Part01.lean, lines 7-11, SHA-256 520235ba3e0676a79463a7504970c992ef8a26fc22f73f75cfd8517dfd0d028b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared48.right_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 32
      (rightCached000.drop 29) (rightRows000.drop 29) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared48
end
