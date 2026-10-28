-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared1_right_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared1.right_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:04:50.164256+00:00
-- url     : https://prove2.me/theorems/602a5627-a8ad-422c-bfa9-1964b459ddc2
-- title:
--   Selected-floor prefix certificate for prepared pair 1, right list, part 1
-- statement:
--   For prepared pair 1, right list, part 1, the selected-floor certificate succeeds for at most `20` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared1.sieve`. Original heads 16 through 35, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight1_000Part01.lean, lines 7-11, SHA-256 8756425acc01df50ad5520fdf38b3024254eb87822cf7198c26bc5a755463fc3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared1.right_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 20
      (rightCached000.drop 16) (rightRows000.drop 16) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared1
end
