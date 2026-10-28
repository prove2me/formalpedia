-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_right_prefix_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared35.right_prefix_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:39.208127+00:00
-- url     : https://prove2.me/theorems/c2f3227d-0ab2-4d4a-beaf-e7a413b48763
-- title:
--   Selected-floor prefix certificate for prepared pair 35, right list, part 0
-- statement:
--   For prepared pair 35, right list, part 0, the selected-floor certificate succeeds for at most `28` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared35.sieve`. Original heads 0 through 27; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight35_000Part00.lean, lines 7-11, SHA-256 771361de7b17c0f20d9c190b5ae2568d90f83256fea1ce303e6fdc40e74650b0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared35.right_prefix_000_part00_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 28
      (rightCached000.drop 0) (rightRows000.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared35
end
