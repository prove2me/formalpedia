-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_right_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared35.right_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:42.709398+00:00
-- url     : https://prove2.me/theorems/b28861fc-54d5-45b8-bf21-2c0d67feb5e6
-- title:
--   Selected-floor prefix certificate for prepared pair 35, right list, part 1
-- statement:
--   For prepared pair 35, right list, part 1, the selected-floor certificate succeeds for at most `30` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared35.sieve`. Original heads 28 through 57; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight35_000Part01.lean, lines 7-11, SHA-256 739526b82251bde9b51aa47ae919eb2dade3b9645123ef3dec966835c2d6bd97. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared35.right_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 30
      (rightCached000.drop 28) (rightRows000.drop 28) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared35
end
