-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_right_prefix_000_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared35.right_prefix_000_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:41.139159+00:00
-- url     : https://prove2.me/theorems/8ccb3e80-e426-4f63-8d3d-94ff341b573b
-- title:
--   Selected-floor prefix certificate for prepared pair 35, right list, part 2
-- statement:
--   For prepared pair 35, right list, part 2, the selected-floor certificate succeeds for at most `34` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared35.sieve`. Original heads 58 through 91; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight35_000Part02.lean, lines 7-11, SHA-256 523bb5c43aa99adaa1a966246b741e67f784fc4562c02470dc6906c57501b7b4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared35.right_prefix_000_part02_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 34
      (rightCached000.drop 58) (rightRows000.drop 58) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared35
end
