-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared35_left_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared35.left_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:09:57.432511+00:00
-- url     : https://prove2.me/theorems/2050ac69-a4c0-405f-9194-9ec961172f25
-- title:
--   Selected-floor prefix certificate for prepared pair 35, left list, part 4
-- statement:
--   For prepared pair 35, left list, part 4, the selected-floor certificate succeeds for at most `2` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared35.sieve`. Original heads 130 through 131; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft35_000Part04.lean, lines 7-11, SHA-256 2a5dd73f6bbefe31fc1fc53a510e7e312a13c6e72d05fc6b36320e46b0d219b3. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared35.left_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 2
      (leftCached000.drop 130) (leftRows000.drop 130) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared35
end
