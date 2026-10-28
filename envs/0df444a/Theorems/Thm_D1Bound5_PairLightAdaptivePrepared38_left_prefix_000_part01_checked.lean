-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared38_left_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared38.left_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:00:29.20497+00:00
-- url     : https://prove2.me/theorems/712b8946-ed7a-4692-9015-ead40653cc68
-- title:
--   Selected-floor prefix certificate for prepared pair 38, left list, part 1
-- statement:
--   For prepared pair 38, left list, part 1, the selected-floor certificate succeeds for at most `45` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared38.sieve`. Original heads 37 through 81; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft38_000Part01.lean, lines 7-11, SHA-256 ff81783486d4b46c34f762109ad683455247199b074e20a105ac90ac5eaa73ad. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData38_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared38.left_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 45
      (leftCached000.drop 37) (leftRows000.drop 37) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared38
end
