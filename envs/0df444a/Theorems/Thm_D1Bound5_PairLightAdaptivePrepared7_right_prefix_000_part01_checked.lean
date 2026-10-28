-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_right_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.right_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:25:12.983271+00:00
-- url     : https://prove2.me/theorems/2d34b557-9c9a-4f6c-960e-544975b1fd83
-- title:
--   Selected-floor prefix certificate for prepared pair 7, right list, part 1
-- statement:
--   For prepared pair 7, right list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 12 through 23, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveRight7_000Part01.lean, lines 11-16, SHA-256 0deaa401b9f8a056d474fc3afd2b6cc9d4b4ab3e16cdfb4673438bf4d640ce34. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.right_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 12
      (PairLightPrepared7.rightCached.drop 12)
      (PairLightPrepared7.rightRows.drop 12) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
