-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared11_left_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared11.left_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:16:14.423255+00:00
-- url     : https://prove2.me/theorems/1ab17b1e-67f5-4306-a1f8-cfc09d3b8432
-- title:
--   Selected-floor prefix certificate for prepared pair 11, left list, part 4
-- statement:
--   For prepared pair 11, left list, part 4, the selected-floor certificate succeeds for at most `26` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared11.sieve`. Original heads 82 through 107, each compared with its entire remaining tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft11_000Part04.lean, lines 7-11, SHA-256 fc5ae1df8b4aa1928e7c0c19aca0aec3aaef20eeb9e22777c64eb159dfdcd7ba. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared11.left_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 26
      (leftCached000.drop 82) (leftRows000.drop 82) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared11
end
