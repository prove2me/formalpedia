-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared18_left_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared18.left_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:00.247995+00:00
-- url     : https://prove2.me/theorems/f6cd3f71-fb37-48df-8132-b51f31539761
-- title:
--   Selected-floor prefix certificate for prepared pair 18, left list, part 1
-- statement:
--   For prepared pair 18, left list, part 1, the selected-floor certificate succeeds for at most `42` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared18.sieve`. Original heads 35 through 76; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft18_000Part01.lean, lines 7-11, SHA-256 341ab8a0fbdc1be7f3dda3e88dc898e9887eabe4bed73258a16e8149586a2830. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData18_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared18.left_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 42
      (leftCached000.drop 35) (leftRows000.drop 35) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared18
end
