-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_left_prefix_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared48.left_prefix_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:02:38.461995+00:00
-- url     : https://prove2.me/theorems/619ed28f-f387-4bfb-9d4e-e8de412587ea
-- title:
--   Selected-floor prefix certificate for prepared pair 48, left list, part 1
-- statement:
--   For prepared pair 48, left list, part 1, the selected-floor certificate succeeds for at most `73` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 8, and the sieve is `PairLightPrepared48.sieve`. Original heads 187 through 259; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft48_001Part01.lean, lines 7-11, SHA-256 0b36bce479fbd7c1b91d08f884d919938b7f11cd1bfda7537b62d0edc601f7b9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared48.left_prefix_001_part01_checked :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 73
      (leftCached001.drop 50) (leftRows001.drop 50) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared48
end
