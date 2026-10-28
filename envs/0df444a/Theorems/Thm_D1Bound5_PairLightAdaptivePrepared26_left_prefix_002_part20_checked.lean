-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_002_part20_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part20_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:56.922168+00:00
-- url     : https://prove2.me/theorems/8882cac7-78d9-4576-bc19-f53e54aa9106
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 20
-- statement:
--   For prepared pair 26, left list, part 20, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 173 through 175; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_002Part20.lean, lines 7-11, SHA-256 61f8e3f66cfb48dfcafacc152f7b02fe61afd889fe78dfbaa25d1513c264d3f6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part20_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached002.drop 60) (leftRows002.drop 60) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
