-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared26_left_prefix_002_part19_checked
-- name    : D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part19_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:11.052522+00:00
-- url     : https://prove2.me/theorems/ecdb2382-aa70-460e-8913-ec3d2bfddff7
-- title:
--   Selected-floor prefix certificate for prepared pair 26, left list, part 19
-- statement:
--   For prepared pair 26, left list, part 19, the selected-floor certificate succeeds for at most `3` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared26.sieve`. Original heads 170 through 172; all later vertices retained.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft26_002Part19.lean, lines 7-11, SHA-256 06bc6c7fc82495f480d38c0b26db8af54ddf8bea548e13de559386db42e0675a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared26.left_prefix_002_part19_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached002.drop 57) (leftRows002.drop 57) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared26
end
