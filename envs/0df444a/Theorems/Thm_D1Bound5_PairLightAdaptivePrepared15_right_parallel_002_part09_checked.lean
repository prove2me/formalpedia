-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part09_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:12:23.438755+00:00
-- url     : https://prove2.me/theorems/b9f4ee30-bc35-4742-bbb5-30f867d2fdb1
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 9
-- statement:
--   For prepared pair 15, right list, part 9, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 322 through 333, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_002Part09.lean, lines 10-14, SHA-256 2adb8b0d2df1f3cac3560245125d23cf30d64e76dfab78e5a9ab884a993ec46c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part09_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 322) (PairLightPrepared15.rightRows.drop 322) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
