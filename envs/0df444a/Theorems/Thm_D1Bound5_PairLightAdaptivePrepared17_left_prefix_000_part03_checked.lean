-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared17_left_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared17.left_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:14:09.175986+00:00
-- url     : https://prove2.me/theorems/21d7e603-8231-49aa-9232-22018727fcc8
-- title:
--   Selected-floor prefix certificate for prepared pair 17, left list, part 3
-- statement:
--   For prepared pair 17, left list, part 3, the selected-floor certificate succeeds for at most `40` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared17.sieve`. Original heads 94 through 133; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft17_000Part03.lean, lines 7-11, SHA-256 2160a850bb1652f77fb59e56b1e1929ec3a096b38d9530db0f82d1172273206e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared17.left_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 40
      (leftCached000.drop 94) (leftRows000.drop 94) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared17
end
