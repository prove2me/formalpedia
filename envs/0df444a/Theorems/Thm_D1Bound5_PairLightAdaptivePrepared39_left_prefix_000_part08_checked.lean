-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_000_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.left_prefix_000_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:15:02.969604+00:00
-- url     : https://prove2.me/theorems/11b374ee-2e38-4d07-9f4b-a5983f4b54a9
-- title:
--   Selected-floor prefix certificate for prepared pair 39, left list, part 8
-- statement:
--   For prepared pair 39, left list, part 8, the selected-floor certificate succeeds for at most `1` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 96 through 96, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft39_000Part08.lean, lines 11-16, SHA-256 352841f278fed3679829b8fb40415018ef14c69a41f5e132e3968c0a816609f2. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.left_prefix_000_part08_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 1
      (PairLightPrepared39.leftCached.drop 96)
      (PairLightPrepared39.leftRows.drop 96) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
