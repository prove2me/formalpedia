-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_pilot12_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.left_pilot12_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:05:28.760879+00:00
-- url     : https://prove2.me/theorems/418f5936-cfd2-48cc-a836-aa01cf59c100
-- title:
--   Selected-floor prefix certificate for prepared pair 7, left list, part 0
-- statement:
--   For prepared pair 7, left list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 0 through 11, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft7_Pilot12Part00.lean, lines 11-16, SHA-256 3a0f74f1a69fc728f9f2a505bffad8ebdf3d9678b603d8b4c7b4ec230910791b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.left_pilot12_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 12
      (PairLightPrepared7.leftCached.drop 0)
      (PairLightPrepared7.leftRows.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
