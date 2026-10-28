-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.left_prefix_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:31:23.330948+00:00
-- url     : https://prove2.me/theorems/f8b36c71-ad6b-424f-bc45-8c3a8cc8c145
-- title:
--   Selected-floor prefix certificate for prepared pair 7, left list, part 3
-- statement:
--   For prepared pair 7, left list, part 3, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 177 through 200, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft7_001Part03.lean, lines 11-16, SHA-256 cad5945de4982b2696af61cb10ad448eed5c8845fd566165a9604d3ef97df862. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.left_prefix_001_part03_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 24
      (PairLightPrepared7.leftCached.drop 177)
      (PairLightPrepared7.leftRows.drop 177) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
