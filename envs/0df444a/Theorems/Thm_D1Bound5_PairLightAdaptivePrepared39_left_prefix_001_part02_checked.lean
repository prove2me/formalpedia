-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared39_left_prefix_001_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared39.left_prefix_001_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:31.073948+00:00
-- url     : https://prove2.me/theorems/dfbeaaae-c08f-473e-a874-c1c2620e34ea
-- title:
--   Selected-floor prefix certificate for prepared pair 39, left list, part 2
-- statement:
--   For prepared pair 39, left list, part 2, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared39.sieve`. Original heads 145 through 168, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft39_001Part02.lean, lines 11-16, SHA-256 5c0451ed2fb91ec1992292dceb5b80a2de4accc794be4e75f2c8401e9ac4c03a. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared39.left_prefix_001_part02_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 24
      (PairLightPrepared39.leftCached.drop 145)
      (PairLightPrepared39.leftRows.drop 145) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared39
end
