-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_002_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_002_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:14.72406+00:00
-- url     : https://prove2.me/theorems/c024420d-05a8-4ba3-9615-d93c97dcb09a
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list, part 0
-- statement:
--   For prepared pair 6, left list, part 0, the selected-floor certificate succeeds for at most `13` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 134 through 146, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_002Part00.lean, lines 11-16, SHA-256 df3449c44d7ebf0ef4e5f1f1bad713d77c7a272695ab9847efef229d92ec5c36. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_002_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 13
      (PairLightPrepared6.leftCached.drop 134)
      (PairLightPrepared6.leftRows.drop 134) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
