-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared6_left_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared6.left_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:26:02.655313+00:00
-- url     : https://prove2.me/theorems/1f4da445-49de-4306-a9ea-b2d7df0f4031
-- title:
--   Selected-floor prefix certificate for prepared pair 6, left list, part 4
-- statement:
--   For prepared pair 6, left list, part 4, the selected-floor certificate succeeds for at most `11` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared6.sieve`. Original heads 41 through 51, retaining complete original tails.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft6_000Part04.lean, lines 11-16, SHA-256 59944967a5cee94a4d89221e60a6334c445793a24f5f66f993ad67afba8cef27. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared6.left_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 11
      (PairLightPrepared6.leftCached.drop 41)
      (PairLightPrepared6.leftRows.drop 41) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared6
end
