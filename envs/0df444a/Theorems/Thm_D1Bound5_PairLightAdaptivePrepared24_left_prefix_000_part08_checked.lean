-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_left_prefix_000_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.left_prefix_000_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:46.672383+00:00
-- url     : https://prove2.me/theorems/16c68189-15d4-4265-a9da-8df1dfb9bbd2
-- title:
--   Selected-floor prefix certificate for prepared pair 24, left list, part 8
-- statement:
--   For prepared pair 24, left list, part 8, the selected-floor certificate succeeds for at most `5` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 96 through 100, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft24_000Part08.lean, lines 11-16, SHA-256 27b42c3e13933552a3c5aa8bff856c85b08cd0ebba7a5e3c9152eaba843ebc9c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.left_prefix_000_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 5
      (PairLightPrepared24.leftCached.drop 96)
      (PairLightPrepared24.leftRows.drop 96) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
