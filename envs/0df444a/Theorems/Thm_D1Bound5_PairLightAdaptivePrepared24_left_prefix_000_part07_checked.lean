-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_left_prefix_000_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.left_prefix_000_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:03.843293+00:00
-- url     : https://prove2.me/theorems/1796ef4f-2efd-4424-98a8-f8937ed96cf4
-- title:
--   Selected-floor prefix certificate for prepared pair 24, left list, part 7
-- statement:
--   For prepared pair 24, left list, part 7, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 84 through 95, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft24_000Part07.lean, lines 11-16, SHA-256 4b7a72a5d2fe5a1da437e89df9c81c251682797663d7923d841b6d85f1579d5f. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.left_prefix_000_part07_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 12
      (PairLightPrepared24.leftCached.drop 84)
      (PairLightPrepared24.leftRows.drop 84) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
