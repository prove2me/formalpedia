-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared36_left_parallel_002_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared36.left_parallel_002_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:28:56.653623+00:00
-- url     : https://prove2.me/theorems/86321852-a8aa-4445-a6e0-1c27b92a2d1e
-- title:
--   Selected-floor prefix certificate for prepared pair 36, left list, part 7
-- statement:
--   For prepared pair 36, left list, part 7, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared36.sieve`. Original heads 251 through 262, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft36_002Part07.lean, lines 10-14, SHA-256 924e9beb8aea9f902588223319f607ee436ffdb6ad79fe8c7b00d7e6b88401a2. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared36.left_parallel_002_part07_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 251) (PairLightPrepared36.leftRows.drop 251) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared36
end
