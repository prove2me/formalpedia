-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_000_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_000_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:20:01.69784+00:00
-- url     : https://prove2.me/theorems/d7813d8c-8925-47e6-a3b2-5834d3ca02d1
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 5
-- statement:
--   For prepared pair 15, right list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 60 through 71, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_000Part05.lean, lines 10-14, SHA-256 2dbe15754b52e3e35a5c758f0a9b4303fa183015de3a4662ad3fb8beb9ec13ac. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_000_part05_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 60) (PairLightPrepared15.rightRows.drop 60) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
