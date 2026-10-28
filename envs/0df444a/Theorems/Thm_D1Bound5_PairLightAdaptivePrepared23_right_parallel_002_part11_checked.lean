-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared23_right_parallel_002_part11_checked
-- name    : D1Bound5.PairLightAdaptivePrepared23.right_parallel_002_part11_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:06:21.149228+00:00
-- url     : https://prove2.me/theorems/7a43b595-2c9a-4484-a4f0-8b36c7002a86
-- title:
--   Selected-floor prefix certificate for prepared pair 23, right list, part 11
-- statement:
--   For prepared pair 23, right list, part 11, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared23.sieve`. Original heads 346 through 357, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight23_002Part11.lean, lines 10-14, SHA-256 37a376abe33baed49668354a476b306529ca8e94f49e73a72d3848679232dd22. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared23.right_parallel_002_part11_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.rightCached.drop 346) (PairLightPrepared23.rightRows.drop 346) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared23
end
