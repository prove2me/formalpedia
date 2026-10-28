-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_parallel_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:23:41.364284+00:00
-- url     : https://prove2.me/theorems/443057ec-5f03-4b13-a0cc-269b00d8057d
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list, part 0
-- statement:
--   For prepared pair 15, left list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 0 through 11, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft15_000Part00.lean, lines 10-14, SHA-256 d37e9e75aae2bb789ae9114468ccd813d999e71a9263a19eb9a2f6ac5b4688c5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_parallel_000_part00_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.leftCached.drop 0) (PairLightPrepared15.leftRows.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
