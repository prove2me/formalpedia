-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared24_left_prefix_002_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared24.left_prefix_002_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:19.554257+00:00
-- url     : https://prove2.me/theorems/7b218950-0664-4574-bc27-a38123418452
-- title:
--   Selected-floor prefix certificate for prepared pair 24, left list, part 5
-- statement:
--   For prepared pair 24, left list, part 5, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared24.sieve`. Original heads 368 through 391, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft24_002Part05.lean, lines 11-16, SHA-256 cc5f5157d7a522486f143e0cdbe9b58e0bd1dd81aee796b5da4dff1b8fbcde46. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared24.left_prefix_002_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 24
      (PairLightPrepared24.leftCached.drop 368)
      (PairLightPrepared24.leftRows.drop 368) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared24
end
