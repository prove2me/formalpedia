-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_002_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.left_prefix_002_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:59:03.229371+00:00
-- url     : https://prove2.me/theorems/a3526a1b-7606-4e18-8c88-98bdcefbe747
-- title:
--   Selected-floor prefix certificate for prepared pair 7, left list, part 4
-- statement:
--   For prepared pair 7, left list, part 4, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 364 through 387, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft7_002Part04.lean, lines 11-16, SHA-256 57d3a1e74059c2c89822ffc2ea50c20737c0ffbf8b65449da06b9b40e952b06f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.left_prefix_002_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 24
      (PairLightPrepared7.leftCached.drop 364)
      (PairLightPrepared7.leftRows.drop 364) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
