-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared7_left_prefix_002_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared7.left_prefix_002_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:18:47.570265+00:00
-- url     : https://prove2.me/theorems/08b3fb88-558a-467a-9beb-415c89904f1c
-- title:
--   Selected-floor prefix certificate for prepared pair 7, left list, part 0
-- statement:
--   For prepared pair 7, left list, part 0, the selected-floor certificate succeeds for at most `24` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared7.sieve`. Original heads 268 through 291, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft7_002Part00.lean, lines 11-16, SHA-256 1fbc4888a414beda98d2a5435ce465b8583f3bf9cf40ae38ab68defa1d8a3d3e. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared7.left_prefix_002_part00_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 24
      (PairLightPrepared7.leftCached.drop 268)
      (PairLightPrepared7.leftRows.drop 268) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared7
end
