-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_left_prefix_001_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared40.left_prefix_001_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:32:41.345457+00:00
-- url     : https://prove2.me/theorems/e7e16ade-6b68-41b2-b916-1b2b72d64d5c
-- title:
--   Selected-floor prefix certificate for prepared pair 40, left list, part 0
-- statement:
--   For prepared pair 40, left list, part 0, the selected-floor certificate succeeds for at most `50` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared40.sieve`. Original heads 137 through 186; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft40_001Part00.lean, lines 7-11, SHA-256 bed9d5189bd00c8ec915dd91c53f8cf50272d21f1d70aa95e4621dd3c196379e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared40.left_prefix_001_part00_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 50
      (leftCached001.drop 0) (leftRows001.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared40
end
