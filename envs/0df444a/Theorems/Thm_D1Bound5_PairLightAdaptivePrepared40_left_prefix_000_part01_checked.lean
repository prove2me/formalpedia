-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_left_prefix_000_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared40.left_prefix_000_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:48.797114+00:00
-- url     : https://prove2.me/theorems/b79340fa-f6cf-4c90-98b4-395f9063fd51
-- title:
--   Selected-floor prefix certificate for prepared pair 40, left list, part 1
-- statement:
--   For prepared pair 40, left list, part 1, the selected-floor certificate succeeds for at most `31` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 2, and the sieve is `PairLightPrepared40.sieve`. Original heads 28 through 58; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft40_000Part01.lean, lines 7-11, SHA-256 8d91568589af76b280bfff2942e229507facd659a92effd7528983a25fe8aa53. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared40.left_prefix_000_part01_checked :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 31
      (leftCached000.drop 28) (leftRows000.drop 28) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared40
end
