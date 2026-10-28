-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared48_left_prefix_000_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared48.left_prefix_000_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:29:08.809461+00:00
-- url     : https://prove2.me/theorems/639f489b-8b5d-4141-919a-e47bd9172494
-- title:
--   Selected-floor prefix certificate for prepared pair 48, left list, part 3
-- statement:
--   For prepared pair 48, left list, part 3, the selected-floor certificate succeeds for at most `40` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 8, and the sieve is `PairLightPrepared48.sieve`. Original heads 94 through 133; each retains its entire original tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft48_000Part03.lean, lines 7-11, SHA-256 3b252163dcb8252c4ba9b56fe7af400c604140dac7dbd84e9138a4580799c415. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared48.left_prefix_000_part03_checked :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 40
      (leftCached000.drop 94) (leftRows000.drop 94) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared48
end
