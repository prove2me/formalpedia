-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_left_parallel_001_part07_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.left_parallel_001_part07_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:10.793054+00:00
-- url     : https://prove2.me/theorems/17109346-2194-486b-b157-5ae304280a51
-- title:
--   Selected-floor prefix certificate for prepared pair 21, left list, part 7
-- statement:
--   For prepared pair 21, left list, part 7, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 166 through 177, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft21_001Part07.lean, lines 10-14, SHA-256 c3ec3a08a23d0cb232104c7fbfedd3874c53efaecde3045a83f53ae534fb95be. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.left_parallel_001_part07_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.leftCached.drop 166) (PairLightPrepared21.leftRows.drop 166) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
