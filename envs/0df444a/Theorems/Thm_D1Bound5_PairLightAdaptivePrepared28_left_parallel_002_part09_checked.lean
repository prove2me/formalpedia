-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_002_part09_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_parallel_002_part09_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:52.279022+00:00
-- url     : https://prove2.me/theorems/41e83ce2-2819-4a7b-9d3e-e67f48eb6242
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list, part 9
-- statement:
--   For prepared pair 28, left list, part 9, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 292 through 303, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft28_002Part09.lean, lines 10-14, SHA-256 db10fbb467274e5fc0391db104a948361430062a306d423dad87355e71e90344. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_parallel_002_part09_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 292) (PairLightPrepared28.leftRows.drop 292) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
