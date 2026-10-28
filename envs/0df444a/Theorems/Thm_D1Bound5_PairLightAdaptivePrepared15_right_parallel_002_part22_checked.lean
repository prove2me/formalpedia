-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part22_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part22_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:35.204588+00:00
-- url     : https://prove2.me/theorems/5f62a988-bff2-41ae-b8cb-44ea067235dc
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 22
-- statement:
--   For prepared pair 15, right list, part 22, the selected-floor certificate succeeds for at most `2` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 478 through 479, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_002Part22.lean, lines 10-14, SHA-256 96527b44c15fd75adc771217afd6bd870f091409db05487a051e5c4a4986d416. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part22_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 2
      (PairLightPrepared15.rightCached.drop 478) (PairLightPrepared15.rightRows.drop 478) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
