-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared3_left_prefix_000_part04_checked
-- name    : D1Bound5.PairLightAdaptivePrepared3.left_prefix_000_part04_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:24:51.390853+00:00
-- url     : https://prove2.me/theorems/0a1cdd2b-777b-4fd1-9d80-2d3ae7249b41
-- title:
--   Selected-floor prefix certificate for prepared pair 3, left list, part 4
-- statement:
--   For prepared pair 3, left list, part 4, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 1, and the sieve is `PairLightPrepared3.sieve`. Original heads 48 through 59, each checked against its complete tail.
-- source:
--   D1Bound5/SmallPairLightAdaptiveLeft3_000Part04.lean, lines 9-14, SHA-256 7d0174abda1fdf18fcc42532fbaef771713eb8954fc9e9babb6f28d5d86eb292. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared3.left_prefix_000_part04_checked :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 12
      (PairLightPrepared3.leftCached.drop 48)
      (PairLightPrepared3.leftRows.drop 48) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared3
end
