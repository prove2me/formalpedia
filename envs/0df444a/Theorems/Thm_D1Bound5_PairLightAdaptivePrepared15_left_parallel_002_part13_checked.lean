-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_left_parallel_002_part13_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.left_parallel_002_part13_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:17:46.670546+00:00
-- url     : https://prove2.me/theorems/63a7efec-f5df-431d-8579-b8a729f686e8
-- title:
--   Selected-floor prefix certificate for prepared pair 15, left list, part 13
-- statement:
--   For prepared pair 15, left list, part 13, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 370 through 381, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft15_002Part13.lean, lines 10-14, SHA-256 83a84728a3aaed5dca1f96e662ed493ba739bd93d41b4a28465400c4fd53c8c6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.left_parallel_002_part13_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.leftCached.drop 370) (PairLightPrepared15.leftRows.drop 370) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
