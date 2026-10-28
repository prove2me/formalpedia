-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_001_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_001_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:30:13.687398+00:00
-- url     : https://prove2.me/theorems/3e8132c1-c12d-44d6-9429-13d3b9ee17f4
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 1
-- statement:
--   For prepared pair 15, right list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 104 through 115, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_001Part01.lean, lines 10-14, SHA-256 c4db52c5c9327a2af7f1e54803284ba4c0221c034c7bd3961b8996584750dedc. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_001_part01_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 104) (PairLightPrepared15.rightRows.drop 104) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
