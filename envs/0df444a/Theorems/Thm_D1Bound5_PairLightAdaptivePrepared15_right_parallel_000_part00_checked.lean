-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_000_part00_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_000_part00_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:19:48.144811+00:00
-- url     : https://prove2.me/theorems/e65e75b8-3452-42d3-ab84-dd1fac7f65e8
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 0
-- statement:
--   For prepared pair 15, right list, part 0, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 0 through 11, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_000Part00.lean, lines 10-14, SHA-256 3363dc931ce000d64e8eb9dcf01582c6e4a9f379fe846787f8f755ef69f28705. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_000_part00_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 0) (PairLightPrepared15.rightRows.drop 0) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
