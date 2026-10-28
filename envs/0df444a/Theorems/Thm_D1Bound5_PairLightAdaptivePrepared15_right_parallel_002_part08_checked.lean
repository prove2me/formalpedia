-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared15_right_parallel_002_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:58:51.802549+00:00
-- url     : https://prove2.me/theorems/cce6cd97-885b-4ac8-b9b8-c84f126e7a79
-- title:
--   Selected-floor prefix certificate for prepared pair 15, right list, part 8
-- statement:
--   For prepared pair 15, right list, part 8, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared15.sieve`. Original heads 310 through 321, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight15_002Part08.lean, lines 10-14, SHA-256 039d8721dac837c0250107c824e90dafee90d8cca51aa2753855f3bc9cbe1503. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared15.right_parallel_002_part08_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 310) (PairLightPrepared15.rightRows.drop 310) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared15
end
