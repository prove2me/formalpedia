-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared14_right_parallel_000_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared14.right_parallel_000_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:13:53.993908+00:00
-- url     : https://prove2.me/theorems/e28cf6b7-2edd-49a3-8854-3f1291b509ce
-- title:
--   Selected-floor prefix certificate for prepared pair 14, right list, part 6
-- statement:
--   For prepared pair 14, right list, part 6, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 0 and ν = 2, and the sieve is `PairLightPrepared14.sieve`. Original heads 72 through 83, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight14_000Part06.lean, lines 10-14, SHA-256 5514c8eb09812da0bcbe65b666ecd789b5224f1b787cff2d5cf96c1a7cf4bdc9. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared14.right_parallel_000_part06_checked :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 72) (PairLightPrepared14.rightRows.drop 72) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared14
end
