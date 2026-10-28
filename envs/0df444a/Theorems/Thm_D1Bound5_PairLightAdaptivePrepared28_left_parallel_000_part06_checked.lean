-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_000_part06_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_parallel_000_part06_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:08:00.291797+00:00
-- url     : https://prove2.me/theorems/1b18930b-f91b-4dcb-8d1f-3c288bd8ea4d
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list, part 6
-- statement:
--   For prepared pair 28, left list, part 6, the selected-floor certificate succeeds for at most `10` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 72 through 81, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft28_000Part06.lean, lines 10-14, SHA-256 2e1ada4c7ce3a4f096ff7681473ed19ca68c9853fb9438770ed37478977702c9. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_parallel_000_part06_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 10
      (PairLightPrepared28.leftCached.drop 72) (PairLightPrepared28.leftRows.drop 72) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
