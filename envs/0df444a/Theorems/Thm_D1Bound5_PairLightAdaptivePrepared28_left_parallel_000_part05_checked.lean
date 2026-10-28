-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_000_part05_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_parallel_000_part05_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:01:32.343378+00:00
-- url     : https://prove2.me/theorems/37e9d111-0109-4df6-bc68-8cabf7e9308c
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list, part 5
-- statement:
--   For prepared pair 28, left list, part 5, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 60 through 71, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft28_000Part05.lean, lines 10-14, SHA-256 ceb911d15368e5c8ef75b9ec8db8b3c32304027e0875b21b52a50cbf3f57bffb. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_parallel_000_part05_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 60) (PairLightPrepared28.leftRows.drop 60) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
