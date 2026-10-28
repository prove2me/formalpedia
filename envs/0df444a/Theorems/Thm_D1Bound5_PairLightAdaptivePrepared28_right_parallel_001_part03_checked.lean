-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_001_part03_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_001_part03_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:10:40.47708+00:00
-- url     : https://prove2.me/theorems/f4babdcc-85c2-4588-9c93-d86667d642cd
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 3
-- statement:
--   For prepared pair 28, right list, part 3, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 118 through 129, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_001Part03.lean, lines 10-14, SHA-256 f26daeccdc6f161869d9958c77f488be2e9932005a472831e56ddb58dc8f9eef. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_001_part03_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 118) (PairLightPrepared28.rightRows.drop 118) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
