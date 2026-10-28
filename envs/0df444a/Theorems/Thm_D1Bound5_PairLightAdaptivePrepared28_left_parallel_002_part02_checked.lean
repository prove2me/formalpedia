-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_left_parallel_002_part02_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.left_parallel_002_part02_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:11:26.392082+00:00
-- url     : https://prove2.me/theorems/8680407b-0439-499b-a80d-aefa8cb200f9
-- title:
--   Selected-floor prefix certificate for prepared pair 28, left list, part 2
-- statement:
--   For prepared pair 28, left list, part 2, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 208 through 219, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelLeft28_002Part02.lean, lines 10-14, SHA-256 15f833dfd0e499b22a81eb5b55ef92a231faf3f3f6706be154505a3bb0e7c9e9. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.left_parallel_002_part02_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 208) (PairLightPrepared28.leftRows.drop 208) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
