-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared21_right_parallel_002_part08_checked
-- name    : D1Bound5.PairLightAdaptivePrepared21.right_parallel_002_part08_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:27:49.160996+00:00
-- url     : https://prove2.me/theorems/98c6b78d-174a-4164-a713-e6bddb6e638f
-- title:
--   Selected-floor prefix certificate for prepared pair 21, right list, part 8
-- statement:
--   For prepared pair 21, right list, part 8, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared21.sieve`. Original heads 280 through 291, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight21_002Part08.lean, lines 10-14, SHA-256 3b79b0f671fb0b42e74cb6d6672354df55b1504dd717829a6de4605d69bb97a0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.PairLightAdaptivePrepared21.right_parallel_002_part08_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.rightCached.drop 280) (PairLightPrepared21.rightRows.drop 280) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared21
end
