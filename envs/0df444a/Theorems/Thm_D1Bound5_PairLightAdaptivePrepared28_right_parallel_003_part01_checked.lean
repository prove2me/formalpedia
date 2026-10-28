-- Prove2me | Theorems.Thm_D1Bound5_PairLightAdaptivePrepared28_right_parallel_003_part01_checked
-- name    : D1Bound5.PairLightAdaptivePrepared28.right_parallel_003_part01_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:07:15.030121+00:00
-- url     : https://prove2.me/theorems/a97aa08d-0bfc-4f95-b92b-d02ffef1b596
-- title:
--   Selected-floor prefix certificate for prepared pair 28, right list, part 1
-- statement:
--   For prepared pair 28, right list, part 1, the selected-floor certificate succeeds for at most `12` head rows of the supplied cached vertex list. Each selected head is checked against its complete remaining tail, including vertices beyond the end of this chunk. The quadratic coordinate parameters are τ = 1 and ν = 1, and the sieve is `PairLightPrepared28.sieve`. Original heads 347 through 358, with every original tail comparison.
-- source:
--   D1Bound5/SmallPairParallelRight28_003Part01.lean, lines 10-14, SHA-256 9e6adbecc17b40a8bce39db50e934a59bd2ac58a0507cb1094610e92a5afd20e. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.PairLightAdaptivePrepared28.right_parallel_003_part01_checked :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 347) (PairLightPrepared28.rightRows.drop 347) = true := by sorry

end D1Bound5.PairLightAdaptivePrepared28
end
